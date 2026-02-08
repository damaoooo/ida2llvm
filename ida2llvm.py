#!/usr/bin/env python3
import idapro  # 必须是第一个 import，用于 idalib
import idc
import ida_idaapi
import ida_kernwin
import idautils
import ida_name
import ida_bytes
import ida_ida
import ida_funcs
import ida_typeinf
import ida_segment
import ida_nalt
import ida_hexrays
import ida_auto
import itertools
import idaapi
import logging
import struct
import numpy as np
import sys
import typer
import llvmlite.binding as llvm
from llvmlite import ir

from contextlib import suppress

# ============================================================================
# 常量定义
# ============================================================================
i8ptr = ir.IntType(8).as_pointer()
ptrsize = 64 if ida_ida.inf_is_64bit() else 32
ptext = {}  # 缓存反编译的函数: {地址: 反编译结果}
refreshed_funcs = set()  # 避免重复触发无缓存反编译

# 线程局部存储段大小（Windows FS段标准大小）
FS_SEGMENT_SIZE = 0x10000  # 64KB

# 浮点数提取失败时的默认值
DEFAULT_FLOAT_VALUE = 1.0

def lift_tif(tif: ida_typeinf.tinfo_t, width = -1) -> ir.Type:
    """
    将IDA类型转换为对应的LLVM类型。
    如果IDA类型是数组/结构体/复合类型，则递归执行类型转换。

    :param tif: 要转换的IDA类型
    :type tif: ida_typeinf.tinfo_t
    :raises NotImplementedError: 不支持可变长度结构体
    :return: 转换后的LLVM类型
    :rtype: ir.Type
    """
    if tif.is_func():
        ida_rettype = tif.get_rettype()                           
        ida_args = (tif.get_nth_arg(i) for i in range(tif.get_nargs()))
        is_vararg = tif.is_vararg_cc()                               
        llvm_rettype = lift_tif(ida_rettype)                            
        llvm_args = (lift_tif(arg) for arg in ida_args)
        return ir.FunctionType(i8ptr if isinstance(llvm_rettype, ir.VoidType) else llvm_rettype, llvm_args, var_arg = is_vararg) 

    elif tif.is_ptr():
        child_tif = tif.get_ptrarr_object()
        if child_tif.is_void():
            return ir.IntType(8).as_pointer()
        return lift_tif(child_tif).as_pointer()

    elif tif.is_array():
        child_tif = tif.get_ptrarr_object()
        element = lift_tif(child_tif)
        count = tif.get_array_nelems()
        if count == 0:
            # 元素数量不确定的数组 = 指针类型
            tif.convert_array_to_ptr()
            return lift_tif(tif)      
        return ir.ArrayType(element, count)

    elif tif.is_void():
        return ir.VoidType()

    elif tif.is_udt():
        udt_data = ida_typeinf.udt_type_data_t()
        tif.get_udt_details(udt_data)
        type_name = tif.get_type_name()
        context = ir.context.global_context
        
        type_name = "struct" if type_name == None else type_name

        if type_name not in context.identified_types:
            struct_t = context.get_identified_type(type_name)
            elementTypes = []
            for idx in range(udt_data.size()):
                udt_member = udt_data.at(idx)
                if udt_member.type.get_type_name() in context.identified_types:
                    elementTypes.append(context.identified_types[udt_member.type.get_type_name()])
                else:
                    element = lift_tif(udt_member.type)
                    elementTypes.append(element)

            struct_t.set_body(*elementTypes)
        return context.get_identified_type(type_name)

    elif tif.is_bool():
        return ir.IntType(1)

    elif tif.is_char():
        return ir.IntType(8)

    elif tif.is_float():
        return ir.FloatType()

    elif tif.is_double():
        return ir.DoubleType()

    # elif tif.is_ldouble():
    #     return ir.DoubleType()  # llvmlite不支持long double

    elif tif.is_decl_int() or tif.is_decl_uint() or tif.is_uint() or tif.is_int():
        return ir.IntType(tif.get_size()*8)
        
    elif tif.is_decl_int16() or tif.is_decl_uint16() or tif.is_uint16() or tif.is_int16():
        return ir.IntType(tif.get_size()*8)
        
    elif tif.is_decl_int32() or tif.is_decl_uint32() or tif.is_uint32() or tif.is_int32():
        return ir.IntType(tif.get_size()*8)
        
    elif tif.is_decl_int64() or tif.is_decl_uint64() or tif.is_uint64() or tif.is_int64():
        return ir.IntType(tif.get_size()*8)
        
    elif tif.is_decl_int128() or tif.is_decl_uint128() or tif.is_uint128() or tif.is_int128():
        return ir.IntType(tif.get_size()*8)

    elif tif.is_ext_arithmetic() or tif.is_arithmetic():
        size_bits = tif.get_size() * 8
        # 防止创建过大的整数类型（限制为128位）
        if size_bits > 128 or size_bits <= 0:
            # logging.warning(f"Invalid type size {tif.get_size()} bytes, using pointer size instead")
            return ir.IntType(ptrsize)
        return ir.IntType(size_bits)
        
    else:
        if width != -1:
            # 防止创建过大的数组（限制为1MB）
            if width > 1024 * 1024 or width <= 0:
                # logging.warning(f"Invalid array width {width} bytes, using pointer type instead")
                return ir.IntType(ptrsize)
            return ir.ArrayType(ir.IntType(8), width)
        else:
            return ir.IntType(ptrsize)

def typecast(src: ir.Value, dst_type: ir.Type, builder: ir.IRBuilder, signed: bool = False) -> ir.Value:
    """
    将源值转换为目标类型。
    转换指令会被插入到builder中。

    :param src: 要转换的值
    :type src: ir.Value
    :param dst_type: 目标类型
    :type dst_type: ir.Type
    :param builder: 指令构建器
    :type builder: ir.IRBuilder
    :param signed: 是否保留符号性，默认False
    :type signed: bool, optional
    :raises NotImplementedError: 不支持的类型转换
    :return: 类型转换后的值
    :rtype: ir.Value   
    """
    if src.type != dst_type:
        if isinstance(src.type, ir.PointerType) and isinstance(dst_type, ir.PointerType):
            return builder.bitcast(src, dst_type)
        elif isinstance(src.type, ir.PointerType) and isinstance(dst_type, ir.IntType):
            return builder.ptrtoint(src, dst_type)
        elif isinstance(src.type, ir.IntType) and isinstance(dst_type, ir.PointerType):
            return builder.inttoptr(src, dst_type)
        elif isinstance(src.type, ir.IntType) and isinstance(dst_type, ir.FloatType):
            return builder.uitofp(src, dst_type)
        elif isinstance(src.type, ir.FloatType) and isinstance(dst_type, ir.IntType):
            if signed == False:
                return builder.fptoui(src, dst_type)
            else:
                return builder.fptosi(src, dst_type)
        elif isinstance(src.type, ir.DoubleType) and isinstance(dst_type, ir.IntType):
            if signed == False:
                return builder.fptoui(src, dst_type)
            else:
                return builder.fptosi(src, dst_type)
        elif isinstance(src.type, ir.FloatType) and isinstance(dst_type, ir.FloatType):
            return src
        elif isinstance(src.type, ir.IntType) and isinstance(dst_type, ir.IntType) and src.type.width < dst_type.width:
            if signed:
                return builder.sext(src, dst_type)
            else:
                return builder.zext(src, dst_type)
        elif isinstance(src.type, ir.IntType) and isinstance(dst_type, ir.IntType) and src.type.width > dst_type.width:
            return builder.trunc(src, dst_type)

        elif isinstance(src.type, ir.IntType) and isinstance(dst_type, ir.DoubleType):
            return builder.uitofp(src, dst_type)

        elif isinstance(src.type, ir.FloatType) and isinstance(dst_type, ir.DoubleType):
            return builder.fpext(src, dst_type)

        elif isinstance(src.type, ir.DoubleType) and isinstance(dst_type, ir.FloatType):
            return builder.fptrunc(src, dst_type)

        elif (isinstance(src.type, ir.DoubleType) or isinstance(src.type, ir.FloatType)) and isinstance(dst_type, ir.PointerType):
            if signed == False:
                tmp =  builder.fptoui(src, ir.IntType(ptrsize))
            else:
                tmp = builder.fptosi(src, ir.IntType(ptrsize))
            return builder.inttoptr(tmp, dst_type)

        elif (isinstance(dst_type, ir.DoubleType) or isinstance(dst_type, ir.FloatType)) and isinstance(src.type, ir.PointerType):
            tmp = builder.ptrtoint(src, ir.IntType(ptrsize))
            return builder.uitofp(tmp, dst_type)

        elif isinstance(dst_type, ir.IdentifiedStructType) or isinstance(dst_type, ir.ArrayType): 
            with builder.goto_entry_block():
                tmp = builder.alloca(src.type)
            builder.store(src, tmp)
            src = builder.load(builder.bitcast(tmp, dst_type.as_pointer()))

        elif isinstance(src.type, ir.IdentifiedStructType) or isinstance(src.type, ir.ArrayType): 
            with builder.goto_entry_block():
                tmp = builder.alloca(src.type)
            builder.store(src, tmp)
            src = builder.load(builder.bitcast(tmp, dst_type.as_pointer()))

        else:
            return builder.bitcast(src, dst_type)
    return src

def storecast(src, dst, builder):
    """
    将目标的类型转换为源的指针类型。
    """
    if dst != None and dst.type != src.type.as_pointer():
        dst = typecast(dst, src.type.as_pointer(), builder) 
    return dst

def get_offset_to(builder: ir.IRBuilder, arg: ir.Value, off: int = 0) -> ir.Value:
    """
    根据偏移量对值进行索引。

    :param arg: 要索引的值
    :type arg: ir.Value
    :param off: 索引偏移量，默认为0
    :type off: int, optional
    :return: 按偏移量索引后的值
    :rtype: ir.Value
    """
    if isinstance(arg.type, ir.PointerType) and isinstance(arg.type.pointee, ir.ArrayType):
        arr = arg.type.pointee
        td = llvm.create_target_data("e")
        size = arr.element.get_abi_size(td)
        return builder.gep(arg, (ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), off // size),))
    # elif isinstance(arg.type, ir.PointerType) and isinstance(arg.type.pointee, ir.LiteralStructType):
    #     return typecast(arg, ir.IntType(8).as_pointer(), builder)
    elif isinstance(arg.type, ir.PointerType) and isinstance(arg.type.pointee, ir.IdentifiedStructType):
        return typecast(arg, ir.IntType(8).as_pointer(), builder)
    elif isinstance(arg.type, ir.PointerType) and off > 0:
        td = llvm.create_target_data("e")
        size = arg.type.pointee.get_abi_size(td)
        return builder.gep(arg, (ir.Constant(ir.IntType(32), off // size),))
    else:
        return arg

def dedereference(arg: ir.Value) -> ir.Value:
    """
    "反解引用"操作：从已加载的值中获取原始内存地址。
    
    在LLVM中，LoadInstruction会从内存地址加载值（解引用）。
    当我们需要获取原始内存地址时，需要"反解引用"。
    
    需要这个操作的原因：
    - IDA微代码将所有局部变量(LVARS)视为寄存器
    - 而在提升时我们将所有LVARS视为栈变量（符合LLVM SSA形式）

    :param arg: 需要反解引用的值
    :type arg: ir.Value
    :raises NotImplementedError: 参数不是LoadInstr类型
    :return: 原始内存地址
    :rtype: ir.Value
    """
    if isinstance(arg, ir.LoadInstr):
        return arg.operands[0]
    elif isinstance(arg.type, ir.PointerType):
        return arg
    else:
        raise NotImplementedError(f"not implemented: get reference for object {arg} of type {arg.type}")


def lift_type_from_address(ea: int, pfunc=None):
    """从地址获取类型信息。"""
    if ida_funcs.get_func(ea) != None and ida_segment.segtype(ea) & ida_segment.SEG_XTRN:
        # 假设这是一个返回void且接受可变参数的函数
        ida_func_details = ida_typeinf.func_type_data_t()
        void = ida_typeinf.tinfo_t()
        void.create_simple_type(ida_typeinf.BTF_VOID)
        ida_func_details.rettype = void
        ida_func_details.cc = ida_typeinf.CM_CC_ELLIPSIS | ida_typeinf.CC_CDECL_OK

        function_tinfo = ida_typeinf.tinfo_t()
        function_tinfo.create_func(ida_func_details)
        return function_tinfo

    if ea in ptext:
        return ptext[ea].type
            
    tif = ida_typeinf.tinfo_t()
    has_tinfo = ida_nalt.get_tinfo(tif, ea)
    if not has_tinfo:
        ida_typeinf.guess_tinfo(tif, ea)
    return tif

def analyze_insn(module, ida_insn, ea):
    """
    Analyzes function call instructions for parameter count mismatches.
    
    Problem: Sometimes IDA's type propagation is incomplete, causing a mismatch
    between the number of arguments in a call and the function's actual signature.
    For example, function A calls function B with 3 arguments, but B's signature
    expects 4 arguments.
    
    Solution: Force re-decompilation of both caller and callee to refresh type
    information and resolve the mismatch.
    
    :param module: LLVM module being constructed
    :param ida_insn: Microcode instruction to analyze
    :param ea: Address of the instruction
    """
    if ida_insn.opcode == ida_hexrays.m_call:
        callnum = len(ida_insn.d.f.args)
        if ida_insn.l.t == ida_hexrays.mop_v: 
            temp_ea = ida_insn.l.g
            func_name = ida_name.get_name(temp_ea)
            temp_func = ida_funcs.get_func(temp_ea)
            if ((temp_func is not None)
            and (temp_func.flags & ida_funcs.FUNC_THUNK)): 
                tfunc_ea, ptr = ida_funcs.calc_thunk_func_target(temp_func)
                if tfunc_ea != ida_idaapi.BADADDR:
                    temp_ea = tfunc_ea
                    func_name = ida_name.get_name(temp_ea)

            tif = lift_type_from_address(temp_ea)
            if tif.is_func() or tif.is_funcptr():
                argnum = tif.get_nargs()
                with suppress(KeyError):
                    if func_name == "":
                        func_name = f"data_{hex(ea)[2:]}"
                    if hasattr(module.get_global(func_name
                                                 ), "args"):
                        argnum = len(module.get_global(func_name).args)

                if callnum != argnum:
                    ida_hf = ida_hexrays.hexrays_failure_t()
                    if temp_ea not in refreshed_funcs:
                        refreshed_funcs.add(temp_ea)
                        try:
                            # 重新反编译被调用函数
                            pfunc = ida_hexrays.decompile(temp_ea, ida_hf, ida_hexrays.DECOMP_NO_CACHE)
                            if pfunc != None:
                                ptext[temp_ea] = pfunc
                        except:
                            pass

                    if ea not in refreshed_funcs:
                        refreshed_funcs.add(ea)
                        try:
                            # 重新反编译调用者函数
                            pfunc = ida_hexrays.decompile(ea, ida_hf, ida_hexrays.DECOMP_NO_CACHE) 
                            if pfunc != None:
                                ptext[ea] = pfunc
                        except:
                            return

    if ida_insn.l.t == ida_hexrays.mop_d:
        analyze_insn(module, ida_insn.l.d, ea)
    if ida_insn.r.t == ida_hexrays.mop_d:
        analyze_insn(module, ida_insn.r.d, ea)
    if ida_insn.d.t == ida_hexrays.mop_d:
        analyze_insn(module, ida_insn.d.d, ea)
    return

def lift_from_address(module: ir.Module, ea: int, typ: ir.Type = None):
    if typ is None:
        tif = lift_type_from_address(ea)
        typ = lift_tif(tif)
    return _lift_from_address(module, ea, typ) 

def _lift_from_address(module: ir.Module, ea: int, typ: ir.Type):
    if isinstance(typ, ir.FunctionType):
        func_name = ida_name.get_name(ea)
        if func_name == "":
            func_name = f"data_{hex(ea)[2:]}"
        res = module.get_global(func_name)
        res.lvars = dict() 
        if ea in ptext:
            pfunc = ptext[ea]
        else:
            return res

        # refresh function call.
        # some functions caller and signature maybe mismatch. refresh with re-decompile.
        mba = pfunc.mba
        for index in range(mba.qty):
            ida_blk = mba.get_mblock(index)
            ida_insn = ida_blk.head
            while ida_insn is not None:
                analyze_insn(module, ida_insn, ea)
                ida_insn = ida_insn.next

        if ea in ptext:
            pfunc = ptext[ea]
        else:
            return res
        
        mba = pfunc.mba
        for index in range(mba.qty):
            res.append_basic_block(name = f"@{index}")

        ida_func_details = ida_typeinf.func_type_data_t()
        tif = lift_type_from_address(ea, pfunc) 
        tif.get_func_details(ida_func_details)
        names = [] 

        builder = ir.IRBuilder(res.entry_basic_block)

        with builder.goto_entry_block():
            # declare function results as stack variable
            if not isinstance(typ.return_type, ir.VoidType):
                res.lvars["funcresult"] = builder.alloca(typ.return_type, name = "funcresult")

            for lvar in list(pfunc.lvars): 
                if lvar.is_result_var:
                    continue
                arg_t = lift_tif(lvar.tif)
                res.lvars[lvar.name] = builder.alloca(arg_t, name = lvar.name)
                if lvar.is_arg_var:
                    names.append(lvar.name)

            # if function is variadic, declare va_start intrinsic
            if tif.is_vararg_cc() and typ.var_arg:  
                ptr = builder.alloca(ir.IntType(8).as_pointer(), name = "ArgList")
                res.lvars["ArgList"] = ptr
                va_start = module.declare_intrinsic('llvm.va_start', fnty=ir.FunctionType(ir.VoidType(), [ir.IntType(8).as_pointer()]))
                ptr = builder.load(ptr)
                builder.call(va_start, (ptr, ))

            # store stack variables
            for arg, arg_n in zip(res.args, names):   
                arg = typecast(arg, res.lvars[arg_n].type.pointee, builder) 
                builder.store(arg, res.lvars[arg_n]) 

        with builder.goto_block(res.blocks[-1]):
            if isinstance(typ.return_type, ir.VoidType):
                builder.ret_void() 
            else:
                builder.ret(builder.load(res.lvars["funcresult"])) 

        # lift each bblk in cfg
        for index, blk in enumerate(res.blocks):
            ida_blk = mba.get_mblock(index)
            ida_insn = ida_blk.head
            while ida_insn is not None:
                lift_insn(ida_insn, blk, builder)
                ida_insn = ida_insn.next

            if not blk.is_terminated and index + 1 < len(res.blocks):
                with builder.goto_block(blk):
                    builder.branch(res.blocks[index + 1])

        # if function is variadic, declare va_end intrinsic
        if tif.is_vararg_cc() and typ.var_arg:
            ptr = res.lvars["ArgList"]
            va_end = module.declare_intrinsic('llvm.va_end', fnty=ir.FunctionType(ir.VoidType(), [ir.IntType(8).as_pointer()]))
            with builder.goto_block(res.blocks[-1]):
                ptr = builder.load(ptr)
                builder.call(va_end, (ptr, ))
        return res

    elif isinstance(typ, ir.IntType):
        # should probably check endianness, BOOL type is IntType(1)
        r = ida_bytes.get_bytes(ea, 1 if typ.width // 8 < 1 else typ.width // 8)
        return typ(0) if r == None else typ(int.from_bytes(r, "little"))
    elif isinstance(typ, ir.FloatType):
        r = ida_bytes.get_bytes(ea, 4)
        value = struct.unpack('f', r)
        return typ(np.float32(0)) if r == None else typ(np.float32(value[0]))
    elif isinstance(typ, ir.DoubleType):
        r = ida_bytes.get_bytes(ea, 8)
        value = struct.unpack('d', r)
        return typ(np.float64(0)) if r == None else typ(np.float64(value[0]))
    elif isinstance(typ, ir.PointerType):
        val = ir.Constant(typ, None)
        return val
    elif isinstance(typ, ir.ArrayType):
        td = llvm.create_target_data("e")
        subSize = typ.element.get_abi_size(td)
        array = [ lift_from_address(module, sub_ea, typ.element)
            for sub_ea in range(ea, ea + subSize * typ.count, subSize)
        ]
        return ir.Constant.literal_array(array)
    elif isinstance(typ, ir.LiteralStructType) or isinstance(typ, ir.IdentifiedStructType):
        td = llvm.create_target_data("e")
        structEles = []
        for el in typ.elements:
            structEle = lift_from_address(module, ea, el)
            structEles.append(structEle)
            subSize = el.get_abi_size(td)
            ea += subSize
        return ir.Constant(typ, structEles)
    else:
        raise NotImplementedError(f"object at {hex(ea)} is of unsupported type {typ}")

def str2size(str_size: str) -> int:
    """
    将表示内存大小的字符串转换为位数。

    :param str_size: 描述大小的字符串
    :type str_size: str
    :return: 字符串的大小，以位为单位
    :rtype: int
    """
    size_map = {
        "byte": 8,
        "word": 16,
        "dword": 32,
        "qword": 64
    }
    if str_size not in size_map:
        raise AssertionError(f"字符串大小必须是 {list(size_map.keys())} 之一，得到的是 '{str_size}'")
    return size_map[str_size]

def lift_intrinsic_function(module: ir.Module, func_name: str):
    """
    将IDA宏转换为LLVM内置函数。

    Hexray的反编译器在微代码层面识别高级函数。
    这些 ida_hexrays.mop_t 对象被标记为 ida_hexrays.mop_h（辅助函数成员）
    
    这改善了反编译器输出，表示无法映射到良好C代码的操作。
    （参考: https://hex-rays.com/blog/igors-tip-of-the-week-67-decompiler-helpers/）

    相关的#define宏请参考IDA SDK: `defs.h` 和 `pro.h`。

    LLVM内置函数具有公认的名称和语义，并且必须遵循某些限制。

    :param module: LLVM模块
    :type module: ir.Module
    :param func_name: 函数名称
    :type func_name: str
    :raises NotImplementedError: 不支持的函数
    :return: LLVM内置函数
    :rtype: ir.Function
    """
    # 如果已存在，直接返回
    with suppress(KeyError):
        return module.get_global(func_name)

    if func_name == "sadd_overflow":
        typ = ir.LiteralStructType((ir.IntType(64), ir.IntType(1)))
        return  module.declare_intrinsic('sadd_overflow', fnty=ir.FunctionType(typ.as_pointer(), [ir.IntType(64), ir.IntType(64)]))

    elif func_name == "__OFSUB__":
        return  module.declare_intrinsic('__OFSUB__', fnty=ir.FunctionType(ir.IntType(1), [ir.IntType(64), ir.IntType(64)]))

    elif func_name == "_mm_cvtsi128_si32":
        return  module.declare_intrinsic('_mm_cvtsi128_si32', fnty=ir.FunctionType(ir.IntType(32), [ir.IntType(128)]))

    elif func_name == "_BitScanReverse":
        return  module.declare_intrinsic('_BitScanReverse', fnty=ir.FunctionType(i8ptr, [ir.IntType(32), ir.IntType(32)]))

    elif func_name == "__FYL2X__":
        return  module.declare_intrinsic('__FYL2X__', fnty=ir.FunctionType(ir.DoubleType(), [ir.DoubleType(), ir.DoubleType()]))

    elif func_name == "__FYL2P__":
        return  module.declare_intrinsic('__FYL2P__', fnty=ir.FunctionType(ir.DoubleType(), [ir.DoubleType(), ir.DoubleType()]))
       
    elif func_name == "fabs":
        return  module.declare_intrinsic('fabs', fnty=ir.FunctionType(ir.DoubleType(), [ir.DoubleType()]))

    elif func_name == "fabsf":
        return  module.declare_intrinsic('fabsf', fnty=ir.FunctionType(ir.FloatType(), [ir.FloatType()]))

    elif func_name == "fabsl":
        return  module.declare_intrinsic('fabs', fnty=ir.FunctionType(ir.DoubleType(), [ir.DoubleType()]))

    elif func_name == "memcpy":
        return  module.declare_intrinsic('memcpy', fnty=ir.FunctionType(i8ptr, [i8ptr, i8ptr, ir.IntType(64)]))

    elif func_name == "_byteswap_ulong":
        return  module.declare_intrinsic('_byteswap_ulong', fnty=ir.FunctionType(ir.IntType(32), [ir.IntType(32)]))

    elif func_name == "_byteswap_uint64":
        return  module.declare_intrinsic('_byteswap_uint64', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(64)]))

    elif func_name == "memset":
        return  module.declare_intrinsic('memset', fnty=ir.FunctionType(i8ptr, [i8ptr, ir.IntType(32), ir.IntType(32)]))

    elif func_name == "abs64":
        return  module.declare_intrinsic('abs64', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(64)]))

    elif func_name == "__PAIR64__":
        return  module.declare_intrinsic('__PAIR64__', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(32), ir.IntType(32)]))

    elif func_name == "__PAIR128__":
        return  module.declare_intrinsic('__PAIR128__', fnty=ir.FunctionType(ir.IntType(128), [ir.IntType(64), ir.IntType(64)]))

    elif func_name == "__PAIR32__":
        return  module.declare_intrinsic('__PAIR32__', fnty=ir.FunctionType(ir.IntType(32), [ir.IntType(16), ir.IntType(16)]))

    elif func_name == "__PAIR16__":
        return  module.declare_intrinsic('__PAIR16__', fnty=ir.FunctionType(ir.IntType(16), [ir.IntType(8), ir.IntType(8)]))

    elif func_name == "_BitScanReverse64":
        return  module.declare_intrinsic('_BitScanReverse64', fnty=ir.FunctionType(i8ptr, [ir.IntType(64).as_pointer(), ir.IntType(64)]))

    elif func_name == "_BitScanForward64":
        return  module.declare_intrinsic('_BitScanForward64', fnty=ir.FunctionType(i8ptr, [ir.IntType(64).as_pointer(), ir.IntType(64)]))


    elif func_name == "__halt":
        fty = ir.FunctionType(ir.VoidType(), [])
        f = ir.Function(module, fty, "__halt")
        f.append_basic_block()
        builder = ir.IRBuilder(f.entry_basic_block)
        builder.asm(fty, "hlt", "", (), True)
        builder.ret_void()
        return f

    elif func_name == "is_mul_ok":
        is_mul_ok = module.declare_intrinsic('is_mul_ok', fnty=ir.FunctionType(ir.IntType(8), [ir.IntType(64), ir.IntType(64)]))
        return is_mul_ok

    elif func_name == "va_start":
        va_start = module.declare_intrinsic('va_start', fnty=ir.FunctionType(ir.VoidType(), [ir.IntType(8).as_pointer()]))
        return va_start

    elif func_name == "va_arg":
        va_arg = module.declare_intrinsic('va_arg', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(8).as_pointer()]))
        return va_arg

    elif func_name == "va_end":
        va_arg = module.declare_intrinsic('va_end', fnty=ir.FunctionType(ir.VoidType(), [ir.IntType(8).as_pointer()]))
        return va_arg

    elif func_name == "_QWORD":
        fQWORD = module.declare_intrinsic('IDA_QWORD', fnty=ir.FunctionType(ir.IntType(8).as_pointer(), []))
        return fQWORD

    elif func_name == "__ROL8__":
        f = module.declare_intrinsic('__ROL8__', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(64), ir.IntType(8)]))
        return f

    elif func_name == "__ROL4__":
        f = module.declare_intrinsic('__ROL4__', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(64), ir.IntType(8)]))
        return f
        
    elif func_name == "__ROR4__":
        f = module.declare_intrinsic('__ROR4__', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(64), ir.IntType(8)]))
        return f

    elif func_name == "__ROR8__":
        f = module.declare_intrinsic('__ROR8__', fnty=ir.FunctionType(ir.IntType(64), [ir.IntType(64), ir.IntType(8)]))
        return f
        
    elif func_name.startswith("__readfs"):
        _, size = func_name.split("__readfs")
        size = str2size(size)

        try:
            fs_reg = module.get_global("virtual_fs")
        except KeyError:
            fs_reg_typ = ir.ArrayType(ir.IntType(8), 65536)
            fs_reg = ir.GlobalVariable(module, fs_reg_typ, "virtual_fs")
            fs_reg.storage_class = "thread_local"
            fs_reg.initializer = fs_reg_typ(None)
        try:
            threadlocal_f = module.get_global('llvm.threadlocal.address')
        except KeyError:
            f_argty = (i8ptr, )
            fnty = ir.FunctionType(i8ptr, f_argty)
            threadlocal_f = module.declare_intrinsic('llvm.threadlocal.address', f_argty, fnty)

        fty = ir.FunctionType(ir.IntType(size), [ir.IntType(32),])

        f = ir.Function(module, fty, func_name)
        offset, = f.args
        f.append_basic_block()
        builder = ir.IRBuilder(f.entry_basic_block)
        fs_reg = typecast(fs_reg, ir.IntType(8).as_pointer(), builder)
        threadlocal_address = builder.call(threadlocal_f, (fs_reg, ))
        pointer = builder.gep(threadlocal_address, (offset,))
        pointer = typecast(pointer, ir.IntType(size).as_pointer(), builder)
        res = builder.load(pointer)
        builder.ret(res)

        return f

    elif func_name.startswith("__writefs"):
        _, size = func_name.split("__writefs")
        size = str2size(size)

        try:
            fs_reg = module.get_global("virtual_fs")
        except KeyError:
            fs_reg_typ = ir.ArrayType(ir.IntType(8), FS_SEGMENT_SIZE)
            fs_reg = ir.GlobalVariable(module, fs_reg_typ, "virtual_fs")
            fs_reg.storage_class = "thread_local"
            fs_reg.initializer = fs_reg_typ(None)            
        try:
            threadlocal_f = module.get_global('llvm.threadlocal.address')
        except KeyError:
            f_argty = (i8ptr, )
            fnty = ir.FunctionType(i8ptr, f_argty)
            threadlocal_f = module.declare_intrinsic('llvm.threadlocal.address', f_argty, fnty)

        fty = ir.FunctionType(ir.VoidType(), [ir.IntType(32), ir.IntType(size)])

        f = ir.Function(module, fty, func_name)
        offset, value  = f.args
        f.append_basic_block()
        builder = ir.IRBuilder(f.entry_basic_block)
        fs_reg = typecast(fs_reg, ir.IntType(8).as_pointer(), builder)
        threadlocal_address = builder.call(threadlocal_f, (fs_reg, ))
        pointer = builder.gep(threadlocal_address, (offset,))
        pointer = typecast(pointer, ir.IntType(size).as_pointer(), builder)
        builder.store(value, pointer)
        builder.ret_void()

        return f

    elif func_name.startswith("sys_"):
        fty = ir.FunctionType(ir.IntType(64), [], var_arg=True)
        f = ir.Function(module, fty, func_name)
        return f

    elif func_name.startswith("_InterlockedCompareExchange") or func_name.startswith("_InterlockedExchange"):
        fty = ir.FunctionType(ir.IntType(64), [], var_arg=True)
        f = ir.Function(module, fty, func_name)
        return f

    else:
        raise NotImplementedError(f"不支持的内置函数: {func_name}")  

def lift_function(module: ir.Module, func_name: str, is_declare: bool, ea = None, tif: ida_typeinf.tinfo_t = None):
    """
    根据函数名声明函数。
    如果 `is_declare` 为False，还会通过递归提升其在IDA反编译输出中的指令来定义函数。
    如果给出了 `tif`，则强制使用给定的函数类型。
    主要工作在 `lift_from_address` 中完成。

    :param module: 函数的父模块
    :type module: ir.Module
    :param func_name: 要提升的函数名
    :type func_name: str
    :param is_declare: 是否只是声明函数，不定义
    :type is_declare: bool
    :param tif: 函数类型，默认为None
    :type tif: ida_typeinf.tinfo_t, optional
    :return: 提升后的函数
    :rtype: ir.Function
    """
    if func_name == "":
        func_name = f"data_{hex(ea)[2:]}"
    with suppress(NotImplementedError):
        return lift_intrinsic_function(module, func_name)

    with suppress(KeyError):
        return module.get_global(func_name) 

    func_ea = ida_name.get_name_ea(ida_idaapi.BADADDR, func_name)
    if ida_segment.segtype(func_ea) & ida_segment.SEG_XTRN:
        is_declare = True 

    if func_ea == ida_idaapi.BADADDR:
        func_ea = ea

    assert func_ea != ida_idaapi.BADADDR
    if tif is None:
        tif = lift_type_from_address(func_ea) 

    typ = lift_tif(tif) 
    if isinstance(typ, ir.PointerType):
        print()
    res = ir.Function(module, typ, func_name)
    if is_declare:
        return res
    return lift_from_address(module, func_ea, typ) 

def calc_instsize(typ):
    """
    计算指令宽度（以位为单位）。
    """
    if isinstance(typ, ir.PointerType):
        return ptrsize
    elif isinstance(typ, ir.ArrayType):
        return -1
    elif isinstance(typ, ir.IdentifiedStructType):
        return -1
    elif isinstance(typ, ir.FloatType):
        return 32
    elif isinstance(typ, ir.DoubleType):
        return 64
    else:
        return typ.width

def lift_mop(mop: ida_hexrays.mop_t, blk: ir.Block, builder: ir.IRBuilder, dest = False, knowntyp = None) -> ir.Value:
    """
    Lifts a microcode operand (mop) to an LLVM value.
    
    Microcode operands come in many types:
    - mop_n: Immediate values (constants)
    - mop_r: Register values
    - mop_l: Local variables (stack-allocated in LLVM)
    - mop_v: Global variables/functions
    - mop_S: Stack variables
    - mop_d: Nested instructions (recursive lifting)
    - mop_f: Function call information
    - mop_a: Addresses of other operands
    - mop_h: Helper/intrinsic functions
    - mop_str: String constants
    - mop_c: Switch cases
    - mop_fn: Floating point constants
    - mop_p: Pair operations
    
    :param mop: The microcode operand to lift
    :param blk: Current LLVM basic block
    :param builder: LLVM IR builder
    :param dest: Whether this operand is a destination (true = return pointer, false = load value)
    :param knowntyp: Optional known type to cast to
    :return: Corresponding LLVM value
    """
    builder.position_at_end(blk)
    if mop.t == ida_hexrays.mop_r: # 寄存器值
        return None
    elif mop.t == ida_hexrays.mop_n: # 立即数
        res = ir.Constant(ir.IntType(mop.size * 8), mop.nnn.value)
        res.parent = blk
        return res
    elif mop.t == ida_hexrays.mop_d: # 另一个指令
        d = lift_insn(mop.d, blk, builder)
        if isinstance(d.type, ir.VoidType):
            pass
        elif mop.size == -1:
            pass
        elif isinstance(mop, ida_hexrays.mcallarg_t):
            lltype = lift_tif(mop.type)
            d = typecast(d, lltype, builder, signed=mop.type.is_signed())  
        elif knowntyp != None:
            d = typecast(d, knowntyp, builder)
        elif calc_instsize(d.type) != mop.size * 8:
            d = typecast(d, ir.IntType(mop.size * 8), builder)
        return d
    elif mop.t == ida_hexrays.mop_l: # 局部变量
        lvar = mop.l.var()
        name = "funcresult" if lvar.is_result_var else lvar.name
        off = mop.l.off
        func = blk.parent
        llvm_arg = func.lvars[name]
        llvm_arg = get_offset_to(builder, llvm_arg, off)
        if mop.size == -1:
            pass
        elif knowntyp != None:
            llvm_arg = typecast(llvm_arg, knowntyp, builder)
        elif calc_instsize(llvm_arg.type.pointee) != mop.size * 8:
            llvm_arg = typecast(llvm_arg, ir.IntType(mop.size * 8).as_pointer(), builder)
        return llvm_arg if dest else builder.load(llvm_arg)
    elif mop.t == ida_hexrays.mop_S: # 栈变量
        name = "stack"
        func = blk.parent
        if name not in func.lvars:
            with builder.goto_entry_block():                
                func.lvars[name] = builder.alloca(ir.IntType(ptrsize), name = name)
        llvm_arg = func.lvars[name]
        llvm_arg = get_offset_to(builder, llvm_arg, mop.s.off)
        if mop.size == -1:
            pass
        elif knowntyp != None:
            llvm_arg = typecast(llvm_arg, knowntyp, builder)
        elif calc_instsize(llvm_arg.type.pointee) != mop.size * 8:
            llvm_arg = typecast(llvm_arg, ir.IntType(mop.size * 8).as_pointer(), builder)
        return llvm_arg if dest else builder.load(llvm_arg) 
    elif mop.t == ida_hexrays.mop_b: # 基本块编号（用于jmp/call指令）
        return blk.parent.blocks[mop.b]
    elif mop.t == ida_hexrays.mop_v: # 全局变量
        ea = mop.g
        name = ida_name.get_name(ea)
        if name == "":
            name = f"data_{hex(ea)[2:]}"

        tif = lift_type_from_address(ea)
        if tif.is_func() or tif.is_funcptr():
            with suppress(KeyError):
                g = blk.parent.parent.get_global(name)
                return g
            if tif.is_funcptr():
                tif = tif.get_ptrarr_object()
            # if function is a thunk function, define the actual function instead
            if ((ida_funcs.get_func(ea) is not None)
            and (ida_funcs.get_func(ea).flags & ida_funcs.FUNC_THUNK)): 
                tfunc_ea, ptr = ida_funcs.calc_thunk_func_target(ida_funcs.get_func(ea))
                if tfunc_ea != ida_idaapi.BADADDR:
                    ea = tfunc_ea
                    name = ida_name.get_name(ea)
                    if name == "":
                        name = f"data_{hex(ea)[2:]}"
                    tif = lift_type_from_address(ea)
            # 如果没有函数定义，
            if ((ida_funcs.get_func(ea) is None)
            # 或者函数是库函数，
            or (ida_funcs.get_func(ea).flags & ida_funcs.FUNC_LIB) 
            # 或者函数在XTRN段中声明，
            or ida_segment.segtype(ea) & ida_segment.SEG_XTRN): 
                # 返回函数声明
                g = lift_function(blk.parent.parent, name, True, ea, tif)
            else:
                g = lift_function(blk.parent.parent, name, False, ea, tif)
            return g
                            
        else:  
            if name in blk.parent.parent.globals:
                g = blk.parent.parent.get_global(name)
            else:
                tif = lift_type_from_address(ea)
                typ = lift_tif(tif)
                g_cmt = lift_from_address(blk.parent.parent, ea, typ)
                g = ir.GlobalVariable(blk.parent.parent, g_cmt.type, name = name)
                g.initializer = g_cmt

            if isinstance(g.type.pointee, ir.IdentifiedStructType) or isinstance(g.type.pointee, ir.ArrayType):
                g = builder.gep(g, (ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)))
            if mop.size == -1:
                pass
            elif knowntyp != None:
                g = typecast(g, knowntyp, builder)
            elif calc_instsize(g.type.pointee) != mop.size * 8:
                g = typecast(g, ir.IntType(mop.size * 8).as_pointer(), builder)     
            return g if dest else builder.load(g)
    elif mop.t == ida_hexrays.mop_f: # 函数调用信息
        mcallinfo = mop.f
        f_args = []
        f_ret = []
        for i in range(mcallinfo.retregs.size()):
            mopt = mcallinfo.retregs.at(i)
            f_ret.append(lift_mop(mopt, blk, builder, dest))
        for arg in mcallinfo.args:
            typ = lift_tif(arg.type)
            f_arg = lift_mop(arg, blk, builder, dest, typ.as_pointer())

            if arg.t == ida_hexrays.mop_h and f_arg == None:
                f_arg = blk.parent.parent.declare_intrinsic(arg.helper, fnty=ir.FunctionType(typ, []))

            if arg.t == ida_hexrays.mop_r and f_arg == None:
                name = "fs"
                func = blk.parent
                if name not in func.lvars:
                    with builder.goto_entry_block():                
                        func.lvars[name] = builder.alloca(ir.IntType(16), name = name)
                llvm_arg = func.lvars[name]
                f_arg = llvm_arg if mop.size == -1 else builder.load(llvm_arg)

            f_arg = typecast(f_arg, typ, builder)
            f_args.append(f_arg)
        return f_ret, f_args
    elif mop.t == ida_hexrays.mop_a: # 操作数地址(mop_l\mop_v\mop_S\mop_r)
        mop_addr = mop.a
        val = lift_mop(mop_addr, blk, builder, True) 
        if isinstance(mop, ida_hexrays.mcallarg_t):
            lltype = lift_tif(mop.type)
            val = typecast(val, lltype, builder)
        elif isinstance(mop, ida_hexrays.mop_addr_t):
            lltype = lift_tif(mop.type)
            val = typecast(val, lltype, builder)
        elif knowntyp != None:
            val = typecast(val, knowntyp, builder)
        return val
    elif mop.t == ida_hexrays.mop_h: # 辅助函数编号
        with suppress(NotImplementedError):
            return lift_intrinsic_function(blk.parent.parent, mop.helper)
        return None
    elif mop.t == ida_hexrays.mop_str: # 字符串常量
        str_csnt = mop.cstr
        strType = ir.ArrayType(ir.IntType(8), len(str_csnt))
        g = ir.GlobalVariable(blk.parent.parent, strType, name=f"cstr_{len(blk.parent.parent.globals)}")
        g.initializer = ir.Constant(strType, bytearray(str_csnt.encode("utf-8")))
        g.linkage = "private"
        g.global_constant = True
        return typecast(g, ir.IntType(8).as_pointer(), builder)
    elif mop.t == ida_hexrays.mop_c: # switch分支和目标
        mcases = {}
        for i in range(mop.c.size()):
            dst = mop.c.targets[i]  
            if mop.c.values[i].size() == 0:
                mcases["default"] = dst 
            for j in range(mop.c.values[i].size()):
                src = mop.c.values[i][j]
                mcases[src] = dst
        return mcases
    elif mop.t == ida_hexrays.mop_fn:
        # IDA获取浮点数值在某些情况下可能会崩溃
        try:
            fp = mop.fpc.fnum.float
        except (AttributeError, ValueError) as e:
            logging.debug(f"Failed to extract float value: {e}, using default {DEFAULT_FLOAT_VALUE}")
            fp = DEFAULT_FLOAT_VALUE
        typ = float_type(mop.size)
        return ir.Constant(typ, fp)         
    elif mop.t == ida_hexrays.mop_p:
        f = lift_intrinsic_function(blk.parent.parent, f"__PAIR{mop.size*8}__")
        l = lift_mop(mop.pair.hop, blk, builder, dest)
        r = lift_mop(mop.pair.lop, blk, builder, dest)
        l = typecast(l, ir.IntType(mop.size*4), builder)
        r = typecast(r, ir.IntType(mop.size*4), builder)
        return builder.call(f, (l, r))
    elif mop.t == ida_hexrays.mop_sc:
        pass
    elif mop.t == ida_hexrays.mop_z:
        return None
    mop_descs = {ida_hexrays.mop_r: "寄存器值",
                ida_hexrays.mop_n: "立即数",
                ida_hexrays.mop_d: "另一个指令",
                ida_hexrays.mop_l: "局部变量",
                ida_hexrays.mop_S: "栈变量",
                ida_hexrays.mop_b: "基本块编号（用于jmp/call指令）",
                ida_hexrays.mop_v: "全局变量",
                ida_hexrays.mop_f: "函数调用信息",
                ida_hexrays.mop_a: r"操作数地址(mop_l\mop_v\mop_S\mop_r)",
                ida_hexrays.mop_h: "辅助函数编号",
                ida_hexrays.mop_str: "字符串常量",
                ida_hexrays.mop_c: "switch分支和目标",
                ida_hexrays.mop_fn: "浮点常量",
                ida_hexrays.mop_p: "配对操作",
                ida_hexrays.mop_sc: "分散操作信息"
    }
    raise NotImplementedError(f"未实现: {mop.dstr()} 类型 {mop_descs[mop.t]}")

def _store_as(l: ir.Value, d: ir.Value, blk: ir.Block, builder: ir.IRBuilder, d_typ: ir.Type = None, signed: bool = True):
    """
    将值存储到目标地址的私有辅助函数。
    """
    if d is None:  # 目标不存在
        return l

    d = dedereference(d)
    if d_typ:
        d = typecast(d, d_typ, builder, signed)
    assert isinstance(d.type, ir.PointerType)

    if isinstance(d.type.pointee, ir.ArrayType):
        arrtoptr = d.type.pointee.element.as_pointer()
        d = typecast(d, arrtoptr.as_pointer(), builder, signed)

    if isinstance(l.type, ir.VoidType):
        return

    with suppress(AttributeError):
        if isinstance(l.type.pointee, ir.IdentifiedStructType) or isinstance(l.type.pointee, ir.ArrayType):
            dest, src = d, l
            td = llvm.create_target_data("e")
            length = ir.Constant(ir.IntType(64), l.type.pointee.get_abi_size(td))
            memcpy = lift_intrinsic_function(blk.parent.parent, "memcpy")
            src = typecast(src, ir.IntType(8).as_pointer(), builder)
            dest = typecast(dest, ir.IntType(8).as_pointer(), builder)
            return builder.call(memcpy, (dest, src, length))
    
    if isinstance(d.type.pointee, ir.IdentifiedStructType):
        d = typecast(d, l.type.as_pointer(), builder)
    else:
        l = typecast(l, d.type.pointee, builder, signed)

    return builder.store(l, d)

def create_intrinsic_function(module: ir.Module, func_name: str, ftif):
    """
    为IDA辅助函数创建内置函数。
    """
    argtypes = []
    for arg in ftif.args:
        argtypes.append(lift_tif(arg.type))

    rettype = lift_tif(ftif.return_type)
    if isinstance(rettype, ir.VoidType):
        rettype = i8ptr
    return module.declare_intrinsic(func_name, fnty=ir.FunctionType(rettype, argtypes))

def float_type(size: int) -> ir.Type:
    """
    根据给定的大小返回适当的LLVM浮点类型。
    
    注意：llvmlite不支持long double，所以大小 > 8 的默认为double。
    
    :param size: 字节大小（4为float，8为double）
    :return: LLVM FloatType 或 DoubleType
    """
    return ir.FloatType() if size == 4 else ir.DoubleType()

# ============================================================================
# 指令提升辅助函数
# ============================================================================

def _handle_binary_arithmetic(l, r, d, op_func, blk, builder, ida_insn, allow_ptr=False):
    """
    处理二元算术运算（加、减、乘、除等）的辅助函数。
    
    :param l: 左操作数
    :param r: 右操作数
    :param d: 目标
    :param op_func: 操作函数（例如 builder.add, builder.mul）
    :param blk: 当前基本块
    :param builder: IR构建器
    :param ida_insn: IDA指令（用于获取大小信息）
    :param allow_ptr: 是否允许指针算术
    """
    # 先将浮点数转换为整数（用于整数运算）
    if isinstance(l.type, (ir.FloatType, ir.DoubleType)):
        l = builder.fptoui(l, ir.IntType(ida_insn.l.size*8))
    if isinstance(r.type, (ir.FloatType, ir.DoubleType)):
        r = builder.fptoui(r, ir.IntType(ida_insn.r.size*8))

    if allow_ptr:
        if isinstance(l.type, ir.PointerType) and isinstance(r.type, ir.IntType):
            castPtr = typecast(l, ir.IntType(8).as_pointer(), builder)
            math = builder.gep(castPtr, (r, ))
            math = typecast(math, l.type, builder)
        elif isinstance(r.type, ir.PointerType) and isinstance(l.type, ir.IntType):
            castPtr = typecast(r, ir.IntType(8).as_pointer(), builder)
            math = builder.gep(castPtr, (l, ))
            math = typecast(math, r.type, builder)
        elif isinstance(l.type, ir.IntType) and isinstance(r.type, ir.IntType):
            math = op_func(l, r)
        elif isinstance(l.type, ir.PointerType) and isinstance(r.type, ir.PointerType):
            ptrType = ir.IntType(64)
            const1 = builder.ptrtoint(l, ptrType)
            const2 = builder.ptrtoint(r, ptrType)
            math = op_func(const1, const2)
        else:
            raise NotImplementedError(f"不支持的操作数类型: {l.type} 和 {r.type}")
    else:
        l = typecast(l, ir.IntType(ida_insn.d.size*8), builder)
        r = typecast(r, ir.IntType(ida_insn.d.size*8), builder)
        math = op_func(l, r)
    
    d = storecast(l, d, builder)
    return _store_as(math, d, blk, builder)

def _handle_comparison(l, r, d, cmp_op, blk, builder, ida_insn, signed=False):
    """
    处理比较操作（setz, setnz, setg 等）的辅助函数。
    
    :param l: 左操作数
    :param r: 右操作数
    :param d: 目标
    :param cmp_op: 比较操作符 ('==', '!=', '>', '<', '>=', '<=')
    :param blk: 当前基本块
    :param builder: IR构建器
    :param ida_insn: IDA指令（用于获取大小信息）
    :param signed: 是否使用有符号比较
    """
    l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
    r = typecast(r, ir.IntType(ida_insn.r.size*8), builder)
    
    if signed:
        cond = builder.icmp_signed(cmp_op, l, r)
    else:
        cond = builder.icmp_unsigned(cmp_op, l, r)
    
    result = builder.select(cond, 
                           ir.IntType(ida_insn.d.size * 8)(1), 
                           ir.IntType(ida_insn.d.size * 8)(0))
    return _store_as(result, d, blk, builder)

def _handle_conditional_jump(l, r, d, next_blk, cmp_op, builder, ida_insn, signed=False):
    """
    处理条件跳转操作（jz, jnz, jg, jl 等）的辅助函数。
    
    :param l: 左操作数
    :param r: 右操作数
    :param d: 目标块
    :param next_blk: 顺序执行的下一个块
    :param cmp_op: 比较操作符
    :param builder: IR构建器
    :param ida_insn: IDA指令（用于获取大小信息）
    :param signed: 是否使用有符号比较
    """
    l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
    r = typecast(r, ir.IntType(ida_insn.r.size*8), builder)
    
    if signed:
        cond = builder.icmp_signed(cmp_op, l, r)
    else:
        cond = builder.icmp_unsigned(cmp_op, l, r)
    
    return builder.cbranch(cond, d, next_blk)

def _handle_float_binary_op(l, r, d, op_func, blk, builder, ida_insn):
    """
    处理浮点二元运算（fadd, fsub, fmul, fdiv）的辅助函数。
    """
    typ = float_type(ida_insn.l.size)
    l = typecast(l, typ, builder)
    r = typecast(r, typ, builder)
    math = op_func(l, r)
    d = storecast(l, d, builder)
    return _store_as(math, d, blk, builder)
 
def lift_insn(ida_insn: ida_hexrays.minsn_t, blk: ir.Block, builder: ir.IRBuilder) -> ir.Instruction:
    """
    Lifts a single IDA microcode instruction to LLVM IR.
    
    This is the main instruction translation function. It processes IDA Hexrays
    microcode instructions and emits corresponding LLVM IR instructions.
    
    Process:
    1. Lift left operand (l), right operand (r), and destination (d)
    2. Handle special cases (load operations use addresses, not values)
    3. Create unknown intrinsic functions if needed (mop_h helpers)
    4. Dispatch to appropriate handler based on opcode
    
    :param ida_insn: IDA microcode instruction to lift
    :param blk: Current LLVM basic block
    :param builder: LLVM IR builder for emitting instructions
    :return: The generated LLVM instruction, or None for no-ops
    """
    builder.position_at_end(blk)
    l = lift_mop(ida_insn.l, blk, builder)
    # 加载操作的源始终是地址
    r = lift_mop(ida_insn.r, blk, builder, ida_insn.opcode == ida_hexrays.m_ldx)
    # 指令目标始终是地址，除非call指令的目标（参数）
    d = lift_mop(ida_insn.d, blk, builder, True and ida_insn.opcode != ida_hexrays.m_call and ida_insn.opcode != ida_hexrays.m_icall)

    # 为未知的内置函数创建声明
    if ida_insn.l.t == ida_hexrays.mop_h and l == None:
        l = create_intrinsic_function(blk.parent.parent, ida_insn.l.helper, ida_insn.d.f)

    blk_itr = iter(blk.parent.blocks)
    list(itertools.takewhile(lambda x: x.name != blk.name, blk_itr))
    # 获取下一个块
    next_blk = next(blk_itr, None)

    if ida_insn.opcode == ida_hexrays.m_nop:    # 0x00,  nop    无操作
        return
    elif ida_insn.opcode == ida_hexrays.m_stx:  # 0x01,  stx  l,    {r=sel, d=off}  存储值到内存
        d = storecast(l, d, builder)
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_ldx:  # 0x02,  ldx  {l=sel,r=off}, d load 从内存加载值
        # 根据是否是FPU指令确定类型
        typ = float_type(ida_insn.d.size) if ida_insn.is_fpinsn() else ir.IntType(ida_insn.d.size * 8)
        r = typecast(r, typ.as_pointer(), builder)  
        r = builder.load(r)
        d = storecast(r, d, builder)
        return _store_as(r, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_ldc:  # 0x03,  ldc  l=const,d   加载常量
        r = ir.Constant(ir.IntType(32), ida_insn.l.nnn)
        return _store_as(r, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_mov:  # 0x04,  mov  l, d   移动
        d = storecast(l, d, builder)
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_neg:  # 0x05,  neg  l, d   取负
        l = typecast(l, ir.IntType(ida_insn.d.size*8), builder)
        l = builder.neg(l)
        d = storecast(l, d, builder)
        return _store_as(l, d, blk, builder)    
    elif ida_insn.opcode == ida_hexrays.m_lnot:  # 0x06,  lnot l, d   逻辑非
        r = ir.IntType(ida_insn.l.size*8)(0)
        r = typecast(r, l.type, builder)  
        cmp = builder.icmp_unsigned("==", l, r)
        d = storecast(cmp, d, builder)
        return _store_as(cmp, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_bnot:  # 0x07,  bnot l, d   按位非
        l = typecast(l, ir.IntType(ida_insn.d.size*8), builder)
        l = builder.not_(l)
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_xds:  # 0x08,  xds  l, d   符号扩展
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_xdu:  # 0x09,  xdu  l, d   无符号扩展
        return _store_as(l, d, blk, builder, signed=False)
    elif ida_insn.opcode == ida_hexrays.m_low:  # 0x0A,  low  l, d   取低位部分
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_high:  # 0x0B,  high l, d   取高位部分
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_add:  # 0x0C,  add  l,   r, d   l + r -> dst
        return _handle_binary_arithmetic(l, r, d, builder.add, blk, builder, ida_insn, allow_ptr=True) 
    elif ida_insn.opcode == ida_hexrays.m_sub:  # 0x0D,  sub  l,   r, d   l - r -> dst
        # 减法的特殊处理，指针减法需要取负
        if isinstance(l.type, ir.FloatType) or isinstance(l.type, ir.DoubleType):
            l = builder.fptoui(l, ir.IntType(ida_insn.l.size*8))
        if isinstance(r.type, ir.FloatType) or isinstance(r.type, ir.DoubleType):
            r = builder.fptoui(r, ir.IntType(ida_insn.r.size*8))

        if isinstance(l.type, ir.PointerType) and isinstance(r.type, ir.IntType):
            r = builder.neg(r)
            castPtr = typecast(l, ir.IntType(8).as_pointer(), builder)
            math = builder.gep(castPtr, (r, ))
            math = typecast(math, l.type, builder)
        elif isinstance(r.type, ir.PointerType) and isinstance(l.type, ir.IntType):
            l = builder.neg(l)
            castPtr = typecast(r, ir.IntType(8).as_pointer(), builder)
            math = builder.gep(castPtr, (l, ))
            math = typecast(math, r.type, builder)
        elif isinstance(l.type, ir.IntType) and isinstance(r.type, ir.IntType):
            math = builder.sub(l, r)
        elif isinstance(l.type, ir.PointerType) and isinstance(r.type, ir.PointerType):
            ptrType = ir.IntType(64)
            const1 = builder.ptrtoint(l, ptrType)
            const2 = builder.ptrtoint(r, ptrType)
            math = builder.sub(const1, const2)
        else:
            raise NotImplementedError("expected subtraction between pointer/integers")
        d = storecast(l, d, builder)
        return _store_as(math, d, blk, builder) 
    elif ida_insn.opcode == ida_hexrays.m_mul:  # 0x0E,  mul  l,   r, d   l * r -> dst
        return _handle_binary_arithmetic(l, r, d, builder.mul, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_udiv:  # 0x0F,  udiv l,   r, d   l / r -> dst
        return _handle_binary_arithmetic(l, r, d, builder.udiv, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_sdiv:  # 0x10,  sdiv l,   r, d   l / r -> dst
        return _handle_binary_arithmetic(l, r, d, builder.sdiv, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_umod:  # 0x11,  umod l,   r, d   l % r -> dst
        return _handle_binary_arithmetic(l, r, d, builder.urem, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_smod:  # 0x12,  smod l,   r, d   l % r -> dst
        return _handle_binary_arithmetic(l, r, d, builder.srem, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_or:  # 0x13,  or   l,   r, d   bitwise or
        return _handle_binary_arithmetic(l, r, d, builder.or_, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_and:  # 0x14,  and  l,   r, d   bitwise and
        return _handle_binary_arithmetic(l, r, d, builder.and_, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_xor:  # 0x15,  xor  l,   r, d   bitwise xor
        return _handle_binary_arithmetic(l, r, d, builder.xor, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_shl:  # 0x16,  shl  l,   r, d   shift logical left
        return _handle_binary_arithmetic(l, r, d, builder.shl, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_shr:  # 0x17,  shr  l,   r, d   shift logical right
        return _handle_binary_arithmetic(l, r, d, builder.ashr, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_sar:  # 0x18,  sar  l,   r, d   shift arithmetic right
        return _handle_binary_arithmetic(l, r, d, builder.ashr, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_cfadd:  # 0x19,  cfadd l,  r,    d=carry    calculate carry    bit of (l+r)
        l = typecast(l, ir.IntType(64), builder)
        r = typecast(r, ir.IntType(64), builder)
        math = builder.call(lift_intrinsic_function(blk.parent.parent, "sadd_overflow"), [l, r])
        math = builder.gep(math, (ir.IntType(32)(0), ir.IntType(32)(0), ))
        math = builder.load(math)
        d = storecast(l, d, builder)
        return _store_as(math, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_ofadd:  # 0x1A,  ofadd l,  r,    d=overf    calculate overflow bit of (l+r)
        l = typecast(l, ir.IntType(64), builder)
        r = typecast(r, ir.IntType(64), builder)
        math = builder.call(lift_intrinsic_function(blk.parent.parent, "sadd_overflow"), [l, r])
        math = builder.gep(math, (ir.IntType(32)(0), ir.IntType(32)(1),))
        math = builder.load(math)
        d = storecast(l, d, builder)
        return _store_as(math, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_cfshl:  # 0x1B,  cfshl l,  r,    d=carry    calculate carry    bit of (l<<r)
        l = typecast(l, ir.IntType(64), builder)
        r = typecast(r, ir.IntType(64), builder)
        func_name = f"m_cfshr_{ida_insn.d.size}"
        if func_name in blk.parent.parent.globals:
            f_func = blk.parent.parent.get_global(func_name)
        else:
            f_func = blk.parent.parent.declare_intrinsic(func_name, fnty=ir.FunctionType(ir.DoubleType(), [ir.IntType(64), ir.IntType(64)]))
        l = builder.call(f_func, [l, r])
        d = storecast(l, d, builder)
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_cfshr:  # 0x1C,  cfshr l,  r,    d=carry    calculate carry    bit of (l>>r)
        l = typecast(l, ir.IntType(64), builder)
        r = typecast(r, ir.IntType(64), builder)
        func_name = f"m_cfshr_{ida_insn.d.size}"
        if func_name in blk.parent.parent.globals:
            f_func = blk.parent.parent.get_global(func_name)
        else:
            f_func = blk.parent.parent.declare_intrinsic(func_name, fnty=ir.FunctionType(ir.DoubleType(), [ir.IntType(64), ir.IntType(64)]))
        l = builder.call(f_func, [l, r])
        d = storecast(l, d, builder)
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_sets:  # 0x1D,  sets  l,d=byte  SF=1Sign
        l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
        r = ir.Constant(ir.IntType(ida_insn.l.size*8), 0)
        cond = builder.icmp_unsigned("<", l, r)
        result = builder.select(cond, ir.IntType(ida_insn.d.size * 8)(1), ir.IntType(ida_insn.d.size * 8)(0))
        return _store_as(result, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_seto:  # 0x1E,  seto  l,  r, d=byte  OF=1Overflow of (l-r)
        l = typecast(l, ir.IntType(64), builder)
        r = typecast(r, ir.IntType(64), builder) 
        math = builder.call(lift_intrinsic_function(blk.parent.parent, "__OFSUB__"), [l, r])
        return _store_as(math, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_setp:  # 0x1F,  setp  l,  r, d=byte  PF=1Unordered/Parity  *F
        func_name = f"setp_{ida_insn.l.size}_{ida_insn.d.size}"
        if func_name in blk.parent.parent.globals:
            f_setp = blk.parent.parent.get_global(func_name)
        else:
            f_setp = blk.parent.parent.declare_intrinsic(func_name, fnty=ir.FunctionType(ir.IntType(ida_insn.d.size*8), [ir.IntType(ida_insn.l.size*8), ir.IntType(32)]))
        l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
        l = builder.call(f_setp, [l, ir.Constant(ir.IntType(32), ida_insn.d.size)])
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_setnz:  # 0x20,  setnz l,  r, d=byte  ZF=0Not Equal    *F
        return _handle_comparison(l, r, d, "!=", blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_setz:  # 0x21,  setz  l,  r, d=byte  ZF=1Equal   *F
        return _handle_comparison(l, r, d, "==", blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_setae:  # 0x22,  setae l,  r, d=byte  CF=0Above or Equal    *F
        return _handle_comparison(l, r, d, ">=", blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_setb:  # 0x23,  setb  l,  r, d=byte  CF=1Below   *F
        return _handle_comparison(l, r, d, "<", blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_seta:  # 0x24,  seta  l,  r, d=byte  CF=0 & ZF=0   Above   *F
        return _handle_comparison(l, r, d, ">", blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_setbe:  # 0x25,  setbe l,  r, d=byte  CF=1 | ZF=1   Below or Equal    *F
        return _handle_comparison(l, r, d, "<=", blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_setg:  # 0x26,  setg  l,  r, d=byte  SF=OF & ZF=0  Greater
        return _handle_comparison(l, r, d, ">", blk, builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_setge:  # 0x27,  setge l,  r, d=byte  SF=OF    Greater or Equal
        return _handle_comparison(l, r, d, ">=", blk, builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_setl:  # 0x28,  setl  l,  r, d=byte  SF!=OF   Less
        return _handle_comparison(l, r, d, "<", blk, builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_setle:  # 0x29,  setle l,  r, d=byte  SF!=OF | ZF=1 Less or Equal
        return _handle_comparison(l, r, d, "<=", blk, builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_jcnd:  # 0x2A,  jcnd   l,    d   d is mop_v or mop_b
        l = typecast(l, ir.IntType(1), builder)
        return builder.cbranch(l, d, next_blk)
    elif ida_insn.opcode == ida_hexrays.m_jnz:  # 0x2B,  jnz    l, r, d   ZF=0Not Equal *F
        return _handle_conditional_jump(l, r, d, next_blk, "!=", builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_jz:  # 0x2C,  jzl, r, d   ZF=1Equal*F
        return _handle_conditional_jump(l, r, d, next_blk, "==", builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_jae:  # 0x2D,  jae    l, r, d   CF=0Above or Equal *F
        return _handle_conditional_jump(l, r, d, next_blk, ">=", builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_jb:  # 0x2E,  jbl, r, d   CF=1Below*F
        return _handle_conditional_jump(l, r, d, next_blk, "<", builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_ja:  # 0x2F,  jal, r, d   CF=0 & ZF=0   Above*F
        return _handle_conditional_jump(l, r, d, next_blk, ">", builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_jbe:  # 0x30,  jbe    l, r, d   CF=1 | ZF=1   Below or Equal *F
        return _handle_conditional_jump(l, r, d, next_blk, "<=", builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_jg:  # 0x31,  jgl, r, d   SF=OF & ZF=0  Greater
        return _handle_conditional_jump(l, r, d, next_blk, ">", builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_jge:  # 0x32,  jge    l, r, d   SF=OF    Greater or Equal
        return _handle_conditional_jump(l, r, d, next_blk, ">=", builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_jl:  # 0x33,  jll, r, d   SF!=OF   Less
        return _handle_conditional_jump(l, r, d, next_blk, "<", builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_jle:  # 0x34,  jle    l, r, d   SF!=OF | ZF=1 Less or Equal
        return _handle_conditional_jump(l, r, d, next_blk, "<=", builder, ida_insn, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_jtbl:  # 0x35,  jtbl   l, r=mcases    Table jump
        l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
        if "default" in r:
            switch = builder.switch(l, blk.parent.basic_blocks[r["default"]])
        else:
            switch = builder.switch(l, blk.parent.basic_blocks[r[list(r.keys())[0]]])
        for value in r.keys():
            if isinstance(value, int):
                switch.add_case(value, blk.parent.basic_blocks[r[value]])
        return switch
    elif ida_insn.opcode == ida_hexrays.m_ijmp:  # 0x36,  ijmp  {r=sel, d=off}  indirect unconditional jump
        return
    elif ida_insn.opcode == ida_hexrays.m_goto:  # 0x37,  goto   l    l是mop_v或mop_b
        return builder.branch(l)
    elif ida_insn.opcode == ida_hexrays.m_call:  # 0x38,  call   ld   l是mop_v或mop_b或mop_h
        rets, args = d
        if not isinstance(l.type, ir.PointerType) or not isinstance(l.type.pointee, ir.FunctionType):
            argtype = []
            for (i, arg) in enumerate(args):
                argtype.append(arg.type)

            new_func_type = ir.FunctionType(i8ptr, argtype, var_arg=False).as_pointer()
            l = typecast(l, new_func_type, builder)

            ret = builder.call(l, args)
            for dst in rets:
                _store_as(ret, dst, blk, builder) 
            return ret

        for (i, llvmtype) in enumerate(l.type.pointee.args):
            if i >= len(args):
                args.append(ir.Constant(ir.IntType(32), 1))
            if args[i].type != llvmtype:
                args[i] = typecast(args[i], llvmtype, builder)
        
        args = args[:len(l.type.pointee.args)]
        
        if l.type.pointee.var_arg: # 函数是可变参数
            ltype = l.type.pointee
            newargs = list(ltype.args)
            for i in range(len(newargs), len(args)):
                newargs.append(args[i].type)
            new_func_type = ir.FunctionType(ltype.return_type, newargs, var_arg=True).as_pointer()
            l = typecast(l, new_func_type, builder)
        ret = builder.call(l, args)
        for dst in rets:
            _store_as(ret, dst, blk, builder) 
        return ret
    elif ida_insn.opcode == ida_hexrays.m_icall:  # 0x39,  icall  {l=sel, r=off} d    间接调用
        rets, args = d
        ftype = ir.FunctionType(ir.IntType(8).as_pointer(), (arg.type for arg in args))
        f = typecast(r, ftype.as_pointer(), builder)
        return builder.call(f, args)
    elif ida_insn.opcode == ida_hexrays.m_ret:  # 0x3A,  ret  返回
        return
    elif ida_insn.opcode == ida_hexrays.m_push:  # 0x3B,  push   l  入栈
        return
    elif ida_insn.opcode == ida_hexrays.m_pop:  # 0x3C,  popd  出栈
        return
    elif ida_insn.opcode == ida_hexrays.m_und:  # 0x3D,  undd   未定义
        return
    elif ida_insn.opcode == ida_hexrays.m_ext:  # 0x3E,  ext  in1, in2,  out1  外部指令，不是微代码 *F
        return
    elif ida_insn.opcode == ida_hexrays.m_f2i:  # 0x3F,  f2il,    d int(l) => d; 浮点 -> 整数   +F
        return typecast(l, ir.IntType(ida_insn.d.size * 8), builder, signed=True)
    elif ida_insn.opcode == ida_hexrays.m_f2u:  # 0x40,  f2ul,    d uint(l)=> d; 浮点 -> 无符号整数  +F
        return typecast(l, ir.IntType(ida_insn.d.size * 8), builder, signed=False)
    elif ida_insn.opcode == ida_hexrays.m_i2f:  # 0x41,  i2fl,    d fp(l)  => d; 整数 -> 浮点 +F
        l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
        typ = float_type(ida_insn.d.size)
        return builder.sitofp(l, typ)
    elif ida_insn.opcode == ida_hexrays.m_u2f:  # 0x42,  i2fl,    d fp(l)  => d; 无符号整数 -> 浮点  +F
        l = typecast(l, ir.IntType(ida_insn.l.size*8), builder)
        typ = float_type(ida_insn.d.size)
        return builder.uitofp(l, typ)
    elif ida_insn.opcode == ida_hexrays.m_f2f:  # 0x43,  f2fl,    d l => d; 改变浮点精度+F
        target_type = float_type(ida_insn.d.size)
        l = typecast(l, target_type, builder)
        if d != None and d.type != target_type.as_pointer():
            d = typecast(d, target_type.as_pointer(), builder)
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_fneg:  # 0x44,  fneg    l,    d -l=> d; 改变符号   +F
        return _store_as(l, d, blk, builder)
    elif ida_insn.opcode == ida_hexrays.m_fadd:  # 0x45,  fadd    l, r, d l + r  => d; 浮点加法 +F
        return _handle_float_binary_op(l, r, d, builder.fadd, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_fsub:  # 0x46,  fsub    l, r, d l - r  => d; 浮点减法 +F
        return _handle_float_binary_op(l, r, d, builder.fsub, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_fmul:  # 0x47,  fmul    l, r, d l * r  => d; 浮点乘法 +F
        return _handle_float_binary_op(l, r, d, builder.fmul, blk, builder, ida_insn)
    elif ida_insn.opcode == ida_hexrays.m_fdiv:  # 0x48,  fdiv    l, r, d l / r  => d; 浮点除法   +F
        return _handle_float_binary_op(l, r, d, builder.fdiv, blk, builder, ida_insn)
    else:
        raise NotImplementedError(f"未实现 {ida_insn.dstr()}")

class BIN2LLVMController():
    """
    IDA到LLVM IR翻译过程的主控制器。
    
    该类统筹完整的二进制到LLVM的提升工作流程：
    1. 通过反编译所有函数并收集元数据来初始化
    2. 为所有数据项创建LLVM全局变量
    3. 将.text段函数提升为LLVM IR
    4. 将生成的IR模块保存到文件
    """
    def __init__(self, target_mode: str = "host"):
        """使用空的LLVM模块初始化控制器。"""
        self.m = ir.Module()
        self._name_cache = {}
        self._func_cache = {}
        if target_mode == "host":
            self._set_module_target_from_host()
        else:
            self._set_module_target_from_ida()

    def _get_name(self, ea):
        name = self._name_cache.get(ea)
        if name is None:
            name = ida_name.get_name(ea)
            self._name_cache[ea] = name
        return name

    def _get_func(self, ea):
        func = self._func_cache.get(ea, "__missing__")
        if func == "__missing__":
            func = ida_funcs.get_func(ea)
            self._func_cache[ea] = func
        return func

    def _set_module_target_from_host(self):
        """Sets module target triple and data layout based on host LLVM."""
        try:
            llvm.initialize()
            llvm.initialize_native_target()
            llvm.initialize_native_asmprinter()
            triple = llvm.get_default_triple()
            target = llvm.Target.from_triple(triple)
            target_machine = target.create_target_machine()
            self.m.triple = triple
            self.m.data_layout = str(target_machine.target_data)
        except Exception as exc:
            logging.warning(f"Failed to set module target from host: {exc}")

    def _set_module_target_from_ida(self):
        """Sets module target triple based on IDA's analysis information."""
        try:
            proc = ida_ida.inf_get_procname()
            is_64 = ida_ida.inf_is_64bit()
            arch = "unknown"

            if proc == "metapc":
                arch = "x86_64" if is_64 else "i386"
            elif proc in ("arm", "ARM"):
                arch = "aarch64" if is_64 else "arm"
            elif proc in ("aarch64", "arm64"):
                arch = "aarch64"
            elif proc == "mips":
                arch = "mips64" if is_64 else "mips"
            elif proc in ("ppc", "ppc64"):
                arch = "powerpc64" if is_64 else "powerpc"
            elif proc == "riscv":
                arch = "riscv64" if is_64 else "riscv32"

            os_name = "unknown"
            with suppress(Exception):
                ostype = ida_ida.inf_get_ostype()
                if hasattr(ida_ida, "OSTYPE_WIN") and ostype == ida_ida.OSTYPE_WIN:
                    os_name = "windows"
                elif hasattr(ida_ida, "OSTYPE_LINUX") and ostype == ida_ida.OSTYPE_LINUX:
                    os_name = "linux"
                elif hasattr(ida_ida, "OSTYPE_MACOS") and ostype == ida_ida.OSTYPE_MACOS:
                    os_name = "darwin"

            self.m.triple = f"{arch}-unknown-{os_name}"
            self.m.data_layout = ""
        except Exception as exc:
            logging.warning(f"Failed to set module target from IDA: {exc}")

    def insertAllFunctions(self):
        """
        将.text段的所有函数提升为LLVM IR。
        
        遍历二进制文件中的所有函数，并将.text段中的函数
        翻译为LLVM IR表示。
        """
        for f_ea in idautils.Functions():
            self.insertFunctionAtEa(f_ea)

    def insertFunctionAtEa(self, ea):
        """
        将给定地址的特定函数提升为LLVM IR。
        
        :param ea: 要提升的函数的有效地址
        """
        if ea in ptext:
            typ = ptext[ea].type
            func_name = self._get_name(ea)
            lift_function(self.m, func_name, False, ea, typ)

    def create_global(self, ea, width, str_dict):
        """
        Creates LLVM global variables for IDA data items.
        
        Process:
        1. Extract data item name and type information from IDA
        2. Handle special cases:
           - Strings: Create constant string globals
           - External functions: Create declarations
           - Thunk functions: Resolve to actual target
           - Data items: Create initialized global variables
        
        :param ea: Address of the data item
        :param width: Size of the data item in bytes
        :param str_dict: Dictionary mapping addresses to string data
        """
        # 获取数据项名称和类型信息
        name = self._get_name(ea)
        if name == "":
            name = f"data_{hex(ea)[2:]}"

        # 如果数据项是字符串，创建字符串全局变量
        if ea in str_dict:
            str_csnt = str_dict[ea][0]
            strType = ir.ArrayType(ir.IntType(8), str_dict[ea][1])
            g = ir.GlobalVariable(self.m, strType, name=name)
            g.initializer = ir.Constant(strType, bytearray(str_csnt))
            g.linkage = "private"
            g.global_constant = True
            return

        tif = ida_typeinf.tinfo_t()
        if not ida_nalt.get_tinfo(tif, ea):
            ida_typeinf.guess_tinfo(tif, ea)

        # 如果数据项是外部函数，创建声明
        elif tif.is_func() or tif.is_funcptr():
            if tif.is_funcptr():
                tif = tif.get_ptrarr_object()
            # if function is a thunk function, define the actual function instead
            func = self._get_func(ea)
            if ((func is not None)
            and (func.flags & ida_funcs.FUNC_THUNK)): 
                tfunc_ea, ptr = ida_funcs.calc_thunk_func_target(func)
                if tfunc_ea != ida_idaapi.BADADDR:
                    ea = tfunc_ea
                    name = self._get_name(ea)
                    func = self._get_func(ea)
            
            # 为声明函数创建定义，
            if ((func is None)
            # 或者函数是库函数，
            or (func.flags & ida_funcs.FUNC_LIB) 
            # 或者函数在XTRN段中声明，
            or ida_segment.segtype(ea) & ida_segment.SEG_XTRN): 
                # 返回函数声明
                g = lift_function(self.m, name, True, ea, tif)

        # 其他数据项，可能是 int/float/数组/结构体
        else:
            typ = lift_tif(tif, width)
            g_cmt = lift_from_address(self.m, ea, typ)
            g = ir.GlobalVariable(self.m, typ, name = name)
            g.initializer = g_cmt

    def initialize(self):
        """
        Initializes the LLVM module by preparing all necessary metadata.
        
        This crucial preparation step:
        1. Decompiles all functions in the binary using IDA Hexrays
        2. Collects all string constants identified by IDA
        3. Creates LLVM global variables for all data items in non-executable segments
        
        The decompiled functions are cached in the global 'ptext' dictionary
        for later use during function lifting.
        
        Note: Decompilation may fail for some functions (e.g., library stubs,
        corrupted code), which are silently skipped.
        """
        # 步骤1：反编译所有函数并缓存结果
        for func in idautils.Functions():
            try:
                pfunc = ida_hexrays.decompile(func)
                if pfunc != None:
                    ptext[func] = pfunc
            except Exception as e:
                # 反编译可能因各种原因失败；跳过并继续
                logging.debug(f"在 {hex(func)} 处反编译函数失败: {e}")
                pass

        # 步骤2：收集所有字符串常量
        str_dict = {}
        for s in idautils.Strings():
            str_dict[s.ea] = [ida_bytes.get_bytes(s.ea, s.length), s.length]

        # 步骤3：为非执行段中的所有数据项创建全局变量
        for i in range(idaapi.get_segm_qty()):
            segm = idaapi.getnseg(i)
            if segm is None:
                continue
            if segm.perm & idaapi.SEGPERM_EXEC:
                continue
            for head in idautils.Heads(segm.start_ea, segm.end_ea):
                end = ida_bytes.get_item_end(head)
                if end <= head:
                    continue
                self.create_global(head, end - head, str_dict)

    def save_to_file(self, filename):
        """
        将LLVM IR模块以文本格式保存到文件。
        
        输出的是人类可读的LLVM IR（.ll格式），可以：
        - 使用clang/llc编译
        - 使用opt优化
        - 使用各种LLVM工具分析
        
        :param filename: 输出.ll文件的路径
        """
        with open(filename, 'w') as f:
            f.write(str(self.m))

app = typer.Typer(
    add_completion=False,
    help="IDA2LLVM - Convert binary to LLVM IR using IDA Pro 9+ idalib",
)


@app.command()
def main(
    file: str = typer.Option(
        ..., "-f", "--file", help="Binary file to be analyzed"
    ),
    output: str = typer.Option(
        ..., "-o", "--output", help="Output file for LLVM IR (.ll)"
    ),
    verbose: bool = typer.Option(
        False, "-v", "--verbose", help="Enable verbose logging"
    ),
    target: str = typer.Option(
        "host", "--target", help="Target triple source: host (default) or ida"
    ),
):
    """
    作为独立应用程序运行（使用 IDA Pro 9+ idalib）。
    """
    if target not in ("host", "ida"):
        raise typer.BadParameter("must be one of: host, ida")

    if verbose:
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig(level=logging.INFO)

    try:
        idapro.open_database(file, True)
        ida_auto.auto_wait()
        bin2llvm = BIN2LLVMController(target_mode=target)
        bin2llvm.initialize()
        bin2llvm.insertAllFunctions()
        bin2llvm.save_to_file(output)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback

        traceback.print_exc()
        sys.exit(1)
    finally:
        idapro.close_database()


if __name__ == "__main__":
    app()

