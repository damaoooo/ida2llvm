<h1 align="center">IDA2LLVM: Lifting IDA Microcode into LLVM IR</h1>

<h4 align="center">
<p>
<a href=#about>About</a> |
<a href=#quickstart>QuickStart</a> |
<a href=#whats-new>What's New</a> |
<a href=#acknowledge>Acknowledge</a> |
<p>
</h4>

## About
Lifting microcode (IDA IR) into LLVM IR. The script has been test in BinaryCorp small test datasets (1584 binaries). The code now is in debug version, we will improve the shitty code later.

## What's New

### IDA Pro 9+ Support (idalib)
This version has been migrated to use **IDA Pro 9.0+** with the new **idalib** (IDA as a library) feature, allowing you to run as a **standalone application** without the IDA GUI.

**Key Changes:**
- ✅ Uses `idapro` module and idalib API
- ✅ Runs as standalone Python script (no IDA GUI required)
- ✅ Migrated from deprecated APIs:
  - `ida_idaapi.get_inf_structure().is_64bit()` → `ida_ida.inf_is_64bit()`
  - Fixed invalid escape sequences for Python 3.x compatibility
  - Added validation for invalid type sizes from IDA

**Migration to IDA Pro 9.0:**
- Removed dependency on `ida_struct` and `ida_enum` modules (superseded by `ida_typeinf`)
- All type operations now use modern `ida_typeinf` APIs

## QuickStart

### For IDA Pro 9.0+ (Recommended - New Method)

#### Prerequisites
1. Install IDA Pro 9.0 or newer
2. Install and configure the `idapro` package:
   ```bash
   # Navigate to IDA installation's idalib/python folder
   cd /path/to/IDA/idalib/python
   pip install .
   
   # Run the activation script
   python /path/to/IDA/py-activate-idalib.py
   ```

3. Install dependencies:
   ```bash
   pip install llvmlite numpy
   ```

#### Usage
Run as a standalone application:
```bash
python ida2llvm.py -f <binary_file> -o <output.ll>

# Examples:
python ida2llvm.py -f ./examples/cp -o ./cp_output.ll
python ida2llvm.py -f ./examples/ls -o ./ls_output.ll -v  # with verbose logging
```

**Options:**
- `-f, --file`: Binary file to analyze (required)
- `-o, --output`: Output LLVM IR file path (required)
- `-v, --verbose`: Enable verbose logging (optional)

### For IDA Pro 8.3 (Legacy Method)
```bash
idat64 -c -A -S"ida2llvm.py [binary].ll" binary
```

### Requirements
- **IDA Pro 9.0+** (for idalib mode) or **IDA Pro 8.3** (for legacy mode)
- Python 3.x
- llvmlite
- numpy

```bash
pip install llvmlite numpy
```

## Acknowledge
- [ida2llvm](https://github.com/loyaltypollution/ida2llvm): The codebase we built on, we fixing most of the bugs (float, unsupport inst, unsupport typecast and structure) and transforming it from an experimental toy to a stable tool.