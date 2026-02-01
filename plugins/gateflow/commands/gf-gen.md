---
name: gf-gen
description: Generate scaffolds
argument-hint: "<type> <name> [options]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
---

# GateFlow Generate Command

Generate SystemVerilog code artifacts: modules, testbenches, or packages.

## Instructions

Parse the arguments to determine generation type:
- `gf-gen module <name>` - Generate a new module
- `gf-gen testbench <name>` - Generate a testbench for a module
- `gf-gen package <name>` - Generate a package

### Module Generation

Create a synthesizable module with:
- Standard header comment with filename and description
- Parameter declarations (if needed)
- Port list with proper directions and types
- Internal signal declarations
- Basic combinational/sequential logic structure
- Proper `always_ff` and `always_comb` blocks

### Testbench Generation

Create a testbench that:
- Instantiates the DUT (Device Under Test)
- Generates clock and reset signals
- Includes initial block with `$dumpfile` and `$dumpvars`
- Has placeholder for test stimulus
- Uses `$finish` to end simulation
- Follows UVM-lite or simple directed test style

### Package Generation

Create a package with:
- Type definitions (enums, structs)
- Parameter constants
- Function declarations
- Proper export statements

## Output

Write the generated file to `<name>.sv` or `<name>_tb.sv` for testbenches.
