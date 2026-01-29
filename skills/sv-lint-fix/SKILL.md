---
name: SystemVerilog Lint Fixing
description: This skill provides patterns for fixing common Verilator lint errors and warnings. Triggers on: "lint error", "lint warning", "UNUSED signal", "UNDRIVEN", "WIDTH mismatch", "CASEINCOMPLETE", "BLKSEQ", "LATCH inferred", "MULTIDRIVEN", "verilator error", "fix compilation error", "suppress warning".
version: 1.0.0
---

# SystemVerilog Lint Fixing Skill

Apply these patterns to fix Verilator lint errors efficiently.

## Lint Fix Patterns

### UNUSED - Unused Signal

**Error**: `Signal is not used: 'foo'`

**Fixes**:
1. Remove the unused signal if truly not needed
2. Add pragma to suppress if intentional:
   ```systemverilog
   /* verilator lint_off UNUSED */
   logic unused_but_needed;
   /* verilator lint_on UNUSED */
   ```
3. Use in a dummy assignment: `assign _unused = foo;`

### UNDRIVEN - Undriven Signal

**Error**: `Signal is not driven: 'bar'`

**Fixes**:
1. Assign a value in appropriate always block
2. Initialize in declaration: `logic bar = 0;`
3. Connect to an input or constant

### WIDTH - Width Mismatch

**Error**: `Operator WIDTH expects X bits but assignment has Y bits`

**Fixes**:
```systemverilog
// Truncation (wider to narrower)
logic [7:0] narrow = wide[7:0];

// Extension (narrower to wider)
logic [15:0] wide = {8'b0, narrow};  // zero extend
logic signed [15:0] wide_s = $signed(narrow);  // sign extend

// Explicit cast
logic [7:0] result = 8'(some_expression);
```

### CASEINCOMPLETE - Missing Case Items

**Error**: `Case values incompletely covered`

**Fixes**:
```systemverilog
case (sel)
    2'b00: out = a;
    2'b01: out = b;
    2'b10: out = c;
    2'b11: out = d;  // Add missing case
endcase

// Or use default
case (sel)
    2'b00: out = a;
    2'b01: out = b;
    default: out = '0;  // Catch-all
endcase
```

### BLKSEQ - Blocking in Sequential

**Error**: `Blocking assignment in sequential logic`

**Fix**: Change `=` to `<=` in `always_ff`:
```systemverilog
// Wrong
always_ff @(posedge clk) begin
    q = d;  // Blocking - BAD
end

// Correct
always_ff @(posedge clk) begin
    q <= d;  // Non-blocking - GOOD
end
```

### LATCH - Inferred Latch

**Error**: `Latch inferred for signal 'foo'`

**Fix**: Ensure all paths assign a value:
```systemverilog
// Wrong - latch inferred
always_comb begin
    if (enable)
        out = in;
    // Missing else!
end

// Correct
always_comb begin
    if (enable)
        out = in;
    else
        out = '0;  // Default value
end
```

### MULTIDRIVEN - Multiple Drivers

**Error**: `Signal has multiple drivers`

**Fix**: Ensure only one always block or assign drives each signal
```systemverilog
// Wrong
always_comb out = a;
always_comb out = b;  // Multiple drivers!

// Correct
always_comb out = sel ? a : b;  // Single driver
```

## Iterative Fix Loop

1. Run lint: `verilator --lint-only -Wall file.sv`
2. Fix highest-priority error first
3. Re-run lint
4. Repeat until clean

## Suppressing Warnings

When warnings are intentional:
```systemverilog
/* verilator lint_off UNUSED */
/* verilator lint_off UNDRIVEN */
// Code with intentional unused/undriven signals
/* verilator lint_on UNDRIVEN */
/* verilator lint_on UNUSED */
```

Or file-wide in a separate file:
```
// verilator.vlt
lint_off -rule UNUSED -file "*/legacy_code.sv"
```
