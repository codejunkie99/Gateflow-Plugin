---
name: SystemVerilog Language
description: This skill provides comprehensive SystemVerilog language knowledge for RTL design, verification, and synthesis. Triggers on: "SystemVerilog syntax", "how do I write", "coding pattern", "best practice for SV", "HDL code help", "always_ff vs always_comb", "data types in SV", "FSM pattern", "reset handling", "naming convention", "module", "wire", "logic", "reg".
version: 1.0.0
---

# SystemVerilog Language Skill

Apply this knowledge when helping users with SystemVerilog code.

## Language Fundamentals

### Data Types
- `logic` - 4-state type (0, 1, X, Z), preferred over reg/wire
- `bit` - 2-state type (0, 1), faster simulation
- `int`, `integer` - 32-bit signed integers
- `real` - floating point (simulation only)
- `string` - text strings (not synthesizable)

### Declarations
```systemverilog
logic [7:0] byte_data;           // 8-bit signal
logic [WIDTH-1:0] param_width;   // parameterized width
logic signed [15:0] signed_val;  // signed arithmetic
logic [3:0][7:0] packed_array;   // packed 2D array
logic unpacked [0:3];            // unpacked array
```

### Always Blocks
```systemverilog
// Sequential logic - use always_ff
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        q <= '0;
    else
        q <= d;
end

// Combinational logic - use always_comb
always_comb begin
    case (sel)
        2'b00: y = a;
        2'b01: y = b;
        2'b10: y = c;
        default: y = d;
    endcase
end

// Latches - use always_latch (avoid if possible)
always_latch begin
    if (enable)
        q = d;
end
```

## Coding Best Practices

### Naming Conventions
- Signals: `snake_case` (data_valid, read_enable)
- Parameters: `UPPER_CASE` (DATA_WIDTH, ADDR_SIZE)
- Modules: `snake_case` (uart_receiver, fifo_sync)
- Prefixes: `i_` input, `o_` output, `r_` register, `w_` wire

### Reset Handling
```systemverilog
// Asynchronous reset (preferred for FPGA)
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= IDLE;
    end else begin
        state <= next_state;
    end
end

// Synchronous reset
always_ff @(posedge clk) begin
    if (rst) begin
        count <= '0;
    end else begin
        count <= count + 1;
    end
end
```

### FSM Patterns
```systemverilog
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    ACTIVE = 2'b01,
    DONE   = 2'b10
} state_t;

state_t state, next_state;

// State register
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= next_state;
end

// Next state logic
always_comb begin
    next_state = state;
    case (state)
        IDLE:   if (start) next_state = ACTIVE;
        ACTIVE: if (done)  next_state = DONE;
        DONE:   next_state = IDLE;
        default: next_state = IDLE;
    endcase
end
```

## Common Lint Errors

| Error | Cause | Fix |
|-------|-------|-----|
| UNUSED | Signal declared but not used | Remove or use `/* verilator lint_off UNUSED */` |
| UNDRIVEN | Signal read but never assigned | Assign a value or remove |
| WIDTH | Bit width mismatch | Match widths or use explicit cast |
| CASEINCOMPLETE | Case without default | Add `default:` clause |
| BLKSEQ | Blocking in sequential block | Use `<=` instead of `=` |

## Synthesis Considerations

### Synthesizable Constructs
- `always_ff`, `always_comb`, `assign`
- `if/else`, `case/casez/casex`
- Arithmetic operators (+, -, *, /)
- Logical operators (&&, ||, !)
- Bitwise operators (&, |, ^, ~)

### Non-Synthesizable (Testbench Only)
- `initial` blocks
- `#` delays
- `$display`, `$monitor`, `$finish`
- `fork/join`
- Dynamic arrays, queues, associative arrays
