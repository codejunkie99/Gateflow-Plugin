## DFT & Testability Planning

### DFT Strategy

```markdown
## DFT Plan

### Test Methods
| Method | Coverage | Overhead | Usage |
|--------|----------|----------|-------|
| Scan chain | Stuck-at faults | 5-15% area | Production test |
| BIST | Logic self-test | 10-20% area | Field test |
| Memory BIST | Memory defects | 3-5% area | Memory test |
| JTAG | Debug/boundary | Minimal | Debug access |

### Scan Planning
| Block | Scan Chains | Length | Clock |
|-------|-------------|--------|-------|
| CPU | 4 | ~2500 | clk_cpu |
| DMA | 2 | ~800 | clk_sys |
| Total | 6 | - | - |
```

### Scan Chain Wrapper
```systemverilog
module scan_ff (
    input  logic clk,
    input  logic rst_n,
    input  logic scan_en,
    input  logic scan_in,
    input  logic d,
    output logic q,
    output logic scan_out
);
    logic mux_out;

    assign mux_out = scan_en ? scan_in : d;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= 1'b0;
        else        q <= mux_out;
    end

    assign scan_out = q;
endmodule
```

### JTAG TAP Controller
```systemverilog
module jtag_tap (
    input  logic tck,
    input  logic trst_n,
    input  logic tms,
    input  logic tdi,
    output logic tdo,
    output logic tdo_en,
    // Internal scan interface
    output logic shift_dr,
    output logic capture_dr,
    output logic update_dr,
    output logic [3:0] ir_out
);
    typedef enum logic [3:0] {
        TEST_LOGIC_RESET = 4'hF,
        RUN_TEST_IDLE    = 4'hC,
        SELECT_DR_SCAN   = 4'h7,
        CAPTURE_DR       = 4'h6,
        SHIFT_DR         = 4'h2,
        EXIT1_DR         = 4'h1,
        PAUSE_DR         = 4'h3,
        EXIT2_DR         = 4'h0,
        UPDATE_DR        = 4'h5,
        SELECT_IR_SCAN   = 4'h4,
        CAPTURE_IR       = 4'hE,
        SHIFT_IR         = 4'hA,
        EXIT1_IR         = 4'h9,
        PAUSE_IR         = 4'hB,
        EXIT2_IR         = 4'h8,
        UPDATE_IR        = 4'hD
    } tap_state_t;

    tap_state_t state, next_state;
    logic [3:0] ir_reg;

    // State machine
    always_ff @(posedge tck or negedge trst_n) begin
        if (!trst_n) state <= TEST_LOGIC_RESET;
        else         state <= next_state;
    end

    always_comb begin
        case (state)
            TEST_LOGIC_RESET: next_state = tms ? TEST_LOGIC_RESET : RUN_TEST_IDLE;
            RUN_TEST_IDLE:    next_state = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            SELECT_DR_SCAN:   next_state = tms ? SELECT_IR_SCAN : CAPTURE_DR;
            CAPTURE_DR:       next_state = tms ? EXIT1_DR : SHIFT_DR;
            SHIFT_DR:         next_state = tms ? EXIT1_DR : SHIFT_DR;
            EXIT1_DR:         next_state = tms ? UPDATE_DR : PAUSE_DR;
            PAUSE_DR:         next_state = tms ? EXIT2_DR : PAUSE_DR;
            EXIT2_DR:         next_state = tms ? UPDATE_DR : SHIFT_DR;
            UPDATE_DR:        next_state = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            SELECT_IR_SCAN:   next_state = tms ? TEST_LOGIC_RESET : CAPTURE_IR;
            CAPTURE_IR:       next_state = tms ? EXIT1_IR : SHIFT_IR;
            SHIFT_IR:         next_state = tms ? EXIT1_IR : SHIFT_IR;
            EXIT1_IR:         next_state = tms ? UPDATE_IR : PAUSE_IR;
            PAUSE_IR:         next_state = tms ? EXIT2_IR : PAUSE_IR;
            EXIT2_IR:         next_state = tms ? UPDATE_IR : SHIFT_IR;
            UPDATE_IR:        next_state = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            default:          next_state = TEST_LOGIC_RESET;
        endcase
    end

    // IR shift register
    always_ff @(posedge tck or negedge trst_n) begin
        if (!trst_n) ir_reg <= 4'b0001;  // IDCODE
        else if (state == CAPTURE_IR) ir_reg <= 4'b0001;
        else if (state == SHIFT_IR) ir_reg <= {tdi, ir_reg[3:1]};
    end

    always_ff @(posedge tck) begin
        if (state == UPDATE_IR) ir_out <= ir_reg;
    end

    assign shift_dr = (state == SHIFT_DR);
    assign capture_dr = (state == CAPTURE_DR);
    assign update_dr = (state == UPDATE_DR);
    assign tdo_en = (state == SHIFT_DR) || (state == SHIFT_IR);
endmodule
```

### Memory BIST
```systemverilog
module mbist_controller #(
    parameter int ADDR_W = 10,
    parameter int DATA_W = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             start,
    output logic             done,
    output logic             pass,
    output logic [ADDR_W-1:0] fail_addr,
    // Memory interface
    output logic             mem_en,
    output logic             mem_we,
    output logic [ADDR_W-1:0] mem_addr,
    output logic [DATA_W-1:0] mem_wdata,
    input  logic [DATA_W-1:0] mem_rdata
);
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ZEROS,
        READ_ZEROS,
        WRITE_ONES,
        READ_ONES,
        WRITE_PATTERN,
        READ_PATTERN,
        DONE_STATE
    } state_t;

    state_t state;
    logic [ADDR_W-1:0] addr;
    logic [DATA_W-1:0] expected;
    logic error_flag;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            addr <= '0;
            done <= 1'b0;
            pass <= 1'b0;
            error_flag <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        state <= WRITE_ZEROS;
                        addr <= '0;
                        error_flag <= 1'b0;
                    end
                end

                WRITE_ZEROS, WRITE_ONES, WRITE_PATTERN: begin
                    if (addr == {ADDR_W{1'b1}}) begin
                        addr <= '0;
                        state <= state_t'(state + 1);
                    end else begin
                        addr <= addr + 1;
                    end
                end

                READ_ZEROS, READ_ONES, READ_PATTERN: begin
                    if (mem_rdata != expected) begin
                        error_flag <= 1'b1;
                        fail_addr <= addr;
                    end
                    if (addr == {ADDR_W{1'b1}}) begin
                        addr <= '0;
                        state <= state_t'(state + 1);
                    end else begin
                        addr <= addr + 1;
                    end
                end

                DONE_STATE: begin
                    done <= 1'b1;
                    pass <= !error_flag;
                end
            endcase
        end
    end

    assign mem_en = (state != IDLE) && (state != DONE_STATE);
    assign mem_we = (state == WRITE_ZEROS) || (state == WRITE_ONES) || (state == WRITE_PATTERN);
    assign mem_addr = addr;

    always_comb begin
        case (state)
            WRITE_ZEROS, READ_ZEROS: begin
                mem_wdata = '0;
                expected = '0;
            end
            WRITE_ONES, READ_ONES: begin
                mem_wdata = '1;
                expected = '1;
            end
            default: begin  // Checkerboard pattern
                mem_wdata = {DATA_W/2{2'b10}};
                expected = {DATA_W/2{2'b10}};
            end
        endcase
    end
endmodule
```

---

## Timing Closure Strategies

### Timing Planning

```markdown
## Timing Closure Plan

### Critical Paths
| Path | From | To | Slack | Fix |
|------|------|----|-------|-----|
| path_1 | reg_a | reg_b | -0.5ns | Pipeline |
| path_2 | mux | reg_c | -0.2ns | Restructure |

### Timing Techniques
| Technique | When to Use | Impact |
|-----------|-------------|--------|
| Pipelining | Long combinational paths | +1 cycle latency |
| Retiming | Balance register stages | Neutral latency |
| Logic restructuring | Deep logic cones | May increase area |
| False path | Truly async paths | Removes constraint |
| Multicycle | Slow paths by design | Relaxes timing |
```

### Retiming Example
```systemverilog
// BEFORE: All logic in one stage
// always_ff @(posedge clk) result <= (a * b) + (c * d);

// AFTER: Retimed with pipeline
module retimed_mac (
    input  logic        clk,
    input  logic [15:0] a, b, c, d,
    output logic [31:0] result
);
    logic [31:0] prod_ab, prod_cd;

    // Stage 1: Multiplies
    always_ff @(posedge clk) begin
        prod_ab <= a * b;
        prod_cd <= c * d;
    end

    // Stage 2: Add
    always_ff @(posedge clk) begin
        result <= prod_ab + prod_cd;
    end
endmodule
```

### Logic Restructuring
```systemverilog
// BEFORE: Deep mux tree (slow)
// assign out = sel[3] ? (sel[2] ? ... ) : ...;

// AFTER: Balanced structure
module balanced_mux8 #(parameter WIDTH = 32) (
    input  logic [7:0][WIDTH-1:0] in,
    input  logic [2:0] sel,
    output logic [WIDTH-1:0] out
);
    logic [WIDTH-1:0] stage1 [3:0];
    logic [WIDTH-1:0] stage2 [1:0];

    // Stage 1: 2:1 muxes
    always_comb begin
        stage1[0] = sel[0] ? in[1] : in[0];
        stage1[1] = sel[0] ? in[3] : in[2];
        stage1[2] = sel[0] ? in[5] : in[4];
        stage1[3] = sel[0] ? in[7] : in[6];
    end

    // Stage 2: 2:1 muxes
    always_comb begin
        stage2[0] = sel[1] ? stage1[1] : stage1[0];
        stage2[1] = sel[1] ? stage1[3] : stage1[2];
    end

    // Stage 3: Final mux
    assign out = sel[2] ? stage2[1] : stage2[0];
endmodule
```

### SDC Timing Exceptions
```tcl
# False path - truly asynchronous
set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]
set_false_path -from [get_ports rst_n]
set_false_path -through [get_pins u_sync/sync_ff_reg[0]/D]

# Multicycle path - slow by design
# Data valid every 2 cycles
set_multicycle_path 2 -setup -from [get_pins u_slow/data_reg*/Q]
set_multicycle_path 1 -hold  -from [get_pins u_slow/data_reg*/Q]

# Max delay - I/O constraints
set_max_delay 5.0 -from [get_ports data_in*] -to [get_pins u_input/reg*/D]

# Clock groups - unrelated clocks
set_clock_groups -asynchronous \
    -group [get_clocks clk_sys] \
    -group [get_clocks clk_ext]
```

---

## RTL Review Checklist

### Common RTL Bugs

```markdown
## RTL Bug Checklist

### Latch Inference
- [ ] All `always_comb` blocks have default assignments
- [ ] All `case` statements have `default:`
- [ ] All `if` statements have `else`
- [ ] No incomplete conditional assignments

### Clock Domain Issues
- [ ] All CDC paths use proper synchronizers
- [ ] Gray code for multi-bit CDC counters
- [ ] Async FIFOs for bulk data transfer
- [ ] Reset synchronized to each domain

### Reset Issues
- [ ] All state registers have reset
- [ ] Async reset, sync deassert pattern used
- [ ] Reset polarity consistent (active-low)
- [ ] No combinational paths from reset

### FSM Issues
- [ ] All states reachable
- [ ] No deadlock states
- [ ] Default state transition defined
- [ ] One-hot encoding for fast FPGAs
- [ ] Binary encoding for small FSMs
```

### Synthesis Warning Checklist
```markdown
## Synthesis Warning Categories

### Critical (Must Fix)
- [ ] Latch inferred (LATCH)
- [ ] Multiple drivers (MULTIDRIVEN)
- [ ] Combinational loop (COMBLOOP)
- [ ] Unconnected port (UNCONNECTED on outputs)

### Important (Should Fix)
- [ ] Width mismatch (WIDTH)
- [ ] Unused signal (UNUSED)
- [ ] Undriven signal (UNDRIVEN)
- [ ] Case not full (CASEINCOMPLETE)

### Review (May Be Intentional)
- [ ] Unsigned comparison with signed
- [ ] Implicit wire declarations
- [ ] Non-synthesizable constructs
```

### CDC Review Checklist
```markdown
## CDC Review

### Single-Bit Signals
- [ ] Uses 2FF or 3FF synchronizer
- [ ] Source signal is registered
- [ ] Destination samples at safe rate
- [ ] No combinational logic before sync

### Multi-Bit Signals
- [ ] Gray code encoding
- [ ] MCP (multi-cycle path) or handshake
- [ ] Async FIFO for data streams
- [ ] Proper empty/full synchronization

### Control Signals
- [ ] Pulse synchronizer for strobes
- [ ] Handshake protocol for commands
- [ ] Level synchronizer for enables
- [ ] Proper acknowledgment
```

### FSM Review Checklist
```markdown
## FSM Review

### Structure
- [ ] Enum type with explicit encoding
- [ ] Separate sequential and combinational
- [ ] Default next_state assignment
- [ ] `unique case` or `default:`

### Behavior
- [ ] All states have defined outputs
- [ ] No floating outputs in any state
- [ ] Error state reachable and recoverable
- [ ] Reset goes to known safe state

### Coverage
- [ ] All states reachable from reset
- [ ] All transitions exercised
- [ ] No dead-end states
- [ ] Timeout for stuck states
```

### Coding Style Checklist
```markdown
## Coding Style

### Naming
- [ ] Modules: snake_case
- [ ] Signals: snake_case
- [ ] Parameters: UPPER_SNAKE
- [ ] Types: _t suffix
- [ ] Active-low: _n suffix
- [ ] Clocks: clk prefix
- [ ] Registers: _q or _reg suffix

### Structure
- [ ] ANSI port declarations
- [ ] Parameters before ports
- [ ] Inputs before outputs
- [ ] Logic declaration (not wire/reg)
- [ ] always_ff/always_comb (not always)

### Organization
- [ ] One module per file
- [ ] File name matches module name
- [ ] Consistent indentation (spaces)
- [ ] No trailing whitespace
```

