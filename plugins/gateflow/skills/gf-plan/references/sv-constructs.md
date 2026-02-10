## SystemVerilog Constructs Reference

Every plan should consider which of these constructs are needed:

### Packages

```markdown
## Package Design: <name>_pkg

### Purpose
[What this package provides]

### Contents
| Item | Type | Description |
|------|------|-------------|
| DATA_WIDTH | parameter | Bus width |
| state_t | enum | FSM states |
| request_t | struct | Request format |
| encode() | function | Encoding helper |

### Dependencies
- Imports: [other packages]
- Imported by: [modules using this]
```

**Package Template:**
```systemverilog
package dma_pkg;
    // Parameters
    parameter int DATA_WIDTH = 32;
    parameter int ADDR_WIDTH = 32;

    // Types
    typedef enum logic [2:0] {
        IDLE    = 3'b000,
        FETCH   = 3'b001,
        XFER    = 3'b010,
        DONE    = 3'b011,
        ERROR   = 3'b100
    } state_t;

    typedef struct packed {
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] data;
        logic                  valid;
    } request_t;

    // Functions
    function automatic logic [7:0] crc8(input logic [7:0] data);
        // CRC calculation
    endfunction
endpackage
```

### Type Definitions

```markdown
## Type Definitions

### Enums
| Name | Values | Width | Usage |
|------|--------|-------|-------|
| state_t | IDLE, RUN, DONE | 2-bit | FSM state |
| opcode_t | ADD, SUB, MUL, DIV | 2-bit | ALU operations |

### Structs
| Name | Fields | Width | Usage |
|------|--------|-------|-------|
| request_t | addr[31:0], data[31:0], valid | 65 bits | Bus request |
| response_t | data[31:0], error, valid | 34 bits | Bus response |

### Unions (rare, use carefully)
| Name | Members | Usage |
|------|---------|-------|
| data_u | bytes[3:0], word | Byte/word access |

### Typedefs
| Alias | Base | Usage |
|-------|------|-------|
| data_t | logic[31:0] | Data bus |
| addr_t | logic[31:0] | Address |
```

**Type Templates:**
```systemverilog
// Enum with explicit encoding
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    ACTIVE = 2'b01,
    DONE   = 2'b10
} state_t;

// Packed struct (synthesizable, bit-addressable)
typedef struct packed {
    logic [7:0]  tag;
    logic [23:0] addr;
    logic [31:0] data;
} transaction_t;  // 64 bits total

// Unpacked struct (simulation, flexible)
typedef struct {
    string       name;
    int          count;
    logic [31:0] data;
} debug_info_t;

// Union (byte/word access)
typedef union packed {
    logic [31:0]     word;
    logic [3:0][7:0] bytes;
} data_u;

// Simple typedef
typedef logic [31:0] data_t;
typedef logic [11:0] addr_t;
```

### Macros and Preprocessor

```markdown
## Preprocessor Directives

### Defines
| Macro | Value | File | Usage |
|-------|-------|------|-------|
| DATA_WIDTH | 32 | defines.svh | Global width |
| DEBUG | (flag) | defines.svh | Debug mode |
| ASSERT_ON | (flag) | defines.svh | Enable assertions |

### Include Structure
​```
include/
├── defines.svh      # Global defines
├── types.svh        # Type definitions
└── macros.svh       # Utility macros
​```

### Conditional Compilation
| Condition | Purpose | Files |
|-----------|---------|-------|
| `ifdef SIMULATION | Sim-only code | tb/*.sv |
| `ifdef SYNTHESIS | Synth-only code | rtl/*.sv |
| `ifdef FPGA | FPGA-specific | rtl/*.sv |
```

**Macro Templates:**
```systemverilog
// defines.svh
`ifndef DEFINES_SVH
`define DEFINES_SVH

`define DATA_WIDTH 32
`define ADDR_WIDTH 32

// Utility macros
`define FF(clk, rst_n, q, d) \
    always_ff @(posedge clk or negedge rst_n) \
        if (!rst_n) q <= '0; \
        else q <= d

// Conditional
`ifdef SIMULATION
    `define DELAY #1
`else
    `define DELAY
`endif

`endif // DEFINES_SVH
```

### Interfaces and Modports

```markdown
## Interface Design

### <name>_if
**Purpose:** [What this interface encapsulates]
**Parameters:** [Configurable widths, depths]

### Signals
| Signal | Type | Width | Description |
|--------|------|-------|-------------|
| clk | logic | 1 | Clock |
| valid | logic | 1 | Data valid |
| data | logic | [WIDTH-1:0] | Payload |
| ready | logic | 1 | Ready to accept |

### Modports
| Name | Direction | Signals |
|------|-----------|---------|
| master | output | valid, data; input ready |
| slave | input | valid, data; output ready |
| monitor | input | all (passive) |
```

**Interface Template:**
```systemverilog
interface stream_if #(
    parameter int WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);
    logic             valid;
    logic             ready;
    logic [WIDTH-1:0] data;
    logic             last;

    modport master (
        output valid, data, last,
        input  ready
    );

    modport slave (
        input  valid, data, last,
        output ready
    );

    modport monitor (
        input valid, ready, data, last
    );

    // Optional: clocking blocks for TB
    clocking cb @(posedge clk);
        default input #1 output #1;
        output valid, data, last;
        input  ready;
    endclocking

    // Optional: assertions
    property p_handshake;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> valid && $stable(data);
    endproperty
    assert property (p_handshake);

endinterface
```

### Generate Blocks

```markdown
## Generate Blocks

### Loop Generate
| Genvar | Range | Creates | Purpose |
|--------|-------|---------|---------|
| i | 0:N-1 | u_channel[i] | Per-channel logic |
| j | 0:M-1 | mem_bank[j] | Memory banks |

### Conditional Generate
| Condition | True Block | False Block |
|-----------|------------|-------------|
| USE_FIFO | fifo_impl | reg_impl |
| WIDTH > 32 | wide_path | narrow_path |
```

**Generate Templates:**
```systemverilog
// Loop generate - multiple instances
genvar i;
generate
    for (i = 0; i < NUM_CHANNELS; i++) begin : gen_channel
        dma_channel #(
            .ID(i)
        ) u_channel (
            .clk    (clk),
            .rst_n  (rst_n),
            .req    (req[i]),
            .grant  (grant[i])
        );
    end
endgenerate

// Conditional generate
generate
    if (USE_FIFO) begin : gen_fifo
        sync_fifo #(.DEPTH(FIFO_DEPTH)) u_fifo (...);
    end else begin : gen_reg
        register_bank u_regs (...);
    end
endgenerate

// Case generate
generate
    case (IMPL_TYPE)
        "FAST": begin : gen_fast
            fast_impl u_impl (...);
        end
        "SMALL": begin : gen_small
            small_impl u_impl (...);
        end
        default: begin : gen_default
            default_impl u_impl (...);
        end
    endcase
endgenerate
```

### Functions and Tasks

```markdown
## Functions and Tasks

### Functions (combinational, no timing)
| Name | Return | Args | Purpose |
|------|--------|------|---------|
| crc8 | logic[7:0] | data[7:0] | CRC calculation |
| encode | logic[3:0] | onehot[15:0] | Priority encode |
| parity | logic | data[31:0] | Parity bit |

### Tasks (can have timing, for TB)
| Name | Args | Purpose |
|------|------|---------|
| send_packet | data[], len | Send test packet |
| wait_ready | timeout | Wait for ready signal |
| check_result | expected | Verify output |
```

**Function/Task Templates:**
```systemverilog
// Pure function (synthesizable)
function automatic logic [7:0] gray_encode(input logic [7:0] bin);
    return bin ^ (bin >> 1);
endfunction

// Function with local variables
function automatic logic [$clog2(N)-1:0] priority_encode(
    input logic [N-1:0] onehot
);
    for (int i = 0; i < N; i++) begin
        if (onehot[i]) return i[$clog2(N)-1:0];
    end
    return '0;
endfunction

// Task for testbench (with timing)
task automatic send_byte(input logic [7:0] data);
    @(posedge clk);
    tx_valid <= 1'b1;
    tx_data  <= data;
    @(posedge clk);
    while (!tx_ready) @(posedge clk);
    tx_valid <= 1'b0;
endtask

// Task with timeout
task automatic wait_for_done(input int timeout_cycles);
    int count = 0;
    while (!done && count < timeout_cycles) begin
        @(posedge clk);
        count++;
    end
    if (!done) $error("Timeout waiting for done");
endtask
```

### Instantiation Patterns

```markdown
## Module Instantiation

### Instance Table
| Instance | Module | Parameters | Connection |
|----------|--------|------------|------------|
| u_fifo | sync_fifo | .DEPTH(16) | Internal signals |
| u_arb | arbiter | .N(4) | Request/grant |
| u_if | axi_if | default | External port |

### Port Connections
- Named: `.port(signal)` (preferred)
- Positional: Avoid except for simple cases
- Wildcard: `.*` with explicit overrides
```

**Instantiation Templates:**
```systemverilog
// Named port connection (preferred)
sync_fifo #(
    .WIDTH (DATA_WIDTH),
    .DEPTH (FIFO_DEPTH)
) u_fifo (
    .clk     (clk),
    .rst_n   (rst_n),
    .wr_en   (fifo_wr),
    .wr_data (fifo_din),
    .rd_en   (fifo_rd),
    .rd_data (fifo_dout),
    .full    (fifo_full),
    .empty   (fifo_empty)
);

// Wildcard with explicit overrides
dma_channel u_channel (
    .*,                    // Connect matching names
    .data_in  (ch_data),   // Override specific
    .data_out (out_data)
);

// Interface connection
axi_if u_axi_if (.clk(clk), .rst_n(rst_n));

axi_master u_master (
    .clk   (clk),
    .rst_n (rst_n),
    .m_axi (u_axi_if.master)  // Interface modport
);

// Array of instances (with generate)
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_ch
        channel u_ch (
            .id   (i),
            .req  (req[i]),
            .data (data[i])
        );
    end
endgenerate
```

### Assertions (SVA)

```markdown
## Assertion Plan

### Immediate Assertions
| Location | Check | Severity |
|----------|-------|----------|
| FSM default | Invalid state | $error |
| FIFO write | Not full | $error |
| Counter | No overflow | $warning |

### Concurrent Assertions
| Property | Type | Description |
|----------|------|-------------|
| p_handshake | assert | valid stable until ready |
| p_no_overflow | assert | count <= MAX |
| p_eventually_ready | assert | req |-> ##[1:100] ack |
| c_all_states | cover | Visit all FSM states |

### Assertion Bind
| Target | Checker | File |
|--------|---------|------|
| dma_channel | dma_sva | rtl/dma_sva.sv |
| axi_master | axi_protocol_check | rtl/axi_sva.sv |
```

**SVA Templates:**
```systemverilog
// Immediate assertion
always_comb begin
    assert (state inside {IDLE, RUN, DONE})
        else $error("Invalid state: %0d", state);
end

// Concurrent assertions
property p_valid_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> valid && $stable(data);
endproperty
assert property (p_valid_stable) else $error("Valid not held");

property p_request_ack;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:10] ack;
endproperty
assert property (p_request_ack) else $error("No ack within 10 cycles");

// Cover property
cover property (@(posedge clk) state == IDLE ##1 state == RUN);

// Sequence
sequence s_burst;
    valid ##1 valid[*3:8] ##1 last;
endsequence

property p_burst_complete;
    @(posedge clk) $rose(valid) |-> s_burst;
endproperty

// Bind assertions to module
bind dma_channel dma_sva u_sva (.*);
```

### Coverage

```markdown
## Coverage Plan

### Functional Coverage
| Covergroup | Sample | Coverpoints |
|------------|--------|-------------|
| cg_fsm | @(posedge clk) | state, transition |
| cg_config | @config_write | mode, size, enable |
| cg_data | @transfer | data ranges, patterns |

### Cross Coverage
| Cross | Points | Purpose |
|-------|--------|---------|
| state x mode | FSM states, operating mode | Mode-specific behavior |
| size x burst | Transfer size, burst type | All size/burst combos |
```

**Coverage Templates:**
```systemverilog
covergroup cg_fsm @(posedge clk);
    cp_state: coverpoint state {
        bins idle   = {IDLE};
        bins active = {FETCH, XFER};
        bins done   = {DONE};
        bins error  = {ERROR};
        illegal_bins invalid = default;
    }

    cp_transition: coverpoint state {
        bins idle_to_fetch = (IDLE => FETCH);
        bins fetch_to_xfer = (FETCH => XFER);
        bins xfer_to_done  = (XFER => DONE);
    }
endgroup

covergroup cg_config @(posedge config_valid);
    cp_mode: coverpoint mode {
        bins single = {0};
        bins burst  = {1};
        bins chain  = {2};
    }

    cp_size: coverpoint size {
        bins small  = {[1:16]};
        bins medium = {[17:256]};
        bins large  = {[257:4096]};
    }

    cross_mode_size: cross cp_mode, cp_size;
endgroup
```

### Classes (Verification)

```markdown
## Class Hierarchy (for Verification)

### Transaction Classes
| Class | Extends | Purpose |
|-------|---------|---------|
| dma_txn | uvm_sequence_item | DMA transaction |
| burst_txn | dma_txn | Burst transfer |

### Component Classes
| Class | Extends | Purpose |
|-------|---------|---------|
| dma_driver | uvm_driver | Drive DUT |
| dma_monitor | uvm_monitor | Observe interface |
| dma_scoreboard | uvm_scoreboard | Check results |
```

**Class Templates:**
```systemverilog
// Transaction class
class dma_transaction extends uvm_sequence_item;
    rand bit [31:0] src_addr;
    rand bit [31:0] dst_addr;
    rand bit [15:0] length;
    rand bit [1:0]  mode;

    constraint c_aligned {
        src_addr[1:0] == 2'b00;
        dst_addr[1:0] == 2'b00;
    }

    constraint c_length {
        length inside {[1:4096]};
    }

    `uvm_object_utils_begin(dma_transaction)
        `uvm_field_int(src_addr, UVM_ALL_ON)
        `uvm_field_int(dst_addr, UVM_ALL_ON)
        `uvm_field_int(length, UVM_ALL_ON)
    `uvm_object_utils_end
endclass

// Simple class (non-UVM)
class Packet;
    bit [7:0] data[];
    bit [31:0] addr;

    function new(int size);
        data = new[size];
    endfunction

    function void randomize_data();
        foreach (data[i]) data[i] = $urandom();
    endfunction
endclass
```

### DPI (Direct Programming Interface)

```markdown
## DPI Integration

### Imported C Functions
| SV Name | C Name | Return | Args | Purpose |
|---------|--------|--------|------|---------|
| c_crc32 | crc32 | int | data[], len | CRC calculation |
| c_model | ref_model | int | in, out* | Reference model |

### Exported SV Functions
| SV Name | C Name | Purpose |
|---------|--------|---------|
| sv_callback | callback | C calls SV |
```

**DPI Templates:**
```systemverilog
// Import C function
import "DPI-C" function int c_crc32(
    input byte data[],
    input int  length
);

// Import C function with output
import "DPI-C" function void c_reference_model(
    input  int  data_in,
    output int  data_out
);

// Export SV function to C
export "DPI-C" function sv_get_status;

function int sv_get_status();
    return current_status;
endfunction

// Usage
initial begin
    byte packet[] = '{8'h01, 8'h02, 8'h03, 8'h04};
    int crc = c_crc32(packet, 4);
    $display("CRC = %08x", crc);
end
```

