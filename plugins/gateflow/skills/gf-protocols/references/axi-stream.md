# AXI-Stream Protocol Reference

## Signals
| Signal | Width | Direction (Source) | Description |
|--------|-------|-------------------|-------------|
| TDATA | DATA_W | output | Data payload |
| TVALID | 1 | output | Data valid |
| TREADY | 1 | input | Sink ready to accept |
| TLAST | 1 | output | Last beat of packet |
| TKEEP | DATA_W/8 | output | Byte qualifiers (1=valid byte) |
| TSTRB | DATA_W/8 | output | Byte is data(1) or position(0) |
| TID | ID_W | output | Stream identifier |
| TDEST | DEST_W | output | Routing destination |
| TUSER | USER_W | output | Sideband user data |

## Transfer Rules
- Transfer occurs when TVALID && TREADY
- TVALID must not depend on TREADY (no combinational loop)
- Once TVALID asserted, cannot deassert until TREADY handshake
- TDATA, TLAST, TKEEP must be stable while TVALID is high

## Common Patterns

### Source (Producer)
```systemverilog
assign m_axis_tvalid = data_available;
assign m_axis_tdata  = data_out;
assign m_axis_tlast  = is_last_beat;
// Advance when handshake: m_axis_tvalid && m_axis_tready
```

### Sink (Consumer)
```systemverilog
assign s_axis_tready = can_accept;
// Capture when handshake: s_axis_tvalid && s_axis_tready
```

### Passthrough (Pipeline Stage)
```systemverilog
// Register slice for timing closure
assign s_axis_tready = !m_axis_tvalid || m_axis_tready;
always_ff @(posedge clk)
    if (s_axis_tvalid && s_axis_tready) begin
        m_axis_tdata  <= s_axis_tdata;
        m_axis_tlast  <= s_axis_tlast;
        m_axis_tvalid <= 1'b1;
    end else if (m_axis_tready)
        m_axis_tvalid <= 1'b0;
```
