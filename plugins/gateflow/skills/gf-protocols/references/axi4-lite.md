# AXI4-Lite Protocol Reference

## Signal List

### Write Address Channel
| Signal | Width | Direction (Slave) | Description |
|--------|-------|-------------------|-------------|
| AWADDR | ADDR_WIDTH | input | Write address |
| AWPROT | 3 | input | Protection type (usually 3'b000) |
| AWVALID | 1 | input | Write address valid |
| AWREADY | 1 | output | Write address ready |

### Write Data Channel
| Signal | Width | Direction (Slave) | Description |
|--------|-------|-------------------|-------------|
| WDATA | DATA_WIDTH | input | Write data |
| WSTRB | DATA_WIDTH/8 | input | Write byte strobes |
| WVALID | 1 | input | Write data valid |
| WREADY | 1 | output | Write data ready |

### Write Response Channel
| Signal | Width | Direction (Slave) | Description |
|--------|-------|-------------------|-------------|
| BRESP | 2 | output | Write response (00=OKAY) |
| BVALID | 1 | output | Write response valid |
| BREADY | 1 | input | Write response ready |

### Read Address Channel
| Signal | Width | Direction (Slave) | Description |
|--------|-------|-------------------|-------------|
| ARADDR | ADDR_WIDTH | input | Read address |
| ARPROT | 3 | input | Protection type |
| ARVALID | 1 | input | Read address valid |
| ARREADY | 1 | output | Read address ready |

### Read Data Channel
| Signal | Width | Direction (Slave) | Description |
|--------|-------|-------------------|-------------|
| RDATA | DATA_WIDTH | output | Read data |
| RRESP | 2 | output | Read response |
| RVALID | 1 | output | Read data valid |
| RREADY | 1 | input | Read data ready |

## Key Rules
- Valid must not depend on ready (no combinational loops)
- Valid must stay asserted until ready handshake
- BRESP after both AWVALID/AWREADY and WVALID/WREADY
- All channels independent (can handshake in any order)
