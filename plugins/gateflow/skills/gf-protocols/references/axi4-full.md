# AXI4-Full Protocol Reference

## Additional Signals (vs AXI4-Lite)

### Burst Support
| Signal | Width | Description |
|--------|-------|-------------|
| AWLEN | 8 | Burst length (0-255, actual = AWLEN+1) |
| AWSIZE | 3 | Bytes per beat (2^AWSIZE) |
| AWBURST | 2 | Burst type: FIXED(00), INCR(01), WRAP(10) |
| ARLEN/ARSIZE/ARBURST | same | Read channel equivalents |

### Write Channel
| Signal | Width | Description |
|--------|-------|-------------|
| WLAST | 1 | Last write beat in burst |

### Read Channel
| Signal | Width | Description |
|--------|-------|-------------|
| RLAST | 1 | Last read beat in burst |

### IDs (for out-of-order support)
| Signal | Width | Description |
|--------|-------|-------------|
| AWID/ARID | ID_W | Transaction ID |
| BID/RID | ID_W | Response ID (must match request) |

## Burst Types
- **FIXED**: Same address every beat (e.g., FIFO access)
- **INCR**: Incrementing address (most common)
- **WRAP**: Wrapping burst (cache line fills)

## Key Rules
- WLAST must be asserted on final write beat
- RLAST must be asserted on final read beat
- Slave must not reorder responses with same ID
- 4KB address boundary must not be crossed by a burst
