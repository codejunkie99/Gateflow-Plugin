# Wishbone Protocol Reference

## Signals (Classic Cycle)
| Signal | Width | Direction (Slave) | Description |
|--------|-------|-------------------|-------------|
| CYC_I | 1 | input | Bus cycle active |
| STB_I | 1 | input | Strobe (transfer request) |
| WE_I | 1 | input | Write enable (1=write, 0=read) |
| ADR_I | ADDR_W | input | Address |
| DAT_I | DATA_W | input | Write data |
| DAT_O | DATA_W | output | Read data |
| ACK_O | 1 | output | Transfer acknowledge |
| SEL_I | DATA_W/8 | input | Byte select |

## Transfer Rules
- CYC must be asserted for entire bus cycle
- STB asserted for each individual transfer
- Slave responds with ACK within same or later cycle
- Data valid on ACK cycle

## Pipelined Mode
- STB can be asserted before previous ACK
- Higher throughput for burst transfers
