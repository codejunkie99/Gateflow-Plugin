# SPI Protocol Reference

## Signals
| Signal | Direction (Master) | Description |
|--------|-------------------|-------------|
| SCLK | output | Serial clock |
| MOSI | output | Master Out Slave In |
| MISO | input | Master In Slave Out |
| CS_N | output | Chip select (active low) |

## Modes
| Mode | CPOL | CPHA | Clock Idle | Data Capture | Data Shift |
|------|------|------|------------|-------------|------------|
| 0 | 0 | 0 | Low | Rising edge | Falling edge |
| 1 | 0 | 1 | Low | Falling edge | Rising edge |
| 2 | 1 | 0 | High | Falling edge | Rising edge |
| 3 | 1 | 1 | High | Rising edge | Falling edge |

## Timing
- CS_N asserted (low) before first SCLK edge
- Data valid before capture edge
- CS_N deasserted (high) after last SCLK edge
- MSB first (default) or LSB first (configurable)
