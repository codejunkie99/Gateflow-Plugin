# I2C Protocol Reference

## Signals
| Signal | Type | Description |
|--------|------|-------------|
| SCL | open-drain | Serial clock (master drives) |
| SDA | open-drain | Serial data (bidirectional) |

## Addressing
- 7-bit address + R/W bit = 8-bit first byte
- 10-bit addressing: two-byte header
- Reserved addresses: 0x00 (general call), 0x78-0x7F (10-bit header)

## Protocol Sequence
1. START: SDA falls while SCL high
2. Address byte: 7-bit addr + R/W, MSB first
3. ACK: slave pulls SDA low for 1 clock
4. Data bytes: 8 bits + ACK each
5. STOP: SDA rises while SCL high

## Clock Stretching
- Slave holds SCL low to pause master
- Master must check SCL before proceeding

## Speed Modes
| Mode | Max Frequency |
|------|---------------|
| Standard | 100 kHz |
| Fast | 400 kHz |
| Fast+ | 1 MHz |
| High-speed | 3.4 MHz |
