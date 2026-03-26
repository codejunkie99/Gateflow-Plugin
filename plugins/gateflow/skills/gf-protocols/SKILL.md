---
name: gf-protocols
description: >
  Protocol scaffolding library. Generates correct, readable protocol
  interface scaffolds (AXI4-Lite, SPI, UART, I2C, AXI4-Full, AXI-Stream,
  Wishbone) with testbench templates and integration examples.
  Example: "create an I2C master interface", "scaffold AXI-Stream source"
allowed-tools:
  - Read
  - Write
  - Glob
  - Grep
  - Task
---

# GF-Protocols — Protocol Scaffolding Library

Not production IP cores. Correct, readable scaffolds that engineers customize.
Plus the testbenches and integration code — that's where the real time goes.

## Available Protocols

| Protocol | Priority | Scaffold Includes |
|----------|----------|-------------------|
| AXI4-Lite | 1 | Slave register interface + master BFM + TB |
| SPI | 2 | Master + slave + loopback TB |
| UART | 3 | TX + RX + loopback TB |
| I2C | 4 | Master + slave model + TB |
| AXI4-Full | 5 | Slave + burst master BFM + TB |
| AXI-Stream | 6 | Source + sink + passthrough + TB |
| Wishbone | 7 | Slave + master + TB |

## Usage

When user requests a protocol interface:
1. Check if the IP library has a complete block (`/gf-ip list`)
2. If available as IP: suggest `/gf-ip add <block>` instead
3. If not available or user wants custom: generate scaffold

## Scaffold Generation

Each scaffold includes:
- RTL skeleton with correct port names and widths
- Signal timing comments (when to assert/deassert)
- Testbench template with BFM (Bus Functional Model)
- Integration example showing how to wire into a design

## Protocol References

Detailed protocol specifications are in `references/`:
- `references/axi4-lite.md` — AXI4-Lite signal list, timing, rules
- `references/spi.md` — SPI modes, timing, signal descriptions
- `references/i2c.md` — I2C protocol, addressing, clock stretching

When generating scaffolds, ALWAYS read the reference first for correct
signal names, widths, and timing requirements.
