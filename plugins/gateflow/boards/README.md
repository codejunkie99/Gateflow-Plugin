# GateFlow Board Database

Curated FPGA board definitions with constraint files.

## Supported Boards

| Board | FPGA | Constraint Format |
|-------|------|-------------------|
| Arty A7-35T | Xilinx xc7a35t | `.xdc` |
| Basys 3 | Xilinx xc7a35t | `.xdc` |
| iCEBreaker | Lattice iCE40UP5K | `.pcf` |
| Tang Nano 9K | Gowin GW1NR-9 | `.cst` |

## Adding a Board

Create `plugins/gateflow/boards/<board-name>/` with:
- `board.yaml` — Board metadata (FPGA, clock, pins, connectors)
- `constraints.<ext>` — Pin constraint file (.xdc/.pcf/.lpf/.cst)

### board.yaml Schema

```yaml
name: Board Display Name
vendor: Manufacturer
fpga:
  family: xilinx-7series | ice40 | ecp5 | gowin
  device: exact part number
  package: package code
synth_target: synth_xilinx | synth_ice40 | synth_ecp5 | synth_gowin
pnr_target: nextpnr command (or null for vendor-only)
programmer: openFPGALoader command
clock:
  pin: pin name/number
  frequency: clock speed
  iostandard: LVCMOS33 (for XDC boards)
leds: [pin list]
buttons: [pin list]
switches: [pin list]  # optional
pmod:
  connector_name: [pin list]
```

## Contributing

1. Create board directory with yaml + constraints
2. Verify pin assignments against official documentation
3. Submit PR with board reference manual link
