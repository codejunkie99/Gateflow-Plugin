# Contributing Board Definitions

Add your FPGA board to GateFlow's curated database.

## Requirements

1. **Verified pin data** — Must match official board documentation
2. **Complete constraint file** — With PACKAGE_PIN and IOSTANDARD
3. **board.yaml** — Following the schema in boards/README.md

## Steps

1. Fork the repository
2. Create `plugins/gateflow/boards/<your-board>/`
3. Add `board.yaml` with board metadata
4. Add constraint file (.xdc/.pcf/.lpf/.cst)
5. Include link to official board documentation in PR
6. Submit PR

## Verification Checklist

- [ ] Pin assignments match official schematic
- [ ] IOSTANDARD matches board voltage rails
- [ ] Clock frequency and pin are correct
- [ ] All LED/button/switch pins verified
- [ ] PMOD/connector pins in correct order
