# Contributing IP Blocks

Submit verified IP blocks to GateFlow's library.

## Requirements

Every IP block MUST include:
1. `rtl/*.sv` — Lint-clean RTL (Verilator -Wall, zero warnings)
2. `tb/tb_*.sv` — Self-checking testbench (pass/fail counters)
3. `formal/*_props.sv` — SVA formal properties
4. `formal/*.sby` — SymbiYosys configuration
5. `block.yaml` — Metadata (name, version, parameters, ports)
6. `README.md` — Usage guide with instantiation example

## Verification Pipeline

Submitted blocks must pass:
```bash
# Lint
verilator --lint-only -Wall rtl/*.sv

# Simulation
verilator --binary -j0 --trace --top-module tb_<name> -Irtl tb/*.sv rtl/*.sv
./obj_dir/Vtb_<name>

# Formal (if SymbiYosys available)
sby -f formal/<name>.sby
```

All three must PASS before acceptance.

## block.yaml Schema

```yaml
name: block_name
version: 1.0.0
description: One-line description
parameters:
  PARAM_NAME: { type: int, default: 8, description: "..." }
ports:
  - { name: clk, dir: input, width: 1 }
formal_proofs:
  - property_name: "What it proves"
dependencies: []  # Other IP blocks required
```
