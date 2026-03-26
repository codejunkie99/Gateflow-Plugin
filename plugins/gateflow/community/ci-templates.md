# GateFlow CI/CD Templates

GitHub Actions and GitLab CI templates for hardware projects.

## GitHub Actions — Lint + Sim on Every PR

```yaml
# .github/workflows/gateflow-ci.yml
name: GateFlow CI
on: [push, pull_request]

jobs:
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install Verilator
        run: sudo apt-get update && sudo apt-get install -y verilator
      - name: Run lint
        run: verilator --lint-only -Wall rtl/*.sv

  simulate:
    runs-on: ubuntu-latest
    needs: lint
    steps:
      - uses: actions/checkout@v4
      - name: Install Verilator
        run: sudo apt-get update && sudo apt-get install -y verilator
      - name: Build and run testbench
        run: |
          verilator --binary -j0 --trace -Wall \
            --top-module tb_top -Irtl tb/*.sv rtl/*.sv
          ./obj_dir/Vtb_top

  formal:
    runs-on: ubuntu-latest
    needs: lint
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v4
      - name: Install tools
        run: |
          sudo apt-get update && sudo apt-get install -y yosys z3
          pip install symbiyosys
      - name: Run formal verification
        run: |
          for f in formal/*.sby; do sby -f "$f"; done

  synthesis:
    runs-on: ubuntu-latest
    needs: [simulate, formal]
    if: github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v4
      - name: Install Yosys
        run: sudo apt-get update && sudo apt-get install -y yosys
      - name: Run synthesis
        run: |
          yosys -p "read_verilog -sv rtl/*.sv; synth; stat"
```

## GitLab CI

```yaml
# .gitlab-ci.yml
stages:
  - lint
  - test
  - verify
  - build

lint:
  stage: lint
  image: verilator/verilator:latest
  script:
    - verilator --lint-only -Wall rtl/*.sv

simulate:
  stage: test
  image: verilator/verilator:latest
  script:
    - verilator --binary -j0 --trace --top-module tb_top -Irtl tb/*.sv rtl/*.sv
    - ./obj_dir/Vtb_top
  artifacts:
    paths: ["*.vcd"]

formal:
  stage: verify
  image: hdlc/formal
  script:
    - for f in formal/*.sby; do sby -f "$f"; done
  only: [main]
```

## Usage

Copy the appropriate template into your project:
```bash
mkdir -p .github/workflows
cp ci-templates.md .github/workflows/gateflow-ci.yml
```

Or ask GateFlow: "Set up CI/CD for my hardware project"
