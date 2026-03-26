---
name: gf-cocotb
description: >
  Python-based testbench generation using Cocotb. Alternative to
  SystemVerilog testbenches for Python-native hardware engineers.
  Example: "create a cocotb test for the FIFO", "write Python testbench"
user-invocable: true
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
---

# GF-Cocotb — Python Testbench Generation

Generate Cocotb testbenches as an alternative to SystemVerilog TBs.

## Tool Detection

```bash
python3 -c "import cocotb" 2>/dev/null
```

If not found, return GATEFLOW-RESULT ERROR with: `pip install cocotb`

## Test Template

```python
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

@cocotb.test()
async def test_reset(dut):
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    dut.rst_n.value = 0
    for _ in range(3):
        await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    assert dut.count.value == 0
```

## When to Use

| Cocotb | SV Testbench |
|--------|-------------|
| Python (lower barrier) | SystemVerilog |
| Complex stimulus (Python libs) | Protocol + coverage |
| Slower (co-simulation) | Faster (native) |
