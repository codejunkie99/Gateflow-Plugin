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
  - Task
  - AskUserQuestion
---

# GF-Cocotb -- Python Testbench Generation

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

## Makefile Template

```makefile
SIM ?= icarus
TOPLEVEL_LANG ?= verilog
VERILOG_SOURCES += $(PWD)/rtl/$(DUT).sv
TOPLEVEL = $(DUT)
MODULE = test_$(DUT)
COCOTB_HDL_TIMEUNIT = 1ns
COCOTB_HDL_TIMEPRECISION = 1ps

ifeq ($(SIM),verilator)
    EXTRA_ARGS += --trace --trace-structs
endif

SIM_BUILD = sim_build/$(SIM)
include $(shell cocotb-config --makefiles)/Makefile.sim
```

## Test Templates

### FIFO Test
```python
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
import random

async def reset_fifo(dut):
    dut.rst.value = 1
    dut.wr_en.value = 0
    dut.rd_en.value = 0
    await ClockCycles(dut.clk, 5)
    dut.rst.value = 0
    await RisingEdge(dut.clk)

@cocotb.test()
async def test_fifo_write_read(dut):
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    await reset_fifo(dut)

    assert dut.empty.value == 1
    written = []
    for i in range(16):
        data = random.randint(0, 255)
        written.append(data)
        dut.din.value = data
        dut.wr_en.value = 1
        await RisingEdge(dut.clk)
    dut.wr_en.value = 0
    await RisingEdge(dut.clk)
    assert dut.full.value == 1

    read = []
    for i in range(16):
        dut.rd_en.value = 1
        await RisingEdge(dut.clk)
        read.append(int(dut.dout.value))
    dut.rd_en.value = 0
    assert read == written
```

### Valid/Ready Handshake Test
```python
@cocotb.test()
async def test_handshake(dut):
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    # ... reset ...

    async def driver():
        for data in range(20):
            dut.s_data.value = data
            dut.s_valid.value = 1
            while True:
                await RisingEdge(dut.clk)
                if dut.s_ready.value == 1:
                    break
        dut.s_valid.value = 0

    async def backpressure():
        while True:
            dut.m_ready.value = random.randint(0, 1)
            await ClockCycles(dut.clk, random.randint(1, 4))

    cocotb.start_soon(driver())
    cocotb.start_soon(backpressure())
    await ClockCycles(dut.clk, 200)
```

### FSM Test
```python
from enum import IntEnum

class State(IntEnum):
    IDLE = 0
    ACTIVE = 1
    DONE = 2

@cocotb.test()
async def test_fsm(dut):
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    # reset...
    assert int(dut.state.value) == State.IDLE
    dut.start.value = 1
    await RisingEdge(dut.clk)
    dut.start.value = 0
    await RisingEdge(dut.clk)
    assert int(dut.state.value) == State.ACTIVE
```

## Python Runner (pytest)

```python
import os
from pathlib import Path
from cocotb_tools.runner import get_runner

def test_module():
    sim = os.getenv("SIM", "icarus")
    runner = get_runner(sim)
    runner.build(
        sources=[Path("rtl/my_module.sv")],
        hdl_toplevel="my_module",
    )
    runner.test(
        hdl_toplevel="my_module",
        test_module="test_my_module",
    )
```

## cocotbext Protocol Libraries

| Package | Protocol | Install |
|---|---|---|
| `cocotbext-axi` | AXI4, AXI-Lite, AXI-Stream | `pip install cocotbext-axi` |
| `cocotbext-wishbone` | Wishbone B4 | `pip install cocotbext-wishbone` |
| `cocotbext-spi` | SPI | `pip install cocotbext-spi` |
| `cocotbext-uart` | UART | `pip install cocotbext-uart` |
| `cocotbext-eth` | Ethernet | `pip install cocotbext-eth` |
| `cocotbext-pcie` | PCIe | `pip install cocotbext-pcie` |

### AXI-Lite Example
```python
from cocotbext.axi import AxiLiteBus, AxiLiteMaster

axil = AxiLiteMaster(AxiLiteBus.from_prefix(dut, "s_axi"), dut.clk, dut.rst)
await axil.write(0x0000, b'\x42\x00\x00\x00')
data = await axil.read(0x0000, 4)
```

## Decision Matrix: Cocotb vs SV TB

| Factor | Use Cocotb | Use SV/UVM |
|---|---|---|
| Team knows Python | Yes | - |
| FPGA project | Yes | - |
| Large ASIC with UVM infra | - | Yes |
| Need open-source CI | Yes | - |
| Standard protocols (AXI, SPI) | Yes (cocotbext) | - |
| Deep constrained random | - | Yes |
| Rapid iteration | Yes | - |

## GATEFLOW-RESULT Integration

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
ERRORS: <count>
WARNINGS: <count>
FILES: <test files>
DETAILS: <summary>
---END-GATEFLOW-RESULT---
```
