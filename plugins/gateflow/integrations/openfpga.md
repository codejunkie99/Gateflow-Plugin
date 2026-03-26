# OpenFPGA Integration — Custom FPGA Architectures

OpenFPGA generates customizable FPGA architectures with Verilog-to-bitstream
support. Integration enables GateFlow to target custom FPGA fabrics.

## What This Enables

- Target custom/academic FPGA architectures
- Generate architecture-specific bitstreams
- "Natural language → custom FPGA architecture → bitstream"

## Setup

```bash
git clone https://github.com/lnis-uofu/OpenFPGA.git
cd OpenFPGA && mkdir build && cd build
cmake .. && make -j$(nproc)
```

## Usage with GateFlow

```
/gf-synth --target openfpga --arch my_architecture.xml rtl/top.sv
```

## Status: Phase 5+ (Future)

This integration requires:
- OpenFPGA architecture XML definitions
- Custom place & route configuration
- Bitstream generation for target architecture
