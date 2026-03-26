# F4PGA Integration — "The GCC of FPGAs"

F4PGA is a fully open-source FPGA toolchain that extends GateFlow's
synthesis coverage to Xilinx 7-series via Project X-Ray.

## What This Enables

- Xilinx 7-series support (Artix-7, Spartan-7) without Vivado
- Unified open-source flow: Yosys → nextpnr-xilinx → bitstream
- `/gf-synth --backend f4pga` for broader device support

## Setup

```bash
# Install F4PGA
conda install -c litex-hub f4pga
# Or from source: https://f4pga.org/

# Set environment
export F4PGA_INSTALL_DIR=~/f4pga
export FPGA_FAM=xc7
```

## Usage with GateFlow

When target board uses Xilinx 7-series AND user prefers open-source:
```
/gf-synth --backend f4pga rtl/top.sv
```

GateFlow auto-detects F4PGA availability and offers it as an alternative
to Vivado for supported devices.

## Supported Devices (via Project X-Ray)

- Artix-7: xc7a35t, xc7a50t, xc7a100t, xc7a200t
- Spartan-7: xc7s6, xc7s15, xc7s25, xc7s50
- Partial: Kintex-7 (experimental)
