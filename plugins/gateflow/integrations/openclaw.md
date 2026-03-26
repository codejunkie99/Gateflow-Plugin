# OpenClaw Integration Guide

GateFlow is available as an OpenClaw skill, enabling autonomous hardware
design through the OpenClaw AI agent framework.

## What This Enables

- **Autonomous hardware design**: "Design me an SPI controller for my Arty A7"
- **Always-on hardware CI**: OpenClaw monitors repos, auto-runs lint/sim/formal
- **Multi-agent workflows**: OpenClaw orchestration + GateFlow hardware agents

## Publishing to ClawHub

GateFlow publishes as a verified skill on ClawHub (not community-submitted,
for security — see Bitdefender audit findings on community skills).

### Skill Configuration

```yaml
# openclaw-skill.yaml
name: gateflow
description: AI-powered hardware development — RTL, verification, synthesis, FPGA deployment
version: 2.1.0
author: codejunkie99
category: development
tags: [hardware, fpga, rtl, systemverilog, vhdl, synthesis, formal-verification]

triggers:
  - "design * hardware"
  - "create * module"
  - "synthesize"
  - "formal verify"
  - "FPGA"
  - "SystemVerilog"
  - "VHDL"

mcp_server:
  transport: stdio
  command: claude
  args: ["--plugin-dir", "~/.claude-plugins/gateflow/plugins/gateflow", "--mcp"]

capabilities:
  - rtl_generation
  - testbench_generation
  - formal_verification
  - synthesis
  - pin_mapping
  - board_targeting
```

### MCP Interface

OpenClaw communicates with GateFlow via MCP (Model Context Protocol):

```json
{
  "method": "tools/call",
  "params": {
    "name": "gateflow_create",
    "arguments": {
      "description": "Create an SPI controller with testbench",
      "board": "arty-a7-35t",
      "hdl": "systemverilog",
      "options": {
        "formal": true,
        "synthesize": true
      }
    }
  }
}
```

## Security

- GateFlow skill is published as **verified/official** on ClawHub
- All hardware-destructive operations require explicit user confirmation:
  - `/gf-flash` (programming FPGA)
  - Pin mapping from web search
  - File overwrites
- OpenClaw's sandbox isolates GateFlow execution

## Ecosystem Combinations

| OpenClaw + GateFlow + ... | Result |
|---------------------------|--------|
| KiCad | Natural language → schematic |
| openFPGALoader | Natural language → running hardware |
| GitHub Actions | Automated hardware CI/CD |
| Ollama (local LLM) | Fully offline hardware development |
