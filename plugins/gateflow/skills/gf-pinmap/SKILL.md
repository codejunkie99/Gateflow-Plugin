---
name: gf-pinmap
description: >
  Board-aware pin mapping. Generates FPGA constraint files (.xdc/.pcf/.lpf/.cst)
  with correct pin assignments, I/O standards, and drive strength for target boards.
  Example: "map SPI to PMOD JA on Arty A7", "generate constraints for my iCEBreaker"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - WebSearch
  - WebFetch
---

# GF-Pinmap — Board-Aware Pin Mapping

## Workflow

1. **Identify board** — Check `.gateflow/project.yaml` target.board or ask user
2. **Check curated database first**:
   ```bash
   ls ${CLAUDE_PLUGIN_ROOT}/boards/<board>/board.yaml 2>/dev/null
   ```
3. **If board found**: Read board.yaml, generate constraint file
4. **If board NOT found**: Web search as fallback, require user confirmation
5. **Cross-reference** generated constraints with RTL port list
6. **Output** constraint file in correct format for target FPGA

## Curated Board Flow

1. Read `boards/<board>/board.yaml` for pin data
2. Read `boards/<board>/constraints.*` for template
3. Map RTL ports → board pins based on user's peripheral selection
4. Generate complete constraint file with:
   - PACKAGE_PIN
   - IOSTANDARD (from board.yaml)
   - DRIVE strength (default 12mA for outputs)
   - SLEW rate (default SLOW)
   - PULLUP for active-low signals

## Web Search Fallback

Only when board is NOT in curated database:

1. Search: `"<board name>" constraint file site:github.com`
2. Search: `"<board name>" pinout .xdc OR .pcf OR .lpf`
3. Present findings to user with WARNING:
   ```
   Found constraint data for <board> via web search.
   Source: <url>
   
   WARNING: This pin data has NOT been verified against the official
   board documentation. Incorrect pin assignments can damage hardware.
   
   Please review before applying:
   [show pin assignments]
   
   Apply these constraints? [Y/n]
   ```
4. NEVER auto-apply web-searched data

## Safety

- Never guess pin assignments
- Always include IOSTANDARD (missing = synthesis error or hardware damage)
- Check voltage bank compatibility
- Warn if mixing I/O standards in the same bank
- Active-low signals get PULLUP
