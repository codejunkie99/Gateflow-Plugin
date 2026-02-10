---
name: gf-build
description: >
  Parallel build orchestrator for SystemVerilog creation tasks.
  Decomposes designs into independent modules, builds in parallel phases,
  runs verification on each component, then integrates.
  Example: "/gf-build RISC-V CPU with ALU, regfile, decoder, control FSM"
allowed-tools:
  - Read
  - Write
  - Edit
  - Glob
  - Grep
  - Bash
  - Task
  - Skill
  - AskUserQuestion
---

# GF-Build: Parallel Design Orchestrator

You orchestrate RTL builds by decomposing designs and spawning parallel agents.

## Invocation

User says: `/gf-build <design description>`

## Workflow

### Step 1: Decompose

Analyze the request and identify:

```markdown
## Design Decomposition: [Name]

### Shared Resources (Phase 0)
| File | Purpose |
|------|---------|
| pkg.sv | Common types, opcodes |

### Independent Components (Phase 1 - Parallel)
| Component | File | Agent | Dependencies |
|-----------|------|-------|--------------|
| ALU | alu.sv | sv-codegen | pkg |
| RegFile | regfile.sv | sv-codegen | pkg |
| ImmGen | imm_gen.sv | sv-codegen | pkg |

### Dependent Components (Phase 2 - Parallel)
| Component | File | Agent | Dependencies |
|-----------|------|-------|--------------|
| Decoder | decoder.sv | sv-codegen | pkg |
| Control | control.sv | sv-codegen | pkg, decoder |

### Integration (Phase 3)
| File | Purpose |
|------|---------|
| top.sv | Connects all components |

### Verification (Phase 4 - Parallel)
| Testbench | Tests |
|-----------|-------|
| tb_alu.sv | ALU operations |
| tb_top.sv | Integration |
```

### Step 2: Ask for Approval

```
I've decomposed your design into [N] components across [M] phases.
Phase 1 will spawn [X] parallel agents.

Proceed with parallel build?
```

### Single-Module Requests

If the design decomposes to a single module:
- Treat it as Phase 1 with one component
- Spawn one sv-codegen task (still using the parallel pattern)
- Continue with lint/testbench/sim as usual

### Step 3: Execute Phases

#### Phase 0: Setup
```bash
mkdir -p rtl tb
```
Spawn sv-codegen to create shared package (stay consistent with agent-only rule).

#### Phase 1: Parallel Component Build

**CRITICAL: Spawn ALL Phase 1 agents in a SINGLE message with multiple Task calls.**

```
<Task 1>
subagent_type: gateflow:sv-codegen
prompt: |
  ## Component: ALU
  [full spec...]
  Write to: rtl/alu.sv
</Task 1>

<Task 2>
subagent_type: gateflow:sv-codegen
prompt: |
  ## Component: Register File
  [full spec...]
  Write to: rtl/regfile.sv
</Task 2>

<Task 3>
subagent_type: gateflow:sv-codegen
prompt: |
  ## Component: Immediate Generator
  [full spec...]
  Write to: rtl/imm_gen.sv
</Task 3>
```

#### Phase 2: Parallel Lint

Run lint on all components:
```
Skill: gf-lint
args: rtl/alu.sv rtl/regfile.sv rtl/imm_gen.sv
```

Parse results. For any failures, spawn sv-refactor agents in parallel.

#### Phase 3: Integration

Either:
- Spawn sv-codegen for top-level with component interfaces
- Or write directly if straightforward

#### Phase 4: Parallel Testbenches

Spawn testbench agents in parallel:
```
<Task 1> sv-testbench for ALU
<Task 2> sv-testbench for RegFile
<Task 3> sv-testbench for top
```

#### Phase 5: Simulation

Run simulations (can be parallel):
```
Skill: gf-sim tb/tb_alu.sv rtl/alu.sv
Skill: gf-sim tb/tb_top.sv rtl/*.sv
```

### Step 4: Report

```markdown
## Build Complete

### Files Created
| Phase | File | Status |
|-------|------|--------|
| 0 | rtl/pkg.sv | ✓ |
| 1 | rtl/alu.sv | ✓ lint-clean |
| 1 | rtl/regfile.sv | ✓ lint-clean |
| 1 | rtl/imm_gen.sv | ✓ lint-clean |
| 3 | rtl/cpu.sv | ✓ lint-clean |
| 4 | tb/tb_cpu.sv | ✓ sim-pass |

### Parallel Efficiency
- Phase 1: 3 agents parallel (vs 3 sequential)
- Phase 4: 2 agents parallel (vs 2 sequential)

### Next Steps
- Run full simulation: `verilator --binary rtl/*.sv tb/tb_cpu.sv`
- Add assertions: `/gf add assertions to cpu.sv`
```

---

## Agent Prompt Templates

### sv-codegen Component Prompt

```markdown
## Component: [NAME]

## Context
Part of: [parent design]
Package: [package to import]

## Specification
[Detailed functional spec]

## Interface
```systemverilog
module [name] #(
    parameter int PARAM = VALUE
) (
    input  logic        clk,
    input  logic        rst_n,
    // [grouped ports]
);
```

## Requirements
1. [Requirement]
2. [Requirement]

## Output
Write to: [path]
```

### sv-testbench Component Prompt

```markdown
## Testbench for: [DUT_NAME]

## DUT Location
rtl/[dut].sv

## Test Scenarios
1. [Test case 1]
2. [Test case 2]
3. [Edge case]

## Self-Checking
- Compare expected vs actual
- Use assertions
- Report pass/fail

## Output
Write to: tb/tb_[dut].sv
```

---

## Parallelism Rules

1. **Same phase = parallel** - Components with no dependencies spawn together
2. **Different phase = sequential** - Wait for previous phase to complete
3. **Lint = batch** - Run on all files at once, or parallel per file
4. **Fix = parallel** - Each failing file gets its own sv-refactor agent
5. **Sim = parallel** - Each testbench can run independently

---

## Error Recovery

| Error | Action |
|-------|--------|
| Agent timeout | Retry once, then ask user |
| Lint failure | Spawn sv-refactor, re-lint |
| Sim failure | Spawn sv-debug, then sv-refactor |
| Integration mismatch | Check interfaces, fix manually |
| 2 consecutive failures | Ask user for guidance |

---

## Return Format

```
---GATEFLOW-RETURN---
STATUS: complete
SUMMARY: Built [design] with [N] components in [M] parallel phases
PARALLEL_SPEEDUP: [X]x (spawned N agents vs sequential)
FILES_CREATED:
  - rtl/pkg.sv
  - rtl/alu.sv
  - rtl/regfile.sv
  - rtl/cpu.sv
  - tb/tb_cpu.sv
VERIFICATION:
  - Lint: PASS (0 errors, 0 warnings)
  - Sim: PASS (all tests)
---END-GATEFLOW-RETURN---
```
