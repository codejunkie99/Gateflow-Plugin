---
name: gf-formal
description: >
  Formal verification from natural language. Generates SVA properties,
  configures SymbiYosys, runs proofs, and explains results.
  Example: "formally verify the FIFO never overflows"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - WebSearch
  - AskUserQuestion
---

# GF-Formal -- Formal Verification Skill

## Tool Detection

```bash
which sby
```

If not found:
```
---GATEFLOW-RESULT---
STATUS: ERROR
DETAILS: SymbiYosys not installed. Install to enable formal verification.
  pip install symbiyosys
  Also need: yosys, z3 (or yices2)
  macOS: brew install yosys z3
  Linux: sudo apt install yosys z3
---END-GATEFLOW-RESULT---
```

## Workflow

1. Parse request -- What properties to verify? Which module?
2. Read the design -- Understand ports, signals, behavior
3. Spawn sv-formal agent -- Generate properties + .sby config
4. Run SymbiYosys: `sby -f <config>.sby`
5. Parse results -- Read sby output for pass/fail/counterexample
6. Report -- 3-layer error translation if failed, clear summary if passed

## Result Format

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
PROOFS: N proved, M failed, K covers
FILES: [generated files]
DETAILS: [proof results or counterexample explanation]
---END-GATEFLOW-RESULT---
```

## Integration with /gf Orchestrator

Formal verification is an optional enhancement step:
- After simulation passes, for safety-critical designs
- When user explicitly requests formal verification
- For CDC, FIFO, or protocol designs

## .sby Configuration Templates

### BMC Template
```sby
[tasks]
bmc
[options]
mode bmc
depth 20
expect pass
[engines]
smtbmc z3
[script]
read -formal design.sv
prep -top top_module
[files]
design.sv
```

### Prove Template
```sby
[tasks]
prove
[options]
mode prove
depth 40
expect pass
[engines]
smtbmc z3
abc pdr
[script]
read -formal design.sv
prep -top top_module
[files]
design.sv
```

### Cover Template
```sby
[tasks]
cover
[options]
mode cover
depth 30
expect pass
[engines]
smtbmc z3
[script]
read -formal design.sv
prep -top top_module
[files]
design.sv
```

### Multi-Task (BMC + Prove + Cover)
```sby
[tasks]
bmc
prove
cover
[options]
bmc: mode bmc
bmc: depth 20
prove: mode prove
prove: depth 40
cover: mode cover
cover: depth 30
expect pass
[engines]
bmc: smtbmc z3
prove: smtbmc z3
prove: abc pdr
cover: smtbmc z3
[script]
read -formal design.sv
prep -top top_module
[files]
design.sv
```

### .sby Options
| Option | Modes | Description |
|--------|-------|-------------|
| `mode` | all | `bmc`, `prove`, `cover`, or `live` |
| `depth` | bmc, cover | Cycles to check (default 20) |
| `timeout` | all | Timeout in seconds |
| `multiclock` | all | Multiple clocks / async |
| `expect` | all | Expected: pass, fail, unknown |

## SVA Property Patterns

### No Overflow
```systemverilog
a_no_overflow: assert property (
    @(posedge clk) disable iff (rst) full |-> !wr_en);
```

### No Underflow
```systemverilog
a_no_underflow: assert property (
    @(posedge clk) disable iff (rst) empty |-> !rd_en);
```

### Valid/Ready Handshake
```systemverilog
a_valid_stable: assert property (
    @(posedge clk) disable iff (rst) (valid && !ready) |=> valid);
a_data_stable: assert property (
    @(posedge clk) disable iff (rst) (valid && !ready) |=> $stable(data));
```

### One-Hot
```systemverilog
a_onehot: assert property (
    @(posedge clk) disable iff (rst) $onehot(state));
```

### Liveness
```systemverilog
a_req_granted: assert property (
    @(posedge clk) disable iff (rst) req |-> ##[1:MAX_LATENCY] grant);
```

### Reset Behavior
```systemverilog
a_reset: assert property (
    @(posedge clk) rst |-> (data_out == '0) && (count == '0));
```

### FIFO Count
```systemverilog
a_count_inc: assert property (
    @(posedge clk) disable iff (rst)
    (wr_en && !rd_en && !full) |=> (count == $past(count) + 1));
```

## Proof Strategy

| Property Type | Approach | Engine |
|---|---|---|
| Simple bounds | BMC then prove | `smtbmc z3` |
| Protocol compliance | BMC + prove | `smtbmc z3`, `abc pdr` |
| FSM correctness | Prove | `abc pdr` |
| Liveness | Live mode | `aiger suprove` |
| Complex arithmetic | BMC | `smtbmc bitwuzla` |

## Engines

| Engine | Modes | Strengths |
|---|---|---|
| `smtbmc` | bmc, prove, cover | Readable traces, k-induction |
| `abc pdr` | prove | Unbounded proofs, auto-invariants |
| `abc bmc3` | bmc | Fast bit-level checking |
| `aiger suprove` | prove, live | Liveness verification |

### SMT Solvers
| Solver | Best For |
|---|---|
| `z3` | Good default |
| `yices` | Fast bit-vectors |
| `bitwuzla` | Complex arithmetic |
| `boolector` | Hardware-specialized |

## Counterexample Interpretation

| Failure | Trace Location |
|---|---|
| BMC | `<task>/engine_0/trace.vcd` |
| Induction | `<task>/engine_0/trace_induct.vcd` |
| Cover | `<task>/engine_0/trace<N>.vcd` |

### Debugging
- BMC fails: counterexample is reachable, fix design
- Prove fails but BMC passes: unreachable induction state, add invariants or use `abc pdr`
- Cover fails: over-constrained, relax assumptions

| Pattern | Fix |
|---|---|
| Missing initial value | Add reset logic |
| Unconstrained input | Add `assume` properties |
| Unreachable induction | Strengthen invariants or use `abc pdr` |

## Formal Extensions

| Directive | Purpose |
|---|---|
| `assert(expr)` | Must always be true |
| `assume(expr)` | Constrain solver inputs |
| `cover(expr)` | Reachability target |

| Attribute | Behavior |
|---|---|
| `(* anyconst *)` | Solver picks constant |
| `(* anyseq *)` | Solver picks per-cycle |

```systemverilog
`ifdef FORMAL
    initial assume(rst);
    always @(posedge clk) begin
        a_example: assert(count <= MAX);
        c_reach: cover(count == MAX);
    end
`endif
```
