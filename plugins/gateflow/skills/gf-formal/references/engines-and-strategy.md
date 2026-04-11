# Proof Strategy and Engines

## Proof Strategy

```
What to verify?
  |
  +-- Bugs in first N cycles? --> BMC (mode bmc)
  +-- Always true, forever?   --> Prove (mode prove)
  +-- Can state be reached?   --> Cover (mode cover)
  +-- Eventually happens?     --> Live (mode live)
```

| Property Type | Approach | Engine |
|---|---|---|
| Simple bounds | BMC first, then prove | `smtbmc z3` |
| Protocol compliance | BMC + prove | `smtbmc z3`, `abc pdr` |
| FSM correctness | Prove with invariants | `abc pdr` |
| Liveness | Live mode | `aiger suprove` |
| Complex arithmetic | BMC (prove may timeout) | `smtbmc bitwuzla` |

## Engine Comparison

| Engine | Modes | Strengths |
|---|---|---|
| `smtbmc` | bmc, prove, cover | Human-readable traces, k-induction |
| `abc pdr` | prove | Powerful unbounded proofs, auto-invariants |
| `abc bmc3` | bmc | Fast bit-level bounded checking |
| `aiger suprove` | prove, live | Liveness verification |

## SMT Solver Options

| Solver | Best For |
|---|---|
| `z3` | Good default, permissive license |
| `yices` | Fast bit-vector problems |
| `bitwuzla` | Complex arithmetic |
| `boolector` | Hardware-specialized |
