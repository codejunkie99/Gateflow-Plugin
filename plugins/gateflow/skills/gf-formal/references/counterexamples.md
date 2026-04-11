# Counterexample Interpretation

## Trace Locations

| Failure | Location |
|---|---|
| BMC failure | `<task>/engine_0/trace.vcd` |
| Induction failure | `<task>/engine_0/trace_induct.vcd` |
| Cover trace | `<task>/engine_0/trace<N>.vcd` |

## Debugging Workflow

```
Assertion Fails
  +-- BMC mode? --> Counterexample is REACHABLE --> Fix design
  +-- Prove mode?
        +-- BMC also fails? --> Real bug, fix design
        +-- BMC passes? --> Unreachable induction state
              --> Add invariant assertions
              --> Or try `abc pdr` (builds invariants automatically)
```

## Common Failure Patterns

| Pattern | Fix |
|---|---|
| Missing initial value | Add reset logic |
| Unconstrained input | Add `assume` properties |
| Unreachable induction state | Strengthen invariants or use `abc pdr` |
| Over-constrained (cover fails) | Relax assumptions |
