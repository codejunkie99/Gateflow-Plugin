---
name: gf-learn-ctx
description: >
  Contextual learning — micro-lessons embedded in workflow output.
  Explains hardware concepts on first encounter, tracks what has been
  taught, generates practice exercises on demand.
  Used internally by orchestrator — not typically invoked directly.
user-invocable: false
---

# GF-Learn-Ctx — Contextual Learning

## Philosophy

Teaching happens WITHIN the workflow, not in a separate mode.
The first time a user encounters a concept, explain it briefly.
Never explain the same concept twice.

## First-Encounter Explanations

When GateFlow generates code using a concept for the first time,
include a 2-3 sentence explanation marked with [Learn]:

```
Generated sync_2ff.sv

[Learn] This is a 2-flip-flop synchronizer. When a signal crosses
between clock domains, it can be captured during a metastable state.
Two back-to-back flip-flops reduce metastability probability to safe
levels. For multi-bit signals, use a Gray code FIFO or handshake instead.
```

## Concept Tracking

Check `~/.gateflow/profile.json` before explaining:

```json
{
  "concepts_introduced": ["cdc", "fsm", "pipeline", "fifo", "axi"]
}
```

If concept is in the list, skip the explanation.
After explaining, add the concept to the list.

## Concept Library

| Concept | Trigger | Explanation Focus |
|---------|---------|-------------------|
| cdc | 2FF sync, async FIFO | Metastability, why 2 FFs |
| fsm | State machine code | Two-process pattern, encoding |
| pipeline | Pipeline register | Throughput vs latency |
| fifo | FIFO instantiation | Full/empty, pointer math |
| axi | AXI interface | Valid/ready handshake rules |
| formal | SVA properties | Bounded proof, counterexample |
| synthesis | Yosys output | LUTs vs FFs, resource meaning |
| constraints | Pin mapping | IOSTANDARD, voltage rails |
| vhdl | VHDL code | Comparison with SystemVerilog |

## Generative Exercises

When user asks to practice:
1. Generate a buggy version of a recent design
2. Ask user to find the error
3. Reveal answer with explanation

Example:
```
Want to practice? Here's a FIFO with a subtle bug.
Find what's wrong:

[buggy code]

Hint: Look at the full/empty logic...
```

## Cross-HDL Explanations

When a SV user sees VHDL for the first time:
```
[Learn] VHDL uses 'signal' instead of 'logic', and 'process'
instead of 'always_ff'. The semantics are similar — sequential
logic with sensitivity lists. VHDL is more verbose but equally
capable for synthesis.
```
