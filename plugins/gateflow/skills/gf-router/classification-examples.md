# Intent Classification Examples

This file contains few-shot examples for semantic intent classification.
Use these to understand how to classify user requests.

---

## High Confidence Examples (>= 0.85)

### CREATE_RTL Examples
```
Query: "I need a 4-stage pipeline register with valid/ready"
Intent: CREATE_RTL | Confidence: 0.95
Target: gateflow:sv-codegen
Reasoning: Explicit request for specific RTL component with clear specs

Query: "Build me an arbiter for 4 masters"
Intent: CREATE_RTL | Confidence: 0.92
Target: gateflow:sv-codegen
Reasoning: "Build me" + specific component type

Query: "Can you make a synchronous FIFO?"
Intent: CREATE_RTL | Confidence: 0.90
Target: gateflow:sv-codegen
Reasoning: "Make" implies creation, FIFO is specific component

Query: "I want a state machine that handles USB enumeration"
Intent: CREATE_RTL | Confidence: 0.93
Target: gateflow:sv-codegen
Reasoning: "I want" + FSM with specific function
```

### DEBUG Examples
```
Query: "My simulation is stuck, nothing happens after reset"
Intent: DEBUG | Confidence: 0.94
Target: gateflow:sv-debug
Reasoning: Describes failure symptom (stuck), simulation issue

Query: "The output is always X, I don't understand why"
Intent: DEBUG | Confidence: 0.92
Target: gateflow:sv-debug
Reasoning: X-value problem, needs diagnosis

Query: "This used to work but now it fails"
Intent: DEBUG | Confidence: 0.88
Target: gateflow:sv-debug
Reasoning: Regression, something broke

Query: "Why does my counter wrap at 255 instead of 1000?"
Intent: DEBUG | Confidence: 0.90
Target: gateflow:sv-debug
Reasoning: Unexpected behavior, needs root cause analysis
```

### CREATE_TB Examples
```
Query: "Write a testbench for uart_tx.sv"
Intent: CREATE_TB | Confidence: 0.95
Target: gateflow:sv-testbench
Reasoning: Explicit testbench request with target file

Query: "I need tests for this module"
Intent: CREATE_TB | Confidence: 0.88
Target: gateflow:sv-testbench
Reasoning: "Tests" implies testbench creation

Query: "Create stimulus for the memory controller"
Intent: CREATE_TB | Confidence: 0.90
Target: gateflow:sv-testbench
Reasoning: Stimulus is testbench component
```

### VERIFY Examples
```
Query: "Add assertions to verify the AXI protocol"
Intent: VERIFY | Confidence: 0.93
Target: gateflow:sv-verification
Reasoning: Explicit assertion request for protocol

Query: "I need SVA properties for this handshake"
Intent: VERIFY | Confidence: 0.95
Target: gateflow:sv-verification
Reasoning: SVA = SystemVerilog Assertions

Query: "Check that the FIFO never overflows"
Intent: VERIFY | Confidence: 0.87
Target: gateflow:sv-verification
Reasoning: Property to verify, not debug
```

### EXPLAIN Examples
```
Query: "What does the state machine in uart_tx.sv do?"
Intent: EXPLAIN | Confidence: 0.94
Target: gateflow:sv-understanding
Reasoning: "What does X do" = understanding request

Query: "Explain how the arbitration logic works"
Intent: EXPLAIN | Confidence: 0.93
Target: gateflow:sv-understanding
Reasoning: Explicit "explain" for understanding

Query: "I'm confused about this module's interface"
Intent: EXPLAIN | Confidence: 0.85
Target: gateflow:sv-understanding
Reasoning: Confusion = needs explanation

Query: "Walk me through this code"
Intent: EXPLAIN | Confidence: 0.91
Target: gateflow:sv-understanding
Reasoning: "Walk through" = explanation request
```

### REFACTOR Examples
```
Query: "This code has too many lint warnings, clean it up"
Intent: REFACTOR | Confidence: 0.92
Target: gateflow:sv-refactor
Reasoning: Lint warnings + cleanup request

Query: "Make this code more readable"
Intent: REFACTOR | Confidence: 0.88
Target: gateflow:sv-refactor
Reasoning: Readability improvement = refactor

Query: "Fix the coding style issues"
Intent: REFACTOR | Confidence: 0.90
Target: gateflow:sv-refactor
Reasoning: Style issues = refactor task

Query: "Optimize this for better timing"
Intent: REFACTOR | Confidence: 0.86
Target: gateflow:sv-refactor
Reasoning: Optimization = refactoring
```

### ORCHESTRATE Examples
```
Query: "Create a FIFO and make sure it works"
Intent: ORCHESTRATE | Confidence: 0.92
Target: gf
Reasoning: Create + verify = orchestration needed

Query: "Build and test a counter module"
Intent: ORCHESTRATE | Confidence: 0.93
Target: gf
Reasoning: Build + test = end-to-end workflow

Query: "I need a working UART with testbench"
Intent: ORCHESTRATE | Confidence: 0.90
Target: gf
Reasoning: "Working" implies verification, multiple outputs
```

### PLAN Examples
```
Query: "How should I design a DMA controller?"
Intent: PLAN | Confidence: 0.91
Target: gf-plan
Reasoning: "How should I design" = architecture question

Query: "Plan out a cache subsystem for me"
Intent: PLAN | Confidence: 0.94
Target: gf-plan
Reasoning: Explicit "plan out" request

Query: "What's the best architecture for a crossbar?"
Intent: PLAN | Confidence: 0.87
Target: gf-plan
Reasoning: Architecture question before implementation
```

### LEARN Examples
```
Query: "I want to practice writing FSMs"
Intent: LEARN | Confidence: 0.95
Target: gf-learn
Reasoning: Explicit "practice" request

Query: "Give me some exercises for pipelining"
Intent: LEARN | Confidence: 0.93
Target: gf-learn
Reasoning: Exercises = learning mode

Query: "I'm learning SystemVerilog, can you help?"
Intent: LEARN | Confidence: 0.88
Target: gf-learn
Reasoning: Learning context
```

---

## Medium Confidence Examples (0.70-0.85) - Trigger Expand Mode

```
Query: "Help me with the FIFO"
Intent: AMBIGUOUS | Confidence: 0.50
Possible: CREATE_RTL, DEBUG, REFACTOR, EXPLAIN
Action: EXPAND MODE
Questions:
  1. "Do you want to create a new FIFO or work with existing code?"
  2. "Is there a specific problem you're trying to solve?"

Query: "Fix this module"
Intent: AMBIGUOUS | Confidence: 0.65
Possible: DEBUG, REFACTOR
Action: EXPAND MODE
Questions:
  1. "Is there a runtime issue (simulation fails) or code quality issue (lint warnings)?"
  2. "What behavior are you seeing vs expecting?"

Query: "Work on the memory interface"
Intent: AMBIGUOUS | Confidence: 0.55
Possible: CREATE_RTL, REFACTOR, DEBUG, EXPLAIN
Action: EXPAND MODE
Questions:
  1. "Are you creating a new interface or modifying existing code?"
  2. "What's the goal - new feature, bug fix, or understanding?"

Query: "Test this"
Intent: AMBIGUOUS | Confidence: 0.70
Possible: CREATE_TB, SIMULATE
Action: EXPAND MODE
Questions:
  1. "Do you want to create a testbench or run existing tests?"
  2. "Which file/module needs testing?"

Query: "Check this code"
Intent: AMBIGUOUS | Confidence: 0.60
Possible: LINT, VERIFY, EXPLAIN, REFACTOR
Action: EXPAND MODE
Questions:
  1. "What kind of check - lint, functional verification, or code review?"
```

---

## Low Confidence Examples (< 0.70) - Request Clarification

```
Query: "Help"
Intent: UNCLEAR | Confidence: 0.20
Action: CLARIFY
Response: "I'd be happy to help! Could you tell me more about what you're working on? For example:
- Are you creating new RTL code?
- Debugging an issue?
- Trying to understand existing code?"

Query: "FIFO"
Intent: UNCLEAR | Confidence: 0.25
Action: CLARIFY
Response: "I see you're interested in FIFOs. What would you like to do?
- Create a new FIFO module
- Debug an existing FIFO
- Understand how a FIFO works"

Query: "This is wrong"
Intent: UNCLEAR | Confidence: 0.40
Action: CLARIFY
Response: "I'd like to help fix the issue. Could you tell me:
- Which file has the problem?
- What behavior are you seeing?"
```

---

## Context-Dependent Examples

### After code was just created:
```
Query: "Test it"
Intent: SIMULATE (not CREATE_TB) | Confidence: 0.85
Reasoning: Testbench likely exists, user wants to run sim
Target: gf-sim
```

### In learning mode:
```
Query: "Check my solution"
Intent: TUTOR | Confidence: 0.90
Reasoning: Learning context, wants review
Target: gateflow:sv-tutor
```

### After simulation failed:
```
Query: "Fix it"
Intent: DEBUG | Confidence: 0.88
Reasoning: Recent failure context
Target: gateflow:sv-debug
```

---

## Disambiguation Signals

### Signals pointing to CREATE_RTL:
- "new", "create", "build", "make", "generate", "need a", "want a"
- Specific component names (FIFO, FSM, arbiter, counter)
- Interface specifications (width, depth, protocol)

### Signals pointing to DEBUG:
- Problem descriptions (stuck, wrong, fails, broken, X-value)
- "used to work", "suddenly", "after I changed"
- Error messages, unexpected behavior

### Signals pointing to REFACTOR:
- "clean", "lint", "style", "optimize", "readable"
- "warnings", "improve", "better"

### Signals pointing to EXPLAIN:
- "what does", "how does", "explain", "understand"
- "walk through", "confused", "why is this"

### Signals pointing to ORCHESTRATE:
- Multiple actions: "create and test", "build and verify"
- "working" (implies verification)
- "end to end", "complete"
