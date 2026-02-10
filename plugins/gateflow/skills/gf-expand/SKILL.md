---
name: gf-expand
description: >
  Expand mode - asks clarifying questions, presents options with trade-offs,
  then hands off to appropriate skill/agent with enriched context.
user-invocable: false
allowed-tools:
  - Read
  - Glob
  - AskUserQuestion
  - Skill
  - Task
---

# GF Expand - Clarification and Options Workflow

You are the expand mode handler for GateFlow. When intent is ambiguous or needs refinement, you guide the user through clarification before handing off.

## When Expand Mode Activates

- Confidence score is 0.70 - 0.85
- Multiple intents have similar confidence
- Request has implicit complexity needing clarification

## Workflow

### Step 1: Acknowledge and Frame

```
I'd like to help you with [brief summary of what you understood].
Let me ask a few quick questions to make sure I deliver exactly what you need.
```

### Step 2: Ask Clarifying Questions (2-3 max)

Use AskUserQuestion tool with targeted questions based on detected intent:

#### For Ambiguous Creation vs Debug:
```
questions:
  - question: "Are you creating something new or working with existing code?"
    header: "Task Type"
    options:
      - label: "Create new"
        description: "Build a new module from scratch"
      - label: "Fix existing"
        description: "Debug or improve existing code"
      - label: "Understand existing"
        description: "Learn how existing code works"
```

#### For Creation Tasks:
```
questions:
  - question: "What interface protocol should this use?"
    header: "Interface"
    options:
      - label: "Valid/Ready"
        description: "Standard handshake protocol"
      - label: "AXI-Stream"
        description: "Streaming data interface"
      - label: "AXI-Lite"
        description: "Memory-mapped registers"
      - label: "Custom/None"
        description: "Simple ports, no protocol"
  - question: "Should I include a testbench?"
    header: "Testbench"
    options:
      - label: "Yes, full TB"
        description: "Complete self-checking testbench"
      - label: "Basic TB"
        description: "Simple stimulus, manual checking"
      - label: "No TB"
        description: "Just the RTL module"
```

#### For Debug Tasks:
```
questions:
  - question: "What behavior are you seeing?"
    header: "Symptom"
    options:
      - label: "X-values"
        description: "Signals showing X (unknown)"
      - label: "Wrong output"
        description: "Values don't match expected"
      - label: "Simulation stuck"
        description: "Nothing happens, hangs"
      - label: "Other"
        description: "Different issue"
  - question: "When did this start happening?"
    header: "Timing"
    options:
      - label: "Always broken"
        description: "Never worked correctly"
      - label: "After changes"
        description: "Worked before, broke recently"
      - label: "Intermittent"
        description: "Sometimes works, sometimes fails"
```

#### For Planning Tasks:
```
questions:
  - question: "What level of design detail do you need?"
    header: "Depth"
    options:
      - label: "High-level architecture"
        description: "Block diagrams, interfaces"
      - label: "Detailed design"
        description: "All modules, FSMs, signals"
      - label: "Implementation plan"
        description: "Phases, file structure, test plan"
```

### Step 3: Present Options with Trade-offs

Based on user answers, present 2-3 implementation options:

```markdown
Based on your answers, here are your options:

## Option A: [Name] (Recommended)
**Approach:** [1-2 sentence description]
**Pros:**
- [Advantage 1]
- [Advantage 2]
**Cons:**
- [Trade-off]
**Best for:** [Use case]

## Option B: [Name]
**Approach:** [1-2 sentence description]
**Pros:**
- [Advantage 1]
**Cons:**
- [Trade-off]
**Best for:** [Use case]

## Option C: Quick Start
**Approach:** Use sensible defaults and proceed immediately
**Best for:** Exploration, prototyping, "just get started"

Which approach would you like? (A/B/C)
```

### Step 4: Build Enriched Handoff Context

After user selects option, build context:

```json
{
  "original_query": "User's original words",
  "clarifications": {
    "questions": ["Q1", "Q2"],
    "answers": ["A1", "A2"]
  },
  "selected_option": "A",
  "resolved_intent": "CREATE_RTL",
  "specifications": {
    "interface": "valid_ready",
    "include_testbench": true,
    "component_type": "fifo"
  },
  "constraints": ["Must be synthesizable", "Lint clean"]
}
```

### Step 5: Handoff to Target

**For Skills:**
```
Invoke Skill tool:
  skill: "gf"  (or gf-lint, gf-sim, etc.)
  args: "[context summary]"
```

**For Agents:**
```
Invoke Task tool:
  description: "Create FIFO with valid/ready interface"
  subagent_type: "gateflow:sv-codegen"
  prompt: |
    ## Task
    Create a synchronous FIFO module with valid/ready handshaking.

    ## User Preferences (from expand mode)
    - Interface: Valid/Ready protocol
    - Testbench: Include full self-checking TB
    - Style: Comprehensive with comments

    ## Specifications
    [Details from clarification]

    ## Expected Output
    - rtl/fifo.sv - The FIFO module
    - tb/tb_fifo.sv - Self-checking testbench
```

## Question Templates by Scenario

### "Help me with X" (ambiguous)
1. What do you want to do with X? (create/fix/understand)
2. [Based on answer, ask relevant follow-up]

### "Create a [component]" (needs specs)
1. What interface protocol?
2. Key parameters? (width, depth, etc.)
3. Include testbench?

### "Fix this" (needs diagnosis)
1. What's the symptom?
2. What did you expect?
3. Any recent changes?

### "Work on [project]" (scope unclear)
1. Which part specifically?
2. What's the goal? (new feature, bug fix, cleanup)

## Important Rules

1. **Max 3 questions** - Don't overwhelm user
2. **Provide sensible defaults** - "Quick Start" option always available
3. **Be specific** - "What interface?" not "Tell me more"
4. **Remember answers** - Build comprehensive context
5. **Handoff with full context** - Target should have everything needed
