---
name: gf-learn
description: SystemVerilog learning mode - generates exercises, reviews solutions
user-invocable: true
allowed-tools:
  - Read
  - Write
  - Bash
  - Task
  - AskUserQuestion
---

# GateFlow Learning Mode

Interactive SystemVerilog learning with exercises and solution review.

## Usage

```
/gf-learn                    # Start learning session, pick topic
/gf-learn <topic>            # Get exercises on specific topic
/gf-learn check <file>       # Submit solution for review
/gf-learn hint               # Get hint for current exercise
/gf-learn solution           # Show solution (gives up)
```

## Topics

| Topic | Exercises |
|-------|-----------|
| `basics` | Signals, always blocks, assignments |
| `fsm` | State machines, encodings, transitions |
| `fifo` | Synchronous FIFOs, pointers, full/empty |
| `pipeline` | Valid/ready, backpressure, stages |
| `cdc` | Clock domain crossing, synchronizers |
| `arbiter` | Round-robin, priority, grant logic |
| `memory` | RAMs, ROMs, register files |
| `protocol` | AXI-lite, Wishbone, handshakes |

## Workflow

### Step 1: Generate Exercise

When user runs `/gf-learn <topic>`:

1. Present 3-5 exercises of increasing difficulty
2. Format each exercise as:

```markdown
## Exercise X: <Title>

**Difficulty:** Beginner/Intermediate/Advanced

**Requirements:**
- [ ] Requirement 1
- [ ] Requirement 2
- [ ] Requirement 3

**Interface:**
```systemverilog
module exercise_name (
    input  logic clk,
    input  logic rst_n,
    // ... define ports
);
```

**Test Cases:**
1. When X happens, Y should occur
2. Edge case: ...

**Starter File:** `exercises/exercise_X.sv`
```

3. Create starter file in `exercises/` directory
4. **STOP and wait for user to attempt solution**

### Step 2: Wait for User

After presenting exercises, say:

```
Your turn! Edit the file and run `/gf-learn check exercises/exercise_X.sv` when ready.

Need help? Run `/gf-learn hint` for a hint.
```

**DO NOT proceed until user submits with `/gf-learn check`**

### Step 3: Review Solution

When user runs `/gf-learn check <file>`:

1. Spawn the `gateflow:sv-tutor` agent to review
2. Present feedback without giving away answers
3. If solution passes, offer next exercise

### Step 4: Hints (on request)

When user runs `/gf-learn hint`:

1. Give progressive hints (hint 1 is vague, hint 3 is specific)
2. Track hint count per exercise
3. Never give full solution in hints

## Exercise Templates

### Beginner: 4-bit Counter
```
Create a 4-bit counter with:
- Synchronous reset
- Enable signal
- Wrap-around at max value
```

### Intermediate: Sync FIFO
```
Create a synchronous FIFO with:
- Parameterized WIDTH and DEPTH
- Full and empty flags
- No overflow/underflow
```

### Advanced: AXI-Lite Slave
```
Create an AXI-Lite slave with:
- 4 read/write registers
- Proper handshaking
- Address decoding
```

## Key Rules

1. **ALWAYS wait for user** after presenting exercises
2. **NEVER show solution** unless explicitly asked with `/gf-learn solution`
3. **Track progress** in `.gateflow/learn/progress.json`
4. **Encourage** - learning is hard, be supportive
