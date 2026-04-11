---
name: gf-viz
description: >
  Terminal visualization for GateFlow codebase maps. Renders module hierarchies,
  FSM state diagrams, and module detail cards as interactive ASCII/Unicode art.
  Example requests: "visualize the codebase", "show hierarchy", "show FSM", "show module detail"
user-invocable: true
allowed-tools:
  - Read
  - Glob
  - Grep
  - Task
  - AskUserQuestion
---

# GF-Viz: Terminal Visualization

Renders `.gateflow/map/` data as interactive ASCII/Unicode diagrams in the terminal.

## Prerequisites

Check for codebase map:

```bash
ls .gateflow/map/CODEBASE.md 2>/dev/null
```

- **Map exists:** Proceed to render
- **No map:** Tell user: "No codebase map found. Run `/gf-map` first to generate one."

## Entry Point

When invoked, render the **Overview Dashboard** and present the navigation menu.

If invoked with an argument (e.g., `/gf-viz uart_tx`), jump directly to the **Module Detail Card** for that module.

---

## View 1: Overview Dashboard

**Data sources:** `CODEBASE.md` (stats, module index), `hierarchy.md` (tree), `fsm.md` (FSM list), `clock-domains.md` (clocks/CDC)

Read these files, extract the data, and render:

```
╔══ CODEBASE: <project_name> ═══════════════════════════════╗
║                                                            ║
║  ● N modules  ● N packages  ● N FSMs  ● N interfaces       ║
║  ● N clocks   ● N CDC       ● N ports   ● N warnings       ║
║                                                            ║
╠══ HIERARCHY (compact) ════════════════════════════════════╣
║                                                            ║
║  ◆ <top> ──┬── <child1> ──┬── <grandchild1>               ║
║            │              └── <grandchild2>                ║
║            └── <child2> ── <grandchild3>                   ║
║                                                            ║
╠══ FSMs ═══════════════════════════════════════════════════╣
║  ↻ <fsm_name> (<module>)  N states: S1→S2→S3→S4           ║
║  ↻ <fsm_name> (<module>)  N states: S1→S2→S3              ║
║                                                            ║
╠══ HEALTH ═════════════════════════════════════════════════╣
║  <✓ or ⚠> lint status  <✓ or ⚠> undriven  <✓ or ⚠> CDC   ║
║                                                            ║
╠═══════════════════════════════════════════════════════════╣
║  [1] Hierarchy  [2] FSMs  [3] Module detail                ║
║  Or ask anything: "show uart_tx", "trace data path"        ║
╚═══════════════════════════════════════════════════════════╝
```

**Rules:**
- Hierarchy flattened to **2 levels max** in dashboard
- FSMs show **one-line summaries** with state chain
- Stats pulled from CODEBASE.md frontmatter and module index
- Health pulled from warnings section
- If any section has no data, show "none detected" rather than omitting

---

## View 2: Hierarchy Explorer

**Data sources:** `hierarchy.md`, `modules/*.md`

```
══ MODULE HIERARCHY ════════════════════════════════════════

◆ <top_module>                                       TOP
├── ■ <inst> : <module> [PARAM=VAL]                   MID
│   ├── ■ <inst> : <module>                           MID
│   │   ├── □ <inst> : <module>                       LEAF
│   │   └── □ <inst> : <module>                       LEAF
│   └── □ <inst> : <module> [W=32, D=16]              LEAF
└── ■ <inst> : <module>                               MID
    └── □ <inst> : <module>                           LEAF

── STATS ──────────────────────────────────────────────
  Total: N modules │ Max depth: N │ Leaf count: N

── INSTANCE TABLE ─────────────────────────────────────
  ┃ Parent       │ Instance   │ Module          │ Params       ┃
  ┃ ...          │ ...        │ ...             │ ...          ┃

═══════════════════════════════════════════════════════════
  [H] Home  [2] FSMs  [3] Module detail: <name>
  Or: "show <module>", "which modules use <module>?"
```

**Module type badges:**
- `◆` **TOP** - bold, top-level module (never instantiated by others)
- `■` **MID** - standard weight, has children
- `□` **LEAF** - lighter weight, no children

**Depth cues:** Deeper modules rendered with lighter visual weight. Top pops, leaves fade.

**Behaviors:**
- Show full tree with all depth levels
- Parameters shown inline as `[PARAM=VAL]`
- Instance table shows all parent→child relationships
- "show <module>" re-renders tree rooted at that module
- "which modules use <module>?" searches instance table, lists parents

---

## View 3: FSM Viewer

**Data sources:** `fsm.md`, per-module pages

**When multiple FSMs exist, show picker first:**

```
══ STATE MACHINES ══════════════════════════════════════════

  [1] ↻ <fsm_name>  (<module>)   N states
  [2] ↻ <fsm_name>  (<module>)   N states
  [3] ↻ <fsm_name>  (<module>)   N states

  Pick a number, or: "show <fsm_name>"
```

**Single FSM rendering:**

```
══ FSM: <fsm_name> ═════════════════════════════════════════
   Module: <module> │ Encoding: N-bit │ Reset: → <reset_state>

                    <condition>
   ┌──────┐  ─────────────►  ┌───────┐
   │      │                  │       │
   │  S1  │                  │  S2   │
   │  ◉   │                  │       │
   └──────┘                  └───┬───┘
      ▲                          │ <condition>
      │                          ▼
   ┌──────┐                  ┌───────┐
   │      │  ◄───────────   │       │──┐
   │  S4  │   <condition>   │  S3   │  │ <self-loop cond>
   │      │                  │       │◄─┘
   └──────┘                  └───────┘

── TRANSITIONS ────────────────────────────────────────────
  ┃ From  │ To    │ Condition     │ Output          ┃
  ┃ S1    │ S2    │ ...           │ ...             ┃
  ┃ S2    │ S3    │ ...           │ ...             ┃
  ┃ ...   │ ...   │ ...           │ ...             ┃

── STATE DETAILS ──────────────────────────────────────────
  ◉ S1   Reset state. <description>
    S2   <description>
    S3   <description>
    S4   <description>

═══════════════════════════════════════════════════════════
  [H] Home  [1] Hierarchy  [3] Module: <parent_module>
  Or: "show another FSM", "explain the S2→S3 transition"
```

**Layout rules for FSM box diagrams:**
- **2-4 states:** Arrange in a line or L-shape
- **4-6 states:** Arrange in a 2x2 or 2x3 grid
- **7+ states:** Use transition table only (too complex for ASCII boxes)
- Reset state always marked with `◉`
- Self-loops shown as `──┐` / `◄─┘` back to same box
- Transition arrows use `──►` with condition labels

**Behaviors:**
- "explain <from>→<to> transition" triggers analysis using RTL source
- "show module" cross-links to parent module's detail card
- Output column in transition table filled when map data includes it

---

## View 4: Module Detail Card

**Data sources:** `modules/<module_name>.md` (primary), `hierarchy.md`, `fsm.md`, `signals.md`

```
╔══════════════════════════════════════════════════════════╗
║  <module_name>                              <TYPE_BADGE> ║
║  <file_path>:<line_range>                                ║
╠══ PARAMETERS ════════════════════════════════════════════╣
║  ┃ Name     │ Type │ Default     │ Description       ┃  ║
║  ┃ ...      │ ...  │ ...         │ ...               ┃  ║
╠══ PORTS ═════════════════════════════════════════════════╣
║  → <name>     input   <width>   <description>           ║
║  → <name>     input   <width>   <description>           ║
║  ← <name>     output  <width>   <description>           ║
║  ← <name>     output  <width>   <description>           ║
╠══ INTERNALS ═════════════════════════════════════════════╣
║                                                          ║
║  Clock : <clock_name> (<domain info>)                    ║
║  Reset : <reset_name> (<type>)                           ║
║  FSM   : ↻ <fsm_name> → <state_list>                    ║
║  Inst  : <instance_count> (<list or "none (leaf)")>      ║
║                                                          ║
╠══ CONNECTIONS ═══════════════════════════════════════════╣
║                                                          ║
║  Instantiated by:                                        ║
║    ■ <parent_module> as <instance_name>                  ║
║      .<port>(<signal>) .<port>(<signal>)                 ║
║      .<port>(<signal>) .<port>(<signal>)                 ║
║                                                          ║
╠══ HEALTH ════════════════════════════════════════════════╣
║  <✓ or ⚠> port connection status                         ║
║  <✓ or ⚠> lint status                                    ║
║  <✓ or ⚠> assertion coverage                             ║
║                                                          ║
╚══════════════════════════════════════════════════════════╝
  [H] Home  [1] Hierarchy  [2] FSM: <fsm_name>
  [↑] Parent: <parent_module>
  Or: "show ports", "explain the handshake", "add assertions"
```

**Port direction symbols:**
- `→` inputs
- `←` outputs
- `↔` bidirectional (inout)

**Type badges:** `TOP`, `MID`, `LEAF`

**Behaviors:**
- Connections section shows **actual signal bindings** from parent instantiation
- If module is instantiated multiple times, show each instance
- FSM line cross-links to FSM viewer
- Parent name cross-links to parent's detail card
- "add assertions" can hand off to `sv-verification` agent
- "explain the handshake" reads RTL source to reason about protocol

---

## Color/Emphasis Vocabulary

Apply these consistently across all views:

| Element | Symbol | Style |
|---------|--------|-------|
| Top module | `◆` | **Bold** |
| Mid module | `■` | Standard |
| Leaf module | `□` | Light |
| Input port | `→` | Green emphasis |
| Output port | `←` | Yellow emphasis |
| Bidir port | `↔` | Cyan emphasis |
| FSM indicator | `↻` | Standard |
| Reset state | `◉` | **Bold/highlighted** |
| Clean/pass | `✓` | Green |
| Warning | `⚠` | Yellow/amber |
| Info/stat | `●` | Standard |
| Transition | `──►` | Standard |

**Depth cues in hierarchy:** Top-level bold, mid standard, leaf dimmed.

---

## Interaction Model

### Menu Navigation

After every render, show a navigation footer with numbered options:
- `[H]` Home - return to dashboard
- `[1]` `[2]` `[3]` - switch between views
- `[↑]` Parent - navigate up in hierarchy (detail card only)

### Free-Form Queries

Always accept natural language alongside menus:
- "show <module_name>" → Module Detail Card
- "show <fsm_name>" → FSM Viewer for that FSM
- "which modules use <module>?" → filtered hierarchy
- "trace <signal> from <module_a> to <module_b>" → signal path analysis
- "explain <aspect>" → reads RTL source, reasons about it
- "add assertions to <module>" → hands off to sv-verification agent
- "back" → previous view
- "home" → dashboard

### Agent Handoff

For queries that go beyond visualization:
- "explain" / "why" → spawn `sv-understanding` agent via Task tool
- "add assertions" → spawn `sv-verification` agent via Task tool
- "fix" / "refactor" → spawn `sv-refactor` agent via Task tool

When handing off, pass the current visualization context (which module, which view) so the agent has full context.

---

## Auto-Trigger After /gf-map

When used as a final step in `gf-architect`, render ONLY the Overview Dashboard (View 1) as a compact summary. Do not show the full interactive menu - just the dashboard with a note:

```
Run /gf-viz to explore interactively.
```

---

## Data Extraction

### Reading CODEBASE.md

Extract from frontmatter:
- `total_files`, `total_tokens`, `commit`, `last_mapped`

Extract from Module Index table:
- Module names, types, files, port summaries

Extract from Warnings section:
- Lint warnings, undriven signals, CDC issues

### Reading hierarchy.md

Extract from Mermaid flowchart:
- Parent→child relationships
- Instance names

Extract from Instance Table:
- Full parent, instance, module, parameters data

### Reading fsm.md

Extract for each FSM:
- FSM name, parent module
- State list with encoding
- Transition table (from, to, condition, output)
- Reset state

### Reading modules/*.md

Extract per module:
- Parameters table
- Ports table (name, direction, width, description)
- Clock/reset info
- Instance list
- Assertion/coverage info

---

## Edge Cases

- **Empty map:** "No codebase map found. Run `/gf-map` first."
- **No FSMs detected:** FSM section shows "No state machines detected in this codebase."
- **Single module:** Hierarchy view shows just the one module. Skip instance table.
- **Module not found:** "Module '<name>' not found in map. Available modules: <list>"
- **Very deep hierarchy (>6 levels):** Render full tree but note: "Deep hierarchy detected. Use 'show <module>' to focus on a subtree."
- **Very wide hierarchy (>10 siblings):** Show first 8, then "... and N more. Use 'show <parent>' to see all."

---

## View 5: Signal Path Trace

Triggered by: "trace data_in from top to digest_out"

Renders signal path across module boundaries as ASCII with boxes for modules, arrows for signals, and `◈` markers for registered boundaries (pipeline stages). Shows hop count and pipeline stage summary.

## View 6: Timing Diagram

Triggered by: "timing uart_tx" or "timing fsm tx_state"

ASCII waveforms: `┌─┐└─┘` for clock, `───` high, `___` low, `╡val╞` for bus/enum values. Auto-generates from FSM data or known protocol patterns. Accepts WaveJSON input for custom diagrams.

## View 7: Diff View

Triggered by: "diff" or "what changed"

Shows structural changes between map snapshots: `+ ADDED`, `~ MODIFIED` (with specific change: port/instance/FSM/parameter), `- REMOVED`. Requires previous snapshot at `.gateflow/map/.prev_*`.

## View 8: Port Connection Matrix

Triggered by: "matrix uart_ctrl" or "connections"

Table showing which parent signals connect to which instance ports. Bottom row shows connected/unconnected counts. Separate section lists all unconnected ports with `⚠` warning. Compact dot-matrix variant for large designs: `●` connected, `○` not connected.

## Search

Triggered by: "find modules with FSM", "find signals named *_valid"

| Query | Finds |
|---|---|
| `find modules with <clock>` | Modules using specific clock |
| `find modules with fsm` | All modules containing FSMs |
| `find modules with >20 ports` | Large interface modules |
| `find signals named <glob>` | Signal name pattern match |
| `find instances of <module>` | All instantiations |
| `find unconnected ports` | Floating ports |
| `find cdc crossings` | Clock domain crossings |
