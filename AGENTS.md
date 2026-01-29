# GateFlow Agent Knowledge Sources

## Primary References

### SystemVerilog for Verification, 3rd ed. — Spear/Tumbush
- **Source:** PDF (2012), ~500 pages
- **Scope:** Verification-focused SystemVerilog (OOP testbenches, randomization, coverage, DPI)
- **URL:** https://picture.iczhiku.com/resource/eetop/wYIEDKFRorpoPvvV.pdf

#### Chapter Index
| Ch | Title | Page |
|----|-------|------|
| 1 | Verification Guidelines | 2 |
| 2 | Data Types | 26 |
| 3 | Procedural Statements and Routines | 70 |
| 4 | Connecting the Testbench and Design | 90 |
| 5 | Basic OOP | 132 |
| 6 | Randomization | 170 |
| 7 | Threads and Interprocess Communication | 266 |
| 8 | Advanced OOP and Testbench Guidelines | 274 |
| 9 | Functional Coverage | 324 |
| 10 | Advanced Interfaces | 364 |
| 11 | A Complete SystemVerilog Testbench | 386 |
| 12 | Interfacing with C/C++ | 416 |

#### Agent Mapping
| Agent | Relevant Chapters |
|-------|-------------------|
| `sv-testbench` | 1, 4, 5, 7, 8, 11 |
| `sv-verification` | 1, 6, 9 |
| `sv-codegen` | 2, 3, 10 |
| `sv-debug` | 3, 7, 11 |
| `sv-developer` | All |

---

## Quick Reference

### Verification Constructs
- **Randomization:** Ch 6 (p.170) — `rand`, `randc`, constraints, `randomize()`
- **Coverage:** Ch 9 (p.324) — covergroups, coverpoints, cross coverage
- **OOP:** Ch 5 (p.132), Ch 8 (p.274) — classes, inheritance, polymorphism
- **Threads:** Ch 7 (p.266) — `fork/join`, mailboxes, semaphores, events
- **DPI:** Ch 12 (p.416) — C/C++ integration, import/export

### Design Constructs
- **Data Types:** Ch 2 (p.26) — logic, structs, enums, arrays, queues
- **Interfaces:** Ch 4 (p.90), Ch 10 (p.364) — modports, clocking blocks
- **Routines:** Ch 3 (p.70) — functions, tasks, automatic/static

---

## Usage Notes

When agents need verification guidance:
1. Reference specific chapter for methodology
2. Use book patterns for testbench architecture
3. Follow Spear/Tumbush conventions for OOP verification
