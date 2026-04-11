# .sby Configuration Templates

## BMC Template
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

## Prove (Induction) Template
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

## Cover Template
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

## Multi-Task Template (BMC + Prove + Cover)
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

## .sby Options Reference

| Option | Modes | Default | Description |
|--------|-------|---------|-------------|
| `mode` | all | (required) | `bmc`, `prove`, `cover`, or `live` |
| `depth` | bmc, cover | 20 | Number of cycles to check |
| `timeout` | all | none | Timeout in seconds |
| `multiclock` | all | off | Multiple clocks / async logic |
| `expect` | all | pass | Expected result: pass, fail, unknown |
