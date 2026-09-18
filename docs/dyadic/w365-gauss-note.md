# W365-GAUSS: the Gauss sign and exponent as standalone theorems

Lane opened against base `ab26b51d`, branch `claude/w365-gauss`.

**Target.** PUB2 note (`docs/dyadic/w363-pub2-note.md`, item 8) records that the Gauss sign
and exponent that the Hessian certificates establish on the way,

```
gaussSum (lSqWallHandlePhase ...) = (-1) * 2 ^ (m * (2 * h + 1))    unramified
gaussSum (lSqWallHandlePhase ...) = (+1) * 2 ^ (m * (2 * h + 1))    ramified
```

exist only as a `have` inside two proofs, so an exporter cannot cite them.  This lane names
them, plus the compact-N and compact-M analogues where those are missing, in one new module
`GQ2/Dyadic/Instances/GaussPhaseValues.lean`.

Status: in progress.
