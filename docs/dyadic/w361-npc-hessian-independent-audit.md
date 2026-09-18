# W361 independent audit: full-offset Npc Hessian records

Verdict: **PASS; no source, resolver, coordinate, or record-interface defect found.**
This was a read-only mathematical/interface audit, supplemented by fresh default-limit
Lean checks. No proof module was edited.

## Verification performed

Fresh compiles of `NpcPhaseAdditiveNormal.lean`, `NpcPhaseAdditiveHead.lean`, and
`NpcHessianCertificates.lean` each exited zero, with no warnings. The separate probe
`/private/tmp/W361NpcHessianIndependentAudit.lean` printed the eight new public
declarations, the generic `sourceWallHessianOfComparison`, and the existing
`NpcBoundaryFinal.wPnpc_branchFreeSupply`. Every footprint is exactly
`propext`, `Classical.choice`, `Quot.sound`; no arithmetic or field axiom entered.

## Exact source and resolver

Every actual-head adapter and Hessian producer uses
`displayedGamma alpha r h q d = GammaR (2+2*h) q (npcW alpha r h d)`.
The same `EtaData d`, source word, generator map, and `rho` survive into the
source endpoint `QZeroBar DD rho`. No isomorphic replacement source is used.

The resolver is consistently
`E = npcResolver (4 * Monoid.exponent (SemiProd DD.C0 DD.Vmod)) d`.
The first-order comparison resolves `WordLift DD.Vmod DD.C0` at that level;
the full-offset phase comparison resolves the central extension over that same
semidirect product. In the ramified projection, the explicit surjectivity of
`semiProdProjHom` transfers the required order bound to the projected central
extension. It is not silently replaced by the base-head exponent. The constant-zero
two-adic resolver is legitimate here because the displayed Npc word has no `z2pow`
node, as documented by `NpcExact.resolvedFamily`.

This is the displayed rational-parameter Npc family. It is not, by itself, a new
theorem that every arbitrary external two-adic unit has an exact rational display.
The existing exact `NpcDisplayFor` transport remains the bridge to a semantic unit.

## Genuine full-offset coordinates and diagonal

The unramified normal map has core coordinates
`(Phi^-1 a, b, a)`, hence generally nonzero `x2`. Its diagonal is literally
`a ↦ npcUnramifiedDiagonal base hbase s E alpha r d Phi (Phi^-1 a)`.
The normal operator `Phi` is constructed from the established equation
`(1-u) Phi = 1-g`, with bijectivity proved from the existing head fixed-point-free
hypotheses. It is not identified with the unrelated `lcOp` inverse.

The ramified normal map has core coordinates
`(Phi^-1 a, b, bInv^-1 • (g • Phi^-1 a - Phi^-1 a))`.
Here `g` and `bInv` are the actual inverse sigma powers in `DD.C0`; their actions
are correctly transported to the projected head. The cross-coordinate equivalence
`Phi` is the action of the actual projected inverse eta power. Its diagonal is
literally `a ↦ npcRamifiedDiagonal base hbase s tau E alpha r d (Phi^-1 a)`.
The full-offset phase theorem retains the nonzero-offset central charge. Neither
the new adapter nor the original record uses the obsolete `x2=0` Hessian theorem.

Both normal maps are proved additive on every handle rank. The additive comparison
is the same underlying phase equivalence already constructed from the unique normal
representative; it is not an unrelated bijection merely having the same cardinality.
The ramified existential explicitly retains its additive witness before constructing
the record.

## Original-record content and scope

`SourceWallHessian` abbreviates the original `HessianCertificate`, with source form
`QZeroBar DD rho`, the literal diagonal above, and target
`d0(a) + polar(qbar)(a,b) + sum_j polar(qbar)(u_j,v_j)`.
The constructor supplies the F₂-linear equivalence and its inverse, exact change-of-
variables identity, quadraticity, nonsingularity, and the original affine-phase
record. It does not assume an unknown Hessian, Gauss value, or inverse operator.
In particular, the diagonal is not replaced by `qbar`: the affine record's diagonal
pin is the actual `d0`. Dimensions and module structures are derived.

`npcUnramifiedHeadHessian` returns an actual record;
`nonempty_npcRamifiedHeadHessian` returns `Nonempty` of an actual record with the
same fully specified diagonal. The latter is an existence statement, not a supplied
computable choice. Both allow arbitrary `r` and `h`, including `h=0`, and retain
`alpha≥2` and even `q`. Their explicit descent, action-compatibility, wild-two,
projected-head, and scalar-H²-cardinality assumptions match the previous actual-head
comparisons in `NpcBoundaryFinal`; no additional analytic premise is introduced.

The unramified producer still explicitly takes fixed-point-freeness of the two
resolved sigma powers. Those are not automatic from sigma fixed-point-freeness for
an arbitrary head, but the existing simple boundary argument proves them. The
ramified producer retains projected tau oddness, fixed-point-freeness, and semidirect
projection surjectivity. The old final boundary argument also proves these facts.

## Branch-free record packaging: inexpensive mathematics, an API seam

No further Hessian calculation is needed. The existing final split on whether tau
acts trivially supplies exactly the two head sectors required here; the nontrivial
simple boundary excludes the scalar unramified case. An existential diagonal with
`Nonempty (SourceWallHessian ... d0 h)` is the natural common output, because the
two actual diagonals differ and must not be artificially identified.

This cannot be recovered merely by applying the exported `wPnpc_branchFreeSupply`:
that conclusion retains a phase comparison and Gauss value, but forgets additivity
and the original Hessian record. Moreover the concrete-head extraction and sigma-
power fixed-point-free helpers in `NpcBoundaryFinal` are private. A clean follow-up
is to expose/factor those already-proved head facts and replay the same two final
calls with these record producers. The mathematical extension is small; the current
private boundary/descent scaffolding prevents an honest one-line external wrapper.
No broader branch-free original-record producer is claimed by the three audited
modules themselves.

Follow-up: the packaging seam is now closed additively by
`NpcBoundaryHessianCertificates.npcBoundaryHessian`; see
`w361-npc-boundary-hessian-record.md`. It reuses the public word-independent head
profiles, shares the descent setup, and copies only the old private resolved-power
helper. No original module or API was changed.
