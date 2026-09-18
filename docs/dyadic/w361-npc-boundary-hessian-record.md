# W361: branch-free original Npc Hessian record

`Instances/NpcBoundaryHessianCertificates.lean` exports
`NpcBoundaryHessianCertificates.npcBoundaryHessian`.

For every actual boundary lift of the displayed source
`GammaR (2+2*h) q (npcW alpha r h d)`, it proves

`∃ d0, Nonempty (SourceWallHessian DD rhoN (scalarActionZmodTwo_triv _) d0 h)`.

Here `DD` is the actual nonzero-radical descent datum and `rhoN` is its actual
`rhoPrimeK` map. The output is the original `HessianCertificate` on
`QZeroBar DD rhoN`, with a linear equivalence and inverse, exact phase identity,
quadratic/nonsingular target, and original affine-phase record. The target is
`d0(a)+polar(qbar)(a,b)+sum polar(qbar)(u_j,v_j)`.

The diagonal is existential only to combine the two genuine head formulas; each
branch constructs the literal full-offset diagonal certified by
`NpcHessianCertificates`. No x₂=0 slice or inverse-`lcOp` assumption is used.

## Scope

The assumptions are the existing `UniformHsimp`, `alpha≥2`, nonzero even `q`,
canonical tame generator equations, and the same finite boundary/block, simple,
nonzero, nontrivial-action hypotheses used by the previous final Npc boundary
theorem. The tame/pro-2 maps and their ν-compatibility are retained unchanged.

There is no supplied ramification-sector choice, fixed-point-free power, head
oddness, H²-cardinality, normal-form, quadraticity, Gauss, or unknown Hessian
premise. Those are discharged internally. The old external `m`, `m≥1`, and
coefficient-cardinality equation are not required: the record constructor derives
its own dimension and cardinality.

The result is uniform in `r` and handle rank `h`, including `h=0`. It concerns the
displayed `EtaData` family; exact semantic-unit transport still uses the existing
`NpcDisplayFor` bridge. It does not assert that every arbitrary external two-adic
unit has a rational display.

## Construction and verification

The proof shares one descent setup and uses the existing public
`projectedHead_marking`, `head_cyclic_of_unramified`,
`head_sigma_fixedPointFree`, and `head_tau_ramified_profile` lemmas. Only the
90-line private resolved-sigma-power fixed-point-free helper is copied, unchanged
in mathematical content, from `NpcBoundaryFinal`. No old API is exposed or edited.

The single split is on trivial versus nontrivial tau action, not on field classes
or handle rank. Both calls retain the same semidirect-product resolver
`npcResolver (4 * exponent (SemiProd DD.C0 DD.Vmod)) d` through the actual-head
Hessian adapters.

The public theorem compiles at default limits, warning-free, with exactly
`propext`, `Classical.choice`, and `Quot.sound`. It is a new additive record
producer, not a change to the old boundary-residue API or a publication-format
approval.
