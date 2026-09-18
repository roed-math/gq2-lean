# W361 independent audit: N-family boundary Hessian records

Status: **PASS within the stated interfaces**, 2026-09-17. Fresh default Lean
checks of both reviewed modules exit 0 without warnings. All five public pins
print exactly `propext`, `Classical.choice`, and `Quot.sound`. No code,
renderer, generated appendix, frozen artifact or owner decision was changed
by this audit.

Reviewed modules:

* [NpcBoundaryHessianCertificates](../../GQ2/Dyadic/Instances/NpcBoundaryHessianCertificates.lean),
  compared with [NpcBoundaryFinal](../../GQ2/Dyadic/Instances/NpcBoundaryFinal.lean)
  and its actual full-offset head producers;
* [CompactNHessianCertificates](../../GQ2/Dyadic/Instances/CompactNHessianCertificates.lean),
  compared with [WordPhaseCompactNData](../../GQ2/Dyadic/Instances/WordPhaseCompactNData.lean).

## 1. Npc source and boundary lift are unchanged

`npcBoundaryHessian` quantifies over the same displayed source
`displayedGamma alpha r h q d`, whose word is `npcW alpha r h d`. Its boundary
map is literally `sourceBoundaryMapK tame pro2 compat`. For each nonzero
radical-cover character and supplied boundary lift it uses

```
DD = (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl,
rhoN = rhoPrimeK (blockFrame T Blk hE2)
          (sourceBoundaryMapK tame pro2 compat) F (En.radData l hl) rfl rho.
```

These are the same definitions as the previous unramified and ramified
boundary theorems, not a replacement quotient, new lift, or abstractly
isomorphic source. `rho0_descData_rhoPrimeK` identifies the lower map with
the supplied lift's head component. The source action is pulled back through
that component, and the proof derives its compatibility with `rho0 DD rhoN`.
The output is an original `HessianCertificate` for
`QZeroBar DD rhoN`, via the abbreviation `SourceWallHessian`.

The retained inputs are the previous boundary interface: `UniformHsimp`,
`alpha≥2`, nonzero even q, finite marked target and minimal block with the
existing normality instances, exponent-two E, boundary frame, compatible
tame/pro-2 maps with the three canonical tame generator equations, simple
nonzero nontrivial block action, nonzero cover character, and its actual
boundary lift. No sector, inverse, phase identity or cardinality input is
added. The old Gauss-output parameters m and `|V|=2^(2m)` are unnecessary for
the new record: its F₂ dimension and cardinality are derived internally.

`UniformHsimp` remains explicit, just as in the old boundary theorem; this
is not an unconditional assertion for arbitrary raw `EtaData`. The existing
`NpcDeterminantFinal.npcAffineDeterminantCertificate` already constructs it
for an exact `NpcDisplayFor eta`, using the display's
`toPadic = 1+2*z` witness and `NProcyclicUnram.uniformPushedHsimp`.
The new wrapper does not introduce a new residue assumption at that
displayed/selected endpoint.

## 2. The Npc sector hypotheses are actually derived

The proof splits on the boundary tame-inertia action; no branch flag appears
in the public conclusion.

| Required head fact | Proof source in the new wrapper |
| --- | --- |
| Projected sigma/tau are the boundary head generators; projected wild entries are **group identities** | `projectedHead_marking`, applied to the same source generators and canonical tame equations |
| Coefficient action descends | `blockProjF_compat` |
| Both factor-set components descend | Actual `blockDatHVK`/`blockDatHV_specK`; the `hf` and `hm` arguments are separate definitional equalities |
| Semidirect-product projection is surjective | Explicit lift of its group coordinate, using surjectivity of `blockProjF` |
| Wild-two condition | `isWildTwo_of_gammaGen`, with the actual lower map's proved surjectivity |
| Scalar H² has cardinality two | `cardH2_of_uniformPushed hsimp` |
| Unramified tau=1 and sigma fixed-point-free | `head_cyclic_of_unramified` and `head_sigma_fixedPointFree` |
| Ramified tau has odd order and is fixed-point-free | `head_tau_ramified_profile` |

In the unramified branch the two additional fixed-point-free power
operators are also proved, not assumed. The private
`unramified_concreteHead_powers_fixedPointFree` transfers to the finite
action image, proves its sigma order divides the original level, and uses
the established resolved-eta and 2-power action theorems. It then transfers
back through action compatibility. Source simplicity is derived from block
simplicity using surjectivity of the supplied lift. The copied helper has
the same argument as the previous boundary proof; it does not strengthen
the public hypotheses.

In particular, the proof does not replace an action-trivial base element by
one in the original group, nor infer descent of an arbitrary central
extension merely from faithful coefficient action.

## 3. The actual full-offset Npc diagonal is retained

The public conclusion is deliberately

```
∃ d0, Nonempty (SourceWallHessian DD rhoN scalarTrivial d0 h).
```

It is not a claim that both sectors have the same diagonal or that `d0=qbar`.
Inspection of [NpcHessianCertificates](../../GQ2/Dyadic/Instances/NpcHessianCertificates.lean)
and [NpcPhaseAdditiveHead](../../GQ2/Dyadic/Instances/NpcPhaseAdditiveHead.lean)
shows the exact branch data:

* The level remains `N=4*exponent(SemiProd DD.C0 DD.Vmod)` and the resolver
  remains `npcResolver N d`. It is not reduced to the exponent of the
  projected head.
* In the unramified sector, with head actions A and B from the resolved eta
  and 2^r powers, `Phi=(1-B⁻¹)⁻¹(1-A⁻¹)`. The normal cochain has
  `x2=Phi x0`, and the coordinate change sends its first head coordinate
  through Phi. The retained diagonal is
  `npcUnramifiedDiagonal base hbase s E alpha r d Phi (Phi.symm a)`.
  Its quadraticity uses the actual normal equation; the graph-factor-set
  terms cancel between both full-offset contributions. It is not the old
  `npcQ0 ∘ Lc⁻¹` slice.
* In the ramified sector, Phi is the additive action of the inverse resolved
  eta power. The retained diagonal is
  `npcRamifiedDiagonal base hbase s tau E alpha r d (Phi.symm a)`, and the
  actual twisted normal cochain is used. The proof keeps its full central
  charge, proves quadraticity, and retains an additive comparison witness.

Both outputs have the full value
`d0(a)+polar qbar a b+sum_j polar qbar u_j v_j`, not merely its polarization
or Gauss sign. There is no x2=0 restriction and no invertible-Lc premise.
The source quotient and full phase equality are preserved by
`sourceWallHessianOfComparison`; the linear change is the additive
comparison's own map. The ramified witness is existential, so this does not
assert equality with an arbitrary separately chosen witness of the old
`Nonempty` comparison.

The attached original phase-cover record has diagonal **d0**, cross pairing
from `DD.dat.f`, and kappa identity `Q(j0(v))=d0(v)`. It does not claim the
generally stronger identity `d0(v)=DD.dat.f(v,v)`. This distinction is
intentional and visible in the original record's type. Its cardinality,
positive Gauss value, quadraticity and nonsingularity are all supplied by
the arbitrary-diagonal wall-handle constructor.

## 4. Compact N preserves the exact existing comparisons

Both compact-N records retain the literal source
`GammaR (2+2*h) q (nCompactW alpha h)`, the caller's rho, projected factor
set, action/factor-set compatibility, wildcard-two condition and existing
sector hypotheses. Their endpoint is the original compact phase
`qbar(a)+polar qbar a b+sum_j polar qbar u_j v_j`.

`compactNUnramifiedComparison_add` and
`compactNRamifiedComparison_add` state additivity of the **named old**
`wPcNComparison_unramifiedHead` and `wPcNComparison_ramifiedHead` maps.
They unfold those definitions and apply `phaseComparison_of_normalForm_add`
to `compactPhaseNormal_add h`. They do not assert additivity for an arbitrary
phase-preserving bijection and do not choose a replacement isometry.

The unramified proof's local `Fintype.ofFinite` on the full coordinate
product aligns the implicit finite-type implementation used by the old
comparison. The elaborated proposition still names that exact comparison.
It introduces neither a caller-supplied Fintype nor a cardinality hypothesis,
and it does not alter the phase map. Both record constructors pass these
same comparisons and their additivity proofs to
`sourceCompactHessianOfComparison`, whose `cov` has the unchanged underlying
function and whose `cov_eq` is the old full phase equality.

The compact-N module is a pair of **projected-head** adapters, not itself a
new branch-free boundary wrapper. Its head hypotheses are exactly those of
the previous comparisons; the existing `wPcNComparison_boundary` derives
the relevant sector data at actual boundary lifts. This scope should remain
visible in publication descriptions.

## 5. Fresh checks and conclusion

Commands run from the campaign tree, with the default runner and no option
overrides:

```
bash /private/tmp/gq2-w360-lean.sh GQ2/Dyadic/Instances/NpcBoundaryHessianCertificates.lean
bash /private/tmp/gq2-w360-lean.sh GQ2/Dyadic/Instances/CompactNHessianCertificates.lean
```

Both exit 0 without warnings. The five in-source axiom prints checked are:

| Public declaration | Exact axiom set |
| --- | --- |
| `npcBoundaryHessian` | standard three |
| `compactNUnramifiedComparison_add` | standard three |
| `compactNRamifiedComparison_add` | standard three |
| `compactNUnramifiedHessian` | standard three |
| `compactNRamifiedHessian` | standard three |

No correctness issue or new mathematical premise was found. The important
scope qualifications are retained `UniformHsimp` at the generic Npc
interface, the existential actual Npc diagonal, and compact-N's head-adapter
scope. This closes original-record packaging at the stated interfaces; it
does not generate the ten-item appendix or certify a synchronized final
export/build tree. No renderer changes were made.
