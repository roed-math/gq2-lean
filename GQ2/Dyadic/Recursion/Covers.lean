/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Frame
import GQ2.SectionEight.Covers

/-!
# §8 covers at the `K`-boundary: the two `b`-typed counts (dyadic campaign, ticket SD-R1)

Clone of the **`b`-typed fragment only** of `GQ2/SectionEight/Covers.lean` (315 ln), namely
`exactImageCountOn` (:102) and `liftableCount` (:110).

## Finding: the model file is 96% boundary-free

`GQ2/SectionEight/Covers.lean` mentions a boundary object in exactly those two definitions.
Everything else — `CentralCover.pullTarget` (:44), the corestriction layer
`cmhCodRestrict`/`cmhInclude` (:77,:85), `CentralCover.pCont` (:96), `scalarTwist` (:143), the
whole scalar-twist torsor core (`z_pow_central`, `orderOf_z`, `z_pow_eq_iff`, `p_z`,
`p_z_pow`, `eq_one_or_z_of_mem_ker`, `p_comp_scalarTwist`, `scalarTwist_left_injective`,
`liftDiff`, `scalarTwist_liftDiff`) and `fiberLiftEquiv` (:302) — is stated purely in terms of
`Γ`, the cover `C`, and `Multiplicative (ZMod 2)`.  All of it is therefore **consumed by
import**, unchanged, and the clone is ~60 lines rather than the ~315 the SD1 memo's §4.3 table
budgeted (that table is explicitly an upper bound; memo §4.3 closing note anticipates exactly
this finer split).

This matters beyond line count: `fiberLiftEquiv` is the torsor that produces the literal `8`
in Lemma 8.3, and it is **degree-independent** — the torsor is under `Hom_cont(Γ, 𝔽₂)` for any
`Γ`.  Degree enters only when that hom-count is *evaluated*, which is why `SN.homScalar` is a
value and not a shape (memo §1.1).

Axioms: none beyond std-3; each declaration's print equals its model's.
-/

open scoped Pointwise

namespace GQ2.Dyadic

open GQ2.SectionEight

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

open scoped Classical in
/-- The exact-image count of the `J`-stratum, totalized (`0` when `J` does not project onto
`H`) — the summand shape of the partitions (124)/(138)/(142).  Clone of
`GQ2.SectionEight.exactImageCountOn` (`GQ2/SectionEight/Covers.lean:102`); the only change is
the type of `b`/`F`.  `MarkedTarget.stratum` is the model's, by import. -/
noncomputable def exactImageCountOnK (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y) (J : Subgroup Y) : ℕ :=
  if h : Function.Surjective (T.piY.comp J.subtype) then exactImageCountK b F (T.stratum J h)
  else 0

/-- **`u^β_Γ(p, J)`** (Lemma 8.3): the number of boundary-framed exact-image maps onto the
`J`-stratum whose pullback central cover is **split**.  Clone of
`GQ2.SectionEight.liftableCount` (`GQ2/SectionEight/Covers.lean:110`); the only change is the
type of `b`/`F`.  `CentralCover` and `CentralCover.p` are the model's, by import. -/
noncomputable def liftableCountK (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y) (C : CentralCover Y)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) : ℕ :=
  Nat.card {f : BoundaryLiftsK b F (T.stratum J hJ) //
    ∃ g : ContinuousMonoidHom Γ C.cover, ∀ γ : Γ, C.p (g γ) = (f.1.1 γ : Y)}

/-! ## The `n = 1` refl-bridges -/

omit [DiscreteTopology Y] in
/-- At `n = 1` the totalized stratum count **is** the model's — `rfl`. -/
theorem exactImageCountOnK_eq (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo))
    (F : BoundaryFrameK 2 PiBd H E) (T : MarkedTarget H E Y) (J : Subgroup Y) :
    exactImageCountOnK b F T J = exactImageCountOn b F.toBoundaryFrame T J := rfl

omit [DiscreteTopology Y] in
/-- At `n = 1` the liftable count **is** the model's — `rfl`. -/
theorem liftableCountK_eq (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo))
    (F : BoundaryFrameK 2 PiBd H E) (T : MarkedTarget H E Y) (C : CentralCover Y)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    liftableCountK b F T C J hJ = liftableCount b F.toBoundaryFrame T C J hJ := rfl

end GQ2.Dyadic
