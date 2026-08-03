/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LExact
import GQ2.Dyadic.LiftingDualityG

/-!
# The truth-side boundary for Euler characteristic and Tate duality on `GammaL`

The L source is the abstract profinite presentation

`GammaL = gamma h q = GammaR (2 * h + 1) q (lSqW h)`.

The full field-style lifting/counting pipeline asks for two analytic inputs on this abstract
group:

* `LocalEulerChar GammaL (2 * h + 1)` for every finite discrete coefficient module;
* `TateDualityG GammaL 2`, again quantified over every finite `2`-torsion module.

Neither input follows in the present development from the admissible presentation, the flexible
`H^2` comparison, or the Demushkin calculations.  The flexible comparison is restricted to
elementary `2`-torsion coefficients and becomes an equivalence only after the relevant `H^2`
cardinality is supplied.  `IsDemushkin` records only the scalar `F_2` cup form on a pro-`2`
group.  In contrast, the two inputs above concern the full profinite group and all finite
coefficients.

## The sharper exponent-two boundary

For the improved L source comparison, the full Euler bundle is stronger than necessary.  The
Euler-free finiteness audit is now reflected in Lean as follows:

* the proved `H¹` word equivalences make primal and dual source `H¹` finite;
* the flexible `H²` injections make primal and dual source `H²` finite;
* `bijective_cup02_dualEvalG_of_finite`, `bijective_cup11_dualEvalG_of_finite`, and
  `bijective_cup20_dualEvalG_of_finite` therefore obtain all cup perfectness from
  `TateDualityG` without `LocalEulerChar`;
* scalar `H²` was already Euler-free.

Consequently the exact remaining interface is the pair of non-scalar cardinal equalities in
`sourceComparisonPackage_of_lFlexibleH2_card_tateDuality`; its canonical regression is
`stokesCohomologyBijections_lCanonical_of_card`.  The old full-Euler constructors remain useful
wrappers which supply those two equalities.

The pair cannot presently be removed.  Write dimensions over `F_2` after the proved `H⁰` and
`H¹` comparisons.  Tate `H¹` duality and the two pure word Euler identities imply only

`dim WordH²(A) = dim H⁰(Aᵛ) + r` and
`dim WordH²(Aᵛ) = dim H⁰(A) + r`

for the same `r`; flexible injectivity proves merely `r ≥ 0`.  For a nontrivial simple module
both invariant terms can vanish, so simplicity still does not force `r = 0`.  An independent
word `(2,0)` Stokes theorem, flexible-`H²` surjectivity/asphericity theorem, or coefficient-wise
source Euler equality is exactly what kills this common defect.  Feeding the final source
comparison's own Stokes bijections back into this step would be circular.

This file records the smallest currently available truth-side bridge.  A
`LocalFieldRealization G d` identifies `G` with an open subgroup of `G_Q2` of index `d`.  That is
strictly weaker than a marked presentation theorem identifying `G` with a specified `G_K`, but
it is enough:

* the Euler characteristic transports across the equivalence from the open subgroup theorem;
* the realization makes `G` a `GQ2.IsLocalDualizingGroup`, so foundational B6 applies.

Thus `Nonempty (GammaLFieldRealization h q)` is an exact, non-analytic missing statement from
which both requested bundles follow.  Apart from the independently proved `(h,q) = (0,2)` case,
it is not currently constructed upstream: obtaining it from the general L presentation would
already prove the unmarked carrier part of the desired presentation theorem, so using the final
carrier equivalence to construct it upstream would be circular.

At exponent two there is a slightly more flexible pure reduction:
`isLocalDualizingGroup_two_of_equiv` transports the truth-side predicate along any topological
group equivalence.  The corresponding `tateDualityG_two_of_equiv` is explicitly a B6 constructor,
not a direct transport of a supplied duality bundle.  Such direct transport would additionally
need group-variable naturality for all three cup maps; the current API provides the three
cohomology equivalences but not those cup-natural squares.

## Axiom posture

The transport theorem `LocalEulerChar.congr`, `isLocalDualizingGroup_two_of_equiv`, the
realization-to-local-dualizing theorem, and the combined boundary theorem are pure and print
exactly the standard three.  The bundle constructors expose the existing foundational inputs
honestly: the Euler constructor adds B7 through `localEulerCharacteristic_open`, while
`tateDualityG_two_of_equiv` and the realization Tate constructor add B6 through
`tateDualityAt`.  There are no new axioms and no `sorry`s.
-/

namespace GQ2.Dyadic.LiftingDualityG.LocalEulerChar

noncomputable section

open GQ2 ContCoh GQ2.Dyadic

/-! ## Euler characteristic is invariant under topological group equivalence -/

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- **Euler characteristic transports across a topological group equivalence.**

For a finite discrete `G`-module `M`, give `M` the pulled-back `G'`-action through `e.symm`.
`H0congrGroup`, `H1congrGroup`, and `H2congrGroup` identify the three continuous cohomology
groups, so all finiteness and cardinality clauses transport verbatim. -/
theorem congr (e : G ≃ₜ* G') {d : ℕ} : LocalEulerChar G' d → LocalEulerChar G d := by
  intro hE M _ _ _ _ _ _
  have hcontinuous_smul_G : Continuous (fun p : G × M => p.1 • p.2) := continuous_smul
  letI : DistribMulAction G' M := DistribMulAction.compHom M e.symm.toMonoidHom
  letI : ContinuousSMul G' M := ⟨by
    exact hcontinuous_smul_G.comp
      ((e.symm.continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩
  obtain ⟨hfin0, hfin1, hfin2, hcard⟩ := hE M
  let e0 : H0 G M ≃+ H0 G' M :=
    H0congrGroup e (AddEquiv.refl M) (by
      intro g m
      change g • m = e.symm (e g) • m
      rw [e.symm_apply_apply])
  let e1 : H1 G M ≃+ H1 G' M :=
    H1congrGroup e (AddEquiv.refl M) continuous_id continuous_id (by
      intro g m
      change g • m = e.symm (e g) • m
      rw [e.symm_apply_apply])
  let e2 : H2 G M ≃+ H2 G' M :=
    H2congrGroup e (AddEquiv.refl M) continuous_id continuous_id (by
      intro g m
      change g • m = e.symm (e g) • m
      rw [e.symm_apply_apply])
  refine ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv,
    Finite.of_equiv _ e2.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e0.toEquiv, Nat.card_congr e2.toEquiv]
  exact hcard

end

end GQ2.Dyadic.LiftingDualityG.LocalEulerChar

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Dyadic GQ2.Dyadic.LiftingDualityG

/-! ## The exact equivalence transport available for B6 -/

section DualizingEquiv

variable {G G' : Type} [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G']

/-- At exponent two, a topological group equivalence transports the truth-side local-dualizing
predicate without an action-compatibility hypothesis.

This is the strongest axiom-free transport needed here.  Both actions on `MuN 2` are trivial,
the equivalence is an open embedding with image `⊤`, and that image has finite index.  Notice
that the conclusion is `IsLocalDualizingGroup`, not `TateDualityG`: constructing the latter is
the separate B6 step below. -/
theorem isLocalDualizingGroup_two_of_equiv
    [DistribMulAction G (MuN 2)] [DistribMulAction G' (MuN 2)]
    (e : G ≃ₜ* G') (hG' : IsLocalDualizingGroup G' 2) :
    IsLocalDualizingGroup G 2 := by
  apply isLocalDualizingGroup_of_openEmbedding hG' e.toMonoidHom
    e.toHomeomorph.isOpenEmbedding
  · rw [MonoidHom.range_eq_top.mpr e.surjective]
    infer_instance
  · intro g x
    rw [smul_muN_two_trivialG, smul_muN_two_trivialG]

/-- **B6 after equivalence transport.**  An equivalence to a local-dualizing group reduces full
Tate duality on the source to the existing foundational axiom `tateDualityAt`.

This does not pretend to transport a supplied `TateDualityG` bundle.  Although the repository
has `H0congrGroup`, `H1congrGroup`, and `H2congrGroup`, it has no corresponding naturality
theorems for `cup02`, `cup11`, and `cup20` in the group variable.  B6 is therefore applied to
the transported truth-side predicate rather than silently assuming those missing squares. -/
noncomputable def tateDualityG_two_of_equiv
    [IsTopologicalGroup G]
    [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
    [DistribMulAction G' (MuN 2)]
    (e : G ≃ₜ* G') (hG' : IsLocalDualizingGroup G' 2) : TateDualityG G 2 :=
  tateDualityAt G 2 (isLocalDualizingGroup_two_of_equiv e hG')

end DualizingEquiv

/-! ## A local-field realization and its consequences -/

/-- A truth-side realization of a topological group `G` as a degree-`d` local Galois group.

This deliberately asks only for an unspecified open subgroup of `G_Q2`, rather than a specified
finite extension `K` or any marking data.  It is therefore the weakest field-identification
interface currently sufficient for both the Euler and Tate-duality bundles. -/
structure LocalFieldRealization (G : Type) [Group G] [TopologicalSpace G] (d : ℕ) where
  subgroup : Subgroup AbsGalQ2
  isOpen_subgroup : IsOpen (subgroup : Set AbsGalQ2)
  equiv : G ≃ₜ* subgroup
  index_eq : subgroup.index = d

namespace LocalFieldRealization

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}

omit [IsTopologicalGroup G] in
/-- The realization transports any supplied Euler bundle on its open subgroup to `G`.

This is the standard-three core of the Euler bridge; the canonical open-subgroup bundle is
inserted separately in `localEulerChar` below, keeping B7's entry point visible. -/
theorem transportLocalEulerChar (R : LocalFieldRealization G d)
    (hE : LocalEulerChar R.subgroup R.subgroup.index) : LocalEulerChar G d := by
  rw [← R.index_eq]
  exact GQ2.Dyadic.LiftingDualityG.LocalEulerChar.congr R.equiv hE

omit [IsTopologicalGroup G] in
/-- A local-field realization makes `G` a local dualizing group at `2`.

No action-compatibility field is needed in `LocalFieldRealization`: every distributive group
action on `MuN 2` is trivial, on both sides. -/
theorem isLocalDualizingGroup (R : LocalFieldRealization G d)
    [DistribMulAction G (MuN 2)] : IsLocalDualizingGroup G 2 := by
  haveI : Finite (AbsGalQ2 ⧸ R.subgroup) :=
    finite_quotient_of_isOpen R.subgroup R.isOpen_subgroup
  haveI : R.subgroup.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _ inferInstance
  apply isLocalDualizingGroup_of_openEmbedding
    (subgroup_isLocalDualizingGroup 2 R.subgroup R.isOpen_subgroup)
    R.equiv.toMonoidHom R.equiv.toHomeomorph.isOpenEmbedding
  · rw [MonoidHom.range_eq_top.mpr R.equiv.surjective]
    infer_instance
  · intro g x
    rw [LiftingDualityG.smul_muN_two_trivialG,
      LiftingDualityG.smul_muN_two_trivialG]

omit [IsTopologicalGroup G] in
/-- The exact standard-three boundary: after a local-field realization, the Euler bundle is
reduced to its already-established open-subgroup instance and the Tate bundle is reduced to the
truth-side predicate gating B6. -/
theorem analyticBoundary (R : LocalFieldRealization G d) [DistribMulAction G (MuN 2)] :
    (LocalEulerChar R.subgroup R.subgroup.index → LocalEulerChar G d) ∧
      IsLocalDualizingGroup G 2 :=
  ⟨R.transportLocalEulerChar, R.isLocalDualizingGroup⟩

omit [IsTopologicalGroup G] in
/-- **B7 constructor.**  An open-subgroup realization supplies the full all-coefficient Euler
characteristic on `G`. -/
theorem localEulerChar (R : LocalFieldRealization G d) : LocalEulerChar G d := by
  apply R.transportLocalEulerChar
  haveI : Finite (AbsGalQ2 ⧸ R.subgroup) :=
    finite_quotient_of_isOpen R.subgroup R.isOpen_subgroup
  intro M _ _ _ _ _ _
  exact localEulerCharacteristic_open R.subgroup R.isOpen_subgroup M

/-- **B6 constructor.**  An open-subgroup realization supplies full Tate duality on `G`.

As it must, this calls the existing foundational axiom `tateDualityAt`; the reduction from the
realization to `IsLocalDualizingGroup` is the axiom-free theorem above. -/
noncomputable def tateDualityG (R : LocalFieldRealization G d)
    [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)] : TateDualityG G 2 :=
  tateDualityAt G 2 R.isLocalDualizingGroup

end LocalFieldRealization

/-! ## The exact missing statement for the L source -/

/-- The minimal current truth-side identification needed for the two analytic L-source bundles:
`gamma h q` is some open subgroup of `G_Q2`, of the expected index `2h+1`. -/
abbrev GammaLFieldRealization (h q : ℕ) :=
  LocalFieldRealization (gamma h q : Type) (2 * h + 1)

/-- A `GammaLFieldRealization` supplies the requested all-coefficient Euler characteristic.
The only non-standard axiom in this wrapper is the pre-existing B7. -/
theorem gammaL_localEulerChar {h q : ℕ} (R : GammaLFieldRealization h q) :
    LocalEulerChar (gamma h q : Type) (2 * h + 1) :=
  R.localEulerChar

/-- A `GammaLFieldRealization` supplies the requested full Tate-duality bundle.  The only
non-standard axiom in this wrapper is the pre-existing B6. -/
noncomputable def gammaL_tateDualityG {h q : ℕ} (R : GammaLFieldRealization h q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)] :
    TateDualityG (gamma h q : Type) 2 :=
  R.tateDualityG

end


end GQ2.Dyadic.LSquare
