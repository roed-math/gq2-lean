/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLTateProviderCore
import GQ2.Dyadic.Instances.GammaLActionImageDevissage
import GQ2.Dyadic.Instances.GammaLSimpleDirectSurjectivity
import GQ2.Dyadic.Instances.LH2ComparisonDevissage
import GQ2.Dyadic.Instances.GammaLH2RightExact

/-!
# Tate duality from the `GammaL` degree-two right-exactness supply

This file closes the coefficientwise part of the direct Tate-duality construction.  For a
finite elementary `GammaL`-module `M`, it uses the actual finite action image `C_M`.  The map
`GammaL -> C_M` is surjective, so the direct simple-coefficient theorem and coefficient
devissage prove both the primal and dual flexible `H^2` comparisons at the uniform word for
`C_M`.  The scalar comparison is oriented directly, and action-image Stokes duality supplies
the independent word-level input.

The exponent and finite target are deliberately allowed to depend on `M`.  This is the natural
output of the action-image construction and avoids enlarging the target to the full additive
automorphism group, where the action map need not be surjective.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven GQ2.LocalLiftingDuality
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

/-! ## The action-image precursor -/

private theorem continuousSMul_comp_actionImage
    {G C A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- The source contragredient action is the pullback of the action-image contragredient
action. -/
theorem finiteActionImageHom_elemDual_smul
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (gamma h q : Type) M]
    [ContinuousSMul (gamma h q : Type) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    (g : (gamma h q : Type)) (lam : ElemDual M) :
    g • lam = finiteActionImageHom h q M g • lam := by
  apply ElemDual.ext
  intro m
  rw [ElemDual.smul_apply]
  change lam (g⁻¹ • m) = lam ((finiteActionImageHom h q M g)⁻¹ • m)
  rw [← map_inv]
  rw [finiteActionImageHom_smul]

/-- The all-coefficient devissage theorem in the instance signature used by a caller.  The
published devissage theorem installs the pullback action definitionally; this corollary uses
the supplied compatibility proof to identify an arbitrary discrete source action with that
pullback action. -/
theorem lModuleH2WordFlexible_bijective_of_simple_and_rightExact_compatible
    {h q : ℕ} {C A : Type}
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom (gamma h q : Type) C)
    (hsimple : UniformSimpleH2SurjectiveSingleProvider rho)
    (hright : GammaLH2RightExactSupply h q)
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (gamma h q : Type) A]
    [ContinuousSMul (gamma h q : Type) A]
    [DistribMulAction C A] [Finite A]
    (hcompat : ∀ (g : (gamma h q : Type)) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0) :
    Function.Bijective
      (lModuleH2WordFlexible rho hcompat hA₂
        (lUniform_wordLift_resolver hA₂)) := by
  have htop : (inferInstance : TopologicalSpace A) = ⊥ := DiscreteTopology.eq_bot
  cases htop
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  have hact : (inferInstance : DistribMulAction (gamma h q : Type) A) =
      DistribMulAction.compHom A rho.toMonoidHom := by
    apply DistribMulAction.ext
    funext g a
    exact hcompat g a
  cases hact
  letI : DistribMulAction (gamma h q : Type) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul (gamma h q : Type) A :=
    continuousSMul_comp_actionImage rho (fun _ _ ↦ rfl)
  change Function.Bijective
    (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hA₂
      (lUniform_wordLift_resolver hA₂))
  exact lModuleH2WordFlexible_bijective_of_simple_and_rightExact
    rho hsimple hright A hA₂

/-- The direct scalar-surjectivity theorem in the instance signature of a caller whose source
scalar action is merely known to be trivial. -/
theorem lUniform_scalarH2WordFlexible_surjective_of_trivialSource
    {h q : ℕ} {C : Type}
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom (gamma h q : Type) C) (hq : Even q)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (ZMod 2)]
    [ContinuousSMul (gamma h q : Type) (ZMod 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s) :
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompat : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = rho g • s :=
      fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
    Function.Surjective
      (lScalarH2WordFlexible rho hcompat
        (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
          (fourMulExponent_ne_zero_and_even C).2)) := by
  have htop : (inferInstance : TopologicalSpace (ZMod 2)) = ⊥ := DiscreteTopology.eq_bot
  cases htop
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have hact : (inferInstance : DistribMulAction (gamma h q : Type) (ZMod 2)) =
      scalarActionZmodTwo (gamma h q : Type) := by
    apply DistribMulAction.ext
    funext g s
    exact htriv g s
  cases hact
  letI : DistribMulAction (gamma h q : Type) (ZMod 2) :=
    scalarActionZmodTwo (gamma h q : Type)
  letI : ContinuousSMul (gamma h q : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul (gamma h q : Type)
  exact lUniform_scalarH2WordFlexible_surjective_of_actionImage rho hq

/-- `GammaLH2RightExactSupply` constructs the strongest natural coefficientwise precursor:
the finite target is the actual action image and the word exponent is its uniform resolving
exponent.  All four mathematical fields of `LModuleTatePrecursor` are theorems. -/
noncomputable def lActionImageModuleTatePrecursor_of_rightExact
    {h q : ℕ} (hq : Even q) (hright : GammaLH2RightExactSupply h q)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (gamma h q : Type) M]
    [ContinuousSMul (gamma h q : Type) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul (gamma h q : Type) (ElemDual M)]
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (ZMod 2)]
    [ContinuousSMul (gamma h q : Type) (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s)
    (hM₂ : ∀ m : M, m + m = 0) :
    let C := FiniteActionImage h q M
    let rho := finiteActionImageHom h q M
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompatM : ∀ (g : (gamma h q : Type)) (m : M), g • m = rho g • m :=
      fun g m ↦ (finiteActionImageHom_smul g m).symm
    let hcompatDual : ∀ (g : (gamma h q : Type)) (lam : ElemDual M),
        g • lam = rho g • lam := finiteActionImageHom_elemDual_smul
    let hcompatScalar : ∀ (g : (gamma h q : Type)) (s : ZMod 2),
        g • s = rho g • s :=
      fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
    LModuleTatePrecursor rho hcompatM hcompatDual hcompatScalar
      htriv hM₂ hq
        (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
          (fourMulExponent_ne_zero_and_even C).2) := by
  let C := FiniteActionImage h q M
  let rho : ContinuousMonoidHom (gamma h q : Type) C := finiteActionImageHom h q M
  let e := omega2Exp (4 * Monoid.exponent C)
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : DistribMulAction (FiniteActionImage h q M) (ZMod 2) :=
    scalarActionZmodTwo (FiniteActionImage h q M)
  let hcompatM : ∀ (g : (gamma h q : Type)) (m : M), g • m = rho g • m :=
    fun g m ↦ (finiteActionImageHom_smul g m).symm
  let hcompatDual : ∀ (g : (gamma h q : Type)) (lam : ElemDual M),
      g • lam = rho g • lam := finiteActionImageHom_elemDual_smul
  let hcompatScalar : ∀ (g : (gamma h q : Type)) (s : ZMod 2),
      g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  let he : Odd e := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  let S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := M) :=
    ⟨resolvesAt_lSqFam_uniformHeis hM₂ h q⟩
  have hrho : Function.Surjective rho :=
    (finiteActionHom (G := (gamma h q : Type)) (M := M)).toMonoidHom.rangeRestrict_surjective
  have hsimple : UniformSimpleH2SurjectiveSingleProvider rho :=
    uniformSimpleH2SurjectiveSingleProvider_of_surjective rho hrho hq
  refine
    { squares := S
      h2A_surjective := ?_
      h2Dual_surjective := ?_
      h2Scalar_surjective := ?_
      stokes := ?_ }
  · exact (lModuleH2WordFlexible_bijective_of_simple_and_rightExact_compatible
      rho hsimple hright hcompatM hM₂).2
  · exact (lModuleH2WordFlexible_bijective_of_simple_and_rightExact_compatible
      rho hsimple hright hcompatDual (fun lam ↦ lam.add_self_eq_zero)).2
  · exact lUniform_scalarH2WordFlexible_surjective_of_trivialSource rho hq htriv
  · exact finiteActionImage_stokesDuality hM₂ hq

/-! ## Target- and exponent-independent cup assembly -/

set_option maxHeartbeats 800000 in
/-- A coefficientwise precursor at any finite target and any odd resolving exponent proves the
three cup clauses in the exact `MuDual`/`MuN` spelling of `TateDualityG`.  In particular, the
finite target and exponent need not be shared by different coefficient modules. -/
theorem LModuleTatePrecursor.tateCupBijections
    {h q e : ℕ} {C M : Type}
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction (gamma h q : Type) M]
    [ContinuousSMul (gamma h q : Type) M]
    [DistribMulAction C M]
    [TopologicalSpace (ElemDual M)] [IsTopologicalAddGroup (ElemDual M)]
    [DiscreteTopology (ElemDual M)]
    [ContinuousSMul (gamma h q : Type) (ElemDual M)]
    [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
    [DiscreteTopology (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (ZMod 2)]
    [ContinuousSMul (gamma h q : Type) (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    [DistribMulAction C (ZMod 2)]
    (rho : ContinuousMonoidHom (gamma h q : Type) C)
    (hcompatM : ∀ (g : (gamma h q : Type)) (m : M), g • m = rho g • m)
    (hcompatDual : ∀ (g : (gamma h q : Type)) (lam : ElemDual M),
      g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : (gamma h q : Type)) (s : ZMod 2),
      g • s = rho g • s)
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s)
    (invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2)
    (hM₂ : ∀ m : M, m + m = 0)
    (hq : Even q) (he : Odd e)
    (D : LModuleTatePrecursor rho hcompatM hcompatDual hcompatScalar
      htriv hM₂ hq he) :
    Function.Bijective (fun c : H0 (gamma h q : Type) (MuDual 2 M) ↦
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H1 (gamma h q : Type) (MuDual 2 M) ↦
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup11 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H2 (gamma h q : Type) (MuDual 2 M) ↦
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup20 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) := by
  let hpair := dualEval_equivariant_of_trivial (M := M) htriv
  let hr := lSource_rel_death rho D.squares.hres
  let h0M := lSourceH0Equiv rho hcompatM
  let h1M := lSourceH1Equiv rho hcompatM hM₂ D.squares.hres
  let h0Dual := lSourceH0Equiv rho hcompatDual
  let h1Dual := lSourceH1Equiv rho hcompatDual
    (fun lam : ElemDual M ↦ lam.add_self_eq_zero) D.squares.hresDual
  let core := D.core
  let hcups := SourceComparisonCore.sourceCupBijections_of_stokesDuality
    (c := fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
    (w := lSqFam h q e) (hr := hr) (hend := lSq_isStokesEndpoint hq he)
    (hpair := hpair) core D.stokes
  letI : Finite (H0 (gamma h q : Type) M) :=
    Finite.of_equiv _ h0M.symm.toEquiv
  letI : Finite (H1 (gamma h q : Type) M) :=
    Finite.of_equiv _ h1M.symm.toEquiv
  letI : Finite (H2 (gamma h q : Type) M) :=
    Finite.of_equiv _ core.h2A.symm.toEquiv
  letI : Finite (H0 (gamma h q : Type) (ElemDual M)) :=
    Finite.of_equiv _ h0Dual.symm.toEquiv
  letI : Finite (H1 (gamma h q : Type) (ElemDual M)) :=
    Finite.of_equiv _ h1Dual.symm.toEquiv
  letI : Finite (H2 (gamma h q : Type) (ElemDual M)) :=
    Finite.of_equiv _ core.h2Dual.symm.toEquiv
  letI : Finite (H2 (gamma h q : Type) (ZMod 2)) :=
    Finite.of_equiv _ invZ.symm.toEquiv
  let e0 := H0congr dualAddEquiv (edEquivariantG hpair htriv)
  let e1 := H1congr dualAddEquiv (edEquivariantG hpair htriv)
  let e2 := H2congr dualAddEquiv (edEquivariantG hpair htriv)
  let psi02 := cup02 (dualEval M).flip (flip_equivariant (dualEval M) hpair)
  let psi11 := cup11 (dualEval M).flip (flip_equivariant (dualEval M) hpair)
  let psi20 := cup20 (dualEval M).flip (flip_equivariant (dualEval M) hpair)
  have hpsi02 : Function.Bijective psi02 := by
    apply transpose_bijective_of_bijective
      (H2_two_torsionG hM₂)
      (fun x : H0 (gamma h q : Type) (ElemDual M) ↦
        Subtype.ext (by simpa using ElemDual.add_self_eq_zero x.1))
      invZ (cup20 (dualEval M) hpair) psi02 hcups.2.2
    intro v w
    exact (cup20_eq_cup02_flip (dualEval M) hpair v w).symm
  have hpsi11 : Function.Bijective psi11 := by
    apply transpose_bijective_of_bijective
      (H1_two_torsionG hM₂) (H1_two_torsionG ElemDual.add_self_eq_zero)
      invZ (cup11 (dualEval M) hpair) psi11 hcups.2.1
    intro v w
    exact (cup11_comm (dualEval M) hpair
      (fun s : ZMod 2 ↦ CharTwo.add_self_eq_zero s) v w).symm
  have hpsi20 : Function.Bijective psi20 := by
    apply transpose_bijective_of_bijective
      (fun x : H0 (gamma h q : Type) M ↦ Subtype.ext (by simpa using hM₂ x.1))
      (H2_two_torsionG ElemDual.add_self_eq_zero)
      invZ (cup02 (dualEval M) hpair) psi20 hcups.1
    intro v w
    exact (cup02_eq_cup20_flip (dualEval M) hpair v w).symm
  constructor
  · apply pairing_bijective_of_transport e0 invZ psi02 _ hpsi02
    intro c d
    change invZ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
      (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c d)) =
        invZ (cup02 (dualEval M).flip (flip_equivariant (dualEval M) hpair) (e0 c) d)
    rw [H2congr_cup02_muDualPairing htriv hpair]
  constructor
  · apply pairing_bijective_of_transport e1 invZ psi11 _ hpsi11
    intro c d
    change invZ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
      (cup11 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c d)) =
        invZ (cup11 (dualEval M).flip (flip_equivariant (dualEval M) hpair) (e1 c) d)
    rw [H2congr_cup11_muDualPairing htriv hpair]
  · apply pairing_bijective_of_transport e2 invZ psi20 _ hpsi20
    intro c d
    change invZ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
      (cup20 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c d)) =
        invZ (cup20 (dualEval M).flip (flip_equivariant (dualEval M) hpair) (e2 c) d)
    rw [H2congr_cup20_muDualPairing htriv hpair]

/-! ## Direct scalar orientation and the Tate bundle -/

/-- The common scalar orientation, constructed directly at the scalar action image.  This
definition uses scalar map surjectivity and the explicit L word trace; it does not use the
right-exactness supply or any coefficient cup-product theorem. -/
noncomputable def lActionImageScalarOrientation
    {h q : ℕ} (hq : Even q)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (ZMod 2)]
    [ContinuousSMul (gamma h q : Type) (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s) :
    H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2 := by
  letI : TopologicalSpace (ElemDual (ZMod 2)) := ⊥
  letI : DiscreteTopology (ElemDual (ZMod 2)) := ⟨rfl⟩
  letI : ContinuousSMul (gamma h q : Type) (ElemDual (ZMod 2)) :=
    finiteElemDualContinuousSMul
  let C := FiniteActionImage h q (ZMod 2)
  let rho : ContinuousMonoidHom (gamma h q : Type) C :=
    finiteActionImageHom h q (ZMod 2)
  let e := omega2Exp (4 * Monoid.exponent C)
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompat : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  let he : Odd e := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  let S : LFlexibleEulerTateSquares
      (h := h) (q := q) (e := e) (C := C) (A := ZMod 2) :=
    ⟨resolvesAt_lSqFam_uniformHeis (fun s : ZMod 2 ↦ CharTwo.add_self_eq_zero s) h q⟩
  let hr := lSource_rel_death rho S.hres
  let hsurj := lUniform_scalarH2WordFlexible_surjective_of_trivialSource rho hq htriv
  exact lScalarH2TraceEquiv_of_surjective rho hcompat hq he hr hsurj

set_option maxHeartbeats 1200000 in
/-- Apply the action-image precursor to one arbitrary finite exponent-two coefficient and
assemble the three Tate cup bijections. -/
theorem actionImageTateCupBijections_of_rightExact
    {h q : ℕ} (hq : Even q) (hright : GammaLH2RightExactSupply h q)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (ZMod 2)]
    [ContinuousSMul (gamma h q : Type) (ZMod 2)]
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s)
    (invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (gamma h q : Type) M]
    [ContinuousSMul (gamma h q : Type) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) :
    Function.Bijective (fun c : H0 (gamma h q : Type) (MuDual 2 M) ↦
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H1 (gamma h q : Type) (MuDual 2 M) ↦
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup11 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H2 (gamma h q : Type) (MuDual 2 M) ↦
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup20 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) := by
  letI : TopologicalSpace (ElemDual M) := ⊥
  letI : DiscreteTopology (ElemDual M) := ⟨rfl⟩
  letI : ContinuousSMul (gamma h q : Type) (ElemDual M) :=
    finiteElemDualContinuousSMul
  let C := FiniteActionImage h q M
  let rho : ContinuousMonoidHom (gamma h q : Type) C := finiteActionImageHom h q M
  let e := omega2Exp (4 * Monoid.exponent C)
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatM : ∀ (g : (gamma h q : Type)) (m : M), g • m = rho g • m :=
    fun g m ↦ (finiteActionImageHom_smul g m).symm
  let hcompatDual : ∀ (g : (gamma h q : Type)) (lam : ElemDual M),
      g • lam = rho g • lam := finiteActionImageHom_elemDual_smul
  let hcompatScalar : ∀ (g : (gamma h q : Type)) (s : ZMod 2),
      g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  let he : Odd e := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  let D := lActionImageModuleTatePrecursor_of_rightExact hq hright M htriv hM₂
  exact D.tateCupBijections rho hcompatM hcompatDual hcompatScalar
    htriv invZ hM₂ hq he

/-- The end-to-end theorem: the continuous `H^2` right-exactness tail for finite elementary
coefficients implies full Tate duality for `GammaL`.  Targets and resolving exponents are
chosen coefficientwise from the actual finite action images. -/
noncomputable def tateDualityG_of_gammaLH2RightExactSupply
    {h q : ℕ} (hq : Even q) (hright : GammaLH2RightExactSupply h q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)] :
    TateDualityG (gamma h q : Type) 2 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction (gamma h q : Type) (ZMod 2) :=
    scalarActionZmodTwo (gamma h q : Type)
  letI : ContinuousSMul (gamma h q : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul (gamma h q : Type)
  let htriv := scalarActionZmodTwo_triv (gamma h q : Type)
  let invZ := lActionImageScalarOrientation hq htriv
  refine
    { inv := (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ
      perfect02 := ?_
      perfect11 := ?_
      perfect20 := ?_ }
  · intro M _ _ _ _ _ _ htor
    have hM₂ : ∀ m : M, m + m = 0 := fun m ↦ by
      simpa only [two_nsmul] using htor m
    exact (actionImageTateCupBijections_of_rightExact
      hq hright htriv invZ M hM₂).1
  · intro M _ _ _ _ _ _ htor
    have hM₂ : ∀ m : M, m + m = 0 := fun m ↦ by
      simpa only [two_nsmul] using htor m
    exact (actionImageTateCupBijections_of_rightExact
      hq hright htriv invZ M hM₂).2.1
  · intro M _ _ _ _ _ _ htor
    have hM₂ : ∀ m : M, m + m = 0 := fun m ↦ by
      simpa only [two_nsmul] using htor m
    exact (actionImageTateCupBijections_of_rightExact
      hq hright htriv invZ M hM₂).2.2

/-! ## The H⁰--H² fragment is sufficient for the improved L presentation -/

/-- At even `q`, the `(0,2)` perfectness fragment already reconstructs the complete Tate
duality bundle for the improved L presentation.  The route is

`H02PerfectDualityG -> GammaLH2RightExactSupply -> TateDualityG`.

Thus neither `(1,1)` nor `(2,0)` perfectness is used as an input. -/
noncomputable def tateDualityG_of_h02PerfectDualityG
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (D : H02PerfectDualityG (gamma h q : Type)) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (finiteTwoH2RightExactSupply_of_h02PerfectDualityG D)

private theorem h02PerfectDualityG_eq_of_inv_eq
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
    (D E : H02PerfectDualityG G) (h : D.inv = E.inv) : D = E := by
  cases D with
  | mk invD perfectD =>
    cases E with
    | mk invE perfectE =>
      dsimp at h
      cases h
      rfl

private theorem tateDualityG_eq_of_inv_eq
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
    (D E : TateDualityG G 2) (h : D.inv = E.inv) : D = E := by
  cases D with
  | mk invD perfect02D perfect11D perfect20D =>
    cases E with
    | mk invE perfect02E perfect11E perfect20E =>
      dsimp at h
      cases h
      rfl

/-- Projecting the bundle reconstructed from an H⁰--H² fragment recovers that fragment.
The invariant equivalence is unique because its codomain is `ZMod 2`; the perfectness field is
a proposition. -/
theorem h02PerfectDualityG_projection_reconstruct
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (D : H02PerfectDualityG (gamma h q : Type)) :
    h02PerfectDualityG_of_tateDualityG
      (tateDualityG_of_h02PerfectDualityG hq D) = D := by
  apply h02PerfectDualityG_eq_of_inv_eq
  exact addEquiv_zmodTwo_unique _ _

/-- Reconstructing from the H⁰--H² projection of a full Tate bundle recovers the full
bundle.  This is an equality of proof packages, not a claim that the reconstruction used the
discarded perfectness fields. -/
theorem tateDualityG_reconstruct_projection
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (D : TateDualityG (gamma h q : Type) 2) :
    tateDualityG_of_h02PerfectDualityG hq
      (h02PerfectDualityG_of_tateDualityG D) = D := by
  apply tateDualityG_eq_of_inv_eq
  exact addEquiv_zmodTwo_unique _ _

/-- For the improved L presentation at even `q`, full Tate duality data are equivalent to the
strictly smaller H⁰--H² fragment.  The forward map is the literal forgetful projection; the
inverse is the noncircular right-exactness/action-image reconstruction above. -/
noncomputable def tateDualityGEquivH02PerfectDualityG
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)] :
    TateDualityG (gamma h q : Type) 2 ≃ H02PerfectDualityG (gamma h q : Type) where
  toFun := h02PerfectDualityG_of_tateDualityG
  invFun := tateDualityG_of_h02PerfectDualityG hq
  left_inv := tateDualityG_reconstruct_projection hq
  right_inv := h02PerfectDualityG_projection_reconstruct hq

/-! ## End-to-end carrier regressions -/

/-- A field realization together with the finite elementary `H²` tail on its open subgroup
gives Tate duality for the presented L group.  The only arithmetic input is the subgroup tail,
not Tate duality on `GammaL`. -/
noncomputable def tateDualityG_of_gammaLFieldRealization
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (R : GammaLFieldRealization h q)
    (hsub : FiniteTwoH2RightExactSupply R.subgroup) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_fieldRealization R hsub)

/-- An independently proved topological group equivalence with `GalK`, followed by the
existing B6 local-duality theorem only on `GalK`, gives Tate duality for `GammaL`. -/
noncomputable def tateDualityG_of_gammaLEquivGalK_B6
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K]
    (e : (gamma h q : Type) ≃ₜ* GalK K) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_equiv_galK_B6 K e)

end

end GQ2.Dyadic.LSquare
