/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLScalarH2Surjectivity
import GQ2.Dyadic.Instances.GammaLSimpleDualSurjectivity
import GQ2.Dyadic.Instances.LFlexibleH2Naturality

/-!
# Direct simple-coefficient H² surjectivity at a generating finite target

For a simple elementary module over a finite target `C`, and a *surjective* finite
quotient `rho : GammaL → C`, the canonical flexible H² comparison is surjective
without coefficient dévissage or a cohomological-dimension hypothesis.

There are two genuinely different branches.

* If the `C`-action is nontrivial, the marked generators generate `C`, so Stokes
  duality identifies word H² with the dual invariants.  Simplicity and nontriviality
  make those invariants zero; the word H² target is therefore a singleton.
* If the `C`-action is trivial, simplicity forces the elementary additive group to be
  additively equivalent to `ZMod 2`.  Coefficient naturality transports the already
  proved scalar comparison surjectivity through that equivalence.

The surjectivity of `rho` is essential to this argument.  Without it, a simple
`C`-module need not remain simple under the subgroup seen by the marked/source action.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

section EquivalenceTransport

variable {h q e : ℕ} {C A B : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A] [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B] [ContinuousSMul ((gamma h q : Type)) B]
  [DistribMulAction C B]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => lSqFam h q e

/-- Coefficient maps induced on word H² by inverse additive equivalences are inverse. -/
theorem moduleWordH2Map_equiv_left_inverse
    (rho : ContinuousMonoidHom GammaL C)
    (E : A ≃+ B)
    (hEC : ∀ (c : C) (a : A), E (c • a) = c • E a)
    (hE'C : ∀ (c : C) (b : B), E.symm (c • b) = c • E.symm b)
    (x : WordH2 (fun i ↦ rho (genL i)) wL A) :
    moduleWordH2Map (fun i ↦ rho (genL i)) wL E.symm.toAddMonoidHom hE'C
        (moduleWordH2Map (fun i ↦ rho (genL i)) wL E.toAddMonoidHom hEC x) = x := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  apply congrArg (QuotientAddGroup.mk'
    (heisD1 (A := A) (fun i ↦ rho (genL i)) wL).range)
  funext k
  exact E.symm_apply_apply (a k)

/-- Surjectivity of the flexible comparison is invariant under an equivariant additive
equivalence of coefficient modules. -/
theorem lModuleH2WordFlexible_surjective_congr
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatB : ∀ (g : GammaL) (b : B), g • b = rho g • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hresA : ResolvesAt WL wL (WordLift A C))
    (hresB : ResolvesAt WL wL (WordLift B C))
    (E : A ≃+ B)
    (hEG : ∀ (g : GammaL) (a : A), E (g • a) = g • E a)
    (hE'G : ∀ (g : GammaL) (b : B), E.symm (g • b) = g • E.symm b)
    (hEC : ∀ (c : C) (a : A), E (c • a) = c • E a)
    (hE'C : ∀ (c : C) (b : B), E.symm (c • b) = c • E.symm b)
    (hsurj : Function.Surjective
      (lModuleH2WordFlexible rho hcompatB hB₂ hresB)) :
    Function.Surjective (lModuleH2WordFlexible rho hcompatA hA₂ hresA) := by
  intro y
  let yB := moduleWordH2Map (fun i ↦ rho (genL i)) wL E.toAddMonoidHom hEC y
  obtain ⟨xB, hxB⟩ := hsurj yB
  let xA : H2 GammaL A :=
    mapCoeff2 E.symm.toAddMonoidHom continuous_of_discreteTopology hE'G xB
  refine ⟨xA, ?_⟩
  have hnat := lModuleH2WordFlexible_natural rho hcompatB hcompatA hB₂ hA₂
    hresB hresA E.symm.toAddMonoidHom hE'G hE'C xB
  calc
    lModuleH2WordFlexible rho hcompatA hA₂ hresA xA =
        moduleWordH2Map (fun i ↦ rho (genL i)) wL
          E.symm.toAddMonoidHom hE'C
          (lModuleH2WordFlexible rho hcompatB hB₂ hresB xB) := hnat.symm
    _ = moduleWordH2Map (fun i ↦ rho (genL i)) wL
          E.symm.toAddMonoidHom hE'C yB := congrArg _ hxB
    _ = y := moduleWordH2Map_equiv_left_inverse rho E hEC hE'C y

end EquivalenceTransport

section SimpleBranches

variable {h q : ℕ} {C V : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [DiscreteTopology V] [Finite V]
  [DistribMulAction ((gamma h q : Type)) V]
  [ContinuousSMul ((gamma h q : Type)) V]
  [DistribMulAction C V]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

/-- A simple elementary module with trivial action is additively `ZMod 2`. -/
noncomputable def simpleTrivialAddEquivZModTwo
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (htriv : ∀ (c : C) (v : V), c • v = v) : V ≃+ ZMod 2 := by
  letI : Nontrivial V := hsimple.1
  let v : V := Classical.choose (exists_ne (0 : V))
  have hv : v ≠ 0 := Classical.choose_spec (exists_ne (0 : V))
  let phi : ElemDual V := Classical.choose (elemDual_separates hV₂ hv)
  have hphiv : phi v ≠ 0 := Classical.choose_spec (elemDual_separates hV₂ hv)
  have hstable : ∀ (c : C) (a : V), a ∈ (phi : V →+ ZMod 2).ker →
      c • a ∈ (phi : V →+ ZMod 2).ker := by
    intro c a ha
    rw [htriv c a]
    exact ha
  have hker : (phi : V →+ ZMod 2).ker = ⊥ := by
    rcases hsimple.2 (phi : V →+ ZMod 2).ker hstable with hbot | htop
    · exact hbot
    · exfalso
      apply hphiv
      have hvker : v ∈ (phi : V →+ ZMod 2).ker := by
        rw [htop]
        exact AddSubgroup.mem_top v
      exact AddMonoidHom.mem_ker.mp hvker
  have hinj : Function.Injective (phi : V →+ ZMod 2) :=
    (injective_iff_map_eq_zero (phi : V →+ ZMod 2)).mpr (fun a ha ↦ by
      have ha' : a ∈ (phi : V →+ ZMod 2).ker := AddMonoidHom.mem_ker.mpr ha
      rw [hker, AddSubgroup.mem_bot] at ha'
      exact ha')
  have hsurj : Function.Surjective (phi : V →+ ZMod 2) := by
    intro z
    rcases ZMod.eq_zero_or_eq_one z with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · refine ⟨v, ?_⟩
      rcases ZMod.eq_zero_or_eq_one (phi v) with hz | ho
      · exact absurd hz hphiv
      · exact ho
  exact AddEquiv.ofBijective (phi : V →+ ZMod 2) ⟨hinj, hsurj⟩

/-- At a generating target, a nontrivial simple action makes the word H² target
trivial, so the canonical comparison is automatically surjective. -/
theorem lUniform_simpleH2WordFlexible_surjective_of_nontrivial_action
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (hnt : ∃ (c : C) (v : V), c • v ≠ v) (hq : Even q) :
    Function.Surjective
      (lModuleH2WordFlexible rho hcompat hV₂ (lUniform_wordLift_resolver hV₂)) := by
  have hd : StokesDuality (fun i ↦ rho (genL i)) wC V :=
    uniformPushedHsimp_of_actionImage hq C rho V hV₂
  have hr := lUniform_rel_death rho
  have hend : IsStokesEndpoint wC :=
    lSq_isStokesEndpoint hq
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2)
  have hgen : Subgroup.closure (Set.range (fun i ↦ rho (genL i))) = ⊤ :=
    closure_range_lower_eq_top rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) hrho
  have hcard : Nat.card (WordH2 (fun i ↦ rho (genL i)) wC V) = 1 := by
    rw [card_wordH2 hd hr hend, card_ker_heisD0_eq_card_fixedPts hgen,
      card_fixedPts_elemDual_eq_one_of_nontrivial hsimple hnt]
  have hsub : Subsingleton (WordH2 (fun i ↦ rho (genL i)) wC V) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  intro y
  exact ⟨0, hsub.elim _ y⟩

/-- At a trivial simple action, scalar surjectivity transports through the unique
one-dimensional additive coefficient. -/
theorem lUniform_simpleH2WordFlexible_surjective_of_trivial_action
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (htriv : ∀ (c : C) (v : V), c • v = v) (hq : Even q) :
    Function.Surjective
      (lModuleH2WordFlexible rho hcompat hV₂ (lUniform_wordLift_resolver hV₂)) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : IsTopologicalAddGroup (ZMod 2) := by infer_instance
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : DistribMulAction GammaL (ZMod 2) := scalarActionZmodTwo GammaL
  letI : ContinuousSMul GammaL (ZMod 2) := scalarActionZmodTwo_continuousSMul GammaL
  letI : DistribMulAction GammaL (MuN 2) :=
    { smul := fun _ m ↦ m
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl
      smul_zero := fun _ ↦ rfl
      smul_add := fun _ _ _ ↦ rfl }
  letI : ContinuousSMul GammaL (MuN 2) := ⟨continuous_snd⟩
  let E : V ≃+ ZMod 2 := simpleTrivialAddEquivZModTwo hV₂ hsimple htriv
  have hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun _ _ ↦ rfl
  have hEG : ∀ (g : GammaL) (v : V), E (g • v) = g • E v := by
    intro g v
    rw [hcompat, htriv, smul_zmod2]
  have hE'G : ∀ (g : GammaL) (s : ZMod 2), E.symm (g • s) = g • E.symm s := by
    intro g s
    rw [smul_zmod2, hcompat, htriv]
  have hEC : ∀ (c : C) (v : V), E (c • v) = c • E v := by
    intro c v
    rw [htriv, smul_zmod2]
  have hE'C : ∀ (c : C) (s : ZMod 2), E.symm (c • s) = c • E.symm s := by
    intro c s
    rw [smul_zmod2, htriv]
  have he : Odd eC := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  have hscalar : Function.Surjective
      (lModuleH2WordFlexible rho hcompatScalar (by decide)
        (lUniform_wordLift_resolver (C := C) (h := h) (q := q) (by decide))) := by
    have hs := lUniform_scalarH2WordFlexible_surjective_of_actionImage rho hq
    have heq : lScalarH2WordFlexible rho hcompatScalar he =
        lModuleH2WordFlexible rho hcompatScalar (by decide)
          (lUniform_wordLift_resolver (C := C) (h := h) (q := q) (by decide)) := by
      ext x
      obtain ⟨z, rfl⟩ := H2mk_surjective (G := GammaL) (M := ZMod 2) x
      rw [lScalarH2WordFlexible_mk, lModuleH2WordFlexible_mk]
    rw [← heq]
    exact hs
  exact lModuleH2WordFlexible_surjective_congr rho hcompat hcompatScalar hV₂
    (by decide) (lUniform_wordLift_resolver hV₂)
    (lUniform_wordLift_resolver (C := C) (h := h) (q := q) (by decide))
    E hEG hE'G hEC hE'C hscalar

/-- The direct simple-coefficient dichotomy at a surjective finite quotient. -/
theorem lUniform_simpleH2WordFlexible_surjective_of_surjective
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (hq : Even q) :
    Function.Surjective
      (lModuleH2WordFlexible rho hcompat hV₂ (lUniform_wordLift_resolver hV₂)) := by
  by_cases htriv : ∀ (c : C) (v : V), c • v = v
  · exact lUniform_simpleH2WordFlexible_surjective_of_trivial_action
      rho hcompat hV₂ hsimple htriv hq
  · push Not at htriv
    exact lUniform_simpleH2WordFlexible_surjective_of_nontrivial_action
      rho hrho hcompat hV₂ hsimple htriv hq

/-- The strongest provider form justified by the direct dichotomy: the existing
single-map provider for every *surjective* finite quotient. -/
theorem uniformSimpleH2SurjectiveSingleProvider_of_surjective
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q) : UniformSimpleH2SurjectiveSingleProvider rho := by
  intro W _ _ _ _ _ _ _ hcompat hW₂ hsimple
  exact lUniform_simpleH2WordFlexible_surjective_of_surjective
    rho hrho hcompat hW₂ hsimple hq

end SimpleBranches

end

end GQ2.Dyadic.LSquare
