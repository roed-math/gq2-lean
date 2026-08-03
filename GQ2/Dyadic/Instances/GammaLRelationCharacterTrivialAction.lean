/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLRelationCharacterVectorwise
import GQ2.Dyadic.Instances.LH2ComparisonDevissage
import GQ2.Dyadic.Count.H2SplitRightExact

/-!
# Refined L relation characters for trivial elementary actions

The direct L theorem supplies every simple elementary coefficient.  For a general elementary
coefficient the remaining obstruction is normally the nonsurjectivity of continuous `H²` along
a nonsplit coefficient quotient.  If the coefficient action is trivial, every additive section
is automatically equivariant, so that obstruction disappears.  Coefficient dévissage therefore
proves the exact finite-cocycle realization theorem, and the cocycle/relation-character inverse
turns it into vectorwise refined relation characters.

This closes all elementary trivial-action coefficients, not only the one-dimensional scalar
coefficient.  The final section packages the honest residual premise: after this result, the
uniform relation-character campaign only has to treat modules on which the finite target acts
nontrivially.  For a `2`-group action those are precisely the genuinely unipotent, nonsplit
extensions that cannot be removed by choosing an equivariant additive section.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

private theorem continuousSMul_comp_trivialAction
    {G C A : Type*} [Monoid G] [TopologicalSpace G]
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

/-! ## Simple modules for a finite `2`-group -/

/-- Every simple finite elementary module for a finite `2`-group has trivial action.

The whole group has a nonzero fixed vector by the `p`-group orbit congruence.  Its fixed
subgroup is stable under the full action (conjugation preserves being fixed), so simplicity
makes every vector fixed.  Thus a nontrivial action of a finite `2`-group on an elementary
module is automatically a nonsimple, genuinely extension-level phenomenon. -/
theorem isSimpleModTwo_trivial_action_of_isPGroup_two
    {C A : Type} [Group C] [Finite C]
    [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hC₂ : IsPGroup 2 C) (hA₂ : ∀ a : A, a + a = 0)
    (hsimple : IsSimpleModTwo C A) :
    ∀ (c : C) (a : A), c • a = a := by
  haveI : Nontrivial A := hsimple.1
  have hcardA : 2 ∣ Nat.card A := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have hord : addOrderOf a = 2 :=
      addOrderOf_eq_prime (by rw [two_nsmul]; exact hA₂ a) ha
    exact hord ▸ addOrderOf_dvd_natCard a
  have hfix0 : (0 : A) ∈ MulAction.fixedPoints C A := fun c ↦ smul_zero c
  obtain ⟨a, haFix, ha0⟩ :=
    hC₂.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hcardA hfix0
  let W : AddSubgroup A :=
    { carrier := {a | ∀ c : C, c • a = a}
      zero_mem' := fun c ↦ smul_zero c
      add_mem' := fun {a b} ha hb c ↦ by rw [smul_add, ha c, hb c]
      neg_mem' := fun {a} ha c ↦ by rw [smul_neg, ha c] }
  have hstable : ∀ (c : C) (a : A), a ∈ W → c • a ∈ W := by
    intro c a ha g
    calc
      g • (c • a) = (g * c) • a := (mul_smul g c a).symm
      _ = (c * (c⁻¹ * g * c)) • a := by group
      _ = c • ((c⁻¹ * g * c) • a) := mul_smul _ _ _
      _ = c • a := by rw [ha]
  have haW : a ∈ W := fun c ↦ haFix c
  have hWtop : W = ⊤ := by
    rcases hsimple.2 W hstable with hbot | htop
    · exfalso
      rw [hbot, AddSubgroup.mem_bot] at haW
      exact ha0 haW.symm
    · exact htop
  intro c a
  exact (hWtop ▸ AddSubgroup.mem_top a : a ∈ W) c

/-- Contrapositive form used by the residual audit: a genuinely nontrivial elementary action
of a finite `2`-group cannot be simple. -/
theorem not_isSimpleModTwo_of_nontrivial_isPGroup_two_action
    {C A : Type} [Group C] [Finite C]
    [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hC₂ : IsPGroup 2 C) (hA₂ : ∀ a : A, a + a = 0)
    (hnt : ∃ (c : C) (a : A), c • a ≠ a) :
    ¬ IsSimpleModTwo C A := by
  intro hsimple
  obtain ⟨c, a, hca⟩ := hnt
  exact hca (isSimpleModTwo_trivial_action_of_isPGroup_two hC₂ hA₂ hsimple c a)

section TrivialActionComparison

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

set_option maxHeartbeats 2400000 in
/-- The canonical flexible L comparison is bijective for every finite elementary module with
trivial target action.

The proof is composition-series induction.  At a stable submodule `W`, the quotient map
`B → B/W` has an additive section because the coefficients are finite `F₂`-vector spaces.
Both actions are trivial, hence the section is equivariant and
`H2RightExactAt.of_equivariantAddSection` supplies exactly the continuous right-exactness
needed by the four-term comparison chase. -/
theorem lModuleH2WordFlexible_bijective_of_trivial_action
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (c : C) (a : A), c • a = a) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction GammaL A :=
      DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul GammaL A :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hA₂
        (lUniform_wordLift_resolver hA₂)) := by
  let P : ContCoh.FiniteTwoModuleProperty (C := C) := fun B _ _ _ ↦
    ∀ hB₂ : ∀ b : B, b + b = 0,
      (∀ (c : C) (b : B), c • b = b) →
      letI : TopologicalSpace B := ⊥
      letI : DiscreteTopology B := ⟨rfl⟩
      letI : DistribMulAction GammaL B :=
        DistribMulAction.compHom B rho.toMonoidHom
      letI : ContinuousSMul GammaL B :=
        continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
      Function.Bijective
        (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂
          (lUniform_wordLift_resolver hB₂))
  refine (ContCoh.finiteTwoModuleProperty_of_simple P ?_ ?_ ?_ hA₂) hA₂ htriv
  · intro B _ _ _ _
    intro hB₂ _htriv
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := ⟨rfl⟩
    letI : DistribMulAction GammaL B :=
      DistribMulAction.compHom B rho.toMonoidHom
    letI : ContinuousSMul GammaL B :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂
        (lUniform_wordLift_resolver hB₂))
    constructor
    · exact lModuleH2WordFlexible_injective rho (fun _ _ ↦ rfl)
        hB₂ (lUniform_wordLift_resolver hB₂)
    · intro y
      refine ⟨0, ?_⟩
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [map_zero]
      symm
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      rw [show z = 0 from Subsingleton.elim _ _]
      exact AddSubgroup.zero_mem _
  · intro B _ _ _ hB₂ hsimple
    intro hB₂' _htriv
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := ⟨rfl⟩
    letI : DistribMulAction GammaL B :=
      DistribMulAction.compHom B rho.toMonoidHom
    letI : ContinuousSMul GammaL B :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂'
        (lUniform_wordLift_resolver hB₂'))
    exact lModuleH2WordFlexible_bijective_of_surjective rho (fun _ _ ↦ rfl) hB₂'
      (lUniform_wordLift_resolver hB₂')
      (lUniform_simpleH2WordFlexible_surjective_of_surjective
        rho hrho (fun _ _ ↦ rfl) hB₂' hsimple hq)
  · intro B _ _ _ _hB₂ W hWstable _hWbot _hWtop ihW ihQ
    intro hB₂ htrivB
    letI : DistribMulAction C ↑W := stableSubAction W hWstable
    letI : DistribMulAction C (B ⧸ W) := stableQuotAction W hWstable
    have htrivW : ∀ (c : C) (w : ↑W), c • w = w := by
      intro c w
      exact Subtype.ext (htrivB c w.1)
    have htrivQ : ∀ (c : C) (x : B ⧸ W), c • x = x := by
      intro c x
      induction x using QuotientAddGroup.induction_on with
      | H b =>
          change QuotientAddGroup.mk' W (c • b) = QuotientAddGroup.mk' W b
          rw [htrivB]
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := ⟨rfl⟩
    letI : TopologicalSpace ↑W := ⊥
    letI : DiscreteTopology ↑W := ⟨rfl⟩
    letI : TopologicalSpace (B ⧸ W) := ⊥
    letI : DiscreteTopology (B ⧸ W) := ⟨rfl⟩
    letI : DistribMulAction GammaL B := DistribMulAction.compHom B rho.toMonoidHom
    letI : DistribMulAction GammaL ↑W := DistribMulAction.compHom ↑W rho.toMonoidHom
    letI : DistribMulAction GammaL (B ⧸ W) :=
      DistribMulAction.compHom (B ⧸ W) rho.toMonoidHom
    letI : ContinuousSMul GammaL B :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    letI : ContinuousSMul GammaL ↑W :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    letI : ContinuousSMul GammaL (B ⧸ W) :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    let f : ↑W →+ B := W.subtype
    let g : B →+ B ⧸ W := QuotientAddGroup.mk' W
    have hfG : ∀ (c : GammaL) (w : ↑W), f (c • w) = c • f w := fun _ _ ↦ rfl
    have hgG : ∀ (c : GammaL) (b : B), g (c • b) = c • g b := fun _ _ ↦ rfl
    have hfC : ∀ (c : C) (w : ↑W), f (c • w) = c • f w := fun _ _ ↦ rfl
    have hgC : ∀ (c : C) (b : B), g (c • b) = c • g b := fun _ _ ↦ rfl
    let S : FiniteDiscreteCoeffSES (G := GammaL) (A' := ↑W) (A := B)
        (A'' := B ⧸ W) := {
      f := f
      g := g
      f_equivariant := hfG
      g_equivariant := hgG
      f_injective := Subtype.val_injective
      g_surjective := QuotientAddGroup.mk'_surjective W
      range_eq_ker := by
        rw [show f.range = W by ext b; simp [f]]
        exact (QuotientAddGroup.ker_mk' W).symm
    }
    have hW₂ : ∀ w : ↑W, w + w = 0 := two_torsion_sub W hB₂
    have hQ₂ : ∀ x : B ⧸ W, x + x = 0 := two_torsion_quot W hB₂
    obtain ⟨sect, hsect⟩ := exists_addSection_of_two_torsion
      g hB₂ hQ₂ (QuotientAddGroup.mk'_surjective W)
    let coeffSection : EquivariantAddSection (G := GammaL) g := {
      sect := sect
      continuous_sect := continuous_of_discreteTopology
      sect_equivariant := by
        intro x b
        rw [show x • b = b from htrivQ (rho x) b,
          show x • sect b = sect b from htrivB (rho x) (sect b)]
      right_inv := hsect
    }
    let hresW := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hW₂
    let hresB := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hB₂
    let hresQ := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hQ₂
    let c := fun i ↦ rho (genL i)
    have hr : ∀ k, FreeGroup.lift c (wC k) = 1 := fun k ↦
      lower_rel (A := B) rho (fun _ ↦ rfl)
        (isAdmissibleMarkedPresentation_gammaR
          (2 * h + 1) q (Words.LSq.lSqW h)) hresB k
    have hrightS : H2RightExactAt S.g S.continuous_g S.g_equivariant :=
      H2RightExactAt.of_equivariantAddSection g continuous_of_discreteTopology hgG coeffSection
    have ihW' := ihW hW₂ htrivW
    have ihQ' := ihQ hQ₂ htrivQ
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hW₂ hresW) at ihW'
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hQ₂ hresQ) at ihQ'
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂ hresB)
    exact ContCoh.fourTermComparison_bijective
      S.delta1
      (mapCoeff2 S.f S.continuous_f S.f_equivariant)
      (mapCoeff2 S.g S.continuous_g S.g_equivariant)
      (S.wordDelta1 c wC hfC hgC hr)
      (S.wordH2MapF c wC hfC)
      (S.wordH2MapG c wC hgC)
      (lSourceH1Equiv rho (fun _ _ ↦ rfl) hQ₂ hresQ)
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hW₂ hresW)
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂ hresB)
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hQ₂ hresQ)
      (fun x ↦ (l_delta1_comparison S rho (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl) hW₂ hQ₂ hresW hresB hresQ hfC hgC x).symm)
      (fun x ↦ (lModuleH2WordFlexible_natural rho (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        hW₂ hB₂ hresW hresB S.f S.f_equivariant hfC x).symm)
      (fun x ↦ (lModuleH2WordFlexible_natural rho (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        hB₂ hQ₂ hresB hresQ S.g S.g_equivariant hgC x).symm)
      S.exact_left S.exact_middle
      (S.wordH2_exact_left c wC hfC hgC hr)
      (S.wordH2_exact_middle c wC hfC hgC)
      hrightS (lSourceH1Equiv rho (fun _ _ ↦ rfl) hQ₂ hresQ).bijective ihW' ihQ'

/-- Exact finite-cocycle relator realization for every elementary trivial-action coefficient. -/
theorem lModuleRelatorRealization_of_trivial_action
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (c : C) (a : A), c • a = a) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction GammaL A :=
      DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul GammaL A :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    LModuleRelatorRealization (A := A) (e := eC) rho := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
  apply moduleRelatorRealization_of_surjective
    (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (Words.LSq.lSqW h)) rho (fun _ _ ↦ rfl)
    (fun V ↦ hwildLevel_gammaR V) hA₂
    (lFlexibleResolverSystem rho (lUniform_wordLift_resolver hA₂))
  exact (lModuleH2WordFlexible_bijective_of_trivial_action
    rho hrho hq A hA₂ htriv).2

/-- Vectorwise refined relation characters for every elementary trivial-action coefficient.

The quotient and character may depend on the requested relator vector, and the quotient uses
the improved L word with its own exponent, exactly as in the general constructor table. -/
theorem vectorwiseRefinedRelationCharacters_of_trivial_action
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (c : C) (a : A), c • a = a) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction GammaL A :=
      DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul GammaL A :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    VectorwiseRefinedRelationCharacterRealization (A := A) (gen := genL) (W := WL)
      rho (fun i ↦ rho (genL i)) wC := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
  exact (vectorwiseRefinedRelationCharacters_iff_lModuleRelatorRealization
    rho hA₂).2 (lModuleRelatorRealization_of_trivial_action
      rho hrho hq A hA₂ htriv)

/-- At one finite `2`-group target, it suffices to construct finite-cocycle realization for
nonsimple elementary modules.  Every simple module is trivial by the fixed-point theorem, and
the preceding split dévissage handles all trivial modules, of arbitrary dimension. -/
theorem lModuleRelatorRealization_of_nonsimple_pGroup_action
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q) (hC₂ : IsPGroup 2 C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0)
    (hresidual : ¬ IsSimpleModTwo C A →
      letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := ⟨rfl⟩
      letI : DistribMulAction GammaL A :=
        DistribMulAction.compHom A rho.toMonoidHom
      letI : ContinuousSMul GammaL A :=
        continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
      LModuleRelatorRealization (A := A) (e := eC) rho) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction GammaL A :=
      DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul GammaL A :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    LModuleRelatorRealization (A := A) (e := eC) rho := by
  by_cases hsimple : IsSimpleModTwo C A
  · exact lModuleRelatorRealization_of_trivial_action rho hrho hq A hA₂
      (isSimpleModTwo_trivial_action_of_isPGroup_two hC₂ hA₂ hsimple)
  · exact hresidual hsimple

/-- Relation-character form of the fixed `2`-group reduction.  The remaining input is only
finite-cocycle realization for nonsimple modules; the exact inverse equivalence constructs the
quotient-dependent L character witnesses. -/
theorem vectorwiseRefinedRelationCharacters_of_nonsimple_pGroup_action
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q) (hC₂ : IsPGroup 2 C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0)
    (hresidual : ¬ IsSimpleModTwo C A →
      letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := ⟨rfl⟩
      letI : DistribMulAction GammaL A :=
        DistribMulAction.compHom A rho.toMonoidHom
      letI : ContinuousSMul GammaL A :=
        continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
      LModuleRelatorRealization (A := A) (e := eC) rho) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction GammaL A :=
      DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul GammaL A :=
      continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
    VectorwiseRefinedRelationCharacterRealization (A := A) (gen := genL) (W := WL)
      rho (fun i ↦ rho (genL i)) wC := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_trivialAction rho (fun _ _ ↦ rfl)
  exact (vectorwiseRefinedRelationCharacters_iff_lModuleRelatorRealization
    rho hA₂).2 (lModuleRelatorRealization_of_nonsimple_pGroup_action
      rho hrho hq hC₂ A hA₂ hresidual)

end TrivialActionComparison

/-! ## The strictly smaller residual premise -/

section ResidualSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- The remaining relation-realization premise after the trivial-action theorem: only
elementary modules with genuinely nontrivial finite-target action are quantified over. -/
noncomputable abbrev UniformElementaryNontrivialActionRelatorRealizationSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
      (∃ (c : C) (a : A), c • a ≠ a) →
        LModuleRelatorRealization (A := A)
          (e := omega2Exp (4 * Monoid.exponent C)) rho

/-- For even `q`, the nontrivial-action premise is sufficient for the full all-elementary
relator-realization supply.  The complementary branch is the theorem above. -/
theorem uniformElementaryRelatorRealizationSurjectiveSupply_of_nontrivialAction
    (hq : Even q)
    (hresidual : UniformElementaryNontrivialActionRelatorRealizationSupply
      (h := h) (q := q)) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  by_cases htriv : ∀ (c : C) (a : A), c • a = a
  · exact lModuleRelatorRealization_of_trivial_action rho hrho hq A hA₂ htriv
  · push Not at htriv
    exact hresidual C rho hrho A hA₂ htriv

/-- Consequently the same strictly smaller premise constructs the exact vectorwise refined
relation-character supply for the improved L presentation. -/
theorem uniformElementaryVectorwiseRefinedRelationCharacterSupply_of_nontrivialAction
    (hq : Even q)
    (hresidual : UniformElementaryNontrivialActionRelatorRealizationSupply
      (h := h) (q := q)) :
    UniformElementaryVectorwiseRefinedRelationCharacterSupply (h := h) (q := q) :=
  uniformElementaryVectorwiseRefinedRelationCharacterSupply_of_relatorRealization
    (uniformElementaryRelatorRealizationSurjectiveSupply_of_nontrivialAction hq hresidual)

/-- Direct end-to-end constructor: for even `q`, it is enough to solve finite relator
realization for elementary coefficients with nontrivial target action.  Trivial actions are
supplied by the split dévissage theorem in this file. -/
noncomputable def tateDualityG_of_nontrivialActionRelatorRealization
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hresidual : UniformElementaryNontrivialActionRelatorRealizationSupply
      (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_vectorwiseRelationCharacters hq
    (uniformElementaryVectorwiseRefinedRelationCharacterSupply_of_nontrivialAction
      hq hresidual)

/-! ## Q₂ regression -/

/-- At the proved Q₂ row, the full finite-cocycle theorem in particular supplies the new,
strictly smaller nontrivial-action residual premise. -/
theorem uniformElementaryNontrivialActionRelatorRealizationSupply_zero_two :
    UniformElementaryNontrivialActionRelatorRealizationSupply (h := 0) (q := 2) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂ _hnt
  exact uniformElementaryRelatorRealizationSurjectiveSupply_zero_two
    C rho hrho A hA₂

end ResidualSupply

end

end GQ2.Dyadic.LSquare
