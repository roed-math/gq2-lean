/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.CohomologyDevissage
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The split part of degree-two coefficient right exactness

An equivariantly split coefficient surjection is automatically surjective on continuous `H²`:
apply the coefficient map induced by the section and then the original coefficient map.  This
elementary observation isolates the genuinely missing CD-2 input to nonsplit finite module
quotients.  No presentation, Tate duality, Euler characteristic, or field realization is used.
-/

namespace GQ2.ContCoh

noncomputable section

variable {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- A continuous equivariant additive right inverse to a coefficient map. -/
structure EquivariantAddSection (g : A →+ B) where
  sect : B →+ A
  continuous_sect : Continuous sect
  sect_equivariant : ∀ (c : G) (b : B), sect (c • b) = c • sect b
  right_inv : ∀ b : B, g (sect b) = b

/-- A continuously and equivariantly split coefficient map is surjective on continuous `H²`.

The proof is on normalized cocycle representatives and therefore does not need a general
functorial-composition theorem for `mapCoeff2`. -/
theorem H2RightExactAt.of_equivariantAddSection
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (S : EquivariantAddSection (G := G) g) : H2RightExactAt g hgC hg := by
  intro y
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := B) y
  let x : H2 G A := mapCoeff2 S.sect S.continuous_sect S.sect_equivariant
    (H2mk G B z)
  refine ⟨x, ?_⟩
  rw [show x = mapCoeff2 S.sect S.continuous_sect S.sect_equivariant
      (H2mk G B z) from rfl]
  rw [mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff]
  apply congrArg (H2mk G B)
  apply Subtype.ext
  funext p
  exact S.right_inv (z.1 p)

/-- The unresolved part of a finite coefficient CD-2 theorem consists only of maps without an
equivariant additive section: split maps are discharged by
`H2RightExactAt.of_equivariantAddSection`. -/
theorem H2RightExactAt.of_nonsplit_or_section
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hnonsplit : (¬ Nonempty (EquivariantAddSection (G := G) g)) →
      H2RightExactAt g hgC hg) :
    H2RightExactAt g hgC hg := by
  by_cases hS : Nonempty (EquivariantAddSection (G := G) g)
  · exact H2RightExactAt.of_equivariantAddSection g hgC hg hS.some
  · exact hnonsplit hS

/-! ## Coefficient composition and its no-go consequence -/

section Composition

variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
  [DistribMulAction G C] [ContinuousSMul G C]

/-- Degree-two coefficient maps compose on continuous cohomology. -/
theorem mapCoeff2_comp
    (f : A →+ B) (hfC : Continuous f)
    (hf : ∀ (c : G) (a : A), f (c • a) = c • f a)
    (g : B →+ C) (hgC : Continuous g)
    (hg : ∀ (c : G) (b : B), g (c • b) = c • g b)
    (x : H2 G A) :
    mapCoeff2 g hgC hg (mapCoeff2 f hfC hf x) =
      mapCoeff2 (g.comp f) (hgC.comp hfC)
        (fun (c : G) (a : A) ↦ by
          simp only [AddMonoidHom.comp_apply]
          rw [hf, hg]) x := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := A) x
  rw [mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff]
  apply congrArg (H2mk G C)
  apply Subtype.ext
  rfl

/-- Surjectivity on `H²` is closed under composition of coefficient maps. -/
theorem h2RightExactAt_comp
    (f : A →+ B) (hfC : Continuous f)
    (hf : ∀ (c : G) (a : A), f (c • a) = c • f a)
    (g : B →+ C) (hgC : Continuous g)
    (hg : ∀ (c : G) (b : B), g (c • b) = c • g b)
    (hRf : H2RightExactAt f hfC hf) (hRg : H2RightExactAt g hgC hg) :
    H2RightExactAt (g.comp f) (hgC.comp hfC)
      (fun (c : G) (a : A) ↦ by
        simp only [AddMonoidHom.comp_apply]
        rw [hf, hg]) := by
  intro z
  obtain ⟨y, hy⟩ := hRg z
  obtain ⟨x, hx⟩ := hRf y
  refine ⟨x, ?_⟩
  rw [← mapCoeff2_comp f hfC hf g hgC hg, hx, hy]

/-- If a composite coefficient map is onto on `H²`, then its second factor already is.
Thus enlarging the source of a nonsplit quotient cannot manufacture right exactness. -/
theorem h2RightExactAt_of_comp
    (f : A →+ B) (hfC : Continuous f)
    (hf : ∀ (c : G) (a : A), f (c • a) = c • f a)
    (g : B →+ C) (hgC : Continuous g)
    (hg : ∀ (c : G) (b : B), g (c • b) = c • g b)
    (hR : H2RightExactAt (g.comp f) (hgC.comp hfC)
      (fun (c : G) (a : A) ↦ by
        simp only [AddMonoidHom.comp_apply]
        rw [hf, hg])) :
    H2RightExactAt g hgC hg := by
  intro z
  obtain ⟨x, hx⟩ := hR z
  refine ⟨mapCoeff2 f hfC hf x, ?_⟩
  rw [mapCoeff2_comp f hfC hf g hgC hg]
  exact hx

/-- Once the first factor is right-exact, the composite has exactly the same `H²`
surjectivity obstruction as the second factor. -/
theorem h2RightExactAt_comp_iff
    (f : A →+ B) (hfC : Continuous f)
    (hf : ∀ (c : G) (a : A), f (c • a) = c • f a)
    (g : B →+ C) (hgC : Continuous g)
    (hg : ∀ (c : G) (b : B), g (c • b) = c • g b)
    (hRf : H2RightExactAt f hfC hf) :
    H2RightExactAt (g.comp f) (hgC.comp hfC)
        (fun (c : G) (a : A) ↦ by
          simp only [AddMonoidHom.comp_apply]
          rw [hf, hg]) ↔
      H2RightExactAt g hgC hg :=
  ⟨h2RightExactAt_of_comp f hfC hf g hgC hg,
    fun hRg ↦ h2RightExactAt_comp f hfC hf g hgC hg hRf hRg⟩

/-- In particular, precomposition by an equivariantly split coefficient map leaves the
remaining right-exactness problem unchanged. -/
theorem h2RightExactAt_comp_iff_of_equivariantAddSection
    (f : A →+ B) (hfC : Continuous f)
    (hf : ∀ (c : G) (a : A), f (c • a) = c • f a)
    (Sf : EquivariantAddSection (G := G) f)
    (g : B →+ C) (hgC : Continuous g)
    (hg : ∀ (c : G) (b : B), g (c • b) = c • g b) :
    H2RightExactAt (g.comp f) (hgC.comp hfC)
        (fun (c : G) (a : A) ↦ by
          simp only [AddMonoidHom.comp_apply]
          rw [hf, hg]) ↔
      H2RightExactAt g hgC hg :=
  h2RightExactAt_comp_iff f hfC hf g hgC hg
    (H2RightExactAt.of_equivariantAddSection f hfC hf Sf)

end Composition

/-! ## Odd action images: the complete split case -/

section OddActionImage

variable {C : Type} [Group C] [Fintype C]
  [DistribMulAction C A] [DistribMulAction C B]
  [DiscreteTopology B]

/-- A surjection of elementary abelian groups has an additive section. -/
theorem exists_addSection_of_two_torsion
    (g : A →+ B) (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hsurj : Function.Surjective g) :
    ∃ s : B →+ A, ∀ b, g (s b) = b := by
  letI : Module (ZMod 2) A :=
    AddCommGroup.zmodModule (fun a ↦ by rw [two_nsmul]; exact hA₂ a)
  letI : Module (ZMod 2) B :=
    AddCommGroup.zmodModule (fun b ↦ by rw [two_nsmul]; exact hB₂ b)
  let gL : A →ₗ[ZMod 2] B := g.toZModLinearMap 2
  obtain ⟨s, hs⟩ := gL.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨s.toAddMonoidHom, fun b ↦ ?_⟩
  have hb := LinearMap.congr_fun hs b
  simpa [gL] using hb

/-- Maschke averaging in characteristic two: when the finite action group has odd order,
every equivariant surjection of elementary coefficient modules splits equivariantly. -/
noncomputable def equivariantAddSection_of_odd_card
    (g : A →+ B) (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hodd : Odd (Fintype.card C)) (hsurj : Function.Surjective g) :
    EquivariantAddSection (G := C) g := by
  classical
  let hsExists := exists_addSection_of_two_torsion g hA₂ hB₂ hsurj
  let s : B →+ A := Classical.choose hsExists
  have hs : ∀ b, g (s b) = b := Classical.choose_spec hsExists
  let avg : B →+ A := {
    toFun := fun b ↦ ∑ c : C, c⁻¹ • s (c • b)
    map_zero' := by simp
    map_add' := by
      intro x y
      simp only [smul_add, map_add, Finset.sum_add_distrib]
  }
  refine {
    sect := avg
    continuous_sect := continuous_of_discreteTopology
    sect_equivariant := ?_
    right_inv := ?_
  }
  · intro d b
    change (∑ c : C, c⁻¹ • s (c • (d • b))) =
      d • ∑ c : C, c⁻¹ • s (c • b)
    rw [Finset.smul_sum,
      ← Equiv.sum_comp (Equiv.mulRight d)
        (fun e : C ↦ d • (e⁻¹ • s (e • b)))]
    apply Finset.sum_congr rfl
    intro c _
    simp [mul_inv_rev, mul_smul]
  · intro b
    change g (∑ c : C, c⁻¹ • s (c • b)) = b
    rw [map_sum]
    simp_rw [hg, hs]
    simp only [inv_smul_smul, Finset.sum_const, Finset.card_univ]
    exact GQ2.odd_nsmul_eq_self hB₂ hodd b

/-- Pull an equivariant section back along a homomorphism of acting groups. -/
def EquivariantAddSection.pullback
    {G : Type} [Group G] [DistribMulAction G A] [DistribMulAction G B]
    {g : A →+ B}
    (rho : G →* C)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b)
    (S : EquivariantAddSection (G := C) g) :
    EquivariantAddSection (G := G) g where
  sect := S.sect
  continuous_sect := S.continuous_sect
  sect_equivariant x b := by
    calc
      S.sect (x • b) = S.sect (rho x • b) := congrArg S.sect (hcompatB x b)
      _ = rho x • S.sect b := S.sect_equivariant (rho x) b
      _ = x • S.sect b := (hcompatA x (S.sect b)).symm
  right_inv := S.right_inv

end OddActionImage

section OddActionImageH2

variable {C : Type} [Group C] [Fintype C]
  [DistribMulAction C A] [DistribMulAction C B]
  [DiscreteTopology B]

/-- A coefficient quotient whose action factors through an odd finite group is automatically
surjective on continuous `H²`.  Hence only even-order action images can contribute to the
remaining CD-2 bottleneck. -/
theorem H2RightExactAt.of_odd_finite_action
    (rho : G →* C)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b)
    (g : A →+ B) (hgC : Continuous g)
    (hgCeq : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hodd : Odd (Fintype.card C)) (hsurj : Function.Surjective g) :
    H2RightExactAt g hgC
      (fun x a ↦ by rw [hcompatA, hgCeq, hcompatB]) := by
  let S0 : EquivariantAddSection (G := C) g :=
    equivariantAddSection_of_odd_card g hgCeq hA₂ hB₂ hodd hsurj
  let S : EquivariantAddSection (G := G) g :=
    S0.pullback rho hcompatA hcompatB
  exact H2RightExactAt.of_equivariantAddSection g hgC
    (fun x a ↦ by rw [hcompatA, hgCeq, hcompatB]) S

end OddActionImageH2

end

end GQ2.ContCoh
