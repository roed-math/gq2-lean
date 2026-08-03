/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.LRoeStokesBridge

/-!
# Roe self-duality as a Stokes quasi-isomorphism

The Roe development packages duality through the three descended pairings `chi0_R`, `chi1_R`,
and `chi2_R`.  The generic dyadic development packages the same assertion as a
`StokesQuasiIso`.  This file identifies the two formulations on Roe's original three-term
complex.  It is deliberately word-independent; the `L_sq` base-word transport belongs in
`LRoeStokesBridge`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH

section RoeLadder

variable {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- Roe's degree-zero evaluation map, before passage to cohomology. -/
def roeEta0 : A →+ ElemDual (ElemDual A × ElemDual A) :=
  AddMonoidHom.mk'
    (fun a ↦ (AddMonoidHom.mk' (fun p : ElemDual A × ElemDual A ↦ p.1 a + p.2 a)
      (fun p q ↦ by
        simp only [Prod.fst_add, Prod.snd_add, ElemDual.add_apply]
        abel_nf) : ElemDual (ElemDual A × ElemDual A)))
    (fun a b ↦ by
      apply ElemDual.ext
      intro p
      change p.1 (a + b) + p.2 (a + b) =
        (p.1 a + p.2 a) + (p.1 b + p.2 b)
      rw [map_add, map_add]
      abel_nf)

/-- Roe's middle Stokes map, bundled from bilinearity of `mixedB_R`. -/
def roeEta1 (t : _root_.GQ2.Marking C) : (Fin 4 → A) →+ ElemDual (Fin 4 → ElemDual A) where
  toFun x :=
    { toFun := fun y ↦ mixedB_R t x y
      map_zero' := mixedB_R_zero_right t x
      map_add' := mixedB_R_add_right t x }
  map_zero' := by
    apply ElemDual.ext
    intro y
    exact mixedB_R_zero_left t y
  map_add' x x' := by
    apply ElemDual.ext
    intro y
    exact mixedB_R_add_left t x x' y

/-- Roe's degree-two evaluation map, before passage to cohomology. -/
def roeEta2 : (A × A) →+ ElemDual (ElemDual A) :=
  AddMonoidHom.mk'
    (fun p ↦ (AddMonoidHom.mk' (fun lam : ElemDual A ↦ lam (p.1 + p.2))
      (fun _ _ ↦ rfl) : ElemDual (ElemDual A)))
    (fun p q ↦ by
      apply ElemDual.ext
      intro lam
      change lam ((p.1 + q.1) + (p.2 + q.2)) =
        lam (p.1 + p.2) + lam (q.1 + q.2)
      rw [add_add_add_comm, map_add])

/-- The left Roe ladder square is exactly Prop. 5.8 left. -/
theorem roe_square_zero (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR) (a : A) :
    dualMap (FoxH.d1R (A := ElemDual A) t) (roeEta0 a)
      = roeEta1 t (FoxH.d0 t a) := by
  apply ElemDual.ext
  intro y
  exact (prop_5_8_left_R t ht hw a y).symm

/-- The right Roe ladder square is exactly Prop. 5.8 right. -/
theorem roe_square_one (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (x : Fin 4 → A) :
    dualMap (FoxH.d0 (A := ElemDual A) t) (roeEta1 t x)
      = roeEta2 (FoxH.d1R t x) := by
  apply ElemDual.ext
  intro lam
  exact prop_5_8_right_R t ht hw x lam

/-- Bijectivity of `g` and of a pointwise-equal composite `g ∘ f` implies bijectivity of `f`. -/
private theorem bijective_of_bijective_comp
    {X Y Z : Type*} {f : X → Y} {g : Y → Z} {h : X → Z}
    (hg : Function.Bijective g) (hh : Function.Bijective h)
    (heq : ∀ x, g (f x) = h x) : Function.Bijective f := by
  constructor
  · intro x y hxy
    apply hh.1
    rw [← heq, ← heq, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hh.2 (g y)
    refine ⟨x, hg.1 ?_⟩
    rw [heq, hx]

/-- Universal coefficients after the Roe degree-zero cohomology map is `chi0_R`. -/
theorem roe_stokesH0_uc (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (a : H0w (A := A) t) :
    stokesUC0 (FoxH.d1R (A := ElemDual A) t)
        (stokesH0Map (roe_square_zero (A := A) t ht hw) a)
      = chi0_R t ht hw a := by
  apply ElemDual.ext
  intro h
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective h
  rfl

/-- Universal coefficients after the Roe degree-one cohomology map is `chi1_R`. -/
theorem roe_stokesH1_uc (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (h : H1wR (A := A) t) :
    stokesUC1 (FoxH.d0 (A := ElemDual A) t) (FoxH.d1R (A := ElemDual A) t)
        (stokesH1Map (roe_square_zero (A := A) t ht hw)
          (roe_square_one (A := A) t ht hw) h)
      = chi1_R t ht hw h := by
  apply ElemDual.ext
  intro h'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective h'
  rfl

/-- Universal coefficients after the Roe degree-two cohomology map is `chi2_R`. -/
theorem roe_stokesH2_uc (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (h : H2wR (A := A) t) :
    stokesUC2 (FoxH.d0 (A := ElemDual A) t)
        (stokesH2Map (roe_square_one (A := A) t ht hw) h)
      = chi2_R t ht hw h := by
  apply ElemDual.ext
  intro lam
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective h
  rfl

set_option maxHeartbeats 800000 in
/-- Roe word-internal self-duality is an actual `StokesQuasiIso` of Roe's three-term ladder. -/
theorem roeStokesQuasiIso_of_isSelfDualW
    (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hA₂ : ∀ a : A, a + a = 0) (hsd : IsSelfDualW_R t A) :
    StokesQuasiIso (FoxH.d0 (A := A) t) (FoxH.d1R t)
      (dualMap (FoxH.d1R (A := ElemDual A) t))
      (dualMap (FoxH.d0 (A := ElemDual A) t))
      roeEta0 (roeEta1 t) roeEta2 := by
  obtain ⟨hchi2, -, hchi0, -, hchi1, -⟩ :=
    chi_bij_of_selfdualW_R t ht hw hA₂ hsd
  apply stokesQuasiIso_of_bijective_cohomology_maps
    (roe_square_zero (A := A) t ht hw) (roe_square_one (A := A) t ht hw)
  · exact bijective_of_bijective_comp
      (stokesUC0_bijective (FoxH.d1R (A := ElemDual A) t)) hchi0
      (roe_stokesH0_uc (A := A) t ht hw)
  · exact bijective_of_bijective_comp
      (stokesUC1_bijective wordDual_two_torsion
        (fun p : ElemDual A × ElemDual A ↦
          Prod.ext p.1.add_self_eq_zero p.2.add_self_eq_zero)
        (FoxH.d0 (A := ElemDual A) t) (FoxH.d1R (A := ElemDual A) t)
        (FoxH.d1FunR_comp_d0 (A := ElemDual A) t ht hw)) hchi1
      (roe_stokesH1_uc (A := A) t ht hw)
  · exact bijective_of_bijective_comp
      (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
        (FoxH.d0 (A := ElemDual A) t)) hchi2
      (roe_stokesH2_uc (A := A) t ht hw)

end RoeLadder

end

end GQ2.Dyadic
