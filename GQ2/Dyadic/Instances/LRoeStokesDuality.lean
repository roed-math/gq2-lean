/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.LRoeStokesBridge
import GQ2.Dyadic.Instances.LHandleDuality
import GQ2.Dyadic.Word.StokesTransport

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

/-! ## Transport to the uniform `L_sq` base word -/

section LBase

variable {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- Contravariant transport of elementary duals along an additive equivalence. -/
def elemDualCongr {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) : ElemDual X ≃+ ElemDual Y where
  toFun lam :=
    ((lam : X →+ ZMod 2).comp e.symm.toAddMonoidHom : Y →+ ZMod 2)
  invFun mu :=
    ((mu : Y →+ ZMod 2).comp e.toAddMonoidHom : X →+ ZMod 2)
  left_inv lam := by
    apply ElemDual.ext
    intro x
    exact congrArg lam (e.symm_apply_apply x)
  right_inv mu := by
    apply ElemDual.ext
    intro y
    exact congrArg mu (e.apply_symm_apply y)
  map_add' _ _ := rfl

@[simp] theorem elemDualCongr_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (lam : ElemDual X) (y : Y) :
    elemDualCongr e lam y = lam (e.symm y) := rfl

set_option maxHeartbeats 800000 in
/-- **Roe self-duality proves generic Stokes duality for the uniform `L_sq` base word.**
This is the final `h = 0`, `q = 2` transport: the only changes of coordinates are
`Fin 4 ≃ Generator 1` and `(Fin 2 → A) ≃ A × A`. -/
theorem lSqStokesDuality_zero_two_uniform_of_isSelfDualW
    (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hA₂ : ∀ a : A, a + a = 0) (hsd : IsSelfDualW_R t A) :
    StokesDuality (⇑(Marking.ofQ2 t))
      (Certificates.LSqStokes.lSqFam 0 2
        (omega2Exp (4 * Monoid.exponent C))) A := by
  let w := Certificates.LSqStokes.lSqFam 0 2
    (omega2Exp (4 * Monoid.exponent C))
  have hroe := roeStokesQuasiIso_of_isSelfDualW t ht hw hA₂ hsd
  refine StokesQuasiIso.transport
    (AddEquiv.refl A) q2OffsetsAddEquiv finTwoProdAddEquiv.symm
    (elemDualCongr (finTwoProdAddEquiv (A := ElemDual A)).symm)
    (elemDualCongr (q2OffsetsAddEquiv (A := ElemDual A)))
    (AddEquiv.refl (ElemDual (ElemDual A)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hroe
  · intro a
    exact (heisD0_ofQ2_eq_q2Offsets_d0 t a).symm
  · intro x
    rw [q2OffsetsAddEquiv_apply]
    change ![(FoxH.d1FunR t x).1, (FoxH.d1FunR t x).2] =
      heisD1 (⇑(Marking.ofQ2 t)) w (q2Offsets x)
    exact (heisD1_lSqFam_zero_two_uniform_q2Offsets hA₂ t x).symm
  · intro lam
    apply ElemDual.ext
    intro y
    change
      (dualMap (FoxH.d1R (A := ElemDual A) t) lam) (q2OffsetsInv y) =
        lam (finTwoProdAddEquiv
          (heisD1 (⇑(Marking.ofQ2 t)) w y))
    rw [← q2Offsets_q2OffsetsInv y,
      heisD1_lSqFam_zero_two_uniform_q2Offsets ElemDual.add_self_eq_zero]
    rfl
  · intro lam
    apply ElemDual.ext
    intro a
    change lam (FoxH.d0 t a) = lam (q2OffsetsInv (heisD0 (⇑(Marking.ofQ2 t)) a))
    rw [heisD0_ofQ2_eq_q2Offsets_d0]
    have hcoord : FoxH.d0 t a = q2OffsetsInv (q2Offsets (FoxH.d0 t a)) := by
      funext i
      fin_cases i <;> rfl
    exact congrArg lam hcoord
  · intro a
    apply ElemDual.ext
    intro xi
    change (finTwoProdAddEquiv xi).1 a + (finTwoProdAddEquiv xi).2 a =
      ∑ k, xi k a
    rw [Fin.sum_univ_two]
    rfl
  · intro x
    apply ElemDual.ext
    intro y
    change mixedB_R t x (q2OffsetsInv y) =
      heisEta1 (⇑(Marking.ofQ2 t)) w (q2Offsets x) y
    calc
      mixedB_R t x (q2OffsetsInv y) =
          heisEta1 (⇑(Marking.ofQ2 t)) w (q2Offsets x)
            (q2Offsets (q2OffsetsInv y)) :=
        (heisEta1_lSqFam_zero_two_uniform_q2Offsets hA₂ t x (q2OffsetsInv y)).symm
      _ = heisEta1 (⇑(Marking.ofQ2 t)) w (q2Offsets x) y := by
        rw [q2Offsets_q2OffsetsInv]
  · intro p
    apply ElemDual.ext
    intro lam
    change lam (p.1 + p.2) = lam (∑ k, finTwoProdAddEquiv.symm p k)
    rw [Fin.sum_univ_two]
    rfl

/-- The directly consumable Roe base theorem: `prop_5_15_R` supplies the old self-duality
package, generation converts it to the word-internal form, and the coordinate transport above
proves generic `L_sq` Stokes duality. -/
theorem lSqStokesDuality_zero_two_uniform_of_roe
    (t : _root_.GQ2.Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates) (hA₂ : ∀ a : A, a + a = 0) (hcore : t.Pro2Core) :
    StokesDuality (⇑(Marking.ofQ2 t))
      (Certificates.LSqStokes.lSqFam 0 2
        (omega2Exp (4 * Monoid.exponent C))) A :=
  lSqStokesDuality_zero_two_uniform_of_isSelfDualW t ht hw hA₂
    ((isSelfDual_iff_W_R t hgen).mp (prop_5_15_R t ht hw hgen hA₂ hcore))

end LBase

end

end GQ2.Dyadic
