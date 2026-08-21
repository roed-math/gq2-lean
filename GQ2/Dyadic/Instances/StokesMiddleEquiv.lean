/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Stokes

/-!
# Stokes quasi-isomorphisms under middle-degree equivalences

A three-term quasi-isomorphism is unchanged when the degree-one terms on both sides of its
ladder are replaced by additively equivalent coordinates.  This is pure homological algebra;
it is independent of a presentation, coefficient module, rank, or dyadic branch.
-/

namespace GQ2.Dyadic

noncomputable section

/-- Transport a three-term Stokes quasi-isomorphism through additive equivalences in degree
one on both sides of the ladder. -/
theorem stokesQuasiIso_iff_middle_addEquiv
    {X₀ X₁ X₁' X₂ Y₀ Y₁ Y₁' Y₂ : Type*}
    [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₁'] [AddCommGroup X₂]
    [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₁'] [AddCommGroup Y₂]
    (dX₀ : X₀ →+ X₁) (dX₁ : X₁ →+ X₂)
    (dX₀' : X₀ →+ X₁') (dX₁' : X₁' →+ X₂)
    (dY₀ : Y₀ →+ Y₁) (dY₁ : Y₁ →+ Y₂)
    (dY₀' : Y₀ →+ Y₁') (dY₁' : Y₁' →+ Y₂)
    (phi₀ : X₀ →+ Y₀) (phi₁ : X₁ →+ Y₁) (phi₂ : X₂ →+ Y₂)
    (phi₁' : X₁' →+ Y₁')
    (eX : X₁ ≃+ X₁') (eY : Y₁ ≃+ Y₁')
    (hX₀ : ∀ x, dX₀' x = eX (dX₀ x))
    (hX₁ : ∀ x, dX₁' (eX x) = dX₁ x)
    (hY₀ : ∀ y, dY₀' y = eY (dY₀ y))
    (hY₁ : ∀ y, dY₁' (eY y) = dY₁ y)
    (hphi₁ : ∀ x, phi₁' (eX x) = eY (phi₁ x)) :
    StokesQuasiIso dX₀ dX₁ dY₀ dY₁ phi₀ phi₁ phi₂ ↔
      StokesQuasiIso dX₀' dX₁' dY₀' dY₁' phi₀ phi₁' phi₂ := by
  constructor
  · intro H
    refine
      { h0_inj := ?_
        h0_surj := ?_
        h1_inj := ?_
        h1_surj := ?_
        h2_inj := ?_
        h2_surj := ?_ }
    · intro x hx hphi
      apply H.h0_inj x
      apply eX.injective
      rw [← hX₀, hx, map_zero]
      exact hphi
    · intro y hy
      have hy' : dY₀ y = 0 := by
        apply eY.injective
        rw [← hY₀, hy, map_zero]
      obtain ⟨x, hx, hxy⟩ := H.h0_surj y hy'
      exact ⟨x, by rw [hX₀, hx, map_zero], hxy⟩
    · intro x hx hboundary
      let x' := eX.symm x
      have hx' : dX₁ x' = 0 := by
        rw [← hX₁, eX.apply_symm_apply, hx]
      obtain ⟨y, hy⟩ := hboundary
      have hy' : dY₀ y = phi₁ x' := by
        apply eY.injective
        rw [← hY₀, ← hphi₁, eX.apply_symm_apply]
        exact hy
      obtain ⟨x₀, hx₀⟩ := H.h1_inj x' hx' ⟨y, hy'⟩
      exact ⟨x₀, by rw [hX₀, hx₀, eX.apply_symm_apply]⟩
    · intro y hy
      let y' := eY.symm y
      have hy' : dY₁ y' = 0 := by
        rw [← hY₁, eY.apply_symm_apply, hy]
      obtain ⟨x, z, hx, hsum⟩ := H.h1_surj y' hy'
      refine ⟨eX x, z, ?_, ?_⟩
      · rw [hX₁, hx]
      · calc
          phi₁' (eX x) + dY₀' z = eY (phi₁ x) + eY (dY₀ z) := by
            rw [hphi₁, hY₀]
          _ = eY (phi₁ x + dY₀ z) := (map_add eY _ _).symm
          _ = eY y' := by rw [hsum]
          _ = y := eY.apply_symm_apply y
    · intro x ⟨y, hy⟩
      let y' := eY.symm y
      have hy' : dY₁ y' = phi₂ x := by
        rw [← hY₁, eY.apply_symm_apply]
        exact hy
      obtain ⟨z, hz⟩ := H.h2_inj x ⟨y', hy'⟩
      exact ⟨eX z, by rw [hX₁, hz]⟩
    · intro y
      obtain ⟨x, z, hz⟩ := H.h2_surj y
      exact ⟨x, eY z, by rw [hY₁, hz]⟩
  · intro H
    refine
      { h0_inj := ?_
        h0_surj := ?_
        h1_inj := ?_
        h1_surj := ?_
        h2_inj := ?_
        h2_surj := ?_ }
    · intro x hx hphi
      apply H.h0_inj x
      rw [hX₀, hx, map_zero]
      exact hphi
    · intro y hy
      have hy' : dY₀' y = 0 := by rw [hY₀, hy, map_zero]
      obtain ⟨x, hx, hxy⟩ := H.h0_surj y hy'
      refine ⟨x, ?_, hxy⟩
      apply eX.injective
      rw [← hX₀, hx, map_zero]
    · intro x hx ⟨y, hy⟩
      have hx' : dX₁' (eX x) = 0 := by rw [hX₁, hx]
      have hy' : dY₀' y = phi₁' (eX x) := by rw [hY₀, hphi₁, hy]
      obtain ⟨z, hz⟩ := H.h1_inj (eX x) hx' ⟨y, hy'⟩
      refine ⟨z, ?_⟩
      apply eX.injective
      rw [← hX₀, hz]
    · intro y hy
      have hy' : dY₁' (eY y) = 0 := by rw [hY₁, hy]
      obtain ⟨x, z, hx, hsum⟩ := H.h1_surj (eY y) hy'
      refine ⟨eX.symm x, z, ?_, ?_⟩
      · rw [← hX₁, eX.apply_symm_apply, hx]
      · apply eY.injective
        calc
          eY (phi₁ (eX.symm x) + dY₀ z) =
              eY (phi₁ (eX.symm x)) + eY (dY₀ z) := map_add eY _ _
          _ = phi₁' x + dY₀' z := by
            rw [← hphi₁, eX.apply_symm_apply, ← hY₀]
          _ = eY y := hsum
    · intro x ⟨y, hy⟩
      have hy' : dY₁' (eY y) = phi₂ x := by rw [hY₁, hy]
      obtain ⟨z, hz⟩ := H.h2_inj x ⟨eY y, hy'⟩
      exact ⟨eX.symm z, by rw [← hX₁, eX.apply_symm_apply, hz]⟩
    · intro y
      obtain ⟨x, z, hz⟩ := H.h2_surj y
      exact ⟨x, eY.symm z, by rw [← hY₁, eY.apply_symm_apply, hz]⟩

#print axioms stokesQuasiIso_iff_middle_addEquiv

end

end GQ2.Dyadic
