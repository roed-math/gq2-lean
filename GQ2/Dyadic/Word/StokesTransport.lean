/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Word.Stokes

/-!
# Transport of Stokes quasi-isomorphisms

`StokesQuasiIso` is invariant under degreewise additive equivalence of its source and target
three-term complexes.  The statement is kept at the abstract ladder level so coordinate
reindexings can be discharged once and reused by every word family.
-/

namespace GQ2.Dyadic

section Transport

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ X₀' X₁' X₂' Y₀' Y₁' Y₂' : Type*}
  [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]
  [AddCommGroup X₀'] [AddCommGroup X₁'] [AddCommGroup X₂']
  [AddCommGroup Y₀'] [AddCommGroup Y₁'] [AddCommGroup Y₂']

variable {dX₀ : X₀ →+ X₁} {dX₁ : X₁ →+ X₂} {dY₀ : Y₀ →+ Y₁} {dY₁ : Y₁ →+ Y₂}
  {φ₀ : X₀ →+ Y₀} {φ₁ : X₁ →+ Y₁} {φ₂ : X₂ →+ Y₂}
  {dX₀' : X₀' →+ X₁'} {dX₁' : X₁' →+ X₂'} {dY₀' : Y₀' →+ Y₁'}
  {dY₁' : Y₁' →+ Y₂'} {φ₀' : X₀' →+ Y₀'} {φ₁' : X₁' →+ Y₁'}
  {φ₂' : X₂' →+ Y₂'}

/-- Transport a relative three-term quasi-isomorphism across a degreewise isomorphism of
ladders. -/
theorem StokesQuasiIso.transport
    (eX₀ : X₀ ≃+ X₀') (eX₁ : X₁ ≃+ X₁') (eX₂ : X₂ ≃+ X₂')
    (eY₀ : Y₀ ≃+ Y₀') (eY₁ : Y₁ ≃+ Y₁') (eY₂ : Y₂ ≃+ Y₂')
    (hX₀ : ∀ x, eX₁ (dX₀ x) = dX₀' (eX₀ x))
    (hX₁ : ∀ x, eX₂ (dX₁ x) = dX₁' (eX₁ x))
    (hY₀ : ∀ y, eY₁ (dY₀ y) = dY₀' (eY₀ y))
    (hY₁ : ∀ y, eY₂ (dY₁ y) = dY₁' (eY₁ y))
    (hφ₀ : ∀ x, eY₀ (φ₀ x) = φ₀' (eX₀ x))
    (hφ₁ : ∀ x, eY₁ (φ₁ x) = φ₁' (eX₁ x))
    (hφ₂ : ∀ x, eY₂ (φ₂ x) = φ₂' (eX₂ x))
    (h : StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂) :
    StokesQuasiIso dX₀' dX₁' dY₀' dY₁' φ₀' φ₁' φ₂' := by
  constructor
  · intro x hx hφx
    have hdx : dX₀ (eX₀.symm x) = 0 := by
      apply eX₁.injective
      rw [hX₀, eX₀.apply_symm_apply, hx, map_zero]
    have hηx : φ₀ (eX₀.symm x) = 0 := by
      apply eY₀.injective
      rw [hφ₀, eX₀.apply_symm_apply, hφx, map_zero]
    have := h.h0_inj (eX₀.symm x) hdx hηx
    apply eX₀.symm.injective
    rw [this, map_zero]
  · intro y hy
    have hdy : dY₀ (eY₀.symm y) = 0 := by
      apply eY₁.injective
      rw [hY₀, eY₀.apply_symm_apply, hy, map_zero]
    obtain ⟨x, hx, hφx⟩ := h.h0_surj (eY₀.symm y) hdy
    refine ⟨eX₀ x, ?_, ?_⟩
    · rw [← hX₀, hx, map_zero]
    · rw [← hφ₀, hφx, eY₀.apply_symm_apply]
  · intro x hx hbound
    have hdx : dX₁ (eX₁.symm x) = 0 := by
      apply eX₂.injective
      rw [hX₁, eX₁.apply_symm_apply, hx, map_zero]
    obtain ⟨y, hy⟩ := hbound
    have hbound' : ∃ y₀, dY₀ y₀ = φ₁ (eX₁.symm x) := by
      refine ⟨eY₀.symm y, eY₁.injective ?_⟩
      rw [hY₀, hφ₁, eY₀.apply_symm_apply, eX₁.apply_symm_apply, hy]
    obtain ⟨x₀, hx₀⟩ := h.h1_inj (eX₁.symm x) hdx hbound'
    exact ⟨eX₀ x₀, by rw [← hX₀, hx₀, eX₁.apply_symm_apply]⟩
  · intro y hy
    have hdy : dY₁ (eY₁.symm y) = 0 := by
      apply eY₂.injective
      rw [hY₁, eY₁.apply_symm_apply, hy, map_zero]
    obtain ⟨x, y₀, hx, hsum⟩ := h.h1_surj (eY₁.symm y) hdy
    refine ⟨eX₁ x, eY₀ y₀, ?_, ?_⟩
    · rw [← hX₁, hx, map_zero]
    · rw [← hφ₁, ← hY₀, ← map_add, hsum, eY₁.apply_symm_apply]
  · intro x hbound
    obtain ⟨y, hy⟩ := hbound
    have hbound' : ∃ y₁, dY₁ y₁ = φ₂ (eX₂.symm x) := by
      refine ⟨eY₁.symm y, eY₂.injective ?_⟩
      rw [hY₁, hφ₂, eY₁.apply_symm_apply, eX₂.apply_symm_apply, hy]
    obtain ⟨x₁, hx₁⟩ := h.h2_inj (eX₂.symm x) hbound'
    exact ⟨eX₁ x₁, by rw [← hX₁, hx₁, eX₂.apply_symm_apply]⟩
  · intro y
    obtain ⟨x, y₁, hsum⟩ := h.h2_surj (eY₂.symm y)
    refine ⟨eX₂ x, eY₁ y₁, ?_⟩
    rw [← hφ₂, ← hY₁, ← map_add, hsum, eY₂.apply_symm_apply]

end Transport

/-! ## Stabilization by a middle-degree isomorphism -/

section MiddleStabilization

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ U V : Type*}
  [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]
  [AddCommGroup U] [AddCommGroup V]

/-- Adjoin a summand with zero incoming differential to the middle term of a complex. -/
def middleExtendD0 (d : X₀ →+ X₁) : X₀ →+ X₁ × U := d.prod 0

@[simp] theorem middleExtendD0_apply (d : X₀ →+ X₁) (x : X₀) :
    middleExtendD0 (U := U) d x = (d x, 0) := rfl

/-- Adjoin a summand killed by the outgoing differential to the middle term of a complex. -/
def middleExtendD1 (d : X₁ →+ X₂) : X₁ × U →+ X₂ :=
  d.comp (AddMonoidHom.fst X₁ U)

@[simp] theorem middleExtendD1_apply (d : X₁ →+ X₂) (x : X₁ × U) :
    middleExtendD1 d x = d x.1 := rfl

/-- Extend a middle ladder map by an additive equivalence on the new summand. -/
def middleExtendMap (f : X₁ →+ Y₁) (e : U ≃+ V) : X₁ × U →+ Y₁ × V :=
  (f.comp (AddMonoidHom.fst X₁ U)).prod
    (e.toAddMonoidHom.comp (AddMonoidHom.snd X₁ U))

@[simp] theorem middleExtendMap_apply (f : X₁ →+ Y₁) (e : U ≃+ V) (x : X₁ × U) :
    middleExtendMap f e x = (f x.1, e x.2) := rfl

/-- A quasi-isomorphism remains one after adjoining a complex concentrated in degree one and
mapping that new summand by an additive equivalence.  This is the abstract handle-stabilization
step: the hyperbolic handle block will supply `e`. -/
theorem StokesQuasiIso.middleStabilization
    {dX₀ : X₀ →+ X₁} {dX₁ : X₁ →+ X₂} {dY₀ : Y₀ →+ Y₁} {dY₁ : Y₁ →+ Y₂}
    {φ₀ : X₀ →+ Y₀} {φ₁ : X₁ →+ Y₁} {φ₂ : X₂ →+ Y₂}
    (e : U ≃+ V)
    (h : StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂) :
    StokesQuasiIso (middleExtendD0 (U := U) dX₀) (middleExtendD1 (U := U) dX₁)
      (middleExtendD0 (U := V) dY₀) (middleExtendD1 (U := V) dY₁)
      φ₀ (middleExtendMap φ₁ e) φ₂ := by
  constructor
  · intro x hx hφx
    exact h.h0_inj x (congrArg Prod.fst hx) hφx
  · intro y hy
    obtain ⟨x, hx, hφx⟩ := h.h0_surj y (congrArg Prod.fst hy)
    exact ⟨x, by ext <;> simp [hx], hφx⟩
  · intro x hx hbound
    obtain ⟨y, hy⟩ := hbound
    have hezero : e x.2 = 0 := (congrArg Prod.snd hy).symm
    obtain ⟨x₀, hx₀⟩ := h.h1_inj x.1 hx ⟨y, congrArg Prod.fst hy⟩
    refine ⟨x₀, Prod.ext hx₀ ?_⟩
    exact (e.injective (hezero.trans (map_zero e).symm)).symm
  · intro y hy
    obtain ⟨x, y₀, hx, hsum⟩ := h.h1_surj y.1 hy
    refine ⟨(x, e.symm y.2), y₀, hx, ?_⟩
    apply Prod.ext
    · exact hsum
    · simp
  · intro x hbound
    obtain ⟨y, hy⟩ := hbound
    obtain ⟨x₁, hx₁⟩ := h.h2_inj x ⟨y.1, hy⟩
    exact ⟨(x₁, 0), hx₁⟩
  · intro y
    obtain ⟨x, y₁, hsum⟩ := h.h2_surj y
    exact ⟨x, (y₁, 0), hsum⟩

end MiddleStabilization

end GQ2.Dyadic
