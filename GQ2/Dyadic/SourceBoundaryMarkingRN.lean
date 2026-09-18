import GQ2.Dyadic.SourceTransportRN

/-!
# Boundary compatibility is stronger than abstract source equivalence

The corrected reconstruction theorem currently supplies an abstract continuous equivalence.
This additive interface does not strengthen that theorem implicitly. It separates the two
boundary squares, constructs the automorphism of the common maximal-pro-2 core induced by any
source equivalence, and characterizes when this automorphism is the identity.

Matching the tame square suffices for the full `Ztwo` unramified character, not merely its
reduction modulo two. No cyclotomic character is a field of `SourceDataRN`; transporting a
specified such character therefore has an explicit core-character hypothesis below.
-/

namespace GQ2.Dyadic.SourceDataRN

open GQ2

noncomputable section

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
  (S₁ S₂ : SourceDataRN n q P hP nuP SN)

/-- Equality in the fiber-product boundary is exactly the pair of boundary squares. -/
theorem boundary_eq_iff_tame_pro2 (e : ContinuousMulEquiv S₁.Γ S₂.Γ) :
    (∀ g, S₂.b (e g) = S₁.b g) ↔
      (∀ g, S₂.tame (e g) = S₁.tame g) ∧
      (∀ g, S₂.pro2 (e g) = S₁.pro2 g) := by
  constructor
  · intro h
    exact ⟨fun g => congrArg (fun z => z.val.1) (h g),
      fun g => congrArg (fun z => z.val.2) (h g)⟩
  · rintro ⟨ht, hp⟩ g
    exact Subtype.ext (Prod.ext (ht g) (hp g))

/-- Tame compatibility alone preserves the complete two-adic unramified character. -/
theorem nu_eq_of_tame_eq (e : ContinuousMulEquiv S₁.Γ S₂.Γ)
    (ht : ∀ g, S₂.tame (e g) = S₁.tame g) (g : S₁.Γ) :
    nuP (S₂.pro2 (e g)) = nuP (S₁.pro2 g) := by
  rw [← S₂.compat, ht, S₁.compat]

private theorem pro2IsoK_mk {Γ : ProfiniteGrp} (p : ContinuousMonoidHom Γ P)
    (hs : Function.Surjective p) (hk : p.toMonoidHom.ker = proPKernel 2 Γ) (g : Γ) :
    pro2IsoK hP p hs hk (maxProPMk 2 Γ g) = p g :=
  DFunLike.congr_fun ((maxProPHomEquiv hP).apply_symm_apply p) g

/-- Every abstract source equivalence induces a definite automorphism of their common core.
This automorphism is not asserted to be the identity. -/
def coreEquiv (e : ContinuousMulEquiv S₁.Γ S₂.Γ) : ContinuousMulEquiv P P :=
  (pro2IsoK hP S₁.pro2 S₁.pro2_surjective S₁.ker_pro2).symm.trans
    (pro2IsoK hP (S₂.pro2.comp (e : ContinuousMonoidHom S₁.Γ S₂.Γ))
      (S₂.pro2_surjective.comp e.surjective)
      (ker_comp_continuousMulEquiv e S₂.pro2 S₂.ker_pro2))

/-- The induced automorphism gives the commuting pro-2 square for every equivalence. -/
theorem coreEquiv_pro2 (e : ContinuousMulEquiv S₁.Γ S₂.Γ) (g : S₁.Γ) :
    coreEquiv S₁ S₂ e (S₁.pro2 g) = S₂.pro2 (e g) := by
  have hs : (pro2IsoK hP S₁.pro2 S₁.pro2_surjective S₁.ker_pro2).symm
      (S₁.pro2 g) = maxProPMk 2 S₁.Γ g := by
    apply (pro2IsoK hP S₁.pro2 S₁.pro2_surjective S₁.ker_pro2).injective
    rw [ContinuousMulEquiv.apply_symm_apply, pro2IsoK_mk (hP := hP)]
  simp only [coreEquiv, ContinuousMulEquiv.trans_apply]
  rw [hs, pro2IsoK_mk (hP := hP)]
  rfl

/-- Preserving the prescribed pro-2 map is equivalent to the induced core map being identity. -/
theorem coreEquiv_eq_refl_iff (e : ContinuousMulEquiv S₁.Γ S₂.Γ) :
    coreEquiv S₁ S₂ e = ContinuousMulEquiv.refl P ↔
      ∀ g, S₂.pro2 (e g) = S₁.pro2 g := by
  constructor
  · intro h g
    rw [← coreEquiv_pro2, h]
    rfl
  · intro h
    ext p
    obtain ⟨g, rfl⟩ := S₁.pro2_surjective p
    exact (coreEquiv_pro2 S₁ S₂ e g).trans (h g)

/-- A tame-compatible equivalence induces a `nuP`-preserving, not necessarily trivial,
core automorphism. -/
theorem coreEquiv_nu_of_tame_eq (e : ContinuousMulEquiv S₁.Γ S₂.Γ)
    (ht : ∀ g, S₂.tame (e g) = S₁.tame g) (p : P) :
    nuP (coreEquiv S₁ S₂ e p) = nuP p := by
  obtain ⟨g, rfl⟩ := S₁.pro2_surjective p
  rw [coreEquiv_pro2]
  exact nu_eq_of_tame_eq S₁ S₂ e ht g

/-- Boundary compatibility has one tame condition and one additional fixed-core condition. -/
theorem boundary_eq_iff_tame_coreEquiv (e : ContinuousMulEquiv S₁.Γ S₂.Γ) :
    (∀ g, S₂.b (e g) = S₁.b g) ↔
      (∀ g, S₂.tame (e g) = S₁.tame g) ∧
      coreEquiv S₁ S₂ e = ContinuousMulEquiv.refl P := by
  rw [boundary_eq_iff_tame_pro2, coreEquiv_eq_refl_iff]

/-- A specified core character is preserved precisely when the induced core equivalence
intertwines it. This is an explicit condition, not an intrinsic-orientation assertion. -/
theorem character_eq_iff_coreEquiv {C : Type*} [Group C]
    (χ₁ χ₂ : P →* C) (e : ContinuousMulEquiv S₁.Γ S₂.Γ) :
    (∀ g, χ₂ (S₂.pro2 (e g)) = χ₁ (S₁.pro2 g)) ↔
      ∀ p, χ₂ (coreEquiv S₁ S₂ e p) = χ₁ p := by
  constructor
  · intro h p
    obtain ⟨g, rfl⟩ := S₁.pro2_surjective p
    rw [coreEquiv_pro2]
    exact h g
  · intro h g
    rw [← coreEquiv_pro2]
    exact h (S₁.pro2 g)

#print axioms boundary_eq_iff_tame_pro2
#print axioms nu_eq_of_tame_eq
#print axioms coreEquiv
#print axioms coreEquiv_pro2
#print axioms coreEquiv_eq_refl_iff
#print axioms coreEquiv_nu_of_tame_eq
#print axioms boundary_eq_iff_tame_coreEquiv
#print axioms character_eq_iff_coreEquiv

end

end GQ2.Dyadic.SourceDataRN
