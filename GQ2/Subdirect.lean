import GQ2.Words
import GQ2.Omega2

/-!
# Admissibility is preserved by quotient maps (paper §2, Lemmas 2.1–2.2)

The paper builds the candidate `Γ_A` as an inverse limit of *admissible* finite quotients, which
requires that admissibility is stable under the maps of the system.  The technical heart is that
the auxiliary words (which involve `ω₂`-powers) commute with group homomorphisms — this is exactly
`GQ2.powOmega2_map`.  Here we push it through the whole word ledger to obtain:

* `GQ2.Marking.map_admissible`: an admissible marking of `G` pushes forward, along any *surjective*
  group homomorphism `f : G → H` (of finite groups), to an admissible marking of `H`.
-/

namespace GQ2

open scoped Classical

namespace Marking

variable {G H : Type*} [Group G] [Group H]

/-- Push a marking forward along a group homomorphism. -/
def map (f : G →* H) (t : Marking G) : Marking H := ⟨f t.σ, f t.τ, f t.x₀, f t.x₁⟩

@[simp] lemma map_σ (f : G →* H) (t : Marking G) : (t.map f).σ = f t.σ := rfl
@[simp] lemma map_τ (f : G →* H) (t : Marking G) : (t.map f).τ = f t.τ := rfl
@[simp] lemma map_x₀ (f : G →* H) (t : Marking G) : (t.map f).x₀ = f t.x₀ := rfl
@[simp] lemma map_x₁ (f : G →* H) (t : Marking G) : (t.map f).x₁ = f t.x₁ := rfl

/-- `f` intertwines the conjugation convention. -/
lemma map_conjP (f : G →* H) (x g : G) : f (conjP x g) = conjP (f x) (f g) := by
  simp only [conjP, map_mul, map_inv]

/-- `f` intertwines the commutator convention. -/
lemma map_commP (f : G →* H) (x y : G) : f (commP x y) = commP (f x) (f y) := by
  simp only [commP, map_mul, map_inv]

section
variable [Finite G] (f : G →* H) (t : Marking G)

@[simp] lemma map_sigma2 : (t.map f).sigma2 = f t.sigma2 := by
  simp only [sigma2, map_σ]; exact (powOmega2_map f t.σ).symm

@[simp] lemma map_u0 : (t.map f).u0 = f t.u0 := by
  simp only [u0, u, map_x₀, map_τ, ← map_mul]; exact (powOmega2_map f _).symm

@[simp] lemma map_u1 : (t.map f).u1 = f t.u1 := by
  simp only [u1, u, map_x₁, map_τ, ← map_mul]; exact (powOmega2_map f _).symm

@[simp] lemma map_d0 : (t.map f).d0 = f t.d0 := by
  simp only [d0, map_u0, map_x₀, map_mul, map_inv]

@[simp] lemma map_z0 : (t.map f).z0 = f t.z0 := by
  simp only [z0, map_x₀, map_sigma2, map_conjP]

@[simp] lemma map_c0 : (t.map f).c0 = f t.c0 := by
  simp only [c0, map_d0, map_z0, map_commP]

@[simp] lemma map_g0 : (t.map f).g0 = f t.g0 := by
  simp only [g0, map_sigma2, map_pow]

@[simp] lemma map_dg : (t.map f).dg = f t.dg := by
  simp only [dg, map_d0, map_g0, map_conjP]

@[simp] lemma map_hc : (t.map f).hc = f t.hc := by
  simp only [hc, map_dg, map_d0, map_commP]

@[simp] lemma map_h0 : (t.map f).h0 = f t.h0 := by
  simp only [h0, map_x₀, map_g0, map_dg, map_d0, map_hc, map_conjP, map_mul, map_pow]

omit [Finite G] in
/-- The tame relation transfers along any group hom. -/
lemma map_tameRel (h : t.TameRel) : (t.map f).TameRel := by
  have h' : conjP t.τ t.σ = t.τ ^ 2 := h
  show conjP (f t.τ) (f t.σ) = (f t.τ) ^ 2
  rw [← map_conjP, h', map_pow]

/-- The wild relator word commutes with any group hom `f`. -/
lemma map_wildLHS :
    (t.map f).h0 * (t.map f).u1⁻¹ * conjP (t.map f).x₁ (t.map f).σ * (t.map f).c0
      = f (t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0) := by
  simp only [map_h0, map_u1, map_x₁, map_σ, map_c0, map_conjP, map_mul, map_inv]

/-- The wild relation transfers along any group hom. -/
lemma map_wildRel (h : t.WildRel) : (t.map f).WildRel := by
  have h' : t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0 = 1 := h
  show (t.map f).h0 * (t.map f).u1⁻¹ * conjP (t.map f).x₁ (t.map f).σ * (t.map f).c0 = 1
  rw [map_wildLHS, h', map_one]

end

/-- **Admissibility pushes forward along surjective quotient maps** (paper §2, cofinality /
Lemma 2.1–2.2).  If `t` is an admissible marking of a finite group `G` and `f : G ↠ H` is a
surjective homomorphism of finite groups, then `t.map f` is an admissible marking of `H`. -/
theorem map_admissible {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (t : Marking G) (ht : t.Admissible) :
    (t.map f).Admissible := by
  obtain ⟨hgen, htame, hwild, hcore⟩ := ht
  refine ⟨?_, map_tameRel f t htame, map_wildRel f t hwild, ?_⟩
  · -- generation is preserved by surjective images
    rw [Generates] at hgen ⊢
    rw [show ({(t.map f).σ, (t.map f).τ, (t.map f).x₀, (t.map f).x₁} : Set H)
          = f '' {t.σ, t.τ, t.x₀, t.x₁} by simp [map, Set.image_insert_eq, Set.image_singleton]]
    rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective f hf]
  · -- the wild generators still have 2-group normal closure
    have himg : Subgroup.normalClosure {(t.map f).x₀, (t.map f).x₁}
        = (Subgroup.normalClosure {t.x₀, t.x₁}).map f := by
      rw [show ({(t.map f).x₀, (t.map f).x₁} : Set H) = f '' {t.x₀, t.x₁} by
            simp [map, Set.image_insert_eq, Set.image_singleton]]
      exact (Subgroup.map_normalClosure {t.x₀, t.x₁} f hf).symm
    rw [Pro2Core] at hcore ⊢
    rw [himg]
    exact hcore.map f

/-- The **product** of two markings (componentwise). -/
def prod (t₁ : Marking G) (t₂ : Marking H) : Marking (G × H) :=
  ⟨(t₁.σ, t₂.σ), (t₁.τ, t₂.τ), (t₁.x₀, t₂.x₀), (t₁.x₁, t₂.x₁)⟩


end Marking

end GQ2
