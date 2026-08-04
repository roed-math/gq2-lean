/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.ProPAbelianization

/-!
# Functoriality of abstract pro-p completion

The universal property already constructs maps from a pro-`p` completion.  This file packages
the induced map of completions, proves its behavior on the dense canonical image, and shows
that an abstract multiplicative equivalence induces a continuous multiplicative equivalence of
pro-`p` completions.
-/

namespace GQ2

noncomputable section

variable {p : ℕ} {A B C : Type} [Group A] [Group B] [Group C]

/-- The canonical map to an abstract pro-`p` completion has dense range. -/
theorem denseRange_proPCompletionMk : DenseRange (proPCompletionMk p A) := by
  change DenseRange
    ((⇑(maxProPMk p (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A)))) ∘
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of A))
  exact DenseRange.comp
    (Function.Surjective.denseRange (maxProPMk_surjective
      (p := p) (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))))
    (ProfiniteGrp.ProfiniteCompletion.denseRange _)
    (maxProPMk p
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))).continuous_toFun

/-- A homomorphism of abstract groups induces a continuous homomorphism of their pro-`p`
completions. -/
def proPCompletionMap (f : A →* B) :
    ContinuousMonoidHom (proPCompletion p A) (proPCompletion p B) :=
  proPCompletionLift isProP_maxProPQuotient ((proPCompletionMk p B).comp f)

@[simp] theorem proPCompletionMap_mk (f : A →* B) (a : A) :
    proPCompletionMap (p := p) f (proPCompletionMk p A a) =
      proPCompletionMk p B (f a) :=
  proPCompletionLift_mk isProP_maxProPQuotient _ _

/-- Functoriality for composition. -/
theorem proPCompletionMap_comp (g : B →* C) (f : A →* B) (x : proPCompletion p A) :
    proPCompletionMap (p := p) (g.comp f) x =
      proPCompletionMap (p := p) g (proPCompletionMap (p := p) f x) := by
  have hfun :
      (⇑(proPCompletionMap (p := p) (g.comp f))) =
        fun z ↦ proPCompletionMap (p := p) g (proPCompletionMap (p := p) f z) := by
    apply Continuous.ext_on (denseRange_proPCompletionMk (p := p) (A := A))
      (proPCompletionMap (p := p) (g.comp f)).continuous_toFun
      ((proPCompletionMap (p := p) g).continuous_toFun.comp
        (proPCompletionMap (p := p) f).continuous_toFun)
    rintro _ ⟨a, rfl⟩
    simp
  exact congrFun hfun x

/-- Functoriality for the identity. -/
@[simp] theorem proPCompletionMap_id (x : proPCompletion p A) :
    proPCompletionMap (p := p) (MonoidHom.id A) x = x := by
  have hfun : (⇑(proPCompletionMap (p := p) (MonoidHom.id A))) =
      (id : proPCompletion p A → proPCompletion p A) := by
    apply Continuous.ext_on (denseRange_proPCompletionMk (p := p) (A := A))
      (proPCompletionMap (p := p) (MonoidHom.id A)).continuous_toFun continuous_id
    rintro _ ⟨a, rfl⟩
    simp
  exact congrFun hfun x

/-- Abstractly isomorphic groups have continuously isomorphic pro-`p` completions. -/
def proPCompletionCongr (e : A ≃* B) :
    ContinuousMulEquiv (proPCompletion p A) (proPCompletion p B) := by
  let f := proPCompletionMap (p := p) e.toMonoidHom
  let g := proPCompletionMap (p := p) e.symm.toMonoidHom
  have hleft : ∀ x, g (f x) = x := by
    intro x
    rw [← proPCompletionMap_comp]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by ext; simp
    rw [he, proPCompletionMap_id]
  have hright : ∀ y, f (g y) = y := by
    intro y
    rw [← proPCompletionMap_comp]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by ext; simp
    rw [he, proPCompletionMap_id]
  exact continuousMulEquivOfBijective f
    (Function.bijective_iff_has_inverse.mpr ⟨g, hleft, hright⟩)

@[simp] theorem proPCompletionCongr_mk (e : A ≃* B) (a : A) :
    proPCompletionCongr (p := p) e (proPCompletionMk p A a) =
      proPCompletionMk p B (e a) :=
  proPCompletionMap_mk _ _

#print axioms proPCompletionCongr

end

end GQ2
