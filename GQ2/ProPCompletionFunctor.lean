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

/-- The induced map of a trivial homomorphism is trivial. -/
@[simp] theorem proPCompletionMap_one (x : proPCompletion p A) :
    proPCompletionMap (p := p) (1 : A →* B) x = 1 := by
  have hfun : (⇑(proPCompletionMap (p := p) (1 : A →* B))) =
      (fun _ : proPCompletion p A ↦ (1 : proPCompletion p B)) := by
    apply Continuous.ext_on (denseRange_proPCompletionMk (p := p) (A := A))
      (proPCompletionMap (p := p) (1 : A →* B)).continuous_toFun continuous_const
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

/-- The pro-`p` completion of a commutative group remains commutative.  This is proved from
the dense canonical image, since the completion is represented by a quotient carrying only a
`Group` instance in the current API. -/
theorem proPCompletion_mul_comm {D : Type} [CommGroup D]
    (x y : proPCompletion p D) : x * y = y * x := by
  have hcanonical : ∀ d : D, proPCompletionMk p D d * y = y * proPCompletionMk p D d := by
    intro d
    have hfun : (fun z : proPCompletion p D ↦ proPCompletionMk p D d * z) =
        (fun z ↦ z * proPCompletionMk p D d) := by
      apply Continuous.ext_on (denseRange_proPCompletionMk (p := p) (A := D))
        (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
      rintro _ ⟨e, rfl⟩
      change proPCompletionMk p D d * proPCompletionMk p D e =
        proPCompletionMk p D e * proPCompletionMk p D d
      rw [← map_mul, ← map_mul, mul_comm]
    exact congrFun hfun y
  have hfun : (fun z : proPCompletion p D ↦ z * y) = (fun z ↦ y * z) := by
    apply Continuous.ext_on (denseRange_proPCompletionMk (p := p) (A := D))
      (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    rintro _ ⟨d, rfl⟩
    exact hcanonical d
  exact congrFun hfun x

/-! ## Binary products of commutative groups -/

section Prod

variable {A₁ B₁ : Type} [CommGroup A₁] [CommGroup B₁]

/-- The canonical map from the completion of a product to the product of the completions. -/
def proPCompletionProdForward :
    ContinuousMonoidHom (proPCompletion p (A₁ × B₁))
      (proPCompletion p A₁ × proPCompletion p B₁) where
  toMonoidHom := (proPCompletionMap (p := p) (MonoidHom.fst A₁ B₁)).toMonoidHom.prod
    (proPCompletionMap (p := p) (MonoidHom.snd A₁ B₁)).toMonoidHom
  continuous_toFun :=
    (proPCompletionMap (p := p) (MonoidHom.fst A₁ B₁)).continuous_toFun.prodMk
      (proPCompletionMap (p := p) (MonoidHom.snd A₁ B₁)).continuous_toFun

/-- The inverse product map, obtained by completing the two coordinate inclusions and
multiplying their commuting images. -/
def proPCompletionProdBackward :
    ContinuousMonoidHom (proPCompletion p A₁ × proPCompletion p B₁)
      (proPCompletion p (A₁ × B₁)) where
  toFun z :=
    proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) z.1 *
      proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) z.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    let a := proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) x.1
    let b := proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) x.2
    let c := proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) y.1
    let d := proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) y.2
    change (a * c) * (b * d) = (a * b) * (c * d)
    calc
      (a * c) * (b * d) = a * (c * b) * d := by group
      _ = a * (b * c) * d := by rw [proPCompletion_mul_comm c b]
      _ = (a * b) * (c * d) := by group
  continuous_toFun :=
    ((proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁)).continuous_toFun.comp
      continuous_fst).mul
    ((proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁)).continuous_toFun.comp
      continuous_snd)

@[simp] theorem proPCompletionProdForward_mk (a : A₁) (b : B₁) :
    proPCompletionProdForward (p := p)
      (proPCompletionMk p (A₁ × B₁) (a, b)) =
        (proPCompletionMk p A₁ a, proPCompletionMk p B₁ b) := by
  change
    (proPCompletionMap (p := p) (MonoidHom.fst A₁ B₁)
        (proPCompletionMk p (A₁ × B₁) (a, b)),
      proPCompletionMap (p := p) (MonoidHom.snd A₁ B₁)
        (proPCompletionMk p (A₁ × B₁) (a, b))) = _
  rw [proPCompletionMap_mk, proPCompletionMap_mk]
  rfl

/-- **Pro-`p` completion preserves binary products of commutative groups.** -/
def proPCompletionProdEquiv :
    ContinuousMulEquiv (proPCompletion p (A₁ × B₁))
      (proPCompletion p A₁ × proPCompletion p B₁) := by
  let F := proPCompletionProdForward (p := p) (A₁ := A₁) (B₁ := B₁)
  let G := proPCompletionProdBackward (p := p) (A₁ := A₁) (B₁ := B₁)
  have hleft : ∀ x, G (F x) = x := by
    have hfun : (fun x ↦ G (F x)) = (id : proPCompletion p (A₁ × B₁) → _) := by
      apply Continuous.ext_on (denseRange_proPCompletionMk (p := p) (A := A₁ × B₁))
        (G.continuous_toFun.comp F.continuous_toFun) continuous_id
      rintro _ ⟨⟨a, b⟩, rfl⟩
      change G (F (proPCompletionMk p (A₁ × B₁) (a, b))) = _
      rw [show F (proPCompletionMk p (A₁ × B₁) (a, b)) =
        (proPCompletionMk p A₁ a, proPCompletionMk p B₁ b) from
          proPCompletionProdForward_mk a b]
      change proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁)
          (proPCompletionMk p A₁ a) *
        proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁)
          (proPCompletionMk p B₁ b) = proPCompletionMk p (A₁ × B₁) (a, b)
      rw [proPCompletionMap_mk, proPCompletionMap_mk, ← map_mul]
      simp
    exact fun x ↦ congrFun hfun x
  have hright : ∀ y, F (G y) = y := by
    rintro ⟨a, b⟩
    have hfa : proPCompletionMap (p := p) (MonoidHom.fst A₁ B₁)
        (proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) a) = a := by
      rw [← proPCompletionMap_comp]
      have he : (MonoidHom.fst A₁ B₁).comp (MonoidHom.inl A₁ B₁) =
          MonoidHom.id A₁ := by ext; simp
      rw [he, proPCompletionMap_id]
    have hfb : proPCompletionMap (p := p) (MonoidHom.fst A₁ B₁)
        (proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) b) = 1 := by
      rw [← proPCompletionMap_comp]
      have he : (MonoidHom.fst A₁ B₁).comp (MonoidHom.inr A₁ B₁) =
          (1 : B₁ →* A₁) := by ext; simp
      rw [he, proPCompletionMap_one]
    have hsa : proPCompletionMap (p := p) (MonoidHom.snd A₁ B₁)
        (proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) a) = 1 := by
      rw [← proPCompletionMap_comp]
      have he : (MonoidHom.snd A₁ B₁).comp (MonoidHom.inl A₁ B₁) =
          (1 : A₁ →* B₁) := by ext; simp
      rw [he, proPCompletionMap_one]
    have hsb : proPCompletionMap (p := p) (MonoidHom.snd A₁ B₁)
        (proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) b) = b := by
      rw [← proPCompletionMap_comp]
      have he : (MonoidHom.snd A₁ B₁).comp (MonoidHom.inr A₁ B₁) =
          MonoidHom.id B₁ := by ext; simp
      rw [he, proPCompletionMap_id]
    apply Prod.ext
    · change proPCompletionMap (p := p) (MonoidHom.fst A₁ B₁)
          (proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) a *
            proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) b) = a
      rw [map_mul, hfa, hfb, mul_one]
    · change proPCompletionMap (p := p) (MonoidHom.snd A₁ B₁)
          (proPCompletionMap (p := p) (MonoidHom.inl A₁ B₁) a *
            proPCompletionMap (p := p) (MonoidHom.inr A₁ B₁) b) = b
      rw [map_mul, hsa, hsb, one_mul]
  exact continuousMulEquivOfBijective F
    (Function.bijective_iff_has_inverse.mpr ⟨G, hleft, hright⟩)

@[simp] theorem proPCompletionProdEquiv_mk (a : A₁) (b : B₁) :
    proPCompletionProdEquiv (p := p)
      (proPCompletionMk p (A₁ × B₁) (a, b)) =
        (proPCompletionMk p A₁ a, proPCompletionMk p B₁ b) :=
  proPCompletionProdForward_mk a b

#print axioms proPCompletionProdEquiv

end Prod

#print axioms proPCompletionCongr

end

end GQ2
