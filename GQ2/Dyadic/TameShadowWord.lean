/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.Instances.StokesEndpointSubstitution

/-!
# Tame shadows and analytic splicing

The shadow is the identity after pro-two specialization and erases all wild bases
at a wild-trivial marking. A splice therefore retains the first word's complete
pro-two core presentation while permitting a separately chosen ramified word.
This module proves the structural and endpoint statements only; the Heisenberg
comparison belongs to the analytic shadow modules.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.Dyadic.Count

/-- The tame-averaging shadow kills tau and replaces a wild letter by its
relative two-primary projection against tau. -/
def tameShadowSubst {n : ℕ} : Generator n → PWord (Generator n)
  | .sigma => .gen .sigma
  | .tau => .one
  | .wild i => .mul (.profPow (.mul (.gen (.wild i)) (.gen .tau)) omega2)
      (.inv (.profPow (.gen .tau) omega2))

/-- Apply the tame-averaging shadow to a word. -/
def tameShadow {n : ℕ} (w : PWord (Generator n)) : PWord (Generator n) :=
  PWord.subst tameShadowSubst w

/-- Retain R's pro-two presentation and splice in H's ramified analytic part. -/
def tameSplice {n : ℕ} (R H : PWord (Generator n)) : PWord (Generator n) :=
  .mul (.mul (tameShadow R) H) (.inv (tameShadow H))

section Eval

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Shadowing is the identity at every tau-trivial, omega-fixed marking. -/
theorem eval_tameShadow_of_omegaFixed (t : Marking n G)
    (htau : t.τ = 1) (homega : ∀ g : G, g ^ᶻ omega2 = g)
    (w : PWord (Generator n)) : t.eval (tameShadow w) = t.eval w := by
  change PWord.eval (⇑t) (PWord.subst tameShadowSubst w) = PWord.eval (⇑t) w
  rw [PWord.eval_subst]
  congr 1
  funext g
  cases g with
  | sigma => rfl
  | tau => exact htau.symm
  | wild i =>
      change (t (.wild i) * t.τ) ^ᶻ omega2 * (t.τ ^ᶻ omega2)⁻¹ = t (.wild i)
      rw [htau, mul_one, homega, homega, inv_one, mul_one]

theorem eval_tameSplice_of_omegaFixed (t : Marking n G)
    (htau : t.τ = 1) (homega : ∀ g : G, g ^ᶻ omega2 = g)
    (R H : PWord (Generator n)) : t.eval (tameSplice R H) = t.eval R := by
  change t.eval (tameShadow R) * t.eval H * (t.eval (tameShadow H))⁻¹ = t.eval R
  rw [eval_tameShadow_of_omegaFixed t htau homega,
    eval_tameShadow_of_omegaFixed t htau homega, mul_inv_cancel_right]

/-- The splice has exactly R's pro-two equation. -/
theorem eval_pro2_tameSplice (t : Marking n G) (hG : IsProP 2 G)
    (htau : t.τ = 1) (R H : PWord (Generator n)) :
    t.eval (pro2 (tameSplice R H)) = t.eval (pro2 R) := by
  have homega := zpowHat_omega2_eq_self_of_isProP hG
  rw [Marking.eval_pro2 t htau homega, Marking.eval_pro2 t htau homega,
    eval_tameSplice_of_omegaFixed t htau homega]

/-- At a wild-trivial marking, shadow evaluation retains only the sigma letter. -/
theorem eval_tameShadow_of_wild_trivial (t : Marking n G)
    (hwild : ∀ i, t (.wild i) = 1) (w : PWord (Generator n)) :
    t.eval (tameShadow w) = PWord.eval
      (fun g : Generator n => match g with | .sigma => t.σ | _ => 1) w := by
  change PWord.eval (⇑t) (PWord.subst tameShadowSubst w) = _
  rw [PWord.eval_subst]
  congr 1
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => simp [tameShadowSubst, hwild]

end Eval

/-- A tame-specializing word dies on every pure-sigma marking, including when
the sigma value is not a pro-two element. -/
theorem eval_pureSigma_of_tameSpecializes
    {n q : ℕ} {R : PWord (Generator n)}
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hspec : TameSpec.TameSpecializes n q R) (g : G) :
    PWord.eval (fun a : Generator n => match a with | .sigma => g | _ => 1) R = 1 := by
  let f : ContinuousMonoidHom (Tq q) G :=
    tqClassify q (ProfiniteGrp.of G) (a := g) (b := 1) (by simp [conjP])
  have hmark : (tameMarking n q).map (⇑f) =
      (⟨fun a : Generator n => match a with | .sigma => g | _ => 1⟩ : Marking n G) := by
    ext a
    cases a with
    | sigma => exact tqClassify_tqSigma q (ProfiniteGrp.of G) (by simp [conjP])
    | tau => exact tqClassify_tqTau q (ProfiniteGrp.of G) (a := g) (by simp [conjP])
    | wild i => exact map_one f
  have H := congrArg (fun x => f x) hspec
  rw [Marking.map_eval, hmark, map_one] at H
  exact H

/-- The resolved pure-sigma equation follows whenever the chosen resolvers are
valid at that marking. -/
theorem evalZ_pureSigma_of_tameSpecializes
    {n q : ℕ} {R : PWord (Generator n)}
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hspec : TameSpec.TameSpecializes n q R) (g : G)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (fun a : Generator n => match a with | .sigma => g | _ => 1) E E₂ R) :
    PWord.evalZ (fun a : Generator n => match a with | .sigma => g | _ => 1) E E₂ R = 1 := by
  rw [← PWord.eval_eq_evalZ _ E E₂ R hres]
  exact eval_pureSigma_of_tameSpecializes hspec g

/-- The shadow of a tame-specializing word is again tame-specializing. -/
theorem tameSpecializes_tameShadow {n q : ℕ} {R : PWord (Generator n)}
    (hR : TameSpec.TameSpecializes n q R) :
    TameSpec.TameSpecializes n q (tameShadow R) := by
  change (tameMarking n q).eval (tameShadow R) = 1
  rw [eval_tameShadow_of_wild_trivial (tameMarking n q) (fun _ => rfl)]
  exact eval_pureSigma_of_tameSpecializes hR (tameMarking n q).σ

/-- Tame splicing preserves tame specialization. -/
theorem tameSpecializes_tameSplice {n q : ℕ} {R H : PWord (Generator n)}
    (hR : TameSpec.TameSpecializes n q R) (hH : TameSpec.TameSpecializes n q H) :
    TameSpec.TameSpecializes n q (tameSplice R H) := by
  have hSR := tameSpecializes_tameShadow hR
  have hSH := tameSpecializes_tameShadow hH
  change (tameMarking n q).eval (tameShadow R) * (tameMarking n q).eval H *
    ((tameMarking n q).eval (tameShadow H))⁻¹ = 1
  rw [hSR, hSH, hH, one_mul, inv_one, mul_one]

/-- The integer-resolved shadow has the same pure-sigma specialization,
without restrictions on the resolver or the tau value. -/
theorem evalZ_tameShadow_of_wild_trivial
    {n : ℕ} {G : Type*} [Group G] (c : Generator n → G)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hwild : ∀ i, c (.wild i) = 1) (w : PWord (Generator n)) :
    PWord.evalZ c E E₂ (tameShadow w) = PWord.evalZ
      (fun g : Generator n => match g with | .sigma => c .sigma | _ => 1) E E₂ w := by
  rw [tameShadow, PWord.evalZ_subst]
  congr 1
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => simp [tameShadowSubst, hwild]

namespace Count.CorePresentation

/-- Tame splicing preserves the complete pro-two core presentation and its marking. -/
def ofTameSplice {n : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    (C : CorePresentation n R P) (H : PWord (Generator n)) :
    CorePresentation n (tameSplice R H) P where
  isProP := C.isProP
  mark := C.mark
  mark_tau := C.mark_tau
  rel := by rw [eval_pro2_tameSplice C.mark C.isProP C.mark_tau]; exact C.rel
  liftHom := fun hQ t htau hrel =>
    C.liftHom hQ t htau ((eval_pro2_tameSplice t hQ htau R H).symm.trans hrel)
  liftHom_mark := by
    intro Q _ _ _ _ _ _ hQ t htau hrel g
    exact C.liftHom_mark hQ t htau _ g
  hom_ext := C.hom_ext

end Count.CorePresentation

/-- The shadow kills the canonical tame relator before taking exponent vectors. -/
theorem heisToFree_tameShadow_tameRelW {n q : ℕ}
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    heisToFree E E₂ (tameShadow (Certificates.tameRelW n q)) = 1 := by
  simp [heisToFree, tameShadow, Certificates.tameRelW,
    tameShadowSubst, conjR]

/-- Shadowing a valid two-relator endpoint kills its entire mod-two exponent vector. -/
theorem heisEps_tameShadow_eq_one_of_endpoint {n q : ℕ}
    {R : PWord (Generator n)} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hend : IsStokesEndpoint (fun k => heisToFree E E₂ (gammaFam n q R k)))
    (i : Generator n) : heisEps i (heisToFree E E₂ (tameShadow R)) = 1 := by
  have H := isStokesEndpoint_heisToFree_subst hend tameShadowSubst i
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  change (∑ k : Fin 2, Multiplicative.toAdd
    (heisEps i (heisToFree E E₂ (tameShadow (gammaFam n q R k))))) = 0 at H
  simpa only [Fin.sum_univ_two, gammaFam_zero, gammaFam_one,
    heisToFree_tameShadow_tameRelW, map_one, toAdd_one, zero_add] using H

/-- Splicing two endpoint words preserves the canonical two-relator endpoint. -/
theorem isStokesEndpoint_tameSplice {n q : ℕ}
    {R H : PWord (Generator n)} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hR : IsStokesEndpoint (fun k => heisToFree E E₂ (gammaFam n q R k)))
    (hH : IsStokesEndpoint (fun k => heisToFree E E₂ (gammaFam n q H k))) :
    IsStokesEndpoint (fun k => heisToFree E E₂ (gammaFam n q (tameSplice R H) k)) := by
  intro i
  have heps : heisEps i (heisToFree E E₂ (tameSplice R H)) =
      heisEps i (heisToFree E E₂ H) := by
    change heisEps i (heisToFree E E₂ (tameShadow R) * heisToFree E E₂ H *
      (heisToFree E E₂ (tameShadow H))⁻¹) = _
    rw [map_mul, map_mul, map_inv, heisEps_tameShadow_eq_one_of_endpoint hR i,
      heisEps_tameShadow_eq_one_of_endpoint hH i, one_mul, inv_one, mul_one]
  simpa only [Fin.sum_univ_two, gammaFam_zero, gammaFam_one, heps] using hH i

#print axioms tameShadowSubst
#print axioms tameShadow
#print axioms tameSplice
#print axioms eval_tameShadow_of_omegaFixed
#print axioms eval_tameSplice_of_omegaFixed
#print axioms eval_pro2_tameSplice
#print axioms eval_tameShadow_of_wild_trivial
#print axioms eval_pureSigma_of_tameSpecializes
#print axioms evalZ_pureSigma_of_tameSpecializes
#print axioms tameSpecializes_tameShadow
#print axioms tameSpecializes_tameSplice
#print axioms evalZ_tameShadow_of_wild_trivial
#print axioms Count.CorePresentation.ofTameSplice
#print axioms heisToFree_tameShadow_tameRelW
#print axioms heisEps_tameShadow_eq_one_of_endpoint
#print axioms isStokesEndpoint_tameSplice

end
end GQ2.Dyadic
