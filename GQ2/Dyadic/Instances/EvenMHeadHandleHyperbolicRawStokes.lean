/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawPairing
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawDetection
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicGeneralFox
import GQ2.Dyadic.Instances.EvenHyperbolicCompletion
import GQ2.Dyadic.Instances.StokesTranspose
import GQ2.Dyadic.Instances.EvenMRamifiedPairing

/-!
# Ramified Stokes duality for the raw hyperbolic source

Only the wild relator is changed; the canonical tame relator is retained. Unlike the older
full-family transport, this theorem imposes no triviality condition on sigma's action.

For alpha at least two, the zero-V pairing formula, the pure dual-U detector, and Heisenberg
transpose symmetry give a rank-uniform separation proof. The existing displaced-head normal
form and the general Fox row then give Stokes duality. The final theorem uses a resolver
depending only on the finite acting group, discharging every resolver premise.

This is the raw-family analytic theorem. It does not assert the sheared/tame-corrected source
certificate: pulling back normalization can make wild generators act by sigma powers, which
does not satisfy the wild-triviality premise below automatically.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairNoGo
open Instances.EvenMHeadHandleHyperbolicRawPairing
open Instances.EvenMHeadHandleHyperbolicRawDetection
open Instances.EvenMHeadHandleHyperbolicGeneralFox

namespace Instances.EvenMHeadHandleHyperbolicRawStokes

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [DistribMulAction C A]

/-- The displaced-head normal coordinates depend additively on their parameters. -/
def pairNormalHom (t : Marking (2 + 2 * h) C) (j : Fin h) :
    HyperbolicCompletion.Coordinates h A →+ (Generator (2 + 2 * h) → A) where
  toFun p := headHandlePairRamNormal t j p.1 p.2.1 p.2.2
  map_zero' := headHandlePairRamNormal_zero t j
  map_add' p r := by
    apply (EvenCore.coreHandleAddEquiv h A).injective
    rw [map_add]
    apply Prod.ext
    · funext g
      cases g with
      | sigma => simp
      | tau => simp
      | wild i => fin_cases i <;> simp
    · funext kl
      rcases kl with ⟨k, l⟩
      fin_cases l
      · simp
      · by_cases hkj : k = j
        · subst k
          simp [smul_add, add_sub_add_comm]
        · simp [headHandlePairRamNormal_handleV_of_ne, hkj]

@[simp] theorem pairNormalHom_apply
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (p : HyperbolicCompletion.Coordinates h A) :
    pairNormalHom t j p = headHandlePairRamNormal t j p.1 p.2.1 p.2.2 := rfl

private def normalPairing (t : Marking (2 + 2 * h) C) (j : Fin h)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) :
    HyperbolicCompletion.Coordinates h A →+
      (HyperbolicCompletion.Coordinates h (ElemDual A) →+ ZMod 2) where
  toFun p := (heisEta1 ⇑t w (pairNormalHom t j p)).comp (pairNormalHom t j)
  map_zero' := by
    ext r
    change (heisEta1 ⇑t w (pairNormalHom t j 0)) (pairNormalHom t j r) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' p s := by
    ext r
    change (heisEta1 ⇑t w (pairNormalHom t j (p + s))) (pairNormalHom t j r) =
      (heisEta1 ⇑t w (pairNormalHom t j p)) (pairNormalHom t j r) +
      (heisEta1 ⇑t w (pairNormalHom t j s)) (pairNormalHom t j r)
    rw [map_add, map_add]
    rfl

private theorem hyperUV_pointwise_zero
    (t : Marking (2 + 2 * h) C) (j : Fin h) (a : A) (lam : ElemDual A) :
    ∀ g, hyperYV t j lam g (hyperXU t j a g) = 0 := by
  have H : (fun g ↦ hyperYV t j lam g (hyperXU t j a g)) = 0 := by
    apply (EvenCore.coreHandleAddEquiv h (ZMod 2)).injective
    apply Prod.ext
    · funext g
      cases g with
      | sigma => simp [hyperXU, hyperYV]
      | tau => simp [hyperXU, hyperYV]
      | wild i => fin_cases i <;> simp [hyperXU, hyperYV, pairUSlot, pairVSlot]
    · funext kl
      rcases kl with ⟨k, l⟩
      fin_cases l
      · simp [hyperXU, hyperYV, pairVSlot]
      · by_cases hkj : k = j
        · subst k
          simp [hyperXU, hyperYV, pairUSlot]
        · simp [hyperXU, hyperYV, headHandlePairRamNormal_handleV_of_ne, hkj, pairUSlot]
  exact fun g ↦ congrFun H g

private theorem hyperXU_bidual
    (t : Marking (2 + 2 * h) C) (j : Fin h) (a : A) :
    (fun g ↦ dualEval A (hyperXU t j a g)) = hyperYU t j (dualEval A a) := by
  apply (EvenCore.coreHandleAddEquiv h (ElemDual (ElemDual A))).injective
  apply Prod.ext
  · funext g
    cases g with
    | sigma => simp [hyperXU, hyperYU]; rfl
    | tau => simp [hyperXU, hyperYU]; rfl
    | wild i => fin_cases i <;> simp [hyperXU, hyperYU, pairUSlot] <;> rfl
  · funext kl
    rcases kl with ⟨k, l⟩
    fin_cases l
    · by_cases hkj : k = j
      · subst k
        simp [hyperXU, hyperYU, pairUSlot]
      · simp [hyperXU, hyperYU, pairUSlot, hkj]
        rfl
    · by_cases hkj : k = j
      · subst k
        simp [hyperXU, hyperYU, pairUSlot]
        rfl
      · simp [hyperXU, hyperYU, headHandlePairRamNormal_handleV_of_ne, hkj, pairUSlot]
        rfl

/-- The promoted UV cross term, without a sigma-triviality hypothesis. -/
theorem heisEta1_hyperbolicRaw_UV_general
    {alpha q : ℕ} (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hα : 2 ≤ alpha)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hrow : IsHeadHandlePairRamRow (q := q) t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j) j A)
    (a : A) (lam : ElemDual A) :
    heisEta1 ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j)
      (hyperXU t j a) (hyperYV t j lam) = lam a := by
  let w := EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j
  have hx : heisD1 ⇑t w (hyperXU t j a) = 0 :=
    heisD1_headHandlePairRamNormal_eq_zero t w j hrow 0 0 (pairUSlot j a)
  rw [heisEta1_swap_of_pointwise_zero_of_cocycle ⇑t w _ _
    (hyperUV_pointwise_zero t j a lam) hx, hyperXU_bidual]
  have H := heisEta1_headHandleHyperbolicRawFamily_normal_pureU
      (A := ElemDual A) (q := q)
      t j E E₂ (fun mu ↦ mu.add_self_eq_zero) hα
      (fun i ↦ elemDual_smul_eq_self (hwild i)) 0 0 (pairVSlot j lam) (dualEval A a)
  rw [pairVSlot_self] at H
  exact H

/-- The normal pairing separates in every handle rank, with arbitrary sigma action. -/
theorem normal_pairing_separates
    [Finite C] [Finite A] {alpha q : ℕ}
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C)
    (hrow : IsHeadHandlePairRamRow (q := q) t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j) j A)
    (p : HyperbolicCompletion.Coordinates h A) (hp : p ≠ 0) :
    ∃ r : HyperbolicCompletion.Coordinates h (ElemDual A),
      heisEta1 ⇑t
        (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j)
        (headHandlePairRamNormal t j p.1 p.2.1 p.2.2)
        (headHandlePairRamNormal t j r.1 r.2.1 r.2.2) ≠ 0 := by
  let w := EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j
  let B := normalPairing (A := A) t j w
  apply HyperbolicCompletion.separates_of_zeroV_and_cross j B
    (fun a ha ↦ elemDual_separates hA₂ ha) ?_ ?_ ?_ p hp
  · intro x y hx hy
    exact heisEta1_headHandleHyperbolicRawFamily_normal_zeroV
      t j E E₂ hA₂ hwild hα hτfpf hTodd hresA hresD hres
      x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 hx hy
  · intro a lam
    change heisEta1 ⇑t w
      (headHandlePairRamNormal t j 0 0 (Pi.single (j, 0) a))
      (headHandlePairRamNormal t j 0 0 (Pi.single (j, 1) lam)) = lam a
    simpa only [hyperXU, hyperYV, pairUSlot, pairVSlot, Pi.single] using
      heisEta1_hyperbolicRaw_UV_general t j E E₂ hα hwild hrow a lam
  · intro a lam
    change heisEta1 ⇑t w
      (headHandlePairRamNormal t j 0 0 (Pi.single (j, 1) a))
      (headHandlePairRamNormal t j 0 0 (Pi.single (j, 0) lam)) = lam a
    have H := heisEta1_headHandleHyperbolicRawFamily_normal_pureU
        (q := q) t j E E₂ hA₂ hα hwild
        0 0 (pairVSlot j a) lam
    rw [pairVSlot_self] at H
    simpa only [hyperYU, pairUSlot, pairVSlot, Pi.single] using H

/-- The raw hyperbolic word has the scalar Stokes endpoint for every odd omega resolver. -/
theorem headHandleHyperbolicRawFamily_isStokesEndpoint
    {alpha h q : ℕ} (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hq : Even q) (he : Odd (E omega2)) :
    IsStokesEndpoint
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j) := by
  have hbase := mCompactOf_isStokesEndpoint (alpha := alpha) (h := h) (E₂ := E₂) hq he
  have hfull := isStokesEndpoint_heisToFree_subst hbase
    (headHandleHyperbolicNielsen j).backward
  intro i
  have H := hfull i
  rw [Fin.sum_univ_two] at H ⊢
  change Multiplicative.toAdd
      (heisEps i (heisToFree E E₂ (tameRelW (2 + 2 * h) q))) +
      Multiplicative.toAdd
      (heisEps i (heisToFree E E₂ (headHandleHyperbolicW alpha j))) = 0
  simp only [gammaFam_zero, gammaFam_one] at H
  rw [heisEps_heisToFree_subst_tameRelW E E₂ (2 + 2 * h) q
    (headHandleHyperbolicNielsen j).backward (headHandleHyperbolicNielsen_backward_tau j)] at H
  exact H

/-- Ramified Stokes duality for the raw hyperbolic family with arbitrary sigma action.
The result is uniform in alpha >= 2, handle rank, and the finite coefficient module. -/
theorem stokesDuality_headHandleHyperbolicRawFamily_ramified
    [Finite C] [Finite A] {alpha q : ℕ}
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha)
    (hq : Even q) (he : Odd (E omega2))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j k) = 1) :
    StokesDuality ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j) A := by
  let w := EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j
  have ht : t.TameRelAt q := by
    have hzero := hr 0
    have hz : PWord.evalZ ⇑t E E₂ (tameRelW (2 + 2 * h) q) = 1 :=
      (lift_heisToFree_eq_one_iff ⇑t E E₂ _).mp hzero
    rw [tameRelW, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
      PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, zpow_natCast] at hz
    exact mul_inv_eq_one.mp hz
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A),
      t.x i • lam = lam := fun i ↦ elemDual_smul_eq_self (hwild i)
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    elemDual_smul_eq_self hTodd
  have hrowA := isHeadHandlePairRamRow_hyperbolicRaw_general (alpha := alpha)
      t E E₂ j hA₂ ht hwild hτfpf hTodd hresA
  have hrowD := isHeadHandlePairRamRow_hyperbolicRaw_general (alpha := alpha)
      t E E₂ j hA₂D ht hwildD hτfpfD hToddD hresD
  exact headHandlePairRamStokesDuality_of_row t w j hA₂ hr
    (headHandleHyperbolicRawFamily_isStokesEndpoint E E₂ j hq he)
    hrowA hrowD hwild hτfpf
    (normal_pairing_separates t j E E₂ hA₂ hα hwild hτfpf hTodd
      hresA hresD hres hrowA)

/-- A coefficient-independent finite resolver discharges all resolver premises. -/
theorem stokesDuality_headHandleHyperbolicRawFamily_ramified_uniform
    [Finite C] [Finite A] {alpha q : ℕ}
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha) (hq : Even q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) alpha h q j k) = 1) :
    StokesDuality ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) alpha h q j) A := by
  have he := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  exact stokesDuality_headHandleHyperbolicRawFamily_ramified t j _ _ hA₂ hα hq
    (by simpa using he) hwild hτfpf hTodd
    (resolverLifts_uniformWordLift_ramified hA₂)
    (resolverLifts_uniformWordLift_ramified (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
    (MCompactRam.resolverLifts_uniform_base C) hr

#print axioms pairNormalHom
#print axioms heisEta1_hyperbolicRaw_UV_general
#print axioms normal_pairing_separates
#print axioms headHandleHyperbolicRawFamily_isStokesEndpoint
#print axioms stokesDuality_headHandleHyperbolicRawFamily_ramified
#print axioms stokesDuality_headHandleHyperbolicRawFamily_ramified_uniform

end Instances.EvenMHeadHandleHyperbolicRawStokes
end
end GQ2.Dyadic

