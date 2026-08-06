/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Instances.M0RamifiedStokes

/-!
# The compact-`M` second-order row on ramified normal offsets

`M0RamifiedStokes` reduces the compact-`M` ramified branch to one input: the value of

`(heisEvalZ ⇑t x y E E₂ (mCompactW α h)).z`

on offsets vanishing at `σ`, `τ` and `x₂`, in the ramified class.  This file computes it.

Why the compact-`N` argument does not transfer, and what replaces it.  On a ramified simple
module `powOmega2 t.σ` need not act trivially (the `𝔽₄` witness in `M0RamifiedStokes`'s module
docstring), so the twisted letters `A₀ = x₀⁻¹σ₂^{−m}`, `σ₂^{2m}` and the four conjugated
`δ`-letters of `E_m^rev` have a **moving base** `K = S₂^m` and are not jet-zero.  Two
observations replace the missing `hS₂` discipline, and neither needs a power law for a moving
base:

* a `σ₂`-power has *vanishing offsets* once `x σ = y σ = 0`, so it is second-order **pure**
  (`heisPure`) whatever its base does — this is what kills factor `3` and makes each `δ`-letter's
  conjugator a plain jet twist;
* the `δ`-letters' own jets are already known, at first order, from `foxD_deltaC_ram`: the
  ramified Fox row of `δ_i` is `−a(x_i)`, and `heisEvalZ_a_eq_foxD` / `heisEvalZ_l_eq_foxD` lift
  that to both halves of the Heisenberg jet.

The one genuinely new second-order rule is the *one-sided* commutator law
(`heisCommR_of_trivial_right`, in `EvenHeisPure`): `[A₀, x₁]` is no longer jet-zero, and its
central value gains the two terms `y₁(x₁) + y₁(K⁻¹x₁)` over the two-sided law.

**The answer.**  Every `K`-twisted contribution of `A₀²`, `[A₀,x₁]` and `E_m^rev` cancels over
`𝔽₂`, exactly as at first order in `foxD_mCompact_ram`, and what is left is

`y₁(x₁) ⊕ (y₀(x₁) + y₁(x₀)) ⊕ Σ_j planes`.

⚠ This is **not** the compact-`N` ramified row.  That row's core matrix is `((1,1),(1,0))` — the
`x₀`-diagonal, from `x₀^{2+2^α}` — whereas the compact-`M` core matrix is `((0,1),(1,1))`: the
diagonal moves to `x₁`, produced by the one-sided commutator, while `A₀`'s own diagonal
`y₀(K⁻¹x₀)` is cancelled by the correction block.  Both matrices are unimodular over `𝔽₂`, which
is all the Stokes pairing needs, and **no Arf sign is consumed**: the pairing separates primal
from dual coordinates and never evaluates a quadratic form, so the `q = 4` refutation recorded in
`GammaLSourceArfGeneral` does not reach this row and no `f`-parity hypothesis is needed.
-/

namespace GQ2.Dyadic.MCompactRam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert
open GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Certificates.MProcyclic

/-! ## The twist operator -/

/-- **The compact-`M` twist** `K = S₂^m`, `m = 2^{α−1}`: the operator by which the Labute letter
`A₀ = x₀⁻¹σ₂^{−m}` moves.  Every offset in the ramified row is one of `K^j·x_i` for
`j ∈ {−2,−1,0,1,2}`. -/
def mTwist {h : ℕ} {C : Type*} [Group C] (t : Marking (2 + 2 * h) C) (α : ℕ) : C :=
  (powOmega2 t.σ) ^ (mOf α)

variable {h α : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- `S₂^{m·j} = K^j`. -/
theorem sigma2_zpow_eq_mTwist (j : ℤ) :
    (powOmega2 t.σ) ^ ((mOf α : ℤ) * j) = (mTwist t α) ^ j := by
  rw [zpow_mul, zpow_natCast, mTwist]

/-! ## The `σ₂`-powers are second-order pure -/

/-- With the offsets vanishing at `σ`, the `σ₂`-atom is the pure-base lift of `σ^{ω₂}`. -/
theorem heisEvalZ_sigma2W_pure (hxσ : x .sigma = 0) (hyσ : y .sigma = 0)
    (hres : ResolverLifts E C) :
    heisEvalZ ⇑t x y E E₂ (sigma2W : PWord (Generator (2 + 2 * h)))
      = heisPure (powOmega2 t.σ) := by
  have hgen : heisEvalZ ⇑t x y E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
      = heisPure t.σ := by
    rw [heisEvalZ_gen, hxσ, hyσ]
    rfl
  show heisEvalZ ⇑t x y E E₂ (.profPow (.gen .sigma) omega2) = _
  rw [heisEvalZ_profPow, hgen, ← map_zpow, hres t.σ]

/-- Hence every `σ₂`-power with a multiple-of-`m` exponent is the pure lift of a `K`-power. -/
theorem heisEvalZ_sigma2Pow_pure (hxσ : x .sigma = 0) (hyσ : y .sigma = 0)
    (hres : ResolverLifts E C) (j : ℤ) :
    heisEvalZ ⇑t x y E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) ((mOf α : ℤ) * j))
      = heisPure ((mTwist t α) ^ j) := by
  rw [heisEvalZ_zpow, heisEvalZ_sigma2W_pure t x y E E₂ hxσ hyσ hres, ← map_zpow,
    sigma2_zpow_eq_mTwist t j]

/-! ## Factor 1: the Labute letter and its square -/

/-- The Labute letter `A₀ = x₀⁻¹σ₂^{−m}` on ramified normal offsets: the jet of `x₀⁻¹` alone,
with the base moved by `K⁻¹`. -/
theorem heisEvalZ_a0W_ram
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) :
    heisEvalZ ⇑t x y E E₂ (a0W α h)
      = ⟨-x (coreLetter h 0), -y (coreLetter h 0), y (coreLetter h 0) (x (coreLetter h 0)),
          (t (coreLetter h 0))⁻¹ * (mTwist t α) ^ (-1 : ℤ)⟩ := by
  have hinv : heisEvalZ ⇑t x y E E₂ (.inv (.gen (coreLetter h 0)))
      = ⟨-x (coreLetter h 0), -y (coreLetter h 0),
          y (coreLetter h 0) (x (coreLetter h 0)), (t (coreLetter h 0))⁻¹⟩ := by
    rw [heisEvalZ_inv, heisEvalZ_gen]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show -((t (coreLetter h 0))⁻¹ • x (coreLetter h 0)) = _
      rw [mem_trivAct.mp (inv_mem (Certificates.trivAct_coreLetter t hwild 0))]
    · show -((t (coreLetter h 0))⁻¹ • y (coreLetter h 0)) = _
      rw [smul_elemDual_of_trivial
        (mem_trivAct.mp (inv_mem (Certificates.trivAct_coreLetter t hwild 0)))]
    · show (0 : ZMod 2) + y (coreLetter h 0) (x (coreLetter h 0)) = _
      rw [zero_add]
  have hexp : (-(mOf α : ℤ)) = (mOf α : ℤ) * (-1 : ℤ) := by ring
  rw [a0W, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_one, mul_one, hexp,
    heisEvalZ_sigma2Pow_pure t x y E E₂ hxσ hyσ hres (-1 : ℤ), hinv]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show -x (coreLetter h 0) + (t (coreLetter h 0))⁻¹ • (0 : A) = _
    rw [smul_zero, add_zero]
  · show -y (coreLetter h 0) + (t (coreLetter h 0))⁻¹ • (0 : ElemDual A) = _
    rw [smul_zero, add_zero]
  · show y (coreLetter h 0) (x (coreLetter h 0)) + 0
        + (-y (coreLetter h 0)) ((t (coreLetter h 0))⁻¹ • (0 : A)) = _
    rw [smul_zero, map_zero, add_zero, add_zero]

/-- The base of `A₀`. -/
theorem heisEvalZ_a0W_base
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (a0W α h)).g
      = (t (coreLetter h 0))⁻¹ * (mTwist t α) ^ (-1 : ℤ) := by
  rw [heisEvalZ_a0W_ram (α := α) t x y E E₂ hwild hxσ hyσ hres]

/-- `A₀` acts by `K⁻¹`: the wild letter is invisible, the `σ₂`-power is not. -/
theorem heisEvalZ_a0W_smul
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) (v : A) :
    (heisEvalZ ⇑t x y E E₂ (a0W α h)).g • v = (mTwist t α) ^ (-1 : ℤ) • v := by
  rw [heisEvalZ_a0W_base (α := α) t x y E E₂ hwild hxσ hyσ hres, mul_smul,
    mem_trivAct.mp (inv_mem (Certificates.trivAct_coreLetter t hwild 0))]

/-- `A₀⁻¹` acts by `K`. -/
theorem heisEvalZ_a0W_inv_smul
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) (v : A) :
    (heisEvalZ ⇑t x y E E₂ (a0W α h)).g⁻¹ • v = (mTwist t α) ^ (1 : ℤ) • v := by
  rw [heisEvalZ_a0W_base (α := α) t x y E E₂ hwild hxσ hyσ hres, mul_inv_rev, inv_inv, mul_smul,
    mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 0), ← zpow_neg]
  norm_num

/-- The contragredient of `A₀`'s action. -/
theorem heisEvalZ_a0W_smul_dual
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) (lam : ElemDual A) :
    (heisEvalZ ⇑t x y E E₂ (a0W α h)).g • lam = (mTwist t α) ^ (-1 : ℤ) • lam := by
  rw [heisEvalZ_a0W_base (α := α) t x y E E₂ hwild hxσ hyσ hres, mul_smul,
    smul_elemDual_of_trivial
      (mem_trivAct.mp (inv_mem (Certificates.trivAct_coreLetter t hwild 0)))]

/-- The contragredient of `A₀⁻¹`'s action. -/
theorem heisEvalZ_a0W_inv_smul_dual
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) (lam : ElemDual A) :
    (heisEvalZ ⇑t x y E E₂ (a0W α h)).g⁻¹ • lam = (mTwist t α) ^ (1 : ℤ) • lam := by
  rw [heisEvalZ_a0W_base (α := α) t x y E E₂ hwild hxσ hyσ hres, mul_inv_rev, inv_inv, mul_smul,
    smul_elemDual_of_trivial (mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 0)),
    ← zpow_neg]
  norm_num

/-! ## Factor 1: `A₀²` -/

/-- **Factor 1 — `A₀²` on ramified normal offsets.**  Not jet-zero: the jet is the coboundary
`(1 + K⁻¹)·x₀`, and the central value is the *twisted* diagonal `y₀(K⁻¹x₀)`. -/
theorem heisEvalZ_leadingSquare_ram (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2)).a
        = x (coreLetter h 0) + (mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 0) ∧
      (heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2)).l
        = y (coreLetter h 0) + (mTwist t α) ^ (-1 : ℤ) • y (coreLetter h 0) ∧
      (heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2)).z
        = y (coreLetter h 0) ((mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 0)) ∧
      ∀ v : A, (heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2)).g • v
        = (mTwist t α) ^ (-2 : ℤ) • v := by
  have hnegA : ∀ a : A, -a = a := fun a ↦ by
    rw [neg_eq_iff_add_eq_zero]; exact hA₂ a
  have hnegD : ∀ lam : ElemDual A, -lam = lam := fun lam ↦ by
    rw [neg_eq_iff_add_eq_zero]; exact ElemDual.add_self_eq_zero lam
  have hA0 := heisEvalZ_a0W_ram (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hA0s := heisEvalZ_a0W_smul (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hA0sD := heisEvalZ_a0W_smul_dual (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hsq : heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2)
      = heisEvalZ ⇑t x y E E₂ (a0W α h) * heisEvalZ ⇑t x y E E₂ (a0W α h) := by
    rw [heisEvalZ_zpow, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsq, HeisLift.mul_a, hA0s]
    simp only [hA0]
    rw [hnegA]
  · rw [hsq, HeisLift.mul_l, hA0sD]
    simp only [hA0]
    rw [hnegD]
  · rw [hsq, HeisLift.mul_z, hA0s]
    simp only [hA0, smul_neg, ElemDual.neg_apply, map_neg, neg_neg]
    rw [CharTwo.add_self_eq_zero, zero_add]
  · intro v
    rw [hsq, HeisLift.mul_g, mul_smul, hA0s, hA0s, ← mul_smul, ← zpow_add]
    norm_num

/-! ## Factor 2: the Labute commutator `[A₀, x₁]` -/

/-- **Factor 2 — `[A₀,x₁]` on ramified normal offsets.**  The one-sided commutator law: the jet
is the coboundary `(1 + K)·x₁`, and the central value carries — besides the hyperbolic cross
`y₀(x₁) + y₁(x₀)` of the two-sided law — the `x₁`-diagonal `y₁(x₁)` and its twist
`y₁(K⁻¹x₁)`. -/
theorem heisEvalZ_leadingComm_ram (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))).a
        = x (coreLetter h 1) + (mTwist t α) ^ (1 : ℤ) • x (coreLetter h 1) ∧
      (heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))).l
        = y (coreLetter h 1) + (mTwist t α) ^ (1 : ℤ) • y (coreLetter h 1) ∧
      (heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))).z
        = y (coreLetter h 1) (x (coreLetter h 1)) + y (coreLetter h 0) (x (coreLetter h 1))
          + y (coreLetter h 1) (x (coreLetter h 0))
          + y (coreLetter h 1) ((mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 1)) ∧
      ∀ v : A, (heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))).g • v = v := by
  have hnegA : ∀ a : A, -a = a := fun a ↦ by
    rw [neg_eq_iff_add_eq_zero]; exact hA₂ a
  have hnegD : ∀ lam : ElemDual A, -lam = lam := fun lam ↦ by
    rw [neg_eq_iff_add_eq_zero]; exact ElemDual.add_self_eq_zero lam
  have hA0 := heisEvalZ_a0W_ram (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hA0s := heisEvalZ_a0W_smul (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hA0i := heisEvalZ_a0W_inv_smul (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hA0iD := heisEvalZ_a0W_inv_smul_dual (α := α) t x y E E₂ hwild hxσ hyσ hres
  have hx1 : ∀ v : A, t (coreLetter h 1) • v = v :=
    mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 1)
  have hcomm : heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))
      = commR (heisEvalZ ⇑t x y E E₂ (a0W α h)) ⟨x (coreLetter h 1), y (coreLetter h 1), 0,
          t (coreLetter h 1)⟩ := by
    rw [heisEvalZ_comm, heisEvalZ_gen]
  rw [hcomm, heisCommR_of_trivial_right _ _ hx1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show x (coreLetter h 1) - (heisEvalZ ⇑t x y E E₂ (a0W α h)).g⁻¹ • x (coreLetter h 1) = _
    rw [hA0i, sub_eq_add_neg, hnegA]
  · show y (coreLetter h 1) - (heisEvalZ ⇑t x y E E₂ (a0W α h)).g⁻¹ • y (coreLetter h 1) = _
    rw [hA0iD, sub_eq_add_neg, hnegD]
  · show y (coreLetter h 1) (x (coreLetter h 1))
        + (heisEvalZ ⇑t x y E E₂ (a0W α h)).l (x (coreLetter h 1))
        + y (coreLetter h 1) (heisEvalZ ⇑t x y E E₂ (a0W α h)).a
        + y (coreLetter h 1)
            ((heisEvalZ ⇑t x y E E₂ (a0W α h)).g • x (coreLetter h 1)) = _
    rw [hA0s]
    simp only [hA0]
    rw [ElemDual.neg_apply, map_neg, CharTwo.neg_eq, CharTwo.neg_eq]
  · intro v
    show commR (heisEvalZ ⇑t x y E E₂ (a0W α h)).g (t (coreLetter h 1)) • v = v
    exact mem_trivAct.mp
      (Certificates.MCompact.trivAct_commR_right (Certificates.trivAct_coreLetter t hwild 1)) v

/-! ## Factors 3 and 4: the balancing power and the boundary block -/

/-- **Factor 4 — `J₂ = x₂^{-σ}(x₂τ)^{ω₂}` is second-order pure.**  Every letter it uses (`x₂`,
`σ`, `τ`) has vanishing offsets on a ramified normal cochain, so the whole block contributes
nothing but a base — no `τ`-class hypothesis at all. -/
theorem heisEvalZ_j2W_pure
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0) :
    heisEvalZ ⇑t x y E E₂ (j2W h)
      = heisPure ((conjR (t (coreLetter h 2)) t.σ)⁻¹
          * (t (coreLetter h 2) * t.τ) ^ E omega2) := by
  have h2 : heisEvalZ ⇑t x y E E₂ (.gen (coreLetter h 2)) = heisPure (t (coreLetter h 2)) := by
    rw [heisEvalZ_gen, hx2, hy2]
    rfl
  have hs : heisEvalZ ⇑t x y E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
      = heisPure t.σ := by
    rw [heisEvalZ_gen, hxσ, hyσ]
    rfl
  have hτ : heisEvalZ ⇑t x y E E₂ (.gen (Generator.tau : Generator (2 + 2 * h)))
      = heisPure t.τ := by
    rw [heisEvalZ_gen, hxτ, hyτ]
    rfl
  have hinner : heisEvalZ ⇑t x y E E₂
      (PWord.prodList [(.gen (coreLetter h 2) : PWord (Generator (2 + 2 * h))), .gen .tau])
      = heisPure (t (coreLetter h 2) * t.τ) := by
    rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
      heisEvalZ_mul, heisEvalZ_one, mul_one, h2, hτ, ← map_mul]
  rw [j2W, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_one, mul_one, heisEvalZ_inv, heisEvalZ_conj, h2, hs,
    heisPure_conjR, ← map_inv, PWord.omega2Pow,
    heisEvalZ_profPow_of_pure ⇑t x y E E₂ _ _ hinner omega2, ← map_mul]

/-- `J₂` acts trivially: the `ω₂`-block does because `τ`'s `2`-primary part does. -/
theorem heisEvalZ_j2W_smul [Finite C]
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) (hres : ResolverLifts E C) (v : A) :
    (heisEvalZ ⇑t x y E E₂ (j2W h)).g • v = v := by
  rw [heisEvalZ_g, evalZ_eq_evalFin_of_resolverLifts hres ⇑t (j2W h)]
  exact Certificates.MCompact.evalFin_j2W_smul t E E₂ hwild
    (Certificates.MCompact.trivAct_deltaBlock_ram t E E₂ hwild hTodd 2) v

/-! ## Factor 5: the `δ`-letters and the reversed correction block -/

/-- **The `δ`-letter `δ_i = (x_iτ)^{ω₂}x_i⁻¹` in the ramified class.**  Its jet is the plain
`x_i`-offset on both sides — the `ω₂`-block is jet-zero because the geometric sum over a
fixed-point-free `τ` vanishes, which is exactly the content of the first-order row
`foxD_deltaC_ram`, lifted to the Heisenberg jet by `heisEvalZ_a_eq_foxD`/`_l_eq_foxD`.  Its base
acts trivially, and its central charge is left opaque: it enters the correction block twice and
cancels. -/
theorem heisEvalZ_deltaCert_ram [Finite C] [Finite A] (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) (i : Fin 3) :
    (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).a = x (coreLetter h i) ∧
      (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).l = y (coreLetter h i) ∧
      ∀ v : A, (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).g • v = v := by
  have hnegA : ∀ a : A, -a = a := fun a ↦ by
    rw [neg_eq_iff_add_eq_zero]; exact hA₂ a
  have hnegD : ∀ lam : ElemDual A, -lam = lam := fun lam ↦ by
    rw [neg_eq_iff_add_eq_zero]; exact ElemDual.add_self_eq_zero lam
  have hwildD : ∀ (j : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x j • lam = lam :=
    fun j lam ↦ elemDual_smul_eq_self (hwild j) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hTodd lam
  refine ⟨?_, ?_, ?_⟩
  · rw [heisEvalZ_a_eq_foxD hresA ⇑t x y (deltaCert h i),
      Certificates.MCompact.foxD_deltaC_ram t E E₂ hwild hτfpf hTodd i, hnegA]
  · rw [heisEvalZ_l_eq_foxD hresD ⇑t x y (deltaCert h i),
      Certificates.MCompact.foxD_deltaC_ram (V := ElemDual A) t E E₂ hwildD hτfpfD hToddD i,
      hnegD]
  · intro v
    rw [heisEvalZ_g, evalZ_eq_evalFin_of_resolverLifts hres ⇑t (deltaCert h i)]
    exact mem_trivAct.mp (Certificates.MCompact.trivAct_deltaC t E E₂ hwild i
      (Certificates.MCompact.trivAct_deltaBlock_ram t E E₂ hwild hTodd i)) v

set_option maxHeartbeats 1600000 in
/-- **Factor 5 — the reversed correction block `E_m^rev = δ₁^{σ₂^{2m}}δ₁^{σ₂^{m}}δ₀^{σ₂^{m}}δ₀`.**

Each conjugator is a *pure* `σ₂`-power, so it twists the jet by `K^{−j}` and leaves the central
charge alone.  The four charges therefore appear in cancelling pairs and the whole central value
is the six ordered cross pairings. -/
theorem heisEvalZ_eRevW_ram [Finite C] [Finite A] (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (eRevW α h)).a
        = (mTwist t α) ^ (-2 : ℤ) • x (coreLetter h 1)
          + ((mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 1)
            + ((mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 0) + x (coreLetter h 0))) ∧
      (heisEvalZ ⇑t x y E E₂ (eRevW α h)).l
        = (mTwist t α) ^ (-2 : ℤ) • y (coreLetter h 1)
          + ((mTwist t α) ^ (-1 : ℤ) • y (coreLetter h 1)
            + ((mTwist t α) ^ (-1 : ℤ) • y (coreLetter h 0) + y (coreLetter h 0))) ∧
      (heisEvalZ ⇑t x y E E₂ (eRevW α h)).z
        = y (coreLetter h 1) ((mTwist t α) ^ (1 : ℤ) • x (coreLetter h 1))
          + y (coreLetter h 1) ((mTwist t α) ^ (2 : ℤ) • x (coreLetter h 0))
          + y (coreLetter h 1) (x (coreLetter h 0))
          + y (coreLetter h 0) ((mTwist t α) ^ (1 : ℤ) • x (coreLetter h 0)) := by
  have hδ := fun i ↦ heisEvalZ_deltaCert_ram t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres i
  have hconj : ∀ (i : Fin 3) (k j : ℤ), k = (mOf α : ℤ) * j →
      heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h i) (.zpow sigma2W k))
        = ⟨(mTwist t α) ^ (-j) • x (coreLetter h i),
            (mTwist t α) ^ (-j) • y (coreLetter h i),
            (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).z,
            conjR (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).g ((mTwist t α) ^ j)⟩ := by
    intro i k j hk
    subst hk
    rw [heisEvalZ_conj, heisEvalZ_sigma2Pow_pure t x y E E₂ hxσ hyσ hres j,
      heisConjR_of_trivial _ _ (hδ i).2.2]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show ((mTwist t α) ^ j)⁻¹ • (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).a = _
      rw [(hδ i).1, ← zpow_neg]
    · show ((mTwist t α) ^ j)⁻¹ • (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).l = _
      rw [(hδ i).2.1, ← zpow_neg]
    · show (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).z
          + (0 : ElemDual A) (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).a
          + (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).l (0 : A) = _
      rw [ElemDual.zero_apply, map_zero, add_zero, add_zero]
  have hprod : heisEvalZ ⇑t x y E E₂ (eRevW α h)
      = heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ))))
        * (heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ)))
          * (heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ)))
            * heisEvalZ ⇑t x y E E₂ (deltaCert h 0))) := by
    rw [eRevW, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_cons,
      PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_mul,
      heisEvalZ_mul, heisEvalZ_one, mul_one]
  have htriv : ∀ (i : Fin 3) (j : ℤ) (v : A),
      (conjR (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).g ((mTwist t α) ^ j)) • v = v := fun i j ↦
    mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr (hδ i).2.2) _)
  have hc1 := hconj 1 (2 * (mOf α : ℤ)) 2 (by ring)
  have hc2 := hconj 1 (mOf α : ℤ) 1 (by ring)
  have hc3 := hconj 0 (mOf α : ℤ) 1 (by ring)
  have hb1 : ∀ v : A, (heisEvalZ ⇑t x y E E₂
      (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ))))).g • v = v := by
    rw [hc1]; exact htriv 1 2
  have hb2 : ∀ v : A, (heisEvalZ ⇑t x y E E₂
      (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ)))).g • v = v := by
    rw [hc2]; exact htriv 1 1
  have hb3 : ∀ v : A, (heisEvalZ ⇑t x y E E₂
      (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ)))).g • v = v := by
    rw [hc3]; exact htriv 0 1
  obtain ⟨ha, hl, hz⟩ := heisMul_four_of_trivial
    (heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ)))))
    (heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ))))
    (heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ))))
    (heisEvalZ ⇑t x y E E₂ (deltaCert h 0)) hb1 hb2 hb3
  refine ⟨?_, ?_, ?_⟩
  · rw [hprod, ha]
    simp only [hc1, hc2, hc3, (hδ 0).1]
  · rw [hprod, hl]
    simp only [hc1, hc2, hc3, (hδ 0).2.1]
  · rw [hprod, hz]
    simp only [hc1, hc2, hc3, (hδ 0).1]
    have n21 : ∀ (lam : ElemDual A) (v : A),
        ((mTwist t α ^ (-2 : ℤ)) • lam) ((mTwist t α ^ (-1 : ℤ)) • v)
          = lam ((mTwist t α ^ (1 : ℤ)) • v) := fun lam v ↦ by
      rw [elemDual_zpow_smul_apply]; norm_num
    have n20 : ∀ (lam : ElemDual A) (v : A), ((mTwist t α ^ (-2 : ℤ)) • lam) v
        = lam ((mTwist t α ^ (2 : ℤ)) • v) := fun lam v ↦ by
      rw [elemDual_zpow_smul_apply_right]; norm_num
    have n11 : ∀ (lam : ElemDual A) (v : A),
        ((mTwist t α ^ (-1 : ℤ)) • lam) ((mTwist t α ^ (-1 : ℤ)) • v) = lam v := fun lam v ↦ by
      rw [elemDual_zpow_smul_apply]; norm_num
    have n10 : ∀ (lam : ElemDual A) (v : A), ((mTwist t α ^ (-1 : ℤ)) • lam) v
        = lam ((mTwist t α ^ (1 : ℤ)) • v) := fun lam v ↦ by
      rw [elemDual_zpow_smul_apply_right]; norm_num
    rw [n21, n21, n20, n11, n10, n10]
    generalize (heisEvalZ ⇑t x y E E₂ (deltaCert h 1)).z = c₁
    generalize (heisEvalZ ⇑t x y E E₂ (deltaCert h 0)).z = c₂
    generalize y (coreLetter h 1) ((mTwist t α ^ (1 : ℤ)) • x (coreLetter h 1)) = c₃
    generalize y (coreLetter h 1) ((mTwist t α ^ (1 : ℤ)) • x (coreLetter h 0)) = c₄
    generalize y (coreLetter h 1) ((mTwist t α ^ (2 : ℤ)) • x (coreLetter h 0)) = c₅
    generalize y (coreLetter h 1) (x (coreLetter h 0)) = c₆
    generalize y (coreLetter h 0) ((mTwist t α ^ (1 : ℤ)) • x (coreLetter h 0)) = c₇
    revert c₁ c₂ c₃ c₄ c₅ c₆ c₇
    decide

/-! ## The two surviving cross terms

The `A₀²`-`[A₀,x₁]` cross and the `(A₀²[A₀,x₁])`-`E_m^rev` cross, each already cancelled over
`𝔽₂`.  They are stated for an arbitrary group element `c` because nothing about `K` enters
beyond the exponent arithmetic. -/

/-- The `[A₀,x₁]`-against-`E_m^rev` cross term. -/
theorem crossA_eq (c : C) (lam : ElemDual A) (u v : A) :
    (lam + c ^ (1 : ℤ) • lam)
        (c ^ (2 : ℤ) • (c ^ (-2 : ℤ) • u
          + (c ^ (-1 : ℤ) • u + (c ^ (-1 : ℤ) • v + v))))
      = lam (c ^ (1 : ℤ) • u) + lam (c ^ (2 : ℤ) • v)
        + lam (c ^ (-1 : ℤ) • u) + lam v := by
  have e0 : ∀ (i j : ℤ) (w : A), c ^ i • (c ^ j • w) = c ^ (i + j) • w :=
    zpow_smul_zpow_smul c
  rw [smul_add, smul_add, smul_add, e0, e0, e0]
  norm_num only [show ((2 : ℤ) + -2) = 0 by norm_num, show ((2 : ℤ) + -1) = 1 by norm_num,
    zpow_zero, one_smul]
  rw [ElemDual.add_apply, map_add, map_add, map_add, map_add, map_add, map_add,
    elemDual_zpow_smul_apply_right, elemDual_zpow_smul_apply, elemDual_zpow_smul_apply,
    elemDual_zpow_smul_apply]
  norm_num only [show ((1 : ℤ) - 1) = 0 by norm_num, show ((2 : ℤ) - 1) = 1 by norm_num,
    show (-(1 : ℤ)) = -1 by norm_num, zpow_zero, one_smul]
  generalize lam u = c₁
  generalize lam (c ^ (1 : ℤ) • u) = c₂
  generalize lam (c ^ (1 : ℤ) • v) = c₃
  generalize lam (c ^ (2 : ℤ) • v) = c₄
  generalize lam (c ^ (-1 : ℤ) • u) = c₅
  generalize lam v = c₆
  revert c₁ c₂ c₃ c₄ c₅ c₆
  decide

/-- The `A₀²`-against-everything-later cross term. -/
theorem crossB_eq (c : C) (lam : ElemDual A) (u v : A) :
    (lam + c ^ (-1 : ℤ) • lam)
        (c ^ (-2 : ℤ) • (u + c ^ (1 : ℤ) • u)
          + (c ^ (-2 : ℤ) • u + (c ^ (-1 : ℤ) • u + (c ^ (-1 : ℤ) • v + v))))
      = lam (c ^ (-1 : ℤ) • v) + lam (c ^ (1 : ℤ) • v) := by
  have e0 : ∀ (i j : ℤ) (w : A), c ^ i • (c ^ j • w) = c ^ (i + j) • w :=
    zpow_smul_zpow_smul c
  rw [smul_add, e0]
  norm_num only [show ((-2 : ℤ) + 1) = -1 by norm_num]
  simp only [ElemDual.add_apply, map_add]
  simp only [elemDual_zpow_smul_apply]
  simp only [elemDual_zpow_smul_apply_right]
  norm_num only [show ((-2 : ℤ) - -1) = -1 by norm_num, show ((-1 : ℤ) - -1) = 0 by norm_num,
    show (-(-1 : ℤ)) = 1 by norm_num, zpow_zero, one_smul]
  generalize lam (c ^ (-2 : ℤ) • u) = c₁
  generalize lam (c ^ (-1 : ℤ) • u) = c₂
  generalize lam (c ^ (-1 : ℤ) • v) = c₃
  generalize lam v = c₄
  generalize lam u = c₅
  generalize lam (c ^ (1 : ℤ) • v) = c₆
  revert c₁ c₂ c₃ c₄ c₅ c₆
  decide

/-! ## The assembled ramified row -/

set_option maxHeartbeats 1600000 in
/-- **The compact-`M` second-order row on ramified normal offsets** — the residual input of
`M0RamifiedStokes`.

Every `K`-twisted contribution cancels over `𝔽₂`: `A₀`'s own diagonal `y₀(K⁻¹x₀)` against the
`A₀²`-`E_m^rev` cross, the `E`-block's `x₁`-terms against the `[A₀,x₁]`-`E_m^rev` cross, and the
`x₀`-cross terms in pairs.  What survives is the unimodular core `((0,1),(1,1))` — the
`x₁`-diagonal and the hyperbolic cross — plus the `h` identity-operator handle planes.

⚠ The `x₀`-diagonal of the compact-`N` ramified row is **not** here; the compact-`M` row's
diagonal sits on `x₁`. -/
theorem heisZ_mCompact_ram [Finite C] [Finite A] (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (mCompactW α h)).z
      = y (coreLetter h 1) (x (coreLetter h 1))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  obtain ⟨h1a, h1l, h1z, h1g⟩ :=
    heisEvalZ_leadingSquare_ram (α := α) t x y E E₂ hA₂ hwild hxσ hyσ hres
  obtain ⟨h2a, h2l, h2z, h2g⟩ :=
    heisEvalZ_leadingComm_ram (α := α) t x y E E₂ hA₂ hwild hxσ hyσ hres
  have h3 : heisEvalZ ⇑t x y E E₂
      (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (2 * (mOf α : ℤ)))
      = heisPure ((mTwist t α) ^ (2 : ℤ)) := by
    rw [show (2 * (mOf α : ℤ)) = (mOf α : ℤ) * 2 by ring]
    exact heisEvalZ_sigma2Pow_pure t x y E E₂ hxσ hyσ hres 2
  have h4 := heisEvalZ_j2W_pure t x y E E₂ hxσ hyσ hxτ hyτ hx2 hy2
  have h4g := heisEvalZ_j2W_smul t x y E E₂ hwild hTodd hres
  have h4jets : (heisEvalZ ⇑t x y E E₂ (j2W h)).a = 0
      ∧ (heisEvalZ ⇑t x y E E₂ (j2W h)).l = 0
      ∧ (heisEvalZ ⇑t x y E E₂ (j2W h)).z = 0 := by
    rw [h4]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨h5a, h5l, h5z⟩ := heisEvalZ_eRevW_ram (α := α) t x y E E₂ hA₂ hwild hτfpf hTodd
    hxσ hyσ hresA hresD hres
  have h6mem := Certificates.MCompact.heisF_handlesW_mem t x y E E₂ hwild
  have h6z := Certificates.MCompact.heisF_handlesW_z t x y E E₂ hwild
  rw [mCompactW, heisEvalZ_prodList, List.map_append, List.prod_append,
    Certificates.MCompact.heisEvalZ_handleTailW t x y E E₂]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [heisMul_z_of_a_eq_zero _ _ h6mem.1,
    heisMul_five_z _ _ _ _ _ ((mTwist t α) ^ (2 : ℤ)) h3 h4jets h4g h2g, h1g, smul_add,
    zpow_smul_zpow_smul]
  norm_num only [show ((-2 : ℤ) + 2) = 0 by norm_num, zpow_zero, one_smul]
  rw [h2a, h5a, h2l, h1l, crossA_eq, crossB_eq, h1z, h2z, h5z, h6z]
  generalize y (coreLetter h 0) ((mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 0)) = c₁
  generalize y (coreLetter h 1) (x (coreLetter h 1)) = c₂
  generalize y (coreLetter h 0) (x (coreLetter h 1)) = c₃
  generalize y (coreLetter h 1) (x (coreLetter h 0)) = c₄
  generalize y (coreLetter h 1) ((mTwist t α) ^ (-1 : ℤ) • x (coreLetter h 1)) = c₅
  generalize y (coreLetter h 1) ((mTwist t α) ^ (1 : ℤ) • x (coreLetter h 1)) = c₆
  generalize y (coreLetter h 1) ((mTwist t α) ^ (2 : ℤ) • x (coreLetter h 0)) = c₇
  generalize y (coreLetter h 0) ((mTwist t α) ^ (1 : ℤ) • x (coreLetter h 0)) = c₈
  generalize (∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j)))) = c₉
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉
  decide

end

end GQ2.Dyadic.MCompactRam

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.MCompactRam.sigma2_zpow_eq_mTwist
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_sigma2W_pure
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_sigma2Pow_pure
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_a0W_ram
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_a0W_base
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_a0W_smul
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_a0W_inv_smul
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_a0W_smul_dual
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_a0W_inv_smul_dual
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_leadingSquare_ram
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_leadingComm_ram
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_j2W_pure
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_j2W_smul
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_deltaCert_ram
#print axioms GQ2.Dyadic.MCompactRam.heisEvalZ_eRevW_ram
#print axioms GQ2.Dyadic.MCompactRam.crossA_eq
#print axioms GQ2.Dyadic.MCompactRam.crossB_eq
#print axioms GQ2.Dyadic.MCompactRam.heisZ_mCompact_ram

end AxiomAudit
