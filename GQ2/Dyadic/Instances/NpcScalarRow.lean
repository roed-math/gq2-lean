/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcUnramifiedBranch

/-!
# The procyclic-`N` second-order row at a completely trivial action, with a free `sigma`

`Certificates.Npc.heisZ_npc_scalar` reads the corrected procyclic-`N` word at a trivial action
*on `sigma`-free offsets*.  That is not enough for the scalar sub-branch: with a trivial action
the bottom differential vanishes, so the `sigma`-coordinate of a normal cochain is **free** and
the row has to be read with `x_σ` and `y_σ` present.

This file does that.  Every base acts trivially, so the whole computation is the class-`2` free
one, and only two factors change: the front block `[x₀, A]` with `A = σ^{n_η}` and the boundary
block `(x₂^{x₁B})⁻¹` with `B = σ^{2^r}` now see the `sigma`-offsets, through the *integers*
`n_η = E(η̂)` and `2^r`.  The result is

```
y₀(x₀) + n_η·(y₀(x_σ) + y_σ(x₀)) + (y₁(x₂) + y₂(x₁)) + 2^r·(y_σ(x₂) + y₂(x_σ)) + Σ handles
```

on `tau`-free offsets: the compact scalar Gram matrix *plus* two `sigma`-hyperbolic planes whose
coefficients are the two conjugator exponents read modulo `2`.  At `x_σ = y_σ = 0` it is
`heisZ_npc_scalar`, as it must be.

**The `n_η`-parity is load-bearing.**  `2^r` is even for every noncompact `r ≥ 1`, so the
`(x_σ, x₂)` plane degenerates and the *only* thing that can see `x_σ` is the `n_η`-plane.  This
is the precise point at which the scalar sub-branch needs `η` to be a `2`-adic **unit**; see
`NpcUnramifiedScalar`, where the left kernel is exhibited when it is not.
-/

namespace GQ2.Dyadic.NProcyclicUnram

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.Npc
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count

/-! ## Every base of a trivially-marked word acts trivially -/

section Bases

/-- **A word in trivially-acting letters acts trivially**, at every `PWord` constructor: the
trivial-action subgroup is closed under products, inverses, conjugates, commutators, integer
powers and the `2`-primary power. -/
theorem trivAct_evalFin_of_gens {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (μ : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hμ : ∀ g : X, μ g ∈ trivAct C A) :
    ∀ w : PWord X, PWord.evalFin μ E E₂ w ∈ trivAct C A
  | .one => one_mem _
  | .gen g => hμ g
  | .mul u v => mul_mem (trivAct_evalFin_of_gens μ E E₂ hμ u)
      (trivAct_evalFin_of_gens μ E E₂ hμ v)
  | .inv u => inv_mem (trivAct_evalFin_of_gens μ E E₂ hμ u)
  | .conj u g => trivAct_conjR (trivAct_evalFin_of_gens μ E E₂ hμ u) _
  | .comm u v => trivAct_commR (trivAct_evalFin_of_gens μ E E₂ hμ u)
      (trivAct_evalFin_of_gens μ E E₂ hμ v)
  | .zpow u _ => zpow_mem (trivAct_evalFin_of_gens μ E E₂ hμ u) _
  | .z2pow u _ => zpow_mem (trivAct_evalFin_of_gens μ E E₂ hμ u) _
  | .profPow u γ => by
      rw [PWord.evalFin]
      by_cases hγ : γ = omega2
      · rw [if_pos hγ]
        exact trivAct_powOmega2 (trivAct_evalFin_of_gens μ E E₂ hμ u)
      · rw [if_neg hγ]
        exact zpow_mem (trivAct_evalFin_of_gens μ E E₂ hμ u) _

/-- The Heisenberg base of every subword of a trivially-marked word acts trivially. -/
theorem heisEvalZ_g_smul_eq {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (μ : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (x : X → A) (y : X → ElemDual A) (hres : ResolverLifts E C)
    (hμ : ∀ g : X, μ g ∈ trivAct C A) (w : PWord X) (v : A) :
    (heisEvalZ μ x y E E₂ w).g • v = v := by
  rw [heisEvalZ_g, evalZ_eq_evalFin_of_resolverLifts hres μ w]
  exact mem_trivAct.mp (trivAct_evalFin_of_gens μ E E₂ hμ w) v

end Bases

/-! ## The two `sigma`-sensitive factors -/

section Factors

variable {h r : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The `η̂`-conjugator with a free `sigma`-offset**: `A = σ^{n_η}` carries the jets
`n_η·x_σ` and `n_η·y_σ`. -/
theorem heisF_aW_free (hσ : ∀ v : A, t.σ • v = v) (d : EtaData) {nn : ℕ}
    (hEη : E d.toZhat = (nn : ℤ)) :
    heisEvalZ ⇑t x y E E₂ (aW h d)
      = ⟨nn • x .sigma, nn • y .sigma, (nn.choose 2) • y .sigma (x .sigma), t.σ ^ (nn : ℕ)⟩ := by
  rw [aW, heisEvalZ_profPow, heisEvalZ_gen, hEη, zpow_natCast,
    heisPow_of_trivial (⟨x .sigma, y .sigma, 0, t Generator.sigma⟩ : HeisLift A C) hσ nn]
  refine HeisLift.ext rfl rfl ?_ rfl
  show nn • (0 : ZMod 2) + (nn.choose 2) • y .sigma (x .sigma) = _
  rw [smul_zero, zero_add]

/-- **The boundary conjugator with a free `sigma`-offset**: `B = σ^{2^r}` carries the jets
`2^r·x_σ` and `2^r·y_σ`. -/
theorem heisF_bW_free (hσ : ∀ v : A, t.σ • v = v) :
    heisEvalZ ⇑t x y E E₂ (bW h r)
      = ⟨(2 ^ r : ℕ) • x .sigma, (2 ^ r : ℕ) • y .sigma,
          ((2 ^ r : ℕ).choose 2) • y .sigma (x .sigma), t.σ ^ (2 ^ r : ℕ)⟩ := by
  rw [bW, heisEvalZ_zpow, heisEvalZ_gen, show ((2 : ℤ) ^ r) = ((2 ^ r : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast,
    heisPow_of_trivial (⟨x .sigma, y .sigma, 0, t Generator.sigma⟩ : HeisLift A C) hσ (2 ^ r)]
  refine HeisLift.ext rfl rfl ?_ rfl
  show (2 ^ r : ℕ) • (0 : ZMod 2) + ((2 ^ r : ℕ).choose 2) • y .sigma (x .sigma) = _
  rw [smul_zero, zero_add]

/-- **Factor 2 with a free `sigma`-offset, at a trivial action**: the front block `[x₀, A]` is
jet-zero with the `n_η`-scaled hyperbolic value on `(x₀, x_σ)`. -/
theorem heisF_commX0A_free (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v)
    (d : EtaData) {nn : ℕ} (hEη : E d.toZhat = (nn : ℤ)) :
    (heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (aW h d))).z
      = nn • y (coreLetter h 0) (x .sigma) + nn • y .sigma (x (coreLetter h 0)) := by
  have hAg : ∀ v : A, (t.σ ^ (nn : ℕ)) • v = v := fun v =>
    mem_trivAct.mp (pow_mem (mem_trivAct.mpr (htriv Generator.sigma)) nn) v
  rw [heisEvalZ_comm, heisEvalZ_gen, heisF_aW_free t x y E E₂ (htriv Generator.sigma) d hEη,
    heisCommR_of_trivial _ _ (htriv (coreLetter h 0)) hAg]
  show y (coreLetter h 0) (nn • x .sigma) + (nn • y .sigma) (x (coreLetter h 0)) = _
  rw [map_nsmul, elemDual_nsmul_apply]

/-- **Factor 3 with a free `sigma`-offset, at a trivial action**: the boundary block
`(x₂^{x₁B})⁻¹` acquires the `2^r`-scaled hyperbolic value on `(x₂, x_σ)` on top of the compact
row's `(x₁, x₂)` plane and its `x₂`-diagonal. -/
theorem heisF_invConjX2G_free (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) :
    (heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 2))
        (PWord.prodList [.gen (coreLetter h 1), bW h r])))).z
      = y (coreLetter h 1) (x (coreLetter h 2)) + (2 ^ r : ℕ) • y .sigma (x (coreLetter h 2))
        + y (coreLetter h 2) (x (coreLetter h 1))
        + (2 ^ r : ℕ) • y (coreLetter h 2) (x .sigma)
        + y (coreLetter h 2) (x (coreLetter h 2)) := by
  have hBg : ∀ v : A, (t.σ ^ (2 ^ r : ℕ)) • v = v := fun v =>
    mem_trivAct.mp (pow_mem (mem_trivAct.mpr (htriv Generator.sigma)) (2 ^ r)) v
  have hgconj : heisEvalZ ⇑t x y E E₂ (PWord.prodList [.gen (coreLetter h 1), bW h r])
      = ⟨x (coreLetter h 1) + (2 ^ r : ℕ) • x .sigma,
          y (coreLetter h 1) + (2 ^ r : ℕ) • y .sigma,
          ((2 ^ r : ℕ).choose 2) • y .sigma (x .sigma)
            + (2 ^ r : ℕ) • y (coreLetter h 1) (x .sigma),
          t (coreLetter h 1) * t.σ ^ (2 ^ r : ℕ)⟩ := by
    rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_one, mul_one, heisF_bW_free t x y E E₂
        (htriv Generator.sigma)]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show x (coreLetter h 1) + t (coreLetter h 1) • ((2 ^ r : ℕ) • x .sigma) = _
      rw [htriv (coreLetter h 1)]
    · show y (coreLetter h 1) + t (coreLetter h 1) • ((2 ^ r : ℕ) • y .sigma) = _
      rw [smul_elemDual_of_trivial (htriv (coreLetter h 1))]
    · show (0 : ZMod 2) + ((2 ^ r : ℕ).choose 2) • y .sigma (x .sigma)
        + y (coreLetter h 1) (t (coreLetter h 1) • ((2 ^ r : ℕ) • x .sigma)) = _
      rw [htriv (coreLetter h 1), map_nsmul, zero_add]
  rw [heisEvalZ_inv_z, heisEvalZ_conj, heisEvalZ_gen, hgconj,
    heisConjR_of_trivial _ _ (htriv (coreLetter h 2))]
  have hbase : ∀ v : A, (t (coreLetter h 1) * t.σ ^ (2 ^ r : ℕ))⁻¹ • v = v := fun v => by
    rw [mul_inv_rev, mul_smul, inv_smul_eq_iff.mpr (htriv (coreLetter h 1) v).symm,
      inv_smul_eq_iff.mpr (hBg v).symm]
  show (0 : ZMod 2) + (y (coreLetter h 1) + (2 ^ r : ℕ) • y .sigma) (x (coreLetter h 2))
      + y (coreLetter h 2) (x (coreLetter h 1) + (2 ^ r : ℕ) • x .sigma)
      + ((t (coreLetter h 1) * t.σ ^ (2 ^ r : ℕ))⁻¹ • y (coreLetter h 2))
          ((t (coreLetter h 1) * t.σ ^ (2 ^ r : ℕ))⁻¹ • x (coreLetter h 2)) = _
  rw [smul_elemDual_of_trivial hbase, hbase, ElemDual.add_apply, map_add, map_nsmul,
    elemDual_nsmul_apply, zero_add]
  abel

end Factors

/-! ## The assembled scalar row -/

section Row

variable {h α r : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The scalar product law.**  Factors `1`, `2`, `5`, `6` are jet-zero and factor `3`'s base
acts trivially, so of the fifteen possible cross terms exactly one survives: `λ₃(a₄)`, the
boundary block's operator against the `ω₂`-block's jet. -/
theorem heisMul_six_z_scalar {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (P1 P2 P3 P4 P5 P6 : HeisLift A C)
    (h1 : P1 ∈ heisJetZero A C) (h2 : P2 ∈ heisJetZero A C) (h5 : P5 ∈ heisJetZero A C)
    (h6 : P6 ∈ heisJetZero A C) (h3g : ∀ v : A, P3.g • v = v) :
    (P1 * (P2 * (P3 * (P4 * (P5 * P6))))).z
      = P1.z + P2.z + P3.z + P4.z + P5.z + P6.z + P3.l P4.a := by
  have h56a : (P5 * P6).a = 0 := by rw [HeisLift.mul_a, h5.1, h6.1, smul_zero, add_zero]
  have h56z : (P5 * P6).z = P5.z + P6.z := heisJetZero_mul_z h5
  have h456a : (P4 * (P5 * P6)).a = P4.a := by
    rw [HeisLift.mul_a, h56a, smul_zero, add_zero]
  have h456z : (P4 * (P5 * P6)).z = P4.z + (P5.z + P6.z) := by
    rw [heisMul_z_of_a_eq_zero _ _ h56a, h56z]
  have h3456z : (P3 * (P4 * (P5 * P6))).z = P3.z + (P4.z + (P5.z + P6.z)) + P3.l P4.a := by
    rw [HeisLift.mul_z, h456z, h456a, h3g]
  rw [heisJetZero_mul_z h1, heisJetZero_mul_z h2, h3456z]
  abel

set_option maxHeartbeats 3200000 in
/-- **The corrected procyclic-`N` second-order row at a completely trivial action, with a free
`sigma`-coordinate and `tau`-free offsets.**

The compact scalar Gram matrix, plus the two `sigma`-hyperbolic planes whose coefficients are
the conjugator exponents `n_η = E(η̂)` and `2^r` read modulo `2`.  The correction block is pure
`tau` and therefore dies; the `ω₂`-block and the `x₂`-diagonal cancel against the single surviving
cross term, exactly as in `heisZ_npc_scalar`. -/
theorem heisZ_npc_scalar_free (hA₂ : ∀ v : A, v + v = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v)
    (hres : ResolverLifts E C) (hxτ : x .tau = 0) (hyτ : y .tau = 0) (hα : 2 ≤ α)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (d : EtaData) {nn : ℕ}
    (hEη : E d.toZhat = (nn : ℤ)) :
    (heisEvalZ ⇑t x y E E₂ (npcW α r h d)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (nn • y (coreLetter h 0) (x .sigma) + nn • y .sigma (x (coreLetter h 0)))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1)))
        + ((2 ^ r : ℕ) • y .sigma (x (coreLetter h 2))
            + (2 ^ r : ℕ) • y (coreLetter h 2) (x .sigma))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hodd : Odd e := odd_of_mod_four_eq_one he
  have hoddsmul : ∀ v : A, e • v = v := by
    intro v
    obtain ⟨m, hm⟩ := hodd
    rw [hm, add_nsmul, mul_nsmul', two_nsmul, hA₂, zero_add, one_nsmul]
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v := fun i v => htriv _ v
  have hτ : ∀ v : A, t.τ • v = v := fun v => htriv _ v
  have hμ : ∀ g : Generator (2 + 2 * h), ⇑t g ∈ trivAct C A :=
    fun g => mem_trivAct.mpr (htriv g)
  have hgtriv : ∀ (w : PWord (Generator (2 + 2 * h))) (v : A),
      (heisEvalZ ⇑t x y E E₂ w).g • v = v :=
    fun w v => heisEvalZ_g_smul_eq ⇑t E E₂ x y hres hμ w v
  have hinvl : ∀ w : PWord (Generator (2 + 2 * h)),
      (heisEvalZ ⇑t x y E E₂ (.inv w)).l = (heisEvalZ ⇑t x y E E₂ w).l := by
    intro w
    rw [heisEvalZ_inv, HeisLift.inv_l,
      smul_elemDual_of_trivial (fun v => inv_smul_eq_iff.mpr (hgtriv w v).symm)]
    exact neg_eq_of_add_eq_zero_left (ElemDual.add_self_eq_zero _)
  have hconjl : ∀ u g : PWord (Generator (2 + 2 * h)),
      (heisEvalZ ⇑t x y E E₂ (.conj u g)).l = (heisEvalZ ⇑t x y E E₂ u).l := by
    intro u g
    rw [heisEvalZ_conj, heisConjR_of_trivial _ _ (hgtriv u)]
    exact smul_elemDual_of_trivial (fun v => inv_smul_eq_iff.mpr (hgtriv g v).symm) _
  -- the six factors
  have e1 := Certificates.Npc.heisF_leadingPow t x y E E₂ hA₂ hwild hα (α := α)
  have e2 := heisF_commX0A_free t x y E E₂ htriv d hEη
  have e3 := heisF_invConjX2G_free (r := r) t x y E E₂ htriv
  have e4 := heisF_omega2Block t x y E E₂ 2 hwild hτ hE
  -- the `δ₀`-letter is jet-zero on `tau`-free offsets, hence so is the whole `D`-block
  have hδa : (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).a = 0 := by
    rw [heisJetA_deltaZeroW_odd t x y E E₂ hA₂ hwild hτ hE hodd, hxτ]
  have hδl : (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).l = 0 := by
    rw [heisJetL_deltaZeroW_odd t x y E E₂ hwild hτ hE hodd, hyτ]
  have hconjjz : ∀ u g : PWord (Generator (2 + 2 * h)),
      heisEvalZ ⇑t x y E E₂ u ∈ heisJetZero A C →
        heisEvalZ ⇑t x y E E₂ (.conj u g) ∈ heisJetZero A C := by
    intro u g hu
    rw [heisEvalZ_conj, heisConjR_of_trivial _ _ (hgtriv u)]
    exact ⟨by show _ • (heisEvalZ ⇑t x y E E₂ u).a = 0; rw [hu.1, smul_zero],
      by show _ • (heisEvalZ ⇑t x y E E₂ u).l = 0; rw [hu.2, smul_zero]⟩
  have hδjz : heisEvalZ ⇑t x y E E₂ (deltaZeroW h) ∈ heisJetZero A C := ⟨hδa, hδl⟩
  have hDjz : heisEvalZ ⇑t x y E E₂ (dBlockW h r d) ∈ heisJetZero A C := by
    rw [dBlockW, prodList_pair, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one]
    refine mul_mem (hconjjz _ _ hδjz) (hconjjz _ _ ?_)
    rw [prodList_pair, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one]
    exact mul_mem hδjz (hconjjz _ _ hδjz)
  have e5 : heisEvalZ ⇑t x y E E₂ (eBlockW h r d)
      = ⟨0, 0, 0, commR (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).g (t (coreLetter h 1))⟩ := by
    rw [eBlockW, heisEvalZ_comm, heisEvalZ_gen,
      heisCommR_of_trivial _ _ (hgtriv (dBlockW h r d)) (htriv (coreLetter h 1))]
    refine HeisLift.ext rfl rfl ?_ rfl
    show (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).l (x (coreLetter h 1))
      + y (coreLetter h 1) (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).a = 0
    rw [hDjz.1, hDjz.2, ElemDual.zero_apply, map_zero, add_zero]
  have h6mem := Certificates.Npc.heisF_handlesW_mem t x y E E₂ hwild
  have h6z := Certificates.Npc.heisF_handlesW_z t x y E E₂ hwild
  have h1jz : heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α))
      ∈ heisJetZero A C := by rw [e1]; exact ⟨rfl, rfl⟩
  have h2jz : heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (aW h d))
      ∈ heisJetZero A C := by
    rw [heisEvalZ_comm, heisEvalZ_gen,
      heisF_aW_free t x y E E₂ (htriv Generator.sigma) d hEη,
      heisCommR_of_trivial _ _ (htriv (coreLetter h 0))
        (fun v => mem_trivAct.mp (pow_mem (mem_trivAct.mpr (htriv Generator.sigma)) nn) v)]
    exact ⟨rfl, rfl⟩
  have h5jz : heisEvalZ ⇑t x y E E₂ (eBlockW h r d) ∈ heisJetZero A C := by
    rw [e5]; exact ⟨rfl, rfl⟩
  have h3l : (heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 2))
        (PWord.prodList [.gen (coreLetter h 1), bW h r])))).l = y (coreLetter h 2) := by
    rw [hinvl, hconjl, heisEvalZ_gen]
  have h4a : (heisEvalZ ⇑t x y E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))).a
        = x (coreLetter h 2) := by
    rw [e4]
    show e • (x (coreLetter h 2) + x .tau) = _
    rw [hxτ, add_zero, hoddsmul]
  rw [npcW, heisEvalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [heisMul_six_z_scalar _ _ _ _ _ _ h1jz h2jz h5jz h6mem
      (hgtriv (.inv (.conj (.gen (coreLetter h 2))
        (PWord.prodList [.gen (coreLetter h 1), bW h r])))),
    h3l, h4a, e1, e2, e3, e4, e5, h6z]
  dsimp only
  rw [hxτ, hyτ, map_zero, add_zero, smul_zero,
    nsmul_zmod2_even (choose_two_even_of_mod_four he)]
  generalize y (coreLetter h 0) (x (coreLetter h 0)) = c₁
  generalize nn • y (coreLetter h 0) (x .sigma) = c₂
  generalize nn • y .sigma (x (coreLetter h 0)) = c₃
  generalize y (coreLetter h 1) (x (coreLetter h 2)) = c₄
  generalize (2 ^ r : ℕ) • y .sigma (x (coreLetter h 2)) = c₅
  generalize y (coreLetter h 2) (x (coreLetter h 1)) = c₆
  generalize (2 ^ r : ℕ) • y (coreLetter h 2) (x .sigma) = c₇
  generalize y (coreLetter h 2) (x (coreLetter h 2)) = c₈
  generalize (∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j)))) = c₉
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉
  decide

set_option maxHeartbeats 3200000 in
/-- **Regression: the free row and the in-tree scalar row agree on their overlap.**  Both sides
are the *same* evaluated word — the left through `heisZ_npc_scalar_free`, the right through
`Certificates.Npc.heisZ_npc_scalar` — so at `sigma`- and `tau`-free offsets the two independent
derivations of the procyclic-`N` scalar row coincide, `sigma`-planes and all. -/
theorem heisZ_npc_scalar_free_regression (hA₂ : ∀ v : A, v + v = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v)
    (hres : ResolverLifts E C) (hxσ : x .sigma = 0) (hyσ : y .sigma = 0)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0) (hα : 2 ≤ α)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (d : EtaData) {nn : ℕ}
    (hEη : E d.toZhat = (nn : ℤ)) :
    y (coreLetter h 0) (x (coreLetter h 0))
        + (nn • y (coreLetter h 0) (x .sigma) + nn • y .sigma (x (coreLetter h 0)))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1)))
        + ((2 ^ r : ℕ) • y .sigma (x (coreLetter h 2))
            + (2 ^ r : ℕ) • y (coreLetter h 2) (x .sigma))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j)))
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1)))
        + (y .tau (x (coreLetter h 1)) + y (coreLetter h 1) (x .tau))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [← heisZ_npc_scalar_free (α := α) (r := r) t x y E (fun _ ↦ (0 : ℤ)) hA₂ htriv hres hxτ hyτ
      hα hE he d hEη,
    ← Certificates.Npc.heisZ_npc_scalar t x y E (fun _ ↦ (0 : ℤ)) hA₂ (fun i v => htriv _ v)
      (fun v => htriv _ v) (fun v => htriv _ v) hxσ hyσ hα hE he d]

end Row

end

end GQ2.Dyadic.NProcyclicUnram

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclicUnram.trivAct_evalFin_of_gens
#print axioms GQ2.Dyadic.NProcyclicUnram.heisEvalZ_g_smul_eq
#print axioms GQ2.Dyadic.NProcyclicUnram.heisF_aW_free
#print axioms GQ2.Dyadic.NProcyclicUnram.heisF_bW_free
#print axioms GQ2.Dyadic.NProcyclicUnram.heisF_commX0A_free
#print axioms GQ2.Dyadic.NProcyclicUnram.heisF_invConjX2G_free
#print axioms GQ2.Dyadic.NProcyclicUnram.heisMul_six_z_scalar
#print axioms GQ2.Dyadic.NProcyclicUnram.heisZ_npc_scalar_free
#print axioms GQ2.Dyadic.NProcyclicUnram.heisZ_npc_scalar_free_regression

end AxiomAudit
