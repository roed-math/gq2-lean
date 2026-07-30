/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Word.Syntax
import GQ2.GaussZ.RelatorGammaA

/-!
# NC lane: the `ω₂`/norm machinery of the corrected noncompact-`N` jet

**Ticket NC3** of the NC lane (design memo `docs/dyadic/nc-design.md`, the R3(a) commission).
This file is the memo's `NpcJet/Omega.lean` file-map row (§4.1): the machinery layer underneath
the corrected cross-operator theorem `npc_cross_operators` (memo §2.3), stated over the
*underlying* `Sd`/`CentExt`/`ℤ̂` vocabulary so that it is independent of the lane's definition
file (NC2) and can be developed in parallel with it.

## The two reduction rules

The Python engine reduces the twisted class-two value of the eq:Npc-word by three syntactic
rewrites (`N.py` `RAMIFIED_REDUCTION_RULES`; memo §1.3).  The Lean proof does *not* replay that
atom algebra — it computes the honest finite evaluation, on which two of the three rules appear
as the lemma families of this file (the third, `diagonal-q-invariance`, is a direct consequence
of `IsEquivariantFactorSet` in characteristic 2 and needs no machinery).

**The rules are sound only on their hypotheses.**  That is the engine-side caveat of memo §1.3,
and it is why every statement below carries its rule's hypothesis explicitly rather than
bundling it into a "ramified simple" side condition:

* **Rule 1, `tame-omega2-power`** — *hypothesis: odd order.*  A profinite `ω₂`-power is computed
  by a finite representative: `zpowHat_omega2_eq_pow_of_dvd_two_mul` (`orderOf y ∣ 2m` with `m`
  odd gives `y ^ᶻ ω₂ = y ^ m`, memo §3.0(c)) and its tame special case
  `zpowHat_omega2_eq_one_of_odd` (`Odd (orderOf y)` gives `y ^ᶻ ω₂ = 1`, the rule proper —
  memo §3.5's boundary block).
* **Rule 2, `tame-geom-vanishes`** — *hypothesis: `V^u = 0`.*  `sum_pow_smul_eq_zero`: the
  `u`-norm `∑_{i<m} uⁱ•` annihilates a module with no nonzero `u`-fixed vector.  Memo §3.0(d)'s
  finding is honored: the proof needs **no semisimplicity and no projector theory** — the norm
  is `u`-fixed by reindexing, so it lands in `V^u = 0`.

The two rules meet in `nc3_zpowHat_omega2_eq_pow_orderOf`: for `y` over the mixed base `(v, u)`
of memo §3.1 (the `x₀τ` element of the `δ₀` block), rule 2 collapses the base of `y ^ orderOf u`
to the identity, whence `orderOf y ∣ 2 · orderOf u` and rule 1 evaluates `y ^ᶻ ω₂ = y ^ orderOf u`
— a *central* element (`nc3_exists_zpowHat_omega2_eq_incl`).  Its fibre charge `z_m` is
deliberately left as `(y ^ orderOf u).fib`: memo risk 2 quarantines that bookkeeping, since the
`E`-block value is charge-independent.

## The `η̂`-power vocabulary

Memo V4: the draft's sum exponent `η̂ − 2^r` has **no `etaHatZ` spelling** (its odd components
are `1 − 2^r ≠ 1`), so both the AST and the Lean word conjugate by the *product*
`σ^{η̂} · σ^{−2^r}`.  No `padicOmega2` additivity is needed — and in the finite evaluation even
`zpowHat_mul` can be shortcut: `nc3_zpowHat_etaHatZ_mem_powers` observes that
`x ^ᶻ η̂` is literally an *ordinary* power of `x` (that is `zpowHat_etaHatZ`, which is itself a
`zpowHat_mul` computation), so all commutation between the `A`- and `B`-conjugators is
`Commute.pow_pow`.  `nc3_prodConj_etaHat_inv` is the spelling NC5's assembly consumes: the
inverse of the third conjugator `â·b⁻¹` is `b·â⁻¹`, i.e. the operator `B·A⁻¹` — the third
summand of the corrected `L_c = A⁻¹ + B + B·A⁻¹`.

## The `κ`-free `C`-line and the power law

Memo §3.0(a)/§3.1: `nc3CLine` is the homomorphism `c ↦ ((0,c),0)` into the `κ⁰`-extension (the
cocycle vanishes on it, so σ/τ-words evaluate with fibre `0` and with `orderOf` transported on
the nose), and `nc3_Sd_mk_pow` is the semidirect power law `((v,c))^k = ((N_k v, c^k))` whose
`V`-part is exactly the partial norm rule 2 kills.
-/

namespace GQ2.Dyadic

open WordCoh2 SectionEight.AffineTLift

/-! ## Reduction rule 1: the `ω₂`-bridge  (memo §1.3 row 1, §3.0(c)) -/

section RuleOne

variable {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **Reduction rule 1, the `ω₂`-power bridge** (memo §3.0(c); the spike-proved lemma of
memo §5.1).  In a finite (discrete) group, if `orderOf y` divides `2m` with `m` **odd**, then
the profinite `ω₂`-power is the finite `m`-th power: `y ^ᶻ ω₂ = y ^ m`.

*Hypothesis carried*: `hm : Odd m` — the rule is the statement that `ω₂` is the projector onto
the `2`-primary part, so the odd cofactor must be pinned; the bridge is false for even `m`
(e.g. `m = 2`, `y` of order `4`).

Proof: `zpowHat_omega2` reduces to `y ^ omega2Exp (orderOf y)`, and `omega2Exp (2m) ≡ m [MOD 2m]`
by CRT over the coprime factorisation `2 · m` — `≡ 1 ≡ m` on the `2`-part
(`omega2Exp_modEq_one`) and `≡ 0 ≡ m` on the odd part (`oddPart_dvd_omega2Exp`).  This is the
congruence toolkit `padicOmega2Exp_modEq` already exercises. -/
theorem zpowHat_omega2_eq_pow_of_dvd_two_mul {y : P} {m : ℕ} (hm : Odd m)
    (hdvd : orderOf y ∣ 2 * m) : y ^ᶻ omega2 = y ^ m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hm
  have h2m : 2 * m ≠ 0 := by omega
  rw [zpowHat_omega2, ← powOmega2_pow_eq y hdvd h2m]
  refine pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd hdvd ?_)
  -- `omega2Exp (2m) ≡ m [MOD 2m]`, by CRT over `2 · m`
  have hnd : ¬ (2 : ℕ) ∣ m := by
    rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff]
    exact hm
  have hfac : (2 * m).factorization 2 = 1 := by
    rw [Nat.factorization_mul two_ne_zero hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hnd]
  have h2part : omega2Exp (2 * m) ≡ m [MOD 2] := by
    have h1 : omega2Exp (2 * m) ≡ 1 [MOD 2] := by
      have := omega2Exp_modEq_one h2m (by rw [hfac]; exact one_ne_zero)
      rwa [hfac, pow_one] at this
    have h2 : m ≡ 1 [MOD 2] := by
      rw [Nat.ModEq, Nat.one_mod, ← Nat.odd_iff.mp hm]
    exact h1.trans h2.symm
  have hoddpart : omega2Exp (2 * m) ≡ m [MOD m] := by
    have hdvdm : m ∣ omega2Exp (2 * m) := by
      have := oddPart_dvd_omega2Exp (2 * m)
      rwa [hfac, pow_one, Nat.mul_div_cancel_left m two_ne_zero.bot_lt] at this
    exact (Nat.modEq_zero_iff_dvd.mpr hdvdm).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd)).mp ⟨h2part, hoddpart⟩

/-- **Reduction rule 1 proper** (`tame-omega2-power`, memo §1.3 row 1): `ω₂` kills an element of
**odd** order, `y ^ᶻ ω₂ = 1`.  This is the `zpowHat_padicOmega2_eq_one_of_odd` shape at the
plain `ω₂`, and it is what makes memo §3.5's boundary block `(x₂τ)^{ω₂}` die *exactly* (no
second-order residue).

*Hypothesis carried*: `h : Odd (orderOf y)` — "tame inertia is pro-odd".  Without it the
`ω₂`-power is the (generally nontrivial) `2`-primary part of `y`.

Immediate from the bridge at `m = orderOf y`. -/
theorem zpowHat_omega2_eq_one_of_odd {y : P} (h : Odd (orderOf y)) : y ^ᶻ omega2 = 1 := by
  rw [zpowHat_omega2_eq_pow_of_dvd_two_mul h (dvd_mul_left _ 2), pow_orderOf_eq_one]

end RuleOne

/-! ## Reduction rule 2: norm vanishing  (memo §1.3 row 2, §3.0(d)) -/

section RuleTwo

variable {C V : Type*} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- **Reduction rule 2, the Lean form** (`tame-geom-vanishes`; memo §3.0(d), and the spike-proved
lemma of memo §5.1).  If `u` fixes only `0` and `u ^ m = 1`, the `u`-norm `∑_{i<m} uⁱ•`
annihilates `V`.

*Hypothesis carried*: `hVu : ∀ v, u • v = v → v = 0`, i.e. `V^u = 0` — the ramified condition.
On a module with `V^u ≠ 0` the rule is false (take `u = 1`, `m = 1`).  The second hypothesis
`hm : u ^ m = 1` fixes the length of the norm.

Memo §3.0(d)'s finding, honored: **no semisimplicity and no projector theory are needed** — the
sum is `u`-fixed by reindexing (`u·S = S + uᵐv − v = S`), hence lies in `V^u = 0`.  This is
strictly elementary, and in particular the statement is at the memo's generality: no `Finite`,
no characteristic assumption, no invariant form.

Implementation note (memo risk 6, "search before committing names"): the `ℚ₂` Fox-Heisenberg
layer already carries this fact as `GQ2.FoxH.WordLift.sum_pow_smul_eq_zero`, in the marginally
more general form with `u ^ m • v = v` in place of `u ^ m = 1`, and that file is in this file's
import closure through `GQ2.WordCoh2`.  The memo planned to transplant the spike's proof; we
reuse the existing lemma instead and keep the memo's NC-facing spelling as the interface. -/
theorem sum_pow_smul_eq_zero {u : C} (hVu : ∀ v : V, u • v = v → v = 0) {m : ℕ} (hm : u ^ m = 1)
    (v : V) : ∑ i ∈ Finset.range m, u ^ i • v = 0 :=
  FoxH.WordLift.sum_pow_smul_eq_zero hVu (by rw [hm, one_smul])

/-- Reduction rule 2 at the canonical length `m = orderOf u` — the form memo §3.1 uses, where
the `δ₀` block's power is taken to the order of the `τ`-image.

*Hypothesis carried*: `hVu` (`V^u = 0`) only; `u ^ orderOf u = 1` is automatic. -/
theorem sum_pow_smul_orderOf_eq_zero {u : C} (hVu : ∀ v : V, u • v = v → v = 0) (v : V) :
    ∑ i ∈ Finset.range (orderOf u), u ^ i • v = 0 :=
  sum_pow_smul_eq_zero hVu (pow_orderOf_eq_one u) v

/-- **The semidirect power law** (memo §3.1): `((v, c))^k = ((N_k v, c^k))` with `N_k = ∑_{i<k} cⁱ•`
the partial norm.  The `V`-slot is exactly the operator reduction rule 2 kills, and the `C`-slot
is the ordinary power; no factor-set data enters, so this lives on `Sd` alone. -/
theorem nc3_Sd_mk_pow (v : V) (c : C) (k : ℕ) :
    Sd.mk v c ^ k = Sd.mk (∑ i ∈ Finset.range k, c ^ i • v) (c ^ k) := by
  induction k with
  | zero => simp only [pow_zero, Finset.range_zero, Finset.sum_empty]; rfl
  | succ k ih =>
    rw [pow_succ, ih]
    refine Sd.ext ?_ ?_
    · show (∑ i ∈ Finset.range k, c ^ i • v) + c ^ k • v = ∑ i ∈ Finset.range (k + 1), c ^ i • v
      rw [Finset.sum_range_succ]
    · show c ^ k * c = c ^ (k + 1)
      rw [pow_succ]

/-- **Rules 1 and 2 meet, base side** (memo §3.1): on a module with `V^u = 0` the semidirect
element `(v, u)` has `(v, u) ^ orderOf u = 1` — the partial norm in the `V`-slot dies by rule 2
and the `C`-slot dies by `pow_orderOf_eq_one`.  This is what makes the `δ₀` block's `ω₂`-power
*central* in the extension.

*Hypothesis carried*: `hVu` (`V^u = 0`), rule 2's. -/
theorem nc3_Sd_mk_pow_orderOf_eq_one {u : C} (hVu : ∀ v : V, u • v = v → v = 0) (v : V) :
    Sd.mk v u ^ orderOf u = 1 := by
  rw [nc3_Sd_mk_pow, sum_pow_smul_orderOf_eq_zero hVu, pow_orderOf_eq_one]
  rfl

end RuleTwo

/-! ## The `η̂`-power vocabulary NC5's assembly consumes  (memo V4, §3.2) -/

section PowerSpellings

variable {G : Type*} [Group G]

/-- `B` as a natural power: the word tree's `σ^{2^r}` node carries the **integer** exponent
`(2 : ℤ)^r`, while the cross operator `L_c` is spelled with the natural power `2^r`. -/
theorem nc3_zpow_two_pow (x : G) (r : ℕ) : x ^ ((2 : ℤ) ^ r) = x ^ (2 ^ r : ℕ) := by
  rw [← zpow_natCast]
  norm_num

/-- `B⁻¹` as the inverse of a natural power: the second `D`-block conjugator is the word node
`σ^{−2^r}` (memo §2.2's compressed spelling). -/
theorem nc3_zpow_neg_two_pow (x : G) (r : ℕ) : x ^ (-(2 ^ r : ℤ)) = (x ^ (2 ^ r : ℕ))⁻¹ := by
  rw [zpow_neg, nc3_zpow_two_pow]

/-- The operator of the second `D`-block conjugator: conjugation by `σ^{−2^r}` applies the
*inverse* of that element (`conjR x g = g⁻¹ x g`), which is `B = σ^{2^r}` — the **second** summand
of the corrected `L_c = A⁻¹ + B + B·A⁻¹`. -/
theorem nc3_inv_zpow_neg_two_pow (x : G) (r : ℕ) : (x ^ (-(2 ^ r : ℤ)))⁻¹ = x ^ (2 ^ r : ℕ) := by
  rw [nc3_zpow_neg_two_pow, inv_inv]

/-- The product-conjugator inversion law, in the group: `conjR` by `a·b⁻¹` applies `b·a⁻¹`. -/
theorem nc3_prodConj_inv (a b : G) : (a * b⁻¹)⁻¹ = b * a⁻¹ := by
  rw [mul_inv_rev, inv_inv]

end PowerSpellings

section EtaHatPowers

variable {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **The `η̂`-power is an ordinary power** (memo V4).  In a finite (discrete) group,
`x ^ᶻ η̂ = x ^ (1 + padicOmega2Exp (η−1) (orderOf x))` — an honest natural power of `x`.

This is the whole content of the memo's "route around `padicOmega2` additivity": the sum exponent
`η̂ − 2^r` has no `etaHatZ` spelling, the word therefore conjugates by the *product*
`σ^{η̂}·σ^{−2^r}`, and every commutation needed to reassociate those conjugators follows from
this lemma by `Commute.pow_pow`.  (`zpowHat_etaHatZ`, which supplies it, is itself the
`zpowHat_mul` computation `η̂ = 1 · (η−1)ω₂` the memo names.) -/
theorem nc3_zpowHat_etaHatZ_mem_powers (η : ℤ_[2]) (x : P) : ∃ k : ℕ, x ^ᶻ etaHatZ η = x ^ k :=
  ⟨1 + padicOmega2Exp (η - 1) (orderOf x), by rw [zpowHat_etaHatZ, pow_add, pow_one]⟩

/-- The `A`-conjugator commutes with every natural power of the same base — in particular with
the `B`-conjugator `σ^{2^r}` of the `D`-block (memo §3.2). -/
theorem nc3_commute_zpowHat_etaHatZ_pow (η : ℤ_[2]) (x : P) (n : ℕ) :
    Commute (x ^ᶻ etaHatZ η) (x ^ n) := by
  obtain ⟨k, hk⟩ := nc3_zpowHat_etaHatZ_mem_powers η x
  rw [hk]
  exact (Commute.refl x).pow_pow k n

/-- The `ℤ`-power form of `nc3_commute_zpowHat_etaHatZ_pow`: the spelling the word tree produces,
where `σ^{±2^r}` is a `PWord.zpow` node. -/
theorem nc3_commute_zpowHat_etaHatZ_zpow (η : ℤ_[2]) (x : P) (n : ℤ) :
    Commute (x ^ᶻ etaHatZ η) (x ^ n) := by
  obtain ⟨k, hk⟩ := nc3_zpowHat_etaHatZ_mem_powers η x
  rw [hk]
  exact ((Commute.refl x).pow_left k).zpow_right n

/-- **The product conjugator's operator** (memo V4/§3.2): the third `D`-block conjugator is the
product `â·b⁻¹` (`â = σ^{η̂}`, `b = σ^{2^r}`), and since `conjR` applies the inverse, its operator
is `b·â⁻¹` — the **third** summand `B·A⁻¹` of the corrected `L_c`, i.e. exactly the term whose
absence refuted draft eq:Ncross.

Stated with the conjugator in the word's own spelling, so that NC5 can rewrite the evaluated
conjugator directly. -/
theorem nc3_prodConj_etaHat_inv (η : ℤ_[2]) (x : P) (r : ℕ) :
    ((x ^ᶻ etaHatZ η) * x ^ (-(2 ^ r : ℤ)))⁻¹ = x ^ (2 ^ r : ℕ) * (x ^ᶻ etaHatZ η)⁻¹ := by
  rw [nc3_zpow_neg_two_pow, nc3_prodConj_inv]

end EtaHatPowers

/-! ## The `κ`-free `C`-line and the `ω₂`-power in the `κ⁰`-extension  (memo §3.0(a), §3.1) -/

section Extension

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] {q : V → ZMod 2}
  (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The `κ`-free `C`-line** (memo §3.0(a)): `c ↦ ((0, c), 0)` is a homomorphism
`C →* CentExt κ⁰`, because `κ⁰((0,c),(0,d)) = f(0, c·0) + m_c(0) = 0` (`f_zero_left` and
`m_zero`).  Consequently σ/τ-words evaluate on this line with fibre `0`, and `orderOf` transports
on the nose (`orderOf_nc3CLine`) — which is how rule 1's odd-order hypothesis reaches the
extension. -/
noncomputable def nc3CLine : C →* CentExt (kappa0Cocycle dat hdat) where
  toFun c := (Sd.mk 0 c, 0)
  map_one' := rfl
  map_mul' c d := by
    refine (CentExt.ext ?_ ?_).symm
    · refine Sd.ext ?_ rfl
      show (0 : V) + c • (0 : V) = 0
      rw [smul_zero, add_zero]
    · show (0 : ZMod 2) + 0 + (kappa0Cocycle dat hdat).κ (Sd.mk 0 c) (Sd.mk 0 d) = 0
      rw [kappa0Cocycle_κ]
      show (0 : ZMod 2) + 0 + (dat.f 0 (c • (0 : V)) + dat.m c 0) = 0
      rw [smul_zero, hdat.f_zero_left, IsEquivariantFactorSet.m_zero dat hdat c]
      simp

@[simp] theorem nc3CLine_base (c : C) : (nc3CLine dat hdat c).base = Sd.mk 0 c := rfl

@[simp] theorem nc3CLine_fib (c : C) : (nc3CLine dat hdat c).fib = 0 := rfl

theorem nc3CLine_injective : Function.Injective (nc3CLine dat hdat) := by
  intro c d h
  have : (nc3CLine dat hdat c).base = (nc3CLine dat hdat d).base := by rw [h]
  simpa [nc3CLine_base, Sd.mk, Sd.cc] using congrArg Sd.cc this

/-- `orderOf` transports along the `C`-line (memo §3.0(a)): `orderOf ((0,c),0) = orderOf c`. -/
theorem orderOf_nc3CLine (c : C) : orderOf (nc3CLine dat hdat c) = orderOf c :=
  orderOf_injective _ (nc3CLine_injective dat hdat) c

/-- **The `C`-line is natural for profinite exponentiation** (memo §3.2): a σ-conjugator of the
word evaluates to `((0, s), 0)` and its `ℤ̂`-powers are computed *downstairs*, in `C`.  This is
what lets the `A`-conjugator `σ^{η̂}` of the `D`-block be read as the element `ŝ = s ^ᶻ η̂ ∈ C`
whose inverse is the first summand of `L_c`.  (`GQ2.map_zpowHat` at the — automatically
continuous — `C`-line.) -/
theorem nc3CLine_zpowHat [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C] (c : C)
    (γ : Zhat) : nc3CLine dat hdat c ^ᶻ γ = nc3CLine dat hdat (c ^ᶻ γ) :=
  (map_zpowHat ⟨nc3CLine dat hdat, continuous_of_discreteTopology⟩ c γ).symm

/-- **Rule 1 in the extension** (memo §3.5, the boundary block): the `ω₂`-power of a `C`-line
element of odd order is the identity — so `(x₂τ)^{ω₂}` dies exactly.

*Hypothesis carried*: `hu : Odd (orderOf u)`, rule 1's. -/
theorem nc3CLine_zpowHat_omega2_eq_one [Finite C] [Finite V] {u : C} (hu : Odd (orderOf u)) :
    nc3CLine dat hdat u ^ᶻ omega2 = 1 :=
  zpowHat_omega2_eq_one_of_odd (by rw [orderOf_nc3CLine]; exact hu)

/-- The base of a power is the power of the base (`CentExt.base` is a homomorphism). -/
theorem nc3_base_pow (y : CentExt (kappa0Cocycle dat hdat)) (k : ℕ) :
    (y ^ k).base = y.base ^ k := by
  induction k with
  | zero => simp only [pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, CentExt.mul_base, ih]

/-- The central fibre is 2-torsion: `((1, z))² = 1`.  (`ZMod 2` coefficients and `κ 1 1 = 0`.) -/
theorem nc3_incl_mul_self {L : Type*} [Group L] {c : TwoCocycle L} (z : ZMod 2) :
    CentExt.incl c z * CentExt.incl c z = 1 := by
  refine CentExt.ext ?_ ?_
  · show (1 : L) * 1 = 1
    rw [mul_one]
  · show z + z + c.κ 1 1 = 0
    rw [c.norm]
    revert z
    decide

/-- An element of the extension whose base power is trivial is *central* at that power: it is
`((1), z)` for the fibre charge `z = (y^k).fib`.  Memo risk 2 quarantines that charge — the
`E`-block value is independent of it — so it is deliberately left unnormalized. -/
theorem nc3_pow_eq_incl {y : CentExt (kappa0Cocycle dat hdat)} {k : ℕ} (h : y.base ^ k = 1) :
    y ^ k = CentExt.incl (kappa0Cocycle dat hdat) ((y ^ k).fib) :=
  (CentExt.base_eq_one_iff _).mp (by rw [nc3_base_pow, h])

/-- If the base power is trivial at `k`, the element's own order divides `2k`: the extension is
central by `ZMod 2`, so one more squaring kills the fibre charge.  This is the input `orderOf y ∣
2m` that rule 1's bridge asks for (memo §3.1). -/
theorem nc3_orderOf_dvd_two_mul {y : CentExt (kappa0Cocycle dat hdat)} {k : ℕ}
    (h : y.base ^ k = 1) : orderOf y ∣ 2 * k := by
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [mul_comm, pow_mul, pow_two, nc3_pow_eq_incl dat hdat h, nc3_incl_mul_self]

/-- **Rules 1 and 2 meet** (memo §3.1, the `δ₀` block).  Let `y` lie over the mixed base `(v, u)`
— the value of `x₀τ` at the Gate-E marking.  On a module with `V^u = 0` and with `orderOf u` odd,
the profinite `ω₂`-power of `y` is the finite power `y ^ orderOf u`.

*Hypotheses carried*: `hu : Odd (orderOf u)` (rule 1) **and** `hVu : V^u = 0` (rule 2).  Both are
genuinely used: rule 2 collapses the partial norm in the `V`-slot so that
`orderOf y ∣ 2 · orderOf u`, and rule 1 then evaluates the `ω₂`-power at that bound. -/
theorem nc3_zpowHat_omega2_eq_pow_orderOf [Finite C] [Finite V] {u : C} (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) {y : CentExt (kappa0Cocycle dat hdat)} {v : V}
    (hy : y.base = Sd.mk v u) : y ^ᶻ omega2 = y ^ orderOf u :=
  zpowHat_omega2_eq_pow_of_dvd_two_mul hu
    (nc3_orderOf_dvd_two_mul dat hdat (by rw [hy]; exact nc3_Sd_mk_pow_orderOf_eq_one hVu v))

/-- **The `δ₀` block's `ω₂`-power is central** (memo §3.1): under rules 1 and 2's hypotheses the
value of `(x₀τ)^{ω₂}` is `((0,1), z_m)` for a fibre charge `z_m` depending on `c₀` alone.  The
charge is returned only existentially — memo risk 2's quarantine: the `E`-block commutator
cancels it, so NC4 never normalizes it.

*Hypotheses carried*: `hu` (rule 1) and `hVu` (rule 2), as in
`nc3_zpowHat_omega2_eq_pow_orderOf`. -/
theorem nc3_exists_zpowHat_omega2_eq_incl [Finite C] [Finite V] {u : C} (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) {y : CentExt (kappa0Cocycle dat hdat)} {v : V}
    (hy : y.base = Sd.mk v u) :
    ∃ z : ZMod 2, y ^ᶻ omega2 = CentExt.incl (kappa0Cocycle dat hdat) z :=
  ⟨(y ^ orderOf u).fib, by
    rw [nc3_zpowHat_omega2_eq_pow_orderOf dat hdat hu hVu hy]
    exact nc3_pow_eq_incl dat hdat (by rw [hy]; exact nc3_Sd_mk_pow_orderOf_eq_one hVu v)⟩

/-- **The product conjugator's operator, on the module** (memo §3.2): the `V`-slot operator of the
third `D`-block conjugator is `B·A⁻¹`, the third summand of the corrected
`L_c = A⁻¹ + B + B·A⁻¹`.  Together with `nc3_inv_zpow_neg_two_pow` (giving `B`) and plain
`inv` (giving `A⁻¹`), this is the "`L_c` is literally the sum of the three inverse-conjugators"
reading that makes the refutation of draft eq:Ncross visible. -/
theorem nc3_prodConj_etaHat_smul [Finite C] [TopologicalSpace C] [DiscreteTopology C] (s : C)
    (η : ℤ_[2]) (r : ℕ) (v : V) :
    ((s ^ᶻ etaHatZ η) * s ^ (-(2 ^ r : ℤ)))⁻¹ • v
      = (s ^ (2 ^ r : ℕ) * (s ^ᶻ etaHatZ η)⁻¹) • v := by
  rw [nc3_prodConj_etaHat_inv]

/-- **`L_c` is the sum of the three inverse-conjugators** (memo §3.2) — the one rewrite the
assembly needs to turn the `D`-block's evaluated `V`-part into the cross operator.

On the left, the conjugators in the **word's own spelling** (memo §2.2's compressed `D`-block:
`â = σ^{η̂}`, then `σ^{−2^r}`, then their product), each contributing the action of its *inverse*
because `conjR x g = g⁻¹ x g`.  On the right, the operator `A⁻¹ + B + B·A⁻¹` in the spelling of
the lane's `lcOp` (NC2's definition file, which this file deliberately does not import): the
right-hand side is definitionally `lcOp s η r v`.

This is where the S3.2 correction becomes visible: draft eq:Ncross claimed `L_c = A⁻¹`, i.e. the
first summand alone; the second and third summands are the two conjugators the draft dropped. -/
theorem nc3_lcOp_spelling [Finite C] [TopologicalSpace C] [DiscreteTopology C] (s : C) (η : ℤ_[2])
    (r : ℕ) (v : V) :
    (s ^ᶻ etaHatZ η)⁻¹ • v + (s ^ (-(2 ^ r : ℤ)))⁻¹ • v
        + ((s ^ᶻ etaHatZ η) * s ^ (-(2 ^ r : ℤ)))⁻¹ • v
      = (s ^ᶻ etaHatZ η)⁻¹ • v + s ^ (2 ^ r : ℕ) • v
        + (s ^ (2 ^ r : ℕ) * (s ^ᶻ etaHatZ η)⁻¹) • v := by
  rw [nc3_inv_zpow_neg_two_pow, nc3_prodConj_etaHat_inv]

end Extension

end GQ2.Dyadic
