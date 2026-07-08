import GQ2.FoxHeisenberg
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Separable

/-!
# P-16d6e4aA-P3 — the ramified isotypic pack (the étale route)

Blueprint: `docs/p16d6e4aA-pack-design.md`.  Target: the pack fields of
`SectionSix.prop_6_9_ramified`, discharging `zeroCount_qDouble_ramified_of_faithful`
(the ONE remaining sorry of the `Γ_A` Gauss lane).

This file builds the generic layer, bottom-up:

* §TwoPowerConj — **every conjugate of `t` is `t^{2^j}`** (the refinement of
  `tau_fixed_eq_zero_of_gen`'s conjugation calculus): the `S`-twist is squaring (the
  tame relation), its inverse is the square ROOT `t^{2^{φ(d)−1}}` (Euler — no
  multiplicative-order machinery), and the exponents compose multiplicatively.  This
  is what makes every `𝔽₂`-isotypic component `C`-stable
  (`P(t^{2^j}) = P(t)^{2^j}`, the char-2 polynomial Frobenius — design doc §3).
-/

namespace GQ2

namespace RamifiedPack

/-! ## §TwoPowerConj: conjugates of `t` are 2-power powers of `t` -/

section TwoPowerConj

variable {C : Type*} [Group C]

/-- Conjugation distributes over `ℕ`-powers (the `MulAut.conj`/`map_pow` massage). -/
theorem conj_pow_eq (z t : C) (N : ℕ) : z * t ^ N * z⁻¹ = (z * t * z⁻¹) ^ N := by
  have h := map_pow (MulAut.conj z) t N
  simpa [MulAut.conj_apply, mul_assoc] using h

/-- Conjugation distributes over `ℕ`-powers, inverse flavor. -/
theorem inv_conj_pow_eq (z t : C) (N : ℕ) : z⁻¹ * t ^ N * z = (z⁻¹ * t * z) ^ N := by
  have h := conj_pow_eq z⁻¹ t N
  rwa [inv_inv] at h

/-- The square-root step: if `x² = t` with `x` of the same odd order `d`, then
`x = t^{2^{φ(d)−1}}` — from Euler's `2^{φ(d)} ≡ 1 (mod d)`. -/
theorem eq_two_pow_of_sq_eq {t x : C} (hd : Odd (orderOf t)) (hpos : 0 < orderOf t)
    (horder : orderOf x = orderOf t) (hx2 : x ^ 2 = t) :
    x = t ^ 2 ^ (Nat.totient (orderOf t) - 1) := by
  have hcop : Nat.Coprime 2 (orderOf t) := by
    refine (Nat.prime_two.coprime_iff_not_dvd).mpr ?_
    rcases hd with ⟨k, hk⟩
    omega
  have htot : (2 : ℕ) ^ Nat.totient (orderOf t) ≡ 1 [MOD orderOf t] :=
    Nat.ModEq.pow_totient hcop
  have htotpos : 0 < Nat.totient (orderOf t) := Nat.totient_pos.mpr hpos
  have h1 : x ^ 2 ^ Nat.totient (orderOf t) = x := by
    have hiff : x ^ 2 ^ Nat.totient (orderOf t) = x ^ 1
        ↔ 2 ^ Nat.totient (orderOf t) ≡ 1 [MOD orderOf x] := pow_eq_pow_iff_modEq
    rw [horder] at hiff
    have h2 := hiff.mpr htot
    rwa [pow_one] at h2
  calc x = x ^ 2 ^ Nat.totient (orderOf t) := h1.symm
    _ = (x ^ 2) ^ 2 ^ (Nat.totient (orderOf t) - 1) := by
        rw [← pow_mul]
        congr 1
        obtain ⟨c, hc⟩ : ∃ c, Nat.totient (orderOf t) = c + 1 :=
          ⟨Nat.totient (orderOf t) - 1, by omega⟩
        rw [hc, Nat.add_sub_cancel, pow_succ]
        ring
    _ = t ^ 2 ^ (Nat.totient (orderOf t) - 1) := by rw [hx2]

/-- **Every element of `C = ⟨s, t⟩` conjugates `t` to a 2-power power of `t`** (both
directions): the `S`-twist is squaring (`hrel`), its inverse the Euler square root,
and exponents compose multiplicatively along the closure induction. -/
theorem conj_eq_two_pow (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
    (hodd : Odd (orderOf t)) (hpos : 0 < orderOf t) (g : C) :
    (∃ j : ℕ, g⁻¹ * t * g = t ^ 2 ^ j) ∧ (∃ j : ℕ, g * t * g⁻¹ = t ^ 2 ^ j) := by
  have hg : g ∈ Subgroup.closure ({s, t} : Set C) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · constructor
      · refine ⟨1, ?_⟩
        rw [hrel]
        norm_num
      · -- the square root `x t x⁻¹ = t^{2^{φ(d)−1}}`
        have hsc : SemiconjBy x t (x * t * x⁻¹) := by
          show x * t = x * t * x⁻¹ * x
          group
        have hx2 : (x * t * x⁻¹) ^ 2 = t := by
          have h2 : (x * t * x⁻¹) ^ 2 = x * t ^ 2 * x⁻¹ := by
            rw [pow_two, pow_two]
            group
          rw [h2, ← hrel]
          group
        exact ⟨Nat.totient (orderOf t) - 1,
          eq_two_pow_of_sq_eq hodd hpos hsc.orderOf_eq.symm hx2⟩
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      constructor
      · refine ⟨0, ?_⟩
        rw [show x⁻¹ * x * x = x from by group]
        norm_num
      · refine ⟨0, ?_⟩
        rw [show x * x * x⁻¹ = x from by group]
        norm_num
  | one =>
    constructor
    · refine ⟨0, ?_⟩
      rw [show (1 : C)⁻¹ * t * 1 = t from by group]
      norm_num
    · refine ⟨0, ?_⟩
      rw [show (1 : C) * t * 1⁻¹ = t from by group]
      norm_num
  | mul x y hx hy ihx ihy =>
    obtain ⟨j₁, hj₁⟩ := ihx.1
    obtain ⟨j₁', hj₁'⟩ := ihx.2
    obtain ⟨j₂, hj₂⟩ := ihy.1
    obtain ⟨j₂', hj₂'⟩ := ihy.2
    constructor
    · refine ⟨j₂ + j₁, ?_⟩
      calc (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y := by group
        _ = y⁻¹ * t ^ 2 ^ j₁ * y := by rw [hj₁]
        _ = (y⁻¹ * t * y) ^ 2 ^ j₁ := inv_conj_pow_eq y t (2 ^ j₁)
        _ = (t ^ 2 ^ j₂) ^ 2 ^ j₁ := by rw [hj₂]
        _ = t ^ 2 ^ (j₂ + j₁) := by rw [← pow_mul, ← pow_add]
    · refine ⟨j₁' + j₂', ?_⟩
      calc (x * y) * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
        _ = x * t ^ 2 ^ j₂' * x⁻¹ := by rw [hj₂']
        _ = (x * t * x⁻¹) ^ 2 ^ j₂' := conj_pow_eq x t (2 ^ j₂')
        _ = (t ^ 2 ^ j₁') ^ 2 ^ j₂' := by rw [hj₁']
        _ = t ^ 2 ^ (j₁' + j₂') := by rw [← pow_mul, ← pow_add]
  | inv x hx ih =>
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hj⟩ := ih.2
      exact ⟨j, by rwa [inv_inv]⟩
    · obtain ⟨j, hj⟩ := ih.1
      exact ⟨j, by rwa [inv_inv]⟩

end TwoPowerConj

/-! ## §PolyFrobenius: the operator-level char-2 Frobenius and kernel stability

Design doc §3: for `P` over `𝔽₂`, `P(φ^{2^j}) = P(φ)^{2^j}` in the endomorphism
algebra (via `expand` + the trivial Frobenius of `ZMod 2`), so the kernel of `P(t̂)`
is stable under any `g` with `g⁻¹tg = t^{2^j}` — combined with §TwoPowerConj this
makes every isotypic component `C`-stable. -/

section PolyFrobenius

open Polynomial

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction C V]

/-- The action of `t : C` as a `ZMod 2`-linear endomorphism (any additive map is). -/
noncomputable def actEnd (t : C) : Module.End (ZMod 2) V :=
  AddMonoidHom.toZModLinearMap 2 (DistribMulAction.toAddMonoidHom V t)

@[simp] theorem actEnd_apply (t : C) (v : V) : actEnd (V := V) t v = t • v := rfl

/-- `actEnd` turns group powers into endomorphism powers. -/
theorem actEnd_pow (t : C) (n : ℕ) :
    actEnd (V := V) (t ^ n) = (actEnd (V := V) t) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    ext v
    rw [Module.End.one_apply]
    show (1 : C) • v = v
    exact one_smul _ v
  | succ k ih =>
    ext v
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    show (t ^ k * t) • v = actEnd (V := V) (t ^ k) (actEnd (V := V) t v)
    rw [mul_smul]
    rfl

/-- The `𝔽₂`-Frobenius is trivial, so `expand` by `2^j` is literally the `2^j`-th
power of the polynomial. -/
theorem expand_two_pow_eq_pow (P : Polynomial (ZMod 2)) (j : ℕ) :
    Polynomial.expand (ZMod 2) (2 ^ j) P = P ^ 2 ^ j := by
  have h := Polynomial.map_iterateFrobenius_expand (p := 2) P j
  have hid : iterateFrobenius (ZMod 2) 2 j = RingHom.id (ZMod 2) := by
    ext x
    rw [iterateFrobenius_def, RingHom.id_apply]
    have : ∀ (k : ℕ) (y : ZMod 2), y ^ 2 ^ k = y := by
      intro k
      induction k with
      | zero => intro y; rw [pow_zero, pow_one]
      | succ i ih =>
        intro y
        rw [pow_succ, pow_mul, ih, pow_two]
        revert y
        decide
    exact this j x
  rwa [hid, Polynomial.map_id] at h

/-- **The operator-level char-2 Frobenius**: evaluating `P` at the `2^j`-th power of an
endomorphism is the `2^j`-th power of the evaluation. -/
theorem aeval_pow_two_pow (φ : Module.End (ZMod 2) V) (P : Polynomial (ZMod 2)) (j : ℕ) :
    Polynomial.aeval (φ ^ 2 ^ j) P = (Polynomial.aeval φ P) ^ 2 ^ j := by
  calc Polynomial.aeval (φ ^ 2 ^ j) P
      = Polynomial.aeval φ (Polynomial.expand (ZMod 2) (2 ^ j) P) :=
        (Polynomial.expand_aeval _ _ _).symm
    _ = Polynomial.aeval φ (P ^ 2 ^ j) := by rw [expand_two_pow_eq_pow]
    _ = (Polynomial.aeval φ P) ^ 2 ^ j := map_pow _ _ _

/-- Polynomial evaluation transports across the group action by conjugating the
operator. -/
theorem aeval_actEnd_smul (t g : C) (P : Polynomial (ZMod 2)) (v : V) :
    Polynomial.aeval (actEnd (V := V) t) P (g • v)
      = g • (Polynomial.aeval (actEnd (V := V) (g⁻¹ * t * g)) P v) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq, smul_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    show (algebraMap (ZMod 2) (Module.End (ZMod 2) V) a * actEnd (V := V) t ^ n) (g • v)
      = g • ((algebraMap (ZMod 2) (Module.End (ZMod 2) V) a
          * actEnd (V := V) (g⁻¹ * t * g) ^ n) v)
    rw [Module.End.mul_apply, Module.End.mul_apply, ← actEnd_pow, ← actEnd_pow]
    show (algebraMap (ZMod 2) (Module.End (ZMod 2) V) a) ((t ^ n) • (g • v))
      = g • ((algebraMap (ZMod 2) (Module.End (ZMod 2) V) a) (((g⁻¹ * t * g) ^ n) • v))
    have hconj : (t ^ n) • (g • v) = g • (((g⁻¹ * t * g) ^ n) • v) := by
      rw [show (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g from by
          have h := conj_pow_eq g⁻¹ t n
          rw [inv_inv] at h
          exact h.symm,
        ← mul_smul, ← mul_smul]
      congr 1
      group
    rw [hconj]
    show a • (g • (((g⁻¹ * t * g) ^ n) • v)) = g • (a • (((g⁻¹ * t * g) ^ n) • v))
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl
    · rw [zero_smul, zero_smul, smul_zero]
    · rw [one_smul, one_smul]

/-- **Kernel stability** (design doc §3): if `g⁻¹tg = t^{2^j}` then the kernel of any
`P(t̂)` is `g`-stable — `P(t^{2^j}) = P(t)^{2^j}` and powers of a vanishing operator
vanish. -/
theorem smul_mem_ker_aeval {t g : C} {j : ℕ} (hconj : g⁻¹ * t * g = t ^ 2 ^ j)
    (P : Polynomial (ZMod 2)) (v : V)
    (hv : Polynomial.aeval (actEnd (V := V) t) P v = 0) :
    Polynomial.aeval (actEnd (V := V) t) P (g • v) = 0 := by
  rw [aeval_actEnd_smul, hconj, actEnd_pow, aeval_pow_two_pow]
  have hzero : ((Polynomial.aeval (actEnd (V := V) t) P) ^ 2 ^ j) v = 0 := by
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ j = k + 1 := ⟨2 ^ j - 1, by omega⟩
    rw [hk, pow_succ, Module.End.mul_apply, hv, map_zero]
  rw [hzero, smul_zero]

end PolyFrobenius

end RamifiedPack

end GQ2
