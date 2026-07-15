/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.RegularSummand.Trace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The cyclic `2`-group freeness criterion for Lemma 6.11

The constructive counting criterion that recognizes a finite `𝔽₂[P]`-module as a finite power of the regular module.
See `GQ2.RegularSummand` for the paper-facing overview and references.
-/

namespace GQ2

/-! ## The counting criterion for `𝔽₂[P]`-freeness over a cyclic 2-group

`free_of_card_fixedPoints_pow_le`: a finite 2-torsion module `V` over a **cyclic 2-group** `P`
satisfying the counting bound `#V^P ^ |P| ≤ #V` is equivariantly isomorphic to a regular
module `Fin r → P → ZMod 2`.  This is the 𝔽₂-rational endgame of the paper's Lemma 6.11
(pp. 29–30): the paper produces a regular `𝔽̄₂[P]`-basis from free weight orbits and descends
projectivity along the faithfully flat `𝔽₂ ⊆ 𝔽̄₂`; the counting criterion is the rational
shadow of that descent (the reverse bound `#V ≤ #V^P ^ |P|` always holds — Jordan filtration
of the nilpotent `ν := γ + 1`, `γ` the generator action — so the hypothesis pins every block
to full size `|P|`).

Proof shape: `ν^{2^s} = 0` and the group sum is `∑_{p ∈ P} p = ν^{2^s−1}` (freshman's dream
in characteristic 2 — no Lucas/Kummer needed).  If some `v₀` has `ν^{2^s−1} v₀ ≠ 0`, pick a
functional `λ` with `λ(ν^{2^s−1} v₀) = 1`; then the composite `T := φ ∘ j` of the orbit map
`j F := ∑_x F x • x•v₀` with the coefficient map `φ w := (x ↦ λ(x⁻¹•w))` is the convolution
by an augmentation-1 element, i.e. `T = 1 + (nilpotent)·B` — invertible by an **explicit
geometric series** — so `ρ := T⁻¹ ∘ φ` retracts `j` and one free rank-1 block splits off
equivariantly; recurse on the complement (the bound is inherited).  Otherwise
`ν^{2^s−1} = 0`, the kernel filtration gives `#V ≤ #V^P ^ (2^s−1)`, and the counting
hypothesis collapses `V = 0`. -/

section FreenessCriterion

private theorem two_zmod_two_eq_zero : (2 : ZMod 2) = 0 := by decide

/-- Freshman's dream for commuting elements in a ring with `2 = 0`:
`(A + B)^(2^k) = A^(2^k) + B^(2^k)`. -/
private theorem add_pow_two_pow_of_two_eq_zero {R : Type} [Ring R] (h2 : (2 : R) = 0)
    {A B : R} (hAB : Commute A B) (k : ℕ) :
    (A + B) ^ 2 ^ k = A ^ 2 ^ k + B ^ 2 ^ k := by
  have key : ∀ x y : R, Commute x y → (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y hxy
    rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add, ← hxy.eq]
    rw [← add_assoc, add_assoc (x * x), ← two_mul, h2, zero_mul, add_zero]
  induction k with
  | zero => rw [pow_zero, pow_one, pow_one, pow_one]
  | succ k IH =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, IH,
      key (A ^ 2 ^ k) (B ^ 2 ^ k) (hAB.pow_pow _ _)]

/-- In a ring with `2 = 0`, the truncated geometric sum over a 2-power range is itself a
power: `∑_{j<2^k} A^j = (A + 1)^(2^k − 1)`.  (The binomial coefficients `C(2^k−1, i)` are
all odd, but no Lucas theorem is needed — squaring induction suffices.) -/
private theorem geom_sum_two_pow_of_two_eq_zero {R : Type} [Ring R] (h2 : (2 : R) = 0)
    (A : R) (k : ℕ) :
    ∑ j ∈ Finset.range (2 ^ k), A ^ j = (A + 1) ^ (2 ^ k - 1) := by
  induction k with
  | zero =>
    rw [pow_zero, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.sub_self, pow_zero]
  | succ k IH =>
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hsp : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
    have hsplit : ∑ j ∈ Finset.range (2 ^ (k + 1)), A ^ j
        = ∑ j ∈ Finset.range (2 ^ k), A ^ j
          + ∑ j ∈ Finset.range (2 ^ k), A ^ (2 ^ k + j) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun j => A ^ j)
        (Nat.zero_le (2 ^ k)) (by omega : (2 : ℕ) ^ k ≤ 2 ^ (k + 1)), ← Finset.range_eq_Ico,
        Finset.sum_Ico_eq_sum_range, (by omega : 2 ^ (k + 1) - 2 ^ k = 2 ^ k)]
    rw [hsplit, Finset.sum_congr rfl (fun j _ => pow_add A (2 ^ k) j), ← Finset.mul_sum, IH,
      show (A + 1) ^ (2 ^ k - 1) + A ^ 2 ^ k * (A + 1) ^ (2 ^ k - 1)
          = (A + 1) ^ 2 ^ k * (A + 1) ^ (2 ^ k - 1) from by
        rw [add_pow_two_pow_of_two_eq_zero h2 (Commute.one_right A) k, one_pow,
          add_comm (A ^ 2 ^ k) 1, add_mul, one_mul],
      ← pow_add, (by omega : 2 ^ k + (2 ^ k - 1) = 2 ^ (k + 1) - 1)]

/-- Explicit two-sided inverse of `x + 1` for nilpotent `x` in a ring with `2 = 0`
(geometric series; note `x + 1 = x − 1` in characteristic 2). -/
private theorem geom_inverse_of_nilpotent {R : Type} [Ring R] (h2 : (2 : R) = 0)
    {x : R} {m : ℕ} (hm : x ^ m = 0) :
    (x + 1) * ∑ i ∈ Finset.range m, x ^ i = 1
      ∧ (∑ i ∈ Finset.range m, x ^ i) * (x + 1) = 1 := by
  have h11 : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hneg : (-1 : R) = 1 := neg_eq_of_add_eq_zero_left h11
  constructor
  · have h := mul_geom_sum x m
    rwa [hm, zero_sub, sub_eq_add_neg, hneg] at h
  · have h := geom_sum_mul x m
    rwa [hm, zero_sub, sub_eq_add_neg, hneg] at h

/-- `Fin.cons` as an additive equivalence `M × (Fin n → M) ≃+ (Fin (n+1) → M)` — the `≃+`
repackaging of Mathlib's `Fin.consLinearEquiv` over `ℕ` (Mathlib has no direct `≃+` form). -/
private def finConsAddEquiv (M : Type) [AddCommMonoid M] (n : ℕ) :
    (M × (Fin n → M)) ≃+ (Fin (n + 1) → M) :=
  (Fin.consLinearEquiv ℕ fun _ : Fin (n + 1) => M).toAddEquiv

variable {P : Type} [Group P] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction P V] [SMulCommClass P (ZMod 2) V]

/-- The action of a fixed group element as a `ZMod 2`-linear endomorphism. -/
private def genOp (g₀ : P) : Module.End (ZMod 2) V where
  toFun v := g₀ • v
  map_add' a b := smul_add g₀ a b
  map_smul' c a := smul_comm g₀ c a

private theorem genOp_pow_apply (g₀ : P) (k : ℕ) (v : V) :
    ((genOp g₀ : Module.End (ZMod 2) V) ^ k) v = g₀ ^ k • v := by
  induction k generalizing v with
  | zero =>
    rw [pow_zero, pow_zero, one_smul]
    rfl
  | succ k IH =>
    rw [pow_succ, pow_succ, mul_smul]
    exact IH (g₀ • v)

/-- `genOp` turns a power of the group element into a power of the operator. -/
private theorem genOp_pow (g₀ : P) (k : ℕ) :
    (genOp (g₀ ^ k) : Module.End (ZMod 2) V) = (genOp g₀) ^ k := by
  apply LinearMap.ext
  intro v
  rw [genOp_pow_apply]
  rfl

/-- `ν := γ + 1`, the augmentation-style nilpotent attached to the generator action. -/
private def nuOp (g₀ : P) : Module.End (ZMod 2) V := genOp g₀ + 1

/-- The endomorphism ring of a `ZMod 2`-module has `2 = 0`. -/
private theorem end_two_eq_zero {M : Type} [AddCommGroup M] [Module (ZMod 2) M] :
    (2 : Module.End (ZMod 2) M) = 0 := by
  have h2 : (2 : Module.End (ZMod 2) M) = 1 + 1 := one_add_one_eq_two.symm
  ext m
  rw [h2]
  show m + m = (0 : Module.End (ZMod 2) M) m
  rw [← two_smul (ZMod 2) m, (by decide : (2 : ZMod 2) = 0), zero_smul]
  rfl

section WithFintype

variable [Fintype P]

/-- Reindex a sum over a cyclic group by powers of a generator. -/
private theorem sum_eq_sum_range_pow (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {M : Type} [AddCommMonoid M] (f : P → M) :
    ∑ x : P, f x = ∑ k ∈ Finset.range (orderOf g₀), f (g₀ ^ k) := by
  calc ∑ x : P, f x
      = ∑ y : ↥(Subgroup.zpowers g₀), f ↑y :=
        (Fintype.sum_equiv (Equiv.subtypeUnivEquiv hg) _ _ (fun y => rfl)).symm
    _ = ∑ k : Fin (orderOf g₀), f ↑(finEquivZPowers (isOfFinOrder_of_finite g₀) k) :=
        (Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite g₀)) _ _
          (fun k => rfl)).symm
    _ = ∑ k : Fin (orderOf g₀), f (g₀ ^ (k : ℕ)) := by
        refine Fintype.sum_congr _ _ fun k => ?_
        rw [finEquivZPowers_apply]
    _ = ∑ k ∈ Finset.range (orderOf g₀), f (g₀ ^ k) :=
        Fin.sum_univ_eq_sum_range (fun k => f (g₀ ^ k)) (orderOf g₀)

private theorem orderOf_generator (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {s : ℕ} (hs : Fintype.card P = 2 ^ s) : orderOf g₀ = 2 ^ s := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hs]

/-- `ν^(2^s) = 0`: the generator action is unipotent of index dividing `|P| = 2^s`. -/
private theorem nuOp_pow_card_eq_zero (g₀ : P) {s : ℕ} (hs : Fintype.card P = 2 ^ s) :
    (nuOp g₀ : Module.End (ZMod 2) V) ^ 2 ^ s = 0 := by
  have hγ : (genOp g₀ : Module.End (ZMod 2) V) ^ 2 ^ s = 1 := by
    apply LinearMap.ext
    intro v
    rw [genOp_pow_apply, ← hs, pow_card_eq_one, one_smul]
    rfl
  show (genOp g₀ + 1 : Module.End (ZMod 2) V) ^ 2 ^ s = 0
  rw [add_pow_two_pow_of_two_eq_zero end_two_eq_zero (Commute.one_right _) s, hγ, one_pow,
    one_add_one_eq_two, end_two_eq_zero]

/-- The group sum acts as `ν^(2^s − 1)` (the norm element in characteristic 2). -/
private theorem sum_smul_eq_nuOp_pow (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {s : ℕ} (hs : Fintype.card P = 2 ^ s) (v : V) :
    ∑ x : P, x • v = ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v := by
  calc ∑ x : P, x • v
      = ∑ k ∈ Finset.range (orderOf g₀), g₀ ^ k • v :=
        sum_eq_sum_range_pow g₀ hg (fun x => x • v)
    _ = ∑ k ∈ Finset.range (2 ^ s), ((genOp g₀ : Module.End (ZMod 2) V) ^ k) v := by
        rw [orderOf_generator g₀ hg hs]
        exact Finset.sum_congr rfl fun k _ => (genOp_pow_apply g₀ k v).symm
    _ = (∑ k ∈ Finset.range (2 ^ s), (genOp g₀ : Module.End (ZMod 2) V) ^ k) v :=
        (LinearMap.sum_apply _ _ v).symm
    _ = ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v := by
        rw [geom_sum_two_pow_of_two_eq_zero end_two_eq_zero]
        rfl

/-- Right translation by the generator on `P → ZMod 2`: `(rtransOp g₀ F) x = F (x * g₀)`.
This is the `μ` of `split_off_block`, the operator conjugate to the generator action. -/
private def rtransOp (g₀ : P) : Module.End (ZMod 2) (P → ZMod 2) where
  toFun F x := F (x * g₀)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype P] in
/-- Powers of right translation: `(rtransOp g₀ ^ k) F x = F (x * g₀ ^ k)`. -/
private theorem rtransOp_pow_apply (g₀ : P) :
    ∀ (k : ℕ) (F : P → ZMod 2) (x : P), (rtransOp g₀ ^ k) F x = F (x * g₀ ^ k) := by
  intro k
  induction k with
  | zero =>
    intro F x
    rw [pow_zero, pow_zero, mul_one]
    rfl
  | succ k IH =>
    intro F x
    rw [pow_succ, pow_succ, ← mul_assoc]
    exact IH (rtransOp g₀ F) x

/-- Right translation is unipotent of index dividing `|P| = 2^s`:
`(rtransOp g₀ + 1) ^ 2 ^ s = 0`. -/
private theorem rtransOp_add_one_pow_card (g₀ : P) {s : ℕ} (hs : Fintype.card P = 2 ^ s) :
    (rtransOp g₀ + 1) ^ 2 ^ s = 0 := by
  have hcard : rtransOp g₀ ^ 2 ^ s = 1 := by
    apply LinearMap.ext
    intro F
    funext x
    rw [rtransOp_pow_apply, ← hs, pow_card_eq_one, mul_one]
    rfl
  rw [add_pow_two_pow_of_two_eq_zero end_two_eq_zero (Commute.one_right _) s, hcard,
    one_pow, one_add_one_eq_two, end_two_eq_zero]

/-- In a ring with `2 = 0`, every power factors as `x ^ k = 1 + (x + 1) * D` with `D`
commuting with `x + 1` — the telescoping that exhibits `μ^k` as `1 + (μ+1)·(…)`. -/
private theorem exists_geom_factor_of_two_eq_zero {R : Type} [Ring R] (h2 : (2 : R) = 0)
    (x : R) (k : ℕ) : ∃ D : R, x ^ k = 1 + (x + 1) * D ∧ Commute (x + 1) D := by
  induction k with
  | zero => exact ⟨0, by rw [pow_zero, mul_zero, add_zero], Commute.zero_right _⟩
  | succ k IH =>
    obtain ⟨D, hDeq, hDcomm⟩ := IH
    have hx1 : x = 1 + (x + 1) := by
      rw [add_comm 1 (x + 1), add_assoc, one_add_one_eq_two, h2, add_zero]
    refine ⟨1 + D * x, ?_, ?_⟩
    · rw [pow_succ, hDeq, add_mul, one_mul, mul_assoc, mul_add, mul_one, ← add_assoc, ← hx1]
    · exact (Commute.one_right _).add_right
        (hDcomm.mul_right ((Commute.refl x).add_left (Commute.one_left x)))

/-- **Expansion of the convolution `T = φ ∘ j` in powers of right translation.**  For the
orbit map `j F = ∑ₓ F x · (x•v₀)` and coefficient map `φ w x = λ(x⁻¹•w)`, the composite
`φ ∘ j` is the convolution operator `∑_{k<2^s} λ(g₀^k•v₀) · μ^k` where `μ = rtransOp g₀`. -/
private theorem convolution_eq_sum_smul_rtransOp (g₀ : P)
    (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀) {s : ℕ} (hs : Fintype.card P = 2 ^ s) (v₀ : V)
    (lam : V →ₗ[ZMod 2] ZMod 2) (jmap : (P → ZMod 2) →ₗ[ZMod 2] V)
    (phim : V →ₗ[ZMod 2] (P → ZMod 2))
    (hjmap : ∀ F : P → ZMod 2, jmap F = ∑ x : P, F x • (x • v₀))
    (hphim : ∀ (w : V) (x : P), phim w x = lam (x⁻¹ • w)) :
    phim ∘ₗ jmap = ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • rtransOp g₀ ^ k := by
  apply LinearMap.ext
  intro F
  funext x
  have hL : lam (x⁻¹ • jmap F) = ∑ y : P, F y * lam ((x⁻¹ * y) • v₀) := by
    rw [hjmap, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_comm x⁻¹ (F y), map_smul, smul_eq_mul, ← mul_smul]
  have hre : ∑ y : P, F y * lam ((x⁻¹ * y) • v₀)
      = ∑ z : P, F (x * z) * lam (z • v₀) := by
    refine ((Equiv.sum_comp (Equiv.mulLeft x)
      (fun y : P => F y * lam ((x⁻¹ * y) • v₀))).symm).trans ?_
    refine Fintype.sum_congr _ _ fun z => ?_
    show F (x * z) * lam ((x⁻¹ * (x * z)) • v₀) = F (x * z) * lam (z • v₀)
    rw [inv_mul_cancel_left]
  have hpw : ∑ z : P, F (x * z) * lam (z • v₀)
      = ∑ k ∈ Finset.range (2 ^ s), F (x * g₀ ^ k) * lam (g₀ ^ k • v₀) := by
    rw [← orderOf_generator g₀ hg hs]
    exact sum_eq_sum_range_pow g₀ hg (fun z => F (x * z) * lam (z • v₀))
  have hR : (∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • rtransOp g₀ ^ k) F x
      = ∑ k ∈ Finset.range (2 ^ s), F (x * g₀ ^ k) * lam (g₀ ^ k • v₀) := by
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, rtransOp_pow_apply, smul_eq_mul, mul_comm]
  rw [LinearMap.comp_apply, hphim, hL, hre, hpw, hR]

/-- **Split off one free block.**  If `ν^(2^s−1) v₀ ≠ 0`, the sub-representation generated by
`v₀` is a free rank-1 block that splits off equivariantly: `V ≃+ (P → ZMod 2) × W` with a
`P`-stable complement `W` and both components equivariant.  The retraction is
`ρ := T⁻¹ ∘ φ` where `φ w := (x ↦ λ(x⁻¹ • w))` for a functional `λ` with
`λ(ν^(2^s−1) v₀) = 1`, `j F := ∑_x F x • x•v₀` is the orbit map, and `T := φ ∘ j` is
convolution by an augmentation-1 element — `T = 1 + (μ+1)·B` with `μ` the right-translation
by the generator, `(μ+1)^(2^s) = 0`, so `T` has an **explicit geometric-series inverse**
(no finiteness of `V` needed). -/
private theorem split_off_block (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {s : ℕ} (hs : Fintype.card P = 2 ^ s) (v₀ : V)
    (hv₀ : ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ ≠ 0) :
    ∃ (W : Submodule (ZMod 2) V) (ψ : V ≃+ ((P → ZMod 2) × ↥W)),
      (∀ (p : P) (v : V), v ∈ W → p • v ∈ W) ∧
      (∀ (p : P) (v : V) (x : P), (ψ (p • v)).1 x = (ψ v).1 (p⁻¹ * x)) ∧
      (∀ (p : P) (v : V), ((ψ (p • v)).2 : V) = p • ((ψ v).2 : V)) := by
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v, two_zmod_two_eq_zero, zero_smul]
  have hR2 : ∀ F : P → ZMod 2, F + F = 0 := fun F => by
    funext x
    exact CharTwo.add_self_eq_zero (F x)
  -- the functional detecting the deepest layer of the block
  set x₀ : V := ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ with hx₀def
  obtain ⟨lam, hlam⟩ : ∃ lam : V →ₗ[ZMod 2] ZMod 2, lam x₀ = 1 :=
    Module.Projective.exists_dual_eq_one (ZMod 2) hv₀
  -- the orbit map and the coefficient map
  set jmap : (P → ZMod 2) →ₗ[ZMod 2] V :=
    { toFun := fun F => ∑ x : P, F x • (x • v₀)
      map_add' := fun F F' => by
        show ∑ x : P, (F x + F' x) • (x • v₀) = _
        rw [Finset.sum_congr rfl fun x _ => add_smul (F x) (F' x) (x • v₀),
          Finset.sum_add_distrib]
      map_smul' := fun c F => by
        show ∑ x : P, (c * F x) • (x • v₀) = c • ∑ x : P, F x • (x • v₀)
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_smul c (F x) (x • v₀) } with hjdef
  set phim : V →ₗ[ZMod 2] (P → ZMod 2) :=
    { toFun := fun w x => lam (x⁻¹ • w)
      map_add' := fun a b => by
        funext x
        show lam (x⁻¹ • (a + b)) = lam (x⁻¹ • a) + lam (x⁻¹ • b)
        rw [smul_add, map_add]
      map_smul' := fun c a => by
        funext x
        show lam (x⁻¹ • c • a) = c * lam (x⁻¹ • a)
        rw [smul_comm, map_smul, smul_eq_mul] } with hphidef
  -- equivariance of both maps
  have hjeq : ∀ (p : P) (F : P → ZMod 2), jmap (fun x => F (p⁻¹ * x)) = p • jmap F := by
    intro p F
    show ∑ x : P, F (p⁻¹ * x) • (x • v₀) = p • ∑ x : P, F x • (x • v₀)
    rw [Finset.smul_sum]
    calc ∑ x : P, F (p⁻¹ * x) • (x • v₀)
        = ∑ x : P, F (p⁻¹ * (p * x)) • ((p * x) • v₀) :=
          (Equiv.sum_comp (Equiv.mulLeft p) (fun x : P => F (p⁻¹ * x) • (x • v₀))).symm
      _ = ∑ x : P, p • (F x • (x • v₀)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [inv_mul_cancel_left, mul_smul]
          exact (smul_comm p (F x) (x • v₀)).symm
  have hphieq : ∀ (p : P) (w : V) (x : P), phim (p • w) x = phim w (p⁻¹ * x) := by
    intro p w x
    show lam (x⁻¹ • p • w) = lam ((p⁻¹ * x)⁻¹ • w)
    rw [← mul_smul, mul_inv_rev, inv_inv]
  -- the right-translation operator and its unipotency
  set mu : Module.End (ZMod 2) (P → ZMod 2) := rtransOp g₀ with hmudef
  have hnumu : (mu + 1) ^ 2 ^ s = 0 := by
    rw [hmudef]; exact rtransOp_add_one_pow_card g₀ hs
  -- the convolution `T = φ ∘ j` and its expansion in powers of `μ`
  set T : Module.End (ZMod 2) (P → ZMod 2) := phim ∘ₗ jmap with hTdef
  have hTeq : ∀ (p : P) (F : P → ZMod 2),
      T (fun x => F (p⁻¹ * x)) = fun x => (T F) (p⁻¹ * x) := by
    intro p F
    show phim (jmap fun x => F (p⁻¹ * x)) = fun x => phim (jmap F) (p⁻¹ * x)
    rw [hjeq]
    funext x
    exact hphieq p (jmap F) x
  have hTform : T = ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • mu ^ k := by
    rw [hTdef, hmudef]
    exact convolution_eq_sum_smul_rtransOp g₀ hg hs v₀ lam jmap phim
      (fun _ => rfl) (fun _ _ => rfl)
  -- the augmentation of the convolution kernel is 1
  have haug : ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) = 1 := by
    have h1 : ∑ x : P, lam (x • v₀) = ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) := by
      rw [← orderOf_generator g₀ hg hs]
      exact sum_eq_sum_range_pow g₀ hg (fun x => lam (x • v₀))
    rw [← h1, ← map_sum lam (fun x => x • v₀) Finset.univ,
      sum_smul_eq_nuOp_pow g₀ hg hs v₀]
    exact hlam
  -- decompose each `μ^k = 1 + (μ+1)·D_k`
  choose Dk hDk hDkcomm using
    fun k => exists_geom_factor_of_two_eq_zero end_two_eq_zero mu k
  set B : Module.End (ZMod 2) (P → ZMod 2) :=
    ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • Dk k with hBdef
  have hTB : T = 1 + (mu + 1) * B := by
    rw [hTform]
    calc ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • mu ^ k
        = ∑ k ∈ Finset.range (2 ^ s),
            (lam (g₀ ^ k • v₀) • (1 : Module.End (ZMod 2) (P → ZMod 2))
              + lam (g₀ ^ k • v₀) • ((mu + 1) * Dk k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hDk k, smul_add]
      _ = (∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀))
            • (1 : Module.End (ZMod 2) (P → ZMod 2))
            + ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • ((mu + 1) * Dk k) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_smul]
      _ = 1 + (mu + 1) * B := by
          rw [haug, one_smul, hBdef, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_smul_comm]
  -- the explicit inverse of `T`
  have hνB : Commute (mu + 1) B := by
    rw [hBdef]
    exact Commute.sum_right _ _ _ fun k _ => (hDkcomm k).smul_right _
  have hnilB : ((mu + 1) * B) ^ 2 ^ s = 0 := by
    rw [hνB.mul_pow, hnumu, zero_mul]
  set Tinv : Module.End (ZMod 2) (P → ZMod 2) :=
    ∑ i ∈ Finset.range (2 ^ s), ((mu + 1) * B) ^ i with hTinvdef
  have hTT1 : T * Tinv = 1 := by
    rw [hTB, add_comm 1 ((mu + 1) * B), hTinvdef]
    exact (geom_inverse_of_nilpotent end_two_eq_zero hnilB).1
  have hTT2 : Tinv * T = 1 := by
    rw [hTB, add_comm 1 ((mu + 1) * B), hTinvdef]
    exact (geom_inverse_of_nilpotent end_two_eq_zero hnilB).2
  -- the retraction and its equivariance
  set rho : V →ₗ[ZMod 2] (P → ZMod 2) := Tinv ∘ₗ phim with hrhodef
  have hTinv_left : Function.LeftInverse ⇑Tinv ⇑T := fun F => LinearMap.congr_fun hTT2 F
  have hrhoj : ∀ F : P → ZMod 2, rho (jmap F) = F := fun F => hTinv_left F
  have hTrho : ∀ u : V, T (rho u) = phim u := fun u => LinearMap.congr_fun hTT1 (phim u)
  have hTinj : Function.Injective T := hTinv_left.injective
  have hrhoeq : ∀ (p : P) (w : V), rho (p • w) = fun x => rho w (p⁻¹ * x) := by
    intro p w
    apply hTinj
    rw [hTrho, hTeq p (rho w), hTrho]
    funext x
    exact hphieq p w x
  -- the complement and the splitting
  have hker_mem : ∀ v : V, v + jmap (rho v) ∈ LinearMap.ker rho := by
    intro v
    rw [LinearMap.mem_ker, map_add, hrhoj]
    exact hR2 (rho v)
  refine ⟨LinearMap.ker rho,
    { toFun := fun v => (rho v, ⟨v + jmap (rho v), hker_mem v⟩)
      invFun := fun a => jmap a.1 + ↑a.2
      left_inv := fun v => by
        show jmap (rho v) + (v + jmap (rho v)) = v
        rw [add_left_comm, hV2, add_zero]
      right_inv := fun a => by
        refine Prod.ext ?_ ?_
        · show rho (jmap a.1 + ↑a.2) = a.1
          rw [map_add, hrhoj, LinearMap.mem_ker.mp a.2.2, add_zero]
        · apply Subtype.ext
          show (jmap a.1 + ↑a.2) + jmap (rho (jmap a.1 + ↑a.2)) = (↑a.2 : V)
          rw [map_add, hrhoj, LinearMap.mem_ker.mp a.2.2, add_zero, add_right_comm, hV2,
            zero_add]
      map_add' := fun v v' => by
        refine Prod.ext ?_ ?_
        · exact map_add rho v v'
        · apply Subtype.ext
          show (v + v') + jmap (rho (v + v'))
              = (v + jmap (rho v)) + (v' + jmap (rho v'))
          rw [map_add, map_add]
          exact add_add_add_comm v v' (jmap (rho v)) (jmap (rho v')) },
    ?_, ?_, ?_⟩
  · intro p v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hrhoeq p v, hv]
    funext x
    rfl
  · intro p v x
    exact congrFun (hrhoeq p v) x
  · intro p v
    show (p • v) + jmap (rho (p • v)) = p • (v + jmap (rho v))
    rw [smul_add, hrhoeq p v, hjeq p (rho v)]

end WithFintype

/-- Kernel filtration bound: `#ker(f^k) ≤ #ker(f)^k`.  Each layer of the filtration
`ker f ⊆ ker f² ⊆ …` maps into the previous one with kernel inside `ker f`. -/
private theorem card_ker_pow_le {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) (k : ℕ) :
    Nat.card ↥(LinearMap.ker (f ^ k)) ≤ Nat.card ↥(LinearMap.ker f) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    have h : LinearMap.ker (1 : Module.End (ZMod 2) V) = ⊥ := LinearMap.ker_id
    rw [h]
    exact le_of_eq Nat.card_unique
  | succ k IH =>
    have hmap : ∀ x ∈ LinearMap.ker (f ^ (k + 1)), f x ∈ LinearMap.ker (f ^ k) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      calc (f ^ k) (f x) = (f ^ (k + 1)) x := by
            rw [pow_succ]
            rfl
        _ = 0 := hx
    set g := f.restrict hmap with hgdef
    have hdom : Nat.card ↥(LinearMap.ker (f ^ (k + 1)))
        = Nat.card (↥(LinearMap.ker (f ^ (k + 1))) ⧸ g.toAddMonoidHom.ker)
          * Nat.card ↥g.toAddMonoidHom.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have hquot : Nat.card (↥(LinearMap.ker (f ^ (k + 1))) ⧸ g.toAddMonoidHom.ker)
        = Nat.card ↥g.toAddMonoidHom.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g.toAddMonoidHom).toEquiv
    have hrange : Nat.card ↥g.toAddMonoidHom.range ≤ Nat.card ↥(LinearMap.ker (f ^ k)) :=
      Nat.card_le_card_of_injective
        (fun y => (y : ↥(LinearMap.ker (f ^ k)))) (fun y y' hyy => Subtype.ext hyy)
    have hkerg : Nat.card ↥g.toAddMonoidHom.ker ≤ Nat.card ↥(LinearMap.ker f) := by
      refine Nat.card_le_card_of_injective
        (fun y => (⟨((y : ↥(LinearMap.ker (f ^ (k + 1)))) : V), ?_⟩ : ↥(LinearMap.ker f)))
        ?_
      · rw [LinearMap.mem_ker]
        have h0 : g (y : ↥(LinearMap.ker (f ^ (k + 1)))) = 0 :=
          AddMonoidHom.mem_ker.mp y.2
        have h1 : ((g (y : ↥(LinearMap.ker (f ^ (k + 1))))) : V)
            = f ((y : ↥(LinearMap.ker (f ^ (k + 1)))) : V) := rfl
        rw [h0] at h1
        exact h1.symm.trans rfl
      · intro y y' hyy
        have h2 := congrArg (Subtype.val : ↥(LinearMap.ker f) → V) hyy
        apply Subtype.ext
        apply Subtype.ext
        exact h2
    calc Nat.card ↥(LinearMap.ker (f ^ (k + 1)))
        = Nat.card ↥g.toAddMonoidHom.range * Nat.card ↥g.toAddMonoidHom.ker := by
          rw [hdom, hquot]
      _ ≤ Nat.card ↥(LinearMap.ker (f ^ k)) * Nat.card ↥(LinearMap.ker f) :=
          Nat.mul_le_mul hrange hkerg
      _ ≤ Nat.card ↥(LinearMap.ker f) ^ k * Nat.card ↥(LinearMap.ker f) :=
          Nat.mul_le_mul_right _ IH
      _ = Nat.card ↥(LinearMap.ker f) ^ (k + 1) := (pow_succ _ _).symm

/-- **One Jordan-increment identity**: `dim ker f^{k+1} = dim ker f^k + dim(im f^k ⊓ ker f)`.
The map `f^k : ker f^{k+1} → im f^k ⊓ ker f` is onto with kernel `ker f^k`; rank-nullity. -/
theorem finrank_ker_pow_succ {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) (k : ℕ) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 1)))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k))
        + Module.finrank (ZMod 2) ↥(LinearMap.range (f ^ k) ⊓ LinearMap.ker f) := by
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hfpow : ∀ w : V, f ((f ^ k) w) = (f ^ (k + 1)) w := fun w => by rw [pow_succ']; rfl
  have hmono : LinearMap.ker (f ^ k) ≤ LinearMap.ker (f ^ (k + 1)) := by
    intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [← hfpow x, hx, map_zero]
  set g : ↥(LinearMap.ker (f ^ (k + 1))) →ₗ[ZMod 2] V :=
    (f ^ k).comp (LinearMap.ker (f ^ (k + 1))).subtype with hg
  have hgapp : ∀ x : ↥(LinearMap.ker (f ^ (k + 1))), g x = (f ^ k) (x : V) := fun _ => rfl
  have hrange : LinearMap.range g = LinearMap.range (f ^ k) ⊓ LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine Submodule.mem_inf.mpr ⟨⟨x, rfl⟩, ?_⟩
      rw [LinearMap.mem_ker, hgapp, hfpow]; exact x.2
    · rintro y hy
      obtain ⟨⟨z, hz⟩, hy2⟩ := Submodule.mem_inf.mp hy
      rw [LinearMap.mem_ker] at hy2
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, ← hfpow z, hz]; exact hy2
      · rw [hgapp]; exact hz
  have hker : LinearMap.ker g = Submodule.comap (LinearMap.ker (f ^ (k + 1))).subtype
      (LinearMap.ker (f ^ k)) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, hgapp]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker] at hrn
  have hcomap : Module.finrank (ZMod 2)
      ↥(Submodule.comap (LinearMap.ker (f ^ (k + 1))).subtype (LinearMap.ker (f ^ k)))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k)) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hmono)
  rw [hcomap] at hrn
  omega

/-- **Concavity of the Jordan-increment sequence**: `k ↦ dim ker f^k` is concave, i.e.
`dim ker f^{k+2} + dim ker f^k ≤ 2·dim ker f^{k+1}`.  The increment `dim(im f^k ⊓ ker f)` is
non-increasing (`im f^{k+1} ≤ im f^k`, intersect with `ker f`, `finrank_mono`).  This is the
linear-algebra heart of the elementary-abelian reduction (see the section docstring). -/
theorem finrank_ker_pow_concave {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) (k : ℕ) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 2)))
        + Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k))
      ≤ 2 * Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 1))) := by
  have hrmono : LinearMap.range (f ^ (k + 1)) ≤ LinearMap.range (f ^ k) := by
    rintro _ ⟨w, rfl⟩; exact ⟨f w, by rw [pow_succ]; rfl⟩
  have hdmono := Submodule.finrank_mono
    (R := ZMod 2) (M := V) (inf_le_inf_right (LinearMap.ker f) hrmono)
  have hA1 := finrank_ker_pow_succ f k
  have hA2 := finrank_ker_pow_succ f (k + 1)
  rw [show k + 1 + 1 = k + 2 from rfl] at hA2
  omega

/-- The fixed points of the action are exactly the kernel of `ν = γ + 1` (as a count). -/
private theorem card_fixedPoints_eq_card_ker_nuOp (g₀ : P)
    (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀) :
    Nat.card {v : V // ∀ p : P, p • v = v}
      = Nat.card ↥(LinearMap.ker (nuOp g₀ : Module.End (ZMod 2) V)) := by
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v, two_zmod_two_eq_zero, zero_smul]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  rw [LinearMap.mem_ker]
  constructor
  · intro hv
    show g₀ • v + v = 0
    rw [hv g₀]
    exact hV2 v
  · intro h
    have h' : g₀ • v + v = 0 := h
    have hfix : g₀ • v = v := add_right_cancel (h'.trans (hV2 v).symm)
    intro p
    have hg₀mem : g₀ ∈ MulAction.stabilizer P v := MulAction.mem_stabilizer_iff.mpr hfix
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg p)
    rw [← hn]
    exact MulAction.mem_stabilizer_iff.mp (zpow_mem hg₀mem n)

/-! ### Numeric core of the elementary-abelian reduction

For a concave monotone sequence `b` with `b 0 = 0` (the Jordan-kernel dimensions
`b k = dim ker ν^k`), the "midpoint is free" hypothesis `2·b m = b(2m)` forces **every**
increment to equal the first, hence `b(2m) = 2m·b 1`.  Concavity alone gives the reverse
`b(2m) ≤ 2·b m` (increments non-increasing), so a future rep-theory leaf only needs the
inequality `2·b m ≤ b(2m)` (the involution acts freely enough), not the full equality. -/

/-- Concavity's automatic half: `b(2m) ≤ 2·b m` for a concave monotone sequence with
`b 0 = 0` (the increments `e k = b(k+1) − b k` are non-increasing, so the second block of
`m` increments is dominated by the first). -/
private theorem seq_double_le (b : ℕ → ℕ) (hb0 : b 0 = 0) (hmono : ∀ k, b k ≤ b (k + 1))
    (hconc : ∀ k, b (k + 2) + b k ≤ 2 * b (k + 1)) (m : ℕ) : b (2 * m) ≤ 2 * b m := by
  set e : ℕ → ℕ := fun k => b (k + 1) - b k with he
  have he_add : ∀ k, b (k + 1) = b k + e k := fun k => (Nat.add_sub_cancel' (hmono k)).symm
  have he_anti_succ : ∀ k, e (k + 1) ≤ e k := by
    intro k
    have h1 := he_add k
    have h2 := he_add (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h2
    have h3 := hconc k
    omega
  have he_anti : Antitone e := antitone_nat_of_succ_le he_anti_succ
  have hsum : ∀ n, b n = ∑ k ∈ Finset.range n, e k := by
    intro n
    induction n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, hb0]
    | succ n IH => rw [Finset.sum_range_succ, ← IH, he_add n]
  have hsplit : b (2 * m) = b m + ∑ j ∈ Finset.range m, e (m + j) := by
    rw [show 2 * m = m + m from by ring, hsum (m + m), hsum m, Finset.sum_range_add]
  have hle2 : ∑ j ∈ Finset.range m, e (m + j) ≤ ∑ j ∈ Finset.range m, e j :=
    Finset.sum_le_sum (fun j _ => he_anti (by omega))
  rw [hsplit, hsum m, two_mul]
  exact Nat.add_le_add_left hle2 _

/-- Numeric core of the reduction: a concave monotone sequence with `b 0 = 0` and
`2·b m = b(2m)` (`m ≥ 1`) satisfies `2m·b 1 ≤ b(2m)` — indeed with equality, all increments
being forced equal to `b 1`.  (Two equal `m`-term sums with pairwise-dominating terms are
termwise equal; antitone squeeze then flattens the first block.) -/
private theorem seq_first_increment_le (b : ℕ → ℕ) (hb0 : b 0 = 0)
    (hmono : ∀ k, b k ≤ b (k + 1)) (hconc : ∀ k, b (k + 2) + b k ≤ 2 * b (k + 1))
    (m : ℕ) (hm : 1 ≤ m) (hhalf : 2 * b m = b (2 * m)) : 2 * m * b 1 ≤ b (2 * m) := by
  set e : ℕ → ℕ := fun k => b (k + 1) - b k with he
  have he_add : ∀ k, b (k + 1) = b k + e k := fun k => (Nat.add_sub_cancel' (hmono k)).symm
  have he_anti_succ : ∀ k, e (k + 1) ≤ e k := by
    intro k
    have h1 := he_add k
    have h2 := he_add (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h2
    have h3 := hconc k
    omega
  have he_anti : Antitone e := antitone_nat_of_succ_le he_anti_succ
  have hsum : ∀ n, b n = ∑ k ∈ Finset.range n, e k := by
    intro n
    induction n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, hb0]
    | succ n IH => rw [Finset.sum_range_succ, ← IH, he_add n]
  have he0 : e 0 = b 1 := by show b 1 - b 0 = b 1; omega
  have hsplit : b (2 * m) = b m + ∑ j ∈ Finset.range m, e (m + j) := by
    rw [show 2 * m = m + m from by ring, hsum (m + m), hsum m, Finset.sum_range_add]
  have heq_sums : ∑ j ∈ Finset.range m, e j = ∑ j ∈ Finset.range m, e (m + j) := by
    have h := hsplit
    rw [← hhalf, two_mul] at h
    have hc := Nat.add_left_cancel h
    rw [hsum m] at hc
    exact hc
  have hle : ∀ j ∈ Finset.range m, e (m + j) ≤ e j := fun j _ => he_anti (by omega)
  have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq_sums.symm
  have he0m : e m = e 0 := by simpa using hterm 0 (Finset.mem_range.mpr hm)
  have hconst : ∀ j, j < m → e j = e 0 := by
    intro j hj
    have h1 : e j ≤ e 0 := he_anti (Nat.zero_le j)
    have h2 : e m ≤ e j := he_anti (by omega)
    omega
  have hbm_eq : b m = m * e 0 := by
    rw [hsum m, Finset.sum_congr rfl (fun j hj => hconst j (Finset.mem_range.mp hj)),
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hfinal : b (2 * m) = 2 * m * b 1 := by rw [← hhalf, hbm_eq, he0]; ring
  exact hfinal.ge

/-- The inductive engine behind the counting criterion: peel off one free block at a time.
Ordinary induction on a bound `n` for `#V` suffices, since the complement has strictly
smaller cardinality. -/
private theorem free_of_card_aux (P : Type) [Group P] [Finite P]
    (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀) (s : ℕ)
    (hs : Nat.card P = 2 ^ s) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Finite V] [DistribMulAction P V],
      Nat.card V ≤ n → (∀ v : V, v + v = 0) →
      Nat.card {v : V // ∀ p : P, p • v = v} ^ 2 ^ s ≤ Nat.card V →
      ∃ (r : ℕ) (φ : V ≃+ (Fin r → P → ZMod 2)),
        ∀ (p : P) (v : V) (m : Fin r) (x : P), φ (p • v) m x = φ v m (p⁻¹ * x) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ hle _ _
    haveI : Nonempty V := ⟨0⟩
    have := Nat.card_pos (α := V)
    omega
  | succ n IH =>
    intro V _ _ _ hle hV2 hcount
    letI : Module (ZMod 2) V := AddCommGroup.zmodModule fun v => (two_nsmul v).trans (hV2 v)
    letI : SMulCommClass P (ZMod 2) V :=
      ⟨fun p c v => by rcases ZMod.eq_zero_or_eq_one c with rfl | rfl <;> simp⟩
    haveI : Fintype P := Fintype.ofFinite P
    have hsF : Fintype.card P = 2 ^ s := by rw [← Nat.card_eq_fintype_card]; exact hs
    have hfixker := card_fixedPoints_eq_card_ker_nuOp (V := V) g₀ hg
    by_cases hex : ∃ v₀ : V, ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ ≠ 0
    · -- a full-depth vector exists: split off one free block and recurse
      obtain ⟨v₀, hv₀⟩ := hex
      obtain ⟨W, ψ, hWstable, hψ1, hψ2⟩ := split_off_block g₀ hg hsF v₀ hv₀
      letI actW : DistribMulAction P ↥W :=
        { smul := fun p w => ⟨p • (w : V), hWstable p (w : V) w.2⟩
          one_smul := fun w => Subtype.ext (one_smul P (w : V))
          mul_smul := fun p q w => Subtype.ext (mul_smul p q (w : V))
          smul_zero := fun p => Subtype.ext (smul_zero p)
          smul_add := fun p w w' => Subtype.ext (smul_add p (w : V) (w' : V)) }
      have hcardR : Nat.card (P → ZMod 2) = 2 ^ 2 ^ s := by
        rw [Nat.card_fun, Nat.card_zmod, hs]
      have hcardV : Nat.card V = 2 ^ 2 ^ s * Nat.card ↥W := by
        rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, hcardR]
      haveI : Nonempty ↥W := ⟨0⟩
      have hWpos : 0 < Nat.card ↥W := Nat.card_pos
      have h2pow : (2 : ℕ) ≤ 2 ^ 2 ^ s := Nat.le_self_pow (Nat.two_pow_pos s).ne' 2
      have hWle : Nat.card ↥W ≤ n := by
        have h3 : 2 * Nat.card ↥W ≤ 2 ^ 2 ^ s * Nat.card ↥W :=
          Nat.mul_le_mul_right _ h2pow
        omega
      have hV2W : ∀ w : ↥W, w + w = 0 := fun w => Subtype.ext (hV2 (w : V))
      -- fixed points inject: `ZMod 2 × Fix(W) ↪ Fix(V)` via `ψ⁻¹(const, ·)`
      have hfixsymm : ∀ (cc : ZMod 2) (w : {w : ↥W // ∀ p : P, p • w = w}) (p : P),
          p • ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W))
            = ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W)) := by
        intro cc w p
        apply ψ.injective
        refine Prod.ext ?_ ?_
        · funext x
          rw [hψ1 p (ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W))) x,
            AddEquiv.apply_symm_apply]
        · apply Subtype.ext
          rw [hψ2 p (ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W))),
            AddEquiv.apply_symm_apply]
          exact congrArg (Subtype.val : ↥W → V) (w.2 p)
      have hfixinj : 2 * Nat.card {w : ↥W // ∀ p : P, p • w = w}
          ≤ Nat.card {v : V // ∀ p : P, p • v = v} := by
        have hcard2 : Nat.card (ZMod 2 × {w : ↥W // ∀ p : P, p • w = w})
            = 2 * Nat.card {w : ↥W // ∀ p : P, p • w = w} := by
          rw [Nat.card_prod, Nat.card_zmod]
        rw [← hcard2]
        refine Nat.card_le_card_of_injective
          (fun cw => ⟨ψ.symm ((fun _ => cw.1 : P → ZMod 2), (cw.2 : ↥W)),
            fun p => hfixsymm cw.1 cw.2 p⟩) ?_
        intro cw cw' hcc
        have h1 : ψ.symm ((fun _ => cw.1 : P → ZMod 2), (cw.2 : ↥W))
            = ψ.symm ((fun _ => cw'.1 : P → ZMod 2), (cw'.2 : ↥W)) :=
          congrArg (Subtype.val : {v : V // ∀ p : P, p • v = v} → V) hcc
        have h2 : ((fun _ => cw.1 : P → ZMod 2), (cw.2 : ↥W))
            = ((fun _ => cw'.1 : P → ZMod 2), (cw'.2 : ↥W)) := ψ.symm.injective h1
        refine Prod.ext ?_ ?_
        · exact congrFun (congrArg Prod.fst h2) (1 : P)
        · exact Subtype.ext (congrArg Prod.snd h2)
      have hcountW : Nat.card {w : ↥W // ∀ p : P, p • w = w} ^ 2 ^ s ≤ Nat.card ↥W := by
        have h4 : (2 * Nat.card {w : ↥W // ∀ p : P, p • w = w}) ^ 2 ^ s ≤ Nat.card V :=
          le_trans (Nat.pow_le_pow_left hfixinj _) hcount
        rw [mul_pow, hcardV] at h4
        exact Nat.le_of_mul_le_mul_left h4 (by omega)
      obtain ⟨r', φ', hφ'⟩ := IH ↥W hWle hV2W hcountW
      refine ⟨r' + 1,
        (ψ.trans ((AddEquiv.refl (P → ZMod 2)).prodCongr φ')).trans
          (finConsAddEquiv (P → ZMod 2) r'), ?_⟩
      have hunfold : ∀ u : V,
          ((ψ.trans ((AddEquiv.refl (P → ZMod 2)).prodCongr φ')).trans
            (finConsAddEquiv (P → ZMod 2) r')) u
            = Fin.cons (α := fun _ => P → ZMod 2) ((ψ u).1) (φ' ((ψ u).2)) :=
        fun u => rfl
      intro p v m x
      rw [hunfold, hunfold]
      refine Fin.cases ?_ (fun i => ?_) m
      · rw [Fin.cons_zero, Fin.cons_zero]
        exact hψ1 p v x
      · rw [Fin.cons_succ, Fin.cons_succ]
        have hw : (ψ (p • v)).2 = p • (ψ v).2 := Subtype.ext (hψ2 p v)
        rw [hw]
        exact hφ' p ((ψ v).2) i x
    · -- no full-depth vector: the filtration bound forces `V = 0`
      have hall : ∀ v₀ : V, ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ = 0 :=
        fun v₀ => not_not.mp fun h => hex ⟨v₀, h⟩
      have hzero : (nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1) = 0 :=
        LinearMap.ext hall
      have hVtop : Nat.card V
          = Nat.card ↥(LinearMap.ker
              ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1))) := by
        rw [hzero, LinearMap.ker_zero]
        exact (Nat.card_congr Submodule.topEquiv.toEquiv).symm
      have hbound : Nat.card V
          ≤ Nat.card {v : V // ∀ p : P, p • v = v} ^ (2 ^ s - 1) := by
        rw [hVtop, hfixker]
        exact card_ker_pow_le _ _
      haveI : Nonempty {v : V // ∀ p : P, p • v = v} := ⟨⟨0, fun p => smul_zero p⟩⟩
      have hfixpos : 0 < Nat.card {v : V // ∀ p : P, p • v = v} := Nat.card_pos
      have hple : Nat.card {v : V // ∀ p : P, p • v = v} ≤ 1 := by
        by_contra hgt
        have hgt' : 1 < Nat.card {v : V // ∀ p : P, p • v = v} := not_le.mp hgt
        have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
        have hlt : Nat.card {v : V // ∀ p : P, p • v = v} ^ (2 ^ s - 1)
            < Nat.card {v : V // ∀ p : P, p • v = v} ^ 2 ^ s :=
          Nat.pow_lt_pow_right hgt' (by omega)
        omega
      have hVone : Nat.card V ≤ 1 := by
        have h5 := Nat.pow_le_pow_left hple (2 ^ s - 1)
        rw [one_pow] at h5
        omega
      haveI : Nonempty V := ⟨0⟩
      have hVcard : Nat.card V = 1 := le_antisymm hVone Nat.card_pos
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hVcard
      exact ⟨0,
        { toFun := fun _ m => m.elim0
          invFun := fun _ => 0
          left_inv := fun v => Subsingleton.elim _ _
          right_inv := fun F => funext fun m => m.elim0
          map_add' := fun a b => funext fun m => m.elim0 },
        fun p v m x => m.elim0⟩

/-- **The counting criterion for `𝔽₂[P]`-freeness over a cyclic 2-group**: a finite
2-torsion `P`-module with `#V^P ^ |P| ≤ #V` is equivariantly isomorphic to a regular module
`Fin r → P → ZMod 2` (with the left-translation action spelled inline).  The reverse
inequality is automatic, so the hypothesis says exactly that the fixed space is as small as
freeness demands. -/
theorem free_of_card_fixedPoints_pow_le {P : Type} [Group P] [Finite P]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction P V]
    (hV2 : ∀ v : V, v + v = 0) (hcyc : IsCyclic P) (h2 : IsPGroup 2 P)
    (hcount : Nat.card {v : V // ∀ p : P, p • v = v} ^ Nat.card P ≤ Nat.card V) :
    ∃ (r : ℕ) (φ : V ≃+ (Fin r → P → ZMod 2)),
      ∀ (p : P) (v : V) (m : Fin r) (x : P), φ (p • v) m x = φ v m (p⁻¹ * x) := by
  obtain ⟨g₀, hg⟩ := hcyc.exists_generator
  obtain ⟨s, hs⟩ := h2.exists_card_eq
  rw [hs] at hcount
  exact free_of_card_aux P g₀ hg s hs (Nat.card V) V le_rfl hV2 hcount

/-- **Elementary-abelian reduction of the counting bound to the involution** `ω = g₀^{2^{s-1}}`.
Given the involution's own counting bound `#V^ω ^ 2 ≤ #V` (ω acts "freely enough"), the full
`𝔽₂[P]`-counting bound `#V^P ^ |P| ≤ #V` follows.  This is the standard reduction of freeness
over a cyclic `p`-group to freeness over its order-`p` subgroup, the `p = 2` case of
Chouinard's theorem, made elementary here: `b k := dim ker ν^k` is concave
(`finrank_ker_pow_concave`) with `b 0 = 0` and `b(2^s) = dim V`; the leaf gives
`2·b(2^{s-1}) ≤ dim V = b(2^s)` and concavity gives the reverse (`seq_double_le`), so
`2·b(2^{s-1}) = b(2^s)` and `seq_first_increment_le` forces `2^s·b 1 = b(2^s)`, whence
`#V^P ^ |P| = 2^{b 1·2^s} ≤ 2^{dim V} = #V`. -/
theorem card_fixedPoints_pow_le_of_half {P : Type} [Group P] [Finite P]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction P V]
    (hV2 : ∀ v : V, v + v = 0) (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    (s : ℕ) (hs : Nat.card P = 2 ^ s)
    (hleaf : Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2 ≤ Nat.card V) :
    Nat.card {v : V // ∀ p : P, p • v = v} ^ Nat.card P ≤ Nat.card V := by
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule fun v => (two_nsmul v).trans (hV2 v)
  letI : SMulCommClass P (ZMod 2) V :=
    ⟨fun p c v => by rcases ZMod.eq_zero_or_eq_one c with rfl | rfl <;> simp⟩
  haveI : Fintype P := Fintype.ofFinite P
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hsF : Fintype.card P = 2 ^ s := by rw [← Nat.card_eq_fintype_card]; exact hs
  -- card ↔ finrank over 𝔽₂
  have hcardpow : ∀ (p : Submodule (ZMod 2) V),
      Nat.card ↥p = 2 ^ Module.finrank (ZMod 2) ↥p := by
    intro p
    haveI : Fintype ↥p := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥p), ZMod.card]
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    haveI : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card]
  set f : Module.End (ZMod 2) V := nuOp g₀ with hf
  set b : ℕ → ℕ := fun k => Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k)) with hb
  have hb0 : b 0 = 0 := by
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ 0)) = 0
    rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id, finrank_bot]
  have hmono : ∀ k, b k ≤ b (k + 1) := by
    intro k; have := finrank_ker_pow_succ f k
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k))
      ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 1)))
    omega
  have hconc : ∀ k, b (k + 2) + b k ≤ 2 * b (k + 1) := fun k => finrank_ker_pow_concave f k
  have hbtop : b (2 ^ s) = Module.finrank (ZMod 2) V := by
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (2 ^ s))) = _
    rw [hf, nuOp_pow_card_eq_zero g₀ hsF, LinearMap.ker_zero, finrank_top]
  -- fixed points of the whole group = 2^{b 1}
  have hb1 : b 1 = Module.finrank (ZMod 2)
      ↥(LinearMap.ker (nuOp g₀ : Module.End (ZMod 2) V)) := by
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ 1)) = _
    rw [pow_one]
  have hVP : Nat.card {v : V // ∀ p : P, p • v = v} = 2 ^ b 1 := by
    rw [card_fixedPoints_eq_card_ker_nuOp g₀ hg, hcardpow, hb1]
  -- s = 0: P trivial, bound is #V^P ≤ #V
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    rw [hs, pow_zero, pow_one]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  set m : ℕ := 2 ^ (t + 1) / 2 with hmdef
  have hm_pow : m = 2 ^ t := by rw [hmdef, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have h2m : 2 * m = 2 ^ (t + 1) := by rw [hm_pow, pow_succ]; ring
  have hm : 1 ≤ m := by rw [hm_pow]; exact Nat.one_le_two_pow
  -- ν^m = nuOp(g₀^m) (freshman, m = 2^t)
  have hnu_m : (nuOp (g₀ ^ m) : Module.End (ZMod 2) V)
      = f ^ m := by
    have h1 : (nuOp (g₀ ^ m) : Module.End (ZMod 2) V)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ m + 1 := by
      show (genOp (g₀ ^ m) + 1 : Module.End (ZMod 2) V)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ m + 1
      rw [genOp_pow]
    have h2 : (f ^ m : Module.End (ZMod 2) V)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ m + 1 := by
      rw [hf, hm_pow]
      show ((genOp g₀ + 1 : Module.End (ZMod 2) V)) ^ (2 ^ t)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ t) + 1
      rw [add_pow_two_pow_of_two_eq_zero end_two_eq_zero
        (Commute.one_right (genOp g₀ : Module.End (ZMod 2) V)) t, one_pow]
    rw [h1, h2]
  -- the leaf count: #V^{g₀^m} = 2^{b m}
  have hleafcard : Nat.card {v : V // (g₀ ^ m) • v = v} = 2 ^ b m := by
    have hbridge : Nat.card {v : V // (g₀ ^ m) • v = v}
        = Nat.card ↥(LinearMap.ker (nuOp (g₀ ^ m) : Module.End (ZMod 2) V)) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      rw [LinearMap.mem_ker]
      constructor
      · intro hv
        show (g₀ ^ m) • v + v = 0
        rw [hv]; exact hV2 v
      · intro h
        have h' : (g₀ ^ m) • v + v = 0 := h
        exact add_right_cancel (h'.trans (hV2 v).symm)
    rw [hbridge, hnu_m, hcardpow]
  -- leaf ⟹ 2·b m ≤ dim V
  have hleafle : 2 * b m ≤ Module.finrank (ZMod 2) V := by
    have hl := hleaf
    rw [hleafcard, hcardV, ← pow_mul,
      Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)] at hl
    omega
  -- concavity's reverse ⟹ equality at the midpoint
  have hdouble : b (2 * m) ≤ 2 * b m := seq_double_le b hb0 hmono hconc m
  have hhalf : 2 * b m = b (2 * m) := by
    refine le_antisymm ?_ hdouble
    rw [h2m, hbtop]; exact hleafle
  have hkey := seq_first_increment_le b hb0 hmono hconc m hm hhalf
  rw [h2m, hbtop] at hkey
  -- assemble
  rw [hVP, hs, hcardV, ← pow_mul, Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), mul_comm]
  exact hkey

end FreenessCriterion

end GQ2
