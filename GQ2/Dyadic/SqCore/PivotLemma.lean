/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.ZtwoPowering
public import GQ2.Roe.ChiR

@[expose] public section

/-!
# SQ4(1) — the `SqMixPivot` exponent datum: `1 + 4ℤ₂` is procyclic

**Ticket SQ4**, part 1, of the dyadic campaign (lane SQ).  MC5's `L_sq` handle-mixing redo
(`GQ2/Dyadic/MarkedCore/Certificate.lean` §6) identified one missing input: the corrected
clearing pivot `w = σ · x₀^{−c}` is defined in terms of an exponent `c` with `X^c = S`, where
`X = rootXUnit` and `S = SvalUnit` are the Hensel orientation values of the `L_sq` core, and
the *existence* of such a `c` — a statement about the procyclic group `1 + 4ℤ₂` — was recorded
as an **SQ4 supply obligation** (board log 2026-07-31, MC5 outcomes item (iv)).  This file
discharges it, unconditionally.

## The mathematics

`GQ2/ZtwoPowering.lean` develops `ℤ₂`-powering on pro-2 groups and proves the *injectivity*
half of "an element of exact level two topologically generates `1 + 4ℤ₂`"
(`zpowZtwo_injective_of_exact_level`).  The missing half is **surjectivity**, and it is proved
here by the classical two-step argument:

1. **Approximation** (`exists_nat_pow_sub_dvd`).  If `η − 1 = 4a` with `a ∈ ℤ₂ˣ` then for every
   `k` some *natural* power `η^n` matches the target `ξ ∈ 1 + 4ℤ₂` modulo `2^{k+2}`.  The
   induction step is the digit step of the 2-adic logarithm, done by hand: `η^{2^k} − 1`
   is `2^{k+2}·(unit)` (`exists_unit_pow_two_pow_sub_one`, already in the repo), so
   multiplying by `η^{2^k}` flips exactly the `2^{k+2}`-digit — and "odd + odd = even" closes
   the step.
2. **Passage to the limit** (`exists_zpowZtwo_eq_of_exact_level`).  The approximation sets
   `A k = {c : ℤ₂ | 2^{k+2} ∣ η^c − ξ}` are closed (preimages of a closed ball under the
   continuous `c ↦ η^c`), nested, and nonempty, and `ℤ₂` is compact — so Cantor's intersection
   theorem produces a genuine 2-adic exponent, and `⋂_k 2^k ℤ₂ = 0` upgrades the congruences
   to an equality.

The **unit-ness** of the exponent (`isUnit_exponent_of_zpowZtwo_eq`) needs the target to have
exact level two as well, and is elementary: if `c` were even then `ξ` would be the square of a
2-adic unit, and odd squares are `1 mod 8`, contradicting `v₂(ξ − 1) = 2`.

## The `L_sq` instance

`exists_isUnit_zpowZtwo_eq_SvalUnit` specializes at `η = X`, `ξ = S`: both have exact level two
(`rootX_sub_one_eq`, `Sval_sub_one_eq` — `GQ2/Roe/OrientationRoot.lean`), so

```text
∃ c : ℤ₂,  IsUnit c  ∧  X ^ c = S .
```

This is exactly the field of MC5's `SqMixPivot` record, which `GQ2/Dyadic/SqCore/Certificate.lean`
therefore produces as a **theorem** rather than carrying as a hypothesis.  MC5's mod-16 evidence
pin `sval_congr_rootX_cubed` (`S ≡ X³ (16)`) says any such `c` satisfies `c ≡ 3 (4)`; nothing
below consumes it, and nothing below determines `c` beyond its existence — the cubic
`Z³ + 2Z² + 1` has no closed-form root, so neither does its exponent.

## Placement (recorded deviation)

§1's content is about `ℤ₂ˣ` alone and its natural home is `GQ2/ZtwoPowering.lean`, next to the
injectivity half (MC5's log says so explicitly).  SQ4 does not own that file, so the general
statements live here in namespace `GQ2` — spelled so that a later hoist is a pure file move,
with no consumer edits.  A `ZtwoPowering.lean` owner should perform that move; this file's §2
is the only `L_sq`-specific content.

## Axiom hygiene

Everything in this file prints within **std-3** (`propext`, `Classical.choice`, `Quot.sound`):
the inputs are `ZtwoPowering`'s pro-2 machinery and `OrientationRoot`'s Hensel data, both
axiom-free beyond std-3.  No census axiom is reachable, so the `L_sq` certificate can consume
the pivot datum without dragging B3c/B8 into the h-generic layer.
-/

namespace GQ2

/-! ## §1 Procyclicity of `1 + 4ℤ₂`

An element of exact level two topologically generates the principal units of level two, so
every other element of exact level two is a *unit* power of it.  Stated for `ℤ₂ˣ` with levels
recorded algebraically (`x − 1 = 4·unit`), the convention `ZtwoPowering.lean` already uses. -/

section ProcyclicLevelTwo

/-- An element of `ℤ₂` not divisible by `2` is a unit (`ℤ₂` is local with maximal ideal
`(2)`). -/
theorem isUnit_of_not_two_dvd {x : ℤ_[2]} (hx : ¬ (2 : ℤ_[2]) ∣ x) : IsUnit x := by
  by_contra hu
  refine hx ?_
  have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  exact hmem

/-- Every `2`-adic unit is `≡ 1 (mod 2)` — the `IsUnit`-shaped form of
`two_dvd_val_sub_one`. -/
theorem two_dvd_sub_one_of_isUnit {x : ℤ_[2]} (hx : IsUnit x) : (2 : ℤ_[2]) ∣ x - 1 := by
  obtain ⟨u, rfl⟩ := hx
  exact two_dvd_val_sub_one u

/-- **Odd + odd = even**, 2-adically: the sum of two units is divisible by `2`.  (The parity
step of the digit induction below.) -/
theorem two_dvd_add_of_isUnit {x y : ℤ_[2]} (hx : IsUnit x) (hy : IsUnit y) :
    (2 : ℤ_[2]) ∣ x + y := by
  have h := dvd_add (two_dvd_sub_one_of_isUnit hx) (two_dvd_sub_one_of_isUnit hy)
  have hxy : x + y = x - 1 + (y - 1) + 2 := by ring
  rw [hxy]
  exact dvd_add h dvd_rfl

/-- **The approximation half** (digit induction): if `η − 1 = 4a` with `a` a unit — i.e.
`v₂(η − 1) = 2` exactly — then every `ξ ∈ 1 + 4ℤ₂` is matched by a *natural* power of `η`
modulo `2^{k+2}`, for every `k`.

The step is the 2-adic digit step: `η^{2^k} = 1 + 2^{k+2}·(unit)`
(`exists_unit_pow_two_pow_sub_one`), so multiplying by `η^{2^k}` changes the residue by exactly
`2^{k+2}·(odd)`; if the current defect digit is odd, that move kills it. -/
theorem exists_nat_pow_sub_dvd (η a : ℤ_[2]ˣ) (hη : ((η : ℤ_[2])) - 1 = 4 * (a : ℤ_[2]))
    {ξ : ℤ_[2]} (hξ : (2 : ℤ_[2]) ^ 2 ∣ ξ - 1) (k : ℕ) :
    ∃ n : ℕ, (2 : ℤ_[2]) ^ (k + 2) ∣ ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) - ξ := by
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := hξ
    refine ⟨0, -t, ?_⟩
    rw [pow_zero, Units.val_one]
    linear_combination -ht
  | succ j ih =>
    obtain ⟨n, d, hd⟩ := ih
    by_cases hdiv : (2 : ℤ_[2]) ∣ d
    · obtain ⟨e, he⟩ := hdiv
      exact ⟨n, e, by rw [hd, he]; ring⟩
    obtain ⟨u, hu⟩ := exists_unit_pow_two_pow_sub_one η a hη j
    have hval : ((η ^ (n + 2 ^ j) : ℤ_[2]ˣ) : ℤ_[2])
        = ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) * ((η ^ 2 ^ j : ℤ_[2]ˣ) : ℤ_[2]) := by
      rw [pow_add, Units.val_mul]
    have hstep : ((η ^ (n + 2 ^ j) : ℤ_[2]ˣ) : ℤ_[2]) - ξ
        = 2 ^ (j + 2) * (d + (u : ℤ_[2]) * ((η ^ n : ℤ_[2]ˣ) : ℤ_[2])) := by
      rw [hval]
      linear_combination hd + ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) * hu
    obtain ⟨e, he⟩ := two_dvd_add_of_isUnit (isUnit_of_not_two_dvd hdiv)
      (u.isUnit.mul (η ^ n).isUnit)
    exact ⟨n + 2 ^ j, e, by rw [hstep, he]; ring⟩

/-- **Procyclic surjectivity of `1 + 4ℤ₂`**: an element `η` of exact level two hits every
`ξ ∈ 1 + 4ℤ₂` at some 2-adic exponent.

*Proof.*  The approximation sets `A k = {c | 2^{k+2} ∣ η^c − ξ}` are closed (the map
`c ↦ η^c` is continuous and the divisibility condition is a closed ball), decreasing, and
nonempty by `exists_nat_pow_sub_dvd` — the integer exponents witnessing the congruences.  `ℤ₂`
is compact, so Cantor's intersection theorem gives a common exponent `c`, and an element
divisible by every `2^n` is zero. -/
theorem exists_zpowZtwo_eq_of_exact_level (η a : ℤ_[2]ˣ)
    (hη : ((η : ℤ_[2])) - 1 = 4 * (a : ℤ_[2])) {ξ : ℤ_[2]ˣ}
    (hξ : (2 : ℤ_[2]) ^ 2 ∣ ((ξ : ℤ_[2])) - 1) :
    ∃ c : ℤ_[2], zpowZtwo isProP_two_unitsPadicInt η c = ξ := by
  set f : ℤ_[2] → ℤ_[2] :=
    fun c => ((zpowZtwo isProP_two_unitsPadicInt η c : ℤ_[2]ˣ) : ℤ_[2]) with hf
  have hcont : Continuous f :=
    Units.continuous_val.comp (continuous_zpowZtwo isProP_two_unitsPadicInt η)
  set A : ℕ → Set ℤ_[2] := fun k => {c | (2 : ℤ_[2]) ^ (k + 2) ∣ f c - (ξ : ℤ_[2])} with hA
  have hball : ∀ k, A k = f ⁻¹' Metric.closedBall ((ξ : ℤ_[2]))
      (((2 : ℕ) : ℝ) ^ (-((k + 2 : ℕ) : ℤ))) := by
    intro k
    ext c
    show (2 : ℤ_[2]) ^ (k + 2) ∣ f c - (ξ : ℤ_[2]) ↔ _
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    norm_cast
  have hclosed : ∀ k, IsClosed (A k) := fun k => by
    rw [hball k]; exact Metric.isClosed_closedBall.preimage hcont
  have hne : ∀ k, (A k).Nonempty := by
    intro k
    obtain ⟨n, hn⟩ := exists_nat_pow_sub_dvd η a hη hξ k
    refine ⟨(n : ℤ_[2]), ?_⟩
    have hpow : f ((n : ℕ) : ℤ_[2]) = ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) :=
      congrArg Units.val (zpowZtwo_natCast isProP_two_unitsPadicInt η n)
    show (2 : ℤ_[2]) ^ (k + 2) ∣ f ((n : ℕ) : ℤ_[2]) - (ξ : ℤ_[2])
    rw [hpow]
    exact hn
  have hmono : ∀ k, A (k + 1) ⊆ A k := by
    intro k c hc
    exact dvd_trans (pow_dvd_pow (2 : ℤ_[2]) (by omega)) hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hmono
    hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hc
  refine ⟨c, Units.ext ?_⟩
  have hzero : f c - (ξ : ℤ_[2]) = 0 := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    have hdvd : (2 : ℤ_[2]) ^ n ∣ f c - (ξ : ℤ_[2]) :=
      dvd_trans (pow_dvd_pow (2 : ℤ_[2]) (by omega)) (hc n)
    rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hdvd
  exact sub_eq_zero.mp hzero

/-- **No unit of exact level two is a square**: `y² − 1 = 4·t(t+1)` with `t(t+1)` always even,
so a square unit satisfies `v₂(· − 1) ≥ 3` — the classical "odd squares are `1 mod 8`". -/
theorem not_sq_eq_of_exact_level (ξ b : ℤ_[2]ˣ)
    (hξ : ((ξ : ℤ_[2])) - 1 = 4 * (b : ℤ_[2])) (y : ℤ_[2]ˣ) : y ^ 2 ≠ ξ := by
  intro hsq
  obtain ⟨t, ht⟩ := two_dvd_val_sub_one y
  have hval : ((y : ℤ_[2])) ^ 2 = (ξ : ℤ_[2]) := by
    rw [← Units.val_pow_eq_pow_val, hsq]
  have hb : (b : ℤ_[2]) = t * (t + 1) :=
    mul_left_cancel₀ (by norm_num : (4 : ℤ_[2]) ≠ 0) (by
      rw [← hξ, ← hval]
      linear_combination ((y : ℤ_[2]) + 1 + 2 * t) * ht)
  have hpar : (2 : ℤ_[2]) ∣ t * (t + 1) := by
    by_cases htdvd : (2 : ℤ_[2]) ∣ t
    · exact htdvd.mul_right _
    · refine Dvd.dvd.mul_left ?_ t
      obtain ⟨s, hs⟩ := two_dvd_sub_one_of_isUnit (isUnit_of_not_two_dvd htdvd)
      exact ⟨s + 1, by linear_combination hs⟩
  exact not_isUnit_two (isUnit_of_dvd_unit (hb ▸ hpar) b.isUnit)

/-- **The exponent is a unit** whenever the *target* also has exact level two: an even exponent
would make `ξ` the square of a 2-adic unit, which `not_sq_eq_of_exact_level` forbids. -/
theorem isUnit_exponent_of_zpowZtwo_eq (η ξ b : ℤ_[2]ˣ)
    (hξ : ((ξ : ℤ_[2])) - 1 = 4 * (b : ℤ_[2])) {c : ℤ_[2]}
    (hc : zpowZtwo isProP_two_unitsPadicInt η c = ξ) : IsUnit c := by
  by_contra hcu
  obtain ⟨d, rfl⟩ : (2 : ℤ_[2]) ∣ c := by
    by_contra hdvd
    exact hcu (isUnit_of_not_two_dvd hdvd)
  refine not_sq_eq_of_exact_level ξ b hξ (zpowZtwo isProP_two_unitsPadicInt η d) ?_
  have hcomp := zpowZtwo_zpowZtwo isProP_two_unitsPadicInt η d 2
  have h2 : zpowZtwo isProP_two_unitsPadicInt (zpowZtwo isProP_two_unitsPadicInt η d)
      (2 : ℤ_[2]) = (zpowZtwo isProP_two_unitsPadicInt η d) ^ 2 := by
    have h := zpowZtwo_intCast isProP_two_unitsPadicInt
      (zpowZtwo isProP_two_unitsPadicInt η d) 2
    norm_num at h
    exact h
  rw [h2, mul_comm] at hcomp
  exact hcomp.trans hc

/-- **The pivot lemma, general form**: two `2`-adic units of exact level two are *unit* powers
of each other.  (`1 + 4ℤ₂ ≅ ℤ₂` as a topological group, with any exact-level-two element a
topological generator; this is the surjectivity companion of
`zpowZtwo_injective_of_exact_level`.) -/
theorem exists_isUnit_zpowZtwo_eq (η ξ a b : ℤ_[2]ˣ)
    (hη : ((η : ℤ_[2])) - 1 = 4 * (a : ℤ_[2])) (hξ : ((ξ : ℤ_[2])) - 1 = 4 * (b : ℤ_[2])) :
    ∃ c : ℤ_[2], IsUnit c ∧ zpowZtwo isProP_two_unitsPadicInt η c = ξ := by
  obtain ⟨c, hcv⟩ := exists_zpowZtwo_eq_of_exact_level η a hη (ξ := ξ)
    ⟨(b : ℤ_[2]), by rw [hξ]; ring⟩
  exact ⟨c, isUnit_exponent_of_zpowZtwo_eq η ξ b hξ hcv, hcv⟩

end ProcyclicLevelTwo

namespace Dyadic

namespace SqCore

open Roe

/-! ## §2 The `L_sq` instance: `S = X^c` at a unit exponent

The two Hensel orientation values of the `L_sq` core both have exact level two
(`rootX_sub_one_eq`, `Sval_sub_one_eq`), which is precisely the hypothesis §1 needs on *both*
sides.  This is the datum MC5's `SqMixPivot` records. -/

/-- `X = rootXUnit` has exact level two: `X − 1 = 4·(unit)`, in `ℤ₂ˣ` coordinates. -/
theorem rootXUnit_sub_one_eq : ∃ a : ℤ_[2]ˣ, ((rootXUnit : ℤ_[2])) - 1 = 4 * (a : ℤ_[2]) := by
  obtain ⟨a, ha⟩ := rootX_sub_one_eq
  exact ⟨a, by rw [val_rootXUnit]; exact ha⟩

/-- `S = SvalUnit` has exact level two: `S − 1 = 4·(unit)`. -/
theorem SvalUnit_sub_one_eq : ∃ b : ℤ_[2]ˣ, ((SvalUnit : ℤ_[2])) - 1 = 4 * (b : ℤ_[2]) := by
  obtain ⟨b, hb⟩ := Sval_sub_one_eq
  exact ⟨b, by rw [val_SvalUnit]; exact hb⟩

/-- **The `SqMixPivot` exponent datum, PROVED** (the SQ4 supply obligation of MC5's §6): there
is a 2-adic **unit** `c` with `X^c = S`.

Both `X` and `S` lie in the procyclic group `1 + 4ℤ₂` at exact level two, so each is a unit
power of the other (§1).  MC5's congruence pin `sval_congr_rootX_cubed` (`S ≡ X³ (16)`) locates
the answer modulo `4`; no closed form exists, and none is claimed. -/
theorem exists_isUnit_zpowZtwo_rootXUnit_eq_SvalUnit :
    ∃ c : ℤ_[2], IsUnit c ∧
      zpowZtwo isProP_two_unitsPadicInt rootXUnit c = SvalUnit := by
  obtain ⟨a, ha⟩ := rootXUnit_sub_one_eq
  obtain ⟨b, hb⟩ := SvalUnit_sub_one_eq
  exact exists_isUnit_zpowZtwo_eq rootXUnit SvalUnit a b ha hb

/-! ## §3 Stress pins

The lane idiom (`SqCore/Rank3.lean` §5): the consumed inputs restated in raw form, so that an
upstream rename or restatement fails here rather than silently changing what the pivot datum
means.  Prints are recorded in the module docstring rather than by committed `#print axioms`. -/

section StressTests

/-- Stress: the general lemma applies to the pair `(X, S)` — the exact hypothesis shape. -/
example : ∃ c : ℤ_[2], IsUnit c ∧ zpowZtwo isProP_two_unitsPadicInt rootXUnit c = SvalUnit :=
  exists_isUnit_zpowZtwo_rootXUnit_eq_SvalUnit

/-- Stress: `X` is its own unit power at exponent `1` — the trivial instance of §1, pinning the
exponent normalization (`zpowZtwo _ x 1 = x`, not `x^0`). -/
example : zpowZtwo isProP_two_unitsPadicInt rootXUnit 1 = rootXUnit :=
  zpowZtwo_one_exp isProP_two_unitsPadicInt rootXUnit

/-- Stress: the exact-level hypothesis is the frozen `OrientationRoot` datum, not a restatement
— `v₂(X − 1) = v₂(S − 1) = 2`. -/
example : (∃ a : ℤ_[2]ˣ, rootX - 1 = 4 * (a : ℤ_[2])) ∧ ∃ b : ℤ_[2]ˣ, Sval - 1 = 4 * (b : ℤ_[2]) :=
  ⟨rootX_sub_one_eq, Sval_sub_one_eq⟩

/-- Stress: the companion injectivity half is the frozen `ZtwoPowering` theorem, so the
exponent produced above is in fact **unique** — recorded, not consumed. -/
example (a : ℤ_[2]ˣ) (ha : ((rootXUnit : ℤ_[2])) - 1 = 4 * (a : ℤ_[2])) :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt rootXUnit) :=
  zpowZtwo_injective_of_exact_level rootXUnit a ha

end StressTests

end SqCore

end Dyadic

end GQ2
