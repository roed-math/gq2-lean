/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenParityModel
import GQ2.Dyadic.CyclotomicKummerBridgeModEight

/-!
# W67-HRANGE: the per-field range identity at the model fields

## What this file is for

Wave 66 closed the even classification at every even-degree ramified-`i` field
(`EvenParityModel.lean` §3), leaving exactly one thing open at a *named* field: which of the two
committed images the cyclotomic range actually is, and at which depth.  Every branch-pinned
endpoint in the tree therefore carries an undischarged

`hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN/M α`

hypothesis.  This file removes as much of that hypothesis as the tree's field data supports.

## The shape of the answer

The abstract classification (`evenRange_classify`, wave 52) already says the range is *some*
`imChiM α` or `imChiN α` with `α ≥ 2`, from three committed inputs: closedness, depth, and the
mod-4 escape supplied by ramified `K(i)`.  What it does not say is *which*.  The observation this
file is built on is that the depth `α` is **not** an extra measurement: it is forced by the
degree.  Writing `[K : ℚ₂] = 2^e · m` with `m` odd, the committed deep supply gives
`1 + 2^{2+e} ℤ₂ ≤ range χ`, and §2 computes exactly when a principal-unit level sits inside each
committed image:

`1 + 2^n ℤ₂ ≤ imChiN α ↔ α + 1 ≤ n`,      `1 + 2^n ℤ₂ ≤ imChiM α ↔ α ≤ n`   (`α, n ≥ 2`).

So the degree bounds `α` from above, and the classification bounds it from below by `2`.  At a
quadratic field the two bounds *meet on the `N` branch*: `α ≤ 2` and `α ≥ 2`.  Hence

**at a quadratic field, `−1 ∉ range χ` alone proves `range χ = imChiN 2`** (§3).

That is the whole of `hrange` at `ℚ₂(√−2)` from a single membership fact, with no depth
measurement at all.  On the `M` branch and at the quartic the degree bound is one step loose, so
one further elementary fact is needed, and §3 names it: the unit `5` (respectively `9`) is not a
cyclotomic value.

## Where the branch fact comes from

The remaining input is genuinely arithmetic, and §4 to §6 supply it.  `chiCycKTwo` unfolds to
Mathlib's `cyclotomicCharacter`, so `g ζ = ζ^{χ(g)}` is available as a theorem
(`cyclotomicCharacter.spec`).  Building a primitive eighth root `ζ` and the two quadratic periods
`α = ζ + ζ⁻¹` (`α² = 2`) and `β = ζ − ζ⁻¹` (`β² = −2`), a Galois element with `χ ≡ 7 (mod 8)`
negates `β` and one with `χ ≡ 5 (mod 8)` negates `α`.  A Galois element over `K` fixes every
element of `K`, and `β ∈ ℚ₂(√−2)`, `α ∈ ℚ₂(√2)` because in each case the period and the field's
chosen square root have the same square.  So `−1` is not a cyclotomic value at `ℚ₂(√−2)` and `5`
is not one at `ℚ₂(√2)`, which is exactly what §3 asks for.  `ζ` and `α` are the same ones the
committed mod-eight Kummer bridge already builds; `β` is new here.

This is the first computation of a cyclotomic range at a named even-degree field in the campaign.
Three committed docstrings asserted the opposite as of wave 66, in the words "no statement in the
tree computes the cyclotomic range at a named field": `EvenRouteModel.lean` §4,
`EvenRouteFinal.lean` §1, `EvenParityModel.lean` §4.  Those three sentences were false from this
file onward, and they are gone: this lane, being new-files-only, did not edit them, and they were
superseded at the wave-67 merge instead.

## What lands and what is left

* `ℚ₂(√−2)`: **unconditional** (§7).  `hrange` is a theorem and the `N` endpoint at depth `2`,
  handle count `0` carries only the reciprocity bundle and the standing instance binders.
* `ℚ₂(√2)`: `hrange` at `imChiM 3` needs two facts; `5 ∉ range χ` is proved here and
  `−1 ∈ range χ` is proved from a reciprocity bundle **at `ℚ₂` itself**, which is the one extra
  datum the `M` branch costs (§8).  A cyclotomic value must be produced, not excluded, and the
  tree's only source of produced values is reciprocity at an odd-degree field.
* `KQuarticN`: **blocked**, and one step earlier than `hrange`.  The tree carries no ramification
  fact for it (there is no `not_hasEqualNormValueGroups_KQuarticN`; its ledger in
  `EvenRouteModel.lean` records `K(i)/K` ramified as *measured*), so §9 states its identity over
  that binder, over the `N`-branch entry condition `−1 ∉ range χ` which nothing here supplies at
  this field, and over the second residue `9 ∉ range χ` which needs a sixteenth root of unity this
  file does not build: three costs, not two.  What does land there is `5 ∉ range χ`, the
  field-to-image direction of the census's criterion `α ≥ 3 ⟺ √2 ∈ K`.  (Superseded at wave 68:
  `EvenRangePolish.lean` discharges all three, so `hrangeFinal_quartic'` and its endpoint carry
  only the field's own reciprocity bundle.  The sixteenth root is built there *from* `β`, which
  is why no root identification was needed after all.)
* The stratum `evenRange_range_eq` excludes turns out to be a third answer rather than a gap
  (§10): when `K(i)/K` is not ramified the range is a principal-unit group `1 + 2^α ℤ₂`, and with
  that case named the range identity holds with **no ramification binder at all**.

## Numbering

1. two-adic level arithmetic;
2. the principal-unit level of each committed image;
3. the degree-indexed deep supply, and the depth-pinned range identities;
4. the eighth root of unity and the two quadratic periods;
5. the Galois action on the periods, and the branch facts;
6. the periods at the model fields;
7. `ℚ₂(√−2)`, unconditional;
8. `ℚ₂(√2)`, over one further reciprocity bundle;
9. the quartic, and what blocks it;
10. the stratum the range identity excludes, and the ramification binder removed;
11. axiom pins.
-/

namespace GQ2.Dyadic.EvenRangeModel

open GQ2 GQ2.Roe.Labute GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenCyclotomicRange

/-! ## §1 Two-adic level arithmetic

One lemma, used twice in §2: divisibility between powers of `2` in `ℤ₂` is the order relation on
the exponents.  `ℤ₂` is a domain in which `2` is not a unit, and that is the whole proof. -/

section Levels

/-- Powers of `2` in `ℤ₂` divide each other exactly according to their exponents. -/
theorem evenRangeF_two_pow_dvd {a b : ℕ} (h : (2 : ℤ_[2]) ^ a ∣ (2 : ℤ_[2]) ^ b) : a ≤ b := by
  by_contra hlt
  obtain ⟨c, hc⟩ := h
  have hne : (2 : ℤ_[2]) ^ b ≠ 0 := pow_ne_zero _ two_ne_zero
  have hsplit : (2 : ℤ_[2]) ^ a = 2 ^ b * 2 ^ (a - b) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, mul_assoc] at hc
  have hone : (1 : ℤ_[2]) = 2 ^ (a - b) * c :=
    mul_left_cancel₀ hne (by rw [mul_one]; exact hc)
  have h2 : (2 : ℤ_[2]) ∣ 1 := by
    rw [hone]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : a - b ≠ 0)) c
  exact not_isUnit_two (isUnit_of_dvd_one h2)

/-- The `N` generator is `≡ −1` modulo `2^α`, straight from its defining relation
`nUnit α · (1 + 2^α) = −1`. -/
theorem evenRangeF_two_pow_dvd_nUnit_add_one {α : ℕ} (hα : 1 ≤ α) :
    (2 : ℤ_[2]) ^ α ∣ ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 1 :=
  ⟨-(((nUnit α : ℤ_[2]ˣ)) : ℤ_[2]), by linear_combination nUnit_mul hα⟩

/-- The unit `1 + 2^n`, the test element of §2. -/
noncomputable def evenRangeF_onePlus (n : ℕ) : ℤ_[2]ˣ :=
  (isUnit_one_add_two_mul ((2 : ℤ_[2]) ^ (n - 1))).unit

/-- The value of the test element at `n ≥ 1`. -/
theorem evenRangeF_onePlus_val {n : ℕ} (hn : 1 ≤ n) :
    ((evenRangeF_onePlus n : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 ^ n := by
  rw [evenRangeF_onePlus, IsUnit.unit_spec]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-- The test element lies at level `n`. -/
theorem evenRangeF_onePlus_mem {n : ℕ} (hn : 1 ≤ n) :
    evenRangeF_onePlus n ∈ evenRangePrin n :=
  evenRange_mem_prin_iff.mpr ⟨1, by rw [evenRangeF_onePlus_val hn]; ring⟩

end Levels

/-! ## §2 The principal-unit level of each committed image

`imChiM α` is the units `≡ ±1 (mod 2^α)`, so it contains `1 + 2^n ℤ₂` exactly when `α ≤ n`.
`imChiN α` is generated by an element `≡ −1 (mod 2^α)` of exact level `α + 1` on squaring, so it
contains `1 + 2^n ℤ₂` exactly when `α + 1 ≤ n`.  In both directions the `≥` half is the committed
inclusion and the `≤` half is the test element `1 + 2^n` of §1: it cannot be `≡ −1` modulo `4`
alongside a generator that is, which is what kills the second alternative in each normal form. -/

section ImageLevels

/-- **The level of the `N` image.**  `1 + 2^n ℤ₂ ≤ imChiN α` exactly when `n ≥ α + 1`. -/
theorem evenRangeF_prin_le_imChiN_iff {α n : ℕ} (hα : 2 ≤ α) (hn : 2 ≤ n) :
    evenRangePrin n ≤ imChiN α ↔ α + 1 ≤ n := by
  refine ⟨fun h => ?_, fun h =>
    (evenRange_prin_antitone h).trans (evenRange_prin_le_imChiN hα)⟩
  have hmem : evenRangeF_onePlus n ∈ imChiN α := h (evenRangeF_onePlus_mem (by omega))
  have hval := evenRangeF_onePlus_val (n := n) (by omega)
  rcases evenRange_mem_imChiN_dvd hα hmem with hd | hd
  · rw [hval] at hd
    exact evenRangeF_two_pow_dvd (a := α + 1) (b := n) (by simpa using hd)
  · exfalso
    rw [hval] at hd
    have hd4 : (2 : ℤ_[2]) ^ 2 ∣ 1 + 2 ^ n - ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) :=
      (pow_dvd_pow _ (by omega : 2 ≤ α + 1)).trans hd
    have hn4 : (2 : ℤ_[2]) ^ 2 ∣ ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 1 :=
      (pow_dvd_pow _ (by omega : 2 ≤ α)).trans
        (evenRangeF_two_pow_dvd_nUnit_add_one (by omega))
    have hsum : (2 : ℤ_[2]) ^ 2 ∣ 2 + 2 ^ n := by
      obtain ⟨p, hp⟩ := hd4
      obtain ⟨q, hq⟩ := hn4
      exact ⟨p + q, by linear_combination hp + hq⟩
    have htwo : (2 : ℤ_[2]) ^ 2 ∣ (2 : ℤ_[2]) ^ 1 := by
      obtain ⟨p, hp⟩ := hsum
      exact ⟨p - 2 ^ (n - 2), by
        have : (2 : ℤ_[2]) ^ n = 2 ^ 2 * 2 ^ (n - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [pow_one]
        linear_combination hp - this⟩
    exact absurd (evenRangeF_two_pow_dvd htwo) (by omega)

/-- **The level of the `M` image.**  `1 + 2^n ℤ₂ ≤ imChiM α` exactly when `n ≥ α`. -/
theorem evenRangeF_prin_le_imChiM_iff {α n : ℕ} (hα : 2 ≤ α) (hn : 2 ≤ n) :
    evenRangePrin n ≤ imChiM α ↔ α ≤ n := by
  refine ⟨fun h => ?_, fun h =>
    (evenRange_prin_antitone h).trans (evenRange_prin_le_imChiM hα)⟩
  have hmem : evenRangeF_onePlus n ∈ imChiM α := h (evenRangeF_onePlus_mem (by omega))
  have hval := evenRangeF_onePlus_val (n := n) (by omega)
  rcases (evenRange_mem_imChiM_iff hα).mp hmem with hd | hd
  · rw [hval] at hd
    exact evenRangeF_two_pow_dvd (a := α) (b := n) (by simpa using hd)
  · exfalso
    rw [hval] at hd
    have hd4 : (2 : ℤ_[2]) ^ 2 ∣ 1 + 2 ^ n + 1 := (pow_dvd_pow _ hα).trans hd
    have htwo : (2 : ℤ_[2]) ^ 2 ∣ (2 : ℤ_[2]) ^ 1 := by
      obtain ⟨p, hp⟩ := hd4
      exact ⟨p - 2 ^ (n - 2), by
        have : (2 : ℤ_[2]) ^ n = 2 ^ 2 * 2 ^ (n - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [pow_one]
        linear_combination hp - this⟩
    exact absurd (evenRangeF_two_pow_dvd htwo) (by omega)

end ImageLevels

/-! ## §3 The degree-indexed deep supply, and the depth pin

`evenRange_prin_le_range` (committed) produces *some* level; what §2 consumes is the level itself,
which the proof computes as `2 + e` for `[K : ℚ₂] = 2^e · m` with `m` odd.  The statement below is
that proof with `e` and `m` named rather than obtained, and it is the only place this file repeats
committed reasoning.  Combining it with §2 bounds the depth from above by the degree; the
classification bounds it from below by `2`; and the three identities below read off the fields
where the two meet. -/

section Supply

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The deep supply at a named degree.**  For `[K : ℚ₂] = 2^e · m` with `m` odd, the cyclotomic
range contains the principal units of level exactly `2 + e`.  This is
`evenRange_prin_le_range` with its existential witness named. -/
theorem evenRangeF_prin_le_range (B : MarkedRecip R K) {e m : ℕ} (hm : Odd m)
    (hd : Module.finrank ℚ_[2] K = 2 ^ e * m) :
    evenRangePrin (2 + e) ≤ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
  intro y hy
  have hlv : (((isUnit_one_add_two_mul (2 : ℤ_[2])).unit : ℤ_[2]ˣ) : ℤ_[2]) - 1
      = 2 ^ 2 * ((1 : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [IsUnit.unit_spec]
    norm_num
  obtain ⟨c, hc⟩ := GQ2.Dyadic.EvenRowSupply.pivot_pow_surjective
    (isUnit_one_add_two_mul (2 : ℤ_[2])).unit 1 2 (le_refl 2) hlv e
    (evenRange_mem_prin_iff.mp hy)
  obtain ⟨x, hx⟩ := GQ2.Dyadic.LSquare.unitsPadicInt_pow_surjective_of_odd hm
    (zpowZtwo isProP_two_unitsPadicInt (isUnit_one_add_two_mul (2 : ℤ_[2])).unit c)
  have hx' : x ^ m
      = zpowZtwo isProP_two_unitsPadicInt (isUnit_one_add_two_mul (2 : ℤ_[2])).unit c := hx
  have hxy : x ^ Module.finrank ℚ_[2] K = y := by
    rw [hd, mul_comm, pow_mul, hx', hc]
  exact hxy ▸ evenRange_pow_finrank_mem_range B x

/-- **The degree bounds the `N` depth from above.**  If the range is `imChiN α` and
`[K : ℚ₂] = 2^e · m` with `m` odd, then `α ≤ 1 + e`. -/
theorem evenRangeF_imChiN_depth_le (B : MarkedRecip R K) {e m alpha : ℕ} (hm : Odd m)
    (hd : Module.finrank ℚ_[2] K = 2 ^ e * m) (halpha : 2 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha) :
    alpha ≤ 1 + e := by
  have h := evenRangeF_prin_le_range B hm hd
  rw [hr] at h
  have := (evenRangeF_prin_le_imChiN_iff halpha (by omega)).mp h
  omega

/-- **The degree bounds the `M` depth from above.**  Same hypotheses, one step looser:
`α ≤ 2 + e`. -/
theorem evenRangeF_imChiM_depth_le (B : MarkedRecip R K) {e m alpha : ℕ} (hm : Odd m)
    (hd : Module.finrank ℚ_[2] K = 2 ^ e * m) (halpha : 2 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    alpha ≤ 2 + e := by
  have h := evenRangeF_prin_le_range B hm hd
  rw [hr] at h
  exact (evenRangeF_prin_le_imChiM_iff halpha (by omega)).mp h

/-- **THE RANGE IDENTITY AT A QUADRATIC FIELD, `N` BRANCH, FROM `−1` ALONE.**  For
`[K : ℚ₂] = 2` with `K(i)/K` ramified, `−1 ∉ range χ` already forces `range χ = imChiN 2`: the
classification puts the depth at `≥ 2` and the degree puts it at `≤ 2`.  No depth measurement
enters. -/
theorem evenRangeF_eq_imChiN_two_of_quadratic (B : MarkedRecip R K)
    (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2 := by
  obtain ⟨alpha, halpha, hr⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  have hle := evenRangeF_imChiN_depth_le B (e := 1) (m := 1) odd_one
    (by rw [hdeg]; norm_num) halpha hr
  obtain rfl : alpha = 2 := by omega
  exact hr

/-- **THE RANGE IDENTITY AT A QUADRATIC FIELD, `M` BRANCH.**  Here the degree bound is one step
loose (`α ≤ 3`), so a second elementary fact is needed to exclude `α = 2`, where `imChiM 2 = ⊤`:
the unit `5 = 1 + 2^2` is not a cyclotomic value. -/
theorem evenRangeF_eq_imChiM_three_of_quadratic (B : MarkedRecip R K)
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hfive : evenRangeF_onePlus 2 ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 3 := by
  obtain ⟨alpha, halpha, hr⟩ := evenRange_range_eq_imChiM B hneg
  have hle := evenRangeF_imChiM_depth_le B (e := 1) (m := 1) odd_one
    (by rw [hdeg]; norm_num) halpha hr
  have hne : alpha ≠ 2 := by
    rintro rfl
    apply hfive
    rw [hr]
    exact evenRange_prin_le_imChiM (le_refl 2) (evenRangeF_onePlus_mem (by omega))
  obtain rfl : alpha = 3 := by omega
  exact hr

/-- **THE RANGE IDENTITY AT A QUARTIC FIELD, `N` BRANCH.**  The degree bound gives `α ≤ 3`, so
one elementary fact excludes `α = 2`: the unit `9 = 1 + 2^3` is not a cyclotomic value. -/
theorem evenRangeF_eq_imChiN_three_of_quartic (B : MarkedRecip R K)
    (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hdeg : Module.finrank ℚ_[2] K = 4)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hnine : evenRangeF_onePlus 3 ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 3 := by
  obtain ⟨alpha, halpha, hr⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  have hle := evenRangeF_imChiN_depth_le B (e := 2) (m := 1) odd_one
    (by rw [hdeg]; norm_num) halpha hr
  have hne : alpha ≠ 2 := by
    rintro rfl
    apply hnine
    rw [hr]
    exact evenRange_prin_le_imChiN (le_refl 2) (evenRangeF_onePlus_mem (by omega))
  obtain rfl : alpha = 3 := by omega
  exact hr

end Supply

/-! ## §4 The eighth root of unity, and the two quadratic periods

The only genuinely arithmetic input a named field can supply is the Galois action on roots of
unity, and Mathlib's `cyclotomicCharacter.spec` is exactly that: `g ζ = ζ^{χ(g)}`.  This section
builds a primitive eighth root `ζ`, the two quadratic periods

`α = ζ + ζ⁻¹`   (`α² = 2`),      `β = ζ − ζ⁻¹`   (`β² = −2`),

and records how a Galois element with a prescribed `χ` modulo `8` moves them.  The pattern of
signs is the whole content:

| `χ(g) mod 8` | `1` | `3` | `5` | `7` |
|---|---|---|---|---|
| `g α` | `α` | `−α` | `−α` | `α` |
| `g β` | `β` | `β` | `−β` | `−β` |

so `α` is fixed exactly on `{1, 7}` and `β` exactly on `{1, 3}`.  Only the three entries this
file consumes are proved: `g β = −β` at `7`, `g α = −α` at `5`, and `g α = α` at `7`.

The construction is the one already used for the mod-eight Kummer bridge
(`GQ2/Dyadic/CyclotomicKummerBridgeModEight.lean`), which builds the same `ζ` and the same `α`;
`β` is new here. -/

section Periods

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- A chosen square root of `−1` in `ℚ̄₂`. -/
noncomputable def evenRangeF_iota : ℚ̄₂ := sqrtCl (-1)

/-- A chosen primitive eighth root of unity: a square root of `i`. -/
noncomputable def evenRangeF_zeta : ℚ̄₂ := sqrtCl evenRangeF_iota

/-- The period `α = ζ + ζ⁻¹`, a square root of `2`. -/
noncomputable def evenRangeF_alpha : ℚ̄₂ := evenRangeF_zeta + evenRangeF_zeta⁻¹

/-- The period `β = ζ − ζ⁻¹`, a square root of `−2`. -/
noncomputable def evenRangeF_beta : ℚ̄₂ := evenRangeF_zeta - evenRangeF_zeta⁻¹

theorem evenRangeF_iota_sq : evenRangeF_iota ^ 2 = -1 := by
  simp [evenRangeF_iota]

theorem evenRangeF_iota_ne_zero : evenRangeF_iota ≠ 0 := by
  intro h
  have hsq := evenRangeF_iota_sq
  rw [h] at hsq
  norm_num at hsq

theorem evenRangeF_zeta_sq : evenRangeF_zeta ^ 2 = evenRangeF_iota := by
  simp [evenRangeF_zeta]

theorem evenRangeF_zeta_ne_zero : evenRangeF_zeta ≠ 0 := by
  intro h
  have := evenRangeF_zeta_sq
  rw [h] at this
  exact evenRangeF_iota_ne_zero (by simpa using this.symm)

theorem evenRangeF_zeta_pow_four : evenRangeF_zeta ^ 4 = -1 := by
  calc evenRangeF_zeta ^ 4 = (evenRangeF_zeta ^ 2) ^ 2 := by ring
    _ = -1 := by rw [evenRangeF_zeta_sq, evenRangeF_iota_sq]

theorem evenRangeF_zeta_pow_eight : evenRangeF_zeta ^ (2 ^ 3) = 1 := by
  change evenRangeF_zeta ^ 8 = 1
  calc evenRangeF_zeta ^ 8 = (evenRangeF_zeta ^ 4) ^ 2 := by ring
    _ = 1 := by rw [evenRangeF_zeta_pow_four]; norm_num

theorem evenRangeF_iota_inv : evenRangeF_iota⁻¹ = -evenRangeF_iota := by
  apply mul_left_cancel₀ evenRangeF_iota_ne_zero
  rw [mul_inv_cancel₀ evenRangeF_iota_ne_zero, mul_neg,
    show evenRangeF_iota * evenRangeF_iota = evenRangeF_iota ^ 2 by ring, evenRangeF_iota_sq]
  ring

theorem evenRangeF_zeta_inv_sq : evenRangeF_zeta⁻¹ ^ 2 = -evenRangeF_iota := by
  rw [inv_pow, evenRangeF_zeta_sq, evenRangeF_iota_inv]

theorem evenRangeF_zeta_mul_inv : evenRangeF_zeta * evenRangeF_zeta⁻¹ = 1 :=
  mul_inv_cancel₀ evenRangeF_zeta_ne_zero

theorem evenRangeF_alpha_sq : evenRangeF_alpha ^ 2 = 2 := by
  rw [evenRangeF_alpha, add_sq, evenRangeF_zeta_sq, evenRangeF_zeta_inv_sq, mul_assoc,
    evenRangeF_zeta_mul_inv]
  ring

theorem evenRangeF_beta_sq : evenRangeF_beta ^ 2 = -2 := by
  rw [evenRangeF_beta, sub_sq, evenRangeF_zeta_sq, evenRangeF_zeta_inv_sq, mul_assoc,
    evenRangeF_zeta_mul_inv]
  ring

theorem evenRangeF_alpha_ne_zero : evenRangeF_alpha ≠ 0 := by
  intro h
  have := evenRangeF_alpha_sq
  rw [h] at this
  norm_num at this

theorem evenRangeF_beta_ne_zero : evenRangeF_beta ≠ 0 := by
  intro h
  have := evenRangeF_beta_sq
  rw [h] at this
  norm_num at this

theorem evenRangeF_zeta_pow_three : evenRangeF_zeta ^ 3 = -evenRangeF_zeta⁻¹ := by
  apply mul_left_cancel₀ evenRangeF_zeta_ne_zero
  rw [mul_neg, mul_inv_cancel₀ evenRangeF_zeta_ne_zero]
  calc evenRangeF_zeta * evenRangeF_zeta ^ 3 = evenRangeF_zeta ^ 4 := by ring
    _ = -1 := evenRangeF_zeta_pow_four

theorem evenRangeF_zeta_pow_five : evenRangeF_zeta ^ 5 = -evenRangeF_zeta := by
  calc evenRangeF_zeta ^ 5 = evenRangeF_zeta ^ 4 * evenRangeF_zeta := by ring
    _ = -evenRangeF_zeta := by rw [evenRangeF_zeta_pow_four]; ring

theorem evenRangeF_zeta_pow_seven : evenRangeF_zeta ^ 7 = evenRangeF_zeta⁻¹ := by
  apply mul_left_cancel₀ evenRangeF_zeta_ne_zero
  rw [mul_inv_cancel₀ evenRangeF_zeta_ne_zero]
  calc evenRangeF_zeta * evenRangeF_zeta ^ 7 = evenRangeF_zeta ^ (2 ^ 3) := by ring
    _ = 1 := evenRangeF_zeta_pow_eight

end Periods

/-! ## §5 The Galois action on the periods, and the branch facts

`cyclotomicCharacter.spec` evaluates a Galois element on `ζ` as `ζ^{χ}`, and an element of `G_K`
fixes every element of `K`.  Putting the two together: if a period lies in `K`, then no Galois
element over `K` can negate it, so no cyclotomic value can have the residue that negates it.  That
single argument produces both branch facts this file needs, at opposite periods. -/

section GaloisAction

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The ambient ring automorphism of `ℚ̄₂` attached to an element of `G_K`. -/
noncomputable def evenRangeF_gr (g : GalK K) : ℚ̄₂ ≃+* ℚ̄₂ :=
  MulSemiringAction.toRingAut (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ℚ̄₂
    (show Field.absoluteGaloisGroup ℚ_[2] from g.1)

/-- The mod-eight residue of the cyclotomic character on `G_K`. -/
noncomputable def evenRangeF_chiEight (g : GalK K) : ZMod 8 :=
  PadicInt.toZModPow 3 (((chiCycK K g : ℤ_[2]ˣ)) : ℤ_[2])

/-- **The defining property of the cyclotomic character**, read at `ζ`: `g ζ = ζ^{χ(g)}`, with the
exponent taken modulo `8` because `ζ^8 = 1`.  This is Mathlib's `cyclotomicCharacter.spec`. -/
theorem evenRangeF_gr_zeta (g : GalK K) :
    evenRangeF_gr g evenRangeF_zeta = evenRangeF_zeta ^ (evenRangeF_chiEight g).val :=
  cyclotomicCharacter.spec 2 (evenRangeF_gr g) evenRangeF_zeta evenRangeF_zeta_pow_eight

/-- An element of `G_K` fixes every element of `K`. -/
theorem evenRangeF_gr_fix (g : GalK K) {x : ℚ̄₂} (hx : x ∈ K) : evenRangeF_gr g x = x :=
  (IntermediateField.mem_fixingSubgroup_iff K
    (show ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂ from g.1)).mp g.2 x hx

/-- **`χ ≡ 7 (mod 8)` negates `β = ζ − ζ⁻¹`.** -/
theorem evenRangeF_gr_beta_of_seven (g : GalK K) (hu : evenRangeF_chiEight g = 7) :
    evenRangeF_gr g evenRangeF_beta = -evenRangeF_beta := by
  have hz := evenRangeF_gr_zeta g
  rw [hu, show (7 : ZMod 8).val = 7 from by decide] at hz
  simp only [evenRangeF_beta, map_sub, map_inv₀, hz, evenRangeF_zeta_pow_seven, inv_inv]
  ring

/-- **`χ ≡ 5 (mod 8)` negates `α = ζ + ζ⁻¹`.** -/
theorem evenRangeF_gr_alpha_of_five (g : GalK K) (hu : evenRangeF_chiEight g = 5) :
    evenRangeF_gr g evenRangeF_alpha = -evenRangeF_alpha := by
  have hz := evenRangeF_gr_zeta g
  rw [hu, show (5 : ZMod 8).val = 5 from by decide] at hz
  simp only [evenRangeF_alpha, map_add, map_inv₀, hz, evenRangeF_zeta_pow_five, inv_neg]
  ring

/-- **`χ ≡ 7 (mod 8)` fixes `α = ζ + ζ⁻¹`.** -/
theorem evenRangeF_gr_alpha_of_seven (g : GalK K) (hu : evenRangeF_chiEight g = 7) :
    evenRangeF_gr g evenRangeF_alpha = evenRangeF_alpha := by
  have hz := evenRangeF_gr_zeta g
  rw [hu, show (7 : ZMod 8).val = 7 from by decide] at hz
  simp only [evenRangeF_alpha, map_add, map_inv₀, hz, evenRangeF_zeta_pow_seven, inv_inv]
  ring

variable [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- Every cyclotomic value on `G_K(2)` is already a value on `G_K`. -/
theorem evenRangeF_exists_chiCycK {v : ℤ_[2]ˣ}
    (hv : v ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    ∃ g : GalK K, chiCycK K g = v := by
  rw [GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_chiCycKAb] at hv
  obtain ⟨a, ha⟩ := hv
  obtain ⟨g, rfl⟩ := surjective_toAbK K a
  exact ⟨g, (chiCycKAb_toAbK K g).symm.trans ha⟩

/-- **The branch fact from a period lying in `K`.**  If a nonzero `x ∈ K` is negated by every
Galois element whose cyclotomic value has residue `r` modulo `8`, then no cyclotomic value has
residue `r`: such an element would have to fix `x` as well, forcing `x = 0`. -/
theorem evenRangeF_notMem_range_of_neg {x : ℚ̄₂} (hx : x ∈ K) (hx0 : x ≠ 0) {r : ZMod 8}
    (hneg : ∀ g : GalK K, evenRangeF_chiEight g = r → evenRangeF_gr g x = -x)
    {v : ℤ_[2]ˣ} (hv : PadicInt.toZModPow 3 ((v : ℤ_[2])) = r) :
    v ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
  intro hmem
  obtain ⟨g, hg⟩ := evenRangeF_exists_chiCycK hmem
  have hr : evenRangeF_chiEight g = r := by
    simp only [evenRangeF_chiEight, hg]
    exact hv
  have h1 := hneg g hr
  rw [evenRangeF_gr_fix g hx] at h1
  have h2 : (2 : ℚ̄₂) * x = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact hx0 h

end GaloisAction

/-! ## §6 The periods at the model fields

`ℚ₂(√−2)` contains `β` and `ℚ₂(√2)` contains `α`, in each case because the field's chosen square
root and the period have the same square and therefore agree up to sign.  §5 then reads off the
residue each field forbids: `7` at `ℚ₂(√−2)`, which is `−1`, and `5` at `ℚ₂(√2)`. -/

section ModelPeriods

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.Fields

/-- Two elements of `ℚ̄₂` with the same square agree up to sign. -/
theorem evenRangeF_eq_or_eq_neg {x y : ℚ̄₂} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rcases mul_eq_zero.mp (show (x - y) * (x + y) = 0 by linear_combination h) with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

/-- `β = ζ − ζ⁻¹` lies in `ℚ₂(√−2)`. -/
theorem evenRangeF_beta_mem_sqrtNegTwo : evenRangeF_beta ∈ KSqrtNegTwo := by
  have hsq : evenRangeF_beta ^ 2 = sqrtIn (-2) ^ 2 := by
    rw [evenRangeF_beta_sq, sqrtIn_sq, map_neg, map_ofNat]
  rcases evenRangeF_eq_or_eq_neg hsq with h | h
  · exact h ▸ sqrtIn_mem_quadField (-2)
  · exact h ▸ neg_mem (sqrtIn_mem_quadField (-2))

/-- `α = ζ + ζ⁻¹` lies in `ℚ₂(√2)`. -/
theorem evenRangeF_alpha_mem_sqrtTwo : evenRangeF_alpha ∈ KSqrtTwo := by
  have hsq : evenRangeF_alpha ^ 2 = sqrtIn 2 ^ 2 := by
    rw [evenRangeF_alpha_sq, sqrtIn_sq, map_ofNat]
  rcases evenRangeF_eq_or_eq_neg hsq with h | h
  · exact h ▸ sqrtIn_mem_quadField 2
  · exact h ▸ neg_mem (sqrtIn_mem_quadField 2)

/-- `−1` reduces to `7` modulo `8`. -/
theorem evenRangeF_neg_one_modEight :
    PadicInt.toZModPow 3 (((-1 : ℤ_[2]ˣ) : ℤ_[2])) = (7 : ZMod 8) := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- `5 = 1 + 2^2` reduces to `5` modulo `8`. -/
theorem evenRangeF_five_modEight :
    PadicInt.toZModPow 3 (((evenRangeF_onePlus 2 : ℤ_[2]ˣ) : ℤ_[2])) = (5 : ZMod 8) := by
  rw [evenRangeF_onePlus_val (by omega)]
  simp only [map_add, map_one, map_pow, map_ofNat]
  decide

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **`−1` IS NOT A CYCLOTOMIC VALUE AT `ℚ₂(√−2)`.**  The branch fact, proved.  A Galois element
over `ℚ₂(√−2)` with `χ = −1` would have residue `7` modulo `8`, hence would negate
`β = ζ − ζ⁻¹`; but `β` spans the same quadratic as `√−2` and so is fixed. -/
theorem evenRangeF_neg_one_notMem_sqrtNegTwo :
    (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom :=
  evenRangeF_notMem_range_of_neg evenRangeF_beta_mem_sqrtNegTwo evenRangeF_beta_ne_zero
    (fun _ hg => evenRangeF_gr_beta_of_seven _ hg) evenRangeF_neg_one_modEight

/-- **`5` IS NOT A CYCLOTOMIC VALUE AT `ℚ₂(√2)`.**  The same argument at the other period: a
Galois element with `χ = 5` negates `α = ζ + ζ⁻¹`, which is `±√2` and so is fixed. -/
theorem evenRangeF_five_notMem_sqrtTwo :
    evenRangeF_onePlus 2 ∉ MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom :=
  evenRangeF_notMem_range_of_neg evenRangeF_alpha_mem_sqrtTwo evenRangeF_alpha_ne_zero
    (fun _ hg => evenRangeF_gr_alpha_of_five _ hg) evenRangeF_five_modEight

end ModelPeriods

/-! ## §7 `ℚ₂(√−2)`: the range identity and the endpoint, unconditional

The headline.  §6 proved the branch fact and §3 showed it is the only one a quadratic `N` field
needs, so the range identity at `ℚ₂(√−2)` is a theorem, and composing it with the wave-66 endpoint
`parityFinal_orientedEquivN_sqrtNegTwo` removes the last hypothesis from the first even field in
the campaign.  What remains on the endpoint is the reciprocity bundle (a datum, parametrized here
rather than instantiated, so `markedRecipAt` is not summoned) and the standing profinite instance
binders. -/

section SqrtNegTwo

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.Fields

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`hrange` AT `ℚ₂(√−2)`, PROVED.**  The cyclotomic image on `G_K(2)` for `K = ℚ₂(√−2)` is
exactly `imChiN 2`, the value the wave-56 census measured.  The branch comes from `β = ζ − ζ⁻¹`
lying in `K` (§6) and the depth from the degree (§3); no measurement is carried. -/
theorem hrangeFinal_sqrtNegTwo (B : MarkedRecip R KSqrtNegTwo) :
    MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom = imChiN 2 :=
  evenRangeF_eq_imChiN_two_of_quadratic B _
    GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq
    (not_hasEqualNormValueGroups_KSqrtNegTwo _
      GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq)
    finrank_KSqrtNegTwo evenRangeF_neg_one_notMem_sqrtNegTwo

/-- **THE FIRST EVEN FIELD CLOSED UNCONDITIONALLY.**  `G_K(2)` for `K = ℚ₂(√−2)` is
oriented-isomorphic to the `N` core at depth `2` and handle count `0`, over the reciprocity bundle
and the standing instance binders alone.  Every previous form of this statement carried `hrange`;
this one does not. -/
theorem hrangeFinal_orientedEquivN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 0) (chiCycKTwo (K := KSqrtNegTwo))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivN_sqrtNegTwo (hrangeFinal_sqrtNegTwo B)

end SqrtNegTwo

/-! ## §8 `ℚ₂(√2)`: the `M` branch

The `M` branch is not symmetric with the `N` branch, and the asymmetry is structural rather than
technical.  `N` asks that a value be **absent**, and absence is what a period lying in `K` proves.
`M` asks that `−1` be **present**, and no exclusion argument produces a value.  The tree's only
source of produced cyclotomic values is reciprocity, and it produces them at odd degree: a bundle
at `ℚ₂` itself makes `χ` surjective there, so some `g` over `ℚ₂` has `χ(g) = −1`; that `g` has
residue `7` modulo `8`, hence fixes `α = ζ + ζ⁻¹ = ±√2`, hence fixes all of `ℚ₂(√2)` and is
therefore a Galois element *over* `ℚ₂(√2)` carrying the value `−1`.  So the `M` endpoint costs one
extra datum, a reciprocity bundle at `ℚ₂`, and nothing else. -/

section SqrtTwo

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.Fields

/-- `evenRangeF_gr` is the underlying field automorphism. -/
theorem evenRangeF_gr_apply {K : IntermediateField ℚ_[2] ℚ̄₂} (g : GalK K) (x : ℚ̄₂) :
    evenRangeF_gr g x = (show ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂ from g.1) x := rfl

/-- **Fixing the square root fixes the quadratic field.**  Every element of `ℚ₂(√a)` is
`x + y√a` (`Fields.exists_repr`), and a `ℚ₂`-algebra automorphism fixes the scalars. -/
theorem evenRangeF_mem_fixingSubgroup_quadField {a : ℚ_[2]} (ha : ¬ IsSquare a)
    (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) (hg : g (sqrtIn a) = sqrtIn a) :
    g ∈ (quadField a).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  obtain ⟨x, y, rfl⟩ := exists_repr ha hz
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hg]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] K] in
/-- Every cyclotomic value on `G_K` is already a value on `G_K(2)`. -/
theorem evenRangeF_mem_range_of_chiCycK {v : ℤ_[2]ˣ} (g : GalK K) (hg : chiCycK K g = v) :
    v ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom :=
  ⟨maxProPMk 2 (GalK K) g, (chiCycKTwo_maxProPMk (K := K) g).trans hg⟩

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`−1` IS A CYCLOTOMIC VALUE AT `ℚ₂(√2)`.**  A reciprocity bundle at `ℚ₂` makes `χ` surjective
on `G_{ℚ₂}(2)` (odd degree `1`), so some `g` over `ℚ₂` has `χ(g) = −1`.  Its residue `7` modulo `8`
fixes `α = ζ + ζ⁻¹`, hence fixes `√2`, hence fixes `ℚ₂(√2)` pointwise; so `g` lies over `ℚ₂(√2)`
and carries `−1` there. -/
theorem evenRangeF_neg_one_mem_sqrtTwo
    (B0 : MarkedRecip R (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom := by
  have htop : MonoidHom.range
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))).toMonoidHom = ⊤ :=
    GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_top_of_odd_finrank _ B0
      (by rw [IntermediateField.finrank_bot]; exact odd_one)
  obtain ⟨g0, hg0⟩ := evenRangeF_exists_chiCycK
    (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) (v := (-1 : ℤ_[2]ˣ)) (by rw [htop]; trivial)
  have hres : evenRangeF_chiEight g0 = 7 := by
    simp only [evenRangeF_chiEight, hg0]
    exact evenRangeF_neg_one_modEight
  have hfix := evenRangeF_gr_alpha_of_seven g0 hres
  have hsq : evenRangeF_alpha ^ 2 = sqrtIn 2 ^ 2 := by
    rw [evenRangeF_alpha_sq, sqrtIn_sq, map_ofNat]
  have hg2 : evenRangeF_gr g0 (sqrtIn 2) = sqrtIn 2 := by
    rcases evenRangeF_eq_or_eq_neg hsq with h | h
    · rw [← h]
      exact hfix
    · have h2 : sqrtIn 2 = -evenRangeF_alpha := by rw [h]; ring
      rw [h2, map_neg, hfix]
  exact evenRangeF_mem_range_of_chiCycK (K := KSqrtTwo)
    ⟨g0.1, evenRangeF_mem_fixingSubgroup_quadField not_isSquare_two _ hg2⟩ hg0

/-- **`hrange` AT `ℚ₂(√2)`, PROVED over a reciprocity bundle at `ℚ₂`.**  The cyclotomic image on
`G_K(2)` for `K = ℚ₂(√2)` is exactly `imChiM 3`, the value the wave-56 census measured. -/
theorem hrangeFinal_sqrtTwo (B : MarkedRecip R KSqrtTwo)
    (B0 : MarkedRecip R (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3 :=
  evenRangeF_eq_imChiM_three_of_quadratic B finrank_KSqrtTwo
    (evenRangeF_neg_one_mem_sqrtTwo B0) evenRangeF_five_notMem_sqrtTwo

/-- **THE SECOND EVEN FIELD CLOSED.**  `G_K(2)` for `K = ℚ₂(√2)` is oriented-isomorphic to the `M`
core at depth `3` and handle count `0`, over the two reciprocity bundles and the standing instance
binders alone. -/
theorem hrangeFinal_orientedEquivM_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo)
    (B0 : MarkedRecip R (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    Nonempty (OrientedContinuousMulEquiv (chiM 3 0) (chiCycKTwo (K := KSqrtTwo))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_sqrtTwo (hrangeFinal_sqrtTwo B B0)

end SqrtTwo

/-! ## §9 The quartic model field

Three things are missing at `KQuarticN`, and two of them are about the range.

*The ramification binder.*  `not_hasEqualNormValueGroups_KQuarticN` does not exist; the quadratic
row gets its ramification from `Fields.not_hasEqualNormValueGroups_quadField`, which is a
`quadField` lemma and does not apply to a field built from a different generator.  The quartic's
own ledger (`EvenRouteModel.lean` §5) records `K(i)/K` ramified as *measured*, not proved.  So the
`N` classification cannot even be started there without that binder.

*The `−1` exclusion.*  What puts a field on the `N` branch at all is `−1 ∉ range χ`, which is the
hypothesis `evenRange_range_eq_imChiN` reads.  At `ℚ₂(√−2)` §6 discharges it outright
(`evenRangeF_neg_one_notMem_sqrtNegTwo`: the period `β = ζ − ζ⁻¹` lies in that field, and a
residue-`7` element negates it).  The tree holds no counterpart at `KQuarticN` and this file does
not build one, so it stays a binder there.

*The second residue.*  On the `N` branch at degree `4` the degree bound gives `α ≤ 3`, and
excluding `α = 2` needs `9 ∉ range χ`, a mod-`16` fact: `imChiN 2` and `imChiN 3` first differ at
level `16`.  The period that separates them is `ζ₁₆ − ζ₁₆⁻¹`, and this file builds only an eighth
root.  (It is exactly the generator `β` of the model, up to which of the four roots
`Classical.choose` picked, so the work is an identification of that choice, not new arithmetic.)

What the eighth root does give at the quartic is the census's structural criterion `α ≥ 3 ⟺ √2 ∈ K`
in its field-to-image direction: `√2 ∈ KQuarticN` is committed
(`evenRouteModel_sqrtTwo_mem`), so `5` is not a cyclotomic value there. -/

section Quartic

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.EvenRouteModel

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `α = ζ + ζ⁻¹` lies in the quartic model field, because `√2` does. -/
theorem evenRangeF_alpha_mem_quartic : evenRangeF_alpha ∈ KQuarticN := by
  obtain ⟨s, hs, hs2⟩ := evenRouteModel_sqrtTwo_mem
  rcases evenRangeF_eq_or_eq_neg (show evenRangeF_alpha ^ 2 = s ^ 2 by
    rw [evenRangeF_alpha_sq, hs2]) with h | h
  · exact h ▸ hs
  · exact h ▸ neg_mem hs

/-- **`5` IS NOT A CYCLOTOMIC VALUE AT THE QUARTIC.**  The field side of the wave-56 criterion
`α ≥ 3 ⟺ √2 ∈ K`, at the field the census singled out. -/
theorem evenRangeF_five_notMem_quartic :
    evenRangeF_onePlus 2 ∉ MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom :=
  evenRangeF_notMem_range_of_neg evenRangeF_alpha_mem_quartic evenRangeF_alpha_ne_zero
    (fun _ hg => evenRangeF_gr_alpha_of_five _ hg) evenRangeF_five_modEight

/-- **`hrange` AT THE QUARTIC**, over the ramification binder the tree does not carry for this
field, the `−1` exclusion that places it on the `N` branch, and the mod-`16` residue this file
does not reach.  Stated so the three costs are visible and separated; none is a supply `Prop`,
all three are elementary statements about `KQuarticN`.  (Wave 68 discharged all three in
`EvenRangePolish.lean`; `hrangeFinal_quartic'` there is this statement with the three
hypotheses gone.) -/
theorem hrangeFinal_quartic (B : MarkedRecip R KQuarticN)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups KQuarticN deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom)
    (hnine : evenRangeF_onePlus 3 ∉
      MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom) :
    MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom = imChiN 3 :=
  evenRangeF_eq_imChiN_three_of_quartic B deltaI hdeltaI hram finrank_KQuarticN hneg hnine

/-- **The quartic endpoint over the same three costs.** -/
theorem hrangeFinal_orientedEquivN_quartic [T2Space (GalK KQuarticN)]
    (B : MarkedRecip R KQuarticN)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups KQuarticN deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom)
    (hnine : evenRangeF_onePlus 3 ∉
      MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom) :
    Nonempty (OrientedContinuousMulEquiv (chiN 3 1) (chiCycKTwo (K := KQuarticN))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivN_quartic
    (hrangeFinal_quartic B deltaI hdeltaI hram hneg hnine)

end Quartic

/-! ## §10 The stratum the range identity excludes

`evenRange_range_eq` carries `hram`, and the reason is visible in its proof: the ramified-`K(i)`
binder is used exactly once, to produce a cyclotomic value that is not `≡ 1 (mod 4)`.  Drop it and
that value may not exist; the classification engine then has nothing to classify.

But the failure is not a gap, it is a third answer.  Every `2`-adic unit is `≡ ±1 (mod 4)`, so if
the range meets no class `3 mod 4` then *every* value is `≡ 1 (mod 4)`, and the depth argument
that `evenRange_mem_prin_depth` already carries collapses the range onto its own least principal
level.  So the honest identity has three strata, not two, and the third is neither `M` nor `N`:

`range χ = imChiM α`,   `range χ = imChiN α`,   or   `range χ = 1 + 2^α ℤ₂`,

the last when `K(i)/K` fails to be ramified.  ⚠ **Corrected at wave 69: that is an
implication, not an `iff`, and the committed theorem proves only the stated direction
(third stratum implies unramified).**  The converse is false: if `K(i)/K` is unramified
quadratic then `i ∉ K`, so `χ mod 4` is the nontrivial character of `Gal(K(i)/K)` and the
range meets the class `3 mod 4`, which the third case excludes.  Witness `K = ℚ₂(√−5)`,
ramified over `ℚ₂` with `K(i) = K(√5)` unramified and `i ∉ K`.  The case split the third
stratum actually records is `i ∈ K` (see `Instances/EvenUnramified.lean` §6, which proves
that direction).  The three are mutually exclusive at `α ≥ 2`
(`−1` lies in the first and not the other two; the class `3 mod 4` meets the first two and not the
third).  This removes `hram` from the range identity outright. -/

section Trichotomy

/-- **The third stratum.**  A closed deep subgroup of `ℤ₂ˣ` all of whose elements are `≡ 1 (mod 4)`
is exactly the principal-unit group at its own least depth. -/
theorem evenRangeF_eq_prin_of_forall_four_dvd (H : Subgroup ℤ_[2]ˣ)
    (hclosed : IsClosed (H : Set ℤ_[2]ˣ)) (hdeep : ∃ N : ℕ, evenRangePrin N ≤ H)
    (h4 : ∀ w ∈ H, (2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) - 1) :
    ∃ beta : ℕ, 2 ≤ beta ∧ H = evenRangePrin beta := by
  obtain ⟨beta, hbeta2, hbetale, hbetamin⟩ := evenRange_exists_depth H hdeep
  exact ⟨beta, hbeta2, le_antisymm
    (fun u hu => evenRange_mem_prin_depth hclosed hbetamin hu (h4 u hu)) hbetale⟩

/-- The third stratum omits `−1`, so it is disjoint from the `M` branch. -/
theorem evenRangeF_neg_one_notMem_prin {beta : ℕ} (hbeta : 2 ≤ beta) :
    (-1 : ℤ_[2]ˣ) ∉ evenRangePrin beta := by
  intro h
  obtain ⟨c, hc⟩ := (pow_dvd_pow (2 : ℤ_[2]) hbeta).trans (evenRange_mem_prin_iff.mp h)
  rw [show (((-1 : ℤ_[2]ˣ)) : ℤ_[2]) - 1 = -2 from by rw [Units.val_neg, Units.val_one]; ring] at hc
  have hd : (2 : ℤ_[2]) ^ 2 ∣ (2 : ℤ_[2]) ^ 1 :=
    ⟨-c, by rw [pow_one]; linear_combination -hc⟩
  exact absurd (evenRangeF_two_pow_dvd hd) (by omega)

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **THE RANGE IDENTITY WITH NO RAMIFICATION BINDER.**  For every finite `K/ℚ₂` carrying a marked
reciprocity bundle, the cyclotomic image on `G_K(2)` is one of exactly three things at an index
`α ≥ 2` determined by `K`: the `M` image, the `N` image, or a principal-unit group.  The third
case is precisely the stratum `evenRange_range_eq` excludes. -/
theorem evenRangeF_range_trichotomy (B : MarkedRecip R K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      (MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha ∨
        MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha ∨
        MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) := by
  by_cases h4 : ∃ w ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom,
      ¬ ((2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) - 1)
  · obtain ⟨alpha, halpha, h⟩ :=
      evenRange_classify _ evenRange_isClosed_range (evenRange_prin_le_range B) h4
    rcases h with h | h
    · exact ⟨alpha, halpha, Or.inl h⟩
    · exact ⟨alpha, halpha, Or.inr (Or.inl h)⟩
  · have h4' : ∀ w ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom,
        (2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) - 1 := by
      intro w hw
      by_contra hcon
      exact h4 ⟨w, hw, hcon⟩
    obtain ⟨beta, hbeta, h⟩ := evenRangeF_eq_prin_of_forall_four_dvd _
      evenRange_isClosed_range (evenRange_prin_le_range B) h4'
    exact ⟨beta, hbeta, Or.inr (Or.inr h)⟩

/-- **The third stratum is exactly the unramified one.**  If the range is a principal-unit group at
depth `≥ 2` then `K(i)/K` is not ramified, for every choice of `i`. -/
theorem evenRangeF_hasEqualNormValueGroups_of_range_eq_prin (B : MarkedRecip R K) {beta : ℕ}
    (hbeta : 2 ≤ beta)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin beta)
    (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1) :
    HasEqualNormValueGroups K deltaI := by
  by_contra hram
  obtain ⟨w, hw, hw4⟩ := evenRange_exists_not_four_dvd B deltaI hdeltaI hram
  rw [hr] at hw
  exact hw4 ((pow_dvd_pow (2 : ℤ_[2]) hbeta).trans (evenRange_mem_prin_iff.mp hw))

end Trichotomy

end GQ2.Dyadic.EvenRangeModel

/-! ## §11 Axiom pins

The two closed endpoints printed side by side with the committed wave-66 endpoints they consume,
with the committed range identity, and with the odd-degree surjectivity the `M` branch borrows.
Nothing here may exceed the committed endpoint set. -/

section AxiomPins

open GQ2.Dyadic.EvenRangeModel

-- §1 to §3 the reduction machinery
#print axioms evenRangeF_two_pow_dvd
#print axioms evenRangeF_prin_le_imChiN_iff
#print axioms evenRangeF_prin_le_imChiM_iff
#print axioms evenRangeF_prin_le_range
#print axioms evenRangeF_imChiN_depth_le
#print axioms evenRangeF_imChiM_depth_le
#print axioms evenRangeF_eq_imChiN_two_of_quadratic
#print axioms evenRangeF_eq_imChiM_three_of_quadratic
#print axioms evenRangeF_eq_imChiN_three_of_quartic

-- §4 to §6 the periods and the branch facts
#print axioms evenRangeF_alpha_sq
#print axioms evenRangeF_beta_sq
#print axioms evenRangeF_gr_zeta
#print axioms evenRangeF_gr_fix
#print axioms evenRangeF_gr_beta_of_seven
#print axioms evenRangeF_gr_alpha_of_five
#print axioms evenRangeF_gr_alpha_of_seven
#print axioms evenRangeF_notMem_range_of_neg
#print axioms evenRangeF_beta_mem_sqrtNegTwo
#print axioms evenRangeF_alpha_mem_sqrtTwo
#print axioms evenRangeF_neg_one_notMem_sqrtNegTwo
#print axioms evenRangeF_five_notMem_sqrtTwo

-- §7 the unconditional field
#print axioms hrangeFinal_sqrtNegTwo
#print axioms hrangeFinal_orientedEquivN_sqrtNegTwo

-- §8 the second field
#print axioms evenRangeF_mem_fixingSubgroup_quadField
#print axioms evenRangeF_neg_one_mem_sqrtTwo
#print axioms hrangeFinal_sqrtTwo
#print axioms hrangeFinal_orientedEquivM_sqrtTwo

-- §9 the quartic
#print axioms evenRangeF_alpha_mem_quartic
#print axioms evenRangeF_five_notMem_quartic
#print axioms hrangeFinal_quartic
#print axioms hrangeFinal_orientedEquivN_quartic

-- §10 the third stratum
#print axioms evenRangeF_eq_prin_of_forall_four_dvd
#print axioms evenRangeF_neg_one_notMem_prin
#print axioms evenRangeF_range_trichotomy
#print axioms evenRangeF_hasEqualNormValueGroups_of_range_eq_prin

-- the committed statements consumed, for the side-by-side
#print axioms GQ2.Dyadic.EvenParity.parityFinal_orientedEquivN_sqrtNegTwo
#print axioms GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_sqrtTwo
#print axioms GQ2.Dyadic.EvenParity.parityFinal_orientedEquivN_quartic
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_classify
#print axioms GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_top_of_odd_finrank

end AxiomPins
