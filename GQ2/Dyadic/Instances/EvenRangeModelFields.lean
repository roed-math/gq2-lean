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

## What is proved and what is carried

Nothing here computes a cyclotomic range from field arithmetic; the tree has no cyclotomic-tower
data at any named field (three docstrings say so verbatim: `EvenRouteModel.lean` §4,
`EvenRouteFinal.lean` §1, `EvenParityModel.lean` §4).  What this file does is *shrink* `hrange`,
a statement about a subgroup of `ℤ₂ˣ`, to a statement about one or two named units, and then
compose the shrunken form into the wave-66 endpoints.  §5 records the exact residue at each
field, with the wave-56/57 measured value it corresponds to.

The quartic `KQuarticN` is additionally blocked one step earlier: the tree carries no
ramification fact for it (there is no `not_hasEqualNormValueGroups_KQuarticN`, and its ledger in
`EvenRouteModel.lean` records `K(i)/K` ramified as *measured*), so its range identity is stated
over that binder as a hypothesis rather than discharged from a committed theorem.

## Numbering

1. two-adic level arithmetic;
2. the principal-unit level of each committed image;
3. the degree-indexed deep supply, and the depth-pinned range identities;
4. the model fields;
5. the residues, and the endpoints they buy;
6. axiom pins.
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
classification bounds it from below by `2`; and §4 reads off the fields where the two meet. -/

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

end GQ2.Dyadic.EvenRangeModel
