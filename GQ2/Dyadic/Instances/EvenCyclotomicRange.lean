/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenRowSupply
import GQ2.Dyadic.Instances.StageAbstractionEvenAssembly
import GQ2.Dyadic.OrientationCorrection

/-!
# The even-degree cyclotomic range identity  (W52-RANGE)

The even forward route assembled in wave 51 funnels through one arithmetic statement: the
image of the cyclotomic character on `G_K(2)` is the committed subgroup `imChiN α` or
`imChiM α` of `ℤ₂ˣ`.  Every even-lane consumer takes that equality as a hypothesis
(`hrange` in `abstractEquiv_KTwoN/M` and `orientedAbstractEquiv_KTwoN/M`, `Hrange` in the
assembly endpoints and the depth supplies).  This file proves it.

## The shape of the answer

`α` is a bare natural number in every consumer: the tree contains no definition of "the
orientation invariant of `K`".  The honest identity is therefore existential in `α`, with the
branch selected by a single computable test:

`range χ = imChiM α` if `-1 ∈ range χ`, and `range χ = imChiN α` if `-1 ∉ range χ`.

The two are never both available: `-1 ∈ imChiM α` always, and `-1 ∉ imChiN α` for `α ≥ 2`.

## The three inputs, and where each comes from

Writing `H = range χ` as a subgroup of `ℤ₂ˣ`, the identity needs exactly:

1. `H` is closed.  `G_K(2)` is compact and `ℤ₂ˣ` is Hausdorff (`evenRange_isClosed_range`).
2. `H` is deep: `1 + 2^N ℤ₂ ≤ H` for some `N`.  This is *not* a gap.  The odd-degree
   surjectivity proof factors as "`χ_K(rec_K(u_K)) = (u^{[K:ℚ₂]})⁻¹`", and only its last
   step uses oddness; the identity itself is degree-free, so every `d`-th power of a
   2-adic unit lies in `H`, and `(ℤ₂ˣ)^d ⊇ 1 + 2^{v₂(d)+2} ℤ₂` (`evenRange_prin_le_range`).
   The reciprocity data enters exactly as it does on the odd route, through the binders
   `R : LocalReciprocity` and `B : MarkedRecip R K`; no census axiom is summoned here.
3. `H` is not contained in `1 + 4ℤ₂`, that is `i ∉ K`.  This is the ramified-`K(i)` binder,
   already committed as `exists_maxProTwo_inertia_chi_modFour_ne_one_of_ramifiedI`.

## The pure 2-adic core

Sections 1 to 4 are unconditional group theory in `ℤ₂ˣ`, and are where the work is.  The
engine is `evenRange_closure_eq_prin`: a unit of exact level `s ≥ 2` topologically generates
the principal units `1 + 2^s ℤ₂`.  Its hard half is a successive-approximation induction
(`evenRange_approx`) followed by a compactness limit in the `ℤ₂`-exponent
(`evenRange_exists_zpow`), so no logarithm and no `Units`-metric is needed.  Section 4 then
classifies: a closed, deep subgroup of `ℤ₂ˣ` meeting the class `3 mod 4` is `imChiM β` for
the least `β` with `1 + 2^β ℤ₂ ≤ H` when `-1 ∈ H`, and `imChiN (β-1)` when `-1 ∉ H`.

## A uniformity warning about the assembly endpoints

`evenAssembly_orientedEquivN/M` take `Hrange` quantified over *all* `K` with one fixed `α`.
That hypothesis is inconsistent, not merely unproved: it applies to odd-degree `K` too,
where the range is `⊤`, and `⊤ = imChiN α` contradicts `neg_one_notMem_imChiN`.  Section 7
records this as `rangeFinal_uniform_Hrange_imChiN_absurd`.  The per-`K` consumers in
`GQ2/Dyadic/OrientationCorrection.lean` have no such defect, and section 7 discharges the
`N` one outright (`rangeFinal_orientedAbstractEquiv_KTwoN`).
-/

namespace GQ2.Dyadic.EvenCyclotomicRange

open GQ2 GQ2.Roe.Labute GQ2.Dyadic.MarkedCore
open scoped Multiplicative

/-! ## §1 The principal-unit filtration of `ℤ₂ˣ`

`evenRangePrin n` is `1 + 2^n ℤ₂`, spelled as the kernel of the reduction of units mod `2^n`
so that the committed lemmas of `GQ2/Roe/Labute/TwoCentralTower.lean` apply verbatim. -/

section Principal

/-- The level-`n` principal units of `ℤ₂ˣ`, that is `1 + 2^n ℤ₂`. -/
noncomputable def evenRangePrin (n : ℕ) : Subgroup ℤ_[2]ˣ :=
  (Units.map (PadicInt.toZModPow (p := 2) n).toMonoidHom).ker

/-- Membership in `evenRangePrin n`, as a divisibility in `ℤ₂`. -/
theorem evenRange_mem_prin_iff {n : ℕ} {u : ℤ_[2]ˣ} :
    u ∈ evenRangePrin n ↔ (2 : ℤ_[2]) ^ n ∣ (u : ℤ_[2]) - 1 := by
  rw [evenRangePrin, mem_ker_units_toZModPow_iff]
  norm_num

/-- The filtration is decreasing: a deeper level is a smaller subgroup. -/
theorem evenRange_prin_antitone {m n : ℕ} (h : m ≤ n) : evenRangePrin n ≤ evenRangePrin m := by
  intro u hu
  rw [evenRange_mem_prin_iff] at hu ⊢
  exact (pow_dvd_pow _ h).trans hu

/-- Each level of the filtration is closed. -/
theorem evenRange_isClosed_prin (n : ℕ) :
    IsClosed ((evenRangePrin n : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
  isClosed_ker_units_toZModPow n

/-- A unit lying in every level of the filtration is `1`. -/
theorem evenRange_eq_one_of_forall_mem_prin {w : ℤ_[2]ˣ} (hw : ∀ n, w ∈ evenRangePrin n) :
    w = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  have h := (evenRange_mem_prin_iff (n := n)).mp (hw n)
  rw [Units.val_one, map_one, ← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := 2) n),
    ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  exact_mod_cast h

/-- A 2-adic integer not divisible by `2` is a unit (the residue field is `𝔽₂`). -/
theorem evenRange_isUnit_of_not_two_dvd {x : ℤ_[2]} (hx : ¬ (2 : ℤ_[2]) ∣ x) : IsUnit x := by
  by_contra h
  have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  exact hx (by exact_mod_cast hmem)

/-- Two 2-adic units differ by an even amount: `2 ∣ a + b` and `2 ∣ a - b`. -/
theorem evenRange_two_dvd_add_of_isUnit {a b : ℤ_[2]} (ha : IsUnit a) (hb : IsUnit b) :
    (2 : ℤ_[2]) ∣ a + b := by
  obtain ⟨c, hc⟩ : (2 : ℤ_[2]) ∣ a - 1 := by
    have := two_dvd_val_sub_one ha.unit
    rwa [IsUnit.unit_spec] at this
  obtain ⟨d, hd⟩ : (2 : ℤ_[2]) ∣ b - 1 := by
    have := two_dvd_val_sub_one hb.unit
    rwa [IsUnit.unit_spec] at this
  exact ⟨c + d + 1, by linear_combination hc + hd⟩

/-- **The mod-4 dichotomy.**  Every 2-adic unit is `≡ 1` or `≡ -1` modulo `4`. -/
theorem evenRange_four_dvd_sub_or_add (u : ℤ_[2]ˣ) :
    (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) - 1 ∨ (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) + 1 := by
  obtain ⟨m, hm⟩ : (2 : ℤ_[2]) ∣ (u : ℤ_[2]) - 1 := by
    have := two_dvd_val_sub_one u
    exact_mod_cast this
  by_cases hm2 : (2 : ℤ_[2]) ∣ m
  · obtain ⟨r, rfl⟩ := hm2
    exact Or.inl ⟨r, by linear_combination hm⟩
  · obtain ⟨r, hr⟩ : (2 : ℤ_[2]) ∣ m + 1 :=
      evenRange_two_dvd_add_of_isUnit (evenRange_isUnit_of_not_two_dvd hm2) isUnit_one
    exact Or.inr ⟨r, by linear_combination hm + 2 * hr⟩

end Principal

/-! ## §2 Exact-level generation

A unit of exact level `s ≥ 2` topologically generates `1 + 2^s ℤ₂`.  Both halves of the
mechanism are committed in `GQ2/Dyadic/Instances/StageAbstractionDeepCorrections.lean`: the
successive-approximation limit `pivot_exists_zpowZtwo_eq` and the density bridge
`mem_topologicalClosure_of_zpowZtwo`.  All this section does is package them as an equality
of subgroups, which is the form sections 3 and 4 consume. -/

section Generation

open GQ2.Dyadic.EvenRowSupply (pivot_exists_zpowZtwo_eq mem_topologicalClosure_of_zpowZtwo)

/-- **Exact-level generation.**  If `η - 1 = 2^s·a` with `a` a unit and `s ≥ 2`, then the
closed subgroup generated by `η` is exactly the level-`s` principal units. -/
theorem evenRange_closure_eq_prin {η a : ℤ_[2]ˣ} {s : ℕ} (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * (a : ℤ_[2])) :
    (Subgroup.closure ({η} : Set ℤ_[2]ˣ)).topologicalClosure = evenRangePrin s := by
  refine le_antisymm ?_ fun ξ hξ => ?_
  · refine Subgroup.topologicalClosure_minimal _ ?_ (evenRange_isClosed_prin s)
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact evenRange_mem_prin_iff.mpr ⟨(a : ℤ_[2]), hη⟩
  · obtain ⟨c, rfl⟩ :=
      pivot_exists_zpowZtwo_eq η a s hs hη (evenRange_mem_prin_iff.mp hξ)
    exact mem_topologicalClosure_of_zpowZtwo η c

/-- A closed subgroup containing a unit of exact level `s ≥ 2` contains all of `1 + 2^s ℤ₂`. -/
theorem evenRange_prin_le_of_mem {H : Subgroup ℤ_[2]ˣ} (hclosed : IsClosed (H : Set ℤ_[2]ˣ))
    {η a : ℤ_[2]ˣ} {s : ℕ} (hs : 2 ≤ s) (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * (a : ℤ_[2]))
    (hmem : η ∈ H) : evenRangePrin s ≤ H := by
  rw [← evenRange_closure_eq_prin hs hη]
  refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
  rw [Subgroup.closure_le, Set.singleton_subset_iff]
  exact hmem

/-- The exact level of a unit `≡ 1 (mod 4)` other than `1`: a level `s ≥ 2` and a unit
coefficient.  This is the only place `PadicInt.unitCoeff` is used. -/
theorem evenRange_exists_exact_level {u : ℤ_[2]ˣ} (hu : u ≠ 1)
    (h4 : (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) - 1) :
    ∃ (s : ℕ) (a : ℤ_[2]ˣ), 2 ≤ s ∧ ((u : ℤ_[2])) - 1 = 2 ^ s * (a : ℤ_[2]) := by
  have hne : ((u : ℤ_[2])) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hu (Units.ext h)
  refine ⟨((u : ℤ_[2]) - 1).valuation, PadicInt.unitCoeff hne, ?_, ?_⟩
  · by_contra hlt
    have hspec : ((u : ℤ_[2])) - 1 =
        ((PadicInt.unitCoeff hne : ℤ_[2]ˣ) : ℤ_[2]) * 2 ^ ((u : ℤ_[2]) - 1).valuation := by
      have := PadicInt.unitCoeff_spec hne
      exact_mod_cast this
    set t := ((u : ℤ_[2]) - 1).valuation with ht
    have hfac : (2 : ℤ_[2]) ^ 2 = 2 ^ t * 2 ^ (2 - t) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hspec, hfac] at h4
    have hcancel : (2 : ℤ_[2]) ^ (2 - t) ∣ ((PadicInt.unitCoeff hne : ℤ_[2]ˣ) : ℤ_[2]) := by
      refine (mul_dvd_mul_iff_left (a := (2 : ℤ_[2]) ^ t) (pow_ne_zero _ two_ne_zero)).mp ?_
      rwa [mul_comm (((PadicInt.unitCoeff hne : ℤ_[2]ˣ)) : ℤ_[2])] at h4
    have h2 : (2 : ℤ_[2]) ∣ ((PadicInt.unitCoeff hne : ℤ_[2]ˣ) : ℤ_[2]) :=
      dvd_trans (dvd_pow_self 2 (by omega : 2 - t ≠ 0)) hcancel
    exact not_isUnit_two (isUnit_of_dvd_one (h2.trans (Units.isUnit _).dvd))
  · have := PadicInt.unitCoeff_spec hne
    rw [mul_comm]
    exact_mod_cast this

end Generation

/-! ## §3 The two committed images in normal form

`imChiM α` is exactly the units `≡ ±1 (mod 2^α)`; the `≤` half is the committed
`evenSharp_pmOne_of_mem_imChiM` and the `≥` half is the committed
`principalUnits_le_imChiM` together with `-1 ∈ imChiM α`.

`imChiN α` is not a principal-unit coset union in the same clean sense, because its generator
is `≡ -1 (mod 2^α)`; what is true, and all that is needed, is the pair of inclusions
`1 + 2^(α+1) ℤ₂ ≤ imChiN α` (from the exact level `α+1` of `nUnit α ^ 2`) and
`imChiN α ≤ {u : u ≡ 1 or nUnit α (mod 2^(α+1))}` (from the committed involution
`nUnit_res_sq` and the closed pair subgroup `modPairSubgroup`). -/

section Images

open GQ2.Dyadic.EvenRowSupply (principalUnits_le_imChiM evenSharp_pmOne_of_mem_imChiM
  evenRow_nUnit_mem_imChiN)

/-- Reduction mod `2^j` detects differences up to `2^j`. -/
theorem evenRange_toZModPow_eq_iff {j : ℕ} {x y : ℤ_[2]} :
    PadicInt.toZModPow j x = PadicInt.toZModPow j y ↔ (2 : ℤ_[2]) ^ j ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]
  norm_num

/-- The `≡ 1` case of `evenRange_toZModPow_eq_iff`. -/
theorem evenRange_toZModPow_eq_one_iff {j : ℕ} {x : ℤ_[2]} :
    PadicInt.toZModPow j x = 1 ↔ (2 : ℤ_[2]) ^ j ∣ x - 1 := by
  rw [← map_one (PadicInt.toZModPow (p := 2) j), evenRange_toZModPow_eq_iff]

/-- `imChiM α` is closed. -/
theorem evenRange_isClosed_imChiM (α : ℕ) :
    IsClosed ((imChiM α : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
  Subgroup.isClosed_topologicalClosure _

/-- `imChiN α` is closed. -/
theorem evenRange_isClosed_imChiN (α : ℕ) :
    IsClosed ((imChiN α : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
  Subgroup.isClosed_topologicalClosure _

/-- The level-`α` principal units sit inside the `M` image. -/
theorem evenRange_prin_le_imChiM {α : ℕ} (hα : 2 ≤ α) : evenRangePrin α ≤ imChiM α :=
  fun _ hξ => principalUnits_le_imChiM hα (evenRange_mem_prin_iff.mp hξ)

/-- **`imChiM α` in normal form**: the units `≡ ±1 (mod 2^α)`. -/
theorem evenRange_mem_imChiM_iff {α : ℕ} (hα : 2 ≤ α) {u : ℤ_[2]ˣ} :
    u ∈ imChiM α ↔
      (2 : ℤ_[2]) ^ α ∣ (u : ℤ_[2]) - 1 ∨ (2 : ℤ_[2]) ^ α ∣ (u : ℤ_[2]) + 1 := by
  refine ⟨fun hu => evenSharp_pmOne_of_mem_imChiM (by omega) hu, ?_⟩
  rintro (h | h)
  · exact evenRange_prin_le_imChiM hα (evenRange_mem_prin_iff.mpr h)
  · have hneg : ((-u : ℤ_[2]ˣ) : ℤ_[2]) - 1 = -((u : ℤ_[2]) + 1) := by push_cast; ring
    have hm : (-u : ℤ_[2]ˣ) ∈ imChiM α :=
      evenRange_prin_le_imChiM hα
        (evenRange_mem_prin_iff.mpr (by rw [hneg]; exact Dvd.dvd.neg_right h))
    simpa using mul_mem (neg_one_mem_imChiM α) hm

/-- The level-`α+1` principal units sit inside the `N` image: `nUnit α ^ 2` has exact
level `α + 1`, and it lies in `imChiN α`. -/
theorem evenRange_prin_le_imChiN {α : ℕ} (hα : 2 ≤ α) : evenRangePrin (α + 1) ≤ imChiN α := by
  obtain ⟨b, hb⟩ := nUnit_sq_sub_one hα
  rw [← evenRange_closure_eq_prin (η := nUnit α ^ 2) (a := b) (by omega) hb]
  refine Subgroup.topologicalClosure_minimal _ ?_ (evenRange_isClosed_imChiN α)
  rw [Subgroup.closure_le, Set.singleton_subset_iff]
  exact pow_mem (evenRow_nUnit_mem_imChiN α) 2

/-- **`imChiN α` in normal form (upper bound)**: every element is `≡ 1` or `≡ nUnit α`
modulo `2^(α+1)`. -/
theorem evenRange_mem_imChiN_dvd {α : ℕ} (hα : 2 ≤ α) {u : ℤ_[2]ˣ} (hu : u ∈ imChiN α) :
    (2 : ℤ_[2]) ^ (α + 1) ∣ (u : ℤ_[2]) - 1 ∨
      (2 : ℤ_[2]) ^ (α + 1) ∣ (u : ℤ_[2]) - (nUnit α : ℤ_[2]) := by
  have hmem : u ∈ GQ2.Dyadic.EvenNLab.modPairSubgroup (α + 1)
      (PadicInt.toZModPow (α + 1) ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]))
      (GQ2.Dyadic.EvenNLab.nUnit_res_sq α hα) := by
    refine Subgroup.topologicalClosure_minimal _ ?_
      (GQ2.Dyadic.EvenNLab.isClosed_modPairSubgroup _ _ _) hu
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact (GQ2.Dyadic.EvenNLab.mem_modPairSubgroup _ (nUnit α)).mpr (Or.inr rfl)
  rcases (GQ2.Dyadic.EvenNLab.mem_modPairSubgroup _ u).mp hmem with h | h
  · exact Or.inl (evenRange_toZModPow_eq_one_iff.mp h)
  · exact Or.inr (evenRange_toZModPow_eq_iff.mp h)

end Images

/-! ## §4 The classification of closed deep subgroups of `ℤ₂ˣ`

Let `H ≤ ℤ₂ˣ` be closed and deep (containing some `1 + 2^N ℤ₂`), and let `β ≥ 2` be least
with `1 + 2^β ℤ₂ ≤ H`.  Then:

* every `u ∈ H` with `u ≡ 1 (mod 4)` already lies in `1 + 2^β ℤ₂`, because otherwise its own
  exact level `s` would satisfy `2 ≤ s < β` and `1 + 2^s ℤ₂ ≤ H` (`evenRange_mem_prin_depth`);
* if `-1 ∈ H` then `H = imChiM β`;
* if `-1 ∉ H` and `H` meets the class `3 mod 4` at some `w`, then `-w` has exact level
  `β - 1 ≥ 2` and `H = imChiN (β-1)`, with `nUnit (β-1)` differing from `w` by an element of
  `1 + 2^β ℤ₂`.

The two conclusions are mutually exclusive, so the branch is decided by `-1 ∈ H` alone. -/

section Classify

open GQ2.Dyadic.EvenRowSupply (evenRow_nUnit_mem_imChiN)

/-- The least depth `β ≥ 2` with `1 + 2^β ℤ₂ ≤ H`. -/
theorem evenRange_exists_depth (H : Subgroup ℤ_[2]ˣ) (hdeep : ∃ N : ℕ, evenRangePrin N ≤ H) :
    ∃ β : ℕ, 2 ≤ β ∧ evenRangePrin β ≤ H ∧
      ∀ s : ℕ, 2 ≤ s → evenRangePrin s ≤ H → β ≤ s := by
  classical
  have hex : ∃ j : ℕ, evenRangePrin (j + 2) ≤ H := by
    obtain ⟨N, hN⟩ := hdeep
    exact ⟨N, le_trans (evenRange_prin_antitone (by omega)) hN⟩
  refine ⟨Nat.find hex + 2, by omega, Nat.find_spec hex, fun s hs hsle => ?_⟩
  by_contra hlt
  refine Nat.find_min hex (m := s - 2) (by omega) ?_
  have heq : s - 2 + 2 = s := by omega
  rw [heq]
  exact hsle

/-- At the least depth `β`, every element of `H` that is `≡ 1 (mod 4)` lies in
`1 + 2^β ℤ₂`. -/
theorem evenRange_mem_prin_depth {H : Subgroup ℤ_[2]ˣ} (hclosed : IsClosed (H : Set ℤ_[2]ˣ))
    {β : ℕ} (hmin : ∀ s : ℕ, 2 ≤ s → evenRangePrin s ≤ H → β ≤ s)
    {u : ℤ_[2]ˣ} (huH : u ∈ H) (hu4 : (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) - 1) :
    u ∈ evenRangePrin β := by
  by_cases hu1 : u = 1
  · rw [hu1]
    exact one_mem _
  obtain ⟨s, a, hs, ha⟩ := evenRange_exists_exact_level hu1 hu4
  exact evenRange_prin_antitone (hmin s hs (evenRange_prin_le_of_mem hclosed hs ha huH))
    (evenRange_mem_prin_iff.mpr ⟨(a : ℤ_[2]), ha⟩)

/-- Negation moves the mod-`2^j` class of a unit from `-1` to `1`. -/
theorem evenRange_neg_dvd_iff {j : ℕ} {u : ℤ_[2]ˣ} :
    (2 : ℤ_[2]) ^ j ∣ ((-u : ℤ_[2]ˣ) : ℤ_[2]) - 1 ↔ (2 : ℤ_[2]) ^ j ∣ (u : ℤ_[2]) + 1 := by
  have hval : ((-u : ℤ_[2]ˣ) : ℤ_[2]) - 1 = -((u : ℤ_[2]) + 1) := by push_cast; ring
  rw [hval, dvd_neg]

/-- **The `M` branch.**  A closed deep subgroup containing `-1` is `imChiM β` at its own
least depth `β ≥ 2`. -/
theorem evenRange_eq_imChiM_of_neg_one_mem (H : Subgroup ℤ_[2]ˣ)
    (hclosed : IsClosed (H : Set ℤ_[2]ˣ)) (hdeep : ∃ N : ℕ, evenRangePrin N ≤ H)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ H) :
    ∃ α : ℕ, 2 ≤ α ∧ H = imChiM α := by
  obtain ⟨β, hβ2, hβle, hβmin⟩ := evenRange_exists_depth H hdeep
  have hnegmem : ∀ u : ℤ_[2]ˣ, u ∈ H → (-u : ℤ_[2]ˣ) ∈ H := by
    intro u hu
    have h1 : (-1 : ℤ_[2]ˣ) * u ∈ H := mul_mem hneg hu
    simpa using h1
  refine ⟨β, hβ2, le_antisymm (fun u huH => ?_) (fun u hu => ?_)⟩
  · rcases evenRange_four_dvd_sub_or_add u with h | h
    · exact (evenRange_mem_imChiM_iff hβ2).mpr
        (Or.inl (evenRange_mem_prin_iff.mp
          (evenRange_mem_prin_depth hclosed hβmin huH h)))
    · refine (evenRange_mem_imChiM_iff hβ2).mpr (Or.inr ?_)
      refine evenRange_neg_dvd_iff.mp (evenRange_mem_prin_iff.mp ?_)
      exact evenRange_mem_prin_depth hclosed hβmin (hnegmem u huH)
        (evenRange_neg_dvd_iff.mpr h)
  · rcases (evenRange_mem_imChiM_iff hβ2).mp hu with h | h
    · exact hβle (evenRange_mem_prin_iff.mpr h)
    · have hm : (-u : ℤ_[2]ˣ) ∈ H :=
        hβle (evenRange_mem_prin_iff.mpr (evenRange_neg_dvd_iff.mpr h))
      simpa using hnegmem _ hm

/-- **The `N` branch.**  A closed deep subgroup that omits `-1` but meets the class
`3 mod 4` is `imChiN (β-1)`, where `β ≥ 3` is its least depth. -/
theorem evenRange_eq_imChiN_of_neg_one_notMem (H : Subgroup ℤ_[2]ˣ)
    (hclosed : IsClosed (H : Set ℤ_[2]ˣ)) (hdeep : ∃ N : ℕ, evenRangePrin N ≤ H)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ H)
    (h4 : ∃ w ∈ H, ¬ ((2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) - 1)) :
    ∃ α : ℕ, 2 ≤ α ∧ H = imChiN α := by
  obtain ⟨β, hβ2, hβle, hβmin⟩ := evenRange_exists_depth H hdeep
  obtain ⟨w, hwH, hw4⟩ := h4
  have hw4' : (2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) + 1 :=
    (evenRange_four_dvd_sub_or_add w).resolve_left hw4
  have hvH : (-w : ℤ_[2]ˣ) ∉ H := by
    intro hvmem
    have h1 : (-w : ℤ_[2]ˣ) * w⁻¹ ∈ H := mul_mem hvmem (inv_mem hwH)
    simpa using hneg (by simpa using h1)
  have hv1 : (-w : ℤ_[2]ˣ) ≠ 1 := fun h => hvH (h ▸ one_mem H)
  obtain ⟨t, a, ht, hta⟩ :=
    evenRange_exists_exact_level hv1 (evenRange_neg_dvd_iff.mpr hw4')
  -- the exact level of `-w` is below `β`, since `-w ∉ H` while `1 + 2^β ℤ₂ ≤ H`
  have htlt : t < β := by
    by_contra hle
    exact hvH (hβle (evenRange_prin_antitone (by omega)
      (evenRange_mem_prin_iff.mpr ⟨(a : ℤ_[2]), hta⟩)))
  -- but `w ^ 2 = (-w) ^ 2 ∈ H` has exact level `t + 1`, so `β ≤ t + 1`
  obtain ⟨b, hb⟩ := mExists_unit_pow_two_pow_sub_one (-w) a t ht hta 1
  rw [pow_one] at hb
  have hsqH : ((-w : ℤ_[2]ˣ) ^ 2) ∈ H := by
    have hsq : ((-w : ℤ_[2]ˣ) ^ 2) = w ^ 2 := by
      refine Units.ext ?_
      push_cast
      ring
    rw [hsq]
    exact pow_mem hwH 2
  have hβt : β ≤ 1 + t :=
    hβmin (1 + t) (by omega) (evenRange_prin_le_of_mem hclosed (by omega) hb hsqH)
  have hβeq : β = t + 1 := by omega
  subst hβeq
  refine ⟨t, ht, ?_⟩
  -- `w` and `nUnit t` differ by an element of `1 + 2^(t+1) ℤ₂`
  have hkey : w * (nUnit t)⁻¹ ∈ evenRangePrin (t + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, t = r + 2 := ⟨t - 2, by omega⟩
    have hii : (((nUnit (r + 2))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((nUnit (r + 2) : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hnu := nUnit_mul (α := r + 2) (by omega)
    have hinv : (((nUnit (r + 2))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = -(1 + 2 ^ (r + 2)) := by
      linear_combination (((nUnit (r + 2))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hnu -
        (1 + (2 : ℤ_[2]) ^ (r + 2)) * hii
    have hwv : ((w : ℤ_[2]ˣ) : ℤ_[2]) = -(((-w : ℤ_[2]ˣ) : ℤ_[2])) := by push_cast; ring
    obtain ⟨e, he⟩ := evenRange_two_dvd_add_of_isUnit (Units.isUnit a) isUnit_one
    refine evenRange_mem_prin_iff.mpr ⟨e + 2 ^ (r + 1) * (a : ℤ_[2]), ?_⟩
    rw [Units.val_mul, hinv, hwv]
    linear_combination (1 + (2 : ℤ_[2]) ^ (r + 2)) * hta + (2 : ℤ_[2]) ^ (r + 2) * he
  have hnuH : nUnit t ∈ H := by
    have h1 : (w * (nUnit t)⁻¹)⁻¹ * w ∈ H := mul_mem (inv_mem (hβle hkey)) hwH
    have h2 : (w * (nUnit t)⁻¹)⁻¹ * w = nUnit t := by group
    rwa [h2] at h1
  refine le_antisymm (fun u huH => ?_) ?_
  · rcases evenRange_four_dvd_sub_or_add u with h | h
    · exact evenRange_prin_le_imChiN ht (evenRange_mem_prin_depth hclosed hβmin huH h)
    · -- `u` and `w` are both `≡ -1 (mod 4)`, so `u * w⁻¹` is `≡ 1 (mod 4)`
      have hq4 : (2 : ℤ_[2]) ^ 2 ∣ ((u * w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
        obtain ⟨p, hp⟩ := h
        obtain ⟨q, hq⟩ := hw4'
        have hwi : (((w⁻¹ : ℤ_[2]ˣ)) : ℤ_[2]) * ((w : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        refine ⟨(p - q) * (((w⁻¹ : ℤ_[2]ˣ)) : ℤ_[2]), ?_⟩
        rw [Units.val_mul]
        linear_combination (((w⁻¹ : ℤ_[2]ˣ)) : ℤ_[2]) * hp -
          (((w⁻¹ : ℤ_[2]ˣ)) : ℤ_[2]) * hq + hwi
      have hqmem : (u * w⁻¹) ∈ evenRangePrin (t + 1) :=
        evenRange_mem_prin_depth hclosed hβmin (mul_mem huH (inv_mem hwH)) hq4
      have hu : u = (u * w⁻¹) * (w * (nUnit t)⁻¹) * nUnit t := by group
      rw [hu]
      exact mul_mem (mul_mem (evenRange_prin_le_imChiN ht hqmem)
        (evenRange_prin_le_imChiN ht hkey)) (evenRow_nUnit_mem_imChiN t)
  · refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact hnuH

/-- **The classification, with the branch selector.**  A closed deep subgroup meeting the
class `3 mod 4` is exactly one of the two committed even images. -/
theorem evenRange_classify (H : Subgroup ℤ_[2]ˣ) (hclosed : IsClosed (H : Set ℤ_[2]ˣ))
    (hdeep : ∃ N : ℕ, evenRangePrin N ≤ H)
    (h4 : ∃ w ∈ H, ¬ ((2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) - 1)) :
    ∃ α : ℕ, 2 ≤ α ∧ (H = imChiM α ∨ H = imChiN α) := by
  by_cases hneg : (-1 : ℤ_[2]ˣ) ∈ H
  · obtain ⟨α, hα, h⟩ := evenRange_eq_imChiM_of_neg_one_mem H hclosed hdeep hneg
    exact ⟨α, hα, Or.inl h⟩
  · obtain ⟨α, hα, h⟩ := evenRange_eq_imChiN_of_neg_one_notMem H hclosed hdeep hneg h4
    exact ⟨α, hα, Or.inr h⟩

end Classify

/-! ## §5 The three arithmetic inputs for `range chiCycKTwo`

Nothing here is new mathematics; each input is a committed statement read in the shape
section 4 wants.  The one worth naming is the deep supply: the odd-degree surjectivity proof
of `GQ2/Dyadic/Instances/GammaLSylowPreimageFieldCore.lean` computes
`χ_K(rec_K(u_K)) = (u^{[K:ℚ₂]})⁻¹` with no parity input at all, and spends oddness only on
inverting `u ↦ u^{[K:ℚ₂]}`.  Keeping the identity and dropping the inversion gives
`(ℤ₂ˣ)^{[K:ℚ₂]} ≤ range χ`, and `(ℤ₂ˣ)^{2^e·m} ⊇ 1 + 2^{e+2} ℤ₂` because odd powers are
surjective on `ℤ₂ˣ` and `2^e`-th roots exist at depth `2 + e`. -/

section Arithmetic

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] K] in
/-- **Input 1.**  The cyclotomic range is closed: it is the continuous image of the compact
group `G_K(2)` in the Hausdorff group `ℤ₂ˣ`. -/
theorem evenRange_isClosed_range :
    IsClosed ((MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom : Subgroup ℤ_[2]ˣ) :
      Set ℤ_[2]ˣ) := by
  rw [MonoidHom.coe_range]
  exact (isCompact_range (chiCycKTwo (K := K)).continuous_toFun).isClosed

/-- **Every `[K:ℚ₂]`-th power of a 2-adic unit is a cyclotomic value.**  This is the
degree-free content of the odd-degree surjectivity proof: norm compatibility of the marked
reciprocity bundle plus the reciprocity clause on units give
`χ_K(rec_K(u_K)) = (u^{[K:ℚ₂]})⁻¹`, and no parity enters. -/
theorem evenRange_pow_finrank_mem_range (B : MarkedRecip R K) (u : ℤ_[2]ˣ) :
    u ^ Module.finrank ℚ_[2] K ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
  rw [GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_chiCycKAb]
  refine ⟨B.recip (GQ2.Dyadic.LSquare.baseChangedPadicUnit K u⁻¹), ?_⟩
  rw [← chiCycAb_inclAbK, B.norm_compat, GQ2.Dyadic.LSquare.normUnitsK_baseChangedPadicUnit,
    R.chiCyc_recip_unit, inv_pow, inv_inv]

/-- **Input 2, the deep supply.**  Writing `[K:ℚ₂] = 2^e · m` with `m` odd, the cyclotomic
range contains all principal units of level `2 + e`.  In particular it is open. -/
theorem evenRange_prin_le_range (B : MarkedRecip R K) :
    ∃ N : ℕ, evenRangePrin N ≤ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
  obtain ⟨e, m, hm, hd⟩ :=
    Nat.exists_eq_two_pow_mul_odd (n := Module.finrank ℚ_[2] K) (Module.finrank_pos).ne'
  refine ⟨2 + e, fun y hy => ?_⟩
  have hηlv : (((isUnit_one_add_two_mul (2 : ℤ_[2])).unit : ℤ_[2]ˣ) : ℤ_[2]) - 1
      = 2 ^ 2 * ((1 : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [IsUnit.unit_spec]
    norm_num
  obtain ⟨c, hc⟩ := GQ2.Dyadic.EvenRowSupply.pivot_pow_surjective
    (isUnit_one_add_two_mul (2 : ℤ_[2])).unit 1 2 (le_refl 2) hηlv e
    (evenRange_mem_prin_iff.mp hy)
  obtain ⟨x, hx⟩ := GQ2.Dyadic.LSquare.unitsPadicInt_pow_surjective_of_odd hm
    (zpowZtwo isProP_two_unitsPadicInt (isUnit_one_add_two_mul (2 : ℤ_[2])).unit c)
  have hx' : x ^ m
      = zpowZtwo isProP_two_unitsPadicInt (isUnit_one_add_two_mul (2 : ℤ_[2])).unit c := hx
  have hxy : x ^ Module.finrank ℚ_[2] K = y := by
    rw [hd, mul_comm, pow_mul, hx', hc]
  exact hxy ▸ evenRange_pow_finrank_mem_range B x

/-- **Input 3, the mod-4 input.**  Ramification of `K(i)/K` supplies a cyclotomic value
`≢ 1 (mod 4)`, that is, the range is not contained in `1 + 4ℤ₂`. -/
theorem evenRange_exists_not_four_dvd (B : MarkedRecip R K)
    (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) :
    ∃ w ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom,
      ¬ ((2 : ℤ_[2]) ^ 2 ∣ (w : ℤ_[2]) - 1) := by
  obtain ⟨q, -, hq⟩ :=
    exists_maxProTwo_inertia_chi_modFour_ne_one_of_ramifiedI B deltaI hdeltaI hram
  exact ⟨chiCycKTwo (K := K) q, ⟨q, rfl⟩, fun h => hq (evenRange_toZModPow_eq_one_iff.mpr h)⟩

end Arithmetic

/-! ## §6 The range identity

The headline.  Note that the degree of `K` plays no role: the identity holds for every finite
`K/ℚ₂` whose `K(i)` is ramified, and at odd degree it lands on the `M` branch at `α = 2`,
where `imChiM 2 = ⊤` recovers the committed surjectivity.  The even-degree binder
`[K:ℚ₂] = 2 + 2h` is therefore not needed and is not imposed. -/

section Identity

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The range identity, `M` branch.**  If `-1` is a cyclotomic value then the range is
`imChiM α` for a unique `α ≥ 2`.  The ramified-`K(i)` binder is not needed here: `-1` is
itself a witness that the range escapes `1 + 4ℤ₂`. -/
theorem evenRange_range_eq_imChiM (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha :=
  evenRange_eq_imChiM_of_neg_one_mem _ evenRange_isClosed_range
    (evenRange_prin_le_range B) hneg

/-- **The range identity, `N` branch.**  If `-1` is not a cyclotomic value, then under the
ramified-`K(i)` binder the range is `imChiN α` for a unique `α ≥ 2`. -/
theorem evenRange_range_eq_imChiN (B : MarkedRecip R K)
    (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha :=
  evenRange_eq_imChiN_of_neg_one_notMem _ evenRange_isClosed_range
    (evenRange_prin_le_range B) hneg (evenRange_exists_not_four_dvd B deltaI hdeltaI hram)

/-- **The range identity.**  For every finite `K/ℚ₂` with `K(i)/K` ramified, the image of the
cyclotomic character on `G_K(2)` is exactly one of the two committed even images, at an index
`α ≥ 2` determined by `K`, with the branch decided by `-1 ∈ range χ`. -/
theorem evenRange_range_eq (B : MarkedRecip R K)
    (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      (MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha ∨
        MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha) :=
  evenRange_classify _ evenRange_isClosed_range (evenRange_prin_le_range B)
    (evenRange_exists_not_four_dvd B deltaI hdeltaI hram)

omit [FiniteDimensional ℚ_[2] K] in
/-- The two branches are mutually exclusive at `α, α' ≥ 2`, so the dichotomy of
`evenRange_range_eq` is sharp. -/
theorem evenRange_not_both {alpha alpha' : ℕ} (halpha' : 2 ≤ alpha')
    (hM : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hN : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha') : False :=
  GQ2.Dyadic.EvenNLab.neg_one_notMem_imChiN halpha' (hN ▸ hM ▸ neg_one_mem_imChiM alpha)

end Identity

/-! ## §7 The three wave-51 mod-8 seams, discharged

`EvenDegreeNModEightImage`, `EvenDegreeMModEightImage` and `EvenDegreeMModEightRowAttained`
are the mod-8 shadows of the range identity, and three docstrings in the wave-51 files assert
that they follow from it without a lemma doing so.  Here they are, from `hrange` alone.  Only
the `M` image statement needs a case split: at `α ≥ 3` the values are `≡ ±1 (mod 8)`, while at
`α = 2` the image is everything and the four listed residues `1, -1, mUnit 2, -mUnit 2` are
`1, 7, 5, 3`, which is every unit class mod 8. -/

section Seams

open GQ2.Dyadic.StageGeneric

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- Divisibility at depth `≥ 3` descends to the mod-8 shadow. -/
theorem evenRange_modEight_of_dvd {j : ℕ} (hj : 3 ≤ j) {x y : ℤ_[2]}
    (h : (2 : ℤ_[2]) ^ j ∣ x - y) :
    PadicInt.toZModPow 3 x = PadicInt.toZModPow 3 y :=
  evenRange_toZModPow_eq_iff.mpr ((pow_dvd_pow _ hj).trans h)

/-- A 2-adic integer `≡ 1 (mod 4)` is `≡ 1` or `≡ 5` mod 8. -/
theorem evenRange_modEight_of_four_dvd_sub {x : ℤ_[2]} (h : (2 : ℤ_[2]) ^ 2 ∣ x - 1) :
    PadicInt.toZModPow 3 x = 1 ∨ PadicInt.toZModPow 3 x = 5 := by
  obtain ⟨k, hk⟩ := h
  have hx : x = 1 + 4 * k := by linear_combination hk
  have hval : PadicInt.toZModPow (p := 2) 3 x = 1 + 4 * PadicInt.toZModPow (p := 2) 3 k := by
    rw [hx]
    simp only [map_add, map_one, map_mul, map_ofNat]
  rw [hval]
  exact (by decide : ∀ c : ZMod (2 ^ 3), (1 : ZMod (2 ^ 3)) + 4 * c = 1 ∨
    (1 : ZMod (2 ^ 3)) + 4 * c = 5) _

/-- A 2-adic integer `≡ -1 (mod 4)` is `≡ -1` or `≡ -5` mod 8. -/
theorem evenRange_modEight_of_four_dvd_add {x : ℤ_[2]} (h : (2 : ℤ_[2]) ^ 2 ∣ x + 1) :
    PadicInt.toZModPow 3 x = -1 ∨ PadicInt.toZModPow 3 x = -5 := by
  obtain ⟨k, hk⟩ := h
  have hx : x = -1 + 4 * k := by linear_combination hk
  have hval : PadicInt.toZModPow (p := 2) 3 x = -1 + 4 * PadicInt.toZModPow (p := 2) 3 k := by
    rw [hx]
    simp only [map_add, map_neg, map_one, map_mul, map_ofNat]
  rw [hval]
  exact (by decide : ∀ c : ZMod (2 ^ 3), (-1 : ZMod (2 ^ 3)) + 4 * c = -1 ∨
    (-1 : ZMod (2 ^ 3)) + 4 * c = -5) _

/-- `mUnit 2 ≡ 5 (mod 8)`, from its defining relation `mUnit 2 · (-3) = 1`. -/
theorem evenRange_mUnit_two_modEight :
    PadicInt.toZModPow 3 ((mUnit 2 : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  have h8 := congrArg (PadicInt.toZModPow (p := 2) 3) (mUnit_mul (α := 2) (by omega))
  rw [map_mul, map_one] at h8
  have hc : PadicInt.toZModPow (p := 2) 3 (1 - 2 ^ 2) = -3 := by
    simp only [map_sub, map_one, map_pow, map_ofNat]
    decide
  rw [hc] at h8
  revert h8
  exact (by decide : ∀ m : ZMod (2 ^ 3), m * (-3) = 1 → m = 5) _

/-- **Seam 1 discharged**: `EvenDegreeNModEightImage` is the mod-8 shadow of the `N` range
identity. -/
theorem evenRange_evenDegreeNModEightImage {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha) :
    EvenDegreeNModEightImage (K := K) alpha := by
  intro g
  have hmem : chiCycKTwo (K := K) g ∈ imChiN alpha := hrange ▸ ⟨g, rfl⟩
  rcases evenRange_mem_imChiN_dvd halpha hmem with h | h
  · exact Or.inl (evenRange_toZModPow_eq_one_iff.mpr ((pow_dvd_pow _ (by omega)).trans h))
  · exact Or.inr (evenRange_modEight_of_dvd (by omega) h)

/-- **Seam 2 discharged**: `EvenDegreeMModEightImage` is the mod-8 shadow of the `M` range
identity. -/
theorem evenRange_evenDegreeMModEightImage {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    EvenDegreeMModEightImage (K := K) alpha := by
  intro g
  have hmem : chiCycKTwo (K := K) g ∈ imChiM alpha := hrange ▸ ⟨g, rfl⟩
  rcases (evenRange_mem_imChiM_iff halpha).mp hmem with h | h
  · rcases Nat.lt_or_ge alpha 3 with h3 | h3
    · obtain rfl : alpha = 2 := by omega
      rcases evenRange_modEight_of_four_dvd_sub h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl (by rw [h1, evenRange_mUnit_two_modEight])))
    · exact Or.inl (evenRange_toZModPow_eq_one_iff.mpr ((pow_dvd_pow _ h3).trans h))
  · rcases Nat.lt_or_ge alpha 3 with h3 | h3
    · obtain rfl : alpha = 2 := by omega
      rcases evenRange_modEight_of_four_dvd_add h with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr (by rw [h1, evenRange_mUnit_two_modEight])))
    · refine Or.inr (Or.inl ?_)
      have hd : (2 : ℤ_[2]) ^ 3 ∣ ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) - (-1) := by
        rw [sub_neg_eq_add]
        exact (pow_dvd_pow _ h3).trans h
      have := evenRange_toZModPow_eq_iff.mpr hd
      rwa [map_neg, map_one] at this

/-- **Seam 3 discharged**: the `M` row value is attained, because `mUnit α` lies in
`imChiM α`. -/
theorem evenRange_evenDegreeMModEightRowAttained {alpha : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    EvenDegreeMModEightRowAttained (K := K) alpha := by
  obtain ⟨g, hg⟩ : mUnit alpha ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
    rw [hrange]
    exact mUnit_mem_imChiM alpha
  have hg' : chiCycKTwo (K := K) g = mUnit alpha := hg
  exact ⟨g, by rw [hg']⟩

end Seams

/-! ## §8 Composition, and a warning about the assembly endpoints

`rangeFinal_orientedAbstractEquiv_KTwoN` is the composition corollary: the per-`K` `N`
endpoint of `GQ2/Dyadic/OrientationCorrection.lean` with `hrange` gone.  Because `α` is
produced by the identity rather than chosen, the Labute hypothesis and the naturality
hypothesis are quantified over `α`; that is the honest shape.

The assembly endpoints of `GQ2/Dyadic/Instances/StageAbstractionEvenAssembly.lean` cannot be
composed with in the same way, and the obstruction is not a missing lemma.  Their `Hrange` is
quantified over *all* `K` at one fixed `α`, and no such `α` exists: odd-degree `K` has range
`⊤`.  On the `N` side that is outright inconsistent; on the `M` side it forces `α = 2`, where
`imChiM 2 = ⊤` and the identity says nothing.  Both are recorded below. -/

section Final

/-- **The composition corollary.**  The per-`K` `N` orientation endpoint with its image
hypothesis discharged, leaving only the Labute classification input, the Demushkin
invariants, canonicity and naturality. -/
theorem rangeFinal_orientedAbstractEquiv_KTwoN
    {R : LocalReciprocity} {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    [DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2)]
    [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)]
    (B : MarkedRecip R K) (deltaI : AlgebraicClosure ℚ_[2]) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ)
    (nIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (hLab : ∀ alpha : ℕ, NLabHypothesis alpha h nIsCanonical)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hcanonical : nIsCanonical (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)).toMonoidHom)
    (hnatural : ∀ alpha : ℕ, PullbackNatural (IsPresentedOrientationN alpha h)
      (fun chi => nIsCanonical (maxProPQuotient 2 (GalK K)) chi.toMonoidHom)) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  exact ⟨alpha, halpha, orientedAbstractEquiv_KTwoN alpha h (by omega) nIsCanonical
    (hLab alpha) hD hrank hq hrange hcanonical (hnatural alpha)⟩

/-- **The `N` assembly warning.**  A uniform-in-`K` image hypothesis at `imChiN α` with
`α ≥ 2` is inconsistent as soon as one odd-degree `K` carries a marked reciprocity bundle,
since there the range is `⊤` and `-1 ∉ imChiN α`. -/
theorem rangeFinal_uniform_Hrange_imChiN_absurd {alpha : ℕ} (halpha : 2 ≤ alpha)
    {R : LocalReciprocity} (K₀ : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K₀] [CompactSpace (GalK K₀)] [T2Space (GalK K₀)]
    [TotallyDisconnectedSpace (GalK K₀)]
    (B : MarkedRecip R K₀) (hodd : Odd (Module.finrank ℚ_[2] K₀))
    (Hrange : ∀ (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
      [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
      [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha) :
    False := by
  have heq : imChiN alpha = ⊤ :=
    (Hrange K₀).symm.trans (GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_top_of_odd_finrank K₀ B hodd)
  exact GQ2.Dyadic.EvenNLab.neg_one_notMem_imChiN halpha
    (by rw [heq]; exact Subgroup.mem_top _)

/-- **The `M` assembly warning.**  A uniform-in-`K` image hypothesis at `imChiM α` forces
`α = 2`, where `imChiM 2 = ⊤`: the unit `3` is not `≡ ±1 (mod 8)`. -/
theorem rangeFinal_uniform_Hrange_imChiM_forces_two {alpha : ℕ} (halpha : 2 ≤ alpha)
    {R : LocalReciprocity} (K₀ : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K₀] [CompactSpace (GalK K₀)] [T2Space (GalK K₀)]
    [TotallyDisconnectedSpace (GalK K₀)]
    (B : MarkedRecip R K₀) (hodd : Odd (Module.finrank ℚ_[2] K₀))
    (Hrange : ∀ (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
      [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
      [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    alpha = 2 := by
  have heq : imChiM alpha = ⊤ :=
    (Hrange K₀).symm.trans (GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_top_of_odd_finrank K₀ B hodd)
  by_contra hne
  have h3 : 3 ≤ alpha := by omega
  have hval : (((isUnit_one_add_two_mul (1 : ℤ_[2])).unit : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
    rw [IsUnit.unit_spec]
    norm_num
  have hmem : (isUnit_one_add_two_mul (1 : ℤ_[2])).unit ∈ imChiM alpha := by
    rw [heq]
    exact Subgroup.mem_top _
  have h3val : PadicInt.toZModPow (p := 2) 3 (3 : ℤ_[2]) = (3 : ZMod (2 ^ 3)) := by
    simp only [map_ofNat]
  rcases (evenRange_mem_imChiM_iff halpha).mp hmem with hd | hd <;> rw [hval] at hd
  · have hone := evenRange_toZModPow_eq_one_iff.mpr ((pow_dvd_pow (2 : ℤ_[2]) h3).trans hd)
    rw [h3val] at hone
    exact absurd hone (by decide)
  · have hneg1 : (2 : ℤ_[2]) ^ 3 ∣ (3 : ℤ_[2]) - (-1) := by
      rw [sub_neg_eq_add]
      exact (pow_dvd_pow (2 : ℤ_[2]) h3).trans hd
    have hx := evenRange_toZModPow_eq_iff.mpr hneg1
    rw [h3val, map_neg, map_one] at hx
    exact absurd hx (by decide)

end Final

end GQ2.Dyadic.EvenCyclotomicRange

/-! ## Axiom pins -/

#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRangePrin
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_mem_prin_iff
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_prin_antitone
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_isClosed_prin
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_eq_one_of_forall_mem_prin
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_isUnit_of_not_two_dvd
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_two_dvd_add_of_isUnit
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_four_dvd_sub_or_add
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_closure_eq_prin
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_prin_le_of_mem
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_exists_exact_level
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_toZModPow_eq_iff
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_toZModPow_eq_one_iff
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_isClosed_imChiM
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_isClosed_imChiN
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_prin_le_imChiM
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_mem_imChiM_iff
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_prin_le_imChiN
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_mem_imChiN_dvd
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_exists_depth
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_mem_prin_depth
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_neg_dvd_iff
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_eq_imChiM_of_neg_one_mem
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_eq_imChiN_of_neg_one_notMem
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_classify
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_isClosed_range
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_pow_finrank_mem_range
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_prin_le_range
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_exists_not_four_dvd
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq_imChiM
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq_imChiN
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_not_both
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_modEight_of_dvd
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_modEight_of_four_dvd_sub
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_modEight_of_four_dvd_add
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_mUnit_two_modEight
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_evenDegreeNModEightImage
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_evenDegreeMModEightImage
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_evenDegreeMModEightRowAttained
#print axioms GQ2.Dyadic.EvenCyclotomicRange.rangeFinal_orientedAbstractEquiv_KTwoN
#print axioms GQ2.Dyadic.EvenCyclotomicRange.rangeFinal_uniform_Hrange_imChiN_absurd
#print axioms GQ2.Dyadic.EvenCyclotomicRange.rangeFinal_uniform_Hrange_imChiM_forces_two
