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

end GQ2.Dyadic.EvenCyclotomicRange
