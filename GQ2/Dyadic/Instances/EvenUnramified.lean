/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenRangeModelFields
import GQ2.Dyadic.Instances.EvenDemushkin

/-!
# W69-UNRAM: the classification on the third stratum of the range identity

## What this file is for

Wave 67 removed the ramification binder from the range identity by adding a third stratum
(`evenRangeF_range_trichotomy`, `EvenRangeModelFields.lean` §10): the cyclotomic image on
`G_K(2)` is `imChiM α`, or `imChiN α`, or the principal-unit group `evenRangePrin α = 1 + 2^α ℤ₂`.
The parity supply and `Hfam` carry no ramification binder, so they hold on the third stratum
already.  What was missing is the branch data: what the even classification *says* there.

This file answers that, and the answer is a boundary rather than a fourth branch.

## The answer, in one line

The presented cores reach the third stratum at exactly one point, `imChiN 1 = evenRangePrin 2`,
and at no point of depth `α ≥ 3`.

## The three things that make it precise

1. **An orientation carries its image** (§1).  `OrientedContinuousMulEquiv chiC chiG` is a
   `ContinuousMulEquiv` together with `∀ x, chiG (e x) = chiC x`, so it forces
   `range chiG = range chiC`.  The tree never extracted this; every consumer took `hrange` as a
   separate hypothesis.  Once extracted, a classification statement at a field *determines* the
   cyclotomic image, so the range identity is not merely an input to the classification but a
   consequence of it, and a range that is no core image refutes every classification statement.

2. **Which core images are principal-unit groups** (§2).  `imChiM a` contains `-1` for every `a`
   and `evenRangePrin α` omits it for `α ≥ 2`, so the `M` row never meets the third stratum.
   On the `N` row the answer is a single point: `nUnit 0 = nUnit 1` definitionally (the `ℕ`
   subtraction in `onePlusTwoPow` truncates), `nUnit 1 = -3⁻¹` has exact level `2`, so
   `imChiN 0 = imChiN 1 = evenRangePrin 2`; and for `a ≥ 2` the generator `nUnit a` is
   `≡ -1 (mod 4)`, which no principal unit is.  The clean form is
   `evenUnram_imChiN_eq_prin_iff`: for `α ≥ 2`, `imChiN a = evenRangePrin α ↔ a ≤ 1 ∧ α = 2`.

3. **The head exponent explains the coincidence** (§3).  The `N` relator head is
   `a ^ (2 + 2 ^ α)` and `2 + 2 ^ a = 2 ^ b` has the unique solution `(a, b) = (1, 2)`, so
   `DN 1 h` is the core whose relator is `x₀ ^ 4 [x₀, x₁] [x₂, x₃]` times handles.  The `M`
   relator head is `a ^ 2` at every `α`.  The third stratum at depth `α` is the locus where
   `μ_{2^α} ⊆ K`, whose Demushkin invariant is `q = 2^α`; the cores realize `q = 4` at
   `(N, α = 1)` and `q = 2` elsewhere, which is the same one-point overlap seen from the
   group side.

## The verdict (§4, §5)

On the third stratum at depth `α ≥ 3` there is **no** presented core, at any parameter and any
handle count, admitting an oriented equivalence with `G_K(2)`: `evenUnram_isEmpty_orientedM` and
`evenUnram_isEmpty_orientedN`.  Consequently the conclusion of `parityFinal_evenClassification`
is refuted at such a field (`evenUnram_classification_conclusion_false`), so its ramification
binder `hram` is necessary and not merely convenient.  This is the boundary result the ticket
asked to state honestly if the cores did not cover the stratum.

At depth `α = 2` the statement survives, at the *shifted* parameter `a = 1`, and only there
(`evenUnram_le_one_of_orientedN`).  The proof does not transport with it: the `N` endpoint chain
needs `2 ≤ α` at five independent leaves, one of which (`evenRawStageShift_n`) is documented
false at `α = 1`, and the frame layer records `IsEmpty (NFrame 1 h)`.  §5 states that
obstruction in the form it takes here: any core admitting an oriented equivalence with a
third-stratum `G_K(2)` has an empty `N` frame.

## The field side (§6)

The stratum is entered by a square root of `-1` in `K`, not by unramifiedness of `K(i)/K`:
`evenUnram_range_le_prin_two_of_sqrt_neg_one`.  This is the converse direction the tree did not
carry (`MarkedRecipBundle.lean:715` records that only data implies field), and it is the honest
characterisation: §10's committed theorem
`evenRangeF_hasEqualNormValueGroups_of_range_eq_prin` gives unramifiedness *from* the stratum,
and the reverse implication is false, since a `K` with `K(i)/K` unramified quadratic has
`i ∉ K` and therefore a cyclotomic value `≢ 1 (mod 4)`.  §6 closes with the model field
`quadField (-1)`, which lies on the stratum with the reciprocity bundle as its only binder.

## Lane

W69-UNRAM.  New file; nothing committed is edited.  Reserved prefix `evenUnram`.
-/

namespace GQ2.Dyadic.EvenUnram

open GQ2 GQ2.Dyadic MarkedCore
open GQ2.Dyadic.EvenCyclotomicRange GQ2.Dyadic.EvenRangeModel

noncomputable section

/-! ## §1 An orientation carries its image

`OrientedContinuousMulEquiv chiC chiG` (`GQ2/Dyadic/OrientationCorrection.lean:82`) bundles a
`ContinuousMulEquiv e : C ≃ G` with `OrientationMatches`, that is `∀ x, chiG (e x) = chiC x`.
Since `e` is bijective this is exactly `chiG ∘ e = chiC`, so the two characters have the same
image.  The converse fails, and the tree already says so
(`inverseChiM_not_orientationMatches`); only this direction is used below. -/

section Orientation

variable {C G A : Type} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A]
  [TopologicalSpace A] [IsTopologicalGroup A]

omit [IsTopologicalGroup C] [IsTopologicalGroup G] [IsTopologicalGroup A] in
/-- **An oriented equivalence forces the images to agree.**  The extractor the even lane's
consumers never had: every one of them carries `hrange` as a separate hypothesis, so no
committed statement reads the image *off* a classification.  With this, a classification
statement at `K` pins `range χ_cyc`. -/
theorem evenUnram_range_eq_of_oriented {chiC : ContinuousMonoidHom C A}
    {chiG : ContinuousMonoidHom G A} (e : OrientedContinuousMulEquiv chiC chiG) :
    MonoidHom.range chiG.toMonoidHom = MonoidHom.range chiC.toMonoidHom := by
  obtain ⟨f, hf⟩ := e
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f.symm x,
      (hf (f.symm x)).symm.trans (congrArg chiG.toMonoidHom (f.apply_symm_apply x))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨f x, hf x⟩

omit [IsTopologicalGroup C] [IsTopologicalGroup G] [IsTopologicalGroup A] in
/-- The contrapositive, in the form §4 consumes: an image that is not the core's image admits no
oriented equivalence. -/
theorem evenUnram_isEmpty_oriented_of_range_ne {chiC : ContinuousMonoidHom C A}
    {chiG : ContinuousMonoidHom G A}
    (h : MonoidHom.range chiG.toMonoidHom ≠ MonoidHom.range chiC.toMonoidHom) :
    IsEmpty (OrientedContinuousMulEquiv chiC chiG) :=
  ⟨fun e => h (evenUnram_range_eq_of_oriented e)⟩

end Orientation

/-! ## §2 Which presented-core images are principal-unit groups

The two committed core images are `imChiM a = closure {-1, mUnit a}` and
`imChiN a = closure {nUnit a}`, both topologically closed
(`MarkedCore/M.lean:1505`, `MarkedCore/N.lean:1290`).  The question of this file is when either
equals `evenRangePrin α`, and the answer is the single point `(a, α) = (0 or 1, 2)`.

The `α = 2` coincidence is not an accident of small numbers: `nUnit a · (1 + 2 ^ a) = -1`, so
`nUnit a - 1 = (2 + 2 ^ a) · nUnit a`, and the exact level of `nUnit a` is the `2`-adic
valuation of `2 + 2 ^ a`, which is `1` for `a ≥ 2` and `2` at `a = 1`.  The same number
`2 + 2 ^ a` is the `N` relator head exponent, which is §3. -/

section Images

/-- `onePlusTwoPow` truncates its `ℕ` subtraction at `0`, so the `N` unit at parameter `0`
is the unit at parameter `1`.  Definitional. -/
theorem evenUnram_nUnit_zero_eq_one : nUnit 0 = nUnit 1 := rfl

/-- Hence the two lowest `N` images coincide. -/
theorem evenUnram_imChiN_zero_eq_one : imChiN 0 = imChiN 1 := by
  rw [imChiN, imChiN, evenUnram_nUnit_zero_eq_one]

/-- The exact level of the `N` generator at parameter `1`: `nUnit 1 = -3⁻¹` satisfies
`nUnit 1 - 1 = 2 ^ 2 · nUnit 1`, so its level is exactly `2`. -/
theorem evenUnram_nUnit_one_sub_one :
    ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ 2 * ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) := by
  have h := nUnit_mul (α := 1) le_rfl
  rw [pow_one] at h
  linear_combination -h

/-- **The one point where an `N` image is a principal-unit group.**  `imChiN 1` is exactly
`1 + 4ℤ₂`.  A unit of exact level `2` topologically generates the level-`2` principal units
(`evenRange_closure_eq_prin`), and `nUnit 1` is such a unit. -/
theorem evenUnram_imChiN_one_eq_prin_two : imChiN 1 = evenRangePrin 2 :=
  evenRange_closure_eq_prin (η := nUnit 1) (a := nUnit 1) le_rfl evenUnram_nUnit_one_sub_one

/-- The same statement at parameter `0`. -/
theorem evenUnram_imChiN_zero_eq_prin_two : imChiN 0 = evenRangePrin 2 :=
  evenUnram_imChiN_zero_eq_one.trans evenUnram_imChiN_one_eq_prin_two

/-- **The `M` row never meets the third stratum.**  `-1` lies in every `imChiM a` and in no
`evenRangePrin α` with `α ≥ 2`.  No hypothesis on `a`. -/
theorem evenUnram_imChiM_ne_prin (a : ℕ) {alpha : ℕ} (halpha : 2 ≤ alpha) :
    imChiM a ≠ evenRangePrin alpha := by
  intro h
  exact evenRangeF_neg_one_notMem_prin halpha (h ▸ neg_one_mem_imChiM a)

/-- A unit `≡ -1 (mod 4)` is in no principal-unit group of level `≥ 2`. -/
theorem evenUnram_notMem_prin_of_add_one {u : ℤ_[2]ˣ} {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hu : (2 : ℤ_[2]) ^ 2 ∣ ((u : ℤ_[2])) + 1) : u ∉ evenRangePrin alpha := by
  intro hmem
  obtain ⟨c, hc⟩ := (pow_dvd_pow (2 : ℤ_[2]) halpha).trans (evenRange_mem_prin_iff.mp hmem)
  obtain ⟨d, hd⟩ := hu
  have hdvd : (2 : ℤ_[2]) ^ 2 ∣ (2 : ℤ_[2]) ^ 1 :=
    ⟨d - c, by rw [pow_one]; linear_combination hd - hc⟩
  exact absurd (evenRangeF_two_pow_dvd hdvd) (by omega)

/-- **The `N` row above parameter `1` never meets the third stratum.**  For `a ≥ 2` the
generator `nUnit a` is `≡ -1 (mod 4)`. -/
theorem evenUnram_imChiN_ne_prin {a alpha : ℕ} (ha : 2 ≤ a) (halpha : 2 ≤ alpha) :
    imChiN a ≠ evenRangePrin alpha := by
  intro h
  refine evenUnram_notMem_prin_of_add_one halpha
    (GQ2.Dyadic.StageGeneric.evenKernel_nUnit_add_one_dvd_four ha) ?_
  exact h ▸ GQ2.Dyadic.EvenRowSupply.evenRow_nUnit_mem_imChiN a

/-- The level-`2` principal units are not the level-`α` ones for `α ≥ 3`: the unit `5` separates
them. -/
theorem evenUnram_prin_two_ne_prin {alpha : ℕ} (halpha : 3 ≤ alpha) :
    evenRangePrin 2 ≠ evenRangePrin alpha := by
  intro h
  have hmem : evenRangeF_onePlus 2 ∈ evenRangePrin alpha :=
    h ▸ evenRangeF_onePlus_mem (by omega)
  have hd := evenRange_mem_prin_iff.mp hmem
  rw [evenRangeF_onePlus_val (by omega)] at hd
  have hd2 : (2 : ℤ_[2]) ^ alpha ∣ (2 : ℤ_[2]) ^ 2 := by
    have hsimp : (1 : ℤ_[2]) + 2 ^ 2 - 1 = 2 ^ 2 := by ring
    rwa [hsimp] at hd
  exact absurd (evenRangeF_two_pow_dvd hd2) (by omega)

/-- **No `N` image is a principal-unit group of level `≥ 3`.**  The two low parameters land on
level `2` and every higher one misses `1 + 4ℤ₂` entirely. -/
theorem evenUnram_imChiN_ne_prin_of_three_le (a : ℕ) {alpha : ℕ} (halpha : 3 ≤ alpha) :
    imChiN a ≠ evenRangePrin alpha := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · rw [evenUnram_imChiN_zero_eq_prin_two]
      exact evenUnram_prin_two_ne_prin halpha
    · rw [evenUnram_imChiN_one_eq_prin_two]
      exact evenUnram_prin_two_ne_prin halpha
  · exact evenUnram_imChiN_ne_prin ha (by omega)

/-- **THE COINCIDENCE, EXACTLY.**  For `α ≥ 2` the `N` image at parameter `a` is the level-`α`
principal-unit group precisely when `a ≤ 1` and `α = 2`.  Together with
`evenUnram_imChiM_ne_prin` this is the complete answer to "which presented-core images are
principal-unit groups": one point, on the `N` row, at the shifted parameter. -/
theorem evenUnram_imChiN_eq_prin_iff {a alpha : ℕ} (halpha : 2 ≤ alpha) :
    imChiN a = evenRangePrin alpha ↔ (a ≤ 1 ∧ alpha = 2) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge a 2 with ha | ha
    · refine ⟨by omega, ?_⟩
      by_contra hne
      exact evenUnram_imChiN_ne_prin_of_three_le a (by omega) h
    · exact absurd h (evenUnram_imChiN_ne_prin ha halpha)
  · rintro ⟨ha, rfl⟩
    interval_cases a
    · exact evenUnram_imChiN_zero_eq_prin_two
    · exact evenUnram_imChiN_one_eq_prin_two

end Images

/-! ## §3 The head exponent, and why the overlap is one point

The `N` core relator is `nWord α a b c d = a ^ (2 + 2 ^ α) * [a,b] * [c,d]` times handles
(`MarkedCore/Cores.lean:123`), and the `M` core relator is
`a ^ 2 * [a,b] * c ^ (2 ^ α) * [c,d]`, whose head exponent is `2` at every `α`.

On the third stratum at depth `α` the range is `1 + 2^α ℤ₂`, which is the image of the
cyclotomic character exactly when `μ_{2^α} ⊆ K`, so the Demushkin invariant is `q = 2 ^ α`, a
power of `2` that is at least `4`.  A presented core can carry that invariant only if its head
exponent is itself such a power, and `2 + 2 ^ a = 2 ^ b` has the single solution
`(a, b) = (1, 2)`.  That is the group-side shadow of §2's one-point coincidence, and it says
which core the surviving point is: `DN 1 h`, with relator `x₀ ^ 4 [x₀, x₁] [x₂, x₃]` and
handles. -/

section HeadExponent

/-- **The head exponent is a power of two at exactly one parameter.** -/
theorem evenUnram_head_eq_two_pow_iff (a b : ℕ) : 2 + 2 ^ a = 2 ^ b ↔ (a = 1 ∧ b = 2) := by
  constructor
  · intro h
    have hpos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
    have hb2 : 2 ≤ b := by
      by_contra hcon
      interval_cases b <;> simp only [pow_zero, pow_one] at h <;> omega
    have h4b : (4 : ℕ) ∣ 2 ^ b := by
      obtain ⟨c, rfl⟩ : ∃ c, b = 2 + c := ⟨b - 2, by omega⟩
      exact ⟨2 ^ c, by rw [pow_add]; norm_num⟩
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · rw [pow_zero] at h
        omega
      · rw [pow_one] at h
        refine ⟨rfl, Nat.pow_right_injective le_rfl (show (2 : ℕ) ^ b = 2 ^ 2 by omega)⟩
    · exfalso
      have h4a : (4 : ℕ) ∣ 2 ^ a := by
        obtain ⟨c, rfl⟩ : ∃ c, a = 2 + c := ⟨a - 2, by omega⟩
        exact ⟨2 ^ c, by rw [pow_add]; norm_num⟩
      omega
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- **The surviving core's relator.**  At parameter `1` the `N` core word is the fourth-power
Demushkin shape. -/
theorem evenUnram_nWord_one {G : Type*} [Group G] (a b c d : G) :
    nWord 1 a b c d = a ^ (2 ^ 2) * commP a b * commP c d := by
  rw [nWord]
  norm_num

/-- The `M` core word's head exponent is `2` at every parameter, so no `M` core carries a
Demushkin invariant above `2`. -/
theorem evenUnram_mWord_head {G : Type*} [Group G] (alpha : ℕ) (a b c d : G) :
    mWord alpha a b c d = a ^ 2 * commP a b * c ^ (2 ^ alpha) * commP c d := rfl

end HeadExponent

end

end GQ2.Dyadic.EvenUnram
