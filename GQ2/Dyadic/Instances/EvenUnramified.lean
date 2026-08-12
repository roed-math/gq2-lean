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
   `DN 1 h` is the core whose relator is `x₀ ^ 4 [x₀, x₁] [σ, x₂]` times handles.  (Wave 70
   fixed the letters: `MarkedCore/Cores.lean:123` fixes `a, b, c, d = x₀, x₁, σ, x₂`, so the
   second bracket is `[σ, x₂]`; this line used to read `[x₂, x₃]`, which names a letter the
   core does not have.)  The `M`
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

At depth `α = 2` the statement survives, at the *shifted* parameter `a ≤ 1`
(`evenUnram_le_one_of_orientedN`), and at no other depth (`evenUnram_eq_two_of_orientedN`).
Wave 70 corrected this line, which used to read `a = 1`, and only there: the cited theorem
concludes `a ≤ 1`, and `a = 0` is not excluded by the image, `imChiN 0` and `imChiN 1` being the
same subgroup.  It is §3's head-exponent criterion, not §2's image criterion, that singles out
`a = 1`.  The proof does not transport with it: the `N` endpoint chain
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
which core the surviving point is: `DN 1 h`, with relator `x₀ ^ 4 [x₀, x₁] [σ, x₂]` and
handles (Labute letters as fixed at `MarkedCore/Cores.lean:123`; wave 70 corrected `[x₂, x₃]`
here).

Note that the two criteria are not equally sharp, and §2's is the weaker one: the *image*
criterion admits `a ≤ 1`, since `imChiN 0 = imChiN 1`, while the *head-exponent* criterion
above singles out `a = 1`. -/

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

/-! ## §4 The verdict: the presented cores do not cover the deep third stratum

Combining §1 and §2 at a field.  If `range χ_cyc = evenRangePrin α` then an oriented equivalence
with `chiM a h` would force `evenRangePrin α = imChiM a`, and with `chiN a h` would force
`evenRangePrin α = imChiN a`.  §2 rules the first out at every `a` and the second out at every
`a` once `α ≥ 3`.

So the ramification binder of `parityFinal_evenClassification` is necessary: its conclusion is
false at any field on the third stratum of depth `α ≥ 3`.  That is a boundary result, not a gap:
the classification target is the two `q = 2` Labute families, and the third stratum is where
`q ≥ 4`. -/

section Verdict

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **No `M` core on the third stratum, at any depth and any parameter.**  `-1` is a value of
`chiM a h` and not of a third-stratum `χ_cyc`. -/
theorem evenUnram_isEmpty_orientedM {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) (a h : ℕ) :
    IsEmpty (OrientedContinuousMulEquiv (chiM a h) (chiCycKTwo (K := K))) := by
  refine evenUnram_isEmpty_oriented_of_range_ne ?_
  rw [hr, range_chiM]
  exact Ne.symm (evenUnram_imChiM_ne_prin a halpha)

/-- **No `N` core on the third stratum at depth `α ≥ 3`.** -/
theorem evenUnram_isEmpty_orientedN {alpha : ℕ} (halpha : 3 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) (a h : ℕ) :
    IsEmpty (OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K))) := by
  refine evenUnram_isEmpty_oriented_of_range_ne ?_
  rw [hr, range_chiN]
  exact Ne.symm (evenUnram_imChiN_ne_prin_of_three_le a halpha)

/-- **THE BOUNDARY.**  At a field whose cyclotomic image is a principal-unit group of level
`α ≥ 3`, no presented even core at any parameter and any handle count is oriented-isomorphic to
`G_K(2)`. -/
theorem evenUnram_no_presented_core {alpha : ℕ} (halpha : 3 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) (a h : ℕ) :
    IsEmpty (OrientedContinuousMulEquiv (chiM a h) (chiCycKTwo (K := K))) ∧
      IsEmpty (OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K))) :=
  ⟨evenUnram_isEmpty_orientedM (by omega) hr a h, evenUnram_isEmpty_orientedN halpha hr a h⟩

/-- **THE RAMIFICATION BINDER IS NECESSARY.**  The conclusion of
`parityFinal_evenClassification`, stated verbatim, is false at a field on the third stratum of
depth `α ≥ 3`.  Since `hram` is the only hypothesis of that theorem which such a field can fail
(the degree hypothesis is free and the bundle is carried), the binder cannot be dropped. -/
theorem evenUnram_classification_conclusion_false {alpha : ℕ} (halpha : 3 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) (h : ℕ) :
    ¬ ∃ a : ℕ, 2 ≤ a ∧
      (Nonempty (OrientedContinuousMulEquiv (chiM a h) (chiCycKTwo (K := K))) ∨
        Nonempty (OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K)))) := by
  rintro ⟨a, -, hor | hor⟩
  · exact (evenUnram_isEmpty_orientedM (by omega) hr a h).elim hor.some
  · exact (evenUnram_isEmpty_orientedN halpha hr a h).elim hor.some

/-- **The shifted-depth statement at `α = 2`.**  On the one stratum depth where a core image can
match, the parameter is forced down to `a ≤ 1`: the classification statement, if it holds at
all, holds at the shifted depth `α - 1` and nowhere else. -/
theorem evenUnram_le_one_of_orientedN {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) {a h : ℕ}
    (e : OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K))) : a ≤ 1 := by
  have hrange := evenUnram_range_eq_of_oriented e
  rw [hr, range_chiN] at hrange
  exact ((evenUnram_imChiN_eq_prin_iff halpha).mp hrange.symm).1

/-- The depth is forced too: only `α = 2` admits a matching core at all. -/
theorem evenUnram_eq_two_of_orientedN {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) {a h : ℕ}
    (e : OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K))) : alpha = 2 := by
  have hrange := evenUnram_range_eq_of_oriented e
  rw [hr, range_chiN] at hrange
  exact ((evenUnram_imChiN_eq_prin_iff halpha).mp hrange.symm).2

end Verdict

/-! ## §5 The machinery obstruction at the surviving point

The surviving parameter is exactly the one at which the committed frame layer has nothing.
`nFrameExists_nonempty_iff` reads `Nonempty (NFrame α h) ↔ 2 ≤ α`, so the `N` frame is empty at
`a ≤ 1`; and the `N` endpoint chain consumes `2 ≤ α` at five independent leaves, one of which
(`evenRawStageShift_n`, `StageAbstractionEvenRawSpan.lean:625`) is recorded false at `α = 1`.

The statement below is the form that obstruction takes on this stratum, and it is uniform in the
depth: a core matching a third-stratum `G_K(2)` has no `N` frame, so no transport of the wave-58
endpoint can produce one.  This is why §4's `α = 2` case is a *statement* that survives and not a
theorem that transports. -/

section FrameObstruction

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **A core matching the third stratum has no `N` frame.**  The parameter forced by §4 is below
the frame threshold. -/
theorem evenUnram_isEmpty_nFrame_of_orientedN {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hr : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha) {a h : ℕ}
    (e : OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K))) :
    IsEmpty (NFrame a h) := by
  have ha : a ≤ 1 := evenUnram_le_one_of_orientedN halpha hr e
  rw [← not_nonempty_iff]
  intro hne
  exact absurd (GQ2.Dyadic.EvenDemushkin.evenDem_nFrame_nonempty_iff a h |>.mp hne) (by omega)

end FrameObstruction

/-! ## §6 The field side: what puts `K` on the third stratum

The trichotomy splits on whether the range meets the class `3 mod 4`, so the third stratum is
exactly the locus `range χ_cyc ≤ 1 + 4ℤ₂`.  A square root of `-1` inside `K` forces that: `i` is
fixed by `G_K`, and `χ(g) ≡ -1 (mod 4)` would send `i` to `i ^ 3 = -i`.

This is the direction the committed tree does not carry.  `MarkedRecipBundle.lean:715` records
that only data implies field, and §10's `evenRangeF_hasEqualNormValueGroups_of_range_eq_prin`
runs from the stratum to unramifiedness of `K(i)/K`.  The reverse implication is not available
and is not true: a `K` with `K(i)/K` unramified quadratic has `i ∉ K`, so `χ mod 4` is the
nontrivial character of `Gal(K(i)/K)` and the range meets the class `3 mod 4`.  The honest
entry condition is `i ∈ K`, that is `μ_4 ⊆ K`, which is the `q ≥ 4` Demushkin locus §3 names. -/

section FieldSide

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.Fields

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **A fourth root of unity in `K` makes every cyclotomic value `≡ 1 (mod 4)`.**  The mod-`4`
half of `evenRangeF_gr_zeta`, run at `i` rather than at `ζ₈`. -/
theorem evenUnram_toZModPow_two_eq_one_of_sqrt {w : ℚ̄₂} (hwK : w ∈ K) (hw : w ^ 2 = -1)
    (g : GalK K) : PadicInt.toZModPow 2 (((chiCycK K g : ℤ_[2]ˣ)) : ℤ_[2]) = 1 := by
  have hw4 : w ^ (2 ^ 2) = 1 := by
    have hsq : w ^ (2 ^ 2) = (w ^ 2) ^ 2 := by ring
    rw [hsq, hw]
    norm_num
  have hspec := cyclotomicCharacter.spec 2 (evenRangeF_gr g) w hw4
  have hval : ((chiCycKModFour (K := K) g : (ZMod 4)ˣ) : ZMod 4)
      = PadicInt.toZModPow 2 (((chiCycK K g : ℤ_[2]ˣ)) : ℤ_[2]) := rfl
  have hspec' : evenRangeF_gr g w
      = w ^ (((chiCycKModFour (K := K) g : (ZMod 4)ˣ) : ZMod 4)).val := by
    rw [hval]
    exact hspec
  rcases unitsModFour_eq_one_or_neg_one (chiCycKModFour (K := K) g) with hu | hu
  · rw [← hval, hu]
    rfl
  · exfalso
    have hfix : evenRangeF_gr g w = w := evenRangeF_gr_fix g hwK
    have hval3 : (((-1 : (ZMod 4)ˣ)) : ZMod 4).val = 3 := by decide
    have hneg : evenRangeF_gr g w = -w := by
      rw [hspec', hu, hval3]
      calc w ^ 3 = w ^ 2 * w := by ring
        _ = -w := by rw [hw]; ring
    have h0 : w = 0 := by
      have hww := hfix.symm.trans hneg
      linear_combination hww / 2
    rw [h0] at hw
    norm_num at hw

/-- **The stratum condition, from the field.**  If `K` contains a square root of `-1` then the
cyclotomic image on `G_K(2)` lies in `1 + 4ℤ₂`. -/
theorem evenUnram_range_le_prin_two_of_sqrt_neg_one {w : ℚ̄₂} (hwK : w ∈ K) (hw : w ^ 2 = -1) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2 := by
  intro v hv
  obtain ⟨g, rfl⟩ := evenRangeF_exists_chiCycK hv
  exact evenRange_mem_prin_iff.mpr
    (evenRange_toZModPow_eq_one_iff.mp (evenUnram_toZModPow_two_eq_one_of_sqrt hwK hw g))

/-- **ENTERING THE THIRD STRATUM.**  A square root of `-1` in `K`, plus a marked reciprocity
bundle, places `K` on the third stratum at a depth `α ≥ 2` determined by `K`.  Composed with §4
this says which fields the boundary is about. -/
theorem evenUnram_exists_range_eq_prin (B : MarkedRecip R K) {w : ℚ̄₂} (hwK : w ∈ K)
    (hw : w ^ 2 = -1) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = evenRangePrin alpha :=
  evenRangeF_eq_prin_of_forall_four_dvd _ evenRange_isClosed_range (evenRange_prin_le_range B)
    (fun _ hu => evenRange_mem_prin_iff.mp
      (evenUnram_range_le_prin_two_of_sqrt_neg_one hwK hw hu))

/-- **The `M` row is excluded at such a field outright**, with no knowledge of the depth. -/
theorem evenUnram_isEmpty_orientedM_of_sqrt (B : MarkedRecip R K) {w : ℚ̄₂} (hwK : w ∈ K)
    (hw : w ^ 2 = -1) (a h : ℕ) :
    IsEmpty (OrientedContinuousMulEquiv (chiM a h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hr⟩ := evenUnram_exists_range_eq_prin B hwK hw
  exact evenUnram_isEmpty_orientedM halpha hr a h

/-- **And the `N` row survives only at the shifted parameter**, again with no knowledge of the
depth. -/
theorem evenUnram_le_one_of_orientedN_of_sqrt (B : MarkedRecip R K) {w : ℚ̄₂} (hwK : w ∈ K)
    (hw : w ^ 2 = -1) {a h : ℕ}
    (e : OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K))) : a ≤ 1 := by
  obtain ⟨alpha, halpha, hr⟩ := evenUnram_exists_range_eq_prin B hwK hw
  exact evenUnram_le_one_of_orientedN halpha hr e

end FieldSide

/-! ## §7 The model field on the stratum

`quadField` is finite-dimensional at every argument and needs a non-square proof only for the
degree computation, which nothing below uses.  So `quadField (-1)` is available with no new
arithmetic, and `evenParity_sqrtIn_neg_one_sq` is the committed square root.  This is the
tree's first named field on the third stratum; the five committed quadratic rows
(`±2, 5, ±10`) all carry odd valuation and are ramified-`i` fields. -/

section ModelField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.Fields GQ2.Dyadic.EvenParity

variable {R : LocalReciprocity}

/-- **The model field `ℚ₂(i)`**, as an intermediate field of `ℚ̄₂/ℚ₂`. -/
abbrev evenUnramKNegOne : IntermediateField ℚ_[2] ℚ̄₂ := quadField (-1)

variable [CompactSpace (GalK evenUnramKNegOne)]
  [TotallyDisconnectedSpace (GalK evenUnramKNegOne)]

/-- **The model field lies on the third stratum**, over its own reciprocity bundle and the
standing profinite instance binders, and nothing else. -/
theorem evenUnram_exists_range_eq_prin_KNegOne (B : MarkedRecip R evenUnramKNegOne) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := evenUnramKNegOne)).toMonoidHom =
        evenRangePrin alpha :=
  evenUnram_exists_range_eq_prin B (sqrtIn_mem_quadField (-1)) evenParity_sqrtIn_neg_one_sq

/-- **No `M` core at the model field**, at any parameter and any handle count. -/
theorem evenUnram_isEmpty_orientedM_KNegOne (B : MarkedRecip R evenUnramKNegOne) (a h : ℕ) :
    IsEmpty (OrientedContinuousMulEquiv (chiM a h) (chiCycKTwo (K := evenUnramKNegOne))) :=
  evenUnram_isEmpty_orientedM_of_sqrt B (sqrtIn_mem_quadField (-1))
    evenParity_sqrtIn_neg_one_sq a h

/-- **The `N` core at the model field is forced to the shifted parameter.**  Together with §5,
any such core has an empty `N` frame, which is where the committed endpoint chain stops. -/
theorem evenUnram_le_one_of_orientedN_KNegOne (B : MarkedRecip R evenUnramKNegOne) {a h : ℕ}
    (e : OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := evenUnramKNegOne))) :
    a ≤ 1 :=
  evenUnram_le_one_of_orientedN_of_sqrt B (sqrtIn_mem_quadField (-1))
    evenParity_sqrtIn_neg_one_sq e

end ModelField

end

/-! ## §8 Axiom pins

Every statement of this file printed against the committed even endpoints it is stated about,
and against the committed range identity and trichotomy, so that the two sets can be read side
by side.  Nothing here may exceed the committed even set. -/

section AxiomPins

open GQ2.Dyadic.EvenUnram

-- §1 the orientation extractor
#print axioms evenUnram_range_eq_of_oriented
#print axioms evenUnram_isEmpty_oriented_of_range_ne

-- §2 the core images that are principal-unit groups
#print axioms evenUnram_nUnit_zero_eq_one
#print axioms evenUnram_imChiN_zero_eq_one
#print axioms evenUnram_nUnit_one_sub_one
#print axioms evenUnram_imChiN_one_eq_prin_two
#print axioms evenUnram_imChiN_zero_eq_prin_two
#print axioms evenUnram_imChiM_ne_prin
#print axioms evenUnram_notMem_prin_of_add_one
#print axioms evenUnram_imChiN_ne_prin
#print axioms evenUnram_prin_two_ne_prin
#print axioms evenUnram_imChiN_ne_prin_of_three_le
#print axioms evenUnram_imChiN_eq_prin_iff

-- §3 the head exponent
#print axioms evenUnram_head_eq_two_pow_iff
#print axioms evenUnram_nWord_one
#print axioms evenUnram_mWord_head

-- §4 the verdict
#print axioms evenUnram_isEmpty_orientedM
#print axioms evenUnram_isEmpty_orientedN
#print axioms evenUnram_no_presented_core
#print axioms evenUnram_classification_conclusion_false
#print axioms evenUnram_le_one_of_orientedN
#print axioms evenUnram_eq_two_of_orientedN

-- §5 the frame obstruction
#print axioms evenUnram_isEmpty_nFrame_of_orientedN

-- §6 the field side
#print axioms evenUnram_toZModPow_two_eq_one_of_sqrt
#print axioms evenUnram_range_le_prin_two_of_sqrt_neg_one
#print axioms evenUnram_exists_range_eq_prin
#print axioms evenUnram_isEmpty_orientedM_of_sqrt
#print axioms evenUnram_le_one_of_orientedN_of_sqrt

-- §7 the model field
#print axioms evenUnram_exists_range_eq_prin_KNegOne
#print axioms evenUnram_isEmpty_orientedM_KNegOne
#print axioms evenUnram_le_one_of_orientedN_KNegOne

-- the committed statements this file is stated against, for the side-by-side
#print axioms GQ2.Dyadic.EvenParity.parityFinal_evenClassification
#print axioms GQ2.Dyadic.EvenRangeModel.evenRangeF_range_trichotomy
#print axioms GQ2.Dyadic.EvenRangeModel.evenRangeF_hasEqualNormValueGroups_of_range_eq_prin
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq
#print axioms GQ2.Dyadic.EvenDemushkin.evenDem_nFrame_nonempty_iff

end AxiomPins

end GQ2.Dyadic.EvenUnram
