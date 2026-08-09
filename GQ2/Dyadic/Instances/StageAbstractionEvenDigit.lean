/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenPerK

/-!
# W53-HUP: the one-digit demand behind `Hup`, settled from the range identity

`Hup` is the raw-to-bracket upgrade `EvenKernelRawToBracketSupply (α - 1)`, the sharper of the
two named inputs on the even route's per-`K` endpoints (`evenPerK_orientedEquiv{N,M}`,
`GQ2/Dyadic/Instances/StageAbstractionEvenPerK.lean` §6).  W52 located its natural route
exactly: the neutralisation supply `EvenRawToNeutralSupply` implies it
(`evenRawTo_supply_of_neutral`), and that supply forces the character filtration not to drop
between consecutive layers, one digit deeper than the committed even bound provides
(`evenRawTo_chi_dvd_of_neutral_deep`, with `evenSharpDeepDefined` recording that the bound has
no slack).  What was not available in W52 is the range identity; with it, this file settles
the demand in both directions.

## The verdict on the natural route

The range identity pins `im χ` to `imChiN α` or `imChiM α` and, decisively, it makes the
committed depth bound *attained*: on either image there is a character preimage of the
orientation unit, and its `2^m`-th powers sit in `λ_{m+1}` (`M` branch, exact level `m + α`)
or `λ_{m+2}` (`N` branch, exact level `m + α + 1`) with *sharp* character level, by the unit
cofactor of the committed telescoping `GQ2.exists_unit_pow_two_pow_sub_one_of_level` (§1, §2).
Consequently:

* **the neutralisation supply is FALSE at every depth `s ≥ α - 2`**, on both branch images
  (`evenDigit_not_neutralSupply_{M,N}`): the witness in `λ_{k-1}` has exact level
  `k + α - 2`, and the W52 necessary condition demands `k + α - 1` there.  In particular it is
  false at the lane's own depth `s = α - 1` (`evenDigit_not_neutralSupply_lane_{M,N}`), which
  is the depth the climb runs at: the corrected deep row seam exists only at `s = α - 1`
  (the W52 depth-necessity pin), so no depth serves both stations;
* **the supply is TRUE at every depth `s ≤ α - 3`**, trivially, because the committed bound
  already reaches the demanded precision (`evenDigit_neutralSupply_of_depth_le`), so `Hup` at
  those depths is free (`evenDigit_rawToBracket_of_depth_le`).  The cliff sits exactly at
  `s = α - 2`.

So the neutral route to `Hup` is dead, and the refutation is by explicit Galois-theoretic
witness, not by an abstract counterexample character.

## The repair: what one digit really costs

The refutation is exactly one digit wide, and the L template shows what to do with a one-digit
defect: do not neutralise coordinates in place, repair them by corrections with *literally
trivial shift word*.  The odd route's
`stageResidual_nonempty_actualDefectSupply_of_kernelAdaptedKill` repairs its two fresh digit
positions by base moves plus central classes of prescribed
character, the latter paid by `Function.Surjective chiCycKTwo`, which is false in even degree.
The even replacement (§4, §5):

* a coordinate of a depth-`k-1` class carries exactly two digits beyond the committed bound,
  at positions `k + α - 2` and `k + α - 1` (precision `k + 1 + (α - 1)` is what the depth
  `s = α - 1` neutral subgroup demands);
* the digit at `k + α - 1` is repaired *for free from the range identity*: the sharp central
  class of §2 (`evenDigit_sharp_zLayer_{M,N}`) is the even analogue of the L template's
  `stageResidual_exists_deep_zLayer_of_surjective`, with surjectivity replaced by the pinned
  image, and central classes move no row at all;
* the digit at `k + α - 2` is the honest residue.  `EvenDigitFlipSupply` asks, per stage and
  per coordinate, for one correction with trivial literal shift word whose class at that slot
  is sharp at `k + α - 2` and trivial elsewhere: the even clone of the odd route's
  `SqStageHandleDigitFlipSupply`, at the even filtration's own depth and at every slot.

The engine `evenDigit_exists_neutral_shift` then repairs an *arbitrary* raw depth correction
to a neutral one with the same literal shift word, so the flips give not merely the residual
instance but the whole span upgrade: `evenDigit_rawToBracket_of_flip` proves
`EvenKernelRawToBracketSupply (α - 1)` outright from `EvenDigitFlipSupply`.  And the converse
holds too: seeding one coordinate with a sharp class of §2 and dividing off the neutral
correction `Hup` provides turns `Hup` back into the flips
(`evenDigit_flip_of_rawToBracket`).  So on either branch image the two statements are
EQUIVALENT (`evenDigit_rawToBracket_iff_flip_{M,N}`): `Hup` is not merely reduced to the
one-digit flip supply, it *is* the one-digit flip supply, with the second digit and the whole
central layer paid by the range identity.

## What is constructed, and what is honestly left

On the `M` branch the flip at coordinate `2` is CONSTRUCTED (§6): the row of coordinate `2` is
the cross bracket `[p, base 3]`, so the `2^(k-2)`-th power of `base 3` is a correction with
literally trivial row, and its character class is `(mUnit α)^(2^(k-2))`, sharp at `k + α - 2`
by the telescoping.  This is the exact even counterpart of the L template's commuting
`2^(k-2)`-power base moves, and it works because the `M` table has a value of exact level `α`
sitting at the bracket partner of a squarefree row.  On the `N` branch every bracket partner
of every squarefree row has table value `1`, so no flip is constructible by partner powers:
the `N` character mass sits at the twisted index `1`, whose row `[p, base 0]` it does not
partner.  The flip supply at the remaining slots is carried, exactly as the odd route carries
`Hflip`.  As a bare statement it asks far less than `Hup` (one digit at one slot per
correction, against a span equality), and §5's equivalence certifies that it asks for exactly
as much as the endpoints need; unlike the neutral supply it is not refutable by depth
counting, since sharp classes at `k + α - 2` exist in abundance (§2) and only their shift
words are in question.

## The per-`K` endpoints, re-cut

§7 restates the per-`K` endpoints with `Hup` replaced by the flip supply:
`evenDigit_orientedEquiv{N,M}` carry the level-three base, `Hfam`, and `EvenPerK{N,M}DigitFlip`,
and the `α = 2` stratum endpoints `evenDigit_orientedEquiv{N,M}_two` carry only `Hfam` and the
flips.  Everything else is discharged as in `StageAbstractionEvenPerK.lean` §6; in addition
the branch's `hbound` and the sharp central class are discharged from the range identity
inside.  The refutation is also recorded per field (`evenDigit_perK_not_neutral{N,M}`), so the
supersession is on the page: the input these endpoints replace could never have been supplied
on its natural route.

## Numbering

1. sharp two-adic powering;
2. the exact-level layer witnesses on the two branch images;
3. the neutral-supply verdict: the cliff sits at `s = α - 2`;
4. the digit flip supply and the repair engine;
5. `Hup` and the flips are the same statement;
6. the constructed flip at coordinate `2`;
7. the per-`K` endpoints, re-cut at the flips;
8. axiom pins.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenRowSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Sharp two-adic powering

The committed telescoping `GQ2.exists_unit_pow_two_pow_sub_one_of_level` produces the
divisibility `2^(m+s) ∣ η^(2^m) - 1` with a *unit* cofactor.  The cofactor is the sharpness:
this section extracts both halves at once, which is the arithmetic engine of the whole file. -/

section SharpPow

/-- A value `2^n · u` with `u` a unit is not divisible by `2^(n+1)`. -/
private theorem evenDigit_not_dvd_of_unit {n : ℕ} {x : ℤ_[2]} (b : ℤ_[2]ˣ)
    (hx : x = 2 ^ n * (b : ℤ_[2])) : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ x := by
  rintro ⟨t, ht⟩
  have hcancel : (2 : ℤ_[2]) ^ n * (b : ℤ_[2]) = 2 ^ n * (2 * t) := by
    rw [← hx, ht, pow_succ]
    ring
  have hdvd : (2 : ℤ_[2]) ∣ (b : ℤ_[2]) :=
    ⟨t, mul_left_cancel₀ (pow_ne_zero n two_ne_zero) hcancel⟩
  obtain ⟨c, hc⟩ := hdvd
  have hone : (2 : ℤ_[2]) ^ 1 ∣ 1 := by
    refine ⟨c * ((b⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), ?_⟩
    have hbb : (b : ℤ_[2]) * ((b⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← hbb, hc, pow_one]
    ring
  rw [two_pow_dvd_iff, map_one] at hone
  exact absurd hone (by decide)

/-- **Sharp two-adic powering.**  From an exact level-`s` congruence `η = 1 + 2^s · a` with
`a` a unit and `s ≥ 2`, the `2^m`-th power has the exact level `m + s`: divisible there and
sharp at the next digit.  The divisibility half is the committed telescoping
`GQ2.exists_unit_pow_two_pow_sub_one_of_level`; the sharpness half is what this lane adds. -/
theorem evenDigit_pow_sharp (η a : ℤ_[2]ˣ) {s : ℕ} (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * a) (m : ℕ) :
    (2 : ℤ_[2]) ^ (m + s) ∣ ((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
      ¬ (2 : ℤ_[2]) ^ (m + s + 1) ∣ ((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨b, hb⟩ := GQ2.exists_unit_pow_two_pow_sub_one_of_level η a s hs hη m
  exact ⟨⟨b, hb⟩, evenDigit_not_dvd_of_unit b hb⟩

/-- `(nUnit α)²` at exact level `α + 1`: squaring the `N` orientation unit lands one digit
deeper than `mUnit α`, with a unit cofactor.  The sign of `nUnit` dies in the square, which
is why the `N` witnesses of §2 run one layer behind the `M` ones. -/
theorem evenDigit_nUnit_sq_eq {α : ℕ} (hα : 2 ≤ α) :
    ∃ a : ℤ_[2]ˣ,
      ((nUnit α ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ (α + 1) * (a : ℤ_[2]) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  have h := nUnit_mul (α := β + 2) (by omega)
  have hu : IsUnit (-(((nUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 * (1 + 2 * 2 ^ β))) := by
    refine IsUnit.neg (IsUnit.mul ?_ (isUnit_one_add_two_mul (2 ^ β)))
    exact (Units.isUnit (nUnit (β + 2))).pow 2
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  have hp2 : (2 : ℤ_[2]) ^ (β + 2) = 4 * 2 ^ β := by rw [pow_add]; ring
  have hp3 : (2 : ℤ_[2]) ^ (β + 2 + 1) = 8 * 2 ^ β := by rw [pow_add, pow_add]; ring
  rw [hp2] at h
  rw [hp3, Units.val_pow_eq_pow_val]
  linear_combination (((nUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) * (1 + 4 * 2 ^ β) - 1) * h

end SharpPow

/-! ## §2 The exact-level layer witnesses on the two branch images

The range identity supplies a character preimage of the branch orientation unit; its
`2`-power powers sink into the two-central tower with sharp character level, by §1.  Three
consumer shapes are cut: the layer witness in raw form, the sharp central class in `λ_k`
(the even analogue of the L template's `stageResidual_exists_deep_zLayer_of_surjective`, with
`Function.Surjective chiCycKTwo` replaced by the range identity), and the refutation witness
in `λ_{k-1}`. -/

section Witnesses

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **The `M`-branch layer witness**: a class in `λ_{m+1}` of exact character level `m + α`. -/
theorem evenDigit_layerWitness_M {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (m : ℕ) :
    ∃ w ∈ twoCentralSeries G (m + 1),
      (2 : ℤ_[2]) ^ (m + α) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (m + α + 1) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨y, hy⟩ := evenRow_mUnit_mem_range_of_imChiM hrange
  refine ⟨y ^ 2 ^ m, pow_two_pow_mem_twoCentralSeries_succ G y m, ?_⟩
  rw [map_pow, hy]
  exact evenDigit_pow_sharp (mUnit α) (mUnit α) hα (mUnit_sub_one (by omega)) m

/-- **The `N`-branch layer witness**: a class in `λ_{m+2}` of exact character level
`m + α + 1`.  One layer behind the `M` branch, because only the square of `nUnit α` is a
principal unit. -/
theorem evenDigit_layerWitness_N {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) (m : ℕ) :
    ∃ w ∈ twoCentralSeries G (m + 2),
      (2 : ℤ_[2]) ^ (m + (α + 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (m + (α + 1) + 1) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨y, hy⟩ := evenRow_nUnit_mem_range_of_imChiN hrange
  obtain ⟨a, ha⟩ := evenDigit_nUnit_sq_eq hα
  refine ⟨y ^ 2 ^ (m + 1), pow_two_pow_mem_twoCentralSeries_succ G y (m + 1), ?_⟩
  have hsq : (nUnit α ^ 2) ^ 2 ^ m = nUnit α ^ 2 ^ (m + 1) := by
    rw [← pow_mul, show 2 * 2 ^ m = 2 ^ (m + 1) by rw [pow_succ]; ring]
  rw [map_pow, hy, ← hsq]
  exact evenDigit_pow_sharp (nUnit α ^ 2) a (by omega) ha m

/-- **The sharp central class, `M` branch.**  In `λ_k` there is a class of exact character
level `k + (α - 1)`: sharp precisely at the even filtration's own depth on `λ_k`, which is
what the fresh-digit flip of the repair engine consumes.  This replaces the L template's
`stageResidual_exists_deep_zLayer_of_surjective`, whose surjectivity input is false in even
degree. -/
theorem evenDigit_sharp_zLayer_M {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) {k : ℕ} (hk : 3 ≤ k) :
    ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨w, hwmem, h1, h2⟩ := evenDigit_layerWitness_M hα hrange (k - 1)
  rw [show k - 1 + 1 = k by omega] at hwmem
  rw [show k + (α - 1) = k - 1 + α by omega, show k + 1 + (α - 1) = k - 1 + α + 1 by omega]
  exact ⟨w, hwmem, h1, h2⟩

/-- **The sharp central class, `N` branch.** -/
theorem evenDigit_sharp_zLayer_N {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) {k : ℕ} (hk : 3 ≤ k) :
    ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨w, hwmem, h1, h2⟩ := evenDigit_layerWitness_N hα hrange (k - 2)
  rw [show k - 2 + 2 = k by omega] at hwmem
  rw [show k + (α - 1) = k - 2 + (α + 1) by omega,
    show k + 1 + (α - 1) = k - 2 + (α + 1) + 1 by omega]
  exact ⟨w, hwmem, h1, h2⟩

/-- **The refutation witness, `M` branch**: a class in `λ_{k-1}` whose character level is
exactly `k + α - 2`, one digit short of the neutralisation demand at depth `α - 1`. -/
theorem evenDigit_lambda_witness_M {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) {k : ℕ} (hk : 3 ≤ k) :
    ∃ g ∈ twoCentralSeries G (k - 1),
      ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨g, hgmem, _, h2⟩ := evenDigit_layerWitness_M hα hrange (k - 2)
  rw [show k - 2 + 1 = k - 1 by omega] at hgmem
  refine ⟨g, hgmem, ?_⟩
  rw [show k + (α - 1) = k - 2 + α + 1 by omega]
  exact h2

/-- **The refutation witness, `N` branch.** -/
theorem evenDigit_lambda_witness_N {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) {k : ℕ} (hk : 3 ≤ k) :
    ∃ g ∈ twoCentralSeries G (k - 1),
      ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨g, hgmem, _, h2⟩ := evenDigit_layerWitness_N hα hrange (k - 3)
  rw [show k - 3 + 2 = k - 1 by omega] at hgmem
  refine ⟨g, hgmem, ?_⟩
  rw [show k + (α - 1) = k - 3 + (α + 1) + 1 by omega]
  exact h2

end Witnesses

/-! ## §3 The neutral-supply verdict

The cliff.  At depths `s ≤ α - 3` the neutralisation supply is trivially true, because the
committed depth bound `evenSharp_map_le_deep` already reaches the demanded precision; from
`s = α - 2` on it is false on both branch images, by the witnesses of §2 against the W52
necessary condition.  The climb runs at `s = α - 1` (the W52 depth-necessity pin leaves the
deep row seam no slack), so the true stratum and the needed stratum do not meet: this is the
exact impasse the flip supply of §4 resolves. -/

section Verdict

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **The neutral supply holds at every depth `s ≤ α - 3`**, with the trivial central factor:
the committed depth bound on `λ_{k-1}` already reaches the demanded precision `k + 1 + s`. -/
theorem evenDigit_neutralSupply_of_depth_le {α s : ℕ} (hα : 1 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hs : s + 3 ≤ α) :
    EvenRawToNeutralSupply s G chi := by
  intro k hk p hp
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  rw [mul_one]
  obtain ⟨u, hu, hurep⟩ := hp
  have hker := evenSharp_map_le_deep hα hbound (k - 1) (by omega) ⟨u, hu, rfl⟩
  have hdvd : (2 : ℤ_[2]) ^ (k + 1 + s) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans (evenSharp_mem_ker_iff.mp hker)
  exact ⟨⟨u, hu, hurep⟩, u, hurep.symm,
    MonoidHom.mem_ker.mp (evenSharp_mem_ker_iff.mpr hdvd)⟩

/-- Consequently `Hup` is free at every depth `s ≤ α - 3`, on any word datum and value
table.  The route dies exactly two depths short of the one the climb runs at. -/
theorem evenDigit_rawToBracket_of_depth_le {α s h : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (hα : 1 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hs : s + 3 ≤ α) :
    EvenKernelRawToBracketSupply s W v G chi :=
  evenRawTo_supply_of_neutral (evenDigit_neutralSupply_of_depth_le hα hbound hs)

/-- **The `M`-branch refutation.**  On the `M` image the neutralisation supply is false at
every depth `s ≥ α - 2`: the witness of §2 has exact level `k + α - 2` on `λ_{k-1}` at
`k = 3`, while the W52 necessary condition `evenRawTo_chi_dvd_of_neutral_of_layer` propagates
the committed `λ_3` bound one layer up and demands `k + α - 1`. -/
theorem evenDigit_not_neutralSupply_M {α s : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (hs : α - 2 ≤ s) :
    ¬ EvenRawToNeutralSupply s G chi := by
  intro Hneut
  have hbound : ∀ g : G, EvenSharpPmOne α (chi g) := fun g ↦
    evenSharp_pmOne_of_mem_imChiM (by omega) (by rw [← hrange]; exact ⟨g, rfl⟩)
  obtain ⟨g, hgmem, hgsharp⟩ := evenDigit_lambda_witness_M hα hrange (le_refl 3)
  refine hgsharp ?_
  have hdvd := evenRawTo_chi_dvd_of_neutral_of_layer Hneut (le_refl 3)
    (d := 3 + (α - 1)) (by omega)
    (fun w hw ↦ by
      exact_mod_cast evenSharp_mem_ker_iff.mp
        (evenSharp_map_le_deep (by omega : 1 ≤ α) hbound 3 (by omega) ⟨w, hw, rfl⟩))
    hgmem
  exact_mod_cast hdvd

/-- **The `N`-branch refutation**, by the same mechanism. -/
theorem evenDigit_not_neutralSupply_N {α s : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) (hs : α - 2 ≤ s) :
    ¬ EvenRawToNeutralSupply s G chi := by
  intro Hneut
  have hbound : ∀ g : G, EvenSharpPmOne α (chi g) := fun g ↦
    evenSharp_pmOne_of_mem_imChiN (by omega) (by rw [← hrange]; exact ⟨g, rfl⟩)
  obtain ⟨g, hgmem, hgsharp⟩ := evenDigit_lambda_witness_N hα hrange (le_refl 3)
  refine hgsharp ?_
  have hdvd := evenRawTo_chi_dvd_of_neutral_of_layer Hneut (le_refl 3)
    (d := 3 + (α - 1)) (by omega)
    (fun w hw ↦ by
      exact_mod_cast evenSharp_mem_ker_iff.mp
        (evenSharp_map_le_deep (by omega : 1 ≤ α) hbound 3 (by omega) ⟨w, hw, rfl⟩))
    hgmem
  exact_mod_cast hdvd

/-- The natural route to `Hup` is dead at the lane's own depth, `M` branch: `s = α - 1` is in
the refuted stratum. -/
theorem evenDigit_not_neutralSupply_lane_M {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) :
    ¬ EvenRawToNeutralSupply (α - 1) G chi :=
  evenDigit_not_neutralSupply_M hα hrange (by omega)

/-- The natural route to `Hup` is dead at the lane's own depth, `N` branch. -/
theorem evenDigit_not_neutralSupply_lane_N {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) :
    ¬ EvenRawToNeutralSupply (α - 1) G chi :=
  evenDigit_not_neutralSupply_N hα hrange (by omega)

end Verdict

/-! ## §4 The digit flip supply and the repair engine

The even clone of the odd route's `SqStageHandleDigitFlipSupply`, at the even filtration's own
depth `k + (α - 1) - 1` and at every slot, in representative form so that the `Prop` carries
no side condition.  The engine turns an arbitrary raw depth correction into a neutral one with
the same literal shift word, in two passes: the flips repair the digit at `k + α - 2` slot by
slot (`Finset` induction, the order-two digit arithmetic of `evenDigit_deep_cancel`), and one
coordinatewise central correction built from the sharp class of §2 repairs the digit at
`k + α - 1`, moving no row at all. -/

section Flip

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

/-- **The even digit flip supply.**  Per level, stage, and coordinate: one raw depth
correction whose literal even shift word is trivial, whose class at that coordinate is sharp
at level `k + α - 2` (some representative escapes `k + (α - 1)` digits), and whose classes at
every other coordinate are trivial there (some representative reaches `k + (α - 1)` digits).
This is the honest one-digit residue of `Hup`: §5 proves it implies the whole raw-to-bracket
upgrade once the range identity pays for everything else. -/
def EvenDigitFlipSupply (α : ℕ) {h : ℕ} (W : StageWord (MarkedCore.coreRank h))
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (T : Tuple W v G chi k) (i₀ : Fin (MarkedCore.coreRank h)),
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1)

/-- Two sharp digits at level `n` cancel to a trivial digit at `n + 1`: the digit group of
the modification space is elementary of order two.  The arithmetic heart of both repair
passes; the L template's private `stageFlip_deep_cancel`, restated. -/
private theorem evenDigit_deep_cancel {n : ℕ} (hn : 1 ≤ n) {u w : ℤ_[2]}
    (hu : (2 : ℤ_[2]) ^ n ∣ u - 1) (hu' : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ u - 1)
    (hw : (2 : ℤ_[2]) ^ n ∣ w - 1) (hw' : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ w - 1) :
    (2 : ℤ_[2]) ^ (n + 1) ∣ u * w - 1 := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hw
  have ha2 : ¬ (2 : ℤ_[2]) ∣ a := by
    rintro ⟨e, rfl⟩
    exact hu' ⟨e, by rw [ha, pow_succ]; ring⟩
  have hb2 : ¬ (2 : ℤ_[2]) ∣ b := by
    rintro ⟨e, rfl⟩
    exact hw' ⟨e, by rw [hb, pow_succ]; ring⟩
  have hab : (2 : ℤ_[2]) ∣ a + b := by
    rw [show (2 : ℤ_[2]) = 2 ^ 1 by ring, two_pow_dvd_iff] at ha2 hb2 ⊢
    rw [map_add]
    revert ha2 hb2
    generalize PadicInt.toZModPow 1 a = x
    generalize PadicInt.toZModPow 1 b = y
    revert x y
    decide
  obtain ⟨e, he⟩ := hab
  refine ⟨e + 2 ^ (n - 1) * (a * b), ?_⟩
  have hu2 : u = 1 + 2 ^ n * a := by linear_combination ha
  have hw2 : w = 1 + 2 ^ n * b := by linear_combination hb
  have hpow : (2 : ℤ_[2]) ^ n * 2 ^ n = 2 ^ (n + 1) * 2 ^ (n - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hu2, hw2]
  linear_combination (2 : ℤ_[2]) ^ n * he + (a * b) * hpow

/-- **Representative independence of the committed depth bound.**  Any ambient representative
of a depth-`k-1` class carries `k - 1 + (α - 1)` character digits: a chosen `λ_{k-1}`
representative does by `evenSharp_map_le_deep`, and any other one differs by a `λ_{k+1}`
factor, which is two digits deeper still. -/
private theorem evenDigit_rep_dvd {α : ℕ} (hα : 1 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hk : 3 ≤ k)
    {q : levelQuot G (k + 1)} (hq : q ∈ lambdaImage G (k - 1) (k + 1))
    {g : G} (hg : q = levelMk G (k + 1) g) :
    (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨u, hu, hurep⟩ := hq
  have hrel : u⁻¹ * g ∈ twoCentralSeries G (k + 1) :=
    QuotientGroup.eq.mp (hurep.trans hg)
  have hsplit : chi g = chi u * chi (u⁻¹ * g) := by
    rw [← map_mul]
    congr 1
    group
  have h1 : (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    evenSharp_mem_ker_iff.mp (evenSharp_map_le_deep hα hbound (k - 1) (by omega) ⟨u, hu, rfl⟩)
  have h2 : (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi (u⁻¹ * g) : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans (evenSharp_mem_ker_iff.mp
      (evenSharp_map_le_deep hα hbound (k + 1) (by omega) ⟨u⁻¹ * g, hrel, rfl⟩))
  rw [hsplit, Units.val_mul]
  exact dvd_mul_sub_one h1 h2

/-- A coordinatewise central correction has literally trivial even shift word: every bracket
dies by centrality and the diagonal square dies by exponent two.  The even clone of the L
template's `sqCoreHandleDbarWord_eq_one_of_zLayer`, and the reason the second repair pass is
free. -/
theorem evenDigit_dbarWord_eq_one_of_zLayer
    (base c : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hc : ∀ i, c i ∈ zLayer G k) :
    evenRawDbarWord base c = 1 := by
  have hcomm : ∀ (i : Fin (MarkedCore.coreRank h)) (t : levelQuot G (k + 1)),
      commP (c i) t = 1 := fun i t ↦ commP_eq_one_of_mul_comm (zLayer_commute (hc i) t).eq
  have hhandle : evenRawHandleDbarWord base c = 1 := by
    rw [evenRawHandleDbarWord]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    rw [hcomm, hcomm, one_mul]
  rw [evenRawDbarWord, hhandle, mul_one, evenRawCoreDbarWord, zLayer_sq G (hc 0)]
  simp only [hcomm]
  group

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **The first repair pass.**  Multiplying by selected flips makes the character class of
every coordinate in `S` trivial one digit above the committed bound, without moving the
literal shift word: at each slot either the class is already trivial there, or the flip's
sharp digit cancels it by the order-two arithmetic, and the flip's other slots only multiply
in trivial classes. -/
private theorem evenDigit_exists_midRepair {α : ℕ} (hα : 2 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hFl : ∀ i₀ : Fin (MarkedCore.coreRank h), ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord base F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1))
    (V : EvenRawDepthCorrection G h k) (S : Finset (Fin (MarkedCore.coreRank h))) :
    ∃ C : EvenRawDepthCorrection G h k,
      evenRawDbarWord base C.correction = evenRawDbarWord base V.correction ∧
      ∀ j ∈ S, ∃ g : G, C.correction j = levelMk G (k + 1) g ∧
        (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨V, rfl, fun j hj ↦ absurd hj (by simp)⟩
  | @insert i₀ S hi₀S ih =>
    obtain ⟨C, hCword, hCS⟩ := ih
    by_cases hδ : ∃ g : G, C.correction i₀ = levelMk G (k + 1) g ∧
        (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1
    · refine ⟨C, hCword, fun j hj ↦ ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · exact hδ
      · exact hCS j hjS
    · obtain ⟨F, hFword, ⟨gd, hgd, hgdsharp⟩, hFoff⟩ := hFl i₀
      have hCF : (C * F).correction = fun i ↦ C.correction i * F.correction i := rfl
      refine ⟨C * F, ?_, ?_⟩
      · rw [hCF, evenRawDbarWord_mul h k hk base C.depth F.depth, hFword, mul_one, hCword]
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjS
        · obtain ⟨u, hu, hurep⟩ := C.depth j
          have husharp :
              ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
            fun hdvd ↦ hδ ⟨u, hurep.symm, hdvd⟩
          have hubase :
              (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
            evenDigit_rep_dvd (by omega) hbound hk (C.depth j) hurep.symm
          have hgdbase :
              (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi gd : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
            evenDigit_rep_dvd (by omega) hbound hk (F.depth j) hgd
          have hcancel : (2 : ℤ_[2]) ^ (k + (α - 1)) ∣
              ((chi u : ℤ_[2]ˣ) : ℤ_[2]) * ((chi gd : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
            have hEq : k + (α - 1) = k - 1 + (α - 1) + 1 := by omega
            rw [hEq] at husharp hgdsharp ⊢
            exact evenDigit_deep_cancel (by omega) hubase husharp hgdbase hgdsharp
          refine ⟨u * gd, ?_, ?_⟩
          · rw [hCF]
            show C.correction j * F.correction j = _
            rw [map_mul, hgd, ← hurep]
          · rw [map_mul, Units.val_mul]
            exact hcancel
        · obtain ⟨gc, hgc, hgcdvd⟩ := hCS j hjS
          obtain ⟨gf, hgf, hgfdvd⟩ := hFoff j (fun hEq ↦ hi₀S (hEq ▸ hjS))
          refine ⟨gc * gf, ?_, ?_⟩
          · rw [hCF]
            show C.correction j * F.correction j = _
            rw [map_mul, hgc, hgf]
          · rw [map_mul, Units.val_mul]
            exact dvd_mul_sub_one hgcdvd hgfdvd

/-- **The repair engine.**  Given the flips, the sharp central class, and the branch depth
bound, every raw depth correction has a *neutral* correction with the same literal shift
word: the flips repair the digit at `k + α - 2` and the central class repairs the digit at
`k + α - 1`, so every coordinate reaches the `k + 1 + (α - 1)` digits the depth-`(α - 1)`
neutral subgroup demands.  This is the even counterpart of the L template's kernel-adapted
upgrade, with `Function.Surjective chiCycKTwo` replaced by §2. -/
theorem evenDigit_exists_neutral_shift {α : ℕ} (hα : 2 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hFl : ∀ i₀ : Fin (MarkedCore.coreRank h), ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord base F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1))
    (hz : ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (V : EvenRawDepthCorrection G h k) :
    ∃ N : EvenSharpNeutralCorrection (α - 1) G chi h k,
      evenRawDbarWord base N.correction = evenRawDbarWord base V.correction := by
  classical
  obtain ⟨C, hCword, hCmid⟩ := evenDigit_exists_midRepair hα hbound hk base hFl V Finset.univ
  obtain ⟨w₀, hw₀mem, hw₀dvd, hw₀sharp⟩ := hz
  have hz₀mem : levelMk G (k + 1) w₀ ∈ zLayer G k := ⟨w₀, hw₀mem, rfl⟩
  have hchoice : ∀ j : Fin (MarkedCore.coreRank h),
      ∃ (zj : levelQuot G (k + 1)) (gj : G), zj ∈ zLayer G k ∧
        C.correction j * zj = levelMk G (k + 1) gj ∧
        (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi gj : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro j
    obtain ⟨gc, hgc, hgcdvd⟩ := hCmid j (Finset.mem_univ j)
    by_cases hfull : (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi gc : ℤ_[2]ˣ) : ℤ_[2]) - 1
    · exact ⟨1, gc, Subgroup.one_mem _, by rw [mul_one, hgc], hfull⟩
    · refine ⟨levelMk G (k + 1) w₀, gc * w₀, hz₀mem, ?_, ?_⟩
      · rw [hgc, ← map_mul]
      · rw [map_mul, Units.val_mul]
        have hEq : k + 1 + (α - 1) = k + (α - 1) + 1 := by omega
        rw [hEq] at hfull hw₀sharp ⊢
        exact evenDigit_deep_cancel (by omega) hgcdvd hfull hw₀dvd hw₀sharp
  choose zf gf hzf hrep hdvd using hchoice
  have hZdepth : ∀ j, zf j ∈ lambdaImage G (k - 1) (k + 1) := fun j ↦
    lambdaImage_le_of_le (by omega) (hzf j)
  refine ⟨{ correction := fun j ↦ C.correction j * zf j
            depth := fun j ↦ Subgroup.mul_mem _ (C.depth j) (hZdepth j)
            neutral := fun j ↦ ⟨gf j, hrep j,
              MonoidHom.mem_ker.mp (evenSharp_mem_ker_iff.mpr (hdvd j))⟩ }, ?_⟩
  show evenRawDbarWord base (fun j ↦ C.correction j * zf j) = _
  rw [evenRawDbarWord_mul h k hk base C.depth hZdepth,
    evenDigit_dbarWord_eq_one_of_zLayer base (fun j ↦ zf j) hzf, mul_one, hCword]

end Flip

/-! ## §5 `Hup` and the flips are the same statement

The engine repairs any raw correction, so the flips deliver not merely the residual instance
the climb needs but the whole span upgrade: the raw shift span *equals* the bracket span
(`evenRawTo_supply_iff_span_eq` reads the conclusion that way).  Conversely, `Hup` produces
the flips outright: seed one coordinate with a sharp class from §2, ask `Hup` for a neutral
correction with the same one-row shift, and divide it off; what remains has literally trivial
shift word, the seeded slot keeps its sharp digit because neutral coordinates cannot touch
it, and every other slot is an inverted neutral coordinate.  So on either branch image the
named input `Hup` of the per-`K` endpoints is *equivalent* to `EvenDigitFlipSupply`
(`evenDigit_rawToBracket_iff_flip_{M,N}`): the flip supply is exactly the content of `Hup`,
with the second digit and the central layer stripped away because the range identity pays
for them. -/

section Supply

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **`Hup` from the flips.**  The digit flip supply, the branch depth bound, and the sharp
central class give the full raw-to-bracket upgrade at depth `α - 1`.  Both side inputs are
theorems on either branch image (§2, and `evenSharp_pmOne_of_mem_imChi{M,N}`), so per field
the only honest content left in `Hup` is the flip supply. -/
theorem evenDigit_rawToBracket_of_flip {α h : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g))
    (hsharp : ∀ k : ℕ, 3 ≤ k → ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (Hflip : EvenDigitFlipSupply α W v G chi) :
    EvenKernelRawToBracketSupply (α - 1) W v G chi := by
  intro k hk T z hz
  obtain ⟨q, hq, rfl⟩ := hz
  obtain ⟨V, rfl⟩ := hq
  obtain ⟨N, hN⟩ := evenDigit_exists_neutral_shift hα hbound hk
    (fun i ↦ canonLift G k (T.generators i)) (Hflip k hk T) (hsharp k hk) V
  rw [← evenSharpNeutralShiftHom_range_eq_bracketSpan
    (s := α - 1) (chi := chi) (fun i ↦ canonLift G k (T.generators i)) hk]
  exact ⟨evenSharpNeutralShiftHom (fun i ↦ canonLift G k (T.generators i)) hk N,
    ⟨N, rfl⟩, hN⟩

/-- Congruence to `1` passes to the inverse unit. -/
private theorem evenDigit_dvd_inv {n : ℕ} {u : ℤ_[2]ˣ}
    (h : (2 : ℤ_[2]) ^ n ∣ ((u : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    (2 : ℤ_[2]) ^ n ∣ ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨c, hc⟩ := h
  have huu : ((u : ℤ_[2]ˣ) : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact ⟨-(((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * c), by
    linear_combination (-((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * hc + huu⟩

/-- A sharp digit is preserved by multiplication with a trivial one. -/
private theorem evenDigit_ndvd_mul {n : ℕ} {u w : ℤ_[2]}
    (hu : ¬ (2 : ℤ_[2]) ^ n ∣ u - 1) (hw : (2 : ℤ_[2]) ^ n ∣ w - 1) :
    ¬ (2 : ℤ_[2]) ^ n ∣ u * w - 1 := by
  intro hd
  refine hu ?_
  have hsplit : u - 1 = (u * w - 1) - u * (w - 1) := by ring
  rw [hsplit]
  exact dvd_sub hd (hw.mul_left u)

/-- **The flips from `Hup`.**  Given one sharp seed class in `λ_{k-1}` per level, the
raw-to-bracket upgrade produces the flip supply: seed a one-coordinate correction, obtain a
neutral correction with the same literal shift, and divide it off.  Together with
`evenDigit_rawToBracket_of_flip` this makes the reduction an equivalence, so nothing is
given away in the re-cut. -/
theorem evenDigit_flip_of_rawToBracket {α h : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (hseed : ∀ k : ℕ, 3 ≤ k → ∃ g ∈ twoCentralSeries G (k - 1),
      ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (Hup : EvenKernelRawToBracketSupply (α - 1) W v G chi) :
    EvenDigitFlipSupply α W v G chi := by
  intro k hk T i₀
  obtain ⟨gs, hgsmem, hgssharp⟩ := hseed k hk
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  have hp : levelMk G (k + 1) gs ∈ lambdaImage G (k - 1) (k + 1) := ⟨gs, hgsmem, rfl⟩
  set coord : EvenRawDepthCorrection G h k :=
    evenRawDepthCoordinateCorrection i₀ ⟨levelMk G (k + 1) gs, hp⟩ with hcoord
  have hrow : ((evenRawDepthShiftHom base hk) coord).1 ∈ evenBracketSpan (α - 1) chi base :=
    Hup k hk T _ (evenRawDepthShift_mem_shiftSpan base hk coord)
  rw [← evenSharpNeutralShiftHom_range_eq_bracketSpan (s := α - 1) (chi := chi) base hk]
    at hrow
  obtain ⟨q, ⟨N, rfl⟩, hval⟩ := hrow
  have hNword : (evenRawDepthShiftHom base hk) (EvenSharpNeutralCorrection.toRawHom N) =
      (evenRawDepthShiftHom base hk) coord := Subtype.ext hval
  have hinvc : ∀ (V : EvenRawDepthCorrection G h k) (j : Fin (MarkedCore.coreRank h)),
      (V⁻¹).correction j = (V.correction j)⁻¹ := fun V j ↦ rfl
  have hNdvd : ∀ j : Fin (MarkedCore.coreRank h), ∃ gN : G,
      N.correction j = levelMk G (k + 1) gN ∧
        (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi gN : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro j
    obtain ⟨gN, hgN, hgNmap⟩ := N.neutral j
    exact ⟨gN, hgN, (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans
      (evenSharp_mem_ker_iff.mp (MonoidHom.mem_ker.mpr hgNmap))⟩
  refine ⟨coord * (EvenSharpNeutralCorrection.toRawHom N)⁻¹, ?_, ?_, ?_⟩
  · have hword : (evenRawDepthShiftHom base hk)
        (coord * (EvenSharpNeutralCorrection.toRawHom N)⁻¹) = 1 := by
      rw [map_mul, map_inv, hNword, mul_inv_cancel]
    exact congrArg Subtype.val hword
  · obtain ⟨gN, hgN, hgNdvd⟩ := hNdvd i₀
    refine ⟨gs * gN⁻¹, ?_, ?_⟩
    · rw [EvenRawDepthCorrection.mul_correction, hinvc, map_mul, map_inv,
        EvenSharpNeutralCorrection.toRawHom_correction, hgN, hcoord,
        evenRawDepthCoordinateCorrection_apply, if_pos rfl]
    · rw [map_mul, map_inv, Units.val_mul]
      exact evenDigit_ndvd_mul hgssharp (evenDigit_dvd_inv hgNdvd)
  · intro j hj
    obtain ⟨gN, hgN, hgNdvd⟩ := hNdvd j
    refine ⟨gN⁻¹, ?_, ?_⟩
    · rw [EvenRawDepthCorrection.mul_correction, hinvc, map_inv,
        EvenSharpNeutralCorrection.toRawHom_correction, hgN, hcoord,
        evenRawDepthCoordinateCorrection_apply, if_neg hj, one_mul]
    · rw [map_inv]
      exact evenDigit_dvd_inv hgNdvd

/-- **`Hup` is the flip supply, `M` branch**: on the `M` image the raw-to-bracket upgrade at
depth `α - 1` and the digit flip supply are equivalent.  The re-cut of §7 loses nothing. -/
theorem evenDigit_rawToBracket_iff_flip_M {α h : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) :
    EvenKernelRawToBracketSupply (α - 1) W v G chi ↔ EvenDigitFlipSupply α W v G chi :=
  ⟨fun Hup ↦ evenDigit_flip_of_rawToBracket
      (fun _k hk ↦ evenDigit_lambda_witness_M hα hrange hk) Hup,
    fun Hflip ↦ evenDigit_rawToBracket_of_flip hα
      (fun g ↦ evenSharp_pmOne_of_mem_imChiM (by omega) (by rw [← hrange]; exact ⟨g, rfl⟩))
      (fun _k hk ↦ evenDigit_sharp_zLayer_M hα hrange hk) Hflip⟩

/-- **`Hup` is the flip supply, `N` branch.** -/
theorem evenDigit_rawToBracket_iff_flip_N {α h : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) :
    EvenKernelRawToBracketSupply (α - 1) W v G chi ↔ EvenDigitFlipSupply α W v G chi :=
  ⟨fun Hup ↦ evenDigit_flip_of_rawToBracket
      (fun _k hk ↦ evenDigit_lambda_witness_N hα hrange hk) Hup,
    fun Hflip ↦ evenDigit_rawToBracket_of_flip hα
      (fun g ↦ evenSharp_pmOne_of_mem_imChiN (by omega) (by rw [← hrange]; exact ⟨g, rfl⟩))
      (fun _k hk ↦ evenDigit_sharp_zLayer_N hα hrange hk) Hflip⟩

end Supply

/-! ## §6 The constructed flip at coordinate `2`

The one slot where the flip is a theorem.  The row of coordinate `2` is the cross bracket
`[p, base 3]` (`evenRawDepthShiftHom_two_apply`), so a power of `base 3` itself has literally
trivial row; and when the table value at index `3` has exact level `α`, the `2^(k-2)`-th power
has exact character level `k + α - 2` by §1, which is precisely the sharp digit the flip
demands.  The `M` table has `v 3 = mUnit α`, of exact level `α`; the `N` table has `1` at
every bracket partner of every squarefree row, so no slot of the `N` flip supply is
constructible this way, and the `M` slots `0, 1, 3` and the handles are likewise carried:
their partners' table values are `1` (slot `0` in addition carries the diagonal square, which
no partner power kills). -/

section SlotTwo

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

/-- **The flip at coordinate `2`, from a sharp table value at index `3`.**  Generic in the
word datum and the table: all it uses is the exact level of `v 3` and the exact fibre of the
tuple's row `3`. -/
theorem evenDigit_flip_two_of_sharp_value {α : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (a : ℤ_[2]ˣ)
    (hv3 : ((v 3 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ α * (a : ℤ_[2]))
    (hk : 3 ≤ k) (T : Tuple W v G chi k) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction 2 = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ 2 →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  obtain ⟨x, hxchi, hxrep⟩ := T.rows 3
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  have hpmem : base 3 ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) := by
    have hmem := pow_two_pow_mem_lambdaImage (base 3) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at hmem
  refine ⟨evenRawDepthCoordinateCorrection 2 ⟨base 3 ^ 2 ^ (k - 2), hpmem⟩, ?_, ?_, ?_⟩
  · have happ := evenRawDepthShiftHom_two_apply base hk ⟨base 3 ^ 2 ^ (k - 2), hpmem⟩
    have hcomm : commP (base 3 ^ 2 ^ (k - 2)) (base 3) = 1 :=
      commP_eq_one_of_mul_comm ((Commute.refl (base 3)).pow_left (2 ^ (k - 2))).eq
    exact happ.trans hcomm
  · refine ⟨x ^ 2 ^ (k - 2), ?_, ?_⟩
    · rw [evenRawDepthCoordinateCorrection_apply, if_pos rfl]
      have hb3 : base 3 = canonLift G k (levelMk G k x) := by
        rw [show base 3 = canonLift G k (T.generators 3) from rfl, hxrep]
      have h1 : base 3 ^ 2 = levelMk G (k + 1) x ^ 2 := by
        rw [hb3]
        exact (sq_levelMk_eq_sq_canonLift G k x).symm
      have hsplit : (2 : ℕ) * 2 ^ (k - 3) = 2 ^ (k - 2) := by
        rw [show k - 2 = k - 3 + 1 by omega, pow_succ']
      show base 3 ^ 2 ^ (k - 2) = levelMk G (k + 1) (x ^ 2 ^ (k - 2))
      calc base 3 ^ 2 ^ (k - 2) = (base 3 ^ 2) ^ 2 ^ (k - 3) := by rw [← pow_mul, hsplit]
        _ = (levelMk G (k + 1) x ^ 2) ^ 2 ^ (k - 3) := by rw [h1]
        _ = levelMk G (k + 1) (x ^ 2 ^ (k - 2)) := by rw [← pow_mul, hsplit, ← map_pow]
    · rw [map_pow, hxchi, show k + (α - 1) = k - 2 + α + 1 by omega]
      exact (evenDigit_pow_sharp (v 3) a hα hv3 (k - 2)).2
  · intro j hj
    refine ⟨1, ?_, ?_⟩
    · rw [evenRawDepthCoordinateCorrection_apply, if_neg hj, map_one]
    · rw [map_one, Units.val_one]
      simp

/-- **The `M`-branch flip at coordinate `2` is a theorem**: `vM α 3 = mUnit α` has exact
level `α` by `mUnit_sub_one`.  One of the `4 + 2h` slots of the `M` flip supply is thereby
discharged; a future re-cut of `EvenDigitFlipSupply` can drop it from the carried set. -/
theorem evenDigit_flipSlotTwo_M {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α} (hk : 3 ≤ k)
    (T : Tuple (mStageWord α h hα₁) (vM α) G chi k) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction 2 = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ 2 →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) :=
  evenDigit_flip_two_of_sharp_value hα (mUnit α)
    (by rw [vM_three]; exact mUnit_sub_one (by omega)) hk T

end SlotTwo

/-! ## §7 The per-`K` endpoints, re-cut at the flips

The endpoints of `StageAbstractionEvenPerK.lean` §6 with the raw-to-bracket input replaced by
the flip supply.  Two per-field bridge theorems turn the flips into the `Hup` instance at the
branch depth the range identity produces, discharging the depth bound and the sharp central
class from the pinned image; the endpoints then run the committed chain unchanged.  The
refutation is recorded per field alongside, so the file states both halves of the trade: what
could never be supplied, and what replaces it. -/

section PerK

open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.EvenForward

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The coefficient action at `G_K(2)`, as on the whole route: the unique action on `𝔽₂`.
Local, exactly as in `StageAbstractionEvenPerK.lean`, for the `κ ≠ 0` binders of the `α = 2`
stratum endpoints. -/
local instance evenDigitScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenDigitContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The flip supply at one field, `N` branch**, quantified over the branch depth exactly as
the carried inputs of `StageAbstractionEvenPerK.lean` §5 are, since `α` is produced by the
range identity rather than chosen. -/
def EvenPerKNDigitFlip (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha),
    EvenDigitFlipSupply alpha (nStageWord alpha h halpha) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

/-- **The flip supply at one field, `M` branch.** -/
def EvenPerKMDigitFlip (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha),
    EvenDigitFlipSupply alpha (mStageWord alpha h halpha) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The per-field `Hup` instance from the flips, `N` branch.**  The depth bound and the
sharp central class are discharged from the pinned image. -/
theorem evenDigit_perKRawToBracketN {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (Hflip : EvenDigitFlipSupply alpha (nStageWord alpha h (Nat.le_of_succ_le halpha))
      (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenKernelRawToBracketSupply (alpha - 1) (nStageWord alpha h (Nat.le_of_succ_le halpha))
      (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenDigit_rawToBracket_of_flip halpha
    (fun g ↦ evenSharp_pmOne_of_mem_imChiN (by omega)
      (by rw [← hrange]; exact ⟨g, rfl⟩))
    (fun _k hk ↦ evenDigit_sharp_zLayer_N halpha hrange hk) Hflip

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The per-field `Hup` instance from the flips, `M` branch.** -/
theorem evenDigit_perKRawToBracketM {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (Hflip : EvenDigitFlipSupply alpha (mStageWord alpha h (Nat.le_of_succ_le halpha))
      (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenKernelRawToBracketSupply (alpha - 1) (mStageWord alpha h (Nat.le_of_succ_le halpha))
      (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenDigit_rawToBracket_of_flip halpha
    (fun g ↦ evenSharp_pmOne_of_mem_imChiM (by omega)
      (by rw [← hrange]; exact ⟨g, rfl⟩))
    (fun _k hk ↦ evenDigit_sharp_zLayer_M halpha hrange hk) Hflip

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The neutral route is dead at one field, `N` branch: the supersession record for
`EvenPerKNRawToBracket`'s only committed discharge route. -/
theorem evenDigit_perK_not_neutralN {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha) :
    ¬ EvenRawToNeutralSupply (alpha - 1) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) :=
  evenDigit_not_neutralSupply_lane_N halpha hrange

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The neutral route is dead at one field, `M` branch. -/
theorem evenDigit_perK_not_neutralM {alpha : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    ¬ EvenRawToNeutralSupply (alpha - 1) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) :=
  evenDigit_not_neutralSupply_lane_M halpha hrange

/-- **The even `N` endpoint at the flips, per field.**  `evenPerK_orientedEquivN` with the
raw-to-bracket input `Hup` replaced by the one-digit flip supply; everything else is
unchanged, and the two side inputs of the reduction are discharged from the range identity
at the produced depth. -/
theorem evenDigit_orientedEquivN {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hbase : EvenPerKNStageBase h K) (Hfam : EvenPerKNFamilySupply h K)
    (Hflip : EvenPerKNDigitFlip h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  obtain ⟨base⟩ := Hbase alpha (Nat.le_of_succ_le halpha)
  exact ⟨alpha, halpha, nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_nModelDemushkin alpha h halpha)
    (evenPerK_forwardGeneratorDataN halpha hrange base
      (Hfam alpha (Nat.le_of_succ_le halpha))
      (evenDigit_perKRawToBracketN halpha hrange
        (Hflip alpha (Nat.le_of_succ_le halpha))))⟩

/-- **The even `M` endpoint at the flips, per field.** -/
theorem evenDigit_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hbase : EvenPerKMStageBase h K) (Hfam : EvenPerKMFamilySupply h K)
    (Hflip : EvenPerKMDigitFlip h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  obtain ⟨base⟩ := Hbase alpha (Nat.le_of_succ_le halpha)
  exact ⟨alpha, halpha, nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_mModelDemushkin alpha h halpha)
    (evenPerK_forwardGeneratorDataM halpha hrange base
      (Hfam alpha (Nat.le_of_succ_le halpha))
      (evenDigit_perKRawToBracketM halpha hrange
        (Hflip alpha (Nat.le_of_succ_le halpha))))⟩

/-- **The `N` endpoint on the `α = 2` stratum at the flips**: the level-three base is built
by `evenPerK_stageBaseN_two`, so only `Hfam` and the flips are carried.  This is the layer's
sharpest non-vacuity statement: on this stratum the even route owes exactly the odd route's
two inputs, with the raw-to-bracket half reduced to one digit per slot. -/
theorem evenDigit_orientedEquivN_two {R : LocalReciprocity} (B : MarkedRecip R K)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 2 h one_le_two) (vN 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupply 2 (nStageWord 2 h one_le_two) (vN 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 h) (chiCycKTwo (K := K))) :=
  evenPerK_orientedEquivN_two B hkappa hrange h hev Hfam
    (evenDigit_perKRawToBracketN (le_refl 2) hrange Hflip)

/-- **The `M` endpoint on the `α = 2` stratum at the flips.** -/
theorem evenDigit_orientedEquivM_two {R : LocalReciprocity} (B : MarkedRecip R K)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord 2 h one_le_two) (vM 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupply 2 (mStageWord 2 h one_le_two) (vM 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 h) (chiCycKTwo (K := K))) :=
  evenPerK_orientedEquivM_two B hkappa hrange h hev Hfam
    (evenDigit_perKRawToBracketM (le_refl 2) hrange Hflip)

end PerK

end

end GQ2.Dyadic.StageGeneric

/-! ## §8 Axiom pins

Every public declaration of this file, printed.  §1 to §6 are arithmetic and span statements
over an abstract character and must stay at std-3, `[propext, Classical.choice, Quot.sound]`.
§7 reaches the field layer through the committed endpoints, so its endpoint theorems acquire
exactly the census axioms of `evenPerK_orientedEquiv{N,M}` and `evenPerK_orientedEquiv{N,M}_two`
(the marked reciprocity clauses of the range identity, the level-three base at `α = 2`, and
`absGalQ2_isTopologicallyFinitelyGenerated`); the bridge theorems
`evenDigit_perKRawToBracket{N,M}` and the per-field refutations stay at std-3.  No axiom of
this file is new. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 sharp two-adic powering
#print axioms evenDigit_pow_sharp
#print axioms evenDigit_nUnit_sq_eq

-- §2 the layer witnesses
#print axioms evenDigit_layerWitness_M
#print axioms evenDigit_layerWitness_N
#print axioms evenDigit_sharp_zLayer_M
#print axioms evenDigit_sharp_zLayer_N
#print axioms evenDigit_lambda_witness_M
#print axioms evenDigit_lambda_witness_N

-- §3 the neutral-supply verdict
#print axioms evenDigit_neutralSupply_of_depth_le
#print axioms evenDigit_rawToBracket_of_depth_le
#print axioms evenDigit_not_neutralSupply_M
#print axioms evenDigit_not_neutralSupply_N
#print axioms evenDigit_not_neutralSupply_lane_M
#print axioms evenDigit_not_neutralSupply_lane_N

-- §4 the flip supply and the repair engine
#print axioms EvenDigitFlipSupply
#print axioms evenDigit_dbarWord_eq_one_of_zLayer
#print axioms evenDigit_exists_neutral_shift

-- §5 `Hup` and the flips are the same statement
#print axioms evenDigit_rawToBracket_of_flip
#print axioms evenDigit_flip_of_rawToBracket
#print axioms evenDigit_rawToBracket_iff_flip_M
#print axioms evenDigit_rawToBracket_iff_flip_N

-- §6 the constructed flip at coordinate `2`
#print axioms evenDigit_flip_two_of_sharp_value
#print axioms evenDigit_flipSlotTwo_M

-- §7 the per-`K` endpoints, with the two local coefficient-action instances
#print axioms evenDigitScalar
#print axioms evenDigitContinuousScalar
#print axioms EvenPerKNDigitFlip
#print axioms EvenPerKMDigitFlip
#print axioms evenDigit_perKRawToBracketN
#print axioms evenDigit_perKRawToBracketM
#print axioms evenDigit_perK_not_neutralN
#print axioms evenDigit_perK_not_neutralM
#print axioms evenDigit_orientedEquivN
#print axioms evenDigit_orientedEquivM
#print axioms evenDigit_orientedEquivN_two
#print axioms evenDigit_orientedEquivM_two

end AxiomPins
