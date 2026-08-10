/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFlip

/-!
# W56-SLOTZERO: the flip at the diagonal coordinate is refuted at **every** branch depth

## Headline

Wave 55 (`StageAbstractionEvenFlip.lean`) reduced the even route's whole flip demand to the
single diagonal coordinate `0` on both branches, and refuted that coordinate at `α = 2`.  It
recorded what coordinate `0` still needed at `α ≥ 3`: *a depth-`(k-1)` class whose square is a
product of commutators and whose character level lies in `[k+1, k+α-2]` - a range nonempty
precisely when `α ≥ 3`.*  This lane was dispatched to produce such a class.

**No such class exists, at any `α`.**  The range is nonempty as a range of integers, but the
character values available on `λ_{k-1}` do not meet it.  The reason is a bound the campaign
already owned and had not applied here: the *range-refined* depth bound
`evenSharp_map_le_deep` of `StageAbstractionEvenRowSupply.lean` §5.1, which for a character
with values `≡ ±1 (mod 2^α)` pins

  `χ(λ_m G) ⊆ 1 + 2^(m+α-1) ℤ₂`   for every `m ≥ 2`.

Wave 55's `evenFlip_slotZero_digit` used instead the *generic* bound
`dvd_chi_of_mem_twoCentralSeries`, which knows nothing about `α` and only gives
`χ(λ_m G) ⊆ 1 + 2^(m+1) ℤ₂`.  At `α = 2` the two agree, which is exactly why wave 55's
refutation stopped there.

With the refined bound the same two-step argument closes at every `α`:

* the coordinate has depth `k-1`, so `χ(g) ≡ 1 (mod 2^(k+α-2))` (`evenSlotZero_depth_boundary`);
* the coordinate's square is a product of commutators (wave 55's
  `evenFlip_slotZero_sq_mem_commutator`), so `χ(g)²` is the character of a `λ_{k+1}` element and
  `χ(g)² ≡ 1 (mod 2^(k+α))`;
* squaring an element of `1 + 2^j ℤ₂` with `j ≥ 2` moves the level up by *exactly* one
  (`evenSlotZero_step`), so `χ(g) ≡ 1 (mod 2^(k+α-1))`.

The flip demands `¬ 2^(k+(α-1)) ∣ χ(g) - 1`, which is the negation.  So

**`EvenDigitFlipSupplySlotZero α W v G chi` is false for every `α ≥ 2`, on every row table, as
soon as one stage tuple exists and the character's values are `≡ ±1 (mod 2^α)`**
(`evenSlotZero_not_slotZeroSupply`).  Both even images satisfy that: the range identity gives it
verbatim (`evenSharp_pmOne_of_mem_imChiM`, `evenSharp_pmOne_of_mem_imChiN`).

## Why the boundary is where it is

The two facts sit one digit apart, and nothing about the row table moves them.

* Every class of `λ_{k-1}` has character level `≥ k+α-2` (`evenSlotZero_depth_boundary`).
* The flip's sharpness demand is level `≤ k+α-2`.

So at a *nonzero* coordinate the demand is met exactly at the boundary, and wave 55's
constructions do meet it there: `evenFlip_flip_of_partner` and `evenFlip_flip_of_diagonal` place
`base i ^ 2^(k-2)`, whose level is exactly `k+α-2`.  Coordinate `0` is the one coordinate whose
row carries a *square*, and a square costs exactly one digit.  One digit is the entire margin.

That is also why no re-cut of the flip helps.  The obstruction is not the choice of table, nor
the choice of correction, nor the paired/diagonal move: it is that the tower's `λ_{k-1}` is
*saturated* against the sharp filtration at `α`, a fact the campaign already met twice - it is
the same one-digit shortfall that refuted `RowExactLevelFibreLiftSupply` at `α ≥ 3`
(`evenSharp_not_imageRelLe_imChiM`) and that the `M` frame had to pay for with the depth class
(`StageAbstractionEvenFrameDeep.lean`).

## What the even route carries after this lane

| statement | flip input | status |
| --- | --- | --- |
| `evenDigit_orientedEquiv{N,M}` (W53) | all slots, all `α ≥ 2` | false |
| `evenEndpoint_orientedEquiv{N,M}` (W54) | all slots, all `α ≥ 2` | false |
| `evenFlip_orientedEquiv{N,M}_atDepth` (W55) | slot `0`, at the produced depth | **false** |
| `evenFlip_orientedEquiv{N,M}_atDepth_deep` (W55) | slot `0`, at depths `α ≥ 3` | **false** |

Every even endpoint that passes through a flip now has an unsatisfiable hypothesis set as soon
as its range identity holds and one stage tuple exists (§4).  `Hup` itself is false at every
`α ≥ 2` on both branches (`evenSlotZero_not_rawToBracket_{M,N}`), by wave 53's equivalence.  The
even route as architected does not reach any stratum through flips; what it needs is a mechanism
that does not ask for a sharp digit at the diagonal coordinate at all.

## Certificates

`scripts/w56_slotzero/slotzero_model.g` builds the honest even relator group of rank `4 + 2h`
(`MarkedCore.mWord` / `MarkedCore.nWord` verbatim), its level-`k` two-quotient `Q = G/λ_{k+1}`
by the `p`-quotient algorithm, and the cyclotomic character into `(ℤ/2^(k+α))^×`; every row
functional is verified to be `GF(2)`-linear on `λ_{k-1}/λ_{k-1}²`, and the flip demand at each
coordinate is then decided exactly as one `GF(2)` linear feasibility problem.  In all twelve
cases run (both branches, `α ∈ {2,3,4,5}`, `k ∈ {3,4}`, `h ∈ {0,1}`, quotients up to `2^110`)
**coordinate `0` is refuted and every other coordinate is supplied**, which reproduces wave 55's
`evenFlip_flipOffZero_{M,N}` and this file's refutation side by side.  The transcript records the
depth bound holding level by level and the mechanism `p² ∈ [Q,Q] ⇒ p` deep.  Output in
`results/w56_slotzero_model.txt`.

`scripts/w56_slotzero/step.py` checks §1 exhaustively, checks that its hypothesis `j ≥ 2` is
sharp, checks the collision of §2 over all residues for `3 ≤ k ≤ 7`, `2 ≤ α ≤ 7`, and checks
that the nonzero coordinates' witness `mUnit α ^ 2^(k-2)` has level *exactly* `k+α-2`, so that
the entire margin is the one digit the slot-`0` square costs.  Output in
`results/w56_slotzero_step.txt`.

## Numbering

1. the two-adic step at an arbitrary index;
2. the refined slot-`0` digit, and the depth boundary it sits against;
3. the refutations: the reduced supply, the full supply, and `Hup`, per branch;
4. the per-field inputs and the endpoints that consume them;
5. axiom pins.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenRowSupply

/-! ## §1 The two-adic step, at an arbitrary index

Wave 55's `evenFlip_two_adic_step` is this at the single index `k`, which is all `α = 2` needs.
The general index is what carries the refined depth bound. -/

section TwoAdic

/-- **Squaring moves the two-adic level up by exactly one.**  If `t ≡ 1 (mod 2^j)` with `j ≥ 2`
and `t² ≡ 1 (mod 2^(j+2))`, then already `t ≡ 1 (mod 2^(j+1))`: writing `t - 1 = 2^j u`,
`t² - 1 = 2^(j+1) · u · (1 + 2^(j-1) u)` and the second factor is odd. -/
theorem evenSlotZero_step {j : ℕ} (hj : 2 ≤ j) {t : ℤ_[2]}
    (h1 : (2 : ℤ_[2]) ^ j ∣ t - 1) (h2 : (2 : ℤ_[2]) ^ (j + 2) ∣ t * t - 1) :
    (2 : ℤ_[2]) ^ (j + 1) ∣ t - 1 := by
  obtain ⟨u, hu⟩ := h1
  have ht : t = 1 + 2 ^ j * u := by linear_combination hu
  have hfac : t * t - 1 = 2 ^ (j + 1) * (u * (2 ^ (j - 1) * u + 1)) := by
    have hjj : (2 : ℤ_[2]) ^ j = 2 ^ (j - 1) * 2 := by
      rw [← pow_succ, show j - 1 + 1 = j by omega]
    rw [ht, show (2 : ℤ_[2]) ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ], hjj]
    ring
  have hcancel : (2 : ℤ_[2]) ∣ u * (2 ^ (j - 1) * u + 1) := by
    rw [hfac, show j + 2 = j + 1 + 1 by omega, pow_succ] at h2
    exact (mul_dvd_mul_iff_left (a := (2 : ℤ_[2]) ^ (j + 1))
      (pow_ne_zero _ two_ne_zero)).mp h2
  have hu2 : (2 : ℤ_[2]) ∣ u := by
    have hdiff : u * (2 ^ (j - 1) * u + 1) - u = 2 * (2 ^ (j - 2) * u * u) := by
      have hjj : (2 : ℤ_[2]) ^ (j - 1) = 2 * 2 ^ (j - 2) := by
        rw [← pow_succ', show j - 2 + 1 = j - 1 by omega]
      rw [hjj]
      ring
    have := dvd_sub hcancel (Dvd.intro _ hdiff.symm)
    simpa using this
  obtain ⟨w, hw⟩ := hu2
  exact ⟨w, by rw [hu, hw, pow_succ]; ring⟩

end TwoAdic

/-! ## §2 The refined slot-`0` digit -/

section SlotZero

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k α : ℕ}

/-- A representative of a depth-`(k-1)` class lies in `λ_{k-1}` (wave 55's `evenFlip_rep_mem`,
which is private there). -/
private theorem evenSlotZero_rep_mem {q : levelQuot G (k + 1)}
    (hq : q ∈ lambdaImage G (k - 1) (k + 1)) {g : G} (hg : q = levelMk G (k + 1) g) :
    g ∈ twoCentralSeries G (k - 1) := by
  obtain ⟨w, hw, hwq⟩ := hq
  have hker : g * w⁻¹ ∈ twoCentralSeries G (k + 1) := by
    have : levelMk G (k + 1) (g * w⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hg, hwq, mul_inv_cancel]
    rwa [levelMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hle : twoCentralSeries G (k + 1) ≤ twoCentralSeries G (k - 1) :=
    twoCentralSeries_antitone G (by omega)
  have := Subgroup.mul_mem _ (hle hker) hw
  simpa using this

omit [IsTopologicalGroup G] in
/-- A character kills the commutator subgroup (wave 55's `evenFlip_chi_commutator`, private
there). -/
private theorem evenSlotZero_chi_commutator {y : G} (hy : y ∈ commutator G) : chi y = 1 := by
  have hle : commutator G ≤ (chi.toMonoidHom).ker := by
    rw [commutator_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨g₁, g₂, rfl⟩
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    exact mul_inv_eq_one.mpr (by rw [mul_comm]; group)
  exact hle hy

/-- **The depth boundary.**  For a character whose values are `≡ ±1 (mod 2^α)`, every element of
`λ_{k-1}` already has character level `≥ k+α-2`.  The flip's sharpness demand at a coordinate is
level `≤ k+α-2`, so the demand at a *nonzero* coordinate sits exactly on this boundary - and
wave 55's constructions meet it there, placing `base i ^ 2^(k-2)`, of level exactly `k+α-2`.
There is no margin. -/
theorem evenSlotZero_depth_boundary (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) {g : G}
    (hg : g ∈ twoCentralSeries G (k - 1)) :
    (2 : ℤ_[2]) ^ (k + α - 2) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have hd := evenSharp_map_le_deep (chi := chi) (by omega : 1 ≤ α) hbound (k - 1) (by omega)
    (Subgroup.mem_map_of_mem _ hg)
  rw [evenSharp_mem_ker_iff] at hd
  rwa [show k - 1 + (α - 1) = k + α - 2 by omega] at hd

/-- **The slot-`0` digit, refined by the range.**  A correction with literally trivial shift word
has `correction 0 ^ 2` in the commutator subgroup (wave 55's
`evenFlip_slotZero_sq_mem_commutator`), so a representative `g` of that coordinate has
`χ(g)²` equal to the character of a `λ_{k+1}` element; the refined depth bound makes that
`≡ 1 (mod 2^(k+α))`, and the coordinate's own depth makes `χ(g) ≡ 1 (mod 2^(k+α-2))`.  §1 then
forces `χ(g) ≡ 1 (mod 2^(k+α-1))`, which is exactly the negation of the flip's demand.

At `α = 2` this is wave 55's `evenFlip_slotZero_digit`; the content is that it holds at every
`α`, because the depth bound the campaign proved in `StageAbstractionEvenRowSupply.lean` is
`α` digits deeper than the generic one wave 55 used. -/
theorem evenSlotZero_digit (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g))
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (F : EvenRawDepthCorrection G h k)
    (hrow : evenRawDbarWord base F.correction = 1) {g : G}
    (hg : F.correction 0 = levelMk G (k + 1) g) :
    (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  -- the coordinate has depth `k-1`
  have hgmem : g ∈ twoCentralSeries G (k - 1) := evenSlotZero_rep_mem (F.depth 0) hg
  have h1 : (2 : ℤ_[2]) ^ (k + α - 2) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    evenSlotZero_depth_boundary hα hk hbound hgmem
  -- the square is a product of commutators
  have hsq := evenFlip_slotZero_sq_mem_commutator base F.correction hrow
  have hmapc : commutator (levelQuot G (k + 1)) =
      Subgroup.map (levelMk G (k + 1)) (commutator G) := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (levelMk_surjective G (k + 1))]
  rw [hmapc, hg, ← map_pow] at hsq
  obtain ⟨y, hy, hyeq⟩ := hsq
  have hker : g ^ 2 * y⁻¹ ∈ twoCentralSeries G (k + 1) := by
    have : levelMk G (k + 1) (g ^ 2 * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hyeq, mul_inv_cancel]
    rwa [levelMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have h2 : (2 : ℤ_[2]) ^ (k + α - 2 + 2) ∣
      ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hchiy : chi.toMonoidHom y = 1 := evenSlotZero_chi_commutator hy
    have hd := evenSharp_map_le_deep (chi := chi) (by omega : 1 ≤ α) hbound (k + 1) (by omega)
      (Subgroup.mem_map_of_mem _ hker)
    rw [evenSharp_mem_ker_iff] at hd
    rw [map_mul, map_inv, map_pow, hchiy, inv_one, mul_one] at hd
    rw [show k + 1 + (α - 1) = k + α - 2 + 2 by omega] at hd
    rwa [Units.val_pow_eq_pow_val, sq] at hd
  have hstep := evenSlotZero_step (j := k + α - 2) (by omega) h1 h2
  rwa [show k + α - 2 + 1 = k + (α - 1) by omega] at hstep

/-! ## §3 The refutations -/

/-- **The reduced flip supply is FALSE at every branch depth `α ≥ 2`**, on every row table, as
soon as one stage tuple exists and the character's values are `≡ ±1 (mod 2^α)`.  This is the
lane's headline: wave 55's `evenFlip_not_slotZeroSupply_two` with the `α = 2` restriction
removed. -/
theorem evenSlotZero_not_slotZeroSupply {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (T : Tuple W v G chi k) :
    ¬ EvenDigitFlipSupplySlotZero α W v G chi := by
  intro H
  obtain ⟨F, hrow, ⟨g, hg, hsharp⟩, -⟩ := H k hk T
  exact hsharp (evenSlotZero_digit hα hk hbound _ F hrow hg)

/-- **The full flip supply is FALSE at every branch depth `α ≥ 2`.**  Wave 55 proved the full
supply equivalent to its slot-`0` restriction on both even tables; here the full supply is
refuted directly, since it contains the slot-`0` demand. -/
theorem evenSlotZero_not_flipSupply {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (T : Tuple W v G chi k) :
    ¬ EvenDigitFlipSupply α W v G chi := fun H ↦
  evenSlotZero_not_slotZeroSupply hα hk hbound T (evenFlip_slotZero_of_flip H)

/-! ### §3.1 The two branches, from the range identity -/

omit [IsTopologicalGroup G] in
/-- The `M` image gives the `±1` bound the digit consumes. -/
theorem evenSlotZero_bound_M (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (g : G) :
    EvenSharpPmOne α (chi g) :=
  evenSharp_pmOne_of_mem_imChiM (by omega) (by rw [← hrange]; exact ⟨g, rfl⟩)

omit [IsTopologicalGroup G] in
/-- The `N` image gives the `±1` bound the digit consumes. -/
theorem evenSlotZero_bound_N (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) (g : G) :
    EvenSharpPmOne α (chi g) :=
  evenSharp_pmOne_of_mem_imChiN (by omega) (by rw [← hrange]; exact ⟨g, rfl⟩)

/-- **`M` branch: the flip supply is false at every `α ≥ 2`.** -/
theorem evenSlotZero_not_flipSupply_M {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (T : Tuple W v G chi k) :
    ¬ EvenDigitFlipSupply α W v G chi :=
  evenSlotZero_not_flipSupply hα hk (evenSlotZero_bound_M hα hrange) T

/-- **`N` branch: the flip supply is false at every `α ≥ 2`.** -/
theorem evenSlotZero_not_flipSupply_N {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) (T : Tuple W v G chi k) :
    ¬ EvenDigitFlipSupply α W v G chi :=
  evenSlotZero_not_flipSupply hα hk (evenSlotZero_bound_N hα hrange) T

/-- **`M` branch: the reduced (slot-`0`) supply is false at every `α ≥ 2`.** -/
theorem evenSlotZero_not_slotZeroSupply_M {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (T : Tuple W v G chi k) :
    ¬ EvenDigitFlipSupplySlotZero α W v G chi :=
  evenSlotZero_not_slotZeroSupply hα hk (evenSlotZero_bound_M hα hrange) T

/-- **`N` branch: the reduced (slot-`0`) supply is false at every `α ≥ 2`.** -/
theorem evenSlotZero_not_slotZeroSupply_N {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) (T : Tuple W v G chi k) :
    ¬ EvenDigitFlipSupplySlotZero α W v G chi :=
  evenSlotZero_not_slotZeroSupply hα hk (evenSlotZero_bound_N hα hrange) T

end SlotZero

/-! ### §3.2 `Hup` itself

Wave 53's `evenDigit_rawToBracket_iff_flip_{M,N}` needs the ambient profinite hypotheses, which
nothing above does; they enter only here. -/

section RawToBracket

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k α : ℕ}

/-- **`Hup` is false at every `α ≥ 2`, `M` branch.**  Wave 53 proved the raw-to-bracket upgrade
at depth `α - 1` *equivalent* to the flip supply on the pinned `M` image, so the refutation
transports verbatim.  Wave 55 had this only at `α = 2`. -/
theorem evenSlotZero_not_rawToBracket_M {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (T : Tuple W v G chi k) :
    ¬ EvenKernelRawToBracketSupply (α - 1) W v G chi := fun Hup ↦
  evenSlotZero_not_flipSupply_M hα hk hrange T
    ((evenDigit_rawToBracket_iff_flip_M hα hrange).mp Hup)

/-- **`Hup` is false at every `α ≥ 2`, `N` branch.** -/
theorem evenSlotZero_not_rawToBracket_N {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) (T : Tuple W v G chi k) :
    ¬ EvenKernelRawToBracketSupply (α - 1) W v G chi := fun Hup ↦
  evenSlotZero_not_flipSupply_N hα hk hrange T
    ((evenDigit_rawToBracket_iff_flip_N hα hrange).mp Hup)

end RawToBracket

/-! ## §4 The per-field flip inputs, and the endpoints that consume them -/

section Fields

open ContCoh
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenEndpoint

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenSlotZeroScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenSlotZeroContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The deep `N` flip input is false**, at any branch depth `α ≥ 3` whose range identity holds
and at which one stage tuple exists.  So the surviving wave-55 `N` endpoint
`evenFlip_orientedEquivN_atDepth_deep` has an unsatisfiable hypothesis set. -/
theorem evenSlotZero_not_nSlotZeroDeep {h k alpha : ℕ} (halpha : 3 ≤ alpha) (hk : 3 ≤ k)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (T : Tuple (nStageWord alpha h (by omega)) (vN alpha) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) k) :
    ¬ EvenFlipNSlotZeroDeep h K := fun H ↦
  evenSlotZero_not_slotZeroSupply_N (by omega) hk hrange T (H alpha halpha)

/-- **The deep `M` flip input is false.**  So `evenFlip_orientedEquivM_atDepth_deep` has an
unsatisfiable hypothesis set. -/
theorem evenSlotZero_not_mSlotZeroDeep {h k alpha : ℕ} (halpha : 3 ≤ alpha) (hk : 3 ≤ k)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (T : Tuple (mStageWord alpha h (by omega)) (vM alpha) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) k) :
    ¬ EvenFlipMSlotZeroDeep h K := fun H ↦
  evenSlotZero_not_slotZeroSupply_M (by omega) hk hrange T (H alpha halpha)

omit [T2Space (GalK K)] in
/-- **The at-depth `N` flip input is false at every depth `α ≥ 2`.**  Wave 55's
`evenFlip_orientedEquivN_atDepth` consumes `EvenDigitFlipSupplySlotZero alpha …` at the one
depth the range identity produces; that hypothesis is false there. -/
theorem evenSlotZero_not_nAtDepth {h k alpha : ℕ} (halpha : 2 ≤ alpha) (hk : 3 ≤ k)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    ¬ EvenDigitFlipSupplySlotZero alpha (nStageWord alpha h (Nat.le_of_succ_le halpha))
      (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenSlotZero_not_slotZeroSupply_N halpha hk hrange T

omit [T2Space (GalK K)] in
/-- **The at-depth `M` flip input is false at every depth `α ≥ 2`.** -/
theorem evenSlotZero_not_mAtDepth {h k alpha : ℕ} (halpha : 2 ≤ alpha) (hk : 3 ≤ k)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    ¬ EvenDigitFlipSupplySlotZero alpha (mStageWord alpha h (Nat.le_of_succ_le halpha))
      (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenSlotZero_not_slotZeroSupply_M halpha hk hrange T

/-- **The `N` stage base is all the refutation needs.**  `EvenPerKNStageBase` produces a level-`3`
stage tuple at every branch depth, so a field whose range identity lands at `α ≥ 3` and which
carries the base has no deep `N` flip supply at all. -/
theorem evenSlotZero_not_nSlotZeroDeep_of_base {h alpha : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (Hbase : EvenPerKNStageBase h K) : ¬ EvenFlipNSlotZeroDeep h K :=
  evenSlotZero_not_nSlotZeroDeep halpha (le_refl 3) hrange (Hbase alpha (by omega)).some

/-- **The `M` stage base is all the refutation needs.** -/
theorem evenSlotZero_not_mSlotZeroDeep_of_base {h alpha : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (Hbase : EvenPerKMStageBase h K) : ¬ EvenFlipMSlotZeroDeep h K :=
  evenSlotZero_not_mSlotZeroDeep halpha (le_refl 3) hrange (Hbase alpha (by omega)).some

end Fields

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins -/

#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_step
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_depth_boundary
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_digit
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_slotZeroSupply
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_flipSupply
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_bound_M
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_bound_N
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_flipSupply_M
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_flipSupply_N
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_slotZeroSupply_M
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_slotZeroSupply_N
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_rawToBracket_M
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_rawToBracket_N
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_nSlotZeroDeep
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_mSlotZeroDeep
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_nAtDepth
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_mAtDepth
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_nSlotZeroDeep_of_base
#print axioms GQ2.Dyadic.StageGeneric.evenSlotZero_not_mSlotZeroDeep_of_base
