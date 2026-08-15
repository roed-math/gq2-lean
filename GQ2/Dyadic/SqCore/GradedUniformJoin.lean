/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedUniformTower
import GQ2.Dyadic.SqCore.GradedDeltaFunctionals

/-!
# W75-JOIN: joining the uniform tower to the delta functionals

Wave 74 landed two modules that were written blind to each other:

* `GQ2/Dyadic/SqCore/GradedUniformTower.lean` (prefix `gTower`), the class-uniform
  engine, which reduces the whole `h ≥ 1` residual `SqLamMarkTransitivity h` to two named
  interfaces `GTowerDefectVanishing h` and `GTowerKnobRealizable h`, plus one base index
  `GTowerLayerReach h ν' 2`;
* `GQ2/Dyadic/SqCore/GradedDeltaFunctionals.lean` (prefix `gDelta`), Labute's Lemma 4
  apparatus, whose interface `GDeltaDefectVanishing h` is **proved outright**.

This file is the join.  It states the shape mismatch between the two interfaces exactly,
records which half of it is a theorem and which half is a genuine mathematical obligation,
and assembles what can be assembled.

## The shape mismatch, precisely

`GDeltaDefectVanishing h` says: for every functional coefficient `c`, marking `ν'`, handle
`j` and dressing `a` with `χ_sq(a i) = 1` at every slot,
`gDelta h c (sqRelWord (sqArbFrame h ν' j a)) = 0`.

`GTowerDefectVanishing h` says: for every *selected* marking `ν'`, handle `j`, level
`k ≥ 2` and dressing `a` with `λ(a i) = 1` and `ν'(a i) = 1` at every slot, the layer class
of the relator lies in `Subgroup.closure (gTowerKnobSet h ν' k)`.

The two differ on **both** sides:

* **Hypothesis side (the torsion gap).**  The tower's dressing clause is the supply's, two
  logged rows; the functional's is `χ_sq = 1`.  The supply's `λ`-clause forces only
  `χ_sq(a i) = ±1` (`gDelta_chiSq_of_nuLam`, wave 74's own honesty artifact).  So
  `GDeltaDefectVanishing` is available on a **strict sub-space** of the dressings that
  `GTowerDefectVanishing` quantifies over.  §1 below makes the containment a theorem and
  isolates the `-1` branch.
* **Conclusion side (Labute's `Im δ = ⋂ ker Δ`).**  The functional side delivers a
  *reading* (`gDelta … = 0`); the tower side wants a *membership* (knob span).  Bridging
  them is the second half of his Lemma 4: the knobs must be invisible to the functionals at
  the layer bit, and the admissible towers must be detected by them.

## What this file proves

* §2 **the torsion gap closes**: a `γ₂`-valued admissible correction is exactly `χ`-trivial,
  so the `-1` branch wave 74 flagged never occurs along the clearing recursion.  §3 re-runs
  the recursion carrying the `χ`-clause, so the weaker interface `GJoinDefectVanishing`
  suffices for the whole residual.
* §4 the `ℤ₂`-exponent tower formula, and the readings of the cleared letters.
* §5 **knob invisibility**: both knob families read one bit deeper than the layer.
* §6 **the invisible tower is a knob**: Labute's excluded column `x̃₁` is manufactured by the
  `x₁`-slot bundle, so it costs nothing.
* §7 **tower detection**, and `gJoin_reach_le`: the reach exceeds the knob span by exactly
  the `2h` handle towers, every one of them functional-visible.
* §8 the join: `GJoinDefectVanishing h`, hence `SqClassClearingSupply h k` at every `k` and
  the `h ≥ 1` residual, from three named inputs: wave 74's depth-`2` base `GJoinBase`, wave
  74's `GTowerKnobRealizable`, and the `𝔽₂` bookkeeping `GJoinSeparationAll` of §7.

The functional half of Labute's Lemma 4 is therefore fully discharged; what remains of the
graded route is the depth-`2` base, the extraction, and one independence bookkeeping step.

-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The hypothesis side: the torsion gap, made a theorem

The `χ`-trivial dressings are exactly the ones the functional interface covers.  They are a
sub-family of the admissible dressings, and the defect of the complement is precisely the
`-1` branch of `gDelta_chiSq_of_nuLam`. -/

section Hypotheses

variable {h : ℕ}

variable (h) in
/-- **The `χ`-trivial dressing space**: the dressings for which `GDeltaDefectVanishing`
speaks.  (Both row clauses of the supply, *plus* exact `χ`-triviality at every slot.) -/
def GJoinChiAdm (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (a : Fin (sqRank h) → (DSq h : Type)) : Prop :=
  (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧ (∀ i, chiSq h (a i) = 1)

/-- A `χ`-trivial dressing is an admissible one: the containment is by definition, and it is
recorded so the direction of the gap is unambiguous. -/
theorem gJoin_chiAdm_rows
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : GJoinChiAdm h nu' a) :
    (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) :=
  ⟨ha.1, ha.2.1⟩

/-- ⭐ **The torsion gap, slot by slot**: an admissible dressing slot is either `χ`-trivial
or carries the torsion value `-1`; there is no third possibility.  So the family that
`GTowerDefectVanishing` quantifies over is covered by `GJoinChiAdm` exactly off the `-1`
branch. -/
theorem gJoin_slot_dichotomy {a : (DSq h : Type)} (hl : nuLam h a = 1) :
    chiSq h a = 1 ∨ chiSq h a = -1 :=
  gDelta_chiSq_of_nuLam hl

/-- The gap is a `2`-torsion phenomenon and nothing more: on admissible slots `χ_sq` takes
values in `μ₂`. -/
theorem gJoin_slot_sq {a : (DSq h : Type)} (hl : nuLam h a = 1) : (chiSq h a) ^ 2 = 1 :=
  gDelta_chiSq_sq_of_nuLam hl

/-- ⭐ **The functional kill on the `χ`-trivial dressing space**: every functional reads
zero on the relator value of every `χ`-trivial dressing of every frame.  This is
`GDeltaDefectVanishing` re-stated in the join's vocabulary, and it is the *whole* of what
the FUNC lane exports towards `GTowerDefectVanishing`. -/
theorem gJoin_reading_zero (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : GJoinChiAdm h nu' a) :
    gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
  gDeltaDefectVanishing_holds h c nu' j a ha.2.2

end Hypotheses

/-! ## §2 The torsion gap closes on the correction calculus

Wave 74's FUNC note listed the `χ_sq = -1` branch as an open gap between its vanishing
statement and the supply's dressing space.  It is not a gap for any dressing the clearing
recursion produces: a `γ₂`-valued admissible correction has `χ_sq ≡ 1 (mod 8)`
(`gDelta_chi_gammaTwo_dvd`) and `χ_sq = ±1` (`gDelta_chiSq_of_nuLam`), and `-1 ≢ 1 (mod 8)`.
So the `χ`-clause is *free* along the recursion, and the vanishing interface may be stated
with it. -/

section Torsion

variable {h : ℕ}

/-- ⭐⭐ **The torsion gap closes**: an admissible correction lying in `γ₂` is exactly
`χ`-trivial.  The two available facts pin opposite residues: `χ_sq(a) = ±1` from the `λ`-row,
`χ_sq(a) ≡ 1 (mod 8)` from `γ₂`-membership, and `-2` is not `8`-divisible in `ℤ₂`. -/
theorem gJoin_chiSq_of_gammaTwo {a : (DSq h : Type)}
    (hm : a ∈ twoCentralSeries (DSq h : Type) 2) (hl : nuLam h a = 1) :
    chiSq h a = 1 := by
  rcases gJoin_slot_dichotomy hl with h1 | h1
  · exact h1
  · exfalso
    have hd := gDelta_chi_gammaTwo_dvd hm
    rw [h1] at hd
    obtain ⟨y, hy⟩ := hd
    rw [Units.val_neg, Units.val_one] at hy
    have hcancel : ((-1 : ℤ_[2]ˣ) : ℤ_[2]) = 2 * (2 * y) := by
      rw [Units.val_neg, Units.val_one]
      have h2 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
      refine mul_left_cancel₀ h2 ?_
      linear_combination hy
    exact gDelta_not_two_dvd_unit (-1) ⟨2 * y, hcancel⟩

/-- The `χ`-clause is preserved by an admissible `γ_k`-correction, `k ≥ 2`: this is why it
costs nothing along the clearing recursion. -/
theorem gJoin_chiSq_mul_correction {a d : (DSq h : Type)} (ha : chiSq h a = 1) {k : ℕ}
    (hk : 2 ≤ k) (hd : d ∈ twoCentralSeries (DSq h : Type) k) (hdl : nuLam h d = 1) :
    chiSq h (a * d) = 1 := by
  rw [map_mul, ha, one_mul]
  exact gJoin_chiSq_of_gammaTwo (twoCentralSeries_antitone (G := (DSq h : Type)) hk hd) hdl

end Torsion

/-! ## §3 The `χ`-restricted vanishing interface, and the recursion that consumes it

The wave-74 assembly quantifies `GTowerDefectVanishing` over *every* admissible dressing.  §2
says the recursion only ever meets `χ`-trivial ones, so the interface may carry the `χ`-clause
as a hypothesis.  This section re-runs wave 74's recursion with the clause threaded through,
producing `SqClassClearingSupply h k` at every `k` from the weaker interface. -/

section ChiRecursion

variable {h : ℕ}

variable (h) in
/-- ⭐⭐ **The `χ`-restricted defect-vanishing interface**: `GTowerDefectVanishing h` with the
extra hypothesis that the dressing is `χ`-trivial at every slot.  Strictly weaker than
`GTowerDefectVanishing h`, and strictly closer to what `GDeltaDefectVanishing h` (proved)
delivers: the functional side speaks *exactly* on this family.

⚠ **[W81-HOUSE, as of `6f2916f3`: THIS `Prop` IS A THEOREM at every `h`** -
`gOdd_defectVanishing` (`SqCore/GradedOddClose.lean`), which is
`gGen_defectVanishing (gExt_separationAll h)`: the kill ladder at every rung plus wave 79's
separation.  Its two per-class instances `GAbsVanishingTwo h` and `GDeepVanishingThree h` are
theorems for the same reason.  Still open, and NOT implied by this: the strictly stronger
`GTowerDefectVanishing h`, which drops the `χ`-triviality clause and which nothing in the tree
proves or refutes.]** -/
def GJoinDefectVanishing : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    ∀ k, 2 ≤ k → ∀ a : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a i) = 1) → (∀ i, nu' (a i) = 1) → (∀ i, chiSq h (a i) = 1) →
      SqModTwoIndep (sqArbFrame h nu' j a) →
      sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) (k + 1) →
      levelMk (DSq h : Type) (k + 2) (sqRelWord (sqArbFrame h nu' j a))
        ∈ Subgroup.closure (gTowerKnobSet h nu' k)

/-- `GTowerDefectVanishing` is the stronger hypothesis.

⚠ **[W81-HOUSE, as of `6f2916f3`: SUPERSEDED - the conclusion is now a theorem outright
(`gOdd_defectVanishing`), so this reduction is no longer a way of getting it.  The
hypothesis `GTowerDefectVanishing h` remains open; this theorem is what would make it
useful if it were ever proved.]** -/
theorem gJoin_defectVanishing_of_tower (H : GTowerDefectVanishing h) :
    GJoinDefectVanishing h :=
  fun nu' j hs hx k hk a hal han _ hai hrel => H nu' j hs hx k hk a hal han hai hrel

variable (h) in
/-- The supply with the `χ`-clause carried: the clearing sets, restricted to `χ`-trivial
dressings.  §2 makes this restriction free.

⚠ **[W81-HOUSE, as of `6f2916f3`: THIS `Prop` IS A THEOREM at every `h` and every `k`** -
`gXf_chiSupply_le (gOdd_chiSupply h k)`, the `x₁`-free refinement `GXfChiSupply h k`
(`SqCore/GradedXFree.lean`) weakened.  No standalone unconditional `gJoin_chiSupply` is
recorded in the tree; the one-step composition above is the route.]** -/
def GJoinChiSupply (k : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ a : Fin (sqRank h) → (DSq h : Type),
        (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧ (∀ i, chiSq h (a i) = 1) ∧
          SqModTwoIndep (sqArbFrame h nu' j a) ∧
            sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) k

/-- The `χ`-carrying supply implies the committed supply. -/
theorem gJoin_supply_of_chiSupply {k : ℕ} (H : GJoinChiSupply h k) :
    SqClassClearingSupply h k := by
  intro nu' j hsigma hx0
  obtain ⟨a, h1, h2, _, h4, h5⟩ := H nu' j hsigma hx0
  exact ⟨a, h1, h2, h4, h5⟩

/-- **The base**: wave 68's bridge dressing is `χ`-trivial (`gDelta_chiSq_bridgeTuple`), so the
committed class-three witness already lives in the `χ`-restricted supply. -/
theorem gJoin_chiSupply_three : GJoinChiSupply h 3 := by
  intro nu' j hsigma hx0
  exact ⟨bridgeTuple nu' j, bridge_tuple_nuLam nu' j, bridge_tuple_nu nu' j hsigma hx0,
    gDelta_chiSq_bridgeTuple nu' j, bridge_modTwoIndep nu' j, bridge_relator_mem nu' j⟩

/-- ⭐⭐ **One clearing step, `χ`-carrying**: the `χ`-clause is restored for free at the
corrected dressing by §2, so the weaker interface suffices for the step. -/
theorem gJoin_clear_step (HV : GJoinDefectVanishing h) (HR : GTowerKnobRealizable h)
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {k : ℕ} (hk : 2 ≤ k)
    {a : Fin (sqRank h) → (DSq h : Type)} (hal : ∀ i, nuLam h (a i) = 1)
    (han : ∀ i, nu' (a i) = 1) (hac : ∀ i, chiSq h (a i) = 1)
    (hai : SqModTwoIndep (sqArbFrame h nu' j a))
    (hrel : sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) (k + 1)) :
    ∃ a' : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a' i) = 1) ∧ (∀ i, nu' (a' i) = 1) ∧ (∀ i, chiSq h (a' i) = 1) ∧
        SqModTwoIndep (sqArbFrame h nu' j a') ∧
          sqRelWord (sqArbFrame h nu' j a') ∈ twoCentralSeries (DSq h : Type) (k + 2) := by
  have hknob := HV nu' j hsigma hx0 k hk a hal han hac hai hrel
  obtain ⟨d, hd, hdl, hdn, hrel'⟩ := HR nu' j hsigma hx0 k hk a hal han hai hrel hknob
  refine ⟨fun i => a i * d i, ?_, ?_, ?_, ?_, hrel'⟩
  · intro i
    rw [map_mul, hal i, hdl i, one_mul]
  · intro i
    rw [map_mul, han i, hdn i, one_mul]
  · intro i
    exact gJoin_chiSq_mul_correction (hac i) hk (hd i) (hdl i)
  · rw [gTower_frame_mul]
    exact cfourId_modTwoIndep_mul hai
      (fun i => twoCentralSeries_antitone (G := (DSq h : Type)) hk (hd i))

/-- ⭐⭐⭐ **The supply at every class, from the `χ`-restricted interface**: wave 74's
`gTower_supply_of_vanishing` with the torsion gap of its FUNC sibling closed.

⚠ **[W81-HOUSE, as of `6f2916f3`: the `_of_vanishing` FAMILY here (`gJoin_clear_step`,
`gJoin_supply_of_vanishing`, `gJoin_markTransitivity_of_vanishing`) has a PROVED `HV` and an
UNPROVED `HR`.**  `HV : GJoinDefectVanishing h` is `gOdd_defectVanishing`;
`HR : GTowerKnobRealizable h` is the interface wave 79 found the route does not prove as
quantified, and it is bypassed rather than discharged.  The live route to the same conclusions
is the `x₁`-free re-run in `SqCore/GradedXFree.lean` §8 (`gXf_supply_of_vanishing`,
`gXf_markTransitivity_of_vanishing`), which needs `HV` alone; both conclusions are then
unconditional in `SqCore/GradedOddClose.lean` (`gOdd_supply`, `gOdd_markTransitivity`).
Statements unchanged.]** -/
theorem gJoin_supply_of_vanishing (HV : GJoinDefectVanishing h)
    (HR : GTowerKnobRealizable h) : ∀ k, SqClassClearingSupply h k := by
  have hmain : ∀ K, GJoinChiSupply h (K + 3) := by
    intro K
    induction K with
    | zero => exact gJoin_chiSupply_three
    | succ K ih =>
      intro nu' j hsigma hx0
      obtain ⟨a, hal, han, hac, hai, hrel⟩ := ih nu' j hsigma hx0
      have hrel' : sqRelWord (sqArbFrame h nu' j a)
          ∈ twoCentralSeries (DSq h : Type) ((K + 2) + 1) := by
        rwa [(by omega : K + 2 + 1 = K + 3)]
      obtain ⟨a', h1, h2, h3, h4, h5⟩ := gJoin_clear_step HV HR hsigma hx0
        (by omega : 2 ≤ K + 2) hal han hac hai hrel'
      refine ⟨a', h1, h2, h3, h4, ?_⟩
      rwa [(by omega : K + 1 + 3 = K + 2 + 2)]
  intro k
  rcases Nat.lt_or_ge k 3 with hk | hk
  · exact sqClassClearingSupply_of_le (by omega) (sqClassThree_supply h)
  · obtain ⟨K, rfl⟩ : ∃ K, k = K + 3 := ⟨k - 3, by omega⟩
    exact gJoin_supply_of_chiSupply (hmain K)

/-- ⭐⭐⭐ **The residual from the `χ`-restricted interface**. -/
theorem gJoin_markTransitivity_of_vanishing (HV : GJoinDefectVanishing h)
    (HR : GTowerKnobRealizable h) : SqLamMarkTransitivity h :=
  limFinal_markTransitivity (gJoin_supply_of_vanishing HV HR)

end ChiRecursion

/-! ## §4 Reading the tower letters

Labute's Lemma 4(3) says the functionals detect the Frobenius towers.  Wave 74 committed that
for the **letters** `σ`, `x₀`, `u_j` at `2^m`-powers.  The tower generators of the reach are
`ℤ₂`-powers of the **cleared** letters `x̃₁`, `U_j`, `V_j`, so this section extends the reading
to `ℤ₂`-exponents and computes it at the cleared letters.

The key device is the vanishing subgroup of a functional.  Because `gDelta` is a crossed
homomorphism, `{x | gDelta c x = 0}` is a closed subgroup; a coefficient vector supported on a
single handle slot therefore kills the whole core (`σ`, `x₀`, `x₁`, the pivot) and every other
handle, and reads the cleared letter of its own slot on the nose. -/

section Readings

variable {h : ℕ}

variable (h) in
/-- **The vanishing subgroup of a functional.**  `gDelta` is a crossed homomorphism, so its
zero set is a subgroup (`D(xy) = Dx + χ(x)·Dy`), and it is closed by continuity. -/
def gJoinVanish (c : Fin (sqRank h) → ℤ_[2]) : Subgroup (DSq h : Type) where
  carrier := {x | gDelta h c x = 0}
  one_mem' := gDelta_one c
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [gDelta_mul, ha, hb, mul_zero, add_zero]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [gDelta_inv, ha, mul_zero, neg_zero]

theorem gJoin_mem_vanish {c : Fin (sqRank h) → ℤ_[2]} {x : (DSq h : Type)} :
    x ∈ gJoinVanish h c ↔ gDelta h c x = 0 := Iff.rfl

theorem gJoin_isClosed_vanish (c : Fin (sqRank h) → ℤ_[2]) :
    IsClosed ((gJoinVanish h c : Subgroup (DSq h : Type)) : Set (DSq h : Type)) :=
  IsClosed.preimage (gDelta_continuous c) isClosed_singleton

/-- **`ℤ₂`-powers stay in the vanishing subgroup**: the procyclic closure of a killed element
is killed. -/
theorem gJoin_zpow_vanish {c : Fin (sqRank h) → ℤ_[2]} {x : (DSq h : Type)}
    (hx : gDelta h c x = 0) (A : ℤ_[2]) :
    gDelta h c (zpowZtwo (isProP_DSq h) x A) = 0 := by
  have hle : (Subgroup.closure ({x} : Set (DSq h : Type))).topologicalClosure
      ≤ gJoinVanish h c :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).2 (by rintro _ rfl; exact hx)) (gJoin_isClosed_vanish c)
  exact hle (zpowZtwo_mem_topologicalClosure (isProP_DSq h) x A)

/-- The pivot `w = σ·x₀^{-c}` is read by the two core rows alone. -/
theorem gJoin_delta_pivot {c : Fin (sqRank h) → ℤ_[2]} (h0 : c 0 = 0) (h1 : c 1 = 0) :
    gDelta h c (sqPivot h) = 0 := by
  have hx0 : gDelta h c (dsqX0 h) = 0 := by rw [dsqX0, gDelta_gen, h1]
  have hzp : gDelta h c (zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp) = 0 :=
    gJoin_zpow_vanish hx0 _
  rw [sqPivot, sqMixPivotElem, gDelta_mul, gDelta_inv, hzp, mul_zero, neg_zero, mul_zero,
    add_zero, dsqSigma, gDelta_gen, h0]

/-- The cleared `x₁`-letter is read by the `x₁`-row alone. -/
theorem gJoin_delta_xOne {c : Fin (sqRank h) → ℤ_[2]} (h1 : c 1 = 0) :
    gDelta h c (gTowerXOne h) = c 2 := by
  have hx0 : gDelta h c (dsqX0 h) = 0 := by rw [dsqX0, gDelta_gen, h1]
  have hzp : gDelta h c (zpowZtwo (isProP_DSq h) (dsqX0 h) 2) = 0 := gJoin_zpow_vanish hx0 _
  rw [gTowerXOne, gDelta_mul, gDelta_inv, hzp, mul_zero, neg_zero, mul_zero, add_zero,
    dsqX1, gDelta_gen]

/-- ⭐ **The cleared `u`-letter is read by its own slot alone**, once the two core rows are
switched off: the pivot factor is invisible and chi-trivial. -/
theorem gJoin_delta_eichU {c : Fin (sqRank h) → ℤ_[2]} (h0 : c 0 = 0) (h1 : c 1 = 0)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (sqEichU h nu' j) = c (sqHandleIdxU j) := by
  have hzp : gDelta h c (zpowZtwo (isProP_DSq h) (sqPivot h)
      (toAdd (nu' (sqGen h (sqHandleIdxU j))))) = 0 :=
    gJoin_zpow_vanish (gJoin_delta_pivot h0 h1) _
  rw [sqEichU, gDelta_mul, gDelta_inv, hzp, mul_zero, neg_zero, zero_add, gDelta_gen,
    map_inv, gDelta_chiSq_zpow_pivot, inv_one, Units.val_one, one_mul]

/-- ⭐ The cleared `v`-letter is read by its own slot alone. -/
theorem gJoin_delta_eichV {c : Fin (sqRank h) → ℤ_[2]} (h0 : c 0 = 0) (h1 : c 1 = 0)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (sqEichV h nu' j) = c (sqHandleIdxV j) := by
  have hzp : gDelta h c (zpowZtwo (isProP_DSq h) (sqPivot h)
      (toAdd (nu' (sqGen h (sqHandleIdxV j))))) = 0 :=
    gJoin_zpow_vanish (gJoin_delta_pivot h0 h1) _
  rw [sqEichV, gDelta_mul, gDelta_inv, hzp, mul_zero, neg_zero, mul_zero, add_zero,
    gDelta_gen]

/-- ⭐⭐ **The `ℤ₂`-tower formula at a chi-trivial base**: `D(x^A) = A·Dx`.  Wave 74's
`gDelta_sigma_tower`/`gDelta_handleU_tower` are the `A = 2^m` instances at the letters; the
reach's tower generators carry genuine `ℤ₂`-exponents, so the formula is pushed to `ℤ₂` by
density of `ℕ` and continuity of both sides. -/
theorem gJoin_delta_zpow (c : Fin (sqRank h) → ℤ_[2]) {x : (DSq h : Type)}
    (hx : chiSq h x = 1) (A : ℤ_[2]) :
    gDelta h c (zpowZtwo (isProP_DSq h) x A) = A * gDelta h c x := by
  refine PadicInt.denseRange_natCast.induction_on A ?_ ?_
  · exact isClosed_eq ((gDelta_continuous c).comp (continuous_zpowZtwo (isProP_DSq h) x))
      (continuous_id.mul continuous_const)
  · intro n
    rw [zpowZtwo_natCast, gDelta_pow, hx, Units.val_one, normSum_one_base]

/-- `ℤ₂`-powers of a chi-trivial element are chi-trivial. -/
theorem gJoin_chiSq_zpow {x : (DSq h : Type)} (hx : chiSq h x = 1) (A : ℤ_[2]) :
    chiSq h (zpowZtwo (isProP_DSq h) x A) = 1 := by
  rw [map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), hx, zpowZtwo_one_base]

end Readings

/-! ## §5 Knob invisibility: the knobs are one bit deeper than the layer

The generic filtration bound puts a `γ_{k+1}`-element's reading in `2^kℤ₂`
(`gDelta_dvd_of_mem_twoCentral`), which is exactly the tower bit: the towers `x^{2^k a}` read
`2^k·a·unit`.  The knobs are **one bit deeper**, and for a structural reason:

* the far span is the `x₁`-free letter span, and every `x₁`-free letter has `χ ≡ 1 (mod 4)`
  (`S ≡ 13`, `X ≡ 5`, handles `= 1`), while `χ(x₁) = Y ≡ 3 (mod 4)`.  So a bracket knob
  `⁅t, q⁆` picks up a factor `χ(q)⁻¹ − 1 ∈ 4ℤ₂`;
* the `x₁`-slot **bundle** `t²·⁅t, x₁⁆` reads `(1 + Y⁻¹)·Dt`, and `Y + 1 = 1 − X²` has
  valuation exactly `3`: the `2` from the square cancels the odd part of `Y − 1`.  This is
  precisely why the inventory bundles the square with the `x₁`-bracket instead of carrying
  either alone.

Both knob families are therefore `2^{k+1}`-invisible, and the correction slot's exact
`χ`-triviality (§2) is what removes the second commutator term outright. -/

section KnobInvisibility

variable {h : ℕ}

/-- `Y + 1 = 1 − X²` has valuation at least `3`: `X − 1 = 4a` gives `1 − X² = −8a(1 + 2a)`. -/
theorem gJoin_Yval_add_one : (2 : ℤ_[2]) ^ 3 ∣ Yval + 1 := by
  obtain ⟨a, ha⟩ := gDelta_rootX_sub_one
  refine ⟨-((a : ℤ_[2]) + 2 * (a : ℤ_[2]) ^ 2), ?_⟩
  rw [Yval_eq]
  linear_combination (-(rootX + 1 + 4 * (a : ℤ_[2]))) * ha

/-- The `x₁`-slot bundle factor `1 + Y⁻¹` has valuation at least `3`. -/
theorem gJoin_one_add_Yval_inv : (2 : ℤ_[2]) ^ 3 ∣ 1 + ((YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
  obtain ⟨a, ha⟩ := gJoin_Yval_add_one
  refine ⟨((YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * a, ?_⟩
  have hinv : ((YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * Yval = 1 := by
    rw [← val_YvalUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination ((YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ha - hinv

variable (h) in
/-- The subgroup of elements with `χ ≡ 1 (mod 4)`: closed, because `χ_sq` is continuous and
the divisibility set is closed. -/
def gJoinChiFour : Subgroup (DSq h : Type) where
  carrier := {x | (2 : ℤ_[2]) ^ 2 ∣ ((chiSq h x : ℤ_[2]ˣ) : ℤ_[2]) - 1}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, Units.val_mul] at ha hb ⊢
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + ((chiSq h a : ℤ_[2]ˣ) : ℤ_[2]) * v, ?_⟩
    linear_combination hu + ((chiSq h a : ℤ_[2]ˣ) : ℤ_[2]) * hv
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
    obtain ⟨u, hu⟩ := ha
    have hinv : (((chiSq h a)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((chiSq h a : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨-((((chiSq h a)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * u), ?_⟩
    linear_combination -(((chiSq h a)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hu + hinv

theorem gJoin_isClosed_chiFour :
    IsClosed ((gJoinChiFour h : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
  have hcont : Continuous fun x : (DSq h : Type) => ((chiSq h x : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    (Units.continuous_val.comp (chiSq h).continuous_toFun).sub continuous_const
  exact (gDelta_isClosed_dvd_set 2).preimage hcont

/-- ⭐ **The far span lies inside `χ ≡ 1 (mod 4)`**: `χ(σ) = S ≡ 13`, `χ(x₀) = X ≡ 5`,
handles `= 1`.  The excluded letter `x₁` (`χ = Y ≡ 7`) is exactly the one the far span leaves
out.  [W76-HOUSE, watch round 13: the headline read "the far span **is** `χ ≡ 1 (mod 4)`",
which is an identity on a one-way containment.  `gTowerFar` is defined by *generators* (every
letter but `x₁`); what is proved here is `gTowerFar h ≤ gJoinChiFour h`, and nothing shows the
converse.  Second site, corrected there: `docs/dyadic/w75-join-note.md`'s T1 conclusion-side
item 1.] -/
theorem gJoin_chi_far {q : (DSq h : Type)} (hq : q ∈ gTowerFar h) :
    (2 : ℤ_[2]) ^ 2 ∣ ((chiSq h q : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have hle : gTowerFar h ≤ gJoinChiFour h := by
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_)
      gJoin_isClosed_chiFour
    rintro x (((rfl | rfl) | hx) | hx)
    · show (2 : ℤ_[2]) ^ 2 ∣ ((chiSq h (dsqSigma h) : ℤ_[2]ˣ) : ℤ_[2]) - 1
      rw [chiSq_sigma, val_SvalUnit]
      obtain ⟨a, ha⟩ := gDelta_Sval_sub_one
      exact ⟨a, ha⟩
    · show (2 : ℤ_[2]) ^ 2 ∣ ((chiSq h (dsqX0 h) : ℤ_[2]ˣ) : ℤ_[2]) - 1
      rw [chiSq_x0, val_rootXUnit]
      obtain ⟨a, ha⟩ := gDelta_rootX_sub_one
      exact ⟨a, ha⟩
    · obtain ⟨j, rfl⟩ := hx
      show (2 : ℤ_[2]) ^ 2 ∣ ((chiSq h (sqGen h (sqHandleIdxU j)) : ℤ_[2]ˣ) : ℤ_[2]) - 1
      rw [chiSq_handleU, Units.val_one, sub_self]
      exact dvd_zero _
    · obtain ⟨j, rfl⟩ := hx
      show (2 : ℤ_[2]) ^ 2 ∣ ((chiSq h (sqGen h (sqHandleIdxV j)) : ℤ_[2]ˣ) : ℤ_[2]) - 1
      rw [chiSq_handleV, Units.val_one, sub_self]
      exact dvd_zero _
  exact hle hq

/-- The inverse form of the far bound. -/
theorem gJoin_chi_far_inv {q : (DSq h : Type)} (hq : q ∈ gTowerFar h) :
    (2 : ℤ_[2]) ^ 2 ∣ (((chiSq h q)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨a, ha⟩ := gJoin_chi_far hq
  have hinv : (((chiSq h q)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((chiSq h q : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact ⟨-((((chiSq h q)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * a), by
    linear_combination -(((chiSq h q)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ha + hinv⟩

/-- An admissible correction at depth `k + 2 ≥ 2` is exactly `χ`-trivial (§2) and has
`2^{k+1}`-divisible reading (the filtration bound). -/
theorem gJoin_adm_reading {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {k : ℕ} {t : (DSq h : Type)} (ht : GTowerAdm h nu' (k + 2) t)
    (c : Fin (sqRank h) → ℤ_[2]) :
    chiSq h t = 1 ∧ (2 : ℤ_[2]) ^ (k + 1) ∣ gDelta h c t := by
  refine ⟨gJoin_chiSq_of_gammaTwo ?_ ht.2.1, gDelta_dvd_of_mem_twoCentral c (k + 1) ht.1⟩
  exact twoCentralSeries_antitone (G := (DSq h : Type)) (by omega : 2 ≤ k + 2) ht.1

/-- ⭐⭐ **The bracket knobs are one bit deeper than the layer**: at correction depth `k + 2`
the layer bit is `2^{k+2}` and the knob reading is `2^{k+3}`-divisible.  The correction slot
is exactly `χ`-trivial, which kills the second commutator term outright, and the far slot
contributes `χ(q)⁻¹ − 1 ∈ 4ℤ₂`. -/
theorem gJoin_knob_dvd {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {k : ℕ} {t : (DSq h : Type)} (ht : GTowerAdm h nu' (k + 2) t)
    {q : (DSq h : Type)} (hq : q ∈ gTowerFar h) (c : Fin (sqRank h) → ℤ_[2]) :
    (2 : ℤ_[2]) ^ (k + 3) ∣ gDelta h c (commP t q) := by
  obtain ⟨hchi, hdvd⟩ := gJoin_adm_reading ht c
  rw [gDelta_commP, hchi]
  simp only [inv_one, Units.val_one, one_mul, sub_self, zero_mul, mul_zero, add_zero]
  rw [(by omega : k + 3 = 2 + (k + 1)), pow_add]
  exact mul_dvd_mul (gJoin_chi_far_inv hq) hdvd

/-- ⭐⭐ **The `x₁`-slot bundles are one bit deeper than the layer**:
`D(t²·⁅t, x₁⁆) = (1 + Y⁻¹)·Dt`, and `v₂(1 + Y⁻¹) = v₂(Y + 1) = 3`.  The square contributes
the `2` that cancels the odd part of `Y − 1`; neither factor is invisible on its own, which
is exactly why the inventory bundles them. -/
theorem gJoin_bundle_dvd {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {k : ℕ} {t : (DSq h : Type)} (ht : GTowerAdm h nu' (k + 2) t)
    (c : Fin (sqRank h) → ℤ_[2]) :
    (2 : ℤ_[2]) ^ (k + 3) ∣ gDelta h c (t ^ 2 * commP t (dsqX1 h)) := by
  obtain ⟨hchi, hdvd⟩ := gJoin_adm_reading ht c
  have hsq : chiSq h (t ^ 2) = 1 := by rw [map_pow, hchi, one_pow]
  have hval : gDelta h c (t ^ 2 * commP t (dsqX1 h))
      = (1 + ((YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * gDelta h c t := by
    rw [gDelta_mul, hsq, Units.val_one, one_mul, gDelta_pow, hchi, Units.val_one,
      normSum_one_base, gDelta_commP, hchi, chiSq_x1]
    simp only [inv_one, Units.val_one, one_mul, sub_self, zero_mul, mul_zero, add_zero]
    push_cast
    ring
  rw [hval]
  have hstep : (2 : ℤ_[2]) ^ (k + 3) ∣ (2 : ℤ_[2]) ^ 3 * (2 : ℤ_[2]) ^ (k + 1) := by
    rw [← pow_add]
    exact pow_dvd_pow _ (by omega : k + 3 ≤ 3 + (k + 1))
  exact hstep.trans (mul_dvd_mul gJoin_one_add_Yval_inv hdvd)

end KnobInvisibility

/-! ## §6 The layer kernel, and the absorption of the invisible tower

Two consequences of §4-§5.

* The **layer kernel** `gJoinLayerDvd c k`: the classes in `Q_{k+2}` whose reading is
  `2^{k+1}`-divisible.  This is well defined on classes (`gDelta_dvd_of_levelMk_eq`), it is a
  subgroup, and by §5 it contains the whole knob span.
* The **`x̃₁` tower is a knob**.  This is the one tower the functionals cannot see
  (`gDelta_x1_tower_dvd`), so it *has* to be absorbed by the moves, and it is: the bundle at
  `t = x̃₁^{2^{k-1}a}` gives `t²·⁅t, x₁⁆`, the bracket splits as `⁅t, x̃₁⁆·⁅t, x₀²⁆` through
  the bracket homomorphism, the first factor is trivial (`t` is a power of `x̃₁`), and the
  second is a far-span knob.  So Labute's excluded column costs nothing here. -/

section LayerKernel

variable {h : ℕ}

variable (h) in
/-- The subgroup of elements with `2^m`-divisible reading. -/
def gJoinDvdSub (c : Fin (sqRank h) → ℤ_[2]) (m : ℕ) : Subgroup (DSq h : Type) where
  carrier := {x | (2 : ℤ_[2]) ^ m ∣ gDelta h c x}
  one_mem' := by
    simp only [Set.mem_setOf_eq, gDelta_one]
    exact dvd_zero _
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [gDelta_mul]
    exact dvd_add ha (hb.mul_left _)
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [gDelta_inv]
    exact dvd_neg.mpr (ha.mul_left _)

variable (h) in
/-- **The layer kernel at correction depth `k`**: the classes in `Q_{k+2}` whose reading is
`2^{k+1}`-divisible, i.e. whose layer bit vanishes.  Well defined by lift independence. -/
noncomputable def gJoinLayerDvd (c : Fin (sqRank h) → ℤ_[2]) (k : ℕ) :
    Subgroup (levelQuot (DSq h : Type) (k + 2)) :=
  (gJoinDvdSub h c (k + 1)).map (levelMk (DSq h : Type) (k + 2))

/-- Membership in the layer kernel is exactly `2^{k+1}`-divisibility of *any* lift's
reading. -/
theorem gJoin_mem_layerDvd {c : Fin (sqRank h) → ℤ_[2]} {k : ℕ} {x : (DSq h : Type)} :
    levelMk (DSq h : Type) (k + 2) x ∈ gJoinLayerDvd h c k ↔
      (2 : ℤ_[2]) ^ (k + 1) ∣ gDelta h c x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact gDelta_dvd_of_levelMk_eq c (k := k + 1) hxy.symm hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- ⭐⭐ **The knob span lies in every layer kernel**: §5, transported to classes. -/
theorem gJoin_knob_le_layerDvd
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ}
    (c : Fin (sqRank h) → ℤ_[2]) :
    Subgroup.closure (gTowerKnobSet h nu' (k + 2)) ≤ gJoinLayerDvd h c (k + 2) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z (⟨t, q, ht, hq, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact gJoin_mem_layerDvd.2 (gJoin_knob_dvd ht hq c)
  · exact gJoin_mem_layerDvd.2 (gJoin_bundle_dvd ht c)

end LayerKernel

section XOneAbsorption

variable {h : ℕ}

variable (h) in
/-- The centralizer of a single element, as a subgroup (built by hand to keep the closedness
argument one line). -/
noncomputable def gJoinCent (x : (DSq h : Type)) : Subgroup (DSq h : Type) where
  carrier := {g | g * x = x * g}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_assoc, mul_inv_cancel, mul_one]

/-- **`ℤ₂`-powers commute with their base.** -/
theorem gJoin_zpow_commP (x : (DSq h : Type)) (e : ℤ_[2]) :
    commP (zpowZtwo (isProP_DSq h) x e) x = 1 := by
  have hclosed : IsClosed ((gJoinCent h x : Subgroup (DSq h : Type)) : Set (DSq h : Type)) :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hle : (Subgroup.closure ({x} : Set (DSq h : Type))).topologicalClosure
      ≤ gJoinCent h x :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).2 (by rintro _ rfl; exact rfl)) hclosed
  have hcomm : zpowZtwo (isProP_DSq h) x e * x = x * zpowZtwo (isProP_DSq h) x e :=
    hle (zpowZtwo_mem_topologicalClosure (isProP_DSq h) x e)
  simp only [commP]
  calc (zpowZtwo (isProP_DSq h) x e)⁻¹ * x⁻¹ * zpowZtwo (isProP_DSq h) x e * x
      = (zpowZtwo (isProP_DSq h) x e)⁻¹ * x⁻¹ * (zpowZtwo (isProP_DSq h) x e * x) := by
        rw [mul_assoc]
    _ = (zpowZtwo (isProP_DSq h) x e)⁻¹ * x⁻¹ * (x * zpowZtwo (isProP_DSq h) x e) := by
        rw [hcomm]
    _ = 1 := by group

/-- The `x₁`-letter as the cleared letter times the `x₀`-tower. -/
theorem gJoin_x1_eq : dsqX1 h = gTowerXOne h * zpowZtwo (isProP_DSq h) (dsqX0 h) 2 := by
  rw [gTowerXOne, inv_mul_cancel_right]

/-- The `x̃₁`-towers are admissible corrections at their depth. -/
theorem gJoin_xOne_tower_adm
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ} (hk : 1 ≤ k)
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (a : ℤ_[2]) :
    GTowerAdm h nu' k (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ (k - 1) * a)) := by
  refine ⟨gTower_zpow_dvd_mem hk ⟨a, rfl⟩ _, ?_, ?_⟩
  · refine Multiplicative.toAdd.injective ?_
    rw [toAdd_map_zpowZtwo, gTower_xOne_nuLam, toAdd_one, mul_zero]
  · refine Multiplicative.toAdd.injective ?_
    rw [toAdd_map_zpowZtwo, gTower_xOne_nu nu' hx0, toAdd_one, mul_zero]

/-- ⭐⭐⭐ **The invisible tower is a knob**: `x̃₁^{2^k a}` lies in the knob span at depth
`k ≥ 1`.  This is what makes Labute's excluded column harmless here: the one tower no
functional detects is the one the `x₁`-slot bundle manufactures.  Every other tower is
detected, and §7 removes those by their readings. -/
theorem gJoin_xOne_tower_knob
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ} (hk : 1 ≤ k)
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (a : ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ k * a))
      ∈ Subgroup.closure (gTowerKnobSet h nu' k) := by
  set t := zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ (k - 1) * a) with ht_def
  have hadm : GTowerAdm h nu' k t := gJoin_xOne_tower_adm hk hx0 a
  have hsq : t ^ 2 = zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ k * a) := by
    rw [ht_def, sq, ← zpowZtwo_add]
    congr 1
    have h2 : (2 : ℤ_[2]) ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    linear_combination a * h2
  have hbundle : levelMk (DSq h : Type) (k + 2) (t ^ 2 * commP t (dsqX1 h))
      ∈ Subgroup.closure (gTowerKnobSet h nu' k) :=
    Subgroup.subset_closure (Or.inr ⟨t, hadm, rfl⟩)
  have hsplit : levelMk (DSq h : Type) (k + 2) (commP t (dsqX1 h))
      ∈ Subgroup.closure (gTowerKnobSet h nu' k) := by
    have hhom : levelMk (DSq h : Type) (k + 2) (commP t (dsqX1 h))
        = levelMk (DSq h : Type) (k + 2) (commP t (gTowerXOne h)) *
          levelMk (DSq h : Type) (k + 2)
            (commP t (zpowZtwo (isProP_DSq h) (dsqX0 h) 2)) := by
      have hmm := map_mul (cfiveCommHom (k := k) hadm.1) (gTowerXOne h)
        (zpowZtwo (isProP_DSq h) (dsqX0 h) 2)
      rw [← gJoin_x1_eq] at hmm
      exact hmm
    have hzero : levelMk (DSq h : Type) (k + 2) (commP t (gTowerXOne h)) = 1 := by
      rw [ht_def, gJoin_zpow_commP, map_one]
    have hfar : zpowZtwo (isProP_DSq h) (dsqX0 h) 2 ∈ gTowerFar h := by
      have hx0mem : dsqX0 h ∈ gTowerFar h :=
        Subgroup.le_topologicalClosure _
          (Subgroup.subset_closure (Or.inl (Or.inl (Or.inr rfl))))
      have hclosedFar :
          IsClosed ((gTowerFar h : Subgroup (DSq h : Type)) : Set (DSq h : Type)) :=
        Subgroup.isClosed_topologicalClosure _
      have hle : (Subgroup.closure ({dsqX0 h} : Set (DSq h : Type))).topologicalClosure
          ≤ gTowerFar h :=
        Subgroup.topologicalClosure_minimal _
          ((Subgroup.closure_le _).2 (by rintro _ rfl; exact hx0mem)) hclosedFar
      exact hle (zpowZtwo_mem_topologicalClosure (isProP_DSq h) (dsqX0 h) 2)
    rw [hhom, hzero, one_mul]
    exact Subgroup.subset_closure (Or.inl ⟨t, _, hadm, hfar, rfl⟩)
  have hform : levelMk (DSq h : Type) (k + 2) (t ^ 2)
      = levelMk (DSq h : Type) (k + 2) (t ^ 2 * commP t (dsqX1 h)) *
        (levelMk (DSq h : Type) (k + 2) (commP t (dsqX1 h)))⁻¹ := by
    rw [map_mul, mul_inv_cancel_right]
  rw [← hsq, hform]
  exact Subgroup.mul_mem _ hbundle (Subgroup.inv_mem _ hsplit)

end XOneAbsorption

/-! ## §7 Tower detection, and where the reach and the knob span actually differ

The other half of Labute's Lemma 4(3).  For each handle slot there is a coefficient vector
that reads **that slot's cleared letter and nothing else**, so its tower is visible at the
layer bit exactly when its exponent is odd.  Combined with §5-§6 this pins the difference
between the reach and the knob span precisely: it is spanned by the `2h` handle towers, every
one of which is functional-visible.  (The `x̃₁` tower, the one the functionals cannot see, is
already a knob by §6.  The two non-admissible towers `x₀`, `w` never enter, the defect being
exactly row-trivial.) -/

section Detection

variable {h : ℕ}

/-- The coefficient vector supported on the `u_j` slot. -/
noncomputable def gJoinRowU (j : Fin h) : Fin (sqRank h) → ℤ_[2] :=
  fun i => if i = sqHandleIdxU j then 1 else 0

/-- The coefficient vector supported on the `v_j` slot. -/
noncomputable def gJoinRowV (j : Fin h) : Fin (sqRank h) → ℤ_[2] :=
  fun i => if i = sqHandleIdxV j then 1 else 0

theorem gJoin_rowU_core (j : Fin h) : gJoinRowU (h := h) j 0 = 0 ∧ gJoinRowU (h := h) j 1 = 0 :=
  ⟨if_neg (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_zero]; omega))),
    if_neg (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_one]; omega)))⟩

theorem gJoin_rowV_core (j : Fin h) : gJoinRowV (h := h) j 0 = 0 ∧ gJoinRowV (h := h) j 1 = 0 :=
  ⟨if_neg (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_zero]; omega))),
    if_neg (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_one]; omega)))⟩

/-- ⭐ **The `u`-row reads its own cleared letter as a unit**, and every other cleared letter
as zero.  This is Labute's `Δ_i(π^{j-1} ξ_k) = π^j δ_{ik}` for the campaign's cleared
basis. -/
theorem gJoin_rowU_eichU (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j j' : Fin h) :
    gDelta h (gJoinRowU j) (sqEichU h nu' j') = if j' = j then 1 else 0 := by
  obtain ⟨h0, h1⟩ := gJoin_rowU_core (h := h) j
  rw [gJoin_delta_eichU h0 h1]
  by_cases hjj : j' = j
  · subst hjj
    simp only [gJoinRowU]
  · rw [if_neg hjj]
    exact if_neg fun hcon => hjj (sqHandleIdxU_injective hcon)

theorem gJoin_rowU_eichV (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j j' : Fin h) : gDelta h (gJoinRowU j) (sqEichV h nu' j') = 0 := by
  obtain ⟨h0, h1⟩ := gJoin_rowU_core (h := h) j
  rw [gJoin_delta_eichV h0 h1]
  exact if_neg (sqHandleIdxU_ne_sqHandleIdxV j j').symm

theorem gJoin_rowU_xOne (j : Fin h) : gDelta h (gJoinRowU j) (gTowerXOne h) = 0 := by
  rw [gJoin_delta_xOne (gJoin_rowU_core (h := h) j).2]
  exact if_neg (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_two]; omega)))

theorem gJoin_rowV_eichV (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j j' : Fin h) :
    gDelta h (gJoinRowV j) (sqEichV h nu' j') = if j' = j then 1 else 0 := by
  obtain ⟨h0, h1⟩ := gJoin_rowV_core (h := h) j
  rw [gJoin_delta_eichV h0 h1]
  by_cases hjj : j' = j
  · subst hjj
    simp only [gJoinRowV]
  · rw [if_neg hjj]
    exact if_neg fun hcon => hjj (sqHandleIdxV_injective hcon)

theorem gJoin_rowV_eichU (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j j' : Fin h) : gDelta h (gJoinRowV j) (sqEichU h nu' j') = 0 := by
  obtain ⟨h0, h1⟩ := gJoin_rowV_core (h := h) j
  rw [gJoin_delta_eichU h0 h1]
  exact if_neg (sqHandleIdxU_ne_sqHandleIdxV j' j)

/-- ⭐⭐ **The handle towers are detected on the nose**: the `u_j`-tower at exponent `2^k a`
reads `2^k a`, so its layer bit is the parity of `a`.  Contrapositive of Labute's Theorem 5
step `0 = Δ_i(ε_j) = a_i π^j`: a knob-span class cannot carry an odd handle-tower
coefficient. -/
theorem gJoin_eichU_tower_reading
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) (k : ℕ)
    (a : ℤ_[2]) :
    gDelta h (gJoinRowU j) (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 ^ k * a))
      = 2 ^ k * a := by
  rw [gJoin_delta_zpow _ (gDelta_chiSq_sqEichU nu' j), gJoin_rowU_eichU nu' j j, if_pos rfl,
    mul_one]

theorem gJoin_eichV_tower_reading
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) (k : ℕ)
    (a : ℤ_[2]) :
    gDelta h (gJoinRowV j) (zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 ^ k * a))
      = 2 ^ k * a := by
  rw [gJoin_delta_zpow _ (gDelta_chiSq_sqEichV nu' j), gJoin_rowV_eichV nu' j j, if_pos rfl,
    mul_one]

/-- ⭐⭐ **An odd-exponent handle tower is outside the layer kernel** - hence, by §6, outside
the knob span.  This is the exact obstruction that `gDelta_cfourCmp_span_hyp_false` exhibited
at `σ`, now at the *admissible* towers where it actually bites the join. -/
theorem gJoin_eichU_tower_notMem
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) {k : ℕ}
    {a : ℤ_[2]} (ha : ¬ (2 : ℤ_[2]) ∣ a) :
    levelMk (DSq h : Type) (k + 2)
        (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 ^ k * a))
      ∉ gJoinLayerDvd h (gJoinRowU j) k := by
  intro hmem
  rw [gJoin_mem_layerDvd, gJoin_eichU_tower_reading] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ha ⟨y, ?_⟩
  have h2 : ((2 : ℤ_[2]) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine mul_left_cancel₀ h2 ?_
  rw [pow_succ] at hy
  linear_combination hy

end Detection

section ReachSplit

open scoped Pointwise

variable {h : ℕ}

variable (h) in
/-- **The handle-tower generators at correction depth `k`**: the admissible towers *other*
than the `x̃₁`-tower, i.e. the ones the functionals detect. -/
noncomputable def gJoinEichSet
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ) :
    Set (levelQuot (DSq h : Type) (k + 2)) :=
  {z | ∃ j : Fin h, ∃ a : ℤ_[2],
      z = levelMk (DSq h : Type) (k + 2)
        (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 ^ k * a)) ∨
      z = levelMk (DSq h : Type) (k + 2)
        (zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 ^ k * a))}

/-- ⭐⭐⭐ **The reach lands inside the knob span joined with the handle towers.**  Wave 74's
reach adds three families of admissible towers to the knobs; §6 absorbs the `x̃₁`-tower into
the knobs outright, so what is left over the knob span is the `2h` **handle** towers - and
every one of those is read as a unit by its own row (§7).  This is the precise form of
Labute's Lemma 3/Theorem 5 division of labour for the sq core: moves span the
functional-invisible part, and the functionals kill the rest.

[W76-HOUSE, watch round 13: the headline read "the reach **is** the knob span together with
the handle towers", an equality where only `≤` is proved, as the declaration's own `_le`
suffix says.  The reverse containment is true and cheap - `gJoinEichSet` generators are
`gTowerTowSet` members by definition, `gTowerXLetters` containing both Eichler ranges - but it
is not stated anywhere, so nothing may cite an equality here.  The *sharpness* the summaries
want is a different statement and it is proved: `gJoin_eichU_tower_notMem` puts an odd-exponent
handle tower outside the knob span, so the join is not redundant.] -/
theorem gJoin_reach_le
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ} (hk : 1 ≤ k)
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    gTowerReach h nu' k ≤
      Subgroup.closure (gTowerKnobSet h nu' k) ⊔ Subgroup.closure (gJoinEichSet h nu' k) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z (hz | ⟨x, hx, a, rfl⟩)
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure hz)
  · simp only [gTowerXLetters, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
    obtain (rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩ := hx
    · exact Subgroup.mem_sup_left (gJoin_xOne_tower_knob hk hx0 a)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, a, Or.inl rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, a, Or.inr rfl⟩)

variable (h) in
/-- ⭐⭐ **The residual separation obligation**, isolated.  Everything Labute's Lemma 4 asks
of the join is proved above *except* one bookkeeping step: that the `2h` handle towers are
`𝔽₂`-independent modulo the knob span, as their readings say they are.  Stated pointwise so
that a consumer can check satisfiability: at `h = 0` it holds vacuously
(`gJoin_towerSeparation_handleFree`), and §7's readings give each generator's own row.

Concretely what remains is: write a class of the handle-tower span in the normal form
`∏_j U_j^{2^k f_j} · V_j^{2^k g_j}`, read off `f_j` and `g_j` by `gJoinRowU j`/`gJoinRowV j`,
and conclude `2 ∣ f_j`, `2 ∣ g_j`, hence triviality in the layer.  No new mathematics; the
friction is that the layer is written inside a non-commutative quotient, so the normal form
needs an ordered product and its exponent-addition law.

⚠ **[W81-HOUSE, as of `6f2916f3`: DISCHARGED.**  `gExt_towerSeparation : GJoinTowerSeparation
h nu' k` (`SqCore/GradedExtraction.lean`, wave 79) proves it at every `h`, every marking and
every `k`, and `gExt_separationAll` bundles it as `GJoinSeparationAll h`.  "What remains" in
the paragraph above is a completed work item, not an open one; the ordered-product normal form
it describes is what that proof builds.]** -/
def GJoinTowerSeparation
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ) : Prop :=
  ∀ z ∈ Subgroup.closure (gJoinEichSet h nu' k),
    (∀ j : Fin h, z ∈ gJoinLayerDvd h (gJoinRowU j) k) →
      (∀ j : Fin h, z ∈ gJoinLayerDvd h (gJoinRowV j) k) → z = 1

/-- The separation is vacuous in the handle-free case. -/
theorem gJoin_towerSeparation_handleFree
    (nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])) (k : ℕ) :
    GJoinTowerSeparation 0 nu' k := by
  intro z hz _ _
  have hempty : gJoinEichSet 0 nu' k = (∅ : Set (levelQuot (DSq 0 : Type) (k + 2))) := by
    ext w
    simp only [gJoinEichSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨j, -, -⟩
    exact absurd j.isLt (by omega)
  rw [hempty, Subgroup.closure_empty] at hz
  exact hz

/-- The handle-tower generators are central in the level quotient (they are images of
`γ_{k+1}`-elements), so their span is normal. -/
theorem gJoin_eichSet_central
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ} :
    Subgroup.closure (gJoinEichSet h nu' k)
      ≤ Subgroup.center (levelQuot (DSq h : Type) (k + 2)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z ⟨j, a, (rfl | rfl)⟩
  · refine Subgroup.mem_center_iff.2 fun x => ?_
    exact gTower_img_central
      (gTower_zpow_dvd_mem (by omega) ⟨a, by rw [Nat.add_sub_cancel]⟩ _) x
  · refine Subgroup.mem_center_iff.2 fun x => ?_
    exact gTower_img_central
      (gTower_zpow_dvd_mem (by omega) ⟨a, by rw [Nat.add_sub_cancel]⟩ _) x

theorem gJoin_eichSub_normal
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ} :
    (Subgroup.closure (gJoinEichSet h nu' k)).Normal := by
  constructor
  intro n hn g
  have hc : g * n = n * g := Subgroup.mem_center_iff.1 (gJoin_eichSet_central hn) g
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hn

/-- ⭐⭐⭐ **The separation, granted the bookkeeping**: a reach class all of whose handle rows
read `2^{k+1}`-divisibly lies in the knob span.  This is Labute's `Im δ = ⋂ ker Δ` in the
campaign's vocabulary, and it is the *whole* of what `GTowerDefectVanishing` needs beyond the
depth-`2` base. -/
theorem gJoin_reach_sep
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ}
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (HS : GJoinTowerSeparation h nu' (k + 2))
    {z : levelQuot (DSq h : Type) (k + 2 + 2)} (hz : z ∈ gTowerReach h nu' (k + 2))
    (hU : ∀ j : Fin h, z ∈ gJoinLayerDvd h (gJoinRowU j) (k + 2))
    (hV : ∀ j : Fin h, z ∈ gJoinLayerDvd h (gJoinRowV j) (k + 2)) :
    z ∈ Subgroup.closure (gTowerKnobSet h nu' (k + 2)) := by
  haveI := gJoin_eichSub_normal (h := h) (nu' := nu') (k := k + 2)
  have hmem : z ∈
      ((Subgroup.closure (gTowerKnobSet h nu' (k + 2)) :
        Subgroup (levelQuot (DSq h : Type) (k + 2 + 2))) :
          Set (levelQuot (DSq h : Type) (k + 2 + 2))) *
      ((Subgroup.closure (gJoinEichSet h nu' (k + 2)) :
        Subgroup (levelQuot (DSq h : Type) (k + 2 + 2))) :
          Set (levelQuot (DSq h : Type) (k + 2 + 2))) := by
    rw [← Subgroup.mul_normal]
    exact gJoin_reach_le (by omega) hx0 hz
  obtain ⟨n, hn, t, ht, rfl⟩ := hmem
  have hn' : n ∈ Subgroup.closure (gTowerKnobSet h nu' (k + 2)) := hn
  have ht' : t ∈ Subgroup.closure (gJoinEichSet h nu' (k + 2)) := ht
  have hprod : (fun x1 x2 => x1 * x2) n t = n * t := rfl
  rw [hprod] at hU hV ⊢
  have hteq : t = n⁻¹ * (n * t) := by group
  have hone : t = 1 := by
    refine HS t ht' (fun j => ?_) (fun j => ?_)
    · rw [hteq]
      exact Subgroup.mul_mem _
        (Subgroup.inv_mem _ (gJoin_knob_le_layerDvd (gJoinRowU j) hn')) (hU j)
    · rw [hteq]
      exact Subgroup.mul_mem _
        (Subgroup.inv_mem _ (gJoin_knob_le_layerDvd (gJoinRowV j) hn')) (hV j)
  rw [hone, mul_one]
  exact hn'

end ReachSplit

/-! ## §8 The join

Everything above assembles.  The `χ`-restricted vanishing interface `GJoinDefectVanishing h`
follows from exactly two further inputs, both uniform in the class:

* `GJoinBase h`, wave 74's depth-`2` base `GTowerLayerReach h ν' 2` at every selected marking
  (the class-four layer, from the committed per-class record).  This is the ENGINE lane's
  stated W75 item and is **not** discharged here;
  ⚠⚠ **[W78-HOUSE, as of `e6bbd2b9`: `GJoinBase h` is REFUTED, at every `h`.**
  `gDecide_not_joinBase` (`SqCore/GradedBaseDecide.lean`, wave 77) proves `¬ GJoinBase h` from
  one group of order sixteen, so every theorem below that takes `hbase : GJoinBase h` is now
  **vacuous**: `gJoin_defectVanishing_of_base`, `gJoin_supply_of_base` and
  `gJoin_markTransitivity_of_base` are correct statements about a hypothesis nothing can
  supply.  Read "not discharged here" as "not dischargeable at all at this depth".  What is
  **not** refuted is the target: `SqClassClearingSupply h k` and `SqLamMarkTransitivity h`
  stand exactly where wave 67 left them, and the depth-`3` re-cut is costed in
  `docs/dyadic/w77-decide-note.md` §T2, where it is shown to need a class-four supply witness
  as well.]**
* `GJoinSeparationAll h`, the `𝔽₂`-independence bookkeeping `GJoinTowerSeparation` of §7 at
  every marking and every depth `k ≥ 2`.

`SqClassClearingSupply h k` at **every** class, and with it the whole `h ≥ 1` residual, needs
a **third**: `GTowerKnobRealizable h`, wave 74's extraction interface, which the recursion of
§3 consumes and which is likewise not discharged here.  See
`gJoin_markTransitivity_of_base`'s own statement below, and `w75-join-note.md`'s headline,
both of which name three inputs.
[W76-HOUSE, watch round 13: this header previously wrote "the whole `h ≥ 1` residual" into
the two-input sentence, contradicting that theorem 45 lines further down inside one file.]

Nothing else is left of the functional side: the vanishing itself is a theorem
(`gDeltaDefectVanishing_holds`), the torsion gap is closed (§2), the knobs are invisible
(§5), the invisible tower is a knob (§6), and the visible towers are read on the nose (§7).

⚠⚠ **[W81-HOUSE, as of `6f2916f3`: EVERY ITEM THIS HEADER LEAVES OPEN IS NOW SETTLED, and
the three-input framing is superseded.**  Taking the three named inputs in turn:
`GJoinBase h` is REFUTED (already marked above, `gDecide_not_joinBase`);
`GJoinSeparationAll h` is a THEOREM (`gExt_separationAll`, `SqCore/GradedExtraction.lean`,
wave 79); `GTowerKnobRealizable h` is neither - it is unproved as quantified (wave 79) and was
BYPASSED, by re-running the recursion in `SqCore/GradedXFree.lean` §8 under an `x₁`-freeness
clause on which the weakened `GXfKnobRealizable h` is a theorem.  Both conclusions this header
tracks are now unconditional at every `h`: `SqClassClearingSupply h k` at every class is
`gOdd_supply`, and `SqLamMarkTransitivity h` is `gOdd_markTransitivity`, both in
`SqCore/GradedOddClose.lean`.  What is **not** superseded: everything this file actually
proves - §§1-7, the join itself, and the refutation record above - stands unchanged, and the
`Prop`s it defines are still the names the rest of the corpus uses.]** -/

section Assembly

variable {h : ℕ}

variable (h) in
/-- The separation bookkeeping of §7, at every selected marking and every depth `k ≥ 2`.

⚠ **[W81-HOUSE, as of `6f2916f3`: DISCHARGED, at every `h`** - `gExt_separationAll (h : ℕ) :
GJoinSeparationAll h` (`SqCore/GradedExtraction.lean`, wave 79), unconditional.  Every
`hsep : GJoinSeparationAll h` binder anywhere in the graded corpus is therefore satisfiable and
routinely satisfied; treating it as an open item is a wave-80-era error (see
`SqCore/GradedUniformGen.lean` §7 and `docs/dyadic/w80-uniform-note.md`, both annotated).]** -/
def GJoinSeparationAll : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ),
    2 ≤ k → GJoinTowerSeparation h nu' k

variable (h) in
/-- Wave 74's depth-`2` base, at every selected marking.

⚠⚠ **FALSE at every `h`**, as of `e6bbd2b9`: `gDecide_not_joinBase`
(`SqCore/GradedBaseDecide.lean`).  The three theorems below that consume it are vacuous.  See
§8's header for what this does and does not settle. -/
def GJoinBase : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      GTowerLayerReach h nu' 2

/-- ⭐⭐⭐ **The vanishing interface, from the base and the separation.**  This is the join:
the defect lands in the reach by the base, its handle rows read zero because the dressing is
`χ`-trivial and Labute's Lemma 4(2) kills dressed relators outright, and §7 converts that
into knob-span membership. -/
theorem gJoin_defectVanishing_of_base (hbase : GJoinBase h) (hsep : GJoinSeparationAll h) :
    GJoinDefectVanishing h := by
  intro nu' j hsigma hx0 k hk a hal han hac hai hrel
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hreach := gTower_defect_reach_of_base (hbase nu' hsigma hx0) hsigma hx0 j
    (by omega : 2 ≤ k' + 2) hal han hrel
  have hzero : ∀ c : Fin (sqRank h) → ℤ_[2],
      gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
    fun c => gJoin_reading_zero c nu' j ⟨hal, han, hac⟩
  refine gJoin_reach_sep hx0 (hsep nu' (k' + 2) (by omega)) hreach (fun jj => ?_) (fun jj => ?_)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)

/-- ⭐⭐⭐ **The per-class supply, at every class.** -/
theorem gJoin_supply_of_base (hbase : GJoinBase h) (hsep : GJoinSeparationAll h)
    (HR : GTowerKnobRealizable h) : ∀ k, SqClassClearingSupply h k :=
  gJoin_supply_of_vanishing (gJoin_defectVanishing_of_base hbase hsep) HR

/-- ⭐⭐⭐ **The `h ≥ 1` residual, from three named inputs.**  Two of them are wave 74's own
open items (the depth-`2` base and the knob realizability); the third is the `𝔽₂`
bookkeeping of §7.  The functional half of Labute's Lemma 4 is fully discharged.

⚠⚠ **[W79-HOUSE, as of `527adf51`: the depth-`2` base is REFUTED, not open.**  `GJoinBase h` is
false at every `h` (`gDecide_not_joinBase`, `SqCore/GradedBaseDecide.lean`), so this theorem is
vacuous and the sentence above should read "one of them is wave 74's own open item (the knob
realizability)".  See the marker on the `GJoinBase` definition and on §8's header.  Wave 78's
annotation pass marked both of those and left this consumer docstring calling the refuted `Prop`
an open item.  The live route to the same conclusion is
`gJoin_markTransitivity_of_vanishing`.]** -/
theorem gJoin_markTransitivity_of_base (hbase : GJoinBase h) (hsep : GJoinSeparationAll h)
    (HR : GTowerKnobRealizable h) : SqLamMarkTransitivity h :=
  limFinal_markTransitivity (gJoin_supply_of_base hbase hsep HR)

end Assembly

/-! ## §9 Axiom pins -/


section AxiomPins

#print axioms GQ2.Dyadic.SqCore.GJoinChiAdm
#print axioms gJoin_chiAdm_rows
#print axioms gJoin_slot_dichotomy
#print axioms gJoin_slot_sq
#print axioms gJoin_reading_zero
#print axioms gJoin_chiSq_of_gammaTwo
#print axioms gJoin_chiSq_mul_correction
#print axioms GQ2.Dyadic.SqCore.GJoinDefectVanishing
#print axioms gJoin_defectVanishing_of_tower
#print axioms GQ2.Dyadic.SqCore.GJoinChiSupply
#print axioms gJoin_supply_of_chiSupply
#print axioms gJoin_chiSupply_three
#print axioms gJoin_clear_step
#print axioms gJoin_supply_of_vanishing
#print axioms gJoin_markTransitivity_of_vanishing
#print axioms GQ2.Dyadic.SqCore.gJoinVanish
#print axioms gJoin_mem_vanish
#print axioms gJoin_isClosed_vanish
#print axioms gJoin_zpow_vanish
#print axioms gJoin_delta_pivot
#print axioms gJoin_delta_xOne
#print axioms gJoin_delta_eichU
#print axioms gJoin_delta_eichV
#print axioms gJoin_delta_zpow
#print axioms gJoin_chiSq_zpow
#print axioms gJoin_Yval_add_one
#print axioms gJoin_one_add_Yval_inv
#print axioms GQ2.Dyadic.SqCore.gJoinChiFour
#print axioms gJoin_isClosed_chiFour
#print axioms gJoin_chi_far
#print axioms gJoin_chi_far_inv
#print axioms gJoin_adm_reading
#print axioms gJoin_knob_dvd
#print axioms gJoin_bundle_dvd
#print axioms GQ2.Dyadic.SqCore.gJoinDvdSub
#print axioms GQ2.Dyadic.SqCore.gJoinLayerDvd
#print axioms gJoin_mem_layerDvd
#print axioms gJoin_knob_le_layerDvd
#print axioms GQ2.Dyadic.SqCore.gJoinCent
#print axioms gJoin_zpow_commP
#print axioms gJoin_x1_eq
#print axioms gJoin_xOne_tower_adm
#print axioms gJoin_xOne_tower_knob
#print axioms GQ2.Dyadic.SqCore.gJoinRowU
#print axioms GQ2.Dyadic.SqCore.gJoinRowV
#print axioms gJoin_rowU_eichU
#print axioms gJoin_rowU_eichV
#print axioms gJoin_rowU_xOne
#print axioms gJoin_rowV_eichV
#print axioms gJoin_rowV_eichU
#print axioms gJoin_eichU_tower_reading
#print axioms gJoin_eichV_tower_reading
#print axioms gJoin_eichU_tower_notMem
#print axioms GQ2.Dyadic.SqCore.gJoinEichSet
#print axioms gJoin_reach_le
#print axioms GQ2.Dyadic.SqCore.GJoinTowerSeparation
#print axioms gJoin_towerSeparation_handleFree
#print axioms gJoin_eichSet_central
#print axioms gJoin_eichSub_normal
#print axioms gJoin_reach_sep
#print axioms GQ2.Dyadic.SqCore.GJoinSeparationAll
#print axioms GQ2.Dyadic.SqCore.GJoinBase
#print axioms gJoin_defectVanishing_of_base
#print axioms gJoin_supply_of_base
#print axioms gJoin_markTransitivity_of_base

end AxiomPins

end SqCore

end Dyadic

end GQ2
