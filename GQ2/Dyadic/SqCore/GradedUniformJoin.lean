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
  them is the second half of his Lemma 4 and needs two further inputs, both named here:
  the knobs must be invisible to the functionals at the layer bit, and the admissible
  towers must be detected by them.

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
delivers: the functional side speaks *exactly* on this family. -/
def GJoinDefectVanishing : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    ∀ k, 2 ≤ k → ∀ a : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a i) = 1) → (∀ i, nu' (a i) = 1) → (∀ i, chiSq h (a i) = 1) →
      SqModTwoIndep (sqArbFrame h nu' j a) →
      sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) (k + 1) →
      levelMk (DSq h : Type) (k + 2) (sqRelWord (sqArbFrame h nu' j a))
        ∈ Subgroup.closure (gTowerKnobSet h nu' k)

/-- `GTowerDefectVanishing` is the stronger hypothesis. -/
theorem gJoin_defectVanishing_of_tower (H : GTowerDefectVanishing h) :
    GJoinDefectVanishing h :=
  fun nu' j hs hx k hk a hal han _ hai hrel => H nu' j hs hx k hk a hal han hai hrel

variable (h) in
/-- The supply with the `χ`-clause carried: the clearing sets, restricted to `χ`-trivial
dressings.  §2 makes this restriction free. -/
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
`gTower_supply_of_vanishing` with the torsion gap of its FUNC sibling closed. -/
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

/-! ## §4 Axiom pins -/

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

end AxiomPins

end SqCore

end Dyadic

end GQ2
