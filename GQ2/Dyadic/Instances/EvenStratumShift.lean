/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenStratumFrame

/-!
# W73-STRATUM: the `α = 1` relator shift, verified against its prose

Lane **W73-STRATUM**, ticket 1.  `StageAbstractionEvenRawSpan.lean` §0 records **in prose**
(lines 44-46 and 65) that the coordinate-`0` row of its literal factorization is *false* at
`α = 1`, and wave 72 relayed that claim without verifying it.  This module settles it in Lean.

The prose is **correct**, and the failure is exactly one atom wide.

* **§1** computes the true `α = 1` shift word.  `MarkedCore.nWord 1 a b c d = a⁴[a,b][c,d]`, and
  `4 = 2 * 2` has an *even* half, so `evenRawPow_of_even_half` applies where
  `evenRawPow_of_odd_half` applies at `2 ≤ α`: the diagonal atom `w₀²·[w₀, base 0]` never
  appears.  `evenStratumShift_n_one` is the resulting literal factorization, valid at `α = 1`
  with no `2 ≤ α` anywhere.
* **§2** measures the gap: `evenRawDbarWord` overshoots the true `α = 1` shift by exactly the
  diagonal atom (`evenStratumShift_dbarWord_eq_diagonalAtom_mul`), so `evenRawStageShift_n`'s
  conclusion at `α = 1` is equivalent to the vanishing of that atom.
* **§3** refutes it: a discrete cyclic group of order eight has a depth-`2` element of `Q₄` whose
  square is not `1`, so `evenStratum_no_rawStageShift_one` says the conclusion of
  `evenRawStageShift_n` is **not** available at `α = 1`.

## What this does and does not say

It says that the *committed middle input* of `evenClimb_defectReachable` on the `N` row, namely
`evenSharpDbarShiftSupply_n` and through it `evenRawStageShift_n`, is unavailable at `α = 1`
as a matter of fact rather than of unproved binders.  Wave 72's §3.1 relayed this as prose; it
is now a theorem, and `EvenStratumClimbN` is therefore blocked at a *named* step.

It says nothing about `EvenStratumClimbN` itself, which quantifies over `EvenSharpDbarShiftSupply`
only through `evenClimb_defectReachable`; a different shift supply, built from
`evenStratumShiftWordOne` instead of `evenRawDbarWord`, is not refuted by anything here.  §1 is
written so that such a rebuild has its literal factorization already available.  And it says
nothing whatever about
`Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`, in either direction.

## Contents

1. §1 the `α = 1` core block, the `α = 1` shift word, and the literal factorization.
2. §2 the diagonal atom as the exact discrepancy, and the conditional consequence.
3. §3 the witness group and the refutation.
4. §4 axiom pins.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## §1 The literal factorization at `α = 1`

Everything here is the `α ≥ 2` development of `StageAbstractionEvenRawSpan.lean` §3-§4 run at
the *other* parity of the first letter's exponent.  The two central regrouping helpers are
re-declared because the originals are `private`. -/

section ShiftOne

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h k : ℕ}

private theorem evenStratumShiftAssembleOne {H' : Type*} [Group H'] (X P Q B C : H')
    (hB : ∀ t : H', Commute B t) : X * (P * B) * (Q * C) = X * P * Q * (B * C) := by
  calc
    X * (P * B) * (Q * C) = X * P * (B * Q) * C := by group
    _ = X * P * (Q * B) * C := by rw [(hB Q).eq]
    _ = X * P * Q * (B * C) := by group

private theorem evenStratumShiftAssemble {H' : Type*} [Group H'] (C Hh d D : H')
    (hd : ∀ t : H', Commute d t) : (C * Hh)⁻¹ * (C * d * (Hh * D)) = d * D := by
  calc
    (C * Hh)⁻¹ * (C * d * (Hh * D)) = (C * Hh)⁻¹ * (C * (d * Hh) * D) := by group
    _ = (C * Hh)⁻¹ * (C * (Hh * d) * D) := by rw [(hd Hh).eq]
    _ = d * D := by group

/-- **The `α = 1` core block**: `evenRawCoreDbarWord` with its diagonal atom deleted.  The two
bracket pairs are untouched; only the first letter's contribution changes with `α`. -/
def evenStratumShiftCoreOne
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  commP (correction 1) (base 0) * commP (correction 0) (base 1) *
    (commP (correction 3) (base 2) * commP (correction 2) (base 3))

/-- **The `α = 1` shift word**: the `α = 1` core block times the (α-independent) handle block. -/
def evenStratumShiftWordOne
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  evenStratumShiftCoreOne base correction * evenRawHandleDbarWord base correction

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The `α = 1` core block lands in the central involutive layer. -/
theorem evenStratumShiftCoreOne_mem_zLayer (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenStratumShiftCoreOne base correction ∈ zLayer G k := by
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (Subgroup.mul_mem _ ?_ ?_) <;>
  exact commP_mem_zLayer k hk (hdepth _) _

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The `α ≥ 2` core block is the `α = 1` one times the diagonal atom.**  A regrouping, no
hypotheses: the two words differ by exactly `w₀² · [w₀, base 0]`. -/
theorem evenStratumShift_coreDbarWord_eq
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenRawCoreDbarWord base correction =
      correction 0 ^ 2 * commP (correction 0) (base 0) *
        evenStratumShiftCoreOne base correction := by
  rw [evenRawCoreDbarWord, evenStratumShiftCoreOne]
  group

/-- **The `N₁` core factorization.**  The `α = 1` analogue of `evenRawNWord_mul_lambdaImage`:
the exponent is `2 + 2 ^ 1 = 4 = 2 * 2`, whose half `2` is **even**, so the diagonal atom of the
first letter is killed by `evenRawPow_of_even_half` instead of surviving. -/
theorem evenStratumShift_nWordOne_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    MarkedCore.nWord 1 (base 0 * correction 0) (base 1 * correction 1)
        (base 2 * correction 2) (base 3 * correction 3) =
      MarkedCore.nWord 1 (base 0) (base 1) (base 2) (base 3) *
        evenStratumShiftCoreOne base correction := by
  have hexp : 2 + 2 ^ 1 = 2 * 2 := by norm_num
  simp only [MarkedCore.nWord, evenStratumShiftCoreOne, hexp]
  rw [evenRawPow_of_even_half k hk (hdepth 0) (base 0) (even_two),
    evenRawHandlePair_mul k hk (base 0) (base 1) (hdepth 0) (hdepth 1),
    evenRawHandlePair_mul k hk (base 2) (base 3) (hdepth 2) (hdepth 3)]
  exact evenStratumShiftAssembleOne _ _ _ _ _
    (zLayer_commute (Subgroup.mul_mem _ (commP_mem_zLayer k hk (hdepth 1) _)
      (commP_mem_zLayer k hk (hdepth 0) _)))

/-- **The `N₁` relator shift, literally.**  The `α = 1` replacement for `evenRawStageShift_n`:
an equality in `Q_{k+1}`, with **no** `2 ≤ α` hypothesis, whose right-hand side is
`evenStratumShiftWordOne` rather than `evenRawDbarWord`. -/
theorem evenStratumShift_n_one (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    stageShift (nStageWord 1 h (le_refl 1)) base correction =
      evenStratumShiftWordOne base correction := by
  show (MarkedCore.nRelWord 1 base)⁻¹ *
    MarkedCore.nRelWord 1 (fun i ↦ base i * correction i) = _
  simp only [MarkedCore.nRelWord]
  rw [evenStratumShift_nWordOne_mul_lambdaImage k hk base correction hdepth,
    evenRawHandleWord_mul_lambdaImage h k hk base correction hdepth, evenStratumShiftWordOne]
  exact evenStratumShiftAssemble _ _ _ _
    (zLayer_commute (evenStratumShiftCoreOne_mem_zLayer k hk base correction hdepth))

/-! ## §2 The exact discrepancy

`evenRawDbarWord` is the `α ≥ 2` right-hand side.  At `α = 1` it overshoots the true shift by
the diagonal atom, and by nothing else. -/

/-- **The measured gap.**  At `α = 1` the `α ≥ 2` shift word equals the diagonal atom times the
true relator shift.  Consequently `evenRawStageShift_n`'s conclusion holds at `α = 1` for a
given `(base, correction)` **iff** that atom is trivial there. -/
theorem evenStratumShift_dbarWord_eq_diagonalAtom_mul (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawDbarWord base correction =
      correction 0 ^ 2 * commP (correction 0) (base 0) *
        stageShift (nStageWord 1 h (le_refl 1)) base correction := by
  rw [evenStratumShift_n_one h k hk base correction hdepth, evenRawDbarWord,
    evenStratumShift_coreDbarWord_eq, evenStratumShiftWordOne]
  group

/-- **The conditional consequence.**  If the `α ≥ 2` factorization did hold at `α = 1` for some
data, the diagonal atom of that data would be trivial. -/
theorem evenStratumShift_diagonalAtom_eq_one_of_rawShift (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1))
    (hshift : stageShift (nStageWord 1 h (le_refl 1)) base correction =
      evenRawDbarWord base correction) :
    correction 0 ^ 2 * commP (correction 0) (base 0) = 1 := by
  have h1 := evenStratumShift_dbarWord_eq_diagonalAtom_mul h k hk base correction hdepth
  rw [← hshift] at h1
  refine mul_right_cancel (b := stageShift (nStageWord 1 h (le_refl 1)) base correction) ?_
  rw [one_mul, ← h1]

end ShiftOne

/-! ## §3 The refutation

One profinite group suffices, and the smallest one does: the cyclic group of order eight with
its discrete topology.  Its `λ₂` contains an element of order four, so the diagonal atom of a
correction supported at coordinate `0` is nontrivial in `Q₄`. -/

section Witness

/-- A discrete abelian group's two-central step is contained in any subgroup absorbing the
squares of its input: the commutator half of `twoCentralSucc` is trivial and the topological
closure is inert. -/
theorem evenStratumShift_twoCentralSucc_le {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [DiscreteTopology A] {H K : Subgroup A}
    (hHK : ∀ v ∈ H, v ^ 2 ∈ K) : twoCentralSucc H ≤ K := by
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_discrete _)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hHK v hv
  · refine Subgroup.commutator_le.2 fun g _ x _ ↦ ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2 (mul_comm g x)]
    exact one_mem K

/-- **The two-central tower of a discrete abelian group sinks into the `2`-power subgroups**:
`λ_{k+1} ≤ A^{2^k}`.  Enough to compute the tower of a finite cyclic `2`-group from above. -/
theorem evenStratumShift_twoCentralSeries_le_pow {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [DiscreteTopology A] (k : ℕ) :
    twoCentralSeries A (k + 1) ≤ (powMonoidHom (2 ^ k) : A →* A).range := by
  induction k with
  | zero =>
      intro x _
      exact ⟨x, by simp [powMonoidHom]⟩
  | succ k ih =>
      rw [twoCentralSeries_succ A (Nat.le_add_left 1 k)]
      refine evenStratumShift_twoCentralSucc_le fun v hv ↦ ?_
      obtain ⟨x, rfl⟩ := ih hv
      refine ⟨x, ?_⟩
      show x ^ 2 ^ (k + 1) = (x ^ 2 ^ k) ^ 2
      rw [← pow_mul, ← pow_succ]

/-- The witness group: the cyclic group of order eight, discrete, hence profinite. -/
abbrev EvenStratumShiftWitness : Type := Multiplicative (ZMod 8)

namespace EvenStratumShiftWitness

instance : TopologicalSpace EvenStratumShiftWitness := ⊥
instance : DiscreteTopology EvenStratumShiftWitness := ⟨rfl⟩
instance : ContinuousMul EvenStratumShiftWitness := ⟨continuous_of_discreteTopology⟩
instance : ContinuousInv EvenStratumShiftWitness := ⟨continuous_of_discreteTopology⟩
instance : IsTopologicalGroup EvenStratumShiftWitness := { }

end EvenStratumShiftWitness

/-- Every element of the witness group has exponent dividing eight. -/
theorem evenStratumShiftWitness_pow_eight (x : EvenStratumShiftWitness) : x ^ 8 = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod 8, Multiplicative.ofAdd a = x := ⟨Multiplicative.toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- The fourth layer of the witness group's two-central tower is trivial, so `Q₄` is the whole
group. -/
theorem evenStratumShiftWitness_twoCentralSeries_four :
    twoCentralSeries EvenStratumShiftWitness 4 = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine le_trans (evenStratumShift_twoCentralSeries_le_pow 3) ?_
  rintro _ ⟨x, rfl⟩
  show (x ^ 2 ^ 3 : EvenStratumShiftWitness) ∈ (⊥ : Subgroup EvenStratumShiftWitness)
  rw [Subgroup.mem_bot, show (2 : ℕ) ^ 3 = 8 from rfl]
  exact evenStratumShiftWitness_pow_eight x

/-- The depth-`2` element of `Q₄` used by the refutation: the image of the square of a
generator. -/
def evenStratumShiftWitnessP : levelQuot EvenStratumShiftWitness 4 :=
  levelMk EvenStratumShiftWitness 4 (Multiplicative.ofAdd (1 : ZMod 8) ^ 2)

theorem evenStratumShiftWitnessP_mem :
    evenStratumShiftWitnessP ∈ lambdaImage EvenStratumShiftWitness 2 4 :=
  ⟨_, sq_mem_twoCentralSeries_succ EvenStratumShiftWitness (Subgroup.mem_top _), rfl⟩

/-- **The diagonal atom can be nontrivial**: the square of that depth-`2` element is not `1` in
`Q₄`.  This is the whole content of the refutation. -/
theorem evenStratumShiftWitnessP_sq_ne_one : evenStratumShiftWitnessP ^ 2 ≠ 1 := by
  intro hcon
  rw [evenStratumShiftWitnessP, ← map_pow] at hcon
  have hmem : (Multiplicative.ofAdd (1 : ZMod 8) ^ 2) ^ 2 ∈
      twoCentralSeries EvenStratumShiftWitness 4 :=
    (QuotientGroup.eq_one_iff _).mp hcon
  rw [evenStratumShiftWitness_twoCentralSeries_four, Subgroup.mem_bot, ← pow_mul,
    ← ofAdd_nsmul] at hmem
  exact absurd (Multiplicative.ofAdd.injective hmem) (by decide)

/-- **The prose is correct: `evenRawStageShift_n`'s conclusion is false at `α = 1`.**  There is
no way to weaken its `2 ≤ α` to `1 ≤ α`: at `α = 1` the literal shift of the `N` relator is
`evenStratumShiftWordOne`, which differs from `evenRawDbarWord` by the diagonal atom, and that
atom is nontrivial already on the cyclic group of order eight. -/
theorem evenStratum_no_rawStageShift_one :
    ¬ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
        [T2Space G] [TotallyDisconnectedSpace G] (h k : ℕ), 3 ≤ k →
        ∀ (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)),
        (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) →
        stageShift (nStageWord 1 h (le_refl 1)) base correction =
          evenRawDbarWord base correction := by
  intro hall
  have hdepth : ∀ i : Fin (MarkedCore.coreRank 0),
      (if i = 0 then evenStratumShiftWitnessP else 1) ∈
        lambdaImage EvenStratumShiftWitness (3 - 1) (3 + 1) := by
    intro i
    by_cases hi : i = 0
    · rw [if_pos hi]
      exact evenStratumShiftWitnessP_mem
    · rw [if_neg hi]
      exact Subgroup.one_mem _
  have hatom := evenStratumShift_diagonalAtom_eq_one_of_rawShift
    (G := EvenStratumShiftWitness) 0 3 (by omega) (fun _ ↦ 1)
    (fun i ↦ if i = 0 then evenStratumShiftWitnessP else 1) hdepth
    (hall EvenStratumShiftWitness 0 3 (by omega) (fun _ ↦ 1)
      (fun i ↦ if i = 0 then evenStratumShiftWitnessP else 1) hdepth)
  refine evenStratumShiftWitnessP_sq_ne_one ?_
  simpa [commP] using hatom

end Witness

/-! ## §4 Axiom pins -/

section Pins

#print axioms evenStratumShiftCoreOne
#print axioms evenStratumShiftWordOne
#print axioms evenStratumShiftCoreOne_mem_zLayer
#print axioms evenStratumShift_coreDbarWord_eq
#print axioms evenStratumShift_nWordOne_mul_lambdaImage
#print axioms evenStratumShift_n_one
#print axioms evenStratumShift_dbarWord_eq_diagonalAtom_mul
#print axioms evenStratumShift_diagonalAtom_eq_one_of_rawShift
#print axioms evenStratumShift_twoCentralSucc_le
#print axioms evenStratumShift_twoCentralSeries_le_pow
#print axioms evenStratumShiftWitness_pow_eight
#print axioms evenStratumShiftWitness_twoCentralSeries_four
#print axioms evenStratumShiftWitnessP
#print axioms evenStratumShiftWitnessP_mem
#print axioms evenStratumShiftWitnessP_sq_ne_one
#print axioms evenStratum_no_rawStageShift_one

end Pins

end

end GQ2.Dyadic.StageGeneric
