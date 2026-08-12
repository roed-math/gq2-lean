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
open GQ2.Dyadic.Certificates.LSqStokes

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

/-! ## §4 The `α = 1` quadratic-initial Gram, in the frame interface

Wave 72's queue item 1 asked for this Gram to be computed.  It **already existed**: wave 70's
`EvenAlphaOne.evenAlphaOneNCupForm` is the quadratic-initial form of `nRelWord 1`, derived from
`evenAlphaOne_nRelWord_fib` and not asserted.  What was missing is the bridge into the shape
`Frame.IsCupAdapted` demands, which takes the Gram as a function of the full matrix of character
products rather than of two vectors.  `evenStratumGramOne` is that bridge, and §4.1 checks it
against wave 70's form on the nose.

The difference from `evenFrameGram h` is exactly the single entry `M 0 0`, which is the frame
shadow of §1: the diagonal atom that the `α = 1` parity kills is the same atom that produces the
`(0,0)` entry of the `α ≥ 2` Gram. -/

section GramOne

/-- **The `α = 1` even quadratic-initial Gram at rank `coreRank h`**, in the shape of the `gram`
parameter of `Frame.IsCupAdapted`: `evenFrameGram h` with its `(0,0)` entry deleted.  Purely
hyperbolic: the plane `(x₀, x₁)`, the plane `(σ, x₂)`, and one plane per handle. -/
def evenStratumGramOne (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) : ZMod 2 :=
  (M 0 1 + M 1 0) + (M 2 3 + M 3 2)
    + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
        + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j))

theorem evenStratumGramOne_expand (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenStratumGramOne h M = (M 0 1 + M 1 0) + (M 2 3 + M 3 2)
      + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
          + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j)) := rfl

/-- **It is wave 70's committed `α = 1` `N` Gram.**  Contracting `evenStratumGramOne h` against
the matrix of coordinate products of two vectors returns `evenAlphaOneNCupForm`, which
`EvenAlphaOne.evenAlphaOne_obsH2_DN` identifies with the `α = 1` relator obstruction.  So no Gram
is invented here: only re-shaped. -/
theorem evenStratumGramOne_alphaOneNCupForm (h : ℕ)
    (v w : Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenStratumGramOne h (fun i j ↦ v i * w j) =
      GQ2.Dyadic.EvenAlphaOne.evenAlphaOneNCupForm v w := rfl

/-- **The two Grams differ by exactly one entry.**  `evenFrameGram h` is `evenStratumGramOne h`
plus the `(0,0)` entry, which is the `x₀`-Bockstein term that `2 + 2 ^ α ≡ 2 (mod 4)` supplies at
`α ≥ 2` and `2 + 2 ^ 1 = 4` does not. -/
theorem evenStratumGramOne_add_diag (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenFrameGram h M = M 0 0 + evenStratumGramOne h M := by
  rw [evenFrameGram_expand, evenStratumGramOne_expand]
  ring

/-- **THE `α = 1` GRAM IS ALTERNATING.**  Contracting it against a rank-one matrix returns `0`,
where `evenStratumFrame_gram_diag` returns `f 0` for `evenFrameGram h`.  This one line is why
wave 72's refutation cannot be reproduced against this Gram: the step that turned
cup-adaptedness into a statement about a single generator produces `0 = 0` here. -/
theorem evenStratumGramOne_diag {h : ℕ} (f : Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenStratumGramOne h (fun i j ↦ f i * f j) = 0 := by
  rw [evenStratumGramOne_alphaOneNCupForm]
  exact GQ2.Dyadic.EvenAlphaOne.evenAlphaOneNCupForm_self f

/-! ### §4.1 The purely hyperbolic model

`evenFrameGramModel h` is `headGram ⊥ H^{⊥(h+1)}`.  The `α = 1` model replaces the
non-alternating head by one more hyperbolic plane, so it is `H^{⊥(h+2)}` written on the same
carrier `evenFrameModel h`; §4.2 records that identification through `Fin.cons`. -/

/-- **The `α = 1` model Gram**: `H^{⊥(h+2)}` on the carrier `evenFrameModel h`, with the head
pair `(x₀, x₁)` read as a hyperbolic plane. -/
def evenStratumGramOneModel (h : ℕ) (z z' : evenFrameModel h) : ZMod 2 :=
  (z.1.1 * z'.1.2 + z.1.2 * z'.1.1) + hypGram z.2 z'.2

/-- **The adapter is the model Gram**, the `α = 1` twin of `evenFrameGram_modelCoord`. -/
theorem evenStratumGramOne_modelCoord (h : ℕ) (z z' : evenFrameModel h) :
    evenStratumGramOne h (fun i j ↦ evenFrameCoord i z * evenFrameCoord j z') =
      evenStratumGramOneModel h z z' := by
  rw [evenStratumGramOne_expand, evenStratumGramOneModel]
  simp only [evenFrameCoord_zero, evenFrameCoord_one, evenFrameCoord_two, evenFrameCoord_three,
    evenFrameCoord_handleU, evenFrameCoord_handleV, hypGram, Fin.sum_univ_succ]
  ring

private abbrev evenStratumPlane : ℕ → Type := fun _ ↦ ZMod 2 × ZMod 2

private theorem evenStratumCons_zero {h : ℕ} (a : ZMod 2 × ZMod 2)
    (p : Fin (h + 1) → ZMod 2 × ZMod 2) :
    Fin.cons (α := fun _ : Fin (h + 2) ↦ ZMod 2 × ZMod 2) a p 0 = a :=
  Fin.cons_zero _ _

private theorem evenStratumCons_succ {h : ℕ} (a : ZMod 2 × ZMod 2)
    (p : Fin (h + 1) → ZMod 2 × ZMod 2) (j : Fin (h + 1)) :
    Fin.cons (α := fun _ : Fin (h + 2) ↦ ZMod 2 × ZMod 2) a p j.succ = p j :=
  Fin.cons_succ _ _ _

private theorem evenStratumCons_self {h : ℕ} (r : Fin (h + 2) → ZMod 2 × ZMod 2) :
    Fin.cons (α := fun _ : Fin (h + 2) ↦ ZMod 2 × ZMod 2) (r 0) (fun j ↦ r j.succ) = r := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact evenStratumCons_zero _ _
  · exact evenStratumCons_succ _ _ j

/-- The relabelling `Fin (h + 2)` planes `↔` head plus `Fin (h + 1)` planes. -/
def evenStratumModelEquiv (h : ℕ) :
    (Fin (h + 2) → ZMod 2 × ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h where
  toFun r := (r 0, fun j ↦ r j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun z := Fin.cons (α := fun _ : Fin (h + 2) ↦ ZMod 2 × ZMod 2) z.1 z.2
  left_inv r := evenStratumCons_self r
  right_inv z :=
    Prod.ext (evenStratumCons_zero z.1 z.2) (funext fun j ↦ evenStratumCons_succ z.1 z.2 j)

@[simp] theorem evenStratumModelEquiv_apply (h : ℕ) (r : Fin (h + 2) → ZMod 2 × ZMod 2) :
    evenStratumModelEquiv h r = (r 0, fun j ↦ r j.succ) := rfl

/-- **The `α = 1` model Gram is the standard `H^{⊥(h+2)}`.**  Both hyperbolic plane counts are
`h + 2`; the only content is where the plane boundaries sit. -/
theorem evenStratumGramOneModel_hypGram (h : ℕ) (r r' : Fin (h + 2) → ZMod 2 × ZMod 2) :
    evenStratumGramOneModel h (evenStratumModelEquiv h r) (evenStratumModelEquiv h r') =
      hypGram r r' := by
  rw [evenStratumModelEquiv_apply, evenStratumModelEquiv_apply, evenStratumGramOneModel]
  conv_rhs => rw [← evenStratumCons_self r, ← evenStratumCons_self r']
  rw [hypGram_cons]

end GramOne

/-! ## §5 On the stratum an adapted coordinate system EXISTS

Wave 71's `evenStratum_no_adaptedModelEquiv` says there is no linear isomorphism carrying the
field cup form to `evenFrameGramModel h`, because the source is alternating and the target is
not.  Against the `α = 1` model Gram the same two facts give the opposite conclusion: the source
is alternating, the target is alternating, both are nondegenerate, and over `𝔽₂` that is a
complete invariant once the ranks agree.  The rank is pinned by the degree.

The committed alternating normal form `FieldDataEven.exists_cupForm_normalForm_alternating` is
applied directly to `frattiniFrameCup`, whose `IsCupFormFp2`, `NondegFp2` and Labute facts are
all committed; the Labute vector is `0` on the stratum by wave 71's
`evenStratum_kappa_eq_zero`. -/

section Adapted

open GQ2.ContCoh
open GQ2.Dyadic.LSquare GQ2.Dyadic.LSquare.FrattiniFrameSupply
open GQ2.Dyadic.EvenCyclotomicRange

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenStratumShiftScalar :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _

local instance evenStratumShiftContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **AN ADAPTED COORDINATE SYSTEM FOR THE `α = 1` GRAM EXISTS ON THE THIRD STRATUM.**  At a
field whose cyclotomic range lies in `evenRangePrin 2` and whose degree is `2 + 2h`, there is a
linear isomorphism of `H¹(G_K(2), 𝔽₂)` with `evenFrameModel h` carrying the field cup form to
`evenStratumGramOneModel h`.

This is the exact statement wave 71 refuted for `evenFrameGramModel h`, with the `α = 1` Gram in
place of the `α ≥ 2` one, and it is **true**. -/
theorem evenStratum_exists_gramOne_modelEquiv {h : ℕ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ∃ Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h,
      ∀ x y, frattiniFrameCup (K := K) x y = evenStratumGramOneModel h (Φ x) (Φ y) := by
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (4 + 2 * h) := by
    rw [card_H1_zmodTwo_maxProTwoGalK, hev]
    congr 1
    omega
  haveI : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨m, φ, hφ⟩ := FieldDataEven.exists_cupForm_normalForm_alternating
    (isCupFormFp2_frattiniFrameCup (K := K)) (nondegFp2_frattiniFrameCup (K := K))
    (fun w ↦ frattiniFrameCup_kappa (K := K) w)
    (GQ2.Dyadic.EvenStratum.evenStratum_kappa_eq_zero hle)
  have hm : m = h + 2 := by
    have h1 : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 4 ^ m := by
      rw [Nat.card_congr φ.toEquiv]
      simp
    have h2 : (2 : ℕ) ^ (2 * m) = 2 ^ (4 + 2 * h) := by
      rw [← hcard, h1, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hm
  refine ⟨φ.trans (evenStratumModelEquiv h), fun x y ↦ ?_⟩
  rw [hφ x y]
  exact (evenStratumGramOneModel_hypGram h (φ x) (φ y)).symm

/-! ### §5.1 From an adapted coordinate system to an adapted frame

The Gram-independent half of `evenFrame_of_adapted`, extracted: a family of group elements
realizing the coordinate functionals generates the Frattini quotient.  Its hypotheses are
satisfied by the realizers of any linear isomorphism onto `evenFrameModel h`, which is exactly
how §5.2 uses it, so it is not general-in-the-binders only. -/

/-- **Realizers of a coordinate system generate the Frattini quotient.**  No Gram enters: the
input is only that evaluation at `gens i` computes the `i`-th coordinate of a linear
isomorphism. -/
theorem evenStratum_levelTwoGen_of_realizers {h : ℕ}
    (Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h)
    (gens : Fin (MarkedCore.coreRank h) → maxProPQuotient 2 (GalK K))
    (hD : ∀ (i : Fin (MarkedCore.coreRank h)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) = evenFrameCoord i (Φ x)) :
    Subgroup.closure
      (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 2 (gens i)) = ⊤ := by
  classical
  by_contra hne
  haveI hFfin : Finite (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
    finite_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient 2
  haveI hFdisc : DiscreteTopology (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
    discreteTopology_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K)
      isProP_maxProPQuotient 2
  obtain ⟨c, hcH, hcne⟩ := frattiniFrame_exists_modTwo_character
    (frattiniFrame_levelTwo_mul_comm (maxProPQuotient 2 (GalK K)))
    (frattiniFrame_levelTwo_sq (maxProPQuotient 2 (GalK K))) hne
  set cQ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
    ⟨c.comp (levelMk (maxProPQuotient 2 (GalK K)) 2), by
      have h1 : Continuous c := continuous_of_discreteTopology
      exact h1.comp (continuous_levelMk (maxProPQuotient 2 (GalK K)) 2)⟩ with hcQ
  have hvanish : ∀ i, frattiniFrameEval
      (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) (gens i) = 0 := by
    intro i
    rw [frattiniFrameEval_characterClass]
    show Multiplicative.toAdd (c (levelMk (maxProPQuotient 2 (GalK K)) 2 (gens i))) = 0
    rw [hcH _ (Subgroup.subset_closure ⟨i, rfl⟩)]
    rfl
  have hΦ0 : Φ (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) = 0 := by
    refine evenFrameCoord_eq_zero _ fun i ↦ ?_
    rw [← hD i]
    exact hvanish i
  have hcc0 : SqCyclotomicFrattiniFrame.characterClass (K := K) cQ = 0 := by
    have hs := congrArg Φ.symm hΦ0
    rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
  apply hcne
  apply MonoidHom.ext
  intro fq
  obtain ⟨g, rfl⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) 2 fq
  have hg : frattiniFrameEval
      (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) g =
        Multiplicative.toAdd (cQ g) := frattiniFrameEval_characterClass cQ g
  rw [hcc0, frattiniFrameEval_zero] at hg
  show c (levelMk (maxProPQuotient 2 (GalK K)) 2 g) = 1
  have hone : cQ g = 1 := by
    apply Multiplicative.toAdd.injective
    rw [← hg]
    rfl
  exact hone

/-- **An adapted coordinate system produces a cup-adapted frame for the `α = 1` Gram**, at the
row table its own realizers carry.  The exact-row supply of `evenFrame_of_adapted` is not used
and not needed: `v` is read off the constructed generators, so the `rows` field is `rfl`.

What this therefore does **not** produce is a frame at a *prescribed* row table, and in
particular not at `vN 1`.  That is the whole remaining cost, and it is stated as such in §5.3. -/
theorem evenStratum_frame_of_gramOne_modelEquiv {h : ℕ}
    (hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)))
    (Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h)
    (hGram : ∀ x y, frattiniFrameCup (K := K) x y = evenStratumGramOneModel h (Φ x) (Φ y)) :
    ∃ (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
      (F : Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))),
      F.IsCupAdapted (evenStratumGramOne h) (evenFramePairing (K := K)) := by
  classical
  haveI := hfin
  choose gens hgens using fun i : Fin (MarkedCore.coreRank h) ↦
    frattiniFrameEval_realizable (K := K) hfin ((evenFrameCoordL i).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (MarkedCore.coreRank h))
      (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) = evenFrameCoord i (Φ x) := fun i x ↦ hgens i x
  refine ⟨fun i ↦ chiCycKTwo (K := K) (gens i),
    ⟨gens, fun _ ↦ rfl, evenStratum_levelTwoGen_of_realizers Φ gens hD⟩, ?_⟩
  intro c d
  show frattiniFrameCup (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) d) =
    evenStratumGramOne h (fun i j ↦ Multiplicative.toAdd (c (gens i)) *
      Multiplicative.toAdd (d (gens j)))
  rw [hGram, ← evenStratumGramOne_modelCoord]
  congr 1
  funext i j
  rw [← hD i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
    ← hD j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
    frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]

/-! ### §5.2 The answer to wave 72's queue item 1 -/

/-- **A FRAME CUP-ADAPTED FOR THE `α = 1` GRAM EXISTS ON THE THIRD STRATUM.**  At a field whose
cyclotomic range lies in `evenRangePrin 2` and whose degree is `2 + 2h`, some row table carries a
`StageGeneric.Frame` that is cup-adapted for `evenStratumGramOne h`.

Read against `evenStratum_no_cupAdaptedFrame`, which says that for `evenFrameGram h` **no** row
table carries one, this is the repair wave 72's queue item 1 asked for: the frame step of the
even stage layer fails on the stratum because it is aimed at the wrong Gram, not because frames
are unavailable there. -/
theorem evenStratum_exists_gramOne_adaptedFrame {h : ℕ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ∃ (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
      (F : Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))),
      F.IsCupAdapted (evenStratumGramOne h) (evenFramePairing (K := K)) := by
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (4 + 2 * h) := by
    rw [card_H1_zmodTwo_maxProTwoGalK, hev]
    congr 1
    omega
  haveI hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨Φ, hΦ⟩ := evenStratum_exists_gramOne_modelEquiv hle hev
  exact evenStratum_frame_of_gramOne_modelEquiv hfin Φ hΦ

/-! ### §5.3 What is **not** claimed

`Frame v G chi` pins the cyclotomic values on the nose, and §5.2 chooses `v` after the fact.  A
level-three base for `EvenStratumBaseN` needs the *prescribed* table `vN 1`, so §5.2 is not a
base: between them stand the row-exactness step (`evenFrameExactLift`, which needs a
`RowExactLevelFibreLiftSupply` at `vN 1`) and the level-three relation
`nRelWord 1 (levelMk 3 ∘ generators) = 1`, neither of which is touched here.

Nothing in this module asserts or denies
`Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`. -/

section ModelField

variable [CompactSpace (GalK EvenUnram.evenUnramKNegOne)]
  [TotallyDisconnectedSpace (GalK EvenUnram.evenUnramKNegOne)]

local instance evenStratumShiftKScalar :
    DistribMulAction (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenStratumShiftKContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **A CUP-ADAPTED FRAME FOR THE `α = 1` GRAM EXISTS AT `ℚ₂(i)`**, at the same field and over the
same standing profinite binders at which wave 72's `evenStratum_no_cupAdaptedFrame_KNegOne`
refutes one for `evenFrameGram 0`.  The degree computation is wave 72's
`evenStratumFrame_finrank_KNegOne`. -/
theorem evenStratum_exists_gramOne_adaptedFrame_KNegOne :
    ∃ (v : Fin (MarkedCore.coreRank 0) → ℤ_[2]ˣ)
      (F : Frame v (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne))
        (chiCycKTwo (K := EvenUnram.evenUnramKNegOne))),
      F.IsCupAdapted (evenStratumGramOne 0)
        (evenFramePairing (K := EvenUnram.evenUnramKNegOne)) :=
  evenStratum_exists_gramOne_adaptedFrame
    (EvenUnram.evenUnram_range_le_prin_two_of_sqrt_neg_one
      (GQ2.Dyadic.Fields.sqrtIn_mem_quadField (-1))
      GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq)
    GQ2.Dyadic.EvenStratumFrame.evenStratumFrame_finrank_KNegOne

end ModelField

end Adapted

/-! ## §6 Axiom pins -/

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

#print axioms evenStratumGramOne
#print axioms evenStratumGramOne_alphaOneNCupForm
#print axioms evenStratumGramOne_add_diag
#print axioms evenStratumGramOne_diag
#print axioms evenStratumGramOneModel
#print axioms evenStratumGramOne_modelCoord
#print axioms evenStratumModelEquiv
#print axioms evenStratumGramOneModel_hypGram
#print axioms evenStratum_exists_gramOne_modelEquiv
#print axioms evenStratum_levelTwoGen_of_realizers
#print axioms evenStratum_frame_of_gramOne_modelEquiv
#print axioms evenStratum_exists_gramOne_adaptedFrame
#print axioms evenStratum_exists_gramOne_adaptedFrame_KNegOne

-- The `α ≥ 2` statements §4 and §5 stand against, printed beside them.
#print axioms GQ2.Dyadic.EvenStratumFrame.evenStratumFrame_gram_diag
#print axioms GQ2.Dyadic.EvenStratum.evenStratum_no_adaptedModelEquiv
#print axioms GQ2.Dyadic.EvenStratumFrame.evenStratum_no_cupAdaptedFrame

end Pins

end

end GQ2.Dyadic.StageGeneric
