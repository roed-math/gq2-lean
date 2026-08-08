/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenWords
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeTransgression

/-!
# W51-EV3D: the even transgression realization

Ticket **EV-3d** of `docs/dyadic/ev4b-stage-abstraction.md` §4: the even-degree clone of
`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteLevelThreeTransgression.lean`.  Its
endpoint is the even analogue of the committed `oddDegreeSqLevelThreeRelationRealization`:
a cup-adapted even frame kills the literal relator word modulo `λ₃`, i.e. satisfies
`StageGeneric.Frame.LevelThreeRelation (nStageWord α h hα)` and its `M` twin.

Nothing in the odd file's *scaffolding* is re-proved: `commP_mul_central`,
`handleWord_mul_central` and `exists_cupDetector_of_zLayerCharacter` are word-generic and are
cited from the committed file.  What is genuinely word-specific, and is what this file
supplies, is

* §1 the two core-word central-offset lemmas `nWord_mul_central` / `mWord_mul_central` and
  their full-rank consequences `nRelWord_mul_central` / `mRelWord_mul_central`;
* §2 the two `λ₂`-membership facts `nRelWord_mem_twoCentralSeries_two` /
  `mRelWord_mem_twoCentralSeries_two`;
* §3 the abstract-gram seam `IsEvenGram` (see below) together with the identification of the
  committed central-extension fibre computations of `MarkedCore/Cores.lean` as gram
  contractions;
* §4 the gram- and rank-abstract vanishing theorem `gram_vanishes_aux`;
* §5 the word-generic realization engine `levelThreeRelation_of_supplies`;
* §6 the field-level wrapper `gram_vanishes` and the four even endpoints;
* §7 the axiom pins.

## The abstract-gram seam (the only cross-lane joint of the wave)

The even Gram matrix is committed and is **not** redefined here: it is
`MarkedCore.nGram = MarkedCore.mGram = [[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]`
(`GQ2/Dyadic/MarkedCore/N.lean:845`, `M.lean:808`, equal by `MarkedCore.mGram_eq_nGram`,
`Variance.lean:105`).  Its extension to the full rank `MarkedCore.coreRank h = 4 + 2h`, which
is what the generic seed layer takes as its `gram` parameter, is built in the concurrent
EV-3c1 lane and is likewise not defined here.  This file therefore states everything against
an **abstract** contraction

  `gram : (Fin (coreRank h) → Fin (coreRank h) → ZMod 2) → ZMod 2`

constrained by the single predicate

  `IsEvenGram gram : ∀ κ, gram κ = κ 0 0 + (κ 0 1 + κ 1 0) + (κ 2 3 + κ 3 2)`
  `                            + ∑ j, (κ (handleIdxU j) (handleIdxV j)`
  `                                  + κ (handleIdxV j) (handleIdxU j))`

which is exactly the right-hand side of the committed `IsCupCocycle.nRelWord_centLift_fib`
and `IsCupCocycle.mRelWord_centLift_fib` (`MarkedCore/Cores.lean:1455`, `:1435`), i.e. the
core block against the committed Variance matrix (machine-checked as
`IsEvenGram.core_eq_nGram` / `core_eq_mGram`) plus the `h` handle hyperbolics.  The predicate
is word-independent: one and the same `IsEvenGram` serves `N` and `M`, which is the seed-layer
reading of `mGram_eq_nGram`.

At EV-3e time the composition with the EV-3c1 adapter is a one-liner: apply
`nLevelThreeRelationRealization` (or the `M` twin) with `gram` the adapter and the
`IsEvenGram` argument discharged by the adapter's own defining equation, `fun _ ↦ rfl` if the
adapter is defined in the displayed shape.  Nothing else about the adapter is consumed.  The
character pairing `P` of `Frame.IsCupAdapted` is likewise abstract, pinned only by a
hypothesis `hP` identifying it with the field cup form through `characterClass`; the
specializations `nLevelThreeRelationRealization_fieldCup` / `..._fieldCup` (M) discharge `hP`
by `rfl` at the pairing spelled exactly as in `StageAbstractionLSq.lean` §3, which is the
spelling EV-3c1 is expected to produce.

## The `α` hypotheses, per declaration

* §1 and §2 (central offsets, `λ₂` membership) need **`1 ≤ α`** and nothing more: they consume
  only that the core exponents `2 + 2 ^ α` (for `N`) and `2`, `2 ^ α` (for `M`) are even.
* §3's fibre identifications and hence the §5 endpoints need **`2 ≤ α`**, because the
  committed `nRelWord_centLift_fib` / `mRelWord_centLift_fib` do: the mod-4 diagonal rule
  gives `diagCoeff (2 ^ α) = 0` and `diagCoeff (2 + 2 ^ α) = 1` only for `α ≥ 2`.  At `α = 1`
  the `N` exponent degenerates to `4`, the diagonal entry of the Gram flips, and the even
  lane's standing `α ≥ 2` is therefore genuinely consumed here, not merely carried.
* §4 is `α`-free: it never mentions a word.

The `nStageWord α h hα` of `StageAbstractionEvenWords.lean` carries a trailing `1 ≤ α` proof
argument; the endpoints below take `2 ≤ α` and pass `Nat.le_of_succ_le hα`.  By proof
irrelevance a caller may instantiate an endpoint at its own `1 ≤ α` proof term.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace evenTransgression

/-! ## §1 Central square-one offsets do not move the even words

The clones of `LSquare.levelThreeTransgression.sqWord_mul_central` at the two even core words.
The commutator halves are the committed `commP_mul_central`; the power halves are the even
exponents, which is where `1 ≤ α` enters. -/

section CentralOffsets

variable {H : Type*} [Group H] {α : ℕ}

/-- A central offset of exponent two dies in any even power. -/
theorem pow_mul_central_of_two_dvd {z : H} (hz : ∀ g : H, Commute z g) (hz2 : z ^ 2 = 1)
    {e : ℕ} (he : 2 ∣ e) (a : H) : (a * z) ^ e = a ^ e := by
  have hze : z ^ e = 1 := by
    obtain ⟨t, rfl⟩ := he
    rw [pow_mul, hz2, one_pow]
  rw [((hz a).symm).mul_pow, hze, mul_one]

/-- **Central square-one offsets do not move the `N_α` core word** `a^{2+2^α}[a,b][c,d]`.
Only the offset on the first letter has to have exponent two, and only because its exponent
`2 + 2 ^ α` is even, which needs `1 ≤ α`; the two commutators absorb their offsets outright. -/
theorem nWord_mul_central (hα : 1 ≤ α) {z₀ z₁ z₂ z₃ : H} (h₀ : ∀ g : H, Commute z₀ g)
    (h₁ : ∀ g : H, Commute z₁ g) (h₂ : ∀ g : H, Commute z₂ g) (h₃ : ∀ g : H, Commute z₃ g)
    (hz₀ : z₀ ^ 2 = 1) (a b c d : H) :
    MarkedCore.nWord α (a * z₀) (b * z₁) (c * z₂) (d * z₃) = MarkedCore.nWord α a b c d := by
  rw [MarkedCore.nWord, MarkedCore.nWord,
    pow_mul_central_of_two_dvd h₀ hz₀ (two_dvd_two_add_two_pow hα) a,
    LSquare.levelThreeTransgression.commP_mul_central h₀ h₁ a b,
    LSquare.levelThreeTransgression.commP_mul_central h₂ h₃ c d]

/-- **Central square-one offsets do not move the `M_α` core word** `a²[a,b]c^{2^α}[c,d]`.
Here both power letters carry an even exponent (`2` outright, `2 ^ α` as soon as `1 ≤ α`), so
both of their offsets must have exponent two. -/
theorem mWord_mul_central (hα : 1 ≤ α) {z₀ z₁ z₂ z₃ : H} (h₀ : ∀ g : H, Commute z₀ g)
    (h₁ : ∀ g : H, Commute z₁ g) (h₂ : ∀ g : H, Commute z₂ g) (h₃ : ∀ g : H, Commute z₃ g)
    (hz₀ : z₀ ^ 2 = 1) (hz₂ : z₂ ^ 2 = 1) (a b c d : H) :
    MarkedCore.mWord α (a * z₀) (b * z₁) (c * z₂) (d * z₃) = MarkedCore.mWord α a b c d := by
  rw [MarkedCore.mWord, MarkedCore.mWord,
    pow_mul_central_of_two_dvd h₀ hz₀ dvd_rfl a,
    pow_mul_central_of_two_dvd h₂ hz₂ (two_dvd_two_pow hα) c,
    LSquare.levelThreeTransgression.commP_mul_central h₀ h₁ a b,
    LSquare.levelThreeTransgression.commP_mul_central h₂ h₃ c d]

variable {h : ℕ}

/-- **Central square-one offsets do not move the full `N_α` relator word** (`1 ≤ α`): the core
is §1's `nWord_mul_central` and the handles are the committed word-generic
`handleWord_mul_central`.  This is the clone of `sqRelWord_mul_central` that the realization
engine of §5 consumes. -/
theorem nRelWord_mul_central (hα : 1 ≤ α) (m ζ : Fin (MarkedCore.coreRank h) → H)
    (hζ : ∀ (i : Fin (MarkedCore.coreRank h)) (g : H), Commute (ζ i) g)
    (hsq : ∀ i : Fin (MarkedCore.coreRank h), ζ i ^ 2 = 1) :
    MarkedCore.nRelWord α (fun i ↦ m i * ζ i) = MarkedCore.nRelWord α m := by
  have e₁ : MarkedCore.nWord α (m 0 * ζ 0) (m 1 * ζ 1) (m 2 * ζ 2) (m 3 * ζ 3) =
      MarkedCore.nWord α (m 0) (m 1) (m 2) (m 3) :=
    nWord_mul_central hα (hζ 0) (hζ 1) (hζ 2) (hζ 3) (hsq 0) (m 0) (m 1) (m 2) (m 3)
  have e₂ : MarkedCore.handleWord
      (fun j ↦ m (MarkedCore.handleIdxU j) * ζ (MarkedCore.handleIdxU j))
      (fun j ↦ m (MarkedCore.handleIdxV j) * ζ (MarkedCore.handleIdxV j)) =
      MarkedCore.handleWord (fun j ↦ m (MarkedCore.handleIdxU j))
        (fun j ↦ m (MarkedCore.handleIdxV j)) :=
    LSquare.levelThreeTransgression.handleWord_mul_central _ _ _ _
      (fun j ↦ hζ (MarkedCore.handleIdxU j)) (fun j ↦ hζ (MarkedCore.handleIdxV j))
  simp only [MarkedCore.nRelWord]
  rw [e₁, e₂]

/-- **Central square-one offsets do not move the full `M_α` relator word** (`1 ≤ α`), the twin
of `nRelWord_mul_central`. -/
theorem mRelWord_mul_central (hα : 1 ≤ α) (m ζ : Fin (MarkedCore.coreRank h) → H)
    (hζ : ∀ (i : Fin (MarkedCore.coreRank h)) (g : H), Commute (ζ i) g)
    (hsq : ∀ i : Fin (MarkedCore.coreRank h), ζ i ^ 2 = 1) :
    MarkedCore.mRelWord α (fun i ↦ m i * ζ i) = MarkedCore.mRelWord α m := by
  have e₁ : MarkedCore.mWord α (m 0 * ζ 0) (m 1 * ζ 1) (m 2 * ζ 2) (m 3 * ζ 3) =
      MarkedCore.mWord α (m 0) (m 1) (m 2) (m 3) :=
    mWord_mul_central hα (hζ 0) (hζ 1) (hζ 2) (hζ 3) (hsq 0) (hsq 2) (m 0) (m 1) (m 2) (m 3)
  have e₂ : MarkedCore.handleWord
      (fun j ↦ m (MarkedCore.handleIdxU j) * ζ (MarkedCore.handleIdxU j))
      (fun j ↦ m (MarkedCore.handleIdxV j) * ζ (MarkedCore.handleIdxV j)) =
      MarkedCore.handleWord (fun j ↦ m (MarkedCore.handleIdxU j))
        (fun j ↦ m (MarkedCore.handleIdxV j)) :=
    LSquare.levelThreeTransgression.handleWord_mul_central _ _ _ _
      (fun j ↦ hζ (MarkedCore.handleIdxU j)) (fun j ↦ hζ (MarkedCore.handleIdxV j))
  simp only [MarkedCore.mRelWord]
  rw [e₁, e₂]

end CentralOffsets

/-! ## §2 The even relators lie in `λ₂`

The clone of `sqRelWord_mem_twoCentralSeries_two`: in the elementary quotient the commutators
and handles die (`nRelWord_comm` / `mRelWord_comm`) and the surviving powers are even, so they
die too by `levelQuot_two_pow_two`.  Both statements need `1 ≤ α` and nothing else. -/

section LambdaTwo

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {α h : ℕ}

/-- **The `N_α` relator word lies in `λ₂` for any marking** (`1 ≤ α`): its image in the
elementary quotient is `x̄₀^{2+2^α} = 1`. -/
theorem nRelWord_mem_twoCentralSeries_two (hα : 1 ≤ α)
    (m : Fin (MarkedCore.coreRank h) → G) :
    MarkedCore.nRelWord α m ∈ twoCentralSeries G 2 := by
  apply (QuotientGroup.eq_one_iff (MarkedCore.nRelWord α m)).mp
  change levelMk G 2 (MarkedCore.nRelWord α m) = 1
  rw [MarkedCore.map_nRelWord (levelMk G 2) α m]
  letI : CommGroup (levelQuot G 2) :=
    { (inferInstance : Group (levelQuot G 2)) with mul_comm := levelQuot_two_mul_comm }
  rw [MarkedCore.nRelWord_comm]
  obtain ⟨t, ht⟩ := two_dvd_two_add_two_pow hα
  rw [ht, pow_mul, levelQuot_two_pow_two, one_pow]

/-- **The `M_α` relator word lies in `λ₂` for any marking** (`1 ≤ α`): its image in the
elementary quotient is `Ā² · C̄₀^{2^α} = 1`. -/
theorem mRelWord_mem_twoCentralSeries_two (hα : 1 ≤ α)
    (m : Fin (MarkedCore.coreRank h) → G) :
    MarkedCore.mRelWord α m ∈ twoCentralSeries G 2 := by
  apply (QuotientGroup.eq_one_iff (MarkedCore.mRelWord α m)).mp
  change levelMk G 2 (MarkedCore.mRelWord α m) = 1
  rw [MarkedCore.map_mRelWord (levelMk G 2) α m]
  letI : CommGroup (levelQuot G 2) :=
    { (inferInstance : Group (levelQuot G 2)) with mul_comm := levelQuot_two_mul_comm }
  rw [MarkedCore.mRelWord_comm]
  obtain ⟨t, ht⟩ := two_dvd_two_pow hα
  rw [ht, pow_mul]
  simp only [levelQuot_two_pow_two, one_pow, one_mul]

end LambdaTwo

/-! ## §3 The abstract-gram seam

`Frame.IsCupAdapted` takes the word's quadratic-initial Gram contraction as a parameter
(board §2.1(a)).  For the even words that contraction is the committed 4x4 Variance matrix on
the core letters plus the `h` handle hyperbolics; its full-rank packaging belongs to the
concurrent EV-3c1 lane, so this file constrains an abstract contraction by the predicate
`IsEvenGram` and never names the adapter.  Every consumer below takes `gram` and an
`IsEvenGram gram` argument. -/

section EvenGram

variable {h : ℕ}

/-- **The abstract-gram seam.**  A contraction `gram` on rank-`coreRank h` matrices is an
*even gram* when it is the even relators' quadratic-initial contraction: the core block
`κ₀₀ + (κ₀₁ + κ₁₀) + (κ₂₃ + κ₃₂)`, which is the committed Variance matrix
`nGram = mGram = [[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]` read on the four core letters
(`core_eq_nGram`, `core_eq_mGram`), plus one hyperbolic pair per handle.

This is the right-hand side of the committed `IsCupCocycle.nRelWord_centLift_fib` and
`IsCupCocycle.mRelWord_centLift_fib` verbatim, so it is exactly the interface the transgression
argument consumes, and it is the *same* predicate for both words: the `N` and `M` cores share
their Gram (`MarkedCore.mGram_eq_nGram`). -/
def IsEvenGram
    (gram : (Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) → ZMod 2) :
    Prop :=
  ∀ κ : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2,
    gram κ = κ 0 0 + (κ 0 1 + κ 1 0) + (κ 2 3 + κ 3 2) +
      ∑ j, (κ (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j) +
        κ (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j))

namespace IsEvenGram

variable {gram : (Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) → ZMod 2}

/-- An even gram kills the zero matrix. -/
theorem zero (hg : IsEvenGram gram) : gram (fun _ _ ↦ 0) = 0 := by
  simpa using hg fun _ _ ↦ (0 : ZMod 2)

/-- An even gram is additive in the matrix. -/
theorem add (hg : IsEvenGram gram)
    (κ κ' : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) :
    gram (fun i j ↦ κ i j + κ' i j) = gram κ + gram κ' := by
  rw [hg fun i j ↦ κ i j + κ' i j, hg κ, hg κ']
  simp only [Finset.sum_add_distrib]
  abel

/-- **The core block of an even gram is the committed Variance matrix** `mGram`, contracted on
the four core letters.  This is the machine-checked reading of the seam: `IsEvenGram` does not
merely have the right shape, it contracts against the committed matrix. -/
theorem core_eq_mGram (κ : Fin 4 → Fin 4 → ZMod 2) :
    ∑ i, ∑ j, MarkedCore.mGram i j * κ i j =
      κ 0 0 + (κ 0 1 + κ 1 0) + (κ 2 3 + κ 3 2) := by
  simp only [Fin.sum_univ_four, MarkedCore.mGram_00, MarkedCore.mGram_01, MarkedCore.mGram_02,
    MarkedCore.mGram_03, MarkedCore.mGram_10, MarkedCore.mGram_11, MarkedCore.mGram_12,
    MarkedCore.mGram_13, MarkedCore.mGram_20, MarkedCore.mGram_21, MarkedCore.mGram_22,
    MarkedCore.mGram_23, MarkedCore.mGram_30, MarkedCore.mGram_31, MarkedCore.mGram_32,
    MarkedCore.mGram_33]
  ring

/-- The same against the `N`-side spelling of the committed matrix, through
`MarkedCore.mGram_eq_nGram`. -/
theorem core_eq_nGram (κ : Fin 4 → Fin 4 → ZMod 2) :
    ∑ i, ∑ j, MarkedCore.nGram i j * κ i j =
      κ 0 0 + (κ 0 1 + κ 1 0) + (κ 2 3 + κ 3 2) := by
  have hnm : ∀ i j : Fin 4, MarkedCore.nGram i j = MarkedCore.mGram i j := by
    intro i j
    rw [MarkedCore.mGram_eq_nGram]
    rfl
  simp only [hnm]
  exact core_eq_mGram κ

/-- Regression for the seam: a contraction *defined* in the displayed shape satisfies
`IsEvenGram` by `fun _ ↦ rfl`, which is the promised one-line discharge at EV-3e time.  The
adapter itself is EV-3c1's and is deliberately not defined here; this example only records
that nothing beyond the defining equation is asked of it. -/
example {h : ℕ} :
    IsEvenGram (h := h) (fun κ ↦ κ 0 0 + (κ 0 1 + κ 1 0) + (κ 2 3 + κ 3 2) +
      ∑ j, (κ (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j) +
        κ (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j))) :=
  fun _ ↦ rfl

/-- **The `N_α` relator's central-extension fibre is the even gram contraction** (`2 ≤ α`):
the committed `nRelWord_centLift_fib` read through the seam. -/
theorem nRelWord_fib {L : Type*} [Group L] {c : GQ2.DRCoh.TwoCocycle L}
    (hg : IsEvenGram gram) (hc : MarkedCore.IsCupCocycle c) {α : ℕ} (hα : 2 ≤ α)
    (m : Fin (MarkedCore.coreRank h) → L) :
    (MarkedCore.nRelWord α fun i ↦ MarkedCore.centLift c (m i)).fib =
      gram fun i j ↦ c.κ (m i) (m j) := by
  rw [hc.nRelWord_centLift_fib hα m, hg fun i j ↦ c.κ (m i) (m j)]

/-- **The `M_α` relator's central-extension fibre is the same even gram contraction**
(`2 ≤ α`), the twin of `nRelWord_fib`: the two cores share their Gram. -/
theorem mRelWord_fib {L : Type*} [Group L] {c : GQ2.DRCoh.TwoCocycle L}
    (hg : IsEvenGram gram) (hc : MarkedCore.IsCupCocycle c) {α : ℕ} (hα : 2 ≤ α)
    (m : Fin (MarkedCore.coreRank h) → L) :
    (MarkedCore.mRelWord α fun i ↦ MarkedCore.centLift c (m i)).fib =
      gram fun i j ↦ c.κ (m i) (m j) := by
  rw [hc.mRelWord_centLift_fib hα m, hg fun i j ↦ c.κ (m i) (m j)]

end IsEvenGram

end EvenGram

/-! ## §4 Vanishing of the Gram contraction

The clone of `levelThreeTransgression.gram_vanishes_aux` and its field-level wrapper, with the
odd Gram replaced by an abstract contraction.  The proofs are the committed proofs: the only
property of the contraction the duality argument consumes is **additivity**, which is why the
abstract statement asks for exactly `gram 0 = 0` and `gram (κ + κ') = gram κ + gram κ'` and
nothing about the word.  Both statements are `α`-free and rank-abstract; the even instances
supply `hzero`/`hadd` from `IsEvenGram`. -/

section GramVanishes

/-- An additive contraction commutes with finite sums of matrices (the `gram_sum` clone). -/
theorem gram_sum_of_add {n : ℕ} {gram : (Fin n → Fin n → ZMod 2) → ZMod 2}
    (hzero : gram (fun _ _ ↦ 0) = 0)
    (hadd : ∀ κ κ' : Fin n → Fin n → ZMod 2,
      gram (fun i j ↦ κ i j + κ' i j) = gram κ + gram κ')
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → Fin n → Fin n → ZMod 2) :
    gram (fun i j ↦ ∑ x ∈ S, f x i j) = ∑ x ∈ S, gram (f x) := by
  induction S using Finset.induction_on with
  | empty => simpa using hzero
  | insert a S ha ih =>
      rw [Finset.sum_insert ha,
        show (fun i j ↦ ∑ x ∈ insert a S, f x i j) =
          fun i j ↦ f a i j + ∑ x ∈ S, f x i j from
            funext fun i ↦ funext fun j ↦ Finset.sum_insert ha,
        hadd, ih]

/-- **The generic heart of the transgression realization, gram- and rank-abstract.**  Let `G`
be a finitely generated pro-2 group, `c` a bi-additive normalized two-cocycle on its elementary
quotient that becomes a coboundary over `G` through a continuous homomorphism `φ` lying over
the projection, and `ℓ` an additive functional on `H²(G, 𝔽₂)` whose values on cup products of
character classes realize an **additive** contraction `gram` at a marking `gens`.  Then the
contraction of `c` at the images of the marking vanishes.

This is `levelThreeTransgression.gram_vanishes_aux` with `sqRelatorQuadraticInitialGram h`
replaced by `gram` and `Fin (sqRank h)` by `Fin n`; the proof is unchanged, which is the
machine-checked statement that the duality argument is word-independent.  Expanding `c` in a
mod-two basis of the elementary quotient writes the contraction matrix as a finite sum of
rank-one products of inflated coordinate characters; the pairing hypothesis turns each term
into an `ℓ`-value; naturality of the cup product under inflation recombines the sum into `ℓ` of
the inflation of the class of `c`, which dies because the fibre of `φ` is a continuous
primitive of the inflated cocycle. -/
theorem gram_vanishes_aux {n : ℕ}
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    {gram : (Fin n → Fin n → ZMod 2) → ZMod 2}
    (hzero : gram (fun _ _ ↦ 0) = 0)
    (hadd : ∀ κ κ' : Fin n → Fin n → ZMod 2,
      gram (fun i j ↦ κ i j + κ' i j) = gram κ + gram κ')
    (gens : Fin n → G)
    (c : GQ2.DRCoh.TwoCocycle (levelQuot G 2)) (hc : MarkedCore.IsCupCocycle c)
    (φ : ContinuousMonoidHom G (GQ2.DRCoh.CentExt c))
    (hbase : ∀ g : G, (φ g).base = levelMk G 2 g)
    (ℓ :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      H2 G (ZMod 2) →+ ZMod 2)
    (hpair :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      ∀ cG dG : ContinuousMonoidHom G (Multiplicative (ZMod 2)),
        ℓ (trivialCupPairing 2 G (fun _ _ ↦ rfl)
            (H1mk G (ZMod 2) (Count.homEquivZ1 cG))
            (H1mk G (ZMod 2) (Count.homEquivZ1 dG))) =
          gram fun i j ↦ Multiplicative.toAdd (cG (gens i)) *
            Multiplicative.toAdd (dG (gens j))) :
    gram (fun i j ↦ c.κ (levelMk G 2 (gens i)) (levelMk G 2 (gens j))) = 0 := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : Finite Q := finite_levelQuot G hfg hpro 2
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with mul_comm := levelQuot_two_mul_comm }
  letI : Fact (∀ q : Q, q ^ 2 = 1) := ⟨levelQuot_two_pow_two⟩
  letI : Module (ZMod 2) (Additive Q) := LSquare.instModuleZModOfNatNatAdditive_gQ2 Q
  letI : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  letI : DistribMulAction Q (ZMod 2) := LSquare.instDistribMulActionZModOfNatNat_gQ2_1 Q
  letI : ContinuousSMul Q (ZMod 2) := LSquare.instContinuousSMulZModOfNatNat_gQ2_1 Q
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  -- The bi-additive cocycle as a bilinear form on the additive elementary quotient.
  let Bform : LinearMap.BilinForm (ZMod 2) (Additive Q) :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v ↦ AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun w ↦ c.κ v.toMul w.toMul)
            (fun w w' ↦ hc.addRight v.toMul w.toMul w'.toMul)))
        (fun v v' ↦ by
          apply LinearMap.ext
          intro w
          exact hc.addLeft v.toMul v'.toMul w.toMul))
  have hB : ∀ v w : Q, c.κ v w = Bform (Additive.ofMul v) (Additive.ofMul w) :=
    fun v w ↦ rfl
  let bas := Module.finBasis (ZMod 2) (Additive Q)
  let d := Module.finrank (ZMod 2) (Additive Q)
  -- Basis expansion of the bilinear form.
  have hrow : ∀ x w : Additive Q,
      Bform x w = ∑ t : Fin d, bas.repr w t * Bform x (bas t) := by
    intro x w
    conv_lhs => rw [← bas.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [map_smul, smul_eq_mul]
  have hcol : ∀ u y : Additive Q,
      Bform u y = ∑ s : Fin d, bas.repr u s * Bform (bas s) y := by
    intro u y
    conv_lhs => rw [← bas.sum_repr u]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hexp : ∀ u w : Additive Q, Bform u w =
      ∑ p : Fin d × Fin d,
        bas.repr u p.1 * bas.repr w p.2 * Bform (bas p.1) (bas p.2) := by
    intro u w
    rw [Fintype.sum_prod_type, hcol u w]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hrow (bas s) w, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    show bas.repr u s * (bas.repr w t * Bform (bas s) (bas t)) =
      bas.repr u s * bas.repr w t * Bform (bas s) (bas t)
    ring
  -- Coordinate characters of the elementary quotient and their inflations.
  let qChar : (Additive Q →+ ZMod 2) → ContinuousMonoidHom Q (Multiplicative (ZMod 2)) :=
    fun f ↦
      { toFun := fun v ↦ Multiplicative.ofAdd (f (Additive.ofMul v))
        map_one' := by simp
        map_mul' := fun v w ↦ by simp
        continuous_toFun := continuous_of_discreteTopology }
  let lmHom : ContinuousMonoidHom G Q := ⟨levelMk G 2, continuous_levelMk G 2⟩
  let gChar : (Additive Q →+ ZMod 2) →
      ContinuousMonoidHom G (Multiplicative (ZMod 2)) :=
    fun f ↦ (qChar f).comp lmHom
  let cFn : Fin d → Additive Q →+ ZMod 2 := fun s ↦
    AddMonoidHom.mk' (fun u ↦ bas.repr u s)
      (fun u u' ↦ by rw [map_add, Finsupp.add_apply])
  let wFn : Fin d × Fin d → Additive Q →+ ZMod 2 := fun p ↦
    AddMonoidHom.mk' (fun u ↦ Bform (bas p.1) (bas p.2) * bas.repr u p.1)
      (fun u u' ↦ by rw [map_add, Finsupp.add_apply, mul_add])
  -- The contraction matrix as a finite sum of rank-one character products.
  have hmatrix : (fun i j ↦ c.κ (levelMk G 2 (gens i)) (levelMk G 2 (gens j))) =
      fun i j ↦ ∑ p : Fin d × Fin d,
        Multiplicative.toAdd (gChar (wFn p) (gens i)) *
          Multiplicative.toAdd (gChar (cFn p.2) (gens j)) := by
    funext i j
    rw [hB, hexp]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    show bas.repr (Additive.ofMul (levelMk G 2 (gens i))) p.1 *
        bas.repr (Additive.ofMul (levelMk G 2 (gens j))) p.2 *
        Bform (bas p.1) (bas p.2) =
      Bform (bas p.1) (bas p.2) *
          bas.repr (Additive.ofMul (levelMk G 2 (gens i))) p.1 *
        bas.repr (Additive.ofMul (levelMk G 2 (gens j))) p.2
    ring
  -- Inflated character classes are inflations of the quotient-level classes.
  have hinfl : ∀ f : Additive Q →+ ZMod 2,
      H1mk G (ZMod 2) (Count.homEquivZ1 (gChar f)) =
        LSquare.lowerTwoCentralH1InflationAt G 2
          (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar f))) := by
    intro f
    rfl
  -- The bi-additive cocycle as a continuous two-cocycle on the elementary quotient.
  let zc : ↥(Z2 Q (ZMod 2)) :=
    ⟨fun pr ↦ c.κ pr.1 pr.2, by
      apply mem_Z2_iff.mpr
      refine ⟨continuous_of_discreteTopology, ?_⟩
      intro g h' k
      change c.κ h' k + c.κ g (h' * k) = c.κ (g * h') k + c.κ g h'
      linear_combination -c.cocyc g h' k⟩
  -- The sum of quotient-level cup classes is the class of the cocycle itself.
  have hsumQ : ∑ p : Fin d × Fin d,
      trivialCupPairing 2 Q (fun _ _ ↦ rfl)
        (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (wFn p))))
        (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (cFn p.2)))) =
      H2mk Q (ZMod 2) zc := by
    have hterm : ∀ p : Fin d × Fin d,
        trivialCupPairing 2 Q (fun _ _ ↦ rfl)
          (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (wFn p))))
          (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (cFn p.2)))) =
        H2mk Q (ZMod 2)
          ⟨cup11Fun AddMonoidHom.mul (Count.homEquivZ1 (qChar (wFn p))).1
              (Count.homEquivZ1 (qChar (cFn p.2))).1,
            cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ ↦ rfl)
              (Count.homEquivZ1 (qChar (wFn p)))
              (Count.homEquivZ1 (qChar (cFn p.2)))⟩ :=
      fun p ↦ rfl
    rw [Finset.sum_congr rfl fun p _ ↦ hterm p, ← map_sum]
    congr 1
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    funext pr
    rw [Finset.sum_apply]
    show ∑ p : Fin d × Fin d,
        Bform (bas p.1) (bas p.2) * bas.repr (Additive.ofMul pr.1) p.1 *
          bas.repr (Additive.ofMul pr.2) p.2 = c.κ pr.1 pr.2
    rw [hB pr.1 pr.2, hexp]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  -- The class of the cocycle dies under inflation: the fibre of `φ` is a primitive.
  have hker : LSquare.lowerTwoCentralH2InflationAt G 2 (H2mk Q (ZMod 2) zc) = 0 := by
    rw [show LSquare.lowerTwoCentralH2InflationAt G 2 =
        inf2 lmHom (fun _ _ ↦ rfl) from rfl, inf2_H2mk]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨fun g ↦ (φ g).fib,
      (continuous_of_discreteTopology :
        Continuous fun p : GQ2.DRCoh.CentExt c ↦ p.fib).comp φ.continuous_toFun, ?_⟩
    funext pr
    obtain ⟨g, l⟩ := pr
    show g • (φ l).fib - (φ (g * l)).fib + (φ g).fib =
      c.κ (levelMk G 2 g) (levelMk G 2 l)
    rw [scalarActionZmodTwo_triv G, map_mul φ g l, GQ2.DRCoh.CentExt.mul_fib,
      hbase g, hbase l]
    calc (φ l).fib - ((φ g).fib + (φ l).fib +
          c.κ (levelMk G 2 g) (levelMk G 2 l)) + (φ g).fib
        = -c.κ (levelMk G 2 g) (levelMk G 2 l) := by ring
      _ = c.κ (levelMk G 2 g) (levelMk G 2 l) := CharTwo.neg_eq _
  -- The `G`-level cup sum vanishes.
  have hGsum : ∑ p : Fin d × Fin d,
      trivialCupPairing 2 G (fun _ _ ↦ rfl)
        (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (wFn p))))
        (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (cFn p.2)))) = 0 := by
    have hstep : ∀ p : Fin d × Fin d,
        trivialCupPairing 2 G (fun _ _ ↦ rfl)
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (wFn p))))
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (cFn p.2)))) =
        LSquare.lowerTwoCentralH2InflationAt G 2
          (trivialCupPairing 2 Q (fun _ _ ↦ rfl)
            (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (wFn p))))
            (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (cFn p.2))))) := by
      intro p
      rw [hinfl (wFn p), hinfl (cFn p.2),
        ← LSquare.lowerTwoCentralH2InflationAt_trivialCupPairing]
    rw [Finset.sum_congr rfl fun p _ ↦ hstep p, ← map_sum, hsumQ, hker]
  -- Assemble.
  rw [hmatrix, gram_sum_of_add hzero hadd Finset.univ]
  have hcup : ∀ p : Fin d × Fin d,
      gram (fun i j ↦ Multiplicative.toAdd (gChar (wFn p) (gens i)) *
          Multiplicative.toAdd (gChar (cFn p.2) (gens j))) =
      ℓ (trivialCupPairing 2 G (fun _ _ ↦ rfl)
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (wFn p))))
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (cFn p.2))))) :=
    fun p ↦ (hpair (gChar (wFn p)) (gChar (cFn p.2))).symm
  rw [Finset.sum_congr rfl fun p _ ↦ hcup p, ← map_sum, hGsum, map_zero]

end GramVanishes

/-! ## §5 The realization engine

The body of the committed `oddDegreeSqLevelThreeRelationRealization` (the layer-character
separation, the cup detector, the central-offset comparison of `φ` with the canonical lift,
and the final Gram contraction) uses the word only through the four facts isolated here.  The
engine is therefore stated once, word-generically, and the two even endpoints of §6 are
instantiations. -/

/-- **The transgression realization, word-generically.**  A marking of a finitely generated
pro-2 group kills the relator shape `W` modulo `λ₃` as soon as

* `hmem`: the word lies in `λ₂` at that marking;
* `hcentral`: the word is insensitive to central square-one offsets of its letters;
* `hfib`: the fibre of the word at the canonical central lifts is the contraction `gram` of
  the cocycle; and
* `hvanish`: that contraction vanishes for every cup cocycle with a continuous primitive.

The proof is the committed odd proof with the word abstracted: separate the class of the word
in `λ₂/λ₃` by a mod-two character, produce the cup detector
(`levelThreeTransgression.exists_cupDetector_of_zLayerCharacter`, word-free), replace `φ` on
each letter by the canonical central lift at the cost of a central square-one offset, and read
the character value off as the Gram contraction, which vanishes. -/
theorem levelThreeRelation_of_supplies {n : ℕ} (W : StageWord n)
    {gram : (Fin n → Fin n → ZMod 2) → ZMod 2}
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (gens : Fin n → G)
    (hmem : W.word gens ∈ twoCentralSeries G 2)
    (hcentral : ∀ {H : Type} [Group H] (m ζ : Fin n → H),
      (∀ (i : Fin n) (g : H), Commute (ζ i) g) → (∀ i : Fin n, ζ i ^ 2 = 1) →
      W.word (fun i ↦ m i * ζ i) = W.word m)
    (hfib : ∀ c : GQ2.DRCoh.TwoCocycle (levelQuot G 2), MarkedCore.IsCupCocycle c →
      ∀ m : Fin n → levelQuot G 2,
        (W.word fun i ↦ MarkedCore.centLift c (m i)).fib = gram fun i j ↦ c.κ (m i) (m j))
    (hvanish : ∀ c : GQ2.DRCoh.TwoCocycle (levelQuot G 2), MarkedCore.IsCupCocycle c →
      ∀ φ : ContinuousMonoidHom G (GQ2.DRCoh.CentExt c),
        (∀ g : G, (φ g).base = levelMk G 2 g) →
        gram (fun i j ↦ c.κ (levelMk G 2 (gens i)) (levelMk G 2 (gens j))) = 0) :
    W.word (fun i ↦ levelMk G 3 (gens i)) = 1 := by
  rw [← W.map_word (levelMk G 3) gens]
  -- The class of the word in the second layer.
  let zW : ↥(zLayer G 2) := ⟨levelMk G 3 (W.word gens), ⟨W.word gens, hmem, rfl⟩⟩
  suffices hz1 : zW = 1 from congrArg Subtype.val hz1
  by_contra hzne
  -- Separation by mod-two characters of the layer.
  letI : CommGroup ↥(zLayer G 2) :=
    { (inferInstance : Group ↥(zLayer G 2)) with
      mul_comm := fun a b ↦
        Subtype.ext (Subgroup.mem_center_iff.mp (zLayer_le_center G 2 a.2) b.1).symm }
  have htwo : ∀ a : Additive ↥(zLayer G 2), a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    change a.toMul * a.toMul = 1
    apply Subtype.ext
    simpa [pow_two] using zLayer_sq G a.toMul.2
  have hzneAdd : Additive.ofMul zW ≠ 0 := by
    intro hz0
    exact hzne (congrArg Additive.toMul hz0)
  obtain ⟨chi, hchi⟩ := GQ2.FoxH.elemDual_separates htwo hzneAdd
  obtain ⟨c, φ, hc, hbase, hfibφ⟩ :=
    LSquare.levelThreeTransgression.exists_cupDetector_of_zLayerCharacter G hfg hpro chi
  -- The character's value on the class of the word …
  have hval : (φ (W.word gens)).fib = chi (Additive.ofMul zW) := hfibφ _ hmem
  -- … is a Gram contraction, because the detector's offsets are central and square one …
  have hkerφ : ∀ i, (MarkedCore.centLift c (levelMk G 2 (gens i)))⁻¹ * φ (gens i) ∈
      (GQ2.DRCoh.CentExt.proj c).ker := by
    intro i
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change ((MarkedCore.centLift c (levelMk G 2 (gens i))).base)⁻¹ * (φ (gens i)).base = 1
    rw [MarkedCore.centLift_base, hbase]
    exact inv_mul_cancel _
  have hcent : ∀ i, ∀ g' : GQ2.DRCoh.CentExt c,
      Commute ((MarkedCore.centLift c (levelMk G 2 (gens i)))⁻¹ * φ (gens i)) g' :=
    fun i g' ↦ ((Subgroup.mem_center_iff.mp (centExtProj_ker_le_center (hkerφ i))) g').symm
  have hsq1 : ∀ i, ((MarkedCore.centLift c (levelMk G 2 (gens i)))⁻¹ * φ (gens i)) ^ 2 = 1 :=
    fun i ↦ centExtProj_ker_sq_eq_one (hkerφ i)
  have hword : φ (W.word gens) =
      W.word (fun i ↦ MarkedCore.centLift c (levelMk G 2 (gens i))) := by
    rw [W.map_word φ gens]
    calc W.word (fun i ↦ φ (gens i))
        = W.word (fun i ↦ MarkedCore.centLift c (levelMk G 2 (gens i)) *
            ((MarkedCore.centLift c (levelMk G 2 (gens i)))⁻¹ * φ (gens i))) := by
          congr 1
          funext i
          rw [mul_inv_cancel_left]
      _ = W.word (fun i ↦ MarkedCore.centLift c (levelMk G 2 (gens i))) :=
          hcentral _ _ hcent hsq1
  -- … and the Gram contraction vanishes.
  have hzero : chi (Additive.ofMul zW) = 0 := by
    rw [← hval, hword, hfib c hc fun i ↦ levelMk G 2 (gens i)]
    exact hvanish c hc φ hbase
  exact hchi hzero

/-! ## §6 The field-level wrapper and the four even endpoints

The local instances are the ones the committed seed layer uses for the mod-two cohomology of
`G_K(2)`; they are `local` in the committed files, so they are restated here (identically) to
elaborate the statements. -/

section FieldFrames

local notation "GK2" K => maxProPQuotient 2 (GalK K)

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **Vanishing of the Gram contraction on a cup-adapted generic frame.**  The field-level
wrapper of `gram_vanishes_aux`, cloned from `levelThreeTransgression.gram_vanishes`: the
functional is `inv_K` composed with inflation to `G_K`, and the pairing hypothesis is exactly
`Frame.IsCupAdapted` read through the compatibility of the mod-two cup product with inflation
along `G_K → G_K(2)`.

Both the contraction `gram` and the character pairing `P` are abstract.  `P` is pinned by `hP`
to the field cup form through `characterClass`, which is the pairing the L instance uses
(`StageAbstractionLSq.lean` §3) and hence the one the even frame supply is expected to
produce; `hP := fun _ _ ↦ rfl` at that spelling is the intended use, and is what the
`_fieldCup` endpoints below pass. -/
theorem gram_vanishes {n : ℕ}
    {gram : (Fin n → Fin n → ZMod 2) → ZMod 2}
    (hzero : gram (fun _ _ ↦ 0) = 0)
    (hadd : ∀ κ κ' : Fin n → Fin n → ZMod 2,
      gram (fun i j ↦ κ i j + κ' i j) = gram κ + gram κ')
    {v : Fin n → ℤ_[2]ˣ}
    {P : ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)) →
      ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)) → ZMod 2}
    (hP : ∀ c d : ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)),
      P c d = FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K)
          (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        (h1MaxProTwoEquivGalK (K := K)
          (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) d)))
    (F : Frame v (GK2 K) (chiCycKTwo (K := K))) (hcup : F.IsCupAdapted gram P)
    (c : GQ2.DRCoh.TwoCocycle (levelQuot (GK2 K) 2))
    (hc : MarkedCore.IsCupCocycle c)
    (φ : ContinuousMonoidHom (GK2 K) (GQ2.DRCoh.CentExt c))
    (hbase : ∀ g : GK2 K, (φ g).base = levelMk (GK2 K) 2 g) :
    gram (fun i j ↦ c.κ (levelMk (GK2 K) 2 (F.generators i))
      (levelMk (GK2 K) 2 (F.generators j))) = 0 := by
  refine gram_vanishes_aux (GK2 K) (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
    isProP_maxProPQuotient hzero hadd F.generators c hc φ hbase
    ((FieldData.invGalK K).toAddMonoidHom.comp (h2InflationGalK (K := K))) ?_
  intro cG dG
  rw [← hcup cG dG, hP cG dG]
  exact congrArg (FieldData.invGalK K)
    (inf2_trivialCupPairing_maxProPMk_galK
      (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) cG)
      (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) dG))

/-- **The even transgression realization, `N` row** (`2 ≤ α`): every cup-adapted even frame
over `K` kills the literal `N_α` relator word `x₀^{2+2^α}[x₀,x₁][σ,x₂]·∏ⱼ[Uⱼ,Vⱼ]` modulo `λ₃`,
i.e. satisfies `Frame.LevelThreeRelation (nStageWord α h hα)`.  This is the even analogue of
the committed `oddDegreeSqLevelThreeRelationRealization`, adapted to the generic seed layer:
the frame is a `StageGeneric.Frame` at an arbitrary row table `v`, and both the Gram
contraction and the character pairing are abstract (see the module docstring for the seam).

The row table plays no part in the argument, exactly as the parity hypothesis plays none in
the odd realization; the hypotheses that are consumed are cup-adaptedness and `2 ≤ α`. -/
theorem nLevelThreeRelationRealization {α h : ℕ} (hα : 2 ≤ α)
    {gram : (Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) → ZMod 2}
    (hg : IsEvenGram gram) {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    {P : ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)) →
      ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)) → ZMod 2}
    (hP : ∀ c d : ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)),
      P c d = FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K)
          (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        (h1MaxProTwoEquivGalK (K := K)
          (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) d)))
    (F : Frame v (GK2 K) (chiCycKTwo (K := K))) (hcup : F.IsCupAdapted gram P) :
    F.LevelThreeRelation (nStageWord α h (Nat.le_of_succ_le hα)) :=
  levelThreeRelation_of_supplies (nStageWord α h (Nat.le_of_succ_le hα)) (GK2 K)
    (LSquare.maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient F.generators
    (nRelWord_mem_twoCentralSeries_two (GK2 K) (Nat.le_of_succ_le hα) F.generators)
    (fun m ζ hζ hsq ↦ nRelWord_mul_central (Nat.le_of_succ_le hα) m ζ hζ hsq)
    (fun _ hc m ↦ hg.nRelWord_fib hc hα m)
    (fun c hc φ hbase ↦ gram_vanishes K hg.zero hg.add hP F hcup c hc φ hbase)

/-- **The even transgression realization, `M` row** (`2 ≤ α`): the twin of
`nLevelThreeRelationRealization` at the literal `M_α` relator word
`A²[A,B]·C₀^{2^α}[C₀,D]·∏ⱼ[Uⱼ,Vⱼ]`.  The two proofs differ only in the exponent pattern of the
core word; the Gram, and hence the cup-adaptedness hypothesis, is literally the same
(`MarkedCore.mGram_eq_nGram`). -/
theorem mLevelThreeRelationRealization {α h : ℕ} (hα : 2 ≤ α)
    {gram : (Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) → ZMod 2}
    (hg : IsEvenGram gram) {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    {P : ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)) →
      ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)) → ZMod 2}
    (hP : ∀ c d : ContinuousMonoidHom (GK2 K) (Multiplicative (ZMod 2)),
      P c d = FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K)
          (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        (h1MaxProTwoEquivGalK (K := K)
          (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) d)))
    (F : Frame v (GK2 K) (chiCycKTwo (K := K))) (hcup : F.IsCupAdapted gram P) :
    F.LevelThreeRelation (mStageWord α h (Nat.le_of_succ_le hα)) :=
  levelThreeRelation_of_supplies (mStageWord α h (Nat.le_of_succ_le hα)) (GK2 K)
    (LSquare.maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient F.generators
    (mRelWord_mem_twoCentralSeries_two (GK2 K) (Nat.le_of_succ_le hα) F.generators)
    (fun m ζ hζ hsq ↦ mRelWord_mul_central (Nat.le_of_succ_le hα) m ζ hζ hsq)
    (fun _ hc m ↦ hg.mRelWord_fib hc hα m)
    (fun c hc φ hbase ↦ gram_vanishes K hg.zero hg.add hP F hcup c hc φ hbase)

/-- `nLevelThreeRelationRealization` at the field cup pairing itself, the spelling of
`Frame.IsCupAdapted` that `StageAbstractionLSq.lean` §3 pins `Iff.rfl` against the committed
odd `IsCupAdapted`.  This is the form EV-3e is expected to consume: supply the EV-3c1 adapter
for `gram` and its defining equation for `hg`, and nothing else. -/
theorem nLevelThreeRelationRealization_fieldCup {α h : ℕ} (hα : 2 ≤ α)
    {gram : (Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) → ZMod 2}
    (hg : IsEvenGram gram) {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (F : Frame v (GK2 K) (chiCycKTwo (K := K)))
    (hcup : F.IsCupAdapted gram fun c d ↦ FieldData.cupFormK K
      (h1MaxProTwoEquivGalK (K := K)
        (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      (h1MaxProTwoEquivGalK (K := K)
        (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) d))) :
    F.LevelThreeRelation (nStageWord α h (Nat.le_of_succ_le hα)) :=
  nLevelThreeRelationRealization K hα hg (fun _ _ ↦ rfl) F hcup

/-- `mLevelThreeRelationRealization` at the field cup pairing itself, the `M` twin of
`nLevelThreeRelationRealization_fieldCup`. -/
theorem mLevelThreeRelationRealization_fieldCup {α h : ℕ} (hα : 2 ≤ α)
    {gram : (Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) → ZMod 2}
    (hg : IsEvenGram gram) {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (F : Frame v (GK2 K) (chiCycKTwo (K := K)))
    (hcup : F.IsCupAdapted gram fun c d ↦ FieldData.cupFormK K
      (h1MaxProTwoEquivGalK (K := K)
        (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      (h1MaxProTwoEquivGalK (K := K)
        (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) d))) :
    F.LevelThreeRelation (mStageWord α h (Nat.le_of_succ_le hα)) :=
  mLevelThreeRelationRealization K hα hg (fun _ _ ↦ rfl) F hcup

/-- Regression: the `N` endpoint's conclusion is the literal committed relator equation modulo
`λ₃`, definitionally (the even analogue of the `Iff.rfl` pins of `StageAbstractionLSq.lean`). -/
example {α h : ℕ} (hα : 1 ≤ α) {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (F : Frame v (GK2 K) (chiCycKTwo (K := K))) :
    F.LevelThreeRelation (nStageWord α h hα) ↔
      MarkedCore.nRelWord α (fun i ↦ levelMk (GK2 K) 3 (F.generators i)) = 1 :=
  Iff.rfl

/-- Regression: the same for the `M` endpoint. -/
example {α h : ℕ} (hα : 1 ≤ α) {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (F : Frame v (GK2 K) (chiCycKTwo (K := K))) :
    F.LevelThreeRelation (mStageWord α h hα) ↔
      MarkedCore.mRelWord α (fun i ↦ levelMk (GK2 K) 3 (F.generators i)) = 1 :=
  Iff.rfl

end FieldFrames

end evenTransgression

end

end GQ2.Dyadic.StageGeneric

/-! ## §7 Axiom pins

Every public declaration of the file.  The field-free ones are expected at std-3; the
field-level ones at the odd transgression template's print, which is std-3 together with
`tateDualityAt` and `absGalQ2_isTopologicallyFinitelyGenerated` (the print of the committed
`levelThreeTransgression.gram_vanishes` and `oddDegreeSqLevelThreeRelationRealization`).
Nothing here may exceed that set. -/

#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.pow_mul_central_of_two_dvd
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.nWord_mul_central
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.mWord_mul_central
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.nRelWord_mul_central
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.mRelWord_mul_central
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.nRelWord_mem_twoCentralSeries_two
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.mRelWord_mem_twoCentralSeries_two
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram.zero
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram.add
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram.core_eq_mGram
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram.core_eq_nGram
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram.nRelWord_fib
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.IsEvenGram.mRelWord_fib
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.gram_sum_of_add
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.gram_vanishes_aux
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.levelThreeRelation_of_supplies
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.gram_vanishes
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.nLevelThreeRelationRealization
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.mLevelThreeRelationRealization
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.nLevelThreeRelationRealization_fieldCup
#print axioms GQ2.Dyadic.StageGeneric.evenTransgression.mLevelThreeRelationRealization_fieldCup
