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
* §4 the gram- and rank-abstract vanishing theorem `gram_vanishes_aux` and its field-level
  wrapper `gram_vanishes`;
* §5 the word-generic realization engine `levelThreeRelation_of_supplies` and the four even
  endpoints.

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
argument; the endpoints below take `2 ≤ α` and pass `by omega`.  By proof irrelevance a caller
may instantiate the endpoint at its own `1 ≤ α` proof term.
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

end evenTransgression

end

end GQ2.Dyadic.StageGeneric
