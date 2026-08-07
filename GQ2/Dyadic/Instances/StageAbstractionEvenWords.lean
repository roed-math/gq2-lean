/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstraction
import GQ2.Dyadic.MarkedCore.Cores

/-!
# W51-EV3AB, part a: the even word data for the abstract stage machinery

Ticket **EV-3a** of `docs/dyadic/ev4b-stage-abstraction.md` §4: the two `StageWord`
instances that let the even-degree forward route run the W50 generic stage layer
(`GQ2/Dyadic/Instances/StageAbstraction.lean`, namespace `GQ2.Dyadic.StageGeneric`) at the
marked cores `D_N`, `D_M`.

The template throughout is `lSqWord` in
`GQ2/Dyadic/Instances/StageAbstractionLSq.lean`: the word datum's fields are the *committed*
constants, so every generic definition specialises to the even relator shape definitionally.
No word constant is redefined here; `nStageWord`'s and `mStageWord`'s `word` fields are the
committed `MarkedCore.nRelWord α` and `MarkedCore.mRelWord α`, and their `map_word` fields
are the committed `map_nRelWord` / `map_mRelWord`.

## Contents

* §1 `zLayer_mul_pow_even`: an even power kills a central exponent-two shift.
* §2 `nWord_zLayer_shift`, `mWord_zLayer_shift`: the four-letter core computations, the only
  real proof obligation of the ticket.
* §3 `nStageWord`, `mStageWord`: the two word data, with `zshift` obtained from the core case
  through `StageGeneric.zshift_of_core_handles` at `c = 4`.
* §4 definitional regressions and the axiom pins.

## The `α` hypothesis

Both core computations need **`1 ≤ α`**, and nothing more: they consume only that the two
exponents carrying a shift are even, namely `2 + 2 ^ α` for `N_α` and `2 ^ α` for `M_α`
(the exponent `2` of `M_α`'s first letter is even outright).  At `α = 0` both statements are
false, since the exponents degenerate to `3` and `1`.  Following the board's instruction to
choose per declaration, everything in this file is stated at the honest `1 ≤ α` rather than
at the even lane's standing `2 ≤ α`; the stronger hypothesis would buy no simplification.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## §1 Even powers absorb a central exponent-two shift -/

/-- A coordinate shift by an element of the central exponent-two layer `Z_k` is invisible to
any **even** power.  This is the single arithmetic input of both core computations of §2:
`Z_k` has exponent two (`zLayer_sq`) and is central (`zLayer_commute`), so `(z * a) ^ (2 * t)`
loses its `z`-part. -/
theorem zLayer_mul_pow_even {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {k : ℕ} {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) (a : levelQuot G (k + 1))
    {e : ℕ} (he : 2 ∣ e) : (z * a) ^ e = a ^ e := by
  obtain ⟨t, rfl⟩ := he
  rw [(zLayer_commute hz a).mul_pow, pow_mul, zLayer_sq G hz, one_pow, one_mul]

/-- The `N_α` core exponent `2 + 2 ^ α` is even as soon as `1 ≤ α`. -/
theorem two_dvd_two_add_two_pow {α : ℕ} (hα : 1 ≤ α) : 2 ∣ 2 + 2 ^ α :=
  Dvd.dvd.add dvd_rfl (dvd_pow_self 2 (by omega))

/-- The `M_α` core exponent `2 ^ α` is even as soon as `1 ≤ α`. -/
theorem two_dvd_two_pow {α : ℕ} (hα : 1 ≤ α) : 2 ∣ 2 ^ α :=
  dvd_pow_self 2 (by omega)

/-! ## §2 The two four-letter core computations

`nWord α a b c d = a ^ (2 + 2 ^ α) * [a,b] * [c,d]` and
`mWord α a b c d = a ^ 2 * [a,b] * c ^ (2 ^ α) * [c,d]` (`MarkedCore/Cores.lean`).  Each is
insensitive to coordinatewise `Z_k`-shifts: the powers are even by §1, and each commutator
slot absorbs a central factor by `commP_central_left` / `commP_central_right`. -/

section CoreShift

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k α : ℕ}
  {z₀ z₁ z₂ z₃ : levelQuot G (k + 1)}

/-- **The `N_α` core word is insensitive to `Z_k`-shifts** (`1 ≤ α`): the exponent
`2 + 2 ^ α` is even and both commutators kill their central factors. -/
theorem nWord_zLayer_shift (hα : 1 ≤ α)
    (h₀ : z₀ ∈ zLayer G k) (h₁ : z₁ ∈ zLayer G k) (h₂ : z₂ ∈ zLayer G k)
    (h₃ : z₃ ∈ zLayer G k) (a b c d : levelQuot G (k + 1)) :
    MarkedCore.nWord α (z₀ * a) (z₁ * b) (z₂ * c) (z₃ * d) =
      MarkedCore.nWord α a b c d := by
  have e0 : (z₀ * a) ^ (2 + 2 ^ α) = a ^ (2 + 2 ^ α) :=
    zLayer_mul_pow_even h₀ a (two_dvd_two_add_two_pow hα)
  simp only [MarkedCore.nWord, e0, commP_central_left (zLayer_commute h₀),
    commP_central_right (zLayer_commute h₁), commP_central_left (zLayer_commute h₂),
    commP_central_right (zLayer_commute h₃)]

/-- **The `M_α` core word is insensitive to `Z_k`-shifts** (`1 ≤ α`): the exponents `2` and
`2 ^ α` are even and both commutators kill their central factors. -/
theorem mWord_zLayer_shift (hα : 1 ≤ α)
    (h₀ : z₀ ∈ zLayer G k) (h₁ : z₁ ∈ zLayer G k) (h₂ : z₂ ∈ zLayer G k)
    (h₃ : z₃ ∈ zLayer G k) (a b c d : levelQuot G (k + 1)) :
    MarkedCore.mWord α (z₀ * a) (z₁ * b) (z₂ * c) (z₃ * d) =
      MarkedCore.mWord α a b c d := by
  have e0 : (z₀ * a) ^ 2 = a ^ 2 := zLayer_mul_pow_even h₀ a dvd_rfl
  have e2 : (z₂ * c) ^ 2 ^ α = c ^ 2 ^ α := zLayer_mul_pow_even h₂ c (two_dvd_two_pow hα)
  simp only [MarkedCore.mWord, e0, e2, commP_central_left (zLayer_commute h₀),
    commP_central_right (zLayer_commute h₁), commP_central_left (zLayer_commute h₂),
    commP_central_right (zLayer_commute h₃)]

end CoreShift

/-! ## §3 The two even word data

The handles are discharged by `zshift_of_core_handles` at `c = 4`: they are honest
commutators, killed by the committed `handleWord_central_shift`.  The core embedding is the
literal four-letter prefix `![0, 1, 2, 3]` of `Fin (coreRank h)`, so the shape hypothesis
`hw` is `rfl` against the committed definitions of `nRelWord` / `mRelWord`. -/

/-- The **`N_α` word datum** at rank `MarkedCore.coreRank h = 4 + 2 * h`: the committed
relator shape `MarkedCore.nRelWord α` with the committed naturality `map_nRelWord` as its
`map_word` field, and central-shift invariance assembled from `nWord_zLayer_shift`.

Requires `1 ≤ α` (see the module docstring); the hypothesis is the *last* explicit argument,
so the board's `nStageWord α h` reads as the prefix of the applied term `nStageWord α h hα`. -/
def nStageWord (α h : ℕ) (hα : 1 ≤ α) : StageWord (MarkedCore.coreRank h) where
  word m := MarkedCore.nRelWord α m
  map_word φ m := MarkedCore.map_nRelWord φ α m
  zshift z m hz :=
    zshift_of_core_handles
      (fun mm ↦ MarkedCore.nWord α (mm 0) (mm 1) (mm 2) (mm 3))
      ![0, 1, 2, 3] MarkedCore.handleIdxU MarkedCore.handleIdxV
      (fun mm ↦ MarkedCore.nRelWord α mm)
      (fun _ ↦ rfl)
      (fun _z' _m' hz' ↦ nWord_zLayer_shift hα (hz' 0) (hz' 1) (hz' 2) (hz' 3) _ _ _ _)
      z m hz

/-- The **`M_α` word datum** at rank `MarkedCore.coreRank h = 4 + 2 * h`, built exactly as
`nStageWord` from the committed `MarkedCore.mRelWord α`, `map_mRelWord`, and
`mWord_zLayer_shift`.  Requires `1 ≤ α`. -/
def mStageWord (α h : ℕ) (hα : 1 ≤ α) : StageWord (MarkedCore.coreRank h) where
  word m := MarkedCore.mRelWord α m
  map_word φ m := MarkedCore.map_mRelWord φ α m
  zshift z m hz :=
    zshift_of_core_handles
      (fun mm ↦ MarkedCore.mWord α (mm 0) (mm 1) (mm 2) (mm 3))
      ![0, 1, 2, 3] MarkedCore.handleIdxU MarkedCore.handleIdxV
      (fun mm ↦ MarkedCore.mRelWord α mm)
      (fun _ ↦ rfl)
      (fun _z' _m' hz' ↦ mWord_zLayer_shift hα (hz' 0) (hz' 1) (hz' 2) (hz' 3) _ _ _ _)
      z m hz

/-! ## §4 Definitional regressions

The `word` fields are the committed constants, so the generic level sets, defect, and shift
specialise to the even relator shapes on the nose — the even analogue of the `rfl` pins of
`StageAbstractionLSq.lean` §2. -/

section DefeqPins

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {α h k : ℕ}
  (hα : 1 ≤ α)

example (m : Fin (MarkedCore.coreRank h) → G) :
    (nStageWord α h hα).word m = MarkedCore.nRelWord α m := rfl

example (m : Fin (MarkedCore.coreRank h) → G) :
    (mStageWord α h hα).word m = MarkedCore.mRelWord α m := rfl

example : stageZero (nStageWord α h hα) G k =
    {T | MarkedCore.nRelWord α T = 1 ∧ Subgroup.closure (Set.range T) = ⊤} := rfl

example : stageZero (mStageWord α h hα) G k =
    {T | MarkedCore.mRelWord α T = 1 ∧ Subgroup.closure (Set.range T) = ⊤} := rfl

example (T : Fin (MarkedCore.coreRank h) → levelQuot G k) :
    stageDefect (nStageWord α h hα) G k T =
      MarkedCore.nRelWord α fun i ↦ canonLift G k (T i) := rfl

example (T : Fin (MarkedCore.coreRank h) → levelQuot G k) :
    stageDefect (mStageWord α h hα) G k T =
      MarkedCore.mRelWord α fun i ↦ canonLift G k (T i) := rfl

/-- Regression: the assembled `zshift` field really is the coordinatewise shift invariance of
the committed `nRelWord α`, at every level of the two-central tower. -/
example (z m : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hz : ∀ i, z i ∈ zLayer G k) :
    MarkedCore.nRelWord α (fun i ↦ z i * m i) = MarkedCore.nRelWord α m :=
  (nStageWord α h hα).zshift z m hz

/-- Regression: the same for the committed `mRelWord α`. -/
example (z m : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hz : ∀ i, z i ∈ zLayer G k) :
    MarkedCore.mRelWord α (fun i ↦ z i * m i) = MarkedCore.mRelWord α m :=
  (mStageWord α h hα).zshift z m hz

end DefeqPins

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins -/

#print axioms GQ2.Dyadic.StageGeneric.zLayer_mul_pow_even
#print axioms GQ2.Dyadic.StageGeneric.two_dvd_two_add_two_pow
#print axioms GQ2.Dyadic.StageGeneric.two_dvd_two_pow
#print axioms GQ2.Dyadic.StageGeneric.nWord_zLayer_shift
#print axioms GQ2.Dyadic.StageGeneric.mWord_zLayer_shift
#print axioms GQ2.Dyadic.StageGeneric.nStageWord
#print axioms GQ2.Dyadic.StageGeneric.mStageWord
