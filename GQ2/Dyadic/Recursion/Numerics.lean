/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.NormNum

/-!
# `SourceNumerics n` — the degree-`n` numeric leaves (dyadic campaign, ticket SD-R1)

The opaque numeric record of SD1 memo §1.1, landed here because SD-R1 is the first ticket of
the spine clone; **SD2 re-exports it** from `GQ2/Dyadic/SourceDataN.lean` and builds the
parameterized source record on top (memo §8).

## Why opaque values, not `n`-exponent shapes  (memo Q3, adopted)

The recursion never *unfolds* a numeric formula.  The §9 solver
(`count_eq_of_closedRecursion`, `GQ2/SectionNine/Induction.lean:503`) consumes the boxed
system only by rewriting both sources' equations to syntactically equal right-hand sides and
cancelling the **shared** coefficient; the existing seam already passes `μ`, `G0`, `DT`,
`phase` as opaque shared data.  So `SourceNumerics` stores **values, not proofs**, and the
packet's formulas live in exactly one place, `standardNumerics`.

This is also what makes the `n = 1` adapters definitional where they can be (memo §1.4,
probe P3): `2 ^ (1 + 2) = 8` and `x ^ (1 + 1) = x ^ 2` are `rfl`, but `x ^ (0 + 1) = x` is
**not** (`pow_one` is a theorem).  The `n = 1` instances therefore pass the *old expressions*
as values; only `hZcard`/`gaussZ_*` need the one-line bridges recorded below.

Both sources of a comparison share **one** `SN`, so no equality side conditions between the
two sources' numerics ever arise (memo §3.2).

Axioms: **strictly below std-3.**  Print check performed for every declaration:
`SourceNumerics` depends on no axioms at all; everything else prints `[propext]`.  (There is
no `ℚ₂` model file for this record — it is new in the degree-`n` layer — so the subset check
is against std-3.)
-/

namespace GQ2.Dyadic

/-- **Degree-`n` numeric leaf values** consumed by the two-sided recursion (SD1 memo §1.1).
Opaque to the induction; both sources of a comparison share one `SN`.

`n` is a phantom index (the values determine everything); keeping it makes instantiation sites
self-documenting and lets `standardNumerics` state the packet formulas.

Not fields, deliberately: `cardH2 = 2` stays a literal in the source record (`dim H² = 1` for
every local field), and the half-torsor `2` of `lem86`, the `±`-class `2`/`zR` of eq. (136) and
the `2 · #D_T` of eq. (140) are degree-independent shapes that cancel (memo §1.1, §4.1). -/
structure SourceNumerics (n : ℕ) where
  /-- `#Hom_cont(Γ, 𝔽₂)`; replaces the literal `8` (`GQ2/SourceData.lean:131`,
  `SectionEight/Partition.lean:214-216`, `SectionEight/Recursion.lean:407,744`). -/
  homScalar : ℕ
  /-- Positivity: the solver's cancellation of the shared coefficient needs `≠ 0` — this is
  the field that replaces the two `omega`-cancels of the literal `8` (memo §4.1(a)). -/
  homScalar_pos : 0 < homScalar
  /-- `#LiftsOver ρ` as a function of `|M_B|`; replaces `(Nat.card ↥RF.MB) ^ 2`
  (`SourceData.lean:143`, `RadicalEdge/Bridge.lean:116-117`, `Recursion.lean:417,721`). -/
  mMult : ℕ → ℕ
  /-- `#Z¹(T)` as a function of `|T|` (the `fixedPts` factor stays a separate literal factor of
  the field shape); replaces the `^ 2` at `SourceData.lean:174-175` and inside `muZero`
  (`Prop89Close.lean:130-133`). -/
  tMult : ℕ → ℕ
  /-- `#Z¹(V) / |V| = #H¹(V)` as a function of `|V|`; replaces the **inner** `|V|` factor —
  `hZcard`'s second `|V|` (`SourceData.lean:218`), `two_mul_card_centralImage`'s inner factor
  (`VLiftCount.lean:780,784`), and eq. (140)'s `#M_B / #T_B` display (`Recursion.lean:429`).
  The **outer** `|V|` is `#B¹` and is degree-independent (memo §1.3). -/
  h1Mult : ℕ → ℕ
  /-- Gauss residue, unramified head, as a function of the half-dimension `m` (`#V = 2^{2m}`);
  replaces `-(2 ^ m : ℤ)` (`SourceData.lean:244`). -/
  gaussUnram : ℕ → ℤ
  /-- Gauss residue, ramified head; replaces `(2 ^ m : ℤ)` (`SourceData.lean:268`). -/
  gaussRam : ℕ → ℤ

/-- **The packet §11 values** (`thm:source-abstract`; magnitudes from `thm:local-gauss`).
The only place in the development where a degree-`n` numeric formula is written down. -/
def standardNumerics (n : ℕ) : SourceNumerics n where
  homScalar := 2 ^ (n + 2)
  homScalar_pos := Nat.two_pow_pos _
  mMult := fun M => M ^ (n + 1)
  tMult := fun T => T ^ (n + 1)
  h1Mult := fun V => V ^ n
  gaussUnram := fun m => (-1) ^ n * 2 ^ (n * m)
  gaussRam := fun m => 2 ^ (n * m)

/-! ## `n = 1` definitional status  (memo §1.4, probe P3)

Three of the five moving values are **definitionally** the `n = 1` literals; two are not, and
those are exactly the two one-line bridges SD2 owes in `sourceA_N`/`sourceR_N`. -/

section NEqOne

/-- `homScalar` at `n = 1` **is** the literal `8` — `rfl`. -/
theorem standardNumerics_one_homScalar : (standardNumerics 1).homScalar = 8 := rfl

/-- `mMult` at `n = 1` **is** the literal `^ 2` — `rfl`. -/
theorem standardNumerics_one_mMult (M : ℕ) : (standardNumerics 1).mMult M = M ^ 2 := rfl

/-- `tMult` at `n = 1` **is** the literal `^ 2` — `rfl`. -/
theorem standardNumerics_one_tMult (T : ℕ) : (standardNumerics 1).tMult T = T ^ 2 := rfl

/-- `h1Mult` at `n = 1` is the inner `|V|` — **not** `rfl` (`pow_one` is a theorem).  This is
SD2's `hZcard` bridge (memo §8 acceptance (2)). -/
theorem standardNumerics_one_h1Mult (V : ℕ) : (standardNumerics 1).h1Mult V = V := pow_one V

/-- `gaussUnram` at `n = 1` is `-(2 ^ m)` — **not** `rfl`.  This is SD2's `gaussZ_unramified`
bridge. -/
theorem standardNumerics_one_gaussUnram (m : ℕ) :
    (standardNumerics 1).gaussUnram m = -(2 ^ m : ℤ) := by
  show (-1 : ℤ) ^ 1 * 2 ^ (1 * m) = -(2 ^ m : ℤ)
  rw [one_mul, pow_one, neg_one_mul]

/-- `gaussRam` at `n = 1` is `+(2 ^ m)` — **not** `rfl`.  This is SD2's `gaussZ_ramified`
bridge. -/
theorem standardNumerics_one_gaussRam (m : ℕ) :
    (standardNumerics 1).gaussRam m = (2 ^ m : ℤ) := by
  show (2 : ℤ) ^ (1 * m) = 2 ^ m
  rw [one_mul]

end NEqOne

end GQ2.Dyadic
