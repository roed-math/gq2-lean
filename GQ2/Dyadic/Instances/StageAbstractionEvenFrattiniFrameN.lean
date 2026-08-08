/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFrameCore

/-!
# W51-EV3C1, part 2: the even Frattini-frame supply at the `N` row

Ticket **EV-3c**, `N`-row half, of `docs/dyadic/ev4b-stage-abstraction.md` §4.  The
core-agnostic scaffolding is `GQ2/Dyadic/Instances/StageAbstractionEvenFrameCore.lean`; this
file adds only what mentions `MarkedCore.nUnit` and the committed `N` row table
`StageGeneric.vN`, so that the `M`-row clone is this file with the `M` tables substituted.

## Board crux (ii): the even mod-sixteen bridge table

The odd route matches its constructor table against the mod-sixteen congruences `S ≡ 13`,
`X ≡ 5`, `Y ≡ 7`, which realise `(−1,−1)_K = −1` and `(2,−1)_K = 1`.  That is the *odd-word*
table.  The even `N`-word table is `(x₀, x₁, σ, x₂) ↦ (1, nUnit α, 1, 1)` with handles `1`, so
its bridge table has a single nontrivial entry, and it is **`α`-dependent**.  From the committed
defining relation `nUnit α · (1 + 2 ^ α) = −1` (`MarkedCore.nUnit_mul`), for `α ≥ 2`:

| `α` | `1 + 2 ^ α` mod 16 | `nUnit α` mod 16 | mod 8 | mod 4 | parity | `ω` |
|---|---|---|---|---|---|---|
| `2` | `5` | **`3`** | `3` | `3` | `1` | **`1`** |
| `3` | `9` | **`7`** | `7` | `3` | `1` | **`0`** |
| `≥ 4` | `1` | **`15`** | `7` | `3` | `1` | **`0`** |

Two things fall out, and both are checkpoints the campaign record should carry.

**(a) The parity column is constant `1`, at the single letter `x₁`.**  By the scaffolding's
§1.5 the model forces the mod-four class `κ` to the frame coordinate vector supported at `x₁`,
so the parity half of the bridge table matches with no hypothesis at all.  This is the even
counterpart of the odd route's "`κ` is the unique vector representing the diagonal", and it is
why the even head's dual-vector map (crux (i)) had to be got right first: the partner of `x₀`
is `x₁`, not `x₀`.

**(b) The `ω` column is not constant: it is `1` at `α = 2` and `0` at `α ≥ 3`.**  So there is no
single even `ω` table; the correct statement carries the scalar
`evenDegreeNOmegaScalar α = if α = 2 then 1 else 0`, and the frame exists exactly when the `ω`
class of `K` is that scalar times the mod-four class (§3).  **This is a genuine constraint on
`K`, not plumbing**: it says `α` really is `K`'s orientation invariant, at least mod eight.
Concretely: at `α ≥ 3` the pin says `ω` vanishes on the whole cyclotomic image, and at `α = 2`
it says `ω` equals mod-four parity there.  Both are exactly what
`im χ_cyc = closure ⟨nUnit α⟩` (`MarkedCore.imChiN α`) gives, since `nUnit α` mod 8 is `3` resp.
`7` and `ω(3) = 1 = parity(3)`, `ω(7) = 0 ≠ 1 = parity(7)`.

The honest hypothesis is therefore §3's `EvenDegreeNModEightImage`, the mod-eight half of that
image identity.  It is stated as a single named `Prop` in the house pattern for priced seams,
and §3 discharges the class pin from it.

## Board crux (iii): the rows and `im χ`

The `N` row table's values are `1` (five kinds of letter) and `nUnit α` (the letter `x₁`).
Membership `nUnit α ∈ im χ_cyc` is **not** proved here and **not** assumed as a bare
side-condition: it is subsumed in the carried `RowExactLevelFibreLiftSupply (vN α)` binder,
which is ticket EV-4a's deliverable and is unsatisfiable without it.  That is the same discipline
`StageAbstraction.lean` §2.1(b) prescribes, and it keeps this file free of any range hypothesis
that EV-4a would then have to re-derive.  For the record, `MarkedCore.imChiN α` is by definition
`(Subgroup.closure {nUnit α}).topologicalClosure`, so the `N` row is the *generator* of the
intended image, unlike the `M` row, whose `−1` entry is a separate branch condition
(`MarkedCore.neg_one_notMem_imChiN` shows the two images genuinely differ).

## What is proved and what is owed

Proved: the bridge table, both shadow tables of `vN α`, the class pin from the mod-eight image
hypothesis, and the supply theorem itself.  Owed, as explicit binders of the supply:
the EV-4a row lift supply, the ramified-`i` binder in the form `κ ≠ 0`, and
`EvenDegreeNModEightImage`.  No `sorry`, no new axiom.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.HilbertSymbol
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The mod-sixteen bridge table at the `N` row unit

Everything comes from the committed defining relation `MarkedCore.nUnit_mul`, pushed through
`PadicInt.toZModPow` and solved in the (tiny, closed) residue ring.  No mod-eight or
mod-sixteen value of `nUnit` existed in the repo before this section. -/

/-- The defining relation of the `N` row unit, reduced mod `2 ^ k`. -/
theorem evenBridgeN_nUnit_mul (k : ℕ) {α : ℕ} (hα : 1 ≤ α) :
    (PadicInt.toZModPow k ((MarkedCore.nUnit α : ℤ_[2]ˣ) : ℤ_[2])) * (1 + 2 ^ α) = -1 := by
  have h := congrArg (PadicInt.toZModPow (p := 2) k) (MarkedCore.nUnit_mul (α := α) hα)
  simpa [map_ofNat] using h

/-- Solving the reduced relation mod eight at `α = 2` (`x · 5 = −1` in `ZMod 8`). -/
theorem evenBridgeN_solve_modEight {x : ZMod (2 ^ 3)} (h : x * (1 + 2 ^ 2) = -1) : x = 3 := by
  revert x
  decide

/-- Solving the reduced relation mod sixteen at `α = 2` (`x · 5 = −1` in `ZMod 16`). -/
theorem evenBridgeN_solve_modSixteen_two {x : ZMod (2 ^ 4)} (h : x * (1 + 2 ^ 2) = -1) :
    x = 3 := by
  revert x
  decide

/-- Solving the reduced relation mod sixteen at `α = 3` (`x · 9 = −1` in `ZMod 16`). -/
theorem evenBridgeN_solve_modSixteen_three {x : ZMod (2 ^ 4)} (h : x * (1 + 2 ^ 3) = -1) :
    x = 7 := by
  revert x
  decide

/-- **`nUnit α ≡ 3 (mod 4)` for `α ≥ 2`**, the parity entry of the bridge table, constant in
`α`.  (Agrees with the committed `MarkedGeneratorData.nUnit_toZModPow_two`, which records the
same value as `−1`.) -/
theorem evenBridgeN_nUnit_modFour {α : ℕ} (hα : 2 ≤ α) :
    PadicInt.toZModPow 2 ((MarkedCore.nUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
  have h := evenBridgeN_nUnit_mul 2 (α := α) (by omega)
  have h2 : (2 : ZMod (2 ^ 2)) ^ α = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, α = 2 + t := ⟨α - 2, by omega⟩
    rw [pow_add, show ((2 : ZMod (2 ^ 2)) ^ 2 = 0) from by decide, zero_mul]
  rw [h2, add_zero, mul_one] at h
  rw [h]
  decide

/-- **`nUnit 2 ≡ 3 (mod 8)`**, the only `α` at which the `ω` entry is nonzero. -/
theorem evenBridgeN_nUnit_modEight_two :
    PadicInt.toZModPow 3 ((MarkedCore.nUnit 2 : ℤ_[2]ˣ) : ℤ_[2]) = 3 :=
  evenBridgeN_solve_modEight (evenBridgeN_nUnit_mul 3 (α := 2) (by omega))

/-- **`nUnit α ≡ 7 (mod 8)` for `α ≥ 3`**: the `ω` entry vanishes from `α = 3` on. -/
theorem evenBridgeN_nUnit_modEight_ge {α : ℕ} (hα : 3 ≤ α) :
    PadicInt.toZModPow 3 ((MarkedCore.nUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 7 := by
  have h := evenBridgeN_nUnit_mul 3 (α := α) (by omega)
  have h2 : (2 : ZMod (2 ^ 3)) ^ α = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, α = 3 + t := ⟨α - 3, by omega⟩
    rw [pow_add, show ((2 : ZMod (2 ^ 3)) ^ 3 = 0) from by decide, zero_mul]
  rw [h2, add_zero, mul_one] at h
  rw [h]
  decide

/-! ### §1.1 The mod-sixteen row of the table

Recorded at the same modulus as the odd route's `S ≡ 13`, `X ≡ 5`, `Y ≡ 7`, for the campaign
record.  Only the mod-eight reductions are consumed downstream. -/

/-- **`nUnit 2 ≡ 3 (mod 16)`.** -/
theorem evenBridgeN_nUnit_modSixteen_two :
    PadicInt.toZModPow 4 ((MarkedCore.nUnit 2 : ℤ_[2]ˣ) : ℤ_[2]) = 3 :=
  evenBridgeN_solve_modSixteen_two (evenBridgeN_nUnit_mul 4 (α := 2) (by omega))

/-- **`nUnit 3 ≡ 7 (mod 16)`.** -/
theorem evenBridgeN_nUnit_modSixteen_three :
    PadicInt.toZModPow 4 ((MarkedCore.nUnit 3 : ℤ_[2]ˣ) : ℤ_[2]) = 7 :=
  evenBridgeN_solve_modSixteen_three (evenBridgeN_nUnit_mul 4 (α := 3) (by omega))

/-- **`nUnit α ≡ 15 (mod 16)` for `α ≥ 4`**: the table is constant from `α = 4` on, since
`2 ^ α` then dies mod sixteen. -/
theorem evenBridgeN_nUnit_modSixteen_ge {α : ℕ} (hα : 4 ≤ α) :
    PadicInt.toZModPow 4 ((MarkedCore.nUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 15 := by
  have h := evenBridgeN_nUnit_mul 4 (α := α) (by omega)
  have h2 : (2 : ZMod (2 ^ 4)) ^ α = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, α = 4 + t := ⟨α - 4, by omega⟩
    rw [pow_add, show ((2 : ZMod (2 ^ 4)) ^ 4 = 0) from by decide, zero_mul]
  rw [h2, add_zero, mul_one] at h
  rw [h]
  decide

/-! ### §1.2 The two shadows of the row unit -/

/-- **The `ω` scalar of the `N` row**: `1` at `α = 2` and `0` at `α ≥ 3`.  The whole
`α`-dependence of the even `N` bridge table is this one bit. -/
def evenDegreeNOmegaScalar (α : ℕ) : ZMod 2 := if α = 2 then 1 else 0

/-- The mod-four parity shadow of the row unit is `1`, for every `α ≥ 2`. -/
theorem evenDegreeN_parity_nUnit {α : ℕ} (hα : 2 ≤ α) :
    Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom (MarkedCore.nUnit α))) = 1 :=
  frattiniFrame_parity_of_val_three (evenBridgeN_nUnit_modFour hα)

/-- The mod-eight `ω` shadow of the row unit is `evenDegreeNOmegaScalar α`. -/
theorem evenDegreeN_omega_nUnit {α : ℕ} (hα : 2 ≤ α) :
    Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom (MarkedCore.nUnit α))) =
        evenDegreeNOmegaScalar α := by
  rcases eq_or_lt_of_le hα with hα2 | hα3
  · subst hα2
    rw [frattiniFrame_omega_of_val evenBridgeN_nUnit_modEight_two, omegaResidue_table.2.1,
      evenDegreeNOmegaScalar, if_pos rfl]
  · rw [frattiniFrame_omega_of_val (evenBridgeN_nUnit_modEight_ge (by omega)),
      omegaResidue_table.2.2.2, evenDegreeNOmegaScalar, if_neg (by omega)]

/-! ## §2 The two shadow tables of the `N` row

The scaffolding's `evenFrame_of_kappaPin` consumes exactly these: the mod-four parity table of
`vN α` must be the indicator of the letter `x₁`, and the mod-eight `ω` table must be
`evenDegreeNOmegaScalar α` times that indicator.  Both are §1's row-unit values spread over the
committed table `vN` through the index eliminator `evenIndex_cases`. -/

/-- **The `N` parity table**: `1` at the letter `x₁` and `0` at every other letter.  This is
the table the model's Labute vector already realises, so it costs no hypothesis on `K`. -/
theorem evenDegreeN_parity_table {α h : ℕ} (hα : 2 ≤ α) (i : Fin (MarkedCore.coreRank h)) :
    Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom (vN α i))) =
        if (i : ℕ) = 1 then 1 else 0 := by
  refine evenIndex_cases
    (P := fun i ↦ Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom (vN α i))) =
        if (i : ℕ) = 1 then 1 else 0) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vN_zero, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_zero]; omega)]
  · rw [vN_one, evenDegreeN_parity_nUnit hα, if_pos (MarkedCore.coreVal_one h)]
  · rw [vN_two, map_one, map_one, toAdd_one, if_neg (by rw [MarkedCore.coreVal_two]; omega)]
  · rw [vN_three, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_three]; omega)]
  · intro j
    rw [vN_handleU, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.handleIdxU_val]; omega)]
  · intro j
    rw [vN_handleV, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.handleIdxV_val]; omega)]

/-- **The `N` `ω` table**: `evenDegreeNOmegaScalar α` at the letter `x₁` and `0` elsewhere. -/
theorem evenDegreeN_omega_table {α h : ℕ} (hα : 2 ≤ α) (i : Fin (MarkedCore.coreRank h)) :
    Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom (vN α i))) =
        evenDegreeNOmegaScalar α * (if (i : ℕ) = 1 then 1 else 0) := by
  refine evenIndex_cases
    (P := fun i ↦ Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom (vN α i))) =
        evenDegreeNOmegaScalar α * (if (i : ℕ) = 1 then 1 else 0)) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vN_zero, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_zero]; omega), mul_zero]
  · rw [vN_one, evenDegreeN_omega_nUnit hα, if_pos (MarkedCore.coreVal_one h), mul_one]
  · rw [vN_two, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_two]; omega), mul_zero]
  · rw [vN_three, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_three]; omega), mul_zero]
  · intro j
    rw [vN_handleU, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.handleIdxU_val]; omega), mul_zero]
  · intro j
    rw [vN_handleV, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.handleIdxV_val]; omega), mul_zero]

/-! ## §3 The mod-eight orientation hypothesis, and the `ω`-class pin

The single priced seam of this ticket, in the house pattern: one named `Prop`, discharged
nowhere here, from which the class pin `τ = c • κ` that the scaffolding needs follows. -/

section EvenFieldN

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenFrameNScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenFrameNContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The even `N`-row mod-eight orientation hypothesis.**  Every cyclotomic value of `G_K(2)`
reduces mod eight into `{1, nUnit α}`.

This is the mod-eight half of `MonoidHom.range chiCycKTwo = MarkedCore.imChiN α`, the identity
that says `α` is `K`'s orientation invariant; it is all the frame construction needs, and it is
finitely checkable.  It is *not* discharged in this lane: the forward route deliberately avoids
assuming the range identity (`EvenForwardRouteSkeleton.lean:20–28`), so a consumer that has the
range identity supplies this, and a consumer that does not must obtain it another way.

Note `(nUnit α) ^ 2 ≡ 1 (mod 8)` for `α ≥ 2` by §1, so the two-element set really is the
mod-eight image of the closed subgroup generated by the row unit. -/
def EvenDegreeNModEightImage (α : ℕ) : Prop :=
  ∀ g : maxProPQuotient 2 (GalK K),
    PadicInt.toZModPow 3 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) = 1 ∨
      PadicInt.toZModPow 3 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) =
        PadicInt.toZModPow 3 ((MarkedCore.nUnit α : ℤ_[2]ˣ) : ℤ_[2])

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The `ω`-class pin at the `N` row.**  The mod-eight orientation hypothesis forces
`τ = evenDegreeNOmegaScalar α • κ`, the class identity the frame assembly consumes.

The check is a finite one on `ZMod 8`: on the value `1` both sides vanish, and on the value
`nUnit α` the pair `(parity, ω)` is `(1, 1)` at `α = 2` and `(1, 0)` at `α ≥ 3`, matching
`c · parity` with `c = 1` resp. `c = 0`. -/
theorem evenDegreeN_omegaPin_of_modEightImage {α : ℕ} (hα : 2 ≤ α)
    (himg : EvenDegreeNModEightImage (K := K) α) :
    cyclotomicModEightOmegaClassKTwo (K := K) =
      evenDegreeNOmegaScalar α • cyclotomicModFourClassKTwo (K := K) := by
  refine evenFrameOmegaPin_of_pointwise _ fun g ↦ ?_
  rcases himg g with hone | hunit
  · -- the cyclotomic value is `1` mod eight: both shadows vanish
    have h4 : PadicInt.toZModPow 2 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← PadicInt.cast_toZModPow 2 3 (by norm_num), hone]
      decide
    rw [frattiniFrame_omega_of_val hone, frattiniFrame_parity_of_val_one h4,
      omegaResidue_table.1, mul_zero]
  · -- the cyclotomic value is the row unit mod eight
    rcases eq_or_lt_of_le hα with hα2 | hα3
    · subst hα2
      have h8 : PadicInt.toZModPow 3 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) = 3 :=
        hunit.trans evenBridgeN_nUnit_modEight_two
      have h4 : PadicInt.toZModPow 2 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
        rw [← PadicInt.cast_toZModPow 2 3 (by norm_num), h8]
        decide
      rw [frattiniFrame_omega_of_val h8, frattiniFrame_parity_of_val_three h4,
        omegaResidue_table.2.1, evenDegreeNOmegaScalar, if_pos rfl, mul_one]
    · have h8 : PadicInt.toZModPow 3 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) = 7 :=
        hunit.trans (evenBridgeN_nUnit_modEight_ge (by omega))
      have h4 : PadicInt.toZModPow 2 ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
        rw [← PadicInt.cast_toZModPow 2 3 (by norm_num), h8]
        decide
      rw [frattiniFrame_omega_of_val h8, frattiniFrame_parity_of_val_three h4,
        omegaResidue_table.2.2.2, evenDegreeNOmegaScalar, if_neg (by omega), zero_mul]

/-! ## §4 The supply

The statement shape mirrors `LSquare.OddDegreeSqCyclotomicFrattiniFrameSupply`
(`GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean:174`): the same ambient binders, the same
`MarkedRecip` bundle binder carried but unused in the conclusion, the degree hypothesis in the
even lane's `2 + 2h` spelling, and an existential over the frame with its cup-adaptation. -/

/-- **The even-degree `N`-row cup-adapted Frattini-frame supply.**  For every even-degree `K`
with the ramified-`i` binder, the mod-eight orientation hypothesis at `α`, and the EV-4a
row-relative exact lift supply, there is a `StageGeneric.Frame` at the committed `N` row table
whose dual Frattini family carries the field cup form to the even relator's Gram.

The three carried binders are exactly the ones ticket EV-3c was priced to carry; none of them is
an admitted goal, and the bundle `_B` is a binder, not an axiom, exactly as in the odd twin. -/
def EvenDegreeNCyclotomicFrattiniFrameSupply (α : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {R : LocalReciprocity} (_B : MarkedRecip R K) (h : ℕ),
    2 ≤ α →
    Module.finrank ℚ_[2] K = 2 + 2 * h →
    cyclotomicModFourClassKTwo (K := K) ≠ 0 →
    EvenDegreeNModEightImage (K := K) α →
    RowExactLevelFibreLiftSupply (vN (h := h) α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) →
      ∃ F : Frame (vN (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
        F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K))

end EvenFieldN

/-- **The supply holds.**  Composition of §1's bridge table, §2's shadow tables, §3's class pin,
and the scaffolding's `evenFrame_of_kappaPin`. -/
theorem evenDegreeNCyclotomicFrattiniFrameSupply_holds (α : ℕ) :
    EvenDegreeNCyclotomicFrattiniFrameSupply α := by
  intro K _ _ _ _ _ B h hα hdeg hkappa himg supply
  exact evenFrame_of_kappaPin (vN (h := h) α) (by omega) hkappa supply
    (evenDegreeNOmegaScalar α) (evenDegreeN_omegaPin_of_modEightImage hα himg)
    (evenDegreeN_parity_table hα) (evenDegreeN_omega_table hα)

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins -/

#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_mul
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_solve_modEight
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_solve_modSixteen_two
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_solve_modSixteen_three
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_modFour
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_modEight_two
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_modEight_ge
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_modSixteen_two
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_modSixteen_three
#print axioms GQ2.Dyadic.StageGeneric.evenBridgeN_nUnit_modSixteen_ge
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeNOmegaScalar
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeN_parity_nUnit
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeN_omega_nUnit
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeN_parity_table
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeN_omega_table
#print axioms GQ2.Dyadic.StageGeneric.EvenDegreeNModEightImage
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeN_omegaPin_of_modEightImage
#print axioms GQ2.Dyadic.StageGeneric.EvenDegreeNCyclotomicFrattiniFrameSupply
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeNCyclotomicFrattiniFrameSupply_holds
