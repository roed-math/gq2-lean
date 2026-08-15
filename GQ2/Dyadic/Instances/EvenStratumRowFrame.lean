/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenStratumShift
import GQ2.Dyadic.Instances.StageAbstractionEvenFrattiniFrameN

/-!
# W74-EVEN: the cup-adapted frame at the prescribed row table `vN 1`

Lane **W74-EVEN**.  Wave 73 (`Instances/EvenStratumShift.lean` §5.2) produced a
`StageGeneric.Frame` cup-adapted for the `α = 1` Gram `evenStratumGramOne h` at *some* row table,
read off its own generators after the fact, and recorded in §5.3 that `EvenStratumBaseN` needs one
at the **prescribed** table `vN 1`.  §4 of this file builds that one.

## Contents

1. §1 the `α = 1` row of the even bridge table, and the two shadow tables of `vN 1`.
2. §2 the symplectic normal form with one nonzero vector pinned to a hyperbolic coordinate.
3. §3 the `α = 1` model equivalence carrying the `ω` class to the `x₁` coordinate vector.
4. §4 the frame at `vN 1`, cup-adapted for `evenStratumGramOne h`.
5. §5 axiom pins.

## What is claimed and what is not

Nothing in this file asserts or denies
`Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`.  §4 delivers the *frame* half of
`EvenStratumBaseN`; the level-three relation `nRelWord 1 (levelMk 3 ∘ generators) = 1` is the
other half and is untouched here.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.HilbertSymbol
open GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply
open GQ2.Dyadic.EvenCyclotomicRange

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The `α = 1` row of the even bridge table

`StageAbstractionEvenFrattiniFrameN.lean` §1 tabulates `nUnit α` mod four, eight and sixteen for
`α ≥ 2` only, and every entry of its parity column is `1`.  The `α = 1` row is the one the table
omits, and it is the **opposite** row:

| `α` | `1 + 2 ^ α` mod 16 | `nUnit α` mod 16 | mod 8 | mod 4 | parity | `ω` |
|---|---|---|---|---|---|---|
| `1` | `3` | **`5`** | `5` | `1` | **`0`** | **`1`** |

Both flips matter.  The parity `0` is the frame shadow of wave 71's `evenStratum_kappa_eq_zero`:
at `α = 1` the mod-four class of `K` is forced to vanish, so the `x₁` placement of `κ` that the
`α ≥ 2` construction relies on is unavailable, and the parity table it has to match is the zero
table.  The `ω` value `1` is what replaces it: the `ω` class, not the mod-four class, is the
nonzero one at `α = 1`, and §3 places *it* at `x₁`.

Everything comes from the committed defining relation `MarkedCore.nUnit_mul`, reduced in the
residue ring exactly as `evenBridgeN_nUnit_mul` does at `α ≥ 2`. -/

section BridgeOne

/-- Solving the reduced relation mod four at `α = 1` (`x · 3 = −1` in `ZMod 4`). -/
theorem evenStratumRow_solve_modFour {x : ZMod (2 ^ 2)} (h : x * (1 + 2 ^ 1) = -1) : x = 1 := by
  revert x
  decide

/-- Solving the reduced relation mod eight at `α = 1` (`x · 3 = −1` in `ZMod 8`). -/
theorem evenStratumRow_solve_modEight {x : ZMod (2 ^ 3)} (h : x * (1 + 2 ^ 1) = -1) : x = 5 := by
  revert x
  decide

/-- Solving the reduced relation mod sixteen at `α = 1` (`x · 3 = −1` in `ZMod 16`). -/
theorem evenStratumRow_solve_modSixteen {x : ZMod (2 ^ 4)} (h : x * (1 + 2 ^ 1) = -1) : x = 5 := by
  revert x
  decide

/-- **`nUnit 1 ≡ 1 (mod 4)`**: the parity entry of the `α = 1` bridge row is `0`, where the
whole `α ≥ 2` column is `1` (`evenBridgeN_nUnit_modFour`). -/
theorem evenStratumRow_nUnit_modFour :
    PadicInt.toZModPow 2 ((MarkedCore.nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) = 1 :=
  evenStratumRow_solve_modFour (evenBridgeN_nUnit_mul 2 (α := 1) (le_refl 1))

/-- **`nUnit 1 ≡ 5 (mod 8)`**: the `ω` entry of the `α = 1` bridge row is `1`, as at `α = 2`
(where the mod-eight value is `3`) and unlike `α ≥ 3` (where it is `7`). -/
theorem evenStratumRow_nUnit_modEight :
    PadicInt.toZModPow 3 ((MarkedCore.nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) = 5 :=
  evenStratumRow_solve_modEight (evenBridgeN_nUnit_mul 3 (α := 1) (le_refl 1))

/-- **`nUnit 1 ≡ 5 (mod 16)`**, recorded at the same modulus as the rest of the bridge table. -/
theorem evenStratumRow_nUnit_modSixteen :
    PadicInt.toZModPow 4 ((MarkedCore.nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) = 5 :=
  evenStratumRow_solve_modSixteen (evenBridgeN_nUnit_mul 4 (α := 1) (le_refl 1))

/-- The mod-four parity shadow of the `α = 1` row unit is `0`. -/
theorem evenStratumRow_parity_nUnit :
    Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom (MarkedCore.nUnit 1))) = 0 :=
  frattiniFrame_parity_of_val_one evenStratumRow_nUnit_modFour

/-- The mod-eight `ω` shadow of the `α = 1` row unit is `1`. -/
theorem evenStratumRow_omega_nUnit :
    Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom (MarkedCore.nUnit 1))) = 1 := by
  rw [frattiniFrame_omega_of_val evenStratumRow_nUnit_modEight, omegaResidue_table.2.2.1]

/-- **The `α = 1` parity table is identically zero.**  The `α ≥ 2` table
(`evenDegreeN_parity_table`) is the indicator of the letter `x₁`; at `α = 1` even that entry
vanishes. -/
theorem evenStratumRow_parity_table {h : ℕ} (i : Fin (MarkedCore.coreRank h)) :
    Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom (vN 1 i))) = 0 := by
  refine evenIndex_cases
    (P := fun i ↦ Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom (vN (h := h) 1 i))) = 0) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vN_zero, map_one, map_one, toAdd_one]
  · rw [vN_one, evenStratumRow_parity_nUnit]
  · rw [vN_two, map_one, map_one, toAdd_one]
  · rw [vN_three, map_one, map_one, toAdd_one]
  · intro j; rw [vN_handleU, map_one, map_one, toAdd_one]
  · intro j; rw [vN_handleV, map_one, map_one, toAdd_one]

/-- **The `α = 1` `ω` table is the indicator of the letter `x₁`.**  This is the table the `α ≥ 2`
route gets from the *parity* column; at `α = 1` the two columns have swapped roles. -/
theorem evenStratumRow_omega_table {h : ℕ} (i : Fin (MarkedCore.coreRank h)) :
    Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom (vN 1 i))) =
        if (i : ℕ) = 1 then 1 else 0 := by
  refine evenIndex_cases
    (P := fun i ↦ Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom (vN (h := h) 1 i))) =
        if (i : ℕ) = 1 then 1 else 0) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vN_zero, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_zero]; omega)]
  · rw [vN_one, evenStratumRow_omega_nUnit, if_pos (MarkedCore.coreVal_one h)]
  · rw [vN_two, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_two]; omega)]
  · rw [vN_three, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.coreVal_three]; omega)]
  · intro j
    rw [vN_handleU, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.handleIdxU_val]; omega)]
  · intro j
    rw [vN_handleV, map_one, map_one, toAdd_one,
      if_neg (by rw [MarkedCore.handleIdxV_val]; omega)]

end BridgeOne

/-! ## §2 The symplectic normal form with one vector pinned

`exists_symplectic_equiv` (`Certificates/L.lean` §1.2) chooses the first hyperbolic pair by
`by_cases` on whether the space is trivial and then takes *any* nonzero vector.  What §3 needs is
the same theorem with that first vector prescribed: a nonzero `t` must land on the second
coordinate of the zeroth plane, because that is where the `x₁` letter sits.

The proof is the outer step of `exists_symplectic_equiv_aux`, run once with `v` and `w` in the
order that puts `t` in the second slot (`hypSplitEquiv` reads `x ↦ (b w x, b v x)`, so `t` goes in
the `v` position), and `exists_symplectic_equiv` itself on the complement.  `t`'s own component in
the complement is `t + t = 0`, which is what makes the pin come out as a single plane. -/

section Pin

universe u

variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- **The pinned symplectic normal form.**  A nondegenerate alternating `𝔽₂` form on a finite
space is an orthogonal sum of hyperbolic planes in which a prescribed nonzero vector is the
second basis vector of the zeroth plane.

The plane count is `m + 1`, so the statement also records that a space carrying a nonzero vector
has at least one plane. -/
theorem evenStratumRow_symplectic_pin [Finite W] (b : W → W → ZMod 2) (hb : IsSymplecticFp2 b)
    (t : W) (ht : t ≠ 0) :
    ∃ (m : ℕ) (φ : W ≃ₗ[ZMod 2] (Fin (m + 1) → ZMod 2 × ZMod 2)),
      (∀ x y, b x y = hypGram (φ x) (φ y)) ∧
        φ t 0 = (0, 1) ∧ ∀ j : Fin m, φ t j.succ = 0 := by
  classical
  have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
  obtain ⟨u, hu⟩ : ∃ u, b t u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ht (hb.nondeg t hcon)
  have hut : b u t = 1 := by
    rw [← hb.symm]
    rcases ZMod.eq_zero_or_eq_one (b t u) with h | h
    · exact absurd h hu
    · exact h
  obtain ⟨m, φ', hφ'⟩ :=
    exists_symplectic_equiv (fun x y : hypPerp b hb u t ↦ b (x : W) (y : W))
      (isSymplectic_restrict hb hut)
  have hzero : (⟨t + (b t t) • u + (b u t) • t, hypProj_mem hb hut t⟩ :
      hypPerp b hb u t) = 0 := by
    refine Subtype.ext ?_
    show t + (b t t) • u + (b u t) • t = 0
    rw [hb.alt t, hut, zero_smul, one_smul, add_zero, h2]
  refine ⟨m, (hypSplitEquiv hb hut).trans
    (((LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)).prodCongr φ').trans
      (consLinearEquiv m (ZMod 2 × ZMod 2))), fun x y ↦ ?_, ?_, fun j ↦ ?_⟩
  · show b x y = hypGram (Fin.cons (b t x, b u x) (φ' _)) (Fin.cons (b t y, b u y) (φ' _))
    rw [hypGram_cons, ← hφ']
    exact hypSplit_gram hb hut x y
  · show Fin.cons (α := fun _ : Fin (m + 1) ↦ ZMod 2 × ZMod 2) (b t t, b u t)
      (φ' ⟨t + (b t t) • u + (b u t) • t, hypProj_mem hb hut t⟩) 0 =
        ((0 : ZMod 2), (1 : ZMod 2))
    rw [Fin.cons_zero, hb.alt t, hut]
  · show Fin.cons (α := fun _ : Fin (m + 1) ↦ ZMod 2 × ZMod 2) (b t t, b u t)
      (φ' ⟨t + (b t t) • u + (b u t) • t, hypProj_mem hb hut t⟩) j.succ = 0
    rw [Fin.cons_succ, hzero, map_zero]
    rfl

end Pin

/-! ## §3 The `α = 1` model equivalence, with the `ω` class at the letter `x₁`

Wave 73's `evenStratum_exists_gramOne_modelEquiv` produces *an* isomorphism onto the `α = 1`
model; §4 needs one that also places the mod-eight `ω` class of `K` at the coordinate vector of
`x₁`, because `evenFrameExactLift` matches its lift targets against the row table's `ω` values and
§1 says those are the indicator of `x₁`.

At `α ≥ 2` the corresponding placement is not a choice at all: the model's Gram is
non-alternating, its Labute vector is `evenDualVec 0 = e₁`, and the mod-four class `κ` is forced
onto it (`StageAbstractionEvenFrameCore.lean` §1.5).  On the third stratum that mechanism is gone
with the diagonal: `κ = 0` (wave 71) and the `α = 1` Gram is alternating, so **nothing** forces
the placement and §2's pin does it by hand.  The cost is that the `ω` class must be nonzero, which
is exactly what `nUnit 1 ≡ 5 (mod 8)` supplies once that value is attained. -/

section ModelPin

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenStratumRowScalar :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _

local instance evenStratumRowContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] in
/-- **The `ω` class is nonzero once the `α = 1` row unit is attained.**  `nUnit 1 ≡ 5 (mod 8)`
and `ω(5) = 1`, so any element whose cyclotomic value is `nUnit 1` witnesses it.

Compare the `α ≥ 2` route, which needs `κ ≠ 0` (the ramified-`i` binder) and gets nothing from
`ω`: at `α = 1` the two are exchanged, and this one is *derived* rather than carried. -/
theorem evenStratumRow_omegaClass_ne_zero
    (hnun : MarkedCore.nUnit 1 ∈ Set.range (chiCycKTwo (K := K))) :
    cyclotomicModEightOmegaClassKTwo (K := K) ≠ 0 := by
  obtain ⟨g, hg⟩ := hnun
  intro h0
  have hval : frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g = 1 := by
    rw [frattiniFrameEval_modEight, hg, evenStratumRow_omega_nUnit]
  rw [h0, frattiniFrameEval_zero] at hval
  exact zero_ne_one hval

/-- The coordinates of the model vector `((0,1), 0)` are the indicator of the letter `x₁`. -/
theorem evenStratumRow_coord_headSecond {h : ℕ} (i : Fin (MarkedCore.coreRank h)) :
    evenFrameCoord i (((0 : ZMod 2), (1 : ZMod 2)), (fun _ ↦ 0 : Fin (h + 1) → ZMod 2 × ZMod 2)) =
      if (i : ℕ) = 1 then 1 else 0 := by
  refine evenIndex_cases
    (P := fun i ↦ evenFrameCoord i (((0 : ZMod 2), (1 : ZMod 2)),
      (fun _ ↦ 0 : Fin (h + 1) → ZMod 2 × ZMod 2)) = if (i : ℕ) = 1 then 1 else 0)
    ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [evenFrameCoord_zero, if_neg (by rw [MarkedCore.coreVal_zero]; omega)]
  · rw [evenFrameCoord_one, if_pos (MarkedCore.coreVal_one h)]
  · rw [evenFrameCoord_two, if_neg (by rw [MarkedCore.coreVal_two]; omega)]
    rfl
  · rw [evenFrameCoord_three, if_neg (by rw [MarkedCore.coreVal_three]; omega)]
    rfl
  · intro j
    rw [evenFrameCoord_handleU, if_neg (by rw [MarkedCore.handleIdxU_val]; omega)]
    rfl
  · intro j
    rw [evenFrameCoord_handleV, if_neg (by rw [MarkedCore.handleIdxV_val]; omega)]
    rfl

/-- **AN ADAPTED COORDINATE SYSTEM FOR THE `α = 1` GRAM WITH THE `ω` CLASS PINNED.**  On the third
stratum, at degree `2 + 2h` and with the `ω` class nonzero, there is a linear isomorphism
`H¹(G_K(2), 𝔽₂) ≃ evenFrameModel h` carrying the field cup form to `evenStratumGramOneModel h`
**and** the mod-eight `ω` class to the coordinate vector of the letter `x₁`.

This is wave 73's `evenStratum_exists_gramOne_modelEquiv` with §2's pin inserted at the first
plane; the plane count is pinned by the same degree computation. -/
theorem evenStratumRow_exists_gramOne_modelEquiv_pin {h : ℕ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hom : cyclotomicModEightOmegaClassKTwo (K := K) ≠ 0) :
    ∃ Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h,
      (∀ x y, frattiniFrameCup (K := K) x y = evenStratumGramOneModel h (Φ x) (Φ y)) ∧
        ∀ i, evenFrameCoord i (Φ (cyclotomicModEightOmegaClassKTwo (K := K))) =
          if (i : ℕ) = 1 then 1 else 0 := by
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (4 + 2 * h) := by
    rw [card_H1_zmodTwo_maxProTwoGalK, hev]
    congr 1
    omega
  haveI : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨m, φ, hφ, hpin0, hpins⟩ := evenStratumRow_symplectic_pin
    (frattiniFrameCup (K := K))
    (GQ2.Dyadic.FieldDataEven.isSymplecticFp2_of_labute_eq_zero
      (isCupFormFp2_frattiniFrameCup (K := K)) (nondegFp2_frattiniFrameCup (K := K))
      (fun w ↦ frattiniFrameCup_kappa (K := K) w)
      (GQ2.Dyadic.EvenStratum.evenStratum_kappa_eq_zero hle))
    (cyclotomicModEightOmegaClassKTwo (K := K)) hom
  have hm : m + 1 = h + 2 := by
    have h1 : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 4 ^ (m + 1) := by
      rw [Nat.card_congr φ.toEquiv]
      simp
    have h2 : (2 : ℕ) ^ (2 * (m + 1)) = 2 ^ (4 + 2 * h) := by
      rw [← hcard, h1, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega
  obtain rfl : m = h + 1 := by omega
  refine ⟨φ.trans (evenStratumModelEquiv h), fun x y ↦ ?_, fun i ↦ ?_⟩
  · rw [hφ x y]
    exact (evenStratumGramOneModel_hypGram h (φ x) (φ y)).symm
  · have hvec : evenStratumModelEquiv h (φ (cyclotomicModEightOmegaClassKTwo (K := K))) =
        (((0 : ZMod 2), (1 : ZMod 2)), (fun _ ↦ 0 : Fin (h + 1) → ZMod 2 × ZMod 2)) := by
      rw [evenStratumModelEquiv_apply]
      exact Prod.ext hpin0 (funext hpins)
    show evenFrameCoord i (evenStratumModelEquiv h
      (φ (cyclotomicModEightOmegaClassKTwo (K := K)))) = _
    rw [hvec]
    exact evenStratumRow_coord_headSecond i

end ModelPin

end

end GQ2.Dyadic.StageGeneric
