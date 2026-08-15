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
5. §5 the `α = 1` shift supply, and the climb that consumes it.
6. §6 the `M` twin: the `α = 1` `M` shift gains an atom, and the committed supply is false.
7. §7 wave 73's span prediction, tested: the `α = 1` shift is square-free.
8. §8 axiom pins.

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

/-! ## §4 The frame at the prescribed row table

`evenFrame_of_adapted` (`StageAbstractionEvenFrameCore.lean` §4; that file's §4 prose names a
"§4.1" its headings do not carry) is the committed assembly, and
it is Gram-generic in everything except the last two lines, where it contracts the model Gram
against the coordinate products.  §4.1 below is that theorem with `evenStratumGramOne` in place of
`evenFrameGram`, reusing wave 73's `evenStratum_levelTwoGen_of_realizers` for the generation half.
The row table stays a parameter, so the `M` row could consume it unchanged.

§4.2 instantiates at `vN 1`.  Its two match tables are §1's, and they are discharged from opposite
directions: the parity table because *both* sides vanish (`κ = 0` on the stratum, and
`nUnit 1 ≡ 1 mod 4`), the `ω` table because §3 placed the `ω` class exactly where `nUnit 1 ≡ 5 mod
8` demands. -/

/-! ### §4.1 The Gram-swapped assembly -/

/-- **The `α = 1` frame assembly.**  `evenFrame_of_adapted` with the `α = 1` Gram: given an adapted
coordinate system for `evenStratumGramOneModel h` whose mod-four and `ω` classes have the row
table's shadows as coordinates, the dual family, corrected to exact cyclotomic values inside its
Frattini cosets, is a `StageGeneric.Frame` at the row table, cup-adapted for
`evenStratumGramOne h`.

Row-table-generic, exactly as the committed theorem is. -/
theorem evenStratumRow_frame_of_gramOne_adapted {h : ℕ}
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
    (hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)))
    (Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h)
    (hGram : ∀ x y, frattiniFrameCup (K := K) x y = evenStratumGramOneModel h (Φ x) (Φ y))
    (supply : RowExactLevelFibreLiftSupply v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (hpar : ∀ i, evenFrameCoord i (Φ (cyclotomicModFourClassKTwo (K := K))) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (v i))))
    (homega : ∀ i, evenFrameCoord i (Φ (cyclotomicModEightOmegaClassKTwo (K := K))) =
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom (v i)))) :
    ∃ F : Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenStratumGramOne h) (evenFramePairing (K := K)) := by
  classical
  haveI := hfin
  choose gens' hgens' using fun i : Fin (MarkedCore.coreRank h) ↦
    frattiniFrameEval_realizable (K := K) hfin ((evenFrameCoordL i).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (MarkedCore.coreRank h))
      (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens' i) = evenFrameCoord i (Φ x) := fun i x ↦ hgens' i x
  have hmatch4 : ∀ i : Fin (MarkedCore.coreRank h),
      frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModFourParity
          (Units.map (PadicInt.toZModPow 2).toMonoidHom (v i))) := by
    intro i
    rw [hD i]
    exact hpar i
  have hmatch8 : ∀ i : Fin (MarkedCore.coreRank h),
      frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModEightOmega
          (Units.map (PadicInt.toZModPow 3).toMonoidHom (v i))) := by
    intro i
    rw [hD i]
    exact homega i
  choose gens hχ hlevel using fun i : Fin (MarkedCore.coreRank h) ↦
    evenFrameExactLift supply i (gens' i) (hmatch4 i) (hmatch8 i)
  have hD2 : ∀ (i : Fin (MarkedCore.coreRank h))
      (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) = evenFrameCoord i (Φ x) := fun i x ↦
    (frattiniFrameEval_eq_of_levelMk_eq x (hlevel i)).trans (hD i x)
  refine ⟨⟨gens, hχ, evenStratum_levelTwoGen_of_realizers Φ gens hD2⟩, ?_⟩
  intro c d
  show frattiniFrameCup (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) d) =
    evenStratumGramOne h (fun i j ↦ Multiplicative.toAdd (c (gens i)) *
      Multiplicative.toAdd (d (gens j)))
  rw [hGram, ← evenStratumGramOne_modelCoord]
  congr 1
  funext i j
  rw [← hD2 i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
    ← hD2 j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
    frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]

/-! ### §4.2 The frame at `vN 1` -/

/-- **A FRAME AT THE PRESCRIBED ROW TABLE `vN 1`, CUP-ADAPTED FOR THE `α = 1` GRAM.**  This is
wave 73 §5.3's first missing piece: on the third stratum, at degree `2 + 2h`, with the `α = 1`
row unit attained and the EV-4a row lift supply at `vN 1`, the `StageGeneric.Frame` whose
existence `EvenStratumBaseN` asserts (bar its level-three relation) exists.

The binders are exactly the ones the `α ≥ 2` supply carries, minus two and plus one:

* **gone**: the ramified-`i` binder `κ ≠ 0` (false here: wave 71 proves `κ = 0`) and the
  mod-eight orientation hypothesis `EvenDegreeNModEightImage`, whose only job at `α ≥ 2` is to pin
  `τ = c • κ`, a pin that says nothing once `κ = 0`;
* **new**: `nUnit 1 ∈ im χ_cyc`, which is what makes the `ω` class nonzero so that §2's pin has
  something to move.  It is implied by the range identity (§4.3).

Read against `evenStratum_no_cupAdaptedFrame`, which refutes the same object for `evenFrameGram h`
at every row table: the two Grams differ in one entry, and that entry is the whole difference
between a frame that cannot exist and one that does. -/
theorem evenStratumRow_exists_adaptedFrame_vN_one {h : ℕ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (hnun : MarkedCore.nUnit 1 ∈ Set.range (chiCycKTwo (K := K)))
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (supply : RowExactLevelFibreLiftSupply (vN (h := h) 1) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))) :
    ∃ F : Frame (vN (h := h) 1) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenStratumGramOne h) (evenFramePairing (K := K)) := by
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (4 + 2 * h) := by
    rw [card_H1_zmodTwo_maxProTwoGalK, hev]
    congr 1
    omega
  haveI hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨Φ, hGram, hpin⟩ := evenStratumRow_exists_gramOne_modelEquiv_pin hle hev
    (evenStratumRow_omegaClass_ne_zero hnun)
  refine evenStratumRow_frame_of_gramOne_adapted _ hfin Φ hGram supply (fun i ↦ ?_) (fun i ↦ ?_)
  · rw [GQ2.Dyadic.EvenStratum.evenStratum_kappa_eq_zero hle, map_zero, evenFrameCoord_zero_vec,
      evenStratumRow_parity_table]
  · rw [hpin i, evenStratumRow_omega_table]

/-! ### §4.3 From the range identity -/

/-- **The frame at `vN 1` from the surviving point's own hypothesis.**  The range identity
`im χ_cyc = imChiN 1` supplies both the principal-unit bound (wave 71) and the row value (the
committed `evenClimb_vN_mem_range`, which carries no `2 ≤ α`), so the only binder left is the
EV-4a row lift supply. -/
theorem evenStratumRow_exists_adaptedFrame_of_rangeN_one {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = MarkedCore.imChiN 1)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (supply : RowExactLevelFibreLiftSupply (vN (h := h) 1) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))) :
    ∃ F : Frame (vN (h := h) 1) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenStratumGramOne h) (evenFramePairing (K := K)) := by
  have hnun : MarkedCore.nUnit 1 ∈ Set.range (chiCycKTwo (K := K)) := by
    have hmem := evenClimb_vN_mem_range (chi := chiCycKTwo (K := K)) (h := h) hrange 1
    rwa [vN_one] at hmem
  exact evenStratumRow_exists_adaptedFrame_vN_one
    (GQ2.Dyadic.EvenStratum.evenStratum_range_le_prin_of_rangeN_one hrange) hnun hev supply

end ModelPin

/-! ## §5 The `α = 1` shift supply, rebuilt on the true `α = 1` word

Wave 73 refuted `EvenSharpDbarShiftSupply` at `α = 1` (`evenStratum_not_dbarShiftSupply_one`): the
committed `Prop` compares the relator shift against `evenRawDbarWord`, and at `α = 1` the true
shift is `evenStratumShiftWordOne`, which differs from it by the diagonal atom.  Queue item 2 asks
for the supply rebuilt around the true word.

The answer is sharper than "rebuilt": **there is nothing left to supply.**  The committed
`EvenSharpDbarShiftSupply` is a `Prop` precisely because the comparison is an assertion about a
word the machinery does not literally produce; `evenStratumShift_n_one` *is* the comparison at
`α = 1`, unconditionally at every profinite group and every `k ≥ 3`.  So restating the
actual-defect supply and the residual against `evenStratumShiftWordOne` removes the middle input
of `evenClimb_defectReachable` altogether, and §5.4 is the `α = 1` climb with two inputs where the
committed one has three.

What this does *not* do is make the climb easier: the residual supply is the input that carries
the arithmetic, and wave 73 §6 showed depth zero does not discharge it.  What changes is that the
climb is no longer blocked at a **false** step. -/

section ShiftOne

open GQ2.Dyadic.EvenRowSupply

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k s : ℕ}
variable {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

private theorem evenStratumRowRegroup {H' : Type*} [Group H'] (x₁ y₁ x₂ y₂ : H')
    (hy₁ : ∀ t : H', Commute y₁ t) : x₁ * y₁ * (x₂ * y₂) = x₁ * x₂ * (y₁ * y₂) := by
  calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
    _ = x₁ * (x₂ * y₁) * y₂ := by rw [(hy₁ x₂).eq]
    _ = x₁ * x₂ * (y₁ * y₂) := by group

/-! ### §5.1 The `α = 1` word is a homomorphism on depth corrections

The three facts `evenRawDbarWord` needs in order to carry the span and torsor calculus, for
`evenStratumShiftWordOne`.  The core block's proof is the committed `evenRawCoreDbarWord_mul`
minus its diagonal step, which is the only step that used `evenRawSq_mul`. -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The `α = 1` shift word lands in the central involutive layer. -/
theorem evenStratumRow_wordOne_mem_zLayer (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenStratumShiftWordOne base correction ∈ zLayer G k :=
  Subgroup.mul_mem _ (evenStratumShiftCoreOne_mem_zLayer k hk base correction hdepth)
    (evenRawHandleDbarWord_mem_zLayer h k hk base correction hdepth)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The trivial correction has trivial `α = 1` shift. -/
theorem evenStratumRow_wordOne_one
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenStratumShiftWordOne base (fun _ ↦ 1) = 1 := by
  rw [evenStratumShiftWordOne, evenRawHandleDbarWord_one, mul_one]
  simp [evenStratumShiftCoreOne, commP]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The `α = 1` core block is multiplicative in the depth correction: four bracket atoms, each
one-coordinate linear, all central. -/
theorem evenStratumRow_coreOne_mul (k : ℕ) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {c c' : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, c' i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenStratumShiftCoreOne base (fun i ↦ c i * c' i) =
      evenStratumShiftCoreOne base c * evenStratumShiftCoreOne base c' := by
  have hpair : ∀ i j : Fin (MarkedCore.coreRank h),
      commP (c i * c' i) (base j) = commP (c i) (base j) * commP (c' i) (base j) :=
    fun i j ↦ evenRawCommP_mul_left_of_depth k hk (hdepth i)
  simp only [evenStratumShiftCoreOne, hpair]
  rw [evenStratumRowRegroup (commP (c 1) (base 0)) (commP (c' 1) (base 0))
      (commP (c 0) (base 1)) (commP (c' 0) (base 1))
      (zLayer_commute (commP_mem_zLayer k hk (hdepth' 1) _)),
    evenStratumRowRegroup (commP (c 3) (base 2)) (commP (c' 3) (base 2))
      (commP (c 2) (base 3)) (commP (c' 2) (base 3))
      (zLayer_commute (commP_mem_zLayer k hk (hdepth' 3) _))]
  exact evenStratumRowRegroup _ _ _ _
    (zLayer_commute (Subgroup.mul_mem _ (commP_mem_zLayer k hk (hdepth' 1) _)
      (commP_mem_zLayer k hk (hdepth' 0) _)))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The `α = 1` shift word is a homomorphism on depth corrections**, the property the torsor
argument of the residual criterion consumes. -/
theorem evenStratumRow_wordOne_mul (h k : ℕ) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {c c' : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, c' i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenStratumShiftWordOne base (fun i ↦ c i * c' i) =
      evenStratumShiftWordOne base c * evenStratumShiftWordOne base c' := by
  rw [evenStratumShiftWordOne, evenStratumShiftWordOne, evenStratumShiftWordOne,
    evenStratumRow_coreOne_mul k hk base hdepth hdepth',
    evenRawHandleDbarWord_mul h k hk base hdepth hdepth']
  exact evenStratumRowRegroup _ _ _ _
    (zLayer_commute (evenStratumShiftCoreOne_mem_zLayer k hk base c' hdepth'))

/-! ### §5.2 The actual-defect supply against the true word -/

variable {T : Tuple (nStageWord 1 h (le_refl 1)) v G chi k}

/-- **A depth-`s` correction whose `α = 1` shift inverts the current defect.**  The `α = 1`
replacement for `EvenSharpActualDefectSupply`, differing from it in exactly one place: the hit
condition is stated against `evenStratumShiftWordOne`, which is what the `N₁` relator's shift
literally is. -/
structure EvenStratumRowActualDefectOne (s : ℕ)
    (T : Tuple (nStageWord 1 h (le_refl 1)) v G chi k) where
  /-- The underlying depth-`s` admissible correction. -/
  correction : DeepSharpAdmissibleCorrection s T
  /-- Its `α = 1` shift word inverts the current defect. -/
  hitsDefect : evenStratumShiftWordOne (fun i ↦ canonLift G k (T.generators i))
    correction.correction =
      (stageDefect (nStageWord 1 h (le_refl 1)) G k T.generators)⁻¹

/-- **THE CROSSED-DERIVATION INPUT IS FREE AT `α = 1`.**  Where
`EvenSharpActualDefectSupply.toDefectReachable` consumes `EvenSharpDbarShiftSupply`, false at
`α = 1` by wave 73, the same passage against the true `α = 1` word consumes **no** shift
hypothesis at all: `evenStratumShift_n_one` supplies the comparison outright. -/
theorem EvenStratumRowActualDefectOne.toDefectReachable
    (S : EvenStratumRowActualDefectOne s T) (hk : 3 ≤ k)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) :
    Tuple.DefectReachable T :=
  deep_defectReachable_of_kills Hlift (by omega) S.correction
    (by rw [evenStratumShift_n_one h k hk _ _ S.correction.depth]; exact S.hitsDefect)

/-! ### §5.3 The residual and its reachability criterion -/

/-- **The `α = 1` residual of a depth-`s` correction**: what a neutral correction must produce,
measured against the true `α = 1` shift word. -/
def evenStratumRowResidualOne (Wc : DeepSharpAdmissibleCorrection s T) : levelQuot G (k + 1) :=
  (evenStratumShiftWordOne (fun i ↦ canonLift G k (T.generators i)) Wc.correction)⁻¹ *
    (stageDefect (nStageWord 1 h (le_refl 1)) G k T.generators)⁻¹

/-- The `α = 1` residual is reachable when some neutral correction has it as its `α = 1`
shift. -/
def EvenStratumRowResidualReachableOne (Wc : DeepSharpAdmissibleCorrection s T) : Prop :=
  ∃ N : EvenSharpNeutralCorrection s G chi h k,
    evenStratumShiftWordOne (fun i ↦ canonLift G k (T.generators i)) N.correction =
      evenStratumRowResidualOne Wc

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The `α = 1` criterion**, the clone of `nonempty_evenSharpActualDefectSupply_iff_residual`
against the true word.  Both directions are the torsor identity together with §5.1's
homomorphism property, which is why §5.1 had to be re-proved rather than reused. -/
theorem evenStratumRow_nonempty_actualDefectOne_iff_residual (hk : 3 ≤ k)
    (Wc : DeepSharpAdmissibleCorrection s T) :
    Nonempty (EvenStratumRowActualDefectOne s T) ↔
      EvenStratumRowResidualReachableOne Wc := by
  constructor
  · rintro ⟨S⟩
    refine ⟨evenSharpDifferenceNeutral Wc S.correction, ?_⟩
    have hmul := evenStratumRow_wordOne_mul h k hk (fun i ↦ canonLift G k (T.generators i))
      Wc.depth (evenSharpDifferenceNeutral Wc S.correction).depth
    have hfun : (fun i ↦ Wc.correction i *
        (evenSharpDifferenceNeutral Wc S.correction).correction i) =
        S.correction.correction :=
      funext fun i ↦ evenSharpMulNeutral_difference_correction Wc S.correction i
    rw [hfun] at hmul
    rw [evenStratumRowResidualOne, ← S.hitsDefect, hmul]
    group
  · rintro ⟨N, hN⟩
    refine ⟨⟨evenSharpMulNeutral Wc N, ?_⟩⟩
    have hmul := evenStratumRow_wordOne_mul h k hk (fun i ↦ canonLift G k (T.generators i))
      Wc.depth N.depth
    show evenStratumShiftWordOne _ (fun i ↦ Wc.correction i * N.correction i) = _
    rw [hmul, hN, evenStratumRowResidualOne]
    group

/-! ### §5.4 The `α = 1` climb, with two inputs -/

/-- **The `α = 1` residual supply**, the clone of `EvenClimbResidualSupply` against the true
`α = 1` word.  This is the one arithmetic input the `α = 1` climb still owes; wave 73 §6 read it
at depth zero and found it neither free nor false. -/
def EvenStratumRowClimbResidualOne (s h : ℕ)
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (T : Tuple (nStageWord 1 h (le_refl 1)) v G chi k)
    (Wc : DeepSharpAdmissibleCorrection s T), EvenStratumRowResidualReachableOne Wc

/-- **THE `α = 1` STAGE CLIMB.**  `evenClimb_defectReachable` at `α = 1`, with the middle input
gone: the residual supply and the deep row supply give defect reachability at every level
`k ≥ 3`.

Stated precisely, so the trade is visible.  The deep row supply `Hlift` is the committed `Prop`
verbatim.  The residual supply is **not** the committed `EvenClimbResidualSupply`: it is that
`Prop` with `evenRawDbarWord` replaced by `evenStratumShiftWordOne` in its two occurrences, which
is the same replacement the whole section makes.  What is genuinely deleted is the third input,
`EvenSharpDbarShiftSupply`, whose general form wave 73 refuted at `α = 1`.

So the obstruction the committed route hits at `α = 1` is in the *word*, not in the climb. -/
theorem evenStratumRow_climb_defectReachable_one (hk : 3 ≤ k)
    (T : Tuple (nStageWord 1 h (le_refl 1)) v G chi k)
    (Hres : EvenStratumRowClimbResidualOne s h v G chi)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) :
    Tuple.DefectReachable T := by
  obtain ⟨Wc⟩ := evenSharpDeepAdmissible_nonempty s T
  obtain ⟨S⟩ := (evenStratumRow_nonempty_actualDefectOne_iff_residual hk Wc).mpr
    (Hres k hk T Wc)
  exact S.toDefectReachable hk Hlift

end ShiftOne

/-! ## §6 The `M` twin: the `α = 1` shift word gains an atom

Wave 73's queue item 3, run.  `MarkedCore.mWord α a b c d = a²[a,b]·c^(2^α)[c,d]`, and
`evenRawMWord_mul_lambdaImage` needs `2 ≤ α` because only then does `2 ^ α = 2 · 2^(α−1)` have an
**even** half, so that `evenRawPow_of_even_half` kills the third letter's diagonal atom.  At
`α = 1` the exponent is `2 = 2 · 1` with an **odd** half, so `evenRawPow_of_odd_half` applies
instead and the atom `w₂² · [w₂, base 2]` *survives*.

So the two even rows fail at `α = 1` in mirror-image ways, and the prediction is confirmed:

* `N`: the exponent is `2 + 2 ^ 1 = 4 = 2 · 2`, even half, and the coordinate-`0` atom **drops
  out**, so the `α ≥ 2` word overshoots (wave 73 §1-§2).
* `M`: the exponent is `2 ^ 1 = 2 = 2 · 1`, odd half, and the coordinate-`2` atom **appears**,
  so the `α ≥ 2` word undershoots.

**Scope, as wave 73 scoped the `N` side.**  §6.3 refutes `EvenSharpDbarShiftSupply` at the `M`
word *quantified over profinite groups*, which is the form `evenRawStageShift_m` and
`evenSharpDbarShiftSupply_m` have.  It does **not** decide it at `maxProPQuotient 2 (GalK K)` for
any particular field; §6.2 reduces that question to whether the coordinate-`2` atom vanishes
there, and nothing here says it does or does not. -/

section MTwin

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h k : ℕ}

private theorem evenStratumRowAssembleM {H' : Type*} [Group H'] (X P Y Y₂ Q A B C : H')
    (hA : ∀ t : H', Commute A t) (hAB : ∀ t : H', Commute (A * B) t)
    (hY₂ : ∀ t : H', Commute Y₂ t) :
    X * A * (P * B) * (Y * Y₂) * (Q * C) = X * P * Y * Q * (Y₂ * (A * B * C)) := by
  calc
    X * A * (P * B) * (Y * Y₂) * (Q * C) = X * (A * P) * (B * (Y * (Y₂ * (Q * C)))) := by group
    _ = X * (P * A) * (B * (Y * (Y₂ * (Q * C)))) := by rw [(hA P).eq]
    _ = X * P * (A * B * (Y * (Y₂ * Q))) * C := by group
    _ = X * P * (Y * (Y₂ * Q) * (A * B)) * C := by rw [(hAB (Y * (Y₂ * Q))).eq]
    _ = X * P * Y * (Y₂ * Q) * (A * B * C) := by group
    _ = X * P * Y * (Q * Y₂) * (A * B * C) := by rw [(hY₂ Q).eq]
    _ = X * P * Y * Q * (Y₂ * (A * B * C)) := by group

private theorem evenStratumRowShiftAssemble {H' : Type*} [Group H'] (C Hh d D : H')
    (hd : ∀ t : H', Commute d t) : (C * Hh)⁻¹ * (C * d * (Hh * D)) = d * D := by
  calc
    (C * Hh)⁻¹ * (C * d * (Hh * D)) = (C * Hh)⁻¹ * (C * (d * Hh) * D) := by group
    _ = (C * Hh)⁻¹ * (C * (Hh * d) * D) := by rw [(hd Hh).eq]
    _ = d * D := by group

/-! ### §6.1 The `α = 1` `M` core block and the literal factorization -/

/-- **The `α = 1` `M` core block**: `evenRawCoreDbarWord` with the coordinate-`2` diagonal atom
prefixed.  Mirror image of `evenStratumShiftCoreOne`, which is `evenRawCoreDbarWord` with the
coordinate-`0` atom deleted. -/
def evenStratumRowMCoreOne
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  correction 2 ^ 2 * commP (correction 2) (base 2) * evenRawCoreDbarWord base correction

/-- **The `α = 1` `M` shift word**: the `α = 1` `M` core block times the handle block. -/
def evenStratumRowMWordOne
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  evenStratumRowMCoreOne base correction * evenRawHandleDbarWord base correction

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The `α = 1` `M` core block lands in the central involutive layer. -/
theorem evenStratumRow_mCoreOne_mem_zLayer (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenStratumRowMCoreOne base correction ∈ zLayer G k :=
  Subgroup.mul_mem _ (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 2) (base 2))
    (evenRawCoreDbarWord_mem_zLayer k hk base correction hdepth)

/-- **The `M₁` core factorization.**  The `α = 1` analogue of `evenRawMWord_mul_lambdaImage`:
the third letter's exponent is `2 ^ 1 = 2 = 2 * 1`, whose half `1` is **odd**, so
`evenRawPow_of_odd_half` applies where `evenRawPow_of_even_half` applies at `2 ≤ α` and the
coordinate-`2` diagonal atom survives. -/
theorem evenStratumRow_mWordOne_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    MarkedCore.mWord 1 (base 0 * correction 0) (base 1 * correction 1)
        (base 2 * correction 2) (base 3 * correction 3) =
      MarkedCore.mWord 1 (base 0) (base 1) (base 2) (base 3) *
        evenStratumRowMCoreOne base correction := by
  have hexp : (2 : ℕ) ^ 1 = 2 * 1 := by norm_num
  simp only [MarkedCore.mWord, evenStratumRowMCoreOne, evenRawCoreDbarWord, hexp]
  rw [evenRawSq_mul k hk (hdepth 0) (base 0),
    evenRawPow_of_odd_half k hk (hdepth 2) (base 2) odd_one,
    evenRawHandlePair_mul k hk (base 0) (base 1) (hdepth 0) (hdepth 1),
    evenRawHandlePair_mul k hk (base 2) (base 3) (hdepth 2) (hdepth 3)]
  exact evenStratumRowAssembleM _ _ _ _ _ _ _ _
    (zLayer_commute (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _))
    (zLayer_commute (Subgroup.mul_mem _
      (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _)
      (Subgroup.mul_mem _ (commP_mem_zLayer k hk (hdepth 1) _)
        (commP_mem_zLayer k hk (hdepth 0) _))))
    (zLayer_commute (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 2) _))

/-- **The `M₁` relator shift, literally.**  The `α = 1` replacement for `evenRawStageShift_m`:
an equality in `Q_{k+1}` with **no** `2 ≤ α` hypothesis, whose right-hand side is
`evenStratumRowMWordOne` rather than `evenRawDbarWord`. -/
theorem evenStratumRow_mShift_one (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    stageShift (mStageWord 1 h (le_refl 1)) base correction =
      evenStratumRowMWordOne base correction := by
  show (MarkedCore.mRelWord 1 base)⁻¹ *
    MarkedCore.mRelWord 1 (fun i ↦ base i * correction i) = _
  simp only [MarkedCore.mRelWord]
  rw [evenStratumRow_mWordOne_mul_lambdaImage k hk base correction hdepth,
    evenRawHandleWord_mul_lambdaImage h k hk base correction hdepth, evenStratumRowMWordOne]
  exact evenStratumRowShiftAssemble _ _ _ _
    (zLayer_commute (evenStratumRow_mCoreOne_mem_zLayer k hk base correction hdepth))

/-! ### §6.2 The exact discrepancy -/

/-- **The measured gap on the `M` row.**  At `α = 1` the true shift is the coordinate-`2`
diagonal atom times the `α ≥ 2` shift word.  Note the atom is on the **other side** of the
equation from the `N` case (`evenStratumShift_dbarWord_eq_diagonalAtom_mul`), because the `M`
word gains an atom where the `N` word loses one. -/
theorem evenStratumRow_mShift_eq_atom_mul (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    stageShift (mStageWord 1 h (le_refl 1)) base correction =
      correction 2 ^ 2 * commP (correction 2) (base 2) *
        evenRawDbarWord base correction := by
  rw [evenStratumRow_mShift_one h k hk base correction hdepth, evenStratumRowMWordOne,
    evenStratumRowMCoreOne, evenRawDbarWord]
  group

/-- **The conditional consequence on the `M` row.**  If the `α ≥ 2` factorization did hold at
`α = 1` for some data, the coordinate-`2` diagonal atom of that data would be trivial. -/
theorem evenStratumRow_mAtom_eq_one_of_rawShift (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1))
    (hshift : stageShift (mStageWord 1 h (le_refl 1)) base correction =
      evenRawDbarWord base correction) :
    correction 2 ^ 2 * commP (correction 2) (base 2) = 1 := by
  have h1 := evenStratumRow_mShift_eq_atom_mul h k hk base correction hdepth
  rw [hshift] at h1
  refine mul_right_cancel (b := evenRawDbarWord base correction) ?_
  rw [one_mul, ← h1]

/-! ### §6.3 The refutation, at the same witness group

Wave 73's cyclic group of order eight, with the correction moved from coordinate `0` to
coordinate `2`.  Nothing else changes: the atom is the same square of the same element. -/

/-- **THE COMMITTED SHIFT SUPPLY IS FALSE AT `α = 1` ON THE `M` ROW TOO.**  The `M` twin of
`evenStratum_not_dbarShiftSupply_one`, at the same group, the same `k`, and the same element,
with the correction supported at coordinate `2` instead of coordinate `0`. -/
theorem evenStratumRow_not_dbarShiftSupply_m_one :
    ¬ EvenSharpDbarShiftSupply (mStageWord 1 0 (le_refl 1)) EvenStratumShiftWitness 3 := by
  intro hall
  have hdepth : ∀ i : Fin (MarkedCore.coreRank 0),
      (if i = 2 then evenStratumShiftWitnessP else 1) ∈
        lambdaImage EvenStratumShiftWitness (3 - 1) (3 + 1) := by
    intro i
    by_cases hi : i = 2
    · rw [if_pos hi]
      exact evenStratumShiftWitnessP_mem
    · rw [if_neg hi]
      exact Subgroup.one_mem _
  have hatom := evenStratumRow_mAtom_eq_one_of_rawShift
    (G := EvenStratumShiftWitness) 0 3 (by omega) (fun _ ↦ 1)
    (fun i ↦ if i = 2 then evenStratumShiftWitnessP else 1) hdepth
    (hall (fun _ ↦ 1) (fun i ↦ if i = 2 then evenStratumShiftWitnessP else 1) hdepth)
  refine evenStratumShiftWitnessP_sq_ne_one ?_
  simpa [commP] using hatom

/-- **`evenRawStageShift_m`'s conclusion is false at `α = 1`**, in its own shape.  The `M` twin
of `evenStratum_no_rawStageShift_one`.

So neither even row's committed crossed-derivation comparison survives the drop to `α = 1`, and
they fail for opposite reasons: the `N` word loses the coordinate-`0` atom, the `M` word gains
the coordinate-`2` one. -/
theorem evenStratumRow_no_rawStageShift_m_one :
    ¬ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
        [T2Space G] [TotallyDisconnectedSpace G] (h k : ℕ), 3 ≤ k →
        ∀ (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)),
        (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) →
        stageShift (mStageWord 1 h (le_refl 1)) base correction =
          evenRawDbarWord base correction := by
  intro hall
  exact evenStratumRow_not_dbarShiftSupply_m_one fun base correction hdepth ↦
    hall EvenStratumShiftWitness 0 3 (by omega) base correction hdepth

end MTwin

/-! ## §7 The `α = 1` span: wave 73's prediction, tested

Wave 73's queue item 2 ends with a **prediction, explicitly not a claim**: rebuilding the span
calculus of `StageAbstractionEvenRawSpan.lean` §5 on `evenStratumShiftWordOne` "should come out
*smaller*, since the slot-zero square is gone, so `evenRawShiftSpan_eq_zLayer` may not clone."

It is correct, and §7.3 says exactly how much.  The committed span calculus closes the central
layer from the rows **plus** `EvenRawPureSquareSpanSupply`, and its coordinate-`0` row
(`evenRawDepthShiftHom_zero_apply`) is `p² · [p, base 0] · [p, base 1]`, the only place a square
appears anywhere in the even shift.  At `α = 1` that row is `[p, base 1]` alone (§7.2), and every
`α = 1` shift whatsoever is a product of brackets (§7.1).

So the failure of `evenRawShiftSpan_eq_zLayer_of_pureSquares` to clone is not a gap in a proof:
its `Hsq` input cannot be obtained from the `α = 1` rows at all, because they emit no square.  The
compensation is real but lies elsewhere: at `α ≥ 2` the square and the bracket `[p, base 1]` sit
in one row, so neither is available without the other, while at `α = 1` the bracket half is
free. -/

section SpanOne

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h k : ℕ}

/-- **The bracket subgroup of a base tuple**: generated by the brackets `[p, base i]` of
depth-`k−1` elements against the displayed letters.  This is what the even shift word can reach
without any square. -/
def evenStratumRowBracketSpan (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    Subgroup (levelQuot G (k + 1)) :=
  Subgroup.closure {x | ∃ p ∈ lambdaImage G (k - 1) (k + 1),
    ∃ i : Fin (MarkedCore.coreRank h), x = commP p (base i)}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Each generating bracket lies in the bracket subgroup. -/
theorem evenStratumRow_commP_mem_bracketSpan
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (i : Fin (MarkedCore.coreRank h)) :
    commP p (base i) ∈ evenStratumRowBracketSpan base :=
  Subgroup.subset_closure ⟨p, hp, i, rfl⟩

/-! ### §7.1 The `α = 1` shift word is square-free -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The handle block reads the correction only at handle letters, so it is trivial as soon as
those are. -/
theorem evenStratumRow_handleDbar_eq_one
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hc : ∀ j : Fin h, correction (MarkedCore.handleIdxU j) = 1 ∧
      correction (MarkedCore.handleIdxV j) = 1) :
    evenRawHandleDbarWord base correction = 1 := by
  rw [evenRawHandleDbarWord]
  refine List.prod_eq_one fun x hx ↦ ?_
  simp only [List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  rw [(hc j).1, (hc j).2]
  simp [commP]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The handle block of a depth correction is a product of brackets. -/
theorem evenStratumRow_handleDbar_mem_bracketSpan
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawHandleDbarWord base correction ∈ evenStratumRowBracketSpan base := by
  rw [evenRawHandleDbarWord]
  refine Subgroup.list_prod_mem _ fun x hx ↦ ?_
  simp only [List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact Subgroup.mul_mem _
    (evenStratumRow_commP_mem_bracketSpan base (hdepth _) _)
    (evenStratumRow_commP_mem_bracketSpan base (hdepth _) _)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **THE `α = 1` SHIFT IS SQUARE-FREE.**  Every `α = 1` relator shift along a depth-`k−1`
correction is a product of brackets `[p, base i]`.

This is the exact sense in which wave 73's predicted span is smaller: the committed
`evenRawDbarWord` is this word times the diagonal atom `p² · [p, base 0]`
(`evenStratumShift_dbarWord_eq_diagonalAtom_mul`), and that atom is the *only* square in the even
shift calculus. -/
theorem evenStratumRow_wordOne_mem_bracketSpan
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenStratumShiftWordOne base correction ∈ evenStratumRowBracketSpan base := by
  rw [evenStratumShiftWordOne, evenStratumShiftCoreOne]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_)
    (Subgroup.mul_mem _ ?_ ?_)) (evenStratumRow_handleDbar_mem_bracketSpan base correction hdepth)
  all_goals exact evenStratumRow_commP_mem_bracketSpan base (hdepth _) _

/-! ### §7.2 The coordinate-`0` row, side by side -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The `α = 1` coordinate-`0` row is a bare bracket.**  Against the committed
`evenRawDepthShiftHom_zero_apply`, whose value is `p² · [p, base 0] · [p, base 1]`: at `α = 1`
both the square and the coordinate-`0` bracket are gone and `[p, base 1]` is delivered alone.

At `α ≥ 2` extracting `[p, base 1]` from this row costs exactly the pure-square supply, which is
why `evenRawBracket_base_mem_shiftSpan` carries `Hsq`; here it costs nothing. -/
theorem evenStratumRow_wordOne_zero_row (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (p : levelQuot G (k + 1)) :
    evenStratumShiftWordOne base
        (fun j ↦ if j = (0 : Fin (MarkedCore.coreRank h)) then p else 1) =
      commP p (base 1) := by
  have hne : ∀ i : Fin (MarkedCore.coreRank h), (i : ℕ) ≠ 0 → i ≠ 0 := by
    intro i hi hcon
    exact hi (by rw [hcon, MarkedCore.coreVal_zero])
  have h1 : (1 : Fin (MarkedCore.coreRank h)) ≠ 0 :=
    hne 1 (by rw [MarkedCore.coreVal_one]; omega)
  have h2 : (2 : Fin (MarkedCore.coreRank h)) ≠ 0 :=
    hne 2 (by rw [MarkedCore.coreVal_two]; omega)
  have h3 : (3 : Fin (MarkedCore.coreRank h)) ≠ 0 :=
    hne 3 (by rw [MarkedCore.coreVal_three]; omega)
  have hhandle : evenRawHandleDbarWord base
      (fun j ↦ if j = (0 : Fin (MarkedCore.coreRank h)) then p else 1) = 1 := by
    refine evenStratumRow_handleDbar_eq_one base _ fun j ↦ ⟨?_, ?_⟩
    · exact if_neg (hne _ (by rw [MarkedCore.handleIdxU_val]; omega))
    · exact if_neg (hne _ (by rw [MarkedCore.handleIdxV_val]; omega))
  rw [evenStratumShiftWordOne, hhandle, mul_one, evenStratumShiftCoreOne,
    if_neg h1, if_pos rfl, if_neg h3, if_neg h2]
  simp [commP]

/-! ### §7.3 The verdict on the prediction -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **THE PREDICTION IS CORRECT, AND THIS IS ITS EXACT CONTENT.**  If a pure square of a
depth-`k−1` element is an `α = 1` shift, it is already a product of brackets.

So the `α = 1` analogue of `EvenRawPureSquareSpanSupply`, the hypothesis
`evenRawShiftSpan_eq_zLayer_of_pureSquares` needs in order to close the central layer, is a
statement *purely about brackets*, with no contribution from the shift rows at all.  At `α ≥ 2`
that is not so: the coordinate-`0` row does emit `p²`, bundled with two brackets, so there the
supply and the rows are entangled.

`evenRawPureSquareSpanSupply_iff_shiftSpan_eq_zLayer` is unaffected in shape; what changes is
where its input could possibly come from. -/
theorem evenStratumRow_sq_mem_bracketSpan_of_isShift
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {p : levelQuot G (k + 1)}
    (hshift : ∃ correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1),
      (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) ∧
        evenStratumShiftWordOne base correction = p ^ 2) :
    p ^ 2 ∈ evenStratumRowBracketSpan base := by
  obtain ⟨correction, hdepth, heq⟩ := hshift
  rw [← heq]
  exact evenStratumRow_wordOne_mem_bracketSpan base correction hdepth

end SpanOne

end

/-! ## §8 Axiom pins -/

section Pins

#print axioms evenStratumRow_solve_modFour
#print axioms evenStratumRow_solve_modEight
#print axioms evenStratumRow_solve_modSixteen
#print axioms evenStratumRow_nUnit_modFour
#print axioms evenStratumRow_nUnit_modEight
#print axioms evenStratumRow_nUnit_modSixteen
#print axioms evenStratumRow_parity_nUnit
#print axioms evenStratumRow_omega_nUnit
#print axioms evenStratumRow_parity_table
#print axioms evenStratumRow_omega_table

#print axioms evenStratumRow_symplectic_pin

#print axioms evenStratumRowScalar
#print axioms evenStratumRowContinuousScalar
#print axioms evenStratumRow_omegaClass_ne_zero
#print axioms evenStratumRow_coord_headSecond
#print axioms evenStratumRow_exists_gramOne_modelEquiv_pin
#print axioms evenStratumRow_frame_of_gramOne_adapted
#print axioms evenStratumRow_exists_adaptedFrame_vN_one
#print axioms evenStratumRow_exists_adaptedFrame_of_rangeN_one

#print axioms evenStratumRow_wordOne_mem_zLayer
#print axioms evenStratumRow_wordOne_one
#print axioms evenStratumRow_coreOne_mul
#print axioms evenStratumRow_wordOne_mul
#print axioms EvenStratumRowActualDefectOne
#print axioms EvenStratumRowActualDefectOne.toDefectReachable
#print axioms evenStratumRowResidualOne
#print axioms EvenStratumRowResidualReachableOne
#print axioms evenStratumRow_nonempty_actualDefectOne_iff_residual
#print axioms EvenStratumRowClimbResidualOne
#print axioms evenStratumRow_climb_defectReachable_one

#print axioms evenStratumRowMCoreOne
#print axioms evenStratumRowMWordOne
#print axioms evenStratumRow_mCoreOne_mem_zLayer
#print axioms evenStratumRow_mWordOne_mul_lambdaImage
#print axioms evenStratumRow_mShift_one
#print axioms evenStratumRow_mShift_eq_atom_mul
#print axioms evenStratumRow_mAtom_eq_one_of_rawShift
#print axioms evenStratumRow_not_dbarShiftSupply_m_one
#print axioms evenStratumRow_no_rawStageShift_m_one

#print axioms evenStratumRowBracketSpan
#print axioms evenStratumRow_commP_mem_bracketSpan
#print axioms evenStratumRow_handleDbar_eq_one
#print axioms evenStratumRow_handleDbar_mem_bracketSpan
#print axioms evenStratumRow_wordOne_mem_bracketSpan
#print axioms evenStratumRow_wordOne_zero_row
#print axioms evenStratumRow_sq_mem_bracketSpan_of_isShift

-- The statements §4 stands against and beside, printed with it.
#print axioms GQ2.Dyadic.EvenStratumFrame.evenStratum_no_cupAdaptedFrame
#print axioms evenStratum_exists_gramOne_adaptedFrame
#print axioms evenDegreeNCyclotomicFrattiniFrameSupply_holds
#print axioms evenClimb_defectReachable
#print axioms evenStratum_not_dbarShiftSupply_one
#print axioms evenSharpDbarShiftSupply_m
#print axioms evenRawDepthShiftHom_zero_apply
#print axioms evenRawShiftSpan_eq_zLayer_of_pureSquares

end Pins

end GQ2.Dyadic.StageGeneric
