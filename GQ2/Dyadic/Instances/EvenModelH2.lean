/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.DemushkinEpimorphismRigidity
import GQ2.Dyadic.MarkedCore.Certificate
import GQ2.Dyadic.MaxProTwoCohomology

/-!
# EV-1a/b/c: mod-two cohomology of the two even marked cores

Tickets **EV-1a**, **EV-1b**, **EV-1c** of the even-degree forward route
(`GQ2/Dyadic/Instances/EvenForwardRouteSkeleton.lean`).  This file computes, for the two
rank-`coreRank h = 4 + 2h` even cores `DN α h` and `DM α h` at branch depth `α ≥ 2`:

* **EV-1c** the coordinate description of `H¹(-, 𝔽₂)`: a mod-two class is exactly a vector
  `Fin (coreRank h) → 𝔽₂` of generator values (`dnCoordinateHOne_bijective`,
  `dmCoordinateHOne_bijective`).  This is the even clone of
  `GQ2.Dyadic.LSquare.dsqCoordinateHOne_bijective`.
* **EV-1a** `Nat.card (H² (-, 𝔽₂)) = 2` (`card_H2_DN`, `card_H2_DM`), by the generic
  one-relator upper bound `WordCoh.card_H2_le_two` together with a nonzero cup square.
* **EV-1b** `demushkinRank 2 (-) = coreRank h` (`demushkinRank_DN`, `demushkinRank_DM`),
  read straight off the `H¹` coordinate bijection.

## The shared even Gram

Both even relators have the *same* cup Gram — MC2's `mRelWord_centLift_fib` and
`nRelWord_centLift_fib` (`GQ2/Dyadic/MarkedCore/Cores.lean:1435`, `:1455`) deliver literally the
same value, in each core's own basis, once `α ≥ 2`:

`v₀w₀ + (v₀w₁ + v₁w₀) + (v₂w₃ + v₃w₂) + Σⱼ (vᵤⱼwᵥⱼ + vᵥⱼwᵤⱼ)`,

which is `evenCupForm` below.  Its head block is `[[1,1],[1,0]]` (the diagonal Bockstein sits in
slot `0`, coming from `a²` on the `M` row and from `a^{2+2^α}` on the `N` row) and every
remaining block is a hyperbolic swap.  The `α ≥ 2` hypothesis is not decoration: it is exactly
what `diagCoeff_two_pow` needs, and at `α = 1` the displayed matrix is wrong on both rows — the
`N` exponent becomes `2 + 2 = 4 ≡ 0 (mod 4)` so the head diagonal entry dies, while on the `M`
row `c^{2^α} = c²` acquires a *second* diagonal entry at slot `2`.  Nothing below applies at
`α = 1`.

Because the form is `α`-independent and identical on the two rows, every statement below is
proved once against `evenCupForm` and instantiated twice.

The **cup square** is especially simple: `evenCupForm v v = v 0` in characteristic two
(`evenCupForm_self`), so any vector with `v 0 = 1` has nonzero cup square — that is the lower
bound `2 ≤ #H²`.
-/

namespace GQ2.Dyadic.EvenModel

noncomputable section

open GQ2 GQ2.Dyadic.MarkedCore ContCoh

/-! ## §0 The (unique) scalar action on `𝔽₂` at the two cores -/

local instance evenScalarActionDN (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenContinuousScalarDN (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

local instance evenScalarActionDM (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenContinuousScalarDM (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The shared even cup form -/

/-- **The even relator Gram, as a bilinear form on coordinate vectors.**  This is verbatim the
right-hand side of MC2's `mRelWord_centLift_fib` / `nRelWord_centLift_fib` after the cup cocycle
`κ(a, b) = ⟨v, a⟩·⟨w, b⟩` is substituted: the head block `[[1,1],[1,0]]` on slots `0, 1`, the
core hyperbolic pair on slots `2, 3`, and one hyperbolic pair per handle. -/
def evenCupForm {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) : ZMod 2 :=
  v 0 * w 0 + (v 0 * w 1 + v 1 * w 0) + (v 2 * w 3 + v 3 * w 2)
    + ∑ j, (v (handleIdxU j) * w (handleIdxV j) + v (handleIdxV j) * w (handleIdxU j))

/-- The even Gram is symmetric — the head block `[[1,1],[1,0]]` and every hyperbolic block are.
This is why one nondegeneracy argument serves both slots of `IsDemushkin`. -/
theorem evenCupForm_comm {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) :
    evenCupForm v w = evenCupForm w v := by
  have hsum : (∑ j, (v (handleIdxU j) * w (handleIdxV j) +
      v (handleIdxV j) * w (handleIdxU j))) =
        ∑ j, (w (handleIdxU j) * v (handleIdxV j) + w (handleIdxV j) * v (handleIdxU j)) :=
    Finset.sum_congr rfl fun j _ => by ring
  simp only [evenCupForm]
  rw [hsum]
  ring

/-- **The cup square is the head coordinate.**  In characteristic two every off-diagonal
contribution to `evenCupForm v v` cancels in pairs, leaving `v₀² = v₀`. -/
theorem evenCupForm_self {h : ℕ} (v : Fin (coreRank h) → ZMod 2) :
    evenCupForm v v = v 0 := by
  have hsum : (∑ j, (v (handleIdxU j) * v (handleIdxV j) +
      v (handleIdxV j) * v (handleIdxU j))) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [mul_comm (v (handleIdxV j))]
      exact CharTwo.add_self_eq_zero _
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  simp only [evenCupForm, hsum, add_zero]
  rw [mul_comm (v 1) (v 0), mul_comm (v 3) (v 2), CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, add_zero, add_zero]
  exact hsq (v 0)

/-! ## §2 The pair-cup detector cocycle

The finite quotient carrying a pair of mod-two coordinate characters, and its bilinear cup
cocycle.  This is the even twin of `GQ2.Dyadic.LSquare.dsqPairCupCocycle`, restated here so that
this file does not import the odd `L_sq` lane. -/

/-- The finite base carrying a pair of coordinate characters. -/
abbrev EvenCupBase := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- The standard cup cocycle on the two coordinate factors. -/
def evenPairCupCocycle : GQ2.DRCoh.TwoCocycle EvenCupBase where
  κ p q := Multiplicative.toAdd p.1 * Multiplicative.toAdd q.2
  norm := by simp
  cocyc p q r := by
    rw [show (p * q).1 = p.1 * q.1 from rfl, show (q * r).2 = q.2 * r.2 from rfl,
      toAdd_mul, toAdd_mul]
    ring

/-- The pair cocycle is bilinear on the elementary abelian base — MC2's `IsCupCocycle`. -/
theorem evenPairCupCocycle_isCup : IsCupCocycle evenPairCupCocycle where
  comm p q := by
    apply Prod.ext
    · exact Multiplicative.toAdd.injective (add_comm _ _)
    · exact Multiplicative.toAdd.injective (add_comm _ _)
  expTwo p := by
    apply Prod.ext
    · exact Multiplicative.toAdd.injective (CharTwo.add_self_eq_zero _)
    · exact Multiplicative.toAdd.injective (CharTwo.add_self_eq_zero _)
  addLeft p q r := by simp [evenPairCupCocycle, add_mul]
  addRight p q r := by simp [evenPairCupCocycle, mul_add]

/-! ## §3 Coordinate characters and `H¹` (EV-1c) -/

section NRow

variable {α h : ℕ}

/-- Mod-two characters of the `N_α` presentation are arbitrary generator values: its relator
abelianizes to `x₀^{2+2^α}` with an even exponent, so it dies in every elementary abelian
target. -/
def dnCharacterEquivFun (α h : ℕ) (hα : 1 ≤ α) :
    ContinuousMonoidHom (DN α h : Type) (Multiplicative (ZMod 2)) ≃
      (Fin (coreRank h) → Multiplicative (ZMod 2)) where
  toFun f i := f (dnGen α h i)
  invFun m :=
    nLiftHom α h isProPTwo_multiplicativeZModTwo m ((markedRelator_DN α h hα).frattini m)
  left_inv f := dn_hom_ext _ _ fun i => by simp
  right_inv m := funext fun i => by simp

/-- The mod-two character with prescribed values on the `N_α` generators. -/
def dnCoordinateCharacter (α h : ℕ) (hα : 1 ≤ α) (v : Fin (coreRank h) → ZMod 2) :
    ContinuousMonoidHom (DN α h : Type) (Multiplicative (ZMod 2)) :=
  (dnCharacterEquivFun α h hα).symm fun i => Multiplicative.ofAdd (v i)

@[simp] theorem dnCoordinateCharacter_gen (α h : ℕ) (hα : 1 ≤ α)
    (v : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)) :
    dnCoordinateCharacter α h hα v (dnGen α h i) = Multiplicative.ofAdd (v i) :=
  congrFun ((dnCharacterEquivFun α h hα).apply_symm_apply
    fun i => Multiplicative.ofAdd (v i)) i

/-- The normalized one-cocycle attached to a coordinate vector. -/
def dnCoordinateZOne (α h : ℕ) (hα : 1 ≤ α) (v : Fin (coreRank h) → ZMod 2) :
    Z1 (DN α h : Type) (ZMod 2) :=
  Count.homEquivZ1 (dnCoordinateCharacter α h hα v)

/-- The corresponding degree-one cohomology class. -/
def dnCoordinateHOne (α h : ℕ) (hα : 1 ≤ α) (v : Fin (coreRank h) → ZMod 2) :
    H1 (DN α h : Type) (ZMod 2) :=
  H1mk _ _ (dnCoordinateZOne α h hα v)

private def dnH1EquivZOne (α h : ℕ) :
    H1 (DN α h : Type) (ZMod 2) ≃+ Z1 (DN α h : Type) (ZMod 2) :=
  H1equivZ1OfTrivial fun _ _ => rfl

private theorem dnH1EquivZOne_coordinate (α h : ℕ) (hα : 1 ≤ α)
    (v : Fin (coreRank h) → ZMod 2) :
    dnH1EquivZOne α h (dnCoordinateHOne α h hα v) = dnCoordinateZOne α h hα v := rfl

/-- **EV-1c, `N` row.**  Coordinate vectors give every mod-two `H¹` class of `D_N`, uniquely. -/
theorem dnCoordinateHOne_bijective (α h : ℕ) (hα : 1 ≤ α) :
    Function.Bijective (dnCoordinateHOne α h hα) := by
  constructor
  · intro v w hvw
    have hz := congrArg (dnH1EquivZOne α h) hvw
    rw [dnH1EquivZOne_coordinate, dnH1EquivZOne_coordinate] at hz
    have hc : dnCoordinateCharacter α h hα v = dnCoordinateCharacter α h hα w :=
      Count.homEquivZ1.injective hz
    funext i
    have hi := DFunLike.congr_fun hc (dnGen α h i)
    rw [dnCoordinateCharacter_gen, dnCoordinateCharacter_gen] at hi
    exact Multiplicative.ofAdd.injective hi
  · intro x
    let c := Count.homEquivZ1.symm (dnH1EquivZOne α h x)
    refine ⟨fun i => Multiplicative.toAdd (c (dnGen α h i)), ?_⟩
    apply (dnH1EquivZOne α h).injective
    rw [dnH1EquivZOne_coordinate]
    change Count.homEquivZ1 (dnCoordinateCharacter α h hα _) = dnH1EquivZOne α h x
    have hc : dnCoordinateCharacter α h hα
        (fun i => Multiplicative.toAdd (c (dnGen α h i))) = c :=
      dn_hom_ext _ _ fun i => by rw [dnCoordinateCharacter_gen]; exact ofAdd_toAdd _
    rw [hc, Count.homEquivZ1.apply_symm_apply]

@[simp] theorem dnCoordinateHOne_zero (α h : ℕ) (hα : 1 ≤ α) :
    dnCoordinateHOne α h hα 0 = 0 := by
  apply (dnH1EquivZOne α h).injective
  rw [dnH1EquivZOne_coordinate, map_zero]
  have hchar : dnCoordinateCharacter α h hα 0 = 1 :=
    dn_hom_ext _ _ fun i => by rw [dnCoordinateCharacter_gen]; rfl
  rw [dnCoordinateZOne, hchar]
  rfl

/-- Nonzero classes are exactly nonzero coordinate vectors. -/
theorem dnCoordinateHOne_ne_zero_iff (α h : ℕ) (hα : 1 ≤ α)
    (v : Fin (coreRank h) → ZMod 2) :
    dnCoordinateHOne α h hα v ≠ 0 ↔ v ≠ 0 := by
  rw [← dnCoordinateHOne_zero α h hα]
  exact (dnCoordinateHOne_bijective α h hα).injective.ne_iff

end NRow

section MRow

variable {α h : ℕ}

/-- Mod-two characters of the `M_α` presentation are arbitrary generator values: its relator
abelianizes to `a²c^{2^α}`, both exponents even once `α ≥ 1`. -/
def dmCharacterEquivFun (α h : ℕ) (hα : 1 ≤ α) :
    ContinuousMonoidHom (DM α h : Type) (Multiplicative (ZMod 2)) ≃
      (Fin (coreRank h) → Multiplicative (ZMod 2)) where
  toFun f i := f (dmGen α h i)
  invFun m :=
    mLiftHom α h isProPTwo_multiplicativeZModTwo m ((markedRelator_DM α h hα).frattini m)
  left_inv f := dm_hom_ext _ _ fun i => by simp
  right_inv m := funext fun i => by simp

/-- The mod-two character with prescribed values on the `M_α` generators. -/
def dmCoordinateCharacter (α h : ℕ) (hα : 1 ≤ α) (v : Fin (coreRank h) → ZMod 2) :
    ContinuousMonoidHom (DM α h : Type) (Multiplicative (ZMod 2)) :=
  (dmCharacterEquivFun α h hα).symm fun i => Multiplicative.ofAdd (v i)

@[simp] theorem dmCoordinateCharacter_gen (α h : ℕ) (hα : 1 ≤ α)
    (v : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)) :
    dmCoordinateCharacter α h hα v (dmGen α h i) = Multiplicative.ofAdd (v i) :=
  congrFun ((dmCharacterEquivFun α h hα).apply_symm_apply
    fun i => Multiplicative.ofAdd (v i)) i

/-- The normalized one-cocycle attached to a coordinate vector. -/
def dmCoordinateZOne (α h : ℕ) (hα : 1 ≤ α) (v : Fin (coreRank h) → ZMod 2) :
    Z1 (DM α h : Type) (ZMod 2) :=
  Count.homEquivZ1 (dmCoordinateCharacter α h hα v)

/-- The corresponding degree-one cohomology class. -/
def dmCoordinateHOne (α h : ℕ) (hα : 1 ≤ α) (v : Fin (coreRank h) → ZMod 2) :
    H1 (DM α h : Type) (ZMod 2) :=
  H1mk _ _ (dmCoordinateZOne α h hα v)

private def dmH1EquivZOne (α h : ℕ) :
    H1 (DM α h : Type) (ZMod 2) ≃+ Z1 (DM α h : Type) (ZMod 2) :=
  H1equivZ1OfTrivial fun _ _ => rfl

private theorem dmH1EquivZOne_coordinate (α h : ℕ) (hα : 1 ≤ α)
    (v : Fin (coreRank h) → ZMod 2) :
    dmH1EquivZOne α h (dmCoordinateHOne α h hα v) = dmCoordinateZOne α h hα v := rfl

/-- **EV-1c, `M` row.** -/
theorem dmCoordinateHOne_bijective (α h : ℕ) (hα : 1 ≤ α) :
    Function.Bijective (dmCoordinateHOne α h hα) := by
  constructor
  · intro v w hvw
    have hz := congrArg (dmH1EquivZOne α h) hvw
    rw [dmH1EquivZOne_coordinate, dmH1EquivZOne_coordinate] at hz
    have hc : dmCoordinateCharacter α h hα v = dmCoordinateCharacter α h hα w :=
      Count.homEquivZ1.injective hz
    funext i
    have hi := DFunLike.congr_fun hc (dmGen α h i)
    rw [dmCoordinateCharacter_gen, dmCoordinateCharacter_gen] at hi
    exact Multiplicative.ofAdd.injective hi
  · intro x
    let c := Count.homEquivZ1.symm (dmH1EquivZOne α h x)
    refine ⟨fun i => Multiplicative.toAdd (c (dmGen α h i)), ?_⟩
    apply (dmH1EquivZOne α h).injective
    rw [dmH1EquivZOne_coordinate]
    change Count.homEquivZ1 (dmCoordinateCharacter α h hα _) = dmH1EquivZOne α h x
    have hc : dmCoordinateCharacter α h hα
        (fun i => Multiplicative.toAdd (c (dmGen α h i))) = c :=
      dm_hom_ext _ _ fun i => by rw [dmCoordinateCharacter_gen]; exact ofAdd_toAdd _
    rw [hc, Count.homEquivZ1.apply_symm_apply]

@[simp] theorem dmCoordinateHOne_zero (α h : ℕ) (hα : 1 ≤ α) :
    dmCoordinateHOne α h hα 0 = 0 := by
  apply (dmH1EquivZOne α h).injective
  rw [dmH1EquivZOne_coordinate, map_zero]
  have hchar : dmCoordinateCharacter α h hα 0 = 1 :=
    dm_hom_ext _ _ fun i => by rw [dmCoordinateCharacter_gen]; rfl
  rw [dmCoordinateZOne, hchar]
  rfl

/-- Nonzero classes are exactly nonzero coordinate vectors. -/
theorem dmCoordinateHOne_ne_zero_iff (α h : ℕ) (hα : 1 ≤ α)
    (v : Fin (coreRank h) → ZMod 2) :
    dmCoordinateHOne α h hα v ≠ 0 ↔ v ≠ 0 := by
  rw [← dmCoordinateHOne_zero α h hα]
  exact (dmCoordinateHOne_bijective α h hα).injective.ne_iff

end MRow

/-! ## §4 The cup product of two coordinate classes -/

section Cup

variable {α h : ℕ}

/-- A cocycle representative for the cup product of two `N`-coordinate classes. -/
def dnCoordinateCupZTwo (α h : ℕ) (hα : 1 ≤ α) (v w : Fin (coreRank h) → ZMod 2) :
    Z2 (DN α h : Type) (ZMod 2) :=
  ⟨cup11Fun AddMonoidHom.mul (dnCoordinateZOne α h hα v).1 (dnCoordinateZOne α h hα w).1,
    cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl)
      (dnCoordinateZOne α h hα v) (dnCoordinateZOne α h hα w)⟩

theorem dnCoordinateHOne_cup (α h : ℕ) (hα : 1 ≤ α) (v w : Fin (coreRank h) → ZMod 2) :
    trivialCupPairing 2 (DN α h : Type) (fun _ _ => rfl)
        (dnCoordinateHOne α h hα v) (dnCoordinateHOne α h hα w) =
      H2mk (DN α h : Type) (ZMod 2) (dnCoordinateCupZTwo α h hα v w) := rfl

/-- **The `N`-row one-relator obstruction of a coordinate cup product is the even Gram.** -/
theorem obsH2_DN_coordinateCup (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α)
    (v w : Fin (coreRank h) → ZMod 2) :
    WordCoh.obsH2 (fun _ _ => rfl) (nNatWord α h) (dnGen α h) (markedRelator_DN α h hα)
        (H2mk (DN α h : Type) (ZMod 2) (dnCoordinateCupZTwo α h hα v w)) =
      evenCupForm v w := by
  let rho : (DN α h : Type) →* EvenCupBase :=
    (dnCoordinateCharacter α h hα v).toMonoidHom.prod
      (dnCoordinateCharacter α h hα w).toMonoidHom
  have hfactor : ∀ g k : (DN α h : Type),
      (dnCoordinateCupZTwo α h hα v w).1 (g, k) =
        (WordCoh.ofDRCoh evenPairCupCocycle).κ (rho g) (rho k) := fun _ _ => rfl
  rw [WordCoh.obsH2_eq_of_factor (fun _ _ => rfl) (nNatWord α h) (dnGen α h)
    (markedRelator_DN α h hα) (dnCoordinateCupZTwo α h hα v w) rho
    (WordCoh.ofDRCoh evenPairCupCocycle) hfactor]
  have hgen : ∀ (u : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)),
      Multiplicative.toAdd ((dnCoordinateCharacter α h hα u).toMonoidHom (dnGen α h i)) = u i := by
    intro u i
    change Multiplicative.toAdd (dnCoordinateCharacter α h hα u (dnGen α h i)) = u i
    rw [dnCoordinateCharacter_gen, toAdd_ofAdd]
  rw [relZ_nNatWord_cupGram evenPairCupCocycle_isCup hα2 fun i => rho (dnGen α h i)]
  simp only [evenCupForm, rho, evenPairCupCocycle, MonoidHom.prod_apply, hgen]

/-- A cocycle representative for the cup product of two `M`-coordinate classes. -/
def dmCoordinateCupZTwo (α h : ℕ) (hα : 1 ≤ α) (v w : Fin (coreRank h) → ZMod 2) :
    Z2 (DM α h : Type) (ZMod 2) :=
  ⟨cup11Fun AddMonoidHom.mul (dmCoordinateZOne α h hα v).1 (dmCoordinateZOne α h hα w).1,
    cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl)
      (dmCoordinateZOne α h hα v) (dmCoordinateZOne α h hα w)⟩

theorem dmCoordinateHOne_cup (α h : ℕ) (hα : 1 ≤ α) (v w : Fin (coreRank h) → ZMod 2) :
    trivialCupPairing 2 (DM α h : Type) (fun _ _ => rfl)
        (dmCoordinateHOne α h hα v) (dmCoordinateHOne α h hα w) =
      H2mk (DM α h : Type) (ZMod 2) (dmCoordinateCupZTwo α h hα v w) := rfl

/-- **The `M`-row one-relator obstruction of a coordinate cup product is the even Gram** — the
same form, in the `M` basis. -/
theorem obsH2_DM_coordinateCup (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α)
    (v w : Fin (coreRank h) → ZMod 2) :
    WordCoh.obsH2 (fun _ _ => rfl) (mNatWord α h) (dmGen α h) (markedRelator_DM α h hα)
        (H2mk (DM α h : Type) (ZMod 2) (dmCoordinateCupZTwo α h hα v w)) =
      evenCupForm v w := by
  let rho : (DM α h : Type) →* EvenCupBase :=
    (dmCoordinateCharacter α h hα v).toMonoidHom.prod
      (dmCoordinateCharacter α h hα w).toMonoidHom
  have hfactor : ∀ g k : (DM α h : Type),
      (dmCoordinateCupZTwo α h hα v w).1 (g, k) =
        (WordCoh.ofDRCoh evenPairCupCocycle).κ (rho g) (rho k) := fun _ _ => rfl
  rw [WordCoh.obsH2_eq_of_factor (fun _ _ => rfl) (mNatWord α h) (dmGen α h)
    (markedRelator_DM α h hα) (dmCoordinateCupZTwo α h hα v w) rho
    (WordCoh.ofDRCoh evenPairCupCocycle) hfactor]
  have hgen : ∀ (u : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)),
      Multiplicative.toAdd ((dmCoordinateCharacter α h hα u).toMonoidHom (dmGen α h i)) = u i := by
    intro u i
    change Multiplicative.toAdd (dmCoordinateCharacter α h hα u (dmGen α h i)) = u i
    rw [dmCoordinateCharacter_gen, toAdd_ofAdd]
  rw [relZ_mNatWord_cupGram evenPairCupCocycle_isCup hα2 fun i => rho (dmGen α h i)]
  simp only [evenCupForm, rho, evenPairCupCocycle, MonoidHom.prod_apply, hgen]

/-- A nonzero Gram value detects a nonzero cup class on the `N` row. -/
theorem dnCoordinateHOne_cup_ne_zero_of_gram (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α)
    {v w : Fin (coreRank h) → ZMod 2} (hgram : evenCupForm v w ≠ 0) :
    trivialCupPairing 2 (DN α h : Type) (fun _ _ => rfl)
        (dnCoordinateHOne α h hα v) (dnCoordinateHOne α h hα w) ≠ 0 := by
  rw [dnCoordinateHOne_cup]
  intro hzero
  have hobs := congrArg
    (WordCoh.obsH2 (fun _ _ => rfl) (nNatWord α h) (dnGen α h) (markedRelator_DN α h hα)) hzero
  rw [obsH2_DN_coordinateCup α h hα hα2, map_zero] at hobs
  exact hgram hobs

/-- A nonzero Gram value detects a nonzero cup class on the `M` row. -/
theorem dmCoordinateHOne_cup_ne_zero_of_gram (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α)
    {v w : Fin (coreRank h) → ZMod 2} (hgram : evenCupForm v w ≠ 0) :
    trivialCupPairing 2 (DM α h : Type) (fun _ _ => rfl)
        (dmCoordinateHOne α h hα v) (dmCoordinateHOne α h hα w) ≠ 0 := by
  rw [dmCoordinateHOne_cup]
  intro hzero
  have hobs := congrArg
    (WordCoh.obsH2 (fun _ _ => rfl) (mNatWord α h) (dmGen α h) (markedRelator_DM α h hα)) hzero
  rw [obsH2_DM_coordinateCup α h hα hα2, map_zero] at hobs
  exact hgram hobs

end Cup

/-! ## §5 EV-1a: `#H² = 2`, and EV-1b: the rank -/

/-- The head coordinate vector `e₀`, whose cup square is the nonzero `H²` class. -/
def evenHeadVector (h : ℕ) : Fin (coreRank h) → ZMod 2 := Pi.single 0 1

@[simp] theorem evenHeadVector_zero (h : ℕ) : evenHeadVector h 0 = 1 := by
  simp [evenHeadVector]

/-- The head cup square is the nonzero Gram value `1`. -/
theorem evenCupForm_head (h : ℕ) : evenCupForm (evenHeadVector h) (evenHeadVector h) = 1 := by
  rw [evenCupForm_self, evenHeadVector_zero]

/-- **EV-1a, `N` row.**  The even `N` core has one-dimensional mod-two `H²`. -/
theorem card_H2_DN (α h : ℕ) (hα2 : 2 ≤ α) :
    Nat.card (H2 (DN α h : Type) (ZMod 2)) = 2 := by
  have hα : 1 ≤ α := le_trans one_le_two hα2
  letI : Finite (H2 (DN α h : Type) (ZMod 2)) :=
    WordCoh.finite_H2 (fun _ _ => rfl) (nNatWord α h) (dnGen α h)
      (markedRelator_DN α h hα) (presentedBy_DN α h) (isProP_DN α h)
  have hle : Nat.card (H2 (DN α h : Type) (ZMod 2)) ≤ 2 :=
    WordCoh.card_H2_le_two (fun _ _ => rfl) (nNatWord α h) (dnGen α h)
      (markedRelator_DN α h hα) (presentedBy_DN α h) (isProP_DN α h)
  letI : Nontrivial (H2 (DN α h : Type) (ZMod 2)) :=
    ⟨trivialCupPairing 2 (DN α h : Type) (fun _ _ => rfl)
        (dnCoordinateHOne α h hα (evenHeadVector h))
        (dnCoordinateHOne α h hα (evenHeadVector h)), 0,
      dnCoordinateHOne_cup_ne_zero_of_gram α h hα hα2
        (by rw [evenCupForm_head]; exact one_ne_zero)⟩
  have hgt : 1 < Nat.card (H2 (DN α h : Type) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

/-- **EV-1a, `M` row.** -/
theorem card_H2_DM (α h : ℕ) (hα2 : 2 ≤ α) :
    Nat.card (H2 (DM α h : Type) (ZMod 2)) = 2 := by
  have hα : 1 ≤ α := le_trans one_le_two hα2
  letI : Finite (H2 (DM α h : Type) (ZMod 2)) :=
    WordCoh.finite_H2 (fun _ _ => rfl) (mNatWord α h) (dmGen α h)
      (markedRelator_DM α h hα) (presentedBy_DM α h) (isProP_DM α h)
  have hle : Nat.card (H2 (DM α h : Type) (ZMod 2)) ≤ 2 :=
    WordCoh.card_H2_le_two (fun _ _ => rfl) (mNatWord α h) (dmGen α h)
      (markedRelator_DM α h hα) (presentedBy_DM α h) (isProP_DM α h)
  letI : Nontrivial (H2 (DM α h : Type) (ZMod 2)) :=
    ⟨trivialCupPairing 2 (DM α h : Type) (fun _ _ => rfl)
        (dmCoordinateHOne α h hα (evenHeadVector h))
        (dmCoordinateHOne α h hα (evenHeadVector h)), 0,
      dmCoordinateHOne_cup_ne_zero_of_gram α h hα hα2
        (by rw [evenCupForm_head]; exact one_ne_zero)⟩
  have hgt : 1 < Nat.card (H2 (DM α h : Type) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

/-- `#H¹(D_N, 𝔽₂) = 2 ^ coreRank h` — the coordinate bijection, counted. -/
theorem card_H1_DN (α h : ℕ) (hα : 1 ≤ α) :
    Nat.card (H1 (DN α h : Type) (ZMod 2)) = 2 ^ coreRank h := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (dnCoordinateHOne_bijective α h hα)),
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- `#H¹(D_M, 𝔽₂) = 2 ^ coreRank h`. -/
theorem card_H1_DM (α h : ℕ) (hα : 1 ≤ α) :
    Nat.card (H1 (DM α h : Type) (ZMod 2)) = 2 ^ coreRank h := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (dmCoordinateHOne_bijective α h hα)),
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **EV-1b, `N` row.**  The relator lies in the Frattini subgroup, so no generator is consumed
and `H¹` has the full literal marking rank. -/
theorem demushkinRank_DN (α h : ℕ) (hα : 1 ≤ α) :
    demushkinRank 2 (DN α h : Type) = coreRank h :=
  demushkinRank_eq_of_card (card_H1_DN α h hα)

/-- **EV-1b, `M` row.** -/
theorem demushkinRank_DM (α h : ℕ) (hα : 1 ≤ α) :
    demushkinRank 2 (DM α h : Type) = coreRank h :=
  demushkinRank_eq_of_card (card_H1_DM α h hα)

/-- `H¹(D_N, 𝔽₂)` is finite. -/
theorem finite_H1_DN (α h : ℕ) (hα : 1 ≤ α) : Finite (H1 (DN α h : Type) (ZMod 2)) :=
  Finite.of_equiv _ (Equiv.ofBijective _ (dnCoordinateHOne_bijective α h hα))

/-- `H¹(D_M, 𝔽₂)` is finite. -/
theorem finite_H1_DM (α h : ℕ) (hα : 1 ≤ α) : Finite (H1 (DM α h : Type) (ZMod 2)) :=
  Finite.of_equiv _ (Equiv.ofBijective _ (dmCoordinateHOne_bijective α h hα))

/-! ## §6 Axiom hygiene

Every declaration in this file is std-3 (`propext`, `Classical.choice`, `Quot.sound`).  No census
axiom is named: the `MarkedRelator` / `PresentedBy` bundles and the `IsCupCocycle` Gram are all
theorems of `MarkedCore/`, and the coefficient action is the canonical `scalarActionZmodTwo`. -/

#print axioms dnCoordinateHOne_bijective
#print axioms dmCoordinateHOne_bijective
#print axioms obsH2_DN_coordinateCup
#print axioms obsH2_DM_coordinateCup
#print axioms card_H2_DN
#print axioms card_H2_DM
#print axioms demushkinRank_DN
#print axioms demushkinRank_DM

end

end GQ2.Dyadic.EvenModel
