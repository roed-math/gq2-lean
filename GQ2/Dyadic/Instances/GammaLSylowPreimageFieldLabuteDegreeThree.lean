/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteElementaryH2
import GQ2.Dyadic.Count.H3CompletedCubicFiniteOperator

/-!
# The first higher lower-two-central layer

This file connects the unconditional cubic completed-Magnus calculation for the literal
improved square relator to the first unresolved numerical lower-two-central layer.  It also
packages the exact degree-three Labute relation-space statement needed on both the model and
arithmetic sides.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh
open GQ2.Dyadic.SqCore

local instance (h : ℕ) : DistribMulAction (SqCore.DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance (h : ℕ) : ContinuousSMul (SqCore.DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## Arbitrary coordinate characters and the model cup form -/

/-- The mod-two character with prescribed values on the improved presentation generators. -/
noncomputable def dsqCoordinateCharacter (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) :
    ContinuousMonoidHom (SqCore.DSq h : Type) (Multiplicative (ZMod 2)) :=
  (dsqCharacterEquivFun h).symm (fun i => Multiplicative.ofAdd (v i))

@[simp] theorem dsqCoordinateCharacter_gen (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) (i : Fin (SqCore.sqRank h)) :
    dsqCoordinateCharacter h v (SqCore.sqGen h i) = Multiplicative.ofAdd (v i) := by
  have he := congrFun ((dsqCharacterEquivFun h).apply_symm_apply
    (fun i => Multiplicative.ofAdd (v i))) i
  exact he

/-- The normalized one-cocycle attached to a coordinate vector. -/
noncomputable def dsqCoordinateZOne (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) :
    Z1 (SqCore.DSq h : Type) (ZMod 2) :=
  Count.homEquivZ1 (dsqCoordinateCharacter h v)

/-- The corresponding degree-one cohomology class. -/
noncomputable def dsqCoordinateHOne (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) :
    H1 (SqCore.DSq h : Type) (ZMod 2) :=
  H1mk _ _ (dsqCoordinateZOne h v)

private noncomputable def dsqH1EquivZOne (h : ℕ) :
    H1 (SqCore.DSq h : Type) (ZMod 2) ≃+
      Z1 (SqCore.DSq h : Type) (ZMod 2) :=
  H1equivZ1OfTrivial (fun _ _ => rfl)

private theorem dsqH1EquivZOne_coordinate (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) :
    dsqH1EquivZOne h (dsqCoordinateHOne h v) = dsqCoordinateZOne h v := by
  rfl

/-- Coordinate vectors give every mod-two `H¹` class of the improved model, uniquely. -/
theorem dsqCoordinateHOne_bijective (h : ℕ) :
    Function.Bijective (dsqCoordinateHOne h) := by
  constructor
  · intro v w hvw
    have hz := congrArg (dsqH1EquivZOne h) hvw
    rw [dsqH1EquivZOne_coordinate, dsqH1EquivZOne_coordinate] at hz
    have hc : dsqCoordinateCharacter h v = dsqCoordinateCharacter h w :=
      Count.homEquivZ1.injective hz
    funext i
    have hi := DFunLike.congr_fun hc (SqCore.sqGen h i)
    rw [dsqCoordinateCharacter_gen, dsqCoordinateCharacter_gen] at hi
    exact Multiplicative.ofAdd.injective hi
  · intro x
    let z := dsqH1EquivZOne h x
    let c := Count.homEquivZ1.symm z
    let v : Fin (SqCore.sqRank h) → ZMod 2 := fun i =>
      Multiplicative.toAdd (c (SqCore.sqGen h i))
    refine ⟨v, ?_⟩
    apply (dsqH1EquivZOne h).injective
    rw [dsqH1EquivZOne_coordinate]
    change Count.homEquivZ1 (dsqCoordinateCharacter h v) = z
    have hc : dsqCoordinateCharacter h v = c := by
      apply SqCore.dsq_hom_ext
      intro i
      rw [dsqCoordinateCharacter_gen]
      exact ofAdd_toAdd _
    rw [hc, Count.homEquivZ1.apply_symm_apply]

/-- The rank-one matrix recording the cup product of two coordinate characters. -/
def dsqCupMatrix (h : ℕ)
    (v w : Fin (SqCore.sqRank h) → ZMod 2)
    (i j : Fin (SqCore.sqRank h)) : ZMod 2 :=
  v i * w j

/-- A cocycle representative for the cup product of two coordinate classes. -/
noncomputable def dsqCoordinateCupZTwo (h : ℕ)
    (v w : Fin (SqCore.sqRank h) → ZMod 2) :
    Z2 (SqCore.DSq h : Type) (ZMod 2) :=
  ⟨cup11Fun AddMonoidHom.mul (dsqCoordinateZOne h v).1
      (dsqCoordinateZOne h w).1,
    cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl)
      (dsqCoordinateZOne h v) (dsqCoordinateZOne h w)⟩

theorem dsqCoordinateHOne_cup (h : ℕ)
    (v w : Fin (SqCore.sqRank h) → ZMod 2) :
    trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqCoordinateHOne h v) (dsqCoordinateHOne h w) =
      H2mk (SqCore.DSq h : Type) (ZMod 2) (dsqCoordinateCupZTwo h v w) := by
  rfl

/-- The finite quotient carrying a pair of coordinate characters. -/
abbrev DsqCupBase := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- The standard cup cocycle on the two coordinate factors. -/
def dsqPairCupCocycle : GQ2.DRCoh.TwoCocycle DsqCupBase where
  κ p q := Multiplicative.toAdd p.1 * Multiplicative.toAdd q.2
  norm := by simp
  cocyc p q r := by
    rw [show (p * q).1 = p.1 * q.1 from rfl,
      show (q * r).2 = q.2 * r.2 from rfl, toAdd_mul, toAdd_mul]
    ring

/-- The pair cocycle is bilinear on an elementary abelian base. -/
theorem dsqPairCupCocycle_isCup :
    GQ2.Dyadic.MarkedCore.IsCupCocycle dsqPairCupCocycle where
  comm p q := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      exact add_comm _ _
    · apply Multiplicative.toAdd.injective
      exact add_comm _ _
  expTwo p := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      exact CharTwo.add_self_eq_zero _
    · apply Multiplicative.toAdd.injective
      exact CharTwo.add_self_eq_zero _
  addLeft p q r := by simp [dsqPairCupCocycle, add_mul]
  addRight p q r := by simp [dsqPairCupCocycle, mul_add]

/-- The one-relator obstruction of an arbitrary coordinate cup product is exactly contraction
against the constructor table of the literal improved quadratic relation. -/
theorem obsH2_DSq_coordinateCup (h : ℕ)
    (v w : Fin (SqCore.sqRank h) → ZMod 2) :
    WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h)
        (SqCore.sqGen h) (markedRelator_DSq h)
        (H2mk (SqCore.DSq h : Type) (ZMod 2) (dsqCoordinateCupZTwo h v w)) =
      sqRelatorQuadraticInitialGram h (dsqCupMatrix h v w) := by
  let rho : (SqCore.DSq h : Type) →* DsqCupBase :=
    (dsqCoordinateCharacter h v).toMonoidHom.prod
      (dsqCoordinateCharacter h w).toMonoidHom
  have hfactor : ∀ g k : (SqCore.DSq h : Type),
      (dsqCoordinateCupZTwo h v w).1 (g, k) =
        (WordCoh.ofDRCoh dsqPairCupCocycle).κ (rho g) (rho k) := by
    intro g k
    rfl
  rw [WordCoh.obsH2_eq_of_factor (fun _ _ => rfl)
    (MarkedCore.sqNatWord h) (SqCore.sqGen h) (markedRelator_DSq h)
    (dsqCoordinateCupZTwo h v w) rho
    (WordCoh.ofDRCoh dsqPairCupCocycle) hfactor]
  rw [WordCoh.relZ_ofDRCoh]
  change (SqCore.sqRelWord (fun i => MarkedCore.centLift dsqPairCupCocycle
    (rho (SqCore.sqGen h i)))).fib = _
  rw [sqRelWord_centLift_fib_eq_quadraticInitialGram dsqPairCupCocycle_isCup]
  congr 1
  funext i j
  simp [rho, dsqCupMatrix, dsqPairCupCocycle]

/-- Standard coordinate basis vector. -/
def dsqCoordinateBasis (h : ℕ) (i : Fin (SqCore.sqRank h)) :
    Fin (SqCore.sqRank h) → ZMod 2 :=
  Pi.single i 1

private theorem sqCore_zero_ne_one (h : ℕ) :
    (0 : Fin (SqCore.sqRank h)) ≠ 1 := by
  intro e
  have := congrArg Fin.val e
  rw [SqCore.sqVal_zero, SqCore.sqVal_one] at this
  omega

private theorem sqCore_zero_ne_two (h : ℕ) :
    (0 : Fin (SqCore.sqRank h)) ≠ 2 := by
  intro e
  have := congrArg Fin.val e
  rw [SqCore.sqVal_zero, SqCore.sqVal_two] at this
  omega

private theorem sqCore_one_ne_two (h : ℕ) :
    (1 : Fin (SqCore.sqRank h)) ≠ 2 := by
  intro e
  have := congrArg Fin.val e
  rw [SqCore.sqVal_one, SqCore.sqVal_two] at this
  omega

/-- Pairing with the basis vector indexed by the partner involution extracts the chosen
coordinate. -/
theorem sqRelatorQuadraticInitialGram_basis_partner (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) (i : Fin (SqCore.sqRank h)) :
    sqRelatorQuadraticInitialGram h
        (dsqCupMatrix h v (dsqCoordinateBasis h (sqInitialPartner h i))) = v i := by
  classical
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [sqRelatorQuadraticInitialGram, dsqCupMatrix, dsqCoordinateBasis,
      sqCore_zero_ne_one h, sqCore_one_ne_two h]
  · simp [sqRelatorQuadraticInitialGram, dsqCupMatrix, dsqCoordinateBasis,
      sqCore_zero_ne_one h, sqCore_zero_ne_two h]
  · simp [sqRelatorQuadraticInitialGram, dsqCupMatrix, dsqCoordinateBasis,
      sqCore_zero_ne_two h, sqCore_one_ne_two h]
  · simp only [sqInitialPartner_handleU, sqRelatorQuadraticInitialGram,
      dsqCupMatrix, dsqCoordinateBasis, Pi.single_apply,
      sqCoreZero_ne_handleV, sqCoreOne_ne_handleV, sqCoreTwo_ne_handleV,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro x hx hne
      simp [hne]
    · simp
  · simp only [sqInitialPartner_handleV, sqRelatorQuadraticInitialGram,
      dsqCupMatrix, dsqCoordinateBasis, Pi.single_apply,
      sqCoreZero_ne_handleU, sqCoreOne_ne_handleU, sqCoreTwo_ne_handleU,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro x hx hne
      simp [hne]
    · simp

/-- The constructor-table form is symmetric after exchanging its two coordinate vectors. -/
theorem sqRelatorQuadraticInitialGram_dsqCupMatrix_comm (h : ℕ)
    (v w : Fin (SqCore.sqRank h) → ZMod 2) :
    sqRelatorQuadraticInitialGram h (dsqCupMatrix h v w) =
      sqRelatorQuadraticInitialGram h (dsqCupMatrix h w v) := by
  have hsum :
      (∑ j, (v (sqHandleIdxU j) * w (sqHandleIdxV j) +
          v (sqHandleIdxV j) * w (sqHandleIdxU j))) =
        ∑ j, (w (sqHandleIdxU j) * v (sqHandleIdxV j) +
          w (sqHandleIdxV j) * v (sqHandleIdxU j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [sqRelatorQuadraticInitialGram, dsqCupMatrix]
  rw [hsum]
  ring

/-- The left-basis version of coordinate extraction. -/
theorem sqRelatorQuadraticInitialGram_partner_basis (h : ℕ)
    (w : Fin (SqCore.sqRank h) → ZMod 2) (i : Fin (SqCore.sqRank h)) :
    sqRelatorQuadraticInitialGram h
        (dsqCupMatrix h (dsqCoordinateBasis h (sqInitialPartner h i)) w) = w i := by
  rw [sqRelatorQuadraticInitialGram_dsqCupMatrix_comm,
    sqRelatorQuadraticInitialGram_basis_partner]

/-- A nonzero contraction in the constructor table detects a nonzero cup-product class. -/
theorem dsqCoordinateHOne_cup_ne_zero_of_gram (h : ℕ)
    {v w : Fin (SqCore.sqRank h) → ZMod 2}
    (hgram : sqRelatorQuadraticInitialGram h (dsqCupMatrix h v w) ≠ 0) :
    trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqCoordinateHOne h v) (dsqCoordinateHOne h w) ≠ 0 := by
  rw [dsqCoordinateHOne_cup]
  intro hzero
  have hobs := congrArg
    (WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h)
      (SqCore.sqGen h) (markedRelator_DSq h)) hzero
  rw [obsH2_DSq_coordinateCup, map_zero] at hobs
  exact hgram hobs

@[simp] theorem dsqCoordinateHOne_zero (h : ℕ) :
    dsqCoordinateHOne h 0 = 0 := by
  apply (dsqH1EquivZOne h).injective
  rw [dsqH1EquivZOne_coordinate, map_zero]
  have hcharacter : dsqCoordinateCharacter h 0 = 1 := by
    apply SqCore.dsq_hom_ext
    intro i
    rw [dsqCoordinateCharacter_gen]
    rfl
  rw [dsqCoordinateZOne, hcharacter]
  rfl

/-- Nonzero cohomology classes are exactly nonzero coordinate vectors. -/
theorem dsqCoordinateHOne_ne_zero_iff (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2) :
    dsqCoordinateHOne h v ≠ 0 ↔ v ≠ 0 := by
  rw [← dsqCoordinateHOne_zero h]
  exact (dsqCoordinateHOne_bijective h).injective.ne_iff

/-- The literal improved one-relator model is a Demushkin pro-`2` group for every handle
count.  Its nondegenerate cup matrix is exactly the certified constructor table
`YY + SX + XS + Σ(UV + VU)`. -/
theorem isDemushkin_DSq (h : ℕ) : IsDemushkin 2 (SqCore.DSq h : Type) :=
  { smul_trivial := fun _ _ => rfl
    isProP := SqCore.isProP_DSq h
    finiteH1 := Nat.finite_of_card_ne_zero (by
      rw [card_H1_zmodTwo_eq_card_zLayer_one
        (dsqFinsetTopGen h) (SqCore.isProP_DSq h), card_zLayer_one_dsq]
      exact (Nat.two_pow_pos _).ne')
    cardH2 := card_H2_DSq h
    nondegen_left := by
      intro x hx
      obtain ⟨v, rfl⟩ := (dsqCoordinateHOne_bijective h).surjective x
      have hv : v ≠ 0 := (dsqCoordinateHOne_ne_zero_iff h v).mp hx
      have hi : ∃ i, v i ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hv (funext hall)
      obtain ⟨i, hi⟩ := hi
      refine ⟨dsqCoordinateHOne h
        (dsqCoordinateBasis h (sqInitialPartner h i)), ?_⟩
      apply dsqCoordinateHOne_cup_ne_zero_of_gram
      rw [sqRelatorQuadraticInitialGram_basis_partner]
      exact hi
    nondegen_right := by
      intro y hy
      obtain ⟨w, rfl⟩ := (dsqCoordinateHOne_bijective h).surjective y
      have hw : w ≠ 0 := (dsqCoordinateHOne_ne_zero_iff h w).mp hy
      have hi : ∃ i, w i ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hw (funext hall)
      obtain ⟨i, hi⟩ := hi
      refine ⟨dsqCoordinateHOne h
        (dsqCoordinateBasis h (sqInitialPartner h i)), ?_⟩
      apply dsqCoordinateHOne_cup_ne_zero_of_gram
      rw [sqRelatorQuadraticInitialGram_partner_basis]
      exact hi }

/-! ## The exact cubic boundary -/

/-- The degree-three dimension of the free restricted Lie algebra on `d` degree-one
generators.  Since three is prime to two, this is the ordinary Witt number. -/
def zassenhausFreeCubicPrimitiveDimension (d : ℕ) : ℕ :=
  (d ^ 3 - d) / 3

/-- The Zassenhaus/restricted-Lie primitive dimension in degree three after quotienting by one
nondegenerate quadratic relator.  For `d ≥ 2`, the degree-three bracket part of the relator
ideal has rank `d`, so this is `((d^3-d)/3)-d = (d^3-4d)/3`.

This number is **not by itself** the degree-three rank of the repository's lower exponent-two
central series: that layer also receives squares from degree two.  Rank one is exceptional:
its cubic bracket is zero, while the Nat-valued formula below still has the intended primitive
value zero. -/
def zassenhausOneRelatorCubicPrimitiveDimension (d : ℕ) : ℕ :=
  (d ^ 3 - 4 * d) / 3

/-- Cardinal form of the formerly expected third lower-two-central layer.  Because `zLayer`
uses the lower exponent-two central series while the displayed exponent is the Zassenhaus
primitive coefficient, this proposition is now an explicit cross-filtration compatibility
assertion, not a consequence of the completed mod-two PBW calculation. -/
def LowerTwoCentralDegreeThreeCrossFiltrationCard
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) : Prop :=
  Nat.card (zLayer G 3) = 2 ^ zassenhausOneRelatorCubicPrimitiveDimension d

/-- The rank-three Zassenhaus primitive regression is the first higher value: `5`. -/
theorem zassenhausOneRelatorCubicPrimitiveDimension_three :
    zassenhausOneRelatorCubicPrimitiveDimension 3 = 5 := by
  norm_num [zassenhausOneRelatorCubicPrimitiveDimension]

/-! ### The literal rank-`d` cubic relation space -/

/-- A length-three word displayed by its three letters, in the recursive finite-word type
used by the completed Magnus/PBW development. -/
def sqCubicGeneratorWord (h : ℕ) (a b c : Fin (SqCore.sqRank h)) :
    FiniteGeneratorWord (Fin (SqCore.sqRank h)) 3 :=
  (((PUnit.unit, a), b), c)

/-- The tensor coefficient of `[v,r₂] = v r₂ + r₂ v` in characteristic two, where `r₂` is
the literal quadratic initial form `YY + SX + XS + Σ(UV + VU)`. -/
def sqCubicRelatorBracketCoefficient (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2)
    (w : FiniteGeneratorWord (Fin (SqCore.sqRank h)) 3) : ZMod 2 :=
  v w.1.1.2 * sqRelatorQuadraticInitialCoefficient h w.1.2 w.2 +
    sqRelatorQuadraticInitialCoefficient h w.1.1.2 w.1.2 * v w.2

/-- Bracketing the quadratic initial relator with an arbitrary degree-one vector, as a
linear map into the free cubic tensor coefficient space used by `sqCubicScalarPBWNormalMap`. -/
def sqCubicRelatorBracketMap (h : ℕ) :
    (Fin (SqCore.sqRank h) → ZMod 2) →ₗ[ZMod 2]
      (FiniteGeneratorWord (Fin (SqCore.sqRank h)) 3 → ZMod 2) where
  toFun := sqCubicRelatorBracketCoefficient h
  map_add' v w := by
    funext word
    simp only [sqCubicRelatorBracketCoefficient, Pi.add_apply]
    ring
  map_smul' a v := by
    funext word
    simp only [sqCubicRelatorBracketCoefficient, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] theorem sqCubicRelatorBracketMap_generatorWord (h : ℕ)
    (v : Fin (SqCore.sqRank h) → ZMod 2)
    (a b c : Fin (SqCore.sqRank h)) :
    sqCubicRelatorBracketMap h v (sqCubicGeneratorWord h a b c) =
      v a * sqRelatorQuadraticInitialCoefficient h b c +
        sqRelatorQuadraticInitialCoefficient h a b * v c := by
  rfl

@[simp] theorem sqRelatorQuadraticInitialCoefficient_two_two (h : ℕ) :
    sqRelatorQuadraticInitialCoefficient h 2 2 = 1 := by
  simp [sqRelatorQuadraticInitialCoefficient]

@[simp] theorem sqRelatorQuadraticInitialCoefficient_zero_one (h : ℕ) :
    sqRelatorQuadraticInitialCoefficient h 0 1 = 1 := by
  simp [sqRelatorQuadraticInitialCoefficient]

@[simp] theorem sqRelatorQuadraticInitialCoefficient_two_zero (h : ℕ) :
    sqRelatorQuadraticInitialCoefficient h 2 0 = 0 := by
  simp [sqRelatorQuadraticInitialCoefficient, sqCore_zero_ne_two h]

theorem sqRelatorQuadraticInitialCoefficient_right_two_of_ne (h : ℕ)
    {i : Fin (SqCore.sqRank h)} (hi : i ≠ 2) :
    sqRelatorQuadraticInitialCoefficient h i 2 = 0 := by
  unfold sqRelatorQuadraticInitialCoefficient
  split_ifs with e
  · exfalso
    apply hi
    have ep := congrArg (sqInitialPartner h) e
    simpa only [sqInitialPartner_two, sqInitialPartner_involutive] using ep.symm
  · rfl

/-- **Literal degree-three relation-rank theorem.**  The map `v ↦ [v,r₂]` is injective for
every improved square relator.  The proof reads two constructor-table columns: `(i,Y,Y)`
recovers every coordinate except `Y`, and `(Y,S,X)` recovers the `Y` coordinate.  The
rank-one exception cannot occur here because `sqRank h = 3 + 2h`. -/
theorem sqCubicRelatorBracketMap_injective (h : ℕ) :
    Function.Injective (sqCubicRelatorBracketMap h) := by
  intro v w hvw
  funext i
  by_cases hi : i = 2
  · subst i
    have hentry := congrFun hvw (sqCubicGeneratorWord h 2 0 1)
    change v 2 * sqRelatorQuadraticInitialCoefficient h 0 1 +
        sqRelatorQuadraticInitialCoefficient h 2 0 * v 1 =
      w 2 * sqRelatorQuadraticInitialCoefficient h 0 1 +
        sqRelatorQuadraticInitialCoefficient h 2 0 * w 1 at hentry
    simpa only [
      sqRelatorQuadraticInitialCoefficient_zero_one,
      sqRelatorQuadraticInitialCoefficient_two_zero,
      mul_one, zero_mul, add_zero] using hentry
  · have hentry := congrFun hvw (sqCubicGeneratorWord h i 2 2)
    change v i * sqRelatorQuadraticInitialCoefficient h 2 2 +
        sqRelatorQuadraticInitialCoefficient h i 2 * v 2 =
      w i * sqRelatorQuadraticInitialCoefficient h 2 2 +
        sqRelatorQuadraticInitialCoefficient h i 2 * w 2 at hentry
    simpa only [
      sqRelatorQuadraticInitialCoefficient_two_two,
      sqRelatorQuadraticInitialCoefficient_right_two_of_ne h hi,
      mul_one, zero_mul, add_zero] using hentry

/-- The degree-three restricted-Lie relation space generated by the literal quadratic initial
form, represented inside the free cubic tensor coefficient space. -/
def sqCubicRelatorBracketSpace (h : ℕ) : Submodule (ZMod 2)
    (FiniteGeneratorWord (Fin (SqCore.sqRank h)) 3 → ZMod 2) :=
  LinearMap.range (sqCubicRelatorBracketMap h)

/-- The literal cubic relation space has exactly the degree-one rank `3 + 2h`. -/
theorem finrank_sqCubicRelatorBracketSpace (h : ℕ) :
    Module.finrank (ZMod 2) (sqCubicRelatorBracketSpace h) = SqCore.sqRank h := by
  unfold sqCubicRelatorBracketSpace
  rw [LinearMap.finrank_range_of_inj (sqCubicRelatorBracketMap_injective h),
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- Once an explicit cross-filtration equality identifies the lower-series Hilbert
coefficient with the Zassenhaus primitive dimension, it gives the corresponding cardinality
of `Z₃ = λ₃/λ₄`.  The premise, not this conversion lemma, carries that identification. -/
theorem lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) {d : ℕ}
    (hcubic : lowerTwoCentralHilbertCoefficient G 2 =
      zassenhausOneRelatorCubicPrimitiveDimension d) :
    LowerTwoCentralDegreeThreeCrossFiltrationCard G d := by
  unfold LowerTwoCentralDegreeThreeCrossFiltrationCard
  change Nat.card (zLayer G (2 + 1)) =
    2 ^ zassenhausOneRelatorCubicPrimitiveDimension d
  rw [card_zLayer_succ_eq_two_pow_hilbertCoefficient hfg hpro, hcubic]

/-- The finite-operator campaign has already discharged the completed cubic Magnus/PBW
kernel identity. -/
theorem sqCompletedCubicMagnusPBWKernelIdentity (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 3 :=
  sqCompletedMonomialPBWKernelIdentity_three h

/-- The corrected model-side Zassenhaus cubic interface: the completed PBW kernel identity
and the literal rank-`d` cubic relation-space theorem.  Both clauses are proved without
identifying a Zassenhaus dimension subgroup with a lower exponent-two central layer. -/
def SqDegreeThreeZassenhausPrimitiveSupply : Prop :=
  ∀ h : ℕ,
    SqCompletedMonomialPBWKernelIdentity h 3 ∧
      Module.finrank (ZMod 2) (sqCubicRelatorBracketSpace h) = SqCore.sqRank h

/-- The finite completed-PBW and constructor-table campaigns discharge the corrected
Zassenhaus primitive supply unconditionally. -/
theorem sqDegreeThreeZassenhausPrimitiveSupply :
    SqDegreeThreeZassenhausPrimitiveSupply := by
  intro h
  exact ⟨sqCompletedCubicMagnusPBWKernelIdentity h,
    finrank_sqCubicRelatorBracketSpace h⟩

/-- **Legacy model cross-filtration bridge.**  The completed augmentation calculation proves
its premise unconditionally.  Its conclusion, however, identifies a Zassenhaus cubic PBW
quotient with a lower exponent-two `zLayer` coefficient.  The regression in
`LowerTwoCentralJenningsDegreeThree` shows that the naive identification is impossible: the
layer-square image is nonzero but dies in the mod-two cubic quotient.  Consequently this
proposition needs a corrected filtration or an additional square summand, rather than merely
a proof of injectivity of the existing layer map. -/
def LegacySqDegreeThreeJenningsCrossFiltrationBridge : Prop :=
  ∀ h : ℕ, SqCompletedMonomialPBWKernelIdentity h 3 →
    lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) 2 =
      zassenhausOneRelatorCubicPrimitiveDimension (SqCore.sqRank h)

/-- The legacy model cross-filtration bridge would compute the third lower-series layer.
The theorem name records that the disputed bridge, not the proved Zassenhaus supply, is the
source of the conclusion. -/
theorem lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyJenningsCrossFiltration
    (H : LegacySqDegreeThreeJenningsCrossFiltrationBridge) (h : ℕ) :
    LowerTwoCentralDegreeThreeCrossFiltrationCard (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  apply lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  exact H h (sqCompletedCubicMagnusPBWKernelIdentity h)

/-- **Legacy cross-filtration universal degree-three supply.**  The bracket calculation says
that the degree-three part of the initial quadratic relation ideal has rank equal to the
degree-one rank, producing the Zassenhaus primitive coefficient `(d^3-4d)/3`.  The conclusion
below applies that number to the lower exponent-two Hilbert coefficient.  After the explicit
square-kernel regression, this is no longer a neutral packaging of a missing theorem: it also
asserts the disputed cross-filtration identification.  New proofs should split the
Zassenhaus Labute formula from the additional lower-series square contribution. -/
def LegacyDemushkinDegreeThreeCrossFiltrationSupply : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)],
    IsTopologicallyFinGen G → IsDemushkin 2 G →
      lowerTwoCentralHilbertCoefficient G 2 =
        zassenhausOneRelatorCubicPrimitiveDimension (demushkinRank 2 G)

/-- The legacy universal cross-filtration assumption specializes to every improved square
model because the constructor-table calculation proves that model is Demushkin.  This is not
a consequence of the Zassenhaus Labute formula alone. -/
theorem lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyCrossFiltration
    (H : LegacyDemushkinDegreeThreeCrossFiltrationSupply) (h : ℕ) :
    LowerTwoCentralDegreeThreeCrossFiltrationCard (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  apply lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  rw [← demushkinRank_DSq h]
  exact H (SqCore.DSq h : Type) (dsqFinsetTopGen h) (isDemushkin_DSq h)

/-- Rank-three regression under the explicit legacy cross-filtration assumption:
`|λ₃(DSq 0)/λ₄(DSq 0)| = 2^5 = 32`.  The value is not asserted as a Labute consequence. -/
theorem card_zLayer_three_dsq_zero_of_legacyCrossFiltration
    (H : LegacyDemushkinDegreeThreeCrossFiltrationSupply) :
    Nat.card (zLayer (SqCore.DSq 0 : Type) 3) = 32 := by
  have hcard := lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyCrossFiltration H 0
  unfold LowerTwoCentralDegreeThreeCrossFiltrationCard at hcard
  rw [SqCore.sqRank, zassenhausOneRelatorCubicPrimitiveDimension_three] at hcard
  norm_num at hcard ⊢
  exact hcard

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The legacy universal cross-filtration assumption gives the asserted third lower-series
cardinality for a finite dyadic field group. -/
theorem maxProTwoGalK_lowerTwoCentralDegreeThreeCrossFiltrationCard_of_legacyCrossFiltration
    (H : LegacyDemushkinDegreeThreeCrossFiltrationSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    LowerTwoCentralDegreeThreeCrossFiltrationCard (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient hfg
    isProP_maxProPQuotient
  have hcubic := H Q hfg (isDemushkin_maxProTwoGalK (K := K))
  rwa [demushkinRank_maxProTwoGalK (K := K)] at hcubic

/-- At `k = 3`, the improved odd-degree model and arithmetic group have equal order under the
same explicit legacy cross-filtration assumption. -/
theorem oddDegreeGalKSq_zLayer_three_cardAgreement_of_legacyCrossFiltration
    (H : LegacyDemushkinDegreeThreeCrossFiltrationSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    Nat.card (zLayer
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 3) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 3) := by
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  have hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2 := by
    obtain ⟨m, hm⟩ := hodd
    dsimp [h]
    rw [hm]
    simp only [SqCore.sqRank]
    omega
  have hmodel :=
    lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyCrossFiltration H h
  have hfield :=
    maxProTwoGalK_lowerTwoCentralDegreeThreeCrossFiltrationCard_of_legacyCrossFiltration
      H K hfg
  unfold LowerTwoCentralDegreeThreeCrossFiltrationCard at hmodel hfield
  rw [hmodel, hfield, hrank]

/-- Equivalently, lower-series Hilbert coefficient `2` agrees under the explicit legacy
cross-filtration assumption. -/
theorem oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_two_of_legacyCrossFiltration
    (H : LegacyDemushkinDegreeThreeCrossFiltrationSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    lowerTwoCentralHilbertCoefficient
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 2 =
      lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 2 := by
  exact congrArg (padicValNat 2)
    (oddDegreeGalKSq_zLayer_three_cardAgreement_of_legacyCrossFiltration H K hodd hfg)

/-! ## A sharply truncated Jennings/PBW route -/

/-- The cubic associative-PBW coefficient of a one-quadratic-relator algebra.  In degree
three, the two forbidden occurrences of the leading quadratic word are disjoint, leaving
`d^3 - 2d` normal words. -/
def zassenhausPBWCubicDimension (d : ℕ) : ℕ :=
  d ^ 3 - 2 * d

/-- What the degree-three restricted-Lie coefficient must be after removing from the cubic
PBW coefficient the contributions `choose(d,3)` and `d * ell₂`. -/
def zassenhausJenningsCubicPrimitiveRemainder (d : ℕ) : ℕ :=
  zassenhausPBWCubicDimension d -
    (d.choose 3 + d * lowerTwoCentralOneRelatorQuadraticDimension d)

/-- A single marked letter as a homogeneous normal word. -/
def sqQuadraticHomogeneousOneOfLetter (h : ℕ)
    (i : Fin (SqCore.sqRank h)) : SqQuadraticHomogeneousNormalWord h 1 :=
  ⟨⟨[i], by simp⟩, by simp⟩

theorem sqQuadraticHomogeneousOneOfLetter_bijective (h : ℕ) :
    Function.Bijective (sqQuadraticHomogeneousOneOfLetter h) := by
  constructor
  · intro i j hij
    have hl := congrArg (fun w : SqQuadraticHomogeneousNormalWord h 1 => w.1.1) hij
    simpa [sqQuadraticHomogeneousOneOfLetter] using hl
  · rintro ⟨⟨w, hw⟩, hlen⟩
    rcases w with _ | ⟨i, w⟩
    · simp at hlen
    rcases w with _ | ⟨j, w⟩
    · exact ⟨i, rfl⟩
    · simp at hlen

/-- Normal quadratic words, displayed as their two letters. -/
abbrev SqQuadraticNormalPair (h : ℕ) :=
  {p : Fin (SqCore.sqRank h) × Fin (SqCore.sqRank h) //
    ¬(p.1 = 1 ∧ p.2 = 0)}

/-- A normal pair as a homogeneous normal word. -/
def sqQuadraticHomogeneousTwoOfPair (h : ℕ) (p : SqQuadraticNormalPair h) :
    SqQuadraticHomogeneousNormalWord h 2 :=
  ⟨⟨[p.1.1, p.1.2], by simpa using p.2⟩, by simp⟩

theorem sqQuadraticHomogeneousTwoOfPair_bijective (h : ℕ) :
    Function.Bijective (sqQuadraticHomogeneousTwoOfPair h) := by
  constructor
  · intro p q hpq
    have hl := congrArg (fun w : SqQuadraticHomogeneousNormalWord h 2 => w.1.1) hpq
    apply Subtype.ext
    have hpairs : p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 := by
      simpa [sqQuadraticHomogeneousTwoOfPair] using hl
    exact Prod.ext hpairs.1 hpairs.2
  · rintro ⟨⟨w, hw⟩, hlen⟩
    rcases w with _ | ⟨a, w⟩
    · simp at hlen
    rcases w with _ | ⟨b, w⟩
    · simp at hlen
    rcases w with _ | ⟨c, w⟩
    · refine ⟨⟨(a, b), ?_⟩, rfl⟩
      simpa using hw
    · simp at hlen

/-- A cubic word is normal precisely when neither adjacent pair is the leading word `XS`. -/
abbrev SqQuadraticNormalTriple (h : ℕ) :=
  {p : (Fin (SqCore.sqRank h) × Fin (SqCore.sqRank h)) ×
      Fin (SqCore.sqRank h) //
    ¬((p.1.1 = 1 ∧ p.1.2 = 0) ∨ (p.1.2 = 1 ∧ p.2 = 0))}

/-- A normal triple as a homogeneous normal word. -/
def sqQuadraticHomogeneousThreeOfTriple (h : ℕ) (p : SqQuadraticNormalTriple h) :
    SqQuadraticHomogeneousNormalWord h 3 :=
  ⟨⟨[p.1.1.1, p.1.1.2, p.1.2], by simpa [not_or] using p.2⟩, by simp⟩

theorem sqQuadraticHomogeneousThreeOfTriple_bijective (h : ℕ) :
    Function.Bijective (sqQuadraticHomogeneousThreeOfTriple h) := by
  constructor
  · intro p q hpq
    have hl := congrArg (fun w : SqQuadraticHomogeneousNormalWord h 3 => w.1.1) hpq
    apply Subtype.ext
    have htriples : p.1.1.1 = q.1.1.1 ∧ p.1.1.2 = q.1.1.2 ∧
        p.1.2 = q.1.2 := by
      simpa [sqQuadraticHomogeneousThreeOfTriple] using hl
    exact Prod.ext (Prod.ext htriples.1 htriples.2.1) htriples.2.2
  · rintro ⟨⟨w, hw⟩, hlen⟩
    rcases w with _ | ⟨a, w⟩
    · simp at hlen
    rcases w with _ | ⟨b, w⟩
    · simp at hlen
    rcases w with _ | ⟨c, w⟩
    · simp at hlen
    rcases w with _ | ⟨d, w⟩
    · refine ⟨⟨((a, b), c), ?_⟩, rfl⟩
      simpa [not_or] using hw
    · simp at hlen

/-- There is only one forbidden quadratic word. -/
private def sqQuadraticBadPairEquiv (h : ℕ) :
    {p : Fin (SqCore.sqRank h) × Fin (SqCore.sqRank h) //
      p.1 = 1 ∧ p.2 = 0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(1, 0), rfl, rfl⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨a, b⟩, ha, hb⟩
    change a = 1 at ha
    change b = 0 at hb
    exact Prod.ext ha.symm hb.symm
  right_inv _ := rfl

theorem card_sqQuadraticNormalPair (h : ℕ) :
    Fintype.card (SqQuadraticNormalPair h) = SqCore.sqRank h ^ 2 - 1 := by
  classical
  rw [Fintype.card_subtype_compl]
  have hbad : Fintype.card
      {p : Fin (SqCore.sqRank h) × Fin (SqCore.sqRank h) //
        p.1 = 1 ∧ p.2 = 0} = 1 := by
    rw [Fintype.card_congr (sqQuadraticBadPairEquiv h)]
    exact Fintype.card_unit
  rw [hbad]
  simp [pow_two]

private abbrev sqCubicBadLeft (h : ℕ)
    (p : (Fin (SqCore.sqRank h) × Fin (SqCore.sqRank h)) ×
      Fin (SqCore.sqRank h)) : Prop :=
  p.1.1 = 1 ∧ p.1.2 = 0

private abbrev sqCubicBadRight (h : ℕ)
    (p : (Fin (SqCore.sqRank h) × Fin (SqCore.sqRank h)) ×
      Fin (SqCore.sqRank h)) : Prop :=
  p.1.2 = 1 ∧ p.2 = 0

private def sqCubicBadLeftEquiv (h : ℕ) :
    {p // sqCubicBadLeft h p} ≃ Fin (SqCore.sqRank h) where
  toFun p := p.1.2
  invFun c := ⟨((1, 0), c), rfl, rfl⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨⟨a, b⟩, c⟩, ha, hb⟩
    change a = 1 at ha
    change b = 0 at hb
    subst a
    subst b
    rfl
  right_inv _ := rfl

private def sqCubicBadRightEquiv (h : ℕ) :
    {p // sqCubicBadRight h p} ≃ Fin (SqCore.sqRank h) where
  toFun p := p.1.1.1
  invFun a := ⟨((a, 1), 0), rfl, rfl⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨⟨a, b⟩, c⟩, hb, hc⟩
    change b = 1 at hb
    change c = 0 at hc
    subst b
    subst c
    rfl
  right_inv _ := rfl

/-- The two forbidden placements of `XS` in a cubic word are disjoint, and each leaves one
free letter. -/
theorem card_sqQuadraticNormalTriple (h : ℕ) :
    Fintype.card (SqQuadraticNormalTriple h) =
      zassenhausPBWCubicDimension (SqCore.sqRank h) := by
  classical
  let P := sqCubicBadLeft h
  let Q := sqCubicBadRight h
  have hdisj : Disjoint P Q := by
    rw [Pi.disjoint_iff]
    intro p
    rw [disjoint_iff_inf_le]
    rintro ⟨hp, hq⟩
    exact sqCore_zero_ne_one h (hp.2.symm.trans hq.1)
  have hbad : Fintype.card {p // P p ∨ Q p} = 2 * SqCore.sqRank h := by
    rw [Fintype.card_subtype_or_disjoint P Q hdisj,
      Fintype.card_congr (sqCubicBadLeftEquiv h),
      Fintype.card_congr (sqCubicBadRightEquiv h), Fintype.card_fin]
    omega
  change Fintype.card {p // ¬(P p ∨ Q p)} = _
  rw [Fintype.card_subtype_compl, hbad]
  unfold zassenhausPBWCubicDimension
  simp only [Fintype.card_prod, Fintype.card_fin]
  congr 1 <;> ring

/-- The finite PBW normal-word spaces have dimensions `d`, `d²-1`, and `d³-2d` in the only
three degrees needed by the truncated Jennings calculation. -/
theorem sqQuadraticPBWFirstThreeDimensions (h : ℕ) :
    Module.finrank (ZMod 2) (SqQuadraticHomogeneousNormalSpace h 1) =
        SqCore.sqRank h ∧
      Module.finrank (ZMod 2) (SqQuadraticHomogeneousNormalSpace h 2) =
        SqCore.sqRank h ^ 2 - 1 ∧
      Module.finrank (ZMod 2) (SqQuadraticHomogeneousNormalSpace h 3) =
        zassenhausPBWCubicDimension (SqCore.sqRank h) := by
  constructor
  · rw [Module.finrank_finsupp_self,
      Fintype.card_congr
        (Equiv.ofBijective _ (sqQuadraticHomogeneousOneOfLetter_bijective h)).symm,
      Fintype.card_fin]
  constructor
  · rw [Module.finrank_finsupp_self,
      Fintype.card_congr
        (Equiv.ofBijective _ (sqQuadraticHomogeneousTwoOfPair_bijective h)).symm,
      card_sqQuadraticNormalPair]
  · rw [Module.finrank_finsupp_self,
      Fintype.card_congr
        (Equiv.ofBijective _ (sqQuadraticHomogeneousThreeOfTriple_bijective h)).symm,
      card_sqQuadraticNormalTriple]

/-- The current normal-word PBW development has finite homogeneous spaces but does not yet
expose these three symbolic finrank counts.  This is the exact finite combinatorial counting
package: one letter, all quadratic words except `XS`, and all cubic words except the two
disjoint placements of `XS`. -/
def SqQuadraticPBWFirstThreeDimensionSupply : Prop :=
  ∀ h : ℕ,
    Module.finrank (ZMod 2) (SqQuadraticHomogeneousNormalSpace h 1) =
        SqCore.sqRank h ∧
      Module.finrank (ZMod 2) (SqQuadraticHomogeneousNormalSpace h 2) =
        SqCore.sqRank h ^ 2 - 1 ∧
      Module.finrank (ZMod 2) (SqQuadraticHomogeneousNormalSpace h 3) =
        zassenhausPBWCubicDimension (SqCore.sqRank h)

/-- The symbolic finite normal-word count is fully discharged. -/
theorem sqQuadraticPBWFirstThreeDimensionSupply :
    SqQuadraticPBWFirstThreeDimensionSupply :=
  sqQuadraticPBWFirstThreeDimensions

/-- The coefficient-of-`t^3` truncation of the restricted PBW/Jennings product

`A(t) = ∏ (1+t^n)^ell_n  (mod t^4)`.

After inserting `ell₁=d`, the already-proved quadratic value
`ell₂=d(d+1)/2-1`, and the one-relator associative PBW value `A₃=d^3-2d`, its entire content is
the displayed finite Nat equality.  No all-degree Hilbert series is hidden in this interface. -/
def LegacyLowerTwoCentralTruncatedJenningsCrossFiltrationFormula
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) : Prop :=
  zassenhausPBWCubicDimension d =
    d.choose 3 + d * lowerTwoCentralOneRelatorQuadraticDimension d +
      lowerTwoCentralHilbertCoefficient G 2

/-- The legacy truncated Jennings cross-filtration formula isolates its claimed cubic
lower-series coefficient as the explicit Zassenhaus PBW remainder. -/
theorem lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}
    (H : LegacyLowerTwoCentralTruncatedJenningsCrossFiltrationFormula G d) :
    lowerTwoCentralHilbertCoefficient G 2 =
      zassenhausJenningsCubicPrimitiveRemainder d := by
  unfold LegacyLowerTwoCentralTruncatedJenningsCrossFiltrationFormula at H
  unfold zassenhausJenningsCubicPrimitiveRemainder
  omega

/-- The remaining elementary arithmetic normalization on the actual improved ranks.  It says
that the coefficient extracted from the finite PBW product is the familiar Labute number
`(d^3-4d)/3`.  Keeping this separate makes it impossible to confuse the Jennings theorem with
polynomial simplification. -/
def SqDegreeThreeZassenhausPrimitiveArithmetic : Prop :=
  ∀ h : ℕ,
    zassenhausJenningsCubicPrimitiveRemainder (SqCore.sqRank h) =
      zassenhausOneRelatorCubicPrimitiveDimension (SqCore.sqRank h)

/-- The finite coefficient remainder simplifies to `(d^3-4d)/3` for every actual improved
rank `d = 3 + 2h`. -/
theorem sqDegreeThreeZassenhausPrimitiveArithmetic :
    SqDegreeThreeZassenhausPrimitiveArithmetic := by
  intro h
  let d := SqCore.sqRank h
  let q := d * (d + 1) / 2
  let c := d.choose 3
  let r := (d ^ 3 - 4 * d) / 3
  have hd : d = 3 + 2 * h := rfl
  have hd3 : 3 ≤ d := by omega
  have hq2 : 2 * q = d * (d + 1) := by
    dsimp [q]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self d)
  have hc6 : 6 * c = d * (d - 1) * (d - 2) := by
    have hc := Nat.descFactorial_eq_factorial_mul_choose d 3
    calc
      6 * c = d.descFactorial 3 := by
        norm_num [c] at hc ⊢
        exact hc.symm
      _ = d * (d - 1) * (d - 2) := by
        simp [Nat.descFactorial]
        ring
  have hfactor : d ^ 3 - 4 * d = d * (d - 2) * (d + 2) := by
    rw [tsub_eq_iff_eq_add_of_le]
    · have hdsub : d - 2 + 2 = d := Nat.sub_add_cancel (by omega)
      nlinarith
    · nlinarith
  have hfactor_dvd : 3 ∣ d * (d - 2) * (d + 2) := by
    have hmod : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hmod with hmod | hmod | hmod
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hmod) (d - 2)) (d + 2)
    · have hdvd : 3 ∣ d + 2 := Nat.dvd_of_mod_eq_zero (by omega)
      exact dvd_mul_of_dvd_right hdvd (d * (d - 2))
    · have hdvd : 3 ∣ d - 2 := Nat.dvd_of_mod_eq_zero (by omega)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdvd d) (d + 2)
  have hdiv : 3 ∣ d ^ 3 - 4 * d := by
    rw [hfactor]
    exact hfactor_dvd
  have hr3 : 3 * r = d ^ 3 - 4 * d := by
    dsimp [r]
    rw [mul_comm, Nat.div_mul_cancel hdiv]
  have hqpos : 1 ≤ q := by nlinarith
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hqpos
  have hAle : 2 * d ≤ d ^ 3 := by nlinarith
  have hAsub : d ^ 3 - 2 * d + 2 * d = d ^ 3 := Nat.sub_add_cancel hAle
  have hRle : 4 * d ≤ d ^ 3 := by nlinarith
  have hRsub : d ^ 3 - 4 * d + 4 * d = d ^ 3 := Nat.sub_add_cancel hRle
  have hdsub1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hdsub2 : d - 2 + 2 = d := Nat.sub_add_cancel (by omega)
  have hsum : d ^ 3 - 2 * d = c + d * (q - 1) + r := by
    nlinarith
  change (d ^ 3 - 2 * d) - (c + d * (q - 1)) = r
  omega

/-- Model-side truncated Jennings supply, sharply limited to coefficient three.

**Filtration warning.**  The mod-two augmentation/PBW coefficient on the left is naturally a
Zassenhaus coefficient.  The `lowerTwoCentralHilbertCoefficient` on the right is currently
defined from the repository's lower exponent-two series
`lambda_(n+1) = closure(lambda_n^2 [lambda_n,G])`.  Thus this proposition is an explicit
additional compatibility assertion; it is not a consequence of the finite layer maps in
`LowerTwoCentralJenningsDegreeThree`.  Indeed
`not_sqDegreeThreeLowerTwoCentralAugmentationInjectionSupply` proves that the naive cubic
injection route is false: nonzero squares from `Z_2` die in `I^3/I^4`.  More sharply,
`modTwoFiniteDimensionSubgroup_four_ne_twoCentralSeries_sqFourthLevel` proves on every improved
model that the two filtrations have already diverged in the common finite quotient `Q_4`.

A proof of this supply therefore requires either an actual Zassenhaus tower on the group side,
or a mixed integral/2-adic augmentation filtration in which multiplication by `2` has degree
one and hence records lower-two-central squares. -/
def LegacySqDegreeThreeTruncatedJenningsCrossFiltrationSupply : Prop :=
  ∀ h : ℕ,
    LegacyLowerTwoCentralTruncatedJenningsCrossFiltrationFormula
      (SqCore.DSq h : Type) (SqCore.sqRank h)

/-- The legacy truncated cross-filtration supply computes the model's lower-series Hilbert
coefficient `2`; the independent Zassenhaus arithmetic normalization is already proved. -/
theorem dsq_lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration
    (Hj : LegacySqDegreeThreeTruncatedJenningsCrossFiltrationSupply) (h : ℕ) :
    lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) 2 =
      zassenhausOneRelatorCubicPrimitiveDimension (SqCore.sqRank h) := by
  rw [lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration (Hj h),
    sqDegreeThreeZassenhausPrimitiveArithmetic h]

/-- Consequently the legacy truncated cross-filtration supply implies the expected exact
third lower-series layer.  The conclusion is not attributed to Jennings alone. -/
theorem lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyTruncatedJennings
    (Hj : LegacySqDegreeThreeTruncatedJenningsCrossFiltrationSupply) (h : ℕ) :
    LowerTwoCentralDegreeThreeCrossFiltrationCard (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  apply lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  exact
    dsq_lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration Hj h

/-- The rank-three arithmetic normalization is already executable. -/
theorem zassenhausJenningsCubicPrimitiveRemainder_three :
    zassenhausJenningsCubicPrimitiveRemainder 3 = 5 := by
  norm_num [zassenhausJenningsCubicPrimitiveRemainder,
    zassenhausPBWCubicDimension,
    lowerTwoCentralOneRelatorQuadraticDimension,
    lowerTwoCentralQuadraticDimension]

/-! ## Deprecated compatibility aliases

These names preserve the pre-audit API.  Their replacements make the filtration explicit.
In particular, every alias whose conclusion concerns `zLayer` or
`lowerTwoCentralHilbertCoefficient` still requires the displayed legacy cross-filtration
input; none packages the Zassenhaus primitive calculation as a lower-series theorem. -/

/-- Deprecated numerical alias; this is a Zassenhaus primitive dimension. -/
@[deprecated zassenhausFreeCubicPrimitiveDimension (since := "2026-08-04")]
abbrev lowerTwoCentralFreeCubicDimension := zassenhausFreeCubicPrimitiveDimension

/-- Deprecated numerical alias; this is a Zassenhaus primitive dimension. -/
@[deprecated zassenhausOneRelatorCubicPrimitiveDimension (since := "2026-08-04")]
abbrev lowerTwoCentralOneRelatorCubicDimension :=
  zassenhausOneRelatorCubicPrimitiveDimension

/-- Deprecated cross-filtration proposition, not a consequence of Labute's Zassenhaus
formula alone. -/
@[deprecated LowerTwoCentralDegreeThreeCrossFiltrationCard (since := "2026-08-04")]
abbrev LowerTwoCentralDegreeThreeExpectedCard :=
  LowerTwoCentralDegreeThreeCrossFiltrationCard

/-- Deprecated numerical regression alias; it has no lower-series content. -/
@[deprecated zassenhausOneRelatorCubicPrimitiveDimension_three (since := "2026-08-04")]
alias lowerTwoCentralOneRelatorCubicDimension_three :=
  zassenhausOneRelatorCubicPrimitiveDimension_three

/-- Deprecated conversion alias.  Its premise is the cross-filtration equality. -/
@[deprecated lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient
  (since := "2026-08-04")]
alias lowerTwoCentralDegreeThreeExpectedCard_of_hilbertCoefficient :=
  lowerTwoCentralDegreeThreeCrossFiltrationCard_of_coefficient

/-- Deprecated name for the legacy model cross-filtration bridge. -/
@[deprecated LegacySqDegreeThreeJenningsCrossFiltrationBridge (since := "2026-08-04")]
abbrev SqDegreeThreeJenningsPrimitiveBridge :=
  LegacySqDegreeThreeJenningsCrossFiltrationBridge

/-- Deprecated theorem alias; the required bridge is a legacy cross-filtration assumption. -/
@[deprecated lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyJenningsCrossFiltration
  (since := "2026-08-04")]
alias lowerTwoCentralDegreeThreeExpectedCard_DSq_of_jenningsBridge :=
  lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyJenningsCrossFiltration

/-- Deprecated name for the universal legacy cross-filtration supply. -/
@[deprecated LegacyDemushkinDegreeThreeCrossFiltrationSupply (since := "2026-08-04")]
abbrev DemushkinDegreeThreeLabuteFormulaSupply :=
  LegacyDemushkinDegreeThreeCrossFiltrationSupply

/-- Deprecated theorem alias; the conclusion uses the legacy cross-filtration supply, not
the Zassenhaus Labute formula alone. -/
@[deprecated lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyCrossFiltration
  (since := "2026-08-04")]
alias lowerTwoCentralDegreeThreeExpectedCard_DSq_of_labute :=
  lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyCrossFiltration

/-- Deprecated theorem alias; the value `32` is conditional on the legacy cross-filtration
supply. -/
@[deprecated card_zLayer_three_dsq_zero_of_legacyCrossFiltration (since := "2026-08-04")]
alias card_zLayer_three_dsq_zero_of_labute :=
  card_zLayer_three_dsq_zero_of_legacyCrossFiltration

/-- Deprecated theorem alias; its field-layer conclusion is conditional on the legacy
cross-filtration supply. -/
@[deprecated
  maxProTwoGalK_lowerTwoCentralDegreeThreeCrossFiltrationCard_of_legacyCrossFiltration
  (since := "2026-08-04")]
alias maxProTwoGalK_lowerTwoCentralDegreeThreeExpectedCard_of_labute :=
  maxProTwoGalK_lowerTwoCentralDegreeThreeCrossFiltrationCard_of_legacyCrossFiltration

/-- Deprecated theorem alias; layer-cardinality agreement is conditional on the legacy
cross-filtration supply. -/
@[deprecated oddDegreeGalKSq_zLayer_three_cardAgreement_of_legacyCrossFiltration
  (since := "2026-08-04")]
alias oddDegreeGalKSq_zLayer_three_cardAgreement_of_labute :=
  oddDegreeGalKSq_zLayer_three_cardAgreement_of_legacyCrossFiltration

/-- Deprecated theorem alias; coefficient agreement is conditional on the legacy
cross-filtration supply. -/
@[deprecated oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_two_of_legacyCrossFiltration
  (since := "2026-08-04")]
alias oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_two_of_labute :=
  oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_two_of_legacyCrossFiltration

/-- Deprecated Zassenhaus PBW numerical alias. -/
@[deprecated zassenhausPBWCubicDimension (since := "2026-08-04")]
abbrev lowerTwoCentralPBWCubicDimension := zassenhausPBWCubicDimension

/-- Deprecated Zassenhaus primitive-remainder alias. -/
@[deprecated zassenhausJenningsCubicPrimitiveRemainder (since := "2026-08-04")]
abbrev lowerTwoCentralJenningsCubicRemainder :=
  zassenhausJenningsCubicPrimitiveRemainder

/-- Deprecated formula alias; this formula is a legacy cross-filtration assertion. -/
@[deprecated LegacyLowerTwoCentralTruncatedJenningsCrossFiltrationFormula
  (since := "2026-08-04")]
abbrev LowerTwoCentralTruncatedJenningsCoefficientFormula :=
  LegacyLowerTwoCentralTruncatedJenningsCrossFiltrationFormula

/-- Deprecated theorem alias; its premise is the legacy truncated cross-filtration formula. -/
@[deprecated lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration
  (since := "2026-08-04")]
alias lowerTwoCentralHilbertCoefficient_two_of_truncatedJennings :=
  lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration

/-- Deprecated name for the purely numerical Zassenhaus primitive arithmetic supply. -/
@[deprecated SqDegreeThreeZassenhausPrimitiveArithmetic (since := "2026-08-04")]
abbrev SqDegreeThreeJenningsArithmetic := SqDegreeThreeZassenhausPrimitiveArithmetic

/-- Deprecated theorem alias for purely numerical Zassenhaus primitive arithmetic. -/
@[deprecated sqDegreeThreeZassenhausPrimitiveArithmetic (since := "2026-08-04")]
alias sqDegreeThreeJenningsArithmetic := sqDegreeThreeZassenhausPrimitiveArithmetic

/-- Deprecated supply alias; it is explicitly a legacy cross-filtration assertion. -/
@[deprecated LegacySqDegreeThreeTruncatedJenningsCrossFiltrationSupply
  (since := "2026-08-04")]
abbrev SqDegreeThreeTruncatedJenningsSupply :=
  LegacySqDegreeThreeTruncatedJenningsCrossFiltrationSupply

/-- Deprecated theorem alias; its premise is the legacy truncated cross-filtration supply. -/
@[deprecated dsq_lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration
  (since := "2026-08-04")]
alias dsq_lowerTwoCentralHilbertCoefficient_two_of_truncatedJennings :=
  dsq_lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration

/-- Deprecated theorem alias; its exact layer conclusion is conditional on the legacy
truncated cross-filtration supply. -/
@[deprecated lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyTruncatedJennings
  (since := "2026-08-04")]
alias lowerTwoCentralDegreeThreeExpectedCard_DSq_of_truncatedJennings :=
  lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyTruncatedJennings

/-- Deprecated numerical Zassenhaus primitive regression alias. -/
@[deprecated zassenhausJenningsCubicPrimitiveRemainder_three (since := "2026-08-04")]
alias lowerTwoCentralJenningsCubicRemainder_three :=
  zassenhausJenningsCubicPrimitiveRemainder_three

#print axioms dsqCoordinateHOne_bijective
#print axioms obsH2_DSq_coordinateCup
#print axioms isDemushkin_DSq
#print axioms sqCubicRelatorBracketMap_injective
#print axioms finrank_sqCubicRelatorBracketSpace
#print axioms sqCompletedCubicMagnusPBWKernelIdentity
#print axioms sqDegreeThreeZassenhausPrimitiveSupply
#print axioms lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyJenningsCrossFiltration
#print axioms lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyCrossFiltration
#print axioms card_zLayer_three_dsq_zero_of_legacyCrossFiltration
#print axioms maxProTwoGalK_lowerTwoCentralDegreeThreeCrossFiltrationCard_of_legacyCrossFiltration
#print axioms oddDegreeGalKSq_zLayer_three_cardAgreement_of_legacyCrossFiltration
#print axioms sqQuadraticPBWFirstThreeDimensionSupply
#print axioms lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration
#print axioms sqDegreeThreeZassenhausPrimitiveArithmetic
#print axioms dsq_lowerTwoCentralHilbertCoefficient_two_of_legacyTruncatedJenningsCrossFiltration
#print axioms lowerTwoCentralDegreeThreeCrossFiltrationCard_DSq_of_legacyTruncatedJennings
#print axioms zassenhausJenningsCubicPrimitiveRemainder_three

end

end GQ2.Dyadic.LSquare
