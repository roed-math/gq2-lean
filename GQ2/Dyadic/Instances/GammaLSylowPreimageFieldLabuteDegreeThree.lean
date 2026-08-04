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
def lowerTwoCentralFreeCubicDimension (d : ℕ) : ℕ :=
  (d ^ 3 - d) / 3

/-- The degree-three dimension after quotienting by one nondegenerate quadratic relator.
The degree-three part of the relator ideal has rank `d`, so this is
`((d^3-d)/3)-d = (d^3-4d)/3`.  The latter integral form is convenient for cardinal
statements. -/
def lowerTwoCentralOneRelatorCubicDimension (d : ℕ) : ℕ :=
  (d ^ 3 - 4 * d) / 3

/-- Cardinal form of the first higher Labute coefficient for a rank-`d` group. -/
def LowerTwoCentralDegreeThreeExpectedCard
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) : Prop :=
  Nat.card (zLayer G 3) = 2 ^ lowerTwoCentralOneRelatorCubicDimension d

/-- The rank-three regression is the first higher value: the cubic coefficient is `5`. -/
theorem lowerTwoCentralOneRelatorCubicDimension_three :
    lowerTwoCentralOneRelatorCubicDimension 3 = 5 := by
  norm_num [lowerTwoCentralOneRelatorCubicDimension]

/-- A coefficient calculation at Hilbert index `2` is exactly the desired cardinality of
`Z₃ = λ₃/λ₄`. -/
theorem lowerTwoCentralDegreeThreeExpectedCard_of_hilbertCoefficient
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) {d : ℕ}
    (hcubic : lowerTwoCentralHilbertCoefficient G 2 =
      lowerTwoCentralOneRelatorCubicDimension d) :
    LowerTwoCentralDegreeThreeExpectedCard G d := by
  unfold LowerTwoCentralDegreeThreeExpectedCard
  change Nat.card (zLayer G (2 + 1)) =
    2 ^ lowerTwoCentralOneRelatorCubicDimension d
  rw [card_zLayer_succ_eq_two_pow_hilbertCoefficient hfg hpro, hcubic]

/-- The model-specific missing primitive bridge.  The completed augmentation calculation
already proves its premise unconditionally; the missing content is the Jennings--Lazard
identification of its cubic PBW quotient with the primitive lower-two-central layer. -/
def SqDegreeThreeJenningsPrimitiveBridge : Prop :=
  ∀ h : ℕ, SqCompletedMonomialPBWKernelIdentity h 3 →
    lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) 2 =
      lowerTwoCentralOneRelatorCubicDimension (SqCore.sqRank h)

/-- The finite-operator campaign has already discharged the completed cubic Magnus/PBW
premise appearing in the preceding bridge. -/
theorem sqCompletedCubicMagnusPBWKernelIdentity (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 3 :=
  sqCompletedMonomialPBWKernelIdentity_three h

/-- Thus a Jennings primitive bridge immediately computes the model's third layer. -/
theorem lowerTwoCentralDegreeThreeExpectedCard_DSq_of_jenningsBridge
    (H : SqDegreeThreeJenningsPrimitiveBridge) (h : ℕ) :
    LowerTwoCentralDegreeThreeExpectedCard (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  apply lowerTwoCentralDegreeThreeExpectedCard_of_hilbertCoefficient
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  exact H h (sqCompletedCubicMagnusPBWKernelIdentity h)

/-- **The narrow universal degree-three theorem still absent from the library.**  For every
finitely generated Demushkin pro-`2` group, the degree-three part of the initial quadratic
relation ideal has rank equal to the degree-one rank.  Equivalently, Hilbert coefficient `2`
is `(d^3-4d)/3`.  This single proposition packages the degree-three Labute relation-space
calculation together with the generic Jennings primitive identification. -/
def DemushkinDegreeThreeLabuteFormulaSupply : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)],
    IsTopologicallyFinGen G → IsDemushkin 2 G →
      lowerTwoCentralHilbertCoefficient G 2 =
        lowerTwoCentralOneRelatorCubicDimension (demushkinRank 2 G)

/-- The universal degree-three Labute formula specializes to every improved square model,
because the constructor-table calculation above proves that model is Demushkin. -/
theorem lowerTwoCentralDegreeThreeExpectedCard_DSq_of_labute
    (H : DemushkinDegreeThreeLabuteFormulaSupply) (h : ℕ) :
    LowerTwoCentralDegreeThreeExpectedCard (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  apply lowerTwoCentralDegreeThreeExpectedCard_of_hilbertCoefficient
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  rw [← demushkinRank_DSq h]
  exact H (SqCore.DSq h : Type) (dsqFinsetTopGen h) (isDemushkin_DSq h)

/-- Rank-three model regression: the universal Labute formula gives
`|λ₃(DSq 0)/λ₄(DSq 0)| = 2^5 = 32`. -/
theorem card_zLayer_three_dsq_zero_of_labute
    (H : DemushkinDegreeThreeLabuteFormulaSupply) :
    Nat.card (zLayer (SqCore.DSq 0 : Type) 3) = 32 := by
  have hcard := lowerTwoCentralDegreeThreeExpectedCard_DSq_of_labute H 0
  unfold LowerTwoCentralDegreeThreeExpectedCard at hcard
  rw [SqCore.sqRank, lowerTwoCentralOneRelatorCubicDimension_three] at hcard
  norm_num at hcard ⊢
  exact hcard

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The same universal theorem gives the exact third lower-two-central layer of every finite
dyadic field group. -/
theorem maxProTwoGalK_lowerTwoCentralDegreeThreeExpectedCard_of_labute
    (H : DemushkinDegreeThreeLabuteFormulaSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    LowerTwoCentralDegreeThreeExpectedCard (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralDegreeThreeExpectedCard_of_hilbertCoefficient hfg
    isProP_maxProPQuotient
  have hcubic := H Q hfg (isDemushkin_maxProTwoGalK (K := K))
  rwa [demushkinRank_maxProTwoGalK (K := K)] at hcubic

/-- At the first unresolved higher layer `k = 3`, the improved odd-degree model and the
arithmetic group have equal order as soon as the universal degree-three Labute formula is
available. -/
theorem oddDegreeGalKSq_zLayer_three_cardAgreement_of_labute
    (H : DemushkinDegreeThreeLabuteFormulaSupply)
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
  have hmodel := lowerTwoCentralDegreeThreeExpectedCard_DSq_of_labute H h
  have hfield := maxProTwoGalK_lowerTwoCentralDegreeThreeExpectedCard_of_labute H K hfg
  unfold LowerTwoCentralDegreeThreeExpectedCard at hmodel hfield
  rw [hmodel, hfield, hrank]

/-- Equivalently, Hilbert coefficient `2` agrees for every odd-degree field. -/
theorem oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_two_of_labute
    (H : DemushkinDegreeThreeLabuteFormulaSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    lowerTwoCentralHilbertCoefficient
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 2 =
      lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 2 := by
  exact congrArg (padicValNat 2)
    (oddDegreeGalKSq_zLayer_three_cardAgreement_of_labute H K hodd hfg)

#print axioms dsqCoordinateHOne_bijective
#print axioms obsH2_DSq_coordinateCup
#print axioms isDemushkin_DSq
#print axioms sqCompletedCubicMagnusPBWKernelIdentity
#print axioms lowerTwoCentralDegreeThreeExpectedCard_DSq_of_jenningsBridge
#print axioms lowerTwoCentralDegreeThreeExpectedCard_DSq_of_labute
#print axioms card_zLayer_three_dsq_zero_of_labute
#print axioms maxProTwoGalK_lowerTwoCentralDegreeThreeExpectedCard_of_labute
#print axioms oddDegreeGalKSq_zLayer_three_cardAgreement_of_labute

end

end GQ2.Dyadic.LSquare
