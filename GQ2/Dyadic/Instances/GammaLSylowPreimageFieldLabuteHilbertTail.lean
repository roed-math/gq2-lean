/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteElementaryH2
import GQ2.Dyadic.FinitelyGeneratedK

/-!
# The higher lower-two-central Hilbert tail

This file isolates the exact all-degree input left after the generator-rank and quadratic-layer
calculations.  It does not assert a numerical Labute formula.  Instead it proves that the
remaining Hilbert-coefficient statement is precisely equality of the graded-layer orders in
depths at least three, and supplies an adapter through which a future explicit dimension formula
can discharge both sides at once.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute

variable {h : ℕ}

/-- Equality of the lower-two-central graded-layer orders from depth `3` onward.  Depths `1`
and `2` are deliberately excluded: they are controlled by generator rank and the quadratic
`H²` calculation, respectively. -/
def SqTwoCentralGradedTailCardAgreement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    Nat.card (zLayer (SqCore.DSq h : Type) k) = Nat.card (zLayer G k)

/-- **Exact higher-tail boundary.**  Equality of Hilbert coefficients in degrees at least `2`
is equivalent to equality of the corresponding elementary-abelian layer orders in depths at
least `3`. -/
theorem sqTwoCentralHilbertTailAgreement_iff_gradedTailCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hGfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    SqTwoCentralHilbertTailAgreement G h ↔
      SqTwoCentralGradedTailCardAgreement G h := by
  constructor
  · intro hcoeff k hk
    cases k with
    | zero => omega
    | succ n =>
        rw [card_zLayer_succ_eq_two_pow_hilbertCoefficient
              (G := (SqCore.DSq h : Type)) (dsqFinsetTopGen h) (SqCore.isProP_DSq h),
          card_zLayer_succ_eq_two_pow_hilbertCoefficient hGfg hpro,
          hcoeff n (by omega)]
  · intro hlayer n hn
    unfold lowerTwoCentralHilbertCoefficient
    exact congrArg (padicValNat 2) (hlayer (n + 1) (by omega))

/-- A specified numerical function computes the higher lower-two-central Hilbert coefficients
of `G`.  The function is an explicit input to this predicate; no formula is postulated here. -/
def LowerTwoCentralHilbertTailFormula
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (dimensions : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → lowerTwoCentralHilbertCoefficient G n = dimensions n

/-- A common explicit dimension formula for the model and arithmetic groups supplies the
entire remaining Hilbert tail. -/
theorem SqTwoCentralHilbertTailAgreement.of_commonFormula
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (dimensions : ℕ → ℕ)
    (hmodel : LowerTwoCentralHilbertTailFormula (SqCore.DSq h : Type) dimensions)
    (hgroup : LowerTwoCentralHilbertTailFormula G dimensions) :
    SqTwoCentralHilbertTailAgreement G h := by
  intro n hn
  exact (hmodel n hn).trans (hgroup n hn).symm

/-- The common-formula adapter is logically exact.  The forward direction chooses the model
Hilbert function itself; applications should instead provide a genuinely explicit function. -/
theorem sqTwoCentralHilbertTailAgreement_iff_exists_commonFormula
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    SqTwoCentralHilbertTailAgreement G h ↔
      ∃ dimensions : ℕ → ℕ,
        LowerTwoCentralHilbertTailFormula (SqCore.DSq h : Type) dimensions ∧
          LowerTwoCentralHilbertTailFormula G dimensions := by
  constructor
  · intro htail
    refine ⟨fun n ↦ lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) n,
      ?_, ?_⟩
    · intro n hn
      rfl
    · intro n hn
      exact (htail n hn).symm
  · rintro ⟨dimensions, hmodel, hgroup⟩
    exact SqTwoCentralHilbertTailAgreement.of_commonFormula dimensions hmodel hgroup

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Finite generation and premise-free low-degree field supplies -/

/-- The maximal pro-`2` quotient of the absolute Galois group of a finite dyadic field is
topologically finitely generated.  This is the existing profinite Nielsen--Schreier theorem for
`G_K`, pushed through the canonical maximal-pro-`2` quotient map. -/
theorem maxProTwoGalK_isTopologicallyFinGen
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)) :=
  IsTopologicallyFinGen.of_surjective
    (maxProPMk 2 (GalK K)).toMonoidHom
    (maxProPMk 2 (GalK K)).continuous_toFun
    (quotientMk_surjective _)
    (absGalK_isTopologicallyFinitelyGenerated K)

/-- Premise-free specialization of the elementary Frattini-quotient `H²` count to a finite
dyadic field. -/
theorem maxProTwoGalK_lowerTwoCentralElementaryH2CardFormula_finiteDyadic
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    LowerTwoCentralElementaryH2CardFormula (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) :=
  maxProTwoGalK_lowerTwoCentralElementaryH2CardFormula H K
    (maxProTwoGalK_isTopologicallyFinGen K)

/-- The kernel-duality route to the arithmetic five-term formula no longer needs an explicit
finite-generation premise. -/
theorem maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteDyadic
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hdual : LowerTwoCentralFiveTermKernelDuality
      (maxProPQuotient 2 (GalK K))) :
    let Q := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    LowerTwoCentralFiveTermCardFormula Q :=
  maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary
    H K (maxProTwoGalK_isTopologicallyFinGen K) hdual

/-- Exact five-term cardinality for every finite dyadic field, with topological finite
generation discharged internally. -/
theorem maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    let Q := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    LowerTwoCentralFiveTermCardFormula Q :=
  maxProTwoGalK_lowerTwoCentralFiveTermCardFormula K
    (maxProTwoGalK_isTopologicallyFinGen K)

/-- Exact arithmetic quadratic-layer cardinality for every finite dyadic field, with no
explicit finite-generation premise. -/
theorem maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    LowerTwoCentralDegreeTwoExpectedCard (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) :=
  maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard K
    (maxProTwoGalK_isTopologicallyFinGen K)

/-- Premise-free degree-zero Hilbert coefficient formula for the arithmetic group. -/
theorem maxProTwoGalK_lowerTwoCentralHilbertCoefficient_zero_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 0 =
      Module.finrank ℚ_[2] K + 2 :=
  maxProTwoGalK_lowerTwoCentralHilbertCoefficient_zero K
    (maxProTwoGalK_isTopologicallyFinGen K)

/-- Premise-free comparison of the quadratic layer in the degree-one field case. -/
theorem degreeOneGalKSq_zLayer_two_cardAgreement_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hone : Module.finrank ℚ_[2] K = 1) :
    Nat.card (zLayer (SqCore.DSq 0 : Type) 2) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 2) :=
  degreeOneGalKSq_zLayer_two_cardAgreement K hone
    (maxProTwoGalK_isTopologicallyFinGen K)

/-- Premise-free quadratic-layer comparison for every odd-degree finite dyadic field. -/
theorem oddDegreeGalKSq_zLayer_two_cardAgreement_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nat.card (zLayer
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 2) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 2) :=
  oddDegreeGalKSq_zLayer_two_cardAgreement_of_expectedCards K hodd
    (sqLowerTwoCentralDegreeTwoExpectedCardSupply
      ((Module.finrank ℚ_[2] K - 1) / 2))
    (maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_finiteDyadic K)

/-- Hilbert-coefficient spelling of the premise-free odd-degree quadratic comparison. -/
theorem oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_one_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    lowerTwoCentralHilbertCoefficient
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 1 =
      lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 1 :=
  congrArg (padicValNat 2)
    (oddDegreeGalKSq_zLayer_two_cardAgreement_finiteDyadic K hodd)

/-- For odd-degree fields, the improved model and arithmetic group agree through the quadratic
layer without any finite-generation or low-degree supply premise. -/
theorem oddDegreeGalKSq_firstThreeLayerCardAgreement_finiteDyadic
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    ∀ k < 3,
      Nat.card (zLayer
          (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) k) =
        Nat.card (zLayer (maxProPQuotient 2 (GalK K)) k) := by
  intro k hk
  by_cases hk' : k < 2
  · exact oddDegreeGalKSq_firstTwoLayerCardAgreement K hodd
      (maxProTwoGalK_isTopologicallyFinGen K) k hk'
  · have hk2 : k = 2 := by omega
    subst k
    exact oddDegreeGalKSq_zLayer_two_cardAgreement_finiteDyadic K hodd

/-- Once the already-proved rank and quadratic-layer inputs are fixed, the higher Hilbert tail
is not merely sufficient for the reverse finite-quotient family: it is equivalent to it. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_hilbertTail_of_modelDegreeTwo
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2)
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq h : Type) (SqCore.sqRank h)) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h ↔
      SqTwoCentralHilbertTailAgreement (maxProPQuotient 2 (GalK K)) h := by
  let Q := maxProPQuotient 2 (GalK K)
  have hfg : IsTopologicallyFinGen Q :=
    IsTopologicallyFinGen.of_surjective
      (D.forward isProP_maxProPQuotient).toMonoidHom
      (D.forward isProP_maxProPQuotient).continuous_toFun
      (D.forward_surjective isProP_maxProPQuotient) (dsqFinsetTopGen h)
  constructor
  · intro hreverse
    have hlayer : SqTwoCentralLayerCardAgreement Q h :=
      (D.reverseFiniteQuotientSurjections_iff_layerCardAgreement
        isProP_maxProPQuotient).mp hreverse
    have hseries : SqTwoCentralHilbertSeriesAgreement Q h :=
      (twoCentralHilbertSeriesAgreement_iff_layerCardAgreement hfg
        isProP_maxProPQuotient).mpr hlayer
    exact fun n _ ↦ hseries n
  · exact D.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_hilbertTail
      K hrank hmodel

/-- With the global model degree-two supply discharged, coefficient agreement from degree `2`
onward is the sole remaining reverse-side input. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_hilbertTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h ↔
      SqTwoCentralHilbertTailAgreement (maxProPQuotient 2 (GalK K)) h :=
  D.reverseFiniteQuotientSurjections_iff_hilbertTail_of_modelDegreeTwo K hrank
    (sqLowerTwoCentralDegreeTwoExpectedCardSupply h)

/-- Direct consumer form of `reverseFiniteQuotientSurjections_iff_hilbertTail`. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_hilbertTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2)
    (htail : SqTwoCentralHilbertTailAgreement
      (maxProPQuotient 2 (GalK K)) h) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h :=
  (D.reverseFiniteQuotientSurjections_iff_hilbertTail K hrank).mpr htail

/-- **Sharp remaining theorem.**  Under the completed low-degree supplies, the old reverse
finite-quotient family is exactly equality of the depth-`≥ 3` graded-layer orders. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_gradedTail_of_modelDegreeTwo
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2)
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq h : Type) (SqCore.sqRank h)) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h ↔
      SqTwoCentralGradedTailCardAgreement
        (maxProPQuotient 2 (GalK K)) h := by
  let Q := maxProPQuotient 2 (GalK K)
  have hfg : IsTopologicallyFinGen Q :=
    IsTopologicallyFinGen.of_surjective
      (D.forward isProP_maxProPQuotient).toMonoidHom
      (D.forward isProP_maxProPQuotient).continuous_toFun
      (D.forward_surjective isProP_maxProPQuotient) (dsqFinsetTopGen h)
  exact (D.reverseFiniteQuotientSurjections_iff_hilbertTail_of_modelDegreeTwo
      K hrank hmodel).trans
    (sqTwoCentralHilbertTailAgreement_iff_gradedTailCardAgreement
      hfg isProP_maxProPQuotient)

/-- Model-degree-two-free form of the sharp remaining theorem.  Apart from the unchanged
forward data and rank match, the only input is equality of graded-layer orders in depths
`k ≥ 3`. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_gradedTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h ↔
      SqTwoCentralGradedTailCardAgreement
        (maxProPQuotient 2 (GalK K)) h :=
  D.reverseFiniteQuotientSurjections_iff_gradedTail_of_modelDegreeTwo K hrank
    (sqLowerTwoCentralDegreeTwoExpectedCardSupply h)

/-- Odd-degree form of the sharp remaining theorem.  Here the improved model rank
`3 + 2 * (([K : ℚ₂] - 1) / 2)` simplifies to `[K : ℚ₂] + 2`, so no separate rank
hypothesis remains. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_iff_gradedTail_of_modelDegreeTwo
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2))) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K))
        ((Module.finrank ℚ_[2] K - 1) / 2) ↔
      SqTwoCentralGradedTailCardAgreement (maxProPQuotient 2 (GalK K))
        ((Module.finrank ℚ_[2] K - 1) / 2) := by
  apply D.reverseFiniteQuotientSurjections_iff_gradedTail_of_modelDegreeTwo K
  obtain ⟨m, hm⟩ := hodd
  rw [hm]
  simp only [SqCore.sqRank]
  omega
  exact hmodel

/-- **Odd-degree exact endpoint.**  The completed model degree-two calculation removes the
last low-degree premise: the reverse finite-quotient family is equivalent solely to equality
of the depth-`≥ 3` graded-layer orders. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_iff_gradedTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K))) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K))
        ((Module.finrank ℚ_[2] K - 1) / 2) ↔
      SqTwoCentralGradedTailCardAgreement (maxProPQuotient 2 (GalK K))
        ((Module.finrank ℚ_[2] K - 1) / 2) :=
  D.reverseFiniteQuotientSurjections_oddDegree_iff_gradedTail_of_modelDegreeTwo
    K hodd (sqLowerTwoCentralDegreeTwoExpectedCardSupply
      ((Module.finrank ℚ_[2] K - 1) / 2))

/-- Hilbert-coefficient spelling of the odd-degree exact endpoint. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_iff_hilbertTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K))) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K))
        ((Module.finrank ℚ_[2] K - 1) / 2) ↔
      SqTwoCentralHilbertTailAgreement (maxProPQuotient 2 (GalK K))
        ((Module.finrank ℚ_[2] K - 1) / 2) := by
  apply D.reverseFiniteQuotientSurjections_iff_hilbertTail K
  obtain ⟨m, hm⟩ := hodd
  rw [hm]
  simp only [SqCore.sqRank]
  omega

/-- Field-facing consumer for a future explicit graded-Lie dimension calculation. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_commonHilbertTailFormula
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2)
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq h : Type) (SqCore.sqRank h))
    (dimensions : ℕ → ℕ)
    (hmodelTail : LowerTwoCentralHilbertTailFormula
      (SqCore.DSq h : Type) dimensions)
    (hfieldTail : LowerTwoCentralHilbertTailFormula
      (maxProPQuotient 2 (GalK K)) dimensions) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h :=
  D.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_hilbertTail K hrank hmodel
    (SqTwoCentralHilbertTailAgreement.of_commonFormula dimensions hmodelTail hfieldTail)

/-- Model-degree-two-free consumer for a future explicit graded-Lie dimension calculation. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_commonHilbertTailFormula
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2)
    (dimensions : ℕ → ℕ)
    (hmodelTail : LowerTwoCentralHilbertTailFormula
      (SqCore.DSq h : Type) dimensions)
    (hfieldTail : LowerTwoCentralHilbertTailFormula
      (maxProPQuotient 2 (GalK K)) dimensions) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h :=
  D.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_commonHilbertTailFormula
    K hrank (sqLowerTwoCentralDegreeTwoExpectedCardSupply h) dimensions
      hmodelTail hfieldTail

#print axioms sqTwoCentralHilbertTailAgreement_iff_gradedTailCardAgreement
#print axioms SqTwoCentralHilbertTailAgreement.of_commonFormula
#print axioms sqTwoCentralHilbertTailAgreement_iff_exists_commonFormula
#print axioms maxProTwoGalK_isTopologicallyFinGen
#print axioms maxProTwoGalK_lowerTwoCentralElementaryH2CardFormula_finiteDyadic
#print axioms maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteDyadic
#print axioms maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_finiteDyadic
#print axioms maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_finiteDyadic
#print axioms maxProTwoGalK_lowerTwoCentralHilbertCoefficient_zero_finiteDyadic
#print axioms degreeOneGalKSq_zLayer_two_cardAgreement_finiteDyadic
#print axioms oddDegreeGalKSq_zLayer_two_cardAgreement_finiteDyadic
#print axioms oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_one_finiteDyadic
#print axioms oddDegreeGalKSq_firstThreeLayerCardAgreement_finiteDyadic
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_hilbertTail_of_modelDegreeTwo
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_hilbertTail
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_hilbertTail
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_gradedTail_of_modelDegreeTwo
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_gradedTail
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_iff_gradedTail_of_modelDegreeTwo
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_iff_gradedTail
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_iff_hilbertTail
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_commonHilbertTailFormula
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_commonHilbertTailFormula

end

end GQ2.Dyadic.LSquare
