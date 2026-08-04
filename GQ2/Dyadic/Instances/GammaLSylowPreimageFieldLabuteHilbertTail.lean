/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteElementaryH2

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
