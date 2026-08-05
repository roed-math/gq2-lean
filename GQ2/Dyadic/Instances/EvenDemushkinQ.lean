/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.ProTwoCompletionDecomposition
import GQ2.Foundations.Axioms

/-!
# Parity-free ramified-`i` Demushkin `q = 2`

The odd-degree route to `demushkinQ (G_K(2)) = 2` detects the class of `-1` through the
cyclotomic character, using `N_{K/ℚ₂}(-1) = (-1)^[K:ℚ₂]`.  That step is genuinely false at
even degree.  This file replaces it by an argument that never mentions the degree.

The source-side statement `proPCompletionMk 2 K× (-1) ≠ 1` is a theorem of the unit
filtration alone.  Indeed `-1` is a depth-one principal unit (`‖-2‖ = ‖π‖^e ≤ ‖π‖`), the
canonical map `U¹ → (U¹)^(2)` is bijective (`DepthPower`), and the two completion
equivalences `(U¹)^(2) ≃ (O_K×)^(2)` and `(K×)^(2) ≃ (O_K×)^(2) × ℤ₂` carry the class of
`-1` across unchanged.  Since `-1 ≠ 1` in `U¹`, its completion class is nontrivial.

Combined with the classification of `2`-primary roots of unity under ramification of
`K(i)/K`, this gives injectivity of `TwoPowerRoots K → (K×)^(2)` with no parity hypothesis;
transporting along an injective completed reciprocity map and pairing with the
unconditional source-torsion theorem yields `q = 2`.
-/

namespace GQ2.Dyadic.EvenDemushkinQ

noncomputable section

open GQ2 GQ2.SectionThree

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-! ## `-1` is a nontrivial depth-one principal unit -/

omit [FiniteDimensional ℚ_[2] K] in
/-- In a dyadic field `‖-2‖ = ‖π‖^e ≤ ‖π‖`, so `-1` lies in the depth-one unit group `U¹`. -/
theorem negOne_mem_depthUnits_one (FF : DyadicUnitFiltration K) :
    (-1 : (↥K)ˣ) ∈ depthUnits K FF.π 1 := by
  have hval : ((((-1 : (↥K)ˣ) : ↥K) : ℚ̄₂)) = -1 := by push_cast; ring
  rw [mem_depthUnits, hval]
  refine ⟨by rw [norm_neg, norm_one], ?_⟩
  rw [show (-1 : ℚ̄₂) - 1 = -(2 : ℚ̄₂) by ring, norm_neg, FF.he]
  exact pow_le_pow_of_le_one (norm_nonneg _) FF.hπ_lt.le FF.he_pos

omit [FiniteDimensional ℚ_[2] K] in
/-- `-1`, packaged as an element of the depth-one unit group. -/
def negOneDepthUnit (FF : DyadicUnitFiltration K) : ↥(depthUnits K FF.π 1) :=
  ⟨-1, negOne_mem_depthUnits_one FF⟩

omit [FiniteDimensional ℚ_[2] K] in
/-- `-1` is not the identity of `U¹`, because `K` has characteristic zero. -/
theorem negOneDepthUnit_ne_one (FF : DyadicUnitFiltration K) :
    negOneDepthUnit FF ≠ 1 := by
  intro h
  have hK : (-1 : ↥K) = 1 := congrArg (fun u : (↥K)ˣ ↦ (u : ↥K)) (congrArg Subtype.val h)
  exact (by norm_num : (-1 : ↥K) ≠ 1) hK

/-! ## `-1` survives in the pro-2 completion of `K×` -/

/-- `-1`, packaged as a 2-primary root of unity in `K`. -/
def negOneRoot (K : IntermediateField ℚ_[2] ℚ̄₂) : TwoPowerRoots K :=
  ⟨-1, 1, by norm_num⟩

omit [FiniteDimensional ℚ_[2] K] in
@[simp] theorem twoPowerRootUnit_negOneRoot :
    twoPowerRootUnit (negOneRoot K) = (-1 : (↥K)ˣ) := Units.ext rfl

/-- The class of `-1` in the completed depth-one unit group is nontrivial: `U¹ → (U¹)^(2)`
is injective by residual 2-finiteness. -/
theorem proTwoCompletionMk_negOneDepthUnit_ne_one (FF : DyadicUnitFiltration K) :
    proPCompletionMk 2 ↥(depthUnits K FF.π 1) (negOneDepthUnit FF) ≠ 1 := by
  intro h
  exact negOneDepthUnit_ne_one FF
    ((injective_iff_map_eq_one (proPCompletionMk 2 ↥(depthUnits K FF.π 1))).mp
      (proTwoCompletionMk_depthUnits_bijective FF (le_refl 1)).1 _ h)

/-- The class of `-1` in the completed norm-unit group is nontrivial: the odd-index bridge
`(U¹)^(2) ≃ (O_K×)^(2)` is an equivalence. -/
theorem proTwoCompletionMk_twoPowerRootNormUnit_negOneRoot_ne_one :
    proPCompletionMk 2 ↥(normUnits K) (twoPowerRootNormUnit (negOneRoot K)) ≠ 1 := by
  intro h
  refine proTwoCompletionMk_negOneDepthUnit_ne_one (dyadicUnitFiltration K) ?_
  apply (proTwoCompletionDepthOneEquivNormUnits (dyadicUnitFiltration K)).injective
  rw [map_one, proTwoCompletionDepthOneEquivNormUnits_mk]
  refine Eq.trans (congrArg (proPCompletionMk 2 ↥(normUnits K)) ?_) h
  exact Subtype.ext (Units.ext rfl)

/-- **The parity-free source-side separation.**  The class of `-1` is nontrivial in the
abstract pro-2 completion of `K×`.  No degree hypothesis and no cyclotomic character are
involved: `-1` is a nontrivial principal unit, and the principal units inject into the
completion. -/
theorem proTwoCompletionMk_neg_one_ne_one :
    proPCompletionMk 2 ((↥K)ˣ) (-1 : (↥K)ˣ) ≠ 1 := by
  intro h
  refine proTwoCompletionMk_twoPowerRootNormUnit_negOneRoot_ne_one (K := K) ?_
  have hmap := congrArg (fun z ↦ (proTwoCompletionUnitsEquiv (K := K) z).1)
    (Eq.trans (congrArg (proPCompletionMk 2 ((↥K)ˣ)) (twoPowerRootUnit_negOneRoot (K := K))) h)
  simpa only [proTwoCompletionUnitsEquiv_mk, normalizedUnit_twoPowerRootUnit, map_one,
    Prod.fst_one] using hmap

/-! ## Parity-free injectivity of the root-to-torsion maps -/

/-- **Parity-free source injectivity.**  Under ramification of `K(i)/K` the two 2-primary
roots `±1` stay distinct in the pro-2 completion of `K×`. -/
theorem twoPowerRootToProTwoCompletionTorsion_injective_of_ramifiedI
    (RI : RamifiedIData K) :
    Function.Injective (twoPowerRootToProTwoCompletionTorsion (K := K)) := by
  intro x y hxy
  have hval : proPCompletionMk 2 ((↥K)ˣ) (twoPowerRootUnit x) =
      proPCompletionMk 2 ((↥K)ˣ) (twoPowerRootUnit y) := congrArg Subtype.val hxy
  apply Subtype.ext
  rcases twoPowerRoot_eq_one_or_neg_one_of_ramifiedI RI.sq_deltaI RI.ramified
      x x.2.choose x.2.choose_spec with hx | hx <;>
    rcases twoPowerRoot_eq_one_or_neg_one_of_ramifiedI RI.sq_deltaI RI.ramified
      y y.2.choose y.2.choose_spec with hy | hy
  · exact hx.trans hy.symm
  · refine absurd ?_ (proTwoCompletionMk_neg_one_ne_one (K := K))
    rw [← show twoPowerRootUnit y = (-1 : (↥K)ˣ) from Units.ext hy, ← hval,
      show twoPowerRootUnit x = (1 : (↥K)ˣ) from Units.ext hx, map_one]
  · refine absurd ?_ (proTwoCompletionMk_neg_one_ne_one (K := K))
    rw [← show twoPowerRootUnit x = (-1 : (↥K)ˣ) from Units.ext hx, hval,
      show twoPowerRootUnit y = (1 : (↥K)ˣ) from Units.ext hy, map_one]
  · exact hx.trans hy.symm

variable [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **Parity-free target injectivity.**  Composing source injectivity with an injective
completed reciprocity map separates `±1` inside the torsion of `G_K(2)^ab`. -/
theorem twoPowerRootToMaxProTwoAbTorsion_injective_of_ramifiedI
    (B : MarkedRecip R K) (RI : RamifiedIData K)
    (hrecip : Function.Injective (proTwoReciprocityToTopAb B)) :
    Function.Injective (twoPowerRootToMaxProTwoAbTorsion B) := by
  intro x y hxy
  refine twoPowerRootToProTwoCompletionTorsion_injective_of_ramifiedI RI
    (Subtype.ext (hrecip ?_))
  exact congrArg Subtype.val hxy

/-! ## The parity-free field theorem -/

/-- **Parity-free ramified-`i` `q = 2`.**  For every finite-dimensional dyadic field `K` with
`K(i)/K` ramified, injectivity of completed reciprocity gives `demushkinQ (G_K(2)) = 2`.
The degree of `K/ℚ₂` is unconstrained. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_ramifiedI
    (B : MarkedRecip R K) (RI : RamifiedIData K)
    (hrecip : Function.Injective (proTwoReciprocityToTopAb B)) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 := by
  rw [demushkinQ]
  let e : TwoPowerRoots K ≃ MaxProTwoAbTorsion K :=
    Equiv.ofBijective (twoPowerRootToMaxProTwoAbTorsion B)
      ⟨twoPowerRootToMaxProTwoAbTorsion_injective_of_ramifiedI B RI hrecip,
        maxProTwoAbTorsionGeneratedByFieldRoots_of_completion B hrecip
          (proTwoCompletionTorsionGeneratedByFieldRoots (K := K))⟩
  rw [← Nat.card_congr e]
  exact natCard_twoPowerRoots_of_ramifiedI RI.sq_deltaI RI.ramified

end

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **Parity-free canonical adapter.**  The exact analogue of the odd-degree wrapper
`GQ2.Dyadic.LSquare.demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective`,
with the ramified-`i` datum supplied explicitly instead of derived from oddness. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_ramifiedI_completedReciprocityInjective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (RI : RamifiedIData K)
    (hrecip : Function.Injective
      (proTwoReciprocityToTopAb (markedRecipAt K))) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_ramifiedI (markedRecipAt K) RI hrecip

#print axioms negOne_mem_depthUnits_one
#print axioms negOneDepthUnit
#print axioms negOneDepthUnit_ne_one
#print axioms negOneRoot
#print axioms twoPowerRootUnit_negOneRoot
#print axioms proTwoCompletionMk_negOneDepthUnit_ne_one
#print axioms proTwoCompletionMk_twoPowerRootNormUnit_negOneRoot_ne_one
#print axioms proTwoCompletionMk_neg_one_ne_one
#print axioms twoPowerRootToProTwoCompletionTorsion_injective_of_ramifiedI
#print axioms twoPowerRootToMaxProTwoAbTorsion_injective_of_ramifiedI
#print axioms demushkinQ_maxProTwoGalK_eq_two_of_ramifiedI
#print axioms demushkinQ_maxProTwoGalK_eq_two_of_ramifiedI_completedReciprocityInjective

end

end GQ2.Dyadic.EvenDemushkinQ
