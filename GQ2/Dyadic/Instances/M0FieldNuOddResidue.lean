/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldNuUnramifiedBridge
import GQ2.Dyadic.Instances.GammaLNuKummerIdentification

/-!
# The compact-M unramified class in odd residue degree

The descent of the mod-two unramified character from `G_{ℚ₂}` to `G_K` only uses that
the residue degree `f(K/ℚ₂)` is odd.  Odd total degree, used by the older endpoint, is a
sufficient but unnecessarily strong premise.

This module separates that closed reciprocity calculation from the remaining field fact.  In
odd residue degree, the square class of `-3` represents the marked unramified character as soon
as adjoining its chosen square root preserves the value group.  The selected compact-M consumer
then needs only this spectral statement and the independently isolated distinguished-D
placement.  No claim that the current filtration bundle proves the spectral statement is made.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open FrattiniFrameSupply

namespace NuKummer

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K]

/-- Mod-two descent only needs odd residue degree. -/
theorem redTwo_nuUr_restrict_of_odd_residueDegree
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    (g : GalK K) :
    MarkedFrame.redTwo
        (Multiplicative.toAdd (R.nu_ur (toAb (g : AbsGalQ2)))) =
      MarkedFrame.redTwo (Multiplicative.toAdd (B.nu_ur (toAbK K g))) := by
  rw [← inclAbK_toAbK K g, toAdd_nuUr_incl B FF (toAbK K g), map_mul,
    redTwo_natCast_of_odd hf, one_mul]

end NuKummer

namespace MarkedFrame

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- In odd residue degree, preservation of the value group by `K(√-3)/K` is the only
remaining input for the `-3` realization of the marked unramified mod-two character. -/
theorem nuUrUnramifiedKummerClass_of_odd_residueDegree
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    (hunram : HasEqualNormValueGroups K
      (sqrtCl (((NuKummer.negThreeUnit K : Kˣ) : K) : AlgebraicClosure ℚ_[2]))) :
    NuUrUnramifiedKummerClass B := by
  have hδ3 :
      (sqrtCl (((NuKummer.negThreeUnit K : Kˣ) : K) :
        AlgebraicClosure ℚ_[2])) ^ 2 = -3 :=
    NuKummer.sq_sqrtCl_negThreeUnit K
  refine ⟨NuKummer.negThreeUnit K,
    sqrtCl (((NuKummer.negThreeUnit K : Kˣ) : K) : AlgebraicClosure ℚ_[2]),
    sqrtCl_sq _, hunram, ?_⟩
  rw [h1MaxProTwoEquivGalK_apply]
  unfold nuUrModTwoClassKTwo SqCyclotomicFrattiniFrame.characterClass kummerClassK
  rw [inf1_H1mk]
  congr 1
  apply Subtype.ext
  funext g
  show redTwo
      (Multiplicative.toAdd (nuUrKTwo B (maxProPMk 2 (GalK K) g))) =
    Kummer.kummerCocycleFun _ _
  rw [nuUrKTwo_maxProPMk]
  exact
    (NuKummer.redTwo_nuUr_restrict_of_odd_residueDegree B FF hf g).symm.trans
      (NuKummer.redTwo_nuUr_eq_kummerCocycle hδ3 R (g : AbsGalQ2))

end MarkedFrame

end
end GQ2.Dyadic.LSquare

namespace GQ2.Dyadic.Instances.M0FieldNuOddResidue

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.M0FieldNuUnramifiedBridge
open GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
open GQ2.Dyadic.LSquare.MarkedFrame
open GQ2.Dyadic.LSquare.NuKummer

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2]

/-- The selected compact-M corrected-RN residual in odd residue degree.  The remaining inputs
are precisely the distinguished-D placement and the spectral unramifiedness of `K(√-3)`. -/
theorem m0RowResidualRN_of_familySelection_of_oddResidue_negThree
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (Hplace : M0UniformizerDPlacement FF alpha (handleCount FP (.M0 alpha)))
    (hunram : HasEqualNormValueGroups K
      (sqrtCl (((negThreeUnit K : Kˣ) : K) : AlgebraicClosure ℚ_[2]))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) :=
  m0RowResidualRN_of_familySelection_of_unramifiedKummer B FF S hbranch Hplace
    (nuUrUnramifiedKummerClass_of_odd_residueDegree B FF hf hunram)

#print axioms GQ2.Dyadic.LSquare.NuKummer.redTwo_nuUr_restrict_of_odd_residueDegree
#print axioms GQ2.Dyadic.LSquare.MarkedFrame.nuUrUnramifiedKummerClass_of_odd_residueDegree
#print axioms m0RowResidualRN_of_familySelection_of_oddResidue_negThree

end
end GQ2.Dyadic.Instances.M0FieldNuOddResidue
