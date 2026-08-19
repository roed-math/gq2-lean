/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.EvenFamilyGeneratorData
import GQ2.Dyadic.Instances.OddDegreeFieldWitness

/-!
# The corrected family witness from the field's actual cyclotomic range

This module removes `FamilyFieldBranchWitness` as a caller-supplied classification packet.
At even degree, the general cyclotomic range dichotomy produces either `imChiM alpha` or
`imChiN alpha`; `EvenFamilyGeneratorData` turns that identity into the corresponding marked
packet.  At odd degree, the existing field theorem supplies the `L` witness.  Thus every field
with the standing ramified-`i` datum has a corrected family witness and selection.

The construction is uniform in the degree, level, and handle count.  It does not inspect or
enumerate individual presentation classes.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenCyclotomicRange

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The even-degree corrected witness, built from the actual cyclotomic range dichotomy. -/
noncomputable def evenDegreeFamilyFieldBranchWitness
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (heven : Even (Module.finrank ℚ_[2] K)) :
    FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF) := by
  let H := evenRange_range_eq B RI.deltaI RI.sq_deltaI RI.ramified
  let alpha := Classical.choose H
  have halpha : 2 ≤ alpha := (Classical.choose_spec H).1
  have hrange := (Classical.choose_spec H).2
  by_cases hM : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom =
      imChiM alpha
  · exact .M alpha halpha (by rw [D.degree_eq]; exact heven)
      (markedGeneratorData_of_range_eq_imChiM B FF halpha hM)
  · exact .N alpha halpha (by rw [D.degree_eq]; exact heven)
      (procyclicMarkedGeneratorData_of_range_eq_imChiN B FF
        (hrange.resolve_left hM))

/-- The corrected all-degree family witness constructed from field data alone. -/
noncomputable def fieldFamilyWitnessFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF) := by
  by_cases heven : Even (Module.finrank ℚ_[2] K)
  · exact evenDegreeFamilyFieldBranchWitness B FF D RI heven
  · exact oddDegreeFamilyFieldBranchWitness B FF D
      ((Nat.even_or_odd (Module.finrank ℚ_[2] K)).resolve_left heven)

/-- The corrected all-degree field selection with no residual family witness argument. -/
noncomputable def selectFieldBranchFamilyFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF)
      (fieldFamilyWitnessFromRange B FF D RI) :=
  selectFieldBranchFamily B FF D RI (fieldFamilyWitnessFromRange B FF D RI)

#print axioms evenDegreeFamilyFieldBranchWitness
#print axioms fieldFamilyWitnessFromRange
#print axioms selectFieldBranchFamilyFromRange

end


end GQ2.Dyadic
