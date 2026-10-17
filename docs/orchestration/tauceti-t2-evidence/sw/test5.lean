module

public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import GQ2.TraceForm

set_option synthInstance.maxHeartbeats 400000

variable (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k] (δ : AlgebraicClosure ℚ_[2])

#synth LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)
#synth CompactSpace (GQ2.Kummer.GaloisGroup ℚ_[2])
example : LocallyCompactSpace ↥k.fixingSubgroup :=
  haveI : CompactSpace ↥k.fixingSubgroup := isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed k).isCompact
  inferInstance
#synth IsTopologicalGroup ↥k.fixingSubgroup
