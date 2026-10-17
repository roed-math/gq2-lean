module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import GQ2.TraceForm

set_option synthInstance.maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k] (δ : ℚ̄₂)

#synth Invertible (2 : ↥k)
#synth Invertible (2 : ↥(GQ2.quadExt k δ))
#synth Field ↥(GQ2.quadExt k δ)
#synth Algebra ↥k ↥(GQ2.quadExt k δ)
#synth CharZero ↥k
#synth LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)
#synth CompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)
#synth TotallyDisconnectedSpace (TauCeti.AbsoluteGaloisGroup ↥k)
#synth IsTopologicalGroup (TauCeti.AbsoluteGaloisGroup ↥k)
#synth IsScalarTower ↥k ↥(GQ2.quadExt k δ) ↥(GQ2.quadExt k δ)

-- `Algebra.IsSeparable` in char 0
example [FiniteDimensional ↥k ↥(GQ2.quadExt k δ)] : Algebra.IsSeparable ↥k ↥(GQ2.quadExt k δ) := by
  infer_instance

-- trace form identification, untwisted
example : GQ2.traceFormOne k δ =
    QuadraticMap.traceTransfer ↥k (QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) :=
  QuadraticMap.traceTransfer_sq.symm

-- trace form identification, twisted
example (a : ↥(GQ2.quadExt k δ)) : GQ2.traceFormTwisted k δ a =
    QuadraticMap.traceTransfer ↥k (a • QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) := by
  ext z
  rw [GQ2.traceFormTwisted_apply, QuadraticMap.traceTransfer_apply, QuadraticMap.smul_apply,
    QuadraticMap.sq_apply, smul_eq_mul, mul_assoc]
