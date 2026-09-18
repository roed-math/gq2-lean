/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.RamificationInertiaBridge

/-!
# Canonical finite dyadic numerical parameters

Both the unit filtration and the fundamental ramification identity are proved constructions.
This convenience producer discharges the filtration/numerical choices in a field-facing theorem;
it introduces no reciprocity, tame quotient, or ramified-i existence claim. In particular a
RamifiedIData hypothesis remains necessary for the campaign's ramified-i family selector.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The field's proved unit filtration and fundamental identity determine its numerical
presentation parameters; callers do not supply a filtration or a divisibility witness. -/
def canonicalFiniteDyadicParameters
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    FiniteDyadicParameters K (dyadicUnitFiltration K) :=
  SpectralLocalField.finiteDyadicParameters

@[simp] theorem canonicalFiniteDyadicParameters_n
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    (canonicalFiniteDyadicParameters K).params.n = Module.finrank ℚ_[2] K := rfl

@[simp] theorem canonicalFiniteDyadicParameters_f
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    (canonicalFiniteDyadicParameters K).params.f = (dyadicUnitFiltration K).f := rfl

@[simp] theorem canonicalFiniteDyadicParameters_qK
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    (canonicalFiniteDyadicParameters K).params.qK = qOf K (dyadicUnitFiltration K) := rfl

@[simp] theorem canonicalFiniteDyadicParameters_e
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    (canonicalFiniteDyadicParameters K).params.e = (dyadicUnitFiltration K).e :=
  ((canonicalFiniteDyadicParameters K).params_e_eq_iff_fundamentalIdentity).mpr
    SpectralLocalField.field_finrank_eq_e_mul_f

#print axioms canonicalFiniteDyadicParameters
#print axioms canonicalFiniteDyadicParameters_n
#print axioms canonicalFiniteDyadicParameters_f
#print axioms canonicalFiniteDyadicParameters_qK
#print axioms canonicalFiniteDyadicParameters_e
end
end GQ2.Dyadic

