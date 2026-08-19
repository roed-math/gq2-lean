/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary

/-!
# Canonical M realizations as full marking orbits

This module identifies W305's canonical marked-core realization boundary with a single
automorphism-orbit problem.  Fix any base topological equivalence from the presented core to
the field's maximal pro-2 quotient.  A realization at a chosen marking exists if and only if a
core automorphism makes that entire marking equal to the transported arithmetic marking.

This is deliberately stronger and cleaner than a one-coordinate pivot condition: every value
of the marking is matched.  Conversely it is exactly what `MarkedCoreRealization` says, so the
orbit condition introduces no excess hypothesis.  The remaining general M-family theorem is
therefore full marking transitivity for `DM alpha h`, uniformly in `alpha` and `h`.
-/

namespace GQ2.Dyadic.Instances.MFieldCanonicalMarkingOrbit

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The full marking-normalization orbit relative to one base equivalence. -/
def MarkedCoreMarkingOrbitAt (B : MarkedRecip R K) {P : ProfiniteGrp}
    (e : ContinuousMulEquiv (P : Type) (maxProPQuotient 2 (GalK K)))
    (nuP : ContinuousMonoidHom (P : Type) Ztwo) : Prop :=
  ∃ Psi : ContinuousMulEquiv (P : Type) (P : Type),
    ∀ x, ztwoIota (nuP x) = nuUrKTwo B (e (Psi x))

/-- A canonical marked-core realization is exactly a full marking orbit. -/
theorem markedCoreRealization_iff_markingOrbitAt
    (B : MarkedRecip R K) {P : ProfiniteGrp}
    (e : ContinuousMulEquiv (P : Type) (maxProPQuotient 2 (GalK K)))
    (nuP : ContinuousMonoidHom (P : Type) Ztwo) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) P nuP) ↔
      MarkedCoreMarkingOrbitAt B e nuP := by
  constructor
  · rintro ⟨M⟩
    let Psi : ContinuousMulEquiv (P : Type) (P : Type) := M.equiv.trans e.symm
    refine ⟨Psi, fun x => ?_⟩
    change ztwoIota (nuP x) = nuUrKTwo B (e (e.symm (M.equiv x)))
    rw [e.apply_symm_apply]
    exact M.nu_equiv x
  · rintro ⟨Psi, hPsi⟩
    exact ⟨{
      equiv := Psi.trans e
      nu_equiv := hPsi }⟩

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Compact-M canonical realization at any proof of the valid alpha bound. -/
theorem m0CanonicalMarkedCoreRealization_iff
    (B : MarkedRecip R K) {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    M0CanonicalMarkedCoreRealization B alpha h ↔
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DM alpha h)
        (fieldId_mNuZtwo alpha h halpha)) := by
  constructor
  · rintro ⟨halpha', H⟩
    simpa only [proof_irrel_heq] using H
  · intro H
    exact ⟨halpha, H⟩

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Procyclic-M canonical realization at any proof of the valid alpha bound. -/
theorem mpcCanonicalMarkedCoreRealization_iff
    (B : MarkedRecip R K) {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (halpha : 1 ≤ alpha) :
    MpcCanonicalMarkedCoreRealization B alpha r h epsilon eta ↔
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DM alpha h)
        (mpcNu alpha r (p epsilon r) h eta halpha)) := by
  constructor
  · rintro ⟨halpha', H⟩
    simpa only [proof_irrel_heq] using H
  · intro H
    exact ⟨halpha, H⟩

/-- The compact-M campaign boundary is exactly full normalization of its canonical marking. -/
theorem m0CanonicalMarkedCoreRealization_iff_markingOrbitAt
    (B : MarkedRecip R K) {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    M0CanonicalMarkedCoreRealization B alpha h ↔
      MarkedCoreMarkingOrbitAt B e (fieldId_mNuZtwo alpha h halpha) :=
  (m0CanonicalMarkedCoreRealization_iff B halpha).trans
    (markedCoreRealization_iff_markingOrbitAt B e
      (fieldId_mNuZtwo alpha h halpha))

/-- The procyclic-M campaign boundary is exactly full normalization of its canonical marking. -/
theorem mpcCanonicalMarkedCoreRealization_iff_markingOrbitAt
    (B : MarkedRecip R K) {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    MpcCanonicalMarkedCoreRealization B alpha r h epsilon eta ↔
      MarkedCoreMarkingOrbitAt B e
        (mpcNu alpha r (p epsilon r) h eta halpha) :=
  (mpcCanonicalMarkedCoreRealization_iff B halpha).trans
    (markedCoreRealization_iff_markingOrbitAt B e
      (mpcNu alpha r (p epsilon r) h eta halpha))

#print axioms MarkedCoreMarkingOrbitAt
#print axioms markedCoreRealization_iff_markingOrbitAt
#print axioms m0CanonicalMarkedCoreRealization_iff
#print axioms mpcCanonicalMarkedCoreRealization_iff
#print axioms m0CanonicalMarkedCoreRealization_iff_markingOrbitAt
#print axioms mpcCanonicalMarkedCoreRealization_iff_markingOrbitAt

end


end GQ2.Dyadic.Instances.MFieldCanonicalMarkingOrbit
