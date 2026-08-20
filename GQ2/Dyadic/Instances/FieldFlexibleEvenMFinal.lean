import GQ2.Dyadic.Instances.MCompactFlexibleCertificate
import GQ2.Dyadic.Instances.MpcFlexibleCertificate
import GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly

/-!
# Field-facing flexible even-M assembly

This module puts the flexible core directly on the field's maximal pro-2 quotient.  Its
unramified marking and realization are tautological.  Therefore one normalized
`CorePresentation` is the sole remaining input before the corrected residual and final
general-K equivalence, for both compact M and displayed procyclic M.  This is a conditional
interface, not an existence claim for the unchanged word: W323 shows that in the obstructed
odd-residue compact-M pattern the presentation word itself must also move.
-/

namespace GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.MCompactFlexibleCertificate
open GQ2.Dyadic.Instances.MpcFlexibleCertificate
open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Words.Mpc

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)

/-- The field's unramified character on its maximal pro-2 quotient, with `Ztwo` codomain. -/
def fieldCoreNuZtwo : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) Ztwo :=
  (ztwoIota.symm : ContinuousMonoidHom (Multiplicative ℤ_[2]) Ztwo).comp (nuUrKTwo B)

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem ztwoIota_fieldCoreNuZtwo (x : maxProPQuotient 2 (GalK K)) :
    ztwoIota (fieldCoreNuZtwo B x) = nuUrKTwo B x :=
  ztwoIota.apply_symm_apply _

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
/-- The field-core marking is onto. -/
theorem fieldCoreNuZtwo_surjective (FF : DyadicUnitFiltration K) :
    Function.Surjective (fieldCoreNuZtwo B) := by
  intro z
  obtain ⟨gbar, hgbar⟩ := B.nuUrSurjective FF (ztwoIota z)
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨maxProPMk 2 (GalK K) g, ?_⟩
  apply ztwoIota.injective
  rw [ztwoIota_fieldCoreNuZtwo, nuUrKTwo_maxProPMk, hgbar]

/-- The field maximal pro-2 quotient realizes itself with its intrinsic marking. -/
def fieldCoreRealization :
    MarkedCoreRealization (K := K) (B := B) (maxProPQuotient 2 (GalK K))
      (fieldCoreNuZtwo B) where
  equiv := ContinuousMulEquiv.refl _
  nu_equiv := fun x => by
    change ztwoIota (fieldCoreNuZtwo B x) = nuUrKTwo B x
    exact ztwoIota_fieldCoreNuZtwo B x

/-- The flexible compact-M branch directly on the field's maximal pro-2 quotient. -/
def mCompactFieldFlexibleBranch (FF : DyadicUnitFiltration K) (alpha h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h) : GenAsmFlexibleBranch K B where
  degree := 2 + 2 * h
  word := mCompactW alpha h
  core := maxProPQuotient 2 (GalK K)
  coreIsProP := isProP_maxProPQuotient
  hdeg := hdeg
  nuP := fieldCoreNuZtwo B
  hnuP := fieldCoreNuZtwo_surjective B FF
  realization := fieldCoreRealization B

/-- An adapted compact-M presentation on the field core supplies the corrected residual. -/
def mCompactFieldFlexibleRowResidualRN
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (C : FlexibleCoreLeavesRN (2 + 2 * h) (mCompactW alpha h)
      (maxProPQuotient 2 (GalK K)) (fieldCoreNuZtwo B)) :
    GenAsmFlexibleRowResidualRN FF (mCompactFieldFlexibleBranch B FF alpha h hdeg) where
  cand := mCompactWordCertificateRN_flexible halpha (qOf_ne_zero K FF)
    (even_qOf K FF) isProP_maxProPQuotient C

/-- General-K compact-M assembly from one adapted field-core presentation. -/
theorem mCompactFieldFlexible_candidate_equiv_galKRN
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (C : FlexibleCoreLeavesRN (2 + 2 * h) (mCompactW alpha h)
      (maxProPQuotient 2 (GalK K)) (fieldCoreNuZtwo B))
    (F : GenAsmCompatibleFieldInputs B FF (2 + 2 * h)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 + 2 * h) (qOf K FF) (mCompactW alpha h) : ProfiniteGrp) : Type)
      (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible
    (mCompactFieldFlexibleBranch B FF alpha h hdeg) F
    (mCompactFieldFlexibleRowResidualRN B FF halpha hdeg C)

/-- The flexible displayed Mpc branch directly on the field's maximal pro-2 quotient. -/
def mpcFieldFlexibleBranch (FF : DyadicUnitFiltration K)
    (alpha r h : ℕ) (epsilon : Bool)
    {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h) : GenAsmFlexibleBranch K B where
  degree := 2 + 2 * h
  word := mpcW alpha r (p epsilon r) d.display h
  core := maxProPQuotient 2 (GalK K)
  coreIsProP := isProP_maxProPQuotient
  hdeg := hdeg
  nuP := fieldCoreNuZtwo B
  hnuP := fieldCoreNuZtwo_surjective B FF
  realization := fieldCoreRealization B

/-- An adapted displayed Mpc presentation on the field core supplies the corrected residual. -/
def mpcFieldFlexibleRowResidualRN
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (C : FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcW alpha r (p epsilon r) d.display h)
      (maxProPQuotient 2 (GalK K)) (fieldCoreNuZtwo B)) :
    GenAsmFlexibleRowResidualRN FF (mpcFieldFlexibleBranch B FF alpha r h epsilon d hdeg) where
  cand := mpcWordCertificateRN_flexible d halpha hr (qOf_ne_zero K FF)
    (even_qOf K FF) isProP_maxProPQuotient C

/-- General-K displayed Mpc assembly from one adapted field-core presentation. -/
theorem mpcFieldFlexible_candidate_equiv_galKRN
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (C : FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcW alpha r (p epsilon r) d.display h)
      (maxProPQuotient 2 (GalK K)) (fieldCoreNuZtwo B))
    (F : GenAsmCompatibleFieldInputs B FF (2 + 2 * h)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 + 2 * h) (qOf K FF)
        (mpcW alpha r (p epsilon r) d.display h) : ProfiniteGrp) : Type)
      (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible
    (mpcFieldFlexibleBranch B FF alpha r h epsilon d hdeg) F
    (mpcFieldFlexibleRowResidualRN B FF d halpha hr hdeg C)

#print axioms fieldCoreNuZtwo
#print axioms fieldCoreNuZtwo_surjective
#print axioms fieldCoreRealization
#print axioms mCompactFieldFlexibleRowResidualRN
#print axioms mCompactFieldFlexible_candidate_equiv_galKRN
#print axioms mpcFieldFlexibleRowResidualRN
#print axioms mpcFieldFlexible_candidate_equiv_galKRN

end

end GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
