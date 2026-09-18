import GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
import GQ2.Dyadic.SourceBoundaryMarkingRN

/-!
# Exact marked consequences of the flexible assembly boundary

The existing flexible assembly returns an abstract equivalence. This file states, without
asserting existence, the extra boundary equality needed for the prescribed marked conclusion.
The field boundary really uses the chosen tame map and the chosen corrected core realization.
Its equality with the candidate boundary gives both maps, full two-adic `nu`, and the exact
maximal-pro-2 square. A cyclotomic conclusion additionally uses a displayed core character
matching the realization; the flexible branch record itself has no such character field.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyFlexibleMarkedBoundary

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  (G : GenAsmFlexibleBranch K B)

/-- The arithmetic boundary of a flexible branch, before any analytic source fields. -/
def fieldBoundary (T : OrientedTameQuotientK B FF) :
    ContinuousMonoidHom (GalK K) ↥(boundarySubgroupQ (qOf K FF) G.nuP) :=
  sourceBoundaryMapK (Γ := galKProfinite K) T.tameFK G.realization.pro2
    (T.compatF_K G.realization.pro2 G.nuP G.realization.nu_compat)

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
@[simp] theorem fieldBoundary_tame (T : OrientedTameQuotientK B FF) (g : GalK K) :
    (fieldBoundary G T g).val.1 = T.tameFK g := rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
@[simp] theorem fieldBoundary_pro2 (T : OrientedTameQuotientK B FF) (g : GalK K) :
    (fieldBoundary G T g).val.2 = G.realization.pro2 g := rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- This is exactly the boundary of the field source used by the existing assembler. -/
theorem fieldSource_boundary (F : GenAsmCompatibleFieldInputs B FF G.degree) :
    ((kExactSupplyRN_of_markedCore (T := F.T) (hP := G.coreIsProP) G.hdeg G.realization.pro2
      G.realization.pro2_surjective G.realization.ker_pro2 G.realization.nu_compat).toSourceRN_compatible
      F.params F.params_n F.params_qK F.ramifiedData).b =
        fieldBoundary G F.T := rfl

variable (W : WordCertificateRN G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
  (standardNumerics G.degree))

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Exact candidate/field boundary equality consists of the tame and prescribed core squares. -/
theorem candidate_fieldBoundary_eq_iff (T : OrientedTameQuotientK B FF)
    (e : ContinuousMulEquiv ((GammaR G.degree (qOf K FF) G.word) : Type) (GalK K)) :
    (∀ g, fieldBoundary G T (e g) =
      (W.toSourceRN (two_le_qOf K FF) (even_qOf K FF)).b g) ↔
      (∀ g, T.tameFK (e g) = TameSpec.tameOfSpec G.degree (qOf K FF) G.word
        W.tameSpecialization g) ∧
      (∀ g, G.realization.pro2 (e g) = W.pro2 g) := by
  constructor
  · intro h
    exact ⟨fun g => congrArg (fun z => z.val.1) (h g),
      fun g => congrArg (fun z => z.val.2) (h g)⟩
  · rintro ⟨ht, hp⟩ g
    exact Subtype.ext (Prod.ext (ht g) (hp g))

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- The full `Ztwo` marking follows already from the tame square. No mod-two upgrade occurs. -/
theorem nu_ur_of_tame_eq (T : OrientedTameQuotientK B FF)
    (e : ContinuousMulEquiv ((GammaR G.degree (qOf K FF) G.word) : Type) (GalK K))
    (ht : ∀ g, T.tameFK (e g) = TameSpec.tameOfSpec G.degree (qOf K FF) G.word
      W.tameSpecialization g) (g : ((GammaR G.degree (qOf K FF) G.word) : Type)) :
    B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g)) := by
  rw [← T.tame_reciprocity_K, ht, W.compat]

omit [T2Space (GalK K)] in
/-- The chosen corrected realization inverts the field's pro-2 projection. -/
theorem realization_equiv_pro2 (g : GalK K) :
    G.realization.equiv (G.realization.pro2 g) = maxProPMk 2 (GalK K) g :=
  G.realization.equiv.apply_symm_apply _

omit [T2Space (GalK K)] in
/-- The prescribed core square implies the exact maximal-pro-2 square. -/
theorem maxProPMk_of_pro2_eq
    (e : ContinuousMulEquiv ((GammaR G.degree (qOf K FF) G.word) : Type) (GalK K))
    (hp : ∀ g, G.realization.pro2 (e g) = W.pro2 g)
    (g : ((GammaR G.degree (qOf K FF) G.word) : Type)) :
    maxProPMk 2 (GalK K) (e g) = G.realization.equiv (W.pro2 g) := by
  rw [← realization_equiv_pro2 G, hp]

omit [T2Space (GalK K)] in
/-- A specified orientation passes through the boundary only after its matching to the
chosen realization has been exhibited. No arbitrary isomorphism invariance is assumed. -/
theorem cyclotomic_of_pro2_eq
    (χP : G.core →* ℤ_[2]ˣ)
    (hχ : ∀ p, chiCycKTwo (K := K) (G.realization.equiv p) = χP p)
    (e : ContinuousMulEquiv ((GammaR G.degree (qOf K FF) G.word) : Type) (GalK K))
    (hp : ∀ g, G.realization.pro2 (e g) = W.pro2 g)
    (g : ((GammaR G.degree (qOf K FF) G.word) : Type)) :
    chiCycK K (e g) = χP (W.pro2 g) := by
  rw [← chiCycKTwo_maxProPMk, maxProPMk_of_pro2_eq G W e hp, hχ]

#print axioms fieldBoundary
#print axioms fieldBoundary_tame
#print axioms fieldBoundary_pro2
#print axioms fieldSource_boundary
#print axioms candidate_fieldBoundary_eq_iff
#print axioms nu_ur_of_tame_eq
#print axioms realization_equiv_pro2
#print axioms maxProPMk_of_pro2_eq
#print axioms cyclotomic_of_pro2_eq

end

end GQ2.Dyadic.Instances.FieldFamilyFlexibleMarkedBoundary
