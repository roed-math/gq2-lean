import GQ2.Dyadic.GeneralCertificatesRN
import GQ2.Dyadic.SourceTransportRN
import GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly

/-!
# Independent core and word transport for corrected certificates

A corrected certificate can be transported across an equivalence of candidate groups without
first constructing a new `CorePresentation`: precompose its pro-2 map with the equivalence.
Combining this with `GeneralCertificatesRN` permits the marked core and the source word to move
independently.  The final declarations feed that combined transport directly into the flexible
general-K assembler.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open TameSpec
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

/-- Transport a corrected word certificate across an equivalence of its candidate group.
The pro-2 map is chosen by precomposition, so no new core presentation is required. -/
noncomputable def WordCertificateRN.transportWordEquiv
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (W : WordCertificateRN n q R₀ P hP nuP SN)
    (hq2 : 2 ≤ q) (hqe : Even q)
    (hspec : TameSpecializes n q R₁)
    (e : ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))
    (htame : tameOfSpec n q R₁ hspec =
      (tameOfSpec n q R₀ W.tameSpecialization).comp
        (e : ContinuousMonoidHom ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))) :
    WordCertificateRN n q R₁ P hP nuP SN := by
  let S := (W.toSourceRN hq2 hqe).transport e
    (scalarActionZmodTwo (GammaR n q R₁))
    (scalarActionZmodTwo_continuousSMul (GammaR n q R₁))
    (scalarActionZmodTwo_triv (GammaR n q R₁))
  have hcompat : ∀ g : ((GammaR n q R₁) : Type),
      nuTq q (tameOfSpec n q R₁ hspec g) =
        nuP ((W.pro2.comp
          (e : ContinuousMonoidHom ((GammaR n q R₁) : Type)
            ((GammaR n q R₀) : Type))) g) := by
    intro g
    rw [DFunLike.congr_fun htame g]
    exact W.compat (e g)
  refine
    { tameSpecialization := hspec
      coreRel := fun G _ _ _ _ _ t => t.eval (_root_.GQ2.Dyadic.pro2 R₁)
      proTwoWord := fun _ _ _ _ _ _ _ => rfl
      pro2 := W.pro2.comp
        (e : ContinuousMonoidHom ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))
      ker_pro2 := ker_comp_continuousMulEquiv e W.pro2 W.ker_pro2
      hpro2 := W.hpro2.comp e.surjective
      compat := hcompat
      tfg := S.tfg
      smulZmod2 := scalarActionZmodTwo _
      contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
      htriv := scalarActionZmodTwo_triv _
      exactLifting := S.exactLifting
      stokes := S.stokes
      scalar := S.scalar
      determinant := ?_
      htame := Count.htame_of_tameSpecializes hspec
      hwild := Count.hwild_of_tameSpecializes hspec }
  exact (affineDeterminantCertificate_congr hcompat S.compat _ htame rfl).mpr S.determinant

/-- Transport a corrected certificate across independent core and word equivalences. -/
noncomputable def WordCertificateRN.transportCoreWord
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P₀ P₁ : ProfiniteGrp}
    {hP₀ : IsProP 2 P₀} {nu₀ : ContinuousMonoidHom P₀ Ztwo}
    {nu₁ : ContinuousMonoidHom P₁ Ztwo} {SN : SourceNumerics n}
    (W : WordCertificateRN n q R₀ P₀ hP₀ nu₀ SN)
    (hP₁ : IsProP 2 P₁)
    (eCore : ContinuousMulEquiv (P₀ : Type) (P₁ : Type))
    (hnu : ∀ x, nu₁ (eCore x) = nu₀ x)
    (hq2 : 2 ≤ q) (hqe : Even q)
    (hspec : TameSpecializes n q R₁)
    (eWord : ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))
    (htame : tameOfSpec n q R₁ hspec =
      (tameOfSpec n q R₀ W.tameSpecialization).comp
        (eWord : ContinuousMonoidHom ((GammaR n q R₁) : Type)
          ((GammaR n q R₀) : Type))) :
    WordCertificateRN n q R₁ P₁ hP₁ nu₁ SN :=
  (W.genCertTransportRN hP₁ eCore hnu).transportWordEquiv hq2 hqe hspec eWord htame

namespace Instances.FieldFamilyFlexibleAssembly

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- Independent core and word transports supply a flexible corrected row residual. -/
noncomputable def GenAsmFlexibleRowResidualRN.ofCoreWordTransport
    (G : GenAsmFlexibleBranch K B)
    {R₀ : PWord (Generator G.degree)} {P₀ : ProfiniteGrp}
    {hP₀ : IsProP 2 P₀} {nu₀ : ContinuousMonoidHom P₀ Ztwo}
    (W : WordCertificateRN G.degree (qOf K FF) R₀ P₀ hP₀ nu₀
      (standardNumerics G.degree))
    (eCore : ContinuousMulEquiv (P₀ : Type) (G.core : Type))
    (hnu : ∀ x, G.nuP (eCore x) = nu₀ x)
    (hspec : TameSpecializes G.degree (qOf K FF) G.word)
    (eWord : ContinuousMulEquiv
      ((GammaR G.degree (qOf K FF) G.word) : Type)
      ((GammaR G.degree (qOf K FF) R₀) : Type))
    (htame : tameOfSpec G.degree (qOf K FF) G.word hspec =
      (tameOfSpec G.degree (qOf K FF) R₀ W.tameSpecialization).comp
        (eWord : ContinuousMonoidHom
          ((GammaR G.degree (qOf K FF) G.word) : Type)
          ((GammaR G.degree (qOf K FF) R₀) : Type))) :
    GenAsmFlexibleRowResidualRN FF G where
  cand := W.transportCoreWord G.coreIsProP eCore hnu (two_le_qOf K FF)
    (even_qOf K FF) hspec eWord htame

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- End-to-end flexible assembly after independent core and word transports. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofCoreWordTransport
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    {R₀ : PWord (Generator G.degree)} {P₀ : ProfiniteGrp}
    {hP₀ : IsProP 2 P₀} {nu₀ : ContinuousMonoidHom P₀ Ztwo}
    (W : WordCertificateRN G.degree (qOf K FF) R₀ P₀ hP₀ nu₀
      (standardNumerics G.degree))
    (eCore : ContinuousMulEquiv (P₀ : Type) (G.core : Type))
    (hnu : ∀ x, G.nuP (eCore x) = nu₀ x)
    (hspec : TameSpecializes G.degree (qOf K FF) G.word)
    (eWord : ContinuousMulEquiv
      ((GammaR G.degree (qOf K FF) G.word) : Type)
      ((GammaR G.degree (qOf K FF) R₀) : Type))
    (htame : tameOfSpec G.degree (qOf K FF) G.word hspec =
      (tameOfSpec G.degree (qOf K FF) R₀ W.tameSpecialization).comp
        (eWord : ContinuousMonoidHom
          ((GammaR G.degree (qOf K FF) G.word) : Type)
          ((GammaR G.degree (qOf K FF) R₀) : Type))) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible G F
    (GenAsmFlexibleRowResidualRN.ofCoreWordTransport G W eCore hnu hspec eWord htame)

end Instances.FieldFamilyFlexibleAssembly

open Instances.FieldFamilyFlexibleAssembly

#print axioms WordCertificateRN.transportWordEquiv
#print axioms WordCertificateRN.transportCoreWord
#print axioms GenAsmFlexibleRowResidualRN.ofCoreWordTransport
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofCoreWordTransport

end

end GQ2.Dyadic
