/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.GaussZ.FinalDK
import GQ2.Dyadic.Instances.RamifiedCertificateCompatible
import GQ2.Dyadic.Instances.KAnalytic
import GQ2.Dyadic.Instances.GammaLOddDegreeGrandAssembly
import GQ2.Dyadic.SqCore.GradedRowUniform

/-!
# Compatibility-aware ramified data through the odd-`L` endpoint

The ramified determinant calculation only applies its certificate supplier to maps satisfying
`rho g = c (tame g)`.  This module carries that actual-use compatibility through
`gaussZResidueDK_ramified`, the affine determinant certificate, the corrected arithmetic source,
and the final odd-`L` reconstruction.  The highest endpoint uses the already-closed uniform row
supply, so no marking, clearing, or frame premise remains.

`CompatibleRamifiedDataAt` repeats the two source-action instances explicitly.  This is needed
because `FinalDK` permits a custom `MuN 2` action path, while the more abstract
`CompatibleRamifiedData` proposition does not retain those instances in its quantifier.  The
new surface is parallel to the legacy universal `ramifiedData` APIs; none of those declarations
is changed.

The surviving arithmetic residual is precisely `CompatibleRamifiedDataAt` for the packet's
`D.params`, the subgroup `GalKsub K`, and the transported oriented tame quotient.  It can be
discharged instance-by-instance by the anchored-split construction once residue-triviality and
the corresponding `InvolutionFieldPackage` are supplied.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open scoped Classical

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section CompatibleHeadInflated

/-- Compatibility-aware ramified data with the source `MuN 2` action kept explicit. -/
def CompatibleRamifiedDataAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    [DistribMulAction ↑U (MuN 2)] [ContinuousSMul ↑U (MuN 2)]
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate P U V c rho)

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
variable {PG : ProfiniteGrp}

/-- The ramified head-inflated Gauss residue using only compatible ramified data. -/
theorem gaussZResidueDK_ramified_compatible
    (FP : FieldParameters) (U : Subgroup AbsGalQ2)
    {nuP : ContinuousMonoidHom PG Ztwo}
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hn : U.index = FP.n)
    [DistribMulAction ↑U (ZMod 2)] [ContinuousSMul ↑U (ZMod 2)]
    [instDMAmu : DistribMulAction ↑U (MuN 2)] [instCSmu : ContinuousSMul ↑U (MuN 2)]
    [CompactSpace ↑U] [TotallyDisconnectedSpace ↑U]
    (D : TateDualityG ↑U 2)
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : FP.qK ≠ 0) (hqe : Even FP.qK)
    (F : BoundaryFrameK FP.qK PG H E)
    (tameFK : ContinuousMonoidHom ↑U (Tq FP.qK)) (htameFK : Function.Surjective tameFK)
    (b : ContinuousMonoidHom ↑U ↑(boundarySubgroupQ FP.qK nuP))
    (hbtame : ∀ g : ↑U, (b g).val.1 = tameFK g)
    (ramifiedData : CompatibleRamifiedDataAt FP U tameFK)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC,
        ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (_hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau FP.qK) • v ≠ v) :
    GaussZResidueK b F (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h
      ((2 : ℤ) ^ (FP.n * m)) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  letI : TopologicalSpace (SectionNine.HVq T Blk) := ⊥
  haveI : DiscreteTopology (SectionNine.HVq T Blk) := ⟨rfl⟩
  have hl' : l.1 ≠ Blk.frattiniK := fun heq ↦ h (Subtype.ext heq)
  set EnD := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEnDdef
  intro rhoCocycle
  set rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
    (EnD.radData l h) rfl rhoCocycle with hrhoMdef
  set cF : ContinuousMonoidHom (Tq FP.qK) (SectionNine.HVq T Blk) :=
    headTameSurjK T Blk F with hcFdef
  have hcF : Function.Surjective cF := headTameSurjK_surjective T Blk F
  set rhoHV : ContinuousMonoidHom ↑U (SectionNine.HVq T Blk) :=
    ⟨(SectionNine.blockProjF T Blk).comp rhoCocycle.1.1.toMonoidHom,
      (continuous_of_discreteTopology (f := fun c :
        (SectionNine.blockFrame T Blk hE2).YC ↦ SectionNine.blockProjF T Blk c)).comp
        rhoCocycle.1.1.continuous_toFun⟩ with hrhoHVdef
  have hfacHV : ∀ g : ↑U, rhoHV g = cF (tameFK g) := fun g ↦ by
    rw [← hbtame g]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rhoCocycle g)
  letI instT : TopologicalSpace (Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⊥
  haveI instD : DiscreteTopology (Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨rfl⟩
  letI instA : DistribMulAction ↑U (Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
    DistribMulAction.compHom _ rhoHV.toMonoidHom
  haveI instC : ContinuousSMul ↑U (Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨by
    show Continuous fun p : ↑U × Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P) ↦
      rhoHV p.1 • p.2
    exact (continuous_of_discreteTopology
        (f := fun z : SectionNine.HVq T Blk × Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P) ↦
          z.1 • z.2)).comp
      ((rhoHV.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace EnD.Vmod := instT
  haveI : DiscreteTopology EnD.Vmod := instD
  letI : DistribMulAction ↑U EnD.Vmod := instA
  haveI : ContinuousSMul ↑U EnD.Vmod := instC
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction ↑U (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul ↑U (EnD.descData l h).Vmod := instC
  letI : DistribMulAction (SectionNine.HVq T Blk) EnD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) (EnD.descData l h).Vmod :=
    SectionNine.hvAct T Blk
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 :=
    (inferInstance : Finite (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace (Y ⧸ Blk.K) :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (Y ⧸ Blk.K) :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  haveI : Finite (Y ⧸ Blk.K) :=
    (inferInstance : Finite (SectionNine.blockFrame T Blk hE2).YC)
  letI : DistribMulAction ((SectionNine.blockFrame T Blk hE2).YC)
      (Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := blockActV Blk
  letI : DistribMulAction ((SectionNine.blockFrame T Blk hE2).YC) (EnD.descData l h).Vmod :=
    blockActV Blk
  have hround : ∀ gamma : ↑U, rho0 (EnD.descData l h) rhoM gamma = rhoCocycle.1.1 gamma :=
    rho0_descData_rhoPrimeK b F EnD l h rhoCocycle
  have hcomp : ∀ (gamma : ↑U) (v : (EnD.descData l h).Vmod),
      gamma • v = rho0 (EnD.descData l h) rhoM gamma • v := by
    intro gamma v
    rw [show rho0 (EnD.descData l h) rhoM gamma • v
        = SectionNine.blockProjF T Blk (rho0 (EnD.descData l h) rhoM gamma) • v from
      SectionNine.blockProjF_compat T Blk _ v, hround gamma]
    rfl
  have hsurjRho : Function.Surjective
      (fun gamma : ↑U ↦ rho0 (EnD.descData l h) rhoM gamma) :=
    fun y ↦ by
      obtain ⟨gamma, hgamma⟩ := rhoCocycle.1.2 y
      exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ gamma : ↑U, rho0 (EnD.descData l h) rhoM gamma • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjRho hsimple hnt
  have hramF : ∃ v : Additive (↑Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      cF (tqTau FP.qK) • v ≠ v := hram
  have hpinned := sum_sign_Q0loc_K_ramified FP U hU hn D tameFK htameFK cF hcF rhoHV hfacHV
    (fun _ _ ↦ rfl) (SectionNine.hvAct_faithful T Blk) (SectionNine.hv_simple T Blk)
    (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
    (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
    (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
    (hv_invK T Blk hq0 hqe F l hl') (blockDatHVK T Blk hq0 hqe F l hl')
    (blockDatHV_specK T Blk hq0 hqe F l hl') m hm hcard hramF
    (ramifiedData _ cF rhoHV hfacHV hramF)
  have hH1c : Nat.card (H1 ↑U (EnD.descData l h).Vmod) = 2 ^ (2 * (m * FP.n)) :=
    card_H1_eq_of_markingK FP U hU hn D tameFK htameFK cF hcF rhoHV hfacHV (fun _ _ ↦ rfl)
      (SectionNine.hv_simple T Blk)
      (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
      (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
      (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l hl')
      (hv_invK T Blk hq0 hqe F l hl') m hm hcard
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) rhoM) :=
    finite_vcocycleG hcomp hfix Nat.card_pos.ne' (by rw [hH1c]; positivity)
  have hbij : Function.Bijective (h1OfVQuot hcomp) :=
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  have hQbar : ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) rhoM smul_zmodTwo x)
      = (2 : ℤ) ^ (FP.n * m) := by
    rw [← hpinned]
    refine finsum_eq_of_bijective (h1OfVQuot hcomp) hbij fun x ↦ ?_
    rw [QZeroBar_eq_Q0locG D hcomp rhoCocycle.1.1 (fun gamma ↦ (hround gamma).symm)
      smul_zmodTwo x]
    exact congrArg SectionEight.sign
      (Q0loc_reindexHom_homG (C := SectionNine.HVq T Blk)
        (C' := (SectionNine.blockFrame T Blk hE2).YC) D
        (blockDatHVK T Blk hq0 hqe F l hl') (SectionNine.blockProjF T Blk)
        (SectionNine.blockProjF_compat T Blk) rhoCocycle.1.1 rhoHV (fun g ↦ rfl)
        (h1OfVQuot hcomp x))
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) rhoM,
        SectionEight.sign (QZero (EnD.descData l h) rhoM cc)
      = (Nat.card EnD.Vmod : ℤ)
          * ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) rhoM smul_zmodTwo x) :=
        gaussZ_reduction smul_zmodTwo hfix
    _ = (Nat.card EnD.Vmod : ℤ) * ((2 : ℤ) ^ (FP.n * m)) := by rw [hQbar]

end CompatibleHeadInflated

/-- Reindex a tame quotient along the parameter modulus equality. -/
noncomputable def tameAtParams {K : IntermediateField ℚ_[2] ℚ̄₂}
    (params : FieldParameters) {q : ℕ}
    (hq : params.qK = q) (tame : ContinuousMonoidHom (GalK K) (Tq q)) :
    ContinuousMonoidHom (GalK K) (Tq params.qK) :=
  hq.symm ▸ tame

section CompatibleDeterminant

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The field-side affine determinant certificate from compatibility-aware ramified data. -/
theorem affineDeterminant_galK_compatible
    (params : FieldParameters) {n q : ℕ} {PG : ProfiniteGrp}
    {nuP : ContinuousMonoidHom PG Ztwo} {SN : SourceNumerics n}
    (params_n : params.n = n) (params_qK : params.qK = q)
    (hdeg : Module.finrank ℚ_[2] K = n)
    (hgu : ∀ m : ℕ, SN.gaussUnram m = (-1 : ℤ) ^ n * 2 ^ (n * m))
    (hgr : ∀ m : ℕ, SN.gaussRam m = (2 : ℤ) ^ (n * m))
    (tame : ContinuousMonoidHom (GalK K) (Tq q))
    (htame : Function.Surjective tame)
    (pro2 : ContinuousMonoidHom (GalK K) PG)
    (compat : ∀ g : GalK K, nuTq q (tame g) = nuP (pro2 g))
    (ramifiedData : CompatibleRamifiedDataAt params (GalKsub K)
      (tameAtParams params params_qK tame)) :
    AffineDeterminantCertificate (galKProfinite K) n q PG nuP SN tame pro2 compat
      (smulZmod2GalK K) := by
  subst params_qK
  subst params_n
  haveI : Finite (AbsGalQ2 ⧸ GalKsub K) :=
    finite_quotient_of_isOpen (GalKsub K) (isOpen_fixingSubgroup K)
  letI dmMu : DistribMulAction (↑(GalKsub K)) (MuN 2) := inferInstance
  haveI csMu : ContinuousSMul (↑(GalKsub K)) (MuN 2) :=
    ⟨Continuous.comp (continuous_smul (M := AbsGalQ2) (X := MuN 2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  have hidx : (GalKsub K).index = params.n :=
    (IntermediateField.finrank_eq_fixingSubgroup_index _ K).symm.trans hdeg
  constructor
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt
      m hm hcard l h hunram
    have key : GaussZResidueK (boundaryMapSub K tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h
        ((-1 : ℤ) ^ params.n * 2 ^ (params.n * m)) :=
      gaussZResidueDK_unramified (instDMAmu := dmMu) (instCSmu := csMu)
        T Blk params (GalKsub K) (isOpen_fixingSubgroup K) hidx
        (FieldData.tateDualityGalK K) hE2 hq0 hqe F tame htame
        (boundaryMapSub K tame pro2 compat) (fun _ ↦ rfl) hsimple hVne hnt m hm hcard l h hunram
    rw [hgu m]
    exact key
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt
      m hm hcard l h hram
    have key : GaussZResidueK (boundaryMapSub K tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h ((2 : ℤ) ^ (params.n * m)) :=
      gaussZResidueDK_ramified_compatible (instDMAmu := dmMu) (instCSmu := csMu)
        T Blk params (GalKsub K) (isOpen_fixingSubgroup K) hidx
        (FieldData.tateDualityGalK K) hE2 hq0 hqe F tame htame
        (boundaryMapSub K tame pro2 compat) (fun _ ↦ rfl) ramifiedData hsimple hVne hnt m hm
        hcard l h hram
    rw [hgr m]
    exact key

end CompatibleDeterminant

section CompatibleSource

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {T : OrientedTameQuotientK B FF} {n : ℕ} {P : ProfiniteGrp}
  {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}

/-- The corrected arithmetic source assembled from compatibility-aware ramified data. -/
noncomputable def KExactSupplyRN.toSourceRN_compatible
    (S : KExactSupplyRN T n P hP nuP)
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : CompatibleRamifiedDataAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK)) :
    SourceDataRN n (qOf K FF) P hP nuP (standardNumerics n) := by
  exact
    { Γ := galKProfinite K
      tame := T.tameFK
      pro2 := S.pro2
      compat := fun g ↦ T.compatF_K S.pro2 nuP S.nu_compat g
      surj := boundary_jointly_surjective_of_maxProP (qOf_ne_zero K FF) (even_qOf K FF) nuP
        T.tameFK S.pro2 T.tameFK_surjective S.hpro2 S.ker_pro2
        (fun g ↦ T.compatF_K S.pro2 nuP S.nu_compat g)
      ker_pro2 := S.ker_pro2
      smulZmod2 := smulZmod2GalK K
      contSMulZmod2 := contSMulZmod2GalK K
      htriv := htriv_galK K
      tfg := tfg_galK K
      exactLifting := S.exactLifting
      stokes := stokesDualityCertificate_galK K S.hdeg
      scalar := scalarHilbert_galK K S.hdeg rfl
      determinant := affineDeterminant_galK_compatible K params params_n params_qK S.hdeg
        (gaussUnram_standard n) (gaussRam_standard n) T.tameFK T.tameFK_surjective S.pro2
        (fun g ↦ T.compatF_K S.pro2 nuP S.nu_compat g) ramifiedData }

end CompatibleSource

namespace LSquare

open GQ2.Dyadic.SqCore

section CompatibleOddL

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

namespace GammaLCorrectedArithmeticInput

/-- Package a corrected odd-`L` arithmetic input from compatibility-aware ramified data. -/
noncomputable def ofKExactSupplyRN_compatible
    {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF} {h : ℕ}
    (S : KExactSupplyRN T (2 * h + 1) (DSq h) (SqCore.isProP_DSq h)
      (Instances.LSquareCore.lNu h))
    (params : FieldParameters) (params_n : params.n = 2 * h + 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : CompatibleRamifiedDataAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K where
  source := S.toSourceRN_compatible params params_n params_qK ramifiedData
  equivGalK := ContinuousMulEquiv.refl (GalK K)
  tame_surjective := T.tameFK_surjective
  wild_isProP := T.ker_tameFK ▸ T.isProP
  degree_eq := S.hdeg

end GammaLCorrectedArithmeticInput

/-- The corrected odd-`L` arithmetic input from a marked core and compatible ramified data. -/
noncomputable def gammaLCorrectedArithmeticInput_of_markedCore_compatible
    {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h))
    (ramifiedData : CompatibleRamifiedDataAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.tameFK)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K :=
  GammaLCorrectedArithmeticInput.ofKExactSupplyRN_compatible
    (kExactSupplyRN_of_markedCore (T := T) hdeg M.pro2 M.pro2_surjective M.ker_pro2 M.nu_compat)
    D.params (by rw [D.degree_eq]; exact hdeg) D.qK_eq_qOf ramifiedData

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- Odd-`L` reconstruction over a marked core and only compatible ramified data. -/
theorem gammaR_lSq_equiv_galK_of_realization_compatible
    (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h))
    (ramifiedData : CompatibleRamifiedDataAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.tameFK)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  lSq_candidate_equiv_galK_of_supplyRN
    (wordCertificateRN_lSq_qOf FF (odd_residueDegree_of_odd_finrank D
      (Nat.odd_iff.mpr (by omega))) h)
    (gammaLCorrectedArithmeticInput_of_markedCore_compatible T D hdeg M ramifiedData)
    (two_le_qOf K FF) (even_qOf K FF)

/-- The uniform odd-`L` classification using only the compatible ramified certificate surface. -/
theorem gammaR_lSq_equiv_galK_oddDegree_compatible
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (ramifiedData : CompatibleRamifiedDataAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.tameFK)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) := by
  obtain ⟨M⟩ := markedCoreRealization_of_supply B h (gOdd_nuClear h)
    (gUni_supply B FF hdeg)
  exact gammaR_lSq_equiv_galK_of_realization_compatible B T D hdeg M ramifiedData

end CompatibleOddL

end LSquare

#print axioms gaussZResidueDK_ramified_compatible
#print axioms CompatibleRamifiedDataAt
#print axioms affineDeterminant_galK_compatible
#print axioms tameAtParams
#print axioms KExactSupplyRN.toSourceRN_compatible
#print axioms LSquare.GammaLCorrectedArithmeticInput.ofKExactSupplyRN_compatible
#print axioms LSquare.gammaLCorrectedArithmeticInput_of_markedCore_compatible
#print axioms LSquare.gammaR_lSq_equiv_galK_of_realization_compatible
#print axioms LSquare.gammaR_lSq_equiv_galK_oddDegree_compatible

end GQ2.Dyadic
