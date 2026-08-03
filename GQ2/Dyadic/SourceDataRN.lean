/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Recursion.InputsRN

/-!
# Corrected degree-indexed source and word-certificate records

`SourceDataN` and `WordCertificate` are frozen public APIs.  This file adds safe `RN`
companions.  The boundary, scalar, Stokes, determinant, and M-stage content is unchanged.  The
only mathematical change is that the R-stage clause comes from `ExactLiftingSemanticsRN`, hence
has coefficient `zRN RF SN`.

The analytic clauses are bundled by the same certificate predicates already used by
`WordCertificate`; namespace projections expose the familiar `SourceDataN` leaf API.  At
`n = 1` and `standardNumerics 1`, explicit conversions in both directions are available and
the corrected coefficient reduces definitionally to the frozen one.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec

set_option linter.unusedVariables false in
/-- The corrected degree-indexed source.  Compared with `SourceDataN`, the unique changed
clause is `exactLifting.2.2`, whose coefficient is `zRN RF SN`. -/
structure SourceDataRN (n q : ℕ) (P : ProfiniteGrp) (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n) where
  Γ : ProfiniteGrp
  tame : ContinuousMonoidHom Γ (Tq q)
  pro2 : ContinuousMonoidHom Γ P
  compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g)
  surj : Function.Surjective
    (fun g : Γ => (⟨(tame g, pro2 g), compat g⟩ : ↥(boundarySubgroupQ q nuP)))
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 Γ
  smulZmod2 : DistribMulAction ↥Γ (ZMod 2)
  contSMulZmod2 : letI := smulZmod2; ContinuousSMul ↥Γ (ZMod 2)
  htriv : letI := smulZmod2; ∀ (γ : ↥Γ) (m : ZMod 2), γ • m = m
  tfg : ∃ s : Finset (Γ : Type),
    (Subgroup.closure (s : Set (Γ : Type))).topologicalClosure = ⊤
  exactLifting : ExactLiftingSemanticsRN Γ n q P nuP SN
  stokes : StokesDualityCertificate Γ n q P nuP SN smulZmod2
  scalar : ScalarHilbertCertificate Γ n SN smulZmod2
  determinant : AffineDeterminantCertificate Γ n q P nuP SN tame pro2 compat smulZmod2

namespace SourceDataRN

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
  (S : SourceDataRN n q P hP nuP SN)

/-- The corrected source's boundary map. -/
noncomputable def b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP) :=
  sourceBoundaryMapK S.tame S.pro2 S.compat

@[simp] theorem b_apply_coe (g : S.Γ) : (S.b g : Tq q × P) = (S.tame g, S.pro2 g) := rfl

theorem b_surjective : Function.Surjective S.b := S.surj

theorem pro2_surjective : Function.Surjective S.pro2 := fun p => by
  obtain ⟨t, ht⟩ := nuTq_surjective q (nuP p)
  obtain ⟨g, hg⟩ := S.surj ⟨(t, p), ht⟩
  exact ⟨g, congrArg (fun x : ↥(boundarySubgroupQ q nuP) => x.val.2) hg⟩

/-! The familiar source-clause surface, projected from the four unchanged certificate bundles. -/

theorem homCard :
    Nat.card (ContinuousMonoidHom S.Γ (Multiplicative (ZMod 2))) = SN.homScalar := S.scalar.1

theorem cardH2 : letI := S.smulZmod2; Nat.card (H2 S.Γ (ZMod 2)) = 2 := S.scalar.2

theorem liftsOver_card : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC),
    Nat.card (LiftsOverK RF b F ρ) = SN.mMult (Nat.card ↥RF.MB) := S.exactLifting.1

theorem lem86 : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg), D.NoDescent →
    ∀ (ρ : ContinuousMonoidHom S.Γ (Bg ⧸ D.M)), Function.Surjective ρ →
      2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  S.exactLifting.2.1

set_option linter.unusedVariables false in
theorem stageR136 : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E),
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = zRN (blockFrameImpl T Blk hE2) SN
          * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
            (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
              - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) :=
  S.exactLifting.2.2

theorem tcocycle_card : letI := S.smulZmod2; ∀ {H E : Type}
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC),
    Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      = SN.tMult (Nat.card (Additive ↥(En.radData l h).T))
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T))) := S.stokes.1

theorem hsep : letI := S.smulZmod2; ∀ {H E : Type}
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)),
    (∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
      TLiftable (descSigma_spec En l h Dsc) c := S.stokes.2.1

theorem hpartial : letI := S.smulZmod2; ∀ {H E : Type}
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))), χ ≠ 0 →
    ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) :=
  S.stokes.2.2.1

theorem hZcard : letI := S.smulZmod2; ∀ {H E : Type}
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ v : En.Vmod, v ≠ 0) →
    (∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) →
    ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * SN.h1Mult (Nat.card En.Vmod) := S.stokes.2.2.2

/-! ### Exact degree-one conversions -/

/-- Forget the corrected wrapper at degree one.  The R-stage target reduces to the frozen one. -/
noncomputable def toSourceDataNStandardOne
    (S : SourceDataRN 1 q P hP nuP (standardNumerics 1)) :
    SourceDataN 1 q P hP nuP (standardNumerics 1) where
  Γ := S.Γ
  tame := S.tame
  pro2 := S.pro2
  compat := S.compat
  surj := S.surj
  ker_pro2 := S.ker_pro2
  smulZmod2 := S.smulZmod2
  contSMulZmod2 := S.contSMulZmod2
  htriv := S.htriv
  tfg := S.tfg
  homCard := S.scalar.1
  cardH2 := S.scalar.2
  liftsOver_card := S.exactLifting.1
  lem86 := S.exactLifting.2.1
  stageR136 := ((exactLiftingSemanticsRN_standard_one_iff _ _ _ _).mp S.exactLifting).2.2
  tcocycle_card := S.stokes.1
  hsep := S.stokes.2.1
  hpartial := S.stokes.2.2.1
  hZcard := S.stokes.2.2.2
  gaussZ_unramified := S.determinant.1
  gaussZ_ramified := S.determinant.2

/-- Every frozen degree-one source has a corrected companion. -/
noncomputable def ofSourceDataNStandardOne
    (S : SourceDataN 1 q P hP nuP (standardNumerics 1)) :
    SourceDataRN 1 q P hP nuP (standardNumerics 1) where
  Γ := S.Γ
  tame := S.tame
  pro2 := S.pro2
  compat := S.compat
  surj := S.surj
  ker_pro2 := S.ker_pro2
  smulZmod2 := S.smulZmod2
  contSMulZmod2 := S.contSMulZmod2
  htriv := S.htriv
  tfg := S.tfg
  exactLifting := exactLiftingSemanticsRN_standard_one_iff _ _ _ _ |>.mpr
    ⟨S.liftsOver_card, S.lem86, S.stageR136⟩
  stokes := ⟨S.tcocycle_card, S.hsep, S.hpartial, S.hZcard⟩
  scalar := ⟨S.homCard, S.cardH2⟩
  determinant := ⟨S.gaussZ_unramified, S.gaussZ_ramified⟩

@[simp] theorem toSourceDataNStandardOne_ofSourceDataNStandardOne
    (S : SourceDataN 1 q P hP nuP (standardNumerics 1)) :
    (ofSourceDataNStandardOne S).toSourceDataNStandardOne = S := by
  cases S
  rfl

@[simp] theorem ofSourceDataNStandardOne_toSourceDataNStandardOne
    (S : SourceDataRN 1 q P hP nuP (standardNumerics 1)) :
    ofSourceDataNStandardOne S.toSourceDataNStandardOne = S := by
  cases S
  rfl

end SourceDataRN

set_option linter.unusedVariables false in
/-- Corrected word certificate.  It is field-for-field the frozen certificate except that
`exactLifting` has type `ExactLiftingSemanticsRN`. -/
structure WordCertificateRN (n q : ℕ) (R : PWord (Generator n)) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n) where
  tameSpecialization : TameSpecializes n q R
  coreRel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G], Marking n G → G
  proTwoWord : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G),
    t.eval (pro2 R) = coreRel G t
  pro2 : ContinuousMonoidHom ((GammaR n q R) : Type) P
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 ((GammaR n q R) : Type)
  hpro2 : Function.Surjective pro2
  compat : ∀ g : ((GammaR n q R) : Type),
    nuTq q (tameOfSpec n q R tameSpecialization g) = nuP (pro2 g)
  tfg : ∃ s : Finset ((GammaR n q R) : Type),
    (Subgroup.closure (s : Set ((GammaR n q R) : Type))).topologicalClosure = ⊤
  smulZmod2 : DistribMulAction ↥(GammaR n q R) (ZMod 2)
  contSMulZmod2 : letI := smulZmod2; ContinuousSMul ↥(GammaR n q R) (ZMod 2)
  htriv : letI := smulZmod2; ∀ (γ : ↥(GammaR n q R)) (m : ZMod 2), γ • m = m
  exactLifting : ExactLiftingSemanticsRN (GammaR n q R) n q P nuP SN
  stokes : StokesDualityCertificate (GammaR n q R) n q P nuP SN smulZmod2
  scalar : ScalarHilbertCertificate (GammaR n q R) n SN smulZmod2
  determinant : AffineDeterminantCertificate (GammaR n q R) n q P nuP SN
    (tameOfSpec n q R tameSpecialization) pro2 compat smulZmod2
  htame : Function.Surjective (tameOfSpec n q R tameSpecialization)
  hwild : IsProP 2 (tameOfSpec n q R tameSpecialization).toMonoidHom.ker

namespace WordCertificateRN

variable {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- Assemble the corrected candidate source directly from the corrected certificate. -/
noncomputable def toSourceRN (W : WordCertificateRN n q R P hP nuP SN)
    (hq2 : 2 ≤ q) (hqe : Even q) : SourceDataRN n q P hP nuP SN where
  Γ := GammaR n q R
  tame := tameOfSpec n q R W.tameSpecialization
  pro2 := W.pro2
  compat := W.compat
  surj := boundary_jointly_surjective_of_maxProP (by omega) hqe nuP _ W.pro2 W.htame W.hpro2
    W.ker_pro2 W.compat
  ker_pro2 := W.ker_pro2
  smulZmod2 := W.smulZmod2
  contSMulZmod2 := W.contSMulZmod2
  htriv := W.htriv
  tfg := W.tfg
  exactLifting := W.exactLifting
  stokes := W.stokes
  scalar := W.scalar
  determinant := W.determinant

end WordCertificateRN

namespace WordCertificateRN

variable {q : ℕ} {R : PWord (Generator 1)} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo}

/-- Convert a corrected degree-one word certificate to the frozen certificate API. -/
noncomputable def toWordCertificateStandardOne
    (W : WordCertificateRN 1 q R P hP nuP (standardNumerics 1)) :
    WordCertificate 1 q R P hP nuP (standardNumerics 1) where
  tameSpecialization := W.tameSpecialization
  coreRel := W.coreRel
  proTwoWord := W.proTwoWord
  pro2 := W.pro2
  ker_pro2 := W.ker_pro2
  hpro2 := W.hpro2
  compat := W.compat
  tfg := W.tfg
  smulZmod2 := W.smulZmod2
  contSMulZmod2 := W.contSMulZmod2
  htriv := W.htriv
  exactLifting := (exactLiftingSemanticsRN_standard_one_iff _ _ _ _).mp W.exactLifting
  stokes := W.stokes
  scalar := W.scalar
  determinant := W.determinant
  htame := W.htame
  hwild := W.hwild

/-- Promote a frozen degree-one word certificate to the corrected API. -/
noncomputable def ofWordCertificateStandardOne
    (W : WordCertificate 1 q R P hP nuP (standardNumerics 1)) :
    WordCertificateRN 1 q R P hP nuP (standardNumerics 1) where
  tameSpecialization := W.tameSpecialization
  coreRel := W.coreRel
  proTwoWord := W.proTwoWord
  pro2 := W.pro2
  ker_pro2 := W.ker_pro2
  hpro2 := W.hpro2
  compat := W.compat
  tfg := W.tfg
  smulZmod2 := W.smulZmod2
  contSMulZmod2 := W.contSMulZmod2
  htriv := W.htriv
  exactLifting := (exactLiftingSemanticsRN_standard_one_iff _ _ _ _).mpr W.exactLifting
  stokes := W.stokes
  scalar := W.scalar
  determinant := W.determinant
  htame := W.htame
  hwild := W.hwild

@[simp] theorem toWordCertificateStandardOne_ofWordCertificateStandardOne
    (W : WordCertificate 1 q R P hP nuP (standardNumerics 1)) :
    (ofWordCertificateStandardOne W).toWordCertificateStandardOne = W := by
  cases W
  rfl

@[simp] theorem ofWordCertificateStandardOne_toWordCertificateStandardOne
    (W : WordCertificateRN 1 q R P hP nuP (standardNumerics 1)) :
    ofWordCertificateStandardOne W.toWordCertificateStandardOne = W := by
  cases W
  rfl

/-- The source assembly square commutes at degree one. -/
theorem toSourceRN_standard_one_toSourceDataN (W : WordCertificateRN 1 q R P hP nuP
    (standardNumerics 1)) (hq2 : 2 ≤ q) (hqe : Even q) :
    (W.toSourceRN hq2 hqe).toSourceDataNStandardOne =
      W.toWordCertificateStandardOne.toSource hq2 hqe := by
  rfl

end WordCertificateRN
end GQ2.Dyadic
