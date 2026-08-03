/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.LocalDuality
import GQ2.Dyadic.Instances.GammaLDualityBoundary
import GQ2.Dyadic.Instances.KSupply
import GQ2.Dyadic.GaussZ.FinalDK
import GQ2.Dyadic.SourceDataRN

/-!
# Arithmetic analytic certificates from local duality

The Stokes fields are assembled from `GQ2.Dyadic.Count.LocalDuality`.  The corrected R-stage
section additionally ports the legacy `AbsGalQ2` hom-lift argument to an arbitrary profinite
source, isolating its sole arithmetic input as Tate `(2,0)` separation, and specializes it to
`G_K`.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open LiftingDualityG

/-- A Tate-duality bundle plus the degree-`d` local Euler characteristic supplies the complete
arithmetic Stokes package.  The scalar continuity proof is explicit because the certificate
stores its scalar action as data rather than as a global instance. -/
theorem stokesDualityCertificate_of_localDualityG
    {Gam : ProfiniteGrp} {d q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    [DistribMulAction (Gam : Type) (MuN 2)] [ContinuousSMul (Gam : Type) (MuN 2)]
    (Dl : TateDualityG (Gam : Type) 2) (hE : LocalEulerChar (Gam : Type) d)
    (smulZ2 : DistribMulAction (Gam : Type) (ZMod 2))
    (contZ2 : letI := smulZ2; ContinuousSMul (Gam : Type) (ZMod 2))
    (htriv : letI := smulZ2; ∀ (gam : (Gam : Type)) (m : ZMod 2), gam • m = m) :
    StokesDualityCertificate Gam d q P nuP (standardNumerics d) smulZ2 :=
  ⟨fun b F En l h rho => Count.tcocycle_field_of_localDualityG Dl hE b F En l h rho,
   fun b F En l h Dsc rho c hc =>
    Count.hsep_field_of_localDualityG Dl smulZ2 contZ2 htriv
      b F En l h Dsc rho c hc,
   fun b F En l h Dsc rho chi hchi =>
    Count.hpartial_field_of_localDualityG Dl smulZ2 contZ2 htriv
      b F En l h Dsc rho chi hchi,
   fun b F En l h hsimple hVne hnt rho =>
    Count.hZcard_field_of_localDualityG Dl hE b F En l h hsimple hVne hnt rho⟩

/-! ## The arithmetic specialization

The local instances below deliberately live at the subtype spelling `GalK K`.  This is the
same carrier as `↥(galKProfinite K)`, but asking typeclass search to discover that through the
bundled profinite topology leads to the instance-path blow-up documented in
`docs/dyadic/followup/stokes-galk-status.md`.  We therefore elaborate the generic certificate
entirely on the subtype side and cross the definitional equality only at the conclusion.
-/

section GalK

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The degree-index form of the local Euler characteristic, kept at the subtype spelling of
`G_K`.  Naming this rewrite prevents the large Stokes record from being present while Lean
normalizes the two degree expressions. -/
theorem localEulerChar_galK_of_finrank {n : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = n) :
    LiftingDualityG.LocalEulerChar (GalK K) n := by
  have h := LiftingDualityG.localEulerChar_galK K
  have hidx : (GalKsub K).index = n :=
    (IntermediateField.finrank_eq_fixingSubgroup_index K).symm.trans hdeg
  rwa [hidx] at h

/-- **The complete Stokes-duality certificate at `G_K`.**

This is assembly-only: B6 supplies `FieldData.tateDualityGalK`, the Shapiro-derived local Euler
characteristic supplies the degree count, and the scalar action, its continuity, and triviality
are the already registered `KSupply` terms. -/
theorem stokesDualityCertificate_galK
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n) :
    StokesDualityCertificate (galKProfinite K) n q P nuP
      (standardNumerics n) (smulZmod2GalK K) := by
  -- Pin both `μ₂` instances on the subtype path before the generic theorem is elaborated.
  letI dmMu : DistribMulAction (GalK K) (MuN 2) := inferInstance
  haveI csMu : ContinuousSMul (GalK K) (MuN 2) :=
    ⟨Continuous.comp (continuous_smul (M := AbsGalQ2) (X := MuN 2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  let Dl : TateDualityG (GalK K) 2 := FieldData.tateDualityGalK K
  let hE : LiftingDualityG.LocalEulerChar (GalK K) n :=
    localEulerChar_galK_of_finrank K hdeg
  have key :
      StokesDualityCertificate (ProfiniteGrp.of (GalK K)) n q P nuP
        (standardNumerics n) (smulZmod2GalK K) :=
    @stokesDualityCertificate_of_localDualityG
      (ProfiniteGrp.of (GalK K)) n q P nuP dmMu csMu Dl hE
      (smulZmod2GalK K) (contSMulZmod2GalK K) (htriv_galK K)
  exact key

end GalK

/-! ## The residual arithmetic supply

`KSupply` predates the generic local-duality and determinant bridges, so it stores their
conclusions as two opaque fields.  The record below is the smaller constructor interface after
those bridges have landed.  Its only analytic field is `exactLifting`: the Stokes and determinant
packages are reconstructed in `toKSupply` from local duality and the standard packet inputs.

| old `KSupply` payload | `KExactSupply` status | supplier |
|---|---|---|
| pro-`2` quotient and orientation | stored | marked-core branch |
| `ExactLiftingSemantics` | stored | word/presentation branch |
| `StokesDualityCertificate` | derived | `stokesDualityCertificate_galK` |
| `AffineDeterminantCertificate` | derived | `affineDeterminant_galK` |

The restriction to `standardNumerics n` is intentional: it eliminates all numerical pin
hypotheses, and it is the slot used by every arbitrary-`K` presentation row.
-/

section ResidualSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The genuine residual data needed to construct the arithmetic source at `G_K`.

The four pro-`2` fields are branch arithmetic.  `exactLifting` remains word-specific: its lift
count needs an admissible presentation and resolver, its half-torsor clause needs a nonzero
variation class, and its stage clause needs the corresponding variation/separation inputs.
Neither local duality nor the Gauss bridge manufactures those data. -/
structure KExactSupply (T : OrientedTameQuotientK B FF) (n : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  /-- The degree of the shared standard-numerics slot. -/
  hdeg : Module.finrank ℚ_[2] K = n
  /-- The standard core coordinate. -/
  pro2 : ContinuousMonoidHom (GalK K) P
  /-- Surjectivity of the standard core coordinate. -/
  hpro2 : Function.Surjective pro2
  /-- The coordinate is the maximal pro-`2` quotient. -/
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K)
  /-- Compatibility with the oriented unramified coordinate. -/
  nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g)
  /-- The only remaining analytic residue. -/
  exactLifting : ExactLiftingSemantics (galKProfinite K) n (qOf K FF) P nuP
    (standardNumerics n)

namespace KExactSupply

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {T : OrientedTameQuotientK B FF} {n : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo}

/-- Upgrade the genuine residual data to the legacy `KSupply` interface.

No Stokes or determinant conclusion is assumed: local duality constructs the former, while the
field packet's existing `ramifiedData` input and the signed Gauss bridge construct the latter.
-/
noncomputable def toKSupply (S : KExactSupply T n P hP nuP) (params : FieldParameters)
    (params_n : params.n = n) (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    KSupply T n P hP nuP (standardNumerics n) where
  hdeg := S.hdeg
  hhom := rfl
  pro2 := S.pro2
  hpro2 := S.hpro2
  ker_pro2 := S.ker_pro2
  nu_compat := S.nu_compat
  exactLifting := S.exactLifting
  stokes := stokesDualityCertificate_galK K S.hdeg
  determinant := affineDeterminant_galK K params params_n params_qK S.hdeg
    (gaussUnram_standard n) (gaussRam_standard n) T.tameFK T.tameFK_surjective S.pro2
    (fun g => T.compatF_K S.pro2 nuP S.nu_compat g) ramifiedData

/-- Regression theorem: a word certificate and the residual arithmetic supply suffice for the
presentation theorem.  In particular, there are no arithmetic-side Stokes or determinant
binders in this statement. -/
theorem candidate_equiv_galK_of_exactSupply {Rw : PWord (Generator n)}
    (W : WordCertificate n (qOf K FF) Rw P hP nuP (standardNumerics n))
    (S : KExactSupply T n P hP nuP) (params : FieldParameters)
    (params_n : params.n = n) (params_qK : params.qK = qOf K FF)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (V : Type) [AddCommGroup V] [DistribMulAction Dg V]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : V, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V cc rho))
    (hnuP : Function.Surjective nuP) :
    Nonempty (ContinuousMulEquiv ((candidateGroup n (qOf K FF) Rw : Type)) (GalK K)) :=
  candidate_equiv_galK_of_supply W
    (S.toKSupply params params_n params_qK ramifiedData)
    params params_n params_qK ramified ramifiedData hnuP

end KExactSupply

end ResidualSupply

/-! ## The corrected arithmetic supply

The corrected recursion changes only the coefficient in the R-stage identity.  The record below
is therefore the `RN` analogue of `KExactSupply`: the marked pro-2 block is unchanged and the
single analytic field has type `ExactLiftingSemanticsRN`.

For comparison with the legacy arithmetic campaign, `CorrectedRStageSemantics` names precisely
the changed third conjunct.  `KExactSupplyRN.ofKExactSupply` reuses the first two legacy exact
lifting clauses and asks only for this corrected R-stage clause.
-/

section CorrectedResidualSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The genuinely changed arithmetic clause: equation (136) with the degree-indexed `zRN`
coefficient.  The lift count and half-torsor clauses are byte-for-byte the legacy ones. -/
def CorrectedRStageSemantics (Γ : ProfiniteGrp) (n q : ℕ) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (_hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (_hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E),
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T =
      zRN (blockFrameImpl T Blk hE2) SN *
        ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ) -
            exactImageCountK b F (blockFrameImpl T Blk hE2).TB)

/-- The two concrete R-stage facts not contained in the existing Stokes or affine-determinant
certificates at `G_K`.  Once these are supplied, `blockStageR136NK` performs the corrected
equation-(136) assembly; scalar `H²`, triviality, and finite generation are already theorems. -/
structure CorrectedRStageResiduesGalK (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (n q : ℕ) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  hsep_hom : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (_hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (_hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB),
    obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
        (htriv_galK K) (card_H2_zmodTwo_galK K) g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom (galKProfinite K) Y,
        ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ
  hZcount : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (_hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (_hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (f₀ : BoundaryLiftsK b F T),
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) =
      zRN (blockFrameImpl T Blk hE2) SN

/-- The corrected R-cocycle count at `G_K`.  This is the degree-`n` version of
`RStageLocal.hZcount_local`: the multiplicative cocycles are identified with continuous
`Z¹(G_K, R)`, and `card_Z1_eqG` supplies the exponent `n + 1`. -/
theorem correctedRStage_hZcount_galK
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = n)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (f₀ : BoundaryLiftsK b F T) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) =
      zRN (blockFrameImpl T Blk hE2) (standardNumerics n) := by
  classical
  let G : Type := ((galKProfinite K : ProfiniteGrp) : Type)
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  set θ : ContinuousMonoidHom (galKProfinite K) (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
      show Continuous fun γ => QuotientGroup.mk' Blk.K (f₀.1.1 γ)
      exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := f₀.1.2 y
    exact ⟨γ, by show QuotientGroup.mk' Blk.K (f₀.1.1 γ) = c; rw [hγ, hy]⟩
  letI actG : DistribMulAction G (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := inferInstance
  haveI csR : ContinuousSMul G (Additive ↥Blk.frattiniK) := by
    refine ⟨?_⟩
    have hfac : (fun p : G × Additive ↥Blk.frattiniK => p.1 • p.2) =
        (fun p : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => p.1 • p.2) ∘
          (fun p : G × Additive ↥Blk.frattiniK => (θ p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcomp : ∀ (γ : G) (a : Additive ↥Blk.frattiniK), γ • a = θ γ • a :=
    fun _ _ => rfl
  have hA2 : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 :=
    RStageLocal.frattiniK_add_self hRK hR2
  have hsmul : ∀ (γ : G) (a : Additive ↥Blk.frattiniK), γ • a = Additive.ofMul
      (⟨f₀.1.1 γ * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * (f₀.1.1 γ)⁻¹,
        RStageLocal.conj_mem_R (f₀.1.1 γ) (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro γ a
    have h1 : γ • a = (QuotientGroup.mk' Blk.K (f₀.1.1 γ) : Y ⧸ Blk.K) •
        Additive.ofMul (Additive.toMul a) := rfl
    rw [h1]
    exact RStageLocal.conjC_smul_of_mk hRK (f₀.1.1 γ) (Additive.toMul a)
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f₀.1.1 ≃
      ↥(Z1 G (Additive ↥Blk.frattiniK)) :=
    { toFun := fun c =>
        ⟨fun γ => Additive.ofMul ⟨c.u γ, c.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun γ => (⟨c.u γ, c.mem γ⟩ : ↥Blk.frattiniK)
            exact Continuous.subtype_mk c.cont _
          · intro γ δ
            rw [hsmul γ (Additive.ofMul ⟨c.u δ, c.mem δ⟩)]
            refine Additive.toMul.injective (Subtype.ext ?_)
            exact c.crossed γ δ⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥Blk.frattiniK) : Y)
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := continuous_subtype_val.comp (mem_Z1_iff.mp z.2).1
          crossed := by
            intro γ δ
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ (z.1 δ)] at hz
            have := congrArg
              (fun a => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) hz
            simpa using this }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun γ => rfl) }
  let e : G ≃ₜ* GalK K := ContinuousMulEquiv.refl (GalK K)
  letI dmTarget : DistribMulAction (GalK K) (MuN 2) := inferInstance
  have hcontTarget : Continuous fun p : (GalK K) × MuN 2 => p.1 • p.2 := continuous_smul
  letI dmMu : DistribMulAction G (MuN 2) :=
    DistribMulAction.compHom _ e.toMonoidHom
  haveI csMu : ContinuousSMul G (MuN 2) :=
    ⟨hcontTarget.comp ((e.continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩
  haveI : (GalKsub K).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  let Dl : TateDualityG G 2 := LSquare.tateDualityG_two_of_equiv e
    (subgroup_isLocalDualizingGroup 2 (GalKsub K) (isOpen_fixingSubgroup K))
  let hEuler : LocalEulerChar G n := LocalEulerChar.congr e
    (localEulerChar_galK_of_finrank K hdeg)
  have key : Nat.card (Z1 G (Additive ↥Blk.frattiniK)) =
      Nat.card (Additive ↥Blk.frattiniK) ^ (n + 1) *
        Nat.card (GQ2.FoxH.fixedPts (Y ⧸ Blk.K)
          (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK))) :=
    card_Z1_eqG (Γ := G) (C := Y ⧸ Blk.K) (ρ := θ)
      (A := Additive ↥Blk.frattiniK) hθs hcomp Dl hEuler hA2
  rw [Nat.card_congr hequiv, key,
    RStageLocal.card_fixedPts_eq_card_RCharSub hRK, blockRChar_card T Blk hE2,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK)), zRN]
  rfl

/-! ### Generic R-stage separation

The legacy `RStageLocal.hsep_hom_local` proof is tied syntactically to `AbsGalQ2`, although its
only arithmetic step is left separation of the Tate `(2,0)` cup pairing.  The theorem below
ports the group-theoretic construction to an arbitrary profinite source and obtains precisely
that step from `Count.isTwoSeparating_of_tateDualityG`. -/

/-- Vanishing of the R-stage obstruction lifts a surjective boundary map to `Y` over any
profinite source carrying Tate duality at `2`.

The scalar action and cardinality equality are explicit because they occur in the obstruction
API.  The actual separation step uses only `Dl`; in particular it does not use a local Euler
characteristic. -/
theorem rStage_hsep_hom_of_tateDualityG
    {Gam : ProfiniteGrp} {q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    [DistribMulAction (Gam : Type) (MuN 2)] [ContinuousSMul (Gam : Type) (MuN 2)]
    (Dl : TateDualityG (Gam : Type) 2)
    (smulZ2 : DistribMulAction (Gam : Type) (ZMod 2))
    (contZ2 : letI := smulZ2; ContinuousSMul (Gam : Type) (ZMod 2))
    (htriv : letI := smulZ2;
      ∀ (gam : (Gam : Type)) (m : ZMod 2), gam • m = m)
    (hcard : letI := smulZ2; Nat.card (H2 (Gam : Type) (ZMod 2)) = 2)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
      htriv hcard g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom Gam Y,
      ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ := by
  classical
  let G : Type := Gam
  letI := smulZ2
  haveI : ContinuousSMul G (ZMod 2) := contZ2
  -- The obstruction functional kills every paired scalar defect class.
  have hall : ∀ d : (blockRObstructionData T Blk hE2).DRmod,
      H2mk G (ZMod 2)
        ⟨fun gd => (blockRObstructionData T Blk hE2).pair d
            (Additive.ofMul
              (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)),
          pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2)
            (blockRObstructionData T Blk hE2) htriv g.1.1 d⟩ = 0 := by
    intro d
    by_cases hd : (blockRObstructionData T Blk hE2).toDR d =
        (blockFrameImpl T Blk hE2).zeroDR
    · have hd0 : d = 0 := by
        rw [← (blockRObstructionData T Blk hE2).h0, ← hd, Equiv.symm_apply_apply]
      subst hd0
      have hz : (⟨fun gd => (blockRObstructionData T Blk hE2).pair 0
          (Additive.ofMul
            (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)),
          pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2)
            (blockRObstructionData T Blk hE2) htriv g.1.1 0⟩ :
          ↥(Z2 G (ZMod 2))) = 0 := by
        apply Subtype.ext
        funext gd
        simp only [map_zero, AddMonoidHom.zero_apply]
        rfl
      rw [hz, map_zero]
    · exact (obs_zero_iff_pairClass_zero (blockFrameImpl T Blk hE2)
        (blockRObstructionData T Blk hE2) htriv hcard g.1.1 d hd).mp
          (LinearMap.congr_fun hg d)
  -- Pull the quotient-conjugation action on R back along the lower boundary map.
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  have hRleK : Blk.frattiniK ≤ Blk.K := SectionSeven.frattiniLike_le Blk.K
  set θ : ContinuousMonoidHom Gam (Y ⧸ Blk.K) :=
    ⟨MonoidHom.mk' (fun γ => QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))) (fun γ δ => by
      rw [← map_mul]
      apply (QuotientGroup.mk'_eq_mk' Blk.K).mpr
      refine ⟨(slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹
          * (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ : Y)
          * slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)),
        hRleK (by
          have hmem := (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem _
            (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ).2
            (slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹
          rwa [inv_inv] at hmem), ?_⟩
      show slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ))
          * ((slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
              * slift (blockFrameImpl T Blk hE2) (g.1.1 δ)
              * (slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹)
            * slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))
        = slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * slift (blockFrameImpl T Blk hE2) (g.1.1 δ)
      group), by
      show Continuous fun γ => QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))
      exact Continuous.comp continuous_of_discreteTopology
        (Continuous.comp continuous_of_discreteTopology g.1.1.continuous_toFun)⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := g.1.2 ((blockFrameImpl T Blk hE2).piB y)
    refine ⟨γ, ?_⟩
    show QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ)) = c
    rw [hγ, ← hy]
    apply (QuotientGroup.mk'_eq_mk' Blk.K).mpr
    have hker :
        (slift (blockFrameImpl T Blk hE2)
          ((blockFrameImpl T Blk hE2).piB y))⁻¹ * y ∈ Blk.frattiniK := by
      rw [← (blockFrameImpl T Blk hE2).ker_piB, MonoidHom.mem_ker, map_mul, map_inv,
        piB_slift]
      group
    exact ⟨(slift (blockFrameImpl T Blk hE2)
        ((blockFrameImpl T Blk hE2).piB y))⁻¹ * y, hRleK hker, by group⟩
  letI actG : DistribMulAction G (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := inferInstance
  haveI : ContinuousSMul G (Additive ↥Blk.frattiniK) := by
    refine ⟨?_⟩
    have hfac : (fun p : G × Additive ↥Blk.frattiniK => p.1 • p.2) =
        (fun p : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => p.1 • p.2) ∘
          (fun p : G × Additive ↥Blk.frattiniK => (θ p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA2 : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 :=
    RStageLocal.frattiniK_add_self hRK hR2
  have hsmul : ∀ (γ : G) (a : Additive ↥Blk.frattiniK), γ • a =
      Additive.ofMul
        (⟨slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * ((Additive.toMul a : ↥Blk.frattiniK) : Y)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))⁻¹,
          RStageLocal.conj_mem_R _ (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro γ a
    have h1 : γ • a = QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ)) •
          Additive.ofMul (Additive.toMul a) := rfl
    rw [h1]
    exact RStageLocal.conjC_smul_of_mk hRK _ (Additive.toMul a)
  have hdefZ2 : (fun p : G × G =>
      Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 p.1 p.2)) ∈
      Z2 G (Additive ↥Blk.frattiniK) := by
    refine mem_Z2_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun p : G × G =>
          (rDefect (blockFrameImpl T Blk hE2) g.1.1 p.1 p.2 : ↥Blk.frattiniK)
      apply Continuous.subtype_mk
      have hs : Continuous fun x : (blockFrameImpl T Blk hE2).YB =>
          slift (blockFrameImpl T Blk hE2) x := continuous_of_discreteTopology
      have h1 : Continuous fun p : G × G =>
          slift (blockFrameImpl T Blk hE2) (g.1.1 p.1) :=
        hs.comp (g.1.1.continuous_toFun.comp continuous_fst)
      have h2 : Continuous fun p : G × G =>
          slift (blockFrameImpl T Blk hE2) (g.1.1 p.2) :=
        hs.comp (g.1.1.continuous_toFun.comp continuous_snd)
      have h3 : Continuous fun p : G × G =>
          slift (blockFrameImpl T Blk hE2) (g.1.1 (p.1 * p.2)) :=
        hs.comp (g.1.1.continuous_toFun.comp continuous_mul)
      exact (h1.mul h2).mul h3.inv
    · intro γ δ ε
      rw [hsmul γ]
      apply Additive.toMul.injective
      show (⟨slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * (rDefect (blockFrameImpl T Blk hE2) g.1.1 δ ε : Y)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))⁻¹, _⟩ :
            ↥Blk.frattiniK) * rDefect (blockFrameImpl T Blk hE2) g.1.1 γ (δ * ε)
        = rDefect (blockFrameImpl T Blk hE2) g.1.1 (γ * δ) ε
          * rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ
      rw [mul_comm (rDefect (blockFrameImpl T Blk hE2) g.1.1 (γ * δ) ε)
        (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ)]
      apply Subtype.ext
      show slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * (rDefect (blockFrameImpl T Blk hE2) g.1.1 δ ε : Y)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))⁻¹
            * (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ (δ * ε) : Y)
        = (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ : Y)
          * (rDefect (blockFrameImpl T Blk hE2) g.1.1 (γ * δ) ε : Y)
      have hrd : ∀ α β : G,
          (rDefect (blockFrameImpl T Blk hE2) g.1.1 α β : Y) =
            slift (blockFrameImpl T Blk hE2) (g.1.1 α)
              * slift (blockFrameImpl T Blk hE2) (g.1.1 β)
              * (slift (blockFrameImpl T Blk hE2) (g.1.1 (α * β)))⁻¹ :=
        fun _ _ => rfl
      rw [hrd, hrd, hrd, hrd,
        show γ * (δ * ε) = γ * δ * ε from (mul_assoc γ δ ε).symm]
      group
  -- Tate `(2,0)` supplies the exact cup-free separation predicate.
  letI : TopologicalSpace (ElemDual (Additive ↥Blk.frattiniK)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥Blk.frattiniK)) := ⟨rfl⟩
  have hcompD : ∀ (γ : G) (lam : ElemDual (Additive ↥Blk.frattiniK)),
      γ • lam = θ γ • lam := by
    intro γ lam
    apply ElemDual.ext
    intro a
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    congr 1
    change θ γ⁻¹ • a = (θ γ)⁻¹ • a
    rw [map_inv]
  haveI : ContinuousSMul G (ElemDual (Additive ↥Blk.frattiniK)) := by
    refine ⟨?_⟩
    have hfac : (fun p : G × ElemDual (Additive ↥Blk.frattiniK) =>
        p.1 • p.2) =
        (fun p : (Y ⧸ Blk.K) × ElemDual (Additive ↥Blk.frattiniK) => p.1 • p.2) ∘
          (fun p => (θ p.1, p.2)) := by
      funext p
      exact hcompD p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hpair : ∀ (γ : G) (a : Additive ↥Blk.frattiniK)
      (lam : ElemDual (Additive ↥Blk.frattiniK)),
      dualEval _ (γ • a) (γ • lam) = γ • dualEval _ a lam := by
    intro γ a lam
    rw [dualEval_apply, ElemDual.smul_apply, inv_smul_smul, dualEval_apply,
      htriv]
  have hsep : Count.IsTwoSeparating G
      (Additive ↥Blk.frattiniK) :=
    Count.isTwoSeparating_of_tateDualityG Dl hA2 htriv hpair
  have hmem : (fun p : G × G =>
      Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 p.1 p.2)) ∈
      B2 G (Additive ↥Blk.frattiniK) := by
    apply hsep ⟨_, hdefZ2⟩
    intro n hn
    have hYinv : ∀ (y : Y) (r : ↥Blk.frattiniK),
        n (Additive.ofMul
          (⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩ : ↥Blk.frattiniK)) =
          n (Additive.ofMul r) := by
      intro y r
      obtain ⟨γ, hγ⟩ := hθs (QuotientGroup.mk' Blk.K y)
      have hfix := hn γ
      have h1 := congrArg (fun mu : ElemDual (Additive ↥Blk.frattiniK) =>
        mu (Additive.ofMul
          (⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩ : ↥Blk.frattiniK))) hfix
      have h2 : (γ • n) (Additive.ofMul
          (⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩ : ↥Blk.frattiniK)) =
          n (Additive.ofMul r) := by
        rw [hcompD γ n]
        show (θ γ • n) _ = _
        rw [ElemDual.smul_apply, hγ, ← map_inv,
          RStageLocal.conjC_smul_of_mk hRK y⁻¹
            ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩]
        refine congrArg _ (congrArg _ (Subtype.ext ?_))
        show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y)
        group
      exact h1.symm.trans h2
    exact (H2mk_eq_zero_iff _).mp
      (hall ⟨(n : Additive ↥Blk.frattiniK →+ ZMod 2), fun y r => hYinv y r⟩)
  -- Extract the continuous splitting cochain and assemble the homomorphic lift.
  obtain ⟨ψ, hψC1, hψeq⟩ := hmem
  have hψc : Continuous ψ := hψC1
  refine homLift_of_split (blockFrameImpl T Blk hE2) g.1.1
    (fun γ => Additive.toMul (ψ γ)) ?_ ?_
  · show Continuous fun γ => ((Additive.toMul (ψ γ) : ↥Blk.frattiniK) : Y)
    exact continuous_subtype_val.comp hψc
  · intro γ δ
    have h : γ • ψ δ - ψ (γ * δ) + ψ γ =
        Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) :=
      congrFun hψeq (γ, δ)
    have hD : -(Additive.ofMul
        (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ)) =
        Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) :=
      neg_eq_of_add_eq_zero_left (hA2 _)
    have h2 : ψ (γ * δ) = ψ γ + γ • ψ δ +
        Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) := by
      have h3 : ψ (γ * δ) = γ • ψ δ + ψ γ -
          Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) := by
        rw [← h]
        abel
      rw [h3, sub_eq_add_neg, hD, add_comm (γ • ψ δ) (ψ γ)]
    rw [hsmul γ (ψ δ)] at h2
    exact congrArg
      (fun a : Additive ↥Blk.frattiniK => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) h2

/-- The one-field interface isolating radical-obstruction separation.  It is retained as a
useful compatibility boundary even though `correctedRStageSeparation_galK` now constructs it. -/
structure CorrectedRStageSeparationGalK (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (q : ℕ) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  hsep_hom : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (_hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (_hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB),
    obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
        (htriv_galK K) (card_H2_zmodTwo_galK K) g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom (galKProfinite K) Y,
        ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ

/-- Tate duality at the open subgroup `G_K` supplies the corrected R-stage separation record.

The record API is unchanged: this is a constructor for its single field.  No degree or Euler
characteristic is required. -/
noncomputable def correctedRStageSeparation_galK
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    CorrectedRStageSeparationGalK K q P nuP := by
  let G : Type := ((galKProfinite K : ProfiniteGrp) : Type)
  let e : G ≃ₜ* GalK K := ContinuousMulEquiv.refl (GalK K)
  letI dmTarget : DistribMulAction (GalK K) (MuN 2) := inferInstance
  have hcontTarget : Continuous fun p : (GalK K) × MuN 2 => p.1 • p.2 := continuous_smul
  letI dmMu : DistribMulAction G (MuN 2) :=
    DistribMulAction.compHom _ e.toMonoidHom
  haveI csMu : ContinuousSMul G (MuN 2) :=
    ⟨hcontTarget.comp ((e.continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩
  haveI : (GalKsub K).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  let Dl : TateDualityG G 2 := LSquare.tateDualityG_two_of_equiv e
    (subgroup_isLocalDualizingGroup 2 (GalKsub K) (isOpen_fixingSubgroup K))
  refine ⟨?_⟩
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F g hg
  exact rStage_hsep_hom_of_tateDualityG Dl (smulZmod2GalK K)
    (contSMulZmod2GalK K) (htriv_galK K) (card_H2_zmodTwo_galK K)
    hE2 hRK hR2 b F g hg

/-- Fill the two-field residue record from separation alone; the `zRN` count is the theorem
`correctedRStage_hZcount_galK`. -/
noncomputable def correctedRStageResiduesGalK_of_separation
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = n)
    (S : CorrectedRStageSeparationGalK K q P nuP) :
    CorrectedRStageResiduesGalK K n q P nuP (standardNumerics n) where
  hsep_hom := S.hsep_hom
  hZcount := fun hE2 hRK hR2 b F f₀ =>
    correctedRStage_hZcount_galK hdeg hE2 hRK hR2 b F f₀

/-- The corrected equation-(136) semantics at `G_K` now reduces to separation alone. -/
theorem correctedRStageSemantics_galK_of_separation
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = n)
    (S : CorrectedRStageSeparationGalK K q P nuP) :
    CorrectedRStageSemantics (galKProfinite K) n q P nuP (standardNumerics n) := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F
  exact blockStageR136NK (standardNumerics n) T Blk hE2 (htriv_galK K)
    (card_H2_zmodTwo_galK K) (tfg_galK K) b F
    (S.hsep_hom hE2 hRK hR2 b F)
    (correctedRStage_hZcount_galK hdeg hE2 hRK hR2 b F)

/-- The corrected equation-(136) semantics at `G_K`, with both analytic residues discharged.
The R-cocycle count uses the degree-`n` Euler formula; separation uses only Tate duality. -/
theorem correctedRStageSemantics_galK
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = n) :
    CorrectedRStageSemantics (galKProfinite K) n q P nuP (standardNumerics n) :=
  correctedRStageSemantics_galK_of_separation hdeg correctedRStageSeparation_galK

/-- `blockStageR136NK` reduces the corrected arithmetic equation exactly to separation and the
degree-corrected R-cocycle count.  The existing GalK scalar and t.f.g. suppliers discharge all
other source-side inputs. -/
theorem correctedRStageSemantics_galK_of_residues
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {SN : SourceNumerics n} [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (R : CorrectedRStageResiduesGalK K n q P nuP SN) :
    CorrectedRStageSemantics (galKProfinite K) n q P nuP SN := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F
  exact blockStageR136NK SN T Blk hE2 (htriv_galK K)
    (card_H2_zmodTwo_galK K) (tfg_galK K) b F
    (R.hsep_hom hE2 hRK hR2 b F) (R.hZcount hE2 hRK hR2 b F)

/-- Reuse the two unchanged legacy exact-lifting clauses and replace only equation (136). -/
theorem exactLiftingSemanticsRN_of_legacy_and_correctedRStage
    {Γ : ProfiniteGrp} {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (legacy : ExactLiftingSemantics Γ n q P nuP SN)
    (stageRN : CorrectedRStageSemantics Γ n q P nuP SN) :
    ExactLiftingSemanticsRN Γ n q P nuP SN :=
  ⟨legacy.1, legacy.2.1, stageRN⟩

/-- The corrected residual data needed to construct the arithmetic `SourceDataRN` at `G_K`. -/
structure KExactSupplyRN (T : OrientedTameQuotientK B FF) (n : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  hdeg : Module.finrank ℚ_[2] K = n
  pro2 : ContinuousMonoidHom (GalK K) P
  hpro2 : Function.Surjective pro2
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K)
  nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g)
  exactLifting : ExactLiftingSemanticsRN (galKProfinite K) n (qOf K FF) P nuP
    (standardNumerics n)

namespace KExactSupplyRN

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {T : OrientedTameQuotientK B FF} {n : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo}

/-- Upgrade a legacy `KExactSupply` by supplying only the genuinely changed R-stage identity. -/
noncomputable def ofKExactSupply (S : KExactSupply T n P hP nuP)
    (stageRN : CorrectedRStageSemantics (galKProfinite K) n (qOf K FF) P nuP
      (standardNumerics n)) :
    KExactSupplyRN T n P hP nuP where
  hdeg := S.hdeg
  pro2 := S.pro2
  hpro2 := S.hpro2
  ker_pro2 := S.ker_pro2
  nu_compat := S.nu_compat
  exactLifting := exactLiftingSemanticsRN_of_legacy_and_correctedRStage
    S.exactLifting stageRN

/-- Upgrade legacy arithmetic data from the two concrete corrected R-stage residues. -/
noncomputable def ofKExactSupplyAndRStageResidues (S : KExactSupply T n P hP nuP)
    (Rstage : CorrectedRStageResiduesGalK K n (qOf K FF) P nuP
      (standardNumerics n)) :
    KExactSupplyRN T n P hP nuP :=
  ofKExactSupply S (correctedRStageSemantics_galK_of_residues Rstage)

/-- Compatibility upgrade accepting an explicit separation record.  The canonical constructor
below now supplies that record from Tate duality. -/
noncomputable def ofKExactSupplyAndRStageSeparation (S : KExactSupply T n P hP nuP)
    (Sep : CorrectedRStageSeparationGalK K (qOf K FF) P nuP) :
    KExactSupplyRN T n P hP nuP :=
  ofKExactSupply S (correctedRStageSemantics_galK_of_separation S.hdeg Sep)

/-- Canonical corrected upgrade of a legacy arithmetic supply.  Local Euler counting supplies
the new `zRN` coefficient and Tate `(2,0)` supplies R-stage separation, so no corrected-stage
residue remains in the constructor API. -/
noncomputable def ofKExactSupplyCanonical (S : KExactSupply T n P hP nuP) :
    KExactSupplyRN T n P hP nuP :=
  ofKExactSupply S (correctedRStageSemantics_galK S.hdeg)

/-- At degree one no corrected R-stage hypothesis is needed: `zRN` is definitionally the
legacy frozen coefficient, so the exact-lifting packet converts directly. -/
noncomputable def ofKExactSupplyStandardOne (S : KExactSupply T 1 P hP nuP) :
    KExactSupplyRN T 1 P hP nuP where
  hdeg := S.hdeg
  pro2 := S.pro2
  hpro2 := S.hpro2
  ker_pro2 := S.ker_pro2
  nu_compat := S.nu_compat
  exactLifting := (exactLiftingSemanticsRN_standard_one_iff _ _ _ _).mpr S.exactLifting

/-- Assemble the corrected arithmetic source.  Every non-RN field is the existing `KSupply`
constructor or its local-duality/Gauss supplier; only `exactLifting` comes from the corrected
record. -/
noncomputable def toSourceRN (S : KExactSupplyRN T n P hP nuP)
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    SourceDataRN n (qOf K FF) P hP nuP (standardNumerics n) where
  Γ := galKProfinite K
  tame := T.tameFK
  pro2 := S.pro2
  compat := fun g => T.compatF_K S.pro2 nuP S.nu_compat g
  surj := boundary_jointly_surjective_of_maxProP (qOf_ne_zero K FF) (even_qOf K FF) nuP
    T.tameFK S.pro2 T.tameFK_surjective S.hpro2 S.ker_pro2
    (fun g => T.compatF_K S.pro2 nuP S.nu_compat g)
  ker_pro2 := S.ker_pro2
  smulZmod2 := smulZmod2GalK K
  contSMulZmod2 := contSMulZmod2GalK K
  htriv := htriv_galK K
  tfg := tfg_galK K
  exactLifting := S.exactLifting
  stokes := stokesDualityCertificate_galK K S.hdeg
  scalar := scalarHilbert_galK K S.hdeg rfl
  determinant := affineDeterminant_galK K params params_n params_qK S.hdeg
    (gaussUnram_standard n) (gaussRam_standard n) T.tameFK T.tameFK_surjective S.pro2
    (fun g => T.compatF_K S.pro2 nuP S.nu_compat g) ramifiedData

/-- The corrected arithmetic source has carrier `G_K` definitionally. -/
theorem toSourceRN_carrier (S : KExactSupplyRN T n P hP nuP)
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    (((S.toSourceRN params params_n params_qK ramifiedData).Γ : ProfiniteGrp) : Type) =
      GalK K := rfl

/-- The corrected arithmetic source's tame coordinate is onto. -/
theorem toSourceRN_htame (S : KExactSupplyRN T n P hP nuP)
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF) (ramifiedData) :
    Function.Surjective (S.toSourceRN params params_n params_qK ramifiedData).tame :=
  T.tameFK_surjective

/-- The corrected arithmetic source's wild kernel is pro-2. -/
theorem toSourceRN_hwild (S : KExactSupplyRN T n P hP nuP)
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF) (ramifiedData) :
    IsProP 2 (S.toSourceRN params params_n params_qK ramifiedData).tame.toMonoidHom.ker :=
  T.ker_tameFK ▸ T.isProP

end KExactSupplyRN

end CorrectedResidualSupply

end GQ2.Dyadic
