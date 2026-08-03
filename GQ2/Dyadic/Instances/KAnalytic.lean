/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.LocalDuality
import GQ2.Dyadic.Instances.KSupply
import GQ2.Dyadic.GaussZ.FinalDK

/-!
# The Stokes-duality certificate from local duality

The four fields are assembled from `GQ2.Dyadic.Count.LocalDuality`; this file contains no new
cohomological argument.  A field-level specialization can therefore be assembly-only once the
`galKProfinite` instance-path elaboration is isolated.
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
    Count.hsep_field_of_localDualityG Dl hE smulZ2 contZ2 htriv
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

end GQ2.Dyadic
