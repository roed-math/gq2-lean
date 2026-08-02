/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.LocalDuality
import GQ2.Dyadic.Instances.KSupply

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

end GQ2.Dyadic
