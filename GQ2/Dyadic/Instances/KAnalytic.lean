/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Count.LocalDuality

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

end GQ2.Dyadic
