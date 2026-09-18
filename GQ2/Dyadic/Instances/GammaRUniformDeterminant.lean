/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformAnalyticCore
import GQ2.Dyadic.Instances.WordPhase

/-!
# A word-independent even-degree determinant assembler

Uniform Stokes supplies the finite cocycle count. The remaining input is precisely a
branch-free phase comparison at the actual source and its actual boundary maps.
-/

namespace GQ2.Dyadic.UniformStokesSupply
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances.WordPhase

variable {n q : ℕ} {R : PWord (Generator n)}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}

/-- At even degree the same phase supply gives both determinant clauses, for any word. -/
theorem determinant_of_branchFree (S : UniformStokesSupply n q R wOf) (hn : Even n)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (GammaR n q R) (Tq q))
    (pro2 : ContinuousMonoidHom (GammaR n q R) P)
    (compat : ∀ g : (GammaR n q R : Type), nuTq q (tame g) = nuP (pro2 g))
    (phase : wPhBranchFreeSupply n nuP tame pro2 compat) :
    AffineDeterminantCertificate (GammaR n q R) n q P nuP (standardNumerics n)
      tame pro2 compat (scalarActionZmodTwo _) := by
  letI := scalarActionZmodTwo ((GammaR n q R : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((GammaR n q R : Type))
  constructor
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply LSquare.gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [S.hZcard (sourceBoundaryMapK tame pro2 compat) F En l hl
          hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · rw [wPh_gaussUnram_eq_gaussRam_of_even hn m]
        exact phase T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply LSquare.gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [S.hZcard (sourceBoundaryMapK tame pro2 compat) F En l hl
          hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact phase T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl

/-- The complete flexible certificate is reduced to a normalized core and its phase supply. -/
def certificateLeaves_of_branchFree (S : UniformStokesSupply n q R wOf)
    (hn : Even n) (hspec : TameSpec.TameSpecializes n q R)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : Instances.FieldFamilyFlexibleCertificate.FlexibleCoreLeavesRN n R P nuP)
    (hq0 : q ≠ 0) (hqe : Even q)
    (phase : wPhBranchFreeSupply n nuP (TameSpec.tameOfSpec n q R hspec)
      (C.pro2 hq0 hqe) (C.compat hq0 hqe hspec)) :
    Instances.FieldFamilyFlexibleCertificate.FlexibleCertificateLeavesRN n q R P hP nuP
      (standardNumerics n) hq0 hqe :=
  S.certificateLeaves hspec hP C hq0 hqe
    (S.determinant_of_branchFree hn nuP _ _ _ phase)

#print axioms determinant_of_branchFree
#print axioms certificateLeaves_of_branchFree

end
end GQ2.Dyadic.UniformStokesSupply
