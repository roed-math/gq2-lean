/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceRamifiedSupply
import GQ2.Dyadic.Instances.NpcActionImageDevissage
import GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

/-!
# Action-image interface for the general tame splice

These declarations connect the word-level gluing theorem to the existing row-independent
devissage. Only the unramified simple branch remains a structural-word-specific analytic
input. The ramified branch, the complete normalized core, and the finite resolver are supplied
uniformly. This interface does not assume a final field identification.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

/-- One coefficient-independent integer family at each finite level. -/
def pinnedResolvedFamily (n q : ℕ) (R : PWord (Generator n)) (N : ℕ) :
    Fin 2 → FreeGroup (Generator n) :=
  fun k ↦ heisToFree (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N)
    (gammaFam n q R k)

/-- The normalized cyclotomic rows are unchanged by tame splicing. -/
def FlexibleCoreLeavesRN.ofTameSplice
    {n : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN n R P nuP) (H : PWord (Generator n)) :
    FlexibleCoreLeavesRN n (tameSplice R H) P nuP where
  presentation := C.presentation.ofTameSplice H
  nu_sigma := C.nu_sigma
  nu_wild := C.nu_wild

/-- The universal pinned resolver needs only an endpoint input for a word. -/
theorem pinnedLevelResolver {n q : ℕ} {R : PWord (Generator n)}
    (hend : ∀ N : ℕ, N ≠ 0 → N.factorization 2 ≠ 0 →
      IsStokesEndpoint (pinnedResolvedFamily n q R N)) :
    LevelResolver n q R (pinnedResolvedFamily n q R) where
  resolves := fun _ _ _ _ _ _ hN hord ↦ resolvesAt_omegaPinnedLevelResolvers hN hord _
  endpoint := hend

/-- Every compact-M template has the pinned endpoint at all nonzero even levels. -/
theorem pinned_mCompact_endpoint {α h q N : ℕ} (hqe : Even q)
    (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0) :
    IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q
      (Words.MCompact.mCompactW α h) N) := by
  unfold pinnedResolvedFamily
  rw [mCompact_pinned_family_eq_level]
  exact Certificates.MCompact.mCompact_isStokesEndpoint hqe (odd_omega2Exp hN hNtwo)

/-- A structural endpoint word yields a complete level resolver for its compact-M splice. -/
theorem pinnedLevelResolver_tameSplice_mCompact {α h q : ℕ}
    {R : PWord (Generator (2 + 2 * h))} (hqe : Even q)
    (hend : ∀ N : ℕ, N ≠ 0 → N.factorization 2 ≠ 0 →
      IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q R N)) :
    LevelResolver (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))
      (pinnedResolvedFamily (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))) := by
  apply pinnedLevelResolver
  intro N hN hNtwo
  exact isStokesEndpoint_tameSplice (hend N hN hNtwo)
    (pinned_mCompact_endpoint hqe hN hNtwo)

/-- The ramified simple action-image branch has no residual analytic premise. -/
theorem ramifiedActionImageStokes_tameSplice_mCompact {α h q : ℕ}
    {R : PWord (Generator (2 + 2 * h))} (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q R)
    (hend : ∀ N : ℕ, N ≠ 0 → N.factorization 2 ≠ 0 →
      IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q R N)) :
    RamifiedActionImageStokes (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))
      (pinnedResolvedFamily (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ
  let W := tameSplice R (Words.MCompact.mCompactW α h)
  let C := ActionImage (2 + 2 * h) q W M
  let t := actionImageMarking (2 + 2 * h) q W M
  apply stokesDuality_tameSplice_mCompact_ramified t R hM₂ hq0 hqe
    actionImage_tameRelAt
  · intro i
    exact actionImage_eq_one_of_smul_eq (t.x i) (actionImage_wild_smul hM₂ hsimple i)
  · exact hτ
  · exact actionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  · exact hend (4 * Monoid.exponent C) (fourMulExponent_ne_zero_and_even C).1
      (fourMulExponent_ne_zero_and_even C).2
  · exact hspec

/-- All finite elementary coefficients are supplied once the single unramified branch is
checked for the normalized structural source. The finite word depends only on the target. -/
theorem pushedStokesDuality_tameSplice_mCompact {α h q : ℕ}
    {R : PWord (Generator (2 + 2 * h))} (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q R)
    (hend : ∀ N : ℕ, N ≠ 0 → N.factorization 2 ≠ 0 →
      IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q R N))
    (hunram : UnramifiedActionImageStokes (2 + 2 * h) q
      (tameSplice R (Words.MCompact.mCompactW α h))
      (pinnedResolvedFamily (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))))
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))) : Type) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g ↦ rho (gammaGen (2 + 2 * h) q
      (tameSplice R (Words.MCompact.mCompactW α h)) g))
      (pinnedResolvedFamily (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h))
        (4 * Monoid.exponent C)) A :=
  uniformPushedStokesDuality_of_actionImage
    (pinnedLevelResolver_tameSplice_mCompact hqe hend)
    (simpleActionImageStokes_of_branches hunram
      (ramifiedActionImageStokes_tameSplice_mCompact hq0 hqe hspec hend)) rho A hA₂

#print axioms FlexibleCoreLeavesRN.ofTameSplice
#print axioms pinnedLevelResolver
#print axioms pinned_mCompact_endpoint
#print axioms pinnedLevelResolver_tameSplice_mCompact
#print axioms ramifiedActionImageStokes_tameSplice_mCompact
#print axioms pushedStokesDuality_tameSplice_mCompact

end
end GQ2.Dyadic
