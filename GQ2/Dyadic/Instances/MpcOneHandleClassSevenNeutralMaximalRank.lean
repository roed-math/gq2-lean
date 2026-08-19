/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityRank

/-!
# Maximal neutral-image rank closes the class-seven correction

W293 identifies the actual dimension of the standard neutral target.  If the compact neutral
image transpose reaches that dimension, then its range has the same cardinality as its dual
domain, hence the transpose is injective.  Every neutral obstruction then lies in the compact
connecting image, which gives the full W6 correction.

Using the exact two-dimensional decomposition from W293, it is enough to prove the single
rank equation `compact-image rank + parity-interaction rank = 2`.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralMaximalRank

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityRank
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel

theorem neutralImageTranspose_injective_of_rank_eq_standardNeutralityFinrank
    (hrank : oneHandleCompactNeutralImageTransposeRank =
      oneHandleC7StandardNeutralityFinrank) :
    Function.Injective oneHandleCompactNeutralImageTranspose := by
  letI : Finite oneHandleCompactNeutralImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  have hcardDual : Nat.card (ElemDual NeutralTarget) =
      Nat.card NeutralTarget :=
    card_elemDual oneHandleC7StandardNeutralityCokernel_add_self
  have hcard : Nat.card (ElemDual NeutralTarget) =
      Nat.card oneHandleCompactNeutralImageTranspose.range := by
    calc
      Nat.card (ElemDual NeutralTarget) = Nat.card NeutralTarget := hcardDual
      _ = 2 ^ oneHandleC7StandardNeutralityFinrank :=
        natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank
      _ = 2 ^ oneHandleCompactNeutralImageTransposeRank := by rw [hrank]
      _ = Nat.card oneHandleCompactNeutralImageTranspose.range :=
        neutralImageTranspose_rangeCard_eq_pow_rank.symm
  have hbij : Function.Bijective
      oneHandleCompactNeutralImageTranspose.rangeRestrict := by
    rw [Nat.bijective_iff_surjective_and_card]
    exact ⟨oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective,
      hcard⟩
  intro x y hxy
  exact hbij.injective (Subtype.ext hxy)

theorem neutralTargetTransposeVanishing_of_rank_eq_standardNeutralityFinrank
    (x : OneHandleC7StandardNeutralityCokernel)
    (hrank : oneHandleCompactNeutralImageTransposeRank =
      oneHandleC7StandardNeutralityFinrank) :
    OneHandleCompactNeutralTargetTransposeVanishing x := by
  intro ell hell
  have hinj :=
    neutralImageTranspose_injective_of_rank_eq_standardNeutralityFinrank hrank
  have hz : ell = 0 := hinj (hell.trans (map_zero _).symm)
  rw [hz]
  exact map_zero _

theorem oneHandleW6Correctable_of_neutralImageTransposeRank_eq_standard
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E)
    (hrank : oneHandleCompactNeutralImageTransposeRank =
      oneHandleC7StandardNeutralityFinrank) :
    OneHandleW6Correctable := by
  rw [oneHandleW6Correctable_iff_neutrality_mem_connectingValues E D hD,
    mem_compactNeutralConnectingValues_iff_transposeVanishing]
  exact neutralTargetTransposeVanishing_of_rank_eq_standardNeutralityFinrank _ hrank

theorem oneHandleW6Correctable_of_imageRank_add_parityRank_eq_two
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E)
    (hrank : oneHandleCompactNeutralImageTransposeRank +
      oneHandleC7StandardParityInteractionRank = 2) :
    OneHandleW6Correctable := by
  apply oneHandleW6Correctable_of_neutralImageTransposeRank_eq_standard E D hD
  have htarget := standardNeutralityFinrank_add_parityInteractionRank
  omega

#print axioms neutralImageTranspose_injective_of_rank_eq_standardNeutralityFinrank
#print axioms neutralTargetTransposeVanishing_of_rank_eq_standardNeutralityFinrank
#print axioms oneHandleW6Correctable_of_neutralImageTransposeRank_eq_standard
#print axioms oneHandleW6Correctable_of_imageRank_add_parityRank_eq_two

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralMaximalRank
