/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
import GQ2.Dyadic.Instances.EvenFamilyConstruct
import GQ2.Dyadic.Instances.StageAbstractionEvenDerivKer

/-!
# The all-degree derivation theorem at the general Mpc finite stages

This module connects the existing derivation-family theorem for the model core `DM alpha h`
to the simultaneous finite-range formulation of the general Mpc pivot problem.  Everything is
parameterized by the degree `alpha`, handle count `h`, and stage `k`; no nilpotency class is
selected.

The derivation family proves that the inverse relator defect lies in the unrestricted raw
shift span.  The only remaining problem is therefore to represent that already-reachable
class by corrections that are individually `chiM`-neutral and whose `C` correction is
abelian-neutral.  That is precisely the constrained range in `MpcGeneralFiniteSpan`.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralDerivationBridge

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenFamily
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Roe.Labute

/-- The model `M` core has unrestricted raw-defect coverage at every degree, handle count,
and stage.  This combines the existing all-tuple derivation family with the generic
derivation-kernel criterion. -/
theorem mpcModelRawDefectSupply {alpha h : ℕ} (halpha : 2 ≤ alpha) :
    EvenKernelRawDefectSupply (mStageWord alpha h (by omega)) (vM alpha)
      (DM alpha h : Type) (chiM alpha h) := by
  apply evenKernel_rawDefectSupply_of_family
  intro k hk T
  obtain ⟨F, hrel⟩ := evenFam_modelHfamM alpha h halpha (by omega) k hk T
  exact ⟨F,
    evenDeriv_derivKerCriterion (dmFinsetTopGen alpha h) (isProP_DM alpha h) hk F
      (evenKernel_vM_sub_one_dvd_four halpha)
      evenKernel_vM_diagonal_add_one_dvd_four,
    hrel⟩

/-- A general finite-stage marking, reduced at level `k`, is a generic oriented stage tuple
for the `M` word. -/
def mpcGeneralTuple {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    Tuple (mStageWord alpha h (by omega)) (vM alpha)
      (DM alpha h : Type) (chiM alpha h) k where
  generators i := levelMk (DM alpha h) k (m i)
  rows i := ⟨m i, (hm.2.1 i).trans (chiM_dmGen alpha h i), rfl⟩
  relation := by
    change mRelWord alpha (fun i => levelMk (DM alpha h) k (m i)) = 1
    rw [← map_mRelWord]
    exact (QuotientGroup.eq_one_iff _).mpr hm.2.2.2
  topGen := by
    have htop := topGen_of_mpcModTwoIndep hm.1
    have H := evenRawClosure_markedBase_eq_top m (dmFinsetTopGen alpha h)
      (isProP_DM alpha h) htop (k - 1)
    rw [show k = (k - 1) + 1 by omega]
    exact H

@[simp] theorem mpcGeneralTuple_generators {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    (mpcGeneralTuple halpha m hm hk).generators =
      fun i => levelMk (DM alpha h) k (m i) :=
  rfl

/-- Raw shift spans are unchanged when their displayed bases have the same projection one
level down. -/
theorem evenRawShiftSpan_eq_of_levelProj_eq
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (hk : 3 ≤ k)
    (base base' : Fin (coreRank h) → levelQuot G (k + 1))
    (hproj : ∀ i, levelProj G k (base i) = levelProj G k (base' i)) :
    evenRawShiftSpan base hk = evenRawShiftSpan base' hk := by
  choose z hz hbase using fun i => exists_zLayer_mul (G := G) (hproj i)
  have hhom : evenRawDepthShiftHom base hk = evenRawDepthShiftHom base' hk := by
    ext V
    change evenRawDbarWord base V.correction = evenRawDbarWord base' V.correction
    rw [show base = fun i => z i * base' i from funext hbase]
    exact evenDeriv_dbarWord_central_base_shift hk hz base' V.depth
  unfold evenRawShiftSpan
  rw [hhom]

/-- For a general stage, the canonical-lift raw span is the literal span based at the chosen
ambient marking. -/
theorem mpcGeneral_rawShiftSpan_eq {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    evenRawShiftSpan
        (fun i => canonLift (DM alpha h) k
          ((mpcGeneralTuple halpha m hm hk).generators i)) hk =
      evenRawShiftSpan (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk := by
  apply evenRawShiftSpan_eq_of_levelProj_eq hk
  intro i
  simp only [mpcGeneralTuple_generators, levelProj_canonLift, levelProj_levelMk]

/-- The inverse relator of every general finite-stage marking lies in the unrestricted raw
shift span at the same stage.  This is the all-degree derivation conclusion in the exact base
used by the finite-range problem. -/
theorem mpcGeneralLevelTarget_mem_rawShiftSpan {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    (mpcGeneralLevelTarget hm).1 ∈
      evenRawShiftSpan (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk := by
  let T := mpcGeneralTuple halpha m hm hk
  have H := mpcModelRawDefectSupply halpha k hk T
  rw [mpcGeneral_rawShiftSpan_eq halpha m hm hk] at H
  have hdef : stageDefect (mStageWord alpha h (by omega)) (DM alpha h) k T.generators =
      levelMk (DM alpha h) (k + 1) (mRelWord alpha m) := by
    calc
      stageDefect (mStageWord alpha h (by omega)) (DM alpha h) k T.generators =
          (mStageWord alpha h (by omega)).word
            (fun i => levelMk (DM alpha h) (k + 1) (m i)) :=
        (stageDefect_eq_of_lift (mStageWord alpha h (by omega)) k T.generators
          (fun i => levelMk (DM alpha h) (k + 1) (m i)) (fun i => by
            simp only [levelProj_levelMk, T, mpcGeneralTuple_generators])).symm
      _ = levelMk (DM alpha h) (k + 1) (mRelWord alpha m) := by
        change mRelWord alpha (fun i => levelMk (DM alpha h) (k + 1) (m i)) = _
        rw [← map_mRelWord]
  simpa only [mpcGeneralLevelTarget, hdef] using H

/-- The unrestricted finite shift homomorphism at a chosen general marking. -/
noncomputable def mpcGeneralRawLevelShiftHom {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) (hk : 3 ≤ k) :
    EvenRawDepthCorrection (DM alpha h) h k →* zLayer (DM alpha h) k :=
  evenRawDepthShiftHom (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk

/-- The general all-degree derivation theorem makes the unrestricted finite fiber nonempty. -/
theorem mpcGeneralLevelTarget_mem_rawRange {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    mpcGeneralLevelTarget hm ∈ (mpcGeneralRawLevelShiftHom m k hk).range := by
  have H := mpcGeneralLevelTarget_mem_rawShiftSpan halpha m hm hk
  change (mpcGeneralLevelTarget hm).1 ∈ Subgroup.map (zLayer (DM alpha h) k).subtype
    (mpcGeneralRawLevelShiftHom m k hk).range at H
  obtain ⟨q, ⟨V, hV⟩, hq⟩ := H
  refine ⟨V, ?_⟩
  apply Subtype.ext
  calc
    ((mpcGeneralRawLevelShiftHom m k hk V).1) = q.1 :=
      congrArg Subtype.val hV
    _ = (mpcGeneralLevelTarget hm).1 := hq

/-- The nonempty affine fiber of unrestricted corrections above the current relator target. -/
def mpcGeneralRawFiber {alpha h k : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    Set (EvenRawDepthCorrection (DM alpha h) h k) :=
  {V | mpcGeneralRawLevelShiftHom m k hk V = mpcGeneralLevelTarget hm}

theorem mpcGeneralRawFiber_nonempty {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    (mpcGeneralRawFiber m hm hk).Nonempty := by
  obtain ⟨V, hV⟩ := mpcGeneralLevelTarget_mem_rawRange halpha m hm hk
  exact ⟨V, hV⟩

/-- Exact remaining boundary: constrained coverage says that the already-nonempty raw fiber
meets the finite subgroup of corrections having exact neutral representatives. -/
theorem mpcGeneral_target_mem_constrainedRange_iff_fiber_meets {alpha h k : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range ↔
      ∃ V ∈ mpcGeneralRawFiber m hm hk,
        V ∈ (mpcGeneralLevelToRawHom alpha h k).range := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨mpcGeneralLevelToRawHom alpha h k E, ?_, ⟨E, rfl⟩⟩
    exact hE
  · rintro ⟨V, hV, E, rfl⟩
    exact ⟨E, hV⟩

end

end GQ2.Dyadic.Instances.MpcGeneralDerivationBridge

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralDerivationBridge

#print axioms mpcModelRawDefectSupply
#print axioms mpcGeneralTuple
#print axioms mpcGeneralTuple_generators
#print axioms evenRawShiftSpan_eq_of_levelProj_eq
#print axioms mpcGeneral_rawShiftSpan_eq
#print axioms mpcGeneralLevelTarget_mem_rawShiftSpan
#print axioms mpcGeneralRawLevelShiftHom
#print axioms mpcGeneralLevelTarget_mem_rawRange
#print axioms mpcGeneralRawFiber
#print axioms mpcGeneralRawFiber_nonempty
#print axioms mpcGeneral_target_mem_constrainedRange_iff_fiber_meets

end AxiomPins
