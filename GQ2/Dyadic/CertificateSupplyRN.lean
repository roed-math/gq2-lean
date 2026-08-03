/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.LExact
import GQ2.Dyadic.Instances.N0Exact
import GQ2.Dyadic.Instances.NpcExact
import GQ2.Dyadic.Instances.M0Exact
import GQ2.Dyadic.Instances.MpcExact
import GQ2.Dyadic.Instances.NpcCore
import GQ2.Dyadic.Instances.MpcCoreUnit
import GQ2.Dyadic.ThmFourTwoRN

/-!
# Unified corrected certificate supply for the improved five-row table

This file is the certificate-facing endpoint of the improved constructor campaign.  A
`FieldBranchSelection` has already chosen one of the five arithmetic rows and, by construction,
its semantic word is the improved word in that row.  The five `exactLiftingRN` theorems supply
the corrected lifting clause from the row's single Stokes residue.  Everything else which is
uniform in the relator is filled here:

* topological finite generation of `GammaR`;
* the scalar action, its continuity, and its triviality;
* tame surjectivity and pro-`2`-ness of the wild kernel.

Thus `SelectedWordLeavesRN` asks only for the genuinely presentation/source-specific leaves:
a presented pro-`2` core with its two cyclotomic normalization rows, and the three remaining
analytic bundles.  Tame specialization and all six word/core/pro-`2` fields are derived here.
In particular it does not ask for `ExactLiftingSemanticsRN`, `StageSep`, `StageZ`, or any copy
of the reconstruction conclusion.
-/

namespace GQ2.Dyadic

open GQ2
open TameSpec
open GQ2.Dyadic.Count

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## The one branch-dependent residue -/

/-- The exact simple-module Stokes residue belonging to the row selected by `S`.

The equality carried by each constructor is intentional: it makes the displayed unit stored in
`S.display` available at the precise dependent type required by the procyclic constructors.  No
arithmetic validity proof is duplicated here; `S.valid` supplies `2 ≤ alpha` and, on procyclic
rows, `1 ≤ r` to the lifting constructors.

The L row takes `LSquare.PushedHsimp`, the honest source-facing residue restricted to markings
pushed forward from the candidate group.  The L count and exact-lifting chain is routed through
that weakening; the historical all-markings `LSquare.Hsimp` API remains available separately as
a compatibility wrapper. -/
inductive SelectedHsimp
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) (q : ℕ) : Prop
  | L (hbranch : S.branch = .L)
      (hsimp : LSquare.PushedHsimp (handleCount FP .L) q)
  | N0 (alpha : ℕ) (hbranch : S.branch = .N0 alpha)
      (hsimp : NCompact.Hsimp alpha (handleCount FP (.N0 alpha)) q)
  | Npc (alpha r : ℕ) (eta : ℤ_[2]ˣ) (hbranch : S.branch = .Npc alpha r eta)
      (hsimp : NProcyclic.Hsimp alpha r (handleCount FP (.Npc alpha r eta)) q
        (hbranch ▸ S.display).data)
  | M0 (alpha : ℕ) (hbranch : S.branch = .M0 alpha)
      (hsimp : MCompact.Hsimp alpha (handleCount FP (.M0 alpha)) q)
  | Mpc (alpha r : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ)
      (hbranch : S.branch = .Mpc alpha r epsilon eta)
      (hsimp : MProcyclicExact.Hsimp alpha r (p epsilon r)
        (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)

namespace SelectedHsimp

/-- Compatibility constructor for callers which still prove the historical all-markings L
residue.  The selected interface stores only its pushed consequence. -/
theorem L_of_hsimp
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    {S : FieldBranchSelection K FP Q W} {q : ℕ} (hbranch : S.branch = .L)
    (hsimp : LSquare.Hsimp (handleCount FP .L) q) : SelectedHsimp S q :=
  .L hbranch (LSquare.pushedHsimp_of_hsimp hsimp)

end SelectedHsimp

/-- Dispatch a selected branch's unique Stokes residue through the corresponding improved
`exactLiftingRN` constructor.  Branch validity is read from `S`; callers do not repeat alpha or
level inequalities. -/
theorem exactLiftingRN_of_selectedHsimp
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN
      (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
      (standardNumerics S.semantic.degree) := by
  cases hsimp with
  | L hbranch hsimp =>
      exact LSquare.exactLiftingRN_of_fieldSelection_pushed S hbranch hsimp hqe nuP
  | N0 alpha hbranch hsimp =>
      have hvalid : 2 ≤ alpha := by
        have h := S.valid
        rw [hbranch] at h
        exact h
      exact NCompact.exactLiftingRN_of_fieldSelection S hbranch hsimp
        (le_trans (by omega) hvalid) hq0 hqe nuP
  | Npc alpha r eta hbranch hsimp =>
      exact NProcyclic.exactLiftingRN_of_fieldSelection S hbranch hsimp hqe nuP
  | M0 alpha hbranch hsimp =>
      exact MCompact.exactLiftingRN_of_fieldSelection S hbranch hsimp hq0 hqe nuP
  | Mpc alpha r epsilon eta hbranch hsimp =>
      exact MProcyclicExact.exactLiftingRN_of_fieldSelection S hbranch hsimp hqe nuP

/-! ## Tame specialization from the improved constructor table -/

/-- Every selected improved word specializes to the tame quotient.  This is a genuine
five-branch dispatch: Npc uses literal equality with the selected arbitrary unit's display,
whereas Mpc uses the evaluation-level transport which deliberately keeps the arbitrary unit and
the literal sign parameter `p epsilon r`. -/
theorem tameSpecialization_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes S.semantic.degree q S.semantic.word := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      cases branch with
      | L =>
          exact Count.tameSpecializes_lSq hq0 hqe (handleCount FP .L)
      | N0 alpha =>
          exact Count.tameSpecializes_nCompact hq0 hqe alpha (handleCount FP (.N0 alpha))
      | Npc alpha r eta =>
          change TameSpecializes (2 + 2 * handleCount FP (.Npc alpha r eta)) q
            (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta)
          rw [Words.Npc.npcWUnit_eq_display alpha r (handleCount FP (.Npc alpha r eta)) display]
          exact Count.tameSpecializes_npcW hq0 hqe alpha r
            (handleCount FP (.Npc alpha r eta)) display.data
      | M0 alpha =>
          exact Count.tameSpecializes_mCompact hq0 hqe alpha (handleCount FP (.M0 alpha))
      | Mpc alpha r epsilon eta =>
          change (tameMarking (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q).eval
            (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta
              (handleCount FP (.Mpc alpha r epsilon eta))) = 1
          rw [Words.Mpc.eval_mpcWUnit_eq_display
            (tameMarking (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q)
            alpha r (p epsilon r) display]
          exact Count.tameSpecializes_mpcW hq0 hqe (le_trans (by omega) valid.1)
            r (p epsilon r) display.display (handleCount FP (.Mpc alpha r epsilon eta))

/-! ## The exact structural residue -/

/-- The minimal marked-core residue.  A `CorePresentation` is exactly the universal property
needed to identify the maximal pro-`2` quotient of the selected `GammaR`; the two normalization
rows are exactly what its generic compatibility theorem consumes.

This record replaces seven formerly independent fields (`coreRel`, `proTwoWord`, `pro2`,
`ker_pro2`, `hpro2`, `compat`, and the now-derived tame specialization) by one coherent
presentation and two equations.

The five improved rows now all have direct branch coverage.  `nCorePresentation`,
`mCorePresentation`, and `LSquareCore.lCorePresentation` provide the compact N/M and L
presentations at every handle count.  The arbitrary-unit Npc and Mpc presentations are paired
below with canonical `Ztwo` orientations obtained by solving the triangular dictionaries in
additive `Z_2` coordinates. -/
structure SelectedCoreLeavesRN
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) where
  presentation : Count.CorePresentation S.semantic.degree S.semantic.word P
  nu_sigma : nuP (presentation.mark .sigma) = ztwoOne
  nu_wild : ∀ j : Fin (S.semantic.degree + 1), nuP (presentation.mark (.wild j)) = 1

namespace SelectedCoreLeavesRN

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
  {S : FieldBranchSelection K FP Q W} {q : ℕ} {P : ProfiniteGrp}
  {nuP : ContinuousMonoidHom P Ztwo}

open Multiplicative
open MarkedCore Count.PilotN

/-! ### Canonical compact-N orientation in the boundary target -/

/-- The canonical `nuN : DN → Multiplicative Z_2` read back through the boundary seam.
This is the handle-generic form of `SqrtNeg2.pilotNuP`; it introduces no new orientation. -/
noncomputable def nNuZtwo (alpha h : ℕ) :
    ContinuousMonoidHom (MarkedCore.DN alpha h : Type) Ztwo :=
  ⟨(ztwoIota.symm.toMulEquiv.toMonoidHom).comp (MarkedCore.nuN alpha h).toMonoidHom,
    ztwoIota.symm.continuous_toFun.comp (MarkedCore.nuN alpha h).continuous_toFun⟩

@[simp] theorem nNuZtwo_apply (alpha h : ℕ) (x : (MarkedCore.DN alpha h : Type)) :
    nNuZtwo alpha h x = ztwoIota.symm (MarkedCore.nuN alpha h x) := rfl

/-- Compact-N sigma normalization, uniformly in alpha and the handle count. -/
theorem nNuZtwo_sigma (alpha h : ℕ) :
    nNuZtwo alpha h ((Count.PilotN.nCorePresentation alpha h).mark .sigma) = ztwoOne := by
  rw [Count.PilotN.nCorePresentation_mark_sigma, nNuZtwo_apply,
    MarkedCore.nuN_dnSigma, ← ztwoIota_ztwoOne]
  exact ztwoIota.symm_apply_apply ztwoOne

/-- Compact-N wild normalization, uniformly including all handle letters. -/
theorem nNuZtwo_wild (alpha h : ℕ) (j : Fin (2 + 2 * h + 1)) :
    nNuZtwo alpha h ((Count.PilotN.nCorePresentation alpha h).mark (.wild j)) = 1 := by
  rw [Count.PilotN.nCorePresentation_mark_wild, nNuZtwo_apply]
  have hne := Instances.MCompactCore.nWildIdx_val_ne_two h j
  rcases MarkedCore.nCoreIdx_cases (Count.PilotN.nWildIdx h j) with
      h0 | h1 | h2 | h3 | ⟨k, hU⟩ | ⟨k, hV⟩
  · rw [h0, show MarkedCore.dnGen alpha h 0 = MarkedCore.dnX0 alpha h from rfl,
      MarkedCore.nuN_dnX0]
    exact map_one ztwoIota.symm.toMulEquiv
  · rw [h1, show MarkedCore.dnGen alpha h 1 = MarkedCore.dnX1 alpha h from rfl,
      MarkedCore.nuN_dnX1]
    exact map_one ztwoIota.symm.toMulEquiv
  · exact (hne (by rw [h2, MarkedCore.coreVal_two])).elim
  · rw [h3, show MarkedCore.dnGen alpha h 3 = MarkedCore.dnX2 alpha h from rfl,
      MarkedCore.nuN_dnX2]
    exact map_one ztwoIota.symm.toMulEquiv
  · rw [hU, MarkedCore.nuN_handleU]
    exact map_one ztwoIota.symm.toMulEquiv
  · rw [hV, MarkedCore.nuN_handleV]
    exact map_one ztwoIota.symm.toMulEquiv

/-! ### Unconditional compact-row constructors -/

/-- The selected compact-N row, with its presentation and both normalization rows derived. -/
noncomputable def ofN0 (S : FieldBranchSelection K FP Q W) {alpha : ℕ}
    (hbranch : S.branch = .N0 alpha) :
    SelectedCoreLeavesRN S (MarkedCore.DN alpha (handleCount FP (.N0 alpha)))
      (nNuZtwo alpha (handleCount FP (.N0 alpha))) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Count.PilotN.nCorePresentation alpha (handleCount FP (.N0 alpha))
          nu_sigma := nNuZtwo_sigma alpha (handleCount FP (.N0 alpha))
          nu_wild := nNuZtwo_wild alpha (handleCount FP (.N0 alpha)) }

/-- Branch validity supplies the sole side condition of the compact-M presentation. -/
theorem one_le_alpha_of_M0 (S : FieldBranchSelection K FP Q W) {alpha : ℕ}
    (hbranch : S.branch = .M0 alpha) : 1 ≤ alpha := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha at hvalid
  omega

/-- The selected compact-M row, with its presentation and both normalization rows derived. -/
noncomputable def ofM0 (S : FieldBranchSelection K FP Q W) {alpha : ℕ}
    (hbranch : S.branch = .M0 alpha) :
    SelectedCoreLeavesRN S (MarkedCore.DM alpha (handleCount FP (.M0 alpha)))
      (Instances.MCompactCore.mNu alpha (handleCount FP (.M0 alpha))
        (one_le_alpha_of_M0 S hbranch)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      have halpha : 1 ≤ alpha := le_trans (by omega) valid
      exact
        { presentation := Instances.MCompactCore.mCorePresentation alpha
            (handleCount FP (.M0 alpha)) halpha
          nu_sigma := Instances.MCompactCore.mNu_sigma alpha
            (handleCount FP (.M0 alpha)) halpha
          nu_wild := Instances.MCompactCore.mNu_wild alpha
            (handleCount FP (.M0 alpha)) halpha }

/-- Constructor-table regression: every selected compact-N row has fully derived structural
core leaves. -/
theorem exists_of_branch_N0 (S : FieldBranchSelection K FP Q W) {alpha : ℕ}
    (hbranch : S.branch = .N0 alpha) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SelectedCoreLeavesRN S P nuP) :=
  ⟨MarkedCore.DN alpha (handleCount FP (.N0 alpha)),
    nNuZtwo alpha (handleCount FP (.N0 alpha)), ⟨ofN0 S hbranch⟩⟩

/-- Constructor-table regression: every selected compact-M row has fully derived structural
core leaves. -/
theorem exists_of_branch_M0 (S : FieldBranchSelection K FP Q W) {alpha : ℕ}
    (hbranch : S.branch = .M0 alpha) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SelectedCoreLeavesRN S P nuP) :=
  ⟨MarkedCore.DM alpha (handleCount FP (.M0 alpha)),
    Instances.MCompactCore.mNu alpha (handleCount FP (.M0 alpha))
      (one_le_alpha_of_M0 S hbranch), ⟨ofM0 S hbranch⟩⟩

/-! ### Canonical procyclic-row orientations -/

/-- The arbitrary-unit Npc orientation before transport across the boundary seam.  In standard
`D_N` coordinates its additive values are `(0, eta, 2^r, 0, 0, ...)`.  The N relator has only
the first coordinate in its abelianization, so this is a genuine continuous group homomorphism,
not merely a coordinate formula. -/
noncomputable def npcNuPadic (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
  nLiftHom alpha h PropOneOne.isProP_two_multPadicInt
    (coreMark (ofAdd 0) (ofAdd (eta : ℤ_[2])) (ofAdd ((2 : ℤ_[2]) ^ r)) (ofAdd 0)) (by
      rw [nRelWord_comm, coreMark_zero, ← ofAdd_nsmul, ← ofAdd_zero]
      congr 1
      simp)

/-- The canonical arbitrary-unit Npc orientation in the certificate target `Ztwo`. -/
noncomputable def npcNu (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    ContinuousMonoidHom (DN alpha h : Type) Ztwo :=
  (ztwoIota.symm : ContinuousMonoidHom (Multiplicative ℤ_[2]) Ztwo).comp
    (npcNuPadic alpha r h eta)

@[simp] theorem npcNuPadic_gen_zero (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    npcNuPadic alpha r h eta (dnGen alpha h 0) = ofAdd 0 := by
  rw [npcNuPadic, nLiftHom_gen, coreMark_zero]

@[simp] theorem npcNuPadic_gen_one (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    npcNuPadic alpha r h eta (dnGen alpha h 1) = ofAdd (eta : ℤ_[2]) := by
  rw [npcNuPadic, nLiftHom_gen, coreMark_one]

@[simp] theorem npcNuPadic_gen_two (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    npcNuPadic alpha r h eta (dnGen alpha h 2) = ofAdd ((2 : ℤ_[2]) ^ r) := by
  rw [npcNuPadic, nLiftHom_gen, coreMark_two]

@[simp] theorem npcNuPadic_gen_three (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    npcNuPadic alpha r h eta (dnGen alpha h 3) = ofAdd 0 := by
  rw [npcNuPadic, nLiftHom_gen, coreMark_three]

@[simp] theorem npcNuPadic_gen_handleU (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (j : Fin h) :
    npcNuPadic alpha r h eta (dnGen alpha h (handleIdxU j)) = 1 := by
  rw [npcNuPadic, nLiftHom_gen, coreMark_handleU]

@[simp] theorem npcNuPadic_gen_handleV (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (j : Fin h) :
    npcNuPadic alpha r h eta (dnGen alpha h (handleIdxV j)) = 1 := by
  rw [npcNuPadic, nLiftHom_gen, coreMark_handleV]

/-- The Npc semantic sigma is `core_1^(eta⁻¹)`, hence has additive value one. -/
theorem npcNuPadic_sigma (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta) :
    npcNuPadic alpha r h eta
      ((Instances.NProcyclicCore.npcCorePresentationUnit alpha r h eta d).mark .sigma) =
        ofAdd 1 := by
  change npcNuPadic alpha r h eta
    (zpowZtwo (isProP_DN alpha h) (dnGen alpha h 1) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = _
  rw [map_zpowZtwo (isProP_DN alpha h) PropOneOne.isProP_two_multPadicInt,
    npcNuPadic_gen_one, SectionThree.zpowZtwo_ofAdd,
    ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- Every Npc wild letter has additive value zero, including all stabilizing handles. -/
theorem npcNuPadic_wild (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta)
    (j : Fin (2 + 2 * h + 1)) :
    npcNuPadic alpha r h eta
      ((Instances.NProcyclicCore.npcCorePresentationUnit alpha r h eta d).mark (.wild j)) = 1 := by
  change npcNuPadic alpha r h eta
    (Instances.NProcyclicCore.npcUntwistUnit (isProP_DN alpha h) eta r h
      (dnGen alpha h) (nWildIdx h j)) = 1
  have hne := Instances.MCompactCore.nWildIdx_val_ne_two h j
  rcases nCoreIdx_cases (nWildIdx h j) with
      h0 | h1 | h2 | h3 | ⟨k, hU⟩ | ⟨k, hV⟩
  · rw [h0, Instances.NProcyclicCore.npcUntwistUnit_apply_ne _ _ _ _ _
        (by rw [coreVal_zero]; omega) (by rw [coreVal_zero]; omega),
      npcNuPadic_gen_zero, ofAdd_zero]
  · rw [h1, Instances.NProcyclicCore.npcUntwistUnit_one, map_mul, map_zpow,
      npcNuPadic_gen_two]
    have hs : npcNuPadic alpha r h eta
        (zpowZtwo (isProP_DN alpha h) (dnGen alpha h 1)
          ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = ofAdd 1 := by
      exact npcNuPadic_sigma alpha r h eta d
    rw [hs, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · exact (hne (by rw [h2, coreVal_two])).elim
  · rw [h3, Instances.NProcyclicCore.npcUntwistUnit_apply_ne _ _ _ _ _
        (by rw [coreVal_three]; omega) (by rw [coreVal_three]; omega),
      npcNuPadic_gen_three, ofAdd_zero]
  · rw [hU, Instances.NProcyclicCore.npcUntwistUnit_apply_ne _ _ _ _ _
        (by rw [handleIdxU_val]; omega) (by rw [handleIdxU_val]; omega),
      npcNuPadic_gen_handleU]
  · rw [hV, Instances.NProcyclicCore.npcUntwistUnit_apply_ne _ _ _ _ _
        (by rw [handleIdxV_val]; omega) (by rw [handleIdxV_val]; omega),
      npcNuPadic_gen_handleV]

theorem npcNu_sigma (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta) :
    npcNu alpha r h eta
      ((Instances.NProcyclicCore.npcCorePresentationUnit alpha r h eta d).mark .sigma) =
        ztwoOne := by
  apply ztwoIota.injective
  change ztwoIota (ztwoIota.symm (npcNuPadic alpha r h eta
    ((Instances.NProcyclicCore.npcCorePresentationUnit alpha r h eta d).mark .sigma))) =
      ztwoIota ztwoOne
  rw [ztwoIota.apply_symm_apply, ztwoIota_ztwoOne, npcNuPadic_sigma]

theorem npcNu_wild (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta)
    (j : Fin (2 + 2 * h + 1)) :
    npcNu alpha r h eta
      ((Instances.NProcyclicCore.npcCorePresentationUnit alpha r h eta d).mark (.wild j)) = 1 := by
  apply ztwoIota.injective
  change ztwoIota (ztwoIota.symm (npcNuPadic alpha r h eta
    ((Instances.NProcyclicCore.npcCorePresentationUnit alpha r h eta d).mark (.wild j)))) =
      ztwoIota 1
  rw [ztwoIota.apply_symm_apply, map_one, npcNuPadic_wild]

/-- The arbitrary-unit Mpc orientation before transport across the boundary seam.  Its standard
`D_M` additive row is `(-m(alpha)s(r), p, s(r), eta, 0, ...)`. -/
noncomputable def mpcNuPadic (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
  mLiftHom alpha h PropOneOne.isProP_two_multPadicInt
    (coreMark
      (ofAdd (-((m alpha : ℤ_[2]) * (s r : ℤ_[2]))))
      (ofAdd (p : ℤ_[2])) (ofAdd (s r : ℤ_[2])) (ofAdd (eta : ℤ_[2]))) (by
        rw [mRelWord_comm, coreMark_zero, coreMark_two,
          ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero]
        congr 1
        have h2 : ((2 * m alpha : ℕ) : ℤ_[2]) = ((2 ^ alpha : ℕ) : ℤ_[2]) :=
          congrArg _ (two_mul_m halpha)
        push_cast at h2
        rw [nsmul_eq_mul, nsmul_eq_mul, mul_neg]
        push_cast
        rw [← h2]
        ring)

/-- The canonical arbitrary-unit Mpc orientation in the certificate target `Ztwo`. -/
noncomputable def mpcNu (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) :
    ContinuousMonoidHom (DM alpha h : Type) Ztwo :=
  (ztwoIota.symm : ContinuousMonoidHom (Multiplicative ℤ_[2]) Ztwo).comp
    (mpcNuPadic alpha r p h eta halpha)

@[simp] theorem mpcNuPadic_gen_zero (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) :
    mpcNuPadic alpha r p h eta halpha (dmGen alpha h 0) =
      ofAdd (-((m alpha : ℤ_[2]) * (s r : ℤ_[2]))) := by
  rw [mpcNuPadic, mLiftHom_gen, coreMark_zero]

@[simp] theorem mpcNuPadic_gen_one (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) :
    mpcNuPadic alpha r p h eta halpha (dmGen alpha h 1) = ofAdd (p : ℤ_[2]) := by
  rw [mpcNuPadic, mLiftHom_gen, coreMark_one]

@[simp] theorem mpcNuPadic_gen_two (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) :
    mpcNuPadic alpha r p h eta halpha (dmGen alpha h 2) = ofAdd (s r : ℤ_[2]) := by
  rw [mpcNuPadic, mLiftHom_gen, coreMark_two]

@[simp] theorem mpcNuPadic_gen_three (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) :
    mpcNuPadic alpha r p h eta halpha (dmGen alpha h 3) = ofAdd (eta : ℤ_[2]) := by
  rw [mpcNuPadic, mLiftHom_gen, coreMark_three]

@[simp] theorem mpcNuPadic_gen_handleU (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (j : Fin h) :
    mpcNuPadic alpha r p h eta halpha (dmGen alpha h (handleIdxU j)) = 1 := by
  rw [mpcNuPadic, mLiftHom_gen, coreMark_handleU]

@[simp] theorem mpcNuPadic_gen_handleV (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (j : Fin h) :
    mpcNuPadic alpha r p h eta halpha (dmGen alpha h (handleIdxV j)) = 1 := by
  rw [mpcNuPadic, mLiftHom_gen, coreMark_handleV]

theorem mpcNuPadic_sigma (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) :
    mpcNuPadic alpha r p h eta halpha
      ((Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark .sigma) =
        ofAdd 1 := by
  change mpcNuPadic alpha r p h eta halpha
    (zpowZtwo (isProP_DM alpha h) (dmGen alpha h 3) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = _
  rw [map_zpowZtwo (isProP_DM alpha h) PropOneOne.isProP_two_multPadicInt,
    mpcNuPadic_gen_three, SectionThree.zpowZtwo_ofAdd,
    ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem mpcNuPadic_wild (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (j : Fin (2 + 2 * h + 1)) :
    mpcNuPadic alpha r p h eta halpha
      ((Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark (.wild j)) =
        1 := by
  change mpcNuPadic alpha r p h eta halpha
    (Instances.MProcyclicCore.mpcUnitUntwist (isProP_DM alpha h) alpha r p eta h
      (dmGen alpha h) (nWildIdx h j)) = 1
  have hne := Instances.MCompactCore.nWildIdx_val_ne_two h j
  rcases nCoreIdx_cases (nWildIdx h j) with
      h0 | h1 | h2 | h3 | ⟨k, hU⟩ | ⟨k, hV⟩
  · rw [h0, Instances.MProcyclicCore.mpcUnitUntwist_zero, map_inv, map_mul, map_pow,
      mpcNuPadic_gen_zero, mpcNuPadic_gen_two, ← ofAdd_nsmul, ← ofAdd_add]
    rw [show -((m alpha : ℤ_[2]) * (s r : ℤ_[2])) +
        (m alpha : ℕ) • (s r : ℤ_[2]) = 0 by
      simp only [nsmul_eq_mul]
      ring, ofAdd_zero, inv_one]
  · rw [h1, Instances.MProcyclicCore.mpcUnitUntwist_one, map_mul, map_zpow,
      mpcNuPadic_gen_one]
    have hs : mpcNuPadic alpha r p h eta halpha
        (zpowZtwo (isProP_DM alpha h) (dmGen alpha h 3)
          ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = ofAdd 1 :=
      mpcNuPadic_sigma alpha r p h eta halpha
    rw [hs, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · exact (hne (by rw [h2, coreVal_two])).elim
  · rw [h3, Instances.MProcyclicCore.mpcUnitUntwist_three, map_mul, map_zpow,
      mpcNuPadic_gen_two]
    have hs : mpcNuPadic alpha r p h eta halpha
        (zpowZtwo (isProP_DM alpha h) (dmGen alpha h 3)
          ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = ofAdd 1 :=
      mpcNuPadic_sigma alpha r p h eta halpha
    rw [hs, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · rw [hU, Instances.MProcyclicCore.mpcUnitUntwist_apply_ne _ _ _ _ _ _ _
        (by rw [handleIdxU_val]; omega) (by rw [handleIdxU_val]; omega)
        (by rw [handleIdxU_val]; omega) (by rw [handleIdxU_val]; omega),
      mpcNuPadic_gen_handleU]
  · rw [hV, Instances.MProcyclicCore.mpcUnitUntwist_apply_ne _ _ _ _ _ _ _
        (by rw [handleIdxV_val]; omega) (by rw [handleIdxV_val]; omega)
        (by rw [handleIdxV_val]; omega) (by rw [handleIdxV_val]; omega),
      mpcNuPadic_gen_handleV]

theorem mpcNu_sigma (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) :
    mpcNu alpha r p h eta halpha
      ((Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark .sigma) =
        ztwoOne := by
  apply ztwoIota.injective
  change ztwoIota (ztwoIota.symm (mpcNuPadic alpha r p h eta halpha
    ((Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark .sigma))) =
      ztwoIota ztwoOne
  rw [ztwoIota.apply_symm_apply, ztwoIota_ztwoOne, mpcNuPadic_sigma]

theorem mpcNu_wild (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (j : Fin (2 + 2 * h + 1)) :
    mpcNu alpha r p h eta halpha
      ((Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark (.wild j)) =
        1 := by
  apply ztwoIota.injective
  change ztwoIota (ztwoIota.symm (mpcNuPadic alpha r p h eta halpha
    ((Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark (.wild j)))) =
      ztwoIota 1
  rw [ztwoIota.apply_symm_apply, map_one, mpcNuPadic_wild]

/-! ### Procyclic-row constructors -/

/-- The landed arbitrary-unit Npc presentation specialized to the display stored by the field
selection.  The semantic word remains `npcWUnit ... eta`; the display is used only to prove the
presentation relation. -/
noncomputable def npcPresentation (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    Count.CorePresentation (2 + 2 * handleCount FP (.Npc alpha r eta))
      (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta)
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta))) :=
  Instances.NProcyclicCore.npcCorePresentationUnit alpha r
    (handleCount FP (.Npc alpha r eta)) eta
      (Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display)

/-- Low-level arbitrary-unit Npc constructor for callers carrying a different normalized
orientation.  The canonical constructor `ofNpc` below needs no such binders. -/
noncomputable def ofNpcWithOrientation (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta)
    (nuP : ContinuousMonoidHom
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta)) : Type) Ztwo)
    (hnuSigma : nuP ((npcPresentation S hbranch).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * handleCount FP (.Npc alpha r eta) + 1),
      nuP ((npcPresentation S hbranch).mark (.wild j)) = 1) :
    SelectedCoreLeavesRN S (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta))) nuP := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Instances.NProcyclicCore.npcCorePresentationUnit alpha r
            (handleCount FP (.Npc alpha r eta)) eta display
          nu_sigma := hnuSigma
          nu_wild := hnuWild }

/-- The arbitrary-unit, arbitrary-handle Npc selected core with its canonical orientation. -/
noncomputable def ofNpc (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    SelectedCoreLeavesRN S (DN alpha (handleCount FP (.Npc alpha r eta)))
      (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Instances.NProcyclicCore.npcCorePresentationUnit alpha r
            (handleCount FP (.Npc alpha r eta)) eta display
          nu_sigma := npcNu_sigma alpha r (handleCount FP (.Npc alpha r eta)) eta display
          nu_wild := npcNu_wild alpha r (handleCount FP (.Npc alpha r eta)) eta display }

/-- Low-level selected Mpc constructor from a presentation.  It pins the selected word with the
literal arithmetic parameter `p epsilon r` and the literal selected unit `eta`; no transport to
the old unit-one, handle-zero row is permitted. -/
noncomputable def ofMpcPresentation (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (presentation : Count.CorePresentation
      (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta))
      (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta
        (handleCount FP (.Mpc alpha r epsilon eta)))
      (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta))))
    (nuP : ContinuousMonoidHom
      (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta)) : Type) Ztwo)
    (hnuSigma : nuP (presentation.mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta) + 1),
      nuP (presentation.mark (.wild j)) = 1) :
    SelectedCoreLeavesRN S (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      nuP := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact { presentation := presentation, nu_sigma := hnuSigma, nu_wild := hnuWild }

/-- Branch validity supplies the side condition of the arbitrary-unit Mpc presentation. -/
theorem one_le_alpha_of_Mpc (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) : 1 ≤ alpha := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  omega

/-- The landed arbitrary-unit, arbitrary-handle Mpc presentation specialized to the literal
parameters selected for the field. -/
noncomputable def mpcPresentation (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    Count.CorePresentation (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta))
      (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta
        (handleCount FP (.Mpc alpha r epsilon eta)))
      (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta))) :=
  Instances.MProcyclicCore.mpcCorePresentationUnit alpha r (p epsilon r) eta
    (handleCount FP (.Mpc alpha r epsilon eta)) (one_le_alpha_of_Mpc S hbranch)

/-- Low-level arbitrary-unit Mpc constructor for callers carrying a different normalized
orientation.  The canonical constructor `ofMpc` below needs no such binders. -/
noncomputable def ofMpcWithOrientation (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (nuP : ContinuousMonoidHom
      (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta)) : Type) Ztwo)
    (hnuSigma : nuP ((mpcPresentation S hbranch).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta) + 1),
      nuP ((mpcPresentation S hbranch).mark (.wild j)) = 1) :
    SelectedCoreLeavesRN S
      (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta))) nuP :=
  ofMpcPresentation S hbranch (mpcPresentation S hbranch) nuP hnuSigma hnuWild

/-- The arbitrary-unit, arbitrary-handle Mpc selected core.  Its word retains the literal
arithmetic parameter `p epsilon r`; the orientation uses the same literal `p`. -/
noncomputable def ofMpc (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    SelectedCoreLeavesRN S (DM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (mpcNu alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) eta
        (one_le_alpha_of_Mpc S hbranch)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      have halpha : 1 ≤ alpha := le_trans (by omega) valid.1
      exact
        { presentation := Instances.MProcyclicCore.mpcCorePresentationUnit alpha r
            (p epsilon r) eta (handleCount FP (.Mpc alpha r epsilon eta)) halpha
          nu_sigma := mpcNu_sigma alpha r (p epsilon r)
            (handleCount FP (.Mpc alpha r epsilon eta)) eta halpha
          nu_wild := mpcNu_wild alpha r (p epsilon r)
            (handleCount FP (.Mpc alpha r epsilon eta)) eta halpha }

/-- Constructor-table regression: every arbitrary-unit Npc row has fully derived structural
core leaves at its selected handle count. -/
theorem exists_of_branch_Npc (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SelectedCoreLeavesRN S P nuP) :=
  ⟨DN alpha (handleCount FP (.Npc alpha r eta)),
    npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta, ⟨ofNpc S hbranch⟩⟩

/-- Constructor-table regression: every arbitrary-unit Mpc row, with literal `p epsilon r`,
has fully derived structural core leaves at its selected handle count. -/
theorem exists_of_branch_Mpc (S : FieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SelectedCoreLeavesRN S P nuP) :=
  ⟨DM alpha (handleCount FP (.Mpc alpha r epsilon eta)),
    mpcNu alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) eta
      (one_le_alpha_of_Mpc S hbranch), ⟨ofMpc S hbranch⟩⟩

/-- **The L-row constructor.**  A field selection on the improved square-word row has a
canonical structural core, with no certificate assumptions: `DSq` supplies the universal
property and `LSquareCore.lNu` supplies both normalization equations at every handle count. -/
noncomputable def ofL (S : FieldBranchSelection K FP Q W) (hbranch : S.branch = .L) :
    SelectedCoreLeavesRN S (SqCore.DSq (handleCount FP .L))
      (Instances.LSquareCore.lNu (handleCount FP .L)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Instances.LSquareCore.lCorePresentation (handleCount FP .L)
          nu_sigma := Instances.LSquareCore.lNu_sigma (handleCount FP .L)
          nu_wild := Instances.LSquareCore.lNu_wild (handleCount FP .L) }

/-- Constructor-table regression: an L selection has a fully derived structural core, rather
than a certificate-supplied presentation or normalization row. -/
theorem exists_of_branch_L (S : FieldBranchSelection K FP Q W) (hbranch : S.branch = .L) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SelectedCoreLeavesRN S P nuP) :=
  ⟨SqCore.DSq (handleCount FP .L), Instances.LSquareCore.lNu (handleCount FP .L),
    ⟨ofL S hbranch⟩⟩

/-- **Five-row structural regression.**  Every field-selected improved presentation has a
presented pro-`2` core and a canonically normalized `Ztwo` orientation. -/
theorem exists_of_fieldSelection (S : FieldBranchSelection K FP Q W) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SelectedCoreLeavesRN S P nuP) := by
  cases hbranch : S.branch with
  | L => exact exists_of_branch_L S hbranch
  | N0 alpha => exact exists_of_branch_N0 S hbranch
  | Npc alpha r eta => exact exists_of_branch_Npc S hbranch
  | M0 alpha => exact exists_of_branch_M0 S hbranch
  | Mpc alpha r epsilon eta => exact exists_of_branch_Mpc S hbranch

/-- `WordCertificateRN.coreRel` and `proTwoWord` contain no mathematical residue: choosing the
evaluated pro-`2` word makes the requested equality reflexive. -/
def coreRel (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking S.semantic.degree G) : G :=
  t.eval (pro2 S.semantic.word)

theorem proTwoWord (_C : SelectedCoreLeavesRN S P nuP)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking S.semantic.degree G) :
    t.eval (pro2 S.semantic.word) = coreRel G t := rfl

/-- The selected candidate's map to its presented pro-`2` core. -/
noncomputable def pro2 (C : SelectedCoreLeavesRN S P nuP) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR S.semantic.degree q S.semantic.word) : Type) P :=
  Count.CorePresentation.coreHom C.presentation hq0 hqe

/-- The core map has exactly the maximal pro-`2` kernel. -/
theorem ker_pro2 (C : SelectedCoreLeavesRN S P nuP) (hq0 : q ≠ 0) (hqe : Even q) :
    (C.pro2 hq0 hqe).toMonoidHom.ker =
      proPKernel 2 ((GammaR S.semantic.degree q S.semantic.word) : Type) :=
  Count.CorePresentation.ker_coreHom C.presentation hq0 hqe

/-- The core map is onto. -/
theorem hpro2 (C : SelectedCoreLeavesRN S P nuP) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (C.pro2 hq0 hqe) :=
  Count.CorePresentation.coreHom_surjective C.presentation hq0 hqe

/-- Cyclotomic compatibility follows from the two normalization rows. -/
theorem compat (C : SelectedCoreLeavesRN S P nuP) (hq0 : q ≠ 0) (hqe : Even q) :
    ∀ g : ((GammaR S.semantic.degree q S.semantic.word) : Type),
      nuTq q (tameOfSpec S.semantic.degree q S.semantic.word
        (tameSpecialization_of_fieldSelection S hq0 hqe) g) = nuP (C.pro2 hq0 hqe g) :=
  Count.CorePresentation.nu_compat_coreHom C.presentation hq0 hqe
    (tameSpecialization_of_fieldSelection S hq0 hqe) nuP C.nu_sigma C.nu_wild

end SelectedCoreLeavesRN

/-! ## The analytic residue, separated from the core -/

/-- The three analytic bundles not supplied by the improved word constructors or the generic
core bridge.  Their dependent arguments are the derived tame specialization, core map, and
compatibility theorem, so they cannot conceal an alternative presentation. -/
structure SelectedAnalyticLeavesRN
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) (q : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    (hq0 : q ≠ 0) (hqe : Even q) (C : SelectedCoreLeavesRN S P nuP) where
  stokes : StokesDualityCertificate
    (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
    (standardNumerics S.semantic.degree)
    (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))
  scalar : ScalarHilbertCertificate
    (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree
    (standardNumerics S.semantic.degree)
    (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))
  determinant : AffineDeterminantCertificate
    (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
    (standardNumerics S.semantic.degree)
    (tameOfSpec S.semantic.degree q S.semantic.word
      (tameSpecialization_of_fieldSelection S hq0 hqe))
    (C.pro2 hq0 hqe) (C.compat hq0 hqe)
    (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))

/-! ## The non-routine certificate leaves -/

/-- The genuinely presentation/source-specific fields of `WordCertificateRN` for a selected
improved word, now split into exact structural and analytic residues.  All routine fields and
all consequences of the presented core are deliberately absent and reconstructed below.

Keeping `stokes`, `scalar`, and `determinant` explicit is honest: the five word-level
`exactLiftingRN` constructors do not prove those source-side analytic certificates. -/
structure SelectedWordLeavesRN
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) (q : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    (hq0 : q ≠ 0) (hqe : Even q) where
  core : SelectedCoreLeavesRN S P nuP
  analytic : SelectedAnalyticLeavesRN S q P hP nuP hq0 hqe core

/-- Assemble the corrected word certificate for the selected improved presentation. -/
noncomputable def wordCertificateRN_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) where
  tameSpecialization := tameSpecialization_of_fieldSelection S hq0 hqe
  coreRel := SelectedCoreLeavesRN.coreRel
  proTwoWord := L.core.proTwoWord
  pro2 := L.core.pro2 hq0 hqe
  ker_pro2 := L.core.ker_pro2 hq0 hqe
  hpro2 := L.core.hpro2 hq0 hqe
  compat := L.core.compat hq0 hqe
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLiftingRN_of_selectedHsimp S hsimp hq0 hqe nuP
  stokes := L.analytic.stokes
  scalar := L.analytic.scalar
  determinant := L.analytic.determinant
  htame := Count.htame_of_tameSpecializes (tameSpecialization_of_fieldSelection S hq0 hqe)
  hwild := Count.hwild_of_tameSpecializes (tameSpecialization_of_fieldSelection S hq0 hqe)

/-! ### Exact structural-field regressions -/

/-- The assembled certificate's tame specialization is exactly the five-row dispatch above. -/
@[simp] theorem wordCertificateRN_of_fieldSelection_tameSpecialization
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).tameSpecialization =
      tameSpecialization_of_fieldSelection S hq0 hqe := rfl

/-- The two formerly caller-supplied word-level fields are definitionally the tautological
evaluation and its reflexivity proof. -/
@[simp] theorem wordCertificateRN_of_fieldSelection_coreRel
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).coreRel =
      SelectedCoreLeavesRN.coreRel := rfl

@[simp] theorem wordCertificateRN_of_fieldSelection_proTwoWord
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).proTwoWord =
      L.core.proTwoWord := rfl

/-- All four pro-`2` fields use the one generic map classified by the presented core. -/
@[simp] theorem wordCertificateRN_of_fieldSelection_pro2
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).pro2 =
      L.core.pro2 hq0 hqe := rfl

@[simp] theorem wordCertificateRN_of_fieldSelection_ker_pro2
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).ker_pro2 =
      L.core.ker_pro2 hq0 hqe := rfl

@[simp] theorem wordCertificateRN_of_fieldSelection_hpro2
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).hpro2 =
      L.core.hpro2 hq0 hqe := rfl

@[simp] theorem wordCertificateRN_of_fieldSelection_compat
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    (wordCertificateRN_of_fieldSelection S hsimp hq0 hqe L).compat =
      L.core.compat hq0 hqe := rfl

/-! ## Corrected reconstruction consequence -/

/-- The unified certificate supply theorem, at its strongest current conclusion: the selected
improved word defines the same profinite group as any corrected reference certificate over the
same boundary slot and standard degree numerics.  This is a direct application of the RN
reconstruction capstone, not a premise of the leaf record. -/
theorem nonempty_continuousMulEquiv_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq2 : 2 ≤ q) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (hnuP : Function.Surjective nuP)
    (L : SelectedWordLeavesRN S q P hP nuP (by omega) hqe)
    {Rref : PWord (Generator S.semantic.degree)}
    (Wref : WordCertificateRN S.semantic.degree q Rref P hP nuP
      (standardNumerics S.semantic.degree)) :
    Nonempty (ContinuousMulEquiv
      (GammaR S.semantic.degree q S.semantic.word)
      (GammaR S.semantic.degree q Rref)) :=
  nonempty_continuousMulEquiv_of_wordCertificatesRN
    (wordCertificateRN_of_fieldSelection S hsimp (by omega) hqe L) Wref hq2 hqe hnuP

/-! ## Canonical arithmetic wrapper -/

/-- Apply the supply interface directly to the canonical field-family witness.  The only
classification input is `CanonicalFieldBranchWitness`; arbitrary M/N orientation units are not
reintroduced. -/
noncomputable def wordCertificateRN_of_canonicalFieldBranch
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (CW : CanonicalFieldBranchWitness D.params (B.fieldMarkedPair FF))
    {q : ℕ} (hsimp : SelectedHsimp (selectFieldBranchCanonical B FF D RI CW) q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN (selectFieldBranchCanonical B FF D RI CW) q P hP nuP hq0 hqe) :
    WordCertificateRN
      (selectFieldBranchCanonical B FF D RI CW).semantic.degree q
      (selectFieldBranchCanonical B FF D RI CW).semantic.word P hP nuP
      (standardNumerics (selectFieldBranchCanonical B FF D RI CW).semantic.degree) :=
  wordCertificateRN_of_fieldSelection (selectFieldBranchCanonical B FF D RI CW)
    hsimp hq0 hqe L

/-! ## Constructor-table regressions -/

/-- L regression: the selected certificate carrier is the improved square word. -/
theorem selectedWord_L
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) (hbranch : S.branch = .L) :
    HEq S.semantic.word (Words.LSq.lSqW (handleCount FP .L)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

/-- Compact-N regression: the selected certificate carrier is `nCompactW`. -/
theorem selectedWord_N0
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha : ℕ} (hbranch : S.branch = .N0 alpha) :
    HEq S.semantic.word (Words.nCompactW alpha (handleCount FP (.N0 alpha))) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

/-- Procyclic-N regression: the arbitrary selected unit remains in `npcWUnit`. -/
theorem selectedWord_Npc
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) :
    HEq S.semantic.word
      (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

/-- Compact-M regression: the selected certificate carrier is `mCompactW`. -/
theorem selectedWord_M0
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    HEq S.semantic.word (Words.MCompact.mCompactW alpha (handleCount FP (.M0 alpha))) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

/-- Procyclic-M regression: both the arbitrary unit and literal `p epsilon r` remain visible. -/
theorem selectedWord_Mpc
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    HEq S.semantic.word (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta
      (handleCount FP (.Mpc alpha r epsilon eta))) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

end

end GQ2.Dyadic
