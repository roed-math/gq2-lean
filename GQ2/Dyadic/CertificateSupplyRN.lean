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

The current direct branch coverage is deliberately not overstated.  `nCorePresentation`,
`mCorePresentation`, and `LSquareCore.lCorePresentation` provide the compact N/M and L
presentations at every handle count.  `npcCorePresentationUnit` now provides the arbitrary-unit
procyclic-N presentation, but its alphabet normalization is not the compact-N normalization and
there is not yet a canonical `Ztwo` orientation for that dictionary.  The arbitrary-unit Mpc
lane still needs its inverse dictionary and `CorePresentation`; `ofMpcPresentation` below pins
the exact interface that result will enter.  These are constructor/orientation-supply gaps for
this record, not additional certificate fields. -/
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

/-! ### Procyclic-row interfaces -/

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

/-- The arbitrary-unit Npc constructor with its exact remaining orientation interface.
Presentation supply is unconditional; only a `Ztwo` map normalized on this procyclic alphabet
is explicit.  In particular, this does not silently reuse the incompatible compact-N rows. -/
noncomputable def ofNpc (S : FieldBranchSelection K FP Q W)
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

/-- Preparation seam for the expected arbitrary-unit Mpc `CorePresentation`.  It pins the
selected word with the literal arithmetic parameter `p epsilon r` and the literal selected
unit `eta`; once `mpcCorePresentationUnit` lands, it is passed as `presentation` without any
transport to the old unit-one, handle-zero row. -/
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
