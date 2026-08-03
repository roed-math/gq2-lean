/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyRN

/-!
# Witness-polymorphic certificate supply for the corrected field selector

`CertificateSupplyRN` predates the family-corrected selector and its public records are indexed
by the legacy `FieldBranchSelection`.  That concrete type cannot represent a valid `N` family:
its arithmetic `Matches` field demands the contradictory product splitting.

This file isolates the exact interface actually consumed downstream: the chosen branch, its
validity, and its display.  Both selector types forget to this semantic view, while all
witness-specific arithmetic matching stays upstream.  The corrected `FamilyFieldBranchSelection`
therefore reaches Stokes residue dispatch, selected cores, and `WordCertificateRN` without ever
constructing a legacy `FieldBranchWitness`.
-/

namespace GQ2.Dyadic

open GQ2
open TameSpec
open GQ2.Dyadic.Count

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-- The minimal selector interface consumed by improved-word certificate supply. -/
structure SemanticSelectionView (FP : FieldParameters) where
  branch : BranchData
  valid : branch.Valid
  display : branch.DisplayFor

namespace SemanticSelectionView

/-- The improved semantic presentation determined by a selection view. -/
def semantic {FP : FieldParameters} (S : SemanticSelectionView FP) : SemanticPresentation :=
  SemanticPresentation.ofBranch (handleCount FP S.branch) S.branch

/-- Forget witness-specific arithmetic matching from the legacy selector. -/
def ofFieldBranchSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) : SemanticSelectionView FP :=
  ⟨S.branch, S.valid, S.display⟩

/-- Forget witness-specific arithmetic matching from the corrected family selector. -/
def ofFamilyFieldBranchSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) : SemanticSelectionView FP :=
  ⟨S.branch, S.valid, S.display⟩

@[simp] theorem ofFieldBranchSelection_branch
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) :
    (ofFieldBranchSelection S).branch = S.branch := rfl

@[simp] theorem ofFamilyFieldBranchSelection_branch
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) :
    (ofFamilyFieldBranchSelection S).branch = S.branch := rfl

@[simp] theorem ofFieldBranchSelection_semantic
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) :
    (ofFieldBranchSelection S).semantic = S.semantic := rfl

@[simp] theorem ofFamilyFieldBranchSelection_semantic
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) :
    (ofFamilyFieldBranchSelection S).semantic = S.semantic := rfl

end SemanticSelectionView

/-- The unique branch-dependent Stokes residue over the witness-polymorphic view. -/
inductive SemanticSelectedHsimpRN {FP : FieldParameters}
    (S : SemanticSelectionView FP) (q : ℕ) : Prop
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

/-- Dispatch exact lifting using only the semantic view. -/
theorem exactLiftingRN_of_semanticSelectedHsimp
    {FP : FieldParameters} (S : SemanticSelectionView FP) {q : ℕ}
    (hsimp : SemanticSelectedHsimpRN S q) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN
      (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
      (standardNumerics S.semantic.degree) := by
  cases hsimp with
  | L hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 * handleCount FP .L + 1) q
              (Words.LSq.lSqW (handleCount FP .L)))
            (2 * handleCount FP .L + 1) q P nuP
            (standardNumerics (2 * handleCount FP .L + 1))
          exact LSquare.exactLiftingRN_of_pushed hsimp hqe nuP
  | N0 alpha hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 + 2 * handleCount FP (.N0 alpha)) q
              (Words.nCompactW alpha (handleCount FP (.N0 alpha))))
            (2 + 2 * handleCount FP (.N0 alpha)) q P nuP
            (standardNumerics (2 + 2 * handleCount FP (.N0 alpha)))
          have hn : 2 * handleCount FP (.N0 alpha) + 2 =
              2 + 2 * handleCount FP (.N0 alpha) := by omega
          exact NCompact.exactLiftingRN_standard_congr hn
            (NCompact.exactLiftingRN hsimp (le_trans (by omega) valid) hq0 hqe nuP)
  | Npc alpha r eta hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 + 2 * handleCount FP (.Npc alpha r eta)) q
              (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta))
            (2 + 2 * handleCount FP (.Npc alpha r eta)) q P nuP
            (standardNumerics (2 + 2 * handleCount FP (.Npc alpha r eta)))
          have hn : 2 * handleCount FP (.Npc alpha r eta) + 2 =
              2 + 2 * handleCount FP (.Npc alpha r eta) := by omega
          exact NProcyclic.exactLiftingRN_standard_congr hn
            (NProcyclic.exactLiftingRN display hsimp
              (le_trans (by omega) valid.1) hqe nuP)
  | M0 alpha hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 + 2 * handleCount FP (.M0 alpha)) q
              (Words.MCompact.mCompactW alpha (handleCount FP (.M0 alpha))))
            (2 + 2 * handleCount FP (.M0 alpha)) q P nuP
            (standardNumerics (2 + 2 * handleCount FP (.M0 alpha)))
          have hn : 2 * handleCount FP (.M0 alpha) + 2 =
              2 + 2 * handleCount FP (.M0 alpha) := by omega
          exact MCompact.exactLiftingRN_standard_congr hn
            (MCompact.exactLiftingRN hsimp (le_trans (by omega) valid) hq0 hqe nuP)
  | Mpc alpha r epsilon eta hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q
              (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta
                (handleCount FP (.Mpc alpha r epsilon eta))))
            (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q P nuP
            (standardNumerics (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)))
          have hn : 2 * handleCount FP (.Mpc alpha r epsilon eta) + 2 =
              2 + 2 * handleCount FP (.Mpc alpha r epsilon eta) := by omega
          exact NProcyclic.exactLiftingRN_standard_congr hn
            (MProcyclicExact.exactLiftingRN display hsimp
              (le_trans (by omega) valid.1) valid.2 hqe nuP)

/-- Tame specialization of the improved word depends only on the semantic view. -/
theorem tameSpecialization_of_semanticSelection
    {FP : FieldParameters} (S : SemanticSelectionView FP) {q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes S.semantic.degree q S.semantic.word := by
  cases S with
  | mk branch valid display =>
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

/-- The structural certificate residue over the witness-polymorphic semantic view. -/
structure SemanticSelectedCoreLeavesRN
    {FP : FieldParameters} (S : SemanticSelectionView FP) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) where
  presentation : Count.CorePresentation S.semantic.degree S.semantic.word P
  nu_sigma : nuP (presentation.mark .sigma) = ztwoOne
  nu_wild : ∀ j : Fin (S.semantic.degree + 1), nuP (presentation.mark (.wild j)) = 1

namespace SemanticSelectedCoreLeavesRN

variable {FP : FieldParameters} {S : SemanticSelectionView FP} {q : ℕ}
  {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-- Compact-N structural leaves over the common view. -/
noncomputable def ofN0 (S : SemanticSelectionView FP) {alpha : ℕ}
    (hbranch : S.branch = .N0 alpha) :
    SemanticSelectedCoreLeavesRN S
      (MarkedCore.DN alpha (handleCount FP (.N0 alpha)))
      (SelectedCoreLeavesRN.nNuZtwo alpha (handleCount FP (.N0 alpha))) := by
  cases S with
  | mk branch valid display =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Count.PilotN.nCorePresentation alpha (handleCount FP (.N0 alpha))
          nu_sigma := SelectedCoreLeavesRN.nNuZtwo_sigma alpha (handleCount FP (.N0 alpha))
          nu_wild := SelectedCoreLeavesRN.nNuZtwo_wild alpha (handleCount FP (.N0 alpha)) }

/-- Constructor regression: compact N is fully supplied through the corrected selection view. -/
theorem exists_of_branch_N0 (S : SemanticSelectionView FP) {alpha : ℕ}
    (hbranch : S.branch = .N0 alpha) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN S P nuP) :=
  ⟨MarkedCore.DN alpha (handleCount FP (.N0 alpha)),
    SelectedCoreLeavesRN.nNuZtwo alpha (handleCount FP (.N0 alpha)), ⟨ofN0 S hbranch⟩⟩

/-- The arbitrary-unit Npc presentation selected by the view's stored display. -/
noncomputable def npcPresentation (S : SemanticSelectionView FP)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    Count.CorePresentation (2 + 2 * handleCount FP (.Npc alpha r eta))
      (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta)
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta))) :=
  Instances.NProcyclicCore.npcCorePresentationUnit alpha r
    (handleCount FP (.Npc alpha r eta)) eta
      (Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display)

/-- Npc structural leaves; only the normalized `Ztwo` orientation remains explicit.
The presentation and its arbitrary selected eta are derived. -/
noncomputable def ofNpc (S : SemanticSelectionView FP)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta)
    (nuP : ContinuousMonoidHom
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta)) : Type) Ztwo)
    (hnuSigma : nuP ((npcPresentation S hbranch).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * handleCount FP (.Npc alpha r eta) + 1),
      nuP ((npcPresentation S hbranch).mark (.wild j)) = 1) :
    SemanticSelectedCoreLeavesRN S
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta))) nuP := by
  cases S with
  | mk branch valid display =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Instances.NProcyclicCore.npcCorePresentationUnit alpha r
            (handleCount FP (.Npc alpha r eta)) eta display
          nu_sigma := hnuSigma
          nu_wild := hnuWild }

/-- The tautological pro-`2` evaluation relator. -/
def coreRel (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking S.semantic.degree G) : G :=
  t.eval (pro2 S.semantic.word)

theorem proTwoWord (_C : SemanticSelectedCoreLeavesRN S P nuP)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking S.semantic.degree G) :
    t.eval (pro2 S.semantic.word) = coreRel G t := rfl

/-- The selected candidate's map to its presented pro-`2` core. -/
noncomputable def pro2 (C : SemanticSelectedCoreLeavesRN S P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR S.semantic.degree q S.semantic.word) : Type) P :=
  Count.CorePresentation.coreHom C.presentation hq0 hqe

theorem ker_pro2 (C : SemanticSelectedCoreLeavesRN S P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) :
    (C.pro2 hq0 hqe).toMonoidHom.ker =
      proPKernel 2 ((GammaR S.semantic.degree q S.semantic.word) : Type) :=
  Count.CorePresentation.ker_coreHom C.presentation hq0 hqe

theorem hpro2 (C : SemanticSelectedCoreLeavesRN S P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) : Function.Surjective (C.pro2 hq0 hqe) :=
  Count.CorePresentation.coreHom_surjective C.presentation hq0 hqe

theorem compat (C : SemanticSelectedCoreLeavesRN S P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) :
    ∀ g : ((GammaR S.semantic.degree q S.semantic.word) : Type),
      nuTq q (tameOfSpec S.semantic.degree q S.semantic.word
        (tameSpecialization_of_semanticSelection S hq0 hqe) g) = nuP (C.pro2 hq0 hqe g) :=
  Count.CorePresentation.nu_compat_coreHom C.presentation hq0 hqe
    (tameSpecialization_of_semanticSelection S hq0 hqe) nuP C.nu_sigma C.nu_wild

end SemanticSelectedCoreLeavesRN

/-- The three genuinely analytic leaves over the witness-polymorphic view. -/
structure SemanticSelectedAnalyticLeavesRN
    {FP : FieldParameters} (S : SemanticSelectionView FP) (q : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    (hq0 : q ≠ 0) (hqe : Even q) (C : SemanticSelectedCoreLeavesRN S P nuP) where
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
      (tameSpecialization_of_semanticSelection S hq0 hqe))
    (C.pro2 hq0 hqe) (C.compat hq0 hqe)
    (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))

/-- All remaining leaves for assembling a corrected word certificate from a semantic view. -/
structure SemanticSelectedWordLeavesRN
    {FP : FieldParameters} (S : SemanticSelectionView FP) (q : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    (hq0 : q ≠ 0) (hqe : Even q) where
  core : SemanticSelectedCoreLeavesRN S P nuP
  analytic : SemanticSelectedAnalyticLeavesRN S q P hP nuP hq0 hqe core

/-- Assemble a corrected word certificate from the witness-polymorphic semantic view. -/
noncomputable def wordCertificateRN_of_semanticSelection
    {FP : FieldParameters} (S : SemanticSelectionView FP) {q : ℕ}
    (hsimp : SemanticSelectedHsimpRN S q) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN S q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) where
  tameSpecialization := tameSpecialization_of_semanticSelection S hq0 hqe
  coreRel := SemanticSelectedCoreLeavesRN.coreRel
  proTwoWord := L.core.proTwoWord
  pro2 := L.core.pro2 hq0 hqe
  ker_pro2 := L.core.ker_pro2 hq0 hqe
  hpro2 := L.core.hpro2 hq0 hqe
  compat := L.core.compat hq0 hqe
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLiftingRN_of_semanticSelectedHsimp S hsimp hq0 hqe nuP
  stokes := L.analytic.stokes
  scalar := L.analytic.scalar
  determinant := L.analytic.determinant
  htame := Count.htame_of_tameSpecializes (tameSpecialization_of_semanticSelection S hq0 hqe)
  hwild := Count.hwild_of_tameSpecializes (tameSpecialization_of_semanticSelection S hq0 hqe)

/-- Direct certificate handoff for a corrected family selection, including genuine `N` data. -/
noncomputable def wordCertificateRN_of_familyFieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) {q : ℕ}
    (hsimp : SemanticSelectedHsimpRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) :=
  wordCertificateRN_of_semanticSelection
    (SemanticSelectionView.ofFamilyFieldBranchSelection S) hsimp hq0 hqe L

/-- End-to-end certificate handoff from the corrected arithmetic selector itself. -/
noncomputable def wordCertificateRN_of_familyFieldBranch
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) {q : ℕ}
    (hsimp : SemanticSelectedHsimpRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection
        (selectFieldBranchFamily B FF D RI W)) q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection
        (selectFieldBranchFamily B FF D RI W)) q P hP nuP hq0 hqe) :
    WordCertificateRN
      (selectFieldBranchFamily B FF D RI W).semantic.degree q
      (selectFieldBranchFamily B FF D RI W).semantic.word P hP nuP
      (standardNumerics (selectFieldBranchFamily B FF D RI W).semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection
    (selectFieldBranchFamily B FF D RI W) hsimp hq0 hqe L

end

end GQ2.Dyadic
