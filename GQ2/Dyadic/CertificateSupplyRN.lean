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
the tame specialization, the marked pro-`2` quotient and its cyclotomic compatibility, and the
three remaining analytic bundles.  In particular it does not ask for `ExactLiftingSemanticsRN`,
`StageSep`, `StageZ`, or any copy of the reconstruction conclusion.
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

/-! ## The non-routine certificate leaves -/

/-- The genuinely presentation/source-specific fields of `WordCertificateRN` for a selected
improved word.  The seven routine fields (`tfg`, the scalar-action trio, `htame`, `hwild`, and
corrected exact lifting) are deliberately absent and are reconstructed below.

Keeping `stokes`, `scalar`, and `determinant` explicit is honest: the five word-level
`exactLiftingRN` constructors do not prove those source-side analytic certificates. -/
structure SelectedWordLeavesRN
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) (q : ℕ) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo) where
  tameSpecialization : TameSpecializes S.semantic.degree q S.semantic.word
  coreRel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G], Marking S.semantic.degree G → G
  proTwoWord : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking S.semantic.degree G),
    t.eval (pro2 S.semantic.word) = coreRel G t
  pro2 : ContinuousMonoidHom ((GammaR S.semantic.degree q S.semantic.word) : Type) P
  ker_pro2 : pro2.toMonoidHom.ker =
    proPKernel 2 ((GammaR S.semantic.degree q S.semantic.word) : Type)
  hpro2 : Function.Surjective pro2
  compat : ∀ g : ((GammaR S.semantic.degree q S.semantic.word) : Type),
    nuTq q (tameOfSpec S.semantic.degree q S.semantic.word tameSpecialization g) = nuP (pro2 g)
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
    (tameOfSpec S.semantic.degree q S.semantic.word tameSpecialization) pro2 compat
    (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))

/-- Assemble the corrected word certificate for the selected improved presentation. -/
noncomputable def wordCertificateRN_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hsimp : SelectedHsimp S q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SelectedWordLeavesRN S q P hP nuP) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) where
  tameSpecialization := L.tameSpecialization
  coreRel := L.coreRel
  proTwoWord := L.proTwoWord
  pro2 := L.pro2
  ker_pro2 := L.ker_pro2
  hpro2 := L.hpro2
  compat := L.compat
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLiftingRN_of_selectedHsimp S hsimp hq0 hqe nuP
  stokes := L.stokes
  scalar := L.scalar
  determinant := L.determinant
  htame := Count.htame_of_tameSpecializes L.tameSpecialization
  hwild := Count.hwild_of_tameSpecializes L.tameSpecialization

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
    (hnuP : Function.Surjective nuP) (L : SelectedWordLeavesRN S q P hP nuP)
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
    (L : SelectedWordLeavesRN (selectFieldBranchCanonical B FF D RI CW) q P hP nuP) :
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
