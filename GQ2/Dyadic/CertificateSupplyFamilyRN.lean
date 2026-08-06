/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyRN
import GQ2.Dyadic.Instances.GammaLActionImageDevissage
import GQ2.Dyadic.Instances.NpcUnramifiedScalar
import GQ2.Dyadic.Instances.MpcUnramifiedBranch

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

The `L` case of the Stokes residue is no longer hypothesis-shaped: the action-image theorem
(`LSquare.uniformPushedHsimp_of_actionImage`) proves the uniform interface from `Even q` alone,
and the `LUniform` case plus `SemanticSelectedHsimpRN.of_L_actionImage` feed it into the same
five-row assembler.  The legacy `L`/`LResolved` cases remain as compatibility entry points.

The procyclic-`N` case is now theorem-shaped in the same way, one branch further along: both of
its action-image obligations are discharged (`NProcyclicUnram.uniformPushedHsimp`), so from
branch validity and `Even q` the row's uniform residue follows outright once the selected display
is read as a `2`-adic unit.  `NpcUniform` plus `SemanticSelectedHsimpRN.of_Npc_actionImage` — and
`SelectedHsimp.of_Npc_actionImage` for the legacy selector — feed it into the assembler.  This
file is where the two are stated because the `Npc` branch files first become visible here; the
`NpcUniform` constructors themselves live with their rows.

The procyclic-`M` case is migrated to the same shape but does **not** reach the same conclusion.
`MpcUniform` carries `MProcyclicExact.UniformHsimp`, and
`SemanticSelectedHsimpRN.of_Mpc_actionImage`
routes the branch through `MProcyclicExact.uniformPushedHsimp_of_pairings`; but that theorem still
binds three named second-order inputs — `UnramifiedNormalPairingIsCompact`,
`ScalarActionImageStokes` and `RamifiedNormalPairingSeparates` — so the `Mpc` producers carry them
as explicit hypotheses.  What the selected row *does* discharge for free is the arithmetic input:
`MpcDisplayFor.represents` is exactly the `RepresentsUnit` obligation, and branch validity supplies
`2 ≤ α` and `1 ≤ r`.  So the `Mpc` row is three second-order statements away from the
unconditionality the `L` and `Npc` rows already have, and not one step more.
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

/-- The unique branch-dependent Stokes residue over the witness-polymorphic view.

For L, `L` preserves the legacy pushed-resolver bundle while `LResolved` stores only the
target-local resolver required by the exact-lifting count.  `LUniform` carries the
coefficient-independent uniform-word interface, which the action-image theorem proves outright
for even `q` (`SemanticSelectedHsimpRN.of_L_actionImage`); on the `L` row the residue is
therefore a theorem, not a hypothesis.

For procyclic `N`, `Npc` preserves the historical all-markings bundle while `NpcUniform` carries
the row's uniform residue `NProcyclic.UniformHsimp`, which is likewise a theorem
(`SemanticSelectedHsimpRN.of_Npc_actionImage`): branch validity and `Even q` are its only inputs,
because the selected display is a `2`-adic unit by
`NpcDisplayFor.exists_toPadic_eq_one_add_two_mul`.

For procyclic `M`, `Mpc` preserves the historical all-markings bundle while `MpcUniform` carries
the row's uniform residue `MProcyclicExact.UniformHsimp`.  That one is *not* a theorem yet:
`SemanticSelectedHsimpRN.of_Mpc_actionImage` still binds the row's three second-order inputs.  The
two compact rows are unchanged. -/
inductive SemanticSelectedHsimpRN {FP : FieldParameters}
    (S : SemanticSelectionView FP) (q : ℕ) : Prop
  | L (hbranch : S.branch = .L)
      (hsimp : LSquare.PushedHsimp (handleCount FP .L) q)
  | LResolved (hbranch : S.branch = .L)
      (hsimp : LSquare.ResolvedPushedHsimp (handleCount FP .L) q)
  | LUniform (hbranch : S.branch = .L)
      (hsimp : LSquare.UniformPushedHsimp (handleCount FP .L) q)
  | N0 (alpha : ℕ) (hbranch : S.branch = .N0 alpha)
      (hsimp : NCompact.Hsimp alpha (handleCount FP (.N0 alpha)) q)
  | Npc (alpha r : ℕ) (eta : ℤ_[2]ˣ) (hbranch : S.branch = .Npc alpha r eta)
      (hsimp : NProcyclic.Hsimp alpha r (handleCount FP (.Npc alpha r eta)) q
        (hbranch ▸ S.display).data)
  | NpcUniform (alpha r : ℕ) (eta : ℤ_[2]ˣ) (hbranch : S.branch = .Npc alpha r eta)
      (hsimp : NProcyclic.UniformHsimp alpha r (handleCount FP (.Npc alpha r eta)) q
        (hbranch ▸ S.display).data)
  | M0 (alpha : ℕ) (hbranch : S.branch = .M0 alpha)
      (hsimp : MCompact.Hsimp alpha (handleCount FP (.M0 alpha)) q)
  | Mpc (alpha r : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ)
      (hbranch : S.branch = .Mpc alpha r epsilon eta)
      (hsimp : MProcyclicExact.Hsimp alpha r (p epsilon r)
        (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
  | MpcUniform (alpha r : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ)
      (hbranch : S.branch = .Mpc alpha r epsilon eta)
      (hsimp : MProcyclicExact.UniformHsimp alpha r (p epsilon r)
        (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)

/-- **The L Stokes residue is a theorem.**  For even `q`, the action-image route
(`LSquare.uniformPushedHsimp_of_actionImage`) supplies the `L` case of the five-row residue
with no hypothesis beyond the branch equation; no pushed or resolved bundle is ever
constructed. -/
theorem SemanticSelectedHsimpRN.of_L_actionImage {FP : FieldParameters}
    {S : SemanticSelectionView FP} {q : ℕ} (hbranch : S.branch = .L) (hqe : Even q) :
    SemanticSelectedHsimpRN S q :=
  .LUniform hbranch (LSquare.uniformPushedHsimp_of_actionImage hqe)

/-- **The procyclic-`N` Stokes residue is a theorem.**  Both action-image branches of the row are
discharged in `NProcyclicUnram.uniformPushedHsimp`, whose remaining inputs are `2 ≤ α` — supplied
by `BranchData.Valid (.Npc α r η)` — and a witness that the display denotes a `2`-adic unit
`1 + 2z` — supplied by the selected display itself.  So for even `q` the `Npc` case of the
five-row residue needs no hypothesis beyond the branch equation, exactly as the `L` case does. -/
theorem SemanticSelectedHsimpRN.of_Npc_actionImage {FP : FieldParameters}
    {S : SemanticSelectionView FP} {q alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) (hqe : Even q) :
    SemanticSelectedHsimpRN S q := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  obtain ⟨z, hz⟩ := NpcDisplayFor.exists_toPadic_eq_one_add_two_mul (hbranch ▸ S.display)
  exact .NpcUniform alpha r eta hbranch
    (NProcyclicUnram.uniformPushedHsimp hvalid.1 hqe z hz)

/-- The same theorem for the legacy selector's residue `SelectedHsimp`.  It is stated here rather
than beside its inductive in `CertificateSupplyRN` because the procyclic-`N` branch files, which
supply the residue, first become visible in this file. -/
theorem SelectedHsimp.of_Npc_actionImage
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    {S : FieldBranchSelection K FP Q W} {q alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) (hqe : Even q) :
    SelectedHsimp S q := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  obtain ⟨z, hz⟩ := NpcDisplayFor.exists_toPadic_eq_one_add_two_mul (hbranch ▸ S.display)
  exact .NpcUniform alpha r eta hbranch
    (NProcyclicUnram.uniformPushedHsimp hvalid.1 hqe z hz)

/-- **The procyclic-`M` Stokes residue, as far as the row currently reaches.**  Unlike the `L` and
`Npc` cases this is not unconditional: `MProcyclicExact.uniformPushedHsimp_of_pairings` reduces the
row's uniform residue to three named second-order inputs, and they are still open, so they appear
here as explicit binders.

What the selected row *does* remove is everything else.  Branch validity supplies `2 ≤ α` (hence
`1 ≤ α`); `MpcDisplayFor.represents` supplies the arithmetic input `RepresentsUnit`, which is
what discharges the display fixed-point-freeness obligation for every display the seam can
produce; and `Even q` is the only remaining numeric side condition.  So `hpair`, `hsc` and `hsep`
are exactly the residue: prove those three and this becomes the `Npc`-shaped theorem. -/
theorem SemanticSelectedHsimpRN.of_Mpc_actionImage {FP : FieldParameters}
    {S : SemanticSelectionView FP} {q alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) (hqe : Even q)
    (hpair : MProcyclicExact.UnramifiedNormalPairingIsCompact alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    (hsc : MProcyclicExact.ScalarActionImageStokes alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    (hsep : MProcyclicExact.RamifiedNormalPairingSeparates alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display) :
    SemanticSelectedHsimpRN S q := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  exact .MpcUniform alpha r epsilon eta hbranch
    (MProcyclicExact.uniformPushedHsimp_of_pairings (le_trans (by omega) hvalid.1) hqe
      (hbranch ▸ S.display).represents hpair hsc hsep)

/-- The same producer for the legacy selector's residue `SelectedHsimp`, stated here for the same
layering reason as `SelectedHsimp.of_Npc_actionImage`: the procyclic-`M` branch files first become
visible in this file. -/
theorem SelectedHsimp.of_Mpc_actionImage
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    {S : FieldBranchSelection K FP Q W} {q alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) (hqe : Even q)
    (hpair : MProcyclicExact.UnramifiedNormalPairingIsCompact alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    (hsc : MProcyclicExact.ScalarActionImageStokes alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    (hsep : MProcyclicExact.RamifiedNormalPairingSeparates alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display) :
    SelectedHsimp S q := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  exact .MpcUniform alpha r epsilon eta hbranch
    (MProcyclicExact.uniformPushedHsimp_of_pairings (le_trans (by omega) hvalid.1) hqe
      (hbranch ▸ S.display).represents hpair hsc hsep)

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
  | LResolved hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 * handleCount FP .L + 1) q
              (Words.LSq.lSqW (handleCount FP .L)))
            (2 * handleCount FP .L + 1) q P nuP
            (standardNumerics (2 * handleCount FP .L + 1))
          exact LSquare.exactLiftingRN_of_resolvedPushed hsimp hqe nuP
  | LUniform hbranch hsimp =>
      cases S with
      | mk branch valid display =>
          dsimp only at hbranch
          subst branch
          change ExactLiftingSemanticsRN
            (GammaR (2 * handleCount FP .L + 1) q
              (Words.LSq.lSqW (handleCount FP .L)))
            (2 * handleCount FP .L + 1) q P nuP
            (standardNumerics (2 * handleCount FP .L + 1))
          exact LSquare.exactLiftingRN_of_uniformPushed hsimp hqe nuP
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
  | NpcUniform alpha r eta hbranch hsimp =>
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
            (NProcyclic.exactLiftingRN_of_uniformPushed display hsimp
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
  | MpcUniform alpha r epsilon eta hbranch hsimp =>
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
            (MProcyclicExact.exactLiftingRN_of_uniformPushed display hsimp
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

/-- Branch validity supplies the sole side condition of the compact-M presentation. -/
theorem one_le_alpha_of_M0 (S : SemanticSelectionView FP) {alpha : ℕ}
    (hbranch : S.branch = .M0 alpha) : 1 ≤ alpha := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha at hvalid
  omega

/-- Compact-M structural leaves over the common view. -/
noncomputable def ofM0 (S : SemanticSelectionView FP) {alpha : ℕ}
    (hbranch : S.branch = .M0 alpha) :
    SemanticSelectedCoreLeavesRN S
      (MarkedCore.DM alpha (handleCount FP (.M0 alpha)))
      (Instances.MCompactCore.mNu alpha (handleCount FP (.M0 alpha))
        (one_le_alpha_of_M0 S hbranch)) := by
  cases S with
  | mk branch valid display =>
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

/-- Constructor regression: compact M is fully supplied through the corrected selection view. -/
theorem exists_of_branch_M0 (S : SemanticSelectionView FP) {alpha : ℕ}
    (hbranch : S.branch = .M0 alpha) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN S P nuP) :=
  ⟨MarkedCore.DM alpha (handleCount FP (.M0 alpha)),
    Instances.MCompactCore.mNu alpha (handleCount FP (.M0 alpha))
      (one_le_alpha_of_M0 S hbranch), ⟨ofM0 S hbranch⟩⟩

/-- The arbitrary-unit Npc presentation selected by the view's stored display. -/
noncomputable def npcPresentation (S : SemanticSelectionView FP)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    Count.CorePresentation (2 + 2 * handleCount FP (.Npc alpha r eta))
      (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta)
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta))) :=
  Instances.NProcyclicCore.npcCorePresentationUnit alpha r
    (handleCount FP (.Npc alpha r eta)) eta
      (Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display)

/-- Low-level Npc constructor for callers carrying a different normalized orientation. -/
noncomputable def ofNpcWithOrientation (S : SemanticSelectionView FP)
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

/-- Arbitrary-unit Npc leaves with the canonical orientation
`(0, eta, 2^r, 0, 0, ...)`; there are no orientation binders. -/
noncomputable def ofNpc (S : SemanticSelectionView FP)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    SemanticSelectedCoreLeavesRN S
      (MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta)))
      (SelectedCoreLeavesRN.npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta) := by
  cases S with
  | mk branch valid display =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Instances.NProcyclicCore.npcCorePresentationUnit alpha r
            (handleCount FP (.Npc alpha r eta)) eta display
          nu_sigma := SelectedCoreLeavesRN.npcNu_sigma alpha r
            (handleCount FP (.Npc alpha r eta)) eta display
          nu_wild := SelectedCoreLeavesRN.npcNu_wild alpha r
            (handleCount FP (.Npc alpha r eta)) eta display }

/-- Constructor regression: arbitrary-eta Npc is fully supplied through the corrected view. -/
theorem exists_of_branch_Npc (S : SemanticSelectionView FP)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN S P nuP) :=
  ⟨MarkedCore.DN alpha (handleCount FP (.Npc alpha r eta)),
    SelectedCoreLeavesRN.npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta,
    ⟨ofNpc S hbranch⟩⟩

/-- Branch validity supplies the side condition of the literal-parameter Mpc presentation. -/
theorem one_le_alpha_of_Mpc (S : SemanticSelectionView FP)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) : 1 ≤ alpha := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  omega

/-- Arbitrary-unit Mpc leaves with literal `p epsilon r`, literal `eta`, and the canonical
orientation `(-m(alpha)s(r), p epsilon r, s(r), eta, 0, ...)`. -/
noncomputable def ofMpc (S : SemanticSelectionView FP)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    SemanticSelectedCoreLeavesRN S
      (MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (SelectedCoreLeavesRN.mpcNu alpha r (p epsilon r)
        (handleCount FP (.Mpc alpha r epsilon eta)) eta
        (one_le_alpha_of_Mpc S hbranch)) := by
  cases S with
  | mk branch valid display =>
      dsimp only at hbranch
      subst branch
      have halpha : 1 ≤ alpha := le_trans (by omega) valid.1
      exact
        { presentation := Instances.MProcyclicCore.mpcCorePresentationUnit alpha r
            (p epsilon r) eta (handleCount FP (.Mpc alpha r epsilon eta)) halpha
          nu_sigma := SelectedCoreLeavesRN.mpcNu_sigma alpha r (p epsilon r)
            (handleCount FP (.Mpc alpha r epsilon eta)) eta halpha
          nu_wild := SelectedCoreLeavesRN.mpcNu_wild alpha r (p epsilon r)
            (handleCount FP (.Mpc alpha r epsilon eta)) eta halpha }

/-- Constructor regression: arbitrary-eta Mpc, with literal `p epsilon r`, is fully supplied. -/
theorem exists_of_branch_Mpc (S : SemanticSelectionView FP)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN S P nuP) :=
  ⟨MarkedCore.DM alpha (handleCount FP (.Mpc alpha r epsilon eta)),
    SelectedCoreLeavesRN.mpcNu alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) eta
      (one_le_alpha_of_Mpc S hbranch), ⟨ofMpc S hbranch⟩⟩

/-- Square-word L leaves at the selected handle count. -/
noncomputable def ofL (S : SemanticSelectionView FP) (hbranch : S.branch = .L) :
    SemanticSelectedCoreLeavesRN S (SqCore.DSq (handleCount FP .L))
      (Instances.LSquareCore.lNu (handleCount FP .L)) := by
  cases S with
  | mk branch valid display =>
      dsimp only at hbranch
      subst branch
      exact
        { presentation := Instances.LSquareCore.lCorePresentation (handleCount FP .L)
          nu_sigma := Instances.LSquareCore.lNu_sigma (handleCount FP .L)
          nu_wild := Instances.LSquareCore.lNu_wild (handleCount FP .L) }

/-- Constructor regression: L is fully supplied through the corrected selection view. -/
theorem exists_of_branch_L (S : SemanticSelectionView FP) (hbranch : S.branch = .L) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN S P nuP) :=
  ⟨SqCore.DSq (handleCount FP .L), Instances.LSquareCore.lNu (handleCount FP .L),
    ⟨ofL S hbranch⟩⟩

/-- **Corrected five-row constructor table.**  Every semantic selection has a presented
pro-`2` core with a canonical normalized `Ztwo` orientation.  In particular, Npc retains its
selected arbitrary `eta`, while Mpc retains both literal `p epsilon r` and literal `eta`. -/
theorem exists_of_semanticSelection (S : SemanticSelectionView FP) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN S P nuP) := by
  cases hbranch : S.branch with
  | L => exact exists_of_branch_L S hbranch
  | N0 alpha => exact exists_of_branch_N0 S hbranch
  | Npc alpha r eta => exact exists_of_branch_Npc S hbranch
  | M0 alpha => exact exists_of_branch_M0 S hbranch
  | Mpc alpha r epsilon eta => exact exists_of_branch_Mpc S hbranch

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

/-- **Family-selector structural regression.**  Every output of the corrected family selector,
including a genuine procyclic N-family witness, reaches one of the five canonical structural
constructors without passing through the contradictory legacy N witness. -/
theorem exists_core_of_familyFieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN
        (SemanticSelectionView.ofFamilyFieldBranchSelection S) P nuP) :=
  SemanticSelectedCoreLeavesRN.exists_of_semanticSelection
    (SemanticSelectionView.ofFamilyFieldBranchSelection S)

/-- End-to-end structural regression from the corrected arithmetic selector. -/
theorem exists_core_of_familyFieldBranch
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) :
    ∃ (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo),
      Nonempty (SemanticSelectedCoreLeavesRN
        (SemanticSelectionView.ofFamilyFieldBranchSelection
          (selectFieldBranchFamily B FF D RI W)) P nuP) :=
  exists_core_of_familyFieldSelection (selectFieldBranchFamily B FF D RI W)

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

/-- Target-local corrected-family handoff for the selected L row.  Unlike the legacy `L`
constructor, this entry point consumes the resolver carried by `ResolvedPushedHsimp` directly;
no universal resolver for every pushed marking is reintroduced. -/
noncomputable def wordCertificateRN_of_familyFieldSelection_resolvedL
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) {q : ℕ} (hbranch : S.branch = .L)
    (hsimp : LSquare.ResolvedPushedHsimp (handleCount FP .L) q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection S
    (.LResolved hbranch hsimp) hq0 hqe L

/-- Action-image corrected-family handoff for the selected L row.  Unlike both legacy L entry
points, this consumes **no** Stokes residue input: for even `q` the action-image theorem
supplies the `LUniform` case outright, so the selected-L certificate needs only the structural
and analytic leaves. -/
noncomputable def wordCertificateRN_of_familyFieldSelection_actionImageL
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) {q : ℕ} (hbranch : S.branch = .L)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection S
    (.of_L_actionImage hbranch hqe) hq0 hqe L

/-- Action-image corrected-family handoff for the selected procyclic-`N` row.  Exactly as on the
`L` row, this consumes **no** Stokes residue input: the branch equation and `Even q` are enough,
since `BranchData.Valid (.Npc α r η)` supplies `2 ≤ α` and the selected display supplies the
`2`-adic unit pair.  So the selected-`Npc` certificate needs only the structural and analytic
leaves. -/
noncomputable def wordCertificateRN_of_familyFieldSelection_actionImageNpc
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) {q alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection S
    (.of_Npc_actionImage hbranch hqe) hq0 hqe L

/-- Action-image corrected-family handoff for the selected procyclic-`M` row.  Unlike the `L` and
`Npc` handoffs this one is **not** free of residue input: the row's three second-order statements
are carried through as binders, because that is exactly what still separates the `Mpc` row from
the other two.  Everything else the row used to need is gone — no `Hsimp`, no separate arithmetic
input, no `α`/`r` inequalities. -/
noncomputable def wordCertificateRN_of_familyFieldSelection_actionImageMpc
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) {q alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) (hq0 : q ≠ 0) (hqe : Even q)
    (hpair : MProcyclicExact.UnramifiedNormalPairingIsCompact alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    (hsc : MProcyclicExact.ScalarActionImageStokes alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    (hsep : MProcyclicExact.RamifiedNormalPairingSeparates alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) q (hbranch ▸ S.display).display)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection S
    (.of_Mpc_actionImage hbranch hqe hpair hsc hsep) hq0 hqe L

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

/-- End-to-end selector handoff on the L row with the Stokes residue supplied theorem-side:
whenever the corrected selector picks `L`, even `q` alone feeds the action-image residue into
the five-row assembler. -/
noncomputable def wordCertificateRN_of_familyFieldBranch_actionImageL
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) {q : ℕ}
    (hbranch : (selectFieldBranchFamily B FF D RI W).branch = .L)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection
        (selectFieldBranchFamily B FF D RI W)) q P hP nuP hq0 hqe) :
    WordCertificateRN
      (selectFieldBranchFamily B FF D RI W).semantic.degree q
      (selectFieldBranchFamily B FF D RI W).semantic.word P hP nuP
      (standardNumerics (selectFieldBranchFamily B FF D RI W).semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection_actionImageL
    (selectFieldBranchFamily B FF D RI W) hbranch hq0 hqe L

/-- End-to-end selector handoff on the procyclic-`N` row with the Stokes residue supplied
theorem-side: whenever the corrected selector picks `.Npc α r η`, even `q` alone feeds the row's
uniform residue into the five-row assembler. -/
noncomputable def wordCertificateRN_of_familyFieldBranch_actionImageNpc
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) {q alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : (selectFieldBranchFamily B FF D RI W).branch = .Npc alpha r eta)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection
        (selectFieldBranchFamily B FF D RI W)) q P hP nuP hq0 hqe) :
    WordCertificateRN
      (selectFieldBranchFamily B FF D RI W).semantic.degree q
      (selectFieldBranchFamily B FF D RI W).semantic.word P hP nuP
      (standardNumerics (selectFieldBranchFamily B FF D RI W).semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection_actionImageNpc
    (selectFieldBranchFamily B FF D RI W) hbranch hq0 hqe L

/-- End-to-end selector handoff on the procyclic-`M` row.  Whenever the corrected selector picks
`.Mpc α r ε η`, the row's three second-order inputs and `Even q` feed its uniform residue into
the five-row assembler; no `Hsimp` and no further arithmetic input is consumed.  The three
binders are the honest statement of how far short of the `L`/`Npc` rows this one still falls. -/
noncomputable def wordCertificateRN_of_familyFieldBranch_actionImageMpc
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) {q alpha r : ℕ}
    {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : (selectFieldBranchFamily B FF D RI W).branch = .Mpc alpha r epsilon eta)
    (hq0 : q ≠ 0) (hqe : Even q)
    (hpair : MProcyclicExact.UnramifiedNormalPairingIsCompact alpha r (p epsilon r)
      (handleCount D.params (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ (selectFieldBranchFamily B FF D RI W).display).display)
    (hsc : MProcyclicExact.ScalarActionImageStokes alpha r (p epsilon r)
      (handleCount D.params (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ (selectFieldBranchFamily B FF D RI W).display).display)
    (hsep : MProcyclicExact.RamifiedNormalPairingSeparates alpha r (p epsilon r)
      (handleCount D.params (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ (selectFieldBranchFamily B FF D RI W).display).display)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection
        (selectFieldBranchFamily B FF D RI W)) q P hP nuP hq0 hqe) :
    WordCertificateRN
      (selectFieldBranchFamily B FF D RI W).semantic.degree q
      (selectFieldBranchFamily B FF D RI W).semantic.word P hP nuP
      (standardNumerics (selectFieldBranchFamily B FF D RI W).semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection_actionImageMpc
    (selectFieldBranchFamily B FF D RI W) hbranch hq0 hqe hpair hsc hsep L

end

end GQ2.Dyadic
