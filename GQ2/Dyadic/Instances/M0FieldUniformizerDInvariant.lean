/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotArtinExact

/-!
# The transported compact-M D class is intrinsic

The distinguished mod-two `D` character transported from a compact-M presentation does not
depend on the chosen oriented equivalence.  The ratio of two such equivalences preserves
`chiM`, and the full group-level invariance theorem for `dmDeltaDRed` therefore identifies the
two transported characters.

This makes uniformizer placement of `D` an intrinsic field condition rather than data attached
to a chosen frame.  Together with the single uniformizer Artin value, it gives a choice-free
selected corrected-RN residual.  No existence assertion for either arithmetic condition is made.
-/

namespace GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0FieldPivotArtinValue
open GQ2.Dyadic.Instances.M0FieldPivotArtinExact
open GQ2.Dyadic.LSquare.NuKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂}
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The transported distinguished `D` character is independent of the oriented equivalence. -/
theorem m0FieldDCharacter_congr_oriented {alpha h : ℕ}
    (halpha : 2 ≤ alpha)
    (e₁ e₂ : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    m0FieldDCharacter e₁.1 = m0FieldDCharacter e₂.1 := by
  let Ψ : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type) :=
    e₁.1.trans e₂.1.symm
  have hchi : ∀ x, chiM alpha h (Ψ x) = chiM alpha h x := by
    intro x
    calc
      chiM alpha h (Ψ x) = chiCycKTwo (K := K) (e₂.1 (Ψ x)) := (e₂.2 (Ψ x)).symm
      _ = chiCycKTwo (K := K) (e₁.1 x) := by
        rw [show e₂.1 (Ψ x) = e₁.1 x by
          change e₂.1 (e₂.1.symm (e₁.1 x)) = e₁.1 x
          exact e₂.1.apply_symm_apply (e₁.1 x)]
      _ = chiM alpha h x := e₁.2 x
  have hinv := dmDeltaDRed_aut_of_chiPreserving halpha Ψ hchi
  ext y
  let x : DM alpha h := e₁.1.symm y
  have hy : y = e₁.1 x := by simp [x]
  have he₂ : e₂.1.symm y = Ψ x := by
    apply e₂.1.injective
    rw [e₂.1.apply_symm_apply]
    change y = e₂.1 (e₂.1.symm (e₁.1 x))
    rw [e₂.1.apply_symm_apply, hy]
  change dmDeltaDRed alpha h (e₁.1.symm y) =
    dmDeltaDRed alpha h (e₂.1.symm y)
  rw [show e₁.1.symm y = x by simp [x], he₂]
  exact DFunLike.congr_fun hinv x |>.symm

variable [FiniteDimensional ℚ_[2] K]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The intrinsic statement that transported `D` is the filtration-uniformizer Kummer class. -/
def M0UniformizerDPlacement (FF : DyadicUnitFiltration K) (alpha h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF)

omit [FiniteDimensional ℚ_[2] K] in
/-- Any oriented equivalence tests the intrinsic uniformizer-D placement. -/
theorem m0UniformizerDPlacement_iff (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    M0UniformizerDPlacement FF alpha h ↔
      h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldDCharacter e.1)) =
        kummerClassK K (piUnitK FF) := by
  constructor
  · rintro ⟨e', he'⟩
    rw [m0FieldDCharacter_congr_oriented halpha e' e] at he'
    exact he'
  · exact fun he => ⟨e, he⟩

/-- Under intrinsic uniformizer-D placement, the pivot is exactly the single Artin value. -/
theorem m0FieldPivotUnit_iff_uniformizerArtinValue_of_placement
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (Hplace : M0UniformizerDPlacement FF alpha h) :
    M0FieldPivotUnit B alpha h ↔ M0UniformizerArtinCompatibility B FF := by
  obtain ⟨e, hD⟩ := Hplace
  exact m0FieldPivotUnit_iff_uniformizerArtinValue B FF halpha e hD

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The selected corrected-RN residual from the two intrinsic compact-M field conditions. -/
theorem m0RowResidualRN_of_familySelection_of_intrinsic_uniformizer_data
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (Hplace : M0UniformizerDPlacement FF alpha (handleCount FP (.M0 alpha)))
    (Hartin : M0UniformizerArtinCompatibility B FF) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  exact m0RowResidualRN_of_familySelection_of_fieldPivot B FF S hbranch
    ((m0FieldPivotUnit_iff_uniformizerArtinValue_of_placement
      B FF halpha Hplace).mpr Hartin)

#print axioms m0FieldDCharacter_congr_oriented
#print axioms M0UniformizerDPlacement
#print axioms m0UniformizerDPlacement_iff
#print axioms m0FieldPivotUnit_iff_uniformizerArtinValue_of_placement
#print axioms m0RowResidualRN_of_familySelection_of_intrinsic_uniformizer_data

end
end GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
