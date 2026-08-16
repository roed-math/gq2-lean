/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotCup
import GQ2.Dyadic.Instances.GammaLUnramifiedHilbertValue

/-!
# Hilbert-symbol reduction of the compact-M field pivot

The intrinsic compact-M pivot is a cup product of two field classes.  Mod-two Kummer
surjectivity supplies representatives `a` and `b` for the transported distinguished `D` class
and the unramified class.  The existing cup--Hilbert dictionary then identifies the pivot with
the failure of `b` to be represented by the quadratic norm form `x^2 - a*y^2`.

This is the strongest unconditional Hilbert-symbol reduction currently available.  Level zero
makes the unramified class nonzero, but does not identify the transported `D` class with a
canonical square class or determine its pairing with the unramified line.  Such a determination
requires an additional arithmetic identification of that transported class; identifying the
unramified character itself with a prescribed Kummer class is the repository's separate
Artin--Kummer compatibility seam.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotHilbert

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.EvenModel
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.LSquare.MarkedFrame

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Once Kummer representatives for the transported `D` class and the unramified class are
fixed, the compact-M pivot is exactly the nontrivial quadratic Hilbert symbol `(a,b)_K`, written
without introducing a separate sign-valued symbol: `b` is not represented by
`x^2 - a*y^2`. -/
theorem m0FieldPivotUnit_iff_not_normForm_of_kummer
    (B : MarkedRecip Rec K) {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (a b : (↥K)ˣ)
    (ha : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) = kummerClassK K a)
    (hb : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldNuCharacter B)) = kummerClassK K b) :
    M0FieldPivotUnit B alpha h ↔
      ¬ ∃ x y : ↥K, (b : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
  rw [m0FieldPivotUnit_iff_cup B halpha e, m0PivotCupValue, ha, hb]
  exact cupFormK_kummer_eq_one_iff K a b

/-- Every compact-M pivot admits a concrete Hilbert-symbol presentation.  The representatives
are noncanonical square classes supplied by mod-two Kummer surjectivity; the theorem deliberately
records both class identifications so later arithmetic input can replace either representative
by a preferred one. -/
theorem exists_kummerRepresentatives_m0FieldPivot
    (B : MarkedRecip Rec K) {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    ∃ a b : (↥K)ˣ,
      h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldDCharacter e.1)) = kummerClassK K a ∧
        h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)) = kummerClassK K b ∧
        (M0FieldPivotUnit B alpha h ↔
          ¬ ∃ x y : ↥K, (b : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2) := by
  obtain ⟨a, ha⟩ := kummerClassK_surjective K
    (h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldDCharacter e.1)))
  obtain ⟨b, hb⟩ := kummerClassK_surjective K
    (h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldNuCharacter B)))
  exact ⟨a, b, ha.symm, hb.symm,
    m0FieldPivotUnit_iff_not_normForm_of_kummer B halpha e a b ha.symm hb.symm⟩

#print axioms m0FieldPivotUnit_iff_not_normForm_of_kummer
#print axioms exists_kummerRepresentatives_m0FieldPivot

end
end GQ2.Dyadic.Instances.M0FieldPivotHilbert
