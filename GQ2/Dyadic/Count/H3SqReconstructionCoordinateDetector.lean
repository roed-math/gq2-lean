/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqReconstructionFiniteDetector

/-!
# Coordinate detector for square-presentation reconstruction

The finite generator system for reconstruction transport is a matrix equation with a
cochain-valued unknown.  This file splits that equation into one ordinary finite linear system
for each output bar-three coordinate.  The coefficient matrix is the transpose of the chosen
single-relator coordinate map.  Its target column is the universal reconstruction correction.

For the concrete adjoint comparison, every entry of the target column is reduced all the way to
coefficient evaluation against the already constructed reverse degree-three bar map.  Thus the
only remaining assertion is that these explicit columns lie in the range of the one-relator
coefficient matrix.  Equivalently, a single function into finite cokernels vanishes.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.FoxH
open GQ2.Dyadic.SqCore

/-! ## The scalar coefficient matrix -/

/-- Standard basis index for the finite one-relator module at a quotient. -/
abbrev SqFiniteRelationReconstructionBasisIndex
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type)) :=
  ((DSq h : Type) ⧸ W.toSubgroup) × Unit

/-- The transpose coefficient matrix of the chosen single-relator coordinate.  A vector x of
unknown one-relator coefficients is sent to its values on all standard input cochains. -/
def sqFiniteInputRelationReconstructionColumnMap
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    (SqFiniteRelationReconstructionBasisIndex h C.W → ZMod 2) →ₗ[ZMod 2]
      (SqFiniteInputReconstructionBasisIndex h V → ZMod 2) where
  toFun x i :=
    finiteFinsuppCoefficientEval x
      (sqFiniteInputSingleRelatorReconstructionCoordinate C L
        (Pi.basisFun (ZMod 2)
          (SqFiniteInputReconstructionBasisIndex h V) i))
  map_add' x y := by
    funext i
    exact finiteFinsuppCoefficientEval_add_function x y _
  map_smul' z x := by
    funext i
    exact finiteFinsuppCoefficientEval_smul_function z x _

/-- One output-coordinate column of the universal reconstruction target. -/
def sqFiniteInputUniversalReconstructionColumn
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (a : SqFiniteInputReconstructionBasisIndex h C.W) :
    SqFiniteInputReconstructionBasisIndex h V → ZMod 2 :=
  fun i ↦
    sqFiniteInputUniversalReconstructionTerm C
      (Pi.basisFun (ZMod 2)
        (SqFiniteInputReconstructionBasisIndex h V) i) a

/-- Columnwise form of the reconstruction system.  It is a family of ordinary finite range
tests, one for each output bar-three basis coordinate. -/
def SqFiniteInputRelationReconstructionColumnRangeSystemAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∀ a : SqFiniteInputReconstructionBasisIndex h C.W,
    sqFiniteInputUniversalReconstructionColumn C a ∈
      LinearMap.range (sqFiniteInputRelationReconstructionColumnMap C L)

/-- Evaluating a linear combination of function-valued vectors is coefficient evaluation
against the corresponding scalar column. -/
theorem finiteFinsuppCoefficientEval_functionLinearCombination
    {J A : Type} (table : J → A → ZMod 2) (v : J →₀ ZMod 2) (a : A) :
    finiteFinsuppCoefficientEval (fun j ↦ table j a) v =
      Finsupp.linearCombination (ZMod 2) table v a := by
  classical
  induction v using Finsupp.induction with
  | zero => simp
  | single_add j z v hj hz ih =>
      rw [map_add, map_add, finiteFinsuppCoefficientEval_single,
        Finsupp.linearCombination_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih]

/-- The cochain-valued generator table is solvable exactly when every scalar output column is
in the range of the single-relator coefficient matrix. -/
theorem sqFiniteInputRelationReconstructionGeneratorSystemAt_iff_columnRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionGeneratorSystemAt C L ↔
      SqFiniteInputRelationReconstructionColumnRangeSystemAt C L := by
  classical
  constructor
  · rintro ⟨table, htable⟩ a
    let x : SqFiniteRelationReconstructionBasisIndex h C.W → ZMod 2 :=
      fun j ↦ table j a
    refine ⟨x, ?_⟩
    funext i
    have hi := congrFun (htable i) a
    change
      finiteFinsuppCoefficientEval (fun j ↦ table j a)
          (sqFiniteInputSingleRelatorReconstructionCoordinate C L
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i)) =
        sqFiniteInputUniversalReconstructionTerm C
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i) a
    rw [finiteFinsuppCoefficientEval_functionLinearCombination]
    exact hi
  · intro hcolumns
    choose x hx using hcolumns
    let table : SqFiniteRelationReconstructionBasisIndex h C.W →
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      fun j a ↦ x a j
    refine ⟨table, fun i ↦ ?_⟩
    funext a
    have ha := congrFun (hx a) i
    change
      finiteFinsuppCoefficientEval (x a)
          (sqFiniteInputSingleRelatorReconstructionCoordinate C L
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i)) =
        sqFiniteInputUniversalReconstructionTerm C
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i) a at ha
    rw [← finiteFinsuppCoefficientEval_functionLinearCombination table _ a]
    exact ha

/-! ## The residual coordinate map -/

/-- The finite cokernel for one scalar output column. -/
abbrev SqFiniteInputRelationReconstructionColumnCokernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :=
  (SqFiniteInputReconstructionBasisIndex h V → ZMod 2) ⧸
    LinearMap.range (sqFiniteInputRelationReconstructionColumnMap C L)

/-- Every scalar column obstruction lives in a finite cokernel. -/
noncomputable instance instFintypeSqFiniteInputRelationReconstructionColumnCokernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    Fintype (SqFiniteInputRelationReconstructionColumnCokernel C L) := by
  let A := SqFiniteInputReconstructionBasisIndex h V → ZMod 2
  letI : Finite A := inferInstance
  let P := LinearMap.range (sqFiniteInputRelationReconstructionColumnMap C L)
  letI : Finite (SqFiniteInputRelationReconstructionColumnCokernel C L) :=
    Finite.of_surjective P.mkQ P.mkQ_surjective
  exact Fintype.ofFinite _

/-- The smallest coordinate obstruction: for each output bar-three basis coordinate, take the
corresponding explicit target column modulo the range of the one-relator coefficient matrix. -/
def sqFiniteInputRelationReconstructionColumnObstruction
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputReconstructionBasisIndex h C.W →
      SqFiniteInputRelationReconstructionColumnCokernel C L :=
  fun a ↦
    (LinearMap.range
      (sqFiniteInputRelationReconstructionColumnMap C L)).mkQ
        (sqFiniteInputUniversalReconstructionColumn C a)

/-- Vanishing of the residual coordinate map is exactly columnwise solvability. -/
theorem sqFiniteInputRelationReconstructionColumnObstruction_eq_zero_iff
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    sqFiniteInputRelationReconstructionColumnObstruction C L = 0 ↔
      SqFiniteInputRelationReconstructionColumnRangeSystemAt C L := by
  constructor
  · intro hzero a
    have ha := congrFun hzero a
    change
      (LinearMap.range
        (sqFiniteInputRelationReconstructionColumnMap C L)).mkQ
          (sqFiniteInputUniversalReconstructionColumn C a) = 0 at ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    exact ha
  · intro hrange
    funext a
    change
      (LinearMap.range
        (sqFiniteInputRelationReconstructionColumnMap C L)).mkQ
          (sqFiniteInputUniversalReconstructionColumn C a) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hrange a

/-- Regression tying the original finite cokernel obstruction to the smallest coordinate
obstruction map. -/
theorem sqFiniteInputRelationReconstructionCokernelClass_eq_zero_iff_columnObstruction
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    sqFiniteInputRelationReconstructionCokernelClass C L = 0 ↔
      sqFiniteInputRelationReconstructionColumnObstruction C L = 0 := by
  rw [sqFiniteInputRelationReconstructionCokernelClass_eq_zero_iff,
    ← sqFiniteInputRelationReconstructionGeneratorSystemAt_iff,
    sqFiniteInputRelationReconstructionGeneratorSystemAt_iff_columnRange,
    ← sqFiniteInputRelationReconstructionColumnObstruction_eq_zero_iff]

/-! ## Complete expansion for the concrete adjoint comparison -/

/-- On a regular bar-three basis vector, the reverse degree-three map is the sum of the four
Schreier defects occurring in its bar boundary. -/
@[simp] theorem finiteBarToUniversalRelationThree_single
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (g q r s : Q) (a : ZMod 2) :
    finiteBarToUniversalRelationThree m heval
        (Finsupp.single (g, (q, r, s)) a) =
      Finsupp.single (g * q, relationDefect heval r s) a +
        Finsupp.single (g, relationDefect heval (q * r) s) a +
        Finsupp.single (g, relationDefect heval q (r * s)) a +
        Finsupp.single (g, relationDefect heval q r) a := by
  classical
  simp [finiteBarToUniversalRelationThree]

/-- The reverse degree-three vectors probed by the reconstruction target lie in the universal
Fox kernel.  Consequently Fox preservation of the chosen one-relator lift does not itself
determine the target columns. -/
theorem finiteUniversalRelationFoxBoundary_barToUniversalRelationThree_eq_zero
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (x : FiniteModTwoBarChainThree Q) :
    (finiteUniversalRelationFoxBoundary m).map
        (finiteBarToUniversalRelationThree m heval x) = 0 := by
  have hboundary :
      finiteModTwoBarBoundaryTwo (finiteModTwoBarBoundaryThree x) = 0 := by
    have h := LinearMap.congr_fun
      (finiteModTwoBarBoundaryTwo_comp_boundaryThree (Q := Q)) x
    simpa using h
  rw [finiteBarToUniversalRelationThree, LinearMap.comp_apply,
    ← finiteBarToMarkedOne_boundaryTwo, hboundary, map_zero]

/-- For the concrete comparison, a target-matrix entry is exactly coefficient evaluation of
the compatible universal output against the reverse degree-three image of the corresponding
regular bar basis vector. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.universalReconstructionColumn_apply
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (a i : SqFiniteInputReconstructionBasisIndex h V) :
    sqFiniteInputUniversalReconstructionColumn S.degreeThreeComparison a i =
      finiteFinsuppCoefficientEval
        (Finsupp.lcoeFun (R := ZMod 2) (S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)))
        (finiteBarToUniversalRelationThree
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (Finsupp.single (1, a) (1 : ZMod 2))) :=
  rfl

/-- Full section-level expansion of a concrete target entry.  Thus each right-hand side in the
finite reconstruction system is the sum of four coefficients of the compatible universal
output, at the four explicit Schreier factors in the bar-three boundary. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.universalReconstructionColumn_apply_sectionDefects
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (q r s : (DSq h : Type) ⧸ V.toSubgroup)
    (i : SqFiniteInputReconstructionBasisIndex h V) :
    sqFiniteInputUniversalReconstructionColumn S.degreeThreeComparison (q, r, s) i =
      S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)
          (q, relationDefect (sqOpenQuotientFreeEvaluation_surjective h V) r s) +
        S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)
          (1, relationDefect
            (sqOpenQuotientFreeEvaluation_surjective h V) (q * r) s) +
        S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)
          (1, relationDefect
            (sqOpenQuotientFreeEvaluation_surjective h V) q (r * s)) +
        S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)
          (1, relationDefect
            (sqOpenQuotientFreeEvaluation_surjective h V) q r) := by
  have hreverse :
      finiteBarToUniversalRelationThree
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (Finsupp.single (1, (q, r, s)) (1 : ZMod 2)) =
        Finsupp.single
            (q, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) r s) 1 +
          Finsupp.single
            (1, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) (q * r) s) 1 +
          Finsupp.single
            (1, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) q (r * s)) 1 +
          Finsupp.single
            (1, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) q r) 1 := by
    simpa using finiteBarToUniversalRelationThree_single
      (sqOpenQuotientMarking h V)
      (sqOpenQuotientFreeEvaluation_surjective h V)
      1 q r s (1 : ZMod 2)
  calc
    sqFiniteInputUniversalReconstructionColumn
        S.degreeThreeComparison (q, r, s) i =
      finiteFinsuppCoefficientEval
        (Finsupp.lcoeFun (R := ZMod 2) (S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)))
        (finiteBarToUniversalRelationThree
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (Finsupp.single (1, (q, r, s)) (1 : ZMod 2))) :=
      S.universalReconstructionColumn_apply (q, r, s) i
    _ = finiteFinsuppCoefficientEval
        (Finsupp.lcoeFun (R := ZMod 2) (S.universalSyzygy.coordinate V
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)))
        (Finsupp.single
            (q, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) r s) 1 +
          Finsupp.single
            (1, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) (q * r) s) 1 +
          Finsupp.single
            (1, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) q (r * s)) 1 +
          Finsupp.single
            (1, relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h V) q r) 1) :=
      congrArg
        (finiteFinsuppCoefficientEval
          (Finsupp.lcoeFun (R := ZMod 2) (S.universalSyzygy.coordinate V
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i))))
        hreverse
    _ = _ := by
      simp only [map_add, finiteFinsuppCoefficientEval_single, one_mul,
        Finsupp.lcoeFun_apply]

/-- Every standard-basis reconstruction equation, expanded to a scalar equation.  The left
side contains only the coefficients of the chosen one-relator lift; the right side contains
only the existing reverse degree-three map and the compatible universal output. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationGenerators_iff_explicitCoordinates
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    SqFiniteInputRelationReconstructionGeneratorSystemAt
        S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation ↔
      ∃ table : SqFiniteRelationReconstructionBasisIndex h V →
          FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup),
        ∀ (i a : SqFiniteInputReconstructionBasisIndex h V),
          finiteFinsuppCoefficientEval (fun j ↦ table j a)
              (sqFiniteInputSingleRelatorReconstructionCoordinate
                S.degreeThreeComparison
                S.universalSyzygy.relationLiftOfSqPresentation
                (Pi.basisFun (ZMod 2)
                  (SqFiniteInputReconstructionBasisIndex h V) i)) =
            finiteFinsuppCoefficientEval
              (Finsupp.lcoeFun (R := ZMod 2) (S.universalSyzygy.coordinate V
                (Pi.basisFun (ZMod 2)
                  (SqFiniteInputReconstructionBasisIndex h V) i)))
              (finiteBarToUniversalRelationThree
                (sqOpenQuotientMarking h V)
                (sqOpenQuotientFreeEvaluation_surjective h V)
                (Finsupp.single (1, a) (1 : ZMod 2))) := by
  classical
  constructor
  · rintro ⟨table, htable⟩
    refine ⟨table, fun i a ↦ ?_⟩
    have hi := congrFun (htable i) a
    rw [← finiteFinsuppCoefficientEval_functionLinearCombination table _ a] at hi
    change
      finiteFinsuppCoefficientEval (fun j ↦ table j a)
          (sqFiniteInputSingleRelatorReconstructionCoordinate
            S.degreeThreeComparison
            S.universalSyzygy.relationLiftOfSqPresentation
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i)) =
        sqFiniteInputUniversalReconstructionColumn S.degreeThreeComparison a i at hi
    exact hi.trans (S.universalReconstructionColumn_apply a i)
  · rintro ⟨table, htable⟩
    refine ⟨table, fun i ↦ ?_⟩
    funext a
    calc
      Finsupp.linearCombination (ZMod 2) table
          (sqFiniteInputSingleRelatorReconstructionCoordinate
            S.degreeThreeComparison
            S.universalSyzygy.relationLiftOfSqPresentation
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i)) a =
        finiteFinsuppCoefficientEval (fun j ↦ table j a)
          (sqFiniteInputSingleRelatorReconstructionCoordinate
            S.degreeThreeComparison
            S.universalSyzygy.relationLiftOfSqPresentation
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i)) :=
        (finiteFinsuppCoefficientEval_functionLinearCombination table _ a).symm
      _ = finiteFinsuppCoefficientEval
            (Finsupp.lcoeFun (R := ZMod 2) (S.universalSyzygy.coordinate V
              (Pi.basisFun (ZMod 2)
                (SqFiniteInputReconstructionBasisIndex h V) i)))
            (finiteBarToUniversalRelationThree
              (sqOpenQuotientMarking h V)
              (sqOpenQuotientFreeEvaluation_surjective h V)
              (Finsupp.single (1, a) (1 : ZMod 2))) := htable i a
      _ = sqFiniteInputUniversalReconstructionColumn S.degreeThreeComparison a i :=
        (S.universalReconstructionColumn_apply a i).symm

/-- Final concrete regression: the named finite-support defect vanishes exactly when the
explicit output-coordinate obstruction map vanishes. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect_eq_zero_iff_columnObstruction
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    S.sqPresentationFiniteSupportTransportDefect = 0 ↔
      sqFiniteInputRelationReconstructionColumnObstruction
        S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation = 0 := by
  let L := S.universalSyzygy.relationLiftOfSqPresentation
  have hiff :=
    S.sqPresentationFiniteSupportTransportDefect_eq_zero_iff_cokernelClass.trans
      (sqFiniteInputRelationReconstructionCokernelClass_eq_zero_iff_columnObstruction
        S.degreeThreeComparison L)
  simpa only [
    SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationReconstructionCokernelClass,
    L] using hiff

#print axioms sqFiniteInputRelationReconstructionGeneratorSystemAt_iff_columnRange
#print axioms SqCompatibleUniversalCocycleCancellingSyzygyAt.universalReconstructionColumn_apply
#print axioms SqCompatibleUniversalCocycleCancellingSyzygyAt.universalReconstructionColumn_apply_sectionDefects
#print axioms SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect_eq_zero_iff_columnObstruction

end

end GQ2.Dyadic.Count
