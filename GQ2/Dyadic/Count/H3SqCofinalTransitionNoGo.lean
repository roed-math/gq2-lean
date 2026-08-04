/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqCofinalTransitionDetector
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# No-go theorem for literal cofinal universal-relation transport

At the terminal quotient, the reverse bar-two image is supported only on the identity relation
word.  Literal range transport from a finer quotient would therefore make every normalized
Schreier defect equal to the identity.  The chosen section would become a group-homomorphic
splitting into a torsion-free free group, forcing the finite source quotient to be trivial.

The first-parity quotient of the square presentation gives an explicit contradiction.  Thus the
simultaneous range-good condition isolated by the compactness argument is not merely unproved:
with the present free universal-relation alphabet it is false.  A successful gluing theorem must
quotient by multiplicative/Peiffer relations or transport reverse outputs only up to an explicit
relation-cell correction.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

private def SqTerminal (h : ℕ) : OpenNormalSubgroup (DSq h : Type) :=
  { toSubgroup := ⊤
    isOpen' := isOpen_univ
    isNormal' := Subgroup.normal_top }

/-- At the terminal quotient, a nonidentity universal relation basis coordinate vanishes on
the entire reverse bar-two image. -/
theorem sqTerminal_barToUniversalRelationTwo_apply_of_relation_ne_one
    (h : ℕ)
    (k : FreeRelationKernel (sqOpenQuotientMarking h (SqTerminal h)))
    (hk : k ≠ 1)
    (b : FiniteModTwoBarChainTwo
      ((DSq h : Type) ⧸ (SqTerminal h).toSubgroup)) :
    sqOpenQuotientBarToUniversalRelationTwo h (SqTerminal h) b
      ((1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup), k) = 0 := by
  classical
  letI : Subsingleton ((DSq h : Type) ⧸ (SqTerminal h).toSubgroup) := by
    simpa [SqTerminal] using
      (QuotientGroup.subsingleton_quotient_top (G := (DSq h : Type)))
  induction b using Finsupp.induction with
  | zero => simp
  | single_add p a b hp ha ih =>
      rcases p with ⟨g, q, r⟩
      have hg : g = 1 := Subsingleton.elim _ _
      have hq : q = 1 := Subsingleton.elim _ _
      have hr : r = 1 := Subsingleton.elim _ _
      subst g
      subst q
      subst r
      have hdefect : relationDefect
          (sqOpenQuotientFreeEvaluation_surjective h (SqTerminal h)) 1 1 = 1 := by
        apply Subtype.ext
        simp [relationDefect]
      simp only [map_add, Finsupp.add_apply, ih, add_zero]
      change (finiteBarToUniversalRelationTwo
        (sqOpenQuotientMarking h (SqTerminal h))
        (sqOpenQuotientFreeEvaluation_surjective h (SqTerminal h))
        (Finsupp.single ((1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup),
          ((1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup),
            (1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup))) a))
          ((1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup), k) = 0
      rw [finiteBarToUniversalRelationTwo_single, hdefect]
      simp [hk]

/-- Literal reverse-two range transport to the terminal quotient forces every source Schreier
factor to be the identity word. -/
theorem relationDefect_eq_one_of_sqUniversalBarInputTransitionRangeAt_top
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type)) (hWtop : W ≤ SqTerminal h)
    (hrange : SqUniversalBarInputTransitionRangeAt h hWtop)
    (q r : (DSq h : Type) ⧸ W.toSubgroup) :
    relationDefect (sqOpenQuotientFreeEvaluation_surjective h W) q r = 1 := by
  classical
  let d := relationDefect (sqOpenQuotientFreeEvaluation_surjective h W) q r
  let d' := sqOpenQuotientFreeRelationKernelMap h hWtop d
  by_contra hd
  have hd' : d' ≠ 1 := by
    intro hd'one
    have hword := congrArg Subtype.val hd'one
    exact hd (Subtype.ext (by simpa [d, d'] using hword))
  let b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ W.toSubgroup) :=
    Finsupp.single ((1 : (DSq h : Type) ⧸ W.toSubgroup), (q, r)) 1
  obtain ⟨b', hb'⟩ := hrange (LinearMap.mem_range_self
    ((sqUniversalRelationModuleTransition h hWtop).comp
      (sqOpenQuotientBarToUniversalRelationTwo h W)) b)
  have hcoord := congrArg
    (fun z : RegularModTwoRelationModule
        ((DSq h : Type) ⧸ (SqTerminal h).toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h (SqTerminal h))) =>
      z ((1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup), d')) hb'
  have hleft := sqTerminal_barToUniversalRelationTwo_apply_of_relation_ne_one
    h d' hd' b'
  rw [hleft] at hcoord
  change 0 = (sqUniversalRelationModuleTransition h hWtop
    (sqOpenQuotientBarToUniversalRelationTwo h W b))
      ((1 : (DSq h : Type) ⧸ (SqTerminal h).toSubgroup), d') at hcoord
  have hzeroone : (0 : ZMod 2) = 1 := by
    simpa [b, d, d', sqOpenQuotientBarToUniversalRelationTwo] using hcoord
  exact zero_ne_one hzeroone

/-- If all normalized Schreier factors are trivial, the normalized relation section is a group
homomorphism splitting free evaluation. -/
def relationSectionHomOfDefectsEqOne
    {Q I : Type} [Group Q] (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (hdefect : ∀ q r : Q, relationDefect heval q r = 1) :
    Q →* FreeGroup I where
  toFun := relationSection heval
  map_one' := relationSection_one heval
  map_mul' q r := by
    have hd := congrArg Subtype.val (hdefect q r)
    symm
    change relationSection heval q * relationSection heval r =
      relationSection heval (q * r)
    change relationSection heval q * relationSection heval r *
        (relationSection heval (q * r))⁻¹ = 1 at hd
    exact mul_inv_eq_one.mp hd

/-- A finite quotient admitting a group-homomorphic normalized section into the free group is
trivial, since free groups are torsion-free. -/
theorem subsingleton_of_relationDefects_eq_one
    {Q I : Type} [Group Q] [Finite Q] (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (hdefect : ∀ q r : Q, relationDefect heval q r = 1) : Subsingleton Q := by
  let s := relationSectionHomOfDefectsEqOne m heval hdefect
  constructor
  intro q r
  have hone (x : Q) : x = 1 := by
    have hpow : (s x) ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hsone : s x = 1 :=
      (pow_eq_one_iff_left (orderOf_pos x).ne').mp hpow
    calc
      x = FreeGroup.lift m (relationSection heval x) :=
        (relationSection_spec heval x).symm
      _ = FreeGroup.lift m (s x) := rfl
      _ = 1 := by rw [hsone, map_one]
  rw [hone q, hone r]

/-- In particular, a range-good transition to the terminal quotient can only start from a
trivial finite quotient. -/
theorem subsingleton_quotient_of_sqUniversalBarInputTransitionRangeAt_top
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type)) (hWtop : W ≤ SqTerminal h)
    (hrange : SqUniversalBarInputTransitionRangeAt h hWtop) :
    Subsingleton ((DSq h : Type) ⧸ W.toSubgroup) := by
  letI : Finite ((DSq h : Type) ⧸ W.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen W.toSubgroup W.isOpen'
  exact subsingleton_of_relationDefects_eq_one
    (sqOpenQuotientMarking h W)
    (sqOpenQuotientFreeEvaluation_surjective h W)
    (relationDefect_eq_one_of_sqUniversalBarInputTransitionRangeAt_top h W hWtop hrange)

/-- Every quotient refining the explicit first-parity kernel remains nontrivial. -/
theorem not_subsingleton_sqOpenQuotient_of_le_firstParityKernel
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type))
    (hWparity : W ≤ sqFirstParityKernel h) :
    ¬ Subsingleton ((DSq h : Type) ⧸ W.toSubgroup) := by
  intro hsub
  have hsource : sqOpenQuotientMarking h W 0 = 1 := hsub.elim _ _
  have htarget : sqOpenQuotientMarking h (sqFirstParityKernel h) 0 = 1 := by
    have hmap := congrArg
      (openNormalQuotientProj hWparity) hsource
    simpa only [openNormalQuotientProj_sqOpenQuotientMarking, map_one] using hmap
  have hparity : Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
    calc
      Multiplicative.ofAdd (1 : ZMod 2) =
          sqFirstParityQuotientHom h
            (sqOpenQuotientMarking h (sqFirstParityKernel h) 0) :=
        (sqFirstParityQuotientHom_marking_zero h).symm
      _ = sqFirstParityQuotientHom h 1 := congrArg _ htarget
      _ = 1 := map_one _
  have hadd := congrArg Multiplicative.toAdd hparity
  exact one_ne_zero hadd

/-- No quotient refining the first-parity level has a range-good reverse-two transition to the
terminal quotient. -/
theorem not_sqUniversalBarInputTransitionRangeAt_top_of_le_firstParityKernel
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type))
    (hWparity : W ≤ sqFirstParityKernel h) (hWtop : W ≤ SqTerminal h) :
    ¬ SqUniversalBarInputTransitionRangeAt h hWtop := by
  intro hrange
  exact not_subsingleton_sqOpenQuotient_of_le_firstParityKernel h W hWparity
    (subsingleton_quotient_of_sqUniversalBarInputTransitionRangeAt_top
      h W hWtop hrange)

/-- **Cofinal transition no-go.**  The simultaneous common-refinement range condition is false
for the current literal universal-relation reverse map. -/
theorem not_sqUniversalBarInputTransitionCommonRefinementRange (h : ℕ) :
    ¬ SqUniversalBarInputTransitionCommonRefinementRange h := by
  intro hcommon
  obtain ⟨W, hWparity, hWtop, _hgoodParity, hgoodTop⟩ :=
    hcommon (sqFirstParityKernel h) (SqTerminal h)
  exact not_sqUniversalBarInputTransitionRangeAt_top_of_le_firstParityKernel
    h W hWparity hWtop hgoodTop

/-- Equivalently, the paired finite detector cannot become trivial cofinally. -/
theorem not_sqUniversalBarInputTransitionPairDetectorCofinallyTrivial (h : ℕ) :
    ¬ SqUniversalBarInputTransitionPairDetectorCofinallyTrivial h := by
  rw [← sqUniversalBarInputTransitionCommonRefinementRange_iff_pairDetector]
  exact not_sqUniversalBarInputTransitionCommonRefinementRange h

/-- Consequently the proposed effective multiplicative marking cannot exist: its existence
would imply the refuted common-refinement range condition. -/
theorem not_sqUniversalBarInputTransitionPairDetectorEffectiveMarking (h : ℕ) :
    ¬ SqUniversalBarInputTransitionPairDetectorEffectiveMarking h := by
  intro heffective
  exact not_sqUniversalBarInputTransitionCommonRefinementRange h
    (sqUniversalBarInputTransitionCommonRefinementRange_of_effectivePairDetectorMarking
      h heffective)

/-- Even the pairwise eventual range condition is false: apply it to the first-parity level
and the terminal target. -/
theorem not_sqUniversalBarInputTransitionEventuallyRange (h : ℕ) :
    ¬ SqUniversalBarInputTransitionEventuallyRange h := by
  intro heventual
  have hparityTop : sqFirstParityKernel h ≤ SqTerminal h := by
    change (sqFirstParityKernel h).toSubgroup ≤ (⊤ : Subgroup (DSq h : Type))
    exact le_top
  obtain ⟨W, hWparity, hgoodTop⟩ := heventual hparityTop
  exact not_sqUniversalBarInputTransitionRangeAt_top_of_le_firstParityKernel
    h W hWparity (hWparity.trans hparityTop) hgoodTop

/-- Hence uniform literal bar-input transition range is false as well. -/
theorem not_sqUniversalBarInputTransitionRange (h : ℕ) :
    ¬ SqUniversalBarInputTransitionRange h := by
  intro hrange
  have hparityTop : sqFirstParityKernel h ≤ SqTerminal h := by
    change (sqFirstParityKernel h).toSubgroup ≤ (⊤ : Subgroup (DSq h : Type))
    exact le_top
  exact not_sqUniversalBarInputTransitionRangeAt_top_of_le_firstParityKernel
    h (sqFirstParityKernel h) (le_refl _) hparityTop (hrange hparityTop)

/-- The synchronized local hypothesis is also false at the first-parity input quotient: its
terminal test would require a nontrivial refinement to have a range-good map to `⊤`. -/
theorem
    not_sqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt_firstParity
    (h : ℕ) :
    ¬ SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt
      h (sqFirstParityKernel h) := by
  intro hlocal
  obtain ⟨W, hWtop, hgoodTop, hWparity, _hsolve⟩ := hlocal (SqTerminal h)
  exact not_sqUniversalBarInputTransitionRangeAt_top_of_le_firstParityKernel
    h W hWparity hWtop hgoodTop

/-- Regression bundle: every capstone premise based on literal range-good universal-relation
transport is uninhabited for the square presentation. -/
theorem sqCofinalTransitionDetector_noGo_regression (h : ℕ) :
    ¬ SqUniversalBarInputTransitionCommonRefinementRange h ∧
      ¬ SqUniversalBarInputTransitionPairDetectorCofinallyTrivial h ∧
        ¬ SqUniversalBarInputTransitionPairDetectorEffectiveMarking h ∧
          ¬ SqUniversalBarInputTransitionEventuallyRange h ∧
            ¬ SqUniversalBarInputTransitionRange h :=
  ⟨not_sqUniversalBarInputTransitionCommonRefinementRange h,
    not_sqUniversalBarInputTransitionPairDetectorCofinallyTrivial h,
    not_sqUniversalBarInputTransitionPairDetectorEffectiveMarking h,
    not_sqUniversalBarInputTransitionEventuallyRange h,
    not_sqUniversalBarInputTransitionRange h⟩

end

end GQ2.Dyadic.Count
