/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqReconstructionJointLiftObstruction
import GQ2.Dyadic.Count.H3SqReconstructionJointLiftCapstone
import GQ2.Dyadic.Count.H3SectionRefinementCoordinates
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Scalar and rank certificates for the joint square reconstruction lift

The affine-cokernel family still quantifies over a reconstruction map.  This file eliminates
that map: after choosing a reachable correction `K`, reconstruction is possible exactly when
the kernel of the corrected relation coordinate is contained in the kernel of the explicit
universal target.  In finite dimension this is the equality of the ranks of the corrected
coordinate and its product with the target.

We also give the fully scalar, basis-indexed bilinear equations.  All quantified types in that
certificate are finite, so it is the direct computational endpoint of the present reduction.

At the terminal quotient the reverse-three map is zero: its four Schreier terms cancel in
pairs.  The zero reconstruction table therefore solves the joint system unconditionally.  At
the first-parity quotient the same theorem specializes the unresolved problem to the finite
rank certificate below; the older terminal-transition obstruction does not constrain its
reachable corrections because all of them are Fox-invisible.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## A generic finite rank lemma -/

/-- For two maps with common finite-dimensional domain, factorization of `T` through `R` is
equivalent to saying that adjoining `T` does not increase the rank of `R`. -/
theorem linearMap_ker_le_ker_iff_finrank_range_prod_eq
    {k A D B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup D] [Module k D]
    [AddCommGroup B] [Module k B]
    (R : A →ₗ[k] D) (T : A →ₗ[k] B) :
    LinearMap.ker R ≤ LinearMap.ker T ↔
      Module.finrank k (LinearMap.range (R.prod T)) =
        Module.finrank k (LinearMap.range R) := by
  constructor
  · intro hker
    have hkerProd : LinearMap.ker (R.prod T) = LinearMap.ker R := by
      rw [LinearMap.ker_prod]
      exact inf_eq_left.mpr hker
    have hp := (R.prod T).finrank_range_add_finrank_ker
    have hR := R.finrank_range_add_finrank_ker
    rw [hkerProd] at hp
    exact Nat.add_right_cancel (hp.trans hR.symm)
  · intro hrank
    have hp := (R.prod T).finrank_range_add_finrank_ker
    have hR := R.finrank_range_add_finrank_ker
    have hkerRank :
        Module.finrank k (LinearMap.ker (R.prod T)) =
          Module.finrank k (LinearMap.ker R) := by
      apply Nat.add_left_cancel
      calc
        Module.finrank k (LinearMap.range R) +
              Module.finrank k (LinearMap.ker (R.prod T)) =
            Module.finrank k (LinearMap.range (R.prod T)) +
              Module.finrank k (LinearMap.ker (R.prod T)) := by rw [hrank]
        _ = Module.finrank k A := hp
        _ = Module.finrank k (LinearMap.range R) +
              Module.finrank k (LinearMap.ker R) := hR.symm
    have hle : LinearMap.ker (R.prod T) ≤ LinearMap.ker R := by
      rw [LinearMap.ker_prod]
      exact inf_le_left
    have heq : LinearMap.ker (R.prod T) = LinearMap.ker R :=
      Submodule.eq_of_le_of_finrank_eq hle hkerRank
    rw [LinearMap.ker_prod] at heq
    exact inf_eq_left.mp heq

/-! ## The smallest corrected-coordinate certificate -/

/-- The space of globally reachable finite relation-coordinate corrections is finite. -/
noncomputable instance instFintypeSqFiniteInputReachableRelationLiftCorrection
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :
    Fintype (SqFiniteInputReachableRelationLiftCorrection C) := by
  classical
  let A := FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)
  let Dambient := RegularModTwoRelationModule
    ((DSq h : Type) ⧸ C.W.toSubgroup) Unit
  let D := SqCompletedModTwoFoxKernelCoordinateRange h C.W
  letI : Fintype A := Fintype.ofFinite _
  letI : Fintype ((DSq h : Type) ⧸ C.W.toSubgroup) := Fintype.ofFinite _
  letI : Fintype Dambient := Finsupp.fintype
  letI : Fintype D := Fintype.ofFinite _
  letI : Finite (A →ₗ[ZMod 2] D) :=
    Finite.of_injective (fun f : A →ₗ[ZMod 2] D ↦ (f : A → D)) <| by
      intro f g hfg
      apply LinearMap.ext
      intro x
      exact congrFun hfg x
  exact Fintype.ofFinite _

/-- The corrected relation coordinate and the universal reconstruction target have the same
input.  The target factors through the corrected coordinate exactly when the displayed kernel
inclusion holds. -/
def SqFiniteInputRelationReconstructionReachableKernelCertificateAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∃ K : SqFiniteInputReachableRelationLiftCorrection C,
    LinearMap.ker
        (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K) ≤
      LinearMap.ker
        ((sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2)

/-- Equivalent rank-only form of the reachable kernel certificate. -/
def SqFiniteInputRelationReconstructionReachableRankCertificateAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∃ K : SqFiniteInputReachableRelationLiftCorrection C,
    let R := sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K
    let T := (sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2
    Module.finrank (ZMod 2) (LinearMap.range (R.prod T)) =
      Module.finrank (ZMod 2) (LinearMap.range R)

/-- Kernel and rank forms of the finite corrected-coordinate certificate agree. -/
theorem sqFiniteInputRelationReconstructionReachableKernelCertificateAt_iff_rank
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionReachableKernelCertificateAt C L₀ ↔
      SqFiniteInputRelationReconstructionReachableRankCertificateAt C L₀ := by
  constructor <;> rintro ⟨K, hK⟩ <;> refine ⟨K, ?_⟩
  · exact (linearMap_ker_le_ker_iff_finrank_range_prod_eq _ _).1 hK
  · exact (linearMap_ker_le_ker_iff_finrank_range_prod_eq _ _).2 hK

/-- Linear factorization through `R` is equivalent to the kernel inclusion, in the finite
vector spaces used here. -/
theorem exists_linearMap_comp_eq_of_ker_le_ker
    {k A D B : Type*} [Field k]
    [AddCommGroup A] [Module k A]
    [AddCommGroup D] [Module k D]
    [AddCommGroup B] [Module k B]
    (R : A →ₗ[k] D) (T : A →ₗ[k] B)
    (hker : LinearMap.ker R ≤ LinearMap.ker T) :
    ∃ E : D →ₗ[k] B, E.comp R = T := by
  let onRange : LinearMap.range R →ₗ[k] B :=
    ((LinearMap.ker R).liftQ T hker).comp
      R.quotKerEquivRange.symm.toLinearMap
  let hExtend := LinearMap.exists_extend onRange
  let E := Classical.choose hExtend
  have hE := Classical.choose_spec hExtend
  refine ⟨E, ?_⟩
  apply LinearMap.ext
  intro c
  let Rc : LinearMap.range R := ⟨R c, ⟨c, rfl⟩⟩
  calc
    E (R c) = E ((LinearMap.range R).subtype Rc) := rfl
    _ = onRange Rc := LinearMap.congr_fun hE Rc
    _ = T c := by simp [onRange, Rc]

/-- **Smallest finite certificate.**  Existence of a reconstruction-compatible lift is exactly
the existence of one reachable corrected relation coordinate whose rank is not increased by
adjoining the universal target. -/
theorem sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_reachableRankCertificate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt C ↔
      SqFiniteInputRelationReconstructionReachableRankCertificateAt C L₀ := by
  rw [← sqFiniteInputRelationReconstructionReachableKernelCertificateAt_iff_rank]
  constructor
  · intro hexists
    obtain ⟨E, hclass⟩ :=
      (sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_affineCokernelClass
        C L₀).1 hexists
    obtain ⟨K, hfactor⟩ :=
      (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
        C L₀ E).1 hclass
    refine ⟨K, fun c hc ↦ ?_⟩
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← LinearMap.congr_fun hfactor c, LinearMap.comp_apply, hc, map_zero]
  · rintro ⟨K, hker⟩
    obtain ⟨E, hfactor⟩ := exists_linearMap_comp_eq_of_ker_le_ker
      (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K)
      ((sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2) hker
    apply (sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_affineCokernelClass
      C L₀).2
    exact ⟨E,
      (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
        C L₀ E).2 ⟨K, hfactor⟩⟩

/-! ## Scalar bilinear equations -/

/-- Basis-indexed scalar form of the joint problem.  The variables are the reachable correction
`K` and the scalar entries of the reconstruction table; their product is the only bilinear
term. -/
def SqFiniteInputRelationReconstructionScalarBilinearCertificateAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∃ K : SqFiniteInputReachableRelationLiftCorrection C,
    ∃ table : SqFiniteRelationReconstructionBasisIndex h C.W →
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup),
      ∀ (i : SqFiniteInputReconstructionBasisIndex h V)
        (a : SqFiniteInputReconstructionBasisIndex h C.W),
        finiteFinsuppCoefficientEval (fun j ↦ table j a)
            (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K
              (Pi.basisFun (ZMod 2)
                (SqFiniteInputReconstructionBasisIndex h V) i)) =
          sqFiniteInputUniversalReconstructionColumn C a i

/-- The pair of finite unknowns enumerated by the scalar bilinear certificate. -/
abbrev SqFiniteInputRelationReconstructionScalarBilinearCandidate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :=
  SqFiniteInputReachableRelationLiftCorrection C ×
    (SqFiniteRelationReconstructionBasisIndex h C.W →
      FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ C.W.toSubgroup))

/-- The candidate space searched by the scalar certificate is finite. -/
noncomputable instance instFintypeSqFiniteInputRelationReconstructionScalarBilinearCandidate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :
    Fintype (SqFiniteInputRelationReconstructionScalarBilinearCandidate C) :=
  Fintype.ofFinite _

/-- The scalar bilinear certificate is exactly the affine-cokernel/rank problem. -/
theorem sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_scalarBilinearCertificate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt C ↔
      SqFiniteInputRelationReconstructionScalarBilinearCertificateAt C L₀ := by
  classical
  rw [sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_affineCokernelClass]
  let b := Pi.basisFun (ZMod 2) (SqFiniteInputReconstructionBasisIndex h V)
  constructor
  · rintro ⟨E, hclass⟩
    obtain ⟨K, hfactor⟩ :=
      (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
        C L₀ E).1 hclass
    let table : SqFiniteRelationReconstructionBasisIndex h C.W →
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      fun j ↦ E (Finsupp.single j 1)
    have htableE : E = Finsupp.linearCombination (ZMod 2) table := by
      apply Finsupp.basisSingleOne.ext
      intro j
      simp [table]
    refine ⟨K, table, fun i a ↦ ?_⟩
    have hi := congrFun (LinearMap.congr_fun hfactor (b i)) a
    rw [htableE] at hi
    change
      Finsupp.linearCombination (ZMod 2) table
          (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K (b i)) a =
        sqFiniteInputUniversalReconstructionTerm C (b i) a at hi
    change
      finiteFinsuppCoefficientEval (fun j ↦ table j a)
          (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K (b i)) =
        sqFiniteInputUniversalReconstructionTerm C (b i) a
    rw [finiteFinsuppCoefficientEval_functionLinearCombination]
    exact hi
  · rintro ⟨K, table, htable⟩
    let E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      Finsupp.linearCombination (ZMod 2) table
    refine ⟨E,
      (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
        C L₀ E).2 ⟨K, ?_⟩⟩
    apply b.ext
    intro i
    funext a
    change
      Finsupp.linearCombination (ZMod 2) table
          (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K (b i)) a =
        sqFiniteInputUniversalReconstructionTerm C (b i) a
    rw [← finiteFinsuppCoefficientEval_functionLinearCombination]
    exact htable i a

/-! ## Terminal and first-parity audit -/

/-- The terminal open normal subgroup. -/
def sqReconstructionTerminal (h : ℕ) : OpenNormalSubgroup (DSq h : Type) :=
  { toSubgroup := ⊤
    isOpen' := isOpen_univ
    isNormal' := Subgroup.normal_top }

/-- At a subsingleton group the degree-three reverse map is zero: the four equal Schreier terms
cancel in characteristic two. -/
theorem finiteBarToUniversalRelationThree_eq_zero_of_subsingleton
    {Q I : Type} [Group Q] [Subsingleton Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    finiteBarToUniversalRelationThree m heval = 0 := by
  classical
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext_ring
  rcases p with ⟨g, q, r, s⟩
  have hg : g = 1 := Subsingleton.elim _ _
  have hq : q = 1 := Subsingleton.elim _ _
  have hr : r = 1 := Subsingleton.elim _ _
  have hs : s = 1 := Subsingleton.elim _ _
  subst g
  subst q
  subst r
  subst s
  change finiteBarToUniversalRelationThree m heval
      (Finsupp.single (1, (1, 1, 1)) 1) = 0
  rw [finiteBarToUniversalRelationThree_single]
  simp only [one_mul]
  let z : RegularModTwoRelationModule Q (FreeRelationKernel m) :=
    Finsupp.single (1, relationDefect heval 1 1) 1
  change z + z + z + z = 0
  calc
    z + z + z + z = (z + z) + (z + z) := by abel
    _ = 0 := by simp only [regularModTwoRelationModule_add_self, zero_add]

/-- The concrete reverse-three map at the terminal quotient vanishes. -/
theorem sqTerminal_finiteBarToUniversalRelationThree_eq_zero (h : ℕ) :
    finiteBarToUniversalRelationThree
      (sqOpenQuotientMarking h (sqReconstructionTerminal h))
      (sqOpenQuotientFreeEvaluation_surjective h (sqReconstructionTerminal h)) = 0 := by
  letI : Subsingleton
      ((DSq h : Type) ⧸ (sqReconstructionTerminal h).toSubgroup) := by
    simp [sqReconstructionTerminal]
  exact finiteBarToUniversalRelationThree_eq_zero_of_subsingleton _ _

/-- The joint reconstruction system is genuinely inhabited at the terminal input quotient.
The solution uses no lift correction and the zero reconstruction table. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.terminal_jointLiftSystem
    {h : ℕ}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h
      (sqReconstructionTerminal h)) :
    SqFiniteInputRelationReconstructionJointLiftSystemAt
      S.degreeThreeComparison
      S.universalSyzygy.relationLiftOfSqPresentation := by
  classical
  refine ⟨fun _ ↦ 0, fun _ ↦ Submodule.zero_mem _, fun _ ↦ 0, fun i ↦ ?_⟩
  simp only [add_zero, Finsupp.linearCombination_apply, smul_zero,
    Finsupp.sum_fun_zero]
  funext a
  have hcolumn := S.universalReconstructionColumn_apply a i
  rw [sqTerminal_finiteBarToUniversalRelationThree_eq_zero h,
    LinearMap.zero_apply, map_zero] at hcolumn
  exact hcolumn.symm

/-- At first parity, reconstruction is reduced without loss to the finite rank certificate.
This is the precise check which remains after the terminal and Fox-parity tests. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.firstParity_compatibleLiftExists_iff_rank
    {h : ℕ}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h
      (sqFirstParityKernel h)) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt S.degreeThreeComparison ↔
      SqFiniteInputRelationReconstructionReachableRankCertificateAt
        S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation :=
  sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_reachableRankCertificate
    S.degreeThreeComparison
    S.universalSyzygy.relationLiftOfSqPresentation

/-- The first parity map is onto: the zeroth marked generator supplies its nontrivial value. -/
theorem sqFirstParityHom_surjective (h : ℕ) :
    Function.Surjective (sqFirstParityHom h).toMonoidHom := by
  intro y
  rcases ZMod.eq_zero_or_eq_one y.toAdd with hy | hy
  · refine ⟨1, ?_⟩
    rw [map_one]
    exact (congrArg Multiplicative.ofAdd hy).symm
  · refine ⟨sqGen h 0, ?_⟩
    exact (sqFirstParityHom_gen_zero h).trans
      (congrArg Multiplicative.ofAdd hy).symm

/-- The first-parity quotient is the two-element group, not merely a group mapping to it. -/
noncomputable def sqFirstParityQuotientEquiv (h : ℕ) :
    ((DSq h : Type) ⧸ (sqFirstParityKernel h).toSubgroup) ≃*
      Multiplicative (ZMod 2) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (sqFirstParityHom h).toMonoidHom (sqFirstParityHom_surjective h)

/-- The finite one-relator coordinate space at first parity has dimension exactly two. -/
theorem sqFirstParity_relationModule_finrank (h : ℕ) :
    Module.finrank (ZMod 2)
      (RegularModTwoRelationModule
        ((DSq h : Type) ⧸ (sqFirstParityKernel h).toSubgroup) Unit) = 2 := by
  classical
  letI : Fintype
      ((DSq h : Type) ⧸ (sqFirstParityKernel h).toSubgroup) :=
    Fintype.ofFinite _
  rw [Module.finrank_finsupp_self, Fintype.card_prod]
  have hcard : Fintype.card
      ((DSq h : Type) ⧸ (sqFirstParityKernel h).toSubgroup) =
        Fintype.card (Multiplicative (ZMod 2)) :=
    Fintype.card_congr (sqFirstParityQuotientEquiv h).toEquiv
  rw [hcard]
  decide

/-- A genuine first-parity no-go can only occur if the target rank exceeds two.  Every joint
solution forces this explicit necessary bound. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.firstParity_target_finrank_le_two
    {h : ℕ}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h
      (sqFirstParityKernel h))
    (H : SqFiniteInputRelationReconstructionCompatibleLiftExistsAt
      S.degreeThreeComparison) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((sqFiniteInputUniversalReconstructionTerm
        S.degreeThreeComparison).toZModLinearMap 2)) ≤ 2 := by
  obtain ⟨E, hclass⟩ :=
    (sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_affineCokernelClass
      S.degreeThreeComparison
      S.universalSyzygy.relationLiftOfSqPresentation).1 H
  obtain ⟨K, hfactor⟩ :=
    (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
      S.degreeThreeComparison
      S.universalSyzygy.relationLiftOfSqPresentation E).1 hclass
  let R := sqFiniteInputRelationReconstructionCoordinateWithCorrection
    S.degreeThreeComparison
    S.universalSyzygy.relationLiftOfSqPresentation K
  let T := (sqFiniteInputUniversalReconstructionTerm
    S.degreeThreeComparison).toZModLinearMap 2
  have hrange : LinearMap.range T = LinearMap.range (E.comp R) := by
    rw [hfactor]
  calc
    Module.finrank (ZMod 2) (LinearMap.range T) =
        Module.finrank (ZMod 2) (LinearMap.range (E.comp R)) :=
      by rw [hrange]
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range E) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range R E)
    _ ≤ Module.finrank (ZMod 2)
        (RegularModTwoRelationModule
          ((DSq h : Type) ⧸
            (sqFirstParityKernel h).toSubgroup) Unit) :=
      E.finrank_range_le
    _ = 2 := sqFirstParity_relationModule_finrank h

/-- Scalar, basis-indexed first-parity regression suitable for a finite computation. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.firstParity_compatibleLiftExists_iff_scalar
    {h : ℕ}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h
      (sqFirstParityKernel h)) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt S.degreeThreeComparison ↔
      SqFiniteInputRelationReconstructionScalarBilinearCertificateAt
        S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation :=
  sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_scalarBilinearCertificate
    S.degreeThreeComparison
    S.universalSyzygy.relationLiftOfSqPresentation

/-! ## Global scalar-certificate consumer -/

/-- One finite basis-indexed bilinear certificate at every input quotient supplies the square
core `H²` right-exactness theorem. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_scalarBilinearCertificates
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hscalar : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionScalarBilinearCertificateAt
        (S V).degreeThreeComparison
        (S V).universalSyzygy.relationLiftOfSqPresentation) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  GQ2.ContCoh.finiteElementaryH2RightExactSupply_DSq_of_jointReconstructionLiftSystems
    h H S (fun V ↦
      (S V).exists_reconstructionCompatibleLift_iff_jointSystem.mp
        ((sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_scalarBilinearCertificate
          (S V).degreeThreeComparison
          (S V).universalSyzygy.relationLiftOfSqPresentation).mpr (hscalar V)))

#print axioms linearMap_ker_le_ker_iff_finrank_range_prod_eq
#print axioms sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_reachableRankCertificate
#print axioms sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_scalarBilinearCertificate
#print axioms SqCompatibleUniversalCocycleCancellingSyzygyAt.terminal_jointLiftSystem
#print axioms SqCompatibleUniversalCocycleCancellingSyzygyAt.firstParity_compatibleLiftExists_iff_rank
#print axioms finiteElementaryH2RightExactSupply_DSq_of_scalarBilinearCertificates

end

end GQ2.Dyadic.Count
