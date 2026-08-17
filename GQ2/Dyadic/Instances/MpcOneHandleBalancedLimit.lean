/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDefectObstruction
import GQ2.Dyadic.Instances.MpcBuild
import GQ2.Dyadic.MarkedCore.MScalingHandles
import GQ2.Dyadic.SqCore.GradedLimit

/-!
# Balanced finite-level production of a one-handle Mpc defect absorber

This file gives two positive routes around
`MpcOneHandleDefectObstruction.lean`'s arbitrary-lift counterexample.

First, `oneHandleDAbsorbable_of_forall_class` proves a fixed-tuple compactness criterion: kernel
corrections solving the `D`-slot equation separately in every finite two-central quotient have
one exact common solution.  The corrected-`D` formulation
`oneHandleDAbsorbable_of_DLetter_forall_class` supports a rungwise climb.
`FixedCRelativeBracketSurjective` states the exact missing graded input, and
`oneHandleDAbsorbable_of_balanced_fixedC` shows that this input plus a balanced class-two seed
produces an exact absorber.  `mpcBld_incr_near` is the engine: a depth-`j` change of the
`D`-letter contributes precisely the fixed-`C` bracket in class `j+2`.

Second, `oneHandleBalancedSet` lets all four lifts and the correction vary simultaneously.
It carries the four forgetful fibers, the kernel condition, the universal `C + 2B` row, the
finite-depth relator equation, and mod-two independence of the corrected marking.  Every clause
is closed.  Nested-set compactness therefore selects one exact balanced tuple, while the pro-2
Frattini criterion promotes its mod-two independence to topological generation.  Consequently
`oneHandleDDefectAbsorption_of_balanced_forall_class` produces the complete landed absorption
predicate, and `mpcPivShiftH_two_one_of_balanced_forall_class` feeds it directly to the existing
one-handle shift consumer.

The inverse-limit step is thus complete.  The remaining substantive mathematical seam for a
rungwise construction is fixed-`C` bracket surjectivity on the relative handle-kernel layers.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleDefectObstruction
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Roe.Labute

/-- The multiplicative error in the one-handle `D`-slot correction equation. -/
def oneHandleDDefect (a b c d z : DM 2 1) : DM 2 1 :=
  conjP (commP c z) d *
    ((mWord 2 a b c d)⁻¹ *
      (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
        (dmGen 2 1 (handleIdxV (0 : Fin 1))))⁻¹)⁻¹

theorem oneHandleDDefect_eq_one_iff (a b c d z : DM 2 1) :
    oneHandleDDefect a b c d z = 1 ↔
      conjP (commP c z) d =
        (mWord 2 a b c d)⁻¹ *
          (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
            (dmGen 2 1 (handleIdxV (0 : Fin 1))))⁻¹ := by
  rw [oneHandleDDefect, mul_inv_eq_one]

theorem continuous_oneHandleDDefect (a b c d : DM 2 1) :
    Continuous fun z => oneHandleDDefect a b c d z := by
  simp only [oneHandleDDefect, commP, conjP, mWord]
  fun_prop

/-- Kernel corrections solving the equation modulo the `k`-th two-central subgroup. -/
def oneHandleDApproxSet (a b c d : DM 2 1) (k : ℕ) : Set (DM 2 1) :=
  {z | dmForgetHandles 2 1 z = 1 ∧
    oneHandleDDefect a b c d z ∈ twoCentralSeries (DM 2 1) k}

theorem mem_oneHandleDApproxSet_iff_level {a b c d z : DM 2 1} (k : ℕ) :
    z ∈ oneHandleDApproxSet a b c d k ↔
      dmForgetHandles 2 1 z = 1 ∧
      levelMk (DM 2 1) k (conjP (commP c z) d) =
        levelMk (DM 2 1) k
          ((mWord 2 a b c d)⁻¹ *
            (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
              (dmGen 2 1 (handleIdxV (0 : Fin 1))))⁻¹) := by
  rw [oneHandleDApproxSet, Set.mem_setOf_eq, lim_mem_twoCentralSeries_iff_levelMk,
    oneHandleDDefect, map_mul, map_inv, mul_inv_eq_one]

theorem oneHandleDApproxSet_antitone {a b c d : DM 2 1} {k k' : ℕ} (hkk : k' ≤ k) :
    oneHandleDApproxSet a b c d k ⊆ oneHandleDApproxSet a b c d k' :=
  fun _ ⟨hz, hdef⟩ =>
    ⟨hz, twoCentralSeries_antitone (G := DM 2 1) hkk hdef⟩

theorem oneHandleDApproxSet_isClosed (a b c d : DM 2 1) (k : ℕ) :
    IsClosed (oneHandleDApproxSet a b c d k) := by
  have hker : IsClosed {z : DM 2 1 | dmForgetHandles 2 1 z = 1} :=
    isClosed_eq (dmForgetHandles 2 1).continuous_toFun continuous_const
  exact hker.inter
    ((isClosed_twoCentralSeries (G := DM 2 1) k).preimage
      (continuous_oneHandleDDefect a b c d))

theorem oneHandle_iInf_twoCentralSeries :
    ⨅ k, twoCentralSeries (DM 2 1) k = ⊥ :=
  iInf_twoCentralSeries (G := DM 2 1) (dm_topologicallyFinGen 2 1) (isProP_DM 2 1)

/-- Per-class solvability by kernel corrections gives one exact correction.  The witnesses at
the different finite classes need not be chosen compatibly: nested closed-set compactness makes
the compatible choice. -/
theorem oneHandleDAbsorbable_of_forall_class {a b c d : DM 2 1}
    (H : ∀ k, (oneHandleDApproxSet a b c d k).Nonempty) :
    MpcOneHandleDAbsorbable a b c d := by
  have hne : (⋂ k, oneHandleDApproxSet a b c d k).Nonempty := by
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro k k'
      exact ⟨max k k', oneHandleDApproxSet_antitone (le_max_left k k'),
        oneHandleDApproxSet_antitone (le_max_right k k')⟩
    · exact H
    · exact fun k => (oneHandleDApproxSet_isClosed a b c d k).isCompact
    · exact oneHandleDApproxSet_isClosed a b c d
  obtain ⟨z, hz⟩ := hne
  have hmem : ∀ k, z ∈ oneHandleDApproxSet a b c d k := Set.mem_iInter.mp hz
  refine ⟨z, (hmem 0).1, ?_⟩
  have hall : oneHandleDDefect a b c d z ∈
      ⨅ k, twoCentralSeries (DM 2 1) k :=
    Subgroup.mem_iInf.mpr fun k => (hmem k).2
  rw [oneHandle_iInf_twoCentralSeries, Subgroup.mem_bot,
    oneHandleDDefect_eq_one_iff] at hall
  exact hall

/-! A rungwise fixed-`C` producer, with the correction absorbed into the `D`-letter. -/

abbrev OneHandleGroup := DM 2 1

def oneHandleDTarget : OneHandleGroup :=
  (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
    (dmGen 2 1 (handleIdxV (0 : Fin 1))))⁻¹

/-- Corrected `D`-letters in the same forgetful fiber as `d`, solving the target core word to
class `k`. -/
def oneHandleDLetterApproxSet (a b c d : OneHandleGroup) (k : ℕ) :
    Set OneHandleGroup :=
  {e | dmForgetHandles 2 1 e = dmForgetHandles 2 1 d ∧
    (mWord 2 a b c e)⁻¹ * oneHandleDTarget ∈
      twoCentralSeries OneHandleGroup k}

theorem oneHandleDLetterApproxSet_antitone (a b c d : OneHandleGroup)
    {k k' : ℕ} (hkk : k' ≤ k) :
    oneHandleDLetterApproxSet a b c d k ⊆ oneHandleDLetterApproxSet a b c d k' :=
  fun _ he => ⟨he.1, twoCentralSeries_antitone OneHandleGroup hkk he.2⟩

theorem oneHandleDLetterApproxSet_isClosed (a b c d : OneHandleGroup) (k : ℕ) :
    IsClosed (oneHandleDLetterApproxSet a b c d k) := by
  have hq : IsClosed {e : OneHandleGroup |
      dmForgetHandles 2 1 e = dmForgetHandles 2 1 d} :=
    isClosed_eq (dmForgetHandles 2 1).continuous_toFun continuous_const
  have hc : Continuous (fun e : OneHandleGroup =>
      (mWord 2 a b c e)⁻¹ * oneHandleDTarget) := by
    simp only [mWord, commP, oneHandleDTarget]
    fun_prop
  exact hq.inter ((isClosed_twoCentralSeries OneHandleGroup k).preimage hc)

/-- The corrected-`D` version of the per-class criterion. -/
theorem oneHandleDAbsorbable_of_DLetter_forall_class
    (a b c d : OneHandleGroup)
    (H : ∀ k, (oneHandleDLetterApproxSet a b c d k).Nonempty) :
    MpcOneHandleDAbsorbable a b c d := by
  have hne : (⋂ k, oneHandleDLetterApproxSet a b c d k).Nonempty := by
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro k k'
      exact ⟨max k k', oneHandleDLetterApproxSet_antitone a b c d (le_max_left k k'),
        oneHandleDLetterApproxSet_antitone a b c d (le_max_right k k')⟩
    · exact H
    · exact fun k => (oneHandleDLetterApproxSet_isClosed a b c d k).isCompact
    · exact fun k => oneHandleDLetterApproxSet_isClosed a b c d k
  obtain ⟨e, he⟩ := hne
  have heall : ∀ k, e ∈ oneHandleDLetterApproxSet a b c d k := Set.mem_iInter.mp he
  have hres : (mWord 2 a b c e)⁻¹ * oneHandleDTarget ∈
      ⨅ k, twoCentralSeries OneHandleGroup k :=
    Subgroup.mem_iInf.mpr fun k => (heall k).2
  rw [oneHandle_iInf_twoCentralSeries, Subgroup.mem_bot] at hres
  have heq : mWord 2 a b c e = oneHandleDTarget := inv_mul_eq_one.mp hres
  let z := e * d⁻¹
  refine ⟨z, ?_, ?_⟩
  · dsimp [z]
    rw [map_mul, map_inv, (heall 0).1, mul_inv_cancel]
  · have hw := mWord_mul_left_D 2 a b c d z
    have hzd : z * d = e := by dsimp [z]; group
    rw [hzd, heq] at hw
    dsimp [oneHandleDTarget] at hw ⊢
    rw [hw]
    group

/-- Exact missing rungwise input: fixed-`C` bracketing is onto every relative handle-kernel
layer. -/
def FixedCRelativeBracketSurjective (c : OneHandleGroup) : Prop :=
  ∀ (j : ℕ) (r : OneHandleGroup),
    r ∈ twoCentralSeries OneHandleGroup (j + 1) →
    dmForgetHandles 2 1 r = 1 →
    ∃ epsilon : OneHandleGroup,
      epsilon ∈ twoCentralSeries OneHandleGroup j ∧
      dmForgetHandles 2 1 epsilon = 1 ∧
      levelMk OneHandleGroup (j + 2) (commP c epsilon) =
        levelMk OneHandleGroup (j + 2) r

/-- One fixed-`C` relative bracket solution climbs a corrected `D`-letter by one class. -/
theorem oneHandleDLetterApproxSet_succ_of_fixedC
    (a b c d e : OneHandleGroup) (j : ℕ)
    (hqword : dmForgetHandles 2 1 (mWord 2 a b c d) = 1)
    (he : e ∈ oneHandleDLetterApproxSet a b c d (j + 1))
    (Had : FixedCRelativeBracketSurjective c) :
    (oneHandleDLetterApproxSet a b c d (j + 2)).Nonempty := by
  let r := (mWord 2 a b c e)⁻¹ * oneHandleDTarget
  have hr : r ∈ twoCentralSeries OneHandleGroup (j + 1) := he.2
  have hqe : dmForgetHandles 2 1 (mWord 2 a b c e) = 1 := by
    rw [map_mWord] at hqword ⊢
    rw [he.1]
    exact hqword
  have hqt : dmForgetHandles 2 1 oneHandleDTarget = 1 := by
    simp only [oneHandleDTarget, map_inv, commP, map_mul, dmForgetHandles_handleU,
      dmForgetHandles_handleV, inv_one, mul_one]
  have hqr : dmForgetHandles 2 1 r = 1 := by
    dsimp [r]
    rw [map_mul, map_inv, hqe, hqt, inv_one, one_mul]
  obtain ⟨epsilon, hepsilon, hqepsilon, had⟩ := Had j r hr hqr
  refine ⟨e * epsilon, ?_, ?_⟩
  · rw [map_mul, hqepsilon, mul_one, he.1]
  · rw [lim_mem_twoCentralSeries_iff_levelMk]
    have hinc :
        levelMk OneHandleGroup (j + 2) (mWord 2 a b c (e * epsilon)) =
          levelMk OneHandleGroup (j + 2) (mWord 2 a b c e * commP c epsilon) := by
      simpa only [map_mWord, map_mul, commP, map_inv] using
        (mpcBld_incr_near (C := levelMk OneHandleGroup (j + 2) c) (y := 1)
          (show levelMk OneHandleGroup (j + 2) c =
            levelMk OneHandleGroup (j + 2) c * 1 by simp)
          (Subgroup.one_mem (lambdaImage OneHandleGroup 2 (j + 2)))
          ⟨epsilon, hepsilon, rfl⟩)
    rw [map_mul, map_inv, hinc, map_mul, mul_inv_rev]
    have hrmap : levelMk OneHandleGroup (j + 2) r =
        (levelMk OneHandleGroup (j + 2) (mWord 2 a b c e))⁻¹ *
          levelMk OneHandleGroup (j + 2) oneHandleDTarget := by
      dsimp [r]
      rw [map_mul, map_inv]
    rw [had, hrmap]
    group

/-- A balanced seed and relative fixed-`C` bracket surjectivity produce an exact one-handle
`D`-slot absorber. -/
theorem oneHandleDAbsorbable_of_balanced_fixedC
    (a b c d : OneHandleGroup)
    (hqword : dmForgetHandles 2 1 (mWord 2 a b c d) = 1)
    (hbase : (mWord 2 a b c d)⁻¹ * oneHandleDTarget ∈
      twoCentralSeries OneHandleGroup 2)
    (Had : FixedCRelativeBracketSurjective c) :
    MpcOneHandleDAbsorbable a b c d := by
  apply oneHandleDAbsorbable_of_DLetter_forall_class
  intro k
  by_cases hk : k ≤ 2
  · exact ⟨d, rfl, twoCentralSeries_antitone OneHandleGroup hk hbase⟩
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    clear hk
    induction n with
    | zero => exact ⟨d, rfl, hbase⟩
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      exact oneHandleDLetterApproxSet_succ_of_fixedC
        a b c d e (n + 1) hqword he Had

/-! The balanced version lets all four lifts and the kernel correction vary together. -/

abbrev OneHandleBalancedPoint :=
  (DM 2 1) × (DM 2 1) × (DM 2 1) × (DM 2 1) × (DM 2 1)

def balancedA (p : OneHandleBalancedPoint) : DM 2 1 := p.1
def balancedB (p : OneHandleBalancedPoint) : DM 2 1 := p.2.1
def balancedC (p : OneHandleBalancedPoint) : DM 2 1 := p.2.2.1
def balancedD (p : OneHandleBalancedPoint) : DM 2 1 := p.2.2.2.1
def balancedZ (p : OneHandleBalancedPoint) : DM 2 1 := p.2.2.2.2

def balancedCorrectedMark (p : OneHandleBalancedPoint) :
    Fin (coreRank 1) → DM 2 1 :=
  standardHandleMark (balancedA p) (balancedB p) (balancedC p)
    (balancedZ p * balancedD p)

theorem continuous_balancedA : Continuous balancedA := continuous_fst
theorem continuous_balancedB : Continuous balancedB := continuous_fst.comp continuous_snd
theorem continuous_balancedC : Continuous balancedC :=
  continuous_fst.comp (continuous_snd.comp continuous_snd)
theorem continuous_balancedD : Continuous balancedD :=
  continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
theorem continuous_balancedZ : Continuous balancedZ :=
  continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))

/-- The mod-two generation condition for a one-handle marking. -/
def OneHandleModTwoIndep (m : Fin (coreRank 1) → DM 2 1) : Prop :=
  ∀ M : OpenNormalSubgroup (DM 2 1), M.toSubgroup.index = 2 →
    ∃ i, m i ∉ M.toSubgroup

/-- A mod-two independent marking topologically generates `DM 2 1`. -/
theorem topGen_of_oneHandleModTwoIndep {m : Fin (coreRank 1) → DM 2 1}
    (hm : OneHandleModTwoIndep m) :
    (Subgroup.closure (Set.range m)).topologicalClosure = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_top_of_forall_not_le_index_p (p := 2) (isProP_DM 2 1)
    (Subgroup.isClosed_topologicalClosure _) ?_
  intro M hM hle
  obtain ⟨i, hi⟩ := hm M hM
  exact hi (hle (Subgroup.le_topologicalClosure _
    (Subgroup.subset_closure (Set.mem_range_self i))))

theorem continuous_balancedCorrectedMark_apply (i : Fin (coreRank 1)) :
    Continuous fun p => balancedCorrectedMark p i := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
  · simp only [balancedCorrectedMark, standardHandleMark_zero]
    exact continuous_balancedA
  · simp only [balancedCorrectedMark, standardHandleMark_one]
    exact continuous_balancedB
  · simp only [balancedCorrectedMark, standardHandleMark_two]
    exact continuous_balancedC
  · simp only [balancedCorrectedMark, standardHandleMark_three]
    exact continuous_balancedZ.mul continuous_balancedD
  · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [balancedCorrectedMark, mHandleIdx_coordU, standardHandleMark_handleU]
      exact continuous_const
    · simp only [balancedCorrectedMark, mHandleIdx_coordV, standardHandleMark_handleV]
      exact continuous_const

/-- Mod-two independence is a closed condition on balanced points. -/
theorem oneHandleBalancedSet_isClosed_indep :
    IsClosed {p : OneHandleBalancedPoint |
      OneHandleModTwoIndep (balancedCorrectedMark p)} := by
  have hset : {p : OneHandleBalancedPoint |
      OneHandleModTwoIndep (balancedCorrectedMark p)} =
      ⋂ (M : OpenNormalSubgroup (DM 2 1)) (_ : M.toSubgroup.index = 2),
        ⋃ i : Fin (coreRank 1),
          {p : OneHandleBalancedPoint |
            balancedCorrectedMark p i ∈ ((M.toSubgroup : Set (DM 2 1)))ᶜ} := by
    ext p
    simp only [OneHandleModTwoIndep, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_compl_iff, SetLike.mem_coe]
  rw [hset]
  refine isClosed_iInter fun M => isClosed_iInter fun _ =>
    isClosed_iUnion_of_finite fun i => ?_
  exact IsClosed.preimage (continuous_balancedCorrectedMark_apply i)
    M.isOpen'.isClosed_compl

def oneHandleBalancedSet
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) (k : ℕ) :
    Set OneHandleBalancedPoint :=
  {p |
    dmForgetHandles 2 1 (balancedA p) = Psi0 (dmA 2 0) ∧
    dmForgetHandles 2 1 (balancedB p) = Psi0 (dmB 2 0) ∧
    dmForgetHandles 2 1 (balancedC p) = Psi0 (dmC 2 0) ∧
    dmForgetHandles 2 1 (balancedD p) = Psi0 (dmD 2 0) ∧
    dmForgetHandles 2 1 (balancedZ p) = 1 ∧
    OneHandleModTwoIndep (balancedCorrectedMark p) ∧
    (∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
      toAdd (f (balancedC p)) =
        toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))) ∧
    oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
      (balancedD p) (balancedZ p) ∈ twoCentralSeries (DM 2 1) k}

theorem oneHandleBalancedSet_antitone
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)} {k k' : ℕ} (hkk : k' ≤ k) :
    oneHandleBalancedSet Psi0 k ⊆ oneHandleBalancedSet Psi0 k' :=
  fun _ ⟨ha, hb, hc, hd, hz, hind, hrow, hdef⟩ =>
    ⟨ha, hb, hc, hd, hz, hind, hrow,
      twoCentralSeries_antitone (G := DM 2 1) hkk hdef⟩

theorem continuous_balancedDefect : Continuous fun p : OneHandleBalancedPoint =>
    oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
      (balancedD p) (balancedZ p) := by
  simp only [oneHandleDDefect, balancedA, balancedB, balancedC, balancedD, balancedZ,
    commP, conjP, mWord]
  fun_prop

theorem oneHandleBalancedSet_isClosed_row : IsClosed
    {p : OneHandleBalancedPoint |
      ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
        toAdd (f (balancedC p)) =
          toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))} := by
  rw [show {p : OneHandleBalancedPoint |
      ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
        toAdd (f (balancedC p)) =
          toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))} =
      ⋂ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
        {p | toAdd (f (balancedC p)) =
        toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))} by ext p; simp]
  exact isClosed_iInter fun f => isClosed_eq
    (continuous_toAdd.comp (f.continuous_toFun.comp continuous_balancedC)) continuous_const

theorem oneHandleBalancedSet_isClosed
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) (k : ℕ) :
    IsClosed (oneHandleBalancedSet Psi0 k) := by
  have ha : IsClosed {p : OneHandleBalancedPoint |
      dmForgetHandles 2 1 (balancedA p) = Psi0 (dmA 2 0)} :=
    isClosed_eq ((dmForgetHandles 2 1).continuous_toFun.comp continuous_balancedA) continuous_const
  have hb : IsClosed {p : OneHandleBalancedPoint |
      dmForgetHandles 2 1 (balancedB p) = Psi0 (dmB 2 0)} :=
    isClosed_eq ((dmForgetHandles 2 1).continuous_toFun.comp continuous_balancedB) continuous_const
  have hc : IsClosed {p : OneHandleBalancedPoint |
      dmForgetHandles 2 1 (balancedC p) = Psi0 (dmC 2 0)} :=
    isClosed_eq ((dmForgetHandles 2 1).continuous_toFun.comp continuous_balancedC) continuous_const
  have hd : IsClosed {p : OneHandleBalancedPoint |
      dmForgetHandles 2 1 (balancedD p) = Psi0 (dmD 2 0)} :=
    isClosed_eq ((dmForgetHandles 2 1).continuous_toFun.comp continuous_balancedD) continuous_const
  have hz : IsClosed {p : OneHandleBalancedPoint |
      dmForgetHandles 2 1 (balancedZ p) = 1} :=
    isClosed_eq ((dmForgetHandles 2 1).continuous_toFun.comp continuous_balancedZ) continuous_const
  exact ha.inter (hb.inter (hc.inter (hd.inter (hz.inter
    (oneHandleBalancedSet_isClosed_indep.inter
      (oneHandleBalancedSet_isClosed_row.inter
        ((isClosed_twoCentralSeries (G := DM 2 1) k).preimage
          continuous_balancedDefect)))))))

/-- The compactness core for balanced points. -/
theorem oneHandleBalanced_iInter_nonempty
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (H : ∀ k, (oneHandleBalancedSet Psi0 k).Nonempty) :
    (⋂ k, oneHandleBalancedSet Psi0 k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k k'
    exact ⟨max k k', oneHandleBalancedSet_antitone (le_max_left k k'),
      oneHandleBalancedSet_antitone (le_max_right k k')⟩
  · exact H
  · exact fun k => (oneHandleBalancedSet_isClosed Psi0 k).isCompact
  · exact oneHandleBalancedSet_isClosed Psi0

/-- A balanced family of finite-class lift/correction solutions has one exact limit tuple.
Unlike arbitrary-lift repair, the lifts and the correction are selected simultaneously. -/
theorem exists_balanced_absorbable_of_forall_class
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (H : ∀ k, (oneHandleBalancedSet Psi0 k).Nonempty) :
    ∃ a b c d : DM 2 1,
      dmForgetHandles 2 1 a = Psi0 (dmA 2 0) ∧
      dmForgetHandles 2 1 b = Psi0 (dmB 2 0) ∧
      dmForgetHandles 2 1 c = Psi0 (dmC 2 0) ∧
      dmForgetHandles 2 1 d = Psi0 (dmD 2 0) ∧
      (∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
        toAdd (f c) = toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))) ∧
      MpcOneHandleDAbsorbable a b c d := by
  obtain ⟨p, hp⟩ := oneHandleBalanced_iInter_nonempty Psi0 H
  have hmem : ∀ k, p ∈ oneHandleBalancedSet Psi0 k := Set.mem_iInter.mp hp
  obtain ⟨ha, hb, hc, hd, hz, _, hrow, -⟩ := hmem 0
  refine ⟨balancedA p, balancedB p, balancedC p, balancedD p,
    ha, hb, hc, hd, hrow, balancedZ p, hz, ?_⟩
  have hall : oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
      (balancedD p) (balancedZ p) ∈ ⨅ k, twoCentralSeries (DM 2 1) k :=
    Subgroup.mem_iInf.mpr fun k => (hmem k).2.2.2.2.2.2.2
  rw [oneHandle_iInf_twoCentralSeries, Subgroup.mem_bot,
    oneHandleDDefect_eq_one_iff] at hall
  exact hall

/-- The balanced per-class criterion supplies the full landed one-handle absorption predicate.
Mod-two independence is a closed finite-stage clause, and the pro-2 Frattini criterion promotes
it to topological generation at the exact limit. -/
theorem oneHandleDDefectAbsorption_of_balanced_forall_class
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (H : ∀ k, (oneHandleBalancedSet Psi0 k).Nonempty) :
    MpcOneHandleDDefectAbsorption Psi0 := by
  obtain ⟨p, hp⟩ := oneHandleBalanced_iInter_nonempty Psi0 H
  have hmem : ∀ k, p ∈ oneHandleBalancedSet Psi0 k := Set.mem_iInter.mp hp
  obtain ⟨ha, hb, hc, hd, hz, hind, hrow, -⟩ := hmem 0
  refine ⟨balancedA p, balancedB p, balancedC p, balancedD p, balancedZ p,
    ha, hb, hc, hd, hz, ?_, topGen_of_oneHandleModTwoIndep hind, hrow⟩
  have hall : oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
      (balancedD p) (balancedZ p) ∈ ⨅ k, twoCentralSeries (DM 2 1) k :=
    Subgroup.mem_iInf.mpr fun k => (hmem k).2.2.2.2.2.2.2
  rw [oneHandle_iInf_twoCentralSeries, Subgroup.mem_bot,
    oneHandleDDefect_eq_one_iff] at hall
  exact hall

/-- Feeding the balanced finite-class criterion to the landed consumer produces the one-handle
odd shear. -/
theorem mpcPivShiftH_two_one_of_balanced_forall_class
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (H : ∀ k, (oneHandleBalancedSet Psi0 k).Nonempty) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_DDefectAbsorption Psi0 hchi0
    (oneHandleDDefectAbsorption_of_balanced_forall_class Psi0 H)

#print axioms oneHandleDAbsorbable_of_forall_class
#print axioms oneHandleBalanced_iInter_nonempty
#print axioms exists_balanced_absorbable_of_forall_class
#print axioms oneHandleDDefectAbsorption_of_balanced_forall_class
#print axioms mpcPivShiftH_two_one_of_balanced_forall_class

end
end GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
