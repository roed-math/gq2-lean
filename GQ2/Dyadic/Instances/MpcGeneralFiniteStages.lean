import GQ2.Dyadic.Instances.MpcGeneralHandleShiftRecipe
import GQ2.Dyadic.Instances.StageAbstractionEvenTransgression
import GQ2.Dyadic.SqCore.ArbFrames

/-!
# Uniform finite-stage criterion for the general Mpc pivot shift

This module works at arbitrary `alpha` and handle count `h`.  A stage is a full marking of
`DM alpha h` with the canonical orientation rows, the universal `C + 2 B` row, mod-two
generation, and relator defect in the `k`-th two-central subgroup.  The stage spaces are nested
closed subsets of a compact function space.  Consequently, solvability at every finite stage is
equivalent to the actual general pivot shift; the witnesses need not be chosen compatibly.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralFiniteStages

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleShiftRecipe
open GQ2.Dyadic.SqCore
open GQ2.Roe.Labute

/-- Mod-two independence for a full marking of `DM alpha h`. -/
def MpcModTwoIndep {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) : Prop :=
  ∀ M : OpenNormalSubgroup (DM alpha h), M.toSubgroup.index = 2 →
    ∃ i, m i ∉ M.toSubgroup

/-- Mod-two independence promotes to topological generation. -/
theorem topGen_of_mpcModTwoIndep {alpha h : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : MpcModTwoIndep m) :
    (Subgroup.closure (Set.range m)).topologicalClosure = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_top_of_forall_not_le_index_p (p := 2) (isProP_DM alpha h)
    (Subgroup.isClosed_topologicalClosure _) ?_
  intro M hM hle
  obtain ⟨i, hi⟩ := hm M hM
  exact hi (hle (Subgroup.le_topologicalClosure _
    (Subgroup.subset_closure (Set.mem_range_self i))))

/-- Topological generation implies mod-two independence. -/
theorem mpcModTwoIndep_of_topGen {alpha h : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : (Subgroup.closure (Set.range m)).topologicalClosure = ⊤) :
    MpcModTwoIndep m := by
  intro M hM
  by_contra hall
  push Not at hall
  have hle : Subgroup.closure (Set.range m) ≤ M.toSubgroup := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hall i
  have htop : (Subgroup.closure (Set.range m)).topologicalClosure ≤ M.toSubgroup :=
    Subgroup.topologicalClosure_minimal _ hle M.toOpenSubgroup.isClosed
  rw [hm] at htop
  have hMtop : M.toSubgroup = ⊤ := eq_top_iff.mpr htop
  rw [hMtop, Subgroup.index_top] at hM
  norm_num at hM

/-- The general finite-stage solution space. -/
def mpcGeneralStage (alpha h k : ℕ) :
    Set (Fin (coreRank h) → (DM alpha h : Type)) :=
  {m | MpcModTwoIndep m ∧
    (∀ i, chiM alpha h (m i) = chiM alpha h (dmGen alpha h i)) ∧
    (∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
      toAdd (f (m 2)) =
        toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))) ∧
    mRelWord alpha m ∈ twoCentralSeries (DM alpha h : Type) k}

theorem mpcGeneralStage_antitone {alpha h k k' : ℕ} (hkk : k' ≤ k) :
    mpcGeneralStage alpha h k ⊆ mpcGeneralStage alpha h k' :=
  fun _ ⟨hind, hchi, hrow, hrel⟩ =>
    ⟨hind, hchi, hrow, twoCentralSeries_antitone (G := (DM alpha h : Type)) hkk hrel⟩

private theorem continuous_eval {alpha h : ℕ} (i : Fin (coreRank h)) :
    Continuous fun m : Fin (coreRank h) → (DM alpha h : Type) => m i :=
  continuous_apply i

theorem mpcGeneralStage_isClosed_indep (alpha h : ℕ) :
    IsClosed {m : Fin (coreRank h) → (DM alpha h : Type) | MpcModTwoIndep m} := by
  have hset : {m : Fin (coreRank h) → (DM alpha h : Type) | MpcModTwoIndep m} =
      ⋂ (M : OpenNormalSubgroup (DM alpha h)) (_ : M.toSubgroup.index = 2),
        ⋃ i : Fin (coreRank h),
          {m | m i ∈ ((M.toSubgroup : Set (DM alpha h : Type)))ᶜ} := by
    ext m
    simp only [MpcModTwoIndep, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_compl_iff, SetLike.mem_coe]
  rw [hset]
  refine isClosed_iInter fun M => isClosed_iInter fun _ =>
    isClosed_iUnion_of_finite fun i => ?_
  exact IsClosed.preimage (continuous_eval i) M.isOpen'.isClosed_compl

theorem mpcGeneralStage_isClosed_chi (alpha h : ℕ) : IsClosed
    {m : Fin (coreRank h) → (DM alpha h : Type) |
      ∀ i, chiM alpha h (m i) = chiM alpha h (dmGen alpha h i)} := by
  rw [show {m : Fin (coreRank h) → (DM alpha h : Type) |
      ∀ i, chiM alpha h (m i) = chiM alpha h (dmGen alpha h i)} =
      ⋂ i, {m | chiM alpha h (m i) = chiM alpha h (dmGen alpha h i)} by
        ext m
        simp]
  exact isClosed_iInter fun i => isClosed_eq
    ((chiM alpha h).continuous_toFun.comp (continuous_eval i)) continuous_const

theorem mpcGeneralStage_isClosed_row (alpha h : ℕ) : IsClosed
    {m : Fin (coreRank h) → (DM alpha h : Type) |
      ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
        toAdd (f (m 2)) =
          toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))} := by
  rw [show {m : Fin (coreRank h) → (DM alpha h : Type) |
      ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
        toAdd (f (m 2)) =
          toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))} =
      ⋂ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
        {m | toAdd (f (m 2)) =
          toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))} by
        ext m
        simp]
  exact isClosed_iInter fun f => isClosed_eq
    (continuous_toAdd.comp (f.continuous_toFun.comp (continuous_eval 2))) continuous_const

theorem continuous_mpcGeneralRelator (alpha h : ℕ) :
    Continuous fun m : Fin (coreRank h) → (DM alpha h : Type) => mRelWord alpha m := by
  simp only [mRelWord, mWord, handleWord, commP]
  fun_prop

theorem mpcGeneralStage_isClosed (alpha h k : ℕ) :
    IsClosed (mpcGeneralStage alpha h k) := by
  exact (mpcGeneralStage_isClosed_indep alpha h).inter
    ((mpcGeneralStage_isClosed_chi alpha h).inter
      ((mpcGeneralStage_isClosed_row alpha h).inter
        ((isClosed_twoCentralSeries (G := (DM alpha h : Type)) k).preimage
          (continuous_mpcGeneralRelator alpha h))))

theorem mpcGeneralStage_iInter_nonempty {alpha h : ℕ}
    (hsupply : ∀ k, (mpcGeneralStage alpha h k).Nonempty) :
    (⋂ k, mpcGeneralStage alpha h k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k k'
    exact ⟨max k k', mpcGeneralStage_antitone (le_max_left k k'),
      mpcGeneralStage_antitone (le_max_right k k')⟩
  · exact hsupply
  · exact fun k => (mpcGeneralStage_isClosed alpha h k).isCompact
  · exact mpcGeneralStage_isClosed alpha h

/-- Solvability in every finite quotient gives the actual general shift. -/
theorem mpcPivShiftH_of_finiteStages {alpha h : ℕ}
    (hsupply : ∀ k, (mpcGeneralStage alpha h k).Nonempty) :
    MpcPivShiftH alpha h := by
  obtain ⟨m, hm⟩ := mpcGeneralStage_iInter_nonempty hsupply
  have hmem : ∀ k, m ∈ mpcGeneralStage alpha h k := Set.mem_iInter.mp hm
  obtain ⟨hind, hchi, hrow, -⟩ := hmem 0
  apply mpcPivShiftH_of_marking m
  · have hall : mRelWord alpha m ∈ ⨅ k, twoCentralSeries (DM alpha h : Type) k :=
      Subgroup.mem_iInf.mpr fun k => (hmem k).2.2.2
    rw [iInf_twoCentralSeries (G := (DM alpha h : Type))
      (dm_topologicallyFinGen alpha h) (isProP_DM alpha h), Subgroup.mem_bot] at hall
    exact hall
  · exact topGen_of_mpcModTwoIndep hind
  · exact hchi
  · exact hrow

/-- Every actual shift supplies every finite stage. -/
theorem finiteStages_of_mpcPivShiftH {alpha h : ℕ}
    (hshift : MpcPivShiftH alpha h) :
    ∀ k, (mpcGeneralStage alpha h k).Nonempty := by
  obtain ⟨m, hrel, hgen, hchi, hrow⟩ := marking_of_mpcPivShiftH hshift
  intro k
  exact ⟨m, mpcModTwoIndep_of_topGen hgen, hchi, hrow,
    by rw [hrel]; exact one_mem _⟩

/-- The uniform finite-stage criterion. -/
theorem mpcPivShiftH_iff_finiteStages {alpha h : ℕ} :
    MpcPivShiftH alpha h ↔
      ∀ k, (mpcGeneralStage alpha h k).Nonempty :=
  ⟨finiteStages_of_mpcPivShiftH, mpcPivShiftH_of_finiteStages⟩

/-- The bare universal `C + 2 B` marking. -/
def mpcBareShiftMark (alpha h : ℕ) :
    Fin (coreRank h) → (DM alpha h : Type) :=
  Function.update (dmGen alpha h) 2 (dmB alpha h ^ 2 * dmC alpha h)

@[simp] theorem mpcBareShiftMark_two (alpha h : ℕ) :
    mpcBareShiftMark alpha h 2 = dmB alpha h ^ 2 * dmC alpha h :=
  Function.update_self _ _ _

theorem mpcBareShiftMark_of_ne {alpha h : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 2) :
    mpcBareShiftMark alpha h i = dmGen alpha h i :=
  Function.update_of_ne hi _ _

theorem mpcBareShiftMark_indep (alpha h : ℕ) :
    MpcModTwoIndep (mpcBareShiftMark alpha h) := by
  intro M hM
  by_contra hall
  push Not at hall
  have hgen : ∀ i, dmGen alpha h i ∈ M.toSubgroup := by
    intro i
    by_cases hi : i = 2
    · subst hi
      have hB2 : dmB alpha h ^ 2 ∈ M.toSubgroup := sq_mem_of_index_two hM _
      have hm2 := hall (2 : Fin (coreRank h))
      rw [mpcBareShiftMark_two] at hm2
      have hc := M.toSubgroup.mul_mem (M.toSubgroup.inv_mem hB2) hm2
      change dmC alpha h ∈ M.toSubgroup
      simpa using hc
    · simpa [mpcBareShiftMark_of_ne hi] using hall i
  have hle : Subgroup.closure (Set.range (dmGen alpha h)) ≤ M.toSubgroup := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have htop := Subgroup.topologicalClosure_minimal _ hle M.toOpenSubgroup.isClosed
  rw [dm_topGen, top_le_iff] at htop
  have hMtop : M.toSubgroup = ⊤ := htop
  rw [hMtop, Subgroup.index_top] at hM
  norm_num at hM

theorem mpcBareShiftMark_chi (alpha h : ℕ) (i : Fin (coreRank h)) :
    chiM alpha h (mpcBareShiftMark alpha h i) = chiM alpha h (dmGen alpha h i) := by
  by_cases hi : i = 2
  · subst hi
    rw [mpcBareShiftMark_two, map_mul, map_pow]
    change chiM alpha h (dmB alpha h) ^ 2 * chiM alpha h (dmC alpha h) =
      chiM alpha h (dmC alpha h)
    rw [chiM_dmB, chiM_dmC]
    norm_num
  · rw [mpcBareShiftMark_of_ne hi]

theorem mpcBareShiftMark_row (alpha h : ℕ)
    (f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])) :
    toAdd (f (mpcBareShiftMark alpha h 2)) =
      toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h)) := by
  rw [mpcBareShiftMark_two, map_mul, map_pow, toAdd_mul, toAdd_pow]
  ring

/-- The finite-stage ladder has an unconditional depth-zero seed for all parameters. -/
theorem mpcGeneralStage_zero_nonempty (alpha h : ℕ) :
    (mpcGeneralStage alpha h 0).Nonempty := by
  refine ⟨mpcBareShiftMark alpha h, mpcBareShiftMark_indep alpha h,
    mpcBareShiftMark_chi alpha h, mpcBareShiftMark_row alpha h, ?_⟩
  rw [twoCentralSeries_zero]
  exact Subgroup.mem_top _

/-- Every marking has relator in `lambda_2`; hence the bare shift gives a uniform depth-two
seed as soon as `alpha` is positive. -/
theorem mpcGeneralStage_two_nonempty {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    (mpcGeneralStage alpha h 2).Nonempty := by
  refine ⟨mpcBareShiftMark alpha h, mpcBareShiftMark_indep alpha h,
    mpcBareShiftMark_chi alpha h, mpcBareShiftMark_row alpha h, ?_⟩
  exact GQ2.Dyadic.StageGeneric.evenTransgression.mRelWord_mem_twoCentralSeries_two
    (DM alpha h : Type) halpha (mpcBareShiftMark alpha h)

/-- The bare shift already kills the relator through `lambda_3`, uniformly in the degree and
the handle count.  In the class-two quotient the inserted `B^2` is a central involution, so
the general even relator is unchanged. -/
theorem mpcBareShiftMark_rel_three {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    mRelWord alpha (mpcBareShiftMark alpha h) ∈
      twoCentralSeries (DM alpha h : Type) 3 := by
  apply (QuotientGroup.eq_one_iff _).mp
  change levelMk (DM alpha h) 3 (mRelWord alpha (mpcBareShiftMark alpha h)) = 1
  rw [map_mRelWord]
  let base : Fin (coreRank h) → levelQuot (DM alpha h) 3 :=
    fun i => levelMk (DM alpha h) 3 (dmGen alpha h i)
  let z : levelQuot (DM alpha h) 3 := (levelMk (DM alpha h) 3 (dmB alpha h)) ^ 2
  let offset : Fin (coreRank h) → levelQuot (DM alpha h) 3 :=
    Function.update (fun _ => 1) 2 z
  have hz : z ∈ zLayer (DM alpha h) 2 := sq_mem_zLayer_two _
  have hoff_comm : ∀ i g, Commute (offset i) g := by
    intro i g
    by_cases hi : i = 2
    · subst hi
      simp only [offset, Function.update_self]
      exact zLayer_commute hz g
    · simp only [offset, Function.update_of_ne hi]
      exact Commute.one_left g
  have hoff_sq : ∀ i, offset i ^ 2 = 1 := by
    intro i
    by_cases hi : i = 2
    · subst hi
      simp only [offset, Function.update_self]
      exact zLayer_sq _ hz
    · simp only [offset, Function.update_of_ne hi, one_pow]
  have hmark :
      (fun i => levelMk (DM alpha h) 3 (mpcBareShiftMark alpha h i)) =
        fun i => base i * offset i := by
    funext i
    by_cases hi : i = 2
    · subst hi
      simp only [mpcBareShiftMark_two, map_mul, map_pow, base, offset,
        Function.update_self, z]
      rw [show dmGen alpha h 2 = dmC alpha h from rfl]
      exact (zLayer_commute hz _).eq
    · simp only [mpcBareShiftMark_of_ne hi, base, offset,
        Function.update_of_ne hi, mul_one]
  rw [hmark,
    GQ2.Dyadic.StageGeneric.evenTransgression.mRelWord_mul_central
      halpha base offset hoff_comm hoff_sq]
  change mRelWord alpha base = 1
  simp only [base]
  rw [← map_mRelWord, dm_relation, map_one]

/-- The uniform finite-stage ladder therefore has a level-three seed, the natural starting
point of the graded successor calculus. -/
theorem mpcGeneralStage_three_nonempty {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    (mpcGeneralStage alpha h 3).Nonempty :=
  ⟨mpcBareShiftMark alpha h, mpcBareShiftMark_indep alpha h,
    mpcBareShiftMark_chi alpha h, mpcBareShiftMark_row alpha h,
    mpcBareShiftMark_rel_three halpha⟩

/-- The single uniform successor statement whose proof settles every handle count. -/
def MpcGeneralStageSuccessorSupply (alpha h : ℕ) : Prop :=
  ∀ k, 3 ≤ k → (mpcGeneralStage alpha h k).Nonempty →
    (mpcGeneralStage alpha h (k + 1)).Nonempty

/-! ## The uniform simultaneous-correction boundary -/

/-- The second two-central subgroup lies in every open normal subgroup of index two. -/
theorem twoCentralSeries_two_le_openNormal_index_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : OpenNormalSubgroup G) (hM : M.toSubgroup.index = 2) :
    twoCentralSeries G 2 ≤ M.toSubgroup := by
  rw [twoCentralSeries_succ G (by omega), twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) M.toOpenSubgroup.isClosed
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, -, rfl⟩
    exact sq_mem_of_index_two hM x
  · rw [Subgroup.commutator_le]
    intro x _ y _
    have hxy := commP_mem_of_index_two hM x⁻¹ y⁻¹
    simpa only [commP, inv_inv, commutatorElement_def] using hxy

/-- Coordinatewise multiplication by a simultaneous correction. -/
def mpcGeneralModify {alpha h : ℕ}
    (m e : Fin (coreRank h) → (DM alpha h : Type)) :
    Fin (coreRank h) → (DM alpha h : Type) :=
  fun i => m i * e i

/-- A simultaneous correction at stage `k`.  The factors are deep and orientation-neutral;
the `C` factor is invisible to every `Z_2`-valued character, which preserves the universal
`C + 2 B` row.  The sole nonlinear clause is the next relator depth. -/
structure MpcGeneralStageCorrection {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) where
  factors : Fin (coreRank h) → (DM alpha h : Type)
  depth : ∀ i, factors i ∈ twoCentralSeries (DM alpha h : Type) (k - 1)
  chi : ∀ i, chiM alpha h (factors i) = 1
  row : ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
    f (factors 2) = 1
  nextRel : mRelWord alpha (mpcGeneralModify m factors) ∈
    twoCentralSeries (DM alpha h : Type) (k + 1)

/-- A deep simultaneous correction preserves mod-two independence. -/
theorem mpcModTwoIndep_modify {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : MpcModTwoIndep m) (E : MpcGeneralStageCorrection m k) (hk : 3 ≤ k) :
    MpcModTwoIndep (mpcGeneralModify m E.factors) := by
  intro M hM
  obtain ⟨i, hi⟩ := hm M hM
  refine ⟨i, ?_⟩
  intro hmod
  have hdepth : E.factors i ∈ twoCentralSeries (DM alpha h : Type) 2 :=
    twoCentralSeries_antitone (G := (DM alpha h : Type)) (by omega) (E.depth i)
  have hfactor : E.factors i ∈ M.toSubgroup :=
    twoCentralSeries_two_le_openNormal_index_two M hM hdepth
  apply hi
  have heq : m i = mpcGeneralModify m E.factors i * (E.factors i)⁻¹ := by
    simp only [mpcGeneralModify]
    group
  rw [heq]
  exact M.toSubgroup.mul_mem hmod (M.toSubgroup.inv_mem hfactor)

/-- A simultaneous correction advances one general stage. -/
theorem mpcGeneralStage_succ_of_correction {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k)
    (E : MpcGeneralStageCorrection m k) (hk : 3 ≤ k) :
    mpcGeneralModify m E.factors ∈ mpcGeneralStage alpha h (k + 1) := by
  rcases hm with ⟨hind, hchi, hrow, -⟩
  refine ⟨mpcModTwoIndep_modify hind E hk, ?_, ?_, E.nextRel⟩
  · intro i
    simp only [mpcGeneralModify, map_mul, E.chi, mul_one]
    exact hchi i
  · intro f
    simp only [mpcGeneralModify, map_mul, toAdd_mul, E.row, toAdd_one, add_zero]
    exact hrow f

/-- The exact general all-degree boundary: every stage admits a simultaneous constrained
correction.  Unlike the refuted coordinatewise-neutral interface, this lets the rows cancel
jointly and is parameterized by arbitrary `alpha`, `h`, and `k`. -/
def MpcGeneralCorrectionSupply (alpha h : ℕ) : Prop :=
  ∀ k, 3 ≤ k → ∀ m ∈ mpcGeneralStage alpha h k,
    Nonempty (MpcGeneralStageCorrection m k)

/-- Simultaneous constrained correction supply implies the stage successor. -/
theorem mpcGeneralStageSuccessor_of_corrections {alpha h : ℕ}
    (H : MpcGeneralCorrectionSupply alpha h) :
    MpcGeneralStageSuccessorSupply alpha h := by
  intro k hk hstage
  obtain ⟨m, hm⟩ := hstage
  obtain ⟨E⟩ := H k hk m hm
  exact ⟨mpcGeneralModify m E.factors,
    mpcGeneralStage_succ_of_correction hm E hk⟩

theorem mpcGeneralStage_nonempty_all {alpha h : ℕ}
    (halpha : 1 ≤ alpha) (hsucc : MpcGeneralStageSuccessorSupply alpha h) :
    ∀ k, (mpcGeneralStage alpha h k).Nonempty := by
  intro k
  by_cases hk : k ≤ 3
  · exact (mpcGeneralStage_three_nonempty halpha).mono
      (mpcGeneralStage_antitone hk)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ k by omega)
    clear hk
    induction d with
    | zero => simpa using mpcGeneralStage_three_nonempty halpha
    | succ d ih =>
      simpa [Nat.add_assoc] using hsucc (3 + d) (by omega) ih

theorem mpcPivShiftH_of_generalStageSuccessor {alpha h : ℕ}
    (halpha : 1 ≤ alpha) (hsucc : MpcGeneralStageSuccessorSupply alpha h) :
    MpcPivShiftH alpha h :=
  mpcPivShiftH_of_finiteStages (mpcGeneralStage_nonempty_all halpha hsucc)

#print axioms MpcModTwoIndep
#print axioms topGen_of_mpcModTwoIndep
#print axioms mpcModTwoIndep_of_topGen
#print axioms mpcGeneralStage
#print axioms mpcGeneralStage_isClosed
#print axioms mpcPivShiftH_iff_finiteStages
#print axioms mpcGeneralStage_zero_nonempty
#print axioms mpcGeneralStage_two_nonempty
#print axioms mpcBareShiftMark_rel_three
#print axioms mpcGeneralStage_three_nonempty
#print axioms MpcGeneralStageSuccessorSupply
#print axioms twoCentralSeries_two_le_openNormal_index_two
#print axioms mpcGeneralModify
#print axioms MpcGeneralStageCorrection
#print axioms mpcGeneralStage_succ_of_correction
#print axioms MpcGeneralCorrectionSupply
#print axioms mpcGeneralStageSuccessor_of_corrections
#print axioms mpcPivShiftH_of_generalStageSuccessor

end
end GQ2.Dyadic.Instances.MpcGeneralFiniteStages
