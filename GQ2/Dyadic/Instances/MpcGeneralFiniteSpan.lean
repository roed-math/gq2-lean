import GQ2.Dyadic.Instances.MpcGeneralFiniteStages
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan
import GQ2.Dyadic.SqCore.GradedLimit

/-!
# The general Mpc successor as one finite graded range problem

For arbitrary `alpha`, handle count `h`, stage `k`, and current marking, this module packages
all simultaneous depth-`k-1` corrections into one finite group.  Every coordinate is
`chiM`-neutral, and the `C` coordinate is additionally invisible to every continuous
`Z_2`-valued character.  The existing even first-variation formula makes the induced relator
shift a homomorphism into the central graded layer.

The main equivalence says that a group-level correction exists exactly when the inverse
current relator belongs to this homomorphism's range.  Thus the whole general pivot campaign
is reduced to one parameterized finite-range theorem; no nilpotency class is singled out.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralFiniteSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Roe.Labute

/-- The exact orientation-neutral subgroup. -/
def mpcGeneralChiKer (alpha h : ℕ) : Subgroup (DM alpha h : Type) :=
  (chiM alpha h).toMonoidHom.ker

/-- Elements invisible to every continuous `Z_2`-valued character. -/
def mpcGeneralRowKer (alpha h : ℕ) : Subgroup (DM alpha h : Type) where
  carrier := {x | ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
    f x = 1}
  one_mem' _ := map_one _
  mul_mem' hx hy f := by rw [map_mul, hx f, hy f, mul_one]
  inv_mem' hx f := by rw [map_inv, hx f, inv_one]

theorem mem_mpcGeneralRowKer_iff {alpha h : ℕ} {x : DM alpha h} :
    x ∈ mpcGeneralRowKer alpha h ↔
      ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
        f x = 1 :=
  Iff.rfl

/-- The exact group-level source allowed in coordinate `i`.  Only coordinate `2` carries the
extra abelian-neutral condition. -/
def mpcGeneralCorrectionSource (alpha h j : ℕ) (i : Fin (coreRank h)) :
    Subgroup (DM alpha h : Type) :=
  if i = 2 then
    (twoCentralSeries (DM alpha h : Type) j ⊓ mpcGeneralChiKer alpha h) ⊓
      mpcGeneralRowKer alpha h
  else
    twoCentralSeries (DM alpha h : Type) j ⊓ mpcGeneralChiKer alpha h

/-- The exact image of one allowed coordinate in a finite two-central quotient. -/
def mpcGeneralCorrectionImage (alpha h j n : ℕ) (i : Fin (coreRank h)) :
    Subgroup (levelQuot (DM alpha h) n) :=
  (mpcGeneralCorrectionSource alpha h j i).map (levelMk (DM alpha h) n)

theorem mem_mpcGeneralCorrectionImage_iff_exists_exact
    {alpha h j n : ℕ} {i : Fin (coreRank h)} (x : levelQuot (DM alpha h) n) :
    x ∈ mpcGeneralCorrectionImage alpha h j n i ↔
      ∃ e : DM alpha h,
        e ∈ twoCentralSeries (DM alpha h : Type) j ∧
        chiM alpha h e = 1 ∧
        (i = 2 → ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
          f e = 1) ∧
        levelMk (DM alpha h) n e = x := by
  constructor
  · rintro ⟨e, he, rfl⟩
    by_cases hi : i = 2
    · rw [mpcGeneralCorrectionSource, if_pos hi] at he
      exact ⟨e, he.1.1, MonoidHom.mem_ker.mp he.1.2, fun _ => he.2, rfl⟩
    · rw [mpcGeneralCorrectionSource, if_neg hi] at he
      exact ⟨e, he.1, MonoidHom.mem_ker.mp he.2, fun h => (hi h).elim, rfl⟩
  · rintro ⟨e, he, hchi, hrow, rfl⟩
    refine ⟨e, ?_, rfl⟩
    by_cases hi : i = 2
    · rw [mpcGeneralCorrectionSource, if_pos hi]
      exact ⟨⟨he, MonoidHom.mem_ker.mpr hchi⟩,
        (mem_mpcGeneralRowKer_iff.mpr (hrow hi))⟩
    · rw [mpcGeneralCorrectionSource, if_neg hi]
      exact ⟨he, MonoidHom.mem_ker.mpr hchi⟩

/-- All coordinate choices at the finite stage. -/
abbrev MpcGeneralLevelCorrection (alpha h k : ℕ) :=
  ∀ i : Fin (coreRank h), mpcGeneralCorrectionImage alpha h (k - 1) (k + 1) i

noncomputable instance mpcGeneralLevelCorrection_finite (alpha h k : ℕ) :
    Finite (MpcGeneralLevelCorrection alpha h k) := by
  letI : Finite (levelQuot (DM alpha h) (k + 1)) :=
    finite_levelQuot (DM alpha h) (dmFinsetTopGen alpha h) (isProP_DM alpha h) (k + 1)
  infer_instance

/-- The underlying correction marking in the finite quotient. -/
def mpcGeneralLevelCorrectionMark {alpha h k : ℕ}
    (E : MpcGeneralLevelCorrection alpha h k) :
    Fin (coreRank h) → levelQuot (DM alpha h) (k + 1) :=
  fun i => (E i).1

theorem mpcGeneralCorrectionImage_le_lambdaImage
    (alpha h j n : ℕ) (i : Fin (coreRank h)) :
    mpcGeneralCorrectionImage alpha h j n i ≤ lambdaImage (DM alpha h) j n := by
  rintro x ⟨e, he, rfl⟩
  by_cases hi : i = 2
  · rw [mpcGeneralCorrectionSource, if_pos hi] at he
    exact ⟨e, he.1.1, rfl⟩
  · rw [mpcGeneralCorrectionSource, if_neg hi] at he
    exact ⟨e, he.1, rfl⟩

/-- Forget the exact row constraints and retain a raw even depth correction. -/
def mpcGeneralLevelToRaw {alpha h k : ℕ}
    (E : MpcGeneralLevelCorrection alpha h k) :
    EvenRawDepthCorrection (DM alpha h) h k where
  correction := mpcGeneralLevelCorrectionMark E
  depth i := mpcGeneralCorrectionImage_le_lambdaImage alpha h (k - 1) (k + 1) i (E i).2

/-- The forgetful map is a group homomorphism. -/
noncomputable def mpcGeneralLevelToRawHom (alpha h k : ℕ) :
    MpcGeneralLevelCorrection alpha h k →*
      EvenRawDepthCorrection (DM alpha h) h k where
  toFun := mpcGeneralLevelToRaw
  map_one' := by
    apply EvenRawDepthCorrection.ext
    rfl
  map_mul' _ _ := by
    apply EvenRawDepthCorrection.ext
    rfl

/-- The finite shift homomorphism for an arbitrary current marking. -/
noncomputable def mpcGeneralLevelShiftHom {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) (hk : 3 ≤ k) :
    MpcGeneralLevelCorrection alpha h k →* zLayer (DM alpha h) k :=
  (evenRawDepthShiftHom
    (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk).comp
      (mpcGeneralLevelToRawHom alpha h k)

/-- The shift homomorphism is the literal general relator shift. -/
theorem mpcGeneralLevelShiftHom_apply {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) (hk : 3 ≤ k)
    (E : MpcGeneralLevelCorrection alpha h k) :
    (mpcGeneralLevelShiftHom m k hk E).1 =
      stageShift (mStageWord alpha h (by omega))
        (fun i => levelMk (DM alpha h) (k + 1) (m i))
        (mpcGeneralLevelCorrectionMark E) := by
  change evenRawDbarWord
      (fun i => levelMk (DM alpha h) (k + 1) (m i))
      (mpcGeneralLevelCorrectionMark E) = _
  symm
  exact evenRawStageShift_m (G := DM alpha h) halpha (by omega) h k hk _ _
    (mpcGeneralLevelToRaw E).depth

/-- The inverse current relator as an element of the current central layer. -/
def mpcGeneralLevelTarget {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k) : zLayer (DM alpha h) k :=
  ⟨(levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹,
    ⟨(mRelWord alpha m)⁻¹, Subgroup.inv_mem _ hm.2.2.2, by rw [map_inv]⟩⟩

/-! ## Exact representatives and the range equivalence -/

/-- The literal stage shift written as the quotient of the modified and original relators. -/
theorem mpcGeneralStageShift_eq {alpha h : ℕ}
    (halpha : 1 ≤ alpha) (m e : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) :
    stageShift (mStageWord alpha h halpha)
        (fun i => levelMk (DM alpha h) (k + 1) (m i))
        (fun i => levelMk (DM alpha h) (k + 1) (e i)) =
      (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ *
        levelMk (DM alpha h) (k + 1) (mRelWord alpha (mpcGeneralModify m e)) := by
  have hmark :
      (fun i => levelMk (DM alpha h) (k + 1) (m i) *
        levelMk (DM alpha h) (k + 1) (e i)) =
      fun i => levelMk (DM alpha h) (k + 1) (mpcGeneralModify m e i) := by
    funext i
    rw [mpcGeneralModify, map_mul]
  rw [stageShift]
  change
    (mRelWord alpha (fun i => levelMk (DM alpha h) (k + 1) (m i)))⁻¹ *
      mRelWord alpha (fun i =>
        levelMk (DM alpha h) (k + 1) (m i) *
          levelMk (DM alpha h) (k + 1) (e i)) = _
  rw [hmark, ← map_mRelWord, ← map_mRelWord]

/-- Send a group-level constrained correction to its finite coordinate tuple. -/
def mpcGeneralCorrectionToLevel {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (E : MpcGeneralStageCorrection m k) : MpcGeneralLevelCorrection alpha h k :=
  fun i => ⟨levelMk (DM alpha h) (k + 1) (E.factors i),
    (mem_mpcGeneralCorrectionImage_iff_exists_exact _).mpr
      ⟨E.factors i, E.depth i, E.chi i, fun hi => by
        subst hi
        exact E.row, rfl⟩⟩

@[simp] theorem mpcGeneralCorrectionToLevel_apply {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
  (E : MpcGeneralStageCorrection m k) (i : Fin (coreRank h)) :
    mpcGeneralLevelCorrectionMark (mpcGeneralCorrectionToLevel E) i =
      levelMk (DM alpha h) (k + 1) (E.factors i) :=
  rfl

/-- A group-level correction hits the finite target. -/
theorem mpcGeneralCorrection_target_mem_range {alpha h k : ℕ}
    (halpha : 2 ≤ alpha) {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k)
    (E : MpcGeneralStageCorrection m k) :
    mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range := by
  refine ⟨mpcGeneralCorrectionToLevel E, Subtype.ext ?_⟩
  rw [mpcGeneralLevelShiftHom_apply halpha]
  change stageShift (mStageWord alpha h (by omega))
      (fun i => levelMk (DM alpha h) (k + 1) (m i))
      (fun i => levelMk (DM alpha h) (k + 1) (E.factors i)) = _
  rw [mpcGeneralStageShift_eq (by omega)]
  have hnext : levelMk (DM alpha h) (k + 1)
      (mRelWord alpha (mpcGeneralModify m E.factors)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr E.nextRel
  change (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ *
      levelMk (DM alpha h) (k + 1)
        (mRelWord alpha (mpcGeneralModify m E.factors)) =
    (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹
  rw [hnext, mul_one]

/-- Conversely, a finite range witness has exact representatives and therefore gives a
group-level simultaneous correction. -/
theorem nonempty_mpcGeneralCorrection_of_target_mem_range {alpha h k : ℕ}
    (halpha : 2 ≤ alpha) {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k)
    (H : mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range) :
    Nonempty (MpcGeneralStageCorrection m k) := by
  obtain ⟨E, hE⟩ := H
  have hex : ∀ i : Fin (coreRank h),
      ∃ e : DM alpha h,
        e ∈ twoCentralSeries (DM alpha h : Type) (k - 1) ∧
        chiM alpha h e = 1 ∧
        (i = 2 → ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
          f e = 1) ∧
        levelMk (DM alpha h) (k + 1) e = (E i).1 :=
    fun i => (mem_mpcGeneralCorrectionImage_iff_exists_exact (E i).1).mp (E i).2
  choose e hdepth hchi hrow hlevel using hex
  refine ⟨{
    factors := e
    depth := hdepth
    chi := hchi
    row := ?_
    nextRel := ?_ }⟩
  · intro f
    exact hrow 2 rfl f
  · apply (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mpr
    have hmark : mpcGeneralLevelCorrectionMark E =
        fun i => levelMk (DM alpha h) (k + 1) (e i) := by
      funext i
      exact (hlevel i).symm
    have hshift := congrArg Subtype.val hE
    rw [mpcGeneralLevelShiftHom_apply halpha] at hshift
    rw [hmark, mpcGeneralStageShift_eq (by omega)] at hshift
    change (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ *
        levelMk (DM alpha h) (k + 1)
          (mRelWord alpha (mpcGeneralModify m e)) =
      (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ at hshift
    apply mul_left_cancel
      (a := (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹)
    simpa only [mul_one] using hshift

/-- Exact finite criterion for one general correction. -/
theorem nonempty_mpcGeneralCorrection_iff_target_mem_range {alpha h k : ℕ}
    (halpha : 2 ≤ alpha) {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    Nonempty (MpcGeneralStageCorrection m k) ↔
      mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range :=
  ⟨fun ⟨E⟩ => mpcGeneralCorrection_target_mem_range halpha hm hk E,
    nonempty_mpcGeneralCorrection_of_target_mem_range halpha hm hk⟩

/-- The sole uniform finite-range statement left by the reduction. -/
def MpcGeneralFiniteRangeSupply (alpha h : ℕ) : Prop :=
  ∀ k (hk : 3 ≤ k) m (hm : m ∈ mpcGeneralStage alpha h k),
    mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range

/-- The finite-range statement is exactly the simultaneous correction supply. -/
theorem mpcGeneralFiniteRangeSupply_iff_correctionSupply {alpha h : ℕ}
    (halpha : 2 ≤ alpha) :
    MpcGeneralFiniteRangeSupply alpha h ↔ MpcGeneralCorrectionSupply alpha h := by
  constructor
  · intro H k hk m hm
    exact (nonempty_mpcGeneralCorrection_iff_target_mem_range halpha hm hk).mpr
      (H k hk m hm)
  · intro H k hk m hm
    exact (nonempty_mpcGeneralCorrection_iff_target_mem_range halpha hm hk).mp
      (H k hk m hm)

/-- One parameterized finite-range theorem proves the pivot shift at every requested degree
and handle count. -/
theorem mpcPivShiftH_of_generalFiniteRange {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralFiniteRangeSupply alpha h) : MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalStageSuccessor (by omega)
    (mpcGeneralStageSuccessor_of_corrections
      ((mpcGeneralFiniteRangeSupply_iff_correctionSupply halpha).mp H))

#print axioms mpcGeneralChiKer
#print axioms mpcGeneralRowKer
#print axioms mpcGeneralCorrectionImage
#print axioms MpcGeneralLevelCorrection
#print axioms mpcGeneralLevelShiftHom
#print axioms mpcGeneralLevelShiftHom_apply
#print axioms mpcGeneralLevelTarget
#print axioms nonempty_mpcGeneralCorrection_iff_target_mem_range
#print axioms MpcGeneralFiniteRangeSupply
#print axioms mpcGeneralFiniteRangeSupply_iff_correctionSupply
#print axioms mpcPivShiftH_of_generalFiniteRange

end
end GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
