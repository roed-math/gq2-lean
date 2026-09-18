import GQ2.Dyadic.MarkedCore.MBasisRowRefinement
import GQ2.Dyadic.MarkedCore.NPlaneAmbientStage

/-!
# Unrestricted actual free-M stages in arbitrary rank

The M twin of `NPlaneAmbientStage`. The all-rank even derivation criterion is
applied on the free pro-two group with the dummy constant-one `StageWord`
`NPlaneAmbientStage.oneWord`; that word only packages the tuple container. The
class tested by the criterion is the actual free-basis target-relative M
defect `mRelWord alpha (e gen) * (mRelWord alpha gen)⁻¹`, whose target is the
literal M relator word of the standard free basis. The coordinate crossed maps
are the committed `evenFamDerivModelM` models pulled back along the free
projection to `DM`, and both actual M words die separately under every such
map because the M relator is universally closed at the `vM` table. No relator
death is imposed on the free tuple itself.

The ambient theorem supplies arbitrary depth corrections improving the actual
M defect by one level; it does not claim that they preserve orientation or
ordinary rows. The composition with the closed derivative-kernel interpolation
is the interface stated at the end: it is proved from the head-cleanup
statement of the coupled M ordinary head row, which is named as a `Prop` and
is not proved in this file.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute FoxH StageGeneric EvenFamily
open GQ2.Dyadic.LSquare (IsChiShadowDeriv)

/-! ## The free projection and the pulled-back canonical M orientation -/

/-- The canonical projection of the free pro-two group of rank `coreRank h`
onto the actual `D_M`, generator to generator. -/
def mBasisProjection (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (DM α h : Type) :=
  presLiftHom 1 (isProP_DM α h) (dmGen α h) (map_one _)

theorem mBasisProjection_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mBasisProjection α h (freeTwoRankGen (coreRank h) i) = dmGen α h i :=
  presLiftHom_gen _ _ _ _ _

/-- The free M orientation: the actual canonical `chiM` pulled back along the
free projection. Its generator values are the `vM` table. -/
def mBasisOrientation (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) ℤ_[2]ˣ :=
  (chiM α h).comp (mBasisProjection α h)

theorem mBasisProjection_orientation (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    chiM α h (mBasisProjection α h x) = mBasisOrientation α h x := rfl

theorem mBasisOrientation_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mBasisOrientation α h (freeTwoRankGen (coreRank h) i) = vM α i := by
  change chiM α h (mBasisProjection α h (freeTwoRankGen (coreRank h) i)) = _
  rw [mBasisProjection_gen, evenFam_chiM_dmGen]

theorem mBasisOrientation_aut {α h : ℕ}
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i))
    (z : FreeTwoRank (coreRank h)) :
    mBasisOrientation α h (e z) = mBasisOrientation α h z := by
  have H : (mBasisOrientation α h).comp (autHom e) = mBasisOrientation α h := by
    apply presPro2_hom_ext
    exact he
  exact DFunLike.congr_fun H z

/-- An element with every ordinary coordinate zero has trivial free M
orientation: the orientation is a commutative pro-two character. -/
theorem mBasisOrientation_eq_one_of_coordinates {α h : ℕ} (x : FreeTwoRank (coreRank h))
    (hx : ∀ j, freeTwoCoordinate (coreRank h) j x = 1) :
    mBasisOrientation α h x = 1 := by
  rw [freeTwo_commutative_hom_coordinates isProP_two_unitsPadicInt (coreRank h)
    (mBasisOrientation α h) x]
  apply Finset.prod_eq_one
  intro i _
  rw [hx i, toAdd_one, zpowZtwo_zero_exp]

/-! ## The coordinate crossed maps on an arbitrary free basis -/

def mBasisCoordinateDeriv {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (i : Fin (coreRank h)) : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (WL N) :=
  ((evenFamDerivModelM α h hα hN (fun j => if j=i then 1 else 0)).comp
    (mBasisProjection α h)).comp (autHom e.symm)

theorem mBasisCoordinateDeriv_gen {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) (i j : Fin (coreRank h)) :
    mBasisCoordinateDeriv hα N hN e i (e (freeTwoRankGen (coreRank h) j)) =
      redWL N ⟨if j=i then 1 else 0, vM α j⟩ := by
  change evenFamDerivModelM α h hα hN _ (mBasisProjection α h (e.symm (e _))) = _
  rw [e.symm_apply_apply, mBasisProjection_gen, evenFamDerivModelM_gen]

theorem mBasisCoordinateDeriv_base {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i))
    (i : Fin (coreRank h)) : IsChiShadowDeriv (mBasisOrientation α h)
      (mBasisCoordinateDeriv hα N hN e i) := by
  intro z
  change (evenFamDerivModelM α h hα hN _ (mBasisProjection α h (e.symm z))).g = _
  rw [evenFamDerivModelM_isChiShadow, mBasisProjection_orientation]
  have H := mBasisOrientation_aut e he (e.symm z)
  rw [e.apply_symm_apply] at H
  rw [← H]

/-- Any finite-level marking whose base component is the `vM` table kills the
actual M relator: the M relator is universally closed at that table. -/
theorem mBasis_finite_mRelWord_eq_one {α h N : ℕ} (hα : 1 ≤ α)
    (m : Fin (coreRank h) → WL N)
    (hm : ∀ i, (m i).g = Units.map (PadicInt.toZModPow N).toMonoidHom (vM α i)) :
    mRelWord α m = 1 := by
  let c : Fin (coreRank h) → ℤ_[2] := fun i => ((m i).u.val : ℤ_[2])
  have H : m = fun i => redWL N ⟨c i, vM α i⟩ := by
    funext i
    apply WordLift.ext
    · change (m i).u = PadicInt.toZModPow N ((m i).u.val : ℤ_[2])
      simp
    · exact hm i
  rw [H, ← map_mRelWord, evenFam_mRelWord_wordLift α hα, map_one]

/-- Both actual M words die separately under each coordinate crossed map, so
the free-basis target-relative defect is in every derivative kernel. -/
theorem mBasisCoordinateDeriv_defect {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i))
    (i : Fin (coreRank h)) :
    mBasisCoordinateDeriv hα N hN e i
      (mRelWord α (fun j => e (freeTwoRankGen (coreRank h) j)) *
        (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹) = 1 := by
  rw [map_mul, map_inv, map_mRelWord, map_mRelWord]
  have H (y : Fin (coreRank h) → FreeTwoRank (coreRank h))
      (hy : ∀ j, mBasisOrientation α h (y j) = vM α j) :
      mRelWord α (fun j => mBasisCoordinateDeriv hα N hN e i (y j)) = 1 := by
    apply mBasis_finite_mRelWord_eq_one hα
    intro j
    rw [mBasisCoordinateDeriv_base hα N hN e he i, hy]
  rw [H _ (fun j => (he j).trans (mBasisOrientation_gen α h j)),
    H _ (mBasisOrientation_gen α h), inv_one, mul_one]

/-! ## The tuple, the derivation family and the raw-span membership -/

def mBasisTuple {α h : ℕ} (k : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i)) :
    Tuple (NPlaneAmbientStage.oneWord (coreRank h)) (vM α) (FreeTwoRank (coreRank h) : Type)
      (mBasisOrientation α h) k where
  generators i := levelMk _ k (e (freeTwoRankGen (coreRank h) i))
  rows i := ⟨e (freeTwoRankGen (coreRank h) i),
    (he i).trans (mBasisOrientation_gen α h i), rfl⟩
  relation := rfl
  topGen := NPlaneAmbientStage.basis_generates e k

def mBasisFamily {α h : ℕ} (hα : 1 ≤ α) (k : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i)) :
    EvenKernelDerivationFamily (mBasisTuple k e he) where
  lifts i := e (freeTwoRankGen (coreRank h) i)
  lifts_chi i := (he i).trans (mBasisOrientation_gen α h i)
  lifts_level _ := rfl
  deriv i _ := mBasisCoordinateDeriv hα (k+1) (by omega) e i
  deriv_base i _ := mBasisCoordinateDeriv_base hα (k+1) (by omega) e he i
  deriv_diag i _ := by
    rw [mBasisCoordinateDeriv_gen]
    change ¬ (2 : ZMod (2^(k+1))) ∣ PadicInt.toZModPow (k+1) (if i=i then 1 else 0)
    simp only [ite_true, map_one]
    rw [evenFam_two_dvd_iff_castHom_eq_zero (by omega), map_one]
    exact one_ne_zero
  deriv_off i _ j _ hj := by
    rw [mBasisCoordinateDeriv_gen]
    change (2 : ZMod (2^(k+1))) ∣ PadicInt.toZModPow (k+1) (if j=i then 1 else 0)
    simp [hj]

/-- The actual free-basis target-relative M defect lies in the raw shift span
whenever it lies in `lambda_k`; the crossed models are the M table models. -/
theorem mBasis_defect_mem_rawSpan {α h k : ℕ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i))
    (herr : mRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) k) :
    levelMk (FreeTwoRank (coreRank h) : Type) (k+1)
      (mRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
        (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹) ∈
      evenRawShiftSpan (fun i => canonLift _ k ((mBasisTuple k e he).generators i)) hk := by
  apply evenDeriv_mem_rawShiftSpan_of_forall_derivKer (NPlaneAmbientStage.free_finite_gen _)
    (isProP_presPro2 1) hk (mBasisFamily (by omega) k e he)
    (fun i hi => evenKernel_vM_sub_one_dvd_four hα i hi)
    evenKernel_vM_diagonal_add_one_dvd_four
  · exact ⟨_, herr, rfl⟩
  · intro i hi
    refine ⟨_, herr, rfl, ?_⟩
    change (2 : ZMod (2^(k+1))) ^ k ∣
      (mBasisCoordinateDeriv (by omega) (k+1) (by omega) e i _).u
    rw [mBasisCoordinateDeriv_defect (by omega) (k+1) (by omega) e he i]
    exact dvd_zero _

/-- **The M ambient stage.** An orientation-compatible free basis whose actual
target-relative M defect lies in `lambda_k` admits a depth-`(k-1)` correction
whose defect lies in `lambda_(k+1)`. Nothing is claimed about the rows or the
orientation of the correction. -/
theorem mBasis_exists_ambient_stage {α h k : ℕ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, mBasisOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation α h (freeTwoRankGen (coreRank h) i))
    (herr : mRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) k) :
    ∃ t : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (k-1)) ∧
      mRelWord α (fun i => e (freeTwoRankGen (coreRank h) i) * t i) *
        (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (k+1) := by
  let f := levelMk (FreeTwoRank (coreRank h) : Type) (k+1)
  let y := fun i => e (freeTwoRankGen (coreRank h) i)
  let x := freeTwoRankGen (coreRank h)
  have H := (evenRawShiftSpan _ hk).inv_mem (mBasis_defect_mem_rawSpan hα hk e he herr)
  obtain ⟨z, ⟨V, hV⟩, hz⟩ := H
  subst z
  change evenRawDbarWord (fun i => canonLift _ k ((mBasisTuple k e he).generators i))
    V.correction = (f (mRelWord α y * (mRelWord α x)⁻¹))⁻¹ at hz
  rw [(mBasisFamily (by omega) k e he).evenDeriv_dbarWord_eq hk V.depth] at hz
  change evenRawDbarWord (fun i => f (y i)) V.correction =
    (f (mRelWord α y * (mRelWord α x)⁻¹))⁻¹ at hz
  choose t ht hp using V.depth
  refine ⟨t, ht, ?_⟩
  have htm : (fun i => f (t i)) = V.correction := funext hp
  have hshift := evenRawStageShift_m hα (by omega) h k hk
    (fun i => f (y i)) V.correction V.depth
  change (mRelWord α (fun i => f (y i)))⁻¹ *
    mRelWord α (fun i => f (y i) * V.correction i) =
      evenRawDbarWord (fun i => f (y i)) V.correction at hshift
  rw [← htm] at hshift
  simp only [← map_mul, ← map_mRelWord] at hshift
  rw [htm, hz] at hshift
  have hnew : f (mRelWord α (fun i => y i*t i)) =
      f (mRelWord α y) * (f (mRelWord α y * (mRelWord α x)⁻¹))⁻¹ := by
    exact (inv_mul_eq_iff_eq_mul).mp hshift
  have hcentral : f (mRelWord α y * (mRelWord α x)⁻¹) ∈
      zLayer (FreeTwoRank (coreRank h) : Type) k := ⟨_, herr, rfl⟩
  have hc := (zLayer_commute hcentral (f (mRelWord α y))).inv_left
  rw [← QuotientGroup.eq_one_iff]
  change f _ = 1
  rw [map_mul, map_inv, hnew, ← hc.eq, mul_assoc]
  simp only [map_mul, map_inv, x]
  group

/-! ## The stage interface consumed downstream -/

/-- The M ambient stage supply in the indexing of the stage induction: the
twin of `NAmbientStageSupply`. -/
def MBasisAmbientStageSupply (alpha h : ℕ) : Prop :=
  ∀ n : ℕ, ∀ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    (∀ i, mBasisOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation alpha h (freeTwoRankGen (coreRank h) i)) →
    mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) →
    ∃ t : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)*t i) *
        (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4)

theorem mBasisAmbientStageSupply {alpha h : ℕ} (halpha : 2 ≤ alpha) :
    MBasisAmbientStageSupply alpha h := by
  intro n e he herr
  have H := mBasis_exists_ambient_stage halpha (by omega : 3 ≤ n+3) e he herr
  simpa only [show n+3-1=n+2 by omega, show n+3+1=n+4 by omega] using H

/-- **The coupled M ordinary-head cleanup, as the input this file consumes.**
For a depth-`m` correction `t` of a marking `y` agreeing with the target on
every ordinary character, with corrected defect in `lambda_(m+2)`, the head
correction has a representative in the same class modulo `lambda_(m+1)` with
every ordinary character trivial. This is the M twin of
`exists_freeTwo_nHead_characterZero_same_class`, stated with the weakest
hypotheses this file needs (all coordinates of depth `m`; only `t 0` and `t 2`
enter the ordinary row `2 f(t 0) + 2^alpha f(t 2)` of the M defect). It is not
proved here. -/
def MBasisHeadCleanupSupply (alpha h : ℕ) : Prop :=
  ∀ (m : ℕ) (y t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (target : FreeTwoRank (coreRank h)),
    (∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2]),
      f (mRelWord alpha y) = f target) →
    (∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) m) →
    mRelWord alpha (fun i => y i * t i) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (m + 2) →
    ∃ t0 : FreeTwoRank (coreRank h),
      t0 ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) m ∧
      (t 0)⁻¹ * t0 ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (m + 1) ∧
      ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2]),
        f t0 = 1

/-- Kernel interpolation packaged for the stage lane: a depth correction whose
head ordinary rows vanish has an all-character-zero, orientation-trivial
replacement with the same literal target-relative M defect one level deeper. -/
theorem exists_mBasis_allRows_relative_correction {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (n : ℕ) (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (target : FreeTwoRank (coreRank h))
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hhead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (t 0)) = 0)
    (hdefect : mRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4)) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      (∀ i, mBasisOrientation alpha h (t' i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (t' i) = 1) ∧
      mRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t') * target⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4) := by
  obtain ⟨t', -, hcoords, ht', heq⟩ :=
    exists_mBasis_allRows_same_kernelCoset halpha n e t ht hhead
  have hzero : ∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      (Multiplicative ℤ_[2]), f (t' i) = 1 := by
    intro i f
    apply toAdd.injective
    rw [freeTwo_character_coordinates]
    simp only [hcoords, toAdd_one, zero_mul, Finset.sum_const_zero]
  refine ⟨t', ht', fun i => mBasisOrientation_eq_one_of_coordinates (t' i) (hcoords i),
    hzero, ?_⟩
  rw [← QuotientGroup.eq_one_iff] at hdefect ⊢
  change levelMk (FreeTwoRank (coreRank h) : Type) (n+4) _ = 1 at hdefect ⊢
  rw [map_mul, heq, ← map_mul]
  exact hdefect

/-- **The one-step M stage interface** (the statement the stage lane consumes):
an orientation-compatible free basis with exact ordinary agreement and actual
target-relative M defect in `lambda_(n+3)` has a depth-`(n+2)` correction with
trivial orientation, every ordinary character trivial (so the coordinate matrix
is retained), and defect in `lambda_(n+4)`. -/
def MBasisStageStep (alpha h : ℕ) : Prop :=
  ∀ n : ℕ, ∀ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    (∀ i, mBasisOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      mBasisOrientation alpha h (freeTwoRankGen (coreRank h) i)) →
    (∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2]),
      f (mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) =
        f (mRelWord alpha (freeTwoRankGen (coreRank h)))) →
    mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) →
    ∃ s : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, s i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      (∀ i, mBasisOrientation alpha h (s i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (s i) = 1) ∧
      mRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*s) *
        (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4)

/-- Ambient stage, head cleanup and kernel interpolation compose to the
one-step interface. The head cleanup is the only input not proved here. -/
theorem mBasisStageStep_of_headCleanup {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hhead : MBasisHeadCleanupSupply alpha h) : MBasisStageStep alpha h := by
  classical
  intro n e he hrow herr
  let y := fun i => e (freeTwoRankGen (coreRank h) i)
  let target := mRelWord alpha (freeTwoRankGen (coreRank h))
  obtain ⟨t, ht, hterr⟩ := mBasisAmbientStageSupply halpha n e he herr
  obtain ⟨t0, ht0, hslack0, hzero0⟩ := hhead (n+2) y t target hrow ht hterr
  let s := Function.update t 0 t0
  have hs : ∀ i, s i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2) := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [s] using ht0
    · simpa [s, hi] using ht i
  have hslack : ∀ i, (t i)⁻¹*s i ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [s] using hslack0
    · simp [s, hi]
  have hshead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (s 0)) = 0 := by
    intro j
    simp only [s, Function.update_self, hzero0, toAdd_one]
  have hsdefect : mRelWord alpha (y*s) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4) :=
    (mBasis_mRelWord_correction_defect_mem_iff (by omega) (n+3) y t s target hslack).mpr hterr
  exact exists_mBasis_allRows_relative_correction halpha n e s target hs hshead hsdefect

#print axioms mBasisProjection
#print axioms mBasisProjection_gen
#print axioms mBasisOrientation
#print axioms mBasisProjection_orientation
#print axioms mBasisOrientation_gen
#print axioms mBasisOrientation_aut
#print axioms mBasisOrientation_eq_one_of_coordinates
#print axioms mBasisCoordinateDeriv
#print axioms mBasisCoordinateDeriv_gen
#print axioms mBasisCoordinateDeriv_base
#print axioms mBasis_finite_mRelWord_eq_one
#print axioms mBasisCoordinateDeriv_defect
#print axioms mBasisTuple
#print axioms mBasisFamily
#print axioms mBasis_defect_mem_rawSpan
#print axioms mBasis_exists_ambient_stage
#print axioms MBasisAmbientStageSupply
#print axioms mBasisAmbientStageSupply
#print axioms MBasisHeadCleanupSupply
#print axioms exists_mBasis_allRows_relative_correction
#print axioms MBasisStageStep
#print axioms mBasisStageStep_of_headCleanup

end
end GQ2.Dyadic.MarkedCore
