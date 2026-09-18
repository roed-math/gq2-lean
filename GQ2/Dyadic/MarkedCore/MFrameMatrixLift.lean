import GQ2.Dyadic.MarkedCore.FreeProTwoMatrixBasis
import GQ2.Dyadic.MarkedCore.MFrameApi
import GQ2.Dyadic.MarkedCore.MFullFrameStages
import GQ2.Dyadic.MarkedCore.N

/-!
# Actual full M-frame automorphisms lifted to free bases

The M relator abelianizes to `2 A + 2^alpha C`, so with `m = 2^(alpha-1)` the
primitive relation vector in the free integral coordinates is `r = e_A + m e_C`
and the frame torsion generator is `Abar + m Cbar`, not `Abar`. The canonical
lift therefore fixes the free element `T = A * C^m` literally and reads every
other generator off the canonical zero-or-one torsion section. The A image is
then `T * (image of C)^(-m)`, which is the explicit inverse substitution
`A = T * C^(-m)` applied to the lifted basis.

This is a free-basis lift, not a relator-preserving automorphism of D_M.
No cup or depth-three relator condition is assumed or asserted here.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative
open scoped GQ2.SectionThree.TopAbInstances

/-! ## The free group over D_M and its canonical orientation

The free projection is MSTAGES's `mStageProjection` (`MFullFrameCompactness`),
and the free orientation is `mStageOrientation = chiM ∘ mStageProjection`; the
presentation-lifted form `mFrameFreeOrientation` below is the same character,
with the coordinate formula that exposes the B parity and the integral D slot. -/

/-- The canonical M orientation `(A, B, C, D) ↦ (1, -1, 1, mUnit α)`, trivial on
every handle letter, read on the free group. -/
def mFrameFreeOrientation (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) ℤ_[2]ˣ :=
  presLiftHom 1 isProP_two_unitsPadicInt (coreMark 1 (-1) 1 (mUnit α)) (map_one _)

theorem mFrameFreeOrientation_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameFreeOrientation α h (freeTwoRankGen (coreRank h) i) =
      coreMark 1 (-1) 1 (mUnit α) i := presLiftHom_gen _ _ _ _ _

theorem mStageProjection_freeOrientation (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    chiM α h (mStageProjection α h x) = mFrameFreeOrientation α h x := by
  have he : (chiM α h).comp (mStageProjection α h) = mFrameFreeOrientation α h := by
    apply presPro2_hom_ext
    intro i
    change chiM α h (mStageProjection α h (freeTwoRankGen (coreRank h) i)) =
      mFrameFreeOrientation α h (freeTwoRankGen (coreRank h) i)
    rw [mStageProjection_gen, chiM, mLiftHom_gen, mFrameFreeOrientation_gen]
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

/-- MSTAGES's free orientation is the presentation-lifted canonical orientation. -/
theorem mStageOrientation_eq_freeOrientation (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mStageOrientation α h x = mFrameFreeOrientation α h x := by
  rw [mStageOrientation_apply, mStageProjection_freeOrientation]

/-- The free orientation is the sign of the B coordinate times the unit power of
the D coordinate: B enters only through its parity. -/
theorem mFrameFreeOrientation_coordinate (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameFreeOrientation α h x =
      mSign (toAdd (freeTwoCoordinate (coreRank h) 1 x)) *
        zpowZtwo isProP_two_unitsPadicInt (mUnit α)
          (toAdd (freeTwoCoordinate (coreRank h) 3 x)) := by
  rw [freeTwo_commutative_hom_coordinates isProP_two_unitsPadicInt (coreRank h)
    (mFrameFreeOrientation α h) x]
  simp only [mFrameFreeOrientation_gen]
  have hne : (1 : Fin (coreRank h)) ≠ 3 := fun hc => by
    have := congrArg Fin.val hc
    rw [coreVal_one, coreVal_three] at this
    omega
  rw [mProd_pair isProP_two_unitsPadicInt _ _ hne (fun i hi1 hi3 => by
    rw [coreMark_apply]
    have hv1 := mCoreVal_ne_one hi1
    have hv3 := mCoreVal_ne_three hi3
    split_ifs <;> rfl), coreMark_one, coreMark_three, mNegOne_zpow]

/-! ## The frame projection of the free group -/

def mFrameFreeAbProjection (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      (topAbelianization (DM α h : Type)) :=
  (⟨abMk, continuous_abMk⟩ : ContinuousMonoidHom (DM α h : Type) _).comp
    (mStageProjection α h)

theorem mFrameFreeAbProjection_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameFreeAbProjection α h (freeTwoRankGen (coreRank h) i) = abMk (dmGen α h i) :=
  congrArg abMk (mStageProjection_gen α h i)

theorem mFrameFreeAbProjection_coordinateWord (α h : ℕ) (a : Fin (coreRank h) → ℤ_[2]) :
    mFrameFreeAbProjection α h (freeTwoCoordinateWord (coreRank h) a) = mAbWord α h a := by
  rw [freeTwoCoordinateWord, map_list_prod, List.map_ofFn, Fin.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  change mFrameFreeAbProjection α h (zpowZtwo (isProP_presPro2 1)
    (freeTwoRankGen (coreRank h) i) (a i)) = _
  rw [map_zpowZtwo (isProP_presPro2 1) (mIsProP_two_topAb_DM α h), mFrameFreeAbProjection_gen]

/-- The actual all-rank M frame `mPhiHom` read on the free group. -/
def mFrameProjection {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (MFrameModel h) :=
  (⟨(mFrameExists_phiEquiv (mStageOneLe hα) h).toMulEquiv.toMonoidHom,
    (mFrameExists_phiEquiv (mStageOneLe hα) h).continuous_toFun⟩ :
      ContinuousMonoidHom _ _).comp (mFrameFreeAbProjection α h)

theorem mFrameProjection_apply {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameProjection hα h x = mPhiHom (mStageOneLe hα) h (mFrameFreeAbProjection α h x) := rfl

theorem mFrameProjection_gen {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (i : Fin (coreRank h)) :
    mFrameProjection hα h (freeTwoRankGen (coreRank h) i) =
      mPhiHom (mStageOneLe hα) h (abMk (dmGen α h i)) := by
  rw [mFrameProjection_apply, mFrameFreeAbProjection_gen]

theorem mFrameProjection_surjective {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    Function.Surjective (mFrameProjection hα h) :=
  (mFrameExists_phiEquiv (mStageOneLe hα) h).surjective.comp
    (abMk_surjective.comp (mStageProjection_surjective α h))

/-- The frame projection of a coordinate word: the torsion slot is the A
coordinate modulo two and the C slot is `a_C - 2^(alpha-1) a_A`. This is the
change of coordinates recorded by `mPhiHom_word`. -/
theorem mFrameProjection_coordinateWord {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (a : Fin (coreRank h) → ℤ_[2]) :
    mFrameProjection hα h (freeTwoCoordinateWord (coreRank h) a) =
      ofAdd ((zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (a 0)).toAdd, a 1,
        -(2 : ℤ_[2]) ^ (α - 1) * a 0 + a 2, a 3, fun k => a (mHandleIdx k)) := by
  rw [mFrameProjection_apply, mFrameFreeAbProjection_coordinateWord, mPhiHom_word]

/-- The canonical section of the frame coordinates: torsion to zero or one, the
C slot corrected by `2^(alpha-1)` times that digit, everything else integral.
This is `mSurjVec`, the exponent vector of `mPhiHom_surjective`. -/
def mFrameCoordinateSection (α : ℕ) {h : ℕ} (z : MFrameModel h) : Fin (coreRank h) → ℤ_[2] :=
  mSurjVec α z.toAdd.1 z.toAdd.2.1 z.toAdd.2.2.1 z.toAdd.2.2.2.1 z.toAdd.2.2.2.2

theorem mFrameProjection_coordinateSection {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (z : MFrameModel h) :
    mFrameProjection hα h (freeTwoCoordinateWord (coreRank h) (mFrameCoordinateSection α z)) =
      z := by
  rw [← ofAdd_toAdd z]
  obtain ⟨a, b, c, d, f⟩ := z.toAdd
  change mFrameProjection hα h (freeTwoCoordinateWord (coreRank h) (mSurjVec α a b c d f)) =
    ofAdd (a, b, c, d, f)
  rw [mFrameProjection_coordinateWord, mSurjVec_zero, mSurjVec_one, mSurjVec_two, mSurjVec_three]
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl (funext fun k => ?_))))
  · rw [zpowZtwo_ofAdd_one_zmod2, toAdd_ofAdd]
  · show -(2 : ℤ_[2]) ^ (α - 1) * (a.val : ℤ_[2])
      + (c + (2 : ℤ_[2]) ^ (α - 1) * (a.val : ℤ_[2])) = c
    ring
  · exact mSurjVec_handle α a b c d f k

/-! ## The canonical orientation transported to the full frame -/

def mFrameOrientation {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (MFrameModel h) ℤ_[2]ˣ :=
  (abLiftG (chiM α h)).comp
    ⟨(mFrameExists_phiEquiv (mStageOneLe hα) h).symm.toMulEquiv.toMonoidHom,
      (mFrameExists_phiEquiv (mStageOneLe hα) h).symm.continuous_toFun⟩

theorem mFrameOrientation_projection {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (x : FreeTwoRank (coreRank h)) :
    mFrameOrientation hα h (mFrameProjection hα h x) = mFrameFreeOrientation α h x := by
  change abLiftG (chiM α h) ((mFrameExists_phiEquiv (mStageOneLe hα) h).symm
    (mFrameExists_phiEquiv (mStageOneLe hα) h (abMk (mStageProjection α h x)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, abLiftG_abMk, mStageProjection_freeOrientation]

/-- The transported actual orientation is the sign of the integral B coordinate
times `mUnit α` to the integral D coordinate. It never sees the torsion, C or
handle slots, and it sees B only through its parity. -/
theorem mFrameOrientation_apply {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (z : MFrameModel h) :
    mFrameOrientation hα h z =
      mSign z.toAdd.2.1 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) z.toAdd.2.2.2.1 := by
  calc
    mFrameOrientation hα h z = mFrameOrientation hα h (mFrameProjection hα h
        (freeTwoCoordinateWord (coreRank h) (mFrameCoordinateSection α z))) :=
      congrArg _ (mFrameProjection_coordinateSection hα h z).symm
    _ = mFrameFreeOrientation α h
        (freeTwoCoordinateWord (coreRank h) (mFrameCoordinateSection α z)) :=
      mFrameOrientation_projection hα h _
    _ = mSign ((mFrameCoordinateSection α z) 1) *
        zpowZtwo isProP_two_unitsPadicInt (mUnit α) ((mFrameCoordinateSection α z) 3) := by
      rw [mFrameFreeOrientation_coordinate, freeTwoCoordinateWord_coordinate,
        freeTwoCoordinateWord_coordinate]
    _ = _ := by rw [mFrameCoordinateSection, mSurjVec_one, mSurjVec_three]

/-- Preserving the actual M orientation is exactly preserving the parity of the
integral B coordinate and the integral D coordinate. It does not fix the
integral B row, unlike the N orientation. -/
theorem mFrameOrientation_preserved_iff {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    (∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z) ↔
      ∀ z, mParityZ (φ z).toAdd.2.1 = mParityZ z.toAdd.2.1 ∧
        (φ z).toAdd.2.2.2.1 = z.toAdd.2.2.2.1 := by
  simp only [mFrameOrientation_apply]
  constructor
  · intro hh z
    have hz := hh z
    rw [mSign_eq_pow_val z.toAdd.2.1] at hz
    exact mChi_row_extract hα hz
  · intro hh z
    rw [mSign_eq_pow_val, mSign_eq_pow_val, (hh z).1, (hh z).2]

/-! ## The primitive relation vector and the head `T = A * C^m` -/

/-- The primitive relation vector `r = e_A + 2^(alpha-1) e_C` in the free integral
coordinates; the M relation submodule is `2 Z_2 r`. -/
def mFrameRelVec (α : ℕ) {h : ℕ} (j : Fin (coreRank h)) : ℤ_[2] :=
  if j = 0 then 1 else if j = 2 then (2 : ℤ_[2]) ^ (α - 1) else 0

theorem mFrameTwo_ne_zero (h : ℕ) : (2 : Fin (coreRank h)) ≠ 0 := mCoreZero_ne_two.symm

theorem mFrameOne_ne_zero (h : ℕ) : (1 : Fin (coreRank h)) ≠ 0 := fun hc => by
  have := congrArg Fin.val hc
  rw [coreVal_one, coreVal_zero] at this
  omega

theorem mFrameThree_ne_zero (h : ℕ) : (3 : Fin (coreRank h)) ≠ 0 := fun hc => by
  have := congrArg Fin.val hc
  rw [coreVal_three, coreVal_zero] at this
  omega

theorem mFrameOne_ne_two (h : ℕ) : (1 : Fin (coreRank h)) ≠ 2 := fun hc => by
  have := congrArg Fin.val hc
  rw [coreVal_one, coreVal_two] at this
  omega

theorem mFrameThree_ne_two (h : ℕ) : (3 : Fin (coreRank h)) ≠ 2 := fun hc => by
  have := congrArg Fin.val hc
  rw [coreVal_three, coreVal_two] at this
  omega

theorem mFrameHandleIdx_ne_zero {h : ℕ} (k : Fin (2 * h)) : mHandleIdx k ≠ 0 := fun hc => by
  have := congrArg Fin.val hc
  rw [mHandleIdx_val, coreVal_zero] at this
  omega

theorem mFrameHandleIdx_ne_two {h : ℕ} (k : Fin (2 * h)) : mHandleIdx k ≠ 2 := fun hc => by
  have := congrArg Fin.val hc
  rw [mHandleIdx_val, coreVal_two] at this
  omega

@[simp] theorem mFrameRelVec_zero (α h : ℕ) : mFrameRelVec α (0 : Fin (coreRank h)) = 1 := by
  rw [mFrameRelVec, if_pos rfl]

@[simp] theorem mFrameRelVec_one (α h : ℕ) : mFrameRelVec α (1 : Fin (coreRank h)) = 0 := by
  rw [mFrameRelVec, if_neg (mFrameOne_ne_zero h), if_neg (mFrameOne_ne_two h)]

@[simp] theorem mFrameRelVec_two (α h : ℕ) :
    mFrameRelVec α (2 : Fin (coreRank h)) = (2 : ℤ_[2]) ^ (α - 1) := by
  rw [mFrameRelVec, if_neg (mFrameTwo_ne_zero h), if_pos rfl]

@[simp] theorem mFrameRelVec_three (α h : ℕ) : mFrameRelVec α (3 : Fin (coreRank h)) = 0 := by
  rw [mFrameRelVec, if_neg (mFrameThree_ne_zero h), if_neg (mFrameThree_ne_two h)]

@[simp] theorem mFrameRelVec_handle (α : ℕ) {h : ℕ} (k : Fin (2 * h)) :
    mFrameRelVec α (mHandleIdx k) = 0 := by
  rw [mFrameRelVec, if_neg (mFrameHandleIdx_ne_zero k), if_neg (mFrameHandleIdx_ne_two k)]

theorem mFrameZMod2_val_one : (1 : ZMod 2).val = 1 := by decide

/-- The free element `T = A * C^(2^(alpha-1))`, the free lift of the frame torsion
generator. Its coordinate vector is the primitive relation vector. -/
def mFrameHead (α h : ℕ) : FreeTwoRank (coreRank h) :=
  freeTwoRankGen (coreRank h) 0 * freeTwoRankGen (coreRank h) 2 ^ (2 ^ (α - 1))

theorem mFrameHead_coordinate (α h : ℕ) (j : Fin (coreRank h)) :
    toAdd (freeTwoCoordinate (coreRank h) j (mFrameHead α h)) = mFrameRelVec α j := by
  rw [mFrameHead, map_mul, map_pow, toAdd_mul, toAdd_pow, freeTwoCoordinate_gen,
    freeTwoCoordinate_gen, toAdd_ofAdd, toAdd_ofAdd, nsmul_eq_mul, mFrameRelVec]
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl, if_pos rfl, if_neg (mFrameTwo_ne_zero h), mul_zero, add_zero]
  · rw [if_neg (Ne.symm h0), if_neg h0, zero_add]
    by_cases h2 : j = 2
    · subst h2
      rw [if_pos rfl, if_pos rfl]
      push_cast
      ring
    · rw [if_neg (Ne.symm h2), if_neg h2, mul_zero]

theorem mFrameProjection_head {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    mFrameProjection hα h (mFrameHead α h) =
      (ofAdd ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
        (0 : Fin (2 * h) → ℤ_[2])) : MFrameModel h) := by
  have ht := mPhiHom_t (mStageOneLe hα) h
  rw [map_mul, map_pow, map_mul, map_pow] at ht
  rw [mFrameHead, map_mul, map_pow, mFrameProjection_gen, mFrameProjection_gen]
  exact ht

/-- Any hom fixing the head `T` preserves the primitive relation vector exactly in
the original integral coordinates: the coordinate matrix `M j i` of the images of
the generators satisfies `M r = r`. -/
theorem mFrameRelVec_fixed_of_head_fixed (α h : ℕ)
    (e : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type))
    (he : e (mFrameHead α h) = mFrameHead α h) (j : Fin (coreRank h)) :
    ∑ i, toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) i))) *
      mFrameRelVec α i = mFrameRelVec α j := by
  have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin (coreRank h))),
      i ∉ ({0, 2} : Finset (Fin (coreRank h))) →
      toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) i))) *
        mFrameRelVec α i = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [mFrameRelVec, if_neg hi.1, if_neg hi.2, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hsupp, Finset.sum_pair mCoreZero_ne_two,
    mFrameRelVec, if_pos rfl, mul_one, mFrameRelVec, if_neg (mFrameTwo_ne_zero h), if_pos rfl,
    ← mFrameHead_coordinate, ← he, mFrameHead, map_mul, map_pow, map_mul, map_pow, toAdd_mul,
    toAdd_pow, nsmul_eq_mul, mul_comm]
  push_cast
  ring

/-! ## The basis change `(A, B, C, D, handles) ↦ (T, B, C, D, handles)` -/

/-- The substitution `A ↦ T = A * C^m`, every other generator fixed. -/
def mFrameBasisChangeHom (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  presLiftHom 1 (isProP_presPro2 1)
    (fun i => if i = 0 then mFrameHead α h else freeTwoRankGen (coreRank h) i) (map_one _)

/-- The explicit inverse substitution `A ↦ T * C^(-m)`, every other generator fixed. -/
def mFrameBasisChangeInvHom (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  presLiftHom 1 (isProP_presPro2 1)
    (fun i => if i = 0 then
      freeTwoRankGen (coreRank h) 0 * (freeTwoRankGen (coreRank h) 2 ^ (2 ^ (α - 1)))⁻¹
      else freeTwoRankGen (coreRank h) i) (map_one _)

theorem mFrameBasisChangeHom_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameBasisChangeHom α h (freeTwoRankGen (coreRank h) i) =
      if i = 0 then mFrameHead α h else freeTwoRankGen (coreRank h) i :=
  presLiftHom_gen _ _ _ _ _

theorem mFrameBasisChangeInvHom_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameBasisChangeInvHom α h (freeTwoRankGen (coreRank h) i) =
      if i = 0 then
        freeTwoRankGen (coreRank h) 0 * (freeTwoRankGen (coreRank h) 2 ^ (2 ^ (α - 1)))⁻¹
      else freeTwoRankGen (coreRank h) i :=
  presLiftHom_gen _ _ _ _ _

theorem mFrameBasisChangeHom_gen_zero (α h : ℕ) :
    mFrameBasisChangeHom α h (freeTwoRankGen (coreRank h) 0) = mFrameHead α h := by
  rw [mFrameBasisChangeHom_gen, if_pos rfl]

theorem mFrameBasisChangeHom_gen_of_ne (α h : ℕ) {i : Fin (coreRank h)} (hi : i ≠ 0) :
    mFrameBasisChangeHom α h (freeTwoRankGen (coreRank h) i) = freeTwoRankGen (coreRank h) i := by
  rw [mFrameBasisChangeHom_gen, if_neg hi]

theorem mFrameBasisChangeInvHom_gen_zero (α h : ℕ) :
    mFrameBasisChangeInvHom α h (freeTwoRankGen (coreRank h) 0) =
      freeTwoRankGen (coreRank h) 0 * (freeTwoRankGen (coreRank h) 2 ^ (2 ^ (α - 1)))⁻¹ := by
  rw [mFrameBasisChangeInvHom_gen, if_pos rfl]

theorem mFrameBasisChangeInvHom_gen_of_ne (α h : ℕ) {i : Fin (coreRank h)} (hi : i ≠ 0) :
    mFrameBasisChangeInvHom α h (freeTwoRankGen (coreRank h) i) =
      freeTwoRankGen (coreRank h) i := by
  rw [mFrameBasisChangeInvHom_gen, if_neg hi]

theorem mFrameBasisChangeHom_comp_inv (α h : ℕ) :
    (mFrameBasisChangeHom α h).comp (mFrameBasisChangeInvHom α h) =
      ContinuousMonoidHom.id (FreeTwoRank (coreRank h) : Type) := by
  apply presPro2_hom_ext
  intro i
  change mFrameBasisChangeHom α h (mFrameBasisChangeInvHom α h (freeTwoRankGen (coreRank h) i)) =
    freeTwoRankGen (coreRank h) i
  by_cases hi : i = 0
  · subst hi
    rw [mFrameBasisChangeInvHom_gen_zero, map_mul, map_inv, map_pow, mFrameBasisChangeHom_gen_zero,
      mFrameBasisChangeHom_gen_of_ne α h (mFrameTwo_ne_zero h), mFrameHead, mul_inv_cancel_right]
  · rw [mFrameBasisChangeInvHom_gen_of_ne α h hi, mFrameBasisChangeHom_gen_of_ne α h hi]

theorem mFrameBasisChangeInvHom_comp (α h : ℕ) :
    (mFrameBasisChangeInvHom α h).comp (mFrameBasisChangeHom α h) =
      ContinuousMonoidHom.id (FreeTwoRank (coreRank h) : Type) := by
  apply presPro2_hom_ext
  intro i
  change mFrameBasisChangeInvHom α h (mFrameBasisChangeHom α h (freeTwoRankGen (coreRank h) i)) =
    freeTwoRankGen (coreRank h) i
  by_cases hi : i = 0
  · subst hi
    rw [mFrameBasisChangeHom_gen_zero, mFrameHead, map_mul, map_pow,
      mFrameBasisChangeInvHom_gen_zero, mFrameBasisChangeInvHom_gen_of_ne α h (mFrameTwo_ne_zero h),
      inv_mul_cancel_right]
  · rw [mFrameBasisChangeHom_gen_of_ne α h hi, mFrameBasisChangeInvHom_gen_of_ne α h hi]

theorem mFrameBasisChangeHom_inv_apply (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameBasisChangeHom α h (mFrameBasisChangeInvHom α h x) = x := by
  have he := congrArg (fun f : ContinuousMonoidHom _ _ => f x) (mFrameBasisChangeHom_comp_inv α h)
  exact he

theorem mFrameBasisChangeInvHom_hom_apply (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameBasisChangeInvHom α h (mFrameBasisChangeHom α h x) = x := by
  have he := congrArg (fun f : ContinuousMonoidHom _ _ => f x) (mFrameBasisChangeInvHom_comp α h)
  exact he

/-- The basis change as an actual continuous automorphism of the free pro-two group. -/
def mFrameBasisChange (α h : ℕ) :
    ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  continuousMulEquivOfBijective (mFrameBasisChangeHom α h)
    (Function.bijective_iff_has_inverse.mpr ⟨mFrameBasisChangeInvHom α h,
      mFrameBasisChangeInvHom_hom_apply α h, mFrameBasisChangeHom_inv_apply α h⟩)

theorem mFrameBasisChange_apply (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameBasisChange α h x = mFrameBasisChangeHom α h x := rfl

theorem mFrameBasisChange_symm_apply (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    (mFrameBasisChange α h).symm x = mFrameBasisChangeInvHom α h x := by
  apply (mFrameBasisChange α h).injective
  rw [ContinuousMulEquiv.apply_symm_apply, mFrameBasisChange_apply, mFrameBasisChangeHom_inv_apply]

theorem mFrameBasisChange_gen_zero (α h : ℕ) :
    mFrameBasisChange α h (freeTwoRankGen (coreRank h) 0) = mFrameHead α h :=
  mFrameBasisChangeHom_gen_zero α h

theorem mFrameBasisChange_gen_of_ne (α h : ℕ) {i : Fin (coreRank h)} (hi : i ≠ 0) :
    mFrameBasisChange α h (freeTwoRankGen (coreRank h) i) = freeTwoRankGen (coreRank h) i :=
  mFrameBasisChangeHom_gen_of_ne α h hi

theorem mFrameBasisChange_symm_gen_zero (α h : ℕ) :
    (mFrameBasisChange α h).symm (freeTwoRankGen (coreRank h) 0) =
      freeTwoRankGen (coreRank h) 0 * (freeTwoRankGen (coreRank h) 2 ^ (2 ^ (α - 1)))⁻¹ := by
  rw [mFrameBasisChange_symm_apply, mFrameBasisChangeInvHom_gen_zero]

/-! ## The coordinate dictionary

`mFrameHeadCoordinate α h j x` is the `j`-th coordinate of `x` in the free basis
`(T, B, C, D, handles)`: the original coordinate of the inverse substitution
`A ↦ T * C^(-m)` applied to `x`. In these coordinates the frame projection has the
N shape (torsion slot = the T coordinate modulo two, every other slot integral). -/

/-- The coordinates in the free basis `(T, B, C, D, handles)`. -/
def mFrameHeadCoordinate (α h : ℕ) (j : Fin (coreRank h)) (x : FreeTwoRank (coreRank h)) : ℤ_[2] :=
  toAdd (freeTwoCoordinate (coreRank h) j ((mFrameBasisChange α h).symm x))

theorem mFrameBasisChange_coordinate_gen (α h : ℕ) (j i : Fin (coreRank h)) :
    toAdd (freeTwoCoordinate (coreRank h) j
      (mFrameBasisChange α h (freeTwoRankGen (coreRank h) i))) =
      (if i = j then 1 else 0) + (if i = 0 ∧ j = 2 then (2 : ℤ_[2]) ^ (α - 1) else 0) := by
  by_cases hi : i = 0
  · subst hi
    rw [mFrameBasisChange_gen_zero, mFrameHead_coordinate, mFrameRelVec]
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, if_pos rfl, if_neg (fun hc => mFrameTwo_ne_zero h hc.2.symm), add_zero]
    · rw [if_neg hj, if_neg (Ne.symm hj), zero_add]
      by_cases hj2 : j = 2
      · subst hj2
        rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hj2, if_neg (fun hc => hj2 hc.2)]
  · rw [mFrameBasisChange_gen_of_ne α h hi, freeTwoCoordinate_gen, toAdd_ofAdd,
      if_neg (show ¬(i = 0 ∧ j = 2) from fun hc => hi hc.1), add_zero]

/-- Original coordinates of the substitution `A ↦ T`: only the C coordinate moves,
by `2^(alpha-1)` times the A coordinate. -/
theorem mFrameBasisChange_coordinate (α h : ℕ) (x : FreeTwoRank (coreRank h))
    (j : Fin (coreRank h)) :
    toAdd (freeTwoCoordinate (coreRank h) j (mFrameBasisChange α h x)) =
      toAdd (freeTwoCoordinate (coreRank h) j x) +
        (if j = 2 then (2 : ℤ_[2]) ^ (α - 1) * toAdd (freeTwoCoordinate (coreRank h) 0 x)
          else 0) := by
  have he := freeTwo_character_coordinates (coreRank h)
    ((freeTwoCoordinate (coreRank h) j).comp (autHom (mFrameBasisChange α h))) x
  change toAdd (freeTwoCoordinate (coreRank h) j (mFrameBasisChange α h x)) = _ at he
  rw [he]
  have hterm : ∀ i, toAdd (freeTwoCoordinate (coreRank h) i x) *
      toAdd (((freeTwoCoordinate (coreRank h) j).comp (autHom (mFrameBasisChange α h)))
        (freeTwoRankGen (coreRank h) i)) =
      (if i = j then toAdd (freeTwoCoordinate (coreRank h) i x) else 0) +
      (if i = 0 ∧ j = 2 then (2 : ℤ_[2]) ^ (α - 1) * toAdd (freeTwoCoordinate (coreRank h) i x)
        else 0) := by
    intro i
    change toAdd (freeTwoCoordinate (coreRank h) i x) *
      toAdd (freeTwoCoordinate (coreRank h) j
        (mFrameBasisChange α h (freeTwoRankGen (coreRank h) i))) = _
    rw [mFrameBasisChange_coordinate_gen, mul_add]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp [mul_comm]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  by_cases hj : j = 2
  · subst hj
    simp
  · simp [hj]

/-- The dictionary: the `(T, B, C, D, handles)` coordinates in terms of the original
ones. Only the C coordinate changes, by `-2^(alpha-1)` times the A coordinate. -/
theorem mFrameHeadCoordinate_eq (α h : ℕ) (j : Fin (coreRank h)) (x : FreeTwoRank (coreRank h)) :
    mFrameHeadCoordinate α h j x =
      toAdd (freeTwoCoordinate (coreRank h) j x) -
        (if j = 2 then (2 : ℤ_[2]) ^ (α - 1) * toAdd (freeTwoCoordinate (coreRank h) 0 x)
          else 0) := by
  have h0 : toAdd (freeTwoCoordinate (coreRank h) 0 ((mFrameBasisChange α h).symm x)) =
      toAdd (freeTwoCoordinate (coreRank h) 0 x) := by
    have := mFrameBasisChange_coordinate α h ((mFrameBasisChange α h).symm x) 0
    rw [ContinuousMulEquiv.apply_symm_apply, if_neg (mFrameTwo_ne_zero h).symm, add_zero] at this
    exact this.symm
  have hj := mFrameBasisChange_coordinate α h ((mFrameBasisChange α h).symm x) j
  rw [ContinuousMulEquiv.apply_symm_apply, h0] at hj
  rw [mFrameHeadCoordinate, hj]
  ring

/-- The head `T` has `(T, B, C, D, handles)` coordinates `e_T`. -/
theorem mFrameHeadCoordinate_head (α h : ℕ) (j : Fin (coreRank h)) :
    mFrameHeadCoordinate α h j (mFrameHead α h) = if j = 0 then 1 else 0 := by
  rw [mFrameHeadCoordinate, ← mFrameBasisChange_gen_zero, ContinuousMulEquiv.symm_apply_apply,
    freeTwoCoordinate_gen, toAdd_ofAdd]
  simp only [eq_comm]

theorem mFrameModel_isProP {α : ℕ} (hα : 2 ≤ α) (h : ℕ) : IsProP 2 (MFrameModel h) :=
  isProP_of_surjective (mPhiHom (mStageOneLe hα) h) (continuous_mPhiHom _ h)
    (mPhiHom_surjective _ h) (mIsProP_two_topAb_DM α h)

/-- The frame projection of an arbitrary free element in the original coordinates. -/
theorem mFrameProjection_coordinate {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameProjection hα h x =
      ofAdd ((zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2))
        (toAdd (freeTwoCoordinate (coreRank h) 0 x))).toAdd,
        toAdd (freeTwoCoordinate (coreRank h) 1 x),
        -(2 : ℤ_[2]) ^ (α - 1) * toAdd (freeTwoCoordinate (coreRank h) 0 x) +
          toAdd (freeTwoCoordinate (coreRank h) 2 x),
        toAdd (freeTwoCoordinate (coreRank h) 3 x),
        fun k => toAdd (freeTwoCoordinate (coreRank h) (mHandleIdx k) x)) := by
  rw [freeTwo_commutative_eq_of_coordinates (mFrameModel_isProP hα h) (coreRank h) x
    (freeTwoCoordinateWord (coreRank h) (fun i => toAdd (freeTwoCoordinate (coreRank h) i x)))
    (fun j => by rw [freeTwoCoordinateWord_coordinate]) (mFrameProjection hα h),
    mFrameProjection_coordinateWord]

/-- In the `(T, B, C, D, handles)` coordinates the frame projection has the N shape:
the torsion slot is the T coordinate modulo two and every other slot is copied. -/
theorem mFrameProjection_headCoordinate {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (x : FreeTwoRank (coreRank h)) :
    mFrameProjection hα h x =
      ofAdd ((zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2))
        (mFrameHeadCoordinate α h 0 x)).toAdd,
        mFrameHeadCoordinate α h 1 x, mFrameHeadCoordinate α h 2 x, mFrameHeadCoordinate α h 3 x,
        fun k => mFrameHeadCoordinate α h (mHandleIdx k) x) := by
  rw [mFrameProjection_coordinate]
  simp only [mFrameHeadCoordinate_eq, if_true, if_neg (mFrameTwo_ne_zero h).symm,
    if_neg (mFrameOne_ne_two h), if_neg (mFrameThree_ne_two h), if_neg (mFrameHandleIdx_ne_two _),
    sub_zero]
  congr 1
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  ring

/-! ## Why independent torsion sections on the A and C columns do not suffice

The literal transcription of the N lift matrix applies the canonical section to
the frame image of every original generator, A and C included. Its A column is the
section of `t * φ(Cbar)^(-m)` and its C column the section of `φ(Cbar)`, and the
two torsion digits are chosen independently. The relation vector is then fixed
exactly if and only if the torsion coordinate of `φ(Cbar)` vanishes; in general
the matrix sends `r` to `(1 + m * digit) r`, a unit multiple. -/

/-- The independent-section matrix: the canonical section of the frame image of
every original generator, including A. -/
def mFrameNaiveLiftMatrix {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2] :=
  fun j i => mFrameCoordinateSection α (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) i))) j

theorem mFrameProjection_gen_zero {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    mFrameProjection hα h (freeTwoRankGen (coreRank h) 0) =
      ofAdd (1, 0, -(2 : ℤ_[2]) ^ (α - 1), 0, 0) := by
  rw [mFrameProjection_gen]
  exact mPhiHom_A (mStageOneLe hα) h

theorem mFrameProjection_gen_two {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    mFrameProjection hα h (freeTwoRankGen (coreRank h) 2) = ofAdd (0, 0, 1, 0, 0) := by
  rw [mFrameProjection_gen]
  exact mPhiHom_C (mStageOneLe hα) h

/-- `2^(alpha-1)` kills `ZMod 2` for `alpha ≥ 2`. -/
theorem mFrame_halfExp_smul_zmod2 {α : ℕ} (hα : 2 ≤ α) (ε : ZMod 2) :
    (2 ^ (α - 1)) • ε = 0 := by
  obtain ⟨r, hr⟩ : ∃ r, α - 1 = r + 1 := ⟨α - 2, by omega⟩
  have h2 : (2 : ℕ) • ε = 0 := by
    revert ε
    decide
  rw [hr, pow_succ', mul_nsmul, h2, nsmul_zero]

/-- The frame image of A under `φ`, from the fixed torsion generator and the image of C. -/
theorem mFrameNaive_image_zero {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) 0))).toAdd =
      ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : Fin (2 * h) → ℤ_[2])) -
        (2 ^ (α - 1)) • (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) 2))).toAdd := by
  have hA : mFrameProjection hα h (freeTwoRankGen (coreRank h) 0) *
      mFrameProjection hα h (freeTwoRankGen (coreRank h) 2) ^ (2 ^ (α - 1)) =
      ofAdd (1, 0, 0, 0, 0) := by
    have := mFrameProjection_head hα h
    rwa [mFrameHead, map_mul, map_pow] at this
  have ht : φ (ofAdd (1, 0, 0, 0, 0)) = ofAdd (1, 0, 0, 0, 0) :=
    nFrameModel_map_t φ.toMulEquiv
  have hφ := congrArg (fun z => toAdd (φ z)) hA
  simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, ht, toAdd_ofAdd] at hφ
  rw [← hφ]
  abel

/-- The independent-section matrix fixes the primitive relation vector exactly
if and only if the torsion coordinate of `φ(Cbar)` vanishes. -/
theorem mFrameNaiveLiftMatrix_relVec_iff {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    (∀ j, ∑ i, mFrameNaiveLiftMatrix hα h φ j i * mFrameRelVec α i = mFrameRelVec α j) ↔
      (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) 2))).toAdd.1 = 0 := by
  set γ := φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) 2)) with hγ
  have hsum : ∀ j, ∑ i, mFrameNaiveLiftMatrix hα h φ j i * mFrameRelVec α i =
      mFrameNaiveLiftMatrix hα h φ j 0 +
        (2 : ℤ_[2]) ^ (α - 1) * mFrameNaiveLiftMatrix hα h φ j 2 := by
    intro j
    have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin (coreRank h))),
        i ∉ ({0, 2} : Finset (Fin (coreRank h))) →
        mFrameNaiveLiftMatrix hα h φ j i * mFrameRelVec α i = 0 := by
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [mFrameRelVec, if_neg hi.1, if_neg hi.2, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ _) hsupp, Finset.sum_pair mCoreZero_ne_two,
      mFrameRelVec_zero, mul_one, mFrameRelVec_two, mul_comm]
  have himg := mFrameNaive_image_zero hα h φ
  rw [← hγ] at himg
  -- the two columns, slot by slot
  have hcol0 : ∀ j, mFrameNaiveLiftMatrix hα h φ j 0 =
      mSurjVec α (1 - (2 ^ (α - 1)) • γ.toAdd.1) (0 - (2 ^ (α - 1)) • γ.toAdd.2.1)
        (0 - (2 ^ (α - 1)) • γ.toAdd.2.2.1) (0 - (2 ^ (α - 1)) • γ.toAdd.2.2.2.1)
        (0 - (2 ^ (α - 1)) • γ.toAdd.2.2.2.2) j := by
    intro j
    rw [mFrameNaiveLiftMatrix, mFrameCoordinateSection, himg]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd]
  have hcol2 : ∀ j, mFrameNaiveLiftMatrix hα h φ j 2 =
      mSurjVec α γ.toAdd.1 γ.toAdd.2.1 γ.toAdd.2.2.1 γ.toAdd.2.2.2.1 γ.toAdd.2.2.2.2 j := by
    intro j
    rfl
  have hε : (1 : ZMod 2) - (2 ^ (α - 1)) • γ.toAdd.1 = 1 := by
    rw [mFrame_halfExp_smul_zmod2 hα, sub_zero]
  have hm0 : (2 : ℤ_[2]) ^ (α - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro hall
    have h0 := hall 0
    rw [hsum, hcol0, hcol2, mSurjVec_zero, mSurjVec_zero, hε, mFrameRelVec_zero,
      mFrameZMod2_val_one] at h0
    have hv : ((2 : ℤ_[2]) ^ (α - 1)) * ((γ.toAdd.1.val : ℕ) : ℤ_[2]) = 0 := by
      push_cast at h0
      linear_combination h0
    rcases mul_eq_zero.mp hv with hc | hc
    · exact absurd hc hm0
    · have : γ.toAdd.1.val = 0 := by exact_mod_cast hc
      exact (ZMod.val_eq_zero _).mp this
  · intro h1 j
    rw [hsum, hcol0, hcol2]
    rcases mIdx_cases j with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · rw [mSurjVec_zero, mSurjVec_zero, hε, h1, mFrameRelVec_zero, ZMod.val_zero,
        mFrameZMod2_val_one]
      push_cast
      ring
    · rw [mSurjVec_one, mSurjVec_one, mFrameRelVec_one, nsmul_eq_mul]
      push_cast
      ring
    · rw [mSurjVec_two, mSurjVec_two, hε, h1, mFrameRelVec_two, ZMod.val_zero,
        mFrameZMod2_val_one, nsmul_eq_mul]
      push_cast
      ring
    · rw [mSurjVec_three, mSurjVec_three, mFrameRelVec_three, nsmul_eq_mul]
      push_cast
      ring
    · rw [mSurjVec_handle, mSurjVec_handle, mFrameRelVec_handle, Pi.sub_apply, Pi.zero_apply,
        Pi.smul_apply, nsmul_eq_mul]
      push_cast
      ring

/-! ## The fixed-T free lift of a frame automorphism -/

section Lift

variable {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))

/-- The canonical coordinate word of the frame image of the generator `i`. -/
def mFrameLiftWord (i : Fin (coreRank h)) : FreeTwoRank (coreRank h) :=
  freeTwoCoordinateWord (coreRank h)
    (mFrameCoordinateSection α (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) i))))

theorem mFrameProjection_liftWord (i : Fin (coreRank h)) :
    mFrameProjection hα h (mFrameLiftWord hα h φ i) =
      φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) i)) :=
  mFrameProjection_coordinateSection hα h _

/-- The marking of the fixed-T lift: `A ↦ T * (lift of C)^(-m)`, the explicit
inverse substitution `A = T * C^(-m)`; every other generator goes to its canonical
coordinate word. -/
def mFrameLiftMark (i : Fin (coreRank h)) : FreeTwoRank (coreRank h) :=
  if i = 0 then mFrameHead α h * (mFrameLiftWord hα h φ 2 ^ (2 ^ (α - 1)))⁻¹
  else mFrameLiftWord hα h φ i

def mFrameLiftHom :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  presLiftHom 1 (isProP_presPro2 1) (mFrameLiftMark hα h φ) (map_one _)

theorem mFrameLiftHom_gen (i : Fin (coreRank h)) :
    mFrameLiftHom hα h φ (freeTwoRankGen (coreRank h) i) = mFrameLiftMark hα h φ i :=
  presLiftHom_gen _ _ _ _ _

theorem mFrameLiftHom_gen_zero :
    mFrameLiftHom hα h φ (freeTwoRankGen (coreRank h) 0) =
      mFrameHead α h * (mFrameLiftWord hα h φ 2 ^ (2 ^ (α - 1)))⁻¹ := by
  rw [mFrameLiftHom_gen, mFrameLiftMark, if_pos rfl]

theorem mFrameLiftHom_gen_of_ne {i : Fin (coreRank h)} (hi : i ≠ 0) :
    mFrameLiftHom hα h φ (freeTwoRankGen (coreRank h) i) = mFrameLiftWord hα h φ i := by
  rw [mFrameLiftHom_gen, mFrameLiftMark, if_neg hi]

/-- The actual head `T = A * C^m` is fixed literally, before taking any quotient. -/
theorem mFrameLiftHom_head : mFrameLiftHom hα h φ (mFrameHead α h) = mFrameHead α h := by
  conv_lhs => rw [mFrameHead, map_mul, map_pow, mFrameLiftHom_gen_zero,
    mFrameLiftHom_gen_of_ne hα h φ (mFrameTwo_ne_zero h)]
  exact inv_mul_cancel_right _ _

theorem mFrameLiftHom_projection_gen (i : Fin (coreRank h)) :
    mFrameProjection hα h (mFrameLiftHom hα h φ (freeTwoRankGen (coreRank h) i)) =
      φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) i)) := by
  by_cases hi : i = 0
  · subst hi
    rw [mFrameLiftHom_gen_zero, map_mul, map_inv, map_pow, mFrameProjection_head,
      mFrameProjection_liftWord]
    have hA : mFrameProjection hα h (freeTwoRankGen (coreRank h) 0) *
        mFrameProjection hα h (freeTwoRankGen (coreRank h) 2) ^ (2 ^ (α - 1)) =
        ofAdd (1, 0, 0, 0, 0) := by
      have := mFrameProjection_head hα h
      rwa [mFrameHead, map_mul, map_pow] at this
    have ht : φ (ofAdd (1, 0, 0, 0, 0)) = ofAdd (1, 0, 0, 0, 0) :=
      nFrameModel_map_t φ.toMulEquiv
    rw [← ht, ← hA, map_mul, map_pow, mul_inv_cancel_right]
  · rw [mFrameLiftHom_gen_of_ne hα h φ hi, mFrameProjection_liftWord]

theorem mFrameLiftHom_projection (x : FreeTwoRank (coreRank h)) :
    mFrameProjection hα h (mFrameLiftHom hα h φ x) = φ (mFrameProjection hα h x) := by
  have he : (mFrameProjection hα h).comp (mFrameLiftHom hα h φ) =
      (autHom φ).comp (mFrameProjection hα h) := by
    apply presPro2_hom_ext
    exact mFrameLiftHom_projection_gen hα h φ
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

theorem mFrameLiftHom_surjective : Function.Surjective (mFrameLiftHom hα h φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective (isProP_presPro2 1) _ ?_
  intro M hM
  letI : Finite ((FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hc : Nat.card ((FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  haveI : IsCyclic ((FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup) := isCyclic_of_prime_card hc
  letI : CommGroup ((FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup) := IsCyclic.commGroup
  let q : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      ((FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  have hQ : IsProP 2 ((FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup) :=
    isProP_of_isPGroup ((isProP_presPro2 1) M)
  have hsq : ∀ y : (FreeTwoRank (coreRank h) : Type) ⧸ M.toSubgroup, y ^ 2 = 1 := by
    intro y
    rw [← hc]
    exact pow_card_eq_one'
  have hrel : (q (freeTwoRankGen (coreRank h) 0)) ^ 2 *
      (q (freeTwoRankGen (coreRank h) 2)) ^ (2 ^ α) = 1 := by
    obtain ⟨r, hr⟩ : ∃ r, α = r + 1 := ⟨α - 1, by omega⟩
    rw [hsq, hr, pow_succ, pow_mul, hsq, one_mul]
  let qAb := mCoordHom α h hQ (fun i => q (freeTwoRankGen (coreRank h) i)) hrel
  let qFrame := qAb.comp
    (⟨(mFrameExists_phiEquiv (mStageOneLe hα) h).symm.toMulEquiv.toMonoidHom,
      (mFrameExists_phiEquiv (mStageOneLe hα) h).symm.continuous_toFun⟩ :
        ContinuousMonoidHom _ _)
  have hfactor : qFrame.comp (mFrameProjection hα h) = q := by
    apply presPro2_hom_ext
    intro i
    change qAb ((mFrameExists_phiEquiv (mStageOneLe hα) h).symm
      (mFrameExists_phiEquiv (mStageOneLe hα) h
        (mFrameFreeAbProjection α h (freeTwoRankGen (coreRank h) i)))) = _
    rw [ContinuousMulEquiv.symm_apply_apply, mFrameFreeAbProjection_gen]
    exact mCoordHom_gen α h hQ _ hrel i
  have hf (x : FreeTwoRank (coreRank h)) : qFrame (mFrameProjection hα h x) = q x :=
    congrArg (fun f : ContinuousMonoidHom _ _ => f x) hfactor
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
  obtain ⟨y, hy⟩ := mFrameProjection_surjective hα h (φ.symm (mFrameProjection hα h x))
  refine ⟨y, ?_⟩
  change q (mFrameLiftHom hα h φ y) = q x
  rw [← hf, mFrameLiftHom_projection, hy, φ.apply_symm_apply, hf]

private theorem mFrameLift_topGen :
    ∃ s : Finset (FreeTwoRank (coreRank h) : Type),
      (Subgroup.closure (s : Set (FreeTwoRank (coreRank h) : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (freeTwoRankGen (coreRank h)), ?_⟩
  have hs : (↑(Finset.univ.image (freeTwoRankGen (coreRank h))) :
      Set (FreeTwoRank (coreRank h) : Type)) = Set.range (freeTwoRankGen (coreRank h)) := by simp
  rw [hs]
  exact presPro2_topGen _

/-- The fixed-T lift as an actual continuous automorphism of the free pro-two group
(surjective through the index-two quotients and Frattini, then Hopfian). -/
def mFrameLiftEquiv :
    ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  continuousMulEquivOfBijective (mFrameLiftHom hα h φ)
    ⟨profinite_hopfian (mFrameLift_topGen h) _ (mFrameLiftHom_surjective hα h φ),
      mFrameLiftHom_surjective hα h φ⟩

theorem mFrameLiftEquiv_apply (x : FreeTwoRank (coreRank h)) :
    mFrameLiftEquiv hα h φ x = mFrameLiftHom hα h φ x := rfl

/-- The actual head `T = A * C^m` is fixed literally by the automorphism. -/
theorem mFrameLiftEquiv_head : mFrameLiftEquiv hα h φ (mFrameHead α h) = mFrameHead α h :=
  mFrameLiftHom_head hα h φ

theorem mFrameLiftEquiv_projection (x : FreeTwoRank (coreRank h)) :
    mFrameProjection hα h (mFrameLiftEquiv hα h φ x) = φ (mFrameProjection hα h x) :=
  mFrameLiftHom_projection hα h φ x

theorem mFrameLiftEquiv_orientation
    (hχ : ∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z)
    (x : FreeTwoRank (coreRank h)) :
    mFrameFreeOrientation α h (mFrameLiftEquiv hα h φ x) = mFrameFreeOrientation α h x := by
  rw [← mFrameOrientation_projection hα h, mFrameLiftEquiv_projection, hχ,
    mFrameOrientation_projection]

/-- The exact coordinates of the lifted generators other than A: the canonical
section of their frame images. -/
theorem mFrameLiftEquiv_coordinate_gen_of_ne {i : Fin (coreRank h)} (hi : i ≠ 0)
    (j : Fin (coreRank h)) :
    toAdd (freeTwoCoordinate (coreRank h) j
      (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i))) =
      mFrameCoordinateSection α (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) i))) j := by
  rw [mFrameLiftEquiv_apply, mFrameLiftHom_gen_of_ne hα h φ hi, mFrameLiftWord,
    freeTwoCoordinateWord_coordinate]

/-- The exact coordinates of the lifted A: the relation vector minus `2^(alpha-1)`
times the lifted C column. -/
theorem mFrameLiftEquiv_coordinate_gen_zero (j : Fin (coreRank h)) :
    toAdd (freeTwoCoordinate (coreRank h) j
      (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) 0))) =
      mFrameRelVec α j - (2 : ℤ_[2]) ^ (α - 1) *
        mFrameCoordinateSection α (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) 2))) j := by
  rw [mFrameLiftEquiv_apply, mFrameLiftHom_gen_zero, map_mul, map_inv, map_pow, toAdd_mul,
    toAdd_inv, toAdd_pow, mFrameHead_coordinate, mFrameLiftWord, freeTwoCoordinateWord_coordinate,
    nsmul_eq_mul, sub_eq_add_neg]
  push_cast
  ring

/-- The primitive relation vector is preserved exactly by the lift. -/
theorem mFrameLiftEquiv_relVec (j : Fin (coreRank h)) :
    ∑ i, toAdd (freeTwoCoordinate (coreRank h) j
      (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i))) * mFrameRelVec α i =
      mFrameRelVec α j :=
  mFrameRelVec_fixed_of_head_fixed α h (mFrameLiftHom hα h φ) (mFrameLiftHom_head hα h φ) j

end Lift

/-- An actual M frame automorphism preserving the canonical orientation has a
free-basis lift fixing the head `T = A * C^(2^(alpha-1))` literally, hence preserving
the primitive relation vector exactly, with the exact frame square and the
orientation preserved. Every column other than A is the canonical section of its
frame image, including torsion and arbitrary handle mixing. -/
theorem exists_mFrame_freeBasis_lift {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hχ : ∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
        (FreeTwoRank (coreRank h) : Type),
      e (mFrameHead α h) = mFrameHead α h ∧
      (∀ j, ∑ i, toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) i))) *
        mFrameRelVec α i = mFrameRelVec α j) ∧
      (∀ x, mFrameFreeOrientation α h (e x) = mFrameFreeOrientation α h x) ∧
      (∀ x, mFrameProjection hα h (e x) = φ (mFrameProjection hα h x)) ∧
      ∀ i, i ≠ 0 → ∀ j,
        toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) i))) =
          mFrameCoordinateSection α (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) i))) j :=
  ⟨mFrameLiftEquiv hα h φ, mFrameLiftEquiv_head hα h φ, mFrameLiftEquiv_relVec hα h φ,
    mFrameLiftEquiv_orientation hα h φ hχ, mFrameLiftEquiv_projection hα h φ,
    fun _ hi j => mFrameLiftEquiv_coordinate_gen_of_ne hα h φ hi j⟩

/-! ## The torsion shear: an orientation-preserving frame automorphism defeating
independent sections

`(ε, b, c, d, f) ↦ (ε + parity c, b, c, d, f)` is a continuous automorphism of the
frame model (an involution), preserves the actual orientation (which reads only
the B and D slots), and sends `Cbar` to `Cbar + t`. For it the independent-section
matrix does not fix the primitive relation vector. -/

theorem mFrameParity_continuous : Continuous mParityZ := by
  have hcont : Continuous (PadicInt.toZModPow (p := 2) 1 : ℤ_[2] → ZMod (2 ^ 1)) := by
    rw [continuous_def]
    intro T _
    exact isOpen_preimage_toZModPow 1 T
  exact (continuous_of_discreteTopology
    (f := fun x : ZMod (2 ^ 1) => ((x.val : ℕ) : ZMod 2))).comp hcont

theorem mFrameParity_add_self (ε p : ZMod 2) : ε + p + p = ε := by
  revert ε p
  decide

def mFrameTorsionShear (h : ℕ) : ContinuousMulEquiv (MFrameModel h) (MFrameModel h) where
  toFun z := ofAdd (z.toAdd.1 + mParityZ z.toAdd.2.2.1, z.toAdd.2.1, z.toAdd.2.2.1,
    z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
  invFun z := ofAdd (z.toAdd.1 + mParityZ z.toAdd.2.2.1, z.toAdd.2.1, z.toAdd.2.2.1,
    z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
  left_inv z := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    conv_rhs => rw [← ofAdd_toAdd z, toAdd_ofAdd]
    exact Prod.ext (mFrameParity_add_self _ _) rfl
  right_inv z := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    conv_rhs => rw [← ofAdd_toAdd z, toAdd_ofAdd]
    exact Prod.ext (mFrameParity_add_self _ _) rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, mParityZ_add]
    refine Prod.ext ?_ rfl
    show x.toAdd.1 + y.toAdd.1 + (mParityZ x.toAdd.2.2.1 + mParityZ y.toAdd.2.2.1) =
      x.toAdd.1 + mParityZ x.toAdd.2.2.1 + (y.toAdd.1 + mParityZ y.toAdd.2.2.1)
    abel
  continuous_toFun := by
    refine continuous_ofAdd.comp ?_
    have h1 : Continuous fun z : MFrameModel h => z.toAdd.1 := continuous_fst.comp continuous_toAdd
    have h21 : Continuous fun z : MFrameModel h => z.toAdd.2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_toAdd)
    have h221 : Continuous fun z : MFrameModel h => z.toAdd.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
    have h2221 : Continuous fun z : MFrameModel h => z.toAdd.2.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp (continuous_snd.comp
        (continuous_snd.comp continuous_toAdd)))
    have h2222 : Continuous fun z : MFrameModel h => z.toAdd.2.2.2.2 :=
      continuous_snd.comp (continuous_snd.comp (continuous_snd.comp
        (continuous_snd.comp continuous_toAdd)))
    exact (h1.add (mFrameParity_continuous.comp h221)).prodMk
      (h21.prodMk (h221.prodMk (h2221.prodMk h2222)))
  continuous_invFun := by
    refine continuous_ofAdd.comp ?_
    have h1 : Continuous fun z : MFrameModel h => z.toAdd.1 := continuous_fst.comp continuous_toAdd
    have h21 : Continuous fun z : MFrameModel h => z.toAdd.2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_toAdd)
    have h221 : Continuous fun z : MFrameModel h => z.toAdd.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
    have h2221 : Continuous fun z : MFrameModel h => z.toAdd.2.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp (continuous_snd.comp
        (continuous_snd.comp continuous_toAdd)))
    have h2222 : Continuous fun z : MFrameModel h => z.toAdd.2.2.2.2 :=
      continuous_snd.comp (continuous_snd.comp (continuous_snd.comp
        (continuous_snd.comp continuous_toAdd)))
    exact (h1.add (mFrameParity_continuous.comp h221)).prodMk
      (h21.prodMk (h221.prodMk (h2221.prodMk h2222)))

theorem mFrameTorsionShear_apply (h : ℕ) (z : MFrameModel h) :
    mFrameTorsionShear h z = ofAdd (z.toAdd.1 + mParityZ z.toAdd.2.2.1, z.toAdd.2.1,
      z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2) := rfl

theorem mFrameTorsionShear_orientation {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (z : MFrameModel h) :
    mFrameOrientation hα h (mFrameTorsionShear h z) = mFrameOrientation hα h z := by
  rw [mFrameOrientation_apply, mFrameOrientation_apply, mFrameTorsionShear_apply, toAdd_ofAdd]

theorem mFrameTorsionShear_gen_two {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    (mFrameTorsionShear h (mFrameProjection hα h (freeTwoRankGen (coreRank h) 2))).toAdd.1 = 1 := by
  rw [mFrameProjection_gen_two, mFrameTorsionShear_apply, toAdd_ofAdd, toAdd_ofAdd]
  show (0 : ZMod 2) + mParityZ 1 = 1
  rw [mParityZ_one, zero_add]

/-- The precise obstruction: for the orientation-preserving torsion shear, the
independent zero-or-one sections on the A and C columns do not fix the primitive
relation vector. The fixed-T lift of the same automorphism does
(`mFrameLiftEquiv_relVec`). -/
theorem mFrameNaiveLiftMatrix_torsionShear_not_relVec {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    ¬ ∀ j, ∑ i, mFrameNaiveLiftMatrix hα h (mFrameTorsionShear h) j i * mFrameRelVec α i =
      mFrameRelVec α j := by
  rw [mFrameNaiveLiftMatrix_relVec_iff, mFrameTorsionShear_gen_two]
  decide

/-! ## The cup-side interface

The fixed-T lift does not fix A literally: `A⁻¹ * e(A) = C^m * (e C)^(-m)`. For
`alpha ≥ 2` both factors are `2^(alpha-1)`-th powers, so `e(A)` agrees with `A`
modulo lambda-two, and every reduced (mod-two) coordinate of `e(A)` is that of `A`. -/

theorem mFrame_pow_halfExp_mem_two {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (g : FreeTwoRank (coreRank h)) :
    g ^ (2 ^ (α - 1)) ∈ Roe.Labute.twoCentralSeries (FreeTwoRank (coreRank h) : Type) 2 :=
  Roe.Labute.twoCentralSeries_antitone (FreeTwoRank (coreRank h) : Type)
    (by omega : 2 ≤ α - 1 + 1)
    (Roe.Labute.pow_two_pow_mem_twoCentralSeries_succ (FreeTwoRank (coreRank h) : Type) g (α - 1))

/-- The cup-side interface, group form: the lifted A agrees with A modulo lambda-two. -/
theorem mFrameLiftEquiv_gen_zero_mem_two {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    (freeTwoRankGen (coreRank h) 0)⁻¹ *
      mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) 0) ∈
      Roe.Labute.twoCentralSeries (FreeTwoRank (coreRank h) : Type) 2 := by
  rw [mFrameLiftEquiv_apply, mFrameLiftHom_gen_zero, mFrameHead, ← mul_assoc, inv_mul_cancel_left]
  exact Subgroup.mul_mem _ (mFrame_pow_halfExp_mem_two hα h _)
    (Subgroup.inv_mem _ (mFrame_pow_halfExp_mem_two hα h _))

/-- The cup-side interface, quotient form: equality in the level-two quotient. -/
theorem mFrameLiftEquiv_levelMk_two_gen_zero {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    Roe.Labute.levelMk (FreeTwoRank (coreRank h) : Type) 2
        (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) 0)) =
      Roe.Labute.levelMk (FreeTwoRank (coreRank h) : Type) 2 (freeTwoRankGen (coreRank h) 0) := by
  symm
  exact (QuotientGroup.eq).mpr (mFrameLiftEquiv_gen_zero_mem_two hα h φ)

theorem mFrame_nRed_two : nRed (2 : ℤ_[2]) = 0 := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
  decide

theorem mFrame_nRed_halfExp {α : ℕ} (hα : 2 ≤ α) : nRed ((2 : ℤ_[2]) ^ (α - 1)) = 0 := by
  obtain ⟨r, hr⟩ : ∃ r, α - 1 = r + 1 := ⟨α - 2, by omega⟩
  rw [hr, pow_succ, map_mul, mFrame_nRed_two, mul_zero]

/-- The cup-side interface, coordinate form: the reduced A column of the lift is the
first standard basis vector, exactly as for the N lift. -/
theorem mFrameLiftEquiv_reduced_gen_zero {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) (j : Fin (coreRank h)) :
    nRed (toAdd (freeTwoCoordinate (coreRank h) j
      (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) 0)))) = if j = 0 then 1 else 0 := by
  rw [mFrameLiftEquiv_coordinate_gen_zero, map_sub, map_mul, mFrame_nRed_halfExp hα, zero_mul,
    sub_zero, mFrameRelVec]
  split_ifs
  · exact map_one nRed
  · exact mFrame_nRed_halfExp hα
  · exact map_zero nRed

/-! ## The MSTAGES interface

`mFullStabilizer_lift` (`MFullFrameStages`) consumes an initial free basis `e0`
with the primitive torsion word `T` fixed, the orientation `mStageOrientation`
preserved on generators and the full frame square through `mPhiHom` on
generators. The fixed-T lift supplies exactly these. The fourth component of
`MStageInitialLift`, the depth-three relator error, is MCUP's obligation and is
carried here as a hypothesis, not proved. -/

/-- The transported orientation on the frame is the existing model character of
`MFrameApi`, so preserving it is preserving the actual `chiM` through the frame. -/
theorem mFrameOrientation_eq_apiChiModel {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (z : MFrameModel h) :
    mFrameOrientation hα h z = mFrameApiChiModel α h z :=
  mFrameOrientation_apply hα h z

theorem mFrameHead_eq_torsionWord (α h : ℕ) :
    mFrameHead α h = mStageTorsionWord α (freeTwoRankGen (coreRank h)) := rfl

theorem mFrameLiftEquiv_torsionWord {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    mStageTorsionWord α (fun i => mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i)) =
      mStageTorsionWord α (freeTwoRankGen (coreRank h)) := by
  have hh := mFrameLiftEquiv_head hα h φ
  rw [mFrameHead_eq_torsionWord, mStageTorsionWord, map_mul, map_pow] at hh
  exact hh

theorem mFrameLiftEquiv_stageOrientation {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hχ : ∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z) (i : Fin (coreRank h)) :
    mStageOrientation α h (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i)) =
      mStageOrientation α h (freeTwoRankGen (coreRank h) i) := by
  rw [mStageOrientation_eq_freeOrientation, mStageOrientation_eq_freeOrientation]
  exact mFrameLiftEquiv_orientation hα h φ hχ _

theorem mFrameLiftEquiv_stageFrame {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) (i : Fin (coreRank h)) :
    mPhiHom (mStageOneLe hα) h (abMk (mStageProjection α h
        (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i)))) =
      φ (mPhiHom (mStageOneLe hα) h (abMk (dmGen α h i))) := by
  have hp := mFrameLiftEquiv_projection hα h φ (freeTwoRankGen (coreRank h) i)
  rw [mFrameProjection_apply, mFrameProjection_apply, mFrameFreeAbProjection_gen] at hp
  exact hp

/-- The packaged initial interface of `MFullFrameStages`, from the fixed-T lift
and MCUP's depth-three relator error for that same lift. Only the error is a
hypothesis here; the basis, the fixed torsion word, the orientation and the
frame square are supplied. -/
theorem mStageInitialLift_of_fixedHead_error {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hχ : ∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z)
    (herror : mRelWord α (fun i => mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i)) *
      (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        Roe.Labute.twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3) :
    MStageInitialLift hα h φ :=
  ⟨mFrameLiftEquiv hα h φ, mFrameLiftEquiv_torsionWord hα h φ,
    mFrameLiftEquiv_stageOrientation hα h φ hχ, mFrameLiftEquiv_stageFrame hα h φ, herror⟩

/-- The composition with `mFullStabilizer_lift`, with the MINIT obligations
discharged by the fixed-T lift. Still conditional on MCUP's depth-three error
for this lift and on the `MStageStep` depth interface; it is not a proved lift. -/
theorem mFullStabilizer_lift_of_fixedHead {α h : ℕ} (hα : 2 ≤ α)
    (φ : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hχ : ∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z)
    (herror : mRelWord α (fun i => mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i)) *
      (mRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        Roe.Labute.twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3)
    (hstep : MStageStep α h) :
    ∃ Psi : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (Psi x) = chiM α h x) ∧
      (∀ x, mPhiHom (mStageOneLe hα) h (abMk (Psi x)) =
        φ (mPhiHom (mStageOneLe hα) h (abMk x))) :=
  mFullStabilizer_lift_of_initialLift hα φ
    (mStageInitialLift_of_fixedHead_error hα h φ hχ herror) hstep

#print axioms mFrameFreeOrientation
#print axioms mFrameFreeOrientation_gen
#print axioms mStageProjection_freeOrientation
#print axioms mStageOrientation_eq_freeOrientation
#print axioms mFrameFreeOrientation_coordinate
#print axioms mFrameFreeAbProjection
#print axioms mFrameFreeAbProjection_gen
#print axioms mFrameFreeAbProjection_coordinateWord
#print axioms mFrameProjection
#print axioms mFrameProjection_apply
#print axioms mFrameProjection_gen
#print axioms mFrameProjection_surjective
#print axioms mFrameProjection_coordinateWord
#print axioms mFrameCoordinateSection
#print axioms mFrameProjection_coordinateSection
#print axioms mFrameOrientation
#print axioms mFrameOrientation_projection
#print axioms mFrameOrientation_apply
#print axioms mFrameOrientation_preserved_iff
#print axioms mFrameRelVec
#print axioms mFrameTwo_ne_zero
#print axioms mFrameOne_ne_zero
#print axioms mFrameThree_ne_zero
#print axioms mFrameOne_ne_two
#print axioms mFrameThree_ne_two
#print axioms mFrameHandleIdx_ne_zero
#print axioms mFrameHandleIdx_ne_two
#print axioms mFrameRelVec_zero
#print axioms mFrameRelVec_one
#print axioms mFrameRelVec_two
#print axioms mFrameRelVec_three
#print axioms mFrameRelVec_handle
#print axioms mFrameZMod2_val_one
#print axioms mFrameHead
#print axioms mFrameHead_coordinate
#print axioms mFrameProjection_head
#print axioms mFrameRelVec_fixed_of_head_fixed
#print axioms mFrameBasisChangeHom
#print axioms mFrameBasisChangeInvHom
#print axioms mFrameBasisChangeHom_gen
#print axioms mFrameBasisChangeInvHom_gen
#print axioms mFrameBasisChangeHom_gen_zero
#print axioms mFrameBasisChangeHom_gen_of_ne
#print axioms mFrameBasisChangeInvHom_gen_zero
#print axioms mFrameBasisChangeInvHom_gen_of_ne
#print axioms mFrameBasisChangeHom_comp_inv
#print axioms mFrameBasisChangeInvHom_comp
#print axioms mFrameBasisChangeHom_inv_apply
#print axioms mFrameBasisChangeInvHom_hom_apply
#print axioms mFrameBasisChange
#print axioms mFrameBasisChange_apply
#print axioms mFrameBasisChange_symm_apply
#print axioms mFrameBasisChange_gen_zero
#print axioms mFrameBasisChange_gen_of_ne
#print axioms mFrameBasisChange_symm_gen_zero
#print axioms mFrameHeadCoordinate
#print axioms mFrameBasisChange_coordinate_gen
#print axioms mFrameBasisChange_coordinate
#print axioms mFrameHeadCoordinate_eq
#print axioms mFrameHeadCoordinate_head
#print axioms mFrameModel_isProP
#print axioms mFrameProjection_coordinate
#print axioms mFrameProjection_headCoordinate
#print axioms mFrameNaiveLiftMatrix
#print axioms mFrameProjection_gen_zero
#print axioms mFrameProjection_gen_two
#print axioms mFrame_halfExp_smul_zmod2
#print axioms mFrameNaive_image_zero
#print axioms mFrameNaiveLiftMatrix_relVec_iff
#print axioms mFrameLiftWord
#print axioms mFrameProjection_liftWord
#print axioms mFrameLiftMark
#print axioms mFrameLiftHom
#print axioms mFrameLiftHom_gen
#print axioms mFrameLiftHom_gen_zero
#print axioms mFrameLiftHom_gen_of_ne
#print axioms mFrameLiftHom_head
#print axioms mFrameLiftHom_projection_gen
#print axioms mFrameLiftHom_projection
#print axioms mFrameLiftHom_surjective
#print axioms mFrameLift_topGen
#print axioms mFrameLiftEquiv
#print axioms mFrameLiftEquiv_apply
#print axioms mFrameLiftEquiv_head
#print axioms mFrameLiftEquiv_projection
#print axioms mFrameLiftEquiv_orientation
#print axioms mFrameLiftEquiv_coordinate_gen_of_ne
#print axioms mFrameLiftEquiv_coordinate_gen_zero
#print axioms mFrameLiftEquiv_relVec
#print axioms exists_mFrame_freeBasis_lift
#print axioms mFrameParity_continuous
#print axioms mFrameParity_add_self
#print axioms mFrameTorsionShear
#print axioms mFrameTorsionShear_apply
#print axioms mFrameTorsionShear_orientation
#print axioms mFrameTorsionShear_gen_two
#print axioms mFrameNaiveLiftMatrix_torsionShear_not_relVec
#print axioms mFrame_pow_halfExp_mem_two
#print axioms mFrameLiftEquiv_gen_zero_mem_two
#print axioms mFrameLiftEquiv_levelMk_two_gen_zero
#print axioms mFrame_nRed_two
#print axioms mFrame_nRed_halfExp
#print axioms mFrameLiftEquiv_reduced_gen_zero
#print axioms mFrameOrientation_eq_apiChiModel
#print axioms mFrameHead_eq_torsionWord
#print axioms mFrameLiftEquiv_torsionWord
#print axioms mFrameLiftEquiv_stageOrientation
#print axioms mFrameLiftEquiv_stageFrame
#print axioms mStageInitialLift_of_fixedHead_error
#print axioms mFullStabilizer_lift_of_fixedHead

end
end GQ2.Dyadic.MarkedCore
