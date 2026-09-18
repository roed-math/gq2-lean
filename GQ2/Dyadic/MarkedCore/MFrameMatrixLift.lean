import GQ2.Dyadic.MarkedCore.FreeProTwoMatrixBasis
import GQ2.Dyadic.MarkedCore.MFrameApi
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

/-! ## The free group over D_M and its canonical orientation -/

def mFrameFreeProjection (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (DM α h : Type) :=
  presLiftHom 1 (isProP_DM α h) (dmGen α h) (map_one _)

theorem mFrameFreeProjection_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameFreeProjection α h (freeTwoRankGen (coreRank h) i) = dmGen α h i :=
  presLiftHom_gen _ _ _ _ _

theorem mFrameFreeProjection_surjective (α h : ℕ) :
    Function.Surjective (mFrameFreeProjection α h) := by
  have hle : Subgroup.closure (Set.range (dmGen α h)) ≤ (mFrameFreeProjection α h).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨freeTwoRankGen (coreRank h) i, mFrameFreeProjection_gen α h i⟩
  have hh := Subgroup.topologicalClosure_minimal _ hle
    (isCompact_range (mFrameFreeProjection α h).continuous_toFun).isClosed
  rw [dm_topGen α h] at hh
  exact MonoidHom.range_eq_top.mp (top_unique hh)

/-- The canonical M orientation `(A, B, C, D) ↦ (1, -1, 1, mUnit α)`, trivial on
every handle letter, read on the free group. -/
def mFrameFreeOrientation (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) ℤ_[2]ˣ :=
  presLiftHom 1 isProP_two_unitsPadicInt (coreMark 1 (-1) 1 (mUnit α)) (map_one _)

theorem mFrameFreeOrientation_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameFreeOrientation α h (freeTwoRankGen (coreRank h) i) =
      coreMark 1 (-1) 1 (mUnit α) i := presLiftHom_gen _ _ _ _ _

theorem mFrameFreeProjection_orientation (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    chiM α h (mFrameFreeProjection α h x) = mFrameFreeOrientation α h x := by
  have he : (chiM α h).comp (mFrameFreeProjection α h) = mFrameFreeOrientation α h := by
    apply presPro2_hom_ext
    intro i
    change chiM α h (mFrameFreeProjection α h (freeTwoRankGen (coreRank h) i)) =
      mFrameFreeOrientation α h (freeTwoRankGen (coreRank h) i)
    rw [mFrameFreeProjection_gen, chiM, mLiftHom_gen, mFrameFreeOrientation_gen]
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

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
    (mFrameFreeProjection α h)

theorem mFrameFreeAbProjection_gen (α h : ℕ) (i : Fin (coreRank h)) :
    mFrameFreeAbProjection α h (freeTwoRankGen (coreRank h) i) = abMk (dmGen α h i) :=
  congrArg abMk (mFrameFreeProjection_gen α h i)

theorem mFrameFreeAbProjection_coordinateWord (α h : ℕ) (a : Fin (coreRank h) → ℤ_[2]) :
    mFrameFreeAbProjection α h (freeTwoCoordinateWord (coreRank h) a) = mAbWord α h a := by
  rw [freeTwoCoordinateWord, map_list_prod, List.map_ofFn, Fin.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  change mFrameFreeAbProjection α h (zpowZtwo (isProP_presPro2 1)
    (freeTwoRankGen (coreRank h) i) (a i)) = _
  rw [map_zpowZtwo (isProP_presPro2 1) (mIsProP_two_topAb_DM α h), mFrameFreeAbProjection_gen]

theorem mFrame_one_le {α : ℕ} (hα : 2 ≤ α) : 1 ≤ α := le_trans one_le_two hα

/-- The actual all-rank M frame `mPhiHom` read on the free group. -/
def mFrameProjection {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (MFrameModel h) :=
  (⟨(mFrameExists_phiEquiv (mFrame_one_le hα) h).toMulEquiv.toMonoidHom,
    (mFrameExists_phiEquiv (mFrame_one_le hα) h).continuous_toFun⟩ :
      ContinuousMonoidHom _ _).comp (mFrameFreeAbProjection α h)

theorem mFrameProjection_apply {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (x : FreeTwoRank (coreRank h)) :
    mFrameProjection hα h x = mPhiHom (mFrame_one_le hα) h (mFrameFreeAbProjection α h x) := rfl

theorem mFrameProjection_gen {α : ℕ} (hα : 2 ≤ α) (h : ℕ) (i : Fin (coreRank h)) :
    mFrameProjection hα h (freeTwoRankGen (coreRank h) i) =
      mPhiHom (mFrame_one_le hα) h (abMk (dmGen α h i)) := by
  rw [mFrameProjection_apply, mFrameFreeAbProjection_gen]

theorem mFrameProjection_surjective {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    Function.Surjective (mFrameProjection hα h) :=
  (mFrameExists_phiEquiv (mFrame_one_le hα) h).surjective.comp
    (abMk_surjective.comp (mFrameFreeProjection_surjective α h))

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
    ⟨(mFrameExists_phiEquiv (mFrame_one_le hα) h).symm.toMulEquiv.toMonoidHom,
      (mFrameExists_phiEquiv (mFrame_one_le hα) h).symm.continuous_toFun⟩

theorem mFrameOrientation_projection {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (x : FreeTwoRank (coreRank h)) :
    mFrameOrientation hα h (mFrameProjection hα h x) = mFrameFreeOrientation α h x := by
  change abLiftG (chiM α h) ((mFrameExists_phiEquiv (mFrame_one_le hα) h).symm
    (mFrameExists_phiEquiv (mFrame_one_le hα) h (abMk (mFrameFreeProjection α h x)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, abLiftG_abMk, mFrameFreeProjection_orientation]

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

#print axioms mFrameFreeProjection
#print axioms mFrameFreeProjection_gen
#print axioms mFrameFreeProjection_surjective
#print axioms mFrameFreeOrientation
#print axioms mFrameFreeOrientation_gen
#print axioms mFrameFreeProjection_orientation
#print axioms mFrameFreeOrientation_coordinate
#print axioms mFrameFreeAbProjection
#print axioms mFrameFreeAbProjection_gen
#print axioms mFrameFreeAbProjection_coordinateWord
#print axioms mFrame_one_le
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

end
end GQ2.Dyadic.MarkedCore
