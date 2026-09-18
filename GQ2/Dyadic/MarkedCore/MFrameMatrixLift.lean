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

/-! ## The primitive relation vector and the head `T = A * C^m` -/

/-- The primitive relation vector `r = e_A + 2^(alpha-1) e_C` in the free integral
coordinates; the M relation submodule is `2 Z_2 r`. -/
def mFrameRelVec (α : ℕ) {h : ℕ} (j : Fin (coreRank h)) : ℤ_[2] :=
  if j = 0 then 1 else if j = 2 then (2 : ℤ_[2]) ^ (α - 1) else 0

theorem mFrameTwo_ne_zero (h : ℕ) : (2 : Fin (coreRank h)) ≠ 0 := mCoreZero_ne_two.symm

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
  have ht := mPhiHom_t (mFrame_one_le hα) h
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
    (⟨(mFrameExists_phiEquiv (mFrame_one_le hα) h).symm.toMulEquiv.toMonoidHom,
      (mFrameExists_phiEquiv (mFrame_one_le hα) h).symm.continuous_toFun⟩ :
        ContinuousMonoidHom _ _)
  have hfactor : qFrame.comp (mFrameProjection hα h) = q := by
    apply presPro2_hom_ext
    intro i
    change qAb ((mFrameExists_phiEquiv (mFrame_one_le hα) h).symm
      (mFrameExists_phiEquiv (mFrame_one_le hα) h
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
#print axioms mFrameRelVec
#print axioms mFrameTwo_ne_zero
#print axioms mFrameHead
#print axioms mFrameHead_coordinate
#print axioms mFrameProjection_head
#print axioms mFrameRelVec_fixed_of_head_fixed
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
#print axioms mFrameLiftEquiv
#print axioms mFrameLiftEquiv_apply
#print axioms mFrameLiftEquiv_head
#print axioms mFrameLiftEquiv_projection
#print axioms mFrameLiftEquiv_orientation
#print axioms mFrameLiftEquiv_coordinate_gen_of_ne
#print axioms mFrameLiftEquiv_coordinate_gen_zero
#print axioms mFrameLiftEquiv_relVec
#print axioms exists_mFrame_freeBasis_lift

end
end GQ2.Dyadic.MarkedCore
