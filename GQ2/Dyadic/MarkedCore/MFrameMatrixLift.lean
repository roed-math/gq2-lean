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

#print axioms mFrameFreeProjection
#print axioms mFrameFreeProjection_gen
#print axioms mFrameFreeProjection_surjective
#print axioms mFrameFreeOrientation
#print axioms mFrameFreeOrientation_gen
#print axioms mFrameFreeProjection_orientation
#print axioms mFrameFreeOrientation_coordinate

end
end GQ2.Dyadic.MarkedCore
