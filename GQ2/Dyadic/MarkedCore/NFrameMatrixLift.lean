import GQ2.Dyadic.MarkedCore.FreeProTwoMatrixBasis
import GQ2.Dyadic.MarkedCore.NFrameExists
import GQ2.Dyadic.MarkedCore.NPlaneFreeStageTransfer

/-!
# Actual full N-frame automorphisms lifted to free bases

The canonical section of the frame coordinates chooses zero or one for the
torsion coordinate and retains every integral coordinate. Its generator words
form a genuine free pro-two basis: each index-two character factors through
the N frame, and the supplied frame automorphism is surjective.

This is a free-basis lift, not a relator-preserving automorphism of D_N.
No cup or depth-three relator condition is assumed or asserted here.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative
open scoped GQ2.SectionThree.TopAbInstances

def freeNAbProjection (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      (topAbelianization (DN α h : Type)) :=
  (⟨abMk, continuous_abMk⟩ : ContinuousMonoidHom (DN α h : Type) _).comp
    (freeNProjection α h)

theorem freeNAbProjection_gen (α h : ℕ) (i : Fin (coreRank h)) :
    freeNAbProjection α h (freeTwoRankGen (coreRank h) i) = abMk (dnGen α h i) := by
  exact congrArg abMk (freeNProjection_gen α h i)

theorem freeNAbProjection_coordinateWord (α h : ℕ) (a : Fin (coreRank h) → ℤ_[2]) :
    freeNAbProjection α h (freeTwoCoordinateWord (coreRank h) a) = nAbWord α h a := by
  rw [freeTwoCoordinateWord, map_list_prod, List.map_ofFn, Fin.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  change freeNAbProjection α h (zpowZtwo (isProP_presPro2 1)
    (freeTwoRankGen (coreRank h) i) (a i)) = _
  rw [map_zpowZtwo (isProP_presPro2 1) (nIsProP_two_topAb_DN α h), freeNAbProjection_gen]

def freeNFrameProjection {α : ℕ} (ha : 2 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (NFrameModel h) :=
  (⟨(nFrameExists_phiEquiv ha h).toMulEquiv.toMonoidHom,
    (nFrameExists_phiEquiv ha h).continuous_toFun⟩ : ContinuousMonoidHom _ _).comp
    (freeNAbProjection α h)

theorem freeNFrameProjection_gen {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (i : Fin (coreRank h)) :
    freeNFrameProjection ha h (freeTwoRankGen (coreRank h) i) =
      nPhiHom ha h (abMk (dnGen α h i)) := by
  change nPhiHom ha h (freeNAbProjection α h (freeTwoRankGen (coreRank h) i)) = _
  rw [freeNAbProjection_gen]

theorem freeNFrameProjection_surjective {α : ℕ} (ha : 2 ≤ α) (h : ℕ) :
    Function.Surjective (freeNFrameProjection ha h) :=
  (nFrameExists_phiEquiv ha h).surjective.comp
    (abMk_surjective.comp (freeNProjection_surjective α h))

/-- The actual canonical orientation transported to the full frame. -/
def nFrameOrientation {α : ℕ} (ha : 2 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (NFrameModel h) ℤ_[2]ˣ :=
  (abLiftG (chiN α h)).comp
    ⟨(nFrameExists_phiEquiv ha h).symm.toMulEquiv.toMonoidHom,
      (nFrameExists_phiEquiv ha h).symm.continuous_toFun⟩

theorem nFrameOrientation_projection {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (x : FreeTwoRank (coreRank h)) :
    nFrameOrientation ha h (freeNFrameProjection ha h x) = freeNOrientation α h x := by
  change abLiftG (chiN α h) ((nFrameExists_phiEquiv ha h).symm
    (nFrameExists_phiEquiv ha h (abMk (freeNProjection α h x)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, abLiftG_abMk, freeNProjection_orientation]

def nFrameCoordinateSection {h : ℕ} (z : NFrameModel h) : Fin (coreRank h) → ℤ_[2] :=
  nSurjVec z.toAdd.1 z.toAdd.2.1 z.toAdd.2.2.1 z.toAdd.2.2.2.1 z.toAdd.2.2.2.2

theorem nPhiHom_coordinateSection {α : ℕ} (ha : 2 ≤ α) (h : ℕ) (z : NFrameModel h) :
    nPhiHom ha h (nAbWord α h (nFrameCoordinateSection z)) = z := by
  rw [← ofAdd_toAdd z]
  obtain ⟨a, b, c, d, f⟩ := z.toAdd
  change nPhiHom ha h (nAbWord α h (nSurjVec a b c d f)) = ofAdd (a,b,c,d,f)
  rw [nPhiHom_word, nSurjVec_zero, nSurjVec_one, nSurjVec_two, nSurjVec_three]
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))))
  · rw [zpowZtwo_ofAdd_one_zmod2, toAdd_ofAdd]
  · exact nSurjVec_handle a b c d f k

/-- The transported actual orientation is precisely nUnit to the integral
b-coordinate. Thus its preservation is the usual marked orientation clause. -/
theorem nFrameOrientation_apply {α : ℕ} (ha : 2 ≤ α) (h : ℕ) (z : NFrameModel h) :
    nFrameOrientation ha h z = zpowZtwo isProP_two_unitsPadicInt (nUnit α) z.toAdd.2.1 := by
  have hp : freeNFrameProjection ha h
      (freeTwoCoordinateWord (coreRank h) (nFrameCoordinateSection z)) = z := by
    change nPhiHom ha h (freeNAbProjection α h
      (freeTwoCoordinateWord (coreRank h) (nFrameCoordinateSection z))) = z
    rw [freeNAbProjection_coordinateWord]
    exact nPhiHom_coordinateSection ha h z
  calc
    nFrameOrientation ha h z = nFrameOrientation ha h (freeNFrameProjection ha h
        (freeTwoCoordinateWord (coreRank h) (nFrameCoordinateSection z))) := congrArg _ hp.symm
    _ = freeNOrientation α h (freeTwoCoordinateWord (coreRank h) (nFrameCoordinateSection z)) :=
      nFrameOrientation_projection ha h _
    _ = zpowZtwo isProP_two_unitsPadicInt (nUnit α) ((nFrameCoordinateSection z) 1) := by
      rw [freeNOrientation_coordinate, freeTwoCoordinateWord_coordinate]
    _ = _ := by rw [nFrameCoordinateSection, nSurjVec_one]

theorem nFrameOrientation_preserved_iff {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    (∀ z, nFrameOrientation ha h (φ z) = nFrameOrientation ha h z) ↔
      ∀ z, (φ z).toAdd.2.1 = z.toAdd.2.1 := by
  simp only [nFrameOrientation_apply]
  exact ⟨fun hh z => nUnit_zpowZtwo_injective ha (hh z),
    fun hh z => congrArg _ (hh z)⟩

def nFrameLiftMatrix {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2] :=
  fun j i => nFrameCoordinateSection
    (φ (freeNFrameProjection ha h (freeTwoRankGen (coreRank h) i))) j

def nFrameLiftHom {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  freeTwoMatrixHom (coreRank h) (nFrameLiftMatrix ha h φ)

theorem nFrameLiftHom_projection_gen {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) (i : Fin (coreRank h)) :
    freeNFrameProjection ha h (nFrameLiftHom ha h φ (freeTwoRankGen (coreRank h) i)) =
      φ (freeNFrameProjection ha h (freeTwoRankGen (coreRank h) i)) := by
  change nPhiHom ha h (freeNAbProjection α h
    (freeTwoMatrixHom (coreRank h) (nFrameLiftMatrix ha h φ) (freeTwoRankGen (coreRank h) i))) = _
  rw [freeTwoMatrixHom_gen, freeNAbProjection_coordinateWord]
  exact nPhiHom_coordinateSection ha h _

set_option synthInstance.maxSize 256 in
theorem nFrameLiftHom_projection {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (x : FreeTwoRank (coreRank h)) :
    freeNFrameProjection ha h (nFrameLiftHom ha h φ x) = φ (freeNFrameProjection ha h x) := by
  have he : (freeNFrameProjection ha h).comp (nFrameLiftHom ha h φ) =
      (autHom φ).comp (freeNFrameProjection ha h) := by
    apply presPro2_hom_ext
    exact nFrameLiftHom_projection_gen ha h φ
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

theorem nFrameLiftHom_surjective {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    Function.Surjective (nFrameLiftHom ha h φ) := by
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
  have hrel : (q (freeTwoRankGen (coreRank h) 0)) ^ (2 + 2^α) = 1 := by
    have hs : q (freeTwoRankGen (coreRank h) 0) ^ 2 = 1 := by
      rw [← hc]
      exact pow_card_eq_one'
    obtain ⟨r, hr⟩ : ∃ r, α = r+1 := ⟨α-1, by omega⟩
    rw [hr, show 2+2^(r+1) = 2*(1+2^r) by ring, pow_mul, hs, one_pow]
  let qAb := nCoordHom α h hQ (fun i => q (freeTwoRankGen (coreRank h) i)) hrel
  let qFrame := qAb.comp
    (⟨(nFrameExists_phiEquiv ha h).symm.toMulEquiv.toMonoidHom,
      (nFrameExists_phiEquiv ha h).symm.continuous_toFun⟩ : ContinuousMonoidHom _ _)
  have hfactor : qFrame.comp (freeNFrameProjection ha h) = q := by
    apply presPro2_hom_ext
    intro i
    change qAb ((nFrameExists_phiEquiv ha h).symm
      (nFrameExists_phiEquiv ha h (freeNAbProjection α h (freeTwoRankGen (coreRank h) i)))) = _
    rw [ContinuousMulEquiv.symm_apply_apply, freeNAbProjection_gen]
    exact nCoordHom_gen α h hQ _ hrel i
  have hf (x : FreeTwoRank (coreRank h)) : qFrame (freeNFrameProjection ha h x) = q x :=
    congrArg (fun f : ContinuousMonoidHom _ _ => f x) hfactor
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
  obtain ⟨y, hy⟩ := freeNFrameProjection_surjective ha h (φ.symm (freeNFrameProjection ha h x))
  refine ⟨y, ?_⟩
  change q (nFrameLiftHom ha h φ y) = q x
  rw [← hf, nFrameLiftHom_projection, hy, φ.apply_symm_apply, hf]

private theorem nFrameLift_topGen (h : ℕ) :
    ∃ s : Finset (FreeTwoRank (coreRank h) : Type),
      (Subgroup.closure (s : Set (FreeTwoRank (coreRank h) : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (freeTwoRankGen (coreRank h)), ?_⟩
  have hs : (↑(Finset.univ.image (freeTwoRankGen (coreRank h))) :
      Set (FreeTwoRank (coreRank h) : Type)) = Set.range (freeTwoRankGen (coreRank h)) := by simp
  rw [hs]
  exact presPro2_topGen _

def nFrameLiftEquiv {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type) (FreeTwoRank (coreRank h) : Type) :=
  continuousMulEquivOfBijective (nFrameLiftHom ha h φ)
    ⟨profinite_hopfian (nFrameLift_topGen h) _ (nFrameLiftHom_surjective ha h φ),
      nFrameLiftHom_surjective ha h φ⟩

theorem nFrameLiftEquiv_projection {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) (x : FreeTwoRank (coreRank h)) :
    freeNFrameProjection ha h (nFrameLiftEquiv ha h φ x) = φ (freeNFrameProjection ha h x) :=
  nFrameLiftHom_projection ha h φ x

theorem nFrameLiftEquiv_coordinate_gen {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) (j i : Fin (coreRank h)) :
    toAdd (freeTwoCoordinate (coreRank h) j
      (nFrameLiftEquiv ha h φ (freeTwoRankGen (coreRank h) i))) = nFrameLiftMatrix ha h φ j i :=
  freeTwoMatrixHom_coordinate_gen (coreRank h) (nFrameLiftMatrix ha h φ) j i

theorem nFrameLiftEquiv_orientation {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (hχ : ∀ z, nFrameOrientation ha h (φ z) = nFrameOrientation ha h z)
    (x : FreeTwoRank (coreRank h)) :
    freeNOrientation α h (nFrameLiftEquiv ha h φ x) = freeNOrientation α h x := by
  rw [← nFrameOrientation_projection ha h, nFrameLiftEquiv_projection, hχ,
    nFrameOrientation_projection]

theorem nFrameCoordinateSection_torsion (h : ℕ) (j : Fin (coreRank h)) :
    nFrameCoordinateSection (ofAdd (1,0,0,0,(0 : Fin (2*h) → ℤ_[2])) : NFrameModel h) j =
      if j = 0 then 1 else 0 := by
  have hj : (j : ℕ) = 0 ↔ j = 0 := by
    rw [← coreVal_zero h]
    exact Fin.val_injective.eq_iff
  norm_num [nFrameCoordinateSection, nSurjVec, hj, ZMod.val_one_eq_one_mod]

theorem nFrameLiftMatrix_column_zero {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) (j : Fin (coreRank h)) :
    nFrameLiftMatrix ha h φ j 0 = if j = 0 then 1 else 0 := by
  have ht : freeNFrameProjection ha h (freeTwoRankGen (coreRank h) 0) =
      (ofAdd (1,0,0,0,(0 : Fin (2*h) → ℤ_[2])) : NFrameModel h) := by
    rw [freeNFrameProjection_gen]
    exact nPhiHom_X0 ha h
  have hφ : φ (ofAdd (1,0,0,0,(0 : Fin (2*h) → ℤ_[2]))) = ofAdd (1,0,0,0,0) :=
    nFrameModel_map_t φ.toMulEquiv
  rw [nFrameLiftMatrix, ht, hφ, nFrameCoordinateSection_torsion]

/-- The actual marked head is fixed literally, before taking any quotient. -/
theorem nFrameLiftEquiv_gen_zero {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    nFrameLiftEquiv ha h φ (freeTwoRankGen (coreRank h) 0) = freeTwoRankGen (coreRank h) 0 := by
  change freeTwoMatrixHom (coreRank h) (nFrameLiftMatrix ha h φ)
    (freeTwoRankGen (coreRank h) 0) = _
  rw [freeTwoMatrixHom_gen]
  simp only [nFrameLiftMatrix_column_zero]
  exact freeTwoCoordinateWord_basis (coreRank h) 0

theorem nFrameLiftMatrix_row_one {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (hχ : ∀ z, nFrameOrientation ha h (φ z) = nFrameOrientation ha h z)
    (i : Fin (coreRank h)) :
    nFrameLiftMatrix ha h φ 1 i = if i = 1 then 1 else 0 := by
  have hc := nFrameLiftEquiv_orientation ha h φ hχ (freeTwoRankGen (coreRank h) i)
  rw [freeNOrientation_coordinate, freeNOrientation_coordinate,
    nFrameLiftEquiv_coordinate_gen, freeTwoCoordinate_gen, toAdd_ofAdd] at hc
  exact nUnit_zpowZtwo_injective ha hc

def nFrameLiftInverseMatrix {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2] := fun j i =>
  toAdd (freeTwoCoordinate (coreRank h) j
    ((nFrameLiftEquiv ha h φ).symm (freeTwoRankGen (coreRank h) i)))

theorem nFrameLiftMatrix_mul_inverse {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    nFrameLiftMatrix ha h φ * nFrameLiftInverseMatrix ha h φ = 1 := by
  refine Matrix.ext fun j i => ?_
  have hc := freeTwoMatrixHom_coordinate (coreRank h) (nFrameLiftMatrix ha h φ)
    ((nFrameLiftEquiv ha h φ).symm (freeTwoRankGen (coreRank h) i)) j
  change toAdd (freeTwoCoordinate (coreRank h) j
    (nFrameLiftEquiv ha h φ ((nFrameLiftEquiv ha h φ).symm (freeTwoRankGen (coreRank h) i)))) = _ at hc
  rw [ContinuousMulEquiv.apply_symm_apply, freeTwoCoordinate_gen, toAdd_ofAdd] at hc
  simpa only [Matrix.mul_apply, nFrameLiftInverseMatrix, Matrix.one_apply, eq_comm] using hc.symm

theorem nFrameLiftMatrix_inverse_mul {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    nFrameLiftInverseMatrix ha h φ * nFrameLiftMatrix ha h φ = 1 := by
  exact mul_eq_one_comm.mp (nFrameLiftMatrix_mul_inverse ha h φ)

theorem nFrameLiftMatrix_isUnit_det {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    IsUnit (nFrameLiftMatrix ha h φ).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  exact ⟨⟨nFrameLiftMatrix ha h φ, nFrameLiftInverseMatrix ha h φ,
    nFrameLiftMatrix_mul_inverse ha h φ, nFrameLiftMatrix_inverse_mul ha h φ⟩, rfl⟩

/-- An actual frame automorphism preserving the canonical orientation has a
free-basis lift fixing the marked torsion generator literally and realizing
every full frame column, including torsion and arbitrary handle mixing. -/
theorem exists_nFrame_freeBasis_lift {α : ℕ} (ha : 2 ≤ α) (h : ℕ)
    (φ : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (hχ : ∀ z, nFrameOrientation ha h (φ z) = nFrameOrientation ha h z) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
        (FreeTwoRank (coreRank h) : Type),
      e (freeTwoRankGen (coreRank h) 0) = freeTwoRankGen (coreRank h) 0 ∧
      (∀ x, freeNOrientation α h (e x) = freeNOrientation α h x) ∧
      (∀ x, freeNFrameProjection ha h (e x) = φ (freeNFrameProjection ha h x)) ∧
      ∀ j i, toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) i))) =
        nFrameLiftMatrix ha h φ j i :=
  ⟨nFrameLiftEquiv ha h φ, nFrameLiftEquiv_gen_zero ha h φ,
    nFrameLiftEquiv_orientation ha h φ hχ, nFrameLiftEquiv_projection ha h φ,
    nFrameLiftEquiv_coordinate_gen ha h φ⟩

#print axioms freeNAbProjection
#print axioms freeNAbProjection_gen
#print axioms freeNAbProjection_coordinateWord
#print axioms freeNFrameProjection
#print axioms freeNFrameProjection_gen
#print axioms freeNFrameProjection_surjective
#print axioms nFrameOrientation
#print axioms nFrameOrientation_projection
#print axioms nFrameCoordinateSection
#print axioms nPhiHom_coordinateSection
#print axioms nFrameOrientation_apply
#print axioms nFrameOrientation_preserved_iff
#print axioms nFrameLiftMatrix
#print axioms nFrameLiftHom
#print axioms nFrameLiftHom_projection_gen
#print axioms nFrameLiftHom_projection
#print axioms nFrameLiftHom_surjective
#print axioms nFrameLiftEquiv
#print axioms nFrameLiftEquiv_projection
#print axioms nFrameLiftEquiv_coordinate_gen
#print axioms nFrameLiftEquiv_orientation
#print axioms nFrameCoordinateSection_torsion
#print axioms nFrameLiftMatrix_column_zero
#print axioms nFrameLiftEquiv_gen_zero
#print axioms nFrameLiftMatrix_row_one
#print axioms nFrameLiftInverseMatrix
#print axioms nFrameLiftMatrix_mul_inverse
#print axioms nFrameLiftMatrix_inverse_mul
#print axioms nFrameLiftMatrix_isUnit_det
#print axioms exists_nFrame_freeBasis_lift

end
end GQ2.Dyadic.MarkedCore
