import GQ2.Dyadic.Instances.MpcGeneralTowerStep
import GQ2.Dyadic.SqCore.GradedGammaThreeFour

namespace GQ2.Dyadic.Instances.MpcGeneralTowerBase

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedStages
open GQ2.Dyadic.Instances.MpcGeneralTowerInduction
open GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction
open GQ2.Dyadic.Instances.MpcGeneralTowerStep
open GQ2.Dyadic.SqCore
open GQ2.Roe.Labute

/-- A commutator, inserted in one marked correction coordinate at the cubic base. -/
def mpcGeneralMarkedCommutatorCoordinate (alpha h : ℕ)
    (i : Fin (coreRank h)) (x y : DM alpha h) :
    MpcGeneralMarkedLevelCorrection alpha h 3 := fun j => by
  classical
  by_cases hj : j = i
  · exact ⟨levelMk (DM alpha h) 4 (commP x y),
      (mem_mpcGeneralMarkedCorrectionImage_iff_exists _).mpr
        ⟨commP x y, cfour_commP_mem_two x y,
          map_commP_eq_one (chiM alpha h).toMonoidHom x y,
          fun _ f => map_commP_eq_one f.toMonoidHom x y,
          fun _ => map_commP_eq_one (mpcGeneralDeltaD alpha h).toMonoidHom x y,
          rfl⟩⟩
  · exact ⟨1, Subgroup.one_mem _⟩

/-- Forgetting the marked proof leaves the corresponding raw coordinate correction. -/
theorem mpcGeneralMarkedCommutatorCoordinate_toRaw
    (alpha h : ℕ) (i : Fin (coreRank h)) (x y : DM alpha h) :
    mpcGeneralMarkedLevelToRaw
        (mpcGeneralMarkedCommutatorCoordinate alpha h i x y) =
      evenRawDepthCoordinateCorrection (G := DM alpha h) (h := h) (k := 3) i
        ⟨levelMk (DM alpha h) 4 (commP x y),
          ⟨commP x y, cfour_commP_mem_two x y, rfl⟩⟩ := by
  classical
  apply EvenRawDepthCorrection.ext
  funext j
  by_cases hj : j = i
  · subst j
    simp [mpcGeneralMarkedLevelToRaw, mpcGeneralMarkedCommutatorCoordinate,
      evenRawDepthCoordinateCorrection_apply]
  · simp [mpcGeneralMarkedLevelToRaw, mpcGeneralMarkedCommutatorCoordinate,
      evenRawDepthCoordinateCorrection_apply, hj]

/-- The canonical cubic atom is the ordinary square of its generator. -/
theorem mpcGeneralCanonicalTowerAtom_three (alpha h : ℕ)
    (i : Fin (coreRank h)) :
    mpcGeneralCanonicalTowerAtom alpha h 3 i = dmGen alpha h i ^ 2 := by
  unfold mpcGeneralCanonicalTowerAtom
  norm_num
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, zpowZtwo_natCast]

/-- The two core correction rows at indices zero and one manufacture
`[x,y]^2 * [[x,y],B]`. -/
theorem exists_mpcGeneralMarked_commutatorSquare_B
    (alpha h : ℕ) (x y : DM alpha h) :
    ∃ E : MpcGeneralMarkedLevelCorrection alpha h 3,
      (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega) E).1 =
        levelMk (DM alpha h) 4 (commP x y) ^ 2 *
          commP (levelMk (DM alpha h) 4 (commP x y))
            (levelMk (DM alpha h) 4 (dmB alpha h)) := by
  let E0 := mpcGeneralMarkedCommutatorCoordinate alpha h 0 x y
  let E1 := mpcGeneralMarkedCommutatorCoordinate alpha h 1 x y
  refine ⟨E0 * E1, ?_⟩
  rw [map_mul]
  change ((evenRawDepthShiftHom
      (fun i => levelMk (DM alpha h) 4 (dmGen alpha h i)) (by omega))
        (mpcGeneralMarkedLevelToRaw E0)).1 *
      ((evenRawDepthShiftHom
      (fun i => levelMk (DM alpha h) 4 (dmGen alpha h i)) (by omega))
        (mpcGeneralMarkedLevelToRaw E1)).1 = _
  rw [mpcGeneralMarkedCommutatorCoordinate_toRaw,
    mpcGeneralMarkedCommutatorCoordinate_toRaw,
    evenRawDepthShiftHom_zero_apply, evenRawDepthShiftHom_one_apply]
  change (_ ^ 2 * commP _ (levelMk (DM alpha h) 4 (dmA alpha h)) *
      commP _ (levelMk (DM alpha h) 4 (dmB alpha h))) *
      commP _ (levelMk (DM alpha h) 4 (dmA alpha h)) = _
  let p := levelMk (DM alpha h) 4 (commP x y)
  let zA := commP p (levelMk (DM alpha h) 4 (dmA alpha h))
  let zB := commP p (levelMk (DM alpha h) 4 (dmB alpha h))
  have hp : p ∈ lambdaImage (DM alpha h) 2 4 := by
    change commP (levelMk (DM alpha h) 4 x)
      (levelMk (DM alpha h) 4 y) ∈ lambdaImage (DM alpha h) 2 4
    exact cfour_commP_mem_lambdaTwo _ _
  have hzA : zA ∈ zLayer (DM alpha h) 3 :=
    cfour_commP_mem_zLayer_left hp _
  have hAB : zA * zB = zB * zA := (zLayer_commute hzA zB).eq
  change (p ^ 2 * zA * zB) * zA = p ^ 2 * zB
  calc
    (p ^ 2 * zA * zB) * zA = p ^ 2 * ((zA * zB) * zA) := by group
    _ = p ^ 2 * ((zB * zA) * zA) := by rw [hAB]
    _ = p ^ 2 * (zB * (zA * zA)) := by group
    _ = p ^ 2 * zB := by rw [cfourDef_z_sq hzA, mul_one]

/-- The `B` canonical base bracket is already in the marked range, uniformly in degree and
handle count. -/
theorem mpcGeneralCanonicalTowerBracketBase_B (alpha h : ℕ) :
    (⟨commP
        (levelMk (DM alpha h) 4
          (mpcGeneralCanonicalTowerAtom alpha h 3 1))
        (levelMk (DM alpha h) 4 (dmD alpha h)),
      commP_mem_zLayer 3 (by omega)
        ⟨mpcGeneralCanonicalTowerAtom alpha h 3 1,
          mpcGeneralCanonicalTowerAtom_mem (by omega) 1, rfl⟩ _⟩ :
      zLayer (DM alpha h) 3) ∈
        (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega)).range := by
  obtain ⟨E, hE⟩ := exists_mpcGeneralMarked_commutatorSquare_B alpha h
    (dmB alpha h) (dmD alpha h)
  refine ⟨E, Subtype.ext ?_⟩
  rw [hE]
  change _ = commP
    (levelMk (DM alpha h) 4 (mpcGeneralCanonicalTowerAtom alpha h 3 1))
      (levelMk (DM alpha h) 4 (dmD alpha h))
  rw [mpcGeneralCanonicalTowerAtom_three, map_pow,
    show dmGen alpha h 1 = dmB alpha h from rfl,
    gThreeFour_commP_sq_left]
  rw [show levelMk (DM alpha h) 4 (commP (dmB alpha h) (dmD alpha h)) =
      commP (levelMk (DM alpha h) 4 (dmB alpha h))
        (levelMk (DM alpha h) 4 (dmD alpha h)) by
    simp only [commP, map_mul, map_inv]]

/-- Every triple bracket whose outer generator is not `B` is one literal marked correction
row. -/
theorem exists_mpcGeneralMarked_triple_of_ne_B
    (alpha h : ℕ) (x y : DM alpha h) (i : Fin (coreRank h)) (hi : i ≠ 1) :
    ∃ E : MpcGeneralMarkedLevelCorrection alpha h 3,
      (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega) E).1 =
        commP (levelMk (DM alpha h) 4 (commP x y))
          (levelMk (DM alpha h) 4 (dmGen alpha h i)) := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨l, rfl⟩
  · refine ⟨mpcGeneralMarkedCommutatorCoordinate alpha h 1 x y, ?_⟩
    change ((evenRawDepthShiftHom
      (fun j => levelMk (DM alpha h) 4 (dmGen alpha h j)) (by omega))
        (mpcGeneralMarkedLevelToRaw
          (mpcGeneralMarkedCommutatorCoordinate alpha h 1 x y))).1 = _
    rw [mpcGeneralMarkedCommutatorCoordinate_toRaw,
      evenRawDepthShiftHom_one_apply]
  · exact (hi rfl).elim
  · refine ⟨mpcGeneralMarkedCommutatorCoordinate alpha h 3 x y, ?_⟩
    change ((evenRawDepthShiftHom
      (fun j => levelMk (DM alpha h) 4 (dmGen alpha h j)) (by omega))
        (mpcGeneralMarkedLevelToRaw
          (mpcGeneralMarkedCommutatorCoordinate alpha h 3 x y))).1 = _
    rw [mpcGeneralMarkedCommutatorCoordinate_toRaw,
      evenRawDepthShiftHom_three_apply]
  · refine ⟨mpcGeneralMarkedCommutatorCoordinate alpha h 2 x y, ?_⟩
    change ((evenRawDepthShiftHom
      (fun j => levelMk (DM alpha h) 4 (dmGen alpha h j)) (by omega))
        (mpcGeneralMarkedLevelToRaw
          (mpcGeneralMarkedCommutatorCoordinate alpha h 2 x y))).1 = _
    rw [mpcGeneralMarkedCommutatorCoordinate_toRaw,
      evenRawDepthShiftHom_two_apply]
  · rcases mHandleCoord_cases l with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨mpcGeneralMarkedCommutatorCoordinate alpha h (handleIdxV j) x y, ?_⟩
      change ((evenRawDepthShiftHom
        (fun l => levelMk (DM alpha h) 4 (dmGen alpha h l)) (by omega))
          (mpcGeneralMarkedLevelToRaw
            (mpcGeneralMarkedCommutatorCoordinate alpha h (handleIdxV j) x y))).1 = _
      rw [mpcGeneralMarkedCommutatorCoordinate_toRaw,
        evenRawDepthShiftHom_handleV_apply]
      rw [mHandleIdx_coordU]
    · refine ⟨mpcGeneralMarkedCommutatorCoordinate alpha h (handleIdxU j) x y, ?_⟩
      change ((evenRawDepthShiftHom
        (fun l => levelMk (DM alpha h) 4 (dmGen alpha h l)) (by omega))
          (mpcGeneralMarkedLevelToRaw
            (mpcGeneralMarkedCommutatorCoordinate alpha h (handleIdxU j) x y))).1 = _
      rw [mpcGeneralMarkedCommutatorCoordinate_toRaw,
        evenRawDepthShiftHom_handleU_apply]
      rw [mHandleIdx_coordV]

/-- Every active canonical cubic bracket lies in the marked range.  The proof is one
parameterized Jacobi calculation, not a list of ranks or nilpotency classes. -/
theorem mpcGeneralCanonicalTowerBracketBase (alpha h : ℕ) :
    MpcGeneralCanonicalTowerBracketBase alpha h := by
  intro i hi
  by_cases hiB : i = 1
  · subst i
    exact mpcGeneralCanonicalTowerBracketBase_B alpha h
  let g := dmGen alpha h i
  let B := dmB alpha h
  let D := dmD alpha h
  obtain ⟨Ebase, hbase⟩ := exists_mpcGeneralMarked_commutatorSquare_B alpha h g D
  obtain ⟨Eg, hg⟩ := exists_mpcGeneralMarked_triple_of_ne_B alpha h g D i hiB
  obtain ⟨Edbg, hdbg⟩ := exists_mpcGeneralMarked_triple_of_ne_B alpha h D B i hiB
  obtain ⟨Ebgd, hbgd⟩ := exists_mpcGeneralMarked_triple_of_ne_B alpha h B g 3 (by
    intro H
    have hv := congrArg Fin.val H
    rw [coreVal_three, coreVal_one] at hv
    omega)
  refine ⟨Ebase * Eg * Edbg * Ebgd, ?_⟩
  apply Subtype.ext
  rw [map_mul, map_mul, map_mul]
  change
    (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega) Ebase).1 *
      (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega) Eg).1 *
      (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega) Edbg).1 *
      (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega) Ebgd).1 = _
  rw [hbase, hg, hdbg, hbgd]
  let gq := levelMk (DM alpha h) 4 g
  let Bq := levelMk (DM alpha h) 4 B
  let Dq := levelMk (DM alpha h) 4 D
  let p := commP gq Dq
  let zB := commP p Bq
  let zg := commP p gq
  let zDBg := commP (commP Dq Bq) gq
  let zBgD := commP (commP Bq gq) Dq
  have hpmap : levelMk (DM alpha h) 4 (commP g D) = p := by
    simp only [p, gq, Dq, commP, map_mul, map_inv]
  have hDBmap : levelMk (DM alpha h) 4 (commP D B) = commP Dq Bq := by
    simp only [Dq, Bq, commP, map_mul, map_inv]
  have hBgmap : levelMk (DM alpha h) 4 (commP B g) = commP Bq gq := by
    simp only [Bq, gq, commP, map_mul, map_inv]
  rw [hpmap, hDBmap, hBgmap]
  have hzg : zg ∈ zLayer (DM alpha h) 3 := gThreeFour_triple_mem _ _ _
  have hzB : zB ∈ zLayer (DM alpha h) 3 := gThreeFour_triple_mem _ _ _
  have hcomm : zB * zg = zg * zB := (zLayer_commute hzB zg).eq
  have hjac : zB * zDBg * zBgD = 1 := gThreeFour_jacobi gq Dq Bq
  change ((p ^ 2 * zB) * zg * zDBg) * zBgD = _
  calc
    ((p ^ 2 * zB) * zg * zDBg) * zBgD =
        p ^ 2 * (zB * zg) * (zDBg * zBgD) := by group
    _ = p ^ 2 * (zg * zB) * (zDBg * zBgD) := by rw [hcomm]
    _ = p ^ 2 * zg * (zB * zDBg * zBgD) := by group
    _ = p ^ 2 * zg := by rw [hjac, mul_one]
    _ = commP (gq ^ 2) Dq := (gThreeFour_commP_sq_left gq Dq).symm
    _ = commP
        (levelMk (DM alpha h) 4
          (mpcGeneralCanonicalTowerAtom alpha h 3 i))
        (levelMk (DM alpha h) 4 (dmD alpha h)) := by
      rw [mpcGeneralCanonicalTowerAtom_three, map_pow]

/-- The general Mpc pivot shift follows in every degree and handle count. -/
theorem mpcPivShiftH_general (alpha h : ℕ) (halpha : 2 ≤ alpha) :
    GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalTowerBase halpha
    (mpcGeneralCanonicalTowerBracketBase alpha h)

end

end GQ2.Dyadic.Instances.MpcGeneralTowerBase

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralTowerBase

#print axioms mpcGeneralMarkedCommutatorCoordinate
#print axioms mpcGeneralMarkedCommutatorCoordinate_toRaw
#print axioms mpcGeneralCanonicalTowerAtom_three
#print axioms exists_mpcGeneralMarked_commutatorSquare_B
#print axioms mpcGeneralCanonicalTowerBracketBase_B
#print axioms exists_mpcGeneralMarked_triple_of_ne_B
#print axioms mpcGeneralCanonicalTowerBracketBase
#print axioms mpcPivShiftH_general

end AxiomPins
