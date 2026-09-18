import GQ2.Dyadic.MarkedCore.FreeProTwoModTwoCharacters
import GQ2.Dyadic.MarkedCore.FreeProTwoMatrixBasis
import GQ2.Dyadic.Instances.DNAutomorphismCup
import GQ2.Roe.Labute.SpanFoundation

/-!
# Exact degree-two coordinates and the initial N-relator error

The central layer in the quotient by lambda-three is elementary abelian.
The lemmas here compute actual commutators, rather than only proving that
they belong to the span of generator commutators. Symmetric coefficient
contraction then proves that full cup preservation fixes the complete
commutator tail. If the actual head element is fixed, the literal N-relator
error lies in lambda-three, uniformly in the rank and exponent. The final
corollary applies to the actual free-basis automorphism from an invertible
integral column matrix, with the precise variance `Abar G Abarᵀ = G`.

This is only the initial-depth step. It does not assert the subsequent
filtered correction or the final arbitrary-frame automorphism lift.
-/

namespace GQ2.Dyadic.MarkedCore.NInitialCupDepth

open GQ2 Multiplicative GQ2.Roe GQ2.Roe.Labute
open GQ2.Dyadic.Instances.DNAutomorphismCup

noncomputable section

section Layer
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

abbrev layerTwoCommGroup : CommGroup (zLayer G 2) :=
  { (inferInstance : Group (zLayer G 2)) with
    mul_comm := fun x y => Subtype.ext ((zLayer_commute x.property y.val).eq) }

attribute [local instance] layerTwoCommGroup

abbrev layerTwoModule : Module (ZMod 2) (Additive (zLayer G 2)) :=
  AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa using zLayer_sq G x.toMul.property)

attribute [local instance] layerTwoModule

def bracket (p q : levelQuot G 3) : Additive (zLayer G 2) :=
  Additive.ofMul ⟨commP p q, commP_mem_zLayer_two p q⟩

theorem bracket_mul_left (p q r : levelQuot G 3) :
    bracket G (p*q) r = bracket G p r + bracket G q r := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change commP (p*q) r = commP p r * commP q r
  exact commP_mul_left_of_three p q r

theorem bracket_mul_right (p q r : levelQuot G 3) :
    bracket G p (q*r) = bracket G p q + bracket G p r := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change commP p (q*r) = commP p q * commP p r
  rw [commP_mul_right_of_three]
  exact (zLayer_commute (commP_mem_zLayer_two p r) (commP p q)).eq

@[simp] theorem bracket_self (p : levelQuot G 3) : bracket G p p = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [bracket, commP]

theorem bracket_symm (p q : levelQuot G 3) : bracket G p q = bracket G q p := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change commP p q = commP q p
  have hz := zLayer_sq G (commP_mem_zLayer_two p q)
  have hi : (commP p q)⁻¹ = commP p q := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hz
  have hs : commP q p = (commP p q)⁻¹ := by simp only [commP]; group
  rw [hs, hi]

def bracketLeftHom (q : levelQuot G 3) : levelQuot G 3 →* zLayer G 2 where
  toFun p := (bracket G p q).toMul
  map_one' := Subtype.ext (by simp [bracket, commP])
  map_mul' p r := congrArg Additive.toMul (bracket_mul_left G p r q)

def bracketRightHom (p : levelQuot G 3) : levelQuot G 3 →* zLayer G 2 where
  toFun q := (bracket G p q).toMul
  map_one' := Subtype.ext (by simp [bracket, commP])
  map_mul' q r := congrArg Additive.toMul (bracket_mul_right G p q r)

theorem bracket_list_prod_left (L : List (levelQuot G 3)) (q : levelQuot G 3) :
    bracket G L.prod q = (L.map (fun p => bracket G p q)).sum := by
  have hh := (bracketLeftHom G q).map_list_prod L
  exact congrArg Additive.ofMul hh

theorem bracket_list_prod_right (p : levelQuot G 3) (L : List (levelQuot G 3)) :
    bracket G p L.prod = (L.map (fun q => bracket G p q)).sum := by
  have hh := (bracketRightHom G p).map_list_prod L
  exact congrArg Additive.ofMul hh

end Layer

attribute [local instance] layerTwoCommGroup layerTwoModule

section Coordinates
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]

local instance : T2Space (Multiplicative V) := inferInstanceAs (T2Space V)

private def expTwoCoordinateHom (n : ℕ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative V)) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative V) where
  toFun x := ofAdd (∑ i, nRed (toAdd (freeTwoCoordinate n i x)) •
    toAdd (f (freeTwoRankGen n i)))
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul, map_add, add_smul, Finset.sum_add_distrib, ofAdd_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_finsetSum _ fun i _ =>
    (continuous_of_discreteTopology (f := fun a : ZMod 2 =>
      a • toAdd (f (freeTwoRankGen n i)))).comp
        (continuous_nRed.comp (continuous_toAdd.comp (freeTwoCoordinate n i).continuous)))

/-- Any continuous hom into a Hausdorff F2-module is exactly given by the
reduced ordinary coordinates. No finite-target or pro-two-target premise. -/
theorem expTwo_character_coordinates (n : ℕ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative V))
    (x : FreeTwoRank n) :
    toAdd (f x) = ∑ i, nRed (toAdd (freeTwoCoordinate n i x)) •
      toAdd (f (freeTwoRankGen n i)) := by
  have he : f = expTwoCoordinateHom n f := by
    apply presPro2_hom_ext
    intro i
    change f (freeTwoRankGen n i) = ofAdd (∑ j,
      nRed (toAdd (freeTwoCoordinate n j (freeTwoRankGen n i))) •
        toAdd (f (freeTwoRankGen n j)))
    simp [freeTwoCoordinate_gen]
  exact congrArg (fun g : ContinuousMonoidHom _ _ => toAdd (g x)) he

end Coordinates

section FreeBracket
variable (n : ℕ)

local instance freeLevelThreeClosed :
    IsClosed (twoCentralSeries (FreeTwoRank n : Type) 3 : Set (FreeTwoRank n : Type)) :=
  isClosed_twoCentralSeries _ _

abbrev FreeLayerTwo := Additive (zLayer (FreeTwoRank n : Type) 2)

local instance : T2Space (FreeLayerTwo n) := by
  letI : IsClosed (twoCentralSeries (FreeTwoRank n : Type) 3 : Set (FreeTwoRank n : Type)) :=
    isClosed_twoCentralSeries _ _
  letI : T2Space (levelQuot (FreeTwoRank n : Type) 3) := inferInstance
  exact inferInstanceAs (T2Space (zLayer (FreeTwoRank n : Type) 2))

def freeBracket (x y : FreeTwoRank n) : FreeLayerTwo n :=
  bracket (FreeTwoRank n : Type) (levelMk _ 3 x) (levelMk _ 3 y)

private def freeBracketLeftChar (y : FreeTwoRank n) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative (FreeLayerTwo n)) where
  toFun x := ofAdd (freeBracket n x y)
  map_one' := by
    change freeBracket n 1 y = 0
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [freeBracket, bracket, commP]
  map_mul' x z := by
    change bracket _ (levelMk _ 3 (x*z)) _ =
      bracket _ (levelMk _ 3 x) _ + bracket _ (levelMk _ 3 z) _
    rw [map_mul, bracket_mul_left]
  continuous_toFun := by
    apply continuous_ofAdd.comp
    apply continuous_ofMul.comp
    apply Continuous.subtype_mk
    change Continuous (fun x => commP (levelMk (FreeTwoRank n : Type) 3 x) _)
    have hcont := continuous_levelMk (FreeTwoRank n : Type) 3
    simp only [commP]
    fun_prop

theorem freeBracket_left_coordinates (x y : FreeTwoRank n) :
    freeBracket n x y = ∑ i, nRed (toAdd (freeTwoCoordinate n i x)) •
      freeBracket n (freeTwoRankGen n i) y :=
  expTwo_character_coordinates n (freeBracketLeftChar n y) x

theorem freeBracket_right_coordinates (x y : FreeTwoRank n) :
    freeBracket n x y = ∑ j, nRed (toAdd (freeTwoCoordinate n j y)) •
      freeBracket n x (freeTwoRankGen n j) := by
  have hs (u v : FreeTwoRank n) : freeBracket n u v = freeBracket n v u :=
    bracket_symm _ _ _
  rw [hs x y, freeBracket_left_coordinates]
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]

/-- Actual arbitrary-rank double-coordinate expansion of a commutator in
lambda-two modulo lambda-three. -/
theorem freeBracket_coordinates (x y : FreeTwoRank n) :
    freeBracket n x y = ∑ i, ∑ j,
      (nRed (toAdd (freeTwoCoordinate n i x)) *
       nRed (toAdd (freeTwoCoordinate n j y))) •
        freeBracket n (freeTwoRankGen n i) (freeTwoRankGen n j) := by
  rw [freeBracket_left_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [freeBracket_right_coordinates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul]

end FreeBracket

section AlternatingContraction
variable {I V : Type} [Fintype I]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- A symmetric coefficient matrix contracts to zero against an alternating
characteristic-two pairing. This is a uniform finite-sum identity. -/
theorem symmetric_contraction_eq_zero
    (D : I → I → ZMod 2) (b : I → I → V)
    (hD : ∀ i j, D i j = D j i)
    (hb : ∀ i j, b i j = b j i) (hdiag : ∀ i, b i i = 0) :
    (∑ i, ∑ j, D i j • b i j) = 0 := by
  rw [← Fintype.sum_prod_type (fun p : I × I => D p.1 p.2 • b p.1 p.2)]
  apply Finset.sum_ninvolution Prod.swap
  · intro a
    rcases a with ⟨i,j⟩
    change D i j • b i j + D j i • b j i = 0
    rw [← hD i j, ← hb i j, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  · intro a ha he
    have hij : a.2 = a.1 := congrArg Prod.fst he
    apply ha
    simp [hij, hdiag]
  · intro a
    simp
  · intro a
    rfl

end AlternatingContraction

section CupContraction
open GQ2.Dyadic.EvenModel

def tailCoefficient {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) : ZMod 2 :=
  v 0 * w 1 + v 2 * w 3 + ∑ j, v (handleIdxU j) * w (handleIdxV j)

theorem evenCupForm_eq_tailCoefficient {h : ℕ}
    (v w : Fin (coreRank h) → ZMod 2) :
    evenCupForm v w = v 0 * w 0 + tailCoefficient v w + tailCoefficient w v := by
  simp only [evenCupForm, tailCoefficient, Finset.sum_add_distrib]
  have hs : (∑ j, v (handleIdxV j) * w (handleIdxU j)) =
      ∑ j, w (handleIdxU j) * v (handleIdxV j) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hs]
  ring

theorem tailCoefficient_contraction_eq_of_cup {h : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V]
    (A B : Fin (coreRank h) → Fin (coreRank h) → ZMod 2)
    (b : Fin (coreRank h) → Fin (coreRank h) → V)
    (hb : ∀ i j, b i j = b j i) (hdiag : ∀ i, b i i = 0)
    (hhead : ∀ i, A i 0 = B i 0)
    (hcup : ∀ i j, evenCupForm (A i) (A j) = evenCupForm (B i) (B j)) :
    (∑ i, ∑ j, tailCoefficient (A i) (A j) • b i j) =
      ∑ i, ∑ j, tailCoefficient (B i) (B j) • b i j := by
  have hs (i j : Fin (coreRank h)) :
      tailCoefficient (A i) (A j) - tailCoefficient (B i) (B j) =
      tailCoefficient (A j) (A i) - tailCoefficient (B j) (B i) := by
    have hh := hcup i j
    simp only [evenCupForm_eq_tailCoefficient, hhead] at hh
    have hh' : tailCoefficient (A i) (A j) + tailCoefficient (A j) (A i) =
        tailCoefficient (B i) (B j) + tailCoefficient (B j) (B i) :=
      add_left_cancel (by simpa only [add_assoc] using hh)
    have htwo (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x
    linear_combination hh' - htwo (tailCoefficient (A j) (A i)) +
      htwo (tailCoefficient (B j) (B i))
  have hz := symmetric_contraction_eq_zero
    (fun i j => tailCoefficient (A i) (A j) - tailCoefficient (B i) (B j))
    b hs hb hdiag
  simpa only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using hz

end CupContraction

section RelatorTail
open GQ2.Dyadic.EvenModel

def freeTail {h : ℕ} (m : Fin (coreRank h) → FreeTwoRank (coreRank h)) :
    FreeLayerTwo (coreRank h) :=
  freeBracket _ (m 0) (m 1) + freeBracket _ (m 2) (m 3) +
    ∑ j, freeBracket _ (m (handleIdxU j)) (m (handleIdxV j))

def reducedRows {h : ℕ} (m : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (i j : Fin (coreRank h)) : ZMod 2 :=
  nRed (toAdd (freeTwoCoordinate _ i (m j)))

theorem contract_tailCoefficient {h : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V]
    (A : Fin (coreRank h) → Fin (coreRank h) → ZMod 2)
    (b : Fin (coreRank h) → Fin (coreRank h) → V) :
    (∑ i, ∑ j, tailCoefficient (A i) (A j) • b i j) =
      (∑ i, ∑ j, (A i 0 * A j 1) • b i j) +
      (∑ i, ∑ j, (A i 2 * A j 3) • b i j) +
      ∑ k, ∑ i, ∑ j, (A i (handleIdxU k) * A j (handleIdxV k)) • b i j := by
  simp only [tailCoefficient, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  congr 1
  calc
    _ = ∑ i, ∑ k, ∑ j, (A i (handleIdxU k) * A j (handleIdxV k)) • b i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem freeTail_coordinates {h : ℕ}
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h)) :
    freeTail m = ∑ i, ∑ j,
      tailCoefficient (reducedRows m i) (reducedRows m j) •
        freeBracket _ (freeTwoRankGen _ i) (freeTwoRankGen _ j) := by
  rw [contract_tailCoefficient]
  unfold freeTail
  rw [freeBracket_coordinates _ (m 0) (m 1),
    freeBracket_coordinates _ (m 2) (m 3)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact freeBracket_coordinates _ _ _

/-- Cup preservation, in the row-vector (column-image) variance, fixes the
actual commutator tail modulo lambda-three when the head column is fixed. -/
theorem freeTail_eq_of_cup {h : ℕ}
    (m m' : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hhead : ∀ i, reducedRows m i 0 = reducedRows m' i 0)
    (hcup : ∀ i j, evenCupForm (reducedRows m i) (reducedRows m j) =
      evenCupForm (reducedRows m' i) (reducedRows m' j)) :
    freeTail m = freeTail m' := by
  rw [freeTail_coordinates, freeTail_coordinates]
  apply tailCoefficient_contraction_eq_of_cup _ _ _ _ _ hhead hcup
  · intro i j
    exact bracket_symm _ _ _
  · intro i
    exact bracket_self _ _

theorem freeTail_value {h : ℕ}
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h)) :
    ((freeTail m).toMul : levelQuot (FreeTwoRank (coreRank h) : Type) 3) =
      commP (levelMk _ 3 (m 0)) (levelMk _ 3 (m 1)) *
      commP (levelMk _ 3 (m 2)) (levelMk _ 3 (m 3)) *
      handleWord (fun j => levelMk _ 3 (m (handleIdxU j)))
        (fun j => levelMk _ 3 (m (handleIdxV j))) := by
  have hh : (∑ j, freeBracket _ (m (handleIdxU j)) (m (handleIdxV j))) =
      ((List.finRange h).map fun j =>
        freeBracket _ (m (handleIdxU j)) (m (handleIdxV j))).sum := by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  unfold freeTail
  change _ * _ * (↑((∑ j, freeBracket _ (m (handleIdxU j))
    (m (handleIdxV j))).toMul) : levelQuot (FreeTwoRank (coreRank h) : Type) 3) = _
  congr 1
  rw [hh]
  have hl (L : List (Fin h)) :
      (((L.map fun j => freeBracket _ (m (handleIdxU j))
        (m (handleIdxV j))).sum).toMul :
        levelQuot (FreeTwoRank (coreRank h) : Type) 3) =
      (L.map fun j => commP (levelMk _ 3 (m (handleIdxU j)))
        (levelMk _ 3 (m (handleIdxV j)))).prod := by
    induction L with
    | nil => rfl
    | cons j L ih =>
      change commP _ _ * _ = commP _ _ * _
      exact congrArg (fun x => commP (levelMk _ 3 (m (handleIdxU j)))
        (levelMk _ 3 (m (handleIdxV j))) * x) ih
  exact hl (List.finRange h)

/-- Literal N-relator congruence for arbitrary rank and exponent. The head
is fixed as a group element, while the tail is controlled by the full cup
form, including every handle block. -/
theorem nRelWord_level_three_eq_of_cup {h : ℕ} (α : ℕ)
    (m m' : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hhead : m 0 = m' 0)
    (hcup : ∀ i j, evenCupForm (reducedRows m i) (reducedRows m j) =
      evenCupForm (reducedRows m' i) (reducedRows m' j)) :
    levelMk (FreeTwoRank (coreRank h) : Type) 3 (nRelWord α m) =
      levelMk (FreeTwoRank (coreRank h) : Type) 3 (nRelWord α m') := by
  have ht := freeTail_eq_of_cup m m' (fun i => by simp only [reducedRows, hhead]) hcup
  have hv := congrArg (fun x : FreeLayerTwo (coreRank h) =>
    (x.toMul : levelQuot (FreeTwoRank (coreRank h) : Type) 3)) ht
  rw [freeTail_value, freeTail_value] at hv
  rw [map_nRelWord, map_nRelWord]
  unfold nRelWord nWord
  dsimp only
  rw [hhead]
  simpa only [mul_assoc, hhead] using congrArg
    (fun x => (levelMk (FreeTwoRank (coreRank h) : Type) 3 (m' 0)) ^
      (2 + 2 ^ α) * x) hv

theorem nRelWord_error_mem_three_of_cup {h : ℕ} (α : ℕ)
    (m m' : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hhead : m 0 = m' 0)
    (hcup : ∀ i j, evenCupForm (reducedRows m i) (reducedRows m j) =
      evenCupForm (reducedRows m' i) (reducedRows m' j)) :
    nRelWord α m * (nRelWord α m')⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 := by
  apply (QuotientGroup.eq_one_iff _).mp
  change levelMk (FreeTwoRank (coreRank h) : Type) 3
    (nRelWord α m * (nRelWord α m')⁻¹) = 1
  rw [map_mul, map_inv, nRelWord_level_three_eq_of_cup α m m' hhead hcup,
    mul_inv_cancel]

/-- Initial lambda-three error for the actual free-basis automorphism built
from an integral column matrix. The cup hypothesis is `Abar G Abarᵀ = G`,
written entrywise using the existing uniform even cup form. It is NOT the
oppositely variant formula `Abarᵀ G Abar = G`.

The head column is literally the first standard basis vector, so the chosen
coordinate-word lift fixes that generator exactly. Consequently this initial
step is valid for every alpha; later N correction theorems require alpha ≥ 2. -/
theorem nInitialMatrixError_mem_three {h : ℕ} (α : ℕ)
    (A B : Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2])
    (hAB : A * B = 1)
    (hhead : ∀ i, A i 0 = if i = 0 then 1 else 0)
    (hcup : ∀ i j,
      evenCupForm (fun k => nRed (A i k)) (fun k => nRed (A j k)) =
      evenCupForm (fun k => if k = i then 1 else 0)
        (fun k => if k = j then 1 else 0)) :
    nRelWord α (fun i => freeTwoMatrixEquivOfRightInverse _ A B hAB
        (freeTwoRankGen _ i)) * (nRelWord α (freeTwoRankGen _))⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 := by
  apply nRelWord_error_mem_three_of_cup
  · exact freeTwoMatrixEquivOfRightInverse_gen_of_column _ A B hAB 0 hhead
  · intro i j
    have hr (s : Fin (coreRank h)) :
        reducedRows (fun k => freeTwoMatrixEquivOfRightInverse _ A B hAB
          (freeTwoRankGen _ k)) s = fun k => nRed (A s k) := by
      funext k
      exact congrArg nRed (freeTwoMatrixEquivOfRightInverse_coordinate_gen _ A B hAB s k)
    have hg (s : Fin (coreRank h)) : reducedRows (freeTwoRankGen (coreRank h)) s =
        fun k => if k = s then 1 else 0 := by
      funext k
      simp [reducedRows, freeTwoCoordinate_gen, eq_comm]
    rw [hr, hr, hg, hg]
    exact hcup i j

end RelatorTail

#print axioms layerTwoCommGroup
#print axioms layerTwoModule
#print axioms bracket
#print axioms bracket_mul_left
#print axioms bracket_mul_right
#print axioms bracket_self
#print axioms bracket_symm
#print axioms bracketLeftHom
#print axioms bracketRightHom
#print axioms bracket_list_prod_left
#print axioms bracket_list_prod_right
#print axioms expTwo_character_coordinates
#print axioms freeBracket
#print axioms freeBracket_left_coordinates
#print axioms freeBracket_right_coordinates
#print axioms freeBracket_coordinates
#print axioms FreeLayerTwo
#print axioms symmetric_contraction_eq_zero
#print axioms tailCoefficient
#print axioms evenCupForm_eq_tailCoefficient
#print axioms tailCoefficient_contraction_eq_of_cup
#print axioms freeTail
#print axioms reducedRows
#print axioms contract_tailCoefficient
#print axioms freeTail_coordinates
#print axioms freeTail_eq_of_cup
#print axioms freeTail_value
#print axioms nRelWord_level_three_eq_of_cup
#print axioms nRelWord_error_mem_three_of_cup
#print axioms nInitialMatrixError_mem_three

end
end GQ2.Dyadic.MarkedCore.NInitialCupDepth
