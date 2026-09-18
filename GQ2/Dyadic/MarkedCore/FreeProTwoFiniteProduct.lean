import GQ2.ProTwoFiniteProduct
import GQ2.Dyadic.MarkedCore.FreeProTwoCommutatorShear

/-! # The actual free pro-two tuple group is pro-two -/

namespace GQ2.Dyadic.MarkedCore

/-- The actual tuple carrier for ordinary-row correction, uniformly in both
the number of tuples and the rank of the free pro-two factor. -/
theorem isProTwo_freeTwoRank_tuple (n m : ℕ) :
    IsProP 2 (Fin n → (FreeTwoRank m : Type)) :=
  isProP_fin_tuple (isProP_presPro2 (1 : FreeProfiniteGroup (Fin m))) n

/-- The paired N-alphabet tuple group, at arbitrary handle rank. -/
theorem isProTwo_freeN_tuple (h : ℕ) :
    IsProP 2 (Fin (coreRank h) → (FreeTwoRank (coreRank h) : Type)) :=
  isProTwo_freeTwoRank_tuple (coreRank h) (coreRank h)

#print axioms isProTwo_freeTwoRank_tuple
#print axioms isProTwo_freeN_tuple

end GQ2.Dyadic.MarkedCore
