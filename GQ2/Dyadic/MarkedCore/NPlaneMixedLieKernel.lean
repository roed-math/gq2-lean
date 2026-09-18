import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# A relative N-derivative kernel vector in a mixed Lie calculation

This is a finite-rank algebra identity, not an instantiation of the associated
graded of a free pro-two group and not a producer of NPlaneScalingHypothesis.
`P` models a power of the square operation on commutator degrees. `H` models
the next square operation on correction degree. The single mixed-square
equation is explicit; in particular its exceptional triple bracket is retained.
No grading, completeness, or group-lifting assertion is hidden in the inputs.
-/

namespace GQ2.Dyadic.MarkedCore

section LieIdentity
variable {L : Type*} [LieRing L]

private theorem mixedLie_symm (h₂ : ∀ x : L, x + x = 0) (x y : L) :
    ⁅x, y⁆ = ⁅y, x⁆ := by
  have hn : -⁅y, x⁆ = ⁅y, x⁆ := (neg_eq_iff_add_eq_zero).mpr (h₂ _)
  rw [← lie_skew, hn]

/-- The Jacobi cancellation used in the kernel vector, including repeated
letters. Only exponent two for the additive group is required. -/
theorem nMixedLie_jacobi (h₂ : ∀ x : L, x + x = 0) (v g b : L) :
    ⁅⁅g, b⁆, v⁆ + ⁅⁅v, b⁆, g⁆ = ⁅⁅v, g⁆, b⁆ := by
  have hj := leibniz_lie v g b
  rw [mixedLie_symm h₂ v ⁅g, b⁆, mixedLie_symm h₂ g ⁅v, b⁆] at hj
  rw [hj, add_assoc, h₂, add_zero]

/-- Uniform mixed-Lie cancellation. For correction degree `j-1`, one intends
`P=pi^(j-3)`, `w=pi^(j-2)v`. The displayed mixed equation includes the extra
term already needed at `j=3`. The theorem itself has no degree parameter. -/
theorem nMixedLie_kernel_identity (h₂ : ∀ x : L, x + x = 0)
    (P H : L →+ L)
    (hP : ∀ x y z : L, P ⁅⁅x, y⁆, z⁆ = ⁅P ⁅x, y⁆, z⁆)
    (a b v g w : L)
    (hw : ⁅w, g⁆ = H (P ⁅v, g⁆) + P ⁅⁅v, g⁆, v⁆) :
    ⁅w, g⁆ + (H (P ⁅v, g⁆) + ⁅P ⁅v, g⁆, a⁆ + ⁅P ⁅v, g⁆, b⁆) +
      ⁅P ⁅v, g⁆, a⁆ + ⁅P (⁅v, g⁆ + ⁅g, b⁆), v⁆ + ⁅P ⁅v, b⁆, g⁆ = 0 := by
  rw [hw, map_add, add_lie, ← hP v g b, ← hP v g v, ← hP g b v, ← hP v b g]
  have hj : P ⁅⁅g, b⁆, v⁆ + P ⁅⁅v, b⁆, g⁆ = P ⁅⁅v, g⁆, b⁆ := by
    rw [← map_add, nMixedLie_jacobi h₂]
  calc
    _ = (H (P ⁅v, g⁆) + H (P ⁅v, g⁆)) +
        (⁅P ⁅v, g⁆, a⁆ + ⁅P ⁅v, g⁆, a⁆) +
        (P ⁅⁅v, g⁆, v⁆ + P ⁅⁅v, g⁆, v⁆) +
        (P ⁅⁅v, g⁆, b⁆ + (P ⁅⁅g, b⁆, v⁆ + P ⁅⁅v, b⁆, g⁆)) := by abel
    _ = 0 := by
      rw [hj]
      simp only [h₂]

end LieIdentity

section IndexedDerivative
variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L]

/-- The head-square term, the additional head `ad_a` term, and every paired
commutator column. In exponent two this is the N mixed derivative. -/
def nMixedDerivative (H : L →+ L) (a : I) (letter : I → L) (partner : I → I)
    (t : I → L) : L :=
  H (t a) + ⁅t a, letter a⁆ + ∑ i, ⁅t i, letter (partner i)⁆

omit [DecidableEq I] in
theorem nMixedDerivative_add (H : L →+ L) (a : I) (letter : I → L)
    (partner : I → I) (t u : I → L) :
    nMixedDerivative H a letter partner (t + u) =
      nMixedDerivative H a letter partner t + nMixedDerivative H a letter partner u := by
  simp only [nMixedDerivative, Pi.add_apply, map_add, add_lie, Finset.sum_add_distrib]
  abel

theorem nMixedDerivative_single (H : L →+ L) (a : I) (letter : I → L)
    (partner : I → I) (i : I) (x : L) :
    nMixedDerivative H a letter partner (Pi.single i x) =
      (if i = a then H x + ⁅x, letter a⁆ else 0) + ⁅x, letter (partner i)⁆ := by
  have hsum : (∑ j, ⁅(Pi.single i x : I → L) j, letter (partner j)⁆) =
      ⁅x, letter (partner i)⁆ := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  unfold nMixedDerivative
  rw [hsum]
  by_cases hi : i = a
  · subst i
    simp
  · simp [hi, Ne.symm hi]

/-- Additive assignments, not overwrites: coincident partner slots are allowed.
The five increments are exactly those of the relative correction calculation. -/
def nMixedKernelVector (P : L →+ L) (a b i v : I) (letter : I → L)
    (partner : I → I) (w : L) : I → L :=
  Pi.single i w + Pi.single a (P ⁅letter v, letter (partner i)⁆) +
    Pi.single b (P ⁅letter v, letter (partner i)⁆) +
    Pi.single (partner v) (P (⁅letter v, letter (partner i)⁆ +
      ⁅letter (partner i), letter b⁆)) +
    Pi.single (partner (partner i)) (P ⁅letter v, letter b⁆)

/-- The explicit vector is in the full finite paired derivative's kernel.
No bound on the number of pairs and no distinctness of the auxiliary slots
is imposed. The supplied mixed-square identity is the concrete-instantiation seam. -/
theorem nMixedDerivative_kernelVector
    (h₂ : ∀ x : L, x + x = 0) (P H : L →+ L)
    (hP : ∀ x y z : L, P ⁅⁅x, y⁆, z⁆ = ⁅P ⁅x, y⁆, z⁆)
    (a b i v : I) (letter : I → L) (partner : I → I)
    (hs : Function.Involutive partner) (hab : partner a = b)
    (hne : a ≠ b) (hi : i ≠ a) (hv : v ≠ b) (w : L)
    (hw : ⁅w, letter (partner i)⁆ = H (P ⁅letter v, letter (partner i)⁆) +
      P ⁅⁅letter v, letter (partner i)⁆, letter v⁆) :
    nMixedDerivative H a letter partner
      (nMixedKernelVector P a b i v letter partner w) = 0 := by
  have hba : partner b = a := by rw [← hab, hs]
  have hva : partner v ≠ a := by
    intro h
    have hh := congrArg partner h
    rw [hs, hab] at hh
    exact hv hh
  have hvi := hs v
  have hii := hs i
  simp only [nMixedKernelVector, nMixedDerivative_add, nMixedDerivative_single,
    hvi, hii, if_neg hi, if_neg (Ne.symm hne), if_neg hva,
    zero_add, hab, hba, ite_true]
  exact nMixedLie_kernel_identity h₂ P H hP (letter a) (letter b)
    (letter v) (letter (partner i)) w hw

omit [Fintype I] in
/-- Every ordinary row is exactly zero except the requested one. The row map
need only kill the powered commutator classes used in the construction. -/
theorem nMixedKernelVector_row {M : Type*} [AddCommGroup M]
    (P : L →+ L) (a b i v : I) (letter : I → L) (partner : I → I) (w : L)
    (row : L →+ M) (hrow : ∀ x y : L, row (P ⁅x, y⁆) = 0) :
    (fun k => row (nMixedKernelVector P a b i v letter partner w k)) =
      Pi.single i (row w) := by
  funext k
  simp only [nMixedKernelVector, Pi.add_apply, map_add]
  by_cases hki : k = i <;>
    simp [Pi.single_apply, apply_ite, map_zero, map_add, hrow, hki]

omit [DecidableEq I] in
/-- In ordinary abelianization, only the head-square column survives. -/
theorem nMixedDerivative_row {M : Type*} [AddCommGroup M]
    (H : L →+ L) (a : I) (letter : I → L) (partner : I → I) (t : I → L)
    (row : L →+ M) (Hbar : M →+ M)
    (hbr : ∀ x y : L, row ⁅x, y⁆ = 0)
    (hH : row (H (t a)) = Hbar (row (t a))) :
    row (nMixedDerivative H a letter partner t) = Hbar (row (t a)) := by
  simp only [nMixedDerivative, map_add, map_sum, hbr, hH, Finset.sum_const_zero, add_zero]

omit [DecidableEq I] in
/-- Zero ordinary error forces the head correction row to vanish when the
ordinary square map is injective. Its injectivity is an explicit input here,
not a claimed fact about an unconstructed associated graded object. -/
theorem nMixedDerivative_headRow_eq_zero {M : Type*} [AddCommGroup M]
    (H : L →+ L) (a : I) (letter : I → L) (partner : I → I) (t : I → L)
    (row : L →+ M) (Hbar : M →+ M)
    (hbr : ∀ x y : L, row ⁅x, y⁆ = 0)
    (hH : row (H (t a)) = Hbar (row (t a)))
    (hinj : Function.Injective Hbar)
    (hz : row (nMixedDerivative H a letter partner t) = 0) : row (t a) = 0 := by
  apply hinj
  rw [← nMixedDerivative_row H a letter partner t row Hbar hbr hH, hz, map_zero]

#print axioms nMixedLie_jacobi
#print axioms nMixedLie_kernel_identity
#print axioms nMixedDerivative
#print axioms nMixedDerivative_add
#print axioms nMixedDerivative_single
#print axioms nMixedKernelVector
#print axioms nMixedDerivative_kernelVector
#print axioms nMixedKernelVector_row
#print axioms nMixedDerivative_row
#print axioms nMixedDerivative_headRow_eq_zero

end IndexedDerivative
end GQ2.Dyadic.MarkedCore
