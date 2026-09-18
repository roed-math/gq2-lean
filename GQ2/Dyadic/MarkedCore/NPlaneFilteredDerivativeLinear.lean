import GQ2.Dyadic.MarkedCore.NPlaneFilteredDerivative
import GQ2.Roe.Labute.StageLemma.CrossedDerivation
import GQ2.Roe.Labute.GradedLie.SpanIdentities

/-!
# Multiplicativity of the actual filtered N derivative

The actual correction map is multiplicative on tuples of lambda_(k-1)
elements in Q_(k+1), k >= 3. This supplies composition of finitely many
kernel corrections, including coincident slots. It is not a range theorem.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 Roe.Labute

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (k : ℕ)

private theorem centerPair {A : Type*} [Group A] (a b z w : A)
    (hz : z*b=b*z) : (a*z)*(b*w)=(a*b)*(z*w) := by
  calc
    (a*z)*(b*w) = a*(z*b)*w := by group
    _ = a*(b*z)*w := by rw [hz]
    _ = (a*b)*(z*w) := by group

theorem nFiltered_comm_mul (hk : 3 ≤ k)
    {u v : levelQuot G (k+1)} (hu : u ∈ lambdaImage G (k-1) (k+1))
    (a : levelQuot G (k+1)) :
    commP (u*v) a = commP u a * commP v a := by
  rw [commP_mul_left, conj_eq_self_of_commP_eq_one
    (commP_eq_one_of_mul_comm (zLayer_commute (commP_mem_zLayer k hk hu a) v).eq)]

theorem nFiltered_pair_mul (hk : 3 ≤ k) (a b : levelQuot G (k+1))
    {u v u' v' : levelQuot G (k+1)}
    (hu : u ∈ lambdaImage G (k-1) (k+1))
    (hv : v ∈ lambdaImage G (k-1) (k+1))
    (hu' : u' ∈ lambdaImage G (k-1) (k+1)) :
    commP (u*u') b * commP (v*v') a =
      (commP u b * commP v a) * (commP u' b * commP v' a) := by
  rw [nFiltered_comm_mul k hk hu, nFiltered_comm_mul k hk hv]
  exact centerPair _ _ _ _ ((zLayer_commute (commP_mem_zLayer k hk hu' b) _).eq)

theorem nFiltered_head_mul (hk : 3 ≤ k) (a : levelQuot G (k+1))
    {u u' : levelQuot G (k+1)}
    (hu : u ∈ lambdaImage G (k-1) (k+1))
    (hu' : u' ∈ lambdaImage G (k-1) (k+1)) :
    (u*u')^2 * commP (u*u') a = (u^2*commP u a) * (u'^2*commP u' a) := by
  rw [sq_mul_of_mem_lambdaImage_pred k hk hu hu', nFiltered_comm_mul k hk hu]
  exact centerPair _ _ _ _ ((zLayer_commute (sq_mem_zLayer k hk hu') _).eq)

theorem nFilteredCoreDerivative_mul (hk : 3 ≤ k)
    (a b c d : levelQuot G (k+1))
    {t s : Fin 4 → levelQuot G (k+1)}
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1))
    (hs : ∀ i, s i ∈ lambdaImage G (k-1) (k+1)) :
    nFilteredCoreDerivative a b c d (t 0*s 0) (t 1*s 1) (t 2*s 2) (t 3*s 3) =
      nFilteredCoreDerivative a b c d (t 0) (t 1) (t 2) (t 3) *
      nFilteredCoreDerivative a b c d (s 0) (s 1) (s 2) (s 3) := by
  unfold nFilteredCoreDerivative
  rw [nFiltered_head_mul k hk a (ht 0) (hs 0),
    nFiltered_pair_mul k hk a b (ht 0) (ht 1) (hs 0),
    nFiltered_pair_mul k hk c d (ht 2) (ht 3) (hs 2)]
  exact central_shuffle3
    (fun x => (zLayer_commute ((zLayer G k).mul_mem (sq_mem_zLayer k hk (hs 0))
      (commP_mem_zLayer k hk (hs 0) a)) x).eq)
    (fun x => (zLayer_commute ((zLayer G k).mul_mem (commP_mem_zLayer k hk (hs 0) b)
      (commP_mem_zLayer k hk (hs 1) a)) x).eq)

theorem nFilteredHandleDerivative_mul (hk : 3 ≤ k) {h : ℕ}
    (u v t s t' s' : Fin h → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1))
    (hs : ∀ i, s i ∈ lambdaImage G (k-1) (k+1))
    (ht' : ∀ i, t' i ∈ lambdaImage G (k-1) (k+1))
    (hs' : ∀ i, s' i ∈ lambdaImage G (k-1) (k+1)) :
    nFilteredHandleDerivative u v (fun i => t i*t' i) (fun i => s i*s' i) =
      nFilteredHandleDerivative u v t s * nFilteredHandleDerivative u v t' s' := by
  unfold nFilteredHandleDerivative
  generalize List.finRange h = l
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [nFiltered_pair_mul k hk (u j) (v j) (ht j) (hs j) (ht' j), ih]
    exact centerPair _ _ _ _ ((zLayer_commute ((zLayer G k).mul_mem
      (commP_mem_zLayer k hk (ht' j) (v j)) (commP_mem_zLayer k hk (hs' j) (u j))) _).eq)

/-- Multiplicativity of the full actual N derivative, with no disjoint-support
condition. The product of two correction tuples is pointwise and ordered. -/
theorem nFilteredDerivative_mul (hk : 3 ≤ k) {h : ℕ}
    (m t s : Fin (coreRank h) → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1))
    (hs : ∀ i, s i ∈ lambdaImage G (k-1) (k+1)) :
    nFilteredDerivative m (fun i => t i*s i) =
      nFilteredDerivative m t * nFilteredDerivative m s := by
  have htc : ∀ i : Fin 4, (![t 0,t 1,t 2,t 3] : Fin 4 → levelQuot G (k+1)) i ∈
      lambdaImage G (k-1) (k+1) := by intro i; fin_cases i <;> simp [ht]
  have hsc : ∀ i : Fin 4, (![s 0,s 1,s 2,s 3] : Fin 4 → levelQuot G (k+1)) i ∈
      lambdaImage G (k-1) (k+1) := by intro i; fin_cases i <;> simp [hs]
  have hc := nFilteredCoreDerivative_mul k hk (m 0) (m 1) (m 2) (m 3) htc hsc
  change nFilteredCoreDerivative (m 0) (m 1) (m 2) (m 3) (t 0*s 0) (t 1*s 1)
      (t 2*s 2) (t 3*s 3) = _ at hc
  unfold nFilteredDerivative
  rw [hc, nFilteredHandleDerivative_mul k hk _ _ _ _ _ _
    (fun j => ht (handleIdxU j)) (fun j => ht (handleIdxV j))
    (fun j => hs (handleIdxU j)) (fun j => hs (handleIdxV j))]
  exact centerPair _ _ _ _ ((zLayer_commute
    (nFilteredCoreDerivative_mem k hk _ _ _ _ (hs 0) (hs 1) (hs 2) (hs 3)) _).eq)

#print axioms nFiltered_comm_mul
#print axioms nFiltered_pair_mul
#print axioms nFiltered_head_mul
#print axioms nFilteredCoreDerivative_mul
#print axioms nFilteredHandleDerivative_mul
#print axioms nFilteredDerivative_mul

end GQ2.Dyadic.MarkedCore
