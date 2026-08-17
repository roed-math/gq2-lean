import GQ2.Dyadic.Instances.MpcBalancedRowLift

/-!
# The base stage of the balanced one-handle construction

W199 constructs a balanced one-handle seed satisfying every condition except finite-depth
control of the relator defect.  This module proves that the defect condition is automatic
through depth two.  Every `M₂` core word is a product of squares and commutators, hence lies in
the Frattini term `λ₂`; the same is then true of the full one-handle correction defect.

Thus `oneHandleBalancedSet Psi0 k` is nonempty for every `k ≤ 2` as soon as the compact
automorphism has the universal pivot row.  The first genuinely informative remaining case is
depth three, equivalently the class `λ₂/λ₃` of the joint relator defect.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedBase

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRowLift
open GQ2.Roe.Labute

private theorem commP_mem_two (x y : DM 2 1) :
    commP x y ∈ twoCentralSeries (DM 2 1) 2 := by
  change commP x y ∈ twoCentralSucc (⊤ : Subgroup (DM 2 1))
  exact commP_mem_twoCentralSucc (Subgroup.mem_top x) y

/-- Every `M₂` core word starts in the Frattini term, independently of its letters. -/
theorem mWord_mem_two (a b c d : DM 2 1) :
    mWord 2 a b c d ∈ twoCentralSeries (DM 2 1) 2 := by
  rw [mWord]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact sq_mem_twoCentralSeries_succ (DM 2 1) (Subgroup.mem_top a)
  · exact commP_mem_two a b
  · exact twoCentralSeries_antitone (DM 2 1) (by omega : 2 ≤ 3)
      (pow_two_pow_mem_twoCentralSeries_succ (DM 2 1) c 2)
  · exact commP_mem_two c d

/-- The one-handle correction defect always begins in the Frattini term. -/
theorem oneHandleDDefect_mem_two (a b c d z : DM 2 1) :
    oneHandleDDefect a b c d z ∈ twoCentralSeries (DM 2 1) 2 := by
  rw [oneHandleDDefect]
  refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (Subgroup.mul_mem _
    (Subgroup.inv_mem _ (mWord_mem_two a b c d)) ?_))
  · simpa [conjP] using
      (twoCentralSeries_normal (DM 2 1) 2).conj_mem
        (commP c z) (commP_mem_two c z) d⁻¹
  · exact Subgroup.inv_mem _ (commP_mem_two
      (dmGen 2 1 (handleIdxU (0 : Fin 1)))
      (dmGen 2 1 (handleIdxV (0 : Fin 1))))

/-- A compact pivot-row witness makes every one-handle balanced set nonempty through the
Frattini stage. -/
theorem oneHandleBalancedSet_nonempty_of_le_two
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (k : ℕ) (hk : k ≤ 2) :
    (oneHandleBalancedSet Psi0 k).Nonempty := by
  obtain ⟨p, ha, hb, hc, hd, hz, hind, hprow⟩ :=
    exists_oneHandleBalancedSeed Psi0 hrow
  refine ⟨p, ha, hb, hc, hd, hz, hind, hprow, ?_⟩
  exact twoCentralSeries_antitone (DM 2 1) hk
    (oneHandleDDefect_mem_two (balancedA p) (balancedB p) (balancedC p)
      (balancedD p) (balancedZ p))

#print axioms mWord_mem_two
#print axioms oneHandleDDefect_mem_two
#print axioms oneHandleBalancedSet_nonempty_of_le_two

end
end GQ2.Dyadic.Instances.MpcBalancedBase
