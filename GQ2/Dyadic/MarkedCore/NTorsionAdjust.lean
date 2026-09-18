import GQ2.Dyadic.MarkedCore.NFrameExists
import GQ2.Dyadic.MarkedCore.N

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative SectionThree

def nTorsionAdjust {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (delta : ZMod 2) : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type) :=
  (dnTauBEquiv alpha h (delta.val : ℤ_[2])).trans Psi

theorem nTorsionAdjust_gen_of_ne {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (delta : ZMod 2) (i : Fin (coreRank h)) (hi : i ≠ 1) :
    nTorsionAdjust Psi delta (dnGen alpha h i) = Psi (dnGen alpha h i) := by
  change Psi (dnTauBEquiv alpha h (delta.val : ℤ_[2]) (dnGen alpha h i)) = _
  rw [dnTauBEquiv_of_ne alpha h _ hi]

theorem nTorsionAdjust_X1 {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (delta : ZMod 2) :
    nTorsionAdjust Psi delta (dnX1 alpha h) =
      Psi (dnX0 alpha h) ^ delta.val * Psi (dnX1 alpha h) := by
  change Psi (dnTauBEquiv alpha h (delta.val : ℤ_[2]) (dnX1 alpha h)) = _
  rw [dnTauBEquiv_dnX1, zpowZtwo_natCast, map_mul, map_pow]

theorem nTorsionAdjust_chi {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (hPsi : ∀ x, chiN alpha h (Psi x) = chiN alpha h x)
    (delta : ZMod 2) (x : DN alpha h) :
    chiN alpha h (nTorsionAdjust Psi delta x) = chiN alpha h x := by
  change chiN alpha h (Psi (dnTauBEquiv alpha h (delta.val : ℤ_[2]) x)) = _
  rw [hPsi, chiN_dnTauBEquiv]

theorem nTorsionAdjust_nuFrame {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (delta : ZMod 2)
    (f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (fun i => nTorsionAdjust Psi delta (dnGen alpha h i)) =
      nuFrame f (fun i => Psi (dnGen alpha h i)) := by
  exact nuFrame_dnTauBEquiv alpha h (delta.val : ℤ_[2]) (f.comp (autHom Psi))

theorem nTorsionAdjust_torsion {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (t : (DN alpha h : Type) →* Multiplicative (ZMod 2))
    (ht : t (Psi (dnX0 alpha h)) = ofAdd 1) (delta : ZMod 2) :
    toAdd (t (nTorsionAdjust Psi delta (dnX1 alpha h))) =
      delta + toAdd (t (Psi (dnX1 alpha h))) := by
  rw [nTorsionAdjust_X1, map_mul, map_pow, ht, toAdd_mul, toAdd_pow, toAdd_ofAdd]
  simp

theorem nTorsionAdjust_torsion_target {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (t : (DN alpha h : Type) →* Multiplicative (ZMod 2))
    (ht : t (Psi (dnX0 alpha h)) = ofAdd 1) (tau : ZMod 2) :
    toAdd (t (nTorsionAdjust Psi (tau - toAdd (t (Psi (dnX1 alpha h))))
      (dnX1 alpha h))) = tau := by
  rw [nTorsionAdjust_torsion Psi t ht, sub_add_cancel]

#print axioms nTorsionAdjust
#print axioms nTorsionAdjust_gen_of_ne
#print axioms nTorsionAdjust_X1
#print axioms nTorsionAdjust_chi
#print axioms nTorsionAdjust_nuFrame
#print axioms nTorsionAdjust_torsion
#print axioms nTorsionAdjust_torsion_target
end
end GQ2.Dyadic.MarkedCore
