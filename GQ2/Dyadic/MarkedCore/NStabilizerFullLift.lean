import GQ2.Dyadic.MarkedCore.NPlaneGeneralScaling
import GQ2.Dyadic.MarkedCore.NStabilizerFullRows
import GQ2.Dyadic.MarkedCore.NTorsionAdjust

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative SectionThree NStabilizerFullRows

/-- Every admissible core stabilizer parameter is realized on the full
canonical abelianization, including torsion, with identity handle columns. -/
theorem nStabParam_fullFrame_lift_general {alpha h : ℕ} (ha : 2 ≤ alpha)
    (P : NStabParam) (hP : P.Admissible) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
        nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h))) ∧
      ∀ i, nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = fullFrameMark P h i := by
  obtain ⟨Psi, hchi, H⟩ := nStabParam_lift_general (h := h) ha hP
  let t := torsionChar (by omega : 1 ≤ alpha) h
  let delta : ZMod 2 := P.tau - toAdd (t (Psi (dnX1 alpha h)))
  let Psi' := nTorsionAdjust Psi delta
  have ht : t (Psi (dnX0 alpha h)) = ofAdd 1 := by
    apply toAdd.injective
    exact torsionChar_aut_zero ha P Psi H
  have H' : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi' (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)) := by
    intro f
    rw [show Psi' = nTorsionAdjust Psi delta from rfl, nTorsionAdjust_nuFrame]
    exact H f
  have htau : toAdd (torsionChar (by omega : 1 ≤ alpha) h
      (Psi' (dnGen alpha h 1))) = P.tau :=
    nTorsionAdjust_torsion_target Psi t.toMonoidHom ht P.tau
  exact ⟨Psi', nTorsionAdjust_chi Psi hchi delta, H',
    nPhiHom_aut_fullFrameMark ha P hP Psi' H' htau⟩

#print axioms nStabParam_fullFrame_lift_general
end
end GQ2.Dyadic.MarkedCore
