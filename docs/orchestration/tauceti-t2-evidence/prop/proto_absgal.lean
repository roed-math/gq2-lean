module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic
public import GQ2.PeripheralAction
public import GQ2.ProfinitePresentation
public import GQ2.Statement
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP

universe u

namespace Scratch

-- (1) carriers / objects
example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := rfl
example (X : Type u) : (GQ2.FreeProfiniteGroup X : Type u) = (TauCeti.freeProfiniteGroup X : Type u) := rfl

theorem of_eq {X : Type u} (x : X) : GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := by
  rw [← TauCeti.freeProfiniteGroup.fromFreeGroup_of, TauCeti.freeProfiniteGroup.coe_fromFreeGroup]
  rfl


theorem proPKernel_eq (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] :
    GQ2.proPKernel p G = TauCeti.proPKernel p G := by
  ext x
  rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩

noncomputable def maxProPEquiv (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    GQ2.maxProPQuotient p G ≃ₜ* TauCeti.maximalProPQuotient p G :=
  (ContinuousMulEquiv.refl G).quotientCongr (GQ2.proPKernel p G) (TauCeti.proPKernel p G)
    (by rw [proPKernel_eq]; exact Subgroup.map_id _)

#synth IsTopologicalGroup GQ2.AbsGalQ2
#synth CompactSpace GQ2.AbsGalQ2
#synth TotallyDisconnectedSpace GQ2.AbsGalQ2

noncomputable example : GQ2.maxProPQuotient 2 GQ2.AbsGalQ2 ≃ₜ* TauCeti.absoluteGaloisGroupProP 2 ℚ_[2] :=
  maxProPEquiv 2 GQ2.AbsGalQ2

end Scratch
