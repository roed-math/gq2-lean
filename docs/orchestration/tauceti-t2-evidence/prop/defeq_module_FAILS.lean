module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic
public import GQ2.PeripheralAction
public import GQ2.ProfinitePresentation

universe u

-- Q1
example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := rfl
example (X : Type u) : (GQ2.FreeProfiniteGroup X : Type u) = (TauCeti.freeProfiniteGroup X : Type u) := rfl
example (X : Type u) (x : X) : GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := rfl
example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := by with_reducible rfl
example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := by unfold GQ2.FreeProfiniteGroup; rfl

-- Q2
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.proPKernel p G = TauCeti.proPKernel p G := rfl
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.IsProP p G ↔ TauCeti.IsProP p G := Iff.rfl
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.IsProP p G = TauCeti.IsProP p G := rfl

example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
  (GQ2.maxProPQuotient p G : Type u) = TauCeti.maximalProPQuotient p G := rfl

example : (GQ2.Delta : Type) = TauCeti.freeProP 2 (Fin 2) := rfl
example : GQ2.deltaP = (TauCeti.freeProP.of 0 : TauCeti.freeProP 2 (Fin 2)) := rfl
example : GQ2.deltaT = (TauCeti.freeProP.of 1 : TauCeti.freeProP 2 (Fin 2)) := rfl

noncomputable example : GQ2.Delta ≃ₜ* TauCeti.freeProP 2 (Fin 2) := ContinuousMulEquiv.refl _

