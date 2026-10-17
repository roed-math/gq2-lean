import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import GQ2.PeripheralAction

universe u

-- non-module file
example (X : Type u) (x : X) : GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := rfl
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.proPKernel p G = TauCeti.proPKernel p G := rfl
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.IsProP p G ↔ TauCeti.IsProP p G := Iff.rfl
example : (GQ2.Delta : Type) = TauCeti.freeProP 2 (Fin 2) := rfl
example : GQ2.deltaP = (TauCeti.freeProP.of 0 : TauCeti.freeProP 2 (Fin 2)) := rfl
