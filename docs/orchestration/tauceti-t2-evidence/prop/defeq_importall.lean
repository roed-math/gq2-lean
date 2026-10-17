module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
import all TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
import all TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import GQ2.PeripheralAction

universe u

-- module file with import all
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.proPKernel p G = TauCeti.proPKernel p G := rfl
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : GQ2.IsProP p G ↔ TauCeti.IsProP p G := Iff.rfl
