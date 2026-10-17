import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import GQ2.Cohomology

section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

example : GQ2.ContCoh.H0 G M = TauCeti.ContCohomology.H0 G M := rfl
example : GQ2.ContCoh.C1 G M = TauCeti.ContCohomology.C1 G M := rfl
example : GQ2.ContCoh.dZero G M = TauCeti.ContCohomology.d0 G M := rfl
example : GQ2.ContCoh.dOne G M = TauCeti.ContCohomology.d1 G M := rfl
example : GQ2.ContCoh.dTwo G M = TauCeti.ContCohomology.d2 G M := rfl
example : GQ2.ContCoh.Z1 G M = TauCeti.ContCohomology.Z1 G M := rfl
example : GQ2.ContCoh.B1 G M = TauCeti.ContCohomology.B1 G M := rfl
example : GQ2.ContCoh.Z2 G M = TauCeti.ContCohomology.Z2 G M := rfl
example : GQ2.ContCoh.B2 G M = TauCeti.ContCohomology.B2 G M := rfl
example : GQ2.ContCoh.H1 G M = TauCeti.ContCohomology.H1 G M := rfl
example : GQ2.ContCoh.H2 G M = TauCeti.ContCohomology.H2 G M := rfl
example (x : GQ2.ContCoh.H1 G M) : TauCeti.ContCohomology.H1 G M := x
example : (inferInstance : AddCommGroup (GQ2.ContCoh.H1 G M)) =
  (inferInstance : AddCommGroup (TauCeti.ContCohomology.H1 G M)) := rfl
example : (inferInstance : AddCommGroup (GQ2.ContCoh.H2 G M)) =
  (inferInstance : AddCommGroup (TauCeti.ContCohomology.H2 G M)) := rfl
noncomputable example : GQ2.ContCoh.H1 G M ≃+ TauCeti.ContCohomology.H1 G M := AddEquiv.refl _
noncomputable example : GQ2.ContCoh.H2 G M ≃+ TauCeti.ContCohomology.H2 G M := AddEquiv.refl _
example (U : Subgroup G) : GQ2.ContCoh.res1 G M U = TauCeti.ContCohomology.explicitRes1 G M U := rfl
example (U : Subgroup G) : GQ2.ContCoh.res2 G M U = TauCeti.ContCohomology.explicitRes2 G M U := rfl
end
