module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import GQ2.CupProduct
import all TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import all TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
import all TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product

section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

example : GQ2.ContCoh.H2 G M = TauCeti.ContCohomology.H2 G M := rfl
noncomputable example : GQ2.ContCoh.H1 G M ≃+ TauCeti.ContCohomology.H1 G M := AddEquiv.refl _
noncomputable example : GQ2.ContCoh.H2 G M ≃+ TauCeti.ContCohomology.H2 G M := AddEquiv.refl _
example (U : Subgroup G) : GQ2.ContCoh.res1 G M U = TauCeti.ContCohomology.explicitRes1 G M U := rfl
example (U : Subgroup G) : GQ2.ContCoh.res2 G M U = TauCeti.ContCohomology.explicitRes2 G M U := rfl
example (z : GQ2.ContCoh.Z1 G M) : (GQ2.ContCoh.H1mk G M z : TauCeti.ContCohomology.H1 G M) =
    TauCeti.ContCohomology.H1pi G M z := rfl
end

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
variable {P : Type} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]
variable (μ : M →+ N →+ P) (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

example : GQ2.ContCoh.cup11 μ hμ =
    TauCeti.ContCohomology.explicitCup11 G M N P μ continuous_of_discreteTopology hμ := rfl
example (x : GQ2.ContCoh.H1 G M) (y : GQ2.ContCoh.H1 G N) : GQ2.ContCoh.cup11 μ hμ x y =
    TauCeti.ContCohomology.explicitCup11 G M N P μ continuous_of_discreteTopology hμ x y := by
  induction x using QuotientAddGroup.induction_on with
  | H a => induction y using QuotientAddGroup.induction_on with
    | H b => rfl
example (m : GQ2.ContCoh.H0 G M) (y : GQ2.ContCoh.H2 G N) : GQ2.ContCoh.cup02 μ hμ m y =
    TauCeti.ContCohomology.explicitCup02 G M N P μ continuous_of_discreteTopology hμ m y := by
  induction y using QuotientAddGroup.induction_on with
  | H b => rfl
example (x : GQ2.ContCoh.H2 G M) (n : GQ2.ContCoh.H0 G N) : GQ2.ContCoh.cup20 μ hμ x n =
    TauCeti.ContCohomology.explicitCup20 G M N P μ continuous_of_discreteTopology hμ x n := by
  induction x using QuotientAddGroup.induction_on with
  | H a => exact (TauCeti.ContCohomology.explicitCup20_mk G M N P μ _ hμ a n).symm
end
