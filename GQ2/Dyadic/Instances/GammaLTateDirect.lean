/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LSourceComparison

/-!
# Direct Tate-duality assembly from the improved L presentation

This file begins the non-field-theoretic route from the abstract L presentation to
`TateDualityG`.  Its first task is structural: every continuous action on a finite discrete
coefficient module has a canonical finite discrete target, namely the full additive
automorphism group of the coefficient.  This avoids choosing an arbitrary quotient before a
uniform source-comparison provider is applied.

The remaining assembly is described after `finiteActionHom`.  Crucially, it must consume
`SourceComparisonCore`, not `SourceComparisonPackage`: continuous cup perfectness is a
conclusion of word Stokes duality and the comparison squares, never an input.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

/-! ## The canonical finite action target -/

/-- The additive automorphism group used as a finite action target carries the discrete
topology.  The instance is useful even before finiteness is installed on the coefficient. -/
instance finiteActionTargetTopologicalSpace {M : Type*} [AddCommGroup M] :
    TopologicalSpace (Multiplicative (AddAut M)) := ⊥

/-- The canonical topology on the additive automorphism action target is discrete. -/
instance finiteActionTargetDiscreteTopology {M : Type*} [AddCommGroup M] :
    DiscreteTopology (Multiplicative (AddAut M)) := ⟨rfl⟩

/-- The tautological distributive action of the multiplicative additive-automorphism group. -/
noncomputable instance finiteActionTargetDistribMulAction {M : Type*} [AddCommGroup M] :
    DistribMulAction (Multiplicative (AddAut M)) M where
  smul g m := Multiplicative.toAdd g m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero g := map_zero (Multiplicative.toAdd g)
  smul_add g := map_add (Multiplicative.toAdd g)

/-- The kernel of the homomorphism to additive automorphisms is the intersection of all point
stabilizers. -/
theorem finiteActionMonoidHom_ker
    {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M] :
    ((DistribMulAction.toAddAut G M).ker : Set G) =
      ((⨅ m : M, MulAction.stabilizer G m : Subgroup G) : Set G) := by
  ext g
  change g ∈ (DistribMulAction.toAddAut G M).ker ↔
    g ∈ (⨅ m : M, MulAction.stabilizer G m : Subgroup G)
  rw [Subgroup.mem_iInf]
  change (DistribMulAction.toAddAut G M g = 1) ↔ ∀ m : M, g • m = m
  constructor
  · intro hg m
    exact DFunLike.congr_fun (congrArg Multiplicative.toAdd hg) m
  · intro hg
    apply Multiplicative.ofAdd.injective
    ext m
    exact hg m

/-- The canonical continuous homomorphism recording the action on a finite discrete module.

Its target is finite because `M` is finite.  Continuity follows from continuity of the original
action: the kernel is the finite intersection of its open point stabilizers. -/
noncomputable def finiteActionHom
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] :
    ContinuousMonoidHom G (Multiplicative (AddAut M)) := by
  refine ⟨DistribMulAction.toAddAut G M, ?_⟩
  change Continuous (DistribMulAction.toAddAut G M : G → Multiplicative (AddAut M))
  apply continuous_of_continuousAt_one (DistribMulAction.toAddAut G M)
  rw [ContinuousAt]
  simp only [map_one]
  rw [show nhds (1 : Multiplicative (AddAut M)) = pure 1 from
      congrFun (nhds_discrete (Multiplicative (AddAut M))) 1,
    Filter.tendsto_pure]
  have hker : IsOpen ((DistribMulAction.toAddAut G M).ker : Set G) := by
    rw [finiteActionMonoidHom_ker]
    exact isOpen_iInf_stabilizer (G := G) (M := M)
  exact hker.mem_nhds (Subgroup.one_mem _)

/-- The action pulled back through `finiteActionHom` is definitionally the original action. -/
@[simp] theorem finiteActionHom_smul
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (g : G) (m : M) : finiteActionHom (G := G) (M := M) g • m = g • m := rfl

/-! ## Remaining direct-assembly interface

For every finite exponent-two `G`-module `M`, a uniform direct proof should now apply the L
provider with

* `C := Multiplicative (AddAut M)`,
* `rho := finiteActionHom`, and
* the tautological target action above.

The provider must return a `SourceComparisonCore` and an independently proved word
`StokesDuality`, sharing a scalar orientation `H²(G, ZMod 2) ≃+ ZMod 2`.  The theorem
`SourceComparisonCore.sourceCupBijections_of_stokesDuality` then proves the three continuous
evaluation-cup maps perfect.  `transpose_bijective_of_bijective` and cup symmetry reverse the
currying, after which `dualAddEquiv`/`edEquivariantG` and
`muNTwoEquiv`/`muNTwoEquiv_equivariantG` transport the result to the exact `MuDual` and `MuN`
spelling of `TateDualityG`.

Thus the remaining mathematical data are the all-coefficient `H²` comparisons, a scalar
orientation/trace proved without Tate duality, and independent word Stokes duality.  The final
coefficient-congruence calculation is representative-level plumbing; it is intentionally not
hidden in an assumed cup-perfectness field here.
-/

end


end GQ2.Dyadic.LSquare
