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

open GQ2 GQ2.FoxH
open ContCoh GQ2.LocalLiftingDuality GQ2.Dyadic.LiftingDualityG

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

/-! ## Coefficient transport for the three Tate cups -/

section CupTransport

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction G (ElemDual A)] [ContinuousSMul G (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

variable
  (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
  (hpair : ∀ (g : G) (a : A) (lam : ElemDual A),
    dualEval A (g • a) (g • lam) = g • dualEval A a lam)

/-- Coefficient naturality of the Tate `(0,2)` cup under
`MuDual 2 A ≃ ElemDual A` and `MuN 2 ≃ ZMod 2`.

This is a representative calculation only; it assumes no duality or finiteness of cohomology. -/
theorem H2congr_cup02_muDualPairing
    (c : H0 G (MuDual 2 A)) (d : H2 G A) :
    H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
        (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c d) =
      cup02 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H0congr dualAddEquiv (edEquivariantG hpair htriv) c) d := by
  obtain ⟨b, rfl⟩ := H2mk_surjective (G := G) (M := A) d
  rw [cup02_mk_mk, cup02_mk_mk, H2congr_mk]
  congr 1

/-- Coefficient naturality of the Tate `(1,1)` cup under
`MuDual 2 A ≃ ElemDual A` and `MuN 2 ≃ ZMod 2`.

The equality is proved on two `H¹` representatives and introduces no mathematical hypothesis. -/
theorem H2congr_cup11_muDualPairing
    (c : H1 G (MuDual 2 A)) (d : H1 G A) :
    H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
        (cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c d) =
      cup11 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H1congr dualAddEquiv (edEquivariantG hpair htriv) c) d := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := G) (M := MuDual 2 A) c
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := G) (M := A) d
  rw [H1congr_mk, cup11_mk_mk, cup11_mk_mk, H2congr_mk]
  congr 1

/-- Coefficient naturality of the Tate `(2,0)` cup under
`MuDual 2 A ≃ ElemDual A` and `MuN 2 ≃ ZMod 2`.

As in the other degrees, this is the direct normalized-cocycle computation. -/
theorem H2congr_cup20_muDualPairing
    (c : H2 G (MuDual 2 A)) (d : H0 G A) :
    H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
        (cup20 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c d) =
      cup20 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H2congr dualAddEquiv (edEquivariantG hpair htriv) c) d := by
  obtain ⟨a, rfl⟩ := H2mk_surjective (G := G) (M := MuDual 2 A) c
  rw [H2congr_mk, cup20_mk_mk, cup20_mk_mk, H2congr_mk]
  congr 1

end CupTransport

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
spelling of `TateDualityG`; the three `H2congr_cup*_muDualPairing` theorems above are the exact
coefficient-naturality identities needed for that last step.

Thus the remaining mathematical data are the all-coefficient `H²` comparisons, a scalar
orientation/trace proved without Tate duality, and independent word Stokes duality.  No
coefficient-congruence calculation remains hidden in an assumed cup-perfectness field here.
-/

end


end GQ2.Dyadic.LSquare
