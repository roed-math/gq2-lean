import Mathlib

/-!
# Discrete topological `G`-modules: conventions and basic facts  (ticket T-01, infra I1)

**Convention — no new structures.**  Throughout the project, a *topological `G`-module* is a type
`M` with the Mathlib classes

  `[AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
   [DistribMulAction G M] [ContinuousSMul G M]`,

a *discrete* `G`-module additionally has `[DiscreteTopology M]` (which already implies
`IsTopologicalAddGroup M` by instance), and a *finite* one `[Finite M]`.  No bundling class is
introduced: instance search composes these freely (products, subgroups, `ZMod n`, `μ_n`, …), and
each B-axiom quantifies over exactly the classes it needs.

This file stress-tests the convention by proving the facts that make discrete modules over
profinite groups *smooth* in the classical sense:

* `GQ2.isOpen_stabilizer` — point stabilizers are open;
* `GQ2.isOpen_iInf_stabilizer` — for finite `M`, the kernel of the action is open;
* `GQ2.exists_openNormalSubgroup_smul_eq_self` — over a profinite `G`, a finite discrete module
  is acted on trivially by some open normal subgroup, i.e. **the action factors through a finite
  quotient** — the bridge between continuous cohomology and finite group cohomology.
-/

namespace GQ2

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- In a discrete module, point stabilizers are open subgroups. -/
theorem isOpen_stabilizer (m : M) : IsOpen ((MulAction.stabilizer G m : Subgroup G) : Set G) := by
  have hc : Continuous fun g : G => g • m := continuous_id.smul continuous_const
  have hset : ((MulAction.stabilizer G m : Subgroup G) : Set G)
      = (fun g : G => g • m) ⁻¹' {m} := by
    ext g; simp [MulAction.mem_stabilizer_iff]
  rw [hset]
  exact (isOpen_discrete _).preimage hc

/-- In a **finite** discrete module, the kernel of the action (the intersection of all point
stabilizers) is an open subgroup. -/
theorem isOpen_iInf_stabilizer [Finite M] :
    IsOpen ((⨅ m : M, MulAction.stabilizer G m : Subgroup G) : Set G) := by
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun m => isOpen_stabilizer m

/-- **Smoothness**: a finite discrete module over a profinite group is acted on trivially by an
open *normal* subgroup — the action factors through a finite quotient of `G`.  This is the
structural fact connecting continuous cohomology of `G` to ordinary cohomology of its finite
quotients. -/
theorem exists_openNormalSubgroup_smul_eq_self [Finite M]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∀ m : M, u • m = m := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_iInf_stabilizer (G := G) (M := M))
    (Subgroup.one_mem _)
  refine ⟨U, fun u hu m => ?_⟩
  have hmem : u ∈ (⨅ m : M, MulAction.stabilizer G m : Subgroup G) := hU hu
  rw [Subgroup.mem_iInf] at hmem
  exact hmem m

end GQ2
