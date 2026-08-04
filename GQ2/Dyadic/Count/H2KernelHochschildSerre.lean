/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2MaxProTwoInflationCriterion
import Mathlib.Topology.CompactOpen

/-!
# A kernel-acyclicity criterion for degree-two inflation

For a profinite quotient `G -> G/N`, degree-two inflation is onto if every continuous
two-cocycle can be normalized to vanish whenever either input lies in `N`.  This file proves
that elementary cochain statement: the cocycle identity then makes the normalized cocycle
constant on both `N`-cosets, and the quotient topology makes the descended cochain continuous.

The final package separates the normalization into the two Hochschild--Serre inputs which a
group-theoretic proof must provide:

* a continuous primitive for the restriction to `N` (the degree-two kernel-acyclicity input);
* an extension/coherence correction killing the two cross terms (the degree-one/transgression
  input).

Neither field mentions inflation or a cochain downstairs.  In particular, the package is not
an alias of the descent criterion.
-/

namespace GQ2.ContCoh

noncomputable section

section NormalizedDescent

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

variable (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)]
variable [DistribMulAction (G ⧸ N) M] [ContinuousSMul (G ⧸ N) M]

/-- A corrected two-cocycle is *kernel normalized* if it vanishes whenever either input lies
in the normal subgroup.  This condition has no quotient or inflation in its statement. -/
def H2KernelNormalizedCorrection (z : Z2 G M) : Prop :=
  ∃ psi : G → M, Continuous psi ∧
    ∀ (g : G) (n : N),
      (z.1 + dOne G M psi) (g, n.1) = 0 ∧
      (z.1 + dOne G M psi) (n.1, g) = 0

/-- A quotient-compatible coefficient action is trivial on the quotient kernel. -/
theorem kernel_smul_eq_of_quotient_compat
    (hcompat : ∀ (g : G) (m : M), quotientMk N g • m = g • m)
    (n : N) (m : M) : n.1 • m = m := by
  rw [← hcompat n.1 m]
  have hn : quotientMk N n.1 = 1 :=
    (QuotientGroup.eq_one_iff n.1).mpr n.2
  rw [hn, one_smul]

private theorem kernelNormalized_right_coset
    (c : Z2 G M)
    (hzero : ∀ (g : G) (n : N), c.1 (g, n.1) = 0 ∧ c.1 (n.1, g) = 0)
    (g h : G) (n : N) : c.1 (g, h * n.1) = c.1 (g, h) := by
  have hc := (mem_Z2_iff.mp c.2).2 g h n.1
  rw [(hzero h n).1, (hzero (g * h) n).1, smul_zero, zero_add, zero_add] at hc
  exact hc

private theorem kernelNormalized_left_coset
    (c : Z2 G M)
    (hzero : ∀ (g : G) (n : N), c.1 (g, n.1) = 0 ∧ c.1 (n.1, g) = 0)
    (g h : G) (n : N) : c.1 (g * n.1, h) = c.1 (g, h) := by
  let n' : N :=
    ⟨h⁻¹ * n.1 * h, by
      simpa using (inferInstance : N.Normal).conj_mem n.1 n.2 h⁻¹⟩
  have hc := (mem_Z2_iff.mp c.2).2 g n.1 h
  rw [(hzero h n).2, (hzero g n).1, smul_zero, zero_add, add_zero] at hc
  have hnh : n.1 * h = h * n'.1 := by
    dsimp [n']
    group
  rw [hnh, kernelNormalized_right_coset N c hzero g h n'] at hc
  exact hc.symm

/-- Kernel normalization is sufficient for explicit continuous descent to the quotient.

The proof is the cochain core of the Hochschild--Serre argument: the cocycle identity upgrades
vanishing on `G × N` and `N × G` to invariance under both right `N`-cosets. -/
theorem h2CocycleInflationDescent_of_kernelNormalized
    (z : Z2 G M) (hnorm : H2KernelNormalizedCorrection N z) :
    H2CocycleInflationDescent (quotientMk N) z := by
  obtain ⟨psi, hpsi, hzero⟩ := hnorm
  have hcob : dOne G M psi ∈ Z2 G M := by
    apply B2_le_Z2
    exact ⟨psi, hpsi, rfl⟩
  let c : Z2 G M := ⟨z.1 + dOne G M psi, (Z2 G M).add_mem z.2 hcob⟩
  have hccont : Continuous c.1 := (mem_Z2_iff.mp c.2).1
  have hczero : ∀ (g : G) (n : N), c.1 (g, n.1) = 0 ∧ c.1 (n.1, g) = 0 :=
    hzero
  let bar : (G ⧸ N) × (G ⧸ N) → M := fun p =>
    Quotient.liftOn₂ p.1 p.2 (fun g h => c.1 (g, h)) (by
      intro x1 y1 x2 y2 hx hy
      have hxn : x1⁻¹ * x2 ∈ N := QuotientGroup.leftRel_apply.mp hx
      have hyn : y1⁻¹ * y2 ∈ N := QuotientGroup.leftRel_apply.mp hy
      let nx : N := ⟨x1⁻¹ * x2, hxn⟩
      let ny : N := ⟨y1⁻¹ * y2, hyn⟩
      have hxmul : x1 * nx.1 = x2 := by dsimp [nx]; group
      have hymul : y1 * ny.1 = y2 := by dsimp [ny]; group
      rw [← hxmul, ← hymul,
        kernelNormalized_left_coset N c hczero,
        kernelNormalized_right_coset N c hczero])
  have hbar_mk (g h : G) :
      bar (quotientMk N g, quotientMk N h) = c.1 (g, h) := rfl
  have hbar : Continuous bar := by
    have hq := QuotientGroup.isQuotientMap_mk N
    apply hq.continuous_lift_prod_left
    apply hq.continuous_lift_prod_right
    have hpull : (fun p : G × G => bar (quotientMk N p.1, quotientMk N p.2)) = c.1 := by
      funext p
      exact hbar_mk p.1 p.2
    change Continuous fun p : G × G => bar (quotientMk N p.1, quotientMk N p.2)
    rw [hpull]
    exact hccont
  refine ⟨psi, hpsi, bar, hbar, ?_⟩
  intro g h
  exact hbar_mk g h

/-- If every two-cocycle can be kernel-normalized, degree-two inflation from `G/N` is onto. -/
theorem surjective_inf2_of_forall_kernelNormalized
    (hcompat : ∀ (g : G) (m : M), quotientMk N g • m = g • m)
    (hnorm : ∀ z : Z2 G M, H2KernelNormalizedCorrection N z) :
    Function.Surjective (inf2 (quotientMk N) hcompat) := by
  rw [surjective_inf2_iff_forall_cocycleInflationDescent
    (quotientMk N) (quotientMk_surjective N) hcompat]
  intro z
  exact h2CocycleInflationDescent_of_kernelNormalized N z (hnorm z)

end NormalizedDescent

section OneTwoPackage

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

variable (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)]
variable [DistribMulAction (G ⧸ N) M] [ContinuousSMul (G ⧸ N) M]

/-- Literal vanishing of continuous degree-two cohomology. -/
def ContinuousH2Vanishes
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction H M] [ContinuousSMul H M] : Prop :=
  ∀ x : H2 H M, x = 0

/-- If `H²(N,M)` vanishes, the restriction of every ambient two-cocycle has a continuous
primitive on `N`. -/
theorem kernelH2Primitive_of_vanishes
    (hvan : ContinuousH2Vanishes N M) (z : Z2 G M) :
    ∃ phi : N → M, Continuous phi ∧
      ∀ n k : N, dOne N M phi (n, k) = z.1 (n.1, k.1) := by
  let rz : Z2 N M :=
    Z2comap (subgroupIncl G N) (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) z
  have hz : H2mk N M rz = 0 := hvan (H2mk N M rz)
  have hmem := (QuotientAddGroup.eq_zero_iff rz).mp hz
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨phi, hphi, hphi_eq⟩ := hmem
  refine ⟨phi, hphi, ?_⟩
  intro n k
  exact congrFun hphi_eq (n, k)

/-- A cochain-level degree `1`--`2` Hochschild--Serre package for one coefficient module.

`kernelH2Vanishes` is the literal `H^2(N,M)=0` input.  The second field is the remaining
degree-one/transgression coherence: it extends the negative kernel primitive and kills both
cross terms.  This field is intentionally stated before forming `G/N`; it is the exact place
where conjugation invariance, not merely kernelwise splitting, must be proved. -/
structure KernelHochschildSerreOneTwoPackage : Prop where
  kernelH2Vanishes : ContinuousH2Vanishes N M
  kernelH1Transgression : ∀ (z : Z2 G M) (phi : N → M),
    Continuous phi →
    (∀ n k : N, dOne N M phi (n, k) = z.1 (n.1, k.1)) →
    ∃ psi : G → M, Continuous psi ∧
      (∀ n : N, psi n.1 = -phi n) ∧
      ∀ (g : G) (n : N),
        (z.1 + dOne G M psi) (g, n.1) = 0 ∧
        (z.1 + dOne G M psi) (n.1, g) = 0

/-- The degree `1`--`2` kernel package produces the normalization required for descent. -/
theorem KernelHochschildSerreOneTwoPackage.kernelNormalized
    (D : KernelHochschildSerreOneTwoPackage (M := M) N) (z : Z2 G M) :
    H2KernelNormalizedCorrection N z := by
  obtain ⟨phi, hphi, hprim⟩ :=
    kernelH2Primitive_of_vanishes (M := M) N D.kernelH2Vanishes z
  obtain ⟨psi, hpsi, _hext, hcross⟩ :=
    D.kernelH1Transgression (M := M) z phi hphi hprim
  exact ⟨psi, hpsi, hcross⟩

/-- The honest kernel `H^1`--`H^2` criterion implies degree-two inflation surjectivity. -/
theorem KernelHochschildSerreOneTwoPackage.surjective_inf2
    (D : KernelHochschildSerreOneTwoPackage (M := M) N)
    (hcompat : ∀ (g : G) (m : M), quotientMk N g • m = g • m) :
    Function.Surjective (inf2 (quotientMk N) hcompat) :=
  surjective_inf2_of_forall_kernelNormalized N hcompat
    (fun z => KernelHochschildSerreOneTwoPackage.kernelNormalized (M := M) N D z)

end OneTwoPackage

/-! ## Coefficient-uniform maximal-pro-2 and Sylow packages -/

section MaxProTwoSupply

variable {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Uniform kernel `H²`-vanishing and degree-one transgression coherence for every finite
elementary coefficient whose action factors through `G(2)`. -/
def FiniteElementaryMaxProTwoKernelOneTwoSupply : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      KernelHochschildSerreOneTwoPackage (M := M) (proPKernel 2 G)

/-- The uniform kernel package discharges the finite-elementary H²-inflation premise. -/
theorem finiteElementaryH2InflationSurjective_of_kernelOneTwo
    (D : FiniteElementaryMaxProTwoKernelOneTwoSupply (G := G)) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) := by
  intro M _ _ _ _ _ _ _ _ _ hM hcompat
  letI : IsClosed (proPKernel 2 G : Set G) := proPKernel_isClosed 2 G
  letI : DistribMulAction (G ⧸ proPKernel 2 G) M := by
    change DistribMulAction (maxProPQuotient 2 G) M
    infer_instance
  letI : ContinuousSMul (G ⧸ proPKernel 2 G) M := by
    change ContinuousSMul (maxProPQuotient 2 G) M
    infer_instance
  apply (maxProTwoH2CocycleDescent_iff_surjective_inf2 hcompat).1
  intro z
  exact h2CocycleInflationDescent_of_kernelNormalized (proPKernel 2 G) z
    (KernelHochschildSerreOneTwoPackage.kernelNormalized
      (M := M) (proPKernel 2 G) (D M hM hcompat) z)

end MaxProTwoSupply

section SylowPreimageSupply

variable {G C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The Sylow-preimage maximal-pro-2 package with inflation supplied by honest kernel
degree-`1`--`2` data, together with the still-independent CD2 field on `U(2)`. -/
structure SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) : Prop where
  inflationKernel : FiniteElementaryMaxProTwoKernelOneTwoSupply
    (G := sylowTwoPreimage rho P)
  cdTwo : FiniteElementaryH2RightExactSupply
    (maxProPQuotient 2 (sylowTwoPreimage rho P))

/-- Kernel `H¹`--`H²` data fills the inflation field of the earlier maximal-pro-2 package. -/
theorem SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage.toCDTwoPackage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (D : SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage rho P) :
    SylowPreimageMaxProTwoCDTwoPackage rho P where
  inflation := finiteElementaryH2InflationSurjective_of_kernelOneTwo D.inflationKernel
  cdTwo := D.cdTwo

/-- Hence the kernel package reaches the scalar-kernel H² tail on the original Sylow
preimage. -/
theorem SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage.toScalarKernelH2Tail
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (D : SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage rho P) :
    TwoGroupActionScalarKernelH2Tail (sylowTwoPreimageHom rho P) :=
  D.toCDTwoPackage rho P |>.toScalarKernelH2Tail rho P

end SylowPreimageSupply

end

end GQ2.ContCoh
