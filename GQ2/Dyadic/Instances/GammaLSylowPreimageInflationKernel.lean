/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageInflationCriterion
import GQ2.SectionSix
import GQ2.Prop32
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.Separation.Profinite

/-!
# The maximal-pro-2 kernel boundary for GammaL inflation

This file specializes the Hochschild--Serre kernel package to
`K₂(G) = proPKernel 2 G`, and then to a `GammaL` Sylow preimage `U`.

There is one unconditional degree-one consequence of the definition of `K₂(G)` which is
important here.  If a finite elementary coefficient action factors through `G(2)`, then every
*ambient* continuous crossed cocycle `G → M` vanishes on `K₂(G)`.  Its graph lands in the
finite semidirect product of `M` by the action image.  That action image is a `2`-group because
it is a finite continuous quotient of `G(2)`, so the graph target is a finite `2`-group and the
universal property of `K₂(G)` kills the graph.

This is deliberately not promoted to intrinsic `H¹(K₂(G),M)=0`: a finite quotient of the
subgroup `K₂(G)` need not extend to an ambient finite quotient of `G`.  For the same reason,
absence of ambient finite `2`-quotients does not imply `H²(K₂(G),M)=0`.

The final definitions split the exact remaining inflation input into:

* literal continuous `H²(K₂(G),M)` vanishing; and
* the primitive-extension/cross-term theorem (the Hochschild--Serre transgression coherence).

Together they reconstruct `FiniteElementaryMaxProTwoKernelOneTwoSupply`, hence degree-two
inflation.  Existing odd-index corestriction applies to the open Sylow preimage `U ≤ GammaL`;
it does not directly apply to `K₂(U)`, which is only known closed and generally has infinite
index.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.LSquare GQ2.SectionSix

section AutomaticDegreeOne

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [Finite M]
  [DistribMulAction G M]
  [DistribMulAction (maxProPQuotient 2 G) M]
  [ContinuousSMul (maxProPQuotient 2 G) M]

/-- A coefficient action factoring through `G(2)` is trivial on `K₂(G)`. -/
theorem maxProTwoKernel_smul_eq
    (hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m)
    (k : proPKernel 2 G) (m : M) : k.1 • m = m := by
  rw [← hcompat k.1 m]
  have hk : maxProPMk 2 G k.1 = 1 :=
    (QuotientGroup.eq_one_iff k.1).mpr k.2
  rw [hk, one_smul]

/-- Every ambient continuous crossed cocycle with finite elementary quotient-compatible
coefficients vanishes on the maximal-pro-`2` kernel.

The finite graph target is `M ⋊ im(G(2) → AddAut(M))`.  The image is a finite `2`-group, and
the elementary additive group `M` also has `2`-power cardinality, so the semidirect product is
a finite `2`-group. -/
theorem maxProTwoKernel_ambientZ1_apply_eq_zero
    (hM2 : ∀ m : M, m + m = 0)
    (hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m)
    (z : Z1 G M) (k : proPKernel 2 G) : z.1 k.1 = 0 := by
  let Q := maxProPQuotient 2 G
  let actionFull : ContinuousMonoidHom Q (Multiplicative (AddAut M)) :=
    finiteActionHom (G := Q) (M := M)
  let C : Type := actionFull.toMonoidHom.range
  let action : ContinuousMonoidHom Q C := {
    toMonoidHom := actionFull.toMonoidHom.rangeRestrict
    continuous_toFun := actionFull.continuous_toFun.subtype_mk _ }
  have hCpro : IsProP 2 C :=
    SectionThree.isProP_of_surjective action.toMonoidHom action.continuous_toFun
      actionFull.toMonoidHom.rangeRestrict_surjective isProP_maxProPQuotient
  let botOpen : OpenNormalSubgroup C :=
    ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩
  have hC : IsPGroup 2 C :=
    (hCpro botOpen).of_equiv QuotientGroup.quotientBot
  letI : Finite (SemiProd C M) := by
    change Finite (M × C)
    infer_instance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : IsPGroup 2 (Multiplicative M) := fun m => ⟨1, by
    show m ^ 2 = 1
    rw [pow_two, ← ofAdd_toAdd m, ← ofAdd_add, hM2, ofAdd_zero]⟩
  obtain ⟨a, ha⟩ :=
    (IsPGroup.iff_card (p := 2) (G := Multiplicative M)).mp hM
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2) (G := C)).mp hC
  have hSemi : IsPGroup 2 (SemiProd C M) :=
    IsPGroup.of_card (n := a + b) (by
      change Nat.card (M × C) = 2 ^ (a + b)
      rw [Nat.card_prod, ← Nat.card_congr Multiplicative.toAdd, ha, hb, pow_add])
  let graph : ContinuousMonoidHom G (SemiProd C M) := {
    toFun g := (z.1 g, action (maxProPMk 2 G g))
    map_one' := by
      change (z.1 1, action (maxProPMk 2 G 1)) = ((0 : M), (1 : C))
      rw [Z1_apply_one, map_one, map_one]
    map_mul' g h := by
      apply Prod.ext
      · change z.1 (g * h) = z.1 g +
          action (maxProPMk 2 G g) • z.1 h
        rw [(mem_Z1_iff.mp z.2).2, ← hcompat]
        rfl
      · change action (maxProPMk 2 G (g * h)) =
          action (maxProPMk 2 G g) * action (maxProPMk 2 G h)
        rw [map_mul, map_mul]
    continuous_toFun := by
      have hp : Continuous fun g : G =>
          ((z.1 g, action (maxProPMk 2 G g)) : M × C) :=
        (mem_Z1_iff.mp z.2).1.prodMk (action.continuous_toFun.comp
          (maxProPMk 2 G).continuous_toFun)
      change @Continuous G (M × C) _ ⊥ _
      rw [← @DiscreteTopology.eq_bot (M × C) _ inferInstance]
      exact hp }
  have hk := proPKernel_le_ker (isProP_of_isPGroup hSemi) graph k.2
  have hk' : graph k.1 = 1 := hk
  exact congrArg Prod.fst hk'

end AutomaticDegreeOne

section ContinuousExtension

variable {G M : Type*}
  [TopologicalSpace G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]

/-- A continuous map from a closed subgroup of a profinite space to a finite discrete additive
group extends to a continuous function on the ambient space.

This is purely topological.  The fibers of the original map are a finite disjoint family of
closed subsets; `exists_clopen_partition_of_clopen_cover` enlarges them to a disjoint clopen
partition of the ambient space, on which the extension is locally constant. -/
theorem exists_continuous_extension_of_closed_subgroup
    [Group G] (N : Subgroup G) [IsClosed (N : Set G)]
    (phi : N → M) (hphi : Continuous phi) :
    ∃ psi : G → M, Continuous psi ∧ ∀ n : N, psi n.1 = phi n := by
  let Z : M → Set G := fun m => ((↑) : N → G) '' (phi ⁻¹' {m})
  have hemb : Topology.IsClosedEmbedding ((↑) : N → G) :=
    (show IsClosed (N : Set G) from inferInstance).isClosedEmbedding_subtypeVal
  have Z_closed (m : M) : IsClosed (Z m) :=
    hemb.isClosed_iff_image_isClosed.mp
      (IsClosed.preimage hphi isClosed_singleton)
  have Z_disj : (Set.univ : Set M).PairwiseDisjoint Z := by
    rw [Set.pairwiseDisjoint_iff]
    simp only [Set.image_inter_nonempty_iff, Z]
    rintro _ _ _ _ ⟨_, rfl, ⟨_, rfl, hy⟩⟩
    rw [Subtype.val_injective hy]
  let D : M → Set G := fun _ => Set.univ
  have D_clopen (m : M) : IsClopen (D m) := isClopen_univ
  have Z_subset_D (m : M) : Z m ⊆ D m := Set.subset_univ _
  obtain ⟨C, C_clopen, Z_subset_C, _C_subset_D, C_cover_D, C_disj⟩ :=
    exists_clopen_partition_of_clopen_cover Z_closed D_clopen Z_subset_D Z_disj
  have D_cover_univ : Set.univ ⊆ ⋃ m, D m := by
    intro g _
    exact Set.mem_iUnion.mpr ⟨(0 : M), Set.mem_univ g⟩
  have C_cover_univ : ⋃ m, C m = Set.univ :=
    Set.univ_subset_iff.mp (Set.Subset.trans D_cover_univ C_cover_D)
  have h_glue (i j : M) (g : G) (hgi : g ∈ C i) (hgj : g ∈ C j) : i = j := by
    rw [Set.pairwiseDisjoint_iff] at C_disj
    exact C_disj (by simp) (by simp) ⟨g, by grind⟩
  let psi : G → M := Set.liftCover C (fun m _ => m) h_glue C_cover_univ
  have hpsi : Continuous psi := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro m
    convert! (C_clopen m).isOpen
    ext g
    simp [psi, Set.preimage_liftCover]
  refine ⟨psi, hpsi, ?_⟩
  intro n
  have hnZ : n.1 ∈ Z (phi n) := ⟨n, by simp, rfl⟩
  exact Set.liftCover_of_mem (Z_subset_C (phi n) hnZ)

variable [Group G] [IsTopologicalGroup G]

/-- In particular, the negative of every continuous kernel primitive has a continuous ambient
extension.  Thus the unresolved transgression input is not the existence of a continuous
extension as a function; it is the two cross-term identities. -/
theorem exists_continuous_neg_extension_maxProTwoKernel
    (phi : proPKernel 2 G → M) (hphi : Continuous phi) :
    ∃ psi : G → M, Continuous psi ∧
      ∀ n : proPKernel 2 G, psi n.1 = -phi n := by
  letI : IsClosed (proPKernel 2 G : Set G) := proPKernel_isClosed 2 G
  exact exists_continuous_extension_of_closed_subgroup (proPKernel 2 G)
    (fun n => -phi n) hphi.neg

end ContinuousExtension

section ConjugationDefect

variable {G M : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

variable (N : Subgroup G) [N.Normal]

/-- After a two-cocycle has been made zero on `N × N`, its remaining conjugation mismatch at
`g` is the function

`n ↦ c(g,n) - c(gng⁻¹,g)`.

If both cross terms vanished this function would be zero. -/
def H2KernelConjugationDefect (c : Z2 G M) (g : G) (n : N) : M :=
  c.1 (g, n.1) - c.1 (g * n.1 * g⁻¹, g)

/-- The conjugation mismatch is an intrinsic continuous kernel one-cocycle.

This is the precise `H¹(N,M)`-shaped obstruction left by kernelwise splitting.  It is intrinsic:
the ambient-Z1 theorem above controls only restrictions of cocycles already defined on `G`, and
does not force this newly constructed cocycle on `N` to vanish. -/
theorem h2KernelConjugationDefect_mem_Z1
    (htriv : ∀ (n : N) (m : M), n.1 • m = m)
    (c : Z2 G M) (hzero : ∀ n k : N, c.1 (n.1, k.1) = 0)
    (g : G) : H2KernelConjugationDefect N c g ∈ Z1 N M := by
  refine mem_Z1_iff.mpr ⟨?_, ?_⟩
  · have hc : Continuous c.1 := (mem_Z2_iff.mp c.2).1
    have hconj : Continuous fun n : N => g * n.1 * g⁻¹ :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    exact (hc.comp (continuous_const.prodMk continuous_subtype_val)).sub
      (hc.comp (hconj.prodMk continuous_const))
  · intro n k
    let a : N := ⟨g * n.1 * g⁻¹, by
      simpa using (inferInstance : N.Normal).conj_mem n.1 n.2 g⟩
    let b : N := ⟨g * k.1 * g⁻¹, by
      simpa using (inferInstance : N.Normal).conj_mem k.1 k.2 g⟩
    have hconjmul : g * (n.1 * k.1) * g⁻¹ = a.1 * b.1 := by
      dsimp [a, b]
      group
    have hag : a.1 * g = g * n.1 := by dsimp [a]; group
    have hbg : b.1 * g = g * k.1 := by dsimp [b]; group
    have h1 := (mem_Z2_iff.mp c.2).2 g n.1 k.1
    rw [hzero n k, smul_zero, zero_add] at h1
    have h2 := (mem_Z2_iff.mp c.2).2 a.1 b.1 g
    rw [htriv a, hzero a b, add_zero] at h2
    have h3 := (mem_Z2_iff.mp c.2).2 a.1 g k.1
    rw [htriv a, hag] at h3
    change H2KernelConjugationDefect N c g (n * k) =
      H2KernelConjugationDefect N c g n + n • H2KernelConjugationDefect N c g k
    rw [show n • H2KernelConjugationDefect N c g k =
      H2KernelConjugationDefect N c g k from htriv n _]
    dsimp [H2KernelConjugationDefect]
    rw [hconjmul]
    change c.1 (g, n.1 * k.1) - c.1 (a.1 * b.1, g) =
      (c.1 (g, n.1) - c.1 (a.1, g)) +
        (c.1 (g, k.1) - c.1 (b.1, g))
    rw [← hbg] at h3
    have hx : c.1 (g * n.1, k.1) =
        c.1 (g, k.1) + c.1 (a.1, b.1 * g) - c.1 (a.1, g) := by
      rw [eq_sub_iff_add_eq]
      exact h3.symm
    rw [h1, ← h2, hx]
    abel

/-- Any correction which is zero on `N` and kills both cross terms forces the intrinsic
conjugation-defect cocycle to vanish pointwise.  Thus this `Z¹(N,M)` class is a necessary
obstruction to the cross-term correction supply; ambient-Z1 restriction vanishing does not
discharge it. -/
theorem h2KernelConjugationDefect_eq_zero_of_crossTermCorrection
    (htriv : ∀ (n : N) (m : M), n.1 • m = m)
    (c : Z2 G M) (theta : G → M)
    (htheta0 : ∀ n : N, theta n.1 = 0)
    (hcross : ∀ (g : G) (n : N),
      (c.1 + dOne G M theta) (g, n.1) = 0 ∧
      (c.1 + dOne G M theta) (n.1, g) = 0)
    (g : G) (n : N) : H2KernelConjugationDefect N c g n = 0 := by
  let a : N := ⟨g * n.1 * g⁻¹, by
    simpa using (inferInstance : N.Normal).conj_mem n.1 n.2 g⟩
  have hag : a.1 * g = g * n.1 := by dsimp [a]; group
  have hd : dOne G M theta (g, n.1) = dOne G M theta (a.1, g) := by
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [htheta0 n, htheta0 a, htriv a, hag]
    simp only [smul_zero]
    abel
  have hr := (hcross g n).1
  have hl := (hcross g a).2
  change c.1 (g, n.1) + dOne G M theta (g, n.1) = 0 at hr
  change c.1 (a.1, g) + dOne G M theta (a.1, g) = 0 at hl
  dsimp [H2KernelConjugationDefect]
  change c.1 (g, n.1) - c.1 (a.1, g) = 0
  rw [hd] at hr
  have heq : c.1 (g, n.1) = c.1 (a.1, g) :=
    add_right_cancel (hr.trans hl.symm)
  rw [heq, sub_self]

end ConjugationDefect

section UniformBoundary

variable {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The unconditional degree-one edge statement, uniformly over the coefficients used by
maximal-pro-`2` inflation.  This concerns restrictions of ambient cocycles, not all intrinsic
cocycles on `K₂(G)`. -/
def FiniteElementaryMaxProTwoKernelAmbientH1RestrictionVanishes : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      ∀ (z : Z1 G M) (k : proPKernel 2 G), z.1 k.1 = 0

/-- The ambient degree-one restriction statement holds solely from the definition of the
maximal-pro-`2` kernel. -/
theorem finiteElementaryMaxProTwoKernelAmbientH1RestrictionVanishes :
    FiniteElementaryMaxProTwoKernelAmbientH1RestrictionVanishes (G := G) := by
  intro M _ _ _ _ _ _ _ _ _ hM2 hcompat z k
  exact maxProTwoKernel_ambientZ1_apply_eq_zero hM2 hcompat z k

/-- First genuinely residual input for inflation: literal continuous `H²`-vanishing on the
maximal-pro-`2` kernel, uniformly for finite elementary quotient-compatible coefficients. -/
def FiniteElementaryMaxProTwoKernelH2VanishesSupply : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      ContinuousH2Vanishes (proPKernel 2 G) M

/-- The original degree-one/transgression field of `KernelHochschildSerreOneTwoPackage`, split
from the independent kernel `H²` statement.  The equivalent cross-term-only form below makes
clear that its continuous-extension clause is automatic. -/
def FiniteElementaryMaxProTwoKernelTransgressionSupply : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      ∀ (z : Z2 G M) (phi : proPKernel 2 G → M),
        Continuous phi →
        (∀ n k : proPKernel 2 G,
          dOne (proPKernel 2 G) M phi (n, k) = z.1 (n.1, k.1)) →
        ∃ psi : G → M, Continuous psi ∧
          (∀ n : proPKernel 2 G, psi n.1 = -phi n) ∧
          ∀ (g : G) (n : proPKernel 2 G),
            (z.1 + dOne G M psi) (g, n.1) = 0 ∧
            (z.1 + dOne G M psi) (n.1, g) = 0

/-- The genuinely residual transgression input after continuous extension has been discharged.

Starting from any continuous extension `psi0` of `-phi`, find a continuous correction `theta`
which is zero on `K₂(G)` and makes `psi0 + theta` kill both cross terms.  Requiring this for an
arbitrary extension records that the obstruction is conjugation/coset coherence, not a choice
of topological extension. -/
def FiniteElementaryMaxProTwoKernelCrossTermCorrectionSupply : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      ∀ (z : Z2 G M) (phi : proPKernel 2 G → M),
        Continuous phi →
        (∀ n k : proPKernel 2 G,
          dOne (proPKernel 2 G) M phi (n, k) = z.1 (n.1, k.1)) →
        ∀ (psi0 : G → M), Continuous psi0 →
          (∀ n : proPKernel 2 G, psi0 n.1 = -phi n) →
          ∃ theta : G → M, Continuous theta ∧
            (∀ n : proPKernel 2 G, theta n.1 = 0) ∧
            ∀ (g : G) (n : proPKernel 2 G),
              (z.1 + dOne G M (fun x => psi0 x + theta x)) (g, n.1) = 0 ∧
              (z.1 + dOne G M (fun x => psi0 x + theta x)) (n.1, g) = 0

/-- The original transgression supply is equivalent to cross-term coherence after an arbitrary
continuous extension.  The reverse implication uses the unconditional clopen-extension theorem;
the forward implication subtracts the arbitrary extension from a successful one. -/
theorem finiteElementaryMaxProTwoKernelTransgressionSupply_iff_crossTermCorrection :
    FiniteElementaryMaxProTwoKernelTransgressionSupply (G := G) ↔
      FiniteElementaryMaxProTwoKernelCrossTermCorrectionSupply (G := G) := by
  constructor
  · intro Dtr M _ _ _ _ _ _ _ _ _ hM2 hcompat z phi hphi hprim psi0 hpsi0 hext0
    obtain ⟨psi, hpsi, hext, hcross⟩ :=
      Dtr M hM2 hcompat z phi hphi hprim
    let theta : G → M := fun g => psi g - psi0 g
    refine ⟨theta, hpsi.sub hpsi0, ?_, ?_⟩
    · intro n
      dsimp [theta]
      rw [hext n, hext0 n]
      exact sub_self _
    · have hsum : (fun x => psi0 x + theta x) = psi := by
        funext x
        dsimp [theta]
        abel
      simpa only [hsum] using hcross
  · intro Dcross M _ _ _ _ _ _ _ _ _ hM2 hcompat z phi hphi hprim
    obtain ⟨psi0, hpsi0, hext0⟩ :=
      exists_continuous_neg_extension_maxProTwoKernel phi hphi
    obtain ⟨theta, htheta, htheta0, hcross⟩ :=
      Dcross M hM2 hcompat z phi hphi hprim psi0 hpsi0 hext0
    refine ⟨fun x => psi0 x + theta x, hpsi0.add htheta, ?_, hcross⟩
    intro n
    change psi0 n.1 + theta n.1 = -phi n
    rw [hext0 n, htheta0 n, add_zero]

/-- The two residual statements reconstruct the existing honest Hochschild--Serre package. -/
theorem finiteElementaryMaxProTwoKernelOneTwoSupply_of_h2Vanishes_transgression
    (D2 : FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G))
    (Dtr : FiniteElementaryMaxProTwoKernelTransgressionSupply (G := G)) :
    FiniteElementaryMaxProTwoKernelOneTwoSupply (G := G) := by
  intro M _ _ _ _ _ _ _ _ _ hM2 hcompat
  exact {
    kernelH2Vanishes := D2 M hM2 hcompat
    kernelH1Transgression := Dtr M hM2 hcompat }

/-- Consequently, these are sufficient for the finite-elementary degree-two inflation theorem. -/
theorem finiteElementaryH2InflationSurjective_of_kernelH2Vanishes_transgression
    (D2 : FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G))
    (Dtr : FiniteElementaryMaxProTwoKernelTransgressionSupply (G := G)) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) :=
  finiteElementaryH2InflationSurjective_of_kernelOneTwo
    (finiteElementaryMaxProTwoKernelOneTwoSupply_of_h2Vanishes_transgression D2 Dtr)

/-- Sharpened constructor: kernel `H²`-vanishing plus the cross-term-only coherence statement
imply degree-two inflation. -/
theorem finiteElementaryH2InflationSurjective_of_kernelH2Vanishes_crossTermCorrection
    (D2 : FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G))
    (Dcross : FiniteElementaryMaxProTwoKernelCrossTermCorrectionSupply (G := G)) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes_transgression D2
    (finiteElementaryMaxProTwoKernelTransgressionSupply_iff_crossTermCorrection.mpr Dcross)

end UniformBoundary

end


end GQ2.ContCoh

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}
variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma h q : Type) A]
  [ContinuousSMul (gamma h q : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma h q : Type) B]
  [ContinuousSMul (gamma h q : Type) B]

local notation "rhoAB" =>
  pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)

local notation "U" P => sylowTwoPreimage rhoAB P

/-- The first residual inflation statement, specialized to a `GammaL` Sylow preimage. -/
noncomputable abbrev GammaLSylowPreimageKernelH2VanishesSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := U P)

/-- The second residual inflation statement, specialized to a `GammaL` Sylow preimage. -/
noncomputable abbrev GammaLSylowPreimageKernelTransgressionSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  FiniteElementaryMaxProTwoKernelTransgressionSupply (G := U P)

/-- The sharpened cross-term-only transgression statement for a `GammaL` Sylow preimage. -/
noncomputable abbrev GammaLSylowPreimageKernelCrossTermCorrectionSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  FiniteElementaryMaxProTwoKernelCrossTermCorrectionSupply (G := U P)

/-- The ambient degree-one edge statement is unconditional for each `GammaL` Sylow preimage. -/
theorem gammaLSylowPreimageKernelAmbientH1RestrictionVanishes
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    FiniteElementaryMaxProTwoKernelAmbientH1RestrictionVanishes (G := U P) :=
  finiteElementaryMaxProTwoKernelAmbientH1RestrictionVanishes

/-- The exact two residual kernel statements imply the sought degree-two inflation theorem for
`U P`. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_kernelH2Vanishes_transgression
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D2 : GammaLSylowPreimageKernelH2VanishesSupply P)
    (Dtr : GammaLSylowPreimageKernelTransgressionSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes_transgression D2 Dtr

/-- Final sharpened boundary for the inflation field on `U P`: literal kernel `H²`-vanishing
and cross-term coherence after continuous extension. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_kernelH2Vanishes_crossTermCorrection
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D2 : GammaLSylowPreimageKernelH2VanishesSupply P)
    (Dcross : GammaLSylowPreimageKernelCrossTermCorrectionSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes_crossTermCorrection D2 Dcross

end


end GQ2.Dyadic.LSquare
