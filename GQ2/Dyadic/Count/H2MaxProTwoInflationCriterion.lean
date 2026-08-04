/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2MaxProTwoTransport

/-!
# An exact cocycle criterion for maximal-pro-2 H² inflation

The universal property of `G(2)` does not, by itself, make
`H²(G(2), M) → H²(G, M)` onto.  A degree-two class descends precisely when one can change a
continuous cocycle representative by a continuous coboundary so that the resulting cocycle is
the pullback of a continuous cochain on `G(2)`.  The cochain downstairs is then automatically a
cocycle.

This file packages that statement at the explicit cochain level.  It also records the first
necessary consequence: the restriction of a descending cocycle to the pro-2 kernel is an
explicit continuous coboundary.  The converse to that kernel test is deliberately not claimed;
additional invariance/transgression coherence is needed in general.
-/

namespace GQ2.ContCoh

noncomputable section

section GeneralQuotient

variable {G Q M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [DistribMulAction Q M] [ContinuousSMul Q M]

/-- A cocycle descends along `pi` after a continuous one-cochain correction.

The raw function `bar` is required only to be continuous and to pull back to
`z + d¹ psi`; when `pi` is onto, the cocycle identity for `bar` follows from the cocycle
identity upstairs. -/
def H2CocycleInflationDescent
    (pi : ContinuousMonoidHom G Q)
    (z : Z2 G M) : Prop :=
  ∃ psi : G → M, Continuous psi ∧
    ∃ bar : Q × Q → M, Continuous bar ∧
      ∀ g h : G,
        bar (pi g, pi h) = z.1 (g, h) + dOne G M psi (g, h)

/-- The cochain downstairs in a descent datum is automatically a two-cocycle. -/
theorem h2CocycleInflationDescent_bar_mem_Z2
    (pi : ContinuousMonoidHom G Q)
    (hpi : Function.Surjective pi)
    (hcompat : ∀ (g : G) (m : M), pi g • m = g • m)
    (z : Z2 G M) (psi : G → M) (hpsi : Continuous psi)
    (bar : Q × Q → M) (hbar : Continuous bar)
    (hdesc : ∀ g h : G,
      bar (pi g, pi h) = z.1 (g, h) + dOne G M psi (g, h)) :
    bar ∈ Z2 Q M := by
  have hcob : dOne G M psi ∈ Z2 G M := by
    apply B2_le_Z2
    exact ⟨psi, hpsi, rfl⟩
  have hsum : (z.1 + dOne G M psi) ∈ Z2 G M :=
    (Z2 G M).add_mem z.2 hcob
  refine mem_Z2_iff.mpr ⟨hbar, ?_⟩
  intro q r s
  obtain ⟨g, rfl⟩ := hpi q
  obtain ⟨h, rfl⟩ := hpi r
  obtain ⟨k, rfl⟩ := hpi s
  have hcoc := (mem_Z2_iff.mp hsum).2 g h k
  rw [hdesc h k, ← map_mul, hdesc g (h * k), ← map_mul,
    hdesc (g * h) k, hdesc g h, hcompat]
  exact hcoc

/-- Exact range criterion for degree-two inflation along a continuous epimorphism.

This is stronger information than the proposition `Function.Surjective (inf2 ...)`: it exposes
the actual cochain correction and the continuous descended cochain that a proof must build. -/
theorem h2CocycleInflationDescent_iff_mem_range
    (pi : ContinuousMonoidHom G Q)
    (hpi : Function.Surjective pi)
    (hcompat : ∀ (g : G) (m : M), pi g • m = g • m)
    (z : Z2 G M) :
    H2CocycleInflationDescent pi z ↔
      H2mk G M z ∈ Set.range (inf2 pi hcompat) := by
  constructor
  · rintro ⟨psi, hpsi, bar, hbar, hdesc⟩
    let w : Z2 Q M :=
      ⟨bar, h2CocycleInflationDescent_bar_mem_Z2
        pi hpi hcompat z psi hpsi bar hbar hdesc⟩
    have hcob : dOne G M psi ∈ Z2 G M := by
      apply B2_le_Z2
      exact ⟨psi, hpsi, rfl⟩
    let cob : Z2 G M := ⟨dOne G M psi, hcob⟩
    let zw : Z2 G M :=
      Z2comap pi (AddMonoidHom.id M) continuous_id hcompat w
    have hzw : zw = z + cob := by
      apply Subtype.ext
      funext p
      exact hdesc p.1 p.2
    refine ⟨H2mk Q M w, ?_⟩
    rw [inf2_H2mk]
    change H2mk G M zw = H2mk G M z
    rw [hzw, map_add]
    have hcob0 : H2mk G M cob = 0 := by
      apply (QuotientAddGroup.eq_zero_iff cob).mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      exact ⟨psi, hpsi, rfl⟩
    rw [hcob0, add_zero]
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := H2mk_surjective (G := Q) (M := M) y
    rw [inf2_H2mk] at hy
    let zw : Z2 G M :=
      Z2comap pi (AddMonoidHom.id M) continuous_id hcompat w
    change H2mk G M zw = H2mk G M z at hy
    have hzero : H2mk G M (zw - z) = 0 := by
      rw [map_sub, hy, sub_self]
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp hzero
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨psi, hpsi, hpsi_eq⟩ := hmem
    refine ⟨psi, hpsi, w.1, (mem_Z2_iff.mp w.2).1, ?_⟩
    intro g h
    have hp := congrFun hpsi_eq (g, h)
    change dOne G M psi (g, h) = zw.1 (g, h) - z.1 (g, h) at hp
    have hzwapp : zw.1 (g, h) = w.1 (pi g, pi h) := rfl
    rw [hp, hzwapp]
    abel

/-- Degree-two inflation is onto exactly when every continuous cocycle admits the explicit
descent datum above. -/
theorem surjective_inf2_iff_forall_cocycleInflationDescent
    (pi : ContinuousMonoidHom G Q)
    (hpi : Function.Surjective pi)
    (hcompat : ∀ (g : G) (m : M), pi g • m = g • m) :
    Function.Surjective (inf2 pi hcompat) ↔
      ∀ z : Z2 G M, H2CocycleInflationDescent pi z := by
  constructor
  · intro hinf z
    apply (h2CocycleInflationDescent_iff_mem_range pi hpi hcompat z).2
    exact hinf (H2mk G M z)
  · intro hdesc y
    obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := M) y
    exact (h2CocycleInflationDescent_iff_mem_range pi hpi hcompat z).1 (hdesc z)

end GeneralQuotient

section MaxProTwo

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [DistribMulAction (maxProPQuotient 2 G) M]
  [ContinuousSMul (maxProPQuotient 2 G) M]

/-- The explicit continuous-cocycle descent supply for one coefficient module on `G(2)`. -/
def MaxProTwoH2CocycleDescent : Prop :=
  ∀ z : Z2 G M, H2CocycleInflationDescent (maxProPMk 2 G) z

/-- Maximal-pro-2 H² inflation for one coefficient is onto iff every cocycle has an explicit
continuous descent datum. -/
theorem maxProTwoH2CocycleDescent_iff_surjective_inf2
    (hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m) :
    MaxProTwoH2CocycleDescent (G := G) (M := M) ↔
      Function.Surjective (inf2 (maxProPMk 2 G) hcompat) := by
  exact (surjective_inf2_iff_forall_cocycleInflationDescent
    (maxProPMk 2 G) (quotientMk_surjective (proPKernel 2 G)) hcompat).symm

/-- A descending cocycle restricts to an explicit continuous coboundary on the pro-2 kernel.

This is only a necessary test: kernelwise splitting alone does not encode the conjugation
coherence needed to descend the extension to `G(2)`. -/
theorem h2CocycleInflationDescent_kernel_coboundary
    (hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m)
    (z : Z2 G M)
    (hdesc : H2CocycleInflationDescent (maxProPMk 2 G) z) :
    ∃ phi : proPKernel 2 G → M, Continuous phi ∧
      ∀ k l : proPKernel 2 G,
        dOne (proPKernel 2 G) M phi (k, l) = z.1 (k.1, l.1) := by
  obtain ⟨psi, hpsi, bar, _hbar, hbar⟩ := hdesc
  let c : M := bar (1, 1)
  let phi : proPKernel 2 G → M := fun k => c - psi k.1
  refine ⟨phi, continuous_const.sub (hpsi.comp continuous_subtype_val), ?_⟩
  intro k l
  have hk : maxProPMk 2 G k.1 = 1 := by
    exact QuotientGroup.eq_one_iff k.1 |>.mpr k.2
  have hl : maxProPMk 2 G l.1 = 1 := by
    exact QuotientGroup.eq_one_iff l.1 |>.mpr l.2
  have hact (m : M) : k • m = m := by
    change k.1 • m = m
    rw [← hcompat k.1 m, hk, one_smul]
  have hd := hbar k.1 l.1
  rw [hk, hl] at hd
  change k • (c - psi l.1) - (c - psi (k.1 * l.1)) + (c - psi k.1) = z.1 (k.1, l.1)
  rw [hact]
  dsimp [c] at ⊢
  change bar (1, 1) = z.1 (k.1, l.1) +
      (k.1 • psi l.1 - psi (k.1 * l.1) + psi k.1) at hd
  rw [← hcompat k.1 (psi l.1), hk, one_smul] at hd
  rw [hd]
  abel

end MaxProTwo

/-! ## Coefficient-uniform reformulation used by the Sylow-preimage package -/

section FiniteElementary

variable {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Coefficient-uniform explicit cocycle descent from `G` to `G(2)`. -/
def FiniteElementaryMaxProTwoH2CocycleDescent (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      MaxProTwoH2CocycleDescent (G := G) (M := M)

/-- The finite-elementary inflation premise is equivalent to constructing explicit descent
data for every finite elementary cocycle.  This is the exact first premise that remains for
each `GammaL` Sylow preimage. -/
theorem finiteElementaryH2InflationSurjective_maxProPMk_iff_descent :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) ↔
      FiniteElementaryMaxProTwoH2CocycleDescent G := by
  constructor
  · intro hinf M _ _ _ _ _ _ _ _ _ hM2 hcompat
    exact (maxProTwoH2CocycleDescent_iff_surjective_inf2 hcompat).2
      (hinf M hM2 hcompat)
  · intro hdesc M _ _ _ _ _ _ _ _ _ hM2 hcompat
    exact (maxProTwoH2CocycleDescent_iff_surjective_inf2 hcompat).1
      (hdesc M hM2 hcompat)

end FiniteElementary

section SylowPreimage

variable {G C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The Sylow-preimage maximal-pro-2 package with its inflation premise replaced by the exact
continuous cocycle-descent construction. -/
structure SylowPreimageMaxProTwoCocycleDescentCDTwoPackage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) : Prop where
  inflationDescent : FiniteElementaryMaxProTwoH2CocycleDescent
    (sylowTwoPreimage rho P)
  cdTwo : FiniteElementaryH2RightExactSupply
    (maxProPQuotient 2 (sylowTwoPreimage rho P))

/-- Explicit cocycle descent fills exactly the inflation field of the earlier transport
package; the finite-elementary CD2 field remains unchanged. -/
theorem SylowPreimageMaxProTwoCocycleDescentCDTwoPackage.toCDTwoPackage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (D : SylowPreimageMaxProTwoCocycleDescentCDTwoPackage rho P) :
    SylowPreimageMaxProTwoCDTwoPackage rho P where
  inflation :=
    finiteElementaryH2InflationSurjective_maxProPMk_iff_descent.mpr
      D.inflationDescent
  cdTwo := D.cdTwo

/-- Hence the explicit descent package supplies the scalar-kernel H² tail on the original
Sylow preimage. -/
theorem SylowPreimageMaxProTwoCocycleDescentCDTwoPackage.toScalarKernelH2Tail
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (D : SylowPreimageMaxProTwoCocycleDescentCDTwoPackage rho P) :
    TwoGroupActionScalarKernelH2Tail (sylowTwoPreimageHom rho P) :=
  D.toCDTwoPackage rho P |>.toScalarKernelH2Tail rho P

end SylowPreimage

end

end GQ2.ContCoh
