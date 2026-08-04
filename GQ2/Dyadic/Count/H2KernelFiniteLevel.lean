/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.ContinuousCochainFiniteLevel
import GQ2.Dyadic.Count.H2KernelHochschildSerre

/-!
# Kernel H² vanishing as eventual finite-quotient splitting

Continuous cohomology with finite discrete coefficients is a direct limit over finite
quotients.  Consequently, `H²(G,M)=0` does **not** say that every finite quotient of `G` has
zero `H²`.  It says that every finite-level two-cocycle becomes a coboundary after pullback to
some finer finite quotient.

This file proves that exact equivalence for a profinite group acting trivially on a finite
discrete additive group.  This is the useful finite target for the remaining maximal-pro-`2`
kernel statement: quotient-compatible coefficients restrict trivially to `proPKernel 2 G`.

For central coefficients, the finite-level equation
`d¹ phi = refine c` is equivalently a splitting of the pulled-back extension represented by
`c`.  Thus the criterion can also be read as eventual splitting of every finite central/module
extension, without making the false demand that it split at its first finite level.
-/

namespace GQ2.ContCoh

noncomputable section

section FiniteLevelCochains

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M]

/-- The explicit trivial action, for an arbitrary additive coefficient group. -/
@[implicit_reducible] def trivialAddAction (H : Type) [Group H] : DistribMulAction H M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The explicit trivial action is continuous. -/
theorem continuousSMul_trivialAddAction (H : Type) [Group H] [TopologicalSpace H] :
    letI := trivialAddAction (M := M) H
    ContinuousSMul H M := by
  letI := trivialAddAction (M := M) H
  exact ⟨continuous_snd⟩

/-- Inflate a one-cochain from an open-normal finite quotient. -/
def finiteQuotientInflateOne (V : OpenNormalSubgroup G)
    (phi : (G ⧸ V.toSubgroup) → M) : G → M :=
  fun g ↦ phi (QuotientGroup.mk' V.toSubgroup g)

/-- Inflate a two-cochain from an open-normal finite quotient. -/
def finiteQuotientInflateTwo (V : OpenNormalSubgroup G)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M) : G × G → M :=
  fun p ↦ c (QuotientGroup.mk' V.toSubgroup p.1, QuotientGroup.mk' V.toSubgroup p.2)

/-- Inflate a three-cochain from an open-normal finite quotient. -/
def finiteQuotientInflateThree (V : OpenNormalSubgroup G)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M) :
    G × G × G → M :=
  fun p ↦ F (QuotientGroup.mk' V.toSubgroup p.1,
    QuotientGroup.mk' V.toSubgroup p.2.1, QuotientGroup.mk' V.toSubgroup p.2.2)

theorem continuous_finiteQuotientInflateOne (V : OpenNormalSubgroup G)
    (phi : (G ⧸ V.toSubgroup) → M) : Continuous (finiteQuotientInflateOne V phi) := by
  exact continuous_of_discreteTopology.comp QuotientGroup.continuous_mk

theorem continuous_finiteQuotientInflateTwo (V : OpenNormalSubgroup G)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M) :
    Continuous (finiteQuotientInflateTwo V c) := by
  exact continuous_of_discreteTopology.comp
    ((QuotientGroup.continuous_mk.comp continuous_fst).prodMk
      (QuotientGroup.continuous_mk.comp continuous_snd))

/-- Pull a one-cochain to a finer finite quotient. -/
def finiteQuotientRefineOne {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup) (phi : (G ⧸ V.toSubgroup) → M) :
    (G ⧸ W.toSubgroup) → M :=
  fun x ↦ phi (openNormalQuotientProj hWV x)

/-- Pull a two-cochain to a finer finite quotient. -/
def finiteQuotientRefineTwo {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M) :
    (G ⧸ W.toSubgroup) × (G ⧸ W.toSubgroup) → M :=
  fun p ↦ c (openNormalQuotientProj hWV p.1, openNormalQuotientProj hWV p.2)

theorem finiteQuotientInflate_refineOne {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup) (phi : (G ⧸ V.toSubgroup) → M) :
    finiteQuotientInflateOne W (finiteQuotientRefineOne hWV phi) =
      finiteQuotientInflateOne V phi := by
  funext g
  change phi (openNormalQuotientProj hWV
      (QuotientGroup.mk' W.toSubgroup g)) =
    phi (QuotientGroup.mk' V.toSubgroup g)
  rw [openNormalQuotientProj_mk]

theorem finiteQuotientInflate_refineTwo {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M) :
    finiteQuotientInflateTwo W (finiteQuotientRefineTwo hWV c) =
      finiteQuotientInflateTwo V c := by
  funext p
  change c (openNormalQuotientProj hWV
      (QuotientGroup.mk' W.toSubgroup p.1),
      openNormalQuotientProj hWV
        (QuotientGroup.mk' W.toSubgroup p.2)) =
    c (QuotientGroup.mk' V.toSubgroup p.1,
      QuotientGroup.mk' V.toSubgroup p.2)
  rw [openNormalQuotientProj_mk, openNormalQuotientProj_mk]

theorem finiteQuotientInflateTwo_injective (V : OpenNormalSubgroup G) :
    Function.Injective (finiteQuotientInflateTwo (M := M) V) := by
  intro c c' h
  funext p
  rcases p with ⟨p, q⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup p
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup q
  exact congrFun h (a, b)

theorem finiteQuotientInflateThree_injective (V : OpenNormalSubgroup G) :
    Function.Injective (finiteQuotientInflateThree (M := M) V) := by
  intro F F' h
  funext p
  rcases p with ⟨p, q, r⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup p
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup r
  exact congrFun h (a, b, c)

/-- Every continuous one-cochain with discrete coefficients factors through a finite quotient. -/
theorem exists_finiteQuotientCochainOne_factor (psi : G → M) (hpsi : Continuous psi) :
    ∃ (V : OpenNormalSubgroup G) (phi : (G ⧸ V.toSubgroup) → M),
      finiteQuotientInflateOne V phi = psi := by
  let padded : G × G → M := fun p ↦ psi p.1
  have hpadded : Continuous padded := hpsi.comp continuous_fst
  obtain ⟨V, hV⟩ :=
    GQ2.Dyadic.WordCoh.exists_openNormalSubgroup_factor_two padded hpadded
  let phi : (G ⧸ V.toSubgroup) → M := fun x ↦ psi (Quotient.out x)
  refine ⟨V, phi, ?_⟩
  funext g
  let a := Quotient.out (QuotientGroup.mk' V.toSubgroup g)
  have hag : a⁻¹ * g ∈ V := by
    apply QuotientGroup.leftRel_apply.mp
    exact Quotient.exact (Quotient.out_eq _)
  have h := hV a a (a⁻¹ * g) hag 1 (one_mem V)
  simpa [finiteQuotientInflateOne, phi, padded, a] using h.symm

/-- Every continuous two-cochain with discrete coefficients factors through a finite quotient. -/
theorem exists_finiteQuotientCochainTwo_factor (k : G × G → M) (hk : Continuous k) :
    ∃ (V : OpenNormalSubgroup G)
      (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M),
      finiteQuotientInflateTwo V c = k := by
  obtain ⟨V, hV⟩ := GQ2.Dyadic.WordCoh.exists_openNormalSubgroup_factor_two k hk
  let c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M :=
    fun p ↦ k (Quotient.out p.1, Quotient.out p.2)
  refine ⟨V, c, ?_⟩
  funext p
  let a := Quotient.out (QuotientGroup.mk' V.toSubgroup p.1)
  let b := Quotient.out (QuotientGroup.mk' V.toSubgroup p.2)
  have ha : a⁻¹ * p.1 ∈ V := by
    apply QuotientGroup.leftRel_apply.mp
    exact Quotient.exact (Quotient.out_eq _)
  have hb : b⁻¹ * p.2 ∈ V := by
    apply QuotientGroup.leftRel_apply.mp
    exact Quotient.exact (Quotient.out_eq _)
  have h := hV a b (a⁻¹ * p.1) ha (b⁻¹ * p.2) hb
  simpa [finiteQuotientInflateTwo, c, a, b] using h.symm

/-- Inflation commutes with `d¹` when the action upstairs is trivial. -/
theorem dOne_finiteQuotientInflateOne
    [DistribMulAction G M] [ContinuousSMul G M]
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (V : OpenNormalSubgroup G) (phi : (G ⧸ V.toSubgroup) → M) :
    letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup)
    dOne G M (finiteQuotientInflateOne V phi) =
      finiteQuotientInflateTwo V (dOne (G ⧸ V.toSubgroup) M phi) := by
  letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup)
  funext p
  have htrivQ (q : G ⧸ V.toSubgroup) (m : M) : q • m = m := rfl
  simp [dOne, finiteQuotientInflateOne, finiteQuotientInflateTwo, htriv, htrivQ]

/-- Inflation commutes with `d²` when the action upstairs is trivial. -/
theorem dTwo_finiteQuotientInflateTwo
    [DistribMulAction G M] [ContinuousSMul G M]
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (V : OpenNormalSubgroup G)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M) :
    letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup)
    dTwo G M (finiteQuotientInflateTwo V c) =
      finiteQuotientInflateThree V (dTwo (G ⧸ V.toSubgroup) M c) := by
  letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup)
  funext p
  have htrivQ (q : G ⧸ V.toSubgroup) (m : M) : q • m = m := rfl
  simp [dTwo, finiteQuotientInflateTwo, finiteQuotientInflateThree, htriv, htrivQ]

end FiniteLevelCochains

section ExactCriterion

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Eventual finite-level vanishing of `H²`: every cocycle on `G/V` becomes a coboundary on
some finer quotient `G/W`.  This is a direct-limit statement, not levelwise finite `H²`
vanishing. -/
def FiniteRefinementTrivialHTwoVanishes : Prop :=
  ∀ (V : OpenNormalSubgroup G)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → M),
    (letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup);
      dTwo (G ⧸ V.toSubgroup) M c = 0) →
      ∃ (W : OpenNormalSubgroup G) (hWV : W.toSubgroup ≤ V.toSubgroup)
        (phi : (G ⧸ W.toSubgroup) → M),
        (letI := trivialAddAction (M := M) (G ⧸ W.toSubgroup);
          dOne (G ⧸ W.toSubgroup) M phi = finiteQuotientRefineTwo hWV c)

/-- Literal continuous `H²`-vanishing with trivial finite coefficients is equivalent to
eventual coboundary after passage to a finer finite quotient. -/
theorem finiteRefinementTrivialHTwoVanishes_iff_continuousH2Vanishes
    (htriv : ∀ (g : G) (m : M), g • m = m) :
    FiniteRefinementTrivialHTwoVanishes (G := G) (M := M) ↔
      ContinuousH2Vanishes G M := by
  constructor
  · intro S x
    obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := M) x
    obtain ⟨V, c, hfactor⟩ := exists_finiteQuotientCochainTwo_factor z.1
      (mem_Z2_iff.mp z.2).1
    have hcocycle :
        letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup)
        dTwo (G ⧸ V.toSubgroup) M c = 0 := by
      letI := trivialAddAction (M := M) (G ⧸ V.toSubgroup)
      apply finiteQuotientInflateThree_injective (G := G) V
      rw [← dTwo_finiteQuotientInflateTwo htriv, hfactor]
      exact z.2.2
    obtain ⟨W, hWV, phi, hphi⟩ := S V c hcocycle
    let psi : G → M := finiteQuotientInflateOne W phi
    have hpsi : Continuous psi := continuous_finiteQuotientInflateOne W phi
    have hdpsi : dOne G M psi = z.1 := by
      rw [dOne_finiteQuotientInflateOne htriv, hphi,
        finiteQuotientInflate_refineTwo hWV, hfactor]
    apply (QuotientAddGroup.eq_zero_iff z).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    exact ⟨psi, hpsi, hdpsi⟩
  · intro hvan V c hcocycle
    let zfun : G × G → M := finiteQuotientInflateTwo V c
    have hzcont : Continuous zfun := continuous_finiteQuotientInflateTwo V c
    have hzcocycle : dTwo G M zfun = 0 := by
      rw [dTwo_finiteQuotientInflateTwo htriv, hcocycle]
      rfl
    have hzmem : zfun ∈ Z2 G M := by
      apply mem_Z2_iff.mpr
      refine ⟨hzcont, ?_⟩
      intro a b c'
      apply sub_eq_zero.mp
      calc
        (a • zfun (b, c') + zfun (a, b * c')) -
              (zfun (a * b, c') + zfun (a, b)) =
            dTwo G M zfun (a, b, c') := by
              simp only [dTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
              abel
        _ = 0 := congrFun hzcocycle (a, b, c')
    let z : Z2 G M := ⟨zfun, hzmem⟩
    have hzzero : H2mk G M z = 0 := hvan (H2mk G M z)
    have hzmem := (QuotientAddGroup.eq_zero_iff z).mp hzzero
    rw [AddSubgroup.mem_addSubgroupOf] at hzmem
    obtain ⟨psi, hpsi, hdpsi⟩ := hzmem
    obtain ⟨U, phi, hfactor⟩ := exists_finiteQuotientCochainOne_factor psi hpsi
    let W : OpenNormalSubgroup G := U ⊓ V
    have hWU : W.toSubgroup ≤ U.toSubgroup := inf_le_left
    have hWV : W.toSubgroup ≤ V.toSubgroup := inf_le_right
    refine ⟨W, hWV, finiteQuotientRefineOne hWU phi, ?_⟩
    letI := trivialAddAction (M := M) (G ⧸ W.toSubgroup)
    apply finiteQuotientInflateTwo_injective (G := G) W
    rw [← dOne_finiteQuotientInflateOne htriv,
      finiteQuotientInflate_refineOne hWU, hfactor, hdpsi,
      finiteQuotientInflate_refineTwo hWV]

end ExactCriterion

section ElementaryCoefficientReduction

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [Finite M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- For trivial actions, mod-two `H²`-vanishing implies `H²`-vanishing for every finite
elementary abelian coefficient group.

The proof is at cochain level.  Choose a finite `𝔽₂`-basis of `M`, project a given
`M`-valued two-cocycle to each scalar coordinate, choose scalar primitives, and assemble the
finitely many primitives through the inverse basis equivalence.  Finiteness of the basis makes
the assembled cochain continuous. -/
theorem continuousH2Vanishes_of_zmodTwo
    (hM₂ : ∀ m : M, m + m = 0)
    (htrivM : ∀ (g : G) (m : M), g • m = m)
    (htriv₂ : ∀ (g : G) (a : ZMod 2), g • a = a)
    (hscalar : ContinuousH2Vanishes G (ZMod 2)) :
    ContinuousH2Vanishes G M := by
  classical
  letI : Module (ZMod 2) M :=
    AddCommGroup.zmodModule (fun m ↦ by rw [two_nsmul]; exact hM₂ m)
  letI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) M
  let e : M ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) M) → ZMod 2) := b.equivFun
  intro x
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := M) x
  let zi (i : Fin (Module.finrank (ZMod 2) M)) : Z2 G (ZMod 2) :=
    ⟨fun p ↦ e (z.1 p) i, by
      apply mem_Z2_iff.mpr
      have heval : Continuous (fun m : M ↦ e m i) := continuous_of_discreteTopology
      refine ⟨heval.comp (mem_Z2_iff.mp z.2).1, ?_⟩
      intro g h k
      have hz := (mem_Z2_iff.mp z.2).2 g h k
      have hz' : z.1 (h, k) + z.1 (g, h * k) =
          z.1 (g * h, k) + z.1 (g, h) := by
        simpa only [htrivM] using hz
      simpa only [htriv₂, map_add, Pi.add_apply] using
        congrArg (fun m : M ↦ e m i) hz'⟩
  have hex : ∀ i : Fin (Module.finrank (ZMod 2) M),
      ∃ psi : G → ZMod 2, Continuous psi ∧ dOne G (ZMod 2) psi = (zi i).1 := by
    intro i
    have hzero : H2mk G (ZMod 2) (zi i) = 0 := hscalar (H2mk G (ZMod 2) (zi i))
    have hmem := (QuotientAddGroup.eq_zero_iff (zi i)).mp hzero
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    exact hmem
  choose psi hpsi hdpsi using hex
  let Psi : G → (Fin (Module.finrank (ZMod 2) M) → ZMod 2) :=
    fun g i ↦ psi i g
  have hPsi : Continuous Psi := continuous_pi fun i ↦ hpsi i
  let phi : G → M := fun g ↦ e.symm (Psi g)
  have hphi : Continuous phi := continuous_of_discreteTopology.comp hPsi
  have hdphi : dOne G M phi = z.1 := by
    funext p
    apply e.injective
    ext i
    have hi := congrFun (hdpsi i) p
    simpa only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, phi, Psi, zi,
      htrivM, htriv₂, map_sub, map_add, LinearEquiv.apply_symm_apply,
      Pi.sub_apply, Pi.add_apply] using hi
  apply (QuotientAddGroup.eq_zero_iff z).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  exact ⟨phi, hphi, hdphi⟩

end ElementaryCoefficientReduction

end

end GQ2.ContCoh
