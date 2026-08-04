/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2ScalarKernelObstruction
import GQ2.Dyadic.Count.H2MaxProTwoTransport
import GQ2.Dyadic.Instances.GammaLTateDirect
import GQ2.Dyadic.SqCore.Cores

/-!
# Pro-2 coefficient CD-2 from one scalar degree-three theorem

For a pro-2 group, every finite coefficient-action image is a finite 2-group.  The existing
coefficient devissage then reduces degree-two right exactness for arbitrary finite elementary
modules to quotients with two-element kernel.  Such a kernel has trivial action.

This file closes the remaining bookkeeping step.  Its sole mathematical premise is exactness
of the continuous cochain complex in degree three for a trivial two-element coefficient group.
It proves the full `FiniteElementaryH2RightExactSupply` for a pro-2 group.  Thus an eventual
one-relator asphericity theorem for `SqCore.DSq h` need only prove the familiar scalar statement
`H^3(D_sq(h), F_2) = 0`; it need not be reproved coefficient by coefficient.

The scalar premise is quantified over abstract two-element additive groups instead of choosing
coordinates with `ZMod 2`.  This is invariantly the same single coefficient: every such group
is additively isomorphic to `ZMod 2`.  The invariant formulation avoids making the cochain
primitive depend on a noncanonical choice of generator.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.FoxH

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The explicit trivial action used to state the one-coefficient scalar theorem without
requiring a global `G`-action instance on `ZMod 2`. -/
@[implicit_reducible] def trivialZModTwoAction (G : Type) [Group G] :
    DistribMulAction G (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

omit [IsTopologicalGroup G] in
/-- Continuity of the explicit trivial action. -/
theorem continuousSMul_trivialZModTwoAction :
    letI := trivialZModTwoAction G
    ContinuousSMul G (ZMod 2) := by
  letI := trivialZModTwoAction G
  exact ⟨continuous_snd⟩

/-- The single classical scalar premise: `H^3(G, F_2) = 0`, written as exactness of continuous
inhomogeneous cochains and using the explicit trivial action. -/
def ModTwoHThreeExact (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  letI := trivialZModTwoAction G
  ∀ F : G × G × G → ZMod 2, Continuous F →
    dThree (G := G) (A := ZMod 2) F = 0 →
      ∃ k : G × G → ZMod 2, Continuous k ∧ dTwo G (ZMod 2) k = F

/-- Scalar cohomological dimension at most two, in the exact cochain-level form needed here.

For every (necessarily `F_2`) two-element discrete additive group with trivial `G`-action,
every continuous degree-three cocycle has a continuous degree-two primitive. -/
def TrivialScalarHThreeExactSupply (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ (K : Type) [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [DiscreteTopology K] [Finite K] [DistribMulAction G K] [ContinuousSMul G K],
    Nat.card K = 2 → (∀ (x : G) (k : K), x • k = k) →
      ∀ F : G × G × G → K, Continuous F →
        dThree (G := G) (A := K) F = 0 →
          ∃ k : G × G → K, Continuous k ∧ dTwo G K k = F

/-- Exactness for the single explicit coefficient `ZMod 2` supplies the invariant scalar
statement for every abstract two-element additive group. -/
theorem trivialScalarHThreeExactSupply_of_modTwo
    (S : ModTwoHThreeExact G) : TrivialScalarHThreeExactSupply G := by
  intro K _ _ _ _ _ _ _ hcard htriv F hFC hFthree
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : K ≃+ ZMod 2 :=
    (hcard ▸ zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hcard)).symm
  letI : DistribMulAction G (ZMod 2) := trivialZModTwoAction G
  letI : ContinuousSMul G (ZMod 2) := continuousSMul_trivialZModTwoAction
  let F₂ : G × G × G → ZMod 2 := fun t ↦ e (F t)
  have hF₂C : Continuous F₂ := continuous_of_discreteTopology.comp hFC
  have hF₂three : dThree (G := G) (A := ZMod 2) F₂ = 0 := by
    funext t
    have ht := congrFun hFthree t
    simp only [dThree, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at ht ⊢
    change e (F (t.2.1, t.2.2.1, t.2.2.2)) -
        e (F (t.1 * t.2.1, t.2.2.1, t.2.2.2)) +
        e (F (t.1, t.2.1 * t.2.2.1, t.2.2.2)) -
        e (F (t.1, t.2.1, t.2.2.1 * t.2.2.2)) +
        e (F (t.1, t.2.1, t.2.2.1)) = 0
    rw [← htriv t.1 (F (t.2.1, t.2.2.1, t.2.2.2))]
    simpa only [map_add, map_sub, map_zero] using congrArg e ht
  obtain ⟨k₂, hk₂C, hk₂⟩ := S F₂ hF₂C hF₂three
  let k : G × G → K := fun p ↦ e.symm (k₂ p)
  refine ⟨k, continuous_of_discreteTopology.comp hk₂C, ?_⟩
  funext t
  apply e.injective
  have ht := congrFun hk₂ t
  change k₂ (t.2.1, t.2.2) - k₂ (t.1 * t.2.1, t.2.2) +
      k₂ (t.1, t.2.1 * t.2.2) - k₂ (t.1, t.2.1) = e (F t) at ht
  change
    e (t.1 • k (t.2.1, t.2.2) - k (t.1 * t.2.1, t.2.2) +
      k (t.1, t.2.1 * t.2.2) - k (t.1, t.2.1)) = e (F t)
  rw [htriv]
  simpa only [k, map_add, map_sub, AddEquiv.apply_symm_apply] using ht

section ScalarKernel

variable {C A B : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
  [DistribMulAction C B]

omit [ContinuousSMul G A] [ContinuousSMul G B] in
/-- Trivial scalar degree-three exactness supplies the kernel-complex primitive for a
two-element coefficient kernel whose action factors through a finite 2-group. -/
theorem kernelHThreeCocyclesExact_of_trivialScalar
    (S : TrivialScalarHThreeExactSupply G)
    (rho : ContinuousMonoidHom G C) (hP : IsPGroup 2 C)
    (g : A →+ B)
    (hgG : ∀ (x : G) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hcard : Nat.card ↑g.ker = 2) :
    KernelHThreeCocyclesExact (G := G) g := by
  let hKstableG : ∀ (x : G) (a : A), a ∈ g.ker → x • a ∈ g.ker := by
    intro x a ha
    rw [AddMonoidHom.mem_ker, hgG, AddMonoidHom.mem_ker.mp ha, smul_zero]
  let hKstableC : ∀ (c : C) (a : A), a ∈ g.ker → c • a ∈ g.ker := by
    intro c a ha
    rw [AddMonoidHom.mem_ker, hgC, AddMonoidHom.mem_ker.mp ha, smul_zero]
  letI : DistribMulAction G ↑g.ker := stableSubAction g.ker hKstableG
  letI : DistribMulAction C ↑g.ker := coefficientKernelAction g hgC
  have hcompatK : ∀ (x : G) (k : ↑g.ker), x • k = rho x • k := by
    intro x k
    exact Subtype.ext (hcompatA x k.1)
  letI : ContinuousSMul G ↑g.ker := by
    constructor
    have hfac : (fun p : G × ↑g.ker ↦ p.1 • p.2) =
        (fun p : C × ↑g.ker ↦ p.1 • p.2) ∘
          (fun p : G × ↑g.ker ↦ (rho p.1, p.2)) := by
      funext p
      exact hcompatK p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have htrivC : ∀ (c : C) (k : ↑g.ker), c • k = k :=
    coefficientKernelAction_smul_eq_self_of_isPGroup_two hP g hgC hA₂ hcard
  have htrivG : ∀ (x : G) (k : ↑g.ker), x • k = k := by
    intro x k
    apply Subtype.ext
    change x • k.1 = k.1
    rw [hcompatA]
    exact congrArg Subtype.val (htrivC (rho x) k)
  intro F hFC hFthree hFg
  let FK : G × G × G → ↑g.ker := fun t ↦ ⟨F t, hFg t⟩
  have hFKC : Continuous FK := hFC.subtype_mk hFg
  have hFKthree : dThree (G := G) (A := ↑g.ker) FK = 0 := by
    funext t
    apply Subtype.ext
    exact congrFun hFthree t
  obtain ⟨k, hkC, hk⟩ := S (↑g.ker) hcard htrivG FK hFKC hFKthree
  refine ⟨fun p ↦ (k p).1, continuous_subtype_val.comp hkC, ?_, ?_⟩
  · exact fun p ↦ AddMonoidHom.mem_ker.mp (k p).2
  · funext t
    exact congrArg Subtype.val (congrFun hk t)

/-- A single trivial-scalar `H^3` theorem gives the entire scalar-kernel tail over a finite
2-group action image. -/
theorem twoGroupActionScalarKernelH2Tail_of_trivialScalarHThree
    (S : TrivialScalarHThreeExactSupply G)
    (rho : ContinuousMonoidHom G C) (hP : IsPGroup 2 C) :
    TwoGroupActionScalarKernelH2Tail rho := by
  apply twoGroupActionScalarKernelH2Tail_of_kernelHThreeCocyclesExact rho
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG hgC hcompatA _hcompatB
    hA₂ _hB₂ _hsurj hcard
  exact kernelHThreeCocyclesExact_of_trivialScalar
    S rho hP g hgG hgC hcompatA hA₂ hcard

end ScalarKernel

/-! ## The finite simultaneous action image -/

section PairAction

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- The simultaneous finite action on a pair of coefficients. -/
noncomputable def elementaryPairActionHom : ContinuousMonoidHom G
    (Multiplicative (AddAut A) × Multiplicative (AddAut B)) :=
  (Dyadic.LSquare.finiteActionHom (G := G) (M := A)).prod
    (Dyadic.LSquare.finiteActionHom (G := G) (M := B))

/-- The actual finite image of the simultaneous coefficient action. -/
noncomputable abbrev ElementaryPairActionImage : Type :=
  ↑((elementaryPairActionHom (G := G) (A := A) (B := B)).toMonoidHom.range)

/-- The surjection to the simultaneous finite action image. -/
noncomputable def elementaryPairActionImageHom : ContinuousMonoidHom G
    (ElementaryPairActionImage (G := G) (A := A) (B := B)) where
  toMonoidHom :=
    (elementaryPairActionHom (G := G) (A := A) (B := B)).toMonoidHom.rangeRestrict
  continuous_toFun :=
    (elementaryPairActionHom (G := G) (A := A) (B := B)).continuous_toFun.subtype_mk _

theorem elementaryPairActionImageHom_surjective : Function.Surjective
    (elementaryPairActionImageHom (G := G) (A := A) (B := B)) :=
  (elementaryPairActionHom (G := G) (A := A) (B := B)).toMonoidHom
    |>.rangeRestrict_surjective

/-- Projection of the simultaneous image to the first action. -/
noncomputable def elementaryPairActionFst :
    ElementaryPairActionImage (G := G) (A := A) (B := B) →*
      Multiplicative (AddAut A) where
  toFun c := c.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of the simultaneous image to the second action. -/
noncomputable def elementaryPairActionSnd :
    ElementaryPairActionImage (G := G) (A := A) (B := B) →*
      Multiplicative (AddAut B) where
  toFun c := c.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem elementaryPairActionImageHom_smul_fst (x : G) (a : A) :
    letI : DistribMulAction
        (ElementaryPairActionImage (G := G) (A := A) (B := B)) A :=
      DistribMulAction.compHom A
        (elementaryPairActionFst (G := G) (A := A) (B := B))
    elementaryPairActionImageHom (G := G) (A := A) (B := B) x • a = x • a := rfl

@[simp] theorem elementaryPairActionImageHom_smul_snd (x : G) (b : B) :
    letI : DistribMulAction
        (ElementaryPairActionImage (G := G) (A := A) (B := B)) B :=
      DistribMulAction.compHom B
        (elementaryPairActionSnd (G := G) (A := A) (B := B))
    elementaryPairActionImageHom (G := G) (A := A) (B := B) x • b = x • b := rfl

/-- Source equivariance descends to the simultaneous finite action image. -/
theorem elementaryPairAction_equivariant
    (f : A →+ B) (hf : ∀ (x : G) (a : A), f (x • a) = x • f a) :
    letI : DistribMulAction
        (ElementaryPairActionImage (G := G) (A := A) (B := B)) A :=
      DistribMulAction.compHom A
        (elementaryPairActionFst (G := G) (A := A) (B := B))
    letI : DistribMulAction
        (ElementaryPairActionImage (G := G) (A := A) (B := B)) B :=
      DistribMulAction.compHom B
        (elementaryPairActionSnd (G := G) (A := A) (B := B))
    ∀ (c : ElementaryPairActionImage (G := G) (A := A) (B := B)) (a : A),
      f (c • a) = c • f a := by
  intro c a
  obtain ⟨x, hx⟩ := c.property
  have hxA : c.1.1 = Dyadic.LSquare.finiteActionHom (G := G) (M := A) x :=
    congrArg Prod.fst hx.symm
  have hxB : c.1.2 = Dyadic.LSquare.finiteActionHom (G := G) (M := B) x :=
    congrArg Prod.snd hx.symm
  change f (c.1.1 • a) = c.1.2 • f a
  rw [hxA, hxB, Dyadic.LSquare.finiteActionHom_smul,
    Dyadic.LSquare.finiteActionHom_smul]
  exact hf x a

end PairAction

/-! ## Pro-2 scalar-to-coefficient devissage -/

/-- The finite image of a continuous surjection from a pro-2 group is a 2-group. -/
theorem isPGroup_elementaryPairActionImage
    {A B : Type}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
    [DistribMulAction G B] [ContinuousSMul G B]
    (hpro : IsProP 2 G) :
    IsPGroup 2 (ElementaryPairActionImage (G := G) (A := A) (B := B)) := by
  let rho := elementaryPairActionImageHom (G := G) (A := A) (B := B)
  have hopen : IsOpen ((rho.toMonoidHom.ker : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete _).preimage rho.continuous_toFun
  let U : OpenNormalSubgroup G := ⟨⟨rho.toMonoidHom.ker, hopen⟩, inferInstance⟩
  exact (hpro U).of_equiv
    (QuotientGroup.quotientKerEquivOfSurjective rho.toMonoidHom
      elementaryPairActionImageHom_surjective)

/-- For a pro-2 group, exactness of the trivial scalar cochain complex in degree three implies
degree-two right exactness for every surjection of finite elementary coefficient modules. -/
theorem finiteElementaryH2RightExactSupply_of_trivialScalarHThree
    (hpro : IsProP 2 G) (S : TrivialScalarHThreeExactSupply G) :
    FiniteElementaryH2RightExactSupply G := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _hfC hfG hA₂ hB₂ hsurj
  let C := ElementaryPairActionImage (G := G) (A := A) (B := B)
  let rho : ContinuousMonoidHom G C :=
    elementaryPairActionImageHom (G := G) (A := A) (B := B)
  letI : DistribMulAction C A := DistribMulAction.compHom A
    (elementaryPairActionFst (G := G) (A := A) (B := B))
  letI : DistribMulAction C B := DistribMulAction.compHom B
    (elementaryPairActionSnd (G := G) (A := A) (B := B))
  have hrho : Function.Surjective rho := elementaryPairActionImageHom_surjective
  have hP : IsPGroup 2 C := isPGroup_elementaryPairActionImage hpro
  have hfC : ∀ (c : C) (a : A), f (c • a) = c • f a :=
    elementaryPairAction_equivariant f hfG
  have hcompatA : ∀ (x : G) (a : A), x • a = rho x • a := by
    intro x a
    exact (elementaryPairActionImageHom_smul_fst x a).symm
  have hcompatB : ∀ (x : G) (b : B), x • b = rho x • b := by
    intro x b
    exact (elementaryPairActionImageHom_smul_snd x b).symm
  exact h2RightExactAt_of_twoGroupActionScalarKernelTail
    rho hrho hP (twoGroupActionScalarKernelH2Tail_of_trivialScalarHThree S rho hP)
    f hfG hfC hcompatA hcompatB hA₂ hB₂ hsurj

/-- Explicit one-coefficient form of the pro-2 CD-2 reduction. -/
theorem finiteElementaryH2RightExactSupply_of_modTwoHThreeExact
    (hpro : IsProP 2 G) (S : ModTwoHThreeExact G) :
    FiniteElementaryH2RightExactSupply G :=
  finiteElementaryH2RightExactSupply_of_trivialScalarHThree hpro
    (trivialScalarHThreeExactSupply_of_modTwo S)

/-- The concrete improved-L square core now has a single exact missing premise: scalar
degree-three exactness. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_trivialScalarHThree (h : ℕ)
    (S : TrivialScalarHThreeExactSupply (Dyadic.SqCore.DSq h)) :
    FiniteElementaryH2RightExactSupply (Dyadic.SqCore.DSq h) :=
  finiteElementaryH2RightExactSupply_of_trivialScalarHThree
    (Dyadic.SqCore.isProP_DSq h) S

/-- For the concrete one-relator improved-L core, the whole finite-elementary coefficient
theorem follows from the single classical assertion `H^3(D_sq(h), F_2) = 0`. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_modTwoHThreeExact (h : ℕ)
    (S : ModTwoHThreeExact (Dyadic.SqCore.DSq h)) :
    FiniteElementaryH2RightExactSupply (Dyadic.SqCore.DSq h) :=
  finiteElementaryH2RightExactSupply_of_modTwoHThreeExact
    (Dyadic.SqCore.isProP_DSq h) S

/-- Constructor for the maximal-pro-2 Sylow package.  The comparison (inflation) premise stays
separate; its CD-2 field is reduced to the one trivial-scalar degree-three theorem. -/
noncomputable def SylowPreimageMaxProTwoCDTwoPackage.of_trivialScalarHThree
    {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (hinf : FiniteElementaryH2InflationSurjective
      (maxProPMk 2 (sylowTwoPreimage rho P)))
    (S : TrivialScalarHThreeExactSupply
      (maxProPQuotient 2 (sylowTwoPreimage rho P))) :
    SylowPreimageMaxProTwoCDTwoPackage rho P where
  inflation := hinf
  cdTwo := finiteElementaryH2RightExactSupply_of_trivialScalarHThree
    isProP_maxProPQuotient S

/-- Explicit `F_2` form of the preceding maximal-pro-2 Sylow constructor. -/
noncomputable def SylowPreimageMaxProTwoCDTwoPackage.of_modTwoHThreeExact
    {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (hinf : FiniteElementaryH2InflationSurjective
      (maxProPMk 2 (sylowTwoPreimage rho P)))
    (S : ModTwoHThreeExact
      (maxProPQuotient 2 (sylowTwoPreimage rho P))) :
    SylowPreimageMaxProTwoCDTwoPackage rho P :=
  .of_trivialScalarHThree rho P hinf
    (trivialScalarHThreeExactSupply_of_modTwo S)

end

end GQ2.ContCoh
