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

The intrinsic degree-one statement can in fact also be proved.  Given a continuous cocycle on
`K₂(G)`, take the ambient normal core `C` of its kernel.  The image of `K₂(G)` in `G/C` has
exponent two: every ambient conjugate of `n²` is killed by the cocycle.  Since `G/K₂(G)` is
pro-`2`, the extension `G/C` is pro-`2`; the universal property of `K₂(G)` then forces the
cocycle to vanish.

Consequently the primitive-extension/cross-term (Hochschild--Serre transgression) field is
automatic.  The exact remaining inflation input is only literal continuous
`H²(K₂(G),M)`-vanishing.  Existing odd-index corestriction applies to the open Sylow preimage
`U ≤ GammaL`; it does not directly apply to `K₂(U)`, which is only known closed and generally
has infinite index.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.LSquare GQ2.SectionSix
open scoped Pointwise

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

section IntrinsicH1Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- An open subgroup of a closed normal subgroup has open ambient normalizer.

This is the compactness input for promoting an intrinsic finite quotient of a closed normal
subgroup to ambient finite data.  Conjugation maps `{1} × K` into `K`; compactness of `K`
gives one neighborhood of `1` which conjugates all of `K` into itself.  Intersecting it with
its inverse gives a neighborhood contained in the normalizer. -/
theorem isOpen_normalizer_map_of_isOpen_closedNormalSubgroup
    (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)]
    (K : Subgroup N) (hKopen : IsOpen (K : Set N)) :
    IsOpen ((Subgroup.normalizer (K.map N.subtype) : Subgroup G) : Set G) := by
  letI : CompactSpace N := isCompact_iff_compactSpace.mp
    (show IsCompact (N : Set G) from
      (show IsClosed (N : Set G) from inferInstance).isCompact)
  have hKclosed : IsClosed (K : Set N) := Subgroup.isClosed_of_isOpen K hKopen
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKclosed.isCompact
  let conjToN : G × K → N := fun p => ⟨p.1 * p.2.1.1 * p.1⁻¹, by
    exact (inferInstance : N.Normal).conj_mem p.2.1.1 p.2.1.2 p.1⟩
  have hconj : Continuous conjToN := by
    apply continuous_induced_rng.mpr
    change Continuous fun p : G × K => p.1 * p.2.1.1 * p.1⁻¹
    fun_prop
  let S : Set (G × K) := conjToN ⁻¹' (K : Set N)
  have hSopen : IsOpen S := hKopen.preimage hconj
  have hbase : ({1} : Set G) ×ˢ (Set.univ : Set K) ⊆ S := by
    rintro ⟨_, k⟩ ⟨rfl, -⟩
    change conjToN (1, k) ∈ K
    simpa only [conjToN, one_mul, inv_one, mul_one] using k.2
  obtain ⟨U, _V, hUopen, _hVopen, h1U, _hKV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set G))
      (isCompact_univ : IsCompact (Set.univ : Set K)) hSopen hbase
  let U0 : Set G := U ∩ (fun g : G => g⁻¹) ⁻¹' U
  have hU0open : IsOpen U0 := hUopen.inter (hUopen.preimage continuous_inv)
  have h1U0 : (1 : G) ∈ U0 := ⟨h1U rfl, by simpa using h1U rfl⟩
  let KG : Subgroup G := K.map N.subtype
  change IsOpen ((Subgroup.normalizer KG : Subgroup G) : Set G)
  apply Subgroup.isOpen_of_mem_nhds (Subgroup.normalizer KG) (g := (1 : G))
  apply Filter.mem_of_superset (hU0open.mem_nhds h1U0)
  intro g hg
  change g ∈ Subgroup.normalizer (KG : Set G)
  apply (Subgroup.mem_set_normalizer_iff).2
  intro x
  constructor
  · intro hx
    change x ∈ K.map N.subtype at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    change g * k.1 * g⁻¹ ∈ K.map N.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨g * k.1 * g⁻¹, ?_⟩, ?_, rfl⟩
    · exact (inferInstance : N.Normal).conj_mem k.1 k.2 g
    · change conjToN (g, ⟨k, hk⟩) ∈ K
      have hkV : (⟨k, hk⟩ : K) ∈ _V := _hKV (Set.mem_univ _)
      exact hUV ⟨hg.1, hkV⟩
  · intro hx
    change g * x * g⁻¹ ∈ K.map N.subtype at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    change x ∈ K.map N.subtype
    rw [Subgroup.mem_map]
    let y : N := ⟨g⁻¹ * k.1 * g, by
      simpa only [inv_inv] using
        (inferInstance : N.Normal).conj_mem k.1 k.2 g⁻¹⟩
    have hyK : y ∈ K := by
      have hkV : (⟨k, hk⟩ : K) ∈ _V := _hKV (Set.mem_univ _)
      have hy := hUV
        (show (g⁻¹, (⟨k, hk⟩ : K)) ∈ U ×ˢ _V from ⟨hg.2, hkV⟩)
      change conjToN (g⁻¹, ⟨k, hk⟩) ∈ K at hy
      simpa only [conjToN, y, inv_inv] using hy
    refine ⟨y, hyK, ?_⟩
    dsimp [y]
    change k.1 = g * x * g⁻¹ at hkx
    rw [hkx]
    group

/-- The ambient normal core of an intrinsic discrete quotient kernel remains open inside the
closed normal subgroup.

The preceding normalizer theorem makes `G / N_G(K)` finite.  Intersecting the corresponding
finite family of conjugate kernels is open in `N`; a coset-representative calculation identifies
that intersection with the restriction of the ambient normal core. -/
theorem normalCore_subgroupOf_isOpen_of_continuous_discrete
    {P : Type*} [Group P] [TopologicalSpace P] [DiscreteTopology P]
    (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)]
    (f : ContinuousMonoidHom N P) :
    IsOpen (((f.toMonoidHom.ker.map N.subtype).normalCore.subgroupOf N : Subgroup N) : Set N) := by
  let K : Subgroup N := f.toMonoidHom.ker
  have hKopen : IsOpen (K : Set N) := by
    change IsOpen (f ⁻¹' {1})
    exact (isOpen_discrete {1}).preimage f.continuous_toFun
  let KG : Subgroup G := K.map N.subtype
  let J : Subgroup G := Subgroup.normalizer (KG : Set G)
  have hJopen : IsOpen (J : Set G) := by
    exact isOpen_normalizer_map_of_isOpen_closedNormalSubgroup N K hKopen
  letI : Finite (G ⧸ J) := Subgroup.quotient_finite_of_isOpen J hJopen
  let rep : (G ⧸ J) → G := fun i => Quotient.out i
  let conjN : (G ⧸ J) → N →* N := fun i =>
    (((MulAut.conj (rep i)⁻¹).toMonoidHom.restrict N).codRestrict N (fun n => by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        MonoidHom.restrict_apply] using
          (inferInstance : N.Normal).conj_mem n.1 n.2 (rep i)⁻¹))
  have hconjN_val (i : G ⧸ J) (n : N) :
      (conjN i n).1 = (rep i)⁻¹ * n.1 * rep i := by
    simp only [conjN, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.restrict_apply, inv_inv]
  let KcoreN : Subgroup N := ⨅ i : G ⧸ J, K.comap (conjN i)
  have hKcoreNopen : IsOpen (KcoreN : Set N) := by
    dsimp only [KcoreN]
    rw [Subgroup.coe_iInf]
    apply isOpen_iInter_of_finite
    intro i
    change IsOpen ((conjN i) ⁻¹' (K : Set N))
    apply hKopen.preimage
    apply continuous_induced_rng.mpr
    have hfun : (Subtype.val ∘ (conjN i : N → N)) =
        fun n : N => (rep i)⁻¹ * n.1 * rep i := by
      funext n
      exact hconjN_val i n
    rw [hfun]
    fun_prop
  suffices ((KG.normalCore.subgroupOf N : Subgroup N)) = KcoreN by
    rwa [this]
  ext n
  constructor
  · intro hn
    change n ∈ ⨅ i : G ⧸ J, K.comap (conjN i)
    rw [Subgroup.mem_iInf]
    intro i
    change conjN i n ∈ K
    change f (conjN i n) = 1
    have hKG : (rep i)⁻¹ * n.1 * rep i ∈ KG := by
      have hn' : n.1 ∈ KG.normalCore := hn
      simpa only [inv_inv] using hn' (rep i)⁻¹
    change (rep i)⁻¹ * n.1 * rep i ∈ K.map N.subtype at hKG
    rw [Subgroup.mem_map] at hKG
    obtain ⟨k, hk, hkval⟩ := hKG
    have heq : k = conjN i n := by
      apply Subtype.ext
      rw [hconjN_val]
      change k.1 = (rep i)⁻¹ * n.1 * rep i at hkval
      exact hkval
    rw [← heq]
    exact hk
  · intro hn
    change n ∈ ⨅ i : G ⧸ J, K.comap (conjN i) at hn
    rw [Subgroup.mem_iInf] at hn
    change n.1 ∈ KG.normalCore
    intro b
    let ib : G ⧸ J := QuotientGroup.mk b⁻¹
    have hrel : QuotientGroup.leftRel J (rep ib) b⁻¹ :=
      Quotient.exact (Quotient.out_eq ib)
    have hj : (rep ib)⁻¹ * b⁻¹ ∈ J :=
      QuotientGroup.leftRel_apply.mp hrel
    let j : J := ⟨(rep ib)⁻¹ * b⁻¹, hj⟩
    have hb : b⁻¹ = rep ib * j.1 := by dsimp [j]; group
    have hcoord : conjN ib n ∈ K := hn ib
    have hcoordKG : (conjN ib n).1 ∈ KG := by
      change (conjN ib n).1 ∈ K.map N.subtype
      rw [Subgroup.mem_map]
      exact ⟨conjN ib n, hcoord, rfl⟩
    have hj_norm : j.1⁻¹ * (conjN ib n).1 * j.1 ∈ KG := by
      have hjmem : j.1 ∈ Subgroup.normalizer (KG : Set G) := j.2
      exact (Subgroup.mem_set_normalizer_iff''.mp hjmem _).mp hcoordKG
    rw [← inv_inv b, hb]
    simp only [inv_inv]
    have heqconj : (rep ib * j.1)⁻¹ * n.1 * (rep ib * j.1) =
        j.1⁻¹ * ((rep ib)⁻¹ * n.1 * rep ib) * j.1 := by group
    rw [heqconj]
    rw [← hconjN_val ib n]
    exact hj_norm

end IntrinsicH1Topology

section ProPExtension

variable {p : ℕ} {G : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A normal extension of a pro-`p` group by a `p`-group is pro-`p`, in the quotient form needed
for ambient normal cores.

For every open normal `V` of `G/K`, let `F = (G/K)/V` and let `H` be the image of `N` in `F`.
The group `H` is a `p`-group by hypothesis.  The quotient `F/H` is a continuous quotient of the
pro-`p` group `G/N`, hence is a `p`-group.  Elementwise, a `p`-power first moves an element of
`F` into `H`, and a second `p`-power kills it. -/
theorem isProP_quotient_of_normal_isPGroup_image
    (N K : Subgroup G) [N.Normal] [K.Normal]
    (hN : IsPGroup p (N.map (QuotientGroup.mk' K)))
    (hGN : IsProP p (G ⧸ N)) :
    IsProP p (G ⧸ K) := by
  intro V
  let Q := G ⧸ K
  let F := Q ⧸ V.toSubgroup
  let q : ContinuousMonoidHom G F :=
    (GQ2.quotientMk V.toSubgroup).comp (GQ2.quotientMk K)
  let H : Subgroup F := N.map q.toMonoidHom
  have hq_surj : Function.Surjective q :=
    (QuotientGroup.mk'_surjective V.toSubgroup).comp (QuotientGroup.mk'_surjective K)
  letI : H.Normal := Subgroup.Normal.map (inferInstance : N.Normal) q.toMonoidHom hq_surj
  have hH : IsPGroup p H := by
    have hh := hN.map (QuotientGroup.mk' V.toSubgroup)
    change IsPGroup p (N.map ((QuotientGroup.mk' V.toSubgroup).comp
      (QuotientGroup.mk' K)))
    rw [← Subgroup.map_map]
    exact hh
  let qH : ContinuousMonoidHom G (F ⧸ H) := (GQ2.quotientMk H).comp q
  have hNker : N ≤ qH.toMonoidHom.ker := by
    intro n hn
    change qH n = 1
    apply (QuotientGroup.eq_one_iff (q n)).mpr
    exact ⟨n, hn, rfl⟩
  let qbar : ContinuousMonoidHom (G ⧸ N) (F ⧸ H) := GQ2.quotientLift N qH hNker
  have hqH_surj : Function.Surjective qH :=
    (QuotientGroup.mk'_surjective H).comp hq_surj
  have hqbar_surj : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective N qH.toMonoidHom hqH_surj hNker
  letI : DiscreteTopology F := QuotientGroup.discreteTopology V.isOpen
  let Hopen : OpenSubgroup F := ⟨H, isOpen_discrete _⟩
  letI : DiscreteTopology (F ⧸ H) := QuotientGroup.discreteTopology Hopen.isOpen
  have hFHpro : IsProP p (F ⧸ H) :=
    SectionThree.isProP_of_surjective qbar.toMonoidHom qbar.continuous_toFun hqbar_surj hGN
  let botFH : OpenNormalSubgroup (F ⧸ H) :=
    ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩
  have hFH : IsPGroup p (F ⧸ H) :=
    (hFHpro botFH).of_equiv QuotientGroup.quotientBot
  intro x
  obtain ⟨j, hj⟩ := hFH (QuotientGroup.mk' H x)
  have hxH : x ^ p ^ j ∈ H := by
    exact (QuotientGroup.eq_one_iff (x ^ p ^ j)).mp (by simpa using hj)
  obtain ⟨k, hk⟩ := hH ⟨x ^ p ^ j, hxH⟩
  refine ⟨j + k, ?_⟩
  have hk' := congrArg Subtype.val hk
  simpa only [Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_one,
    ← pow_mul, ← pow_add] using hk'

end ProPExtension

/-- Literal vanishing of continuous one-cocycles.  When the action is trivial this is the
cochain-level form of `H¹(H,M)=0`, since every one-coboundary is zero. -/
def ContinuousH1CocyclesVanish
    (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction H M] : Prop :=
  ∀ z : Z1 H M, z = 0

section IntrinsicH1Automatic

variable {G M : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [Finite M]
  [DistribMulAction G M]
  [DistribMulAction (maxProPQuotient 2 G) M]
  [ContinuousSMul (maxProPQuotient 2 G) M]

/-- Every intrinsic continuous one-cocycle on the maximal-pro-`2` kernel vanishes for finite
elementary quotient-compatible coefficients.

The action on `N = K₂(G)` is trivial, so the cocycle is a continuous homomorphism
`f : N → Multiplicative M`.  Let `C` be the ambient normal core of its kernel.  Conjugates of
squares lie in `ker f`, so the image of `N` in `G/C` has exponent two.  The normal-extension
lemma makes `G/C` pro-`2`; the universal property `K₂(G) ≤ ker(G → G/C)` then gives
`N ≤ C ≤ ker f`. -/
theorem maxProTwoKernel_intrinsicH1CocyclesVanish
    (hM2 : ∀ m : M, m + m = 0)
    (hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m) :
    ContinuousH1CocyclesVanish (proPKernel 2 G) M := by
  let N : Subgroup G := proPKernel 2 G
  have htriv : ∀ (n : N) (m : M), n • m = m := by
    intro n m
    exact maxProTwoKernel_smul_eq hcompat n m
  intro z
  let f : ContinuousMonoidHom N (Multiplicative M) := {
    toFun n := Multiplicative.ofAdd (z.1 n)
    map_one' := by rw [Z1_apply_one]; rfl
    map_mul' := by
      intro n k
      change Multiplicative.ofAdd (z.1 (n * k)) =
        Multiplicative.ofAdd (z.1 n) * Multiplicative.ofAdd (z.1 k)
      rw [(mem_Z1_iff.mp z.2).2, htriv n]
      rfl
    continuous_toFun := (mem_Z1_iff.mp z.2).1 }
  let K : Subgroup N := f.toMonoidHom.ker
  have hKopen : IsOpen (K : Set N) := by
    change IsOpen (f ⁻¹' {1})
    exact (isOpen_discrete {1}).preimage f.continuous_toFun
  have hKclosed : IsClosed (K : Set N) := Subgroup.isClosed_of_isOpen K hKopen
  let KG : Subgroup G := K.map N.subtype
  have hKGclosed : IsClosed (KG : Set G) := by
    have hemb : Topology.IsClosedEmbedding ((↑) : N → G) :=
      (show IsClosed (N : Set G) from proPKernel_isClosed 2 G).isClosedEmbedding_subtypeVal
    rw [show (KG : Set G) = N.subtype '' (K : Set N) by ext; simp [KG]]
    exact hemb.isClosed_iff_image_isClosed.mp hKclosed
  let C : Subgroup G := KG.normalCore
  letI : C.Normal := Subgroup.normalCore_normal KG
  letI : IsClosed (C : Set G) := KG.normalCore_isClosed hKGclosed
  have hNimage : IsPGroup 2 (N.map (QuotientGroup.mk' C)) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨n, hn, hnx⟩ := x.2
    apply Subtype.ext
    change x.1 ^ 2 ^ 1 = 1
    rw [← hnx]
    change (QuotientGroup.mk' C n) ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow]
    apply (QuotientGroup.eq_one_iff (n ^ 2)).mpr
    change n ^ 2 ∈ KG.normalCore
    intro b
    have hconjN : b * n * b⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem n hn b
    let nb : N := ⟨b * n * b⁻¹, hconjN⟩
    have hfb : f nb ^ 2 = 1 := by
      change Multiplicative.ofAdd (z.1 nb) ^ 2 = 1
      rw [pow_two, ← ofAdd_add, hM2, ofAdd_zero]
    have hnb2 : nb ^ 2 ∈ K := by
      change f (nb ^ 2) = 1
      rw [map_pow]
      exact hfb
    change b * n ^ 2 * b⁻¹ ∈ K.map N.subtype
    rw [Subgroup.mem_map]
    refine ⟨nb ^ 2, hnb2, ?_⟩
    change (b * n * b⁻¹) ^ 2 = b * n ^ 2 * b⁻¹
    simp only [pow_two]
    group
  have hquot : IsProP 2 (G ⧸ C) :=
    isProP_quotient_of_normal_isPGroup_image N C hNimage isProP_maxProPQuotient
  let qC : ContinuousMonoidHom G (G ⧸ C) := GQ2.quotientMk C
  have hNleC : N ≤ C := by
    intro n hn
    have hnker := proPKernel_le_ker hquot qC hn
    exact (QuotientGroup.eq_one_iff n).mp hnker
  apply Subtype.ext
  funext n
  change z.1 n = 0
  have hnKG : n.1 ∈ KG := Subgroup.normalCore_le KG (hNleC n.2)
  change n.1 ∈ K.map N.subtype at hnKG
  rw [Subgroup.mem_map] at hnKG
  obtain ⟨k, hk, hkn⟩ := hnKG
  have hkeq : k = n := Subtype.ext hkn
  subst k
  change f n = 1 at hk
  exact congrArg Multiplicative.toAdd hk

end IntrinsicH1Automatic

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

/-- Intrinsic one-cocycle vanishing kills the conjugation defect. -/
theorem h2KernelConjugationDefect_eq_zero_of_h1CocyclesVanish
    (htriv : ∀ (n : N) (m : M), n.1 • m = m)
    (hH1 : ContinuousH1CocyclesVanish N M)
    (c : Z2 G M) (hzero : ∀ n k : N, c.1 (n.1, k.1) = 0)
    (g : G) (n : N) : H2KernelConjugationDefect N c g n = 0 := by
  let defect : Z1 N M :=
    ⟨H2KernelConjugationDefect N c g,
      h2KernelConjugationDefect_mem_Z1 N htriv c hzero g⟩
  have hdefect := congrArg (fun z : Z1 N M => z.1 n) (hH1 defect)
  simpa only [defect, Subtype.coe_eta, AddSubgroup.coe_zero, Pi.zero_apply] using hdefect

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

/-- For a profinite ambient group, vanishing of the intrinsic conjugation defect is also
sufficient for a continuous cross-term correction.

Continuity introduces no further quotient-cochain obstruction.  The cocycle is locally zero
on both axes through the identity, hence on both cross terms of some open normal subgroup `L`.
After enlarging `L` by `N`, the cocycle vanishes on an open normal subgroup `H`.  Representatives
of the finite quotient `G/H` then give a continuous right-coset primitive; defect-zero is exactly
the compatibility which makes the left cross terms vanish as well. -/
theorem h2CrossTermCorrection_of_conjugationDefect_eq_zero
    [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology M]
    (htriv : ∀ (n : N) (m : M), n.1 • m = m)
    (c : Z2 G M) (hzero : ∀ n k : N, c.1 (n.1, k.1) = 0)
    (hdefect : ∀ (g : G) (n : N), H2KernelConjugationDefect N c g n = 0) :
    ∃ theta : G → M, Continuous theta ∧
      (∀ n : N, theta n.1 = 0) ∧
      ∀ (g : G) (n : N),
        (c.1 + dOne G M theta) (g, n.1) = 0 ∧
        (c.1 + dOne G M theta) (n.1, g) = 0 := by
  have hcoc := (mem_Z2_iff.mp c.2).2
  have hc11 : c.1 (1, 1) = 0 := by
    simpa using hzero (1 : N) (1 : N)
  have hc_one_right (g : G) : c.1 (g, 1) = 0 := by
    have h := hcoc g 1 1
    rw [hc11, smul_zero, zero_add] at h
    simp only [mul_one] at h
    apply add_left_cancel (a := c.1 (g, 1))
    simpa using h.symm
  have hc_one_left (g : G) : c.1 (1, g) = 0 := by
    have h := hcoc 1 1 g
    rw [hc11, one_smul, add_zero] at h
    simp only [one_mul] at h
    apply add_left_cancel (a := c.1 (1, g))
    simpa using h
  let Z : Set (G × G) := c.1 ⁻¹' {0}
  have hZopen : IsOpen Z :=
    (mem_Z2_iff.mp c.2).1.isOpen_preimage _ (isOpen_discrete {0})
  have hright : (Set.univ : Set G) ×ˢ ({1} : Set G) ⊆ Z := by
    rintro ⟨g, _⟩ ⟨-, rfl⟩
    exact hc_one_right g
  obtain ⟨_u, v, _huo, hvo, _huniv, h1v, huv⟩ :=
    generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set G))
      (isCompact_singleton : IsCompact ({1} : Set G)) hZopen hright
  have hleft : ({1} : Set G) ×ˢ (Set.univ : Set G) ⊆ Z := by
    rintro ⟨_, g⟩ ⟨rfl, -⟩
    exact hc_one_left g
  obtain ⟨u, _v, huo, _hvo, h1u, _hvuniv, huv'⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set G))
      (isCompact_univ : IsCompact (Set.univ : Set G)) hZopen hleft
  obtain ⟨L, hL⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (huo.inter hvo) ⟨h1u rfl, h1v rfl⟩
  have hc_right_L (g : G) (l : L) : c.1 (g, l.1) = 0 := by
    exact huv ⟨_huniv (Set.mem_univ g), (hL l.2).2⟩
  have hc_left_L (l : L) (g : G) : c.1 (l.1, g) = 0 := by
    exact huv' ⟨(hL l.2).1, _hvuniv (Set.mem_univ g)⟩
  let Hsub : Subgroup G := N ⊔ (L : Subgroup G)
  let H : OpenNormalSubgroup G := {
    toSubgroup := Hsub
    isOpen' := Subgroup.isOpen_mono
      (show (L : Subgroup G) ≤ Hsub from le_sup_right) L.isOpen
    isNormal' := Subgroup.sup_normal N (L : Subgroup G) }
  have hNleH : N ≤ (H : Subgroup G) := le_sup_left
  have hc_right_L' (g l : G) (hl : l ∈ L) : c.1 (g, l) = 0 :=
    hc_right_L g ⟨l, hl⟩
  have hc_left_L' (l : G) (hl : l ∈ L) (g : G) : c.1 (l, g) = 0 :=
    hc_left_L ⟨l, hl⟩ g
  have hc_right_coset_L (g h l : G) (hl : l ∈ L) :
      c.1 (g, h * l) = c.1 (g, h) := by
    have hc := hcoc g h l
    rw [hc_right_L' h l hl, hc_right_L' (g * h) l hl,
      smul_zero, zero_add, zero_add] at hc
    exact hc
  have hc_left_coset_L (g h l : G) (hl : l ∈ L) :
      c.1 (g * l, h) = c.1 (g, h) := by
    let l' : L := ⟨h⁻¹ * l * h, by
      change h⁻¹ * l * h ∈ L.toSubgroup
      simpa only [inv_inv] using
        (inferInstance : L.toSubgroup.Normal).conj_mem l hl h⁻¹⟩
    have hc := hcoc g l h
    rw [hc_left_L' l hl h, hc_right_L' g l hl,
      smul_zero, zero_add, add_zero] at hc
    have hlh : l * h = h * l'.1 := by dsimp [l']; group
    rw [hlh, hc_right_coset_L g h l'.1 l'.2] at hc
    exact hc.symm
  have hc_H_zero (x y : H) : c.1 (x.1, y.1) = 0 := by
    have hx : x.1 ∈ ((↑(N ⊔ L.toSubgroup) : Set G)) := x.2
    rw [Subgroup.normal_mul N L.toSubgroup] at hx
    have hy : y.1 ∈ ((↑(N ⊔ L.toSubgroup) : Set G)) := y.2
    rw [Subgroup.normal_mul N L.toSubgroup] at hy
    obtain ⟨n, hn, l, hl, hxl⟩ := hx
    obtain ⟨k, hk, r, hr, hyr⟩ := hy
    rw [← hxl, ← hyr]
    rw [hc_right_coset_L (n * l) k r hr,
      hc_left_coset_L n k l hl]
    exact hzero ⟨n, hn⟩ ⟨k, hk⟩
  let rep : G → G := fun g => Quotient.out (quotientMk (H : Subgroup G) g)
  letI : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
    QuotientGroup.discreteTopology H.isOpen
  have hrep_cont : Continuous rep := by
    exact continuous_of_discreteTopology.comp
      (quotientMk (H : Subgroup G)).continuous_toFun
  have hrep_quot (g : G) : quotientMk (H : Subgroup G) (rep g) =
      quotientMk (H : Subgroup G) g := Quotient.out_eq _
  have htail (g : G) : (rep g)⁻¹ * g ∈ (H : Subgroup G) := by
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact (hrep_quot g))
  let theta : G → M := fun g => c.1 (rep g, (rep g)⁻¹ * g)
  have htheta : Continuous theta := by
    exact (mem_Z2_iff.mp c.2).1.comp
      (hrep_cont.prodMk (by fun_prop))
  have hrep_mul_N (g : G) (n : N) : rep (g * n.1) = rep g := by
    dsimp [rep]
    apply congrArg Quotient.out
    change (quotientMk (H : Subgroup G) g) * quotientMk (H : Subgroup G) n.1 =
      quotientMk (H : Subgroup G) g
    have hnq : quotientMk (H : Subgroup G) n.1 = 1 := by
      change (n.1 : G ⧸ (H : Subgroup G)) = 1
      exact (QuotientGroup.eq_one_iff n.1).mpr (hNleH n.2)
    rw [hnq, mul_one]
  have htheta_N (n : N) : theta n.1 = 0 := by
    apply hc_H_zero ⟨rep n.1, ?_⟩ ⟨(rep n.1)⁻¹ * n.1, htail n.1⟩
    have ht := htail n.1
    have hn := hNleH n.2
    have heq : rep n.1 = n.1 * ((rep n.1)⁻¹ * n.1)⁻¹ := by group
    rw [heq]
    exact (H : Subgroup G).mul_mem hn ((H : Subgroup G).inv_mem ht)
  have htheta_right (g : G) (n : N) :
      theta (g * n.1) - theta g = c.1 (g, n.1) := by
    have ha : (rep g)⁻¹ * g ∈ (H : Subgroup G) := htail g
    have hnH : n.1 ∈ (H : Subgroup G) := hNleH n.2
    have hc := hcoc (rep g) ((rep g)⁻¹ * g) n.1
    rw [hc_H_zero ⟨(rep g)⁻¹ * g, ha⟩ ⟨n.1, hnH⟩,
      smul_zero, zero_add] at hc
    dsimp [theta]
    have hr := hrep_mul_N g n
    rw [hr]
    have hmul : (rep g)⁻¹ * (g * n.1) = ((rep g)⁻¹ * g) * n.1 := by group
    rw [hmul, hc]
    have hrg : rep g * ((rep g)⁻¹ * g) = g := by group
    rw [hrg]
    abel
  refine ⟨theta, htheta, htheta_N, ?_⟩
  intro g n
  constructor
  · simp only [Pi.add_apply, dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      htheta_N, smul_zero, zero_sub]
    rw [← htheta_right g n]
    abel
  · let k : N := ⟨g⁻¹ * n.1 * g, by
      simpa using (inferInstance : N.Normal).conj_mem n.1 n.2 g⁻¹⟩
    have hgk : g * k.1 = n.1 * g := by dsimp [k]; group
    have hd := hdefect g k
    have hcrossEq : c.1 (g, k.1) = c.1 (n.1, g) := by
      dsimp [H2KernelConjugationDefect] at hd
      have hconj : g * k.1 * g⁻¹ = n.1 := by dsimp [k]; group
      rw [hconj] at hd
      exact sub_eq_zero.mp hd
    simp only [Pi.add_apply, dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      htheta_N, htriv, add_zero]
    rw [← hgk, ← hcrossEq, ← htheta_right g k]
    abel

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

/-- The genuinely residual input for inflation: literal continuous `H²`-vanishing on the
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

/-- Intrinsic kernel `H¹`-vanishing in the literal cocycle form needed by transgression.

The quotient-compatible action is trivial on `K₂(G)`, so all one-coboundaries there are zero;
thus `∀ z : Z¹(K₂(G),M), z = 0` is exactly the useful cochain form of `H¹(K₂(G),M)=0`.
Unlike ambient-cocycle restriction vanishing, this quantifies cocycles defined intrinsically on
the kernel.  The ambient-normal-core argument above proves this supply unconditionally. -/
def FiniteElementaryMaxProTwoKernelH1VanishesSupply : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      ContinuousH1CocyclesVanish (proPKernel 2 G) M

/-- Intrinsic kernel `H¹`-vanishing is unconditional for finite elementary coefficients whose
action factors through the maximal pro-`2` quotient. -/
theorem finiteElementaryMaxProTwoKernelH1VanishesSupply :
    FiniteElementaryMaxProTwoKernelH1VanishesSupply (G := G) := by
  intro M _ _ _ _ _ _ _ _ _ hM2 hcompat
  exact maxProTwoKernel_intrinsicH1CocyclesVanish hM2 hcompat

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

/-- The cross-term formulation of the transgression input after continuous extension.

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

/-- Intrinsic kernel `H¹`-vanishing discharges the whole cross-term supply.

For a chosen extension `psi0`, the corrected cocycle `c = z + d psi0` vanishes on the kernel
square.  Its conjugation defect is an intrinsic kernel one-cocycle, hence zero by `D1`; the
profinite defect-zero theorem then constructs the continuous correction. -/
theorem finiteElementaryMaxProTwoKernelCrossTermCorrection_of_h1Vanishes
    (D1 : FiniteElementaryMaxProTwoKernelH1VanishesSupply (G := G)) :
    FiniteElementaryMaxProTwoKernelCrossTermCorrectionSupply (G := G) := by
  intro M _ _ _ _ _ _ _ _ _ hM2 hcompat z phi hphi hprim psi0 hpsi0 hext0
  let N : Subgroup G := proPKernel 2 G
  have htriv : ∀ (n : N) (m : M), n.1 • m = m :=
    maxProTwoKernel_smul_eq hcompat
  have htrivN : ∀ (n : N) (m : M), n • m = m := htriv
  have hcob : dOne G M psi0 ∈ Z2 G M := by
    apply B2_le_Z2
    exact ⟨psi0, hpsi0, rfl⟩
  let c : Z2 G M := ⟨z.1 + dOne G M psi0, (Z2 G M).add_mem z.2 hcob⟩
  have hzero (n k : N) : c.1 (n.1, k.1) = 0 := by
    change z.1 (n.1, k.1) + dOne G M psi0 (n.1, k.1) = 0
    rw [← hprim n k]
    have hext_mul : psi0 (n.1 * k.1) = -phi (n * k) := by
      simpa using hext0 (n * k)
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hext0 n, hext0 k, hext_mul, htrivN n, htriv n]
    abel
  have hdefect (g : G) (n : N) : H2KernelConjugationDefect N c g n = 0 :=
    h2KernelConjugationDefect_eq_zero_of_h1CocyclesVanish N htriv
      (D1 M hM2 hcompat) c hzero g n
  obtain ⟨theta, htheta, htheta0, hcross⟩ :=
    h2CrossTermCorrection_of_conjugationDefect_eq_zero N htriv c hzero hdefect
  refine ⟨theta, htheta, htheta0, ?_⟩
  have hdadd : dOne G M (fun x => psi0 x + theta x) =
      dOne G M psi0 + dOne G M theta := map_add (dOne G M) psi0 theta
  intro g n
  constructor
  · simpa only [c, hdadd, Pi.add_apply, add_assoc] using (hcross g n).1
  · simpa only [c, hdadd, Pi.add_apply, add_assoc] using (hcross g n).2

/-- Equivalently, intrinsic kernel `H¹`-vanishing supplies the original transgression field. -/
theorem finiteElementaryMaxProTwoKernelTransgression_of_h1Vanishes
    (D1 : FiniteElementaryMaxProTwoKernelH1VanishesSupply (G := G)) :
    FiniteElementaryMaxProTwoKernelTransgressionSupply (G := G) :=
  finiteElementaryMaxProTwoKernelTransgressionSupply_iff_crossTermCorrection.mpr
    (finiteElementaryMaxProTwoKernelCrossTermCorrection_of_h1Vanishes D1)

/-- The cross-term correction supply is unconditional: the only obstruction is an intrinsic
kernel one-cocycle, and those cocycles vanish by the ambient-normal-core argument. -/
theorem finiteElementaryMaxProTwoKernelCrossTermCorrection :
    FiniteElementaryMaxProTwoKernelCrossTermCorrectionSupply (G := G) :=
  finiteElementaryMaxProTwoKernelCrossTermCorrection_of_h1Vanishes
    finiteElementaryMaxProTwoKernelH1VanishesSupply

/-- Hence the original Hochschild--Serre transgression supply is unconditional as well. -/
theorem finiteElementaryMaxProTwoKernelTransgression :
    FiniteElementaryMaxProTwoKernelTransgressionSupply (G := G) :=
  finiteElementaryMaxProTwoKernelTransgression_of_h1Vanishes
    finiteElementaryMaxProTwoKernelH1VanishesSupply

/-- The split kernel statements reconstruct the existing honest Hochschild--Serre package. -/
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

/-- The classical kernel-acyclicity boundary: intrinsic `H¹`- and `H²`-vanishing on
`K₂(G)` imply finite-elementary degree-two inflation from `G(2)`. -/
theorem finiteElementaryH2InflationSurjective_of_kernelH1H2Vanishes
    (D1 : FiniteElementaryMaxProTwoKernelH1VanishesSupply (G := G))
    (D2 : FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G)) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes_crossTermCorrection D2
    (finiteElementaryMaxProTwoKernelCrossTermCorrection_of_h1Vanishes D1)

/-- Final maximal-pro-`2` kernel boundary: literal continuous kernel `H²`-vanishing alone
implies finite-elementary degree-two inflation.  The degree-one/transgression input is supplied
unconditionally by `finiteElementaryMaxProTwoKernelH1VanishesSupply`. -/
theorem finiteElementaryH2InflationSurjective_of_kernelH2Vanishes
    (D2 : FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G)) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) :=
  finiteElementaryH2InflationSurjective_of_kernelH1H2Vanishes
    finiteElementaryMaxProTwoKernelH1VanishesSupply D2

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

/-- The sole residual inflation statement, specialized to a `GammaL` Sylow preimage. -/
noncomputable abbrev GammaLSylowPreimageKernelH2VanishesSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := U P)

/-- Intrinsic kernel `H¹`-vanishing, specialized to a `GammaL` Sylow preimage.  This is
discharged unconditionally below. -/
noncomputable abbrev GammaLSylowPreimageKernelH1VanishesSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  FiniteElementaryMaxProTwoKernelH1VanishesSupply (G := U P)

/-- The transgression field, specialized to a `GammaL` Sylow preimage.  It is automatic below. -/
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

/-- Intrinsic kernel `H¹`-vanishing is unconditional for every `GammaL` Sylow preimage. -/
theorem gammaLSylowPreimageKernelH1Vanishes
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH1VanishesSupply P :=
  finiteElementaryMaxProTwoKernelH1VanishesSupply

/-- The kernel transgression field is therefore unconditional for every `GammaL` Sylow
preimage. -/
theorem gammaLSylowPreimageKernelTransgression
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelTransgressionSupply P :=
  finiteElementaryMaxProTwoKernelTransgression

/-- The legacy split kernel statements imply the sought degree-two inflation theorem for `U P`.
The transgression hypothesis is discharged unconditionally below. -/
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

/-- For a `GammaL` Sylow preimage, intrinsic kernel `H¹`- and `H²`-vanishing suffice for
the sought degree-two inflation theorem. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_kernelH1H2Vanishes
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D1 : GammaLSylowPreimageKernelH1VanishesSupply P)
    (D2 : GammaLSylowPreimageKernelH2VanishesSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelH1H2Vanishes D1 D2

/-- Final boundary for a `GammaL` Sylow preimage: literal kernel `H²`-vanishing alone implies
the sought degree-two inflation theorem. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_kernelH2Vanishes
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D2 : GammaLSylowPreimageKernelH2VanishesSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes D2

end


end GQ2.Dyadic.LSquare
