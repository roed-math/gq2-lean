import Mathlib
import GQ2.ProfiniteQuotient

/-!
# The maximal pro-`p` quotient  (ticket T-05, plan item I4)

For a profinite group `G` and a prime `p`, the paper repeatedly uses the **maximal pro-`p`
quotient** `G(p)` (e.g. `G_{ℚ₂}(2)` in B4, and `Δ = maxPro2(FreeProfinite (Fin 2))` in B8).
This file constructs it and proves the two facts that pin it down:

* it is a **pro-`p` group** (`isProP_maxProPQuotient`), and
* it enjoys the **universal property**: continuous homomorphisms from `G` into a pro-`p` group
  factor *uniquely* through `G(p)` (`maxProPHomEquiv`, an explicit bijection of hom-sets).

## Design

`G(p) := G ⧸ K`, where the **pro-`p` kernel** `K = proPKernel p G` is the intersection of all
open normal subgroups `U ≤ G` whose (finite) quotient `G ⧸ U` is a `p`-group:
```
proPKernel p G = ⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.toSubgroup.
```
`K` is a closed normal subgroup (an intersection of clopen normal subgroups), so
`GQ2.profiniteQuotient` packages `G ⧸ K` as a `ProfiniteGrp`.  A profinite group `P` is
**pro-`p`** (`IsProP p P`) exactly when every finite continuous quotient `P ⧸ V` is a `p`-group.

The universal property rests on the **kernel-containment lemma** `proPKernel_le_ker`: for pro-`p`
`P` and continuous `f : G → P`, `K ≤ ker f` (each `f⁻¹ V` is an open normal subgroup with
`G ⧸ f⁻¹V ↪ P ⧸ V` a `p`-group, so it lies in the defining family; and the open normal subgroups
of the profinite group `P` intersect in `1`).  Pro-`p`-ness of `G(p)` is the harder direction: an
open normal `Ŵ ≥ K` contains some member `U` of the defining family (a directed family of clopen
sets whose intersection lies in the open set `Ŵ`, so — by compactness — one member already does),
whence `G ⧸ Ŵ` is a quotient of the `p`-group `G ⧸ U`.

Stress tests: a `p`-group is its own maximal pro-`p` quotient (`proPKernel_eq_bot_of_isProP`,
`maxProPMk_bijective_of_isProP`; idempotence), instantiated on the finite `2`-group `ZMod 4`.
-/

open scoped Pointwise

namespace GQ2

/-! ## The `IsProP` predicate -/

/-- A topological group `P` is **pro-`p`** if every finite continuous quotient `P ⧸ U`
(`U` an open normal subgroup) is a `p`-group.  For profinite `P` this is the usual notion of a
pro-`p` group (an inverse limit of finite `p`-groups). -/
def IsProP (p : ℕ) (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  ∀ U : OpenNormalSubgroup P, IsPGroup p (P ⧸ U.toSubgroup)

/-- A `p`-group is pro-`p`: every quotient of a `p`-group is a `p`-group. -/
theorem isProP_of_isPGroup {p : ℕ} {P : Type*} [Group P] [TopologicalSpace P]
    (hP : IsPGroup p P) : IsProP p P :=
  fun U => hP.to_quotient U.toSubgroup

/-! ## Small group-theoretic helpers -/

/-- A product of two `p`-groups is a `p`-group. -/
theorem isPGroup_prod {p : ℕ} {M N : Type*} [Group M] [Group N]
    (hM : IsPGroup p M) (hN : IsPGroup p N) : IsPGroup p (M × N) := by
  rintro ⟨a, b⟩
  obtain ⟨i, hi⟩ := hM a
  obtain ⟨j, hj⟩ := hN b
  refine ⟨i + j, ?_⟩
  have ha : a ^ p ^ (i + j) = 1 := by rw [pow_add, pow_mul, hi, one_pow]
  have hb : b ^ p ^ (i + j) = 1 := by rw [pow_add, mul_comm, pow_mul, hj, one_pow]
  ext
  · simpa using ha
  · simpa using hb

/-- If the quotients of `G` by two normal subgroups `A`, `B` are `p`-groups, then so is the
quotient by `A ⊓ B` (it embeds in `(G ⧸ A) × (G ⧸ B)`). -/
theorem isPGroup_quotient_inf {p : ℕ} {G : Type*} [Group G] {A B : Subgroup G}
    [A.Normal] [B.Normal] (hA : IsPGroup p (G ⧸ A)) (hB : IsPGroup p (G ⧸ B)) :
    IsPGroup p (G ⧸ (A ⊓ B)) := by
  refine (isPGroup_prod hA hB).of_injective
    (QuotientGroup.lift (A ⊓ B) ((QuotientGroup.mk' A).prod (QuotientGroup.mk' B)) ?_) ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    ext
    · simpa using (QuotientGroup.eq_one_iff x).mpr hx.1
    · simpa using (QuotientGroup.eq_one_iff x).mpr hx.2
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.lift_mk', MonoidHom.prod_apply, Prod.ext_iff] at hx
    simp only [QuotientGroup.mk'_apply, Prod.fst_one, Prod.snd_one,
      QuotientGroup.eq_one_iff] at hx
    exact (QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_inf.mpr hx)

/-- The whole group as an open normal subgroup (for non-vacuity of the defining family). -/
def topOpenNormalSubgroup (G : Type*) [Group G] [TopologicalSpace G] : OpenNormalSubgroup G where
  toSubgroup := ⊤
  isOpen' := isOpen_univ


/-- The trivial quotient `G ⧸ ⊤` is a `p`-group. -/
theorem isPGroup_quotient_top {p : ℕ} {G : Type*} [Group G] :
    IsPGroup p (G ⧸ (⊤ : Subgroup G)) := by
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  exact fun g => ⟨0, by rw [pow_zero, pow_one]; exact Subsingleton.elim g 1⟩

/-! ## Intersection of open normal subgroups of a profinite group -/

/-- In a profinite group, an element lying in *every* open normal subgroup is trivial. -/
theorem eq_one_of_forall_mem_openNormalSubgroup {P : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] {x : P}
    (h : ∀ V : OpenNormalSubgroup P, x ∈ V) : x = 1 := by
  by_contra hx
  obtain ⟨V, hVsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := x)) (Set.mem_compl_singleton_iff.mpr fun he => hx he.symm)
  exact (hVsub (h V)) rfl

/-! ## The pro-`p` kernel and the maximal pro-`p` quotient -/

/-- The **pro-`p` kernel** of `G`: the intersection of all open normal subgroups `U ≤ G` with
`G ⧸ U` a `p`-group.  `G(p) := G ⧸ proPKernel p G`. -/
def proPKernel (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  ⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.1.toSubgroup

instance proPKernel_normal (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    (proPKernel p G).Normal :=
  Subgroup.normal_iInf_normal fun U => U.1.isNormal'

theorem proPKernel_isClosed (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : IsClosed (proPKernel p G : Set G) := by
  rw [proPKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun U => U.1.toOpenSubgroup.isClosed

/-- `proPKernel p G ≤ U` for every open normal `U` with `G ⧸ U` a `p`-group. -/
theorem proPKernel_le {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) (hU : IsPGroup p (G ⧸ U.toSubgroup)) :
    proPKernel p G ≤ U.toSubgroup :=
  iInf_le (fun W : {W : OpenNormalSubgroup G // IsPGroup p (G ⧸ W.1.toSubgroup)} =>
    W.1.toSubgroup) ⟨U, hU⟩

/-- The **maximal pro-`p` quotient** `G(p)` of a profinite group `G`, as an object of
`ProfiniteGrp`. -/
noncomputable def maxProPQuotient (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp :=
  haveI : IsClosed (proPKernel p G : Set G) := proPKernel_isClosed p G
  profiniteQuotient (proPKernel p G)

/-- The canonical projection `G → G(p)`, a continuous homomorphism. -/
noncomputable def maxProPMk (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    ContinuousMonoidHom G (maxProPQuotient p G) :=
  quotientMk (proPKernel p G)

/-! ## Universal property (kernel containment + hom-set bijection) -/

/-- **Kernel-containment lemma.**  A continuous homomorphism from `G` to a *pro-`p`* profinite
group `P` kills the pro-`p` kernel: `proPKernel p G ≤ ker f`.  Hence it factors through `G(p)`. -/
theorem proPKernel_le_ker {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (f : ContinuousMonoidHom G P) :
    proPKernel p G ≤ f.toMonoidHom.ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply eq_one_of_forall_mem_openNormalSubgroup
  intro V
  -- `φ = (P ↠ P⧸V) ∘ f : G → P⧸V`; its kernel is the open normal subgroup `f⁻¹ V`.
  set φ : G →* (P ⧸ V.toSubgroup) := (QuotientGroup.mk' V.toSubgroup).comp f.toMonoidHom with hφ
  have hset : ((φ.ker : Subgroup G) : Set G) = f.toMonoidHom ⁻¹' (V.toSubgroup : Set P) := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hopen : IsOpen ((φ.ker : Subgroup G) : Set G) := by
    rw [hset]; exact V.toOpenSubgroup.isOpen.preimage f.continuous_toFun
  let U : OpenNormalSubgroup G := { toSubgroup := φ.ker, isOpen' := hopen }
  have hUpg : IsPGroup p (G ⧸ U.toSubgroup) :=
    ((hP V).to_subgroup φ.range).of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  have hgU : g ∈ φ.ker := proPKernel_le U hUpg hg
  rwa [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hgU

/-- **Universal property of `G(p)`.**  For a pro-`p` profinite group `P`, restriction along the
projection `G → G(p)` is a bijection `Hom_cont(G(p), P) ≃ Hom_cont(G, P)`: every continuous
`f : G → P` factors *uniquely* through `G(p)`. -/
noncomputable def maxProPHomEquiv {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP p P) :
    ContinuousMonoidHom (maxProPQuotient p G) P ≃ ContinuousMonoidHom G P where
  toFun φ := φ.comp (maxProPMk p G)
  invFun f := quotientLift (proPKernel p G) f (proPKernel_le_ker hP f)
  left_inv φ := by
    ext x
    obtain ⟨y, rfl⟩ := quotientMk_surjective (proPKernel p G) x
    rfl
  right_inv f := by
    ext x
    rfl

/-! ## Pro-`p`-ness of `G(p)` -/

/-- If `Ŵ` is an open normal subgroup containing the pro-`p` kernel, then `G ⧸ Ŵ` is a `p`-group.
(By compactness some member `U` of the defining family already sits inside `Ŵ`, and `G ⧸ Ŵ` is
then a quotient of the `p`-group `G ⧸ U`.) -/
theorem isPGroup_quotient_of_proPKernel_le {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (W : OpenNormalSubgroup G)
    (hle : proPKernel p G ≤ W.toSubgroup) : IsPGroup p (G ⧸ W.toSubgroup) := by
  -- Step 1: some `U` in the defining family sits inside `Ŵ`.
  obtain ⟨U, hUpg, hUW⟩ :
      ∃ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) ∧ U.toSubgroup ≤ W.toSubgroup := by
    by_contra hcon
    replace hcon : ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) →
        ¬ U.toSubgroup ≤ W.toSubgroup := fun U hU hle => hcon ⟨U, hU, hle⟩
    set ι := {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)} with hι
    haveI : Nonempty ι := ⟨⟨topOpenNormalSubgroup G, isPGroup_quotient_top⟩⟩
    set t : ι → Set G := fun U => (U.1 : Set G) ∩ (W.toSubgroup : Set G)ᶜ with ht
    have htn : ∀ U, (t U).Nonempty := by
      intro U
      obtain ⟨x, hxU, hxW⟩ := SetLike.not_le_iff_exists.mp (hcon U.1 U.2)
      exact ⟨x, hxU, hxW⟩
    have htcl : ∀ U, IsClosed (t U) :=
      fun U => (U.1.toOpenSubgroup.isClosed).inter W.toOpenSubgroup.isOpen.isClosed_compl
    have htc : ∀ U, IsCompact (t U) := fun U => (htcl U).isCompact
    have htd : Directed (· ⊇ ·) t := by
      intro U V
      refine ⟨⟨U.1 ⊓ V.1, isPGroup_quotient_inf U.2 V.2⟩, ?_, ?_⟩
      · exact Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr inf_le_left)
      · exact Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr inf_le_right)
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl
    rw [Set.mem_iInter] at hx
    have hxK : x ∈ proPKernel p G := by
      rw [proPKernel, Subgroup.mem_iInf]; intro U; exact (hx U).1
    exact (hx (Classical.arbitrary ι)).2 (hle hxK)
  -- Step 2: `G ⧸ Ŵ` is a quotient of the `p`-group `G ⧸ U`.
  exact (hUpg.to_quotient (W.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))).of_equiv
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hUW)

/-- **`G(p)` is pro-`p`** (stated on the underlying quotient group).  Every finite continuous
quotient of `G ⧸ proPKernel p G` is a `p`-group. -/
theorem isProP_quotient_proPKernel {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    IsProP p (G ⧸ proPKernel p G) := by
  intro W
  -- pull `W` back to an open normal subgroup `Ŵ ≥ proPKernel p G` of `G`
  let Ŵ : OpenNormalSubgroup G :=
    { toSubgroup := W.toSubgroup.comap (QuotientGroup.mk' (proPKernel p G))
      isOpen' := W.toOpenSubgroup.isOpen.preimage continuous_quotient_mk'
      isNormal' := W.isNormal'.comap (QuotientGroup.mk' (proPKernel p G)) }
  have hKle : proPKernel p G ≤ Ŵ.toSubgroup := by
    intro g hg
    show QuotientGroup.mk' (proPKernel p G) g ∈ W.toSubgroup
    have hmkg : QuotientGroup.mk' (proPKernel p G) g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [hmkg]; exact one_mem _
  have hWpg : IsPGroup p (G ⧸ Ŵ.toSubgroup) := isPGroup_quotient_of_proPKernel_le Ŵ hKle
  have hmap : Ŵ.toSubgroup.map (QuotientGroup.mk' (proPKernel p G)) = W.toSubgroup :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact (hWpg.of_equiv (QuotientGroup.quotientQuotientEquivQuotient (proPKernel p G)
    Ŵ.toSubgroup hKle).symm).of_equiv (QuotientGroup.quotientMulEquivOfEq hmap)

/-- **`G(p)` is pro-`p`.**  This is the defining property of the maximal pro-`p` quotient
(same statement, phrased on the bundled `ProfiniteGrp` object). -/
theorem isProP_maxProPQuotient {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    IsProP p (maxProPQuotient p G) :=
  isProP_quotient_proPKernel

/-! ## Idempotence: a pro-`p` group is its own maximal pro-`p` quotient -/

/-- If `G` is already pro-`p`, its pro-`p` kernel is trivial. -/
theorem proPKernel_eq_bot_of_isProP {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : IsProP p G) : proPKernel p G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply eq_one_of_forall_mem_openNormalSubgroup
  intro V
  rw [proPKernel, Subgroup.mem_iInf] at hg
  exact hg ⟨V, hG V⟩


/-! ## Finite stress test: the finite `2`-group `Multiplicative (ZMod 4)` is its own maximal
pro-`2` quotient. -/

section FiniteExample


/-- `Multiplicative (ZMod 4)` is a finite `2`-group, hence pro-`2`; its pro-`2` kernel is
trivial, i.e. it is its own maximal pro-`2` quotient. -/
example : proPKernel 2 (Multiplicative (ZMod 4)) = ⊥ :=
  proPKernel_eq_bot_of_isProP
    (isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 2)
      (by rw [Nat.card_eq_fintype_card]; decide)))

end FiniteExample

end GQ2
