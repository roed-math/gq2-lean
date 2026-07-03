import Mathlib
import GQ2.MaxProP

/-!
# The pro-`p` Frattini/Burnside criterion  (ticket P-21, phase (iv))

The "surjective on the Frattini quotient ⇒ surjective" criterion for pro-`p` groups, in
**index-`p` detection form** — no Frattini subgroup object is introduced; the criterion
quantifies over the open normal subgroups of index `p` directly (they are exactly the kernels
of the maps to the Frattini quotient's `ℤ/p`-lines, and this is the form P-08's surjectivity
legs check on generators):

* `coatom_normal_of_pGroup` / `coatom_index_of_pGroup` — the **finite** ingredients: a maximal
  subgroup of a finite `p`-group is normal of index `p` (finite `p`-groups are nilpotent, so
  the normalizer condition makes maximal subgroups normal; the resulting simple quotient is an
  abelian simple `p`-group, i.e. `ℤ/p`).
* `eq_top_of_forall_map_eq_top` — a closed subgroup of a profinite group whose image in every
  open-normal finite quotient is everything is everything (density via the open-normal
  neighbourhood basis).
* **`eq_top_of_forall_not_le_index_p`** — the criterion, subgroup form: a closed subgroup of a
  pro-`p` group contained in **no** open normal subgroup of index `p` is the whole group.
  (This *is* `H·Φ(K) = K ⇒ H = K`: the open normal subgroups of index `p` are precisely the
  maximal open subgroups, by the finite ingredients, and `Φ(K)` is their intersection.)
* **`surjective_of_forall_not_le_index_p`** / `surjective_of_forall_index_p_quotient_surjective`
  — the hom forms (Burnside basis criterion): a continuous homomorphism into a pro-`p` group
  whose composites to all index-`p` quotients are surjective is surjective.

Everything is proved (no axioms, no sorries; std-3).  Paper use: Lemma 3.7 / Prop. 3.8's lift
legs show constructed endomorphisms of `D₀` are surjective by checking on
`B/2B = D₀^{ab} ⊗ 𝔽₂` — i.e. exactly on the index-2 quotients (`p = 2`).
-/

open scoped Classical

namespace GQ2

/-! ## Finite `p`-groups: maximal subgroups are normal of index `p` -/

section FrattiniFinite

variable {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]

/-- A maximal subgroup of a finite `p`-group is normal (nilpotency ⇒ normalizer condition). -/
theorem coatom_normal_of_pGroup (hQ : IsPGroup p Q) {M : Subgroup Q} (hM : IsCoatom M) :
    M.Normal := by
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom _
    Group.normalizerCondition_of_isNilpotent hM

/-- A maximal subgroup of a finite `p`-group has index `p` (the quotient is a simple abelian
`p`-group, i.e. `ℤ/p`). -/
theorem coatom_index_of_pGroup (hQ : IsPGroup p Q) {M : Subgroup Q} (hM : IsCoatom M) :
    M.index = p := by
  haveI hMn : M.Normal := coatom_normal_of_pGroup hQ hM
  have hT : IsPGroup p (Q ⧸ M) := hQ.to_quotient M
  -- the quotient is nontrivial …
  haveI : Nontrivial (Q ⧸ M) := by
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (Ne.lt_top hM.1)
    exact nontrivial_of_ne (QuotientGroup.mk x) 1
      (fun hone => hx ((QuotientGroup.eq_one_iff x).mp hone))
  -- … and simple (subgroup correspondence + maximality)
  haveI : IsSimpleGroup (Q ⧸ M) := by
    constructor
    intro N hN
    have hle : M ≤ N.comap (QuotientGroup.mk' M) := fun m hm => by
      have : QuotientGroup.mk' M m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      simp [Subgroup.mem_comap, this]
    rcases eq_or_lt_of_le hle with heq | hlt
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) N, ← heq,
        Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    · right
      have htop : N.comap (QuotientGroup.mk' M) = ⊤ := hM.2 _ hlt
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) N, htop]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)
  -- a simple `p`-group is abelian (its centre is nontrivial and normal) …
  have hZ : Subgroup.center (Q ⧸ M) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ M)) inferInstance
      with hbot | htop
    · haveI := hT.center_nontrivial
      rw [hbot] at this
      exact absurd this (not_nontrivial _)
    · exact htop
  letI : CommGroup (Q ⧸ M) :=
    { (inferInstance : Group (Q ⧸ M)) with
      mul_comm := fun a b => (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top b)) a }
  -- … hence of prime order, and the prime is `p`
  have hprime : (Nat.card (Q ⧸ M)).Prime := IsSimpleGroup.prime_card
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT
  rw [Subgroup.index_eq_card, hk]
  rw [hk] at hprime
  have hk1 : k = 1 := by
    cases k with
    | zero => exact absurd (by simpa using hprime) Nat.not_prime_one
    | succ j =>
      rcases hprime.eq_one_or_self_of_dvd p (dvd_pow_self p (Nat.succ_ne_zero j)) with h1 | hself
      · exact absurd h1 (Fact.out (p := p.Prime)).ne_one
      · have hpow : p ^ 1 = p ^ (j + 1) := by rw [pow_one]; exact hself
        have := Nat.pow_right_injective (Fact.out (p := p.Prime)).two_le hpow
        omega
  rw [hk1, pow_one]

end FrattiniFinite

/-! ## The profinite criterion -/

section FrattiniProfinite

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Group K] [TopologicalSpace K]
  [IsTopologicalGroup K] [CompactSpace K] [TotallyDisconnectedSpace K]

/-- A closed subgroup of a profinite group whose image in **every** open-normal finite quotient
is everything is everything (the open normal subgroups are a neighbourhood basis at `1`, so
full images at every level mean density). -/
lemma eq_top_of_forall_map_eq_top {H : Subgroup K} (hHc : IsClosed (H : Set K))
    (h : ∀ U : OpenNormalSubgroup K, H.map (QuotientGroup.mk' U.toSubgroup) = ⊤) : H = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun x => ?_
  have hx : x ∈ closure (H : Set K) := by
    rw [mem_closure_iff]
    intro O hO hxO
    have hO' : IsOpen ((x * ·) ⁻¹' O) := hO.preimage (continuous_const_mul x)
    have h1O' : (1 : K) ∈ (x * ·) ⁻¹' O := by simpa using hxO
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO' h1O'
    have hmem : QuotientGroup.mk' U.toSubgroup x ∈ H.map (QuotientGroup.mk' U.toSubgroup) := by
      rw [h U]
      exact Subgroup.mem_top _
    obtain ⟨h₀, hh₀H, hh₀x⟩ := hmem
    have hU' : x⁻¹ * h₀ ∈ U.toSubgroup := QuotientGroup.eq.mp hh₀x.symm
    refine ⟨h₀, ?_, hh₀H⟩
    have hmemO := hU hU'
    simpa [mul_inv_cancel_left] using hmemO
  rwa [hHc.closure_eq] at hx

/-- **The pro-`p` Frattini criterion, subgroup form**: a closed subgroup of a pro-`p` group
contained in no open normal subgroup of index `p` is the whole group.  (Equivalently
`H·Φ(K) = K ⇒ H = K`: by `coatom_normal_of_pGroup`/`coatom_index_of_pGroup` the index-`p` open
normal subgroups are exactly the maximal open subgroups.) -/
theorem eq_top_of_forall_not_le_index_p (hK : IsProP p K) {H : Subgroup K}
    (hHc : IsClosed (H : Set K))
    (h : ∀ M : OpenNormalSubgroup K, M.toSubgroup.index = p → ¬ H ≤ M.toSubgroup) :
    H = ⊤ := by
  refine eq_top_of_forall_map_eq_top hHc fun U => ?_
  by_contra hne
  haveI hfin : Finite (K ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  haveI : Finite (Subgroup (K ⧸ U.toSubgroup)) :=
    Finite.of_injective _ SetLike.coe_injective
  rcases eq_top_or_exists_le_coatom (H.map (QuotientGroup.mk' U.toSubgroup))
    with htop | ⟨Mbar, hMbar, hle⟩
  · exact hne htop
  have hpg : IsPGroup p (K ⧸ U.toSubgroup) := hK U
  haveI hMbarN : Mbar.Normal := coatom_normal_of_pGroup hpg hMbar
  -- pull the maximal subgroup back to an open normal subgroup of `K` of index `p`
  have hUle : U.toSubgroup ≤ Mbar.comap (QuotientGroup.mk' U.toSubgroup) := fun u hu => by
    have : QuotientGroup.mk' U.toSubgroup u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    simp [Subgroup.mem_comap, this]
  have hMopen : IsOpen ((Mbar.comap (QuotientGroup.mk' U.toSubgroup)) : Set K) :=
    Subgroup.isOpen_mono hUle U.isOpen'
  haveI hMnormal : (Mbar.comap (QuotientGroup.mk' U.toSubgroup)).Normal :=
    Subgroup.Normal.comap hMbarN _
  have hMindex : (Mbar.comap (QuotientGroup.mk' U.toSubgroup)).index = p := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact coatom_index_of_pGroup hpg hMbar
  have hHM : H ≤ Mbar.comap (QuotientGroup.mk' U.toSubgroup) :=
    le_trans (Subgroup.le_comap_map _ _) (Subgroup.comap_mono hle)
  exact h { toSubgroup := Mbar.comap (QuotientGroup.mk' U.toSubgroup), isOpen' := hMopen }
    hMindex hHM

/-- **The Burnside basis / Frattini criterion, hom form**: a continuous homomorphism from a
compact group into a pro-`p` group whose range lies in no index-`p` open normal subgroup is
surjective. -/
theorem surjective_of_forall_not_le_index_p [T2Space K]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (hK : IsProP p K) (f : ContinuousMonoidHom G K)
    (h : ∀ M : OpenNormalSubgroup K, M.toSubgroup.index = p →
      ¬ f.toMonoidHom.range ≤ M.toSubgroup) :
    Function.Surjective f := by
  have hclosed : IsClosed ((f.toMonoidHom.range : Subgroup K) : Set K) := by
    have hset : ((f.toMonoidHom.range : Subgroup K) : Set K) = Set.range f :=
      MonoidHom.coe_range f.toMonoidHom
    rw [hset]
    exact (isCompact_range f.continuous_toFun).isClosed
  have htop := eq_top_of_forall_not_le_index_p hK hclosed h
  exact MonoidHom.range_eq_top.mp htop

/-- Convenience form: it suffices that the composite to **every** index-`p` quotient is
surjective (the check P-08's legs perform on the marked generators). -/
theorem surjective_of_forall_index_p_quotient_surjective [T2Space K]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (hK : IsProP p K) (f : ContinuousMonoidHom G K)
    (h : ∀ M : OpenNormalSubgroup K, M.toSubgroup.index = p →
      Function.Surjective (QuotientGroup.mk' M.toSubgroup ∘ f)) :
    Function.Surjective f := by
  refine surjective_of_forall_not_le_index_p hK f fun M hM hle => ?_
  haveI : Finite (K ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  haveI : Nontrivial (K ⧸ M.toSubgroup) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index_eq_card, hM]
    exact (Fact.out (p := p.Prime)).one_lt
  obtain ⟨t, ht⟩ := exists_ne (1 : K ⧸ M.toSubgroup)
  obtain ⟨g, hg⟩ := h M hM t
  have hone : QuotientGroup.mk' M.toSubgroup (f g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hle ⟨g, rfl⟩)
  rw [Function.comp_apply] at hg
  exact ht (hg.symm.trans hone)

end FrattiniProfinite

end GQ2
