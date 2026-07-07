import GQ2.DimClose

/-!
# The residue-trivial tame lift — proved, no new axiom  (P-15f8)

`DimClose.lemma_6_17_dim_of_residueLift` reduced `lemma_6_17_dim` to one arithmetic input: a
lift `g₀` of tame inertia (`ρ g₀ = c tameTau`) acting trivially on the residue field
(`IsResidueTrivial (ker ρ) g₀`).  The classical statement is *"tame inertia acts trivially on
residue fields"* (Serre, *Local Fields*, Ch. IV §1: inertia is by definition the kernel of the
residue action, and wild + tame inertia sit inside it).  This file **derives it from the
existing axiom budget** — no residue fields and no new axiom — by a commutator trick:

1. **τ is a commutator.**  The tame relation `σ⁻¹τσ = τ²` gives `τ = (σ⁻¹τσ)τ⁻¹ = [σ⁻¹, τ]`
   in `T_tame`, so `tameF`-surjectivity produces a lift of `τ` that is a literal commutator
   `g₀ = s⁻¹ t s t⁻¹` in `G_ℚ₂`.
2. **Commutators are residue-trivial**, because the residue action is abelian
   (`Gal(𝔽̄₂/𝔽₂) = Ẑ`).  In the repo's spectral-norm vocabulary this is proved from scratch:
   * *Teichmüller approximation* (`exists_rootOfUnity_near`): every `y ∈ ℚ̄₂` with `‖y‖ = 1`
     is within norm `< 1` of a root of unity.  Proof: `k := ℚ₂(y)` is finite over `ℚ₂`; the
     B13 unit-filtration bundle gives `#(U⁰(k)/U¹(k)) = 2^f − 1 =: m`, so `‖y^m − 1‖ < 1`;
     `X^m − 1` splits over `ℚ̄₂` and `∏_ζ ‖y − ζ‖ = ‖y^m − 1‖ < 1`, so some factor is `< 1`
     (ultrametric pigeonhole — no Hensel needed).
   * *Commuting action on roots of unity* (`galois_smul_smul_comm_of_rootOfUnity`): Galois
     elements act on `⟨ζ⟩` by power maps (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), which
     commute.
   * Hence `‖[a,b]x − x‖ = ‖(ab)y − (ba)y‖ ≤ max(‖y − ζ‖, 0, ‖ζ − y‖) < 1`
     (`commutator_isResidueTrivial`).

The deliverable is `exists_residueTrivial_tameLift`.  Everything is `#print axioms` ⊆ std-3 +
B13 (`dyadicUnitFiltration`), already in the census.
-/

namespace GQ2

namespace ResidueLift

open Polynomial

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Step 1: the ultrametric pigeonhole -/

/-- If `‖y^m − 1‖ < 1` (`m ≥ 1`), some `m`-th root of unity is within norm `< 1` of `y`:
`X^m − 1` splits over `ℚ̄₂` and the product of the root distances is `‖y^m − 1‖`. -/
theorem exists_nthRoot_near (y : ℚ̄₂) (m : ℕ) (hm : 1 ≤ m) (h : ‖y ^ m - 1‖ < 1) :
    ∃ ζ : ℚ̄₂, ζ ^ m = 1 ∧ ‖y - ζ‖ < 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  set p : Polynomial ℚ̄₂ := X ^ m - C 1 with hp
  have hmonic : p.Monic := monic_X_pow_sub_C 1 (by omega)
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hfact : p = (p.roots.map (fun r => X - C r)).prod :=
    hsplits.eq_prod_roots_of_monic hmonic
  -- evaluate at `y` and take norms
  have heval : y ^ m - 1 = (p.roots.map (fun r => y - r)).prod := by
    have h1 : y ^ m - 1 = p.eval y := by simp [hp]
    rw [h1]
    conv_lhs => rw [hfact]
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp
  have hnorm : ‖y ^ m - 1‖ = (p.roots.map (fun r => ‖y - r‖)).prod := by
    rw [heval]
    induction (p.roots) using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]
  -- every root is an `m`-th root of unity, hence at distance `≥ 1` from `y` by `hcon`
  have hge : ∀ z ∈ p.roots.map (fun r => ‖y - r‖), (1 : ℝ) ≤ z := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
    have hroot : r ^ m = 1 := by
      have h0 : p.eval r = 0 := (mem_roots hmonic.ne_zero).mp hr
      have h1 : r ^ m - 1 = 0 := by simpa [hp] using h0
      exact sub_eq_zero.mp h1
    exact hcon r hroot
  have hprod : (1 : ℝ) ≤ (p.roots.map (fun r => ‖y - r‖)).prod :=
    Multiset.one_le_prod hge
  rw [hnorm] at h
  linarith

/-! ## Step 2: Teichmüller approximation via the B13 unit filtration -/

/-- **Every norm-one element of `ℚ̄₂` is within norm `< 1` of a root of unity.**  `k := ℚ₂(y)`
is finite over `ℚ₂`; the B13 bundle gives `#(U⁰(k)/U¹(k)) = 2^f − 1 =: m`, so
`‖y^m − 1‖ ≤ ‖π‖ < 1`, and the pigeonhole produces the nearby `m`-th root of unity. -/
theorem exists_rootOfUnity_near (y : ℚ̄₂) (hy : ‖y‖ = 1) :
    ∃ (m : ℕ) (ζ : ℚ̄₂), 1 ≤ m ∧ ζ ^ m = 1 ∧ ‖y - ζ‖ < 1 := by
  classical
  have hint : IsIntegral ℚ_[2] y := Algebra.IsIntegral.isIntegral y
  set k : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.adjoin ℚ_[2] {y} with hk
  haveI : FiniteDimensional ℚ_[2] k := IntermediateField.adjoin.finiteDimensional hint
  set D := dyadicUnitFiltration k with hD
  have hymem : y ∈ k := IntermediateField.mem_adjoin_simple_self ℚ_[2] y
  have hy0 : (⟨y, hymem⟩ : ↥k) ≠ 0 := by
    intro h0
    rw [Subtype.ext_iff] at h0
    rw [show y = (0 : ℚ̄₂) from h0, norm_zero] at hy
    exact one_ne_zero hy.symm
  set u : (↥k)ˣ := Units.mk0 ⟨y, hymem⟩ hy0 with hu
  have humem : u ∈ normUnits k := by
    show ‖((u : ↥k) : ℚ̄₂)‖ = 1
    exact hy
  set m : ℕ := 2 ^ D.f - 1 with hm_def
  have hm : 1 ≤ m := by
    have h2 : 2 ≤ 2 ^ D.f := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ D.f := Nat.pow_le_pow_right (by norm_num) D.hf_pos
    omega
  -- the class of `u` in the order-`m` residue quotient has `u^m ∈ U¹`
  have hcardQ : Nat.card (↥(normUnits k) ⧸
      (depthUnits k D.π 1).subgroupOf (normUnits k)) = m := D.card_gr_zero
  have hq : (QuotientGroup.mk' ((depthUnits k D.π 1).subgroupOf (normUnits k))
      ((⟨u, humem⟩ : ↥(normUnits k)) ^ m)) = 1 := by
    rw [map_pow]
    have := pow_card_eq_one'
      (x := QuotientGroup.mk' ((depthUnits k D.π 1).subgroupOf (normUnits k)) ⟨u, humem⟩)
    rwa [hcardQ] at this
  have hmem2 : (⟨u, humem⟩ : ↥(normUnits k)) ^ m
      ∈ (depthUnits k D.π 1).subgroupOf (normUnits k) :=
    (QuotientGroup.eq_one_iff _).mp hq
  have hdepth : u ^ m ∈ depthUnits k D.π 1 := by
    have h1 := (Subgroup.mem_subgroupOf).mp hmem2
    simpa using h1
  have hbound := ((mem_depthUnits k D.π 1 (u ^ m)).mp hdepth).2
  have hcoe : (((u ^ m : (↥k)ˣ) : ↥k) : ℚ̄₂) = y ^ m := by
    rw [Units.val_pow_eq_pow_val]
    push_cast
    rfl
  rw [hcoe, pow_one] at hbound
  have hlt : ‖y ^ m - 1‖ < 1 := lt_of_le_of_lt hbound D.hπ_lt
  obtain ⟨ζ, hζ, hnear⟩ := exists_nthRoot_near y m hm hlt
  exact ⟨m, ζ, hm, hζ, hnear⟩

/-! ## Step 3: Galois elements commute on roots of unity -/

/-- Galois elements act on the powers of a root of unity by commuting power maps. -/
theorem galois_smul_smul_comm_of_rootOfUnity (ζ : ℚ̄₂) (m : ℕ) (hm : 1 ≤ m) (hζ : ζ ^ m = 1)
    (a b : Kummer.GaloisGroup ℚ_[2]) : a • (b • ζ) = b • (a • ζ) := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hζ⟩
  have hm₀ : 0 < orderOf ζ := hfin.orderOf_pos
  haveI : NeZero (orderOf ζ) := ⟨hm₀.ne'⟩
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  have key : ∀ w : Kummer.GaloisGroup ℚ_[2], ∃ i, w • ζ = ζ ^ i := by
    intro w
    have hpow : (w • ζ) ^ orderOf ζ = 1 := by
      rw [AlgEquiv.smul_def, ← map_pow, pow_orderOf_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
    exact ⟨i, hi.symm⟩
  obtain ⟨i, hi⟩ := key a
  obtain ⟨j, hj⟩ := key b
  calc a • (b • ζ) = a • ζ ^ j := by rw [hj]
    _ = (a • ζ) ^ j := by rw [AlgEquiv.smul_def, AlgEquiv.smul_def, map_pow]
    _ = ζ ^ (i * j) := by rw [hi, ← pow_mul]
    _ = ζ ^ (j * i) := by rw [Nat.mul_comm]
    _ = (b • ζ) ^ i := by rw [hj, ← pow_mul]
    _ = b • ζ ^ i := by rw [AlgEquiv.smul_def, AlgEquiv.smul_def, map_pow]
    _ = b • (a • ζ) := by rw [hi]

/-! ## Step 4: commutators are residue-trivial -/

/-- **Commutators of `G_ℚ₂` are residue-trivial** — the residue action is abelian, in
spectral-norm form: for any `a, b` and integral `x`, `‖(aba⁻¹b⁻¹)x − x‖ < 1`.  (The
`N`-fixedness hypothesis of `IsResidueTrivial` is not even needed.) -/
theorem commutator_isResidueTrivial (N : Subgroup (Kummer.GaloisGroup ℚ_[2]))
    (a b : Kummer.GaloisGroup ℚ_[2]) :
    IsResidueTrivial N (a * b * a⁻¹ * b⁻¹) := by
  intro x _ hx1
  set y : ℚ̄₂ := (b * a)⁻¹ • x with hy_def
  have hyx : (b * a) • y = x := smul_inv_smul _ x
  have hcomm : (a * b * a⁻¹ * b⁻¹) • x = (a * b) • y := by
    rw [show a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ from by group, mul_smul, hy_def]
  have hgoal : (a * b * a⁻¹ * b⁻¹) • x - x = (a * b) • y - (b * a) • y := by
    rw [hcomm, hyx]
  rw [hgoal]
  have hy1 : ‖y‖ ≤ 1 := by rw [hy_def, norm_galois]; exact hx1
  rcases lt_or_eq_of_le hy1 with hlt | heq
  · -- `‖y‖ < 1`: both terms are already small
    have h1 : ‖(a * b) • y - (b * a) • y‖ ≤ max ‖(a * b) • y‖ ‖(b * a) • y‖ := by
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_neg]
    have hn1 : ‖(a * b) • y‖ = ‖y‖ := norm_galois _ _
    have hn2 : ‖(b * a) • y‖ = ‖y‖ := norm_galois _ _
    rw [hn1, hn2, max_self] at h1
    exact lt_of_le_of_lt h1 hlt
  · -- `‖y‖ = 1`: approximate by a root of unity, where the actions commute exactly
    obtain ⟨m, ζ, hm, hζ, hnear⟩ := exists_rootOfUnity_near y heq
    have hcommζ : (a * b) • ζ = (b * a) • ζ := by
      rw [mul_smul, mul_smul]
      exact galois_smul_smul_comm_of_rootOfUnity ζ m hm hζ a b
    have hsplit : (a * b) • y - (b * a) • y
        = ((a * b) • y - (a * b) • ζ) + ((b * a) • ζ - (b * a) • y) := by
      rw [hcommζ]
      ring
    have hA : ‖(a * b) • y - (a * b) • ζ‖ < 1 := by
      have h1 : (a * b) • y - (a * b) • ζ = (a * b) • (y - ζ) := by
        rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_sub]
      rw [h1, norm_galois]
      exact hnear
    have hB : ‖(b * a) • ζ - (b * a) • y‖ < 1 := by
      have h1 : (b * a) • ζ - (b * a) • y = (b * a) • (ζ - y) := by
        rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_sub]
      rw [h1, norm_galois, norm_sub_rev]
      exact hnear
    rw [hsplit]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hA hB)

/-! ## Step 5: the residue-trivial tame lift -/

/-- **The residue-trivial tame lift — proved** (no axiom): the tame relation `σ⁻¹τσ = τ²`
makes `τ` a commutator, so it lifts to a commutator of `G_ℚ₂`, which is residue-trivial by
`commutator_isResidueTrivial`.  This is the last input of
`DimClose.lemma_6_17_dim_of_residueLift`. -/
theorem exists_residueTrivial_tameLift {C : Type} [Group C] [TopologicalSpace C]
    (B : BoundaryMaps) (c : ContinuousMonoidHom Ttame C)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g)) :
    ∃ g₀ : AbsGalQ2, ρ g₀ = c tameTau ∧
      IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) g₀ := by
  obtain ⟨s, hs⟩ := B.tameF_surjective tameSigma
  obtain ⟨t, ht⟩ := B.tameF_surjective tameTau
  refine ⟨s⁻¹ * t * s * t⁻¹, ?_, ?_⟩
  · rw [hfac]
    have hτ : B.tameF (s⁻¹ * t * s * t⁻¹) = tameTau := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs, ht]
      have hrel : tameSigma⁻¹ * tameTau * tameSigma = tameTau ^ 2 := tame_relation
      calc tameSigma⁻¹ * tameTau * tameSigma * tameTau⁻¹
          = (tameSigma⁻¹ * tameTau * tameSigma) * tameTau⁻¹ := by group
        _ = tameTau ^ 2 * tameTau⁻¹ := by rw [hrel]
        _ = tameTau := by group
    rw [hτ]
  · have hct : IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
        (s⁻¹ * t * s⁻¹⁻¹ * t⁻¹) :=
      commutator_isResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) s⁻¹ t
    rwa [inv_inv] at hct

/-! ## Step 6: the splitting-field plumbing from the infinite Galois correspondence -/

section Plumbing

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The identity bridge from the `AlgEquiv`-view Galois group to `AbsGalQ2` (the two views
are the same type; the bridge keeps function applications in one view). -/
def toAbs (x : Kummer.GaloisGroup ℚ_[2]) : AbsGalQ2 := x

/-- `ker ρ`, repackaged as a subgroup of the `AlgEquiv`-view Galois group (the two views'
`Group` instances agree only at default transparency, so the closure proofs go by `exact`). -/
def kerGal (ρ : ContinuousMonoidHom AbsGalQ2 C) : Subgroup (Kummer.GaloisGroup ℚ_[2]) where
  carrier := {x : Kummer.GaloisGroup ℚ_[2] | ρ (toAbs x) = 1}
  one_mem' := map_one ρ
  mul_mem' := fun {a b} ha hb => by
    have hab : toAbs (a * b) = toAbs a * toAbs b := rfl
    show ρ (toAbs (a * b)) = 1
    rw [hab, map_mul, ha, hb, one_mul]
  inv_mem' := fun {a} ha => by
    have hia : toAbs a⁻¹ = (toAbs a)⁻¹ := rfl
    show ρ (toAbs a⁻¹) = 1
    rw [hia, map_inv, ha, inv_one]

theorem mem_kerGal (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : Kummer.GaloisGroup ℚ_[2]) :
    x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ kerGal ρ := Iff.rfl

theorem kerGal_isOpen (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    IsOpen ((kerGal ρ : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2])) := by
  have hcont : Continuous fun x : Kummer.GaloisGroup ℚ_[2] => ρ (toAbs x) :=
    ρ.continuous_toFun
  have h1 : ((kerGal ρ : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2]))
      = (fun x : Kummer.GaloisGroup ℚ_[2] => ρ (toAbs x)) ⁻¹' {1} := rfl
  rw [h1]
  exact (isOpen_discrete ({1} : Set C)).preimage hcont

theorem kerGal_isClosed (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    IsClosed ((kerGal ρ : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2])) :=
  Subgroup.isClosed_of_isOpen _ (kerGal_isOpen ρ)

/-- The splitting field of `ρ`: the fixed field of `ker ρ`. -/
noncomputable def splitField (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    IntermediateField ℚ_[2] ℚ̄₂ :=
  IntermediateField.fixedField (kerGal ρ)

/-- The closed-subgroup Galois correspondence recovers `ker ρ` from its fixed field. -/
theorem fixingSubgroup_splitField (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    (splitField ρ).fixingSubgroup = kerGal ρ :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨kerGal ρ, kerGal_isClosed ρ⟩

/-- `ker ρ` is open, so its fixed field is finite over `ℚ₂`. -/
theorem splitField_finiteDimensional (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    FiniteDimensional ℚ_[2] (splitField ρ) := by
  refine (InfiniteGalois.isOpen_iff_finite (splitField ρ)).mp ?_
  rw [fixingSubgroup_splitField]
  exact kerGal_isOpen ρ

theorem hker_splitField (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (x : Kummer.GaloisGroup ℚ_[2]) :
    x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ (splitField ρ).fixingSubgroup := by
  rw [fixingSubgroup_splitField]
  exact mem_kerGal ρ x

/-- Any action of any group on `𝔽₂` is trivial. -/
theorem htriv_zmod2 {G : Type*} [Group G] [DistribMulAction G (ZMod 2)] (g : G) (m : ZMod 2) :
    g • m = m := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz m with rfl | rfl
  · exact smul_zero g
  · by_contra hne
    have h1 : g • (1 : ZMod 2) = 0 := by
      rcases hz (g • (1 : ZMod 2)) with h | h
      · exact h
      · exact absurd h hne
    have h2 : (1 : ZMod 2) = g⁻¹ • (0 : ZMod 2) := by
      rw [← h1, inv_smul_smul]
    rw [smul_zero] at h2
    exact one_ne_zero h2

end Plumbing

/-! ## Step 7: `lemma_6_17_dim`, fully closed downstream -/

section Final

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

open ContCoh QuadraticFp2 in
/-- **`lemma_6_17_dim`, closed** (P-15f8 + the residue-lift derivation): the §6.3 deep-half
dimension identity `#X₊² = #H¹(ℚ₂, V)`, from `SectionSix.lemma_6_17_dim`'s own hypothesis set
plus only the finiteness instance `[Finite (H¹(ker ρ, 𝔽₂))]` (the local finiteness
`H¹(G_K, 𝔽₂) ≅ K^×/2`; a B12/B13 consequence, threaded pending its own splice).  No new
axiom: the residue-trivial tame lift is `exists_residueTrivial_tameLift`, and the splitting
field with its Galois-correspondence data is `splitField`. -/
theorem lemma_6_17_dim_final (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))] :
    Nat.card (SectionSix.deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  haveI : FiniteDimensional ℚ_[2] (splitField ρ) := splitField_finiteDimensional ρ
  obtain ⟨g₀, hg₀, hg₀rt⟩ := exists_residueTrivial_tameLift B c ρ hfac
  exact DimClose.lemma_6_17_dim_of_residueLift B c hc ρ hfac hρ hV2 hfaith hsimple hram
    q hq hns hinv (splitField ρ) (fun g m => htriv_zmod2 g m) (hker_splitField ρ)
    g₀ hg₀ hg₀rt

end Final

end ResidueLift

end GQ2
