import GQ2.DeepPart.MuTwoPolarDual

/-!
# The `Q⁰_loc` quadratic structure  (§6.3, eq. (93))

`Q⁰_loc` is a quadratic map on `H¹(G_ℚ₂, V)` whose polar form is the cup product of the polar
pairing (through `ι_F`): at the cochain level,
`gp(b₁+b₂) − gp(b₁) − gp(b₂) − (b₂ ∪_B b₁) = δ¹(g ↦ f(b₁ g, b₂ g))`,
by four instances of the factor-set cocycle identity and `f_polar` — no bilinearity of `f`
needed.  Class level via `RepIndependence.repIndep` (Lemma 6.4).  This layer also proves the
nonsingularity of `Q⁰_loc`, that the deep half `X₊` is an additive subgroup, and the dim clause
feeding Prop 6.18 (ramified).

This file is part of the `GQ2.DeepPart` split (P-15f); see `GQ2/DeepPart.lean` for the overview.
-/

open scoped Classical

namespace GQ2.DeepPart

open GQ2 GQ2.ContCoh GQ2.Foundations

section Q0locLayer

open Corestriction SectionSix RepIndependence GQ2.QuadraticFp2

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **The (93) cochain identity**: the graph pullback is quadratic in the cocycle, with the
cup cocycle of the polar pairing (swapped slots) as cross-term, up to the explicit coboundary
`δ¹(g ↦ f(b₁ g, b₂ g))`. -/
theorem graphPullback_add_sub_mem_B2 (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (b₁ b₂ : ↥(Z1 AbsGalQ2 V)) :
    graphPullback dat ρ ((b₁ + b₂ : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V)
      - (graphPullback dat ρ b₁.1 + graphPullback dat ρ b₂.1
        + cup11Fun (polarBihom q hq) b₂.1 b₁.1) ∈ B2 AbsGalQ2 (ZMod 2) := by
  obtain ⟨hb₁c, hb₁⟩ := mem_Z1_iff.mp b₁.2
  obtain ⟨hb₂c, hb₂⟩ := mem_Z1_iff.mp b₂.2
  refine AddSubgroup.mem_map.mpr ⟨fun g => dat.f (b₁.1 g) (b₂.1 g), ?_, ?_⟩
  · -- continuity of the correcting 1-cochain
    refine mem_C1_iff.mpr ?_
    have hF : Continuous fun g : AbsGalQ2 => ((b₁.1 g, b₂.1 g) : V × V) := hb₁c.prodMk hb₂c
    exact (continuous_of_discreteTopology (f := fun t : V × V => dat.f t.1 t.2)).comp hF
  · funext p
    obtain ⟨g, h⟩ := p
    have hgh₁ : b₁.1 (g * h) = b₁.1 g + ρ g • b₁.1 h := by rw [hb₁ g h, hρ]
    have hgh₂ : b₂.1 (g * h) = b₂.1 g + ρ g • b₂.1 h := by rw [hb₂ g h, hρ]
    have hm := hdat.m_quad (ρ g) (b₁.1 h) (b₂.1 h)
    have R₁ := hdat.f_cocycle (b₁.1 g) (b₂.1 g) (ρ g • b₁.1 h + ρ g • b₂.1 h)
    have R₂ := hdat.f_cocycle (b₁.1 g) (ρ g • b₁.1 h) (b₂.1 g + ρ g • b₂.1 h)
    have R₃ := hdat.f_cocycle (b₂.1 g) (ρ g • b₁.1 h) (ρ g • b₂.1 h)
    have R₄ := hdat.f_cocycle (ρ g • b₁.1 h) (b₂.1 g) (ρ g • b₂.1 h)
    have P := hdat.f_polar (b₂.1 g) (ρ g • b₁.1 h)
    rw [show b₂.1 g + (ρ g • b₁.1 h + ρ g • b₂.1 h)
        = ρ g • b₁.1 h + (b₂.1 g + ρ g • b₂.1 h) from by abel] at R₁
    rw [show ρ g • b₁.1 h + b₂.1 g = b₂.1 g + ρ g • b₁.1 h from by abel] at R₄
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, absGal_smul_zmodTwo,
      Pi.sub_apply, Pi.add_apply, AddSubgroup.coe_add, graphPullback, cup11Fun,
      polarBihom_apply, smul_add]
    rw [hgh₁, hgh₂]
    simp only [hρ]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hm + R₁ + R₂ + R₃ + R₄ + P

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- `Q⁰_loc` unfolded (definitional). -/
theorem Q0loc_apply (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : H1 AbsGalQ2 V) :
    Q0loc D dat ρ x
      = iotaF D (H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1)) := rfl

omit [TopologicalSpace V] [DiscreteTopology V] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- The polar pairing is `G_ℚ₂`-equivariant for a Galois-invariant `q` (`𝔽₂` acts trivially). -/
theorem polarBihom_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) (g : AbsGalQ2) (v w : V) :
    polarBihom q hq (g • v) (g • w) = g • polarBihom q hq v w := by
  rw [absGal_smul_zmodTwo, polarBihom_apply, polarBihom_apply]
  exact polar_smul_smul V q hqG g v w

omit [Finite C] [Finite V] in
/-- **Eq. (93), class level**: `Q⁰_loc(x+y) = Q⁰_loc(x) + Q⁰_loc(y) + ι_F(y ∪_B x)`. -/
theorem Q0loc_add (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (x y : H1 AbsGalQ2 V) :
    Q0loc D dat ρ (x + y)
      = Q0loc D dat ρ x + Q0loc D dat ρ y
        + iotaF D (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x) := by
  classical
  have hmem₁ : graphPullback dat ρ (Quotient.out x).1 ∈ Z2 AbsGalQ2 (ZMod 2) :=
    graphPullback_mem_Z2 dat hdat ρ hρ _
  have hmem₂ : graphPullback dat ρ (Quotient.out y).1 ∈ Z2 AbsGalQ2 (ZMod 2) :=
    graphPullback_mem_Z2 dat hdat ρ hρ _
  have hmem₃ : cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1
      ∈ Z2 AbsGalQ2 (ZMod 2) :=
    cup11_mem_Z2 _ (polarBihom_equivariant q hq hqG) _ _
  have hrep : H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out (x + y)).1)
      = H2ofFun AbsGalQ2 (graphPullback dat ρ
          ((Quotient.out x + Quotient.out y : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V)) := by
    apply repIndep dat hdat ρ hρ
    rw [H1mk_out, map_add, H1mk_out, H1mk_out]
  have hsplit : H2ofFun AbsGalQ2 (graphPullback dat ρ
        ((Quotient.out x + Quotient.out y : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V))
      = H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1
          + graphPullback dat ρ (Quotient.out y).1
          + cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1) :=
    h2ofFun_eq_of_sub_mem_B2 (graphPullback_add_sub_mem_B2 q hq dat hdat ρ hρ _ _)
  rw [Q0loc_apply, Q0loc_apply, Q0loc_apply, hrep, hsplit,
    H2ofFun_of_mem (add_mem (add_mem hmem₁ hmem₂) hmem₃),
    H2ofFun_of_mem hmem₁, H2ofFun_of_mem hmem₂]
  have hmk : (⟨graphPullback dat ρ (Quotient.out x).1
        + graphPullback dat ρ (Quotient.out y).1
        + cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1,
      add_mem (add_mem hmem₁ hmem₂) hmem₃⟩ : ↥(Z2 AbsGalQ2 (ZMod 2)))
      = ⟨graphPullback dat ρ (Quotient.out x).1, hmem₁⟩
        + ⟨graphPullback dat ρ (Quotient.out y).1, hmem₂⟩
        + ⟨cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1, hmem₃⟩ :=
    Subtype.ext rfl
  rw [hmk, map_add, map_add, map_add, map_add]
  congr 1
  conv_rhs => rw [← H1mk_out y, ← H1mk_out x, cup11_mk_mk]

omit [Finite C] [Finite V] in
/-- **The polar form of `Q⁰_loc`** is the (swapped) polar-pairing cup through `ι_F` —
eq. (93) in polar form. -/
theorem polar_Q0loc (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (x y : H1 AbsGalQ2 V) :
    polar (Q0loc D dat ρ) x y
      = iotaF D (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x) := by
  unfold GQ2.QuadraticFp2.polar
  rw [Q0loc_add D q hq dat hdat ρ hρ hqG x y]
  linear_combination CharTwo.add_self_eq_zero (Q0loc D dat ρ x)
    + CharTwo.add_self_eq_zero (Q0loc D dat ρ y)

omit [Finite C] [Finite V] in
/-- **`Q⁰_loc` is a quadratic map** on `H¹(G_ℚ₂, V)` (eq. (93)): normalized with biadditive
polar form. -/
theorem isQuadraticFp2_Q0loc (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) :
    IsQuadraticFp2 (Q0loc D dat ρ (V := V)) := by
  constructor
  · -- normalization `Q⁰_loc(0) = 0`
    have hzero : graphPullback dat ρ ((0 : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V) = 0 := by
      funext p
      show dat.f ((0 : AbsGalQ2 → V) p.1) (ρ p.1 • (0 : AbsGalQ2 → V) p.2)
          + dat.m (ρ p.1) ((0 : AbsGalQ2 → V) p.2) = 0
      simp only [Pi.zero_apply]
      rw [hdat.f_zero_left, hdat.m_zero, add_zero]
    have hrep0 : H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out (0 : H1 AbsGalQ2 V)).1)
        = H2ofFun AbsGalQ2 (graphPullback dat ρ ((0 : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V)) := by
      apply repIndep dat hdat ρ hρ
      rw [H1mk_out, map_zero]
    rw [Q0loc_apply, hrep0, hzero, H2ofFun_of_mem (zero_mem _),
      show (⟨(0 : AbsGalQ2 × AbsGalQ2 → ZMod 2), zero_mem _⟩
        : ↥(Z2 AbsGalQ2 (ZMod 2))) = 0 from rfl,
      map_zero, map_zero]
  · -- polar additive, left
    intro u v w
    rw [polar_Q0loc D q hq dat hdat ρ hρ hqG, polar_Q0loc D q hq dat hdat ρ hρ hqG,
      polar_Q0loc D q hq dat hdat ρ hρ hqG, map_add, map_add]
  · -- polar additive, right
    intro u v w
    rw [polar_Q0loc D q hq dat hdat ρ hρ hqG, polar_Q0loc D q hq dat hdat ρ hρ hqG,
      polar_Q0loc D q hq dat hdat ρ hρ hqG, map_add, AddMonoidHom.add_apply, map_add]

/-! ### Nonsingularity of `Q⁰_loc`  (B6 `perfect11` via the polar `μ₂`-dual) -/

/-- SectionSix's `𝔽₂ → μ₂` bridge is (definitionally) the `DeepPart` one. -/
theorem muTwoOfF2_eq : SectionSix.muTwoOfF2 = zmodTwoToMuTwo := rfl

theorem zmodTwoToMuTwo_injective : Function.Injective zmodTwoToMuTwo :=
  zmodTwoEquivMuTwo.injective

theorem muTwoOfF2_injective : Function.Injective SectionSix.muTwoOfF2 :=
  zmodTwoToMuTwo_injective

/-- The `μ₂`-valued polar self-duality `v ↦ (w ↦ bridge(B(v,w)))` — definitionally
`postPairing` of the polar pairing with the bridge, viewed into the `μ₂`-dual. -/
noncomputable def polarMuDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q) : V →+ MuDual 2 V :=
  postPairing (polarBihom q hq) SectionSix.muTwoOfF2


omit [TopologicalSpace V] [DiscreteTopology V] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- Equivariance of the polar `μ₂`-dual map. -/
theorem polarMuDual_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) (g : AbsGalQ2) (v : V) :
    polarMuDual q hq (g • v) = g • polarMuDual q hq v := by
  refine DFunLike.ext _ _ fun m => ?_
  rw [muDual_smul_apply, muTwo_smul_trivial]
  show SectionSix.muTwoOfF2 (polar q (g • v) m) = SectionSix.muTwoOfF2 (polar q v (g⁻¹ • m))
  congr 1
  have hps := polar_smul_smul V q hqG g v (g⁻¹ • m)
  rwa [smul_inv_smul] at hps

omit [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction AbsGalQ2 V]
  [ContinuousSMul AbsGalQ2 V] in
/-- `#Hom(V, μ₂) = #V` for exp-2 `V`. -/
theorem card_muDual (h2 : ∀ v : V, v + v = 0) : Nat.card (MuDual 2 V) = Nat.card V := by
  have h1 : Nat.card (MuDual 2 V) = Nat.card (V →+ ZMod 2) := by
    refine Nat.card_congr ⟨fun f => zmodTwoEquivMuTwo.symm.toAddMonoidHom.comp (f : V →+ MuN 2),
      fun f => (zmodTwoEquivMuTwo.toAddMonoidHom.comp f : MuDual 2 V), fun f => ?_, fun f => ?_⟩
    · refine DFunLike.ext _ _ fun m => ?_
      show zmodTwoEquivMuTwo (zmodTwoEquivMuTwo.symm ((f : V →+ MuN 2) m)) = f m
      rw [AddEquiv.apply_symm_apply]
    · ext m
      show zmodTwoEquivMuTwo.symm (zmodTwoEquivMuTwo (f m)) = f m
      rw [AddEquiv.symm_apply_apply]
  rw [h1, card_addHom_zmod2 V h2]

omit [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction AbsGalQ2 V]
  [ContinuousSMul AbsGalQ2 V] in
/-- The polar `μ₂`-dual map is bijective (nonsingularity + counting). -/
theorem polarMuDual_bijective (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0) :
    Function.Bijective (polarMuDual q hq (V := V)) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (MuDual 2 V) := Fintype.ofFinite _
  have hinj : Function.Injective (polarMuDual q hq (V := V)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    obtain ⟨w, hw⟩ := hns v hne
    apply hw
    have h0 : SectionSix.muTwoOfF2 (polar q v w) = 0 := by
      have := DFunLike.congr_fun hv w
      rwa [MuDual.zero_apply] at this
    exact muTwoOfF2_injective (by rw [h0, map_zero])
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_muDual h2]

/-- **`mapCoeff1` of an equivariant additive bijection is injective** (coboundaries pull back
along the inverse). -/
theorem mapCoeff1_injective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A] [DiscreteTopology B]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    [DistribMulAction AbsGalQ2 B] [ContinuousSMul AbsGalQ2 B]
    (f : A →+ B) (hf : Continuous f)
    (hcompat : ∀ (g : AbsGalQ2) (a : A), f (g • a) = g • f a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    Function.Injective (mapCoeff1 f hf hcompat) := by
  rw [injective_iff_map_eq_zero]
  intro xq
  induction xq using QuotientAddGroup.induction_on with
  | H b =>
    intro hxq
    have hxq' : H1mk AbsGalQ2 B
        (Z1comap (ContinuousMonoidHom.id AbsGalQ2) f hf (fun g n => hcompat g n) b) = 0 := hxq
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp hxq'
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨n, hn⟩ := hmem
    obtain ⟨m, rfl⟩ := hsurj n
    show H1mk AbsGalQ2 A b = 0
    refine (QuotientAddGroup.eq_zero_iff b).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨m, ?_⟩
    funext g
    apply hinj
    have hg := congrFun hn g
    show f (g • m - m) = f (b.1 g)
    rw [map_sub, hcompat]
    exact hg

omit [Finite V] in
/-- **Cup coefficient naturality at the polar pairing**: pushing the `𝔽₂`-valued polar cup along
the `μ₂`-bridge is the `μ₂`-evaluation cup against the polar `μ₂`-dual class (definitional at
representatives). -/
theorem mapCoeff2_muTwo_cup (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (y x : H1 AbsGalQ2 V) :
    mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology
        SectionSix.muTwoOfF2_equivariant
        (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x)
      = cup11 (muDualPairing 2 V) (muDualPairing_equivariant 2 V)
          (mapCoeff1 (polarMuDual q hq) continuous_of_discreteTopology
            (polarMuDual_equivariant q hq hqG) y) x := by
  induction y using QuotientAddGroup.induction_on with
  | H b =>
    induction x using QuotientAddGroup.induction_on with
    | H a => rfl

omit [Finite C] in
/-- **`Q⁰_loc` is nonsingular** (§6.3): its polar form is a perfect pairing on `H¹(G_ℚ₂, V)`,
via B6's `perfect11` clause through the polar `μ₂`-self-duality. -/
theorem nonsingular_Q0loc (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) :
    Nonsingular (Q0loc D dat ρ (V := V)) := by
  intro x hx
  have htor : ∀ v : V, (2 : ℕ) • v = 0 := fun v => (two_nsmul v).trans (h2 v)
  have hbij := polarMuDual_bijective q hq hns h2
  have hxne : mapCoeff1 (polarMuDual q hq) continuous_of_discreteTopology
      (polarMuDual_equivariant q hq hqG) x ≠ 0 := by
    intro h0
    exact hx (mapCoeff1_injective _ _ _ hbij.1 hbij.2 (by rw [h0, map_zero]))
  obtain ⟨d, hd⟩ := D.exists_cup_ne_zero_of_ne_zero V htor hxne
  refine ⟨d, ?_⟩
  rw [polar_comm, polar_Q0loc D q hq dat hdat ρ hρ hqG d x]
  have hnat := mapCoeff2_muTwo_cup q hq hqG x d
  intro h0
  apply hd
  have hz : mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology
      SectionSix.muTwoOfF2_equivariant
      (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) x d) = 0 := by
    apply D.inv.injective
    rw [map_zero]
    exact h0
  rwa [hnat] at hz

/-! ### The deep half `X₊` is a subgroup

`0 ∈ X₊` (witness `A = β = 1`; the zero class restricts to `0` on `ker ρ` since coboundaries die
there) and `X₊ + X₊ ⊆ X₊` (witness products: deep units are closed under multiplication, Kummer
cocycles are multiplicative on `ker ρ`-fixed squares, and `out(x+y) = out x + out y` up to a
coboundary that dies on `ker ρ`). -/
omit [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- `H¹` of an exponent-2 module has exponent 2. -/
theorem h1_add_self (hV2 : ∀ v : V, v + v = 0) (x : H1 AbsGalQ2 V) : x + x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      funext g
      exact hV2 _
    show H1mk AbsGalQ2 V z + H1mk AbsGalQ2 V z = 0
    rw [← map_add, hz, map_zero]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- A `Z¹`-cocycle whose class vanishes dies pointwise on `ker ρ` (the coboundary
`g ↦ g•w₀ − w₀` is trivial there since the action factors through `ρ`). -/
theorem vanish_on_ker_of_H1mk_eq_zero (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    {d : ↥(Z1 AbsGalQ2 V)} (hd : H1mk AbsGalQ2 V d = 0)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) : d.1 ↑n = 0 := by
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hd
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨w₀, hw₀⟩ := hmem
  have hn := congrFun hw₀ (↑n : AbsGalQ2)
  rw [← hn]
  show (↑n : AbsGalQ2) • w₀ - w₀ = 0
  rw [hρ, show ρ ↑n = 1 from n.2, one_smul, sub_self]

/-- The restricted Kummer cocycle of an `N`-fixed square is a hom on `N` (sign bookkeeping via
`two_values_of_fixed`). -/
theorem kummerRestrict_hom {N : Subgroup (Kummer.GaloisGroup ℚ_[2])}
    {A β : AlgebraicClosure ℚ_[2]}
    (hsq : β ^ 2 = A) (hβ0 : β ≠ 0) (hAfix : ∀ g ∈ N, g • A = A) (n m : ↥N) :
    Kummer.kummerCocycleFun β ((↑n : Kummer.GaloisGroup ℚ_[2]) * ↑m)
      = Kummer.kummerCocycleFun β ↑n + Kummer.kummerCocycleFun β ↑m := by
  have h2v : ∀ (g : ↥N), (↑g : Kummer.GaloisGroup ℚ_[2]) • β = β
      ∨ (↑g : Kummer.GaloisGroup ℚ_[2]) • β = -β := fun g =>
    two_values_of_fixed hsq (hAfix ↑g g.2)
  have heq1 : ∀ {g : Kummer.GaloisGroup ℚ_[2]}, g • β = -β →
      Kummer.kummerCocycleFun β g = 1 := fun {g} h =>
    if_neg (fun e => ne_neg_of_ne_zero hβ0 (e.symm.trans h))
  rcases h2v n with hg | hg <;> rcases h2v m with hh | hh
  · rw [Kummer.kummerCocycleFun_eq0 hg, Kummer.kummerCocycleFun_eq0 hh,
      Kummer.kummerCocycleFun_eq0 (by rw [mul_smul, hh, hg])]
    decide
  · rw [Kummer.kummerCocycleFun_eq0 hg, heq1 hh, heq1 (by rw [mul_smul, hh, smul_neg, hg])]
    decide
  · rw [heq1 hg, Kummer.kummerCocycleFun_eq0 hh, heq1 (by rw [mul_smul, hh, hg])]
    decide
  · rw [heq1 hg, heq1 hh,
      Kummer.kummerCocycleFun_eq0 (by rw [mul_smul, hh, smul_neg, hg, neg_neg])]
    decide

/-- The restricted Kummer cocycle of an `N`-fixed square lies in `Z¹(N, 𝔽₂)`. -/
theorem kummerRestrict_mem_Z1 {N : Subgroup (Kummer.GaloisGroup ℚ_[2])}
    {A β : AlgebraicClosure ℚ_[2]}
    (hsq : β ^ 2 = A) (hβ0 : β ≠ 0) (hAfix : ∀ g ∈ N, g • A = A) :
    (fun n : ↥N => Kummer.kummerCocycleFun β ↑n) ∈ Z1 ↥N (ZMod 2) := by
  refine mem_Z1_iff.mpr ⟨?_, fun n m => ?_⟩
  · exact (Kummer.kummerCocycleFun_continuous β).comp continuous_subtype_val
  · show Kummer.kummerCocycleFun β ↑(n * m)
      = Kummer.kummerCocycleFun β ↑n + n • Kummer.kummerCocycleFun β ↑m
    have htriv : n • Kummer.kummerCocycleFun β ↑m = Kummer.kummerCocycleFun β ↑m := rfl
    rw [htriv, show (↑(n * m) : Kummer.GaloisGroup ℚ_[2]) = ↑n * ↑m from rfl,
      kummerRestrict_hom hsq hβ0 hAfix n m]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- The `φ`-coordinate of a cocycle restricted to `ker ρ` lies in `Z¹(ker ρ, 𝔽₂)` (the action
is trivial there). -/
theorem phiRestrict_mem_Z1 (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (b : ↥(Z1 AbsGalQ2 V)) (φ : V →+ ZMod 2) :
    (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) => φ (b.1 ↑n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine mem_Z1_iff.mpr ⟨?_, fun n m => ?_⟩
  · exact (continuous_of_discreteTopology (f := fun v : V => φ v)).comp
      (hbc.comp continuous_subtype_val)
  · show φ (b.1 ↑(n * m)) = φ (b.1 ↑n) + n • φ (b.1 ↑m)
    have htriv : n • φ (b.1 ↑m) = φ (b.1 ↑m) := rfl
    rw [htriv, show (↑(n * m) : AbsGalQ2) = ↑n * ↑m from rfl, hb ↑n ↑m, hρ,
      show ρ ↑n = 1 from n.2, one_smul, map_add]

/-- `H1ofFun` is additive on actual cocycles. -/
theorem H1ofFun_add {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    {f g : G → ZMod 2} (hf : f ∈ Z1 G (ZMod 2)) (hg : g ∈ Z1 G (ZMod 2)) :
    H1ofFun G (f + g) = H1ofFun G f + H1ofFun G g := by
  rw [H1ofFun_of_mem (add_mem hf hg), H1ofFun_of_mem hf, H1ofFun_of_mem hg, ← map_add]
  rfl

/-- **The deep half `X₊` is an additive subgroup** of `H¹(G_ℚ₂, V)`. -/
noncomputable def deepPartSubgroup (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) : AddSubgroup (H1 AbsGalQ2 V) where
  carrier := deepPart (V := V) ρ
  zero_mem' := by
    intro φ
    refine ⟨1, 1, ?_, one_pow 2, one_ne_zero, ?_⟩
    · exact ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one],
        0, fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_lt_one⟩
    · congr 1
      funext n
      rw [Kummer.kummerCocycleFun_eq0 (by rw [AlgEquiv.smul_def, map_one])]
      have hv := vanish_on_ker_of_H1mk_eq_zero ρ hρ (H1mk_out (0 : H1 AbsGalQ2 V)) n
      rw [hv, map_zero]
  add_mem' := by
    intro x y hx hy φ
    obtain ⟨A₁, β₁, hd₁, hsq₁, hne₁, heq₁⟩ := hx φ
    obtain ⟨A₂, β₂, hd₂, hsq₂, hne₂, heq₂⟩ := hy φ
    obtain ⟨hA₁0, hA₁fix, b₁, hb₁fix, hA₁eq, hb₁⟩ := hd₁
    obtain ⟨hA₂0, hA₂fix, b₂, hb₂fix, hA₂eq, hb₂⟩ := hd₂
    have h2le : ‖(2 : AlgebraicClosure ℚ_[2])‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_natCast_le_one (AlgebraicClosure ℚ_[2]) 2
    refine ⟨A₁ * A₂, β₁ * β₂, ?_, by rw [mul_pow, hsq₁, hsq₂],
      mul_ne_zero hne₁ hne₂, ?_⟩
    · -- deep units are closed under products
      refine ⟨mul_ne_zero hA₁0 hA₂0, fun g hg => ?_, b₁ + b₂ + 2 * b₁ * b₂,
        fun g hg => ?_, by rw [hA₁eq, hA₂eq]; ring, ?_⟩
      · rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
          hA₁fix g hg, hA₂fix g hg]
      · rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
          ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hb₁fix g hg, hb₂fix g hg]
      · -- ‖b₁ + b₂ + 2b₁b₂‖ < 1 (ultrametric)
        have hprod : ‖(2 : AlgebraicClosure ℚ_[2]) * b₁ * b₂‖ < 1 := by
          rw [norm_mul, norm_mul]
          calc ‖(2 : AlgebraicClosure ℚ_[2])‖ * ‖b₁‖ * ‖b₂‖
              ≤ 1 * ‖b₁‖ * ‖b₂‖ := by
                have := mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right h2le (norm_nonneg b₁)) (norm_nonneg b₂)
                simpa using this
            _ = ‖b₁‖ * ‖b₂‖ := by ring
            _ ≤ ‖b₁‖ * 1 := mul_le_mul_of_nonneg_left hb₂.le (norm_nonneg b₁)
            _ = ‖b₁‖ := mul_one _
            _ < 1 := hb₁
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
        rw [max_lt_iff]
        refine ⟨lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_, hprod⟩
        rw [max_lt_iff]
        exact ⟨hb₁, hb₂⟩
    · -- the Kummer coordinate of the sum
      -- LHS: κ_{β₁β₂}|N = κ_{β₁}|N + κ_{β₂}|N
      have hLHS : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          Kummer.kummerCocycleFun (β₁ * β₂) (n : AbsGalQ2))
          = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₁ (n : AbsGalQ2))
            + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₂ (n : AbsGalQ2) := by
        funext n
        exact kcf_mul_of_fixed (by rw [mul_pow, hsq₁, hsq₂]) hsq₁ hsq₂ hne₁ hne₂
          (hA₁fix (n : AbsGalQ2) n.2) (hA₂fix (n : AbsGalQ2) n.2)
      -- RHS: φ∘out(x+y)|N = φ∘out x|N + φ∘out y|N
      have hRHS : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          φ ((Quotient.out (x + y)).1 (n : AbsGalQ2)))
          = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              φ ((Quotient.out x).1 (n : AbsGalQ2)))
            + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              φ ((Quotient.out y).1 (n : AbsGalQ2)) := by
        funext n
        have hd0 : H1mk AbsGalQ2 V
            (Quotient.out (x + y) - (Quotient.out x + Quotient.out y)) = 0 := by
          rw [map_sub, map_add, H1mk_out, H1mk_out, H1mk_out, sub_self]
        have hv := vanish_on_ker_of_H1mk_eq_zero ρ hρ hd0 n
        have hpt : (Quotient.out (x + y)).1 (n : AbsGalQ2)
            = (Quotient.out x).1 (n : AbsGalQ2) + (Quotient.out y).1 (n : AbsGalQ2) := by
          have hexp : (Quotient.out (x + y) - (Quotient.out x + Quotient.out y) :
              ↥(Z1 AbsGalQ2 V)).1 (n : AbsGalQ2)
              = (Quotient.out (x + y)).1 (n : AbsGalQ2)
                - ((Quotient.out x).1 (n : AbsGalQ2)
                    + (Quotient.out y).1 (n : AbsGalQ2)) := by
            show (Quotient.out (x + y)).1 (n : AbsGalQ2)
                - ((Quotient.out x).1 + (Quotient.out y).1) (n : AbsGalQ2) = _
            rw [Pi.add_apply]
          rw [hexp] at hv
          exact sub_eq_zero.mp hv
        show φ ((Quotient.out (x + y)).1 (n : AbsGalQ2)) = _
        rw [hpt, map_add]
        rfl
      have hadd₁ : H1ofFun (↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
          ((fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₁ (n : AbsGalQ2))
            + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₂ (n : AbsGalQ2))
          = H1ofFun (↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
              (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
                Kummer.kummerCocycleFun β₁ (n : AbsGalQ2))
            + H1ofFun (↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
              (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
                Kummer.kummerCocycleFun β₂ (n : AbsGalQ2)) :=
        H1ofFun_add (kummerRestrict_mem_Z1 hsq₁ hne₁ hA₁fix)
          (kummerRestrict_mem_Z1 hsq₂ hne₂ hA₂fix)
      rw [hLHS, hRHS, hadd₁,
        H1ofFun_add (phiRestrict_mem_Z1 ρ hρ _ φ) (phiRestrict_mem_Z1 ρ hρ _ φ),
        heq₁, heq₂]
  neg_mem' := by
    intro x hx
    have hneg : -x = x := neg_eq_of_add_eq_zero_left (h1_add_self hV2 x)
    rw [hneg]
    exact hx


/-! ### The dim clause and Prop 6.18 (ramified), reduced to the two Kummer cores -/


omit [Finite C] in
/-- **Prop 6.18 (eq. (115), ramified) from Lemma 6.17**: given the dim clause (`hdim`,
`#X₊² = #H¹`) and the vanishing clause (`hvanish`, `Q⁰_loc|X₊ = 0`), the zero-count of
`Q⁰_loc` is `2^{2m−1} + 2^{m−1}` — the positive Gauss sign, via the Lagrangian Arf package
(`arf_zero_of_card_sq`) and the Euler-characteristic count.  Ax: **B6** (via `D`), **B7**. -/
theorem card_Q0loc_zero_eq_of_dim_of_vanish (D : TateDuality 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ρ)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₀ : C) (hmoves : ∃ v : V, h₀ • v ≠ v)
    (hinv : ∀ (c : C) (v : V), q (c • v) = q v)
    (hV2 : ∀ v : V, v + v = 0)
    (hdim : Nat.card (deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V))
    (hvanish : ∀ x ∈ deepPart (V := V) ρ, Q0loc D dat ρ x = 0)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    Nat.card {x : H1 AbsGalQ2 V // Q0loc D dat ρ x = 0}
      = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  haveI : Finite (H1 AbsGalQ2 V) := finite_H1 V
  haveI : Fintype (H1 AbsGalQ2 V) := Fintype.ofFinite _
  have hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v := fun g v => by
    rw [hρ]; exact hinv _ v
  have hq' := isQuadraticFp2_Q0loc D q hq dat hdat ρ hρ hqG
  have hns' := nonsingular_Q0loc D q hq hns hV2 dat hdat ρ hρ hqG
  have h2H1 := h1_add_self (V := V) hV2
  have hH1card : Nat.card (H1 AbsGalQ2 V) = 2 ^ (2 * m) := by
    rw [card_H1_eq_card_of_simple V D ρ.toMonoidHom hρsurj hρ hsimple h₀ hmoves
      q hq hns hinv hV2, hcard]
  have harf : arf (Q0loc D dat ρ (V := V)) = 0 :=
    arf_zero_of_card_sq _ hq' h2H1 hns' (deepPartSubgroup ρ hρ hV2) hvanish hdim
  exact zeroCount_of_arf_zero (Q0loc D dat ρ) hq' hns' hm
    (by rw [← Nat.card_eq_fintype_card]; exact hH1card) harf

omit [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction AbsGalQ2 V]
  [ContinuousSMul AbsGalQ2 V] in
/-- The two-torsion subgroup of a `2^{2m}`-order simple module is everything: `V` has
exponent 2 (additive Cauchy + simplicity). -/
theorem exp_two_of_simple_of_card {C : Type*} [Group C] [DistribMulAction C V]
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) : ∀ v : V, v + v = 0 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  set T : AddSubgroup V :=
    { carrier := {v : V | v + v = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        show a + b + (a + b) = 0
        have h : a + b + (a + b) = (a + a) + (b + b) := by abel
        rw [h, ha, hb, add_zero]
      neg_mem' := fun {a} ha => by
        show -a + -a = 0
        have h : -a + -a = -(a + a) := by abel
        rw [h, ha, neg_zero] } with hT
  have hstable : ∀ (h : C), ∀ w ∈ T, h • w ∈ T := by
    intro h w hw
    show h • w + h • w = 0
    rw [← smul_add, hw, smul_zero]
  have hTne : T ≠ ⊥ := by
    have h2 : (2 : ℕ) ∣ Nat.card V := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    rw [Nat.card_eq_fintype_card] at h2
    obtain ⟨v, hv⟩ := exists_prime_addOrderOf_dvd_card 2 h2
    intro hbot
    have hvT : v ∈ T := by
      show v + v = 0
      have := addOrderOf_nsmul_eq_zero v
      rwa [hv, two_nsmul] at this
    rw [hbot, AddSubgroup.mem_bot] at hvT
    rw [hvT] at hv
    simp at hv
  have htop := (hsimple T hstable).resolve_left hTne
  exact fun v => (htop ▸ AddSubgroup.mem_top v : v ∈ T)

/- **Proposition 6.18 (dyadic base determinant theorem), ramified case** — re-homed to
`GQ2.DetRamified.prop_6_18_ramified` (P-15f8/f2d statement-move, 2026-07-08): now that both
Lemma-6.17 clauses are proved DOWNSTREAM (`ResidueLift.lemma_6_17_dim_final`,
`VanishClose.lemma_6_17_vanish_final`), `prop_6_18_ramified` — their sole consumer — moves below
them so it cites the real proofs (`card_Q0loc_zero_eq_of_dim_of_vanish` above is the banked
reduction it feeds).  This file (`DeepPart`) is upstream of the two proofs, hence the move; the
`(R, horient)` amendment travels with it. -/

end Q0locLayer
end GQ2.DeepPart
