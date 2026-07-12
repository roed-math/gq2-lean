import GQ2.KeystoneDelta

/-!
# P-16d6e4, layer (I): the generic `Z¹ → H¹` reduction of the source-Gauss sum

The `phase140_from_residues` residue `hGaussZ` is
`∑ᶠ c : VCocycle DD ρ', sign (QZero DD ρ' c) = #V · G0`.  This file reduces it — **generically
in `Γ`, source-free** — to a Gauss sum over the `#V`-sized quotient `Z¹ ⧸ B¹`, whose value is
the (83)-evaluation `G0` (P-16d6e4a).  Design record: `docs/p16d6e4-gauss-design.md` §2.

Contents:
* `iotaB_add_mem_B2` — `ι_Γ` absorbs a `B²`-shift (no `#H² = 2` needed);
* `graphPullback_shift_mem_B2` — the base determinant graph pullback is unchanged mod `B²`
  under a `vCob`-shift (the generic-`Γ` form of `RepIndependence.graphPullback_sub_mem_B2`,
  reusing its `innerConj` conjugation identity and `KeystoneDelta.graphCob_mem_B2` continuity);
* `QZero_add_vCob` — hence `Q⁰` is `B¹`-invariant;
* `vCobHom`/`vCobRange`, `hfix_of_simple` (the `V^{C₀} = 0` freeness), `QZeroBar`;
* `gaussZ_reduction` — `∑ᶠ c, sign(Q⁰ c) = #V · ∑ᶠ x : Z¹⧸B¹, sign(Q̄⁰ x)`, and
  `card_quotient_vCobRange` — `#(Z¹⧸B¹) = #V`.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh SectionSix

/-! ### Generic factor-set conjugation algebra (clean-context copies)

`RepIndependence`'s `kappa0_cocycle`/`etaS`/`innerConj` are stated in an `AbsGalQ2`-bound
section (their `C`/`W` carry `[TopologicalSpace]` and an `AbsGalQ2`-action), so they do not
apply to `DD.C0`/`DD.Vmod`.  These are the same identities in a clean generic context. -/

section FactorSetConj

variable {C : Type*} [Group C] {W : Type*} [AddCommGroup W] [DistribMulAction C W]

/-- **`κ⁰` is a 2-cocycle on `V ⋊ C`** (display (61)/Lemma 6.1, from the factor-set axioms). -/
theorem kappa0_cocycle {q : W → ZMod 2} {dat : FactorSet C W}
    (hdat : IsEquivariantFactorSet q dat) (a b c : SemiProd C W) :
    kappa0 dat a b + kappa0 dat (a * b) c = kappa0 dat a (b * c) + kappa0 dat b c := by
  obtain ⟨fcoc, _, _, _, _, mquad, mmul, _⟩ := hdat
  obtain ⟨v, cc⟩ := a; obtain ⟨w, d⟩ := b; obtain ⟨x, e⟩ := c
  simp only [kappa0, SemiProd.mul_def, smul_add, mul_smul]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    mmul cc d x + mquad cc w (d • x) + fcoc v (cc • w) (cc • (d • x))

/-- The inner-conjugation 1-cochain `η_s(x) = κ⁰(s, x) + κ⁰(sxs⁻¹, s)` on `V ⋊ C`. -/
def etaS (dat : FactorSet C W) (s x : SemiProd C W) : ZMod 2 :=
  kappa0 dat s x + kappa0 dat (s * x * s⁻¹) s

/-- **Inner automorphisms act trivially on `H²`**: `c_s^*κ⁰ − κ⁰ = δ¹(η_s)` pointwise. -/
theorem innerConj {q : W → ZMod 2} {dat : FactorSet C W}
    (hdat : IsEquivariantFactorSet q dat) (s x y : SemiProd C W) :
    etaS dat s y + etaS dat s (x * y) + etaS dat s x
      = kappa0 dat (s * x * s⁻¹) (s * y * s⁻¹) + kappa0 dat x y := by
  have A1 := kappa0_cocycle hdat s x y
  have A3 := kappa0_cocycle hdat (s * x * s⁻¹) s y
  have A2 := kappa0_cocycle hdat (s * x * s⁻¹) (s * y * s⁻¹) s
  rw [show s * x * s⁻¹ * s = s * x from by group] at A3
  rw [show s * x * s⁻¹ * (s * y * s⁻¹) = s * (x * y) * s⁻¹ from by group,
    show s * y * s⁻¹ * s = s * y from by group] at A2
  simp only [etaS]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) A1 + A2 + A3

end FactorSetConj

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

section GaussZ

variable {DD : DescData D}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- `ι_Γ` is invariant under adding a continuous coboundary (`B²` is its zero fibre). -/
theorem iotaB_add_mem_B2 {φ β : Γ × Γ → ZMod 2} (hβ : β ∈ B2 Γ (ZMod 2)) :
    iotaB (φ + β) = iotaB φ := by
  unfold iotaB
  by_cases h : φ ∈ B2 Γ (ZMod 2)
  · rw [if_pos h, if_pos (AddSubgroup.add_mem _ h hβ)]
  · rw [if_neg h, if_neg fun hc => h (by simpa using AddSubgroup.sub_mem _ hc hβ)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The base determinant graph pullback is `B¹`-shift-invariant mod `B²`** (generic-`Γ` form
of `RepIndependence.graphPullback_sub_mem_B2`): shifting the cocycle `c` by the principal
coboundary `vCob v` changes `(c, ρ')^* κ⁰` by the `(−v, 1)`-conjugation phase, a continuous
2-coboundary.  Reuses the generic `innerConj` identity and `graphCob_mem_B2`'s continuity. -/
theorem graphPullback_shift_mem_B2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (c : VCocycle DD ρ) (v : DD.Vmod) :
    graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c
        - graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c ∈ B2 Γ (ZMod 2) := by
  set s : SemiProd DD.C0 DD.Vmod := ((-v : DD.Vmod), (1 : DD.C0)) with hs
  set φ : Γ → SemiProd DD.C0 DD.Vmod := fun γ => (c.c γ, rho0 DD ρ γ) with hφ
  set u : DD.Vmod × DD.C0 → ZMod 2 := fun p => etaS DD.dat s p with hu
  -- the conjugation identity `s · (c γ, ρ'γ) · s⁻¹ = ((c + vCob v).c γ, ρ'γ)`
  have hconj : ∀ γ : Γ, s * φ γ * s⁻¹ = ((c + vCob DD ρ v).c γ, rho0 DD ρ γ) := by
    intro γ
    simp only [hs, hφ, SemiProd.mul_def, SemiProd.inv_def, one_smul, one_mul, mul_one,
      inv_one, neg_neg]
    show ((-v + c.c γ + rho0 DD ρ γ • v, rho0 DD ρ γ) : DD.Vmod × DD.C0)
      = (c.c γ + (rho0 DD ρ γ • v - v), rho0 DD ρ γ)
    rw [Prod.mk.injEq]
    exact ⟨by abel, rfl⟩
  -- graph multiplicativity `φ(γδ) = φ γ · φ δ`
  have hmul : ∀ γ δ : Γ, φ (γ * δ) = φ γ * φ δ := by
    intro γ δ
    simp only [hφ, SemiProd.mul_def]
    rw [c.crossed γ δ, map_mul (rho0 DD ρ) γ δ]
  -- pointwise: the shift-difference is the graph coboundary of `u`
  have hpt : graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c
        - graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c
      = fun p : Γ × Γ => u (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
          + u (c.c p.1, rho0 DD ρ p.1) + u (c.c p.2, rho0 DD ρ p.2) := by
    funext p
    obtain ⟨g, h⟩ := p
    have hgpS : graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c (g, h)
        = kappa0 DD.dat (s * φ g * s⁻¹) (s * φ h * s⁻¹) := by
      rw [hconj g, hconj h]; rfl
    have hgpC : graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c (g, h)
        = kappa0 DD.dat (φ g) (φ h) := rfl
    have hIC := innerConj DD.hdat s (φ g) (φ h)
    rw [← hmul g h] at hIC
    show graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c (g, h)
        - graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c (g, h)
      = etaS DD.dat s (φ (g * h)) + etaS DD.dat s (φ g) + etaS DD.dat s (φ h)
    rw [hgpS, hgpC]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hIC
  rw [hpt]
  exact graphCob_mem_B2 htriv u c

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **`Q⁰` is `B¹`-invariant**: the base determinant form is unchanged by a `vCob`-shift. -/
theorem QZero_add_vCob (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (c : VCocycle DD ρ) (v : DD.Vmod) :
    QZero DD ρ (c + vCob DD ρ v) = QZero DD ρ c := by
  have hmem := graphPullback_shift_mem_B2 htriv c v
  have hsplit : graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c
      = graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c
        + (graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c
            - graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c) := by abel
  show iotaB (graphPullback DD.dat (fun γ => rho0 DD ρ γ) (c + vCob DD ρ v).c)
    = iotaB (graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c)
  rw [hsplit, iotaB_add_mem_B2 hmem]

/-! ### The `B¹ ≅ V` translation group and the freeness criterion -/

variable (DD ρ) in
/-- The principal-coboundary hom `V →+ Z¹_{Γ,ρ}(V)` (its image is `B¹`). -/
noncomputable def vCobHom : DD.Vmod →+ VCocycle DD ρ :=
  AddMonoidHom.mk' (vCob DD ρ) vCob_add

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
@[simp] theorem vCobHom_apply (v : DD.Vmod) : vCobHom DD ρ v = vCob DD ρ v := rfl

variable (DD ρ) in
/-- `B¹_{Γ,ρ}(V) ≤ Z¹_{Γ,ρ}(V)` as the range of the coboundary hom. -/
noncomputable def vCobRange : AddSubgroup (VCocycle DD ρ) := (vCobHom DD ρ).range

omit [DiscreteTopology Bg] [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] in
/-- **The `V^{C₀} = 0` freeness** (design §2 item 4): for a faithful simple `C₀`-module `V`
with `C₀` nontrivial and `ρ'` surjective, the only `ρ'`-fixed vector is `0`.  Discharges the
`hfix` hypothesis of `vCob_injective` from the block's chief-factor data. -/
theorem hfix_of_simple [Nontrivial DD.C0]
    (hsurj : Function.Surjective (fun γ : Γ => rho0 DD ρ γ))
    (hsimple : ∀ W : AddSubgroup DD.Vmod, (∀ (g : DD.C0), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hfaith : ∀ g : DD.C0, (∀ v : DD.Vmod, g • v = v) → g = 1)
    (v : DD.Vmod) (hv : ∀ γ : Γ, rho0 DD ρ γ • v = v) : v = 0 := by
  -- `v` is fixed by all of `C₀` (surjectivity of `ρ'`)
  have hvC : ∀ cc : DD.C0, cc • v = v := fun cc =>
    (hsurj cc).elim fun γ hγ => hγ ▸ hv γ
  -- the fixed submodule
  let W : AddSubgroup DD.Vmod :=
    { carrier := {w | ∀ cc : DD.C0, cc • w = w}
      zero_mem' := fun cc => smul_zero cc
      add_mem' := fun {a b} ha hb cc => by rw [smul_add, ha cc, hb cc]
      neg_mem' := fun {a} ha cc => by rw [smul_neg, ha cc] }
  have hWinv : ∀ (g : DD.C0), ∀ w ∈ W, g • w ∈ W := fun g w hw cc => by
    rw [hw g, hw cc]
  rcases hsimple W hWinv with hbot | htop
  · have : v ∈ W := hvC
    rwa [hbot, AddSubgroup.mem_bot] at this
  · -- `W = ⊤` ⟹ every `cc` acts trivially ⟹ `C₀` trivial, contradicting `Nontrivial`
    exfalso
    obtain ⟨a, b, hab⟩ := (Nontrivial.exists_pair_ne (α := DD.C0))
    apply hab
    have hall : ∀ (cc : DD.C0) (w : DD.Vmod), cc • w = w := by
      intro cc w
      have hwW : w ∈ W := by rw [htop]; exact AddSubgroup.mem_top w
      exact hwW cc
    rw [hfaith a (hall a), hfaith b (hall b)]

/-! ### The descended Gauss form and the reduction -/

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- `vCob` is injective when `V` carries no nonzero `ρ'`-fixed vector, hence the coboundary
hom is injective (`|B¹| = #V`). -/
theorem vCobHom_injective (hfix : ∀ v : DD.Vmod, (∀ γ : Γ, rho0 DD ρ γ • v = v) → v = 0) :
    Function.Injective (vCobHom DD ρ) := vCob_injective hfix

variable (DD ρ) in
/-- **The descended base determinant form `Q̄⁰`** on the `#V`-sized quotient `Z¹ ⧸ B¹`
(design §2 item 5): `Q⁰` descends because it is `B¹`-invariant (`QZero_add_vCob`).  Its Gauss
sum is the (83)-value `G0` (P-16d6e4a). -/
noncomputable def QZeroBar (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (x : VCocycle DD ρ ⧸ vCobRange DD ρ) : ZMod 2 :=
  Quotient.liftOn' x (QZero DD ρ) fun a b hab => by
    rw [QuotientAddGroup.leftRel_apply] at hab
    obtain ⟨w, hw⟩ := hab
    rw [vCobHom_apply] at hw
    rw [show b = a + vCob DD ρ w by rw [hw]; abel, QZero_add_vCob htriv a w]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
@[simp] theorem QZeroBar_mk (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (c : VCocycle DD ρ) :
    QZeroBar DD ρ htriv (QuotientAddGroup.mk c) = QZero DD ρ c := rfl

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The generic `Z¹ → H¹` reduction** (design §2 item 5): the source-Gauss sum over all of
`Z¹_{Γ,ρ}(V)` is `#V` times the Gauss sum of the descended form `Q̄⁰` on `Z¹ ⧸ B¹`.  The free
`B¹`-translation (`vCob` injective) makes every fibre of `Z¹ ↠ Z¹⧸B¹` a `#V`-sized coset on
which `Q⁰` is constant.  Finiteness of `Z¹` is a hypothesis — supply `finite_vcocycle` (a
splitting + t.f.g.) or, σ-free, a nonzero `Nat.card`-count such as `hZcard_local`
(P-16d6e4a composition). -/
theorem gaussZ_reduction [Finite (VCocycle DD ρ)]
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfix : ∀ v : DD.Vmod, (∀ γ : Γ, rho0 DD ρ γ • v = v) → v = 0) :
    ∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c)
      = (Nat.card DD.Vmod : ℤ)
          * ∑ᶠ x : (VCocycle DD ρ ⧸ vCobRange DD ρ), sign (QZeroBar DD ρ htriv x) := by
  classical
  haveI : Fintype (VCocycle DD ρ) := Fintype.ofFinite _
  haveI : Fintype (VCocycle DD ρ ⧸ vCobRange DD ρ) := Fintype.ofFinite _
  haveI : Fintype DD.Vmod := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  set π : VCocycle DD ρ → VCocycle DD ρ ⧸ vCobRange DD ρ :=
    fun c => QuotientAddGroup.mk c with hπ
  have hinj : Function.Injective (vCobHom DD ρ) := vCobHom_injective hfix
  -- every fibre of `π` has `#V` elements
  have hfib : ∀ q : VCocycle DD ρ ⧸ vCobRange DD ρ,
      (Finset.univ.filter (fun c => π c = q)).card = Nat.card DD.Vmod := by
    intro q
    obtain ⟨c₀, hc₀⟩ := QuotientAddGroup.mk_surjective q
    have hbij : Function.Bijective
        (fun z : ↥(vCobRange DD ρ) => (⟨(c₀ + z), by
          show (↑(c₀ + (z : VCocycle DD ρ)) : VCocycle DD ρ ⧸ vCobRange DD ρ) = q
          rw [← hc₀, QuotientAddGroup.eq_iff_sub_mem, add_sub_cancel_left]
          exact z.2⟩ : {c // π c = q})) := by
      constructor
      · intro z₁ z₂ hz
        exact Subtype.ext (add_left_cancel (Subtype.ext_iff.mp hz))
      · rintro ⟨c, hc⟩
        have h1 : (↑c : VCocycle DD ρ ⧸ vCobRange DD ρ) = ↑c₀ := hc.trans hc₀.symm
        refine ⟨⟨c - c₀, (QuotientAddGroup.eq_iff_sub_mem).mp h1⟩, ?_⟩
        exact Subtype.ext (by show c₀ + (c - c₀) = c; abel)
    have hcard : Nat.card {c : VCocycle DD ρ // π c = q} = Nat.card DD.Vmod := by
      rw [← Nat.card_eq_of_bijective _ hbij]
      exact (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- group the sum by fibre
  have hstep : (∑ c, sign (QZero DD ρ c)) = ∑ c, sign (QZeroBar DD ρ htriv (π c)) :=
    Finset.sum_congr rfl fun c _ => by rw [hπ, QZeroBar_mk]
  rw [hstep, Finset.sum_comp (fun q => sign (QZeroBar DD ρ htriv q)) π]
  have huniv : Finset.univ.image π = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective q
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hc⟩
  rw [huniv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hfib q, nsmul_eq_mul]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **The `H¹`-model is `#V`-sized** (design §2 item 6): `#(Z¹ ⧸ B¹) = #V`, from `#B¹ = #V`
(free translation) and `#Z¹ = #V²` (`hZcard`, the source's 5.15/5.16 numerics).  Lets
P-16d6e4a exhibit the descended form as a form on a `#V`-space. -/
theorem card_quotient_vCobRange
    (hfix : ∀ v : DD.Vmod, (∀ γ : Γ, rho0 DD ρ γ • v = v) → v = 0)
    (hZcard : Nat.card (VCocycle DD ρ) = Nat.card DD.Vmod * Nat.card DD.Vmod) :
    Nat.card (VCocycle DD ρ ⧸ vCobRange DD ρ) = Nat.card DD.Vmod := by
  have hrange : Nat.card ↥(vCobRange DD ρ) = Nat.card DD.Vmod :=
    (Nat.card_congr (AddMonoidHom.ofInjective (vCobHom_injective hfix)).toEquiv).symm
  have hlag : Nat.card (VCocycle DD ρ)
      = Nat.card (VCocycle DD ρ ⧸ vCobRange DD ρ) * Nat.card ↥(vCobRange DD ρ) := by
    rw [← (vCobRange DD ρ).index_mul_card, (vCobRange DD ρ).index_eq_card]
  rw [hrange, hZcard] at hlag
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hlag).symm

end GaussZ

end AffineTLift

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
-/
