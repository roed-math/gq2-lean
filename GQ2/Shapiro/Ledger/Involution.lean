/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Shapiro.Ledger.Free

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The involution-orbit Shapiro ledger

The compatible transversal, position identity, and final involution coboundary chain.

See `GQ2.Shapiro.Ledger` for the paper-facing overview, source citations, and deviations.
-/

open scoped Pointwise

namespace GQ2

open ContCoh Corestriction

namespace ShapiroLedger

private theorem lWordT_mem {G : Type*} [Group G] (U : Subgroup G)
    (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (v : G ⧸ U) (γ : G) : lWordT U T v γ ∈ U := by
  have h1 : ((T (γ⁻¹ • v) : G) : G ⧸ U) = γ⁻¹ • v := hT _
  have h2 : ((γ⁻¹ * T v : G) : G ⧸ U) = γ⁻¹ • v := by
    conv_rhs => rw [← hT v]
    exact MulAction.Quotient.smul_mk U γ⁻¹ (T v)
  have h4 : (γ⁻¹ * T v)⁻¹ * T (γ⁻¹ • v) = lWordT U T v γ := by
    rw [lWordT]; group
  exact h4 ▸ (QuotientGroup.eq (s := U)).mp (h2.trans h1.symm)

/-! ## Lemma 6.15, involution orbits (105) — foundations

The involution case compares `graphPullback(invOrbitDatum_{N,ḡ})` with `cor_{U₀→G}` of the
two-point Evens cocycle `evensNormFun_{N≤U₀}` (paper (107)–(109)), where `U₀ = ⟨N, ĝ⟩` is the
index-2-over-`N` subgroup (fixed field `K₀ = K^{⟨ḡ⟩}`) and `ḡ = mk ĝ` is an involution of
`G/N`.  These are the setup lemmas: `ḡ` is an involution, `G/U₀` is finite, and the two
index sets `G/U₀` and `(G/N)/⟨ḡ⟩` correspond (`U₀` maps onto `⟨ḡ⟩` under `G ↠ G/N`). -/

section Involution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable (N : Subgroup G) [N.Normal]


omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] in
/-- `ḡ = mk ĝ` is an involution of `G/N` when `ĝ² ∈ N`. -/
theorem ghatQuot_sq (ghat : G) (hg2 : ghat * ghat ∈ N) :
    (QuotientGroup.mk' N ghat) * (QuotientGroup.mk' N ghat) = 1 := by
  rwa [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] in
/-- The image of `U₀ = ⟨N, ĝ⟩` under `G ↠ G/N` is `⟨ḡ⟩` (`N` dies, `ĝ ↦ ḡ`). -/
theorem map_U0_eq_zpowers (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    U₀.map (QuotientGroup.mk' N) = Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
  rw [hU₀, Subgroup.map_sup, MonoidHom.map_zpowers,
    (Subgroup.map_eq_bot_iff N).mpr (QuotientGroup.ker_mk' N).ge, bot_sup_eq]

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [N.Normal] in
/-- `G/U₀` is finite (`U₀ ⊇ N` has index dividing the finite `N.index`). -/
theorem finite_quot_U0 [Finite (G ⧸ N)] (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) : Finite (G ⧸ U₀) := by
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : U₀.FiniteIndex := Subgroup.finiteIndex_of_le (hU₀ ▸ le_sup_left)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The index correspondence** `G/U₀ ≃ (G/N)/⟨ḡ⟩`: both are the coset space of the
index-2-over-`N` subgroup `U₀ = ⟨N, ĝ⟩` (whose image in `G/N` is `⟨ḡ⟩`).  This bijects the two
orbit index sets of the involution comparison. -/
def invIndexEquiv (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    (G ⧸ U₀) ≃ ((G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)) where
  toFun := Quotient.lift (fun g : G => (QuotientGroup.mk (QuotientGroup.mk g)))
    (fun a b hab => Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
      have hm : (QuotientGroup.mk' N a)⁻¹ * QuotientGroup.mk' N b
          ∈ U₀.map (QuotientGroup.mk' N) := by
        rw [← map_inv, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (QuotientGroup.leftRel_apply.mp hab)
      rwa [map_U0_eq_zpowers N ghat U₀ hU₀] at hm)))
  invFun := Quotient.lift
    (Quotient.lift (fun g : G => (QuotientGroup.mk g : G ⧸ U₀))
      (fun a b hab => Quotient.sound (QuotientGroup.leftRel_apply.mpr
        ((hU₀ ▸ le_sup_left : N ≤ U₀) (QuotientGroup.leftRel_apply.mp hab)))))
    (Quotient.ind fun a => Quotient.ind fun b => fun hxy =>
      Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
        have hxy' : (QuotientGroup.mk' N a)⁻¹ * QuotientGroup.mk' N b
            ∈ Subgroup.zpowers (QuotientGroup.mk' N ghat) := QuotientGroup.leftRel_apply.mp hxy
        rw [← map_inv, ← map_mul, ← map_U0_eq_zpowers N ghat U₀ hU₀, Subgroup.mem_map] at hxy'
        obtain ⟨u, hu, hue⟩ := hxy'
        have hn : u⁻¹ * (a⁻¹ * b) ∈ N := QuotientGroup.eq.mp (by
          rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]; exact hue)
        have hrw : a⁻¹ * b = u * (u⁻¹ * (a⁻¹ * b)) := by group
        rw [hrw]
        exact mul_mem hu ((hU₀ ▸ le_sup_left : N ≤ U₀) hn))))
  left_inv := Quotient.ind fun _ => rfl
  right_inv := Quotient.ind fun y => QuotientGroup.induction_on y fun _ => rfl

variable [Finite (G ⧸ N)]

/-- The `⟨ḡ⟩`-orbit canonical representative of a `G/N`-element `z`. -/
noncomputable def orbOut (ghat : G) (z : G ⧸ N) : G ⧸ N :=
  ((z : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)).out)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
open scoped Classical in
/-- The involution graph pullback, unfolded to the two explicit sums of paper eq. (107)
(the oriented factor-set term + the orientation-reversal correction). -/
theorem phi_inv_eq (α : Z1 N (ZMod 2)) (ghat : G) (γ η : G) :
    graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat)) (QuotientGroup.mk' N)
        (shapiroFun N α.1) (γ, η)
      = (∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
          α.1 (lTrans N u.out γ)
            * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹ * (u.out * QuotientGroup.mk' N ghat)) η))
        + ∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
            (if (QuotientGroup.mk' N γ)⁻¹ * u.out
                  = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out) then 0 else 1)
              * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out)) η)
                * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out)
                    * QuotientGroup.mk' N ghat) η)) := rfl


omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `ḡ = mk ĝ` has order exactly 2 in `G/N` (`ĝ ∉ N`, `ĝ² ∈ N`). -/
theorem orderOf_ghatQuot (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N) :
    orderOf (QuotientGroup.mk' N ghat) = 2 := by
  have hne : QuotientGroup.mk' N ghat ≠ 1 := by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact hg
  exact orderOf_eq_prime (by rw [sq]; exact ghatQuot_sq N ghat hg2) hne

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `N` has index 2 in `U₀ = ⟨N, ĝ⟩`: the map `U₀ → G/N` has kernel `N.subgroupOf U₀` and
range `⟨ḡ⟩` (order 2), so `U₀/(N.subgroupOf U₀) ≅ ⟨ḡ⟩`. -/
theorem subgroupOf_index_two (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    (N.subgroupOf U₀).index = 2 := by
  set f : U₀ →* G ⧸ N := (QuotientGroup.mk' N).comp U₀.subtype with hf
  have hker : f.ker = N.subgroupOf U₀ := by
    ext u
    simp only [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
  have hrange : f.range = Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
    rw [hf, MonoidHom.range_comp, Subgroup.subtype_range, map_U0_eq_zpowers N ghat U₀ hU₀]
  have hcard : Nat.card (U₀ ⧸ N.subgroupOf U₀) = 2 := by
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange,
      Nat.card_zpowers, orderOf_ghatQuot N ghat hg hg2]
  rw [Subgroup.index, hcard]

/-! ### Involution assembly — setup -/
omit [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  [N.Normal] [Finite (G ⧸ N)] in
/-- `N.subgroupOf U₀` is open in `U₀` (preimage of the open `N` under `U₀ ↪ G`). -/
theorem subgroupOf_isOpen (hNo : IsOpen (N : Set G)) (U₀ : Subgroup G) :
    IsOpen ((N.subgroupOf U₀ : Subgroup U₀) : Set U₀) := by
  rw [Subgroup.coe_subgroupOf]
  exact hNo.preimage continuous_subtype_val

/-- The restriction of `α` to `N.subgroupOf U₀` (reading `α` at the underlying `N`-element). -/
noncomputable def alphaOn (α : Z1 N (ZMod 2)) (U₀ : Subgroup G) :
    (N.subgroupOf U₀) → ZMod 2 := fun u ↦ α.1 ⟨u.1.1, u.2⟩

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
/-- `alphaOn` is additive (inherited from `α`, a hom on `N`). -/
theorem alphaOn_hom (α : Z1 N (ZMod 2)) (U₀ : Subgroup G)
    (x y : N.subgroupOf U₀) : alphaOn N α U₀ (x * y) = alphaOn N α U₀ x + alphaOn N α U₀ y :=
  z1_mul N α ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
/-- `alphaOn` is continuous. -/
theorem alphaOn_continuous (α : Z1 N (ZMod 2)) (U₀ : Subgroup G) :
    Continuous (alphaOn N α U₀) := by
  have hα : Continuous α.1 := (mem_Z1_iff.mp α.2).1
  exact hα.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)


/-! ### Step 2 — the Evens-norm building blocks as explicit `α`-values

`evensAux`/`bS` on `U₀` (relative to `N.subgroupOf U₀`, shift `ĝ`) read `α` at the underlying
`N`-element, using the index-2 side bookkeeping (`ĝ ∉ N`; `x·ĝ ∈ N ⟺ x ∉ N`). -/
omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
private theorem evensAux_alphaOn_mem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (x : U₀) (hx : (x : G) ∈ N) :
    evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) x = α.1 ⟨(x : G), hx⟩ :=
  evensAux_of_mem (alphaOn N α U₀) (Subgroup.mem_subgroupOf.mpr hx)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
private theorem evensAux_alphaOn_notMem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (x : U₀) (hx : (x : G) ∉ N) (hmem : (x : G) * ghat ∈ N) :
    evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) x = α.1 ⟨(x : G) * ghat, hmem⟩ :=
  evensAux_of_notMem hUi hs (alphaOn N α U₀) (fun h => hx (Subgroup.mem_subgroupOf.mp h))

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
private theorem bS_alphaOn_mem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (y : U₀) (hy : (y : G) ∈ N) (hmem : ghat⁻¹ * (y : G) * ghat ∈ N) :
    bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) y = α.1 ⟨ghat⁻¹ * (y : G) * ghat, hmem⟩ :=
  bS_of_mem hUi hs (alphaOn N α U₀) (Subgroup.mem_subgroupOf.mpr hy)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
private theorem bS_alphaOn_notMem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (y : U₀) (hy : (y : G) ∉ N) (hmem : ghat⁻¹ * (y : G) ∈ N) :
    bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) y = α.1 ⟨ghat⁻¹ * (y : G), hmem⟩ :=
  bS_of_notMem hUi hs (alphaOn N α U₀) (fun h => hy (Subgroup.mem_subgroupOf.mp h))

/-! ### Step 3 — the transversal reconciliation

Both sides are now sums over `O = (G/N)/⟨ḡ⟩` (`phi_inv_eq`, `psi_inv_reindex`).  The pieces below
bridge the `U₀`-transversal words (`ℓ^{U₀}`, used by `psi`) and the `N`-transversal words (`ℓ^N`,
used by `phi`), and the orientation. -/
omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **Orbit equivariance**: the `⟨ḡ⟩`-orbit of `mk((γ⁻¹•v).out)` equals that of `γ̄⁻¹·mk(v.out)`
(both are `N`-images of `U₀`-lifts of `γ⁻¹•v`). -/
theorem orbit_equiv (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (v : G ⧸ U₀) (γ : G) :
    (QuotientGroup.mk (QuotientGroup.mk' N ((γ⁻¹ • v).out)) :
        (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat))
      = QuotientGroup.mk ((QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N (v.out : G)) := by
  rw [QuotientGroup.eq, ← map_U0_eq_zpowers N ghat U₀ hU₀, Subgroup.mem_map]
  refine ⟨(γ⁻¹ • v).out⁻¹ * (γ⁻¹ * (v.out : G)), ?_, ?_⟩
  · have h1 : ((( γ⁻¹ • v).out : G) : G ⧸ U₀) = γ⁻¹ • v := QuotientGroup.out_eq' _
    have h2 : ((γ⁻¹ * (v.out : G)) : G ⧸ U₀) = γ⁻¹ • v := by
      conv_rhs => rw [← QuotientGroup.out_eq' v]
      exact MulAction.Quotient.smul_mk U₀ γ⁻¹ v.out
    exact (QuotientGroup.eq (s := U₀)).mp (h1.trans h2.symm)
  · rw [map_mul, map_mul, map_inv, map_inv]

/-- In `⟨g⟩` with `g² = 1`, every element is `1` or `g`. -/
theorem mem_zpowers_sq_one {H : Type*} [Group H] {g t : H} (hg2 : g * g = 1)
    (ht : t ∈ Subgroup.zpowers g) : t = 1 ∨ t = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hsq : g ^ (2 : ℤ) = 1 := (zpow_two g).trans hg2
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left; rw [← two_mul, zpow_mul, hsq, one_zpow]
  · right; rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]


omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `.out` shift: `(k·ḡ).out = k.out · ĝ · shiftCorr(k)` (rearranged `shiftCorr`). -/
theorem out_ghat_shift (ghat : G) (k : G ⧸ N) :
    (k * (ghat : G ⧸ N)).out = k.out * ghat * shiftCorr N ghat k := by
  rw [shiftCorr]; group


/-! ### The compatible transversal `invLift` (Step 2)

`invLift v := ((invIndexEquiv v).out).out` lifts each `U₀`-coset through the orbit-canonical
`G/N`-base point `z_u` — the same base point `phi_inv_eq` reads.  Along it the `ℓ^T`-words are
based exactly at `phi`'s indices and the aligned/flipped discriminant is literally `phi`'s
`ε`-condition. -/
omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `invIndexEquiv` computes on `mk`-classes (definitional). -/
theorem invIndexEquiv_mk (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (g : G) :
    invIndexEquiv N ghat U₀ hU₀ ((g : G ⧸ U₀))
      = (QuotientGroup.mk (QuotientGroup.mk g : G ⧸ N) :
          (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)) := rfl

/-- The **compatible transversal**: lift each `U₀`-coset through the orbit-canonical
`G/N`-representative. -/
noncomputable def invLift (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) : G ⧸ U₀ → G :=
  fun v => (((invIndexEquiv N ghat U₀ hU₀ v).out : G ⧸ N).out : G)

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `G/N`-image of `invLift v` is the orbit-canonical base point `z_u`. -/
theorem mk_invLift (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (v : G ⧸ U₀) :
    (QuotientGroup.mk (invLift N ghat U₀ hU₀ v) : G ⧸ N)
      = (invIndexEquiv N ghat U₀ hU₀ v).out :=
  QuotientGroup.out_eq' _

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `invLift` is a genuine transversal: it lifts `v` to `v`. -/
theorem invLift_spec (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (v : G ⧸ U₀) :
    ((invLift N ghat U₀ hU₀ v : G) : G ⧸ U₀) = v := by
  apply (invIndexEquiv N ghat U₀ hU₀).injective
  rw [invIndexEquiv_mk, mk_invLift]
  exact QuotientGroup.out_eq' _

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `γ`-shifted index in orbit form: `invIndexEquiv (γ⁻¹ • v) = mk_O (γ̄⁻¹ · z_u)`. -/
theorem invIndexEquiv_smul (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G) :
    invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)
      = (QuotientGroup.mk ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out) :
          (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)) := by
  have h1 : invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)
      = QuotientGroup.mk (QuotientGroup.mk' N ((γ⁻¹ • v).out)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' (γ⁻¹ • v)]
    rfl
  rw [h1, orbit_equiv N ghat U₀ hU₀ v γ]
  -- replace `mk_N (v.out)` by the orbit-canonical `z_u` (same `⟨ḡ⟩`-orbit)
  rw [QuotientGroup.eq]
  have horb : (QuotientGroup.mk (QuotientGroup.mk' N (v.out : G)) :
        (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat))
      = QuotientGroup.mk ((invIndexEquiv N ghat U₀ hU₀ v).out) := by
    have h2 : invIndexEquiv N ghat U₀ hU₀ v
        = QuotientGroup.mk (QuotientGroup.mk' N (v.out : G)) := by
      conv_lhs => rw [← QuotientGroup.out_eq' v]
      rfl
    rw [← h2, QuotientGroup.out_eq']
  have hmem : (QuotientGroup.mk' N (v.out : G))⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out
      ∈ Subgroup.zpowers (QuotientGroup.mk' N ghat) := QuotientGroup.eq.mp horb
  have hrw : ((QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N (v.out : G))⁻¹
      * ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out)
      = (QuotientGroup.mk' N (v.out : G))⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out := by
    group
  rw [hrw]
  exact hmem

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `γ`-shifted base point is the orbit-canonical rep of `γ̄⁻¹ · z_u`. -/
theorem invIndexEquiv_smul_out (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G) :
    (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out) := by
  rw [orbOut, invIndexEquiv_smul N ghat U₀ hU₀ v γ]

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `G/N`-image of the compatible-transversal word: `z_u⁻¹ · γ̄ · z_{u'}`. -/
theorem mk_lWordT_invLift (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G) :
    (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v γ) : G ⧸ N)
      = ((invIndexEquiv N ghat U₀ hU₀ v).out)⁻¹ * (QuotientGroup.mk' N γ)
        * ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out) := by
  show QuotientGroup.mk' N (lWordT U₀ (invLift N ghat U₀ hU₀) v γ) = _
  simp only [lWordT, map_mul, map_inv]
  rw [show QuotientGroup.mk' N (invLift N ghat U₀ hU₀ v)
        = (invIndexEquiv N ghat U₀ hU₀ v).out from mk_invLift N ghat U₀ hU₀ v,
    show QuotientGroup.mk' N (invLift N ghat U₀ hU₀ (γ⁻¹ • v))
        = (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out from mk_invLift N ghat U₀ hU₀ (γ⁻¹ • v)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **Alignment discriminant**: the compatible-transversal word lies in `N` iff `γ̄⁻¹ · z_u` is
its own orbit-canonical rep — literally `phi_inv_eq`'s `ε`-condition. -/
theorem lWordT_invLift_mem_N_iff (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G) :
    lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N
      ↔ (QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out
          = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out) := by
  rw [← QuotientGroup.eq_one_iff (lWordT U₀ (invLift N ghat U₀ hU₀) v γ),
    mk_lWordT_invLift N ghat U₀ hU₀ v γ, invIndexEquiv_smul_out N ghat U₀ hU₀ v γ,
    mul_eq_one_iff_inv_eq, mul_inv_rev, inv_inv]

/-! ### Word identities and α-reads along `invLift` (Step 3)

On the compatible transversal the aligned reads are **on the nose** and every flipped or
`bS`-read carries only `shiftCorr`-corrections, collapsed to the single correction read
`dRead` via the duality `sc(m·ḡ) = (ĝ·sc(m)·ĝ)⁻¹`. -/
omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **Aligned `z'`-characterization**: if the compatible word lies in `N`, the shifted base
point is the plain `γ`-shift of the base point. -/
theorem invIndexEquiv_out_aligned (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G)
    (hx : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N) :
    (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out) := by
  have h1 : (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v γ) : G ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hx
  rw [mk_lWordT_invLift N ghat U₀ hU₀ v γ] at h1
  have h2 : (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = (QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out) := by
    rw [← mul_eq_one_iff_inv_eq.mp h1]
    group
  rw [h2, quot_smul_eq_mk_mul]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **Flipped `z'`-characterization**: if the compatible word is not in `N`, the shifted base
point is the `γ`-shift times `ḡ`. -/
theorem invIndexEquiv_out_flipped (ghat : G) (_ : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G)
    (hx : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∉ N) :
    (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * (QuotientGroup.mk' N ghat) := by
  -- the word's image lies in `map U₀ = ⟨ḡ⟩` and is `≠ 1`, hence `= ḡ`
  have hmemU : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ U₀ :=
    lWordT_mem U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ
  have himg : (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v γ) : G ⧸ N)
      ∈ Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
    rw [← map_U0_eq_zpowers N ghat U₀ hU₀]
    exact Subgroup.mem_map.mpr ⟨_, hmemU, rfl⟩
  have hne1 : (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v γ) : G ⧸ N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hx
  have heq : (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v γ) : G ⧸ N)
      = QuotientGroup.mk' N ghat :=
    (mem_zpowers_sq_one (ghatQuot_sq N ghat hg2) himg).resolve_left hne1
  rw [mk_lWordT_invLift N ghat U₀ hU₀ v γ] at heq
  have h2 : (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = (QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)
          * QuotientGroup.mk' N ghat :=
    calc (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
        = ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out)
            * (((invIndexEquiv N ghat U₀ hU₀ v).out)⁻¹ * (QuotientGroup.mk' N γ)
              * ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out)) := by group
      _ = _ := by rw [heq]
  rw [h2, quot_smul_eq_mk_mul]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **W1 (aligned word identity)**: on the aligned locus the compatible word IS the canonical
`N`-transversal word at the base point — on the nose. -/
theorem lWordT_invLift_aligned (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G)
    (hx : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N) :
    lWordT U₀ (invLift N ghat U₀ hU₀) v γ
      = lWord N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ := by
  have hz' := invIndexEquiv_out_aligned N ghat U₀ hU₀ v γ hx
  show (invLift N ghat U₀ hU₀ v)⁻¹ * γ * invLift N ghat U₀ hU₀ (γ⁻¹ • v) = _
  rw [lWord]
  show _ = ((invIndexEquiv N ghat U₀ hU₀ v).out).out⁻¹ * γ
      * ((γ⁻¹ • (invIndexEquiv N ghat U₀ hU₀ v).out).out)
  rw [invLift, invLift, hz']

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **W2 (flipped word identity)**: on the flipped locus the compatible word is the canonical
word times `ĝ` times a `shiftCorr` correction. -/
theorem lWordT_invLift_flipped (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G)
    (hx : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∉ N) :
    lWordT U₀ (invLift N ghat U₀ hU₀) v γ
      = lWord N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ * ghat
        * shiftCorr N ghat (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) := by
  have hz' := invIndexEquiv_out_flipped N ghat hg hg2 U₀ hU₀ v γ hx
  have hout : ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out).out
      = (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)).out * ghat
        * shiftCorr N ghat (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) := by
    rw [hz']
    exact out_ghat_shift N ghat _
  show (invLift N ghat U₀ hU₀ v)⁻¹ * γ * invLift N ghat U₀ hU₀ (γ⁻¹ • v) = _
  rw [lWord]
  show ((invIndexEquiv N ghat U₀ hU₀ v).out).out⁻¹ * γ
      * ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out).out = _
  rw [hout]
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **`shiftCorr` duality**: `sc(m·ḡ) = (ĝ · sc(m) · ĝ)⁻¹` (from shifting twice, `ḡ² = 1`). -/
theorem shiftCorr_ghat_mul (ghat : G) (hg2 : ghat * ghat ∈ N) (m : G ⧸ N) :
    shiftCorr N ghat (m * (ghat : G ⧸ N)) = (ghat * shiftCorr N ghat m * ghat)⁻¹ := by
  have hsq : (m * (ghat : G ⧸ N)) * (ghat : G ⧸ N) = m := by
    rw [mul_assoc, ← QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (ghat * ghat)).mpr hg2, mul_one]
  have h1 : ((m * (ghat : G ⧸ N)) * (ghat : G ⧸ N)).out
      = (m * (ghat : G ⧸ N)).out * ghat * shiftCorr N ghat (m * (ghat : G ⧸ N)) :=
    out_ghat_shift N ghat _
  have h2 : (m * (ghat : G ⧸ N)).out = m.out * ghat * shiftCorr N ghat m :=
    out_ghat_shift N ghat m
  rw [hsq, h2] at h1
  -- h1 : m.out = m.out * ĝ * sc(m) * ĝ * sc(mḡ)
  rw [eq_inv_mul_iff_mul_eq.mpr h1.symm]
  group


omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `ĝ`-conjugated canonical word (rearranged `lWord_shift`):
`ĝ⁻¹·ℓ_k(η)·ĝ = sc(k) · ℓ_{kḡ}(η) · sc(η⁻¹•k)⁻¹`. -/
theorem ghat_conj_lWord (ghat : G) (k : G ⧸ N) (η : G) :
    ghat⁻¹ * lWord N k η * ghat
      = shiftCorr N ghat k * lWord N (k * (ghat : G ⧸ N)) η
        * (shiftCorr N ghat (η⁻¹ • k))⁻¹ := by
  rw [lWord_shift N ghat k η]
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `x ∈ U₀ \ N` has `G/N`-image exactly `ḡ`. -/
theorem mk_eq_ghat_of_notMem (ghat : G) (_ : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (x : G) (hxU : x ∈ U₀) (hx : x ∉ N) :
    (QuotientGroup.mk x : G ⧸ N) = QuotientGroup.mk' N ghat := by
  have himg : (QuotientGroup.mk x : G ⧸ N) ∈ Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
    rw [← map_U0_eq_zpowers N ghat U₀ hU₀]
    exact Subgroup.mem_map.mpr ⟨_, hxU, rfl⟩
  have hne1 : (QuotientGroup.mk x : G ⧸ N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]; exact hx
  exact (mem_zpowers_sq_one (ghatQuot_sq N ghat hg2) himg).resolve_left hne1

/-- `shiftCorr` as an element of `↥N`. -/
noncomputable def scEl (ghat : G) (m : G ⧸ N) : N :=
  ⟨shiftCorr N ghat m, shiftCorr_mem N ghat m⟩

/-- The correction read `D(m) = α(sc(m))`. -/
noncomputable def dRead (α : Z1 N (ZMod 2)) (ghat : G) (m : G ⧸ N) : ZMod 2 :=
  α.1 (scEl N ghat m)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **R1 (aligned `evensAux`-read)**: on the aligned locus, the `evensAux`-read of the
compatible word is the canonical `α`-read at the base point — no corrections. -/
theorem evensAux_lTransT_aligned (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀) (v : G ⧸ U₀) (γ : G)
    (hx : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N) :
    evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ)
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ) := by
  rw [evensAux_alphaOn_mem N α ghat U₀ hgU _ hx]
  exact congrArg α.1 (Subtype.ext (lWordT_invLift_aligned N ghat U₀ hU₀ v γ hx))

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **R2 (flipped `evensAux`-read)**: on the flipped locus, the read is the canonical `α`-read
plus the correction `D((γ⁻¹•z)·ḡ)`. -/
theorem evensAux_lTransT_flipped (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N)
    (hg2 : ghat * ghat ∈ N) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (v : G ⧸ U₀) (γ : G)
    (hx : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∉ N) :
    evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ)
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
        + dRead N α ghat ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * (ghat : G ⧸ N)) := by
  have hword := lWordT_invLift_flipped N ghat hg hg2 U₀ hU₀ v γ hx
  have hmem : ((lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ : U₀) : G)
      * ghat ∈ N := by
    show lWordT U₀ (invLift N ghat U₀ hU₀) v γ * ghat ∈ N
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul,
      mk_eq_ghat_of_notMem N ghat hg hg2 U₀ hU₀ _
        (lWordT_mem U₀ _ (invLift_spec N ghat U₀ hU₀) v γ) hx,
      QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hg2
  rw [evensAux_alphaOn_notMem N α ghat U₀ hgU hUi hs _ hx hmem]
  -- the read word factors as `ℓ_z(γ) · (sc((γ⁻¹•z)ḡ))⁻¹`
  have hfac : (⟨((lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ : U₀) : G)
        * ghat, hmem⟩ : N)
      = lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ
        * (scEl N ghat ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * (ghat : G ⧸ N)))⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, InvMemClass.coe_inv]
    show lWordT U₀ (invLift N ghat U₀ hU₀) v γ * ghat
        = lWord N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ
          * (shiftCorr N ghat ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * (ghat : G ⧸ N)))⁻¹
    rw [hword, shiftCorr_ghat_mul N ghat hg2]
    group
  rw [hfac, z1_mul N α, z1_inv N α]
  rfl

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **R5 (aligned `bS`-read)**: for an aligned `η`-slot at base `z'`, the `bS`-read is the
canonical `α`-read at `z'·ḡ` plus corrections `D(z') + D(η⁻¹•z')`. -/
theorem bS_lTransT_aligned (α : Z1 N (ZMod 2)) (ghat : G) (_ : ghat ∉ N)
    (_ : ghat * ghat ∈ N) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (w : G ⧸ U₀) (η : G)
    (hy : lWordT U₀ (invLift N ghat U₀ hU₀) w η ∈ N) :
    bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) w η)
      = dRead N α ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
        + α.1 (lTrans N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η)
        + dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)) := by
  have hword := lWordT_invLift_aligned N ghat U₀ hU₀ w η hy
  have hmem : ghat⁻¹
      * ((lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) w η : U₀) : G)
      * ghat ∈ N := by
    show ghat⁻¹ * lWordT U₀ (invLift N ghat U₀ hU₀) w η * ghat ∈ N
    have := Subgroup.Normal.conj_mem ‹N.Normal› _ hy ghat⁻¹
    simpa using this
  rw [bS_alphaOn_mem N α ghat U₀ hgU hUi hs _ hy hmem]
  have hfac : (⟨ghat⁻¹
        * ((lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) w η : U₀) : G)
        * ghat, hmem⟩ : N)
      = scEl N ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
        * lTrans N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η
        * (scEl N ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)))⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    show ghat⁻¹ * lWordT U₀ (invLift N ghat U₀ hU₀) w η * ghat
        = shiftCorr N ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
          * lWord N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η
          * (shiftCorr N ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)))⁻¹
    rw [hword]
    exact ghat_conj_lWord N ghat _ η
  rw [hfac, z1_mul N α, z1_mul N α, z1_inv N α]
  rfl

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **R6 (flipped `bS`-read)**: for a flipped `η`-slot at base `z'`, the `bS`-read is
`D(z')` plus the canonical `α`-read at `z'·ḡ`. -/
theorem bS_lTransT_flipped (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N)
    (hg2 : ghat * ghat ∈ N) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (w : G ⧸ U₀) (η : G)
    (hy : lWordT U₀ (invLift N ghat U₀ hU₀) w η ∉ N) :
    bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) w η)
      = dRead N α ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
        + α.1 (lTrans N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η) := by
  have hword := lWordT_invLift_flipped N ghat hg hg2 U₀ hU₀ w η hy
  have hmem : ghat⁻¹
      * ((lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) w η : U₀) : G)
      ∈ N := by
    show ghat⁻¹ * lWordT U₀ (invLift N ghat U₀ hU₀) w η ∈ N
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      mk_eq_ghat_of_notMem N ghat hg hg2 U₀ hU₀ _
        (lWordT_mem U₀ _ (invLift_spec N ghat U₀ hU₀) w η) hy,
      QuotientGroup.mk'_apply, inv_mul_cancel]
  rw [bS_alphaOn_notMem N α ghat U₀ hgU hUi hs _ hy hmem]
  have hfac : (⟨ghat⁻¹
        * ((lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) w η : U₀) : G),
        hmem⟩ : N)
      = scEl N ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
        * lTrans N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    show ghat⁻¹ * lWordT U₀ (invLift N ghat U₀ hU₀) w η
        = shiftCorr N ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
          * lWord N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η
    have hc := ghat_conj_lWord N ghat ((invIndexEquiv N ghat U₀ hU₀ w).out) η
    calc ghat⁻¹ * lWordT U₀ (invLift N ghat U₀ hU₀) w η
        = (ghat⁻¹ * lWord N ((invIndexEquiv N ghat U₀ hU₀ w).out) η * ghat)
          * shiftCorr N ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)) := by
          rw [hword]; group
      _ = (shiftCorr N ghat ((invIndexEquiv N ghat U₀ hU₀ w).out)
            * lWord N (((invIndexEquiv N ghat U₀ hU₀ w).out) * (ghat : G ⧸ N)) η
            * (shiftCorr N ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)))⁻¹)
          * shiftCorr N ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)) := by rw [hc]
      _ = _ := by group
  rw [hfac, z1_mul N α]
  rfl

/-! ### The position identity (Step 4a)

Per orbit position, the compatible-transversal `evensNormFun`-read equals `phi_inv_eq`'s
two summands plus the three coboundary terms of the aligned-locus
`Λ(σ) = Σ_{u aligned-for-σ} α(ℓ_{z_u}σ)·D(σ̄⁻¹•z_u)` — verified cell-by-cell over the four
aligned/flipped combinations. -/
omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `ḡ²`-collapse on `G/N`. -/
theorem quot_mul_ghat_sq (ghat : G) (hg2 : ghat * ghat ∈ N) (m : G ⧸ N) :
    (m * (ghat : G ⧸ N)) * (ghat : G ⧸ N) = m := by
  rw [mul_assoc, ← QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff (ghat * ghat)).mpr hg2, mul_one]

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `σ`-action commutes with right-`ḡ`: `σ⁻¹•(m·ḡ) = (σ⁻¹•m)·ḡ`. -/
theorem smul_mul_ghat (ghat : G) (σ : G) (m : G ⧸ N) :
    σ⁻¹ • (m * (ghat : G ⧸ N)) = (σ⁻¹ • m) * (ghat : G ⧸ N) := by
  rw [quot_smul_eq_mk_mul, quot_smul_eq_mk_mul, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The `mk'`-form of the plain shift. -/
theorem mk'_inv_mul (σ : G) (m : G ⧸ N) :
    (QuotientGroup.mk' N σ)⁻¹ * m = σ⁻¹ • m := by
  rw [quot_smul_eq_mk_mul, QuotientGroup.mk_inv]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **(F,F) product membership**: two flipped words multiply into `N` (`ḡ² = 1`). -/
theorem lWordT_mul_mem_of_notMem (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (T : G ⧸ U₀ → G) (hT : ∀ v : G ⧸ U₀, (T v : G ⧸ U₀) = v) (v : G ⧸ U₀) (γ η : G)
    (hx : lWordT U₀ T v γ ∉ N) (hy : lWordT U₀ T (γ⁻¹ • v) η ∉ N) :
    lWordT U₀ T v (γ * η) ∈ N := by
  rw [← QuotientGroup.eq_one_iff, lWordT_mul U₀ T v γ η, QuotientGroup.mk_mul,
    mk_eq_ghat_of_notMem N ghat hg hg2 U₀ hU₀ _ (lWordT_mem U₀ T hT v γ) hx,
    mk_eq_ghat_of_notMem N ghat hg hg2 U₀ hU₀ _ (lWordT_mem U₀ T hT (γ⁻¹ • v) η) hy]
  exact ghatQuot_sq N ghat hg2

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
open scoped Classical in
/-- **Position identity, `γ`-aligned case** (`ℓ_v γ ∈ N`, so `z' = γ⁻¹•z`): the two aligned
cells `(A,A)` and `(A,F)` of `invPositionEval`. -/
private theorem invPositionEval_aligned (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N)
    (hg2 : ghat * ghat ∈ N) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (hgU : ghat ∈ U₀) (hUi : (N.subgroupOf U₀).index = 2)
    (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀) (v : G ⧸ U₀) (γ η : G)
    (hX : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N) :
    evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ,
         lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) (γ⁻¹ • v) η)
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
          * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹
              * ((invIndexEquiv N ghat U₀ hU₀ v).out * QuotientGroup.mk' N ghat)) η)
        + (if (QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out
              = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out)
            then 0 else 1)
          * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                * (invIndexEquiv N ghat U₀ hU₀ v).out)) η)
             * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                * (invIndexEquiv N ghat U₀ hU₀ v).out) * QuotientGroup.mk' N ghat) η))
        + ((if lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
                * dRead N α ghat (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)
          + (if lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out) η)
                * dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out)) else 0)
          + (if lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) (γ * η))
                * dRead N α ghat ((γ * η)⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)) := by
  have hidx1 : (QuotientGroup.mk' N γ)⁻¹
        * ((invIndexEquiv N ghat U₀ hU₀ v).out * QuotientGroup.mk' N ghat)
      = (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat := by
    rw [← mul_assoc, mk'_inv_mul N γ]
  have hcond : ((QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)
        = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)))
      ↔ lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N :=
    (lWordT_invLift_mem_N_iff N ghat U₀ hU₀ v γ).symm
  have hXmem : (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ
      ∈ N.subgroupOf U₀) ↔ lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N :=
    Subgroup.mem_subgroupOf
  have hcompose : (γ * η)⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)
      = η⁻¹ • (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) := by
    rw [← mul_smul, mul_inv_rev]
  have hcoe : (ghat : G ⧸ N) = QuotientGroup.mk' N ghat := rfl
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hsplit : α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) (γ * η))
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
        + α.1 (lTrans N (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) η) := by
    rw [lTrans_mul' N _ γ η, z1_mul N α]
  -- `γ`-aligned: `z' = γ⁻¹•z`
  have hz' : (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out) :=
    invIndexEquiv_out_aligned N ghat U₀ hU₀ v γ hX
  have hεpos : (QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)
      = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
          * ((invIndexEquiv N ghat U₀ hU₀ v).out)) := hcond.mpr hX
  simp only [evensNormFun]
  rw [if_pos (hXmem.mpr hX)]
  rw [evensAux_lTransT_aligned N α ghat U₀ hU₀ hgU v γ hX]
  by_cases hY : lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η ∈ N
  · -- cell (A,A)
    have hXY : lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∈ N := by
      rw [lWordT_mul]
      exact mul_mem hX hY
    rw [bS_lTransT_aligned N α ghat hg hg2 U₀ hU₀ hgU hUi hs (γ⁻¹ • v) η hY]
    rw [if_pos hX, if_pos hY, if_pos hXY, if_pos hεpos]
    rw [hsplit, hidx1, hcompose, hz', hcoe]
    linear_combination (-(dRead N α ghat (η⁻¹ • (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)))
      * α.1 (lTrans N (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) η))) * h2
  · -- cell (A,F)
    have hXY : lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∉ N := by
      intro hmem
      apply hY
      have h1 : lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η
          = (lWordT U₀ (invLift N ghat U₀ hU₀) v γ)⁻¹
            * lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) := by
        rw [lWordT_mul]; group
      rw [h1]
      exact mul_mem (inv_mem hX) hmem
    rw [bS_lTransT_flipped N α ghat hg hg2 U₀ hU₀ hgU hUi hs (γ⁻¹ • v) η hY]
    rw [if_pos hX, if_neg hY, if_neg hXY, if_pos hεpos]
    rw [hidx1, hz', hcoe]
    ring

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
open scoped Classical in
/-- **Position identity, `γ`-flipped case** (`ℓ_v γ ∉ N`, so `z' = (γ⁻¹•z)·ḡ`): the two
flipped cells `(F,A)` and `(F,F)` of `invPositionEval`. -/
private theorem invPositionEval_flipped (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N)
    (hg2 : ghat * ghat ∈ N) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (hgU : ghat ∈ U₀) (hUi : (N.subgroupOf U₀).index = 2)
    (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀) (v : G ⧸ U₀) (γ η : G)
    (hX : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∉ N) :
    evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ,
         lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) (γ⁻¹ • v) η)
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
          * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹
              * ((invIndexEquiv N ghat U₀ hU₀ v).out * QuotientGroup.mk' N ghat)) η)
        + (if (QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out
              = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out)
            then 0 else 1)
          * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                * (invIndexEquiv N ghat U₀ hU₀ v).out)) η)
             * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                * (invIndexEquiv N ghat U₀ hU₀ v).out) * QuotientGroup.mk' N ghat) η))
        + ((if lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
                * dRead N α ghat (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)
          + (if lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out) η)
                * dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out)) else 0)
          + (if lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) (γ * η))
                * dRead N α ghat ((γ * η)⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)) := by
  have hidx1 : (QuotientGroup.mk' N γ)⁻¹
        * ((invIndexEquiv N ghat U₀ hU₀ v).out * QuotientGroup.mk' N ghat)
      = (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat := by
    rw [← mul_assoc, mk'_inv_mul N γ]
  have horb : orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out))
      = (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out :=
    (invIndexEquiv_smul_out N ghat U₀ hU₀ v γ).symm
  have hcond : ((QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)
        = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)))
      ↔ lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N :=
    (lWordT_invLift_mem_N_iff N ghat U₀ hU₀ v γ).symm
  have hXmem : (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ
      ∈ N.subgroupOf U₀) ↔ lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N :=
    Subgroup.mem_subgroupOf
  have hcompose : (γ * η)⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)
      = η⁻¹ • (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) := by
    rw [← mul_smul, mul_inv_rev]
  have hcoe : (ghat : G ⧸ N) = QuotientGroup.mk' N ghat := rfl
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hsplit : α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) (γ * η))
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
        + α.1 (lTrans N (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) η) := by
    rw [lTrans_mul' N _ γ η, z1_mul N α]
  -- `γ`-flipped: `z' = (γ⁻¹•z)·ḡ`
  have hz' : (invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out
      = (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * (ghat : G ⧸ N) :=
    invIndexEquiv_out_flipped N ghat hg hg2 U₀ hU₀ v γ hX
  have hεneg : ¬ ((QuotientGroup.mk' N γ)⁻¹ * ((invIndexEquiv N ghat U₀ hU₀ v).out)
      = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
          * ((invIndexEquiv N ghat U₀ hU₀ v).out))) := fun h => hX (hcond.mp h)
  simp only [evensNormFun]
  rw [if_neg (fun h => hX (hXmem.mp h))]
  rw [evensAux_lTransT_flipped N α ghat hg hg2 U₀ hU₀ hgU hUi hs v γ hX]
  by_cases hY : lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η ∈ N
  · -- cell (F,A)
    have hXY : lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∉ N := by
      intro hmem
      apply hX
      have h1 : lWordT U₀ (invLift N ghat U₀ hU₀) v γ
          = lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η)
            * (lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η)⁻¹ := by
        rw [lWordT_mul]; group
      rw [h1]
      exact mul_mem hmem (inv_mem hY)
    rw [evensAux_lTransT_aligned N α ghat U₀ hU₀ hgU (γ⁻¹ • v) η hY]
    rw [bS_lTransT_aligned N α ghat hg hg2 U₀ hU₀ hgU hUi hs (γ⁻¹ • v) η hY]
    rw [if_neg hX, if_pos hY, if_neg hXY, if_neg hεneg, horb]
    rw [hidx1, hz']
    rw [quot_mul_ghat_sq N ghat hg2 (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out))]
    rw [smul_mul_ghat N ghat η (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out))]
    rw [hcoe]
    rw [show ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat)
          * QuotientGroup.mk' N ghat = γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out) from
      quot_mul_ghat_sq N ghat hg2 _]
    linear_combination (α.1 (lTrans N
        ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat) η)
      * dRead N α ghat
        ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat)) * h2
  · -- cell (F,F)
    have hXY : lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∈ N :=
      lWordT_mul_mem_of_notMem N ghat hg hg2 U₀ hU₀ _ (invLift_spec N ghat U₀ hU₀)
        v γ η hX hY
    rw [evensAux_lTransT_flipped N α ghat hg hg2 U₀ hU₀ hgU hUi hs (γ⁻¹ • v) η hY]
    rw [bS_lTransT_flipped N α ghat hg hg2 U₀ hU₀ hgU hUi hs (γ⁻¹ • v) η hY]
    rw [if_neg hX, if_neg hY, if_pos hXY, if_neg hεneg, horb]
    rw [hsplit, hidx1, hz']
    rw [quot_mul_ghat_sq N ghat hg2 (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out))]
    rw [smul_mul_ghat N ghat η (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out))]
    rw [quot_mul_ghat_sq N ghat hg2 (η⁻¹ • (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)))]
    rw [hcompose, hcoe]
    rw [show ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat)
          * QuotientGroup.mk' N ghat = γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out) from
      quot_mul_ghat_sq N ghat hg2 _]
    linear_combination (α.1 (lTrans N
          ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat) η)
        * dRead N α ghat
          ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat)
      + dRead N α ghat
          ((γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) * QuotientGroup.mk' N ghat)
        * dRead N α ghat (η⁻¹ • (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)))) * h2

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
open scoped Classical in
/-- **The position identity**: at each orbit position, the compatible-transversal Evens-norm
read equals the two `phi_inv_eq` summands plus the three coboundary terms of the aligned-locus
`Λ`. -/
theorem invPositionEval (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (v : G ⧸ U₀) (γ η : G) :
    evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
        (lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) v γ,
         lTransT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) (γ⁻¹ • v) η)
      = α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
          * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹
              * ((invIndexEquiv N ghat U₀ hU₀ v).out * QuotientGroup.mk' N ghat)) η)
        + (if (QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out
              = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out)
            then 0 else 1)
          * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                * (invIndexEquiv N ghat U₀ hU₀ v).out)) η)
             * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                * (invIndexEquiv N ghat U₀ hU₀ v).out) * QuotientGroup.mk' N ghat) η))
        + ((if lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
                * dRead N α ghat (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)
          + (if lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out) η)
                * dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out)) else 0)
          + (if lWordT U₀ (invLift N ghat U₀ hU₀) v (γ * η) ∈ N then
              α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) (γ * η))
                * dRead N α ghat ((γ * η)⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)) := by
  by_cases hX : lWordT U₀ (invLift N ghat U₀ hU₀) v γ ∈ N
  · exact invPositionEval_aligned N α ghat hg hg2 U₀ hU₀ hgU hUi hs v γ η hX
  · exact invPositionEval_flipped N α ghat hg hg2 U₀ hU₀ hgU hUi hs v γ η hX

/-! ### The involution coboundary `invLambda` and the δ-assembly (Step 4b) -/

open scoped Classical in
/-- The involution transversal-change 1-cochain: the aligned-locus sum
`Λ(σ) = Σ_{v aligned-for-σ} α(ℓ_{z_v}σ)·D(σ⁻¹•z_v)`. -/
noncomputable def invLambda (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) : G → ZMod 2 :=
  fun σ => ∑ᶠ v : G ⧸ U₀,
    if lWordT U₀ (invLift N ghat U₀ hU₀) v σ ∈ N then
      α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) σ)
        * dRead N α ghat (σ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
open scoped Classical in
/-- The aligned-indicator summand in indicator-product form (for continuity). -/
theorem invLambda_summand_eq (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (σ : G) :
    (if lWordT U₀ (invLift N ghat U₀ hU₀) v σ ∈ N then
        α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) σ)
          * dRead N α ghat (σ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)
      = (if (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v σ) : G ⧸ N) = 1
            then (1 : ZMod 2) else 0)
        * (α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) σ)
            * dRead N α ghat (σ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out))) := by
  simp only [QuotientGroup.eq_one_iff, ite_mul, one_mul, zero_mul]

omit [ContinuousSMul G (ZMod 2)] in
/-- `invLambda` is continuous (`U₀ ⊇ N` is open; the alignment indicator factors through the
discrete `G/N`). -/
theorem invLambda_continuous (hNo : IsOpen (N : Set G)) (α : Z1 N (ZMod 2)) (ghat : G)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    Continuous (invLambda N α ghat U₀ hU₀) := by
  classical
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  haveI : Finite (G ⧸ U₀) := finite_quot_U0 N ghat U₀ hU₀
  haveI : Fintype (G ⧸ U₀) := Fintype.ofFinite _
  have hU₀o : IsOpen (U₀ : Set G) :=
    Subgroup.isOpen_mono (hU₀ ▸ le_sup_left : N ≤ U₀) hNo
  have hα : Continuous α.1 := (mem_Z1_iff.mp α.2).1
  have hEq : invLambda N α ghat U₀ hU₀ = fun σ => ∑ v : G ⧸ U₀,
      (if (QuotientGroup.mk (lWordT U₀ (invLift N ghat U₀ hU₀) v σ) : G ⧸ N) = 1
          then (1 : ZMod 2) else 0)
        * (α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) σ)
            * dRead N α ghat (σ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out))) :=
    funext fun σ => (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl
      fun v _ => invLambda_summand_eq N α ghat U₀ hU₀ v σ)
  rw [hEq]
  refine continuous_finsetSum Finset.univ (fun v _ => ?_)
  refine Continuous.mul ?_ (Continuous.mul ?_ ?_)
  · -- the alignment indicator factors through the discrete `G/N`
    have hword : Continuous fun σ : G => lWordT U₀ (invLift N ghat U₀ hU₀) v σ := by
      simp only [lWordT]
      exact (continuous_const_mul _).mul
        (continuous_comp_inv_smul U₀ hU₀o v (invLift N ghat U₀ hU₀))
    exact (continuous_of_discreteTopology
      (f := fun q : G ⧸ N => if q = 1 then (1 : ZMod 2) else 0)).comp
      (QuotientGroup.continuous_mk.comp hword)
  · exact hα.comp (continuous_lTrans' N hNo _)
  · exact (continuous_of_discreteTopology (f := fun m : G ⧸ N => dRead N α ghat m)).comp
      (continuous_inv_smul N hNo _)

omit [ContinuousSMul G (ZMod 2)] in
open scoped Classical in
/-- **The involution coboundary (Step 4b)**: the graph pullback differs from the
compatible-transversal corestriction by `δ¹(invLambda)`. -/
theorem graphPullback_sub_cor2FunT_mem_B2 (hNo : IsOpen (N : Set G))
    (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀) :
    graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat)) (QuotientGroup.mk' N)
        (shapiroFun N α.1)
      - cor2FunT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀)
          (fun p => evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (p.1, p.2))
      ∈ B2 G (ZMod 2) := by
  haveI : Finite (G ⧸ U₀) := finite_quot_U0 N ghat U₀ hU₀
  haveI : Fintype (G ⧸ U₀) := Fintype.ofFinite _
  haveI : Fintype ((G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)) := Fintype.ofFinite _
  simp only [B2, AddSubgroup.mem_map]
  refine ⟨invLambda N α ghat U₀ hU₀,
    mem_C1_iff.mpr (invLambda_continuous N hNo α ghat U₀ hU₀), ?_⟩
  funext p
  obtain ⟨γ, η⟩ := p
  have hL : dOne G (ZMod 2) (invLambda N α ghat U₀ hU₀) (γ, η)
      = invLambda N α ghat U₀ hU₀ η + invLambda N α ghat U₀ hU₀ (γ * η)
        + invLambda N α ghat U₀ hU₀ γ := by
    show γ • invLambda N α ghat U₀ hU₀ η - invLambda N α ghat U₀ hU₀ (γ * η)
        + invLambda N α ghat U₀ hU₀ γ = _
    rw [smul_zmodTwo, sub_eq_add_neg, CharTwo.neg_eq]
  rw [hL, Pi.sub_apply, phi_inv_eq]
  -- convert the two `O`-sums to `G/U₀`-sums along `invIndexEquiv`
  rw [show (∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
        α.1 (lTrans N u.out γ)
          * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹ * (u.out * QuotientGroup.mk' N ghat)) η))
      = ∑ᶠ v : G ⧸ U₀,
          α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) γ)
            * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹
                * ((invIndexEquiv N ghat U₀ hU₀ v).out * QuotientGroup.mk' N ghat)) η) from
    (finsum_comp_equiv (invIndexEquiv N ghat U₀ hU₀)).symm]
  rw [show (∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
        (if (QuotientGroup.mk' N γ)⁻¹ * u.out
            = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out) then 0 else 1)
          * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out)) η)
            * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out)
                * QuotientGroup.mk' N ghat) η)))
      = ∑ᶠ v : G ⧸ U₀,
          (if (QuotientGroup.mk' N γ)⁻¹ * (invIndexEquiv N ghat U₀ hU₀ v).out
              = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                  * (invIndexEquiv N ghat U₀ hU₀ v).out) then 0 else 1)
            * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                  * (invIndexEquiv N ghat U₀ hU₀ v).out)) η)
              * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹
                  * (invIndexEquiv N ghat U₀ hU₀ v).out) * QuotientGroup.mk' N ghat) η)) from
    (finsum_comp_equiv (invIndexEquiv N ghat U₀ hU₀)).symm]
  -- everything as `Fintype` sums
  show _ = _ - cor2FunT U₀ (invLift N ghat U₀ hU₀) (invLift_spec N ghat U₀ hU₀) _ (γ, η)
  simp only [cor2FunT, invLambda, finsum_eq_sum_of_fintype]
  -- rewrite the corestriction summand by the position identity
  rw [Finset.sum_congr rfl (fun v _ =>
    invPositionEval N α ghat hg hg2 U₀ hU₀ hgU hUi hs v γ η)]
  -- reindex the `η`-Λ sum onto the `γ`-shifted positions
  have hreindex : (∑ v : G ⧸ U₀,
        if lWordT U₀ (invLift N ghat U₀ hU₀) v η ∈ N then
          α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ v).out) η)
            * dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ v).out)) else 0)
      = ∑ v : G ⧸ U₀,
          if lWordT U₀ (invLift N ghat U₀ hU₀) (γ⁻¹ • v) η ∈ N then
            α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out) η)
              * dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ (γ⁻¹ • v)).out)) else 0 :=
    (sum_reindex_smul' U₀ γ (fun w =>
      if lWordT U₀ (invLift N ghat U₀ hU₀) w η ∈ N then
        α.1 (lTrans N ((invIndexEquiv N ghat U₀ hU₀ w).out) η)
          * dRead N α ghat (η⁻¹ • ((invIndexEquiv N ghat U₀ hU₀ w).out)) else 0)).symm
  rw [hreindex]
  simp only [Finset.sum_add_distrib]
  abel_nf
  simp only [neg_one_zsmul, CharTwo.neg_eq]

/-! ### The final chain (Step 5): `lemma_6_15_involution_aux` -/
omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
/-- `alphaOn` kills the identity. -/
theorem alphaOn_one (α : Z1 N (ZMod 2)) (U₀ : Subgroup G) :
    alphaOn N α U₀ 1 = 0 :=
  left_eq_add.mp (show alphaOn N α U₀ 1 = alphaOn N α U₀ 1 + alphaOn N α U₀ 1 by
    simpa using alphaOn_hom N α U₀ 1 1)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
/-- The Evens-norm cochain is right-normalized: `ν(z, 1) = 0`. -/
theorem evensNormFun_right_one (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G)
    (hgU : ghat ∈ U₀) (hUi : (N.subgroupOf U₀).index = 2)
    (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀) (z : U₀) :
    evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (z, 1) = 0 := by
  have hb1 : evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) 1 = 0 := by
    rw [evensAux_of_mem (alphaOn N α U₀) (one_mem _)]
    exact alphaOn_one N α U₀
  have hval : ∀ (u : N.subgroupOf U₀), (u : U₀) = 1 → alphaOn N α U₀ u = 0 := by
    intro u hu
    rw [show u = 1 from Subtype.ext hu]
    exact alphaOn_one N α U₀
  have hbS1 : bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) 1 = 0 := by
    rw [bS, mul_one, evensAux_of_notMem hUi hs (alphaOn N α U₀) (inv_notMem hs)]
    exact hval _ (inv_mul_cancel _)
  rw [evensNormFun]
  by_cases hz : z ∈ N.subgroupOf U₀
  · rw [if_pos hz]
    show _ * bS _ _ _ 1 = 0
    rw [hbS1, mul_zero]
  · rw [if_neg hz]
    show _ * evensAux _ _ _ 1 + evensAux _ _ _ 1 * bS _ _ _ 1 = 0
    rw [hb1, hbS1, mul_zero, zero_mul, add_zero]

omit [ContinuousSMul G (ZMod 2)] [N.Normal] [Finite (G ⧸ N)] in
/-- The Evens-norm cochain satisfies the char-2 four-term cocycle identity. -/
theorem evensNormFun_cocForm (hNo : IsOpen (N : Set G)) (α : Z1 N (ZMod 2)) (ghat : G)
    (U₀ : Subgroup G) (hgU : ghat ∈ U₀) (hUi : (N.subgroupOf U₀).index = 2)
    (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀) (a b c : U₀) :
    evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (b, c)
      + evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (a * b, c)
      + evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (a, b * c)
      + evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (a, b) = 0 := by
  have hZ2 : evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
      ∈ Z2 ↥U₀ (ZMod 2) :=
    evensNormFun_mem_Z2 (smul_zmodTwo) (subgroupOf_isOpen N hNo U₀) hUi hs
      (alphaOn N α U₀) (alphaOn_hom N α U₀) (alphaOn_continuous N α U₀)
  have e := (mem_Z2_iff.mp hZ2).2 a b c
  rw [smul_zmodTwo] at e
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination e
    + (evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (a * b, c)
        + evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (a, b)) * h2

/-- **Lemma 6.15, involution orbits (105)** — the graph pullback of the involution orbit datum
equals the corestriction of the index-two Evens norm, as `H2ofFun`-classes.  Chains the
compatible-transversal coboundary (`graphPullback_sub_cor2FunT_mem_B2`) with the
transversal-change coboundary (`cor2FunT_sub_cor2Fun_mem_B2`). -/
theorem lemma_6_15_involution_aux (hNo : IsOpen (N : Set G)) (α : Z1 N (ZMod 2)) (ghat : G)
    (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (hs : (⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩ : U₀)
        ∉ N.subgroupOf U₀) :
    H2ofFun G (graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat))
        (QuotientGroup.mk' N) (shapiroFun N α.1))
      = H2ofFun G (cor2Fun U₀ (fun p ↦
          evensNormFun (N.subgroupOf U₀)
            ⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩
            (fun u ↦ α.1 ⟨u.1.1, u.2⟩) (p.1, p.2))) := by
  classical
  have hgU : ghat ∈ U₀ := by
    rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)
  have hUi : (N.subgroupOf U₀).index = 2 := subgroupOf_index_two N ghat hg hg2 U₀ hU₀
  have hU₀o : IsOpen (U₀ : Set G) :=
    Subgroup.isOpen_mono (hU₀ ▸ le_sup_left : N ≤ U₀) hNo
  haveI : Finite (G ⧸ U₀) := finite_quot_U0 N ghat U₀ hU₀
  apply H2ofFun_eq_of_sub_mem_B2
  have h1 := graphPullback_sub_cor2FunT_mem_B2 N hNo α ghat hg hg2 U₀ hU₀ hgU hUi hs
  have h2 := cor2FunT_sub_cor2Fun_mem_B2 U₀ hU₀o (invLift N ghat U₀ hU₀)
    (invLift_spec N ghat U₀ hU₀)
    (fun p => evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) (p.1, p.2))
    (evensNormFun_continuous (subgroupOf_isOpen N hNo U₀) hUi hs
      (alphaOn_continuous N α U₀))
    (evensNormFun_cocForm N hNo α ghat U₀ hgU hUi hs)
    (evensNormFun_right_one N α ghat U₀ hgU hUi hs)
  have h3 := add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3

end Involution

end ShapiroLedger

end GQ2
