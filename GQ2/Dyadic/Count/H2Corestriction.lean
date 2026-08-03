/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2SylowTransfer
import GQ2.Shapiro.Ledger.Free

/-!
# General-coefficient corestriction in continuous degree two

This file constructs the low-degree transfer needed by the odd-index reduction in
`GQ2.Dyadic.Count.H2SylowTransfer`.  For an open finite-index subgroup `U ≤ G` and a
continuous `G`-module `M`, the cochain formulas are

* `cor¹(c)(g) = Σ_u ũ • c(ℓ_u(g))`;
* `cor²(z)(g,h) = Σ_u ũ • z(ℓ_u(g), ℓ_{g⁻¹u}(h))`.

The representative `ũ` is `Quotient.out u`, and `ℓ` is the canonical transversal word
from `GQ2.Corestriction`.  The extra `ũ`-action is exactly what is absent for the existing
trivial-`ZMod 2` formula.

The proofs below are explicit inhomogeneous-cochain calculations.  In particular, no derived
functor comparison or new axiom is used.
-/

namespace GQ2.ContCoh

noncomputable section

open Corestriction

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-! ## Raw cochain formulas -/

/-- General-coefficient degree-one corestriction on raw cochains. -/
def cor1Coeff (U : Subgroup G) (c : U → M) : G → M :=
  fun g ↦ ∑ᶠ u : G ⧸ U, u.out • c (lTrans U u g)

/-- General-coefficient degree-two corestriction on raw cochains. -/
def cor2Coeff (U : Subgroup G) (z : U × U → M) : G × G → M :=
  fun p ↦ ∑ᶠ u : G ⧸ U,
    u.out • z (lTrans U u p.1, lTrans U (p.1⁻¹ • u) p.2)

/-! ## Transversal algebra and continuity -/

/-- The defining factorization of the transversal word, in the orientation used by transfer. -/
theorem out_mul_lTrans (U : Subgroup G) (u : G ⧸ U) (g : G) :
    u.out * (lTrans U u g : G) = g * (g⁻¹ • u).out := by
  simp only [lTrans, lWord, Subgroup.coe_mk]
  group

/-- Moving the leading `g`-action across a reindexed transversal summand. -/
theorem smul_out_eq_out_smul_lTrans (U : Subgroup G) (u : G ⧸ U) (g : G) (m : M) :
    g • ((g⁻¹ • u).out • m) = u.out • ((lTrans U u g : G) • m) := by
  rw [← mul_smul, ← mul_smul, out_mul_lTrans]

/-- The second, moving transversal word in `cor²` is continuous when `U` is open. -/
theorem continuous_lTrans_inv_smul_snd (U : Subgroup G) (hU : IsOpen (U : Set G))
    (u : G ⧸ U) :
    Continuous fun p : G × G ↦ lTrans U (p.1⁻¹ • u) p.2 := by
  have hfirst : Continuous fun p : G × G ↦ ((p.1⁻¹ • u).out : G) :=
    (GQ2.ShapiroLedger.continuous_comp_inv_smul U hU u
      (fun v ↦ (v.out : G))).comp continuous_fst
  have hlast : Continuous fun p : G × G ↦ ((p.2⁻¹ • (p.1⁻¹ • u)).out : G) := by
    have h := (GQ2.ShapiroLedger.continuous_comp_inv_smul U hU u
      (fun v ↦ (v.out : G))).comp (continuous_fst.mul continuous_snd)
    convert h using 1
    funext p
    change (p.2⁻¹ • (p.1⁻¹ • u)).out = ((p.1 * p.2)⁻¹ • u).out
    rw [mul_inv_rev, mul_smul]
  have hw : Continuous fun p : G × G ↦ lWord U (p.1⁻¹ • u) p.2 := by
    simp only [lWord]
    exact hfirst.inv.mul continuous_snd |>.mul hlast
  exact hw.subtype_mk _

/-- `cor¹` sends continuous cochains to continuous cochains. -/
theorem continuous_cor1Coeff (U : Subgroup G) [Finite (G ⧸ U)]
    (hU : IsOpen (U : Set G)) (c : U → M) (hc : Continuous c) :
    Continuous (cor1Coeff U c) := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  change Continuous fun g ↦ ∑ᶠ u : G ⧸ U, u.out • c (lTrans U u g)
  rw [show (fun g ↦ ∑ᶠ u : G ⧸ U, u.out • c (lTrans U u g)) =
      fun g ↦ ∑ u : G ⧸ U, u.out • c (lTrans U u g) from
    funext fun _ ↦ finsum_eq_sum_of_fintype _]
  exact continuous_finsetSum Finset.univ fun u _ ↦
    continuous_const.smul (hc.comp (GQ2.ShapiroLedger.continuous_lTrans' U hU u))

/-- `cor²` sends continuous cochains to continuous cochains. -/
theorem continuous_cor2Coeff (U : Subgroup G) [Finite (G ⧸ U)]
    (hU : IsOpen (U : Set G)) (z : U × U → M) (hz : Continuous z) :
    Continuous (cor2Coeff U z) := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  change Continuous fun (p : G × G) ↦ ∑ᶠ u : G ⧸ U,
    u.out • z (lTrans U u p.1, lTrans U (p.1⁻¹ • u) p.2)
  rw [show (fun (p : G × G) ↦ ∑ᶠ u : G ⧸ U,
      u.out • z (lTrans U u p.1, lTrans U (p.1⁻¹ • u) p.2)) =
      fun (p : G × G) ↦ ∑ u : G ⧸ U,
        u.out • z (lTrans U u p.1, lTrans U (p.1⁻¹ • u) p.2) from
    funext fun _ ↦ finsum_eq_sum_of_fintype _]
  exact continuous_finsetSum Finset.univ fun u _ ↦ continuous_const.smul
    (hz.comp ((GQ2.ShapiroLedger.continuous_lTrans' U hU u).comp continuous_fst |>.prodMk
      (continuous_lTrans_inv_smul_snd U hU u)))

/-! ## Compatibility with the differential -/

/-- General-coefficient corestriction commutes with `δ¹`. -/
theorem cor2Coeff_dOne (U : Subgroup G) [Finite (G ⧸ U)] (c : U → M) :
    cor2Coeff U (dOne U M c) = dOne G M (cor1Coeff U c) := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  funext p
  obtain ⟨g, h⟩ := p
  simp only [cor2Coeff, cor1Coeff, dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    finsum_eq_sum_of_fintype, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · congr 1
    · exact Fintype.sum_bijective (fun u : G ⧸ U ↦ g⁻¹ • u)
        (MulAction.bijective g⁻¹) _ _
        (fun u ↦ (smul_out_eq_out_smul_lTrans U u g _).symm)
    · apply Finset.sum_congr rfl
      intro u _
      rw [← GQ2.ShapiroLedger.lTrans_mul']

/-! ## Corestriction on cocycles and cohomology -/

/-- General-coefficient degree-two corestriction sends continuous cocycles to continuous
cocycles. -/
theorem cor2Coeff_mem_Z2 (U : Subgroup G) [Finite (G ⧸ U)]
    (hU : IsOpen (U : Set G)) (z : Z2 U M) : cor2Coeff U z.1 ∈ Z2 G M := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  obtain ⟨hzc, hz⟩ := mem_Z2_iff.mp z.2
  refine mem_Z2_iff.mpr ⟨continuous_cor2Coeff U hU z.1 hzc, fun g h k ↦ ?_⟩
  have hfirst :
      g • (∑ u : G ⧸ U,
        u.out • z.1 (lTrans U u h, lTrans U (h⁻¹ • u) k)) =
        ∑ u : G ⧸ U, u.out • ((lTrans U u g : G) •
          z.1 (lTrans U (g⁻¹ • u) h, lTrans U (h⁻¹ • (g⁻¹ • u)) k)) := by
    rw [Finset.smul_sum]
    exact Fintype.sum_bijective (fun u : G ⧸ U ↦ g • u)
      (MulAction.bijective g) _ _ (fun u ↦ by
        simpa using smul_out_eq_out_smul_lTrans U (g • u) g
          (z.1 (lTrans U u h, lTrans U (h⁻¹ • u) k)))
  change g • (∑ᶠ u : G ⧸ U,
      u.out • z.1 (lTrans U u h, lTrans U (h⁻¹ • u) k)) +
      (∑ᶠ u : G ⧸ U,
        u.out • z.1 (lTrans U u g, lTrans U (g⁻¹ • u) (h * k))) =
    (∑ᶠ u : G ⧸ U,
      u.out • z.1 (lTrans U u (g * h), lTrans U ((g * h)⁻¹ • u) k)) +
      (∑ᶠ u : G ⧸ U,
        u.out • z.1 (lTrans U u g, lTrans U (g⁻¹ • u) h))
  simp only [finsum_eq_sum_of_fintype, hfirst]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hind : h⁻¹ • (g⁻¹ • u) = (g * h)⁻¹ • u := by
    rw [← mul_smul, mul_inv_rev]
  rw [GQ2.ShapiroLedger.lTrans_mul', GQ2.ShapiroLedger.lTrans_mul', ← hind]
  simpa only [smul_add, MulAction.subgroup_smul_def] using congrArg (u.out • ·)
    (hz (lTrans U u g) (lTrans U (g⁻¹ • u) h)
      (lTrans U (h⁻¹ • (g⁻¹ • u)) k))

/-- Corestriction on degree-two cocycles. -/
def corZ2 (U : Subgroup G) [Finite (G ⧸ U)] (hU : IsOpen (U : Set G)) :
    Z2 U M →+ Z2 G M where
  toFun z := ⟨cor2Coeff U z.1, cor2Coeff_mem_Z2 U hU z⟩
  map_zero' := Subtype.ext (funext fun _ ↦ by simp [cor2Coeff])
  map_add' z w := Subtype.ext (funext fun _ ↦ by
    classical
    letI : Fintype (G ⧸ U) := Fintype.ofFinite _
    simp only [cor2Coeff, AddSubgroup.coe_add, Pi.add_apply, smul_add,
      finsum_eq_sum_of_fintype, Finset.sum_add_distrib])

/-- Corestriction carries degree-two coboundaries into degree-two coboundaries. -/
theorem corZ2_maps_B2 (U : Subgroup G) [Finite (G ⧸ U)] (hU : IsOpen (U : Set G))
    (z : Z2 U M) (hz : z ∈ (B2 U M).addSubgroupOf (Z2 U M)) :
    corZ2 U hU z ∈ (B2 G M).addSubgroupOf (Z2 G M) := by
  rw [AddSubgroup.mem_addSubgroupOf] at hz ⊢
  rw [B2, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨c, hc, hcz⟩ := hz
  refine ⟨cor1Coeff U c, continuous_cor1Coeff U hU c hc, ?_⟩
  rw [← cor2Coeff_dOne U c]
  exact congrArg (cor2Coeff U) hcz

/-- General-coefficient corestriction in continuous degree two. -/
def cor2 (U : Subgroup G) [Finite (G ⧸ U)] (hU : IsOpen (U : Set G)) :
    H2 U M →+ H2 G M :=
  QuotientAddGroup.map _ _ (corZ2 U hU) (corZ2_maps_B2 U hU)

/-- Corestriction computes on a represented cocycle. -/
theorem cor2_H2mk (U : Subgroup G) [Finite (G ⧸ U)] (hU : IsOpen (U : Set G))
    (z : Z2 U M) :
    cor2 U hU (H2mk U M z) = H2mk G M (corZ2 U hU z) := rfl

/-! ## Naturality in coefficients -/

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]

/-- The raw degree-two corestriction formula is natural in equivariant additive coefficient
maps. -/
theorem map_cor2Coeff (U : Subgroup G) [Finite (G ⧸ U)]
    (f : M →+ N) (hfG : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (z : U × U → M) (p : G × G) :
    f (cor2Coeff U z p) = cor2Coeff U (fun ab ↦ f (z ab)) p := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  simp only [cor2Coeff, finsum_eq_sum_of_fintype, map_sum, hfG]

/-- General-coefficient degree-two corestriction commutes with a continuous equivariant
coefficient map. -/
theorem mapCoeff2_cor2 (U : Subgroup G) [Finite (G ⧸ U)] (hU : IsOpen (U : Set G))
    (f : M →+ N) (hf : Continuous f)
    (hfG : ∀ (g : G) (m : M), f (g • m) = g • f m) (x : H2 U M) :
    mapCoeff2 f hf hfG (cor2 U hU x) =
      cor2 U hU (mapCoeff2 f hf (fun (u : U) m ↦ hfG u.1 m) x) := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := U) (M := M) x
  rw [cor2_H2mk, mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff, cor2_H2mk]
  apply congrArg (H2mk G N)
  apply Subtype.ext
  funext p
  exact map_cor2Coeff U f hfG z.1 p

/-! ## The restriction-transfer chain homotopy -/

/-- The standard degree-one homotopy comparing `cor ∘ res` with multiplication by the
subgroup index. -/
def corResHomotopy (U : Subgroup G) (z : G × G → M) : G → M :=
  fun g ↦ ∑ᶠ u : G ⧸ U,
    (z (u.out, (lTrans U u g : G)) - z (g, (g⁻¹ • u).out))

/-- The restriction-transfer homotopy is continuous for an open finite-index subgroup. -/
theorem continuous_corResHomotopy (U : Subgroup G) [Finite (G ⧸ U)]
    (hU : IsOpen (U : Set G)) (z : G × G → M) (hz : Continuous z) :
    Continuous (corResHomotopy U z) := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  change Continuous fun g ↦ ∑ᶠ u : G ⧸ U,
    (z (u.out, (lTrans U u g : G)) - z (g, (g⁻¹ • u).out))
  rw [show (fun g ↦ ∑ᶠ u : G ⧸ U,
      (z (u.out, (lTrans U u g : G)) - z (g, (g⁻¹ • u).out))) =
      fun g ↦ ∑ u : G ⧸ U,
        (z (u.out, (lTrans U u g : G)) - z (g, (g⁻¹ • u).out)) from
    funext fun _ ↦ finsum_eq_sum_of_fintype _]
  exact continuous_finsetSum Finset.univ fun u _ ↦
    (hz.comp (continuous_const.prodMk
      ((GQ2.ShapiroLedger.continuous_lTrans' U hU u).subtype_val))).sub
      (hz.comp (continuous_id.prodMk
        (GQ2.ShapiroLedger.continuous_comp_inv_smul U hU u fun v ↦ (v.out : G))))

/-- The three cocycle identities underlying one summand of the restriction-transfer chain
homotopy. -/
theorem corResHomotopy_term {z : G × G → M}
    (hz : ∀ g h k : G, g • z (h, k) + z (g, h * k) = z (g * h, k) + z (g, h))
    {t v w g h a b : G} (hta : t * a = g * v) (hvb : v * b = h * w) :
    t • z (a, b) =
      g • (z (v, b) - z (h, w)) - (z (t, a * b) - z (g * h, w)) +
        (z (t, a) - z (g, v)) + z (g, h) := by
  have h1 := hz t a b
  have h2 := hz g v b
  have h3 := hz g h w
  rw [hta] at h1
  rw [hvb] at h2
  have e1 : t • z (a, b) = z (g * v, b) + z (t, a) - z (t, a * b) := by
    rw [eq_sub_iff_add_eq]
    exact h1
  have e2 : z (g * v, b) = g • z (v, b) + z (g, h * w) - z (g, v) := by
    rw [eq_sub_iff_add_eq]
    exact h2.symm
  have e3 : z (g, h * w) = z (g * h, w) + z (g, h) - g • z (h, w) := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using h3
  rw [e1, e2, e3, smul_sub]
  abel

/-- On raw cocycles, corestriction after restriction is index multiplication up to the
explicit continuous coboundary `corResHomotopy`. -/
theorem cor2Coeff_restrict_eq_dOne_add_index (U : Subgroup G) [Finite (G ⧸ U)]
    (z : Z2 G M) :
    cor2Coeff U (fun ab : U × U ↦ z.1 (ab.1.1, ab.2.1)) =
      dOne G M (corResHomotopy U z.1) + U.index • z.1 := by
  classical
  letI : Fintype (G ⧸ U) := Fintype.ofFinite _
  obtain ⟨_, hz⟩ := mem_Z2_iff.mp z.2
  funext p
  obtain ⟨g, h⟩ := p
  have hshift :
      g • (∑ u : G ⧸ U,
        (z.1 (u.out, (lTrans U u h : G)) - z.1 (h, (h⁻¹ • u).out))) =
        ∑ u : G ⧸ U, g •
          (z.1 ((g⁻¹ • u).out, (lTrans U (g⁻¹ • u) h : G)) -
            z.1 (h, (h⁻¹ • (g⁻¹ • u)).out)) := by
    rw [Finset.smul_sum]
    exact Fintype.sum_bijective (fun u : G ⧸ U ↦ g • u)
      (MulAction.bijective g) _ _ (fun u ↦ by simp)
  have hindex : (∑ _u : G ⧸ U, z.1 (g, h)) = U.index • z.1 (g, h) := by
    rw [Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card,
      Nat.card_eq_fintype_card]
  change (∑ᶠ u : G ⧸ U, u.out •
      z.1 ((lTrans U u g : G), (lTrans U (g⁻¹ • u) h : G))) =
    (g • (∑ᶠ u : G ⧸ U,
        (z.1 (u.out, (lTrans U u h : G)) - z.1 (h, (h⁻¹ • u).out))) -
      (∑ᶠ u : G ⧸ U,
        (z.1 (u.out, (lTrans U u (g * h) : G)) - z.1 (g * h, ((g * h)⁻¹ • u).out))) +
      (∑ᶠ u : G ⧸ U,
        (z.1 (u.out, (lTrans U u g : G)) - z.1 (g, (g⁻¹ • u).out)))) +
      U.index • z.1 (g, h)
  simp only [finsum_eq_sum_of_fintype, hshift]
  calc
    (∑ u : G ⧸ U, u.out •
        z.1 ((lTrans U u g : G), (lTrans U (g⁻¹ • u) h : G))) =
      ∑ u : G ⧸ U,
        (g • (z.1 ((g⁻¹ • u).out, (lTrans U (g⁻¹ • u) h : G)) -
            z.1 (h, (h⁻¹ • (g⁻¹ • u)).out)) -
          (z.1 (u.out, (lTrans U u (g * h) : G)) -
            z.1 (g * h, ((g * h)⁻¹ • u).out)) +
          (z.1 (u.out, (lTrans U u g : G)) - z.1 (g, (g⁻¹ • u).out)) +
          z.1 (g, h)) := by
        apply Finset.sum_congr rfl
        intro u _
        have hind : h⁻¹ • (g⁻¹ • u) = (g * h)⁻¹ • u := by
          rw [← mul_smul, mul_inv_rev]
        rw [GQ2.ShapiroLedger.lTrans_mul', ← hind]
        exact corResHomotopy_term hz (out_mul_lTrans U u g)
          (out_mul_lTrans U (g⁻¹ • u) h)
    _ =
      ((∑ u : G ⧸ U, g •
          (z.1 ((g⁻¹ • u).out, (lTrans U (g⁻¹ • u) h : G)) -
            z.1 (h, (h⁻¹ • (g⁻¹ • u)).out))) -
        (∑ u : G ⧸ U,
          (z.1 (u.out, (lTrans U u (g * h) : G)) -
            z.1 (g * h, ((g * h)⁻¹ • u).out))) +
        (∑ u : G ⧸ U,
          (z.1 (u.out, (lTrans U u g : G)) - z.1 (g, (g⁻¹ • u).out)))) +
        U.index • z.1 (g, h) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        hindex]

/-- Corestriction after restriction is multiplication by the subgroup index on continuous
degree-two cohomology with arbitrary coefficients. -/
theorem cor2_res2 (U : Subgroup G) [Finite (G ⧸ U)] (hU : IsOpen (U : Set G))
    (x : H2 G M) : cor2 U hU (res2 G M U x) = U.index • x := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := M) x
  rw [res2_H2mk, cor2_H2mk, ← map_nsmul]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [AddSubgroup.mem_addSubgroupOf, B2, AddSubgroup.mem_map]
  refine ⟨corResHomotopy U z.1,
    continuous_corResHomotopy U hU z.1 (mem_Z2_iff.mp z.2).1, ?_⟩
  apply funext
  intro p
  have hp := congrFun (cor2Coeff_restrict_eq_dOne_add_index U z) p
  change dOne G M (corResHomotopy U z.1) p =
    cor2Coeff U (fun ab : U × U ↦ z.1 (ab.1.1, ab.2.1)) p -
      (U.index • z.1) p
  rw [hp]
  change dOne G M (corResHomotopy U z.1) p =
    (dOne G M (corResHomotopy U z.1) p + (U.index • z.1) p) -
      (U.index • z.1) p
  abel

/-! ## Constructor for the odd-index transfer square -/

/-- The canonical general-coefficient corestrictions supply the abstract transfer square used
by the Sylow reduction. -/
def h2RestrictionTransferSquare (U : Subgroup G) [Finite (G ⧸ U)]
    (hU : IsOpen (U : Set G)) (f : M →+ N) (hf : Continuous f)
    (hfG : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    H2RestrictionTransferSquare U f hf hfG where
  corSource := cor2 U hU
  corTarget := cor2 U hU
  naturality := mapCoeff2_cor2 U hU f hf hfG
  cor_res_target := cor2_res2 U hU

/-- For a compact group, openness supplies the finite-index instance needed by the canonical
transfer square. -/
def h2RestrictionTransferSquareOfOpen [CompactSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G))
    (f : M →+ N) (hf : Continuous f)
    (hfG : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    H2RestrictionTransferSquare U f hf hfG := by
  letI : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  exact h2RestrictionTransferSquare U hU f hf hfG

end

end GQ2.ContCoh
