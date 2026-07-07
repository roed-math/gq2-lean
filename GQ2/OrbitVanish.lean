import GQ2.SectionSix
import GQ2.CorestrictionCohomology
import GQ2.LocalKummer

/-!
# P-15f2 (increment 1): the corestriction-of-coboundary bridge for Lemma 6.17's vanishing clause

`lemma_6_17_vanish` (`Q⁰_loc|X₊ = 0`) reduces — after the `H_V`-split embedding of Lemma 6.14 and
the orbit decomposition of Lemma 6.15 — to a sum of per-orbit contributions, each of the form
`H²ofFun G_ℚ₂ (cor2Fun U inner)` where `inner` is a scalar cup (free/square orbits) or an Evens
norm (involution orbits).  For a deep class every such `inner` **is a coboundary**: free/square by
the (94) orthogonality (`LocalKummer.cup_deepClasses` / `HilbertLedger.cup_deep_self`), involution
by Lemma 6.16.

This file supplies the reusable brick that turns "`inner` is a coboundary" into "its corestriction
vanishes in `H²`" — the cochain heart the P-15f2 scoping doc flagged as *"the continuity → B2 step
still needed"*.  `Corestriction.cor2Fun_dOne` gives `cor2Fun U (δ¹c) = δ¹(cor1Fun U c)`, the trivial
`𝔽₂`-action (`absGal_smul_zmodTwo`, `rfl`) identifies it with the genuine coboundary
`dOne (cor1Fun U c)`, and `cor1Fun U c` is continuous (`ShapiroLedger.continuous_lTrans'`), so the
corestriction lands in `B²` and its class is `0`.  All std-3, no axiom.
-/

namespace GQ2

namespace OrbitVanish

open Corestriction ShapiroLedger ContCoh

/-- **Corestriction of a coboundary vanishes in `H²`** (P-15f2, the per-orbit cochain heart):
if `inner = δ¹c` is the trivial-action coboundary of a continuous 1-cochain `c : ↥U → 𝔽₂`, then
the degree-2 corestriction `cor2Fun U inner` is `0` in `H²(G_ℚ₂, 𝔽₂)`.

`cor2Fun_dOne` rewrites `cor2Fun U (δ¹c) = δ¹(cor1Fun U c)`, which is the coboundary of the
continuous cochain `cor1Fun U c` (`continuous_lTrans'`), so it lies in `B²` and `H²ofFun` sends it
to `0`. -/
theorem H2ofFun_cor2Fun_coboundary_eq_zero (U : Subgroup AbsGalQ2) [Finite (AbsGalQ2 ⧸ U)]
    (hUo : IsOpen (U : Set AbsGalQ2)) (c : ↥U → ZMod 2) (hc : Continuous c) :
    H2ofFun AbsGalQ2 (cor2Fun U (fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1)) = 0 := by
  classical
  haveI : Fintype (AbsGalQ2 ⧸ U) := Fintype.ofFinite _
  -- (1) `cor2Fun` of the coboundary form = `δ¹(cor1Fun c)` (trivial `𝔽₂`-action)
  have hcor : cor2Fun U (fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1)
      = dOne AbsGalQ2 (ZMod 2) (cor1Fun U c) := by
    rw [cor2Fun_dOne U c]
    funext p
    show cor1Fun U c p.2 - cor1Fun U c (p.1 * p.2) + cor1Fun U c p.1
        = p.1 • cor1Fun U c p.2 - cor1Fun U c (p.1 * p.2) + cor1Fun U c p.1
    rw [absGal_smul_zmodTwo]
  -- (2) `cor1Fun c` is continuous (finite sum of `c ∘ ℓ_u`, each continuous by `continuous_lTrans'`)
  have hcont : Continuous (cor1Fun U c) := by
    have hEq : cor1Fun U c = fun γ => ∑ u : AbsGalQ2 ⧸ U, c (lTrans U u γ) := by
      funext γ; exact finsum_eq_sum_of_fintype _
    rw [hEq]
    exact continuous_finsetSum _ fun u _ => hc.comp (continuous_lTrans' U hUo u)
  -- (3) hence the corestriction lies in `B²`, so its `H²`-class is `0`
  have hB2 : cor2Fun U (fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1)
      ∈ B2 AbsGalQ2 (ZMod 2) := by
    rw [hcor]; exact ⟨cor1Fun U c, hcont, rfl⟩
  have hz : H2ofFun AbsGalQ2 (0 : AbsGalQ2 × AbsGalQ2 → ZMod 2) = 0 := by
    rw [H2ofFun_of_mem (zero_mem _)]; exact map_zero _
  rw [← hz]
  exact H2ofFun_eq_of_sub_mem_B2 (by rw [sub_zero]; exact hB2)

/-- **Class-level form** (the Lemma-6.15 orbit consumer): if a 2-cocycle `inner` on the subgroup
`↥U` has trivial class in `H²(↥U, 𝔽₂)`, its degree-2 corestriction vanishes in `H²(G_ℚ₂, 𝔽₂)`.

This is the shape the per-orbit outputs feed: the free/square-orbit cup and the involution-orbit
Evens norm each vanish in the subgroup's `H²` (by the (94) orthogonality `cup_deepClasses` resp.
Lemma 6.16 for a deep class), and corestriction carries that vanishing up to `G_ℚ₂`.  Extracts the
explicit continuous coboundary (`H² = 0` + `smul_zmodTwo` trivial action) and applies
`H2ofFun_cor2Fun_coboundary_eq_zero`. -/
theorem H2ofFun_cor2Fun_eq_zero_of_H2_eq_zero (U : Subgroup AbsGalQ2) [Finite (AbsGalQ2 ⧸ U)]
    (hUo : IsOpen (U : Set AbsGalQ2)) (inner : ↥U × ↥U → ZMod 2)
    (hZ2 : inner ∈ Z2 ↥U (ZMod 2)) (h0 : H2ofFun ↥U inner = 0) :
    H2ofFun AbsGalQ2 (cor2Fun U inner) = 0 := by
  -- `H² = 0` ⟹ `inner ∈ B²(↥U)` ⟹ `inner = δ¹c` for a continuous `c`
  rw [H2ofFun_of_mem hZ2] at h0
  have hmem : ((⟨inner, hZ2⟩ : Z2 ↥U (ZMod 2)) : ↥U × ↥U → ZMod 2) ∈ B2 ↥U (ZMod 2) := by
    have h := (QuotientAddGroup.eq_zero_iff _).mp h0
    rwa [AddSubgroup.mem_addSubgroupOf] at h
  simp only [B2, AddSubgroup.mem_map] at hmem
  obtain ⟨c, hc, hceq⟩ := hmem
  -- rewrite `inner` in the trivial-action coboundary form and apply the cochain bridge
  have hform : inner = fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1 := by
    rw [← hceq]; funext ab
    show ab.1 • c ab.2 - c (ab.1 * ab.2) + c ab.1 = c ab.2 - c (ab.1 * ab.2) + c ab.1
    rw [smul_zmodTwo]
  rw [hform]
  exact H2ofFun_cor2Fun_coboundary_eq_zero U hUo c hc

end OrbitVanish

end GQ2
