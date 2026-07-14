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

/-- Carrier of the twisted extension `V ×_{Δf} 𝔽₂` used to split a zero-form factor set
(P-15f2a, increment A): a pair `(base, fib)` carrying the twisted addition
`(v,a) + (w,b) = (v+w, a+b+Δf v w)`.  For a **symmetric, zero-diagonal** cocycle `Δf` on a
`2`-torsion `V` this is an elementary abelian `2`-group, hence an `𝔽₂`-vector space; the `𝔽₂`-linear
section of the `base` projection provides the quadratic refinement `Δφ`. -/
@[ext]
private structure ZFExt (V : Type*) where
  /-- The `V`-coordinate. -/
  base : V
  /-- The central `𝔽₂`-coordinate. -/
  fib : ZMod 2

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
  have hz : H2ofFun AbsGalQ2 (0 : AbsGalQ2 × AbsGalQ2 → ZMod 2) = 0 := by
    rw [H2ofFun_of_mem (zero_mem _)]; exact map_zero _
  rw [← hz]
  exact H2ofFun_eq_of_sub_mem_B2 (by rw [sub_zero, hcor]; exact ⟨cor1Fun U c, hcont, rfl⟩)

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

/-! ## The Lemma-6.17 vanishing assembly (the verified reduction, parametric over gap 2) -/

section Assembly

open SectionSix

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **The Lemma-6.17 vanishing assembly** (P-15f2, the verified reduction): if `Q⁰_loc` at a class
`x` decomposes as a finite sum of per-orbit corestriction contributions — the monomial expansion
`hexp`, i.e. Lemma 6.14 through the regular embedding + Lemma 6.15's orbit classes (the combinatorial
"gap 2" of `docs/p15f2-scoping.md`) — and each orbit's inner `2`-cocycle vanishes in the subgroup's
`H²` (`hvanish`: free/square by the (94) orthogonality `cup_deepClasses`, involution by Lemma 6.16,
for a deep class), then `Q⁰_loc x = 0`.

Isolates the remaining combinatorial input `hexp` from the arithmetic vanishing, which discharges
through the corestriction bridge `H2ofFun_cor2Fun_eq_zero_of_H2_eq_zero`.  Mirrors the f8 pattern:
verified reduction separated from the hard analytic input. -/
theorem Q0loc_vanish_of_orbit_sum (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : H1 AbsGalQ2 V)
    {ι : Type*} (s : Finset ι) (U : ι → Subgroup AbsGalQ2)
    (hfin : ∀ o ∈ s, Finite (AbsGalQ2 ⧸ U o))
    (hopen : ∀ o ∈ s, IsOpen (U o : Set AbsGalQ2))
    (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2)
    (hZ2 : ∀ o ∈ s, inner o ∈ Z2 ↥(U o) (ZMod 2))
    (hexp : Q0loc D dat ρ x
      = ∑ o ∈ s, iotaF D (H2ofFun AbsGalQ2 (cor2Fun (U o) (inner o))))
    (hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0) :
    Q0loc D dat ρ x = 0 := by
  rw [hexp]
  refine Finset.sum_eq_zero fun o ho => ?_
  haveI := hfin o ho
  rw [H2ofFun_cor2Fun_eq_zero_of_H2_eq_zero (U o) (hopen o ho) (inner o) (hZ2 o ho)
    (hvanish o ho), map_zero]

end Assembly

/-! ## Additivity backbone: reducing `hexp` to the raw cochain-level orbit decomposition

`hexp` (the monomial expansion) is `Q⁰_loc x = Σ_orbit iotaF(H2ofFun(cor2Fun …))`.  Since
`Q⁰_loc x = iotaF(H2ofFun(graphPullback dat ρ (out x)))` by definition and `iotaF` is additive,
`hexp` follows once (a) `graphPullback dat ρ (out x)` decomposes as a **sum of per-orbit
2-cocycles** `Σ_o φ_o` (the genuine combinatorial core — "gap 2", the paper's `q∘p` monomial
expansion via Lemma 6.14 + the datum decomposition `datW = Σ orbitDatum`) and (b) each `φ_o` is
cohomologous to the corresponding `cor2Fun (U_o) (inner_o)` (Lemma 6.15, banked).  The additivity
of `iotaF ∘ H2ofFun` on cocycles is the reusable plumbing, isolated here. -/

section Additivity

open SectionSix

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- `H²ofFun` is additive on a finite sum of continuous 2-cocycles. -/
theorem H2ofFun_sum_of_mem_Z2 {ι : Type*} (s : Finset ι) (φ : ι → G × G → ZMod 2) :
    (∀ i ∈ s, φ i ∈ Z2 G (ZMod 2)) →
      H2ofFun G (∑ i ∈ s, φ i) = ∑ i ∈ s, H2ofFun G (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.sum_empty, Finset.sum_empty, H2ofFun_of_mem (zero_mem _)]
    exact map_zero _
  | @insert a s ha ih =>
    intro h
    have hmem_a : φ a ∈ Z2 G (ZMod 2) := h a (Finset.mem_insert_self a s)
    have hmem_s : ∀ i ∈ s, φ i ∈ Z2 G (ZMod 2) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hsum_s : (∑ i ∈ s, φ i) ∈ Z2 G (ZMod 2) := sum_mem hmem_s
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H2ofFun_of_mem (add_mem hmem_a hsum_s),
      H2ofFun_of_mem hmem_a, ← ih hmem_s, H2ofFun_of_mem hsum_s, ← map_add]
    rfl

end Additivity

/-! ## The `hexp` reducer and the full f2 reducer -/

section Reducer

open SectionSix

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **The `hexp` producer** (P-15f2): the monomial expansion in cochain-level form.  If the
graph pullback of the base class decomposes as a finite sum of per-orbit `2`-cocycles `φ_o`
(`hdecomp` — the combinatorial "gap 2") and each `φ_o` is cohomologous to `cor2Fun (U_o) (inner_o)`
(`hcoh` — Lemma 6.15, banked), then `Q⁰_loc x` is the orbit sum `hexp` consumed by
`Q0loc_vanish_of_orbit_sum`.  Pure additivity plumbing (`H2ofFun_sum_of_mem_Z2` + `iotaF`'s
`map_sum`); isolates the raw decomposition `hdecomp` as the sole remaining combinatorial input. -/
theorem Q0loc_eq_orbit_sum_of_decomp (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : H1 AbsGalQ2 V)
    {ι : Type*} (s : Finset ι) (φ : ι → AbsGalQ2 × AbsGalQ2 → ZMod 2)
    (hφZ2 : ∀ o ∈ s, φ o ∈ Z2 AbsGalQ2 (ZMod 2))
    (hdecomp : graphPullback dat ρ (Quotient.out x).1 = ∑ o ∈ s, φ o)
    (U : ι → Subgroup AbsGalQ2) (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2)
    (hcoh : ∀ o ∈ s, H2ofFun AbsGalQ2 (φ o) = H2ofFun AbsGalQ2 (cor2Fun (U o) (inner o))) :
    Q0loc D dat ρ x = ∑ o ∈ s, iotaF D (H2ofFun AbsGalQ2 (cor2Fun (U o) (inner o))) := by
  show iotaF D (H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1)) = _
  rw [hdecomp, H2ofFun_sum_of_mem_Z2 s φ hφZ2, map_sum]
  exact Finset.sum_congr rfl fun o ho => congrArg (iotaF D) (hcoh o ho)

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **The full P-15f2 reducer** (`lemma_6_17_vanish` modulo the monomial expansion): given the raw
per-orbit cochain decomposition `hdecomp`, the Lemma-6.15 cohomologies `hcoh`, and the deep-class
per-orbit vanishing `hvanish` (free/square = `cup_deepClasses`, involution = `lemma_6_16`),
`Q⁰_loc x = 0`.  Composes `Q0loc_eq_orbit_sum_of_decomp` (→ `hexp`) with
`Q0loc_vanish_of_orbit_sum`.  The **sole remaining input** for `lemma_6_17_vanish` is `hdecomp` —
the `q∘p` monomial expansion over the regular module (Lemma 6.14 + the datum decomposition). -/
theorem Q0loc_vanish_of_decomp (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : H1 AbsGalQ2 V)
    {ι : Type*} (s : Finset ι) (φ : ι → AbsGalQ2 × AbsGalQ2 → ZMod 2)
    (hφZ2 : ∀ o ∈ s, φ o ∈ Z2 AbsGalQ2 (ZMod 2))
    (hdecomp : graphPullback dat ρ (Quotient.out x).1 = ∑ o ∈ s, φ o)
    (U : ι → Subgroup AbsGalQ2) (hfin : ∀ o ∈ s, Finite (AbsGalQ2 ⧸ U o))
    (hopen : ∀ o ∈ s, IsOpen (U o : Set AbsGalQ2))
    (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2) (hZ2 : ∀ o ∈ s, inner o ∈ Z2 ↥(U o) (ZMod 2))
    (hcoh : ∀ o ∈ s, H2ofFun AbsGalQ2 (φ o) = H2ofFun AbsGalQ2 (cor2Fun (U o) (inner o)))
    (hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0) :
    Q0loc D dat ρ x = 0 :=
  Q0loc_vanish_of_orbit_sum D dat ρ x s U hfin hopen inner hZ2
    (Q0loc_eq_orbit_sum_of_decomp D dat ρ x s φ hφZ2 hdecomp U inner hcoh) hvanish

end Reducer

/-! ## §6.2 datum-additivity assembly: from the datum-level orbit decomposition to `hdecomp`

The paper assembles the multi-orbit contribution as **additivity of `graphPullback` in the datum**
(the Lemma-6.15 deviation note, `SectionSix.lean:646`): once the invariant datum on the regular
module decomposes as a pointwise (block) sum of the per-orbit datums `datW = Σ_o datum_o` (each an
orbit datum of §6.2 extended by zero to the regular module), its graph pullback is the sum of the
per-orbit pullbacks — each of which is a banked Lemma-6.15 corestriction.  This section supplies
that additivity brick and the resulting **datum-level** reducer, landing the sole remaining input
of `lemma_6_17_vanish` (through the Lemma-6.14 transport) on the *datum identity*
`datW = Σ_o datf_o` and the banked 6.15 cohomologies. -/

section DatumSum

variable {C : Type*} [Group C]
variable {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- **Pointwise (block) sum of factor-set datums** (§6.2 assembly): the datum whose factor set and
central corrections are the coordinatewise finite sums.  This is the datum-level form of the
paper's multi-orbit decomposition `datW = Σ_o datum_o` (each `datum_o` an orbit datum extended by
zero to the regular module `𝔽₂[H_V]^N`). -/
def sumDatum {ι : Type*} (s : Finset ι) (datf : ι → FactorSet C V) : FactorSet C V where
  f v w := ∑ o ∈ s, (datf o).f v w
  m c v := ∑ o ∈ s, (datf o).m c v

/-- **Additivity of `graphPullback` in the datum**: the graph pullback of a pointwise datum sum is
the sum of the graph pullbacks.  This is the paper's "multi-orbit assembly = additivity of
`graphPullback` in the datum" (Lemma-6.15 deviation note), which turns a datum-level orbit
decomposition `datW = Σ_o datf_o` into the cochain-level `hdecomp` consumed by
`Q0loc_vanish_of_decomp`. -/
theorem graphPullback_sumDatum {ι : Type*} (s : Finset ι) (datf : ι → FactorSet C V)
    {Γ : Type*} (ρ : Γ → C) (b : Γ → V) :
    graphPullback (sumDatum s datf) ρ b = ∑ o ∈ s, graphPullback (datf o) ρ b := by
  funext p
  rw [Finset.sum_apply]
  show (∑ o ∈ s, (datf o).f (b p.1) (ρ p.1 • b p.2)) + (∑ o ∈ s, (datf o).m (ρ p.1) (b p.2))
      = ∑ o ∈ s, ((datf o).f (b p.1) (ρ p.1 • b p.2) + (datf o).m (ρ p.1) (b p.2))
  rw [Finset.sum_add_distrib]

end DatumSum

section DatumReducer

open SectionSix

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

omit [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **The datum-level P-15f2 reducer** (`lemma_6_17_vanish` modulo the §6.2 datum decomposition):
if the (regular-module) datum decomposes as a pointwise sum of per-orbit equivariant factor sets
`dat = Σ_o datf_o` (`hdat_eq` — the datum-level "gap 2", `sumDatum`), each per-orbit pullback is
cohomologous to its Lemma-6.15 corestriction (`hcoh` — free/square = eq. (103)/(104), involution =
eq. (105), all banked in `ShapiroLedger`), and each corestriction's inner cocycle vanishes in the
subgroup's `H²` (`hvanish` — deep-class (94)/6.16), then `Q⁰_loc x = 0`.

Composes the datum-additivity brick `graphPullback_sumDatum` (turning `hdat_eq` into the cochain
decomposition `hdecomp`) with the full reducer `Q0loc_vanish_of_decomp`; per-orbit `Z²`-membership
is discharged from the equivariant-factor-set hypotheses via `graphPullback_mem_Z2`.  Applied at the
regular module `V := 𝔽₂[H_V]^N` after the Lemma-6.14 transport `Q⁰_loc dat ρ x = Q⁰_loc datW ρ ι_*x`,
the **sole remaining input** for `lemma_6_17_vanish` is `hdat_eq` — the datum-level orbit
decomposition of §6.2. -/
theorem Q0loc_vanish_of_datum_decomp (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (x : H1 AbsGalQ2 V)
    {ι : Type*} (s : Finset ι) (datf : ι → FactorSet C V)
    (qf : ι → V → ZMod 2) (hdatf : ∀ o ∈ s, IsEquivariantFactorSet (qf o) (datf o))
    (hdat_eq : dat = sumDatum s datf)
    (U : ι → Subgroup AbsGalQ2) (hfin : ∀ o ∈ s, Finite (AbsGalQ2 ⧸ U o))
    (hopen : ∀ o ∈ s, IsOpen (U o : Set AbsGalQ2))
    (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2) (hZ2 : ∀ o ∈ s, inner o ∈ Z2 ↥(U o) (ZMod 2))
    (hcoh : ∀ o ∈ s, H2ofFun AbsGalQ2 (graphPullback (datf o) ρ (Quotient.out x).1)
      = H2ofFun AbsGalQ2 (cor2Fun (U o) (inner o)))
    (hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0) :
    Q0loc D dat ρ x = 0 := by
  refine Q0loc_vanish_of_decomp D dat ρ x s
    (fun o => graphPullback (datf o) ρ (Quotient.out x).1)
    (fun o ho => graphPullback_mem_Z2 (datf o) (hdatf o ho) ρ hρ (Quotient.out x))
    ?_ U hfin hopen inner hZ2 hcoh hvanish
  rw [hdat_eq]
  exact graphPullback_sumDatum s datf (⇑ρ) (Quotient.out x).1

end DatumReducer

/-! ## `Q⁰_loc` datum-independence, reduced to its Lemma-6.1/6.4 core

The orbit route needs the base connecting map computed with the *orbit-sum* datum on the regular
module, but `lemma_6_17_vanish` is stated for an **arbitrary** equivariant factor set `dat` for `q`.
Bridging the two requires **`Q⁰_loc` datum-independence**: any two equivariant factor sets for the
same form give the same `Q⁰_loc` (Lemma 6.1 — "different equivariant lifts give cohomologous
cocycles" — feeding Lemma 6.4).  Only a *special isometry case* is banked
(`UnramifiedModel.graphPullback_comap_smul_sub_mem_B2`, comap along a `q`-isometry `g₀ ∈ C`).

This section reduces the general statement to a single crisp cohomological input, exactly as the
rest of f2 was reduced: the **difference datum** `diffDatum dat1 dat2` (pointwise 𝔽₂-sum, = the
char-2 difference) is an equivariant factor set for the **zero form**
(`isEquivariantFactorSet_diffDatum`), and `graphPullback` is additive along it
(`graphPullback_diffDatum`), so datum-independence follows once the graph pullback of a **zero-form**
factor set is a coboundary (`hcore` — *DI-core*, the isolated Lemma-6.1/6.4 heart: the class
`[κ⁰]` of a zero-form factor set on `V ⋊ C` is trivial, so its graph pullback lands in `B²`).  DI-core
is **not** discharged here: the coboundary `Λ(g) = Δφ(b g)` needs a quadratic refinement `Δφ` of the
difference (which *exists* — the two data share the polar, so `Δf` is a symmetric coboundary over 𝔽₂)
corrected against the C-equivariance defect `Δm` (an `H¹(C, V*)` obstruction — the genuine Lemma
6.1/6.4 content).  It is stated as the parametric hypothesis so consumers and the eventual proof
share the exact interface; see `docs/p15f2-option1-scoping.md`. -/

section DatumIndependence

open SectionSix QuadraticFp2

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- The **difference datum** of two factor sets: the pointwise 𝔽₂-sum of their factor sets and
central corrections.  Over 𝔽₂ this is simultaneously the sum and the difference (`sub = add`), and
is the object measuring how `Q⁰_loc` can change with the datum choice. -/
def diffDatum (dat1 dat2 : FactorSet C V) : FactorSet C V where
  f v w := dat1.f v w + dat2.f v w
  m c v := dat1.m c v + dat2.m c v

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **Additivity of `graphPullback` along the difference datum**: `graphPullback` is 𝔽₂-linear in the
datum, so the pullback of `diffDatum dat1 dat2` is the sum of the two pullbacks. -/
theorem graphPullback_diffDatum (dat1 dat2 : FactorSet C V) {Γ : Type*} (ρ : Γ → C) (b : Γ → V) :
    graphPullback (diffDatum dat1 dat2) ρ b = graphPullback dat1 ρ b + graphPullback dat2 ρ b := by
  funext p
  show (dat1.f (b p.1) (ρ p.1 • b p.2) + dat2.f (b p.1) (ρ p.1 • b p.2))
      + (dat1.m (ρ p.1) (b p.2) + dat2.m (ρ p.1) (b p.2))
    = (dat1.f (b p.1) (ρ p.1 • b p.2) + dat1.m (ρ p.1) (b p.2))
      + (dat2.f (b p.1) (ρ p.1 • b p.2) + dat2.m (ρ p.1) (b p.2))
  ring

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **The difference of two equivariant factor sets for the same form is one for the zero form**
(Lemma 6.1, gauge level): both share the form `q`, so their pointwise 𝔽₂-difference kills the
diagonal and the polar, leaving an equivariant factor set for `0`.  This is the datum whose graph
pullback measures the `Q⁰_loc` datum-defect. -/
theorem isEquivariantFactorSet_diffDatum {q : V → ZMod 2} {dat1 dat2 : FactorSet C V}
    (hdat1 : IsEquivariantFactorSet q dat1) (hdat2 : IsEquivariantFactorSet q dat2) :
    IsEquivariantFactorSet (fun _ => (0 : ZMod 2)) (diffDatum dat1 dat2) where
  f_cocycle v w x := by
    show (dat1.f (v + w) x + dat2.f (v + w) x) + (dat1.f v w + dat2.f v w)
        = (dat1.f v (w + x) + dat2.f v (w + x)) + (dat1.f w x + dat2.f w x)
    linear_combination (norm := ring_nf) hdat1.f_cocycle v w x + hdat2.f_cocycle v w x
  f_diag v := by
    show dat1.f v v + dat2.f v v = 0
    rw [hdat1.f_diag, hdat2.f_diag]; exact CharTwo.add_self_eq_zero _
  f_polar v w := by
    show (dat1.f v w + dat2.f v w) + (dat1.f w v + dat2.f w v) = polar (fun _ => (0 : ZMod 2)) v w
    have hp : polar (fun _ => (0 : ZMod 2)) v w = 0 := by simp [polar]
    rw [hp]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hdat1.f_polar v w + hdat2.f_polar v w
  f_zero_left v := by
    show dat1.f 0 v + dat2.f 0 v = 0
    rw [hdat1.f_zero_left, hdat2.f_zero_left, add_zero]
  f_zero_right v := by
    show dat1.f v 0 + dat2.f v 0 = 0
    rw [hdat1.f_zero_right, hdat2.f_zero_right, add_zero]
  m_quad c v w := by
    show (dat1.m c (v + w) + dat2.m c (v + w)) + (dat1.m c v + dat2.m c v)
        + (dat1.m c w + dat2.m c w)
      = (dat1.f (c • v) (c • w) + dat2.f (c • v) (c • w)) + (dat1.f v w + dat2.f v w)
    linear_combination (norm := ring_nf) hdat1.m_quad c v w + hdat2.m_quad c v w
  m_mul c d v := by
    show dat1.m (c * d) v + dat2.m (c * d) v
        = (dat1.m c (d • v) + dat2.m c (d • v)) + (dat1.m d v + dat2.m d v)
    linear_combination (norm := ring_nf) hdat1.m_mul c d v + hdat2.m_mul c d v
  m_one v := by
    show dat1.m 1 v + dat2.m 1 v = 0
    rw [hdat1.m_one, hdat2.m_one, add_zero]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **`Q⁰_loc` datum-independence, parametric on DI-core** (Lemma 6.1/6.4): if the graph pullback of
the zero-form difference datum lands in `B²` (`hcore` — the isolated cohomological heart), then
`Q⁰_loc` agrees for the two equivariant factor sets `dat1`, `dat2` of the same form `q`.  Composes
`graphPullback_diffDatum` (𝔽₂-linearity, with `sub = add` in char 2) and `H2ofFun_eq_of_sub_mem_B2`.
This is the bridge that lets `lemma_6_17_vanish` (stated for arbitrary `dat`) be reduced to the
orbit-sum datum on the regular module. -/
theorem Q0loc_datum_indep_of_core (D : TateDuality 2) (dat1 dat2 : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : H1 AbsGalQ2 V)
    (hcore : graphPullback (diffDatum dat1 dat2) ρ (Quotient.out x).1 ∈ B2 AbsGalQ2 (ZMod 2)) :
    Q0loc D dat1 ρ x = Q0loc D dat2 ρ x := by
  show iotaF D (H2ofFun AbsGalQ2 (graphPullback dat1 ρ (Quotient.out x).1))
      = iotaF D (H2ofFun AbsGalQ2 (graphPullback dat2 ρ (Quotient.out x).1))
  refine congrArg _ (H2ofFun_eq_of_sub_mem_B2 ?_)
  have hlin : graphPullback dat1 ρ (Quotient.out x).1 - graphPullback dat2 ρ (Quotient.out x).1
      = graphPullback (diffDatum dat1 dat2) ρ (Quotient.out x).1 := by
    rw [graphPullback_diffDatum]
    funext p
    simp only [Pi.sub_apply, Pi.add_apply, CharTwo.sub_eq_add]
  rw [hlin]; exact hcore

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **(a1) the C-independent quadratic refinement** (P-15f2a increment A): a zero-form equivariant
factor set `Δdat` admits a **quadratic refinement** `Δφ` with polar `Δdat.f`, i.e.
`Δφ(u+w) = Δφ u + Δφ w + Δdat.f u w` (the identity `(Q)`).  The zero form makes `Δdat.f` symmetric
(`f_polar`) with zero diagonal (`f_diag`), so the twisted extension `ZFExt` — addition
`(v,a)+(w,b) = (v+w, a+b+Δdat.f v w)` — is an elementary abelian `2`-group (`hV2`), hence an
`𝔽₂`-vector space; its `base`-projection is a surjective `𝔽₂`-linear map, and any linear right
inverse `s` gives `Δφ v := (s v).fib` with `(Q)` (from `s` additive).  C-independent (no `Δm`); the
equivariance defect is corrected in increment B. -/
theorem exists_refinement_of_zero_form (Δdat : FactorSet C V)
    (hΔ : IsEquivariantFactorSet (fun _ => (0 : ZMod 2)) Δdat) (hV2 : ∀ v : V, v + v = 0) :
    ∃ Δφ : V → ZMod 2, ∀ u w : V, Δφ (u + w) = Δφ u + Δφ w + Δdat.f u w := by
  classical
  have hdiag : ∀ v : V, Δdat.f v v = 0 := hΔ.f_diag
  have h0l : ∀ v : V, Δdat.f 0 v = 0 := hΔ.f_zero_left
  have hsymm : ∀ v w : V, Δdat.f v w = Δdat.f w v := by
    intro v w
    have h := hΔ.f_polar v w
    have hp0 : polar (fun _ => (0 : ZMod 2)) v w = 0 := by simp [polar]
    rw [hp0] at h
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV2 v)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  letI addInst : Add (ZFExt V) :=
    ⟨fun p q => ⟨p.base + q.base, p.fib + q.fib + Δdat.f p.base q.base⟩⟩
  letI zeroInst : Zero (ZFExt V) := ⟨⟨0, 0⟩⟩
  letI negInst : Neg (ZFExt V) := ⟨id⟩
  have hassoc : ∀ p q r : ZFExt V, p + q + r = p + (q + r) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
    refine ZFExt.ext (add_assoc a b c) ?_
    show x + y + Δdat.f a b + z + Δdat.f (a + b) c
        = x + (y + z + Δdat.f b c) + Δdat.f a (b + c)
    linear_combination (norm := ring_nf) hΔ.f_cocycle a b c
  have hzero_add : ∀ p : ZFExt V, 0 + p = p := by
    rintro ⟨a, x⟩
    refine ZFExt.ext (zero_add a) ?_
    show (0 : ZMod 2) + x + Δdat.f 0 a = x
    rw [h0l]; ring
  have hneg_add : ∀ p : ZFExt V, -p + p = 0 := by
    rintro ⟨a, x⟩
    refine ZFExt.ext (hV2 a) ?_
    show x + x + Δdat.f a a = (0 : ZMod 2)
    rw [hdiag, add_zero]; exact CharTwo.add_self_eq_zero x
  letI grp : AddCommGroup (ZFExt V) :=
    { AddGroup.ofLeftAxioms hassoc hzero_add hneg_add with
      add_comm := by
        rintro ⟨a, x⟩ ⟨b, y⟩
        refine ZFExt.ext (add_comm a b) ?_
        show x + y + Δdat.f a b = y + x + Δdat.f b a
        rw [hsymm a b]; ring }
  have htor : ∀ p : ZFExt V, p + p = 0 := fun p => neg_add_cancel p
  letI mod : Module (ZMod 2) (ZFExt V) :=
    AddCommGroup.zmodModule (fun p => by rw [two_nsmul]; exact htor p)
  let π : ZFExt V →ₗ[ZMod 2] V :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' ZFExt.base (fun _ _ => rfl))
  have hπsurj : Function.Surjective π := fun v => ⟨⟨v, 0⟩, rfl⟩
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπsurj)
  have hsbase : ∀ v, (s v).base = v := fun v => by
    have := LinearMap.congr_fun hs v; simpa [π] using this
  refine ⟨fun v => (s v).fib, fun u w => ?_⟩
  show (s (u + w)).fib = (s u).fib + (s w).fib + Δdat.f u w
  rw [congrArg ZFExt.fib (map_add s u w)]
  show (s u).fib + (s w).fib + Δdat.f (s u).base (s w).base
      = (s u).fib + (s w).fib + Δdat.f u w
  rw [hsbase u, hsbase w]

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V]
  [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **Step A of the equivariance correction** (P-15f2a, averaging kernel): for a right `1`-cocycle
defect `D` (`hDcoc`) on an odd subgroup `I`, the banked average `L = Σ_{i∈I} D i` satisfies
`L(j•v) + L v = D j v` for `j ∈ I`.  Cocycle expansion `D(ij) = D i (j•v) + D j v`, `mulRight`
reindexing of `Σ_i D(ij)` back to `L`, and `|I|` odd in `𝔽₂` collapse the correction. -/
private lemma defect_avg_smul (D : C → V → ZMod 2)
    (hDcoc : ∀ (c d : C) (v : V), D (c * d) v = D c (d • v) + D d v)
    (I : Subgroup C) [Fintype ↥I] (hoddsmul : ∀ x : ZMod 2, Fintype.card ↥I • x = x)
    (j : ↥I) (v : V) :
    (∑ i : ↥I, D (i : C) ((j : C) • v)) + ∑ i : ↥I, D (i : C) v = D (j : C) v := by
  have e1 : (∑ i : ↥I, D (i : C) ((j : C) • v))
      = (∑ i : ↥I, D ((i : C) * (j : C)) v) + ∑ _i : ↥I, D (j : C) v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hDcoc (i : C) (j : C) v
  have e2 : (∑ i : ↥I, D ((i : C) * (j : C)) v) = ∑ i : ↥I, D (i : C) v := by
    refine Fintype.sum_equiv (Equiv.mulRight j) _ _ fun i => ?_
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul]
  have e3 : (∑ _i : ↥I, D (j : C) v) = D (j : C) v := by
    rw [Finset.sum_const, Finset.card_univ, hoddsmul]
  rw [e1, e2, e3]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V]
  [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **The `H¹`-correction kills the defect** (P-15f2a increment B, Steps A+B core): for an additive
(`hDadd`) right `1`-cocycle (`hDcoc`) defect `D` with banked average `L = Σ_{i∈I} D i` over an odd
normal subgroup `I ◁ C` acting fixed-point-freely (`hVI : V^I = 0`), the corrected defect
`D' c v = D c v + (L(c•v) + L v)` vanishes identically.  **Step A** (`defect_avg_smul`) makes `D'`
vanish on `I`; **Step B**: normality makes `D'` `I`-invariant, so
`D' c v = Σ_{i∈I} D' c (i•v) = D' c (Σ i•v) = D' c 0 = 0` since `Σ_{i∈I} i•v ∈ V^I = 0`.
No general `H¹(C,V*)` theory. -/
private lemma corrected_defect_vanishes (D : C → V → ZMod 2)
    (hDadd : ∀ (c : C) (v w : V), D c (v + w) = D c v + D c w)
    (hDcoc : ∀ (c d : C) (v : V), D (c * d) v = D c (d • v) + D d v)
    (I : Subgroup C) [Fintype ↥I] (hIn : I.Normal) (hodd : Odd (Nat.card I))
    (hVI : ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0)
    (L : V → ZMod 2) (hLdef : ∀ v, L v = ∑ i : ↥I, D (i : C) v) (c : C) (v : V) :
    D c v + (L (c • v) + L v) = 0 := by
  have hoddsmul : ∀ x : ZMod 2, Fintype.card ↥I • x = x := by
    intro x
    have h1 : (Fintype.card ↥I : ZMod 2) = 1 := by
      have : Odd (Fintype.card ↥I) := by rwa [Nat.card_eq_fintype_card] at hodd
      obtain ⟨k, hk⟩ := this; rw [hk]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
    rw [nsmul_eq_mul, h1, one_mul]
  have hLadd : ∀ x y, L (x + y) = L x + L y := by
    intro x y
    rw [hLdef, hLdef, hLdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hDadd (i : C) x y
  set D' : C → V → ZMod 2 := fun c v => D c v + (L (c • v) + L v) with hD'
  have hD'add : ∀ (c : C) (x y : V), D' c (x + y) = D' c x + D' c y := by
    intro c x y
    show D c (x + y) + (L (c • (x + y)) + L (x + y))
        = (D c x + (L (c • x) + L x)) + (D c y + (L (c • y) + L y))
    rw [hDadd, smul_add, hLadd, hLadd]; ring
  have hD'I : ∀ (j : ↥I) (w : V), D' (j : C) w = 0 := by
    intro j w
    show D (j : C) w + (L ((j : C) • w) + L w) = 0
    have hs : L ((j : C) • w) + L w = D (j : C) w := by
      rw [hLdef, hLdef]; exact defect_avg_smul D hDcoc I hoddsmul j w
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hs
  have hD'coc : ∀ (a d : C) (w : V), D' (a * d) w = D' a (d • w) + D' d w := by
    intro a d w
    show D (a * d) w + (L ((a * d) • w) + L w)
        = (D a (d • w) + (L (a • d • w) + L (d • w))) + (D d w + (L (d • w) + L w))
    rw [mul_smul]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hDcoc a d w
  have hinv : ∀ (a : C) (i : ↥I) (w : V), D' a ((i : C) • w) = D' a w := by
    intro a i w
    have hmem : a * (i : C) * a⁻¹ ∈ I := hIn.conj_mem _ i.2 a
    set i' : ↥I := ⟨a * (i : C) * a⁻¹, hmem⟩ with hi'
    have hci : a * (i : C) = (i' : C) * a := by
      show a * (i : C) = a * (i : C) * a⁻¹ * a
      group
    have h1 := hD'coc a (i : C) w
    have h2 := hD'coc (i' : C) a w
    rw [hci] at h1
    rw [hD'I i w, add_zero] at h1
    rw [hD'I i' (a • w), zero_add] at h2
    rw [h1] at h2; exact h2
  show D' c v = 0
  set S : V := ∑ i : ↥I, (i : C) • v with hS
  have hSfix : ∀ j ∈ I, j • S = S := by
    intro j hj
    have step : j • S = ∑ i : ↥I, ((⟨j, hj⟩ * i : ↥I) : C) • v := by
      rw [hS, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← mul_smul, Subgroup.coe_mul]
    rw [step, hS]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨j, hj⟩ : ↥I)) _ _ fun i => rfl
  have hS0 : S = 0 := hVI S hSfix
  let hom : V →+ ZMod 2 := AddMonoidHom.mk' (D' c) (fun a b => hD'add c a b)
  have hmapsum : D' c S = ∑ i : ↥I, D' c ((i : C) • v) := by
    show hom S = ∑ i : ↥I, hom ((i : C) • v)
    rw [hS, map_sum]
  calc D' c v = ∑ _i : ↥I, D' c v := by rw [Finset.sum_const, Finset.card_univ, hoddsmul]
    _ = ∑ i : ↥I, D' c ((i : C) • v) := (Finset.sum_congr rfl fun i _ => hinv c i v).symm
    _ = D' c S := hmapsum.symm
    _ = D' c 0 := by rw [hS0]
    _ = 0 := hom.map_zero

omit [TopologicalSpace C] [DiscreteTopology C] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **(a2) the equivariance correction** (P-15f2a increment B): given the C-structure of an odd
normal subgroup `I ◁ C` acting fixed-point-freely (`hVI : V^I = 0`), the quadratic refinement of
increment A can be corrected to also satisfy the **equivariance-defect identity** `(E)`
`Δφ(c•v) = Δφ v + Δdat.m c v`, giving the full refinement `(Q) ∧ (E)` that
`graphPullback_mem_B2_of_refinement` consumes.

Proof (the banked f1 averaging pattern, cf. `inflationVanishes_of_oddNormal`): the defect
`D c v = Δφ₀(c•v) + Δφ₀ v + Δm c v` is additive in `v` (`(Q)` + `m_quad`) and a right `1`-cocycle in
`c` (`m_mul`).  **Step A**: `L₀ = Σ_{i∈I} D i` kills the defect on `I` (cocycle expansion +
`mulRight` reindex + `|I|` odd in `𝔽₂`), and `Δφ = Δφ₀ + L₀` keeps `(Q)` (`L₀` additive).  **Step B**:
normality makes the corrected defect `D'` `I`-invariant (`D' c (i•v) = D' c v` via
`c i = i' c`, `i' = c i c⁻¹ ∈ I`), whence `D' c v = Σ_{i∈I} D' c (i•v) = D' c (Σ_{i∈I} i•v) = D' c 0 = 0`
since `Σ_{i∈I} i•v ∈ V^I = 0`.  No general `H¹(C,V*)` theory. -/
theorem exists_equivariant_refinement (Δdat : FactorSet C V)
    (hΔ : IsEquivariantFactorSet (fun _ => (0 : ZMod 2)) Δdat) (hV2 : ∀ v : V, v + v = 0)
    (I : Subgroup C) (hIn : I.Normal) (hodd : Odd (Nat.card I))
    (hVI : ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0) :
    ∃ Δφ : V → ZMod 2, (∀ u w : V, Δφ (u + w) = Δφ u + Δφ w + Δdat.f u w) ∧
      (∀ (c : C) (v : V), Δφ (c • v) = Δφ v + Δdat.m c v) := by
  obtain ⟨φ0, hQ0⟩ := exists_refinement_of_zero_form Δdat hΔ hV2
  have hmmul := hΔ.m_mul
  haveI : Fintype ↥I := Fintype.ofFinite _
  set D : C → V → ZMod 2 := fun c v => φ0 (c • v) + φ0 v + Δdat.m c v with hD
  have hDadd : ∀ (c : C) (v w : V), D c (v + w) = D c v + D c w := by
    intro c v w
    have h1 := hQ0 (c • v) (c • w); have h2 := hQ0 v w; have h3 := hΔ.m_quad c v w
    show φ0 (c • (v + w)) + φ0 (v + w) + Δdat.m c (v + w)
        = (φ0 (c • v) + φ0 v + Δdat.m c v) + (φ0 (c • w) + φ0 w + Δdat.m c w)
    rw [smul_add]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 + h2 + h3
  have hDcoc : ∀ (c d : C) (v : V), D (c * d) v = D c (d • v) + D d v := by
    intro c d v
    show φ0 ((c * d) • v) + φ0 v + Δdat.m (c * d) v
      = (φ0 (c • d • v) + φ0 (d • v) + Δdat.m c (d • v)) + (φ0 (d • v) + φ0 v + Δdat.m d v)
    rw [mul_smul, hmmul c d v]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
  set L : V → ZMod 2 := fun v => ∑ i : ↥I, D (i : C) v with hL
  have hLadd : ∀ v w, L (v + w) = L v + L w := by
    intro v w
    show (∑ i : ↥I, D (i : C) (v + w)) = (∑ i : ↥I, D (i : C) v) + ∑ i : ↥I, D (i : C) w
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => hDadd (i : C) v w
  set Δφ : V → ZMod 2 := fun v => φ0 v + L v with hΔφ
  have hQ : ∀ u w, Δφ (u + w) = Δφ u + Δφ w + Δdat.f u w := by
    intro u w
    show φ0 (u + w) + L (u + w) = (φ0 u + L u) + (φ0 w + L w) + Δdat.f u w
    rw [hQ0 u w, hLadd u w]; ring
  refine ⟨Δφ, hQ, fun c v => ?_⟩
  have hmain := corrected_defect_vanishes D hDadd hDcoc I hIn hodd hVI L
    (fun v => congrFun hL v) c v
  show φ0 (c • v) + L (c • v) = φ0 v + L v + Δdat.m c v
  have h0 : φ0 (c • v) + φ0 v + Δdat.m c v + (L (c • v) + L v) = 0 := hmain
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h0

/-! ### f2a (P-15f2a): the DI-core cochain assembly — reduced to the existence of a refinement

DI-core (`graphPullback (zero-form factor set) ∈ B²`) has an explicit coboundary witness
`Λ(g) = Δφ(b g)` for a **quadratic refinement** `Δφ : V → 𝔽₂` of the datum, i.e. a `Δφ` with polar
`Δdat.f` (`hQ`: `Δφ(u+w) = Δφ u + Δφ w + Δf u w`) and equivariance defect `Δdat.m`
(`hE`: `Δφ(c•v) = Δφ v + Δm c v`).  The verification `δ¹Λ = graphPullback Δdat` is the char-2 identity
below.  This lemma discharges the *cochain heart*; the **sole remaining input** for full DI-core /
`Q0loc_datum_indep` is the **existence** of such a `Δφ` for the difference datum — the
`H²(V;𝔽₂)`-splitting `[Δf]=0` (free: `Δf` has zero diagonal) plus the `H¹(C,V*)` equivariance
correction (`docs/p15f2-option1-scoping.md` §P0, sub-bricks a1/a2). -/
omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
theorem graphPullback_mem_B2_of_refinement (Δdat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (Δφ : V → ZMod 2)
    (hQ : ∀ u w : V, Δφ (u + w) = Δφ u + Δφ w + Δdat.f u w)
    (hE : ∀ (c : C) (v : V), Δφ (c • v) = Δφ v + Δdat.m c v)
    (b : Z1 AbsGalQ2 V) :
    graphPullback Δdat ρ b.1 ∈ B2 AbsGalQ2 (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine AddSubgroup.mem_map.mpr ⟨fun g => Δφ (b.1 g), ?_, ?_⟩
  · exact mem_C1_iff.mpr ((continuous_of_discreteTopology (f := Δφ)).comp hbc)
  · funext p
    obtain ⟨g, h⟩ := p
    have hbgh : b.1 (g * h) = b.1 g + ρ g • b.1 h := by rw [hb g h, hρ]
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, absGal_smul_zmodTwo, graphPullback]
    rw [hbgh]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hQ (b.1 g) (ρ g • b.1 h) + hE (ρ g) (b.1 h)

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **`Q⁰_loc` datum-independence from a refinement** (P-15f2a capstone): a quadratic refinement `Δφ`
of the difference datum `diffDatum dat1 dat2` (with polar `hQ` and equivariance-defect `hE`) makes
`Q⁰_loc` agree for `dat1` and `dat2`.  Composes `graphPullback_mem_B2_of_refinement` (the coboundary)
with `Q0loc_datum_indep_of_core`.  The remaining f2a input is the *construction* of `Δφ` (the
`H²(V;𝔽₂)`-splitting + `H¹(C,V*)` correction). -/
theorem Q0loc_datum_indep_of_refinement (D : TateDuality 2) (dat1 dat2 : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (x : H1 AbsGalQ2 V) (Δφ : V → ZMod 2)
    (hQ : ∀ u w : V, Δφ (u + w) = Δφ u + Δφ w + (diffDatum dat1 dat2).f u w)
    (hE : ∀ (c : C) (v : V), Δφ (c • v) = Δφ v + (diffDatum dat1 dat2).m c v) :
    Q0loc D dat1 ρ x = Q0loc D dat2 ρ x :=
  Q0loc_datum_indep_of_core D dat1 dat2 ρ x
    (graphPullback_mem_B2_of_refinement (diffDatum dat1 dat2) ρ hρ Δφ hQ hE (Quotient.out x))

omit [DiscreteTopology C] [ContinuousSMul AbsGalQ2 V] in
/-- **(a3) `Q⁰_loc` datum-independence** (P-15f2a capstone): for two equivariant factor sets
`dat1`, `dat2` of the **same** form `q`, an odd normal subgroup `I ◁ C` acting fixed-point-freely
(`hVI : V^I = 0`) forces `Q⁰_loc dat1 = Q⁰_loc dat2`.  Composes `isEquivariantFactorSet_diffDatum`
(the difference is a zero-form datum) → `exists_equivariant_refinement` (the full `(Q)∧(E)` refinement,
increments A+B) → `Q0loc_datum_indep_of_refinement`.  This is the f2a deliverable; the tame
instantiation of `(I, hIn, hodd, hVI)` (e.g. `I = zpowers (c tameTau)`, via the banked producers
`tameInertia_normal` / `odd_orderOf_tameInertia` / `fixedByNormal_eq_bot`) stays with f2d. -/
theorem Q0loc_datum_indep (D : TateDuality 2) {q : V → ZMod 2}
    (dat1 dat2 : FactorSet C V)
    (hdat1 : IsEquivariantFactorSet q dat1) (hdat2 : IsEquivariantFactorSet q dat2)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (I : Subgroup C) (hIn : I.Normal) (hodd : Odd (Nat.card I))
    (hVI : ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0)
    (x : H1 AbsGalQ2 V) :
    Q0loc D dat1 ρ x = Q0loc D dat2 ρ x := by
  obtain ⟨Δφ, hQ, hE⟩ := exists_equivariant_refinement (diffDatum dat1 dat2)
    (isEquivariantFactorSet_diffDatum hdat1 hdat2) hV2 I hIn hodd hVI
  exact Q0loc_datum_indep_of_refinement D dat1 dat2 ρ hρ x Δφ hQ hE

end DatumIndependence

end OrbitVanish

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (103) = ⟦eq-shapirosquare⟧
  * eq. (105) = ⟦eq-shapiroevens⟧
  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
  * Lemma 6.14 = ⟦lem-regularrealization⟧
  * Lemma 6.15 = ⟦lem-orbitshapiro⟧
  * Lemma 6.16 = ⟦lem-evensvanish⟧
  * Lemma 6.17 = ⟦lem-shapirodet⟧
  * Lemma 6.4 = ⟦lem-detnormalizationindependence⟧
-/
