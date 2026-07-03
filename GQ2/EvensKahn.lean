import Mathlib
import GQ2.CupProduct
import GQ2.Kummer
import GQ2.Demushkin

/-!
# B9: corestriction, the index-two Evens norm, and eq. (111)'s ingredients  (ticket T-18)

Statement infrastructure for the paper's **Evens/Kahn/Kozlowski** leaf (**B9**): the paper's
eq. (111)

  `w(Tr_{L/k}⟨a⟩) = w(Tr_{L/k}⟨1⟩) · (1 + cor_{L/k}[a] + N^{Ev}_{L/k}([a]))`

(Kahn, Théorème 2 at the rank-1 form `⟨a⟩`, expanded through Evens' Theorem 1 for index 2;
the index-2 case is Kozlowski Thm 1.1) — truncated to degrees ≤ 2 and scoped to the concrete
diagonalizations the paper uses in Lemma 6.16.  The axiom itself
(`GQ2.evensKahn_dyadic`, the degree-1 and degree-2 components of (111)) lives in
`GQ2/Foundations/Axioms.lean`; this file provides all definitions and their well-formedness.

## What is defined (all *unconditional* constructions)

For a topological group `G`, an **open subgroup `U` of index 2** and a fixed `s ∉ U`, and a
continuous homomorphism `α : U → 𝔽₂` (a trivial-action 1-cocycle):

* `evensAux U s α : G → 𝔽₂` — the paper's normalized Shapiro cocycle component
  `b(γ)₁ = α(γ·s̃^{c(γ)})` of eq. (97) (`c(γ) = [γ ∉ U]`); the other component is
  **`bS U s α = evensAux U s α ∘ (s⁻¹·)`** (a simplification of (97) recorded here:
  `b(γ)_s = b(s⁻¹γ)₁`).
* `corFun U s α = b₁ + b_s` — the **degree-1 corestriction** cocycle (sum over the coset
  transversal `{1, s}`); `corFun_mem_Z1` packages it for `Z¹(G, 𝔽₂)`.
* `evensNormFun U s α : G × G → 𝔽₂` — the paper's **two-point graph cocycle** (98):
  `ν_α(γ,η) = b(γ)₁·b(η)_{γ̄⁻¹s} + ε(γ̄)·b(η)₁·b(η)_s`; `evensNormH2` packages its class in
  `H²(G,𝔽₂)`.  By the paper's Lemma 6.13 (eq. (99)) this class **is** the index-two Evens
  norm `N^{Ev}([α])` — we *define* the Evens norm by this cocycle, exactly as the plan
  prescribes ("transcribe (95)–(98) as the definition").
* Over `k` with algebraic closure `k̄` (T-13's setting): `kummerZ1On` — the **Kummer cocycle
  of `a ∈ Lˣ` over the subgroup** `N = G_L` (`β² = a`, `N` fixing `a`), generalizing T-13's
  full-group `kummerCocycle` to elements algebraic over `k`.
* Stiefel–Whitney classes of **diagonal rank-2 forms** are *notational*: for `⟨x, y⟩` over
  `ℚ₂`, `w₁ = [x] + [y]` (Kummer classes, T-13) and `w₂ = [x] ∪ [y]`
  (`trivialCupPairing`, T-09/T-04).  Following the plan, no `QuadraticForm` machinery is
  used: (111) is asserted at the paper's fixed diagonal representatives
  `Tr_{L/k}⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr_{L/k}⟨1⟩ ≃ ⟨2, 2d⟩` (Lemma 6.16), absorbing the Delzant
  well-definedness question into the axiom's scoping.  **Deviation flagged.**

## The cocycle identity

`ν_α ∈ Z²` is proved from the uniform expansion rules (index 2)

  `b₁(xy) = b₁(x) + D₀(x;y)`,  `b_s(xy) = b_s(x) + D₁(x;y)`,

where `D₀(x;y) = if x ∈ U then b₁(y) else b_s(y)` and `D₁` is the other branch; the cocycle
sum then cancels pairwise in characteristic 2 using `D₀(h;k)·D₁(h;k) = b₁(k)·b_s(k)`.
Convention anchor (checked by hand, model `G = C₄ ⊇ U = C₂`, `α ≠ 0`): the class restricts on
`U` to the nontrivial `H²(C₂)`-class, and the fibre extension of the universal two-point
cocycle is `D₈` (paper, Lemma 6.13).

## Citations

Evens, Trans. AMS 108 (1963), Thm 1 (§§4–5); Kahn, Invent. Math. 78 (1984), Théorèmes 1–3;
Kozlowski, Proc. AMS 91 (1984), Thm 1.1; paper §6, eqs. (95)–(100), (111), Lemmas 6.13/6.16.
`docs/literature-axioms.md` B9.
-/

namespace GQ2

open ContCoh

open scoped Classical

/-! ## Index-2 helpers -/

section IndexTwo

variable {G : Type*} [Group G]

/-- Product membership for an index-2 subgroup: `xy ∈ U ↔ (x ∈ U ↔ y ∈ U)`. -/
lemma mul_mem_iff_of_index_two {U : Subgroup G} (h : U.index = 2) (x y : G) :
    x * y ∈ U ↔ (x ∈ U ↔ y ∈ U) := by
  by_cases hx : x ∈ U
  · rw [U.mul_mem_cancel_left hx]
    simp [hx]
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp h
    have hax : a * x ∈ U := by
      rcases ha x with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exact absurd h1 hx
    have hxy := ha (x * y)
    rw [← mul_assoc, U.mul_mem_cancel_left hax] at hxy
    rcases hxy with ⟨hy, hnxy⟩ | ⟨hxy', hny⟩
    · simp [hnxy, hy, hx]
    · simp [hxy', hny, hx]

lemma notMem_mul_mem {U : Subgroup G} (h : U.index = 2) {x y : G}
    (hx : x ∉ U) (hy : y ∉ U) : x * y ∈ U :=
  (mul_mem_iff_of_index_two h x y).mpr (iff_of_false hx hy)

lemma notMem_mul_notMem {U : Subgroup G} (h : U.index = 2) {x y : G}
    (hx : x ∉ U) (hy : y ∈ U) : x * y ∉ U := fun hxy =>
  hx (((mul_mem_iff_of_index_two h x y).mp hxy).mpr hy)

lemma mem_mul_notMem {U : Subgroup G} (h : U.index = 2) {x y : G}
    (hx : x ∈ U) (hy : y ∉ U) : x * y ∉ U := fun hxy =>
  hy (((mul_mem_iff_of_index_two h x y).mp hxy).mp hx)

lemma inv_notMem {U : Subgroup G} {s : G} (hs : s ∉ U) : s⁻¹ ∉ U :=
  fun h => hs (U.inv_mem_iff.mp h)

end IndexTwo

/-! ## The Shapiro components `b₁`, `b_s` and their expansion rules -/

section Shapiro

variable {G : Type*} [Group G]

/-- The first Shapiro component (paper eq. (97), `u = 1`):
`b(γ)₁ = α(γ)` for `γ ∈ U` and `α(γs)` otherwise.  (Total function: junk `0` if the
membership bookkeeping fails, which cannot happen at index 2.) -/
noncomputable def evensAux (U : Subgroup G) (s : G) (α : U → ZMod 2) : G → ZMod 2 := fun x =>
  if hx : x ∈ U then α ⟨x, hx⟩ else if hxs : x * s ∈ U then α ⟨x * s, hxs⟩ else 0

/-- The second Shapiro component `b(γ)_s`, via the identity `b(γ)_s = b(s⁻¹γ)₁`. -/
noncomputable def bS (U : Subgroup G) (s : G) (α : U → ZMod 2) : G → ZMod 2 :=
  fun x => evensAux U s α (s⁻¹ * x)

variable {U : Subgroup G} {s : G}

lemma evensAux_of_mem (α : U → ZMod 2) {x : G} (hx : x ∈ U) :
    evensAux U s α x = α ⟨x, hx⟩ := dif_pos hx

lemma evensAux_of_notMem (hUi : U.index = 2) (hs : s ∉ U) (α : U → ZMod 2) {x : G}
    (hx : x ∉ U) : evensAux U s α x = α ⟨x * s, notMem_mul_mem hUi hx hs⟩ := by
  rw [evensAux, dif_neg hx, dif_pos (notMem_mul_mem hUi hx hs)]

lemma bS_of_mem (hUi : U.index = 2) (hs : s ∉ U) (α : U → ZMod 2) {x : G} (hx : x ∈ U) :
    bS U s α x = α ⟨s⁻¹ * x * s,
      notMem_mul_mem hUi (notMem_mul_notMem hUi (inv_notMem hs) hx) hs⟩ := by
  rw [bS, evensAux_of_notMem hUi hs α (notMem_mul_notMem hUi (inv_notMem hs) hx)]

lemma bS_of_notMem (hUi : U.index = 2) (hs : s ∉ U) (α : U → ZMod 2) {x : G} (hx : x ∉ U) :
    bS U s α x = α ⟨s⁻¹ * x, notMem_mul_mem hUi (inv_notMem hs) hx⟩ := by
  rw [bS, evensAux_of_mem α (notMem_mul_mem hUi (inv_notMem hs) hx)]

/-- **Expansion rule** for `b₁` on a product. -/
lemma evensAux_mul (hUi : U.index = 2) (hs : s ∉ U) (α : U → ZMod 2)
    (hα : ∀ u v : U, α (u * v) = α u + α v) (x y : G) :
    evensAux U s α (x * y)
      = evensAux U s α x + if x ∈ U then evensAux U s α y else bS U s α y := by
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
  · have hxy : x * y ∈ U := mul_mem hx hy
    rw [evensAux_of_mem α hxy, evensAux_of_mem α hx, if_pos hx, evensAux_of_mem α hy,
      show (⟨x * y, hxy⟩ : U) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, hα]
  · have hxy : x * y ∉ U := mem_mul_notMem hUi hx hy
    rw [evensAux_of_notMem hUi hs α hxy, evensAux_of_mem α hx, if_pos hx,
      evensAux_of_notMem hUi hs α hy,
      show (⟨x * y * s, notMem_mul_mem hUi hxy hs⟩ : U)
        = ⟨x, hx⟩ * ⟨y * s, notMem_mul_mem hUi hy hs⟩
        from Subtype.ext (show x * y * s = x * (y * s) by group), hα]
  · have hxy : x * y ∉ U := notMem_mul_notMem hUi hx hy
    rw [evensAux_of_notMem hUi hs α hxy, evensAux_of_notMem hUi hs α hx, if_neg hx,
      bS_of_mem hUi hs α hy,
      show (⟨x * y * s, notMem_mul_mem hUi hxy hs⟩ : U)
        = ⟨x * s, notMem_mul_mem hUi hx hs⟩ *
          ⟨s⁻¹ * y * s, notMem_mul_mem hUi (notMem_mul_notMem hUi (inv_notMem hs) hy) hs⟩
        from Subtype.ext (show x * y * s = (x * s) * (s⁻¹ * y * s) by group), hα]
  · have hxy : x * y ∈ U := notMem_mul_mem hUi hx hy
    rw [evensAux_of_mem α hxy, evensAux_of_notMem hUi hs α hx, if_neg hx,
      bS_of_notMem hUi hs α hy,
      show (⟨x * y, hxy⟩ : U)
        = ⟨x * s, notMem_mul_mem hUi hx hs⟩ *
          ⟨s⁻¹ * y, notMem_mul_mem hUi (inv_notMem hs) hy⟩
        from Subtype.ext (show x * y = (x * s) * (s⁻¹ * y) by group), hα]

/-- **Expansion rule** for `b_s` on a product (the two branches swap). -/
lemma bS_mul (hUi : U.index = 2) (hs : s ∉ U) (α : U → ZMod 2)
    (hα : ∀ u v : U, α (u * v) = α u + α v) (x y : G) :
    bS U s α (x * y) = bS U s α x + if x ∈ U then bS U s α y else evensAux U s α y := by
  have hsx : s⁻¹ * x ∈ U ↔ ¬ x ∈ U := by
    rw [mul_mem_iff_of_index_two hUi]
    simp [inv_notMem hs]
  rw [bS, show s⁻¹ * (x * y) = (s⁻¹ * x) * y by group, evensAux_mul hUi hs α hα]
  by_cases hx : x ∈ U
  · rw [if_neg (fun h => (hsx.mp h) hx), if_pos hx]; rfl
  · rw [if_pos (hsx.mpr hx), if_neg hx]; rfl

lemma evensAux_zero_fun (U : Subgroup G) (s : G) :
    evensAux U s (0 : U → ZMod 2) = 0 := by
  funext x
  rw [evensAux]
  split_ifs <;> rfl

/-! ### Continuity -/

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- `b₁` is locally constant, hence continuous: on `U` it is `α ∘ ι`, off `U` it is
`α ∘ (·s) ∘ ι`, both witnessed on open sets. -/
lemma evensAux_continuous (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    {α : U → ZMod 2} (hαc : Continuous α) : Continuous (evensAux U s α) := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  by_cases hg : g ∈ U
  · refine ⟨Subtype.val '' (α ⁻¹' {α ⟨g, hg⟩}),
      hUo.isOpenMap_subtype_val _ (hαc.isOpen_preimage _ (isOpen_discrete _)),
      ⟨⟨g, hg⟩, rfl, rfl⟩, ?_⟩
    rintro x ⟨⟨x', hx'⟩, hval, rfl⟩
    rw [evensAux_of_mem α hx', evensAux_of_mem α hg]
    exact hval
  · have hgs : g * s ∈ U := notMem_mul_mem hUi hg hs
    refine ⟨(· * s) ⁻¹' (Subtype.val '' (α ⁻¹' {α ⟨g * s, hgs⟩})),
      (hUo.isOpenMap_subtype_val _ (hαc.isOpen_preimage _ (isOpen_discrete _))).preimage
        (continuous_mul_const s), ⟨⟨g * s, hgs⟩, rfl, rfl⟩, ?_⟩
    rintro x ⟨⟨x', hx'⟩, hval, hxs⟩
    obtain rfl : x' = x * s := hxs
    have hxU : x ∉ U := fun h => hs ((U.mul_mem_cancel_left h).mp hx')
    rw [evensAux_of_notMem hUi hs α hxU, evensAux_of_notMem hUi hs α hg]
    exact hval

lemma bS_continuous (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    {α : U → ZMod 2} (hαc : Continuous α) : Continuous (bS U s α) :=
  (evensAux_continuous hUo hUi hs hαc).comp (continuous_const_mul s⁻¹)

end Shapiro

/-! ## Degree-1 corestriction -/

section Cor

variable {G : Type*} [Group G]

/-- The **degree-1 corestriction cocycle**: `cor(α) = b₁ + b_s` (sum over the transversal
`{1, s}`). -/
noncomputable def corFun (U : Subgroup G) (s : G) (α : U → ZMod 2) : G → ZMod 2 :=
  fun x => evensAux U s α x + bS U s α x

variable {U : Subgroup G} {s : G}

/-- `cor(α)` is a homomorphism (the two expansion cross-terms recombine). -/
lemma corFun_hom (hUi : U.index = 2) (hs : s ∉ U) (α : U → ZMod 2)
    (hα : ∀ u v : U, α (u * v) = α u + α v) (x y : G) :
    corFun U s α (x * y) = corFun U s α x + corFun U s α y := by
  simp only [corFun, evensAux_mul hUi hs α hα, bS_mul hUi hs α hα]
  split_ifs <;> abel

variable [TopologicalSpace G] [IsTopologicalGroup G]

lemma corFun_continuous (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    {α : U → ZMod 2} (hαc : Continuous α) : Continuous (corFun U s α) :=
  (evensAux_continuous hUo hUi hs hαc).add (bS_continuous hUo hUi hs hαc)

variable [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

omit [ContinuousSMul G (ZMod 2)] in
/-- `cor(α)` as a continuous 1-cocycle (trivial action): membership in `Z¹(G, 𝔽₂)`. -/
lemma corFun_mem_Z1 (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : U → ZMod 2) (hα : ∀ u v : U, α (u * v) = α u + α v) (hαc : Continuous α) :
    corFun U s α ∈ Z1 G (ZMod 2) :=
  (mem_Z1_iff_of_trivial htriv).mpr
    ⟨corFun_continuous hUo hUi hs hαc, corFun_hom hUi hs α hα⟩

/-- The **degree-1 corestriction class** `cor([α]) ∈ H¹(G, 𝔽₂)`. -/
noncomputable def corH1 (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : U → ZMod 2) (hα : ∀ u v : U, α (u * v) = α u + α v) (hαc : Continuous α) :
    H1 G (ZMod 2) :=
  H1mk G (ZMod 2) ⟨corFun U s α, corFun_mem_Z1 htriv hUo hUi hs α hα hαc⟩

end Cor

/-! ## The index-two Evens norm (the paper's two-point graph cocycle (98)) -/

section EvensNorm

variable {G : Type*} [Group G]

/-- The paper's eq. (98): `ν_α(γ,η) = b(γ)₁·b(η)_{γ̄⁻¹s} + ε(γ̄)·b(η)₁·b(η)_s`.  Its class is
the **index-two Evens norm** `N^{Ev}_{U→G}([α])` (paper Lemma 6.13, eq. (99)). -/
noncomputable def evensNormFun (U : Subgroup G) (s : G) (α : U → ZMod 2) :
    G × G → ZMod 2 := fun q =>
  if q.1 ∈ U then evensAux U s α q.1 * bS U s α q.2
  else evensAux U s α q.1 * evensAux U s α q.2 + evensAux U s α q.2 * bS U s α q.2

variable {U : Subgroup G} {s : G}

/-- Stress test: the Evens norm cocycle of `α = 0` is `0` (`N` is normalized). -/
lemma evensNormFun_zero (U : Subgroup G) (s : G) :
    evensNormFun U s (0 : U → ZMod 2) = 0 := by
  funext q
  have h0 := evensAux_zero_fun U s
  rw [evensNormFun]
  split_ifs <;> simp [h0, bS]

variable [TopologicalSpace G] [IsTopologicalGroup G]

lemma evensNormFun_continuous (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    {α : U → ZMod 2} (hαc : Continuous α) : Continuous (evensNormFun U s α) := by
  have hb1 := evensAux_continuous hUo hUi hs hαc
  have hbs := bS_continuous hUo hUi hs hαc
  have hUc : IsClopen (U : Set G) := ⟨(OpenSubgroup.mk U hUo).isClosed, hUo⟩
  have hclopen : IsClopen {q : G × G | q.1 ∈ U} := IsClopen.preimage hUc continuous_fst
  have hfr : frontier {q : G × G | q.1 ∈ U} = ∅ := IsClopen.frontier_eq hclopen
  refine Continuous.if (fun q hq => absurd (hfr ▸ hq) (Set.notMem_empty q)) ?_ ?_
  · exact (hb1.comp continuous_fst).mul (hbs.comp continuous_snd)
  · exact ((hb1.comp continuous_fst).mul (hb1.comp continuous_snd)).add
      ((hb1.comp continuous_snd).mul (hbs.comp continuous_snd))

variable [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

omit [ContinuousSMul G (ZMod 2)] in
/-- **`ν_α` is a 2-cocycle** — the pairwise-cancellation calculation of the module docstring
(uniform expansion rules + `D₀·D₁ = b₁(k)·b_s(k)`, characteristic 2). -/
lemma evensNormFun_mem_Z2 (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : U → ZMod 2) (hα : ∀ u v : U, α (u * v) = α u + α v) (hαc : Continuous α) :
    evensNormFun U s α ∈ Z2 G (ZMod 2) := by
  refine mem_Z2_iff.mpr ⟨evensNormFun_continuous hUo hUi hs hαc, fun g h k => ?_⟩
  rw [htriv]
  by_cases hg : g ∈ U <;> by_cases hh : h ∈ U
  · have hgh : g * h ∈ U := mul_mem hg hh
    simp only [evensNormFun, if_pos hg, if_pos hh, if_pos hgh,
      evensAux_mul hUi hs α hα, bS_mul hUi hs α hα]
    ring
  · have hgh : g * h ∉ U := mem_mul_notMem hUi hg hh
    simp only [evensNormFun, if_pos hg, if_neg hh, if_neg hgh,
      evensAux_mul hUi hs α hα, bS_mul hUi hs α hα]
    ring
  · have hgh : g * h ∉ U := notMem_mul_notMem hUi hg hh
    simp only [evensNormFun, if_neg hg, if_pos hh, if_neg hgh,
      evensAux_mul hUi hs α hα, bS_mul hUi hs α hα]
    -- characteristic 2: one doubled cross-term dies
    linear_combination CharTwo.add_self_eq_zero (evensAux U s α h * bS U s α k)
  · have hgh : g * h ∈ U := notMem_mul_mem hUi hg hh
    simp only [evensNormFun, if_neg hg, if_neg hh, if_pos hgh,
      evensAux_mul hUi hs α hα, bS_mul hUi hs α hα]
    -- characteristic 2: two doubled cross-terms die
    linear_combination CharTwo.add_self_eq_zero (evensAux U s α h * evensAux U s α k)
      + CharTwo.add_self_eq_zero (evensAux U s α k * bS U s α k)

/-- The **index-two Evens norm** `N^{Ev}([α]) ∈ H²(G, 𝔽₂)`, defined as the class of the
two-point graph cocycle (98) (= the paper's Lemma 6.13/eq. (99) normalization). -/
noncomputable def evensNormH2 (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : U → ZMod 2) (hα : ∀ u v : U, α (u * v) = α u + α v) (hαc : Continuous α) :
    H2 G (ZMod 2) :=
  H2mk G (ZMod 2) ⟨evensNormFun U s α, evensNormFun_mem_Z2 htriv hUo hUi hs α hα hαc⟩

end EvensNorm

/-! ## Kummer cocycles over a subgroup (T-13, relativized)

For `a ∈ Lˣ` (rather than `kˣ`), the Kummer cocycle `g ↦ [g√a ≠ √a]` is a homomorphism on any
subgroup `N ≤ G_k` that fixes `a` — the input `[a] ∈ H¹(G_L, 𝔽₂)` of the Evens norm and
corestriction in (111). -/

section SubgroupKummer

variable {K : Type*} [Field K] [CharZero K]

open Kummer

/-- A nonzero element of a characteristic-zero field is not its own negative. -/
lemma ne_neg_of_ne_zero {β : AlgebraicClosure K} (hβ0 : β ≠ 0) : β ≠ -β := by
  intro h
  have h2 : (2 : AlgebraicClosure K) * β = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h' | h'
  · exact two_ne_zero h'
  · exact hβ0 h'

omit [CharZero K] in
/-- If `g` fixes `β²`, then `g√ = ±√`: the two-values lemma with an abstract fixed square
(T-13's `two_values`, relativized off the base field). -/
lemma two_values_of_fixed {A β : AlgebraicClosure K} (hβ : β ^ 2 = A)
    {g : GaloisGroup K} (hg : g • A = A) : g • β = β ∨ g • β = -β := by
  have key : (g • β) ^ 2 = β ^ 2 := by
    rw [AlgEquiv.smul_def, ← map_pow, hβ, ← AlgEquiv.smul_def, hg]
  have hfac : (g • β - β) * (g • β + β) = 0 := by linear_combination key
  rcases mul_eq_zero.1 hfac with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.1 h)

variable {A β : AlgebraicClosure K} {N : Subgroup (GaloisGroup K)}

/-- The Kummer cocycle function is a homomorphism on a subgroup fixing `β²`. -/
lemma kummerCocycleFun_hom_on (hβ : β ^ 2 = A) (hβ0 : β ≠ 0)
    (hN : ∀ g ∈ N, g • A = A) (g h : N) :
    kummerCocycleFun β ((g : GaloisGroup K) * h)
      = kummerCocycleFun β g + kummerCocycleFun β h := by
  have hgA := hN g g.2
  have hhA := hN h h.2
  have eq1 : ∀ {x : GaloisGroup K}, x • β = -β → kummerCocycleFun β x = 1 :=
    fun hx => if_neg (fun e => ne_neg_of_ne_zero hβ0 (e.symm.trans hx))
  rcases two_values_of_fixed hβ hgA with hg' | hg' <;>
    rcases two_values_of_fixed hβ hhA with hh' | hh'
  · rw [kummerCocycleFun_eq0 hg', kummerCocycleFun_eq0 hh',
      kummerCocycleFun_eq0 (by rw [mul_smul, hh', hg'])]
    decide
  · rw [kummerCocycleFun_eq0 hg', eq1 hh', eq1 (by rw [mul_smul, hh', smul_neg, hg'])]
    decide
  · rw [eq1 hg', kummerCocycleFun_eq0 hh', eq1 (by rw [mul_smul, hh', hg'])]
    decide
  · rw [eq1 hg', eq1 hh',
      kummerCocycleFun_eq0 (by rw [mul_smul, hh', smul_neg, hg', neg_neg])]
    decide

/-- **The Kummer cocycle of `a` over a subgroup `N` fixing it**, as an element of
`Z¹(N, 𝔽₂)`: the input class `[a] ∈ H¹(G_L, 𝔽₂)` of (111) (with `N = G_L`, `a = β²`). -/
noncomputable def kummerZ1On (N : Subgroup (GaloisGroup K)) (hβ : β ^ 2 = A) (hβ0 : β ≠ 0)
    (hN : ∀ g ∈ N, g • A = A) : Z1 N (ZMod 2) :=
  ⟨fun g => kummerCocycleFun β g,
    (mem_Z1_iff_of_trivial (fun _ _ => rfl)).mpr
      ⟨(kummerCocycleFun_continuous β).comp continuous_subtype_val,
        fun g h => kummerCocycleFun_hom_on hβ hβ0 hN g h⟩⟩

@[simp] lemma kummerZ1On_apply (hβ : β ^ 2 = A) (hβ0 : β ≠ 0)
    (hN : ∀ g ∈ N, g • A = A) (g : N) :
    (kummerZ1On N hβ hβ0 hN).1 g = kummerCocycleFun β g := rfl

omit [CharZero K] in
/-- The stabilizer of `δ` fixes every `k`-linear combination `u + vδ` — the fixedness input
for the Kummer cocycle of `a = u + v√d` over `N = G_L`, `L = k(√d)`. -/
lemma stabilizer_fixes_linear (u v : K) (δ : AlgebraicClosure K) :
    ∀ g ∈ MulAction.stabilizer (GaloisGroup K) δ,
      g • (algebraMap K (AlgebraicClosure K) u + algebraMap K (AlgebraicClosure K) v * δ)
        = algebraMap K (AlgebraicClosure K) u + algebraMap K (AlgebraicClosure K) v * δ := by
  intro g hg
  have hgδ : g • δ = δ := hg
  rw [AlgEquiv.smul_def, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
    ← AlgEquiv.smul_def, hgδ]

end SubgroupKummer

/-! ## `Z¹`-level packaging (for the axiom statement) -/

section Z1Wrappers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] {U : Subgroup G} {s : G}

/-- The **corestriction class** `cor([α]) ∈ H¹(G, 𝔽₂)` of a 1-cocycle `α ∈ Z¹(U, 𝔽₂)`. -/
noncomputable def corH1Z (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : Z1 U (ZMod 2)) : H1 G (ZMod 2) :=
  have h := (mem_Z1_iff_of_trivial (fun u m => htriv u.1 m)).mp α.2
  corH1 htriv hUo hUi hs α.1 h.2 h.1

/-- The **index-two Evens norm** `N^{Ev}([α]) ∈ H²(G, 𝔽₂)` of a 1-cocycle `α ∈ Z¹(U, 𝔽₂)`. -/
noncomputable def evensNormH2Z (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : Z1 U (ZMod 2)) : H2 G (ZMod 2) :=
  have h := (mem_Z1_iff_of_trivial (fun u m => htriv u.1 m)).mp α.2
  evensNormH2 htriv hUo hUi hs α.1 h.2 h.1

end Z1Wrappers

end GQ2
