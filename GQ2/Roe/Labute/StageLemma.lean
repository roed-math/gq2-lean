/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.Levelwise
import GQ2.Roe.Labute.GradedLie.SpanAssembly
import GQ2.FrattiniNongen

/-!
# The defect calculus, the span theorem, and the stage lemma  (L-campaign ticket L1/L4)

**Statements final (ticket L1); fills tickets L4a (calculus + `d̄` + SL2) and L4b (span
theorem + SL1)** — the split of spike §4.8, recorded as binding in the design memo.
Design record: `docs/orchestration/labute-l1-design.md`; sources: `labute-spike.md`
§2.1–2.5 (formulas, thresholds, and the statement freeze), `labute-plan.md` §2.2.

All statements live at the calculus threshold `k ≥ 3` (spike §2.1: at `k = 2` squaring is
not additive and `λ₁`-moves change the Frattini class — *base-case territory, not calculus
territory*).

## The shift word shapes (spike §2.2, signs resolved)

In `Z_k` every sign is trivial, so the frozen formulas fix one multiplicative order:

* `r₀`-side, triple `(a, s, y)`, modification `(w₁, w₂, w₃)`:
  `d̄(w) = w₁² · [w₁,a] · [w₂,y] · [w₃,s]`  (`dbarWordR0`; the `S⁴` factor is inert, the
  `A²` factor gives the π-diagonal `w₁²[w₁,a]`, `[S,Y]` the two cross terms);
* `r₂`-side, triple `(s, x, y)`, modification `(u, v, w)`:
  `d̄(u,v,w) = w² · [w,y] · [u,x] · [v,s]`  (`dbarWordR2`; `y` is the distinguished
  squared generator, the x-block is π-inert but contributes both cross terms, `[y, y^s]`
  is fully inert).

All commutators are repo-convention (`commP`; see `TwoCentralTower.lean`).

## The span theorem (spike §2.3 — L4b's load-bearing wall)

Free pro-2 form only (`freeProTwo`): for `k ≥ 3`,
`Zₖ(F₃) ≤ ⟨Im d̄ₖ, g₂^{2^{k-1}}, g₃^{2^{k-1}}⟩` with the **relator-adapted tail pair**
(`r₀`: tails `(S, Y)` = generators 1,2; `r₂`: tails `(s, x)` = generators 0,1 — an early
spike run with the wrong pair `(x, y)` failed rank checks, so the pair is load-bearing),
and the **`2^{k-1}` exponent** (level-`k` classes; Serre §7 prints `2^h`, off by one —
spike §2.3 erratum, machine-confirmed).  Only the `≤` direction is frozen (the reverse
inclusion has no consumer).  Descent to the towers at any generating triple is a separate
statement (`span_descent_*`), via `map_twoCentralSeries_eq`.

Proof route for the fills: the no-basis-theorem structural induction of spike §2.5(a);
fallbacks O1/O2 of plan §7 (owner-gated) if it snags — the named residual risk.

## The stage lemma (spike §2.4)

`SL1` (reachability, L4b): for `T ∈ S^P_ₖ`, the defect is hit by a modification —
`∃ w ∈ (λ_{k-1}/λ_{k+1})³, d̄_T(w) = δ(T)⁻¹` (inverse form for exact composability with
the shift formula; in `Zₖ` inverses are trivial, so this is the memo's `δ ∈ Im d̄`).
`SL2` (digit adjustment, L4a): once the defect vanishes, a `ker d̄`-modification places
the corrected lift in `S^P_{k+1}` — the memo's "`ker d̄ₖ → (ℤ/2)²` is onto" collapsed to
its consumed form; the digit bookkeeping ((ℤ/2)²-ontoness, the automatic vanishing of the
π'd slot's fresh digit) is deliberately *not* frozen — it is L4a's internal proof
mechanism, with the dimension-count fallback of spike §2.5(c) equally admissible.
`stageStep` (proved here, modulo the sorried inputs): `S^P_ₖ ≠ ∅ → S^P_{k+1} ≠ ∅` — the
composability certificate for the frozen statements, and the exact interface Assembly
consumes.
-/

namespace GQ2.Roe.Labute

/-! ## The congruence calculus (spike §2.1; generic pro-2 `G`, `k ≥ 3`)

The full profinite instance pack is carried deliberately (the fills run through
closed-map/compactness arguments on λ-layers); the three instantiations `D_R`, `D₀`,
`freeProTwo` all satisfy it. -/

section Congruence

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `λₘ` dies in `Qₘ` (the top layer image is trivial). -/
private theorem lambdaImage_self (m : ℕ) : lambdaImage G m m = ⊥ := by
  rw [lambdaImage, Subgroup.map_eq_bot_iff, levelMk, QuotientGroup.ker_mk']

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `λ₁ = ⊤` survives to every level quotient. -/
private theorem lambdaImage_one_eq_top (m : ℕ) : lambdaImage G 1 m = ⊤ := by
  rw [lambdaImage, twoCentralSeries_one]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G m)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
open scoped commutatorElement in
/-- The λ-grading lemma, transported to the level quotients and to the repo commutator
convention: `commP λₐ λᵦ ⊆ λ_{a+b}` in `Qₘ`. -/
private theorem commP_mem_lambdaImage_add {a b m : ℕ} {v g : levelQuot G m}
    (hv : v ∈ lambdaImage G a m) (hg : g ∈ lambdaImage G b m) :
    commP v g ∈ lambdaImage G (a + b) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨commP x y, ?_, by simp only [commP, map_mul, map_inv]⟩
  have h : commP x y = ⁅x⁻¹, y⁻¹⁆ := by simp only [commP, commutatorElement_def, inv_inv]
  rw [h]
  exact commutator_mem_twoCentralSeries_add G ((twoCentralSeries G a).inv_mem hx)
    ((twoCentralSeries G b).inv_mem hy)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A `Zₖ`-congruence is realized by a *left* central factor (centrality moves it across). -/
private theorem exists_zLayer_mul_left {k : ℕ} {v v' : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : ∃ z ∈ zLayer G k, v' = z * v := by
  refine ⟨v⁻¹ * v', h, ?_⟩
  rw [← Subgroup.mem_center_iff.mp (zLayer_le_center G k h) v]
  group

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The slot-congruence atom** (spike §2.1): for `v ∈ λ_{k-1}`, `commP v g` depends only on
`g` modulo `λ₂`.  Both error terms die: `commP v (g⁻¹g') ∈ λ_{k+1} = 1`, and the surviving
`commP v g ∈ λₖ = Zₖ` is central, so the conjugation by `g⁻¹g'` is trivial. -/
private theorem commP_congr_slot (k : ℕ) (hk : 3 ≤ k) {v g g' : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (hg : g⁻¹ * g' ∈ lambdaImage G 2 (k + 1)) :
    commP v g = commP v g' := by
  have hg' : g' = g * (g⁻¹ * g') := by group
  have h1 : commP v (g⁻¹ * g') = 1 := by
    have h := commP_mem_lambdaImage_add hv hg
    rw [show k - 1 + 2 = k + 1 by omega, lambdaImage_self] at h
    simpa using h
  have h2 : commP v g ∈ zLayer G k := by
    have hgt : g ∈ lambdaImage G 1 (k + 1) := by rw [lambdaImage_one_eq_top]; trivial
    have h := commP_mem_lambdaImage_add hv hgt
    rwa [show k - 1 + 1 = k by omega] at h
  have key : commP v (g * (g⁻¹ * g')) =
      commP v (g⁻¹ * g') * ((g⁻¹ * g')⁻¹ * commP v g * (g⁻¹ * g')) := by
    simp only [commP]; group
  have hcen := Subgroup.mem_center_iff.mp (zLayer_le_center G k h2) (g⁻¹ * g')
  rw [hg', key, h1, one_mul, mul_assoc, ← hcen, ← mul_assoc, inv_mul_cancel, one_mul]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The modification-congruence atoms** (spike §2.1): squaring is `𝔽₂`-linear on `Zₖ`-classes
and `commP · g` is insensitive to a central left factor. -/
private theorem sq_congr_mod {k : ℕ} {v v' : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : v ^ 2 = v' ^ 2 := by
  obtain ⟨z, hz, rfl⟩ := exists_zLayer_mul_left h
  rw [(zLayer_commute hz v).mul_pow, zLayer_sq G hz, one_mul]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem commP_congr_mod {k : ℕ} {v v' g : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : commP v g = commP v' g := by
  obtain ⟨z, hz, rfl⟩ := exists_zLayer_mul_left h
  rw [commP_central_left (zLayer_commute hz)]

/-- **Frattini-only dependence on the triple slots** (spike §2.1: `[v, g]` depends only on
`g mod λ₂` for `v ∈ λ_{k-1}`; §4.3: worth its own lemma — it makes the census-style
base-case checks small): the `r₀`-shift word is unchanged when the slots move by
`λ₂`-classes.  Fill: L4a. -/
theorem dbarWordR0_congr_slots (k : ℕ) (hk : 3 ≤ k)
    {a s y a' s' y' : levelQuot G (k + 1)}
    (ha : a⁻¹ * a' ∈ lambdaImage G 2 (k + 1)) (hs : s⁻¹ * s' ∈ lambdaImage G 2 (k + 1))
    (hy : y⁻¹ * y' ∈ lambdaImage G 2 (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR0 a s y w = dbarWordR0 a' s' y' w := by
  simp only [dbarWordR0, commP_congr_slot k hk (hw 0) ha, commP_congr_slot k hk (hw 1) hy,
    commP_congr_slot k hk (hw 2) hs]

/-- Frattini-only dependence, `r₂` side.  Fill: L4a. -/
theorem dbarWordR2_congr_slots (k : ℕ) (hk : 3 ≤ k)
    {s x y s' x' y' : levelQuot G (k + 1)}
    (hs : s⁻¹ * s' ∈ lambdaImage G 2 (k + 1)) (hx : x⁻¹ * x' ∈ lambdaImage G 2 (k + 1))
    (hy : y⁻¹ * y' ∈ lambdaImage G 2 (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y w = dbarWordR2 s' x' y' w := by
  simp only [dbarWordR2, commP_congr_slot k hk (hw 2) hy, commP_congr_slot k hk (hw 0) hx,
    commP_congr_slot k hk (hw 1) hs]

-- `hk` and `hw` are part of the frozen interface; the `Zₖ`-congruence argument below
-- happens to need neither (it is pure centrality + exponent 2).
set_option linter.unusedVariables false in
/-- **`Z_{k-1}`-class dependence on the modification** (spike §2.1: `v ↦ v²` is
`𝔽₂`-linear on classes and `[v, g]` depends only on `v mod λₖ`): the `r₀`-shift word is
unchanged when `w` moves by `λₖ`-classes.  Fill: L4a. -/
theorem dbarWordR0_congr_mod (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hww' : ∀ i, (w i)⁻¹ * w' i ∈ lambdaImage G k (k + 1)) :
    dbarWordR0 a s y w = dbarWordR0 a s y w' := by
  simp only [dbarWordR0, sq_congr_mod (hww' 0), commP_congr_mod (hww' 0),
    commP_congr_mod (hww' 1), commP_congr_mod (hww' 2)]

-- `hk` and `hw` are part of the frozen interface; the `Zₖ`-congruence argument below
-- happens to need neither (it is pure centrality + exponent 2).
set_option linter.unusedVariables false in
/-- `Z_{k-1}`-class dependence on the modification, `r₂` side.  Fill: L4a. -/
theorem dbarWordR2_congr_mod (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hww' : ∀ i, (w i)⁻¹ * w' i ∈ lambdaImage G k (k + 1)) :
    dbarWordR2 s x y w = dbarWordR2 s x y w' := by
  simp only [dbarWordR2, sq_congr_mod (hww' 2), commP_congr_mod (hww' 2),
    commP_congr_mod (hww' 0), commP_congr_mod (hww' 1)]

end Congruence

/-! ### Shift-calculus toolkit (L4a fill helpers; not part of the frozen interface)

The whole shift computation runs on three facts about a modification `v ∈ λ_{k-1}` of
`Q_{k+1}` with `k ≥ 3`: `v²` and every `commP v g` lie in the central involutive layer `Zₖ`,
and `v` commutes with `λ₂` outright (`[λ₂, λ_{k-1}] ⊆ λ_{k+1} = 1`).  Everything else is the
move rule `v * a = a * v * commP v a`, which is a pure group identity. -/

/-- The fundamental move rule (pure group identity, no hypotheses). -/
private theorem mul_swap_commP {H : Type*} [Group H] (v a : H) :
    v * a = a * v * commP v a := by simp only [commP]; group

/-- Left expansion of `commP` (pure group identity). -/
private theorem commP_mul_left {H : Type*} [Group H] (x u g : H) :
    commP (x * u) g = u⁻¹ * commP x g * u * commP u g := by simp only [commP]; group

/-- Right expansion of `commP` (pure group identity). -/
private theorem commP_mul_right {H : Type*} [Group H] (x g v : H) :
    commP x (g * v) = commP x v * (v⁻¹ * commP x g * v) := by simp only [commP]; group

/-- `commP` is antisymmetric (pure group identity). -/
private theorem commP_symm {H : Type*} [Group H] (x y : H) : commP x y = (commP y x)⁻¹ := by
  simp only [commP]; group

/-- A vanishing `commP` is exactly a trivial conjugation. -/
private theorem conj_eq_self_of_commP_eq_one {H : Type*} [Group H] {x u : H}
    (h : commP x u = 1) : u⁻¹ * x * u = x := by
  simp only [commP] at h
  calc u⁻¹ * x * u = x * (x⁻¹ * u⁻¹ * x * u) := by group
    _ = x := by rw [h, mul_one]

/-- Commuting elements have trivial `commP` (pure group identity). -/
private theorem commP_eq_one_of_mul_comm {H : Type*} [Group H] {x y : H} (h : x * y = y * x) :
    commP x y = 1 := by
  have hy : y⁻¹ * (x * y) = x := by rw [h]; group
  calc commP x y = x⁻¹ * (y⁻¹ * (x * y)) := by simp only [commP]; group
    _ = x⁻¹ * x := by rw [hy]
    _ = 1 := by group

/-- Conjugation expressed through `commP` (pure group identity). -/
private theorem conj_eq_mul_commP {H : Type*} [Group H] (v a : H) :
    v⁻¹ * a * v = a * (commP v a)⁻¹ := by simp only [commP]; group

/-- **The conjugation-shift core**: an abstract two-central-factor rearrangement, stated with
opaque atoms so that the group-normalizing steps are honest free-group identities. -/
private theorem conj_shift_core {H : Type*} [Group H] (a v₀ v₁ c₀ c₁ : H)
    (h₀ : ∀ t : H, c₀ * t = t * c₀) (h₁ : ∀ t : H, c₁ * t = t * c₁)
    (hvv : v₁ * v₀ = v₀ * v₁) (hconj : v₀⁻¹ * a * v₀ = a * c₀) :
    v₀⁻¹ * (a * v₁ * c₁) * v₀ = a * v₁ * (c₀ * c₁) := by
  calc v₀⁻¹ * (a * v₁ * c₁) * v₀ = v₀⁻¹ * (a * (v₁ * (c₁ * v₀))) := by group
    _ = v₀⁻¹ * (a * (v₁ * (v₀ * c₁))) := by rw [h₁ v₀]
    _ = v₀⁻¹ * (a * (v₁ * v₀ * c₁)) := by group
    _ = v₀⁻¹ * (a * (v₀ * v₁ * c₁)) := by rw [hvv]
    _ = v₀⁻¹ * a * v₀ * (v₁ * c₁) := by group
    _ = a * c₀ * (v₁ * c₁) := by rw [hconj]
    _ = a * (c₀ * v₁) * c₁ := by group
    _ = a * (v₁ * c₀) * c₁ := by rw [h₀ v₁]
    _ = a * v₁ * (c₀ * c₁) := by group

/-- **The `r₂` two-inverse core**: the `x`-slot modification appears once in the `x^s` block and
once in the `x³` block, and the two copies cancel against `zB² = 1`. -/
private theorem dr_inv_core {H : Type*} [Group H] (X A v zA zB c : H)
    (hA : ∀ t : H, zA * t = t * zA) (hB : ∀ t : H, zB * t = t * zB)
    (hc : ∀ t : H, c * t = t * c) (hvA : v * A = A * v * c) (hzB : zB = v * v * c)
    (hzB2 : zB * zB = 1) :
    X * v * zB * (A * v * zA) = X * A * zA := by
  calc X * v * zB * (A * v * zA) = X * v * (zB * (A * v * zA)) := by group
    _ = X * v * ((A * v * zA) * zB) := by rw [hB]
    _ = X * (v * A) * v * (zA * zB) := by group
    _ = X * (A * v * c) * v * (zA * zB) := by rw [hvA]
    _ = X * A * v * (c * v) * (zA * zB) := by group
    _ = X * A * v * (v * c) * (zA * zB) := by rw [hc]
    _ = X * A * (v * v * c) * (zA * zB) := by group
    _ = X * A * zB * (zA * zB) := by rw [← hzB]
    _ = X * A * (zB * (zA * zB)) := by group
    _ = X * A * ((zA * zB) * zB) := by rw [hB (zA * zB)]
    _ = X * A * (zA * (zB * zB)) := by group
    _ = X * A * zA := by rw [hzB2, mul_one]

/-- Three central factors collected on the right (the `r₂` assembly shape). -/
private theorem central_reorder₃ {H : Type*} [Group H] {zA zC : H}
    (hA : ∀ t : H, zA * t = t * zA) (hC : ∀ t : H, zC * t = t * zC) (p q d : H) :
    p * zA * (q * zC) * d = p * q * d * (zC * zA) := by
  calc p * zA * (q * zC) * d = p * (zA * (q * zC)) * d := by group
    _ = p * ((q * zC) * zA) * d := by rw [hA]
    _ = p * q * (zC * (zA * d)) := by group
    _ = p * q * ((zA * d) * zC) := by rw [hC]
    _ = p * q * ((d * zA) * zC) := by rw [hA]
    _ = p * q * d * (zA * zC) := by group
    _ = p * q * d * (zC * zA) := by rw [hA zC]

/-- Two central factors can be collected on the right. -/
private theorem central_reorder₂ {H : Type*} [Group H] {z₀ z₁ : H}
    (h₀ : ∀ t : H, z₀ * t = t * z₀) (h₁ : ∀ t : H, z₁ * t = t * z₁) (p q r : H) :
    p * z₀ * q * (r * z₁) = p * q * r * (z₀ * z₁) := by
  simp only [mul_assoc]
  rw [h₀ (q * (r * z₁))]
  simp only [mul_assoc]
  rw [h₁ z₀]

section ShiftCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The layer images are antitone in the depth index. -/
private theorem lambdaImage_le_of_le {j j' m : ℕ} (h : j ≤ j') :
    lambdaImage G j' m ≤ lambdaImage G j m :=
  Subgroup.map_mono (twoCentralSeries_antitone G h)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A `λ_{k-1}`-modification squares into the central layer. -/
private theorem sq_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) : v ^ 2 ∈ zLayer G k := by
  obtain ⟨x, hx, rfl⟩ := hv
  refine ⟨x ^ 2, ?_, by rw [map_pow]⟩
  have h := sq_mem_twoCentralSeries_succ G hx
  rwa [show k - 1 + 1 = k by omega] at h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Every `commP` of a `λ_{k-1}`-modification is central. -/
private theorem commP_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (g : levelQuot G (k + 1)) :
    commP v g ∈ zLayer G k := by
  have hgt : g ∈ lambdaImage G 1 (k + 1) := by rw [lambdaImage_one_eq_top]; trivial
  have h := commP_mem_lambdaImage_add hv hgt
  rwa [show k - 1 + 1 = k by omega] at h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `λ₂` and `λ_{k-1}` commute outright in `Q_{k+1}` (`[λ₂, λ_{k-1}] ⊆ λ_{k+1} = 1`). -/
private theorem commP_lambdaTwo_eq_one (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP c v = 1 := by
  have h := commP_mem_lambdaImage_add hc hv
  rw [show 2 + (k - 1) = k + 1 by omega, lambdaImage_self] at h
  simpa using h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Any `commP` of two elements of `Q_{k+1}` lies in `λ₂` (`λ₁ = ⊤`). -/
private theorem commP_mem_lambdaTwo (m : ℕ) (x y : levelQuot G m) :
    commP x y ∈ lambdaImage G 2 m := by
  have hx : x ∈ lambdaImage G 1 m := by rw [lambdaImage_one_eq_top]; trivial
  have hy : y ∈ lambdaImage G 1 m := by rw [lambdaImage_one_eq_top]; trivial
  exact commP_mem_lambdaImage_add hx hy

/-- Conjugation by a `λ_{k-1}`-modification is trivial on `λ₂`. -/
private theorem conj_lambdaTwo_eq_self (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    v⁻¹ * c * v = c :=
  conj_eq_self_of_commP_eq_one (commP_lambdaTwo_eq_one k hk hc hv)

/-- **The square shift**: `(a·v)² = a² · (v² · commP v a)`, the π-diagonal of spike §2.2. -/
private theorem sq_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (a : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (a * v) ^ 2 = a ^ 2 * (v ^ 2 * commP v a) := by
  have hc : commP v a * v = v * commP v a :=
    ((zLayer_commute (commP_mem_zLayer k hk hv a) v)).eq
  calc (a * v) ^ 2 = a * (v * a) * v := by rw [pow_two (a * v)]; group
    _ = a * (a * v * commP v a) * v := by rw [mul_swap_commP v a]
    _ = a * a * v * (commP v a * v) := by group
    _ = a * a * v * (v * commP v a) := by rw [hc]
    _ = a ^ 2 * (v ^ 2 * commP v a) := by rw [pow_two a, pow_two v]; group

/-- **The fourth-power inertness**: `(s·v)⁴ = s⁴` — the `S⁴` factor of `r₀` is inert
because the first-order correction is a central involution. -/
private theorem pow_four_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (s * v) ^ 4 = s ^ 4 := by
  have hz : v ^ 2 * commP v s ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk hv) (commP_mem_zLayer k hk hv s)
  have hcen := (zLayer_commute hz (s ^ 2)).eq
  calc (s * v) ^ 4 = ((s * v) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (s ^ 2 * (v ^ 2 * commP v s)) ^ 2 := by rw [sq_mul_lambdaImage k hk s hv]
    _ = s ^ 2 * ((v ^ 2 * commP v s) * s ^ 2) * (v ^ 2 * commP v s) := by
        rw [pow_two (s ^ 2 * (v ^ 2 * commP v s))]; group
    _ = s ^ 2 * (s ^ 2 * (v ^ 2 * commP v s)) * (v ^ 2 * commP v s) := by rw [hcen]
    _ = s ^ 2 * s ^ 2 * ((v ^ 2 * commP v s) * (v ^ 2 * commP v s)) := by group
    _ = s ^ 2 * s ^ 2 := by rw [← pow_two (v ^ 2 * commP v s), zLayer_sq G hz, mul_one]
    _ = s ^ 4 := by group

/-- **The cross-term shift**: `commP (s·v₁) (y·v₂) = commP s y · (commP v₁ y · commP v₂ s)` —
each modification contributes exactly one central cross term, and the conjugations they
generate are trivial because the surviving factors already lie in `λ₂`. -/
private theorem commP_mul_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s y : levelQuot G (k + 1))
    {v₁ v₂ : levelQuot G (k + 1)} (hv₁ : v₁ ∈ lambdaImage G (k - 1) (k + 1))
    (hv₂ : v₂ ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (s * v₁) (y * v₂) = commP s y * (commP v₁ y * commP v₂ s) := by
  have hz₁ : commP v₁ y ∈ zLayer G k := commP_mem_zLayer k hk hv₁ y
  have hz₂ : commP v₂ s ∈ zLayer G k := commP_mem_zLayer k hk hv₂ s
  have hsy : commP s y ∈ lambdaImage G 2 (k + 1) := commP_mem_lambdaTwo (k + 1) s y
  have hv₂' : v₂ ∈ lambdaImage G 2 (k + 1) := lambdaImage_le_of_le (by omega) hv₂
  have h2 : commP v₁ (y * v₂) = commP v₁ y :=
    commP_congr_slot k hk hv₁ (by
      have h : (y * v₂)⁻¹ * y = v₂⁻¹ := by group
      rw [h]; exact (lambdaImage G 2 (k + 1)).inv_mem hv₂')
  have h3 : commP s (y * v₂) = commP v₂ s * commP s y := by
    rw [commP_mul_right, commP_symm s v₂, zLayer_inv_self hz₂,
      conj_lambdaTwo_eq_self k hk hsy hv₂]
  have h7 : v₁⁻¹ * (commP v₂ s * commP s y) * v₁ = commP v₂ s * commP s y :=
    conj_lambdaTwo_eq_self k hk
      (Subgroup.mul_mem _ (lambdaImage_le_of_le (by omega) hz₂) hsy) hv₁
  rw [commP_mul_left, h3, h2, h7, (zLayer_commute hz₂ (commP s y)).eq, mul_assoc,
    ← (zLayer_commute hz₁ (commP v₂ s)).eq]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Two `λ_{k-1}`-modifications commute: `[λ_{k-1}, λ_{k-1}] ⊆ λ_{2k-2} ⊆ λ_{k+1} = 1`
(this is exactly where `k ≥ 3` enters). -/
private theorem commP_lambdaImage_eq_one (k : ℕ) (hk : 3 ≤ k) {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP u v = 1 := by
  have h := lambdaImage_le_of_le (G := G) (m := k + 1)
    (show k + 1 ≤ k - 1 + (k - 1) by omega) (commP_mem_lambdaImage_add hu hv)
  rw [lambdaImage_self] at h
  simpa using h

private theorem mul_comm_lambdaImage (k : ℕ) (hk : 3 ≤ k) {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    u * v = v * u := by
  rw [mul_swap_commP u v, commP_lambdaImage_eq_one k hk hu hv, mul_one]

/-- **The conjugation shift** (`r₂`'s `x^s` block): `(x·v₁)^{s·v₀} = x^s · v₁ · ([v₀,x]·[v₁,s])`.
Both cross terms are central; the `v₀`-conjugation only sees `x` modulo `λ₂`. -/
private theorem conjP_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s x : levelQuot G (k + 1))
    {v₀ v₁ : levelQuot G (k + 1)} (hv₀ : v₀ ∈ lambdaImage G (k - 1) (k + 1))
    (hv₁ : v₁ ∈ lambdaImage G (k - 1) (k + 1)) :
    conjP (x * v₁) (s * v₀) = conjP x s * v₁ * (commP v₀ x * commP v₁ s) := by
  have hax : commP v₀ (conjP x s) = commP v₀ x :=
    commP_congr_slot k hk hv₀ (by
      have h : (conjP x s)⁻¹ * x = commP s x := by simp only [conjP, commP]; group
      rw [h]; exact commP_mem_lambdaTwo (k + 1) s x)
  have hc₀ : commP v₀ x ∈ zLayer G k := hax ▸ commP_mem_zLayer k hk hv₀ (conjP x s)
  have hc₁ : commP v₁ s ∈ zLayer G k := commP_mem_zLayer k hk hv₁ s
  have hconj : v₀⁻¹ * conjP x s * v₀ = conjP x s * commP v₀ x := by
    rw [conj_eq_mul_commP, hax, zLayer_inv_self hc₀]
  have hstart : conjP (x * v₁) (s * v₀) = v₀⁻¹ * (conjP x s * v₁ * commP v₁ s) * v₀ := by
    simp only [conjP, commP]; group
  rw [hstart]
  exact conj_shift_core _ _ _ _ _ (fun t => (zLayer_commute hc₀ t).eq)
    (fun t => (zLayer_commute hc₁ t).eq) (mul_comm_lambdaImage k hk hv₁ hv₀) hconj

/-- **The cube shift** (`r₂`'s `x³` block): `(x·v)³ = x³ · v · (v²·[v,x])`. -/
private theorem pow_three_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (x : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (x * v) ^ 3 = x ^ 3 * v * (v ^ 2 * commP v x) := by
  have hz : v ^ 2 * commP v x ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk hv) (commP_mem_zLayer k hk hv x)
  calc (x * v) ^ 3 = (x * v) ^ 2 * (x * v) := by rw [← pow_succ]
    _ = x ^ 2 * (v ^ 2 * commP v x) * (x * v) := by rw [sq_mul_lambdaImage k hk x hv]
    _ = x ^ 2 * ((v ^ 2 * commP v x) * x) * v := by group
    _ = x ^ 2 * (x * (v ^ 2 * commP v x)) * v := by rw [(zLayer_commute hz x).eq]
    _ = x ^ 3 * ((v ^ 2 * commP v x) * v) := by group
    _ = x ^ 3 * (v * (v ^ 2 * commP v x)) := by rw [(zLayer_commute hz v).eq]
    _ = x ^ 3 * v * (v ^ 2 * commP v x) := by group

/-- **Full inertness of the `[y, y^s]` block** (spike §2.2): the `y`-slot modification enters
both arguments of the commutator and cancels, so this block sees no shift at all. -/
private theorem commP_conjP_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s y : levelQuot G (k + 1))
    {v₀ v₂ : levelQuot G (k + 1)} (hv₀ : v₀ ∈ lambdaImage G (k - 1) (k + 1))
    (hv₂ : v₂ ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (y * v₂) (conjP (y * v₂) (s * v₀)) = commP y (conjP y s) := by
  rw [conjP_mul_lambdaImage k hk s y hv₀ hv₂]
  have hz : commP v₀ y * commP v₂ s ∈ zLayer G k :=
    Subgroup.mul_mem _ (commP_mem_zLayer k hk hv₀ y) (commP_mem_zLayer k hk hv₂ s)
  have hzy : commP v₂ y ∈ zLayer G k := commP_mem_zLayer k hk hv₂ y
  have hyb : commP y (conjP y s) ∈ lambdaImage G 2 (k + 1) :=
    commP_mem_lambdaTwo (k + 1) y (conjP y s)
  have hby : (conjP y s)⁻¹ * y = commP s y := by simp only [conjP, commP]; group
  have hv₂z : v₂ * (commP v₀ y * commP v₂ s) ∈ lambdaImage G (k - 1) (k + 1) :=
    Subgroup.mul_mem _ hv₂ (lambdaImage_le_of_le (by omega) hz)
  -- the second slot is `y` modulo `λ₂`, so the `v₂`-bracket only sees `y`
  have h2 : commP v₂ (conjP y s * v₂ * (commP v₀ y * commP v₂ s)) = commP v₂ y :=
    commP_congr_slot k hk hv₂ (by
      have h : (conjP y s * v₂ * (commP v₀ y * commP v₂ s))⁻¹ * y =
          (commP v₀ y * commP v₂ s)⁻¹ * (v₂⁻¹ * ((conjP y s)⁻¹ * y)) := by group
      rw [h, hby]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (lambdaImage_le_of_le (by omega) hz))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (lambdaImage_le_of_le (by omega) hv₂))
          (commP_mem_lambdaTwo (k + 1) s y)))
  -- the `y`-bracket picks up exactly one central cross term
  have h3 : commP y (conjP y s * v₂ * (commP v₀ y * commP v₂ s)) =
      commP v₂ y * commP y (conjP y s) := by
    have hsplit : conjP y s * v₂ * (commP v₀ y * commP v₂ s) =
        conjP y s * (v₂ * (commP v₀ y * commP v₂ s)) := by group
    have hleft : commP y (v₂ * (commP v₀ y * commP v₂ s)) = commP v₂ y := by
      rw [commP_symm, commP_mul_left,
        commP_eq_one_of_mul_comm (zLayer_commute hz y).eq, mul_one,
        conj_eq_self_of_commP_eq_one
          (commP_eq_one_of_mul_comm (zLayer_commute hz (commP v₂ y)).eq.symm),
        zLayer_inv_self hzy]
    rw [hsplit, commP_mul_right, hleft, conj_lambdaTwo_eq_self k hk hyb hv₂z]
  rw [commP_mul_left, h2, h3, conj_lambdaTwo_eq_self k hk
    (Subgroup.mul_mem _ (lambdaImage_le_of_le (by omega) hzy) hyb) hv₂,
    (zLayer_commute hzy (commP y (conjP y s))).eq, mul_assoc, ← pow_two, zLayer_sq G hzy,
    mul_one]

/-- **The `r₂` shift identity** (spike §2.2): the `x`-block is π-inert but contributes both
cross terms, the `[y, y^s]` block is fully inert, and the `y²` block gives the diagonal. -/
private theorem drWord_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    drWord (s * w 0) (x * w 1) (y * w 2) = drWord s x y * dbarWordR2 s x y w := by
  have hzA : commP (w 0) x * commP (w 1) s ∈ zLayer G k :=
    Subgroup.mul_mem _ (commP_mem_zLayer k hk (hw 0) x) (commP_mem_zLayer k hk (hw 1) s)
  have hzB : w 1 ^ 2 * commP (w 1) x ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk (hw 1)) (commP_mem_zLayer k hk (hw 1) x)
  have hzC : w 2 ^ 2 * commP (w 2) y ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk (hw 2)) (commP_mem_zLayer k hk (hw 2) y)
  have hcx : commP (w 1) x ∈ zLayer G k := commP_mem_zLayer k hk (hw 1) x
  have hvx : commP (w 1) (conjP x s) = commP (w 1) x :=
    commP_congr_slot k hk (hw 1) (by
      have h : (conjP x s)⁻¹ * x = commP s x := by simp only [conjP, commP]; group
      rw [h]; exact commP_mem_lambdaTwo (k + 1) s x)
  have hAB : (conjP x s * w 1 * (commP (w 0) x * commP (w 1) s))⁻¹ *
      (x ^ 3 * w 1 * (w 1 ^ 2 * commP (w 1) x))⁻¹ =
      (conjP x s)⁻¹ * (x ^ 3)⁻¹ * (commP (w 0) x * commP (w 1) s) := by
    rw [← mul_inv_rev, dr_inv_core (x ^ 3) (conjP x s) (w 1) _ _ (commP (w 1) x)
      (fun t => (zLayer_commute hzA t).eq) (fun t => (zLayer_commute hzB t).eq)
      (fun t => (zLayer_commute hcx t).eq)
      (by rw [mul_swap_commP, hvx]) (by rw [pow_two])
      (by rw [← pow_two, zLayer_sq G hzB]),
      mul_inv_rev (x ^ 3 * conjP x s) (commP (w 0) x * commP (w 1) s),
      zLayer_inv_self hzA, mul_inv_rev (x ^ 3) (conjP x s),
      (zLayer_commute hzA ((conjP x s)⁻¹ * (x ^ 3)⁻¹)).eq]
  rw [drWord, drWord, dbarWordR2, conjP_mul_lambdaImage k hk s x (hw 0) (hw 1),
    pow_three_mul_lambdaImage k hk x (hw 1), sq_mul_lambdaImage k hk y (hw 2),
    commP_conjP_mul_lambdaImage k hk s y (hw 0) (hw 2), hAB,
    central_reorder₃ (fun t => (zLayer_commute hzA t).eq)
      (fun t => (zLayer_commute hzC t).eq)]
  group

/-- **The `r₀` shift identity** (spike §2.2): modifying the triple `(a, s, y)` by
`λ_{k-1}`-elements multiplies the relator value by `dbarWordR0` — the `S⁴` block is inert,
the `A²` block contributes the π-diagonal `w₀²·[w₀,a]`, and `[S,Y]` the two cross terms. -/
private theorem d0Word_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    d0Word (a * w 0) (s * w 1) (y * w 2) = d0Word a s y * dbarWordR0 a s y w := by
  have hz₀ : w 0 ^ 2 * commP (w 0) a ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk (hw 0)) (commP_mem_zLayer k hk (hw 0) a)
  have hz₁ : commP (w 1) y * commP (w 2) s ∈ zLayer G k :=
    Subgroup.mul_mem _ (commP_mem_zLayer k hk (hw 1) y) (commP_mem_zLayer k hk (hw 2) s)
  rw [d0Word, d0Word, dbarWordR0, sq_mul_lambdaImage k hk a (hw 0),
    pow_four_mul_lambdaImage k hk s (hw 1), commP_mul_mul_lambdaImage k hk s y (hw 1) (hw 2),
    central_reorder₂ (fun t => (zLayer_commute hz₀ t).eq) (fun t => (zLayer_commute hz₁ t).eq)]
  group

end ShiftCalculus

/-! ## Shift formula and modification stability (spike §2.1–2.2; concrete towers) -/

/-- **The transported shift formula, direction 1** (spike §2.2, machine-verified 24/24):
modifying a level-`k` triple by the projection of a `λ_{k-1}`-modification `w` shifts the
defect by exactly `d̄(w)` at the canonical lift.  No relator hypothesis: the identity is
pure `k ≥ 3` λ-calculus.  Fill: L4a. -/
theorem defectR0_mul (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    {w : Fin 3 → levelQuot (DR : Type) (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) :
    defectR0 k (fun i => T i * levelProj (DR : Type) k (w i)) =
      defectR0 k T *
        dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
          (canonLift (DR : Type) k (T 2)) w := by
  have hlift : ∀ i, levelProj (DR : Type) k (canonLift (DR : Type) k (T i) * w i) =
      T i * levelProj (DR : Type) k (w i) := by
    intro i; rw [map_mul, levelProj_canonLift]
  rw [← defectR0_eq_of_lift k _ (fun i => canonLift (DR : Type) k (T i) * w i) hlift, defectR0]
  exact d0Word_mul_lambdaImage k hk _ _ _ hw

/-- The transported shift formula, direction 2.  Fill: L4a. -/
theorem defectR2_mul (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    {w : Fin 3 → levelQuot (D0 : Type) (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) :
    defectR2 k (fun i => T i * levelProj (D0 : Type) k (w i)) =
      defectR2 k T *
        dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
          (canonLift (D0 : Type) k (T 2)) w := by
  have hlift : ∀ i, levelProj (D0 : Type) k (canonLift (D0 : Type) k (T i) * w i) =
      T i * levelProj (D0 : Type) k (w i) := by
    intro i; rw [map_mul, levelProj_canonLift]
  rw [← defectR2_eq_of_lift k _ (fun i => canonLift (D0 : Type) k (T i) * w i) hlift, defectR2]
  exact drWord_mul_lambdaImage k hk _ _ _ hw

/-! ### Level-`k` modification facts (L4a fill helpers)

At its *own* level a `λ_{k-1}`-modification is already central of exponent 2 in `Qₖ` — both
`v²` and `commP v g` land in `λₖ`, which is trivial in `Qₖ`.  So the relator clause of `S⁰ₖ`
is preserved for the cheapest possible reason, and the χ-clause survives because
`χ(λ_{k-1}) ⊆ 1 + 2^kℤ₂` — one digit sharper than `chiShadow_eq_one_of_mem` gives, which is
exactly the design reason the invariant `P` is stated at modulus `2^k`. -/

section LevelShift

variable {H : Type*} [Group H]

/-- The `r₀` word is blind to central involutive shifts of its slots. -/
private theorem d0Word_central_shift {z₀ z₁ z₂ : H}
    (h₀ : ∀ t : H, Commute z₀ t) (h₁ : ∀ t : H, Commute z₁ t) (h₂ : ∀ t : H, Commute z₂ t)
    (e₀ : z₀ ^ 2 = 1) (e₁ : z₁ ^ 2 = 1) (_e₂ : z₂ ^ 2 = 1) (a s y : H) :
    d0Word (a * z₀) (s * z₁) (y * z₂) = d0Word a s y := by
  have hz4 : z₁ ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e₁, one_pow]
  rw [d0Word, d0Word, (h₀ a).symm.mul_pow, e₀, mul_one, (h₁ s).symm.mul_pow, hz4, mul_one,
    ← (h₁ s).eq, ← (h₂ y).eq, commP_central_left h₁, commP_central_right h₂]

/-- The `r₂` word is blind to central involutive shifts of its slots. -/
private theorem drWord_central_shift {z₀ z₁ z₂ : H}
    (h₀ : ∀ t : H, Commute z₀ t) (h₁ : ∀ t : H, Commute z₁ t) (h₂ : ∀ t : H, Commute z₂ t)
    (e₁ : z₁ ^ 2 = 1) (e₂ : z₂ ^ 2 = 1) (s x y : H) :
    drWord (s * z₀) (x * z₁) (y * z₂) = drWord s x y := by
  have hconj : ∀ (u : H) (z : H), (∀ t : H, Commute z t) →
      conjP (u * z) (s * z₀) = conjP u s * z := by
    intro u z hz
    rw [← (hz u).eq, ← (h₀ s).eq, conjP_central_left hz, conjP_central_right h₀, (hz _).eq]
  have hz3 : z₁ ^ 3 = z₁ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, e₁, one_mul, pow_one]
  rw [drWord, drWord, hconj x z₁ h₁, hconj y z₂ h₂, (h₁ x).symm.mul_pow, hz3,
    (h₂ y).symm.mul_pow, e₂, mul_one, ← (h₂ y).eq, commP_central_left h₂,
    ← (h₂ (conjP y s)).eq, commP_central_right h₂,
    ← (h₁ (conjP x s)).eq, ← (h₁ (x ^ 3)).eq,
    inv_mul_inv_central h₁ (by rw [← pow_two]; exact e₁)]

end LevelShift

section LevelFacts

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- At its own level a `λ_{k-1}`-modification squares to `1`. -/
private theorem lambdaImage_pred_sq (k : ℕ) (hk : 1 ≤ k) {v : levelQuot G k}
    (hv : v ∈ lambdaImage G (k - 1) k) : v ^ 2 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hv
  rw [← map_pow]
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  have h := sq_mem_twoCentralSeries_succ G hx
  rwa [show k - 1 + 1 = k by omega] at h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- At its own level a `λ_{k-1}`-modification is central. -/
private theorem lambdaImage_pred_commute (k : ℕ) (hk : 1 ≤ k) {v : levelQuot G k}
    (hv : v ∈ lambdaImage G (k - 1) k) (g : levelQuot G k) : Commute v g := by
  have hgt : g ∈ lambdaImage G 1 k := by rw [lambdaImage_one_eq_top]; trivial
  have h := commP_mem_lambdaImage_add hv hgt
  rw [show k - 1 + 1 = k by omega, lambdaImage_self] at h
  have hc : commP v g = 1 := by simpa using h
  simp only [commP] at hc
  refine (commute_iff_eq v g).mpr ?_
  calc v * g = g * v * (v⁻¹ * g⁻¹ * v * g) := by group
    _ = g * v := by rw [hc, mul_one]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The χ-clause survives** (spike §2.1's design reason for the modulus `2^k`): a character
kills `λ_{k-1}` to precision `2^k`, one digit sharper than the generic layer bound, because
`λ_{k-1}(ℤ₂ˣ) ⊆ 1 + 2^kℤ₂` (`twoCentralSeries_units_le` at index `k - 1`). -/
private theorem chiLevel_lambdaImage_pred (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (k : ℕ)
    (hk : 3 ≤ k) {v : levelQuot G k} (hv : v ∈ lambdaImage G (k - 1) k) :
    chiLevel χ k v = 1 := by
  obtain ⟨g, hg, rfl⟩ := hv
  rw [chiLevel_levelMk]
  have h1 : χ g ∈ twoCentralSeries ℤ_[2]ˣ (k - 1) :=
    map_twoCentralSeries_le χ.toMonoidHom χ.continuous_toFun (k - 1) ⟨g, hg, rfl⟩
  have h2 := twoCentralSeries_units_le (k - 1) (by omega) h1
  rw [show k - 1 + 1 = k by omega] at h2
  exact MonoidHom.mem_ker.mp h2

end LevelFacts

/-- `D_R` is topologically generated by `{s, x, y}`, `Finset` form (private replica of the
Assembly-file packaging of `dr_topGen`; needed here for the tower instance pack). -/
private theorem drTopGenFinset :
    ∃ s : Finset (DR : Type),
      (Subgroup.closure (s : Set (DR : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{drS, drX, drY}, ?_⟩
  have h : (({drS, drX, drY} : Finset (DR : Type)) : Set (DR : Type))
      = ({drS, drX, drY} : Set (DR : Type)) := by simp
  rw [h]
  exact dr_topGen

/-- `D₀` is topologically generated by `{A, S, Y}`, `Finset` form (private replica). -/
private theorem d0TopGenFinset :
    ∃ s : Finset (D0 : Type),
      (Subgroup.closure (s : Set (D0 : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{d0A, d0S, d0Y}, ?_⟩
  have h : (({d0A, d0S, d0Y} : Finset (D0 : Type)) : Set (D0 : Type))
      = ({d0A, d0S, d0Y} : Set (D0 : Type)) := by simp
  rw [h]
  exact SectionThree.topGen_d0

/-! ### Frattini generation transfer (the non-generator argument at the level quotients) -/

section FrattiniTransfer

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]

open scoped commutatorElement in
/-- **`λ₂` is Frattini in every level quotient**: the image `λ₂λₘ/λₘ ≤ Qₘ` lies in the
Frattini-like subgroup `Φ(Qₘ) = Qₘ²[Qₘ, Qₘ]` (`SectionSeven.frattiniLike ⊤`).  Immediate
from the atomization principle `lambdaImage_induction` at `j = 1` (`λ₁ = ⊤`): `λ₂` is
verbally generated by squares and commutators of `λ₁`-elements, and both kinds of residue
are Frattini generators. -/
theorem lambdaImage_two_le_frattiniLike
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) :
    lambdaImage G 2 m ≤ SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)) := by
  intro q hq
  refine lambdaImage_induction G hfg hpro (j := 1) le_rfl
    (p := fun x => x ∈ SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)))
    ?_ ?_ (one_mem _) (fun _ _ hx hy => mul_mem hx hy) (fun _ hx => inv_mem hx) hq
  · intro v _
    rw [map_pow, pow_two]
    exact sq_mem_frattiniLike (Subgroup.mem_top _)
  · intro v _ g
    rw [map_commutatorElement, commutatorElement_def]
    exact comm_mem_frattiniLike (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **Generation transfer** (Frattini non-generation): a generating family `T` of a level
quotient `Qₘ` stays generating after each member is multiplied by an element of the
`λ₂`-image.  Indeed `T i = (T i · u i) · (u i)⁻¹` puts `⟨T⟩ = ⊤` inside `H ⊔ λ₂`, where
`H = ⟨T · u⟩`; since `Qₘ` is a finite `2`-group and `λ₂ ≤ Φ(Qₘ)`, Frattini non-generation
(`frattiniLike_nongen`) upgrades `H ⊔ Φ(Qₘ) = ⊤` to `H = ⊤`. -/
theorem closure_range_mul_eq_top_of_mem_lambdaImage_two
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {m : ℕ} {ι : Type*} (T u : ι → levelQuot G m)
    (hgen : Subgroup.closure (Set.range T) = ⊤)
    (hu : ∀ i, u i ∈ lambdaImage G 2 m) :
    Subgroup.closure (Set.range fun i => T i * u i) = ⊤ := by
  haveI := finite_levelQuot G hfg hpro m
  have h2 : IsPGroup 2 ↥(⊤ : Subgroup (levelQuot G m)) :=
    (isPGroup_levelQuot G hfg hpro m).of_equiv Subgroup.topEquiv.symm
  have hΦ := lambdaImage_two_le_frattiniLike G hfg hpro m
  have hle : Subgroup.closure (Set.range T) ≤
      Subgroup.closure (Set.range fun i => T i * u i) ⊔
        SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    have h1 : T i * u i ∈ Subgroup.closure (Set.range fun i => T i * u i) :=
      Subgroup.subset_closure ⟨i, rfl⟩
    have h3 : (u i)⁻¹ ∈ SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)) :=
      inv_mem (hΦ (hu i))
    have h4 : T i = T i * u i * (u i)⁻¹ := by group
    rw [SetLike.mem_coe, h4]
    exact Subgroup.mul_mem_sup h1 h3
  rw [hgen] at hle
  exact frattiniLike_nongen h2 le_top (le_antisymm le_top hle)

end FrattiniTransfer

/-- **Modification stability of `S^P_ₖ`, direction 1** (spike §2.1 + §2.4): `λ_{k-1}`-moves
preserve all three clauses — relator kill (the shift lands in `λₖ`), generation
(Frattini: `λ_{k-1} ⊆ λ₂` for `k ≥ 3`), and the χ-clause (`χ(λ_{k-1}) ⊆ 1 + 2^k ℤ₂` — the
design reason `P` survives the calculus).  Fill: L4a. -/
theorem sPR0_mul_mem (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) {w : Fin 3 → levelQuot (DR : Type) k}
    (hw : ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) k) :
    (fun i => T i * w i) ∈ sPR0 k := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hcen : ∀ i, ∀ g, Commute (w i) g :=
    fun i => lambdaImage_pred_commute k (by omega) (hw i)
  have hsq : ∀ i, w i ^ 2 = 1 := fun i => lambdaImage_pred_sq k (by omega) (hw i)
  refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
  · rw [d0Word_central_shift (hcen 0) (hcen 1) (hcen 2) (hsq 0) (hsq 1) (hsq 2)]
    exact hrel
  · exact closure_range_mul_eq_top_of_mem_lambdaImage_two (DR : Type) drTopGenFinset isProP_DR
      T w hgen fun i => lambdaImage_le_of_le (by omega) (hw i)
  · rw [map_mul, hchi i, chiLevel_lambdaImage_pred chiR k hk (hw i), mul_one]

/-- Modification stability, direction 2.  Fill: L4a. -/
theorem sPR2_mul_mem (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) {w : Fin 3 → levelQuot (D0 : Type) k}
    (hw : ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) k) :
    (fun i => T i * w i) ∈ sPR2 k := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hcen : ∀ i, ∀ g, Commute (w i) g :=
    fun i => lambdaImage_pred_commute k (by omega) (hw i)
  have hsq : ∀ i, w i ^ 2 = 1 := fun i => lambdaImage_pred_sq k (by omega) (hw i)
  refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
  · rw [drWord_central_shift (hcen 0) (hcen 1) (hcen 2) (hsq 1) (hsq 2)]
    exact hrel
  · exact closure_range_mul_eq_top_of_mem_lambdaImage_two (D0 : Type) d0TopGenFinset
      SectionThree.d0_isProP T w hgen fun i => lambdaImage_le_of_le (by omega) (hw i)
  · rw [map_mul, hchi i, chiLevel_lambdaImage_pred chiD0pres k hk (hw i), mul_one]

/-! ## The span theorem (spike §2.3; L4b) -/

/-- **The span theorem, free form, `r₀`-shape** (spike §2.3; Serre 252 §7 p. 151 with the
`2^{h-1}` erratum): for `k ≥ 3`, the graded layer `Zₖ(F₃)` is contained in the subgroup
generated by the `d̄`-image over `λ_{k-1}`-modifications at the standard generators
together with the two adapted tails `g₁^{2^{k-1}}, g₂^{2^{k-1}}` (the non-π'd generators
`(S, Y)`-slots = generators 1, 2).  Machine-verified `k ≤ 5` free / `k ≤ 6` towers
(20/20 rank rows).  Fill: L4b — via the structural reduction of spike §2.5(a); on a snag,
plan §7 O1/O2 apply (owner gate). -/
theorem span_free_r0 (k : ℕ) (hk : 3 ≤ k) :
    zLayer (freeProTwo : Type) k ≤
      Subgroup.closure
        ((fun w : Fin 3 → levelQuot (freeProTwo : Type) (k + 1) =>
            dbarWordR0 (levelMk (freeProTwo : Type) (k + 1) (freeGen 0))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 1))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 2)) w) ''
          {w | ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (k - 1) (k + 1)} ∪
        {levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1),
          levelMk (freeProTwo : Type) (k + 1) (freeGen 2) ^ 2 ^ (k - 1)}) :=
  span_free_r0_proof k hk

/-- The span theorem, free form, `r₂`-shape: tails at the `(s, x)`-slots = generators
0, 1 (the relator-adapted pair — spike §2.3's caught wrong-pair failure makes this
placement load-bearing).  Fill: L4b. -/
theorem span_free_r2 (k : ℕ) (hk : 3 ≤ k) :
    zLayer (freeProTwo : Type) k ≤
      Subgroup.closure
        ((fun w : Fin 3 → levelQuot (freeProTwo : Type) (k + 1) =>
            dbarWordR2 (levelMk (freeProTwo : Type) (k + 1) (freeGen 0))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 1))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 2)) w) ''
          {w | ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (k - 1) (k + 1)} ∪
        {levelMk (freeProTwo : Type) (k + 1) (freeGen 0) ^ 2 ^ (k - 1),
          levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1)}) :=
  span_free_r2_proof k hk

/-- **Span descent, direction 1** (spike §2.3: λ is verbal, so the statement descends
along `F₃ ↠ D_R` and holds *at any generating triple* of `Q_{k+1}(D_R)`; tails at the
`(S, Y)`-slots of the triple).  Fill: L4b (from `span_free_r0` + `map_twoCentralSeries_eq`
+ the congruence calculus).  -/
theorem span_descent_r0 (k : ℕ) (hk : 3 ≤ k)
    (T' : Fin 3 → levelQuot (DR : Type) (k + 1))
    (hgen : Subgroup.closure (Set.range T') = ⊤) :
    zLayer (DR : Type) k ≤
      Subgroup.closure
        ((fun w => dbarWordR0 (T' 0) (T' 1) (T' 2) w) ''
          {w : Fin 3 → levelQuot (DR : Type) (k + 1) |
            ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)} ∪
        {T' 1 ^ 2 ^ (k - 1), T' 2 ^ 2 ^ (k - 1)}) := by
  -- Instance pack on the finite discrete target `Q := Q_{k+1}(D_R)`.
  haveI := discreteTopology_levelQuot (DR : Type) drTopGenFinset isProP_DR (k + 1)
  haveI : Finite (levelQuot (DR : Type) (k + 1)) :=
    finite_levelQuot (DR : Type) drTopGenFinset isProP_DR (k + 1)
  have hproQ : IsProP 2 (levelQuot (DR : Type) (k + 1)) :=
    isProP_of_isPGroup (isPGroup_levelQuot (DR : Type) drTopGenFinset isProP_DR (k + 1))
  -- The classifying epi `φ : F₃ → Q` at the triple `T'`, and its λ-level factorization `ψ`.
  set φ := freeProTwoLift hproQ T' with hφ
  have hφs : Function.Surjective φ.toMonoidHom := by
    rw [← MonoidHom.range_eq_top, ← top_le_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨freeGen i, freeProTwoLift_freeGen hproQ T' i⟩
  have hkill : twoCentralSeries (freeProTwo : Type) (k + 1) ≤ φ.toMonoidHom.ker := by
    rw [← Subgroup.map_eq_bot_iff (f := φ.toMonoidHom), ← le_bot_iff,
      ← twoCentralSeries_levelQuot_self (DR : Type) drTopGenFinset isProP_DR (k + 1)]
    exact map_twoCentralSeries_le φ.toMonoidHom φ.continuous_toFun (k + 1)
  set ψ : levelQuot (freeProTwo : Type) (k + 1) →* levelQuot (DR : Type) (k + 1) :=
    QuotientGroup.lift _ φ.toMonoidHom hkill with hψ
  have hψmk : ψ.comp (levelMk (freeProTwo : Type) (k + 1)) = φ.toMonoidHom := by
    ext x
    exact QuotientGroup.lift_mk' _ hkill x
  -- λ-transport: `ψ` carries the free `lambdaImage` onto the tower `lambdaImage`, level-wise.
  have htrans : ∀ j : ℕ,
      (lambdaImage (freeProTwo : Type) j (k + 1)).map ψ = lambdaImage (DR : Type) j (k + 1) := by
    intro j
    rw [lambdaImage, Subgroup.map_map, hψmk,
      map_twoCentralSeries_eq φ.toMonoidHom φ.continuous_toFun hφs j,
      lambdaImage_eq_twoCentralSeries_levelQuot (DR : Type) drTopGenFinset isProP_DR j (k + 1)]
  -- Evaluation of `ψ` on the marked residues.
  have heval : ∀ j : Fin 3, ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = T' j := by
    intro j
    have h1 : ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = φ (freeGen j) :=
      QuotientGroup.lift_mk' _ hkill (freeGen j)
    rw [h1, hφ]
    exact freeProTwoLift_freeGen hproQ T' j
  -- Chase: lift a layer element, apply the free span theorem, push the generators forward.
  intro z hz
  rw [show zLayer (DR : Type) k = lambdaImage (DR : Type) k (k + 1) from rfl, ← htrans k] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hmap := Subgroup.mem_map_of_mem (K := Subgroup.closure _) ψ (span_free_r0 k hk hz₀)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rw [Set.image_union]
  refine Set.union_subset_union ?_ ?_
  · -- d̄-image terms: naturality of the shift word + λ-transport of the modifications.
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => ψ (w i), fun i => (htrans (k - 1)) ▸ Subgroup.mem_map_of_mem ψ (hw i), ?_⟩
    rw [map_dbarWordR0, heval 0, heval 1, heval 2]
  · -- Tail terms.
    rintro _ ⟨x, hx | hx, rfl⟩ <;> subst hx
    · exact Or.inl (by rw [map_pow, heval 1])
    · exact Or.inr (show _ = T' 2 ^ 2 ^ (k - 1) by rw [map_pow, heval 2])

/-- Span descent, direction 2 (tails at the `(s, x)`-slots).  Fill: L4b. -/
theorem span_descent_r2 (k : ℕ) (hk : 3 ≤ k)
    (T' : Fin 3 → levelQuot (D0 : Type) (k + 1))
    (hgen : Subgroup.closure (Set.range T') = ⊤) :
    zLayer (D0 : Type) k ≤
      Subgroup.closure
        ((fun w => dbarWordR2 (T' 0) (T' 1) (T' 2) w) ''
          {w : Fin 3 → levelQuot (D0 : Type) (k + 1) |
            ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)} ∪
        {T' 0 ^ 2 ^ (k - 1), T' 1 ^ 2 ^ (k - 1)}) := by
  -- Mirror of `span_descent_r0` in the `D₀`-tower with the `r₂`-shape and `(s, x)`-tails.
  haveI := discreteTopology_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1)
  haveI : Finite (levelQuot (D0 : Type) (k + 1)) :=
    finite_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1)
  have hproQ : IsProP 2 (levelQuot (D0 : Type) (k + 1)) :=
    isProP_of_isPGroup (isPGroup_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1))
  set φ := freeProTwoLift hproQ T' with hφ
  have hφs : Function.Surjective φ.toMonoidHom := by
    rw [← MonoidHom.range_eq_top, ← top_le_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨freeGen i, freeProTwoLift_freeGen hproQ T' i⟩
  have hkill : twoCentralSeries (freeProTwo : Type) (k + 1) ≤ φ.toMonoidHom.ker := by
    rw [← Subgroup.map_eq_bot_iff (f := φ.toMonoidHom), ← le_bot_iff,
      ← twoCentralSeries_levelQuot_self (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1)]
    exact map_twoCentralSeries_le φ.toMonoidHom φ.continuous_toFun (k + 1)
  set ψ : levelQuot (freeProTwo : Type) (k + 1) →* levelQuot (D0 : Type) (k + 1) :=
    QuotientGroup.lift _ φ.toMonoidHom hkill with hψ
  have hψmk : ψ.comp (levelMk (freeProTwo : Type) (k + 1)) = φ.toMonoidHom := by
    ext x
    exact QuotientGroup.lift_mk' _ hkill x
  have htrans : ∀ j : ℕ,
      (lambdaImage (freeProTwo : Type) j (k + 1)).map ψ = lambdaImage (D0 : Type) j (k + 1) := by
    intro j
    rw [lambdaImage, Subgroup.map_map, hψmk,
      map_twoCentralSeries_eq φ.toMonoidHom φ.continuous_toFun hφs j,
      lambdaImage_eq_twoCentralSeries_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient j (k + 1)]
  have heval : ∀ j : Fin 3, ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = T' j := by
    intro j
    have h1 : ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = φ (freeGen j) :=
      QuotientGroup.lift_mk' _ hkill (freeGen j)
    rw [h1, hφ]
    exact freeProTwoLift_freeGen hproQ T' j
  intro z hz
  rw [show zLayer (D0 : Type) k = lambdaImage (D0 : Type) k (k + 1) from rfl, ← htrans k] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hmap := Subgroup.mem_map_of_mem (K := Subgroup.closure _) ψ (span_free_r2 k hk hz₀)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rw [Set.image_union]
  refine Set.union_subset_union ?_ ?_
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => ψ (w i), fun i => (htrans (k - 1)) ▸ Subgroup.mem_map_of_mem ψ (hw i), ?_⟩
    rw [map_dbarWordR2, heval 0, heval 1, heval 2]
  · rintro _ ⟨x, hx | hx, rfl⟩ <;> subst hx
    · exact Or.inl (by rw [map_pow, heval 0])
    · exact Or.inr (show _ = T' 1 ^ 2 ^ (k - 1) by rw [map_pow, heval 1])

/-! ## The digit calculus (SL2's internal mechanism; spike §2.4, memo §1)

A level-`k` triple carries character values `χ(Tᵢ) = targetᵢ·ρᵢ` with `ρᵢ ≡ 1 mod 2^k`
(the invariant `P`); SL2 must kill the fresh level-`k` digits of the `ρᵢ`.  Three `2`-adic
facts do it, all proved here from scratch over `ℤ₂` (parity steps run through the residue
field `𝔽₂ = ZMod (2^1)`):

* **lifting the exponent** (`sharp_pow_two_pow`): `v₂(u − 1) = 2` forces
  `v₂(u^{2^m} − 1) = m + 2`.  All three relevant orientation units are `≡ 5 (mod 8)`
  (`η`, `X`, `S` — `chiTargetR0_three`, `chiTargetR2_three`), so their `2^{k-2}`-powers
  have a *sharp* digit at level `k` — and the `1 mod 2^k` deviation carried along by the
  actual triple is invisible there (`sharp_move`: its junk enters at `2^{2k-2}`, and
  `2k − 2 ≥ k + 1` exactly when `k ≥ 3`);
* **the dichotomy** (`dvd_or_dvd_mul`): against such a move, one of `ρ`, `ρ·μ` is
  `≡ 1 mod 2^{k+1}` — one move per free slot suffices;
* **the automatic digit** (`dvd_succ_of_sq`, memo §1.1): the slot carrying the relator's
  *square* needs no move at all.  Its level-`(k+1)` clause follows from the level-`(k+1)`
  relator clause itself: the corrected word lies in `λ_{k+1}`, so its χ-value lies in
  `1 + 2^{k+2}ℤ₂` (`twoCentralSeries_units_le` at index `k+1`), and with the `⁴`-slot
  contributing only at `2^{k+2}` this reads `ρ² ≡ 1 mod 2^{k+2}`, forcing
  `ρ ≡ 1 mod 2^{k+1}`.  Both exact target relations hold in `ℤ₂ˣ` on the nose:
  `(−1)²·1⁴ = 1` and `X⁻⁴·Y² = 1` (`YvalUnit_sq_eq`). -/

section DigitCalculus

open PadicInt

/-- `2^n ∣ x` read off the mod-`2^n` reduction. -/
private theorem two_pow_dvd_iff {n : ℕ} {x : ℤ_[2]} :
    (2 : ℤ_[2]) ^ n ∣ x ↔ toZModPow n x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  norm_num

/-- `2 ∣ x` read off the residue field. -/
private theorem two_dvd_iff {x : ℤ_[2]} : (2 : ℤ_[2]) ∣ x ↔ toZModPow 1 x = 0 := by
  rw [show ((2 : ℤ_[2])) = 2 ^ 1 by ring]
  exact two_pow_dvd_iff

/-- Two odd `2`-adic integers have even sum. -/
private theorem two_dvd_add_of_not_dvd {r m : ℤ_[2]} (hr : ¬ (2 : ℤ_[2]) ∣ r)
    (hm : ¬ (2 : ℤ_[2]) ∣ m) : (2 : ℤ_[2]) ∣ r + m := by
  rw [two_dvd_iff] at hr hm ⊢
  rw [map_add]
  revert hr hm
  generalize toZModPow 1 r = a
  generalize toZModPow 1 m = b
  revert a b
  decide

/-- A product of odd `2`-adic integers is odd. -/
private theorem two_not_dvd_mul {r m : ℤ_[2]} (hr : ¬ (2 : ℤ_[2]) ∣ r)
    (hm : ¬ (2 : ℤ_[2]) ∣ m) : ¬ (2 : ℤ_[2]) ∣ r * m := by
  rw [two_dvd_iff] at hr hm ⊢
  rw [map_mul]
  revert hr hm
  generalize toZModPow 1 r = a
  generalize toZModPow 1 m = b
  revert a b
  decide

/-- `1 + 2x` is odd. -/
private theorem two_not_dvd_one_add_two_mul (x : ℤ_[2]) : ¬ (2 : ℤ_[2]) ∣ 1 + 2 * x := by
  rw [two_dvd_iff, map_add, map_one, map_mul, map_ofNat]
  generalize toZModPow 1 x = a
  revert a
  decide

/-- Adding an even number preserves oddness. -/
private theorem two_not_dvd_add_two_mul {r : ℤ_[2]} (hr : ¬ (2 : ℤ_[2]) ∣ r) (x : ℤ_[2]) :
    ¬ (2 : ℤ_[2]) ∣ r + 2 * x := fun h => hr (by simpa using dvd_sub h (Dvd.intro x rfl))

/-- Congruences to `1` multiply. -/
private theorem dvd_mul_sub_one {A B : ℤ_[2]} {n : ℕ} (hA : (2 : ℤ_[2]) ^ n ∣ A - 1)
    (hB : (2 : ℤ_[2]) ^ n ∣ B - 1) : (2 : ℤ_[2]) ^ n ∣ A * B - 1 := by
  obtain ⟨s, hs⟩ := hA
  obtain ⟨t, ht⟩ := hB
  exact ⟨s * B + t, by linear_combination B * hs + ht⟩

/-- Congruences to `1` cancel. -/
private theorem dvd_sub_one_of_mul {A B : ℤ_[2]} {n : ℕ} (h : (2 : ℤ_[2]) ^ n ∣ A * B - 1)
    (hB : (2 : ℤ_[2]) ^ n ∣ B - 1) : (2 : ℤ_[2]) ^ n ∣ A - 1 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := hB
  exact ⟨s - A * t, by linear_combination hs - A * ht⟩

/-- Congruences to `1` are inherited by powers. -/
private theorem dvd_pow_sub_one {A : ℤ_[2]} {n : ℕ} (hA : (2 : ℤ_[2]) ^ n ∣ A - 1) (b : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ A ^ b - 1 := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ]; exact dvd_mul_sub_one ih hA

/-- **Lifting the exponent**: `v₂(u − 1) = 2` forces `v₂(u^{2^m} − 1) = m + 2`. -/
private theorem sharp_pow_two_pow {u c : ℤ_[2]} (hc : u - 1 = 2 ^ 2 * c)
    (hc2 : ¬ (2 : ℤ_[2]) ∣ c) (m : ℕ) :
    ∃ d : ℤ_[2], u ^ 2 ^ m - 1 = 2 ^ (m + 2) * d ∧ ¬ (2 : ℤ_[2]) ∣ d := by
  induction m with
  | zero => exact ⟨c, by simpa using hc, hc2⟩
  | succ m ih =>
    obtain ⟨d, hd, hd2⟩ := ih
    refine ⟨d * (1 + 2 ^ (m + 1) * d), ?_, ?_⟩
    · have hu : u ^ 2 ^ m = 1 + 2 ^ (m + 2) * d := by linear_combination hd
      have h : u ^ 2 ^ (m + 1) = (u ^ 2 ^ m) ^ 2 := by rw [← pow_mul, ← pow_succ]
      rw [h, hu]
      ring
    · refine two_not_dvd_mul hd2 ?_
      rw [show (2 : ℤ_[2]) ^ (m + 1) * d = 2 * (2 ^ m * d) by ring]
      exact two_not_dvd_one_add_two_mul _

/-- Squaring deepens a congruence: `ρ ≡ 1 mod 2^k` gives `ρ^{2^n} ≡ 1 mod 2^{k+n}`. -/
private theorem dvd_pow_two_pow_sub_one {ρ : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (h : (2 : ℤ_[2]) ^ k ∣ ρ - 1) (n : ℕ) : (2 : ℤ_[2]) ^ (k + n) ∣ ρ ^ 2 ^ n - 1 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hfac : ρ ^ 2 ^ (n + 1) - 1 = (ρ ^ 2 ^ n - 1) * (ρ ^ 2 ^ n + 1) := by
      rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by ring, pow_mul]; ring
    have h2 : (2 : ℤ_[2]) ∣ ρ ^ 2 ^ n + 1 := by
      obtain ⟨c, hc⟩ := ih
      refine ⟨2 ^ (k + n - 1) * c + 1, ?_⟩
      have hρ : ρ ^ 2 ^ n = 1 + 2 ^ (k + n) * c := by linear_combination hc
      rw [hρ, show (2 : ℤ_[2]) ^ (k + n) = 2 * 2 ^ (k + n - 1) by
        rw [← pow_succ']; congr 1; omega]
      ring
    rw [hfac, show k + (n + 1) = k + n + 1 by ring, pow_succ]
    exact mul_dvd_mul ih h2

/-- A deeper factor does not disturb a sharp digit. -/
private theorem sharp_mul_of_dvd {μ ρ d : ℤ_[2]} {k : ℕ} (hμ : μ - 1 = 2 ^ k * d)
    (hd : ¬ (2 : ℤ_[2]) ∣ d) (hρ : (2 : ℤ_[2]) ^ (k + 1) ∣ ρ - 1) :
    ∃ d' : ℤ_[2], μ * ρ - 1 = 2 ^ k * d' ∧ ¬ (2 : ℤ_[2]) ∣ d' := by
  obtain ⟨e, he⟩ := hρ
  have hρ' : ρ = 1 + 2 * (2 ^ k * e) := by rw [pow_succ'] at he; linear_combination he
  have hμ' : μ = 1 + 2 ^ k * d := by linear_combination hμ
  refine ⟨d * ρ + 2 * e, by rw [hμ', hρ']; ring, ?_⟩
  exact two_not_dvd_add_two_mul (two_not_dvd_mul hd (hρ' ▸ two_not_dvd_one_add_two_mul _)) e

/-- **The digit dichotomy**: a sharp level-`k` move fixes the level-`k` digit of `ρ`. -/
private theorem dvd_or_dvd_mul {ρ μ d : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (hρ : (2 : ℤ_[2]) ^ k ∣ ρ - 1) (hμ : μ - 1 = 2 ^ k * d) (hd : ¬ (2 : ℤ_[2]) ∣ d) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ρ - 1 ∨ (2 : ℤ_[2]) ^ (k + 1) ∣ ρ * μ - 1 := by
  obtain ⟨r, hr⟩ := hρ
  by_cases hr2 : (2 : ℤ_[2]) ∣ r
  · obtain ⟨c, rfl⟩ := hr2
    exact Or.inl ⟨c, by rw [hr, pow_succ]; ring⟩
  · refine Or.inr ?_
    obtain ⟨c, hc⟩ := two_dvd_add_of_not_dvd hr2 hd
    refine ⟨c + 2 ^ (k - 1) * (r * d), ?_⟩
    have hρ' : ρ = 1 + 2 ^ k * r := by linear_combination hr
    have hμ' : μ = 1 + 2 ^ k * d := by linear_combination hμ
    have hpow : (2 : ℤ_[2]) ^ k * 2 ^ k = 2 ^ (k + 1) * 2 ^ (k - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hρ', hμ']
    linear_combination (2 : ℤ_[2]) ^ k * hc + (r * d) * hpow

/-- **The automatic digit** (memo §1.1): `ρ ≡ 1 mod 2^k` together with
`ρ² ≡ 1 mod 2^{k+2}` already gives `ρ ≡ 1 mod 2^{k+1}` (`k ≥ 2`). -/
private theorem dvd_succ_of_sq {ρ : ℤ_[2]} {k : ℕ} (hk : 2 ≤ k)
    (hρ : (2 : ℤ_[2]) ^ k ∣ ρ - 1) (hsq : (2 : ℤ_[2]) ^ (k + 2) ∣ ρ ^ 2 - 1) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ρ - 1 := by
  obtain ⟨r, hr⟩ := hρ
  obtain ⟨t, ht⟩ := hsq
  have hρ' : ρ = 1 + 2 ^ k * r := by linear_combination hr
  have hpow : (2 : ℤ_[2]) ^ k * 2 ^ k = 2 ^ (k + 1) * 2 ^ (k - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have key : (2 : ℤ_[2]) ^ (k + 1) * (r * (1 + 2 ^ (k - 1) * r)) = 2 ^ (k + 1) * (2 * t) := by
    rw [hρ'] at ht
    linear_combination ht - (r * r) * hpow
  have hcancel : r * (1 + 2 ^ (k - 1) * r) = 2 * t :=
    mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) key
  have hodd : ¬ (2 : ℤ_[2]) ∣ 1 + 2 ^ (k - 1) * r := by
    rw [show (2 : ℤ_[2]) ^ (k - 1) * r = 2 * (2 ^ (k - 2) * r) by
      rw [← mul_assoc, ← pow_succ']; congr 2; omega]
    exact two_not_dvd_one_add_two_mul _
  have h2r : (2 : ℤ_[2]) ∣ r := by
    by_contra hr2
    exact two_not_dvd_mul hr2 hodd ⟨t, hcancel⟩
  obtain ⟨c, rfl⟩ := h2r
  exact ⟨c, by rw [hr, pow_succ]; ring⟩

/-- A `2`-adic integer that is `5 mod 8` has a sharp digit at level `2`. -/
private theorem sharp_two_of_toZModPow_three {u : ℤ_[2]} (h : toZModPow 3 u = 5) :
    ∃ c : ℤ_[2], u - 1 = 2 ^ 2 * c ∧ ¬ (2 : ℤ_[2]) ∣ c := by
  have h8 : (2 : ℤ_[2]) ^ 3 ∣ u - 1 - 4 := by
    rw [two_pow_dvd_iff, map_sub, map_sub, h, map_one, map_ofNat]
    decide
  obtain ⟨e, he⟩ := h8
  exact ⟨1 + 2 * e, by linear_combination he, two_not_dvd_one_add_two_mul e⟩

/-- **The move digit** (memo §1.2): the `2^{k-2}`-power of a unit whose target is `5 mod 8`
has a sharp level-`k` digit — the `1 mod 2^k` deviation of the actual triple slot only
enters at `2^{2k-2}`, and `2k − 2 ≥ k + 1` exactly at the calculus threshold `k ≥ 3`. -/
private theorem sharp_move {base c : ℤ_[2]ˣ} {k : ℕ} (hk : 3 ≤ k)
    (hbase : toZModPow 3 ((base : ℤ_[2]ˣ) : ℤ_[2]) = 5)
    (hc : (2 : ℤ_[2]) ^ k ∣ ((c * base⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    ∃ d : ℤ_[2], ((c ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
  obtain ⟨e, he, he2⟩ := sharp_two_of_toZModPow_three hbase
  obtain ⟨d, hd, hd2⟩ := sharp_pow_two_pow he he2 (k - 2)
  rw [show k - 2 + 2 = k by omega] at hd
  have hjunk : (2 : ℤ_[2]) ^ (k + 1) ∣ ((c * base⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 ^ (k - 2) - 1 :=
    dvd_trans (pow_dvd_pow 2 (by omega : k + 1 ≤ k + (k - 2)))
      (dvd_pow_two_pow_sub_one (by omega) hc (k - 2))
  obtain ⟨d', hd', hd'2⟩ := sharp_mul_of_dvd hd hd2 hjunk
  refine ⟨d', ?_, hd'2⟩
  rw [← hd']
  have hbc : base * (c * base⁻¹) = c := by
    rw [mul_comm c base⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← mul_pow, ← Units.val_mul, hbc, Units.val_pow_eq_pow_val]

end DigitCalculus

/-! ### The χ-plumbing and the kernel witnesses (SL2 fill helpers) -/

/-- Two `2`-adic units agree mod `2^n` exactly when their ratio is `1 mod 2^n`. -/
private theorem units_map_eq_iff_dvd {n : ℕ} {x y : ℤ_[2]ˣ} :
    Units.map (PadicInt.toZModPow n).toMonoidHom x =
        Units.map (PadicInt.toZModPow n).toMonoidHom y ↔
      (2 : ℤ_[2]) ^ n ∣ ((x * y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have h : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  rw [← h, ← mem_ker_units_toZModPow_iff, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

section ChiPlumbing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The χ-clause of the levelwise sets, read as a `2`-adic congruence at a chosen lift. -/
private theorem dvd_of_chiLevel_eq (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (target : ℤ_[2]ˣ)
    {n : ℕ} {q : levelQuot G n} {a : G} (haq : levelMk G n a = q)
    (h : chiLevel χ n q = Units.map (PadicInt.toZModPow n).toMonoidHom target) :
    (2 : ℤ_[2]) ^ n ∣ ((χ a * target⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
  units_map_eq_iff_dvd.mp (by rwa [← haq, chiLevel_levelMk] at h)

/-- The converse direction: a `2`-adic congruence certifies the χ-clause. -/
private theorem chiLevel_eq_of_dvd (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (target : ℤ_[2]ˣ)
    {n : ℕ} {q : levelQuot G n} {a : G} (haq : levelMk G n a = q)
    (h : (2 : ℤ_[2]) ^ n ∣ ((χ a * target⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    chiLevel χ n q = Units.map (PadicInt.toZModPow n).toMonoidHom target := by
  rw [← haq, chiLevel_levelMk]
  exact units_map_eq_iff_dvd.mpr h

/-- **The χ-depth bound at index `k`** (`twoCentralSeries_units_le`): a word that dies in
`Qₖ` has χ-value in `1 + 2^{k+1}ℤ₂`.  This is the mechanism of `chiLevel_lambdaImage_pred`,
re-instantiated one digit deeper than the generic layer bound. -/
private theorem dvd_chi_of_mem_twoCentralSeries (χ : ContinuousMonoidHom G ℤ_[2]ˣ) {k : ℕ}
    (hk : 2 ≤ k) {r : G} (hr : r ∈ twoCentralSeries G k) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ((χ r : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have h1 : χ r ∈ twoCentralSeries ℤ_[2]ˣ k :=
    map_twoCentralSeries_le χ.toMonoidHom χ.continuous_toFun k ⟨r, hr, rfl⟩
  simpa using mem_ker_units_toZModPow_iff.mp (twoCentralSeries_units_le k hk h1)

/-- `2`-power powers of any element sink into the λ-tower (`λ₁ = ⊤` plus `λⱼ² ⊆ λ_{j+1}`). -/
private theorem pow_two_pow_mem_twoCentralSeries (g : G) (n : ℕ) :
    g ^ 2 ^ n ∈ twoCentralSeries G (1 + n) := by
  induction n with
  | zero => simp [twoCentralSeries_one]
  | succ n ih =>
    have h : g ^ 2 ^ (n + 1) = (g ^ 2 ^ n) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [h, show 1 + (n + 1) = 1 + n + 1 from rfl]
    exact sq_mem_twoCentralSeries_succ G ih

/-- The level-quotient form of the previous lemma. -/
private theorem pow_two_pow_mem_lambdaImage {m : ℕ} (q : levelQuot G m) (n : ℕ) :
    q ^ 2 ^ n ∈ lambdaImage G (1 + n) m := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G m q
  exact ⟨g ^ 2 ^ n, pow_two_pow_mem_twoCentralSeries g n, map_pow _ _ _⟩

end ChiPlumbing

/-- **The `r₀` kernel witnesses** (memo §1.2): the `s`-slot moves by `p` and the `y`-slot by
`q`, where `p` commutes with `y` and `q` commutes with `s·y`.  Then `d̄` dies: the `p`-bracket
vanishes outright, and the two `q`-brackets recombine into `[q, s·y] = 1` (centrality lets
them be collected).  Both free digit moves of `ker d̄` have this shape — `p` a power of `y`,
`q` a power of `s·y`. -/
private theorem dbarWordR0_kernel_witness {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 3 ≤ k) (a s y p q : levelQuot G (k + 1))
    (hq : q ∈ lambdaImage G (k - 1) (k + 1)) (hp : commP p y = 1)
    (hqsy : commP q (s * y) = 1) :
    dbarWordR0 a s y ![1, p * q, q] = 1 := by
  have hone : ∀ z : levelQuot G (k + 1), commP (1 : levelQuot G (k + 1)) z = 1 := by
    intro z; simp only [commP]; group
  have hzs : commP q s ∈ zLayer G k := commP_mem_zLayer k hk hq s
  have hleft : commP (p * q) y = commP q y := by
    rw [commP_mul_left, hp, mul_one, inv_mul_cancel, one_mul]
  have hsplit : commP q y * commP q s = 1 := by
    rw [← hqsy, commP_mul_right, conj_eq_self_of_commP_eq_one
      (commP_eq_one_of_mul_comm (zLayer_commute hzs y).eq)]
  simp only [dbarWordR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_pow, hone, one_mul, hleft]
  exact hsplit

/-- **The `r₂` kernel witnesses** (memo §1.2): the `s`-slot moves by a power of `x` and the
`x`-slot by a power of `s`; each move kills its own bracket definitionally, and the `y`-slot
— the only one entering `d̄` through a square — is left alone.  No hypotheses at all. -/
private theorem dbarWordR2_kernel_witness {H : Type*} [Group H] (s x y p q : H)
    (hp : commP p x = 1) (hq : commP q s = 1) : dbarWordR2 s x y ![p, q, 1] = 1 := by
  have hone : ∀ z : H, commP (1 : H) z = 1 := by intro z; simp only [commP]; group
  simp only [dbarWordR2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_pow, hone, hp, hq, mul_one]

/-- **Generation lifts along the tower**: a subgroup of `Q_{k+1}` surjecting onto `Qₖ` is
everything — the kernel `Zₖ ≤ λ₂` is Frattini (`lambdaImage_two_le_frattiniLike`), so
non-generation applies. -/
private theorem eq_top_of_map_levelProj_eq_top (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {k : ℕ} (hk : 2 ≤ k) {H : Subgroup (levelQuot G (k + 1))}
    (h : H.map (levelProj G k) = ⊤) : H = ⊤ := by
  haveI := finite_levelQuot G hfg hpro (k + 1)
  have h2 : IsPGroup 2 ↥(⊤ : Subgroup (levelQuot G (k + 1))) :=
    (isPGroup_levelQuot G hfg hpro (k + 1)).of_equiv Subgroup.topEquiv.symm
  have hΦ := lambdaImage_two_le_frattiniLike G hfg hpro (k + 1)
  refine frattiniLike_nongen h2 le_top (le_antisymm le_top ?_)
  intro q _
  obtain ⟨x, hx, hxq⟩ : levelProj G k q ∈ H.map (levelProj G k) := by rw [h]; trivial
  have hz : x⁻¹ * q ∈ zLayer G k := by
    rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, map_mul, map_inv, hxq, inv_mul_cancel]
  have hker : x⁻¹ * q ∈ lambdaImage G 2 (k + 1) := lambdaImage_le_of_le (by omega) hz
  rw [show q = x * (x⁻¹ * q) by group]
  exact Subgroup.mul_mem_sup hx (hΦ hker)

/-! ### The χ-twisted crossed derivations (SL1's separating functionals)

SL1 needs functionals on `Zₖ` that kill `Im d̄` and the defect but pair non-degenerately with
the two tails.  The numerics report (`docs/orchestration/sl1-numerics.md` §6) identifies them
as digit-`(k−1)` shadows of **θ-crossed derivations**; the repo already carries the exact
(un-truncated) version of that calculus — Labute's descent condition
`IsLabuteOrientationDatum` (`GQ2/Roe/CrossedDerivation.lean`), which says that for the
canonical orientation `χ` **every** crossed derivation `D(gh) = Dg + χ(g)·Dh` kills the
presenting relator.  So the functionals descend to the towers *on the nose*, with no relation
module theory: a derivation is just the `.u`-component of a hom into `A ⋊ ℤ₂ˣ`.

Since `ℤ₂ ⋊ ℤ₂ˣ` is not known here to be pro-2 (the universal properties `drLiftHom` /
`d0LiftHom` demand that), we run the whole calculus at the finite shadow
`WL N = ℤ/2^N ⋊ (ℤ/2^N)ˣ`, which is a finite 2-group by cardinality.  All the sharp 2-adic
input (the orientation values, `η⁻¹ = −3`, `v₂(X−1) = v₂(S−1) = 2`, `v₂(Y+1) = 3`) stays in
`ℤ₂` and is pushed down by the reduction ring hom. -/

open FoxH in
/-- The **finite lift group** `ℤ/2^N ⋊ (ℤ/2^N)ˣ` (`WordLift`, product law
`(u,g)(v,h) = (u + g·v, gh)`): the mod-`2^N` shadow of Labute's `ℤ₂(χ) ⋊ ℤ₂ˣ`. -/
private abbrev WL (N : ℕ) : Type := FoxH.WordLift (ZMod (2 ^ N)) ((ZMod (2 ^ N))ˣ)

local instance instTopologicalSpaceWL (N : ℕ) : TopologicalSpace (WL N) := ⊥
local instance instDiscreteTopologyWL (N : ℕ) : DiscreteTopology (WL N) := ⟨rfl⟩
local instance instTopUnitsZMod (N : ℕ) : TopologicalSpace ((ZMod (2 ^ N))ˣ) := ⊥
local instance instDiscUnitsZMod (N : ℕ) : DiscreteTopology ((ZMod (2 ^ N))ˣ) := ⟨rfl⟩

section CrossedFunctional

open FoxH

/-- `WL N` is a finite 2-group: `|ℤ/2^N| · |(ℤ/2^N)ˣ| = 2^N · 2^{N-1}`. -/
private theorem isPGroup_WL {N : ℕ} (hN : 1 ≤ N) : IsPGroup 2 (WL N) := by
  have hcard : Nat.card (WL N) = 2 ^ (N + (N - 1)) := by
    have h1 : Nat.card (WL N) = Nat.card (ZMod (2 ^ N)) * Nat.card ((ZMod (2 ^ N))ˣ) := by
      rw [Nat.card_congr (WordLift.equivProd (A := ZMod (2 ^ N)) (C := (ZMod (2 ^ N))ˣ)),
        Nat.card_prod]
    have h2 : Nat.card (ZMod (2 ^ N)) = 2 ^ N := by
      haveI : NeZero (2 ^ N) := ⟨by positivity⟩
      simp [Nat.card_eq_fintype_card]
    have h3 : Nat.card ((ZMod (2 ^ N))ˣ) = 2 ^ (N - 1) := by
      haveI : NeZero (2 ^ N) := ⟨by positivity⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    rw [h1, h2, h3, ← pow_add]
  exact IsPGroup.of_card hcard

/-- `WL N` is pro-2, hence a legal target for `drLiftHom` / `d0LiftHom`. -/
private theorem isProP_WL {N : ℕ} (hN : 1 ≤ N) : IsProP 2 (WL N) :=
  isProP_of_isPGroup (isPGroup_WL hN)

/-- The reduction `ℤ₂ ⋊ ℤ₂ˣ → ℤ/2^N ⋊ (ℤ/2^N)ˣ` (a group hom: reduction is a ring hom, so it
intertwines the two product laws). -/
private noncomputable def redWL (N : ℕ) : WordLift ℤ_[2] ℤ_[2]ˣ →* WL N where
  toFun p := ⟨PadicInt.toZModPow N p.u, Units.map (PadicInt.toZModPow N).toMonoidHom p.g⟩
  map_one' := by ext <;> simp
  map_mul' p q := by
    ext
    · show PadicInt.toZModPow N (p.u + (p.g : ℤ_[2]) * q.u)
        = PadicInt.toZModPow N p.u
          + ((Units.map (PadicInt.toZModPow N).toMonoidHom p.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))
            * PadicInt.toZModPow N q.u
      simp
    · exact map_mul _ _ _

@[simp] private theorem redWL_u (N : ℕ) (p : WordLift ℤ_[2] ℤ_[2]ˣ) :
    (redWL N p).u = PadicInt.toZModPow N p.u := rfl

@[simp] private theorem redWL_g (N : ℕ) (p : WordLift ℤ_[2] ℤ_[2]ˣ) :
    (redWL N p).g = Units.map (PadicInt.toZModPow N).toMonoidHom p.g := rfl

/-- The `.g`-projection `A ⋊ C → C`, as a monoid hom. -/
private def wlBase (N : ℕ) : WL N →* (ZMod (2 ^ N))ˣ where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Powers in `R ⋊ Rˣ`: the offset picks up the geometric sum of the base. -/
private theorem wl_pow {R : Type*} [CommRing R] (u : R) (g : Rˣ) (m : ℕ) :
    ((⟨u, g⟩ : WordLift R Rˣ) ^ m) = ⟨(∑ j ∈ Finset.range m, (g : R) ^ j) * u, g ^ m⟩ := by
  induction m with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext
    · show (∑ j ∈ Finset.range m, (g : R) ^ j) * u + ((g ^ m : Rˣ) : R) * u
        = (∑ j ∈ Finset.range (m + 1), (g : R) ^ j) * u
      rw [Finset.sum_range_succ, add_mul, Units.val_pow_eq_pow_val]
    · simp [pow_succ]

/-! #### `2`-power divisibility in `ℤ/2^N`, read through the reductions -/

private theorem two_pow_zmod_self {j : ℕ} : (2 : ZMod (2 ^ j)) ^ j = 0 := by
  have h : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact h

/-- Divisibility by `2^j` in `ℤ/2^N` (`j ≤ N`) is the vanishing of the mod-`2^j` reduction. -/
private theorem two_pow_dvd_zmod_iff {N j : ℕ} (hj : j ≤ N) {x : ZMod (2 ^ N)} :
    (2 : ZMod (2 ^ N)) ^ j ∣ x ↔ ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) x = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_pow, map_ofNat, two_pow_zmod_self, zero_mul]
  · intro h
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) x
    rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨(c : ZMod (2 ^ N)), by rw [hc]; push_cast; ring⟩

/-- Divisibility by `2^j` in `ℤ/2^N` is read off any `2`-adic lift (`j ≤ N`). -/
private theorem two_pow_dvd_toZModPow_iff {N j : ℕ} (hj : j ≤ N) {x : ℤ_[2]} :
    (2 : ZMod (2 ^ N)) ^ j ∣ PadicInt.toZModPow N x ↔ (2 : ℤ_[2]) ^ j ∣ x := by
  rw [two_pow_dvd_zmod_iff hj, two_pow_dvd_iff, ZMod.castHom_apply, PadicInt.cast_toZModPow j N hj]

/-- Units of `ℤ/2^N` are odd. -/
private theorem two_dvd_units_sub_one {N : ℕ} (hN : 1 ≤ N) (g : (ZMod (2 ^ N))ˣ) :
    (2 : ZMod (2 ^ N)) ∣ (g : ZMod (2 ^ N)) - 1 := by
  have h1 : (1 : ℕ) ≤ N := hN
  have hcast := two_pow_dvd_zmod_iff (N := N) (j := 1) h1 (x := (g : ZMod (2 ^ N)) - 1)
  rw [pow_one] at hcast
  refine hcast.mpr ?_
  set ρ := ZMod.castHom (pow_dvd_pow 2 h1) (ZMod (2 ^ 1)) with hρ
  have hu : IsUnit (ρ (g : ZMod (2 ^ N))) := (g.isUnit).map ρ
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hone : ρ (g : ZMod (2 ^ N)) = 1 :=
    (by decide : ∀ a b : ZMod (2 ^ 1), a * b = 1 → a = 1) _ _ hv
  rw [map_sub, hone, map_one, sub_self]

/-- Halving: if `2^k` divides `2^{k-1}·z` in `ℤ/2^N` (`k ≤ N`), then `z` is even. -/
private theorem two_dvd_of_two_pow_dvd_mul {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    {z : ZMod (2 ^ N)} (h : (2 : ZMod (2 ^ N)) ^ k ∣ (2 : ZMod (2 ^ N)) ^ (k - 1) * z) :
    (2 : ZMod (2 ^ N)) ∣ z := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) z
  rw [two_pow_dvd_zmod_iff hkN] at h
  rw [show (2 : ZMod (2 ^ N)) = ((2 : ℤ) : ZMod (2 ^ N)) by push_cast; ring, ← Int.cast_pow,
    ← Int.cast_mul, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h2 : (2 : ℤ) ∣ m := by
    have hpow : ((2 ^ k : ℕ) : ℤ) = 2 ^ (k - 1) * 2 := by
      push_cast
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at h
    have hne : (2 : ℤ) ^ (k - 1) ≠ 0 := by positivity
    exact (mul_dvd_mul_iff_left hne).mp (by rw [mul_comm ((2 : ℤ) ^ (k - 1)) 2] at h ⊢; exact h)
  obtain ⟨c, hc⟩ := h2
  exact ⟨(c : ZMod (2 ^ N)), by rw [hc]; push_cast; ring⟩

/-! #### The congruence filtration of `WL N` and the `λ`-bound -/

open scoped commutatorElement in
/-- The repo-convention commutator in `R ⋊ Rˣ` (the base components cancel). -/
private theorem wl_commutator {R : Type*} [CommRing R] (p q : WordLift R Rˣ) :
    ⁅p, q⁆ = ⟨p.u * (1 - (q.g : R)) + q.u * ((p.g : R) - 1), 1⟩ := by
  have hpg : ((p.g : R)) * ((p.g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqg : ((q.g : R)) * ((q.g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hpq : ((p.g : R)) * ((q.g : R)) * ((p.g⁻¹ : Rˣ) : R) * ((q.g⁻¹ : Rˣ) : R) = 1 := by
    calc ((p.g : R)) * ((q.g : R)) * ((p.g⁻¹ : Rˣ) : R) * ((q.g⁻¹ : Rˣ) : R)
        = (((p.g : R)) * ((p.g⁻¹ : Rˣ) : R)) * (((q.g : R)) * ((q.g⁻¹ : Rˣ) : R)) := by ring
      _ = 1 := by rw [hpg, hqg]; ring
  rw [commutatorElement_def]
  ext
  · simp only [WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, Units.smul_def,
      smul_eq_mul, Units.val_mul]
    linear_combination (-(p.u) * (q.g : R)) * hpg + (-(q.u)) * hpq
  · have hg : (p * q * p⁻¹ * q⁻¹).g = (1 : Rˣ) := by
      show p.g * q.g * p.g⁻¹ * q.g⁻¹ = 1
      rw [mul_comm p.g q.g]
      group
    rw [hg]

/-- The **congruence subgroup** `K_j = {(u,g) : 2^{j-1} ∣ u, 2^j ∣ g − 1}` of `WL N`: the
receptacle of the lower 2-central series (Labute's filtration bound in its finite shadow). -/
private def wlCong (N j : ℕ) : Subgroup (WL N) where
  carrier := {p | (2 : ZMod (2 ^ N)) ^ (j - 1) ∣ p.u ∧
    (2 : ZMod (2 ^ N)) ^ j ∣ (p.g : ZMod (2 ^ N)) - 1}
  one_mem' := by
    refine ⟨by simp, ?_⟩
    show (2 : ZMod (2 ^ N)) ^ j ∣ ((1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
    simp
  mul_mem' := by
    rintro p q ⟨hpu, hpg⟩ ⟨hqu, hqg⟩
    refine ⟨?_, ?_⟩
    · rw [WordLift.mul_u, Units.smul_def, smul_eq_mul]
      exact dvd_add hpu (Dvd.dvd.mul_left hqu _)
    · rw [WordLift.mul_g]
      have hexp : ((p.g * q.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
          = ((p.g : ZMod (2 ^ N)) - 1) * (q.g : ZMod (2 ^ N)) + ((q.g : ZMod (2 ^ N)) - 1) := by
        push_cast
        ring
      rw [hexp]
      exact dvd_add (Dvd.dvd.mul_right hpg _) hqg
  inv_mem' := by
    rintro p ⟨hpu, hpg⟩
    refine ⟨?_, ?_⟩
    · rw [WordLift.inv_u, Units.smul_def, smul_eq_mul]
      exact (Dvd.dvd.mul_left hpu _).neg_right
    · rw [WordLift.inv_g]
      have hpginv : ((p.g : ZMod (2 ^ N))) * ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hexp : ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
          = -(((p.g : ZMod (2 ^ N)) - 1) * ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) := by
        linear_combination hpginv
      rw [hexp]
      exact (Dvd.dvd.mul_right hpg _).neg_right

private theorem mem_wlCong {N j : ℕ} {p : WL N} :
    p ∈ wlCong N j ↔ (2 : ZMod (2 ^ N)) ^ (j - 1) ∣ p.u ∧
      (2 : ZMod (2 ^ N)) ^ j ∣ (p.g : ZMod (2 ^ N)) - 1 := Iff.rfl

/-- **The filtration bound** (the finite shadow of `D(λ_j) ⊆ 2^{j-1}ℤ₂` and
`χ(λ_j) ⊆ 1 + 2^jℤ₂`): the lower 2-central series of `WL N` sinks into the congruence
filtration.  Both halves are needed: the base congruence drives the offset congruence one
step deeper at each squaring and each commutator. -/
private theorem twoCentralSeries_WL_le {N : ℕ} (hN : 1 ≤ N) {j : ℕ} (hj : 1 ≤ j) :
    twoCentralSeries (WL N) j ≤ wlCong N j := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro p _
    exact ⟨by simp, by rw [pow_one]; exact two_dvd_units_sub_one hN p.g⟩
  | succ j hj ih =>
    rw [twoCentralSeries_succ (WL N) hj]
    refine le_trans (twoCentralSucc_mono ih) ?_
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_discrete _)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨hpu, hpg⟩ := hp
      show p ^ 2 ∈ wlCong N (j + 1)
      have h2g : (2 : ZMod (2 ^ N)) ∣ (p.g : ZMod (2 ^ N)) - 1 :=
        dvd_trans (dvd_pow_self 2 (by omega : j ≠ 0)) hpg
      obtain ⟨c, hc⟩ := h2g
      have h1 : (2 : ZMod (2 ^ N)) ∣ 1 + (p.g : ZMod (2 ^ N)) := ⟨c + 1, by linear_combination hc⟩
      have h1' : (2 : ZMod (2 ^ N)) ∣ (p.g : ZMod (2 ^ N)) + 1 := ⟨c + 1, by linear_combination hc⟩
      refine ⟨?_, ?_⟩
      · have hval : (p ^ 2).u = (1 + (p.g : ZMod (2 ^ N))) * p.u := by
          rw [pow_two, WordLift.mul_u, Units.smul_def, smul_eq_mul]
          ring
        have hmul := mul_dvd_mul h1 hpu
        rw [show (2 : ZMod (2 ^ N)) * 2 ^ (j - 1) = 2 ^ j by
          rw [← pow_succ']; congr 1; omega] at hmul
        rw [hval, show j + 1 - 1 = j from rfl]
        exact hmul
      · have hval : ((p ^ 2).g : ZMod (2 ^ N)) - 1
            = ((p.g : ZMod (2 ^ N)) - 1) * ((p.g : ZMod (2 ^ N)) + 1) := by
          rw [pow_two, WordLift.mul_g, Units.val_mul]
          ring
        rw [hval, pow_succ]
        exact mul_dvd_mul hpg h1'
    · refine Subgroup.commutator_le.2 ?_
      rintro p ⟨hpu, hpg⟩ q -
      rw [wl_commutator]
      refine ⟨?_, by simp⟩
      show (2 : ZMod (2 ^ N)) ^ (j + 1 - 1) ∣
        p.u * (1 - (q.g : ZMod (2 ^ N))) + q.u * ((p.g : ZMod (2 ^ N)) - 1)
      rw [show j + 1 - 1 = j from rfl]
      refine dvd_add ?_ (Dvd.dvd.mul_left hpg _)
      obtain ⟨c, hc⟩ := two_dvd_units_sub_one hN q.g
      have h1 : (2 : ZMod (2 ^ N)) ∣ 1 - (q.g : ZMod (2 ^ N)) := ⟨-c, by linear_combination -hc⟩
      have hmul := mul_dvd_mul hpu h1
      rw [show (2 : ZMod (2 ^ N)) ^ (j - 1) * 2 = 2 ^ j by
        rw [← pow_succ]; congr 1; omega] at hmul
      exact hmul

/-! #### The derivations out of the two towers -/

/-- Direction 1: the derivation `D_R → WL N` with generator data `(v i, χ_R)`.  It exists
because `χ_R` is Labute's orientation — **every** crossed derivation kills `r₂`
(`isLabuteOrientation_chiR`), which is exactly the relator hypothesis `drLiftHom` wants. -/
private noncomputable def derivR (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    ContinuousMonoidHom (DR : Type) (WL N) :=
  drLiftHom (isProP_WL hN)
    ![redWL N ⟨v 0, chiR drS⟩, redWL N ⟨v 1, chiR drX⟩, redWL N ⟨v 2, chiR drY⟩]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [← map_drWord, show drWord (⟨v 0, chiR drS⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨v 1, chiR drX⟩
          ⟨v 2, chiR drY⟩ = 1 from isLabuteOrientation_chiR (v 0) (v 1) (v 2), map_one])

@[simp] private theorem derivR_drS (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    derivR N hN v drS = redWL N ⟨v 0, chiR drS⟩ := drLiftHom_S _ _ _

@[simp] private theorem derivR_drX (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    derivR N hN v drX = redWL N ⟨v 1, chiR drX⟩ := drLiftHom_X _ _ _

@[simp] private theorem derivR_drY (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    derivR N hN v drY = redWL N ⟨v 2, chiR drY⟩ := drLiftHom_Y _ _ _

/-- **The base component is `χ_R`** (mod `2^N`): both sides are continuous homs `D_R → (ℤ/2^N)ˣ`
agreeing on `s, x, y`, so `dr_hom_ext` applies.  The right-hand side is continuous because it
factors through the discrete level quotient `Q_N`. -/
private theorem derivR_base (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) (a : (DR : Type)) :
    (derivR N hN v a).g = Units.map (PadicInt.toZModPow N).toMonoidHom (chiR a) := by
  haveI := discreteTopology_levelQuot (DR : Type) drTopGenFinset isProP_DR N
  set f : ContinuousMonoidHom (DR : Type) ((ZMod (2 ^ N))ˣ) :=
    (⟨wlBase N, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ)).comp (derivR N hN v) with hf
  set g : ContinuousMonoidHom (DR : Type) ((ZMod (2 ^ N))ˣ) :=
    ⟨(chiLevel chiR N).comp (levelMk (DR : Type) N),
      show Continuous ((chiLevel chiR N) ∘ (levelMk (DR : Type) N)) from
        (continuous_of_discreteTopology (f := ⇑(chiLevel chiR N))).comp
          (continuous_levelMk (DR : Type) N)⟩ with hg
  have hval : ∀ b : (DR : Type), f b = (derivR N hN v b).g := fun _ => rfl
  have hval' : ∀ b : (DR : Type),
      g b = Units.map (PadicInt.toZModPow N).toMonoidHom (chiR b) := fun b => by
    show chiLevel chiR N (levelMk (DR : Type) N b) = _
    rw [chiLevel_levelMk]
  have hext : f = g := by
    refine dr_hom_ext f g ?_ ?_ ?_
    · rw [hval, hval', derivR_drS]; rfl
    · rw [hval, hval', derivR_drX]; rfl
    · rw [hval, hval', derivR_drY]; rfl
  rw [← hval a, hext, hval' a]

/-- **Hom-extensionality for `D₀`** (private clone of `dr_hom_ext`, on `SectionThree.topGen_d0`). -/
private theorem d0_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] (φ ψ : ContinuousMonoidHom (D0 : Type) A)
    (hA : φ d0A = ψ d0A) (hS : φ d0S = ψ d0S) (hY : φ d0Y = ψ d0Y) : φ = ψ := by
  have hgens : Set.EqOn φ ψ ({d0A, d0S, d0Y} : Set (D0 : Type)) := by
    rintro w (rfl | rfl | rfl)
    exacts [hA, hS, hY]
  have hsub : Set.EqOn φ ψ (Subgroup.closure ({d0A, d0S, d0Y} : Set (D0 : Type))) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact hgens hx
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, ha]
  have hdense :
      Dense ((Subgroup.closure ({d0A, d0S, d0Y} : Set (D0 : Type))) : Set (D0 : Type)) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, SectionThree.topGen_d0,
      Subgroup.coe_top]
  refine ContinuousMonoidHom.ext (fun z => ?_)
  exact (hsub.closure φ.continuous_toFun ψ.continuous_toFun) (hdense z)

/-- **The `r₀`-side Labute datum**: with the orientation values `(−1, 1, η)` every crossed
derivation kills `r₀ = A²S⁴[S,Y]`.  The computation is the one 2-adic miracle behind SL1:
the `S⁴`-block contributes `4·Ds` and the commutator `(η⁻¹ − 1)·Ds`, and `η⁻¹ = −3` exactly,
so the total `(3 + η⁻¹)·Ds` vanishes on the nose. -/
private theorem d0Word_wordLift_target (Da Ds Dy : ℤ_[2]) :
    d0Word (⟨Da, -1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Ds, 1⟩ ⟨Dy, etaUnit⟩ = 1 := by
  have hetainv : ((etaUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = -3 := by
    rw [etaUnit, inv_inv, negThreeUnit_val]
  have hsq : (⟨Da, -1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ 2 = ⟨0, 1⟩ := by
    rw [wl_pow]
    ext
    · show (∑ j ∈ Finset.range 2, ((-1 : ℤ_[2]ˣ) : ℤ_[2]) ^ j) * Da = (0 : ℤ_[2])
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      push_cast
      ring
    · show (((-1 : ℤ_[2]ˣ) ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2])
      push_cast
      ring
  have hfour : (⟨Ds, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ 4 = ⟨4 * Ds, 1⟩ := by
    rw [wl_pow]
    ext
    · show (∑ j ∈ Finset.range 4, ((1 : ℤ_[2]ˣ) : ℤ_[2]) ^ j) * Ds = 4 * Ds
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      push_cast
      ring
    · show (((1 : ℤ_[2]ˣ) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2])
      push_cast
      ring
  rw [d0Word, hsq, hfour, commP_wordLift]
  ext
  · simp only [WordLift.mul_u, WordLift.mul_g, WordLift.one_u, Units.smul_def, smul_eq_mul,
      Units.val_one, Units.val_mul, inv_one]
    rw [hetainv]
    ring
  · simp [commP_eq_one]

/-- Direction 2: the derivation `D₀ → WL N` with generator data `(v i, (−1, 1, η))`. -/
private noncomputable def deriv0 (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    ContinuousMonoidHom (D0 : Type) (WL N) :=
  SectionThree.d0LiftHom (isProP_WL hN)
    ![redWL N ⟨v 0, -1⟩, redWL N ⟨v 1, 1⟩, redWL N ⟨v 2, etaUnit⟩]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      show d0Word (redWL N ⟨v 0, -1⟩) (redWL N ⟨v 1, 1⟩) (redWL N ⟨v 2, etaUnit⟩) = 1
      rw [← map_d0Word, d0Word_wordLift_target, map_one])

@[simp] private theorem deriv0_d0A (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    deriv0 N hN v d0A = redWL N ⟨v 0, -1⟩ := by
  show ((maxProPHomEquiv (isProP_WL hN)).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = _
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] private theorem deriv0_d0S (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    deriv0 N hN v d0S = redWL N ⟨v 1, 1⟩ := by
  show ((maxProPHomEquiv (isProP_WL hN)).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = _
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] private theorem deriv0_d0Y (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    deriv0 N hN v d0Y = redWL N ⟨v 2, etaUnit⟩ := by
  show ((maxProPHomEquiv (isProP_WL hN)).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2))) = _
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-- The base component of the `D₀`-derivation is the mod-`2^N` shadow of `χ₀`. -/
private theorem deriv0_base (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) (a : (D0 : Type)) :
    (deriv0 N hN v a).g = Units.map (PadicInt.toZModPow N).toMonoidHom (chiD0pres a) := by
  haveI := discreteTopology_levelQuot (D0 : Type) d0TopGenFinset SectionThree.d0_isProP N
  set f : ContinuousMonoidHom (D0 : Type) ((ZMod (2 ^ N))ˣ) :=
    (⟨wlBase N, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ)).comp (deriv0 N hN v) with hf
  set g : ContinuousMonoidHom (D0 : Type) ((ZMod (2 ^ N))ˣ) :=
    ⟨(chiLevel chiD0pres N).comp (levelMk (D0 : Type) N),
      show Continuous ((chiLevel chiD0pres N) ∘ (levelMk (D0 : Type) N)) from
        (continuous_of_discreteTopology (f := ⇑(chiLevel chiD0pres N))).comp
          (continuous_levelMk (D0 : Type) N)⟩ with hg
  have hval : ∀ b : (D0 : Type), f b = (deriv0 N hN v b).g := fun _ => rfl
  have hval' : ∀ b : (D0 : Type),
      g b = Units.map (PadicInt.toZModPow N).toMonoidHom (chiD0pres b) := fun b => by
    show chiLevel chiD0pres N (levelMk (D0 : Type) N b) = _
    rw [chiLevel_levelMk]
  have hext : f = g := by
    refine d0_hom_ext f g ?_ ?_ ?_
    · rw [hval, hval', deriv0_d0A, chiD0pres_d0A]; rfl
    · rw [hval, hval', deriv0_d0S, chiD0pres_d0S]; rfl
    · rw [hval, hval', deriv0_d0Y, chiD0pres_d0Y]; rfl
  rw [← hval a, hext, hval' a]

/-! #### The derivation kernel in `Zₖ`, and the tail pairing -/

/-- Powers of a general point of `R ⋊ Rˣ` (structure eta on `wl_pow`). -/
private theorem wl_pow' {R : Type*} [CommRing R] (p : WordLift R Rˣ) (m : ℕ) :
    p ^ m = ⟨(∑ j ∈ Finset.range m, (p.g : R) ^ j) * p.u, p.g ^ m⟩ := wl_pow p.u p.g m

/-- **The geometric sum at a base `≡ 1 (mod 4)`** is `2^m · odd`: doubling multiplies it by
`1 + u^{2^m} ∈ 2·(1 + 2ℤ₂)`.  This is what makes the two tails pair non-degenerately. -/
private theorem geom_sum_two_pow {u : ℤ_[2]} (hu : (2 : ℤ_[2]) ^ 2 ∣ u - 1) (m : ℕ) :
    ∃ c : ℤ_[2], (∑ j ∈ Finset.range (2 ^ m), u ^ j) = 2 ^ m * c ∧ ¬ (2 : ℤ_[2]) ∣ c := by
  induction m with
  | zero =>
    refine ⟨1, by simp, ?_⟩
    simpa using two_not_dvd_one_add_two_mul 0
  | succ m ih =>
    obtain ⟨c, hc, hc2⟩ := ih
    obtain ⟨d, hd⟩ := dvd_pow_sub_one hu (2 ^ m)
    refine ⟨c * (1 + 2 * d), ?_, two_not_dvd_mul hc2 (two_not_dvd_one_add_two_mul d)⟩
    have hsplit : (∑ j ∈ Finset.range (2 ^ (m + 1)), u ^ j)
        = (∑ j ∈ Finset.range (2 ^ m), u ^ j) * (1 + u ^ 2 ^ m) := by
      rw [show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by ring, Finset.sum_range_add]
      have hshift : ∀ j : ℕ, u ^ (2 ^ m + j) = u ^ 2 ^ m * u ^ j := fun j => by rw [pow_add]
      simp only [hshift, ← Finset.mul_sum]
      ring
    have hval : 1 + u ^ 2 ^ m = 2 * (1 + 2 * d) := by
      have hpow : u ^ 2 ^ m = 1 + 2 ^ 2 * d := by linear_combination hd
      rw [hpow]
      ring
    rw [hsplit, hc, hval]
    ring

section DerivKer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Transport of the filtration bound `λ_j(WL N) ⊆ K_j` to the tower along a derivation. -/
private theorem deriv_mem_wlCong {N : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {j : ℕ} (hj : 1 ≤ j) {a : G} (ha : a ∈ twoCentralSeries G j) : Φ a ∈ wlCong N j :=
  twoCentralSeries_WL_le hN hj
    (map_twoCentralSeries_le Φ.toMonoidHom Φ.continuous_toFun j ⟨a, ha, rfl⟩)

/-- **The vanishing subgroup** `𝒜_Φ ⊆ Q_{k+1}`: classes admitting a `λₖ`-representative whose
derivation offset is divisible by `2^k`.  This is the Lean form of "the coker functional
`digit_{k-1} ∘ D` vanishes"; `derivKer_dvd` shows the condition does not depend on the
representative. -/
private def derivKer {N : ℕ} (Φ : ContinuousMonoidHom G (WL N)) (k : ℕ) :
    Subgroup (levelQuot G (k + 1)) where
  carrier := {q | ∃ a, a ∈ twoCentralSeries G k ∧ levelMk G (k + 1) a = q ∧
    (2 : ZMod (2 ^ N)) ^ k ∣ (Φ a).u}
  one_mem' := ⟨1, one_mem _, map_one _, by simp⟩
  mul_mem' := by
    rintro q q' ⟨a, ha, rfl, hda⟩ ⟨b, hb, rfl, hdb⟩
    refine ⟨a * b, mul_mem ha hb, map_mul _ _ _, ?_⟩
    rw [map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul]
    exact dvd_add hda (Dvd.dvd.mul_left hdb _)
  inv_mem' := by
    rintro q ⟨a, ha, rfl, hda⟩
    refine ⟨a⁻¹, inv_mem ha, map_inv _ _, ?_⟩
    rw [map_inv, WordLift.inv_u, Units.smul_def, smul_eq_mul]
    exact (Dvd.dvd.mul_left hda _).neg_right

/-- Representative-independence: membership of `levelMk b` forces the divisibility at `b`
itself (the ambiguity `λ_{k+1}` is already killed by the filtration bound). -/
private theorem derivKer_dvd {N : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N)) {k : ℕ}
    {b : G} (hb : levelMk G (k + 1) b ∈ derivKer Φ k) :
    (2 : ZMod (2 ^ N)) ^ k ∣ (Φ b).u := by
  obtain ⟨a, ha, hab, hda⟩ := hb
  have hmem : a⁻¹ * b ∈ twoCentralSeries G (k + 1) := QuotientGroup.eq.mp hab
  have hcong := (deriv_mem_wlCong hN Φ (by omega) hmem).1
  rw [show b = a * (a⁻¹ * b) by group, map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul]
  exact dvd_add hda (Dvd.dvd.mul_left hcong _)

end DerivKer

end CrossedFunctional

/-! ### Additivity of the shift word in the modification (`Im d̄` is a subgroup)

SL1 must produce a *single* modification, so the `d̄`-image has to be closed under products.
It is: every factor of `d̄` is `𝔽₂`-linear in `w` up to central corrections, and for `k ≥ 3`
all corrections lie in `Zₖ`, which is central. -/

section DbarAdditive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Moving a central factor one step to the right. -/
private theorem central_move {H : Type*} [Group H] {z : H} (hz : ∀ t : H, z * t = t * z)
    (x y : H) : z * (x * y) = x * (z * y) := by
  rw [← mul_assoc, hz, mul_assoc]

/-- Interleaving four central pairs (only the primed entries need to be central). -/
private theorem central_shuffle {H : Type*} [Group H] {A B C D A' B' C' D' : H}
    (hA' : ∀ t : H, A' * t = t * A') (hB' : ∀ t : H, B' * t = t * B')
    (hC' : ∀ t : H, C' * t = t * C') :
    A * A' * (B * B') * (C * C') * (D * D') = A * B * C * D * (A' * B' * C' * D') := by
  simp only [mul_assoc]
  rw [central_move hA' B, central_move hB' C, central_move hA' C, central_move hC' D,
    central_move hB' D, central_move hA' D]

/-- Interleaving three central pairs. -/
private theorem central_shuffle3 {H : Type*} [Group H] {A B C A' B' C' : H}
    (hA' : ∀ t : H, A' * t = t * A') (hB' : ∀ t : H, B' * t = t * B') :
    A * A' * (B * B') * (C * C') = A * B * C * (A' * B' * C') := by
  simp only [mul_assoc]
  rw [central_move hA' B, central_move hB' C, central_move hA' C]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `commP · g` is additive on `λ_{k-1}`-modifications (the correction is central). -/
private theorem commP_mul_lambdaImage_left (k : ℕ) (hk : 3 ≤ k)
    {u u' : levelQuot G (k + 1)} (hu : u ∈ lambdaImage G (k - 1) (k + 1))
    (g : levelQuot G (k + 1)) : commP (u * u') g = commP u g * commP u' g := by
  rw [commP_mul_left, conj_eq_self_of_commP_eq_one
    (commP_eq_one_of_mul_comm (zLayer_commute (commP_mem_zLayer k hk hu g) u').eq)]

set_option linter.unusedSectionVars false in
/-- **Additivity of `d̄` in the modification, `r₀`-side.** -/
private theorem dbarWordR0_mul (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hw' : ∀ i, w' i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR0 a s y (fun i => w i * w' i) = dbarWordR0 a s y w * dbarWordR0 a s y w' := by
  have hcen : ∀ {z : levelQuot G (k + 1)}, z ∈ zLayer G k → ∀ t, z * t = t * z :=
    fun hz t => (zLayer_commute hz t).eq
  have hcomm : Commute (w 0) (w' 0) := mul_comm_lambdaImage k hk (hw 0) (hw' 0)
  have hsq : (w 0 * w' 0) ^ 2 = w 0 ^ 2 * w' 0 ^ 2 := hcomm.mul_pow 2
  simp only [dbarWordR0, hsq, commP_mul_lambdaImage_left k hk (hw 0),
    commP_mul_lambdaImage_left k hk (hw 1), commP_mul_lambdaImage_left k hk (hw 2)]
  exact central_shuffle (hcen (sq_mem_zLayer k hk (hw' 0)))
    (hcen (commP_mem_zLayer k hk (hw' 0) a)) (hcen (commP_mem_zLayer k hk (hw' 1) y))

set_option linter.unusedSectionVars false in
/-- **Additivity of `d̄` in the modification, `r₂`-side.** -/
private theorem dbarWordR2_mul (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hw' : ∀ i, w' i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y (fun i => w i * w' i) = dbarWordR2 s x y w * dbarWordR2 s x y w' := by
  have hcen : ∀ {z : levelQuot G (k + 1)}, z ∈ zLayer G k → ∀ t, z * t = t * z :=
    fun hz t => (zLayer_commute hz t).eq
  have hcomm : Commute (w 2) (w' 2) := mul_comm_lambdaImage k hk (hw 2) (hw' 2)
  have hsq : (w 2 * w' 2) ^ 2 = w 2 ^ 2 * w' 2 ^ 2 := hcomm.mul_pow 2
  simp only [dbarWordR2, hsq, commP_mul_lambdaImage_left k hk (hw 2),
    commP_mul_lambdaImage_left k hk (hw 0), commP_mul_lambdaImage_left k hk (hw 1)]
  exact central_shuffle (hcen (sq_mem_zLayer k hk (hw' 2)))
    (hcen (commP_mem_zLayer k hk (hw' 2) y)) (hcen (commP_mem_zLayer k hk (hw' 0) x))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The shift word lands in the central layer `Zₖ`. -/
private theorem dbarWordR0_mem_zLayer (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR0 a s y w ∈ zLayer G k :=
  mul_mem (mul_mem (mul_mem (sq_mem_zLayer k hk (hw 0)) (commP_mem_zLayer k hk (hw 0) a))
    (commP_mem_zLayer k hk (hw 1) y)) (commP_mem_zLayer k hk (hw 2) s)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem dbarWordR2_mem_zLayer (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y w ∈ zLayer G k :=
  mul_mem (mul_mem (mul_mem (sq_mem_zLayer k hk (hw 2)) (commP_mem_zLayer k hk (hw 2) y))
    (commP_mem_zLayer k hk (hw 0) x)) (commP_mem_zLayer k hk (hw 1) s)

end DbarAdditive

/-! ### The endgame: the coordinate derivations separate the two tails -/

section TailSeparation

open FoxH

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The mod-2 reduction of `ℤ/2^N`. -/
private def redTwo {N : ℕ} (hN : 1 ≤ N) : ZMod (2 ^ N) →+* ZMod (2 ^ 1) :=
  ZMod.castHom (pow_dvd_pow 2 hN) (ZMod (2 ^ 1))

/-- Units reduce to `1` mod `2`. -/
private theorem redTwo_units {N : ℕ} (hN : 1 ≤ N) (g : (ZMod (2 ^ N))ˣ) :
    redTwo hN (g : ZMod (2 ^ N)) = 1 := by
  obtain ⟨v, hv⟩ := (g.isUnit.map (redTwo hN)).exists_right_inv
  exact (by decide : ∀ a b : ZMod (2 ^ 1), a * b = 1 → a = 1) _ _ hv

/-- Odd `2`-adics reduce to `1` mod `2`. -/
private theorem redTwo_odd {N : ℕ} (hN : 1 ≤ N) {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    redTwo hN (PadicInt.toZModPow N c) = 1 := by
  have h : redTwo hN (PadicInt.toZModPow N c) ≠ 0 := by
    intro h0
    refine hc ?_
    rw [← pow_one (2 : ℤ_[2]), ← two_pow_dvd_toZModPow_iff hN, two_pow_dvd_zmod_iff hN]
    exact h0
  revert h
  generalize redTwo hN (PadicInt.toZModPow N c) = z
  revert z
  decide

/-- The mod-2 coordinate vector of the derivations at the three coordinate directions. -/
private noncomputable def thetaVec {N : ℕ} (hN : 1 ≤ N) (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N))
    (x : G) : Fin 3 → ZMod (2 ^ 1) :=
  fun j => redTwo hN ((Φ (Pi.single j 1) x).u)

private theorem thetaVec_mul {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (x y : G) :
    thetaVec hN Φ (x * y) = thetaVec hN Φ x + thetaVec hN Φ y := by
  funext j
  show redTwo hN ((Φ (Pi.single j 1) (x * y)).u) = _
  rw [map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul, map_add, map_mul, redTwo_units hN,
    one_mul]
  rfl

private theorem thetaVec_one {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) : thetaVec hN Φ (1 : G) = 0 := by
  funext j
  show redTwo hN ((Φ (Pi.single j 1) 1).u) = 0
  rw [map_one]
  simp

private theorem thetaVec_inv {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (x : G) :
    thetaVec hN Φ x⁻¹ = -thetaVec hN Φ x := by
  have h := thetaVec_mul hN Φ x x⁻¹
  rw [mul_inv_cancel, thetaVec_one] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

/-- `θ` kills `λ₂` (the offset of a `λ₂`-element is already even). -/
private theorem thetaVec_lambdaTwo {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) {x : G}
    (hx : x ∈ twoCentralSeries G 2) : thetaVec hN Φ x = 0 := by
  funext j
  have h := (deriv_mem_wlCong hN (Φ (Pi.single j 1)) (by omega) hx).1
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  show redTwo hN ((Φ (Pi.single j 1) x).u) = 0
  have hz : (2 : ZMod (2 ^ N)) ^ 1 ∣ (Φ (Pi.single j 1) x).u := by rwa [pow_one]
  exact (two_pow_dvd_zmod_iff (N := N) (j := 1) hN).mp hz

/-- The mod-2 reduction of a geometric sum of units counts its terms. -/
private theorem redTwo_geom {N : ℕ} (hN : 1 ≤ N) (h : (ZMod (2 ^ N))ˣ) (m : ℕ) :
    redTwo hN (∑ j ∈ Finset.range m, ((h : ZMod (2 ^ N))) ^ j) = (m : ZMod (2 ^ 1)) := by
  rw [map_sum]
  simp only [map_pow, redTwo_units hN, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]

/-- **The tail offset**: `(Φ ((x^{2^{k-1}})^α)).u = 2^{k-1}·C·(Φ x).u` with `C ≡ α (mod 2)` —
the sharpness of the geometric sum at a base `≡ 1 (mod 4)`. -/
private theorem deriv_tail_u {N k : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {x : G} {u : ℤ_[2]} (hu : (2 : ℤ_[2]) ^ 2 ∣ u - 1)
    (hg : ((Φ x).g : ZMod (2 ^ N)) = PadicInt.toZModPow N u) (α : ℕ) :
    ∃ C : ZMod (2 ^ N), redTwo hN C = (α : ZMod (2 ^ 1)) ∧
      (Φ ((x ^ 2 ^ (k - 1)) ^ α)).u = 2 ^ (k - 1) * (C * (Φ x).u) := by
  obtain ⟨c, hc, hc2⟩ := geom_sum_two_pow hu (k - 1)
  have hSxval : (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ N)) ^ j)
      = 2 ^ (k - 1) * PadicInt.toZModPow N c := by
    have hmap : (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ N)) ^ j)
        = PadicInt.toZModPow N (∑ j ∈ Finset.range (2 ^ (k - 1)), u ^ j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_pow, hg]
    rw [hmap, hc, map_mul, map_pow, map_ofNat]
  refine ⟨(∑ j ∈ Finset.range α, ((Φ (x ^ 2 ^ (k - 1))).g : ZMod (2 ^ N)) ^ j) *
    PadicInt.toZModPow N c, ?_, ?_⟩
  · rw [map_mul, redTwo_geom hN, redTwo_odd hN hc2, mul_one]
  · have h1 : (Φ (x ^ 2 ^ (k - 1))).u
        = (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ N)) ^ j) * (Φ x).u := by
      rw [map_pow, wl_pow']
    have h2 : (Φ ((x ^ 2 ^ (k - 1)) ^ α)).u
        = (∑ j ∈ Finset.range α, ((Φ (x ^ 2 ^ (k - 1))).g : ZMod (2 ^ N)) ^ j) *
          (Φ (x ^ 2 ^ (k - 1))).u := by
      conv_lhs => rw [map_pow, wl_pow']
    rw [h2, h1, hSxval]
    ring

/-- **The tail parity relation**: if a tail combination lies in every coordinate derivation's
kernel, the two coordinate vectors satisfy the corresponding `𝔽₂`-linear relation. -/
private theorem tail_parity {N k : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N) (hkN : k ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N))
    {x y : G} {ux uy : ℤ_[2]}
    (hux : (2 : ℤ_[2]) ^ 2 ∣ ux - 1) (huy : (2 : ℤ_[2]) ^ 2 ∣ uy - 1)
    (hgx : ∀ v, ((Φ v x).g : ZMod (2 ^ N)) = PadicInt.toZModPow N ux)
    (hgy : ∀ v, ((Φ v y).g : ZMod (2 ^ N)) = PadicInt.toZModPow N uy)
    (α β : ℕ)
    (hmem : ∀ v, levelMk G (k + 1) ((x ^ 2 ^ (k - 1)) ^ α * (y ^ 2 ^ (k - 1)) ^ β) ∈
      derivKer (Φ v) k) :
    (α : ZMod (2 ^ 1)) • thetaVec hN Φ x + (β : ZMod (2 ^ 1)) • thetaVec hN Φ y = 0 := by
  funext j
  obtain ⟨Cx, hCx, hxval⟩ := deriv_tail_u (k := k) hN (Φ (Pi.single j 1)) hux (hgx _) α
  obtain ⟨Cy, hCy, hyval⟩ := deriv_tail_u (k := k) hN (Φ (Pi.single j 1)) huy (hgy _) β
  have hdvd := derivKer_dvd hN (Φ (Pi.single j 1)) (hmem (Pi.single j 1))
  rw [map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul, hxval, hyval] at hdvd
  set gα : ZMod (2 ^ N) :=
    ((Φ (Pi.single j 1) ((x ^ 2 ^ (k - 1)) ^ α)).g : ZMod (2 ^ N)) with hgα
  have hfac : (2 : ZMod (2 ^ N)) ^ (k - 1) * (Cx * (Φ (Pi.single j 1) x).u)
        + gα * (2 ^ (k - 1) * (Cy * (Φ (Pi.single j 1) y).u))
      = 2 ^ (k - 1) * (Cx * (Φ (Pi.single j 1) x).u
        + gα * (Cy * (Φ (Pi.single j 1) y).u)) := by ring
  rw [hfac] at hdvd
  have h2 := two_dvd_of_two_pow_dvd_mul (by omega : 1 ≤ k) hkN hdvd
  have hred : redTwo hN (Cx * (Φ (Pi.single j 1) x).u
      + gα * (Cy * (Φ (Pi.single j 1) y).u)) = 0 := by
    have hz : (2 : ZMod (2 ^ N)) ^ 1 ∣ Cx * (Φ (Pi.single j 1) x).u
        + gα * (Cy * (Φ (Pi.single j 1) y).u) := by rwa [pow_one]
    exact (two_pow_dvd_zmod_iff (N := N) (j := 1) hN).mp hz
  rw [map_add, map_mul, map_mul, map_mul, hCx, hCy, hgα, redTwo_units hN, one_mul] at hred
  show (α : ZMod (2 ^ 1)) * thetaVec hN Φ x j + (β : ZMod (2 ^ 1)) * thetaVec hN Φ y j = 0
  exact hred

/-- The coordinate vectors of the tower generators are the standard basis. -/
private theorem thetaVec_gen {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (gen : Fin 3 → G)
    (hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3), (Φ v (gen j)).u = PadicInt.toZModPow N (v j))
    (j : Fin 3) : thetaVec hN Φ (gen j) = Pi.single j (1 : ZMod (2 ^ 1)) := by
  funext i
  show redTwo hN ((Φ (Pi.single i 1) (gen j)).u) = _
  rw [hgenval, Pi.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    simp

/-- **Independence of a generating triple's coordinate vectors.**  The coordinate map
`𝔽₂³ → 𝔽₂³`, `c ↦ ∑ cᵢ·θ(aᵢ)`, hits the standard basis (the classes of the `aᵢ` generate
`Q_{k+1}`, and `θ` factors through it), hence is onto, hence — same finite type — injective. -/
private theorem thetaVec_indep {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (gen a : Fin 3 → G)
    (hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3), (Φ v (gen j)).u = PadicInt.toZModPow N (v j))
    (hgent : Subgroup.closure (Set.range fun i => levelMk G (k + 1) (a i)) = ⊤)
    {c : Fin 3 → ZMod (2 ^ 1)}
    (hc : c 0 • thetaVec hN Φ (a 0) + c 1 • thetaVec hN Φ (a 1) + c 2 • thetaVec hN Φ (a 2) = 0) :
    c = 0 := by
  classical
  set L : (Fin 3 → ZMod (2 ^ 1)) → (Fin 3 → ZMod (2 ^ 1)) := fun d =>
    d 0 • thetaVec hN Φ (a 0) + d 1 • thetaVec hN Φ (a 1) + d 2 • thetaVec hN Φ (a 2) with hLdef
  have hLadd : ∀ d d' : Fin 3 → ZMod (2 ^ 1), L (d + d') = L d + L d' := by
    intro d d'
    funext i
    simp only [hLdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hLsmul : ∀ (z : ZMod (2 ^ 1)) (d : Fin 3 → ZMod (2 ^ 1)), L (z • d) = z • L d := by
    intro z d
    funext i
    simp only [hLdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hLzero : L 0 = 0 := by simp [hLdef]
  have hLbasis : ∀ i : Fin 3, L (Pi.single i 1) = thetaVec hN Φ (a i) := by
    intro i
    fin_cases i <;> simp [hLdef]
  set S : Subgroup (levelQuot G (k + 1)) :=
    { carrier := {q | ∃ x : G, levelMk G (k + 1) x = q ∧ thetaVec hN Φ x ∈ Set.range L}
      one_mem' := ⟨1, map_one _, ⟨0, by rw [hLzero, thetaVec_one]⟩⟩
      mul_mem' := by
        rintro p q ⟨x, rfl, d, hd⟩ ⟨y, rfl, d', hd'⟩
        exact ⟨x * y, map_mul _ _ _, ⟨d + d', by rw [hLadd, hd, hd', thetaVec_mul]⟩⟩
      inv_mem' := by
        rintro p ⟨x, rfl, d, hd⟩
        refine ⟨x⁻¹, map_inv _ _, ⟨-d, ?_⟩⟩
        have hneg : L (-d) = -L d := by
          have h := hLadd d (-d)
          rw [add_neg_cancel, hLzero] at h
          exact eq_neg_of_add_eq_zero_right h.symm
        rw [hneg, hd, thetaVec_inv] } with hSdef
  have hStop : S = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgent, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, rfl, ⟨Pi.single i 1, hLbasis i⟩⟩
  have hbasis : ∀ j : Fin 3, (Pi.single j (1 : ZMod (2 ^ 1))) ∈ Set.range L := by
    intro j
    have hmem : levelMk G (k + 1) (gen j) ∈ S := by rw [hStop]; trivial
    obtain ⟨x, hx, d, hd⟩ := hmem
    have hdiff : x⁻¹ * gen j ∈ twoCentralSeries G 2 :=
      twoCentralSeries_antitone G (by omega : 2 ≤ k + 1) (QuotientGroup.eq.mp hx)
    have hθ : thetaVec hN Φ (gen j) = thetaVec hN Φ x := by
      have hsplit : thetaVec hN Φ (x * (x⁻¹ * gen j))
          = thetaVec hN Φ x + thetaVec hN Φ (x⁻¹ * gen j) := thetaVec_mul hN Φ _ _
      rw [show x * (x⁻¹ * gen j) = gen j by group, thetaVec_lambdaTwo hN Φ hdiff,
        add_zero] at hsplit
      exact hsplit
    rw [← thetaVec_gen hN Φ gen hgenval j, hθ]
    exact ⟨d, hd⟩
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨d0, hd0⟩ := hbasis 0
    obtain ⟨d1, hd1⟩ := hbasis 1
    obtain ⟨d2, hd2⟩ := hbasis 2
    refine ⟨z 0 • d0 + (z 1 • d1 + z 2 • d2), ?_⟩
    rw [hLadd, hLadd, hLsmul, hLsmul, hLsmul, hd0, hd1, hd2]
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  have hinj : Function.Injective L := Finite.injective_iff_surjective.mpr hsurj
  have hLc : L c = L 0 := by rw [hLzero]; exact hc
  exact hinj hLc

end TailSeparation

/-! ### The congruence bookkeeping: reference words at the pinned targets

Both "functional vanishes" statements (`φ(δ) = 0` and `φ(Im d̄) = 0`) are proved by *comparison*:
the actual triple is congruent, modulo the two-sided congruence subgroup `wlKer N k`, to a
reference triple whose χ-values are the pinned targets exactly.  At the reference the word
value is computed in closed form — and vanishes, by Labute's descent datum (for `δ`) or by the
target valuations (for `d̄`). -/

section Reference

open FoxH

/-- Every residue lifts to `ℤ₂`. -/
private theorem toZModPow_surj {N : ℕ} (z : ZMod (2 ^ N)) :
    ∃ x : ℤ_[2], PadicInt.toZModPow N x = z := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) z
  exact ⟨(m : ℤ_[2]), by rw [map_intCast]⟩

/-- The two-sided mod-`2^k` congruence subgroup of `WL N`. -/
private def wlKer (N k : ℕ) : Subgroup (WL N) where
  carrier := {p | (2 : ZMod (2 ^ N)) ^ k ∣ p.u ∧
    (2 : ZMod (2 ^ N)) ^ k ∣ (p.g : ZMod (2 ^ N)) - 1}
  one_mem' := by
    refine ⟨by simp, ?_⟩
    show (2 : ZMod (2 ^ N)) ^ k ∣ ((1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
    simp
  mul_mem' := by
    rintro p q ⟨hpu, hpg⟩ ⟨hqu, hqg⟩
    refine ⟨?_, ?_⟩
    · rw [WordLift.mul_u, Units.smul_def, smul_eq_mul]
      exact dvd_add hpu (Dvd.dvd.mul_left hqu _)
    · rw [WordLift.mul_g]
      have hexp : ((p.g * q.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
          = ((p.g : ZMod (2 ^ N)) - 1) * (q.g : ZMod (2 ^ N)) + ((q.g : ZMod (2 ^ N)) - 1) := by
        push_cast
        ring
      rw [hexp]
      exact dvd_add (Dvd.dvd.mul_right hpg _) hqg
  inv_mem' := by
    rintro p ⟨hpu, hpg⟩
    refine ⟨?_, ?_⟩
    · rw [WordLift.inv_u, Units.smul_def, smul_eq_mul]
      exact (Dvd.dvd.mul_left hpu _).neg_right
    · rw [WordLift.inv_g]
      have hpginv : ((p.g : ZMod (2 ^ N))) * ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hexp : ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
          = -(((p.g : ZMod (2 ^ N)) - 1) * ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) := by
        linear_combination hpginv
      rw [hexp]
      exact (Dvd.dvd.mul_right hpg _).neg_right

private instance wlKer_normal (N k : ℕ) : (wlKer N k).Normal := by
  constructor
  rintro p ⟨hpu, hpg⟩ q
  refine ⟨?_, ?_⟩
  · have hval : (q * p * q⁻¹).u
        = (q.g : ZMod (2 ^ N)) * p.u + q.u * (1 - (p.g : ZMod (2 ^ N))) := by
      have hq : ((q.g : ZMod (2 ^ N))) * ((q.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp only [WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, Units.smul_def,
        smul_eq_mul, Units.val_mul]
      linear_combination (-(q.u) * (p.g : ZMod (2 ^ N))) * hq
    rw [hval]
    refine dvd_add (Dvd.dvd.mul_left hpu _) (Dvd.dvd.mul_left ?_ _)
    obtain ⟨c, hc⟩ := hpg
    exact ⟨-c, by linear_combination -hc⟩
  · have hval : ((q * p * q⁻¹).g : ZMod (2 ^ N)) = (p.g : ZMod (2 ^ N)) := by
      have hg : (q * p * q⁻¹).g = p.g := by
        show q.g * p.g * q.g⁻¹ = p.g
        rw [mul_comm q.g p.g]
        group
      rw [hg]
    rw [hval]
    exact hpg

/-- The membership criterion used throughout: equal offsets and congruent base values. -/
private theorem inv_mul_mem_wlKer {N k : ℕ} {p q : WL N} (hu : p.u = q.u)
    (hg : (2 : ZMod (2 ^ N)) ^ k ∣ ((p.g⁻¹ * q.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1) :
    p⁻¹ * q ∈ wlKer N k := by
  refine ⟨?_, ?_⟩
  · have hval : (p⁻¹ * q).u
        = ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) * (q.u - p.u) := by
      simp only [WordLift.mul_u, WordLift.inv_u, WordLift.inv_g, Units.smul_def, smul_eq_mul]
      ring
    rw [hval, hu, sub_self, mul_zero]
    exact dvd_zero _
  · exact hg

/-- Flipping the side of a unit congruence. -/
private theorem dvd_inv_mul_of_dvd_mul_inv {A B : ℤ_[2]ˣ} {n : ℕ}
    (h : (2 : ℤ_[2]) ^ n ∣ ((A * B⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    (2 : ℤ_[2]) ^ n ∣ ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨c, hc⟩ := h
  have hunit : ((A * B⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, show A * B⁻¹ * (A⁻¹ * B) = 1 by rw [mul_comm A B⁻¹]; group,
      Units.val_one]
  exact ⟨-c * ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]),
    by linear_combination hunit - ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]) * hc⟩

/-- `commP` at a base-`1` modification slot. -/
private theorem commP_wl_one {R : Type*} [CommRing R] (d D : R) (t : Rˣ) :
    commP (⟨d, 1⟩ : WordLift R Rˣ) ⟨D, t⟩ = ⟨(((t⁻¹ : Rˣ) : R) - 1) * d, 1⟩ := by
  have ht : ((t⁻¹ : Rˣ) : R) * (t : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  ext
  · simp only [commP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g,
      Units.smul_def, smul_eq_mul, Units.val_mul, inv_one, Units.val_one]
    ring
  · simp [commP]

/-- Squaring a base-`1` slot. -/
private theorem sq_wl_one {R : Type*} [CommRing R] (d : R) :
    (⟨d, 1⟩ : WordLift R Rˣ) ^ 2 = ⟨2 * d, 1⟩ := by
  rw [pow_two]
  ext
  · show d + ((1 : Rˣ) : R) * d = 2 * d
    push_cast
    ring
  · simp

/-- Product of base-`1` points adds the offsets. -/
private theorem mul_wl_one {R : Type*} [CommRing R] (d d' : R) :
    (⟨d, 1⟩ : WordLift R Rˣ) * ⟨d', 1⟩ = ⟨d + d', 1⟩ := by
  ext
  · show d + ((1 : Rˣ) : R) * d' = d + d'
    push_cast
    ring
  · simp

/-- **The reference shift word, `r₀`-side**, in closed form. -/
private theorem dbarWordR0_ref {R : Type*} [CommRing R] (D0 D1 D2 d0 d1 d2 : R) (t0 t1 t2 : Rˣ) :
    dbarWordR0 (⟨D0, t0⟩ : WordLift R Rˣ) ⟨D1, t1⟩ ⟨D2, t2⟩ ![⟨d0, 1⟩, ⟨d1, 1⟩, ⟨d2, 1⟩]
      = ⟨(1 + ((t0⁻¹ : Rˣ) : R)) * d0 + (((t2⁻¹ : Rˣ) : R) - 1) * d1
          + (((t1⁻¹ : Rˣ) : R) - 1) * d2, 1⟩ := by
  simp only [dbarWordR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, sq_wl_one, commP_wl_one, mul_wl_one]
  ext
  · show 2 * d0 + (((t0⁻¹ : Rˣ) : R) - 1) * d0 + ((((t2⁻¹ : Rˣ) : R) - 1) * d1)
        + (((t1⁻¹ : Rˣ) : R) - 1) * d2 = _
    ring
  · rfl

/-- **The reference shift word, `r₂`-side**, in closed form. -/
private theorem dbarWordR2_ref {R : Type*} [CommRing R] (D0 D1 D2 d0 d1 d2 : R) (t0 t1 t2 : Rˣ) :
    dbarWordR2 (⟨D0, t0⟩ : WordLift R Rˣ) ⟨D1, t1⟩ ⟨D2, t2⟩ ![⟨d0, 1⟩, ⟨d1, 1⟩, ⟨d2, 1⟩]
      = ⟨(1 + ((t2⁻¹ : Rˣ) : R)) * d2 + (((t1⁻¹ : Rˣ) : R) - 1) * d0
          + (((t0⁻¹ : Rˣ) : R) - 1) * d1, 1⟩ := by
  simp only [dbarWordR2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, sq_wl_one, commP_wl_one, mul_wl_one]
  ext
  · show 2 * d2 + (((t2⁻¹ : Rˣ) : R) - 1) * d2 + ((((t1⁻¹ : Rˣ) : R) - 1) * d0)
        + (((t0⁻¹ : Rˣ) : R) - 1) * d1 = _
    ring
  · rfl

/-- Reduction of a `1 + t⁻¹` coefficient. -/
private theorem red_coeff_one_add {N : ℕ} (t : ℤ_[2]ˣ) :
    (1 : ZMod (2 ^ N))
        + (((Units.map (PadicInt.toZModPow N).toMonoidHom t)⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))
      = PadicInt.toZModPow N (1 + ((t⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
  rw [map_add, map_one, ← map_inv]
  rfl

/-- Reduction of a `t⁻¹ − 1` coefficient. -/
private theorem red_coeff_sub_one {N : ℕ} (t : ℤ_[2]ˣ) :
    (((Units.map (PadicInt.toZModPow N).toMonoidHom t)⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
      = PadicInt.toZModPow N (((t⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  rw [map_sub, map_one, ← map_inv]
  rfl

/-- A `4`-divisible coefficient times a `2^{k-2}`-divisible offset is `2^k`-divisible. -/
private theorem dvd_coeff_mul {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) {c : ℤ_[2]}
    (hc : (2 : ℤ_[2]) ^ 2 ∣ c) {d : ZMod (2 ^ N)} (hd : (2 : ZMod (2 ^ N)) ^ (k - 2) ∣ d) :
    (2 : ZMod (2 ^ N)) ^ k ∣ PadicInt.toZModPow N c * d := by
  have h1 : (2 : ZMod (2 ^ N)) ^ 2 ∣ PadicInt.toZModPow N c :=
    (two_pow_dvd_toZModPow_iff (by omega)).mpr hc
  have h := mul_dvd_mul h1 hd
  rwa [← pow_add, show 2 + (k - 2) = k by omega] at h

end Reference

/-! ## The stage lemma: SL1, SL2, and the step (spike §2.4) -/

set_option maxHeartbeats 400000 in
/-- **SL1 (reachability), direction 1**: for `T ∈ S^P_ₖ` (`k ≥ 3`), the defect is
reachable — some `λ_{k-1}`-modification's shift equals `δ(T)⁻¹` (inverse form; in `Zₖ`
inverses are trivial, so this is the memo's `δₖ(T) ∈ Im d̄ₖ(T)`).  This is where the
invariant `P` earns its keep: the spike's census shows the statement is *false* without
the χ-clause (192/192 `P`-violating classes unreachable at `k = 4`).  Fill: L4b (span
theorem + the two separating functionals of spike §2.5(b)). -/
theorem stageSL1R0 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) :
    ∃ w : Fin 3 → levelQuot (DR : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) ∧
      dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
        (canonLift (DR : Type) k (T 2)) w = (defectR0 k T)⁻¹ := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hN : 1 ≤ k + 1 := by omega
  have hkN : k ≤ k + 1 := by omega
  choose a ha using fun i : Fin 3 =>
    levelMk_surjective (DR : Type) (k + 1) (canonLift (DR : Type) k (T i))
  have hproj : ∀ i, levelMk (DR : Type) k (a i) = T i := fun i => by
    rw [← levelProj_levelMk, ha i, levelProj_canonLift]
  have himg : (levelProj (DR : Type) k) ''
      (Set.range fun i => canonLift (DR : Type) k (T i)) = Set.range T := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => levelProj_canonLift (DR : Type) k (T i))
  have hgent : Subgroup.closure (Set.range fun i => canonLift (DR : Type) k (T i)) = ⊤ := by
    refine eq_top_of_map_levelProj_eq_top (DR : Type) drTopGenFinset isProP_DR (by omega) ?_
    rw [MonoidHom.map_closure, himg, hgen]
  have hgent' : Subgroup.closure (Set.range fun i => levelMk (DR : Type) (k + 1) (a i)) = ⊤ := by
    rw [show (fun i => levelMk (DR : Type) (k + 1) (a i))
      = fun i => canonLift (DR : Type) k (T i) from funext ha]
    exact hgent
  set Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom (DR : Type) (WL (k + 1)) :=
    fun v => derivR (k + 1) hN v with hΦ
  have hbase : ∀ (v : Fin 3 → ℤ_[2]) (x : (DR : Type)),
      (Φ v x).g = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiR x) :=
    fun v x => derivR_base (k + 1) hN v x
  have hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3),
      (Φ v (![drS, drX, drY] j)).u = PadicInt.toZModPow (k + 1) (v j) := by
    intro v j
    fin_cases j
    · show (derivR (k + 1) hN v drS).u = _
      rw [derivR_drS]; rfl
    · show (derivR (k + 1) hN v drX).u = _
      rw [derivR_drX]; rfl
    · show (derivR (k + 1) hN v drY).u = _
      rw [derivR_drY]; rfl
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiR (a i) * (chiTargetUnitsR0 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiR (chiTargetUnitsR0 i) (hproj i) ?_
    simpa [chiTargetR0] using hchi i
  -- congruence of a slot with its pinned target
  have hslot : ∀ (v : Fin 3 → ℤ_[2]) (i : Fin 3) (x : ℤ_[2]),
      PadicInt.toZModPow (k + 1) x = (Φ v (a i)).u →
      (Φ v (a i))⁻¹ * redWL (k + 1) ⟨x, chiTargetUnitsR0 i⟩ ∈ wlKer (k + 1) k := by
    intro v i x hx
    refine inv_mul_mem_wlKer hx.symm ?_
    have h2 : (2 : ℤ_[2]) ^ k ∣
        (((chiR (a i))⁻¹ * chiTargetUnitsR0 i : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      dvd_inv_mul_of_dvd_mul_inv (hdev i)
    have hred := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := k) hkN).mpr h2
    rw [map_sub, map_one] at hred
    have hg : ((Φ v (a i)).g⁻¹ * (redWL (k + 1) ⟨x, chiTargetUnitsR0 i⟩).g
          : (ZMod (2 ^ (k + 1)))ˣ)
        = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
          ((chiR (a i))⁻¹ * chiTargetUnitsR0 i) := by
      rw [map_mul, map_inv, hbase v (a i), redWL_g]
    rw [hg]
    exact hred
  -- congruence of a `λ_{k-1}`-modification slot with base `1`
  have hwslot : ∀ (v : Fin 3 → ℤ_[2]) (x : (DR : Type)),
      x ∈ twoCentralSeries (DR : Type) (k - 1) →
      (Φ v x)⁻¹ * (⟨(Φ v x).u, 1⟩ : WL (k + 1)) ∈ wlKer (k + 1) k := by
    intro v x hx
    refine inv_mul_mem_wlKer rfl ?_
    have h1 : (2 : ℤ_[2]) ^ k ∣ ((chiR x : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      have h := dvd_chi_of_mem_twoCentralSeries chiR (k := k - 1) (by omega) hx
      rwa [show k - 1 + 1 = k by omega] at h
    have h2 : (2 : ℤ_[2]) ^ k ∣ (((chiR x)⁻¹ * 1 : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      dvd_inv_mul_of_dvd_mul_inv (by simpa using h1)
    have hred := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := k) hkN).mpr h2
    rw [map_sub, map_one] at hred
    have hg : ((Φ v x).g⁻¹ * (⟨(Φ v x).u, 1⟩ : WL (k + 1)).g : (ZMod (2 ^ (k + 1)))ˣ)
        = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom ((chiR x)⁻¹ * 1) := by
      rw [map_mul, map_inv, map_one, mul_one, mul_one, hbase v x]
    rw [hg]
    exact hred
  -- the defect lies in every derivation kernel (the `r₀`-datum at the pinned targets)
  have hδker : ∀ v, defectR0 k T ∈ derivKer (Φ v) k := by
    intro v
    refine ⟨d0Word (a 0) (a 1) (a 2), ?_, ?_, ?_⟩
    · have hmk : levelMk (DR : Type) k (d0Word (a 0) (a 1) (a 2)) = 1 := by
        rw [map_d0Word, hproj, hproj, hproj]
        exact hrel
      exact (QuotientGroup.eq_one_iff _).mp hmk
    · rw [map_d0Word, ha 0, ha 1, ha 2]
      rfl
    · obtain ⟨x0, hx0⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 0)).u)
      obtain ⟨x1, hx1⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 1)).u)
      obtain ⟨x2, hx2⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 2)).u)
      have href : d0Word (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩)
          (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩) = 1 := by
        rw [show chiTargetUnitsR0 0 = -1 from by simp [chiTargetUnitsR0],
          show chiTargetUnitsR0 1 = 1 from by simp [chiTargetUnitsR0],
          show chiTargetUnitsR0 2 = etaUnit from by simp [chiTargetUnitsR0],
          ← map_d0Word, d0Word_wordLift_target, map_one]
      have hmkeq : ∀ {p q : WL (k + 1)}, p⁻¹ * q ∈ wlKer (k + 1) k →
          (QuotientGroup.mk' (wlKer (k + 1) k)) p = (QuotientGroup.mk' (wlKer (k + 1) k)) q := by
        intro p q h
        simp only [QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr h
      have hcong : (QuotientGroup.mk' (wlKer (k + 1) k))
            (d0Word (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)))
          = (QuotientGroup.mk' (wlKer (k + 1) k))
            (d0Word (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
              (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩)
              (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)) := by
        rw [map_d0Word, map_d0Word, hmkeq (hslot v 0 x0 hx0), hmkeq (hslot v 1 x1 hx1),
          hmkeq (hslot v 2 x2 hx2)]
      rw [href, map_one] at hcong
      have hmem : d0Word (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)) ∈ wlKer (k + 1) k :=
        (QuotientGroup.eq_one_iff _).mp hcong
      have := hmem.1
      rwa [← map_d0Word] at this
  -- every `d̄`-value lies in every derivation kernel
  have hdbarker : ∀ (v : Fin 3 → ℤ_[2]) (w : Fin 3 → levelQuot (DR : Type) (k + 1)),
      (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) →
      dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
        (canonLift (DR : Type) k (T 2)) w ∈ derivKer (Φ v) k := by
    intro v w hw
    choose ŵ hŵmem hŵeq using fun i => hw i
    refine ⟨dbarWordR0 (a 0) (a 1) (a 2) ŵ, ?_, ?_, ?_⟩
    · have hsq : ŵ 0 ^ 2 ∈ twoCentralSeries (DR : Type) k := by
        have h := sq_mem_twoCentralSeries_succ (DR : Type) (hŵmem 0)
        rwa [show k - 1 + 1 = k by omega] at h
      have hcm : ∀ (i : Fin 3) (g : (DR : Type)),
          commP (ŵ i) g ∈ twoCentralSeries (DR : Type) k := by
        intro i g
        have h := commP_mem_twoCentralSucc (hŵmem i) g
        rwa [← twoCentralSeries_succ (DR : Type) (by omega : 1 ≤ k - 1),
          show k - 1 + 1 = k by omega] at h
      exact mul_mem (mul_mem (mul_mem hsq (hcm 0 (a 0))) (hcm 1 (a 2))) (hcm 2 (a 1))
    · rw [map_dbarWordR0, ha 0, ha 1, ha 2]
      exact congrArg _ (funext hŵeq)
    · obtain ⟨x0, hx0⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 0)).u)
      obtain ⟨x1, hx1⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 1)).u)
      obtain ⟨x2, hx2⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 2)).u)
      have hmkeq2 : ∀ {p q : WL (k + 1)}, p⁻¹ * q ∈ wlKer (k + 1) k →
          (QuotientGroup.mk' (wlKer (k + 1) k)) p = (QuotientGroup.mk' (wlKer (k + 1) k)) q := by
        intro p q h
        simp only [QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr h
      have hval : dbarWordR0 (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)
          ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]
          = ⟨(1 + ((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR0 0))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)) * (Φ v (ŵ 0)).u
              + (((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR0 2))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) - 1) * (Φ v (ŵ 1)).u
              + (((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR0 1))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) - 1) * (Φ v (ŵ 2)).u, 1⟩ :=
        dbarWordR0_ref (R := ZMod (2 ^ (k + 1)))
          (PadicInt.toZModPow (k + 1) x0) (PadicInt.toZModPow (k + 1) x1)
          (PadicInt.toZModPow (k + 1) x2) (Φ v (ŵ 0)).u (Φ v (ŵ 1)).u (Φ v (ŵ 2)).u
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR0 0))
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR0 1))
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR0 2))
      have href : dbarWordR0 (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)
          ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]
          ∈ wlKer (k + 1) k := by
        rw [hval]
        have hd : ∀ i : Fin 3, (2 : ZMod (2 ^ (k + 1))) ^ (k - 2) ∣ (Φ v (ŵ i)).u := by
          intro i
          have h := (deriv_mem_wlCong hN (Φ v) (by omega : 1 ≤ k - 1) (hŵmem i)).1
          rwa [show k - 1 - 1 = k - 2 by omega] at h
        have hcoef0 : (2 : ℤ_[2]) ^ 2 ∣ 1 + (((chiTargetUnitsR0 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
          rw [show chiTargetUnitsR0 0 = -1 from by simp [chiTargetUnitsR0]]
          exact ⟨0, by simp⟩
        have hcoef1 : (2 : ℤ_[2]) ^ 2 ∣ (((chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
          rw [show chiTargetUnitsR0 1 = 1 from by simp [chiTargetUnitsR0]]
          exact ⟨0, by simp⟩
        have hcoef2 : (2 : ℤ_[2]) ^ 2 ∣ (((chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
          rw [show chiTargetUnitsR0 2 = etaUnit from by simp [chiTargetUnitsR0], etaUnit,
            inv_inv, negThreeUnit_val]
          exact ⟨-1, by ring⟩
        refine ⟨?_, ?_⟩
        · show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ _
          rw [red_coeff_one_add, red_coeff_sub_one, red_coeff_sub_one]
          exact dvd_add (dvd_add (dvd_coeff_mul (by omega) hkN hcoef0 (hd 0))
            (dvd_coeff_mul (by omega) hkN hcoef2 (hd 1)))
            (dvd_coeff_mul (by omega) hkN hcoef1 (hd 2))
        · show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ ((1 : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) - 1
          simp
      have hcong : (QuotientGroup.mk' (wlKer (k + 1) k))
            (dbarWordR0 (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)) (fun i => Φ v (ŵ i)))
          = (QuotientGroup.mk' (wlKer (k + 1) k))
            (dbarWordR0 (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
              (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)
              ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]) := by
        rw [map_dbarWordR0, map_dbarWordR0]
        have hfun : (fun i => (QuotientGroup.mk' (wlKer (k + 1) k)) (Φ v (ŵ i)))
            = fun i => (QuotientGroup.mk' (wlKer (k + 1) k))
              ((![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩,
                ⟨(Φ v (ŵ 2)).u, 1⟩]) i) := by
          funext i
          fin_cases i
          · exact hmkeq2 (hwslot v (ŵ 0) (hŵmem 0))
          · exact hmkeq2 (hwslot v (ŵ 1) (hŵmem 1))
          · exact hmkeq2 (hwslot v (ŵ 2) (hŵmem 2))
        rw [hfun, hmkeq2 (hslot v 0 x0 hx0), hmkeq2 (hslot v 1 x1 hx1),
          hmkeq2 (hslot v 2 x2 hx2)]
      have hB := (QuotientGroup.eq_one_iff _).mpr href
      have hmem := (QuotientGroup.eq_one_iff _).mp (hcong.trans hB)
      have hu := hmem.1
      rwa [← map_dbarWordR0] at hu
  -- the two tails, and the decomposition subgroup supplied by the span theorem
  have htz : ∀ i : Fin 3, canonLift (DR : Type) k (T i) ^ 2 ^ (k - 1) ∈ zLayer (DR : Type) k := by
    intro i
    have h := pow_two_pow_mem_lambdaImage (canonLift (DR : Type) k (T i)) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at h
  set P : Subgroup (levelQuot (DR : Type) (k + 1)) :=
    { carrier := {z | ∃ w : Fin 3 → levelQuot (DR : Type) (k + 1),
        (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) ∧ ∃ α β : ℕ,
          z = dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
                (canonLift (DR : Type) k (T 2)) w
              * (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α
              * (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β}
      one_mem' := ⟨fun _ => 1, fun _ => one_mem _, 0, 0, by
        rw [dbarWordR0_one, pow_zero, pow_zero, mul_one, mul_one]⟩
      mul_mem' := by
        rintro z z' ⟨w, hw, α, β, rfl⟩ ⟨w', hw', α', β', rfl⟩
        refine ⟨fun i => w i * w' i, fun i => mul_mem (hw i) (hw' i), α + α', β + β', ?_⟩
        have hcen : ∀ {z : levelQuot (DR : Type) (k + 1)}, z ∈ zLayer (DR : Type) k →
            ∀ t, z * t = t * z := fun hz t => (zLayer_commute hz t).eq
        rw [dbarWordR0_mul k hk _ _ _ hw hw', pow_add, pow_add]
        exact (central_shuffle3 (hcen (dbarWordR0_mem_zLayer (G := (DR : Type)) k hk _ _ _ hw'))
          (hcen (pow_mem (htz 1) α'))).symm
      inv_mem' := by
        rintro z ⟨w, hw, α, β, rfl⟩
        refine ⟨w, hw, α, β, ?_⟩
        refine zLayer_inv_self (G := (DR : Type)) ?_
        exact mul_mem (mul_mem (dbarWordR0_mem_zLayer (G := (DR : Type)) k hk _ _ _ hw)
          (pow_mem (htz 1) α)) (pow_mem (htz 2) β) } with hP
  have hδP : defectR0 k T ∈ P := by
    have hδz : defectR0 k T ∈ zLayer (DR : Type) k := defectR0_mem_zLayer k hrel
    have hsp := span_descent_r0 k hk (fun i => canonLift (DR : Type) k (T i)) hgent hδz
    refine (Subgroup.closure_le P).mpr ?_ hsp
    rintro z (⟨w, hw, rfl⟩ | hz)
    · exact ⟨w, hw, 0, 0, by rw [pow_zero, pow_zero, mul_one, mul_one]⟩
    · rcases hz with rfl | rfl
      · exact ⟨fun _ => 1, fun _ => one_mem _, 1, 0, by
          rw [dbarWordR0_one, pow_zero, pow_one, mul_one, one_mul]⟩
      · exact ⟨fun _ => 1, fun _ => one_mem _, 0, 1, by
          rw [dbarWordR0_one, pow_zero, pow_one, mul_one, one_mul]⟩
  obtain ⟨w, hw, α, β, hdec⟩ := hδP
  -- the tail combination lies in every derivation kernel
  have htail : ∀ v, levelMk (DR : Type) (k + 1)
      ((a 1 ^ 2 ^ (k - 1)) ^ α * (a 2 ^ 2 ^ (k - 1)) ^ β) ∈ derivKer (Φ v) k := by
    intro v
    have hz : levelMk (DR : Type) (k + 1) ((a 1 ^ 2 ^ (k - 1)) ^ α * (a 2 ^ 2 ^ (k - 1)) ^ β)
        = (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α
          * (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β := by
      rw [map_mul, map_pow, map_pow, map_pow, map_pow, ha 1, ha 2]
    have hsplit : (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α
          * (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β
        = (dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
            (canonLift (DR : Type) k (T 2)) w)⁻¹ * defectR0 k T := by
      rw [hdec]
      group
    rw [hz, hsplit]
    exact mul_mem (inv_mem (hdbarker v w hw)) (hδker v)
  -- the base values of the two tail slots are `≡ 1 (mod 4)`
  have hchi1 : (2 : ℤ_[2]) ^ 2 ∣ ((chiR (a 1) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have h := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) (hdev 1)
    rwa [show chiTargetUnitsR0 1 = 1 by simp [chiTargetUnitsR0], inv_one, mul_one] at h
  have heta4 : (2 : ℤ_[2]) ^ 2 ∣ ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have h3 : ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) * (-3) = 1 := by
      have h : ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) * ((negThreeUnit : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
        rw [etaUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      rwa [negThreeUnit_val] at h
    exact ⟨((etaUnit : ℤ_[2]ˣ) : ℤ_[2]), by linear_combination h3⟩
  have hchi2 : (2 : ℤ_[2]) ^ 2 ∣ ((chiR (a 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hA := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) (hdev 2)
    have hB : (2 : ℤ_[2]) ^ 2 ∣ ((chiTargetUnitsR0 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      rwa [show chiTargetUnitsR0 2 = etaUnit by simp [chiTargetUnitsR0]]
    have h := dvd_mul_sub_one hA hB
    rwa [← Units.val_mul, show chiR (a 2) * (chiTargetUnitsR0 2)⁻¹ * chiTargetUnitsR0 2
      = chiR (a 2) by group] at h
  have hpar := tail_parity (G := (DR : Type)) hk hN hkN Φ hchi1 hchi2
    (fun v => by rw [hbase v (a 1)]; rfl) (fun v => by rw [hbase v (a 2)]; rfl) α β htail
  have hc0 : (![0, (α : ZMod (2 ^ 1)), (β : ZMod (2 ^ 1))] : Fin 3 → ZMod (2 ^ 1)) = 0 := by
    refine thetaVec_indep hN (by omega) Φ ![drS, drX, drY] a hgenval hgent' ?_
    simpa using hpar
  have hα : (2 : ℕ) ∣ α := by
    have h1 := congrFun hc0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
    have := (ZMod.natCast_eq_zero_iff α (2 ^ 1)).mp h1
    rwa [pow_one] at this
  have hβ : (2 : ℕ) ∣ β := by
    have h2 := congrFun hc0 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at h2
    have := (ZMod.natCast_eq_zero_iff β (2 ^ 1)).mp h2
    rwa [pow_one] at this
  have htriv1 : (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α = 1 := by
    obtain ⟨m, rfl⟩ := hα
    rw [pow_mul, zLayer_sq (DR : Type) (htz 1), one_pow]
  have htriv2 : (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β = 1 := by
    obtain ⟨m, rfl⟩ := hβ
    rw [pow_mul, zLayer_sq (DR : Type) (htz 2), one_pow]
  rw [htriv1, htriv2, mul_one, mul_one] at hdec
  exact ⟨w, hw, by rw [← hdec, zLayer_inv_self (defectR0_mem_zLayer k hrel)]⟩

/-- SL1 (reachability), direction 2.  Fill: L4b. -/
theorem stageSL1R2 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) :
    ∃ w : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
        (canonLift (D0 : Type) k (T 2)) w = (defectR2 k T)⁻¹ := by
  sorry

/-- **SL2 (digit adjustment), direction 1**: for `T ∈ S^P_ₖ` (`k ≥ 3`) with vanishing
defect, some `ker d̄`-modification of the canonical lift lands in `S^P_{k+1}` — the memo's
"`ker d̄ₖ → (ℤ/2)²` onto" in its consumed form (the digit bookkeeping, including the
automatic vanishing of the π'd slot's fresh digit, is L4a's internal mechanism; the
dimension-count fallback of spike §2.5(c) is equally admissible).  Fill: L4a. -/
theorem stageSL2R0 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) (hδ : defectR0 k T = 1) :
    ∃ w : Fin 3 → levelQuot (DR : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) ∧
      dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
        (canonLift (DR : Type) k (T 2)) w = 1 ∧
      (fun i => canonLift (DR : Type) k (T i) * w i) ∈ sPR0 (k + 1) := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  choose g hg using fun i : Fin 3 =>
    levelMk_surjective (DR : Type) (k + 1) (canonLift (DR : Type) k (T i))
  -- the pinned targets and the mod-`8` anchor `η ≡ 5` (the `f = 2` discriminator)
  have ht0 : chiTargetUnitsR0 0 = -1 := by simp [chiTargetUnitsR0]
  have ht1 : chiTargetUnitsR0 1 = 1 := by simp [chiTargetUnitsR0]
  have ht2 : chiTargetUnitsR0 2 = etaUnit := by simp [chiTargetUnitsR0]
  have hη : PadicInt.toZModPow 3 ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR0, chiTargetUnitsR0] using chiTargetR0_three 2
  -- the level-`k` deviations of the three slots (this is the invariant `P` at level `k`)
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiR (g i) * (chiTargetUnitsR0 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiR (chiTargetUnitsR0 i)
      (by rw [← levelProj_levelMk, hg i, levelProj_canonLift]) ?_
    simpa [chiTargetR0] using hchi i
  -- the two moves at the group level, and their sharp level-`k` digits
  obtain ⟨Ug, hUg⟩ : ∃ Ug : (DR : Type), Ug = g 2 ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨Vg, hVg⟩ : ∃ Vg : (DR : Type), Vg = (g 1 * g 2) ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨du, hdu, hdu2⟩ : ∃ d : ℤ_[2], ((chiR Ug : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hUg, map_pow]
    exact sharp_move hk hη (by rw [← ht2]; exact hdev 2)
  obtain ⟨dv, hdv, hdv2⟩ : ∃ d : ℤ_[2], ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hVg, map_pow, map_mul]
    refine sharp_move hk hη ?_
    have h := dvd_mul_sub_one (hdev 1) (hdev 2)
    rw [← Units.val_mul] at h
    rwa [show (chiR (g 1) * (chiTargetUnitsR0 1)⁻¹) * (chiR (g 2) * (chiTargetUnitsR0 2)⁻¹)
      = chiR (g 1) * chiR (g 2) * etaUnit⁻¹ by rw [ht1, ht2]; group] at h
  -- the digit choices: the `y`-slot first, then the `s`-slot against the residue
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 2) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b - 1 := by
    rcases dvd_or_dvd_mul (by omega) (hdev 2) hdv hdv2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 1) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        (((chiR Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a * ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b) - 1 := by
    have h1 : (2 : ℤ_[2]) ^ k ∣
        ((chiR (g 1) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b - 1 :=
      dvd_mul_sub_one (hdev 1) (dvd_pow_sub_one ⟨dv, hdv⟩ b)
    rcases dvd_or_dvd_mul (by omega) h1 hdu hdu2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa [pow_one, mul_comm, mul_assoc, mul_left_comm] using h⟩
  -- the modification in `Q_{k+1}`: `p` a power of the `y`-slot, `q` a power of `s·y`
  obtain ⟨p, hpdef⟩ : ∃ p : levelQuot (DR : Type) (k + 1),
      p = (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 2)) ^ a := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : levelQuot (DR : Type) (k + 1),
      q = ((canonLift (DR : Type) k (T 1) * canonLift (DR : Type) k (T 2)) ^ 2 ^ (k - 2)) ^ b :=
    ⟨_, rfl⟩
  have hpm : p ∈ lambdaImage (DR : Type) (k - 1) (k + 1) := by
    rw [hpdef]
    refine Subgroup.pow_mem _ ?_ a
    have h := pow_two_pow_mem_lambdaImage (canonLift (DR : Type) k (T 2)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hqm : q ∈ lambdaImage (DR : Type) (k - 1) (k + 1) := by
    rw [hqdef]
    refine Subgroup.pow_mem _ ?_ b
    have h := pow_two_pow_mem_lambdaImage
      (canonLift (DR : Type) k (T 1) * canonLift (DR : Type) k (T 2)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hw : ∀ i, (![1, p * q, q] : Fin 3 → levelQuot (DR : Type) (k + 1)) i ∈
      lambdaImage (DR : Type) (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact one_mem _
    · exact mul_mem hpm hqm
    · exact hqm
  have hdbar : dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
      (canonLift (DR : Type) k (T 2)) ![1, p * q, q] = 1 := by
    refine dbarWordR0_kernel_witness k hk _ _ _ p q hqm ?_ ?_
    · rw [hpdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left a).eq
    · rw [hqdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left b).eq
  -- the corrected triple, presented at the group level
  have hlift0 : levelMk (DR : Type) (k + 1) (g 0)
      = canonLift (DR : Type) k (T 0) * ![1, p * q, q] 0 := by
    rw [hg 0]; simp
  have hlift1 : levelMk (DR : Type) (k + 1) (g 1 * (Ug ^ a * Vg ^ b))
      = canonLift (DR : Type) k (T 1) * ![1, p * q, q] 1 := by
    rw [hUg, hVg, hpdef, hqdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hlift2 : levelMk (DR : Type) (k + 1) (g 2 * Vg ^ b)
      = canonLift (DR : Type) k (T 2) * ![1, p * q, q] 2 := by
    rw [hVg, hqdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  -- the relator clause at level `k+1` (the defect is gone and the move is in `ker d̄`)
  have hrelQ : d0Word (canonLift (DR : Type) k (T 0) * ![1, p * q, q] 0)
      (canonLift (DR : Type) k (T 1) * ![1, p * q, q] 1)
      (canonLift (DR : Type) k (T 2) * ![1, p * q, q] 2) = 1 := by
    rw [d0Word_mul_lambdaImage k hk _ _ _ hw, hdbar, mul_one]
    exact hδ
  -- the `s`-slot clause, and then the π'd slot's automatic digit (memo §1.1)
  have hchi1 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 1 * (Ug ^ a * Vg ^ b)) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiR (g 1 * (Ug ^ a * Vg ^ b)) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiR (g 1) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          (((chiR Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a * ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b) := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact ha
  have hchi2 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 2 * Vg ^ b) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiR (g 2 * Vg ^ b) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiR (g 2) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact hb
  have hchi0 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 0) * (chiTargetUnitsR0 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    refine dvd_succ_of_sq (by omega) (hdev 0) ?_
    -- the corrected word dies in `Q_{k+1}`, so its χ-value is `1 mod 2^{k+2}`
    have hrelG : d0Word (g 0) (g 1 * (Ug ^ a * Vg ^ b)) (g 2 * Vg ^ b) ∈
        twoCentralSeries (DR : Type) (k + 1) := by
      have hmk : levelMk (DR : Type) (k + 1)
          (d0Word (g 0) (g 1 * (Ug ^ a * Vg ^ b)) (g 2 * Vg ^ b)) = 1 := by
        rw [map_d0Word, hlift0, hlift1, hlift2]
        exact hrelQ
      exact (QuotientGroup.eq_one_iff _).mp hmk
    have hW := dvd_chi_of_mem_twoCentralSeries chiR (k := k + 1) (by omega) hrelG
    rw [map_d0Word, d0Word_comm, Units.val_mul] at hW
    -- the `⁴`-slot is invisible at `2^{k+2}`, and `(−1)² = 1` kills the target of the `π`'d slot
    have h4 : (2 : ℤ_[2]) ^ (k + 1 + 1) ∣
        ((chiR (g 1 * (Ug ^ a * Vg ^ b)) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      rw [ht1, inv_one, mul_one] at hchi1
      refine dvd_trans (pow_dvd_pow 2 (by omega : k + 1 + 1 ≤ k + 1 + 2)) ?_
      have h := dvd_pow_two_pow_sub_one (k := k + 1) (by omega) hchi1 2
      rw [Units.val_pow_eq_pow_val]
      simpa using h
    have hsq0 : chiR (g 0) ^ 2 = (chiR (g 0) * (chiTargetUnitsR0 0)⁻¹) ^ 2 := by
      rw [ht0, mul_pow, show ((-1 : ℤ_[2]ˣ)⁻¹) ^ 2 = 1 by
        rw [inv_pow, neg_one_sq, inv_one], mul_one]
    rw [hsq0, Units.val_pow_eq_pow_val] at hW
    exact dvd_sub_one_of_mul hW h4
  refine ⟨![1, p * q, q], hw, hdbar, ⟨hrelQ, ?_⟩, ?_⟩
  · -- generation: the canonical lift generates (Frattini), and `λ₂`-moves preserve that
    have himg : (levelProj (DR : Type) k) ''
        (Set.range fun i => canonLift (DR : Type) k (T i)) = Set.range T := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => levelProj_canonLift (DR : Type) k (T i))
    have hgent : Subgroup.closure (Set.range fun i => canonLift (DR : Type) k (T i)) = ⊤ := by
      refine eq_top_of_map_levelProj_eq_top (DR : Type) drTopGenFinset isProP_DR (by omega) ?_
      rw [MonoidHom.map_closure, himg, hgen]
    exact closure_range_mul_eq_top_of_mem_lambdaImage_two (DR : Type) drTopGenFinset isProP_DR
      _ _ hgent fun i => lambdaImage_le_of_le (by omega) (hw i)
  · -- the χ-clause at level `k+1`
    intro i
    fin_cases i
    · exact chiLevel_eq_of_dvd chiR (chiTargetUnitsR0 0) hlift0 hchi0
    · exact chiLevel_eq_of_dvd chiR (chiTargetUnitsR0 1) hlift1 hchi1
    · exact chiLevel_eq_of_dvd chiR (chiTargetUnitsR0 2) hlift2 hchi2

/-- SL2 (digit adjustment), direction 2.  Fill: L4a. -/
theorem stageSL2R2 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) (hδ : defectR2 k T = 1) :
    ∃ w : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
        (canonLift (D0 : Type) k (T 2)) w = 1 ∧
      (fun i => canonLift (D0 : Type) k (T i) * w i) ∈ sPR2 (k + 1) := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  choose g hg using fun i : Fin 3 =>
    levelMk_surjective (D0 : Type) (k + 1) (canonLift (D0 : Type) k (T i))
  -- the pinned targets and the mod-`8` anchors `S ≡ X ≡ 5`
  have ht0 : chiTargetUnitsR2 0 = SvalUnit := by simp [chiTargetUnitsR2]
  have ht1 : chiTargetUnitsR2 1 = rootXUnit := by simp [chiTargetUnitsR2]
  have ht2 : chiTargetUnitsR2 2 = YvalUnit := by simp [chiTargetUnitsR2]
  have hS : PadicInt.toZModPow 3 ((SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 0
  have hX : PadicInt.toZModPow 3 ((rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 1
  -- the level-`k` deviations of the three slots
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiD0pres (g i) * (chiTargetUnitsR2 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiD0pres (chiTargetUnitsR2 i)
      (by rw [← levelProj_levelMk, hg i, levelProj_canonLift]) ?_
    simpa [chiTargetR2] using hchi i
  -- the two moves: a power of the `x`-slot moves slot `0`, a power of the `s`-slot moves
  -- slot `1`; each kills its own bracket, and the digits are independent
  obtain ⟨Ug, hUg⟩ : ∃ Ug : (D0 : Type), Ug = g 1 ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨Vg, hVg⟩ : ∃ Vg : (D0 : Type), Vg = g 0 ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨du, hdu, hdu2⟩ : ∃ d : ℤ_[2], ((chiD0pres Ug : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hUg, map_pow]
    exact sharp_move hk hX (by rw [← ht1]; exact hdev 1)
  obtain ⟨dv, hdv, hdv2⟩ : ∃ d : ℤ_[2], ((chiD0pres Vg : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hVg, map_pow]
    exact sharp_move hk hS (by rw [← ht0]; exact hdev 0)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 0) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiD0pres Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a - 1 := by
    rcases dvd_or_dvd_mul (by omega) (hdev 0) hdu hdu2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 1) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiD0pres Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b - 1 := by
    rcases dvd_or_dvd_mul (by omega) (hdev 1) hdv hdv2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  -- the modification in `Q_{k+1}`
  obtain ⟨p, hpdef⟩ : ∃ p : levelQuot (D0 : Type) (k + 1),
      p = (canonLift (D0 : Type) k (T 1) ^ 2 ^ (k - 2)) ^ a := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : levelQuot (D0 : Type) (k + 1),
      q = (canonLift (D0 : Type) k (T 0) ^ 2 ^ (k - 2)) ^ b := ⟨_, rfl⟩
  have hpm : p ∈ lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    rw [hpdef]
    refine Subgroup.pow_mem _ ?_ a
    have h := pow_two_pow_mem_lambdaImage (canonLift (D0 : Type) k (T 1)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hqm : q ∈ lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    rw [hqdef]
    refine Subgroup.pow_mem _ ?_ b
    have h := pow_two_pow_mem_lambdaImage (canonLift (D0 : Type) k (T 0)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hw : ∀ i, (![p, q, 1] : Fin 3 → levelQuot (D0 : Type) (k + 1)) i ∈
      lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact hpm
    · exact hqm
    · exact one_mem _
  have hdbar : dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
      (canonLift (D0 : Type) k (T 2)) ![p, q, 1] = 1 := by
    refine dbarWordR2_kernel_witness _ _ _ p q ?_ ?_
    · rw [hpdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left a).eq
    · rw [hqdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left b).eq
  -- the corrected triple, presented at the group level
  have hlift0 : levelMk (D0 : Type) (k + 1) (g 0 * Ug ^ a)
      = canonLift (D0 : Type) k (T 0) * ![p, q, 1] 0 := by
    rw [hUg, hpdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_zero]
  have hlift1 : levelMk (D0 : Type) (k + 1) (g 1 * Vg ^ b)
      = canonLift (D0 : Type) k (T 1) * ![p, q, 1] 1 := by
    rw [hVg, hqdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hlift2 : levelMk (D0 : Type) (k + 1) (g 2)
      = canonLift (D0 : Type) k (T 2) * ![p, q, 1] 2 := by
    rw [hg 2]; simp
  -- the relator clause at level `k+1`
  have hrelQ : drWord (canonLift (D0 : Type) k (T 0) * ![p, q, 1] 0)
      (canonLift (D0 : Type) k (T 1) * ![p, q, 1] 1)
      (canonLift (D0 : Type) k (T 2) * ![p, q, 1] 2) = 1 := by
    rw [drWord_mul_lambdaImage k hk _ _ _ hw, hdbar, mul_one]
    exact hδ
  -- the two moved slots, then the squared slot's automatic digit (memo §1.1, `r₂` mirror)
  have hchi0 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 0 * Ug ^ a) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiD0pres (g 0 * Ug ^ a) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiD0pres (g 0) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiD0pres Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact ha
  have hchi1 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiD0pres (g 1) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiD0pres Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact hb
  have hchi2 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 2) * (chiTargetUnitsR2 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    refine dvd_succ_of_sq (by omega) (hdev 2) ?_
    have hrelG : drWord (g 0 * Ug ^ a) (g 1 * Vg ^ b) (g 2) ∈
        twoCentralSeries (D0 : Type) (k + 1) := by
      have hmk : levelMk (D0 : Type) (k + 1) (drWord (g 0 * Ug ^ a) (g 1 * Vg ^ b) (g 2)) = 1 := by
        rw [map_drWord, hlift0, hlift1, hlift2]
        exact hrelQ
      exact (QuotientGroup.eq_one_iff _).mp hmk
    have hW := dvd_chi_of_mem_twoCentralSeries chiD0pres (k := k + 1) (by omega) hrelG
    rw [map_drWord, drWord_comm] at hW
    -- the `x`-slot enters only at `2^{k+2}`, and `X⁻⁴·Y² = 1` holds on the nose
    have h4 : (2 : ℤ_[2]) ^ (k + 1 + 1) ∣
        (((chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      refine dvd_trans (pow_dvd_pow 2 (by omega : k + 1 + 1 ≤ k + 1 + 2)) ?_
      have h := dvd_pow_two_pow_sub_one (k := k + 1) (by omega) hchi1 2
      rw [Units.val_pow_eq_pow_val]
      simpa using h
    have hid : (chiD0pres (g 2) * (chiTargetUnitsR2 2)⁻¹) ^ 2
        = ((chiD0pres (g 1 * Vg ^ b) ^ 4)⁻¹ * chiD0pres (g 2) ^ 2) *
          (chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹) ^ 4 := by
      have hAB : ∀ A B C : ℤ_[2]ˣ, A⁻¹ * B * (A * C) = B * C := by
        intro A B C
        rw [show A⁻¹ * B * (A * C) = A⁻¹ * (B * A) * C by group, mul_comm B A,
          show A⁻¹ * (A * B) * C = A⁻¹ * A * (B * C) by group, inv_mul_cancel, one_mul]
      rw [mul_pow, mul_pow, hAB, ht1, ht2, inv_pow, inv_pow, YvalUnit_sq_eq]
    have hcomb := dvd_mul_sub_one hW h4
    rw [← Units.val_mul, ← hid, Units.val_pow_eq_pow_val] at hcomb
    exact hcomb
  refine ⟨![p, q, 1], hw, hdbar, ⟨hrelQ, ?_⟩, ?_⟩
  · -- generation
    have himg : (levelProj (D0 : Type) k) ''
        (Set.range fun i => canonLift (D0 : Type) k (T i)) = Set.range T := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => levelProj_canonLift (D0 : Type) k (T i))
    have hgent : Subgroup.closure (Set.range fun i => canonLift (D0 : Type) k (T i)) = ⊤ := by
      refine eq_top_of_map_levelProj_eq_top (D0 : Type) d0TopGenFinset SectionThree.d0_isProP
        (by omega) ?_
      rw [MonoidHom.map_closure, himg, hgen]
    exact closure_range_mul_eq_top_of_mem_lambdaImage_two (D0 : Type) d0TopGenFinset
      SectionThree.d0_isProP _ _ hgent fun i => lambdaImage_le_of_le (by omega) (hw i)
  · -- the χ-clause at level `k+1`
    intro i
    fin_cases i
    · exact chiLevel_eq_of_dvd chiD0pres (chiTargetUnitsR2 0) hlift0 hchi0
    · exact chiLevel_eq_of_dvd chiD0pres (chiTargetUnitsR2 1) hlift1 hchi1
    · exact chiLevel_eq_of_dvd chiD0pres (chiTargetUnitsR2 2) hlift2 hchi2

/-- **The stage step, direction 1** (spike §2.4's conclusion; the exact interface the
assembly consumes): `S^P_ₖ ≠ ∅ → S^P_{k+1} ≠ ∅` for `k ≥ 3`.

Proved here from the frozen statements (SL1 → shift formula → modification stability →
SL2) as the L1 composability certificate — no fill needed; it inherits the upstream
sorries. -/
theorem stageStepR0 (k : ℕ) (hk : 3 ≤ k) (h : (sPR0 k).Nonempty) :
    (sPR0 (k + 1)).Nonempty := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨w, hw, hd⟩ := stageSL1R0 k hk hT
  have hT₁ : (fun i => T i * levelProj (DR : Type) k (w i)) ∈ sPR0 k :=
    sPR0_mul_mem k hk hT fun i => levelProj_mem_lambdaImage (DR : Type) (hw i)
  have hδ₁ : defectR0 k (fun i => T i * levelProj (DR : Type) k (w i)) = 1 := by
    rw [defectR0_mul k hk hw, hd, mul_inv_cancel]
  obtain ⟨w', hw', hker, hmem⟩ := stageSL2R0 k hk hT₁ hδ₁
  exact ⟨_, hmem⟩

/-- The stage step, direction 2 (proved from the frozen statements; composability
certificate). -/
theorem stageStepR2 (k : ℕ) (hk : 3 ≤ k) (h : (sPR2 k).Nonempty) :
    (sPR2 (k + 1)).Nonempty := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨w, hw, hd⟩ := stageSL1R2 k hk hT
  have hT₁ : (fun i => T i * levelProj (D0 : Type) k (w i)) ∈ sPR2 k :=
    sPR2_mul_mem k hk hT fun i => levelProj_mem_lambdaImage (D0 : Type) (hw i)
  have hδ₁ : defectR2 k (fun i => T i * levelProj (D0 : Type) k (w i)) = 1 := by
    rw [defectR2_mul k hk hw, hd, mul_inv_cancel]
  obtain ⟨w', hw', hker, hmem⟩ := stageSL2R2 k hk hT₁ hδ₁
  exact ⟨_, hmem⟩

end GQ2.Roe.Labute
