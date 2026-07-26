/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.Levelwise

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

/-! ## The shift word shapes -/

/-- The **`r₀`-side defect-shift word** `d̄(w) = w₁²·[w₁,a]·[w₂,y]·[w₃,s]` at the triple
`(a, s, y)` (spike §2.2; repo `commP`).  A word shape in any group; its homomorphism
property on `Z`-layer classes is part of the L4a calculus, not of the definition. -/
def dbarWordR0 {G : Type*} [Group G] (a s y : G) (w : Fin 3 → G) : G :=
  w 0 ^ 2 * commP (w 0) a * commP (w 1) y * commP (w 2) s

/-- The **`r₂`-side defect-shift word** `d̄(u,v,w) = w²·[w,y]·[u,x]·[v,s]` at the triple
`(s, x, y)` (spike §2.2 — note the r₂-tails/cross-terms pair `(u,x), (v,s)`, *not* the
draft's `(x, y)` pairing). -/
def dbarWordR2 {G : Type*} [Group G] (s x y : G) (w : Fin 3 → G) : G :=
  w 2 ^ 2 * commP (w 2) y * commP (w 0) x * commP (w 1) s

/-- Naturality of the `r₀`-shift word (smoke). -/
theorem map_dbarWordR0 {F G H : Type*} [Group G] [Group H] [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (a s y : G) (w : Fin 3 → G) :
    φ (dbarWordR0 a s y w) = dbarWordR0 (φ a) (φ s) (φ y) (fun i => φ (w i)) := by
  simp only [dbarWordR0, commP, map_mul, map_inv, map_pow]

/-- Naturality of the `r₂`-shift word (smoke). -/
theorem map_dbarWordR2 {F G H : Type*} [Group G] [Group H] [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (s x y : G) (w : Fin 3 → G) :
    φ (dbarWordR2 s x y w) = dbarWordR2 (φ s) (φ x) (φ y) (fun i => φ (w i)) := by
  simp only [dbarWordR2, commP, map_mul, map_inv, map_pow]

/-- Abelian collapse (smoke): only the square survives — the cross terms are honest
commutators. -/
theorem dbarWordR0_comm {G : Type*} [CommGroup G] (a s y : G) (w : Fin 3 → G) :
    dbarWordR0 a s y w = w 0 ^ 2 := by
  rw [dbarWordR0, commP_eq_one, commP_eq_one, commP_eq_one, mul_one, mul_one, mul_one]

/-- Trivial modification, trivial shift (smoke). -/
theorem dbarWordR0_one {G : Type*} [Group G] (a s y : G) :
    dbarWordR0 a s y (fun _ => 1) = 1 := by
  simp [dbarWordR0, commP]

/-- Trivial modification, trivial shift, `r₂` side (smoke). -/
theorem dbarWordR2_one {G : Type*} [Group G] (s x y : G) :
    dbarWordR2 s x y (fun _ => 1) = 1 := by
  simp [dbarWordR2, commP]

/-! ### The λ-grading lemma (L4b fill helper; Hall–Witt calculus)

`⁅λₐ, λᵦ⁆ ≤ λ_{a+b}` — the graded-bracket bound underlying every depth estimate of the
span reduction (spike §2.5(a)'s identity list).  Proved by induction on `b` via the three
subgroups lemma (transported from mathlib's `⊥`-form through the quotient by `λ_{a+b}`)
and the closed-subgroup trick for the topological closure step. -/

section Grading

variable {G : Type*} [Group G]

open scoped commutatorElement in
/-- The three subgroups lemma, `≤ N`-form: transport of
`Subgroup.commutator_commutator_eq_bot_of_rotate` through `G ⧸ N`. -/
theorem commutator_commutator_le_of_rotate {A B C N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅B, C⁆, A⁆ ≤ N) (h2 : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  have key : ∀ X Y Z : Subgroup G, ⁅⁅X, Y⁆, Z⁆ ≤ N ↔
      ⁅⁅X.map (QuotientGroup.mk' N), Y.map (QuotientGroup.mk' N)⁆,
        Z.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    intro X Y Z
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

variable (G) [TopologicalSpace G] [IsTopologicalGroup G]

open scoped commutatorElement in
/-- One-step bound, subgroup form: `⁅λₐ, ⊤⁆ ≤ λ_{a+1}`. -/
theorem commutator_twoCentralSeries_top_le (a : ℕ) :
    ⁅twoCentralSeries G a, (⊤ : Subgroup G)⁆ ≤ twoCentralSeries G (a + 1) := by
  rw [Subgroup.commutator_le]
  intro v hv g _
  exact commutator_mem_twoCentralSeries_succ G hv g

open scoped commutatorElement in
/-- **The λ-grading lemma** (`GRAD`): `⁅λₐ, λᵦ⁆ ≤ λ_{a+b}`. -/
theorem commutator_twoCentralSeries_le :
    ∀ (b a : ℕ), ⁅twoCentralSeries G a, twoCentralSeries G b⁆ ≤ twoCentralSeries G (a + b)
  | 0, a => by
    simpa using (commutator_twoCentralSeries_top_le G a).trans
      (twoCentralSeries_antitone G (Nat.le_succ a))
  | 1, a => by simpa using commutator_twoCentralSeries_top_le G a
  | (b + 2), a => by
    -- Notation: `N = λ_{a+b+2}` is the target, `H = λ_{b+1}` the penultimate layer.
    set N := twoCentralSeries G (a + (b + 2)) with hN
    set H := twoCentralSeries G (b + 1) with hH
    haveI hNn : N.Normal := twoCentralSeries_normal G _
    rw [Subgroup.commutator_le]
    intro v hv h hh
    -- The membership set of `v`-brackets is a closed subgroup; unfold `λ_{b+2}` into it.
    set S : Subgroup G :=
      { carrier := {g | ⁅v, g⁆ ∈ N}
        one_mem' := by simp
        mul_mem' := by
          intro g₁ g₂ hg₁ hg₂
          show ⁅v, g₁ * g₂⁆ ∈ N
          have hexp : ⁅v, g₁ * g₂⁆ = ⁅v, g₁⁆ * (g₁ * ⁅v, g₂⁆ * g₁⁻¹) := by group
          rw [hexp]
          exact N.mul_mem hg₁ (Subgroup.Normal.conj_mem hNn _ hg₂ g₁)
        inv_mem' := by
          intro g hg
          show ⁅v, g⁻¹⁆ ∈ N
          have hexp : ⁅v, g⁻¹⁆ = g⁻¹ * ⁅v, g⁆⁻¹ * g := by group
          rw [hexp]
          exact Subgroup.Normal.conj_mem' hNn _ (N.inv_mem hg) g } with hS
    have hSclosed : IsClosed (S : Set G) := by
      have : (S : Set G) = (fun g => ⁅v, g⁆) ⁻¹' (N : Set G) := rfl
      rw [this]
      refine (isClosed_twoCentralSeries G _).preimage ?_
      simp only [commutatorElement_def]
      fun_prop
    -- Atom cases over `λ_{b+1}`.
    have hsq : ∀ u ∈ H, u ^ 2 ∈ S := by
      intro u hu
      have hvu : ⁅v, u⁆ ∈ twoCentralSeries G (a + (b + 1)) :=
        commutator_twoCentralSeries_le (b + 1) a (Subgroup.commutator_mem_commutator hv hu)
      have hexp : ⁅v, u ^ 2⁆ = ⁅v, u⁆ ^ 2 * ⁅⁅v, u⁆⁻¹, u⁆ := by
        simp [commutatorElement_def, pow_two, mul_assoc]
      have h1 : ⁅v, u⁆ ^ 2 ∈ N := by
        have := sq_mem_twoCentralSeries_succ G hvu
        rwa [show a + (b + 1) + 1 = a + (b + 2) from rfl] at this
      have h2 : ⁅⁅v, u⁆⁻¹, u⁆ ∈ N := by
        have := commutator_mem_twoCentralSeries_succ G
          ((twoCentralSeries G (a + (b + 1))).inv_mem hvu) u
        rwa [show a + (b + 1) + 1 = a + (b + 2) from rfl] at this
      show ⁅v, u ^ 2⁆ ∈ N
      rw [hexp]
      exact N.mul_mem h1 h2
    have hbr : ∀ u ∈ H, ∀ g : G, ⁅u, g⁆ ∈ S := by
      intro u hu g
      have hrot : ⁅⁅H, (⊤ : Subgroup G)⁆, twoCentralSeries G a⁆ ≤ N := by
        refine commutator_commutator_le_of_rotate ?_ ?_
        · -- `⁅⁅⊤, λₐ⁆, λ_{b+1}⁆ ≤ N` via the induction hypothesis at `(a+1, b+1)`.
          refine (Subgroup.commutator_mono
            ((Subgroup.commutator_comm _ _).le.trans
              (commutator_twoCentralSeries_top_le G a)) le_rfl).trans ?_
          have := commutator_twoCentralSeries_le (b + 1) (a + 1)
          rwa [show a + 1 + (b + 1) = a + (b + 2) from by omega] at this
        · -- `⁅⁅λₐ, λ_{b+1}⁆, ⊤⁆ ≤ N` via the induction hypothesis at `(a, b+1)` + one step.
          refine (Subgroup.commutator_mono
            (commutator_twoCentralSeries_le (b + 1) a) le_rfl).trans ?_
          exact (commutator_twoCentralSeries_top_le G _)
      show ⁅v, ⁅u, g⁆⁆ ∈ N
      refine hrot ?_
      have hw : ⁅u, g⁆ ∈ ⁅H, (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator hu (Subgroup.mem_top g)
      have hflip : ⁅v, ⁅u, g⁆⁆ = ⁅⁅u, g⁆, v⁆⁻¹ := by group
      rw [hflip]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hw hv)
    -- Assemble: `S` contains the generating join and is closed, hence contains `λ_{b+2}`.
    have hle : twoCentralSeries G (b + 2) ≤ S := by
      rw [twoCentralSeries_succ G (Nat.le_add_left 1 b), twoCentralSucc]
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hSclosed
      · rw [Subgroup.closure_le]
        rintro _ ⟨u, hu, rfl⟩
        exact hsq u hu
      · rw [Subgroup.commutator_le]
        intro u hu g _
        exact hbr u hu g
    exact hle hh

open scoped commutatorElement in
/-- Element form of the grading lemma. -/
theorem commutator_mem_twoCentralSeries_add {a b : ℕ} {v h : G}
    (hv : v ∈ twoCentralSeries G a) (hh : h ∈ twoCentralSeries G b) :
    ⁅v, h⁆ ∈ twoCentralSeries G (a + b) :=
  commutator_twoCentralSeries_le G b a (Subgroup.commutator_mem_commutator hv hh)

end Grading

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

/-- **The modification-congruence atoms** (spike §2.1): squaring is `𝔽₂`-linear on `Zₖ`-classes
and `commP · g` is insensitive to a central left factor. -/
private theorem sq_congr_mod {k : ℕ} {v v' : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : v ^ 2 = v' ^ 2 := by
  obtain ⟨z, hz, rfl⟩ := exists_zLayer_mul_left h
  rw [(zLayer_commute hz v).mul_pow, zLayer_sq G hz, one_mul]

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

/-- A `λ_{k-1}`-modification squares into the central layer. -/
private theorem sq_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) : v ^ 2 ∈ zLayer G k := by
  obtain ⟨x, hx, rfl⟩ := hv
  refine ⟨x ^ 2, ?_, by rw [map_pow]⟩
  have h := sq_mem_twoCentralSeries_succ G hx
  rwa [show k - 1 + 1 = k by omega] at h

/-- Every `commP` of a `λ_{k-1}`-modification is central. -/
private theorem commP_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (g : levelQuot G (k + 1)) :
    commP v g ∈ zLayer G k := by
  have hgt : g ∈ lambdaImage G 1 (k + 1) := by rw [lambdaImage_one_eq_top]; trivial
  have h := commP_mem_lambdaImage_add hv hgt
  rwa [show k - 1 + 1 = k by omega] at h

/-- `λ₂` and `λ_{k-1}` commute outright in `Q_{k+1}` (`[λ₂, λ_{k-1}] ⊆ λ_{k+1} = 1`). -/
private theorem commP_lambdaTwo_eq_one (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP c v = 1 := by
  have h := commP_mem_lambdaImage_add hc hv
  rw [show 2 + (k - 1) = k + 1 by omega, lambdaImage_self] at h
  simpa using h

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
    (e₀ : z₀ ^ 2 = 1) (e₁ : z₁ ^ 2 = 1) (e₂ : z₂ ^ 2 = 1) (a s y : H) :
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

/-- **Modification stability of `S^P_ₖ`, direction 1** (spike §2.1 + §2.4): `λ_{k-1}`-moves
preserve all three clauses — relator kill (the shift lands in `λₖ`), generation
(Frattini: `λ_{k-1} ⊆ λ₂` for `k ≥ 3`), and the χ-clause (`χ(λ_{k-1}) ⊆ 1 + 2^k ℤ₂` — the
design reason `P` survives the calculus).  Fill: L4a. -/
theorem sPR0_mul_mem (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) {w : Fin 3 → levelQuot (DR : Type) k}
    (hw : ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) k) :
    (fun i => T i * w i) ∈ sPR0 k := by
  sorry

/-- Modification stability, direction 2.  Fill: L4a. -/
theorem sPR2_mul_mem (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) {w : Fin 3 → levelQuot (D0 : Type) k}
    (hw : ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) k) :
    (fun i => T i * w i) ∈ sPR2 k := by
  sorry

/-! ## The span theorem (spike §2.3; L4b) -/

/-- The free pro-2 group `F₃` on three generators — the *only* group in which the span
theorem is proved (spike §2.3: "The Lean statement only ever needs the free version");
the towers receive it by descent. -/
noncomputable def freeProTwo : ProfiniteGrp :=
  maxProPQuotient 2 (FreeProfiniteGroup (Fin 3))

/-- The marked generators of `F₃`. -/
noncomputable def freeGen (i : Fin 3) : (freeProTwo : Type) :=
  maxProPMk 2 (FreeProfiniteGroup (Fin 3)) (FreeProfiniteGroup.of i)

/-! ### Descent infrastructure (L4b fill helpers; not part of the frozen interface)

For a topologically f.g. pro-2 `G` the level quotients are finite *discrete* groups, the
λ-series of `Qₘ` is the image of the λ-series of `G` (`map_twoCentralSeries_eq` along
`levelMk`), and in particular `λₘ(Qₘ) = ⊥`.  These are the transport facts through which
the free span statement descends to the towers. -/

section DescentInfra

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The level quotients of a topologically f.g. pro-2 group are discrete (`λₘ` is open). -/
theorem discreteTopology_levelQuot
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) : DiscreteTopology (levelQuot G m) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨g, rfl⟩ := levelMk_surjective G m q
  have hset : (QuotientGroup.mk : G → levelQuot G m) ⁻¹' {levelMk G m g} =
      (fun x : G => x⁻¹ * g) ⁻¹' (twoCentralSeries G m : Set G) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    exact (QuotientGroup.eq (s := twoCentralSeries G m)).trans Iff.rfl
  have hopen : IsOpen ((QuotientGroup.mk : G → levelQuot G m) ⁻¹' {levelMk G m g}) := by
    rw [hset]
    exact (isOpen_twoCentralSeries G hfg hpro m).preimage (by fun_prop)
  exact ((QuotientGroup.isQuotientMap_mk (twoCentralSeries G m)).isOpen_preimage).mp hopen

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The canonical projection `levelMk` is continuous. -/
theorem continuous_levelMk (m : ℕ) : Continuous (levelMk G m) :=
  QuotientGroup.continuous_mk

/-- **λ-transport along `levelMk`**: the two-index image `λⱼλₘ/λₘ` *is* the `j`-th layer of
the λ-series of the level quotient `Qₘ` (verbal functoriality for the continuous epi
`levelMk`, using discreteness of the target). -/
theorem lambdaImage_eq_twoCentralSeries_levelQuot
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (j m : ℕ) :
    lambdaImage G j m = twoCentralSeries (levelQuot G m) j := by
  haveI := discreteTopology_levelQuot G hfg hpro m
  exact map_twoCentralSeries_eq (levelMk G m) (continuous_levelMk G m)
    (levelMk_surjective G m) j

/-- The λ-series of the level-`m` quotient vanishes at level `m`. -/
theorem twoCentralSeries_levelQuot_self
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) : twoCentralSeries (levelQuot G m) m = ⊥ := by
  rw [← lambdaImage_eq_twoCentralSeries_levelQuot G hfg hpro m m, lambdaImage,
    Subgroup.map_eq_bot_iff, levelMk, QuotientGroup.ker_mk']

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Mapping into a *discrete* group erases topological closures: the image of `cl K` is
the image of `K` (the preimage of the image subgroup is clopen). -/
theorem map_topologicalClosure_eq_of_discrete {H : Type*} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] (K : Subgroup G) (f : G →* H) (hf : Continuous f) :
    K.topologicalClosure.map f = K.map f := by
  refine le_antisymm ?_ (Subgroup.map_mono K.le_topologicalClosure)
  have hle : K.topologicalClosure ≤ Subgroup.comap f (K.map f) := by
    refine Subgroup.topologicalClosure_minimal K (Subgroup.le_comap_map f K) ?_
    exact (isClosed_discrete ((K.map f : Subgroup H) : Set H)).preimage hf
  exact (Subgroup.map_mono hle).trans (Subgroup.map_comap_le f (K.map f))

omit [T2Space G] [TotallyDisconnectedSpace G] in
open scoped commutatorElement in
/-- **Atomization of the layer images** (L4b workhorse): for topologically f.g. pro-2 `G`,
a property closed under the group operations that holds on the residues of squares `v²`
and brackets `⁅v, g⁆` (`v ∈ λⱼ`, `g ∈ G`) holds on all of `λ_{j+1}λₘ/λₘ ≤ Qₘ`.  This is
the mod-`λₘ` shadow of the verbal generation of `λ_{j+1}`, with the topological closure
erased by discreteness of the finite quotient. -/
theorem lambdaImage_induction [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {j m : ℕ} (hj : 1 ≤ j) {p : levelQuot G m → Prop}
    (hsq : ∀ v ∈ twoCentralSeries G j, p (levelMk G m (v ^ 2)))
    (hbr : ∀ v ∈ twoCentralSeries G j, ∀ g : G, p (levelMk G m ⁅v, g⁆))
    (hone : p 1) (hmul : ∀ x y, p x → p y → p (x * y)) (hinv : ∀ x, p x → p x⁻¹)
    {q : levelQuot G m} (hq : q ∈ lambdaImage G (j + 1) m) : p q := by
  haveI := discreteTopology_levelQuot G hfg hpro m
  have hsucc : twoCentralSeries G (j + 1) =
      (Subgroup.closure (((fun v : G => v ^ 2) '' (twoCentralSeries G j : Set G)) ∪
        {g | ∃ g₁ ∈ twoCentralSeries G j, ∃ g₂ ∈ (⊤ : Subgroup G), ⁅g₁, g₂⁆ = g})
      ).topologicalClosure := by
    rw [twoCentralSeries_succ G hj, twoCentralSucc, Subgroup.closure_union,
      ← Subgroup.commutator_def]
  rw [lambdaImage, hsucc,
    map_topologicalClosure_eq_of_discrete G _ _ (continuous_levelMk G m),
    MonoidHom.map_closure] at hq
  refine Subgroup.closure_induction ?_ hone (fun x y _ _ => hmul x y) (fun x _ => hinv x) hq
  rintro _ ⟨x, hx | hx, rfl⟩
  · obtain ⟨v, hv, rfl⟩ := hx
    exact hsq v hv
  · obtain ⟨v, hv, g, -, rfl⟩ := hx
    exact hbr v hv g

end DescentInfra

section FreeLift

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `F₃`** (L4b helper): a bare triple in a pro-2 group `H`
classifies a continuous hom `F₃ → H` — `drLiftHom`/`d0LiftHom` without the relator step. -/
noncomputable def freeProTwoLift (hH : IsProP 2 H) (m : Fin 3 → H) :
    ContinuousMonoidHom (freeProTwo : Type) H :=
  (maxProPHomEquiv hH).symm
    ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom

@[simp] theorem freeProTwoLift_freeGen (hH : IsProP 2 H) (m : Fin 3 → H) (i : Fin 3) :
    freeProTwoLift hH m (freeGen i) = m i := by
  show ((maxProPHomEquiv hH).symm _)
    (maxProPMk 2 (FreeProfiniteGroup (Fin 3)) (FreeProfiniteGroup.of i)) = m i
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact FreeProfiniteGroup.homEquiv_symm_of _ _ _

end FreeLift

/-- **`F₃` is topologically generated by its marked generators** (density of the abstract
free group in its profinite completion — `ProfiniteGrp.ProfiniteCompletion.denseRange` — pushed through
the surjective pro-2 projection; the `AdmissibleLimit.lean` generation pattern). -/
theorem topGen_freeProTwo :
    (Subgroup.closure (Set.range freeGen)).topologicalClosure = ⊤ := by
  have hdense : DenseRange (⇑(maxProPMk 2 (FreeProfiniteGroup (Fin 3))) ∘
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3)))) :=
    DenseRange.comp (Function.Surjective.denseRange (quotientMk_surjective _))
      (ProfiniteGrp.ProfiniteCompletion.denseRange _)
      (maxProPMk 2 (FreeProfiniteGroup (Fin 3))).continuous_toFun
  -- every word-image lies in the subgroup generated by the marked generators
  have hmem : ∀ w : FreeGroup (Fin 3),
      maxProPMk 2 (FreeProfiniteGroup (Fin 3))
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3))) w)
        ∈ Subgroup.closure (Set.range freeGen) := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 =>
      show (1 : (freeProTwo : Type)) ∈ _
      exact one_mem _
    | of x => exact Subgroup.subset_closure ⟨x, rfl⟩
    | inv_of x hx =>
      show (maxProPMk 2 (FreeProfiniteGroup (Fin 3))
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3)))
          (FreeGroup.of x)))⁻¹ ∈ _
      exact Subgroup.inv_mem _ hx
    | mul x y hx hy =>
      show maxProPMk 2 (FreeProfiniteGroup (Fin 3))
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3))) x) *
        maxProPMk 2 (FreeProfiniteGroup (Fin 3))
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3))) y) ∈ _
      exact Subgroup.mul_mem _ hx hy
  refine SetLike.ext' ?_
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top]
  refine Dense.closure_eq (Dense.mono ?_ hdense)
  rintro _ ⟨w, rfl⟩
  exact hmem w

/-- `Finset` form of `topGen_freeProTwo` (the `hfg`-hypothesis shape of the tower API). -/
private theorem freeTopGenFinset :
    ∃ s : Finset (freeProTwo : Type),
      (Subgroup.closure (s : Set (freeProTwo : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{freeGen 0, freeGen 1, freeGen 2}, ?_⟩
  have h : (({freeGen 0, freeGen 1, freeGen 2} : Finset (freeProTwo : Type)) :
      Set (freeProTwo : Type)) = Set.range freeGen := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> tauto
  rw [h]
  exact topGen_freeProTwo

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
          levelMk (freeProTwo : Type) (k + 1) (freeGen 2) ^ 2 ^ (k - 1)}) := by
  sorry

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
          levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1)}) := by
  sorry

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

/-! ## The stage lemma: SL1, SL2, and the step (spike §2.4) -/

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
  sorry

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
  sorry

/-- SL2 (digit adjustment), direction 2.  Fill: L4a. -/
theorem stageSL2R2 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) (hδ : defectR2 k T = 1) :
    ∃ w : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
        (canonLift (D0 : Type) k (T 2)) w = 1 ∧
      (fun i => canonLift (D0 : Type) k (T i) * w i) ∈ sPR2 (k + 1) := by
  sorry

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
