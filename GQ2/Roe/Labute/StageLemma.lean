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

/-! ## The congruence calculus (spike §2.1; generic pro-2 `G`, `k ≥ 3`)

The full profinite instance pack is carried deliberately (the fills run through
closed-map/compactness arguments on λ-layers); the three instantiations `D_R`, `D₀`,
`freeProTwo` all satisfy it. -/

section Congruence

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

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
  sorry

/-- Frattini-only dependence, `r₂` side.  Fill: L4a. -/
theorem dbarWordR2_congr_slots (k : ℕ) (hk : 3 ≤ k)
    {s x y s' x' y' : levelQuot G (k + 1)}
    (hs : s⁻¹ * s' ∈ lambdaImage G 2 (k + 1)) (hx : x⁻¹ * x' ∈ lambdaImage G 2 (k + 1))
    (hy : y⁻¹ * y' ∈ lambdaImage G 2 (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y w = dbarWordR2 s' x' y' w := by
  sorry

/-- **`Z_{k-1}`-class dependence on the modification** (spike §2.1: `v ↦ v²` is
`𝔽₂`-linear on classes and `[v, g]` depends only on `v mod λₖ`): the `r₀`-shift word is
unchanged when `w` moves by `λₖ`-classes.  Fill: L4a. -/
theorem dbarWordR0_congr_mod (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hww' : ∀ i, (w i)⁻¹ * w' i ∈ lambdaImage G k (k + 1)) :
    dbarWordR0 a s y w = dbarWordR0 a s y w' := by
  sorry

/-- `Z_{k-1}`-class dependence on the modification, `r₂` side.  Fill: L4a. -/
theorem dbarWordR2_congr_mod (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hww' : ∀ i, (w i)⁻¹ * w' i ∈ lambdaImage G k (k + 1)) :
    dbarWordR2 s x y w = dbarWordR2 s x y w' := by
  sorry

end Congruence

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
  sorry

/-- The transported shift formula, direction 2.  Fill: L4a. -/
theorem defectR2_mul (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    {w : Fin 3 → levelQuot (D0 : Type) (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) :
    defectR2 k (fun i => T i * levelProj (D0 : Type) k (w i)) =
      defectR2 k T *
        dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
          (canonLift (D0 : Type) k (T 2)) w := by
  sorry

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
