# B9-A proof plan — restate B9 via the relative Stiefel–Whitney identity

Owner-approved 2026-07-24 (Angdinata review response, `docs/angdinata-review-plan.md` §5, option
B9-A).  Goal: replace the composite axiom **B9** (`GQ2.evensKahn_dyadic`) by a cleaner axiom
stated at the quadratic-form level — the *relative Stiefel–Whitney identity* — and **prove**
today's `evensKahn_dyadic` from it, with a byte-identical statement (the B7′/B11b/B12/B13 flip
pattern: same name, zero consumer churn).  Census stays at 9; ledger label **B9** moves to the
new declaration.

## The new axiom (working name `relativeStiefelWhitney_dyadic`)

Setting (unchanged from B9): `k/ℚ₂` finite inside the fixed `ℚ̄₂`; `d ∈ kˣ` with `δ² = d` and
`L = k(δ)` quadratic over `k`; `a ∈ Lˣ`; `[a] ∈ H¹(G_L, 𝔽₂)` enters through the Kummer cocycle
`α` of a square root `β` of `a` (the current `hαdef` plumbing — this is the faithful encoding and
stays).  New content: the left-hand sides become genuine **form invariants**.  In total-class
form (docstring; the Lean statement carries the two components):

  `w(Tr_{L/k}⟨a⟩) = w(Tr_{L/k}⟨1⟩) · (1 + cor_{L/k}[a] + N^{Ev}_{L/k}[a])`   (degrees ≤ 2)

i.e. componentwise, with `w₁ q ∈ H¹(G_k, 𝔽₂)`, `w₂ q ∈ H²(G_k, 𝔽₂)` *defined on isometry
classes* of nondegenerate binary quadratic forms over `k`:

* degree 1: `w₁(Tr⟨a⟩) = w₁(Tr⟨1⟩) + cor[a]`;
* degree 2: `w₂(Tr⟨a⟩) = w₂(Tr⟨1⟩) + w₁(Tr⟨1⟩) ⌣[htriv] cor[a] + N^{Ev}[a]`.

Citation match: Kahn, Invent. Math. 78 (1984), Théorème 2 at the rank-1 form `⟨a⟩`, expanded via
Evens Thm 1 / Kozlowski Thm 1.1 at index 2 — now checkable against the source *without* the
Lemma 6.16 diagonalization scoping.  Deviations that remain (unchanged, flagged): degrees ≤ 2
truncation; `N^{Ev}` *defined* by the two-point cocycle (98) (Lemma 6.13 identification);
dyadic base.

## Why this discharges the old B9

Old B9 is the new axiom evaluated at `a = u + vδ` (`u, n, d` units, `n = u² − dv²`), rewritten
through two *provable* inputs:

* `Tr_{L/k}⟨a⟩ ≃ ⟨2u, 2dn/u⟩` and `Tr_{L/k}⟨1⟩ ≃ ⟨2, 2d⟩` (Lemma 6.16's diagonalizations —
  basis `{1, δ}`, Gram `(2u, 2vd; 2vd, 2ud)`, complete the square using `u ∈ kˣ`);
* `w₁⟨x,y⟩ = [x] + [y]`, `w₂⟨x,y⟩ = [x] ⌣ [y]` (evaluation of the well-defined invariants at a
  diagonalization).

## Node decomposition

* **N1 (defs, new file `GQ2/StiefelWhitney.lean`).**  Binary quadratic forms over `F := ↥k`:
  default design is mathlib `QuadraticForm F V` on 2-dimensional `V` with
  `QuadraticMap.Equivalent`; diagonal models via `weightedSumSquares`.  `swOne q`, `swTwo q`
  defined by `Classical.choice` of a diagonalization (nondegenerate ⇒ diagonal entries are
  units), values `[x] + [y]` and `kummerClassK k x ⌣[htriv] kummerClassK k y`.  Fallback design
  if `QuadraticForm` plumbing fights the `IntermediateField` types: a light structure of
  diagonal representatives with an explicit equivalence relation — T1 decides and records why.
* **N2 (Delzant invariance, the hard node).**  `q ≃ q'` nondegenerate binary ⇒ `swOne q = swOne
  q'` and `swTwo q = swTwo q'`.  Degree 1 is discriminant invariance (change-of-basis determinant
  squares).  Degree 2 is the classical binary Hasse-invariant well-definedness: representation
  lemma (an isometry `⟨x,y⟩ ≃ ⟨x',y'⟩` exhibits `x' = x a² + y b²`), chain equivalence
  `⟨x,y⟩ ≃ ⟨x', x' x y⟩`, then cup identities.  **Relation inputs come from B11a** (the norm
  criterion; Steinberg-type identities `[t] ⌣ [1−t] = 0`, `[t] ⌣ [t] = [t] ⌣ [−1]` are its
  consequences, as the §B11 header notes).  Consequence to record: the flipped
  `evensKahn_dyadic` (and its §6 consumers) will list **both** the new axiom and B11a in their
  `#print axioms` — App. D rows in `docs/literature-axioms.md` §C must be updated (T6).
* **N3 (trace forms, new file `GQ2/TraceForm.lean`).**  `L = adjoin ↥k {δ}` with
  `¬IsSquare (d : ↥k)` ⇒ `finrank ↥k ↥L = 2`, basis `{1, δ}` (bridge from the current
  subgroup-level `hidx` hypothesis via `GQ2/KummerKrullBridge.lean`, the B12-flip machinery);
  the `a`-twisted trace form `q_a(z) = Tr_{L/k}(a z²)`; the two diagonalizations above.
* **N4 (glue algebra).**  Truncated total-class product ↔ componentwise statement; cup
  bilinearity and char-2 commutativity (`GQ2/CupSymmetry.lean`, `HilbertLedger`
  `trivialCupPairing_comm`).  Small; folds into T5 if trivial.
* **N5 (the flip, gated).**  Move the new axiom into `GQ2/Foundations/Axioms.lean`; turn
  `evensKahn_dyadic` into a `theorem` with byte-identical statement proved from N1–N4; update in
  the same commit: `AxiomLedger.bAxioms` (B9 ↦ new name), `scripts/check_axioms.sh`
  `EXPECTED_AXIOMS`, `formalization.yaml` axiom list, `docs/literature-axioms.md` §B9 + §C rows.
  **Gate: owner sign-off on the exact axiom statement before this node runs.**

## Verification and conventions

* Branch `b9a`, worktree `~/claude/gq2-b9a` (keeps `master` green and the census gate clean —
  the new axiom may not appear on `master` except atomically with the flip in N5).
* Workers: no Lean LSP MCP in the worktree (it is bound to the main checkout) — use
  `lake env lean GQ2/<File>.lean` from the worktree root as the file gate and `lake build` as the
  project gate; `lean_leansearch`/`lean_loogle` (remote services) remain available for search.
* First-time setup in the worktree: `lake exe cache get` then `lake build` (GQ2's own oleans
  rebuild once; mathlib comes from the shared cache).
* `sorry` allowed on the branch between tickets, never at N5; no new `axiom` outside
  `Foundations/Axioms.lean` at any point (`scripts/check_axioms.sh` discipline).
* Statements of existing declarations are frozen (byte-identical `evensKahn_dyadic`); new names
  follow mathlib conventions; 100-char lines.
* Commit after every green ticket (swarm-volatility rule).

## Risks / fallbacks

* **R1 — N2 size.**  Binary-only Delzant is contained, but if the chain-equivalence route
  balloons: fallback A = state the axiom with `swOne/swTwo` *on diagonalizations* plus an
  explicit well-definedness **clause inside the axiom** (still strictly better than today —
  the diagonalization scoping becomes hypothesis-free); fallback B = keep old B9 and record
  B9-A as attempted with the blocker documented.
* **R2 — `hidx` ↔ field-degree bridge friction.**  Mitigation: `KummerKrullBridge` already
  crosses this gap (B12 flip); T2 starts by inventorying its lemmas.
* **R3 — statement churn.**  Mitigated by the N5 owner gate; T1's deliverable includes the
  axiom statement *as Lean source that elaborates*, so review is of a compiling artifact.
* **R4 — B11a dependence of the flip** (see N2).  If the owner prefers the flipped B9 to stay
  independent of B11a, fallback: add the two needed cup relations as explicit hypotheses of the
  new axiom (they are literature facts over any field, Serre CiA III §1.2) — decide at the N5
  gate.
