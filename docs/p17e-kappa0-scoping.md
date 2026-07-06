# P-17e scoping — `kappa0_exists` is Lemma 6.3, not Lemma 6.1 (escalation)

**Status:** the general statement of `SectionNine.kappa0_exists` currently on the board is **not
a paper theorem** and is very likely **false** as stated.  This note records the finding, the
honest interface, the reusable core that *is* proved (std-3, Ax ∅), and the remaining
obligations.  Flagged per the ticket's standing instruction *"escalate rather than weaken
`IsEquivariantFactorSet`."*  Author: Opus, 2026-07-06 (autonomous; user asleep — no interface
change made unilaterally, only additive proved lemmas + this note + a board flag).

## The current statement

```lean
theorem kappa0_exists {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet q dat
```

i.e. *"every invariant nonsingular quadratic form on an arbitrary finite `𝔽₂[C]`-module admits an
equivariant factor-set datum."*

## Why this is not what the paper proves

Read the paper (pp. 25–26) carefully:

* **Lemma 6.1** ("Equivariant extraspecial connecting cocycle") does **not construct** the
  correction family `m`.  Its entire proof is the *equivalence*
  > eq. (59) ⟺ `(v,z) ↦ (cv, z + m_c(v))` preserves multiplication in `E_f`;
  > eq. (60) ⟺ these automorphisms form a genuine `C`-action.

  It opens with *"**When** an equivariant lift is chosen, its action … is written by functions
  `m_c` …"* — existence of the lift is **assumed**, and the paper even warns one line earlier
  (p. 25): *"A `C`-invariant quadratic form on `V` does **not in general** admit a `C`-invariant
  factor set … the central correction terms … are part of the data."*

* **Existence** is **Lemma 6.3** ("Base equivariant determinant class"), whose hypotheses are
  strictly stronger than the Lean statement:
  > Let `V` be a **nontrivial simple self-dual tame** `𝔽₂[C]`-module, `H = H_V` its faithful
  > tame image, `q` a nonzero `H`-invariant nonsingular quadratic form.

  and whose proof is a concrete construction, **not** a general lift argument:
  1. choose an **`H`-split** pair `V ⟶i W = 𝔽₂[H]^N ⟶p V`, `p∘i = 1` (exists because `V` is
     **projective**: ramified ⟹ projective by Lemma 6.11; unramified ⟹ `H` odd ⟹ Maschke);
  2. `q_W := q∘p` on the permutation module `W` has an **algebraic normal form** = a sum of
     *orbit polynomials* `S_j` (square), `C_{j,k,g}` (free), `E_{j,g}` (involution);
  3. each orbit polynomial has an explicit **invariant** factor set — squares (75) and frees
     (76) with `m = 0`, involutions via Lemma 6.2's cocycle (73) with explicit `m`;
  4. sum them → `κ⁰_{q_W}`; pull back `κ⁰_q := (i⋊1)^* κ⁰_{q_W}` (eq. (77)).

## Why the general statement is (essentially certainly) false

The datum `(f, m)` for `q` is exactly a `C`-action on the extraspecial-type 2-group
`E_f = 𝔽₂ ×_f V` lifting the `C`-action on `V` and fixing the centre `𝔽₂`
(Lemma 6.1's own equivalence).  Equivalently, a lift of `ρ : C → O(q)` through
`1 → V^∨ → Aut_ctr(E_f) → O(q) → 1` (with `V^∨ ≅ V` via the nonsingular `B`).  The obstruction
lives in `H²(C, V^∨)`, which for a general finite 2-group `C` and nontrivial module `V^∨` is
**nonzero** (there is no averaging/transfer vanishing: `|C|` is a power of 2 and `V^∨` is
2-torsion).  The `Aut_ctr(E_f) → O(q)` extension is the classical spin/theta extension, famously
**non-split** for larger extraspecial groups.  So a general lift need not exist.

The projectivity hypothesis is exactly what removes the obstruction: `V` projective ⟹ `iV` is a
`C`-summand of a permutation module `W`, `q` extends to the invariant `q_W`, and every invariant
form on a permutation module has an `m = 0` (or Lemma-6.2-explicit) factor set — no `H²`
obstruction because the orbit factor sets are literally invariant.

**Sanity anchor for the consumer.**  P-17d (`blockEnrichment`) only ever calls `kappa0_exists`
at `V = Vmod = Additive(P/S)` — the block chief factor, which the `MinimalBlock`/`prop_7_4`
machinery guarantees is **simple self-dual** (and tame, as a 2-group chief factor of the tame
frame).  So the honest hypotheses are available at the call site; the general statement is
broader than any consumer needs.

## What is proved now (std-3, Ax ∅, in `GQ2/SectionNine.lean`)

The three structural moves of Lemma 6.3 — each source-generic and unconditionally true — plus
the reduction that assembles them:

| lemma | content | paper |
|---|---|---|
| `isEquivariantFactorSet_of_invariant` | an **invariant** normalized factor set has `m = 0` | (75)/(76) |
| `isEquivariantFactorSet_of_biadditive_invariant` | **biadditive + invariant** ⟹ `m = 0` (cocycle + normalization automatic) — the entry point for the concrete orbit data | (75)/(76) |
| `IsEquivariantFactorSet.add` | datum of `q + q'` = pointwise sum of data | "sum of the orbit cocycles" |
| `IsEquivariantFactorSet.comap` | **pullback** along an equivariant `i : V →+ W` | eq. (77) |
| `kappa0_exists_of_split` | split embedding + known `datW` for `q_W` with `q_W∘i = q` ⟹ datum for `q` | Lemma 6.3 reduction |

`kappa0_exists_of_split` is the **honest, true, closeable** form of the reduction:

```lean
theorem kappa0_exists_of_split {C V W} [Group C] [AddCommGroup V] [AddCommGroup W]
    [DistribMulAction C V] [DistribMulAction C W] {q : V → ZMod 2} {qW : W → ZMod 2}
    (datW : FactorSet C W) (hdatW : IsEquivariantFactorSet qW datW)
    (i : V →+ W) (hi : ∀ c v, i (c • v) = c • i v) (hq : ∀ v, qW (i v) = q v) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet q dat
```

(Namespacing note: these live in `namespace GQ2.SectionNine`, so the `.add`/`.comap` dot-notation
does **not** fire on a bare `IsEquivariantFactorSet` term — call them explicitly, e.g.
`SectionNine.IsEquivariantFactorSet.comap hdatW i hi`.  If they are promoted to a dedicated
`GQ2/FactorSetLemmas.lean` (namespace `GQ2`, importing only `OrbitData`) the dot-notation would
fire; deferred to avoid churn on the shared low-DAG files during the parallel §9 push.)

## Remaining obligations (to close the honest `kappa0_exists`)

Everything left is exactly Lemma 6.3's inputs to `kappa0_exists_of_split`:

1. **Split embedding** `i : V →+ 𝔽₂[H]^N`, `hi` equivariant, with `q_W := q∘p` — needs `V`
   projective (Lemma 6.11, ramified) or `H` odd + Maschke (unramified).  **Sub-ticket
   material** (call it P-17e1): produce the `H`-split pair for a simple self-dual tame module.
2. **Orbit-cocycle data on `W`** — that the concrete `squareOrbitDatum`/`freeOrbitDatum`
   (already defined in `OrbitData.lean`, `m = 0`) are `IsEquivariantFactorSet` for their square
   maps, and that `invOrbitDatum` is one with its explicit `m` (**Lemma 6.2** — the
   orientation-bookkeeping cocycle, genuinely involved).  **Entry point landed:**
   `isEquivariantFactorSet_of_biadditive_invariant` reduces the square/free cases to
   *biadditivity + permutation-invariance* of `∑ᶠ h, x h * y h` (resp. the shifted free form) —
   a short `finsum_add_distrib`/`finsum_comp_equiv` (via `Equiv.mulLeft`) computation, deferred
   as **sub-ticket P-17e2** so this note stays a clean checkpoint (the finsum plumbing for
   `hpolar`/`HasFiniteSupport` is straightforward but not worth blocking the escalation on).
   The involution datum (Lemma 6.2, nonzero `m`) is the harder **P-17e2′**.
3. **Algebraic normal form** — that an `H`-invariant quadratic map on `𝔽₂[H]^N` equals a sum of
   `S_j`/`C_{j,k,g}`/`E_{j,g}` (paper: "determined by its values on the coordinate vectors and
   its polar form; invariance makes coefficients constant on orbits of degree-two monomials").
   The classification that stabilizers of unordered coordinate pairs are trivial or order-two
   (free action ⟹ the `E_{j,g}` case).  **Sub-ticket P-17e3**, the analytic heart.

## Recommendation for the user (decision needed)

**Option A (preferred): restate `kappa0_exists`** to take the split datum as hypotheses — i.e.
make `kappa0_exists_of_split` *the* statement, and push obligations (1)–(3) into P-17d's call
site / new sub-tickets P-17e1–e3.  This is honest, already half-proved (the reduction is done),
and matches the paper's actual Lemma 6.1-vs-6.3 split.  P-17d supplies `W, datW, i` from the
block structure (`prop_7_4` already produces the self-dual simple `Vmod`).

**Option B: keep the general statement** and prove obligations (1)–(3) in full generality —
**do not do this**: it is false without projectivity; it would require assuming an axiom.

**Option C: keep the general `sorry` for now**, land the reusable core + this note (current
state), and let P-17d/P-17i decide the interface when they wire the block module in.  This is
what has been done tonight; `kappa0_exists` remains sorried with a docstring pointer here.

No unilateral restatement was made because `kappa0_exists` is a shared interface consumed by the
in-flight P-17d, and the batch owner should choose A-vs-C.
