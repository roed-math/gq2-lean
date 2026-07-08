# P-17e scoping — `kappa0_exists` is Lemma 6.3, not Lemma 6.1 (escalation → RESOLVED)

**Status: RESOLVED (F-review, Fable 2026-07-06).**  The escalation was reviewed and the
statement **amended** (Option A′ below): `kappa0_exists` now carries the paper's own Lemma 6.3
hypotheses — `hsimple : FoxH.IsSimpleModTwo C V` and `htame : ActsThroughTame C V` — making it a
true paper theorem, dischargeable at the sole call site (P-17d), with the `sorry` guarding
honest future work (sub-obligations P-17e1–e5 below).  The original general form is **false**,
not merely unproved: see the sharpened verdict below (Griess 1973).  History: escalated by Opus
2026-07-06 (finding + reusable core, no unilateral interface change); resolved same day on
user instruction after F-escalation.

## The statements

**Original (P-17a; now amended)** — *"every invariant nonsingular quadratic form on an
arbitrary finite `𝔽₂[C]`-module admits an equivariant factor-set datum"*:

```lean
theorem kappa0_exists … (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q) : ∃ dat : FactorSet C V, IsEquivariantFactorSet q dat
```

**Amended (current, = paper Lemma 6.3)** — adds the two paper hypotheses:

```lean
def ActsThroughTame (C : Type*) [Group C] (V : Type*) [AddCommGroup V]
    [DistribMulAction C V] : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (_ : DistribMulAction H V)
    (π : C →* H) (s t : H),
    Function.Surjective π ∧ (∀ (c : C) (v : V), c • v = π c • v) ∧
    Subgroup.closure {s, t} = ⊤ ∧ s⁻¹ * t * s = t ^ 2

theorem kappa0_exists … (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q) (hsimple : FoxH.IsSimpleModTwo C V)
    (htame : ActsThroughTame C V) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet q dat
```

Notes on the amended shape: self-duality needs no separate hypothesis (`hns` + `hinv` make
`v ↦ polar q v ·` a `C`-iso `V ≅ V^∨`); "nontrivial" is inside `IsSimpleModTwo` (`Nontrivial V`);
"`q` nonzero" is automatic (`q = 0` kills `Nonsingular` on a nontrivial `V`); `ActsThroughTame`
mirrors `tame_two_nilpotent`'s `(hgen, hrel)` interface — the finite avatar of a tame quotient —
and its `π`-surjectivity is what transports `hinv`/`hsimple` to the group the proof works over.

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

## Why the general statement is false (sharpened at F-review)

The datum is *equivalent data* to a lifted action — Lemma 6.1's own proof.  Precisely, given
`(f, m)` with `IsEquivariantFactorSet q`, set `α_c (v, z) := (c • v, z + m_c v)` on
`E_f = V × 𝔽₂` with multiplication `(v,z)(w,t) = (v+w, z+t+f(v,w))`:

* (59) `⟺` each `α_c ∈ Aut(E_f)` (and `m_c 0 = 0` follows from (59) at `v = w = 0`);
* (60)+`m_1 = 0` `⟺` `c ↦ α_c` is a homomorphism;
* each `α_c` fixes the centre `{0} × 𝔽₂` pointwise and induces `c` on `V = E_f/Z`.

For `q` nonsingular of rank `2n`, `E_f` is extraspecial of order `2^{1+2n}` (type ± per Arf),
`Z(E_f) = 𝔽₂` (nonsingularity), squaring map = `q`, commutator = `B`.  Since `Z ≅ ℤ/2` every
automorphism fixes the centre pointwise and preserves squaring, giving the classical exact
sequence

```
1 → V^∨ → Aut(E_f) → O(q) → 1        (kernel: (v,z) ↦ (v, z + λ v), λ ∈ Hom(V, 𝔽₂))
```

so a datum for `(C, ρ, q)` = a homomorphic lift `C → Aut(E_f)` of `ρ : C → O(q)`.  **Take
`C := O(q)` with the tautological action** (finite ✓, `q` invariant by definition ✓): a datum is
then literally a splitting of the sequence — and **Griess** (*Automorphisms of extra special
groups and nonvanishing degree 2 cohomology*, Pacific J. Math. **48** (1973) 403–422) proved
this extension is **non-split** (equivalently `H²(O^ε_{2n}(2), V) ≠ 0`, `V ≅ V^∨` the natural
module) for all sufficiently large `n` — already in single digits; small ranks (`D₈`, `Q₈`,
`n = 1, 2`) do split, which is why no tiny counterexample exists.  So the unamended
`kappa0_exists` is refuted by a classical theorem, not merely unproved.  (Consistency check:
`O^ε_{2n}(2)` is far from metacyclic — no conflict with the tame case.)

The projectivity/tameness hypothesis is exactly what removes the obstruction: `V` projective ⟹
`iV` is an equivariant summand of a free permutation module `W`, `q` extends to the invariant
`q_W = q ∘ p`, and every invariant form on a permutation module has an `m = 0` (or
Lemma-6.2-explicit) factor set — no `H²` obstruction survives the pullback (77).

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
| `IsEquivariantFactorSet.comapHom` | **pullback along a group hom** `π : C →* D` with `c • v = π c • v` (`m_c := m_{π c}`) — reduction to the faithful tame image | "let `H = H_V` be the faithful tame image" |
| `kappa0_exists_of_split` | split embedding + known `datW` for `q_W` with `q_W∘i = q` ⟹ datum for `q` | Lemma 6.3 reduction |
| `exists_biadditive_refinement` | a char-2 `IsQuadraticFp2` form is the diagonal of a biadditive `f` (via Mathlib `QuadraticMap.toBilin`) | upper-triangular companion |
| **`kappa0_exists_of_odd`** | **`Odd \|H\|` ⟹ datum exists** (`m=0`), by averaging `f₀` over `H` — the entire unramified case | Lemma 6.3, odd/unramified branch |

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

## Resolution (Option A′, executed at F-review)

Neither pure Option A (make `kappa0_exists_of_split` *the* statement — pushes Lemma 6.11's
projectivity plus the whole orbit/normal-form machine onto the consumer P-17d) nor Option C
(leave the false statement sorried) was taken.  The executed **Option A′**: keep `kappa0_exists`
as the named interface, with **the paper's own Lemma 6.3 hypotheses** added — `hsimple`
(existing `FoxH.IsSimpleModTwo`) and `htame` (new `ActsThroughTame`, mirroring
`tame_two_nilpotent`'s `(hgen, hrel)` finite-tame interface).  Rationale:

* **True**: it is now literally Lemma 6.3 (+ the trivial reductions recorded in the docstring),
  so the `sorry` guards honest work rather than a falsehood.
* **Dischargeable at the sole call site** (P-17d, `Vmod = P/S`, `C = Y/K`):
  - `hsimple` ⟸ `MinimalBlock.chief` + `nontrivial_action` (Y-normal chiefness → `C`-stable
    `AddSubgroup` dictionary; `C`-stable = `Y`-invariant since the action is induced
    conjugation).
  - `htame` with `H :=` the frame head: `K` acts trivially by `[K,P] ≤ [P,P] ≤ S` (P-17d's
    existing `Vmod` descent), and the rest of `L_Y` acts trivially by the **already-proved**
    `FoxH.lemma_5_12` (normal 2-subgroup acts trivially on a simple char-2 module), so the
    action descends along `Y/K ↠ Y/L_Y ≅ H`; generators = marked images (`gen_ttame_quotient`
    ✓ + `tame_relation` ✓), surjectivity from the frame.
* **Provable by the paper's route**, staged as P-17e1–e5 below, with the reduction/assembly
  layer already proved (previous section).
* Datum-*choice* independence downstream is already covered by `RepIndependence.repIndep`
  (Lemma 6.4), so an ∃-statement is the right strength.

## Remaining obligations (the staged proof of the amended `kappa0_exists`)

0. **Faithful-image reduction** — pass along `htame`'s `π` via `IsEquivariantFactorSet.comapHom`
   (✓ proved), then quotient `H` by the action kernel (tame-generation and `q`-invariance
   survive; simplicity transports by surjectivity).  Routine; part of e1.
1. **P-17e1 — split embedding.**  ✅ **UNRAMIFIED BRANCH DONE** (`kappa0_exists_of_odd`, std-3):
   the odd case needs *no embedding, Maschke, orbit data, or Schur–Zassenhaus on an extension
   group* — just **average the bilinear form**.  Given any refinement `f₀` of `q`
   (`exists_biadditive_refinement`, itself a short wrap of Mathlib's `QuadraticMap.toBilin`),
   `f(v,w) := ∑_{h∈H} f₀(h•v, h•w)` is `H`-invariant (reindex `h ↦ h·g`) and biadditive, with
   diagonal `∑_h q(h•v) = |H|·q(v) = q(v)` because `|H|` is odd (`= 1` in `𝔽₂`); `m = 0`.  This is
   the vanishing of `H²(odd, 2-torsion)` in elementary averaged-cochain form, and it is *cleaner*
   than the originally-planned SZ/Maschke route.  **Remaining = the ramified branch (P-17e4):**
   `H_V` has a nontrivial 2-part, averaging fails, and one needs the split embedding
   `V ↪ 𝔽₂[H_V]^N` via **Lemma 6.11** (projectivity of simple ramified tame modules, cyclic
   Sylow-2) — the long pole, feeding `kappa0_exists_of_split` with the orbit data below.
2. **P-17e2 — orbit data**: `squareOrbitDatum`/`freeOrbitDatum` are `IsEquivariantFactorSet`
   for their square maps — reduce via `isEquivariantFactorSet_of_biadditive_invariant` (✓) to
   biadditivity + invariance of `∑ᶠ h, x h * y h` (finsum reindex along `Equiv.mulLeft`,
   `finsum_add_distrib`).  **P-17e3**: the involution datum `invOrbitDatum` with its explicit
   nonzero `m` (**Lemma 6.2**, orientation bookkeeping — genuinely involved; note
   `lemma_6_15`'s (105) already exercises this datum downstream).
3. **P-17e4 (ramified split, Lemma 6.11) + P-17e5 (algebraic normal form + final assembly)**: the
   split embedding `V ↪ 𝔽₂[H_V]^N` (projectivity, the long pole), then that an `H`-invariant
   quadratic map on `𝔽₂[H]^N` is a sum of
   orbit polynomials `S_j`/`C_{j,k,g}`/`E_{j,g}` (coefficients constant on orbits of unordered
   degree-2 coordinate monomials; free coordinate action ⟹ pair-stabilizers trivial or
   order-2-swap).  The analytic heart; combine with e2 via `IsEquivariantFactorSet.add` and
   close through `kappa0_exists_of_split`.

## Addendum (2026-07-06, Fable): P-17e4 reduced to a counting inequality

The Lemma 6.11 kernel is now two pieces in `GQ2/RegularSummand.lean`:

1. **`free_of_card_fixedPoints_pow_le` (PROVED, std-3, Ax ∅)** — the counting criterion:
   over a cyclic 2-group `P`, a finite 2-torsion module with `#V^P ^ |P| ≤ #V` is
   equivariantly isomorphic to a regular module.  Fully constructive (explicit
   geometric-series inverse of the convolution `T = 1 + nilpotent`; one free block splits
   per step; induction on `#V`).  This replaces the paper's two Lean-hostile endgame steps
   (regular basis over an algebraic closure; faithfully-flat projectivity descent).
2. **`card_fixedPoints_pow_le_of_ramified` (the SOLE remaining sorry)** — the bound
   `#V^P ^ |P| ≤ #V` on a ramified simple faithful module.  F2-rational discharge plan
   (recorded deviation from the paper's F2bar weight-line argument): the group algebra of
   the odd inertia is etale, so `V` decomposes along factor fields; simplicity forces a
   single orbit of factors and faithfulness (cyclic inertia: subgroups characteristic)
   forces them faithful; a Sylow-element stabilizing a factor acts semilinearly through a
   **nontrivial** Frobenius power — else it centralizes the inertia, its normal closure is
   abelian with nontrivial O_2, and `FoxH.lemma_5_12` contradicts faithfulness; finite-field
   semilinear fixed points descend (additive Hilbert 90 / normal basis), giving
   `dim V^P = dim V / |P|` exactly.  Inputs needed from scratch: primitive idempotents of
   `F2[C_m]` (m odd) and the semilinear descent dimension count — finite-field linear
   algebra, no Clifford induction, no base change.

## Addendum 2 (2026-07-06, Opus): counting bound reduced to the involution

`GQ2/RegularSummand.lean` now proves `card_fixedPoints_pow_le_of_ramified` from a **strictly
smaller** leaf.  Landed std-3 (Ax empty), all constructive:

1. **`finrank_ker_pow_succ` / `finrank_ker_pow_concave`** — the Jordan-increment sequence
   `b k = dim ker ν^k` is concave (`b(k+2)+b(k) ≤ 2 b(k+1)`).  Proof: the increment equals
   `dim(im ν^k ⊓ ker ν)` (rank-nullity for `ν^k : ker ν^{k+1} → im ν^k ⊓ ker ν`), which is
   antitone by `finrank_mono` on `im ν^{k+1} ≤ im ν^k`.
2. **`seq_double_le` / `seq_first_increment_le`** — two `ℕ`-sequence lemmas: concavity gives
   the automatic `b(2m) ≤ 2 b m`; and IF `2 b m = b(2m)` then all increments are equal, so
   `2m·b 1 = b(2m)` (equal antitone `m`-sums are termwise equal, then a squeeze flattens the
   first block).
3. **`card_fixedPoints_pow_le_of_half`** — the elementary-abelian reduction (the `p=2`
   Chouinard reduction to the order-2 subgroup): given `#V^ω ^ 2 ≤ #V` for the involution
   `ω = g₀^{2^{s-1}}`, the full `#V^P ^ |P| ≤ #V` follows.  Wires the numerics to
   `b k = dim ker(nuOp g₀)^k` via card↔finrank (`Module.card_eq_pow_finrank`, `ZMod.card`),
   `b(2^s) = dim V`, and the freshman `nuOp(g₀^{2^t}) = (nuOp g₀)^{2^t}`.

**Remaining leaf: `involution_fixedPoints_sq_le`** — `#V^ω ^ 2 ≤ #V` for a single involution
on the ramified simple faithful module.  This is the involution (order-2) case only, so the
descent is quadratic: additive Hilbert 90 for the degree-2 semilinear action, rather than the
full weight-orbit analysis over a cyclic 2-group.  The rep-theoretic core (why `ω` acts
freely: étale odd inertia + single faithful orbit + the O2-linchpin via `FoxH.lemma_5_12`)
is unchanged, but the linear-algebra endgame is now the simplest possible case.
