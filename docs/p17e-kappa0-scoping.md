# P-17e scoping — `kappa0_exists` is Lemma 6.3, not Lemma 6.1 (escalation → RESOLVED)

**Status: RESOLVED (F-review, Fable 2026-07-06).**  The escalation was reviewed and the
statement **amended** (Option A′ below): `kappa0_exists` now carries the paper's own Lemma 6.3
hypotheses — `hsimple : FoxH.IsSimpleModTwo C V` and `htame : ActsThroughTame C V` — making it a
true paper theorem, dischargeable at the sole call site (P-17d), with the `sorry` guarding
honest future work (sub-obligations P-17e1–e3 below).  The original general form is **false**,
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
`V` is an equivariant summand of a free permutation module `W`, `q` extends to `q_W = q ∘ p`,
and invariant forms on permutation modules have explicit orbit data — no `H²` obstruction
survives the pullback (77).

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
| `IsEquivariantFactorSet.comapHom` | **pullback along a group hom** `π : C →* D` with `c • v = π c • v` (`m_c := m_{π c}`) — reduction to the faithful tame image | "let `H = H_V` be the faithful tame image" |
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
* **Provable by the paper's route**, staged as P-17e1–e3 below, with the reduction/assembly
  layer already proved (previous section).
* Datum-*choice* independence downstream is already covered by `RepIndependence.repIndep`
  (Lemma 6.4), so an ∃-statement is the right strength.

## Remaining obligations (the staged proof of the amended `kappa0_exists`)

0. **Faithful-image reduction** — pass along `htame`'s `π` via `IsEquivariantFactorSet.comapHom`
   (✓ proved), then quotient `H` by the action kernel (tame-generation and `q`-invariance
   survive; simplicity transports by surjectivity).  Routine; part of e1.
1. **P-17e1 — split embedding** `i : V →+ 𝔽₂[H_V]^N` equivariant with retraction: *unramified*
   branch (`t̄` acts trivially ⟹ `H_V` cyclic ⟹ **odd**, via the central-involution argument
   already packaged in `TameSimple.central_pow2_smul_trivial`; then Maschke).  *Ramified*
   branch = **Lemma 6.11** (projectivity of simple ramified tame modules; `H_V` has cyclic
   Sylow-2) — the long pole.  Note: an alternative closes the *unramified* branch without any
   embedding: for odd `H_V`, split `1 → V^∨ → E' → H_V → 1` directly by Schur–Zassenhaus
   (`Subgroup.exists_right_complement'_of_coprime`, already used at P-17b1) and read `m` off the
   complement; worth doing first as it may cover a large share of the induction's blocks.
2. **P-17e2 — orbit data**: `squareOrbitDatum`/`freeOrbitDatum` are `IsEquivariantFactorSet`
   for their square maps — reduce via `isEquivariantFactorSet_of_biadditive_invariant` (✓) to
   biadditivity + invariance of `∑ᶠ h, x h * y h` (finsum reindex along `Equiv.mulLeft`,
   `finsum_add_distrib`).  **P-17e2′**: the involution datum `invOrbitDatum` with its explicit
   nonzero `m` (**Lemma 6.2**, orientation bookkeeping — genuinely involved; note
   `lemma_6_15`'s (105) already exercises this datum downstream).
3. **P-17e3 — algebraic normal form**: an `H`-invariant quadratic map on `𝔽₂[H]^N` is a sum of
   orbit polynomials `S_j`/`C_{j,k,g}`/`E_{j,g}` (coefficients constant on orbits of unordered
   degree-2 coordinate monomials; free coordinate action ⟹ pair-stabilizers trivial or
   order-2-swap).  The analytic heart; combine with e2 via `IsEquivariantFactorSet.add` and
   close through `kappa0_exists_of_split`.
