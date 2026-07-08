# P-15i design-gap resolution — the dropped `κ⁰_q` hypothesis of Lemma 6.21

**Date**: 2026-07-04 · **Author**: Fable (design pass over the Opus gap report in
`docs/section67-extraction.md` §"P-15i status" and the board row).  Status: **IMPLEMENTED &
CLOSED (2026-07-04, user-approved amendments)** — R1–R6 all landed; `lemma_6_21` proved &
spliced (std-3, no B-axioms); `GQ2/Transgression.lean` sorry-free, removed from
`SORRY_ALLOWLIST`; deviation note 3 in `docs/section67-extraction.md` amended.  The plan below
is kept as the design record.

## 1. Assessment: the gap is real, and it is a *statement-extraction* gap

The Opus finding is confirmed (defect formula re-derived by hand, §4): `mixedA c` is not
additive in `v`, and **no fibre-local repair can work** — choosing pointwise primitives for the
defect `D_c` leaves a coherence obstruction which is again exactly `[B_q^♭ f] ∈ H²(C, V^∨)`.
The vanishing of that class is the genuine content, and it is **not derivable from the current
hypotheses** of `Transgression.splitting_of_global_cocycle` / `SectionSix.lemma_6_21`.

Root cause: the paper's Lemma 6.21 is stated **"relative to the fixed equivariant class"**:

> *Let `q` be a nonsingular `C`-invariant quadratic form on `V`, **and assume that a
> zero-section-normalized equivariant class `κ⁰_q ∈ H²(V ⋊ C, 𝔽₂)` restricting to `q` on `V`
> has been fixed**.*  [paper, Lemma 6.21; its proof uses `κ⁰_q` to produce the coherent
> automorphisms `α_c ∈ Aut(E_q)`, `α_c α_d = α_{cd}`.]

The extraction to "consequence form" (deviation note 3 in `docs/section67-extraction.md`)
kept the conclusion but **dropped this hypothesis**.  Without it the statement asserts the
splitting for *every* `(B, ξ)`, which the paper's mechanism cannot prove: `κ⁰_q` is what
trivializes the *intrinsic equivariance obstruction* `o(q, ρ) ∈ H²(C, V^∨)` (the obstruction to
lifting the `C`-action on `V` coherently to the `q`-extraspecial cover `E_q`).  A global `ξ`
forces `[B_q^♭ f] = o(q, ρ)` — it does **not** force either to vanish.  (Whether the
unconditional statement is actually false requires realizing a nonzero `o` by a pair `(B, ξ)`
— an Eilenberg–MacLane 3-obstruction construction we do not need to settle: faithfulness to
the paper requires the hypothesis regardless.)

## 2. The good news: the repo already has `κ⁰_q` — it is Lemma 6.1's `IsEquivariantFactorSet`

`GQ2/OrbitData.lean` packages the paper's eqs. (59)–(61) as `FactorSet C V` (`f`, `m`) with
`IsEquivariantFactorSet q dat`:

* `m_quad` (eq. 59): `m_c(v+w) + m_c(v) + m_c(w) = f(c•v, c•w) + f(v, w)`
* `m_mul` (eq. 60): `m_{cd}(v) = m_c(d•v) + m_d(v)`, `m_one`
* `f_cocycle`, `f_diag : f(v,v) = q v`, `f_polar`, `f_zero_*`

and `lemma_6_22` already consumes `κ⁰_q` in exactly this form (`kappa0 dat`).  **The `m`-family
is precisely the coherent automorphism data `α_c` of the paper's proof**, in cochain avatar: an
automorphism of the central extension `𝔽₂ ×_f V` fixing the center and lifting `c•` is exactly
a function `m_c : V → 𝔽₂` with the `m_quad` defect (automorphism condition), and
`α_c α_d = α_{cd}` is exactly `m_mul`.  No new vocabulary is needed; the fix is to *thread the
existing vocabulary into 6.21*, matching how 6.22 already takes it.

Two derivability notes (so no further hypotheses are needed):
* `q` `C`-invariance (the paper's other stated hypothesis) is forced: `m_quad` at `(c, v, v)`
  plus `m_c(0) = 0` (from `m_quad` at `(c,0,0)`) gives `q(c•v) = q(v)`.
* `t_c(0) = 0` is likewise forced by the defect identity at `(0,0)`.

## 3. The remedy — proof mechanism (paper's proof, cochain-level, no new groups)

Work in `GQ2/Transgression.lean`'s notation; `R(v,w) := ξ(iv, iw)` (fibre restriction).  The
paper's `E`/`E_q`/`Aut` story is encoded entirely by cochain bookkeeping:

1. **`mixedA_defect`** (new lemma; confirms the Opus formula by 3 `hcocycle` instances on
   `(σc, i(c⁻¹v), i(c⁻¹w))`, `(iv, σc, i(c⁻¹w))`, `(iv, iw, σc)` + the `hconj` move
   `σc·i(c⁻¹v) = iv·σc`, then `linear_combination`):

   `mixedA c (v+w) + mixedA c v + mixedA c w = R(c⁻¹•v, c⁻¹•w) + R(v, w)`.

2. **Transport `m` to `ξ`'s fibre model** (`θ`-bridge).  `hdat`'s `f` and `R` are both
   2-cocycles on `V` with diagonal `q` (`f_diag` / `hξq`), so `S := f + R` is a *symmetric*
   (`f_polar` + `polar_fibre`) *zero-diagonal* 2-cocycle, hence a coboundary: `S = δθ`,
   `θ(0) = 0` — see §3a.  Then `t c v := m c v + θ(c•v) + θ(v)` satisfies the same two
   identities **with `R` in place of `f`**:
   * (i) `t c (v+w) + t c v + t c w = R(c•v, c•w) + R(v, w)`
   * (ii) `t (c*d) v = t c (d•v) + t d v`
   (both are 2-line checks; the `θ`-terms cancel in pairs in (ii)).

3. **Close the sorry.**  Set `Ã c v := mixedA c v + t c⁻¹ v`.  Then:
   * `Ã c` is **additive**: its defect is `[R(c⁻¹•v,c⁻¹•w) + R(v,w)]` (step 1) `+`
     `[R(c⁻¹•v,c⁻¹•w) + R(v,w)]` (step 2(i) at `c⁻¹`) `= 0`.
   * `δÃ = δ(mixedA)`: the `t`-part telescopes to zero by 2(ii) at `(d⁻¹, c⁻¹)`:
     `t (cd)⁻¹ v = t d⁻¹ (c⁻¹•v) + t c⁻¹ v`.
   * `key_transgression` (proven) gives `δ(mixedA) = B_q^♭ f`, so
     `polar q (f c d) v = Ã c v + Ã d (c⁻¹•v) + Ã (c*d) v` with each `Ã c` additive.
   * `bflat_bijective` (proven) yields `g c` with `polar q (g c) = Ã c`; this is exactly the
     `∃ g` demanded by the sorry.  The already-proven descent + section finish the theorem.

Conceptual dictionary (for review): step 3 is the paper's comparison `γ(c) := β_c α_c⁻¹ ∈ V^∨`
between the `ξ`-conjugation family `β_c` (= `mixedA`, via `key_transgression`) and the
`κ⁰_q`-coherent family `α_c` (= `t`); `δγ = B_q^♭ η` is (119).

### 3a. New reusable lemma: symmetric zero-diagonal 2-cocycles on `V` are coboundaries

`symm_cocycle_is_coboundary`: for finite elementary-abelian `V` and `S : V → V → ZMod 2` with
the (additive, trivial-coefficient) cocycle identity, `S(v,w) = S(w,v)`, `S(v,v) = 0`:
`∃ θ, θ 0 = 0 ∧ ∀ v w, S v w = θ (v+w) + θ v + θ w`.

Proof design (no basis induction): the twisted product `E := ZMod 2 × V`,
`(z,v) * (z',w) := (z + z' + S(v,w), v + w)`, is an **abelian group of exponent 2** (comm =
symmetry, assoc = cocycle, inverses = zero diagonal; `S(0,·) = S(·,0) = 0` are forced), hence a
`ZMod 2`-module (`AddCommGroup.zmodModule`, as in `bflat_bijective`).  The projection
`E → V` is `ZMod 2`-linear and surjective, so it has a **linear section** (vector spaces over
the field `𝔽₂`; `LinearMap.exists_rightInverse_of_surjective`), and the section's first
coordinate is `θ`.  This is the injectivity half of `H²(V,𝔽₂) ≅ {quadratic forms}` — likely
reusable (e.g. P-13f trivial-module table).  ~60 lines, std-3.

## 4. Verification notes

* The defect formula `D_c = R(c⁻¹·, c⁻¹·) + R` was re-derived by hand and matches the Opus
  report; the three cocycle instances and the single `hconj` move are listed in §3.1 —
  same `linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))` engine as
  `key_transgression`.
* Conventions checked against the live file: `polar q v w = q(v+w) + q v + q w`;
  `m_quad` uses `c•` (so `Ã` uses `t c⁻¹`); the sorry's middle term is `polar q (g dd) (cc⁻¹•v)`,
  matching the contragredient twist of `Ã`'s coherence. ✓
* Import graph: `Transgression.lean` gains `import GQ2.OrbitData` (no cycle — only the root
  imports Transgression; OrbitData sits below SectionSix precisely for this own-file pattern).
  The eventual splice adds `import GQ2.Transgression` to `SectionSix.lean` (no cycle). ✓
* Axioms: everything is finite/char-2 algebra + one mathlib linear-section — std-3, `Ax = ∅`
  (matches the P-15i board row). ✓

## 5. Statement amendments (REVIEW REQUIRED — frozen-statement changes)

1. **`SectionSix.lemma_6_21`** gains the paper's hypothesis, in the repo's own 6.22 form:
   `(dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)` — restoring the clause
   *"assume a zero-section-normalized equivariant class `κ⁰_q` restricting to `q` has been
   fixed"* that the consequence-form extraction dropped.  Deviation note 3 in
   `docs/section67-extraction.md` is amended accordingly (this is the reviewed statement
   change that note anticipated).  Downstream (§8 phase covers) fixes `κ⁰_q` via Lemma 6.3
   before invoking 6.21/6.22, so the hypothesis is available at all call sites (none exist in
   Lean yet — the addition breaks nothing).
2. **`Transgression.splitting_of_global_cocycle`** gains the raw cochain form
   `(t : C → V → ZMod 2) (ht_quad : …(i) vs R…) (ht_mul : …(ii)…)` — proof-side, self-contained
   (no `FactorSet` dependency in the theorem statement); a bridge lemma
   `equivariant_lift_of_factorSet : IsEquivariantFactorSet q dat → ∃ t, (i) ∧ (ii)`
   (via §3a + §3.2) connects the two layers.

## 6. Implementation plan (single session, ~200 lines total)

| # | Item | Where | Size |
|---|------|-------|------|
| R1 | `symm_cocycle_is_coboundary` | Transgression.lean (lift later if wanted) | ~60 |
| R2 | `mixedA_defect` | Transgression.lean | ~30 |
| R3 | amend `splitting_of_global_cocycle` signature; fill sorry via §3.3 | Transgression.lean | ~45 |
| R4 | bridge `equivariant_lift_of_factorSet` (`import GQ2.OrbitData`) | Transgression.lean | ~40 |
| R5 | amend `lemma_6_21` signature (+ docstring, deviation note 3, board row) | SectionSix.lean, docs | small |
| R6 | (optional, closes P-15i) splice `lemma_6_21 := … splitting_of_global_cocycle … (bridge …)` | SectionSix.lean | ~10 |

Gate: `lake build` + `scripts/check_axioms.sh`; all new declarations `#print axioms` = std-3.
After R6, `Transgression.lean` is sorry-free (remove from `SORRY_ALLOWLIST`), and
`SectionSix.lean` loses the `lemma_6_21` sorry.
