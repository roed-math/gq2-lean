# P-15f7 axiom proposal — the K-level pairing inputs of the deep/quotient duality

**Date**: 2026-07-06 (Fable).  **Status**: ✅ **APPROVED (user, 2026-07-07) — both parts**: §1
(B6 base-generalization) **EXECUTED** (`GQ2/TateDuality.lean`: `TateDualityG G n` +
`IsLocalDualizingGroup` gate + `TateDuality n` abbrev; `GQ2/Foundations/Axioms.lean`:
`axiom tateDualityAt` replacing `axiom tateDuality`, base member re-derived as
`def tateDuality`; `GQ2/AxiomLedger.lean` B6 entry → `tateDualityAt`; docs `review-packet.md` /
`literature-axioms.md` / `literature-axioms-onepage.md` updated; census 15 unchanged, guard
green); §2 ((H4) in-repo proof route) approved as the plan of record — the counting route is
a P-15f7 work item, fallback leaf only on a second explicit approval.
**Consumer**: the three pairing hypotheses of `GQ2.card_equivHoms_deep_eq_quot`
(`GQ2/DeepDuality.lean` §F — the abstract `hduality` of the f6 capstone
`card_deepPart_sq_of_duality`): a `C`-invariant biadditive `B` on `M = H¹(G_K, 𝔽₂)`,
its **nondegeneracy** (H2), and the **one sharp instance** `Deep^⊥ ≤ E` (H4).
Everything else in the f7 chain is proved (std-3) or derivable (handoff §8).

All citations below are **verified against the `references/` scans this session**
(pages read on-screen): FV = Fesenko–Vostokov, *Local Fields and their Extensions*
(2nd ed.), Ch. IV §5 pp. 143–146; O'Meara, *Introduction to Quadratic Forms*,
§§63A–63B pp. 160–166; plus the P-15f1-audit-verified Serre LF pins.

---

## 1. RECOMMENDED: base-generalize B6 (census-neutral) — the pairing + nondegeneracy

**Change**: `axiom tateDuality (n : ℕ) [NeZero n] : TateDuality n` (G_ℚ₂-only) becomes a
family over finite extensions: for every `k : IntermediateField ℚ_[2] ℚ̄₂` with
`[FiniteDimensional ℚ_[2] k]`, a `TateDuality`-style bundle **at `G_k = k.fixingSubgroup`**
(the current axiom is the `k = ⊥` member).

**Informal statement (the generalized B6)**: *Let `k/ℚ₂` be a finite extension and `n ≥ 1`.
There is an isomorphism `inv_k : H²(G_k, μ_n) ≅ ℤ/n`, and for every finite discrete
`n`-torsion `G_k`-module `M` the evaluation cup pairings*
`Hⁱ(G_k, Hom(M, μ_n)) × H^{2−i}(G_k, M) → H²(G_k, μ_n) ≅ ℤ/n`
*are perfect, for `i = 0, 1, 2`.*

**Citations** (identical to the current B6 — the theorem in the literature is already stated
for arbitrary local fields, so the ℚ₂-only form under-uses its own citation):
* **NSW [1], Ch. VII §7.2, Theorem (7.2.6)** — local Tate duality, for `k` any finite
  extension of `ℚ_p`.
* Serre, *Galois Cohomology*, II §5.2 Theorem 2; Milne, *ADT* I.2.3.

**Why this covers (H2) and the pairing `B`**: at `n = 2`, `M = 𝔽₂`
(`Hom(𝔽₂, μ₂) ≅ 𝔽₂`), take `B := inv_K ∘ (cup)` on `H¹(G_K, 𝔽₂)`.  The `(1,1)`-perfectness
clause is exactly the nondegeneracy (H2).  The `C = Gal(K/ℚ₂)`-invariance (H1) costs **no
clause**: conjugation acts on `H²(G_K, μ₂) ≅ ℤ/2` by additive automorphisms, and
`Aut(ℤ/2) = 1` — invariance is free at `n = 2` once cup-conjugation-equivariance is proved
(cochain-level, the in-repo `conjAct` style; provable, no axiom).  The isotropy (H3) is the
banked Tier-5 `cup_deepClasses` (`= 0` **in `H²`**, so `inv∘cup` vanishes on the nose).

**Precedent**: B9 was base-generalized by explicit census decision (P-15 escalation,
user-approved 2026-07-03) with **no census change**.  Same shape here: census stays 15.

**Symbol-side documentation** (equivalent classical content, for `docs/literature-axioms.md`):
the induced pairing on square classes is the mod-2 Hilbert symbol, whose properties are
**FV Ch. IV §5, Proposition (5.1)** (pp. 143–144, verified): (1) bilinearity; (5) the norm
criterion `(α,β)_n = 1 ⟺ β ∈ N_{F(ⁿ√α)/F}` (= B11a's content at `n = 2` via the cup
bridge); (6) **nondegeneracy** `((α,β)_n = 1 ∀β ⟺ α ∈ F^{*n})`; (9) Galois equivariance
`(σα, σβ)_{n,σL} = σ(α,β)_{n,L}`; plus the **Corollary** (p. 145): the induced pairing
`F^*/F^{*n} × F^*/F^{*n} → μ_n` is nondegenerate.  Independent second home for
nondegeneracy: **O'Meara, ITQF, 63:13** (p. 166, verified): *"given any non-square β in Ḟ
there is an α in Ḟ with (α,β/𝔭) = −1"*.  Third: Serre LF **XIV §1, Prop. 3 Corollary**
(P-15f1 audit, verified).

---

## 2. (H4) the sharp instance `U_{e+1}^⊥ ⊆ U_e·(K^×)²` — RECOMMEND: prove in-repo, NO leaf

The one (94)-instance the minimal route consumes.  **Informal**: *a square class of `K`
pairing trivially (mod-2 Hilbert symbol) with every unit of `U_{e+1} = 1 + 𝔭^{e+1}` is
represented by a unit of `U_e = 1 + 𝔭^e`* (`e = v_K(2)`).

**No single numbered literature home** (P-15f1 audit, reconfirmed): FV states the general
`U_i^⊥ = U_{2e−i+1}` only as Ch. VII §4 **Exercises 4c/5b** (exercise-grade — ruled out as
an axiom basis by the user's 2026-07-06 directive); O'Meara §63 *assembles* it but does not
number it; the paper's own bracket "[7, Ch. XIV §§2–3]" is coarse (audit note: the
filtration itself is Serre Ch. IV §2).

**In-repo proof route (recommended; all ingredients verified available)** — the counting
argument, using the §1 nondegeneracy:
1. `#(Deep^⊥) = #M / #Deep` — perfect-pairing count; the perp machinery is **already
   banked** (`pairPerp`, `perpEquivDualQuot`, `card_addHom_zmod2`, all std-3 in
   `DeepDuality.lean`).
2. `E ⊆ Deep^⊥`, i.e. the isotropy instance `(U_e, U_{e+1}) = 1` — extend the Tier-5
   Brahmagupta/contraction descent (`normForm_of_deep`, proved for deep×deep) to base
   `a ∈ U_e`: the contraction budget changes from `j + (e+1) ≥ 2e+2` to `j + e ≥ 2e+1`,
   still at the Local Square Theorem threshold (`sq_of_near_one`, banked).  *Moderate risk;
   the one genuinely new proof.*
3. `#E/#Deep = 2^f` — the mid graded size, from **B13** (`card_gr` at `i = e`) plus the
   square-class analysis: at odd depth `j < 2e` squares do not enter
   (`‖u²−1‖ = ‖u−1‖·‖u±…‖` parity, value-group discreteness `hπ_max`), so the M-level
   graded piece is the full `U_e/U_{e+1}`.  Note `e` **odd** is Lemma 6.10's conclusion
   for tame `K/ℚ₂` (paper p. 29).  The corresponding classical statements — verified,
   citable in comments: **O'Meara 63:2** (defect ladder `0 ⊂ 4𝔬 ⊂ 4𝔭⁻¹ ⊂ ⋯ ⊂ 𝔭`, only odd
   exponents below `4𝔬`), **63:5** (`ε = 1+α`, `|4| < |α| < 1`, `ord α` odd ⟹ `𝔡(ε) = α𝔬`),
   **63:8(2)** (`(1+𝔭^r)² = 1+2𝔭^r` for `𝔭^r ⊆ 2𝔭`).
4. `#M = #E · #Deep` — global square-class count `(K^×:K^{×2}) = 4·(N𝔭)^{ord 2} = 2^{d+2}`
   (**O'Meara 63:9**, verified numbered!) assembled from B13's graded sizes + the valuation
   split; alternatively organized to avoid `#M` entirely by comparing `Deep^⊥` with `E`
   through steps 1–3 only.
5. Steps 1–4 give `Deep^⊥ = E` (⊇ from 2, equality by count), hence (H4).

**Fallback if step 2 stalls** (second approval point, only then): leaf the single instance
as a **B14** clause with the assembled citation *"O'Meara ITQF §63 (63:2 + 63:5 + 63:8; the
standard quadratic-defect computation), FV Ch. VII §4 (exercise phrasing)"* — flagged as the
weakest-citation leaf in the project; NOT recommended while route 2 is untried.

---

## 3. What is explicitly NOT proposed

* **No symbol-side new axiom** (a "B14 Hilbert-symbol bundle") — everything it would assert
  is covered by §1's base-generalized B6 + the banked B11a bridge; adding it would duplicate
  the pairing object and add census.
* **No (F2)/inertia leaf** — the twist is derivable (`GQ2/UnitFiltration.lean` docstring;
  handoff §8 item 5).
* **No graded-(93) leaf** — the minimal route avoids the per-level computation; the two
  sizes it does use come from B13 + elementary norm algebra (§2.3).
* `−1 ∈ U_e` (the other half of the paper's (94) display): trivially provable
  (`‖−1−1‖ = ‖2‖`), nothing needed.

## 4. Net census effect

* **Recommended package**: B6 base-generalized in place (census **unchanged**, 15), zero new
  axioms; (H4) proved in-repo.
* **Worst case** (step-2 fallback triggered): +1 (a single-clause B14), census 15 → 16.
