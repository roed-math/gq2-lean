# Theorem 1.2 (`G_ℚ₂` presentation) — classical inputs, one page

*Condensed list for expert review. Full statements + verification ledger: `literature-axioms.md`.*

**Reduction.** `G_ℚ₂ ≅ Γ_A` (Theorem 1.2) follows from **Lemma 2.5** (one-sided profinite
reconstruction) applied to **eq. (154)**: `|Sur(Γ_A,G)| = |Sur(G_ℚ₂,G)|` for every finite `G`.
Lemma 2.5's only classical input is *proved* in the formalization (see foot); eq. (154) — the paper's
§§3–9 tower (Prop. 3.2, Thm. 4.2, Lemma 10.1) — rests on the nine classical results below.

| # | classical statement | citation | ✓ |
|---|---|---|:--:|
| B1 | `G_ℚ₂` is topologically finitely generated (`N+3` generators) | NSW **(7.5.14)** (Jannsen–Wingberg) | ✓ |
| ~~B2~~ | ~~2-adic cyclotomic character `Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective~~ *(deleted 2026-07-09: never consumed)* | Washington, *Cyclotomic Fields*, **Ch. 2 Thm 2.5** | ✓ |
| B3 | Demushkin classification; `G_ℚ₂(2) ≅ ⟨A,S,Y \| A²S⁴[S,Y]=1⟩` | Labute **Thm 8** (`d=1`), **Thm 4 case (2)** | ✓ |
| B4 | `G_ℚ₂(2)` is a Demushkin group of rank `3` (`q=2`) | NSW **(7.5.11)(ii)** | ✓ (deleted 2026-07-10, unused) |
| B5 | local reciprocity: `(G_k, k̄ˣ)` is a class formation | NSW **(7.1.1)**, **(7.1.5)** | ✓ |
| B6 | local Tate duality (**every finite `k/ℚ₂`**): `H^i(k,A)×H^{2-i}(k,A′) → ℚ/ℤ` perfect (`0≤i≤2`) | NSW **(7.2.6)**; Serre *GC* **II §5.2 Thm 2**; Hilbert nondeg. FV **IV §5 (5.1)(6)/(5.2)**, O'Meara **63:13** | ✓✓ |
| B7 | local Euler characteristic: `χ(A) = ‖#A‖_k` | NSW **(7.3.1)**; Serre *GC* **II §5.7 Thm 5** | ✓✓ |
| ~~B7′~~ | dyadic Hilbert symbol `(2^α u, 2^β v)₂ = (-1)^{ε(u)ε(v)+αω(v)+βω(u)}` — **discharged 2026-07-09, proved in-repo** | Serre, *Course in Arithmetic*, **III §1.2 Thm 1** | ✓ |
| B8 | Galois action on `π₁^{(2)}(ℙ¹∖{0,1,∞})`: cyclotomic on peripheral inertia | Stix **[8] §3.3 + Def 37** | ✓ |
| B9 | Evens norm + Evens–Kahn formula for the total Stiefel–Whitney class | Evens **§§4–5 Thm 1**; Kahn **Thm 1–3**; Kozlowski **Thm 1.1** | ✓ |

**Discharged (proved in the Lean formalization, not axioms).**
**Ribes–Zalesskiĭ Prop. 2.5.2** (a finitely generated profinite group is Hopfian — Lemma 2.5's only
classical input) and **Schur–Zassenhaus** (§9.1 terminal case).

**Status.** The **ten leaves above are source-verified** — each has an exact theorem number and a
verbatim statement checked against the cited book/paper (`✓`; `✓✓` = two independent sources).
*Later census additions are off this condensed page:* **B10** (tame quotient, NSW **(7.5.3)** —
verified; **oriented form B10′ since 2026-07-06**: reciprocity-orientation clauses, Neukirch ANT
**V (6.2)** units ↦ inertia + **V (1.2)** units-are-unramified-norms, both verified),
**B11a**/~~**B11b**~~ (dyadic norm criterion, Serre *Local Fields* **XIV §2 Prop. 7 iii** /
**V §2 Prop. 3** — line-checked by P-20, 2026-07-05; **B11b discharged 2026-07-09**), and **B13**
(dyadic unit filtration, Serre *Local Fields* **IV §2 Prop. 6** — line-checked by P-15f1,
2026-07-06, **discharged 2026-07-09**); see
`literature-axioms.md`.  **2026-07-09 census flips (B12, B7′, B13 + B11b boards, user-approved):**
**B12** (local Kummer surjectivity, NSW **(6.2.1)** — added 2026-07-06), **B7′** (dyadic Hilbert
symbol, struck above), **B13** (dyadic unit filtration), and **B11b** (unramified units are norms —
so `dyadicNormCriterion` rests on B11a alone) are **discharged, proved in-repo** as
same-name std-3 declarations, and the never-consumed **B2** is **deleted** (struck above).  Full
census: **10** axioms, all source-verified.

**Legend / refs.** `✓` checked against source; `✓✓` two sources. — **NSW** =
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.; **Serre *GC*** = *Galois
Cohomology*; **Evens/Kahn/Kozlowski** = the three Evens–Kahn-formula papers; Labute, *Classification
of Demushkin groups*, Canad. J. Math. 19 (1967).
