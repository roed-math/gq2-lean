# Theorem 1.2 (`G_ℚ₂` presentation) — classical inputs, one page

*Condensed list for expert review. Full statements + verification ledger: `literature-axioms.md`.*

**Reduction.** `G_ℚ₂ ≅ Γ_A` (Theorem 1.2) follows from **Lemma 2.5** (one-sided profinite
reconstruction) applied to **eq. (154)**: `|Sur(Γ_A,G)| = |Sur(G_ℚ₂,G)|` for every finite `G`.
Lemma 2.5's only classical input is *proved* in the formalization (see foot); eq. (154) — the paper's
§§3–9 tower (Prop. 3.2, Thm. 4.2, Lemma 10.1) — rests on the nine classical results below.

| # | classical statement | citation | ✓ |
|---|---|---|:--:|
| B1 | `G_ℚ₂` is topologically finitely generated (`N+3` generators) | NSW **(7.5.14)** (Jannsen–Wingberg) | ✓ |
| B2 | 2-adic cyclotomic character `Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective | Washington, *Cyclotomic Fields*, **Thm 2.5** | std |
| B3 | Demushkin pro-`p` groups classified by rank and invariant `q` | Labute (1967), **Thm 4 (case 2), Thm 8** | q |
| B4 | `G_ℚ₂(2)` is a Demushkin group of rank `3` (`q=2`) | NSW **(7.5.11)(ii)** | ✓ |
| B5 | local reciprocity: `(G_k, k̄ˣ)` is a class formation | NSW **(7.1.1)**, **(7.1.5)** | ✓ |
| B6 | local Tate duality: `H^i(k,A)×H^{2-i}(k,A′) → ℚ/ℤ` perfect (`0≤i≤2`) | NSW **(7.2.6)**; Serre *GC* **II §5.2 Thm 2** | ✓✓ |
| B7 | local Euler characteristic: `χ(A) = ‖#A‖_k` | NSW **(7.3.1)**; Serre *GC* **II §5.7 Thm 5** | ✓✓ |
| B7′ | dyadic Hilbert symbol `(2^α u, 2^β v)₂ = (-1)^{ε(u)ε(v)+αω(v)+βω(u)}` | Serre, *Course in Arithmetic*, **III §1.2 Thm 1** | ✓ |
| B8 | Galois action on `π₁^{(2)}(ℙ¹∖{0,1,∞})`: cyclotomic on peripheral inertia | Stix (2012); Deligne (1989) | q |
| B9 | Evens norm + Evens–Kahn formula for the total Stiefel–Whitney class | Evens **§§4–5 Thm 1**; Kahn **Thm 1–3**; Kozlowski **Thm 1.1** | ✓ |

**Discharged (proved in the Lean formalization, not axioms).**
**Ribes–Zalesskiĭ Prop. 2.5.2** (a finitely generated profinite group is Hopfian — Lemma 2.5's only
classical input) and **Schur–Zassenhaus** (§9.1 terminal case).

**Legend.** `✓` theorem number + statement checked against the source PDF; `✓✓` two independent
sources; `q` taken verbatim from the paper's bibliography; `std` standard textbook (source not on
hand). — References: **NSW** = Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.;
**Serre *GC*** = *Galois Cohomology*; Labute, *Classification of Demushkin groups*, Canad. J. Math.
19 (1967).
