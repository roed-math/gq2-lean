# Theorem 1.2 (`G_ℚ₂` presentation) — literature inputs, one page

*Condensed list for expert review. Full statements, encodings, adapter conventions and the
verification ledger: `literature-axioms.md`.*

**Status (2026-10-17): census 0.** The library contains no `axiom`.  The nine classical inputs
below were axioms until ticket C2 deleted `GQ2/Foundations/Axioms.lean`.  Each is now proved from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) at revision `706344c35` by an adapter
`GQ2/TauCeti/<file>` (namespace `GQ2.TauCetiBridge`, named `<legacy name>_tauceti`).  The legacy
names keep their byte-identical statements in `GQ2/Foundations/TauCetiInstance.lean`.  Trust base:
Lean's standard three axioms plus Tau Ceti's proofs (owner gate G0, 2026-10-16).

**Reduction.** `G_ℚ₂ ≅ Γ_A` (Theorem 1.2) follows from **Lemma 2.5** (one-sided profinite
reconstruction) applied to **eq. (154)**: `|Sur(Γ_A,G)| = |Sur(G_ℚ₂,G)|` for every finite `G`.
Lemma 2.5's only classical input is *proved* in the formalization (see below); eq. (154) — the
paper's §§3–9 tower (Prop. 3.2, Thm. 4.2, Lemma 10.1) — rests on the nine classical results below.

| leaf | classical statement — citation | Tau Ceti source (`TauCeti.` omitted) | adapter |
|---|---|---|---|
| B1 | `G_ℚ₂` is topologically finitely generated (`N+2` generators) — NSW **(7.4.1)** ✓ | `isTopologicallyFinitelyGenerated_absoluteGaloisGroup` | `B1.lean` |
| B3c | marked Demushkin form `G_ℚ₂(2) ≅ D₀ = ⟨A,S,Y \| A²S⁴[S,Y]⟩`, cyclotomic orientation `(−1, 1, (−3)⁻¹)` — Labute **Thm 8** (`d=1`), **Thm 4 case (2)** ✓ | `absoluteGaloisGroupProP_two_ratPadic_marked`, `standardD0Orientation_d0A/_d0S/_d0Y` | `B3c.lean` |
| B5 | local reciprocity for `ℚ₂` (Artin map, `ν_ur`, norm groups, `χ_cyc∘rec`) — NSW **(7.1.1)**, **(7.1.5)** ✓ | `ClassFieldTheory.artinMap` and its `Local.*` lemmas | `B5.lean` |
| B6 | local Tate duality (every finite `k/ℚ₂`): `H^i(k,A)×H^{2-i}(k,A′) → ℚ/ℤ` perfect — NSW **(7.2.6)**; Serre *GC* **II §5.2 Thm 2**; Hilbert nondeg. FV **IV §5**, O'Meara **63:13** ✓✓ | `ClassFieldTheory.tateDualityPairing_perfect_mixed`, `h2MuEquivZMod_mixed` | `B6.lean`, `DualizingGroup.lean` |
| B7 | local Euler characteristic `χ(A) = ‖#A‖_k` — NSW **(7.3.1)**; Serre *GC* **II §5.7 Thm 5** ✓✓ | `ClassFieldTheory.eulerCharacteristic_mixed`, `finite_H` | `B7.lean` |
| B8 | cyclotomic action on the peripheral generators of `π₁^{(2)}(ℙ¹∖{0,1,∞})`, group-theoretic form — Stix **§3.3 + Def 37** ✓ | `Peripheral.exists_peripheralPowerAutomorphism_two` | `B8.lean` |
| B9 | relative Stiefel–Whitney identity `w(Tr⟨a⟩) = w(Tr⟨1⟩)(1 + cor[a] + N^{Ev}[a])`, degrees ≤ 2 — Evens **Thm 1**; Kahn **Thm 1–3**; Kozlowski **Thm 1.1** ✓ | `sw1_eq_add_galoisCor_of_equivalent_traceTransfer`, `sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer` | `B9.lean`, `StiefelWhitneyDict.lean` |
| B10 | oriented tame quotient `G_ℚ₂/W ≅ ⟨σ,τ \| τ^σ=τ²⟩` — NSW **(7.5.3)**; orientation: Serre *LF* **XIII §4 Prop. 13** + cor., Neukirch ANT **V (1.2)** ✓ | `wildInertiaSubgroup`, `isProP_wildInertiaSubgroup`, `tameQuotientGeometricEquiv`, `iwasawaCoordinateGeometric` | `B10.lean` |
| B11a | dyadic norm criterion `[a]∪[b] = 0 ⟺ b = x² − a y²` (finite `k/ℚ₂`) — Serre *LF* **XIV §2 Prop. 4(iii)**, Prop. 5 ✓ | `cup_kummerClass_eq_zero_iff` | `B11a.lean` |

**Adapter conventions** (per leaf in `literature-axioms.md` §B).  Tau Ceti's Frobenius is
arithmetic and gq2's `ν_ur` (B5) and `ν_t` (B10) are geometric; the adapters invert.  The B3c
relators agree (same commutator convention).  B8 takes the exponent `ι u = ω₂ · s(u)`.  B7's adapter
covers `M : Type` and is transported to `M : Type*` in `TauCetiInstance.lean`.  Shared dictionaries:
`GaloisDict`, `CohomologyDict`, `ProPDict`.

**Not in the census.**  Deleted as never consumed: ~~B2~~ (2-adic cyclotomic surjectivity,
Washington **Ch. 2 Thm 2.5**; 2026-07-09) and ~~B4~~ (`G_ℚ₂(2)` rank-3 Demushkin, NSW
**(7.5.11)(ii)**; 2026-07-10; B3c subsumes a marked B4).  Discharged in-repo on 2026-07-09 as
same-name std-3 declarations: **B7′** (dyadic Hilbert symbol, Serre *Course in Arithmetic*
**III §1.2 Thm 1**), **B11b** (unramified units are norms, Serre *LF* **V §2 Prop. 3**), **B12**
(local Kummer surjectivity, NSW **(6.2.1)**), **B13** (dyadic unit filtration, Serre *LF*
**IV §2 Prop. 6**).  Proved in-repo: **Ribes–Zalesskiĭ Prop. 2.5.2** (f.g. profinite groups are
Hopfian — Lemma 2.5's only classical input), **Schur–Zassenhaus** (§9.1), and **B-Lab** (the B3
classification at `D_R ≅ D₀` for the `Γ_R` route; declined as a tenth axiom 2026-07-25, proved
2026-07-26 as `GQ2.Roe.Labute.bLab`).

**Census history.**  Peak 15 (2026-07-06) → 10 (2026-07-09: B12, B7′, B13, B11b discharged; B2
deleted) → 9 (2026-07-10: B4 deleted) → **0** (2026-10-17, ticket C2, owner gate G1: the nine
proved via Tau Ceti).

**Citations.**  The published ingredients of every leaf are source-audited.  Direct leaves have an
exact theorem number and checked statement; the composite bundles (B3c, B5, B8, B9, B10) also need
the normalization/dictionary steps recorded in `literature-axioms.md`.  Kahn's verified Theorem 2
is the direct source for B9; the exact Kozlowski 1984 text was not independently obtainable in the
2026-07-12 audit.  The source PDFs are not vendored in the public repository.  Since the discharge
the citations document which published theorem each Tau Ceti proof establishes.

**Checks.**  `scripts/check_axioms.sh` (census 0; capstones at exactly the standard three),
`GQ2/AxiomLedger.lean`, `GQ2/TauCetiAxiomAudit.lean` (the four `*_tauceti` capstones of
`GQ2/TauCeti/Main.lean`), `GQ2/PalomarAxiomAudit.lean`.

**Legend / refs.** `✓` checked against source; `✓✓` two sources. — **NSW** =
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.; **Serre *GC*** = *Galois
Cohomology*; **Serre *LF*** = *Local Fields*; **Evens/Kahn/Kozlowski** = the three Evens–Kahn-formula
papers; Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967).
