# Literature axioms for Theorem 1.2 — reviewer's enumeration

**Purpose.** This document reduces the formalization of the paper *A Profinite Presentation of the
Absolute Galois Group of `ℚ₂`* (D. C. Turturean, 2026) to a **minimal list of classical results that
already exist in the literature**, and enumerates them with precise statements and citations. It is
meant for a quick expert check (R. Hill, K. Buzzard): *does each "leaf" below correctly match a known
theorem in the cited reference?*

**Scope of the reduction.** The paper's *own* §§3–9 argument (its Propositions and Lemmas) is
**granted** here — those are the paper's contribution, not literature, and are listed separately in
§C so you can also check they match the *paper*. What we isolate in §B are the **classical
foundations** the paper builds on. If every item in §B is a correct citation and every node in §C is
faithful to the paper, then (modulo the routine profinite assembly noted in §A) Theorem 1.2 follows.

**Lean status legend.**
- ✅ **faithful** — stated as a typechecked Lean `axiom`/`theorem` against current Mathlib, in
  `GQ2/Foundations.lean` (or already *proved*, in which case it is not a leaf at all).
- 🟡 **schematic** — the mathematical statement is precise (below) but a faithful Lean signature needs
  infrastructure Mathlib lacks (continuous Galois cohomology of a profinite group, Demushkin groups,
  local Tate duality pairings, the Hilbert symbol), so it is documented here, not in Lean.

---

## A. Top-level spine (how Theorem 1.2 is assembled)

```
Theorem 1.2   G_ℚ₂ ≅ ⟨σ,τ,x₀,x₁ | τ^σ=τ², h₀u₁⁻¹x₁^σc₀=1, ⟨⟨x₀,x₁⟩⟩ pro-2⟩
  │
  ├─ Lemma 2.5  (one-sided profinite reconstruction)          [Lean: reconstruction / reconstruction_of_equinum]
  │     needs only:  RZ Hopfian for f.g. profinite groups  →  PROVED here (profinite_hopfian); not a leaf
  │
  └─ eq. (154)  ∀ finite G,  |Sur(Γ_A,G)| = |Sur(G_ℚ₂,G)|    [Lean: main_surjection_count, via Γ_A]
        │
        ├─ Prop 2.3   |Sur(Γ_A,G)| = admissibleCount G         [Lean: admissibleCount; hypothesised in main_presentation]
        ├─ Lemma 10.1 exhaustion by tame frames                [paper node — §C]
        └─ Theorem 4.2 boundary-framed exact-image (§9)        [paper node — §C]  ← the classical leaves in §B feed here
```

**On Lemma 2.5.** The paper states it with `Q` *any* profinite group and `|Sur(P,H)| = |Sur(Q,H)|`
as genuine cardinalities. The faithful Lean encoding is `GQ2.reconstruction_of_equinum`
(hypothesis `∀ H, Nonempty (ContSurj P H ≃ ContSurj Q H)`, i.e. equinumerosity — which for
finitely generated `P` forces the counts finite, matching the paper). `GQ2.reconstruction` is a
convenience specialization assuming *both* `P,Q` topologically f.g. with equal `Nat.card`. Its one
literature input — *a finitely generated profinite group is Hopfian* (RZ [4, §2.5], i.e.
Ribes–Zalesskiĭ *Profinite Groups* Prop. 2.5.2) — is **proved in this repo** as
`GQ2.profinite_hopfian`, so Lemma 2.5 has **no** remaining literature leaf; only the standard
profinite assembly `exists_contSurj_of_card_le` (below) is deferred, and it is Mathlib-provable, not
a literature gap.

**On `exists_contSurj_of_card_le` (not a literature leaf).** "A profinite group `R` is the inverse
limit of its finite quotients, so compatible surjections onto every finite quotient of `R` assemble
into a surjection onto `R`." This is standard (RZ Ch. 1–2) **and already available in Mathlib**:
`ProfiniteGrp.isoLimittoFiniteQuotientFunctor` (`R ≅ lim R/V`) plus
`nonempty_sections_of_finite_cofiltered_system` (König over `OpenNormalSubgroup R`, a
`SemilatticeInf`). Its arithmetic core is proved (`contSurj_quotient_nonempty_finite`); the remaining
categorical wiring is deferred work, **not** an axiom.

---

## B. The classical foundations (the minimal literature list)

Each is a published theorem. "Used at" points to the paper node in §C that consumes it.
**Citation-confidence markers** (the point of this pass — see §E for what to confirm):
`[quoted]` the paper itself cites this exact result; `[confirmed]` I verified the exact number against
a reliable source; `[likely]` my identification of a standard result — **please confirm the exact
theorem number** from the book.

### B1. `G_ℚ₂` is topologically finitely generated  ✅ faithful
- **Statement.** The absolute Galois group of a `p`-adic local field `K` is topologically finitely
  generated (by `[K:ℚ_p]+3` generators when `μ_p ⊆ K`; `[K:ℚ_p]+2` otherwise).
- **Citation.** Primary: **Jannsen–Wingberg, *Die Struktur der absoluten Galoisgruppe `p`-adischer
  Zahlkörper*, Invent. Math. 70 (1982/83), 71–98** — the full presentation of `G_K`, from which
  finite generation is immediate; finite generation alone is **Jannsen, *Über die Galoisgruppen
  lokaler Körper*, Invent. Math. 70 (1982), 53–69** `[confirmed as the source: Jannsen's theorem]`.
  Reproduced in **NSW [1], Ch. VII §7.5** (the presentation is **Thm 7.5.14** for `p` odd; the
  general structure theorem there covers `p=2`) `[likely for the exact NSW number]`.
- **Lean.** `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`.
- **Used at.** `main_presentation` (`hfgG`), feeding Lemma 2.5.

### B2. 2-adic cyclotomic character is surjective  ✅ faithful
- **Statement.** `χ_cyc : Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective; equivalently `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`.
- **Citation.** Classical. **Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Theorem 2.5 / §2** (`Gal(ℚ(μ_{p^n})/ℚ) ≅ (ℤ/p^n)ˣ`, hence the inverse limit `≅ ℤ_pˣ`) `[likely]`;
  also NSW [1] §7.5. `[the math is standard]`
- **Lean.** `GQ2.Foundations.cyclotomicCharacter_two_surjective` (via Mathlib `cyclotomicCharacter 2`).
- **Used at.** Lemma 3.6 (cyclotomic powering of the three peripheral inertia classes).

### B3. Classification of Demushkin groups (Labute)  🟡 schematic
- **Statement.** A Demushkin pro-`p` group (finitely generated one-relator pro-`p` group with
  `dim H²(G,𝔽_p) = 1` and non-degenerate cup product `H¹×H¹→H²`) is determined up to isomorphism by
  its rank `n = dim H¹` and its invariant `q` (with a secondary invariant in the exceptional dyadic
  case). For the rank-3, `q=2` dyadic normal form the relator can be taken as `A²S⁴[S,Y]`, and the
  canonical orientation character is computed explicitly.
- **Citation.** **Labute [2], *Classification of Demushkin groups*, Canad. J. Math. 19 (1967),
  106–132: Theorem 4 (case (2)) and Theorem 8** `[quoted — the paper cites exactly these]`; see also
  Serre [3].
- **Lean.** Schematic (Mathlib has no `Demushkin` predicate; a faithful statement needs pro-`p`
  cohomology with cup products).
- **Used at.** Lemma 3.4 → Prop 1.1.

### B4. `G_ℚ₂(2)` is the rank-3 dyadic Demushkin group  🟡 schematic
- **Statement.** The maximal pro-2 quotient `G_ℚ₂(2)` of the absolute Galois group is a Demushkin
  group of rank `[ℚ₂:ℚ₂]+2 = 3` with `q = 2`; concretely `G_ℚ₂(2) ≅ ⟨A,S,Y | A²S⁴[S,Y]=1⟩_{pro-2}`.
- **Citation.** That `G_K(p)` is Demushkin: **Demushkin (1961/63)**; **Serre [3], *Structure de
  certains pro-`p`-groupes (d'après Demushkin)*, Sém. Bourbaki 252 (1962/63)**; **NSW [1], Ch. VII
  §7.5, Theorem 7.5.11** (`G_K(p)` is Demushkin of rank `[K:ℚ_p]+2`, with the relevant invariants)
  `[likely for the exact NSW number]`. The concrete dyadic normal form / invariants are Labute [2].
- **Lean.** Schematic (needs the maximal pro-2 quotient of `G_ℚ₂` as an object; the *relator*
  `A²S⁴[S,Y]` itself is expressible in `FreeProfiniteGroup (Fin 3)` — it uses no `ω₂`).
- **Used at.** Lemma 3.4 → Prop 1.1.

### B5. Local reciprocity (local class field theory for `ℚ₂`)  🟡 schematic
- **Statement.** The local Artin/reciprocity map `rec : ℚ₂ˣ → G_ℚ₂^{ab}` is an injective homomorphism
  with dense image, normalized so that a uniformizer maps to (arithmetic) Frobenius, inducing
  `ℚ₂ˣ / N_{L/ℚ₂}(Lˣ) ≅ Gal(L/ℚ₂)` for finite abelian `L/ℚ₂`; on the cyclotomic quotient it recovers
  `χ_cyc(rec(u)) = u⁻¹`.
- **Citation.** **Serre, *Local Fields* [7], Part IV: Ch. XI (Class Formations) and Ch. XII (Local
  Class Field Theory)** `[likely — corrects an earlier "Ch. VI" typo]`; **NSW [1], Ch. VII §7.1** (the
  local reciprocity map) `[likely]`. Normalization (uniformizer ↦ arithmetic Frobenius): the paper's
  Lemma 3.5.
- **Lean.** Schematic (CFT provides abstract class-formation reciprocity `reciprocityIso`/`localInv`,
  but not the specific local Artin map `ℚ₂ˣ → G^{ab}`; `LocalCFT/` is early).
- **Used at.** Lemma 3.5 (marked abelianization, orientation, initial form).

### B6. Local Tate duality  🟡 schematic
- **Statement.** For a `p`-adic local field `K` and a finite `G_K`-module `M` (with `M' = Hom(M,μ)`
  the Tate dual), the cup product `H^i(G_K,M) × H^{2-i}(G_K,M') → H²(G_K,μ) ≅ ℚ/ℤ` is a perfect
  pairing of finite groups, for `i = 0,1,2`.
- **Citation.** **NSW [1], Ch. VII §7.2, Theorem 7.2.6** `[likely]`; **Serre, *Galois Cohomology*,
  Ch. II §5.2 ("Dualité locale", Théorème 2)** `[likely]`; **Milne, *Arithmetic Duality Theorems*,
  2nd ed., Ch. I, Theorem I.2.1 (Cor. I.2.3)** `[likely]`. Original: Tate (1962/1963).
- **Lean.** Schematic (needs continuous Galois cohomology of the profinite `G_K` and the cup-product
  pairing; Mathlib/CFT have finite-group `H^i` via `Rep R G` but not the continuous duality package).
- **Used at.** §5 (the three-term duality complex, Lemmas 5.11/5.13) and §9.2.

### B7. Local Euler–Poincaré characteristic  🟡 schematic
- **Statement.** For `K` `p`-adic and finite `G_K`-module `M`,
  `|H⁰(G_K,M)| · |H²(G_K,M)| / |H¹(G_K,M)| = ‖#M‖_K = (#M)^{-[K:ℚ_p]}` (the `p`-part). In particular
  for the elementary 2-modules `M` of §9.2 over `ℚ₂` this gives `H²=0` and `|Z¹(M)| = 2^{2·dim M}`.
- **Citation.** **NSW [1], Ch. VII §7.3, Theorem 7.3.1** `[likely]`; **Serre, *Galois Cohomology*,
  Ch. II §5.7 (Tate's local Euler–Poincaré formula, Théorème 5)** `[likely]`; **Milne, *ADT*, Ch. I,
  Theorem I.2.8** `[likely]`. Original: Tate.
- **Lean.** Schematic (same continuous-cohomology gap as B6).
- **Used at.** §9.2 (lifting through the elementary quotient `M`; strict decrease (145)).

### B7′. Dyadic Hilbert symbol formula  🟡 schematic
- **Statement.** For `ℚ₂` the Hilbert symbol `(·,·)₂ : ℚ₂ˣ/ℚ₂ˣ² × ℚ₂ˣ/ℚ₂ˣ² → {±1}` is given by
  `(2^α u, 2^β v)₂ = (-1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`, where `ε(u) = (u-1)/2 mod 2`,
  `ω(u) = (u²-1)/8 mod 2`. In the square-class basis `(-1,2,-3)` this yields `(-1,-1)₂ = -1`,
  `(2,-3)₂ = -1`, others trivial — the cup-product initial form `α² + βγ + γβ`.
- **Citation.** **Serre, *A Course in Arithmetic*, GTM 7, Ch. III, Theorem 1 (and the explicit
  local formulas of §1.1–1.2)** `[likely — the dyadic (ε, ω) formula is exactly here]`; **Serre,
  *Local Fields* [7], Ch. XIV (Explicit Reciprocity Laws)** `[likely]`.
- **Lean.** Schematic (Mathlib has no Hilbert symbol).
- **Used at.** Lemma 3.5 and §6 (base quadratic form, Arf invariant).

### B8. Galois action on `π₁(ℙ¹∖{0,1,∞})` and its peripheral structure  🟡 schematic
- **Statement.** The outer Galois action `G_ℚ → Out(Δ)` on the geometric maximal pro-2 fundamental
  group `Δ = π₁^{pro-2}(ℙ¹_{ℚ̄}∖{0,1,∞})` sends the three peripheral inertia generators `P,T,C` to
  cyclotomic conjugates (`φ_u(P) = c_P^{-1} P^u c_P`, etc., for `u ∈ ℤ₂ˣ`).
- **Citation.** **Stix [8], *On cuspidal sections of algebraic fundamental groups*, in Galois–
  Teichmüller Theory and Arithmetic Geometry, ASPM 63 (2012), 519–563** `[quoted]`; the cyclotomic
  action on inertia originates with **Deligne, *Le groupe fondamental de la droite projective moins
  trois points*, in Galois Groups over ℚ, MSRI Publ. 16 (1989), §§8, 15–19** `[likely]`; Ihara.
- **Lean.** Schematic (no étale/anabelian `π₁` in Mathlib).
- **Used at.** Lemma 3.6.

### B9. Evens transfer / total Stiefel–Whitney class machinery  🟡 schematic
- **Statement.** The Evens multiplicative transfer and the Evens–Kahn formula for the total
  Stiefel–Whitney class of an induced/quadratic representation, used to normalize the half-orbit
  Evens class and compute the base Arf invariant over `𝔽₂[C]`.
- **Citation.** **Evens [9], *A generalization of the transfer map in the cohomology of groups*,
  Trans. AMS 108 (1963), 54–65** (the multiplicative transfer / norm); **Kahn [10], Invent. Math. 78
  (1984), 223–256**; **Kozlowski [11], *The Evens–Kahn formula for the total Stiefel–Whitney class*,
  Proc. AMS 91 (1984), 309–313**; **Guillot [6], *The computation of Stiefel–Whitney classes*, Ann.
  Inst. Fourier 60 (2010), 565–606** `[all quoted]`. Background: Brown [5], *Cohomology of Groups*.
- **Lean.** Schematic (no Stiefel–Whitney/Evens classes in Mathlib).
- **Used at.** §6 (Lemmas 6.13, 6.15, 6.8, 6.16, 6.21).

**Already discharged (not leaves).**
- **Ribes–Zalesskiĭ Hopfian** (a finitely generated profinite group is Hopfian): **RZ [4],
  *Profinite Groups*, 2nd ed. (2010), Proposition 2.5.2** `[confirmed]` (the paper cites "[4, §2.5]").
  *Proved* in this repo as `GQ2.profinite_hopfian` (standard axioms).
- **Schur–Zassenhaus** (§9.1 terminal case) — in Mathlib (`Mathlib.GroupTheory.SchurZassenhaus`);
  used via `GQ2.FiniteGroup.oddOrder_twoQuotient_split`, already proved.

---

## C. The paper's own intermediate nodes (check against the *paper*, not the literature)

These reduce eq. (154) to the leaves in §B. They are the paper's contribution; listed so a reviewer
can confirm the Lean statements (where present) match the paper, and see the dependency structure
(paper Appendix D, "Proof dependency certificate").

| paper node | statement (abbrev.) | reduces to | Lean |
|---|---|---|---|
| **Prop 1.1** | marked dyadic Demushkin normalization of `G_ℚ₂(2)`: `⟨a,s,y \| a²s⁴[s,y]=1⟩`, `ν_ur=(-2,1,0)` | B3, B4, B5, B7′ (via Lemmas 3.4–3.6) | — |
| **Prop 2.3** | `Sur(Γ_A,G) ↔` admissible marked quadruples `(σ,τ,x₀,x₁)∈G⁴` | (elementary, given `Γ_A`) | `admissibleCount`; hyp. `hΓA` |
| **Lemma 3.1** | finite `t^s=t²` quotient is `C_e⋊C_n`, normal 2-subgroups central | (finite group theory) | ✅ **proved** (`Tame.lean`) |
| **Prop 3.2** | `Γ_A/W_A ≅ T_tame ≅ G_ℚ₂/W_F` (common tame quotient) | Lemma 3.1 (tame side); B5 (local side) | tame side proved |
| **Lemma 3.3** | `T_tame` has no nontrivial closed normal pro-2 subgroup (`O₂ = W`) | (Lemma 3.1) | ✅ **proved** (`Tame.lean`) |
| **Thm 4.2** | boundary-framed exact-image count agrees for both sources (§9, induction on `\|L_Y\|`) | B6, B7, B7′, B8, B9 + §§5–8 finite calcs | — |
| **Lemma 10.1** | ordinary surjection set = disjoint union of fixed-frame sets over tame frames | Prop 3.2 | — |
| **eq. (154)** | `\|Sur(Γ_A,G)\| = \|Sur(G_ℚ₂,G)\|` | Thm 4.2 + Lemma 10.1 + Prop 2.3 | `main_surjection_count` |

Internal dependency chain feeding **Thm 4.2** (paper App. D), all *paper* lemmas resting on §B:
5.7/5.8 (Stokes) → 5.10 (Fox–Heisenberg chain map); 5.11/5.13 → 5.15 (elementary-module duality, uses
B6); 6.13 → Evens normalization (B9); 6.15 → 6.17 (deep-half vanishing); 6.8 → 6.9 (ramified Gauss
sign, B7′/B9); 6.16 → 6.18 (local ramified hyperbolicity, B7′); 6.21 → `B/T ≅ V⋊C` split; 8.6 →
half-torsor count; 8.9 (closed recursion (136)–(142)) → Thm 4.2.

---

## D. Status summary

| leaf | precise citation | conf. | Lean |
|---|---|---|---|
| B1  `G_ℚ₂` top. f.g. | Jannsen–Wingberg, Invent. Math. 70 (1982); NSW §7.5 (Thm 7.5.14, `p` odd) | ✓ source / ~ number | ✅ axiom |
| B2  2-adic cyclotomic surjective | Washington, *Cyclotomic Fields*, Thm 2.5; NSW §7.5 | ~ | ✅ axiom |
| B3  Demushkin classification | Labute [2], Thm 4 (case 2) & Thm 8 | **quoted** | 🟡 |
| B4  `G_ℚ₂(2)` is rank-3 Demushkin | Serre [3]; NSW §7.5 Thm 7.5.11; Labute [2] | ~ | 🟡 |
| B5  local reciprocity for `ℚ₂` | Serre *LF* Ch. XI–XII; NSW §7.1 | ~ | 🟡 |
| B6  local Tate duality | NSW Thm 7.2.6; Serre *GC* II §5.2; Milne *ADT* I.2.1 | ~ | 🟡 |
| B7  local Euler characteristic | NSW Thm 7.3.1; Serre *GC* II §5.7; Milne *ADT* I.2.8 | ~ | 🟡 |
| B7′ dyadic Hilbert symbol | Serre *Course in Arithmetic* Ch. III Thm 1; Serre *LF* Ch. XIV | ~ | 🟡 |
| B8  Galois action on `π₁(ℙ¹∖{0,1,∞})` | Stix [8]; Deligne, MSRI 16 (1989) §§8,15–19 | quoted / ~ | 🟡 |
| B9  Evens / Stiefel–Whitney | Evens [9]; Kahn [10]; Kozlowski [11]; Guillot [6] | **quoted** | 🟡 |
| — RZ Hopfian | RZ [4], Prop. 2.5.2 | **confirmed** | ✅ **proved** |
| — Schur–Zassenhaus | Mathlib | — | ✅ **proved** |

(`✓/quoted/confirmed` = reliable; `~` = my identification of the exact number, to confirm — see §E.)

**Bottom line for review.** The whole theorem rests on **nine** classical inputs (B1–B9); of the two
finite-group inputs that would also have appeared (RZ Hopfian, Schur–Zassenhaus) both are already
proved. B1–B2 are machine-checked faithful statements; B3–B9 are precise here but await Mathlib
infrastructure (Demushkin groups, continuous Galois cohomology + Tate duality, Hilbert symbols,
Stiefel–Whitney/Evens classes, étale `π₁`) before they can be stated faithfully in Lean.

---

## E. What is solid vs. what to confirm (and sources that would let me finalize)

**Solid (no action needed):**
- **B3, B9** — theorem numbers are taken verbatim from the paper's own citations.
- **RZ Hopfian = Prop. 2.5.2** — confirmed against a secondary source; and it's proved anyway.
- **B1 source** — the finite-generation result is Jannsen / Jannsen–Wingberg (1982); this is not in
  doubt, only the exact NSW cross-reference number is.

**To confirm — my identifications of exact numbers (marked `~` above).** These are standard results
whose *existence* is not in question; only the precise theorem number/section should be checked:
1. **NSW Thm 7.2.6** (local Tate duality, B6) and **Thm 7.3.1** (local Euler char, B7).
2. **NSW Thm 7.5.11** (`G_K(p)` Demushkin, B4) and **Thm 7.5.14** (the `p`-odd presentation cross-ref
   for B1); and the exact §/theorem for the **local reciprocity map** in NSW Ch. VII (B5).
3. **Serre, *Galois Cohomology*** II §5.2 (local duality) and II §5.7 (Euler char).
4. **Milne, *Arithmetic Duality Theorems*** I.2.1 (duality) and I.2.8 (Euler char).
5. **Serre, *Local Fields*** chapter numbers for local CFT (XI–XII) and the norm-residue/Hilbert
   symbol (XIV); and **Serre, *A Course in Arithmetic*** Ch. III Thm 1 for the explicit dyadic
   Hilbert symbol (B7′).
6. **Washington, *Introduction to Cyclotomic Fields*** Thm 2.5 for `Gal(ℚ(μ_{p^n})/ℚ) ≅ (ℤ/p^n)ˣ` (B2).

**Sources that would let me finalize every `~` above (in priority order):**
- **Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.** — single highest-value source;
  confirms B1, B4, B5, B6, B7 at once (Ch. VII).
- **Serre, *Galois Cohomology*** (Springer) — B6, B7 (Ch. II §5).
- **Milne, *Arithmetic Duality Theorems***, 2nd ed. — B6, B7 (Ch. I). *(freely available on Milne's
  website.)*
- **Serre, *Local Fields*** (GTM 67) and **Serre, *A Course in Arithmetic*** (GTM 7) — B5, B7′.
- **Washington, *Introduction to Cyclotomic Fields*** (GTM 83) — B2.

If you can drop any of these PDFs where I can read them, I'll replace every `~` with an exact,
verified theorem number and note the precise statement each gives.
