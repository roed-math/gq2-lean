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

### B1. `G_ℚ₂` is topologically finitely generated  ✅ faithful
- **Statement.** The absolute Galois group of a `p`-adic local field `K` is topologically finitely
  generated (by `[K:ℚ_p]+3` generators when `μ_p ⊆ K`; `[K:ℚ_p]+2` otherwise).
- **Citation.** NSW [1], §7.4 (following Jannsen–Wingberg).
- **Lean.** `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`.
- **Used at.** `main_presentation` (`hfgG`), feeding Lemma 2.5.

### B2. 2-adic cyclotomic character is surjective  ✅ faithful
- **Statement.** `χ_cyc : Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective; equivalently `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`.
- **Citation.** Classical (Gauss/Weber; NSW [1]).
- **Lean.** `GQ2.Foundations.cyclotomicCharacter_two_surjective` (via Mathlib `cyclotomicCharacter 2`).
- **Used at.** Lemma 3.6 (cyclotomic powering of the three peripheral inertia classes).

### B3. Classification of Demushkin groups (Labute)  🟡 schematic
- **Statement.** A Demushkin pro-`p` group (finitely generated one-relator pro-`p` group with
  `dim H²(G,𝔽_p) = 1` and non-degenerate cup product `H¹×H¹→H²`) is determined up to isomorphism by
  its rank `n = dim H¹` and its invariant `q` (with a secondary invariant in the exceptional dyadic
  case). For the rank-3, `q=2` dyadic normal form the relator can be taken as `A²S⁴[S,Y]`, and the
  canonical orientation character is computed explicitly.
- **Citation.** Labute [2], *Classification of Demushkin groups*, Thm 4 (case (2)) and Thm 8; see also
  Serre [3].
- **Lean.** Schematic (Mathlib has no `Demushkin` predicate; a faithful statement needs pro-`p`
  cohomology with cup products).
- **Used at.** Lemma 3.4 → Prop 1.1.

### B4. `G_ℚ₂(2)` is the rank-3 dyadic Demushkin group  🟡 schematic
- **Statement.** The maximal pro-2 quotient `G_ℚ₂(2)` of the absolute Galois group is a Demushkin
  group of rank `[ℚ₂:ℚ₂]+2 = 3` with `q = 2`; concretely `G_ℚ₂(2) ≅ ⟨A,S,Y | A²S⁴[S,Y]=1⟩_{pro-2}`.
- **Citation.** Demushkin; Serre [3]; NSW [1], §7.5 (structure of `G_K(p)` for local `K`). The
  concrete dyadic normal form is Labute [2] applied to these invariants.
- **Lean.** Schematic (needs the maximal pro-2 quotient of `G_ℚ₂` as an object; the *relator*
  `A²S⁴[S,Y]` itself is expressible in `FreeProfiniteGroup (Fin 3)` — it uses no `ω₂`).
- **Used at.** Lemma 3.4 → Prop 1.1.

### B5. Local reciprocity (local class field theory for `ℚ₂`)  🟡 schematic
- **Statement.** The local Artin/reciprocity map `rec : ℚ₂ˣ → G_ℚ₂^{ab}` is an injective homomorphism
  with dense image, normalized so that a uniformizer maps to (arithmetic) Frobenius, inducing
  `ℚ₂ˣ / N_{L/ℚ₂}(Lˣ) ≅ Gal(L/ℚ₂)` for finite abelian `L/ℚ₂`; on the cyclotomic quotient it recovers
  `χ_cyc(rec(u)) = u⁻¹`.
- **Citation.** Serre, *Local Fields* [7], Ch. VI; NSW [1], Ch. VII.
- **Lean.** Schematic (CFT provides abstract class-formation reciprocity `reciprocityIso`/`localInv`,
  but not the specific local Artin map `ℚ₂ˣ → G^{ab}`; `LocalCFT/` is early).
- **Used at.** Lemma 3.5 (marked abelianization, orientation, initial form).

### B6. Local Tate duality  🟡 schematic
- **Statement.** For a `p`-adic local field `K` and a finite `G_K`-module `M` (with `M' = Hom(M,μ)`
  the Tate dual), the cup product `H^i(G_K,M) × H^{2-i}(G_K,M') → H²(G_K,μ) ≅ ℚ/ℤ` is a perfect
  pairing of finite groups, for `i = 0,1,2`.
- **Citation.** NSW [1], Thm 7.2.6; Milne, *Arithmetic Duality Theorems*, Thm I.2.1.
- **Lean.** Schematic (needs continuous Galois cohomology of the profinite `G_K` and the cup-product
  pairing; Mathlib/CFT have finite-group `H^i` via `Rep R G` but not the continuous duality package).
- **Used at.** §5 (the three-term duality complex, Lemmas 5.11/5.13) and §9.2.

### B7. Local Euler–Poincaré characteristic  🟡 schematic
- **Statement.** For `K` `p`-adic and finite `G_K`-module `M`,
  `|H⁰(G_K,M)| · |H²(G_K,M)| / |H¹(G_K,M)| = ‖#M‖_K = (#M)^{-[K:ℚ_p]}` (the `p`-part). In particular
  for the elementary 2-modules `M` of §9.2 over `ℚ₂` this gives `H²=0` and `|Z¹(M)| = 2^{2·dim M}`.
- **Citation.** NSW [1], Thm 7.3.1; Serre, *Galois Cohomology*, Ch. II §5.7 (Tate).
- **Lean.** Schematic (same continuous-cohomology gap as B6).
- **Used at.** §9.2 (lifting through the elementary quotient `M`; strict decrease (145)).

### B7′. Dyadic Hilbert symbol formula  🟡 schematic
- **Statement.** For `ℚ₂` the Hilbert symbol `(·,·)₂ : ℚ₂ˣ/ℚ₂ˣ² × ℚ₂ˣ/ℚ₂ˣ² → {±1}` is given by
  `(2^α u, 2^β v)₂ = (-1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`, where `ε(u) = (u-1)/2 mod 2`,
  `ω(u) = (u²-1)/8 mod 2`. In the square-class basis `(-1,2,-3)` this yields `(-1,-1)₂ = -1`,
  `(2,-3)₂ = -1`, others trivial — the cup-product initial form `α² + βγ + γβ`.
- **Citation.** Serre, *Local Fields* [7], Ch. XIV; Serre, *A Course in Arithmetic*, Ch. III Thm 1.
- **Lean.** Schematic (Mathlib has no Hilbert symbol).
- **Used at.** Lemma 3.5 and §6 (base quadratic form, Arf invariant).

### B8. Galois action on `π₁(ℙ¹∖{0,1,∞})` and its peripheral structure  🟡 schematic
- **Statement.** The outer Galois action `G_ℚ → Out(Δ)` on the geometric maximal pro-2 fundamental
  group `Δ = π₁^{pro-2}(ℙ¹_{ℚ̄}∖{0,1,∞})` sends the three peripheral inertia generators `P,T,C` to
  cyclotomic conjugates (`φ_u(P) = c_P^{-1} P^u c_P`, etc., for `u ∈ ℤ₂ˣ`).
- **Citation.** Stix [8], *On cuspidal sections of algebraic fundamental groups*; Deligne, Ihara
  (tangential base points / cyclotomic character on inertia).
- **Lean.** Schematic (no étale/anabelian `π₁` in Mathlib).
- **Used at.** Lemma 3.6.

### B9. Evens transfer / total Stiefel–Whitney class machinery  🟡 schematic
- **Statement.** The Evens multiplicative transfer and the Evens–Kahn formula for the total
  Stiefel–Whitney class of an induced/quadratic representation, used to normalize the half-orbit
  Evens class and compute the base Arf invariant over `𝔽₂[C]`.
- **Citation.** Evens [9]; Kahn [10]; Kozlowski [11]; Guillot [6]. Background: Brown [5].
- **Lean.** Schematic (no Stiefel–Whitney/Evens classes in Mathlib).
- **Used at.** §6 (Lemmas 6.13, 6.15, 6.8, 6.16, 6.21).

**Already discharged (not leaves).**
- **Ribes–Zalesskiĭ Hopfian** (f.g. profinite ⇒ Hopfian), RZ [4, §2.5] — *proved* as
  `GQ2.profinite_hopfian` (standard axioms).
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

| leaf | citation | Lean status |
|---|---|---|
| B1  `G_ℚ₂` top. f.g. | NSW [1] §7.4 | ✅ faithful axiom |
| B2  2-adic cyclotomic surjective | classical / NSW [1] | ✅ faithful axiom |
| B3  Demushkin classification | Labute [2] Thm 4,8 | 🟡 schematic |
| B4  `G_ℚ₂(2)` is rank-3 Demushkin | Serre [3], NSW [1] §7.5, Labute [2] | 🟡 schematic |
| B5  local reciprocity for `ℚ₂` | Serre [7] Ch. VI, NSW [1] Ch. VII | 🟡 schematic |
| B6  local Tate duality | NSW [1] Thm 7.2.6 | 🟡 schematic |
| B7  local Euler characteristic | NSW [1] Thm 7.3.1 | 🟡 schematic |
| B7′ dyadic Hilbert symbol | Serre [7] Ch. XIV | 🟡 schematic |
| B8  Galois action on `π₁(ℙ¹∖{0,1,∞})` | Stix [8] | 🟡 schematic |
| B9  Evens / Stiefel–Whitney | Evens [9], Kahn [10], Guillot [6] | 🟡 schematic |
| — RZ Hopfian | RZ [4] §2.5 | ✅ **proved** (`profinite_hopfian`) |
| — Schur–Zassenhaus | Mathlib | ✅ **proved** (in repo) |

**Bottom line for review.** The whole theorem rests on **nine** classical inputs (B1–B9); of the two
finite-group inputs that would also have appeared (RZ Hopfian, Schur–Zassenhaus) both are already
proved. B1–B2 are machine-checked faithful statements; B3–B9 are precise here but await Mathlib
infrastructure (Demushkin groups, continuous Galois cohomology + Tate duality, Hilbert symbols,
Stiefel–Whitney/Evens classes, étale `π₁`) before they can be stated faithfully in Lean.

*Please flag any citation whose theorem number or statement is off — those are my best identifications
and are the point of this review.*
