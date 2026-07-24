# Literature axioms for Theorem 1.2 — reviewer's enumeration

**Purpose.** This document reduces the formalization of the paper *A Profinite Presentation of the
Absolute Galois Group of `ℚ₂`* (D. C. Turturean, 2026) to a **minimal list of classical results that
already exist in the literature**, and enumerates them with precise statements and citations. It is
meant for a quick expert check: *does each "leaf" below correctly match a known
theorem in the cited reference?*

> **Update (T-20):** all leaves are now *stated in Lean* (current census: **nine** axioms) — see
> [`review-packet.md`](orchestration/review-packet.md) for the Lean axiom name per leaf, the consolidated
> deviations table, and mechanical verification instructions.  The citations and per-result
> discussion below remain the authoritative literature reference.

**Scope of the reduction.** The paper's *own* §§3–9 argument (its Propositions and Lemmas) is
**granted** here — those are the paper's contribution, not literature, and are listed separately in
§C so you can also check they match the *paper*. What we isolate in §B are the **classical
foundations** the paper builds on. If every item in §B is a correct citation and every node in §C is
faithful to the paper, then (modulo the routine profinite assembly noted in §A) Theorem 1.2 follows.

**Lean status legend.**
- ✅ **faithful** — stated as a typechecked Lean `axiom`/`theorem` against current Mathlib, in
  `GQ2/Foundations/Axioms.lean` (or already *proved*, in which case it is not a leaf at all).
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
**Citation-confidence markers** (see §E for the status summary):
`[✓ source-audited]` checked directly against the cited PDF (exact theorem number and statement;
the audit copies are not vendored in this repository); `[quoted]` the paper itself cites this exact result; `[confirmed]`
checked against a reliable secondary source; `[likely]` my identification of a standard result, source
not yet to hand.

### B1. `G_ℚ₂` is topologically finitely generated  ✅ faithful
- **Statement.** The absolute Galois group of a `p`-adic local field `K` is topologically finitely
  generated; NSW gives `[K:ℚ_p]+2` generators.
- **Citation.** **NSW [1], Ch. VII §7.4, Theorem (7.4.1)** `[✓ source-audited]` — verbatim,
  for a `p`-adic local field `k` of degree `N`, `G_k` is generated by `N+2` elements.  This applies
  at `p=2`.  Jannsen, *Invent. Math.* 70 (1982), 53–69, Satz 3.2 + Lemma 3.3 gives the weaker
  `N+3` bound, which also implies the Lean statement.  NSW (7.5.14) is not the right direct
  citation here: its surrounding subsection assumes `p ≠ 2`.
- **Lean.** `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`.
- **Used at.** `main_presentation` (`hfgG`), feeding Lemma 2.5.

### B2. 2-adic cyclotomic character is surjective  ✅ faithful · **DELETED 2026-07-09 (unused)**
- **Statement.** `χ_cyc : Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective; equivalently `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`.
- **Citation.** **Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Ch. 2,
  Theorem 2.5** `[✓ verified in the provided source]` — verbatim: `deg(ℚ(ζ_n)/ℚ) = φ(n)` and
  `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ`, with `a` corresponding to `ζ_n ↦ ζ_n^a` (the cyclotomic character).
  Taking `n = 2^k` and the inverse limit gives `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`, whence surjectivity.
- **Lean.** ~~`GQ2.Foundations.cyclotomicCharacter_two_surjective`~~ — **deleted 2026-07-09**
  (census decision, B12 board; census 15 → 13 together with the B12 discharge).
- **Used at.** Nothing — it never acquired a Lean consumer (adversarial review 2026-07-04, §4):
  Lemma 3.6 enters through **B8** (`peripheralCyclotomicAction`), which bundles its own
  cyclotomic-surjectivity need (carried in the census by B5's `χ_cyc∘rec = (·)⁻¹`).  Retained
  2026-07-04 → 2026-07-09 as B8's citation companion, then deleted as unused; this entry stays as
  the citation record.

### B3. Classification of Demushkin groups (Labute)  🟡 schematic
- **Statement.** A Demushkin pro-`p` group (finitely generated one-relator pro-`p` group with
  `dim H²(G,𝔽_p) = 1` and non-degenerate cup product `H¹×H¹→H²`) is determined up to isomorphism by
  its rank `n = dim H¹` and its invariant `q` (with a secondary invariant in the exceptional dyadic
  case). For the rank-3, `q=2` dyadic normal form the relator can be taken as `A²S⁴[S,Y]`, and the
  canonical orientation character is computed explicitly.
- **Citation.** **Labute [2], Theorem 8** (§5, "the group of the maximal `p`-extension of a local
  field") `[✓ verified in the provided source]`: for `q=2` and `d=[K:ℚ_p]` odd, `G_K(2)` is defined
  by `d+2` generators `x₁,…,x_{d+2}` with the single relation `x₁²x₂⁴[x₂,x₃][x₄,x₅]⋯=1`. For `K=ℚ₂`
  (`d=1`, odd) this is `⟨x₁,x₂,x₃ | x₁²x₂⁴[x₂,x₃]=1⟩` — **exactly the paper's `D₀=⟨A,S,Y|A²S⁴[S,Y]=1⟩`**.
  **Theorem 4, case (2)** (`q=2`, `n` odd) `[✓ verified]`: the canonical character `χ(x₁)=−1`,
  `χ(x₃)=(1−2^f)^{-1}`, `χ(x_i)=1` otherwise — the paper's `−1, 1, (1−2^f)^{-1}`. Labute attributes
  Theorem 8 to Serre [3]. (Canad. J. Math. 19 (1967), 106–132.)
- **Lean.** Schematic (Mathlib has no `Demushkin` predicate; a faithful statement needs pro-`p`
  cohomology with cup products).
- **Axiom form (B3c), a composite interface** (adversarial review 2026-07-04, §3): the axiomatized
  *orientation* half `GQ2.dyadicOrientation` is **not** a bare Labute citation — it bundles Labute's
  Thm 4(2) values *plus* the local-Galois fact (the Demushkin dualizing character equals the
  cyclotomic character, through *this* quotient map) *plus* the choice of a normalized B4
  isomorphism, and therefore **subsumes a marked B4**.  See its docstring and the classification
  table (`docs/orchestration/review-packet.md` §2).
- **Used at.** Lemma 3.4 → Prop 1.1.

### B4. `G_ℚ₂(2)` is the rank-3 dyadic Demushkin group  🟡 schematic · **DELETED 2026-07-10 (unused — B3c subsumes a marked B4)**
- **Statement.** The maximal pro-2 quotient `G_ℚ₂(2)` of the absolute Galois group is a Demushkin
  group of rank `[ℚ₂:ℚ₂]+2 = 3` with `q = 2`; concretely `G_ℚ₂(2) ≅ ⟨A,S,Y | A²S⁴[S,Y]=1⟩_{pro-2}`.
- **Citation.** **NSW [1], Ch. VII §7.5, Theorem (7.5.11)(ii)** `[✓ verified in the provided NSW]` —
  verbatim: if `μ_p ⊆ k` then `G_k(p)` is a Poincaré group of dimension 2 (i.e. a Demushkin group)
  of rank `N+2` (`N=[k:ℚ_p]`), with dualizing module the group of `p`-power roots of unity in `k(p)`.
  For `k=ℚ₂`: `p=2`, `N=1`, `μ_2={±1}⊆ℚ₂`, so **rank `1+2 = 3`** ✓. The explicit relation is
  **Labute [2], Theorem 8** at `d=1`: `⟨A,S,Y | A²S⁴[S,Y]=1⟩` `[✓ verified]` (= the paper's `D₀`).
  Also **Serre [3]**, Sém. Bourbaki 252 (1962/63); **Demushkin**.
- **Lean.** Schematic (needs the maximal pro-2 quotient of `G_ℚ₂` as an object; the *relator*
  `A²S⁴[S,Y]` itself is expressible in `FreeProfiniteGroup (Fin 3)` — it uses no `ω₂`).
- **Used at.** Lemma 3.4 → Prop 1.1.

### B5. Local reciprocity (local class field theory for `ℚ₂`)  🟡 schematic
- **Statement.** The local Artin/reciprocity map `rec : ℚ₂ˣ → G_ℚ₂^{ab}` is an injective homomorphism
  with dense image, normalized so that a uniformizer maps to (arithmetic) Frobenius, inducing
  `ℚ₂ˣ / N_{L/ℚ₂}(Lˣ) ≅ Gal(L/ℚ₂)` for finite abelian `L/ℚ₂`; on the cyclotomic quotient it recovers
  `χ_cyc(rec(u)) = u⁻¹`.
- **Citation.** **NSW [1], Ch. VII §7.1: Theorem (7.1.1) (Class Field Axiom) and Corollary (7.1.5)**
  `[✓ verified in the provided NSW]` — (7.1.5): `(G_k, k̄ˣ)` is a class formation, whence the local
  reciprocity/norm-residue homomorphism `k ˣ → G_k^{ab}` (and (7.1.9) for the `p`-adic case).
  Secondary: **Serre, *Local Fields* [7], Part IV, Ch. XI–XII** (Class Formations / Local CFT)
  `[likely; corrects an earlier "Ch. VI" typo]`. Normalization (uniformizer ↦ arith. Frobenius):
  paper Lemma 3.5.
- **Lean.** Schematic (CFT provides abstract class-formation reciprocity `reciprocityIso`/`localInv`,
  but not the specific local Artin map `ℚ₂ˣ → G^{ab}`; `LocalCFT/` is early).
- **Used at.** Lemma 3.5 (marked abelianization, orientation, initial form).

### B6. Local Tate duality  🟡 schematic  *(base-generalized to all finite `k/ℚ₂`, 2026-07-06)*
- **Statement.** For a `p`-adic local field `K` and a finite `G_K`-module `M` (with `M' = Hom(M,μ)`
  the Tate dual), the cup product `H^i(G_K,M) × H^{2-i}(G_K,M') → H²(G_K,μ) ≅ ℚ/ℤ` is a perfect
  pairing of finite groups, for `i = 0,1,2`.
- **Citation.** **NSW [1], Ch. VII §7.2, Theorem (7.2.6) "Tate Duality"** `[✓ verified in the
  provided NSW]` — verbatim: for a `p`-adic local field `k`, finite `G_k`-module `A`, `A₀=Hom(A,μ)`,
  the cup product `H^i(k,A₀) × H^{2-i}(k,A) → H^2(k,μ) ≅ ℚ/ℤ` induces isomorphisms of finite abelian
  groups `H^i(k,A₀) ≅ H^{2-i}(k,A)*` for `0 ≤ i ≤ 2`. Also **Serre, *Galois Cohomology*, Ch. II §5.2,
  Theorem 2** `[✓ verified in the provided source]` (same cup-product duality; "due to Tate"); Milne,
  *ADT*, Ch. I, Thm I.2.1. Original: Tate.  **The citation is already stated for arbitrary `p`-adic
  `k`** — the Lean encoding was `ℚ₂`-only and is now base-generalized to match (below).
- **Lean.** The bundle `TateDualityAt G n` over a group `G` realized as an open finite-index local
  Galois subgroup of `G_ℚ₂` (`inv : H²(G,μₙ) ≅ ℤ/n`, the three degree-pair perfectness clauses);
  axiom `GQ2.tateDualityAt` quantifies over such `G`, gated by an open topological embedding
  `G ↪ G_ℚ₂` with finite-index image
  (identity for `G = G_ℚ₂`, subgroup inclusion for `G = G_K`).  The old `ℚ₂`-only
  `GQ2.tateDuality : TateDuality n` is now an in-repo `def` = the `G = G_ℚ₂` member (no consumer
  churn: `TateDuality n := TateDualityAt G_ℚ₂ n`).  **Census unchanged** — one axiom, base-generalized
  in place (the B9/B11 2026-07-03 pattern).  (Same continuous-cohomology encoding decisions as before;
  Mathlib/CFT lack the continuous duality package, so the perfectness is still asserted, not derived.)
- **Induced Hilbert pairing** (the symbol-side content used by the K-level consumer): at `n=2`,
  `B := inv_K ∘ cup` is the mod-2 Hilbert pairing on `K^×/2 ≅ H¹(G_K,𝔽₂)`; its **nondegeneracy** is
  **FV [11] Ch. IV §5 Prop (5.1)(6) + Corollary p.145** and **Theorem (5.2)** (perp-biduality
  `A = A^⊥⊥ = N_{L/K}L^×`) `[✓ verified 2026-07-06]`, independently **O'Meara [O] ITQF 63:13**
  `[✓]`, and Serre LF **XIV §1 Prop 3 Corollary** `[✓]`; bilinearity/Galois-equivariance are
  (5.1)(1)/(9).
- **Used at.** §5 (the three-term duality complex, Lemmas 5.11/5.13), §9.2, and **§6.3 P-15f7**
  (the `(1,1)` pairing at `G_K = ker ρ` is the invariant nondegenerate `B` of
  `GQ2.card_equivHoms_deep_eq_quot`, `GQ2/DeepDuality.lean`; proposal
  `docs/orchestration/p15f7-axiom-proposal.md`).

### B7. Local Euler–Poincaré characteristic  🟡 schematic
- **Statement.** For `K` `p`-adic and finite `G_K`-module `M`,
  `|H⁰(G_K,M)| · |H²(G_K,M)| / |H¹(G_K,M)| = ‖#M‖_K = (#M)^{-[K:ℚ_p]}` (the `p`-part). In particular
  for the elementary 2-modules `M` of §9.2 over `ℚ₂` this gives `H²=0` and `|Z¹(M)| = 2^{2·dim M}`.
- **Citation.** **NSW [1], Ch. VII §7.3, Theorem (7.3.1) (Tate)** `[✓ verified in the provided NSW]`
  — verbatim: for every finite `G_k`-module `A` of order `a` prime to `char(k)`, `χ(k,A) = ‖a‖_k`
  (the normalized absolute value); so `|H⁰||H²|/|H¹| = ‖a‖_k = a^{-[k:ℚ_p]}` (`p`-part). Also
  **Serre, *Galois Cohomology*, Ch. II §5.7, Theorem 5** `[✓ verified in the provided source]`
  (`χ(A)=‖a‖_k`, Tate; `χ` defined in §5.4; the `𝔽_p`-coefficient form `ϱ(A)=-N·dim A` is Exercise 2,
  p. 101 — exactly the `|Z¹|=2^{2·dim M}` input of §9.2); Milne, *ADT*, Ch. I, Thm I.2.8.
- **Lean.** Schematic (same continuous-cohomology gap as B6).
- **Used at.** §9.2 (lifting through the elementary quotient `M`; strict decrease (145)).

### B7′. Dyadic Hilbert symbol formula  ✅ faithful · **DISCHARGED — proved in-repo 2026-07-09**
- **Statement.** For `ℚ₂` the Hilbert symbol `(·,·)₂ : ℚ₂ˣ/ℚ₂ˣ² × ℚ₂ˣ/ℚ₂ˣ² → {±1}` is given by
  `(2^α u, 2^β v)₂ = (-1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`, where `ε(u) = (u-1)/2 mod 2`,
  `ω(u) = (u²-1)/8 mod 2`. In the square-class basis `(-1,2,-3)` this yields `(-1,-1)₂ = -1`,
  `(2,-3)₂ = -1`, others trivial — the cup-product initial form `α² + βγ + γβ`.
- **Citation.** **Serre, *A Course in Arithmetic*, GTM 7, Ch. III (Hilbert symbol) §1.2, Theorem 1**
  `[✓ verified in the provided source]` — verbatim, for `k=ℚ_p`, `a=p^α u`, `b=p^β v` (`u,v ∈ U`):
  `(a,b) = (-1)^{ε(u)ε(v) + αω(v) + βω(u)}` when `p=2`, where **`ε(u) ≡ (u-1)/2`, `ω(u) ≡ (u²-1)/8`
  (mod 2)** are defined in Ch. II §3.3 (p. 18) — exactly the paper's Lemma 3.5 formula.
- **Lean.** `GQ2.HilbertSymbol.hilbertSymbol_dyadic` — since 2026-07-09 a same-name **theorem**
  (zero consumer churn, the B11/B12 precedent), proved **std-3** (no B-axioms) in the
  `DyadicSquares` → `HilbertSymbolDyadic` → `Necessity`/`Sufficiency` →
  `HilbertSymbolDyadicClose` lane: the 2-adic Hensel square criterion, the norm-form identity
  `(a,b) = (a,−ab)` (killing the `(2u,2v)` family), a primitivity-descent mod-transfer engine,
  and finite mod-8 `decide`s (B7′ board, `docs/orchestration/b7prime-tickets.md` /
  `b7prime-proof-plan.md`; census 13 → 12, user-approved 2026-07-09).
- **Used at.** Lemma 3.5 and §6 (base quadratic form, Arf invariant).

### B8. Galois action on `π₁(ℙ¹∖{0,1,∞})` and its peripheral structure  🟡 schematic · composite
- **Statement.** The outer Galois action `G_ℚ → Out(Δ)` on the geometric maximal pro-2 fundamental
  group `Δ = π₁^{pro-2}(ℙ¹_{ℚ̄}∖{0,1,∞})` sends the three peripheral inertia generators `P,T,C` to
  cyclotomic conjugates (`φ_u(P) = c_P^{-1} P^u c_P`, etc., for `u ∈ ℤ₂ˣ`).
- **Composite** (adversarial review 2026-07-04, §1): the Stix citation supports the *action through
  the cyclotomic character*; producing an automorphism for **every** `u ∈ ℤ₂ˣ` additionally needs
  cyclotomic surjectivity (B5's `χ_cyc∘rec = (·)⁻¹` locally; the global companion B2 was deleted
  2026-07-09 as unused).  The statement is kept
  in all-units form (P-22, user decision); weakening to the cyclotomic image was declined.
- **Citation.** **Stix [8], §3.3 ("Cusps and inertia subgroups") and Definition 37 ("local
  orientation at each cusp")** `[✓ verified in the provided source]` — exactly the paper's citation
  `[8, Section 3.3 and Definition 37]`: the decomposition group of a rational cusp acts on the
  procyclic inertia group through the cyclotomic character. (Full ref: J. Stix, *On cuspidal sections
  of algebraic fundamental groups*, in *Galois–Teichmüller Theory and Arithmetic Geometry*, ASPM 63
  (2012), 519–563.) The paper does **not** cite Deligne; the classical *origin* of the cyclotomic
  inertia action is Deligne, *Le groupe fondamental de la droite projective moins trois points*, in
  *Galois Groups over ℚ* (Ihara–Ribet–Serre, eds.), MSRI Publ. 16 (1989), §§8, 15–19.
- **Lean.** Schematic (no étale/anabelian `π₁` in Mathlib).
- **Used at.** Lemma 3.6.

### B9. Evens transfer / total Stiefel–Whitney class machinery  🟡 schematic
- **Statement.** The Evens multiplicative transfer and the Evens–Kahn formula for the total
  Stiefel–Whitney class of an induced/quadratic representation, used to normalize the half-orbit
  Evens class and compute the base Arf invariant over `𝔽₂[C]`.
- **Citation** (precise; verified against the provided PDFs):
  * **Evens norm** `N_{H→G} : H²(H,k) → H²(G,k)`, with `N(1+x) = 1 + tr_{H→G}(x) + N(x)` for index 2,
    and its double-coset (Mackey) restriction formula: **Evens [9], §§4–5, Theorem 1**
    `[✓ verified]` (Trans. AMS 108 (1963), 54–65).
  * **Total SW class of a transferred quadratic form**: **Kahn [10], Théorème 2**
    `w(T(q)) = N′(w(q))·w(T(1))^r` — with **Théorème 1** (induced reps `w(Ind ρ)=N′(w(ρ))w(Ind1)^r`)
    and **Théorème 3** `w(T⟨a⟩)=w(Ind ρ_a)(1+(2,d))`; topological version **Théorème 1.3.2**
    `[✓ verified]` (Invent. Math. 78 (1984), 223–256).
  * **Index-2 Evens–Kahn formula** (total SW class of an index-2 induced rep): **Kozlowski [11],
    Theorem 1.1** (index-2 special case) (Proc. AMS 91 (1984), 309–313).  The exact 1984 paper
    was not independently obtainable in the 2026-07-12 audit; Kahn's verified Theorem 2 is the
    direct load-bearing source, and a later paper by Kozlowski corroborates this attribution.
  The paper's eq. (111) `w(Tr_{L/k}⟨a⟩) = w(Tr_{L/k}⟨1⟩)(1 + cor_{L/k}[a] + N^{Ev}_{L/k}[a])` is
  Kahn Th. 2 at `q=⟨a⟩` (rank 1) expanded via Evens Th. 1. **Guillot [6]** is a *background* reference
  (in the bibliography only — no body citation).
- **Lean.** Schematic (no Stiefel–Whitney/Evens classes in Mathlib).
- **Used at.** §6 (Lemmas 6.13 (Evens norm normalization), 6.16 (deep-unit Evens norm)); the
  Shapiro–corestriction of Lemma 6.15 is Kahn Th. 2's Shapiro case.

**Already discharged (not leaves).**
- **Ribes–Zalesskiĭ Hopfian** (a finitely generated profinite group is Hopfian): **RZ [4],
  *Profinite Groups*, 2nd ed. (2010), Proposition 2.5.2** `[confirmed]` (the paper cites "[4, §2.5]").
  *Proved* in this repo as `GQ2.profinite_hopfian` (standard axioms).
- **Schur–Zassenhaus** (§9.1 terminal case) — in Mathlib (`Mathlib.GroupTheory.SchurZassenhaus`);
  used via `GQ2.FiniteGroup.oddOrder_twoQuotient_split`, already proved.


### B10–B11b (added post-freeze)  ✅ faithful
Recorded in §E below and in `orchestration/review-packet.md` §2 (the census-amendment history): **B10**
(oriented tame quotient, NSW (7.5.3)/(7.5.2) + Serre LF XIII §4 Prop. 13 and its corollary),
**B11a** (norm criterion, Serre LF XIV §2 Props. 4(iii), 5, 7(iii)), ~~**B11b**~~
(unramified units are norms, Serre LF V §2 Prop. 3 +
Cor. + Rem. 1) — **B11b discharged 2026-07-09** (B11b board): now a same-name std-3 **theorem**,
proved in-repo (`GQ2/UnramifiedQuadraticNorms.lean` + `GQ2/TeichmullerLift.lean`) by completing
the square + a depth-by-depth norm-form approximation against the B13 filtration, so
`dyadicNormCriterion` now rests on **B11a alone**.

### B12. Local Kummer theory (surjective half)  ✅ faithful · **DISCHARGED — proved in-repo 2026-07-09**
- **Statement.** For `k` finite over `ℚ₂`, the Kummer class map descends to an isomorphism
  `k^×/(k^×)² ≅ H¹(G_k, ℤ/2)`.  Was leafed: **surjectivity only** — injectivity is proved
  (`Kummer.kummerClass_eq_zero_iff`, via Mathlib's infinite Galois correspondence).
- **Citation** (kept for the record). **NSW [1], Ch. VI §2: Theorem (6.2.1) (Hilbert's Satz 90) +
  the Kummer-sequence isomorphism `H¹(G_K, μ_n) ≅ K^×/K^{×n}` displayed immediately after it
  (electronic ed. p. 344); dual form Theorem (6.2.2)** `[✓ verified in the provided NSW]`.
  Secondary: **Serre LF [7], Ch. XIV §2 (p. 206)** — `K*/K*ⁿ ≅ {characters of order ∣ n}`
  (construction Ch. X §3) `[✓ verified in the provided scan]`.
- **Lean.** `GQ2.kummerClassK_surjective` — since 2026-07-09 a same-name **theorem** (zero
  consumer churn, the B11 precedent), proved **std-3** (no B-axioms) in
  `GQ2/KummerSurjectivity.lean` + `GQ2/KummerKrullBridge.lean`: completing the square + the
  Krull–Galois correspondence (B12 board, `docs/orchestration/b12-tickets.md` /
  `b12-proof-plan.md`; census 15 → 13 together with the B2 deletion).
- **Used at.** Lemma 6.17 (P-15f1: transport of the unit filtration to `H¹(G_K, 𝔽₂)`); §6.3.

### B13. Dyadic unit-filtration graded structure  ✅ faithful · **DISCHARGED — proved in-repo 2026-07-09**
- **Statement.** `k` finite over `ℚ₂`, `U^{(i)} = 1 + 𝔭_k^i`: a uniformizer exists (value-group
  discreteness), `‖2‖ = ‖π‖^e` (`e ≥ 1`), and the graded counts `#(U^{(0)}/U^{(1)}) = 2^f − 1`,
  `#(U^{(i)}/U^{(i+1)}) = 2^f` (`i ≥ 1`), `f ≥ 1` the residue degree.
- **Citation.** **Serre LF [7], Ch. IV §2, Prop. 6** `[✓ verified verbatim, pp. 66–67]`
  (graded pieces `≅ k̄^×` at depth 0 and `≅ k̄⁺` at depth `i ≥ 1`); uniformizer existence:
  Serre LF Ch. I–II (standard).  NB the paper's own bracket for (93)/(94) ("[7, Ch. XIV
  §§2–3]") is coarse — the filtration is Ch. IV §2.
- **Lean.** `GQ2.dyadicUnitFiltration : DyadicUnitFiltration k` — since 2026-07-09 a same-name
  **`noncomputable def`** (zero consumer churn, the B7′/B11/B12 precedent), proved **std-3**
  (`Classical.choice` only — it pulls witnesses from the existence lemmas) in the
  `UnitFiltrationTop` → `UnitFiltrationCounts` lane: the uniformizer from compactness of the unit
  ball + an `O/2O` pigeonhole (no spectral-norm value formula), the finite residue field `O/𝔪`,
  and the two graded counts as explicit isomorphisms `U^{(0)}/U^{(1)} ≅ (O/𝔪)ˣ` and
  `U^{(i)}/U^{(i+1)} ≅ (O/𝔪)⁺` (B13 board, `docs/orchestration/b13-tickets.md` /
  `b13-proof-plan.md`; census 12 → 11, user-approved 2026-07-09).  The structure bundle lives in
  `GQ2/UnitFiltration.lean` (spectral-norm vocabulary, no valuation ring is constructed).
  Excluded because provable: the square-class graded computation (93),
  `U^{(2e+1)} ⊆ squares` (= `sq_of_near_one`, proved P-15e), `−1 ∈ U^{(e)}`, the graded
  duality, Lemma 6.10, and the proposal's (F2) inertia-twist clause (found derivable from the
  `he` normalization during statement design — `docs/orchestration/p15f1-axiom-proposal.md`).
- **Used at.** Lemma 6.17 dim clause (P-15f1 `DeepKummerData` instantiation).

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
| **Prop 3.2** | `Γ_A/W_A ≅ T_tame ≅ G_ℚ₂/W_F` (common tame quotient) | Lemma 3.1 (tame side); **B10** (local side; Lemma 3.3 maximality stays a theorem) | statements P-06 (`SectionThree.lean`) |
| **Lemma 3.3** | `T_tame` has no nontrivial closed normal pro-2 subgroup (`O₂ = W`) | (Lemma 3.1) | ✅ **proved** (`Tame.lean`) |
| **Thm 4.2** | boundary-framed exact-image count agrees for both sources (§9, induction on `\|L_Y\|`) | B6, B7, B7′, B8, B9 + §§5–8 finite calcs | — |
| **Lemma 10.1** | ordinary surjection set = disjoint union of fixed-frame sets over tame frames | Prop 3.2 | — |
| **eq. (154)** | `\|Sur(Γ_A,G)\| = \|Sur(G_ℚ₂,G)\|` | Thm 4.2 + Lemma 10.1 + Prop 2.3 | `main_surjection_count` |

**Verified footprints (P-20, 2026-07-05).**  The "reduces to" column above records the *paper's*
claim; the machine-checked per-node `#print axioms` footprints are tabulated in
[`review-packet.md`](orchestration/review-packet.md) §5 (and computed whole-library by `GQ2/AxiomLedger.lean`).
Two are **tighter** than the claim: **Prop 1.1** is `{B3c, B8}` (not `B3,B4,B5,B7′` — B3c subsumes a
marked B4, and B5/B7′ enter at the `lemma_3_5_hilbert_ledger` sub-node), and **Prop 5.15** is
**std-3** (the §C annotation "uses B6" is discharged at `prop_5_16` instead, where `H²` is computed).
**Prop 3.2** (local) is `{B10}` as §C states — note the `AxiomLedger.lean` header's older
"Prop 3.2 → B5" predates the B10 census decision.

Internal dependency chain feeding **Thm 4.2** (paper App. D), all *paper* lemmas resting on §B:
5.7/5.8 (Stokes) → 5.10 (Fox–Heisenberg chain map); 5.11/5.13 → 5.15 (elementary-module duality, uses
B6); 6.13 → Evens normalization (B9); 6.15 → 6.17 (deep-half vanishing); 6.8 → 6.9 (ramified Gauss
sign, B7′/B9); 6.16 → 6.18 (local ramified hyperbolicity, B7′); 6.21 → `B/T ≅ V⋊C` split; 8.6 →
half-torsor count; 8.9 (closed recursion (136)–(142)) → Thm 4.2.

---

## D. Status summary

| leaf | precise citation | conf. | Lean |
|---|---|---|---|
| B1  `G_ℚ₂` top. f.g. | **NSW (7.4.1)** (`N+2` generators; valid at `p=2`) | ✅ **verified** | ✅ axiom |
| B2  2-adic cyclotomic surjective | Washington, *Cyclotomic Fields*, **Ch. 2 Thm 2.5** | ✅ **verified** | ❌ **deleted 2026-07-09** (unused) |
| B3  Demushkin classification | **Labute [2] Thm 8** (`D₀` at `d=1`) & **Thm 4 case (2)** | ✅ **verified** | 🟡 |
| B4  `G_ℚ₂(2)` is rank-3 Demushkin | **NSW (7.5.11)(ii)** (rank `N+2=3`); Serre [3]; Labute [2] | ✅ **verified** | ❌ **deleted 2026-07-10** (unused; B3c subsumes a marked B4) |
| B5  local reciprocity for `ℚ₂` | **NSW (7.1.1)/(7.1.5)** (class formation); Serre *LF* XI–XII | ✅ **verified** | 🟡 |
| B6  local Tate duality (all finite `k/ℚ₂`) | **NSW (7.2.6) "Tate Duality"**; Serre *GC* II §5.2; Milne I.2.1; induced Hilbert nondeg.: **FV IV §5 (5.1)(6)/(5.2)**, O'Meara **63:13** | ✅ **verified** | 🟡 |
| B7  local Euler characteristic | **NSW (7.3.1) (Tate)** `χ=‖a‖`; Serre *GC* II §5.7; Milne I.2.8 | ✅ **verified** | 🟡 |
| B7′ dyadic Hilbert symbol | **Serre *Course in Arithmetic* Ch. III §1.2 Thm 1** (`ε,ω`: Ch. II §3.3) | ✅ **verified** | ✅ **proved** (2026-07-09) |
| B8  Galois action on `π₁(ℙ¹∖{0,1,∞})` | **Stix [8] §3.3 + Def 37** (Deligne MSRI 16: classical origin) | ✅ **verified** | ✅ axiom (bundle) |
| B9  Evens / Stiefel–Whitney | **Evens [9] §§4–5 Thm 1**; **Kahn [10] Thm 1–3**; **Kozlowski [11] Thm 1.1** (Guillot [6]: background only) | ✅ **verified** | 🟡 |
| B10 tame quotient of `G_ℚ₂` (**oriented**, B10′ since 2026-07-06) | **NSW (7.5.3) (Iwasawa)** with (7.5.2); Serre *LF* Ch. IV (wild pro-`p`); orientation clauses: **Serre *LF* XIII §4 Prop. 13 + cor.** (units ↦ inertia, prime ↦ Frobenius) + **Neukirch ANT V (1.2)** / NSW (7.1.2)(i) (units are unramified norms) | ✅ **verified** | ✅ axiom (bundle) |
| — RZ Hopfian | RZ [4], Prop. 2.5.2 | **confirmed** | ✅ **proved** |
| — Schur–Zassenhaus | Mathlib | — | ✅ **proved** |

(`✅ verified` = checked against the cited source PDF; audit copies are not vendored in this
repository. `quoted` = taken from the paper's own citation; `confirmed` = checked against a
reliable secondary source; `~` = identification made without the primary source to hand.)

**Bottom line for review.** The whole theorem rests on **nine** active classical interfaces
(B1, B3c, B5–B11a — B10 added post-kickoff by the P-06 census decision, B11–B13 by the
P-15/P-23/P-15f1 census decisions; **B12 discharged in-repo as a same-name std-3 theorem and the
unused B2 deleted**, B12-board census flip, user-approved 2026-07-09; **B7′, B13, and B11b likewise
discharged in-repo** (B13 a same-name `noncomputable def` over the `UnitFiltrationTop`/`Counts`
lane; B11b a same-name theorem over the norm-form engine `UnramifiedQuadraticNorms`/`TeichmullerLift`;
the never-consumed **B4 deleted 2026-07-10** (user-approved; census 10 → 9, citation record in its §B4 above),
so `dyadicNormCriterion` rests on B11a alone), B7′-, B13-, and B11b-board census flips,
user-approved 2026-07-09); of the two
finite-group inputs that would also have appeared (RZ Hopfian, Schur–Zassenhaus) both are already
proved.  The active declarations are faithful project interfaces over the repository's encodings;
B3c, B5, B8, B9, and B10 are composite interfaces whose cited ingredients require the explicit
normalization/dictionary steps documented in their sections, rather than verbatim statements of a
single published theorem.

---

## E. Verification status (against cited source PDFs; audit copies not vendored)

**✅ Verified against the cited sources (exact theorem number + statement checked):**
- **B1** — NSW **(7.4.1)**: for a `p`-adic local field of degree `N`, `G_k` is generated by
  `N+2` elements.  This applies at `p=2`.  NSW (7.5.14) is not the right citation because its
  surrounding subsection assumes `p ≠ 2`.
- **B4** — NSW **(7.5.11)(ii)** (`μ_p⊆k ⇒ G_k(p)` Demushkin of rank `N+2`); for `ℚ₂`, rank `3`.
- **B5** — NSW **(7.1.1)** Class Field Axiom, **(7.1.5)** `(G_k,k̄ˣ)` is a class formation.
- **B6** — NSW **(7.2.6)** "Tate Duality" (exact cup-product pairing verified verbatim; the
  theorem is stated there for arbitrary `p`-adic `k`, so the 2026-07-06 base-generalization of the
  Lean encoding to all finite `k/ℚ₂` is census-neutral).  Induced mod-2 Hilbert-pairing
  nondegeneracy (the K-level P-15f7 consumer): **FV Ch. IV §5 Prop (5.1)(6) + Cor. p.145 + Thm
  (5.2)** and **O'Meara ITQF 63:13** `[both ✓ verified 2026-07-06]`.
- **B7** — NSW **(7.3.1)** (Tate): `χ(k,A)=‖a‖_k` (verified verbatim).
- **B7′** — Serre, *Course in Arithmetic*, **Ch. III §1.2 Thm 1** — the `p=2` formula
  `(a,b)=(-1)^{ε(u)ε(v)+αω(v)+βω(u)}` and `ε,ω` (Ch. II §3.3) verified verbatim (= paper Lemma 3.5).
  *(Discharged in-repo 2026-07-09 — citation record kept.)*
- **B6 / B7 secondary** — Serre, *Galois Cohomology*, **Ch. II §5.2 Theorem 2** (Tate duality) and
  **§5.7 Theorem 5** (`χ(A)=‖a‖_k`) verified verbatim (corroborate the NSW primaries).
- **B9** — **Evens [9] §§4–5 Thm 1** (norm map; `N(1+x)=1+tr(x)+N(x)`, index 2) and
  **Kahn [10] Théorèmes 1–3** (SW class of induced/transferred forms) were checked directly.
  **Kozlowski [11] Theorem 1.1** is the cited index-2 special case, but its exact 1984 text was
  not independently obtainable in the 2026-07-12 audit; it is non-load-bearing because Kahn
  Theorem 2 directly gives the formula. **Guillot [6]** is bibliography-only background.

**Also verified (later-added sources):**
- **B2** — Washington, *Introduction to Cyclotomic Fields*, **Ch. 2 Theorem 2.5**
  (`Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)ˣ` via the cyclotomic character) — verified verbatim.  (Axiom deleted
  2026-07-09 as unused; the verification record stays.)
- **B10** — NSW **(7.5.3) (Iwasawa)** — "the Galois group of the maximal tamely ramified
  extension of a local field is the profinite group generated by two elements σ, τ with the
  only relation στσ⁻¹ = τ^q" — verified verbatim, with **(7.5.2)** (the split extension).
  Convention note: NSW's arithmetic `σ` vs the paper's geometric `σ` (`τ^σ = τ²`) — the
  presentations agree under `σ ↦ σ⁻¹` (see `GQ2/TameQuotient.lean`).
  **Oriented form B10′ (strengthened in place 2026-07-06, P-25 escalation, user-approved;
  census unchanged):** two reciprocity-orientation clauses added to the bundle
  (`OrientedTameQuotient`): units land in the `ν_t`-kernel; `rec(2)` (arithmetic Frobenius)
  has geometric coordinate `ztwoOne⁻¹`.  Citations verified in the source PDFs:
  **Serre, *Local Fields*, Ch. XIII §4, Proposition 13 and its corollary** give units ↦
  inertia and prime elements ↦ Frobenius.  Neukirch ANT **Chap. V, Theorem (6.2)** is stated
  for `n > 0`, so it supports the higher-unit filtration, not the `n = 0` orientation clause.
  Neukirch **Chap. V, (1.2)** (`Ĥ^i(G(L|K), U_L) = 1` for `L|K` unramified) says units are
  norms at every finite unramified level; NSW (7.1.2)(i)
  is the cohomological-triviality form).  The clauses are pinned to the B5 constant (a
  ∀-bundle form would be false under Frobenius-coordinate twists); discharge `tame_reciprocity`
  = Prop 3.14's `compatF` (`docs/orchestration/p25-tame-reciprocity-plan.md`).
- **B8** — Stix [8], **§3.3 + Definition 37** (the paper's exact citation): cyclotomic action on
  cuspidal inertia — verified. (Deligne, MSRI 16 (1989), is the classical *origin*, not cited by the
  paper.)
- **B3** — Labute [2], **Theorem 8** (`q=2`, `d` odd: `G_K(2)` has `d+2` generators, relation
  `x₁²x₂⁴[x₂,x₃]⋯`; at `d=1` = the paper's `D₀`) and **Theorem 4 case (2)** (canonical character
  `−1, (1−2^f)^{-1}, 1`) — both verified verbatim.

**✅ Line-checked by P-20 (2026-07-05), against Serre *Local Fields* (GTM 67):**
- **B11a** — Serre, *Local Fields* [7], **Ch. XIV §2 "The Symbol (a,b)", Proposition 4, clause iii)**
  (book pp. 206–207): "in order that `(a,b) = 0`, it is necessary and sufficient that `b` be a norm in
  the extension `K(a^{1/n})/K`."  The symbol-as-cup identification is **§2, Proposition 5**
  (`(a,b) = i(φ_a ⌣ φ_b)`), so at `n = 2` this is `[a]∪[b]=0 ⟺ b ∈ N_{K(√a)/K} ⟺ b = x²−ay²`.
  *(Correction 2026-07-06, P-15f1: re-checked against the **updated** scan — Ch. XIV runs
  Props 1–3 in §1 and Props 4–5 in §2; the previously recorded "Prop. 7 iii, p. 209" came from
  the pre-update scan.  Remark 3 of §2 gives the `n = 2` conic form.)*  (Ch. XIV §2 Exercise 3
  gives the odd-degree Steinberg relation; Ch. XIV §4, p. 214, computes the symbol for `Q_p, n=2`.)
- **B11b** — Serre, *Local Fields* [7], **Ch. V §2 "The Unramified Case", Proposition 3** (book p. 82)
  with its **Corollary + Remark 1**: `N(Uⁿ_L) = Uⁿ_K` for `n ≥ 1`, and the equivalence
  `[K*:NL*]=f ⟺ U_K=NU_L ⟺ K̄*=NL̄*`, the last holding when the residue field is finite (Remark 1).
  So for `K` with finite residue field (`ℚ₂`: residue `𝔽₂`) and `L/K` unramified, `U_K = N_{L/K}(U_L)`:
  every unit is a norm.  Rests on Prop. 1 (`N: Uⁿ_L→Uⁿ_K`) and Prop. 2 (graded pieces = residue
  norm/trace) of §2.  The repo-specific "unramified = equal spectral-norm value groups" bridge is a
  `def` (`GQ2.HasEqualNormValueGroups`, named `GQ2.IsUnramifiedQuadraticSpectral` before
  2026-07-24), a named convention rather than a cited theorem, so it
  adds no proof-theoretic strength (P-23).  (**Discharged 2026-07-09** (B11b board): no longer an
  axiom — proved in-repo, std-3, in `GQ2/UnramifiedQuadraticNorms.lean` + `GQ2/TeichmullerLift.lean`
  via the norm-form successive-approximation engine against the B13 filtration; `dyadicNormCriterion`
  now rests on B11a alone.)

**Discharged (proved in-repo):** RZ Hopfian = **Prop. 2.5.2** (also confirmed against source);
Schur–Zassenhaus (Mathlib).

**Tertiary corroboration still unchecked:** **Milne *ADT* I.2.1/I.2.8** (free online) — for B6/B7,
superfluous now that both NSW **and** Serre *GC* are verified.

**✅ Line-checked by P-15f1 (2026-07-06), against the cited scans:**
- **B12** — NSW **(6.2.1)** (Satz 90) + the displayed Kummer isomorphism
  `H¹(G_K, μ_n) ≅ K^×/K^{×n}` of Ch. VI §2 and its dual **(6.2.2)** — verified verbatim;
  Serre LF **Ch. XIV §2 p. 206** (isomorphism onto characters; construction Ch. X §3) —
  verified verbatim.  (**Discharged 2026-07-09**: no longer an axiom — proved in-repo, std-3.)
- **B13** — Serre LF **Ch. IV §2, Prop. 6** (graded pieces of the unit filtration) and, for the
  in-repo (F2) discharge, **Prop. 7** (+ Prop. 5) (`s(π)/π`, uniformizer-independent) — verified
  verbatim.  The (93) square-class consequence and the Hensel top are *proved*, not leafed.
  (**Discharged 2026-07-09**: no longer an axiom — proved in-repo, std-3.)
- (Supporting, for the `hinf`/`hext` in-repo proofs:) Brown [5] **Ch. III §10, Corollary (10.2)**
  (`|G|` annihilates `H^n(G,M)`, `n > 0`; invertible ⟹ vanishing) and **Theorem (10.3)**
  (Sylow restriction) — verified verbatim in the provided Brown scan.

**Net.**  The underlying published inputs for every active leaf have been source-audited, with
explicit dictionary steps recorded for the composite interfaces.  B6/B7 are doubly sourced;
B3's Theorem 8 at `d=1` reproduces the paper's `D₀`; B11a/B11b were line-checked by P-20.
The exact Kozlowski 1984 paper was not independently obtainable in this audit, but Kahn's
Theorem 2 is the direct load-bearing source for the formula and a later paper by Kozlowski
corroborates the attribution.  The two would-be finite-group inputs (RZ Hopfian Prop. 2.5.2,
Schur–Zassenhaus) are proved in the formalization.  Of the fifteen historical leaves,
**nine remain axioms**: B12, B7′, B13, and B11b are discharged, while the never-consumed B2
and B4 are deleted.
