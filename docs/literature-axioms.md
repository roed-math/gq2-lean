# Literature inputs for Theorem 1.2 — reviewer's enumeration

**Purpose.** This document reduces the formalization of the paper *A Profinite Presentation of the
Absolute Galois Group of `ℚ₂`* (D. C. Turturean, 2026) to a **minimal list of classical results that
already exist in the literature**, and enumerates them with precise statements and citations. It is
meant for a quick expert check: *does each "leaf" below correctly match a known
theorem in the cited reference?*

> **Status (2026-10-17): census 0; every input is proved via Tau Ceti.** The library contains no
> `axiom` declaration.  Ticket C2 of the Tau Ceti discharge campaign (owner gate G1) deleted
> `GQ2/Foundations/Axioms.lean` and `GQ2/Foundations/AxiomInstance.lean`.  Each of the nine leaves
> that were axioms until then (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) is proved from the
> [Tau Ceti](https://github.com/TauCetiProject/TauCeti) library at revision `706344c35` by an
> adapter in `GQ2/TauCeti/`.  The nine legacy names are kept, with statements **byte-identical** to
> the former axioms, as theorems or definitions in `GQ2/Foundations/TauCetiInstance.lean`, whose
> docstrings keep the citations.  **The statements below did not change; what changed is why they
> hold.**  The citations, faithfulness classes and encoding notes in §B still describe what each
> Lean statement asserts and which published theorem it encodes.  Each §B entry now also records its
> Tau Ceti source and gq2 adapter, and §T summarizes the new trust base.
>
> *On the `dyadic` branch (2026-10-17):* the census there was 2 after the merge of this discharge.
> The two `K`-level inputs B5-K `markedRecipAt` and B10-K `orientedTameQuotientAt` were the
> remaining axioms, and ticket C1' proved them from Tau Ceti too
> (`GQ2/TauCeti/{GaloisDictK,B5K,B10K}.lean`). The census is 0 there as well (§T, §D).
>
> *Earlier status (T-20):* all leaves were *stated in Lean*, as nine axioms.
> [`review-packet.md`](orchestration/review-packet.md), written in that period, gives the Lean name
> per leaf, the consolidated deviations table, and mechanical verification instructions.  The
> citations and per-result discussion below remain the authoritative literature reference.

**Scope of the reduction.** The paper's *own* §§3–9 argument (its Propositions and Lemmas) is
**granted** here — those are the paper's contribution, not literature, and are listed separately in
§C so you can also check they match the *paper*. What we isolate in §B are the **classical
foundations** the paper builds on. If every item in §B is a correct citation and every node in §C is
faithful to the paper, then (modulo the routine profinite assembly noted in §A) Theorem 1.2 follows.

**Lean status legend.**  The marks classify the *statement's encoding*; they say nothing about
how it is proved.
- ✅ **faithful** — stated as a typechecked Lean statement against current Mathlib.  Until
  2026-10-17 the active leaves were `axiom`s in `GQ2/Foundations/Axioms.lean`; since then each is a
  same-name theorem or definition in `GQ2/Foundations/TauCetiInstance.lean`, proved via Tau Ceti.
  (A leaf already *proved* in-repo is not a leaf at all; those are marked as discharged.)
- 🟡 **schematic** — the mathematical statement is precise (below) but a faithful Lean signature needs
  infrastructure Mathlib lacks (continuous Galois cohomology of a profinite group, Demushkin groups,
  local Tate duality pairings, the Hilbert symbol), so it is documented here, not in Lean.  (This
  was the state at the freeze.  Since T-20 every active 🟡 leaf has a Lean statement over the
  repository's own encodings, such as the `GQ2.ContCoh` continuous cohomology, rather than
  Mathlib-native notions; B3 appears in Lean only in its B3c form.)

---

## T. Trust base since the Tau Ceti discharge (2026-10-17)

**What the theorem now rests on.** Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) plus Tau Ceti's proofs at revision `706344c35426d3df6931a2457271dceb3f9ac507` (Tau
Ceti `main`, 2026-10-16; <https://github.com/TauCetiProject/TauCeti>, required in `lakefile.toml`).
Owner gate **G0** (2026-10-16) accepted this change of trust base: from "nine cited theorems, stated
in this repository as axioms" to "Tau Ceti's proofs of them".  Tau Ceti is machine-written; its own
CI enforces zero sorries and an axiom allowlist.  Owner gate **G1** (2026-10-17) approved the census
flip.  Platform for the campaign: Lean `v4.35.0`, Mathlib `cfc55fc58`.  Campaign records:
[`tauceti-proof-plan.md`](orchestration/tauceti-proof-plan.md),
[`tauceti-tickets.md`](orchestration/tauceti-tickets.md) and the recon memo
[`tauceti-t2-recon.md`](orchestration/tauceti-t2-recon.md), whose per-lane sections describe how
each adapter bridges conventions.

**Census history.** The census rose to its peak of 15 on 2026-07-06.  On 2026-07-09 it went
15 → 13 (B12 discharged in-repo, B2 deleted) → 12 (B7′) → 11 (B13) → 10 (B11b).  On 2026-07-10 it
went 10 → 9 (B4 deleted).  It stayed 9 through the B9 restatement (2026-07-24) and the B-Lab
decision (2026-07-25/26, §B3 addendum).  On 2026-10-17 it went **9 → 0** (ticket C2): the nine
were proved via Tau Ceti.

**On the `dyadic` branch.** The general-2-adic campaign added two `K`-level inputs at gate G-AX
(2026-07-29): **B5-K** `GQ2.markedRecipAt` (AX3, census 9 → 10) and **B10-K**
`GQ2.orientedTameQuotientAt` (AX4, census 10 → 11). Their record is in
[`dyadic/literature-axioms-dyadic.md`](dyadic/literature-axioms-dyadic.md). The dyadic Tau Ceti
discharge ([`dyadic/tauceti-discharge-plan.md`](dyadic/tauceti-discharge-plan.md),
[`dyadic/tauceti-discharge-tickets.md`](dyadic/tauceti-discharge-tickets.md)) went in two steps on
2026-10-17. Ticket T0 merged the ℚ₂ discharge above into that branch, taking the census from 11
to 2. Ticket C1' took it
from 2 to 0: both inputs are now `noncomputable def`s in `GQ2/Foundations/TauCetiInstance.lean`,
with statements byte-identical to the deleted axioms. Their bodies are the adapters
`TauCetiBridge.markedRecipAt_tauceti` (`GQ2/TauCeti/B5K.lean`) and
`TauCetiBridge.orientedTameQuotientAt_tauceti` (`GQ2/TauCeti/B10K.lean`), both on the `K`-level
dictionary `GQ2/TauCeti/GaloisDictK.lean`. B5-K comes from Tau Ceti's local class field theory at
`↥K` (`ClassFieldTheory.artinMap`, `unramifiedCoordinate`, `artinMap_norm`, and inertia ⊆
`ker ν_ur` through `map_inertiaSubgroup_le_fixingSubgroup_iff`). B10-K comes from
`wildInertiaSubgroup` and the geometric Iwasawa presentation (`tameQuotientGeometricEquiv`, with
`IwasawaGroupGeometric ≃ₜ* Tq q`). On that branch `scripts/check_axioms.sh` check 5b pins the two
names and the W361 endpoint `GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI`
at exactly the standard three. Check 8 (`GQ2/DyadicTauCetiAxiomAudit.lean`) re-checks them in the
environment of the whole dyadic tree.

**The map.** Each adapter lives in namespace `GQ2.TauCetiBridge` and prints exactly the standard
three axioms.  Each legacy name is now a theorem or definition in
`GQ2/Foundations/TauCetiInstance.lean` whose body is the adapter (for B7, a universe transport of
the adapter).  Tau Ceti declarations are listed
by their main names; modules and conventions are in each §B entry.

| leaf | legacy name (now in `TauCetiInstance.lean`) | adapter, file | Tau Ceti source (main declarations) |
|---|---|---|---|
| B1 | `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | `absGalQ2_isTopologicallyFinitelyGenerated_tauceti`, `GQ2/TauCeti/B1.lean` | `TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup` |
| B3c | `GQ2.dyadicOrientation` | `dyadicOrientation_tauceti`, `GQ2/TauCeti/B3c.lean` | `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`; `TauCeti.standardD0Orientation_d0A/_d0S/_d0Y` |
| B5 | `GQ2.localReciprocity` | `localReciprocity_tauceti`, `GQ2/TauCeti/B5.lean` | `TauCeti.ClassFieldTheory.artinMap` with `continuous_artinMap`, `denseRange_artinMap`, `unramifiedCoordinate_artinMap`, `artinMap_restrict`, `localArtinMap_eq_zero_iff`, `localCyclotomicCharacter_artinMap_padic(_uniformizer)` |
| B6 | `GQ2.tateDualityAt` | `tateDualityAt_tauceti`, `GQ2/TauCeti/B6.lean` + `DualizingGroup.lean` | `TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed`, `h2MuEquivZMod_mixed` |
| B7 | `GQ2.Foundations.absGalQ2_localEulerCharacteristic` | `absGalQ2_localEulerCharacteristic_tauceti` (`M : Type`), `GQ2/TauCeti/B7.lean`; universe transport `localEulerCharacteristic_of_type` in `TauCetiInstance.lean` | `TauCeti.ClassFieldTheory.eulerCharacteristic_mixed`, `finite_H` |
| B8 | `GQ2.peripheralCyclotomicAction` | `peripheralCyclotomicAction_tauceti`, `GQ2/TauCeti/B8.lean` | `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two` |
| B9 | `GQ2.relativeStiefelWhitney_dyadic` | `relativeStiefelWhitney_dyadic_tauceti`, `GQ2/TauCeti/B9.lean` + `StiefelWhitneyDict.lean` | `TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer`, `TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer` |
| B10 | `GQ2.tameQuotient` | `tameQuotient_tauceti`, `GQ2/TauCeti/B10.lean` | `TauCeti.wildInertiaSubgroup`, `isProP_wildInertiaSubgroup`, `TauCeti.tameQuotientGeometricEquiv`, `iwasawaCoordinateGeometric` |
| B11a | `GQ2.hilbertSymbol_normCriterion_finiteDyadic` | `hilbertSymbol_normCriterion_finiteDyadic_tauceti`, `GQ2/TauCeti/B11a.lean` | `TauCeti.cup_kummerClass_eq_zero_iff` |

**Shared dictionaries.** `GQ2/TauCeti/GaloisDict.lean` (A1: `k.fixingSubgroup ≃ₜ*` Tau Ceti's
absolute Galois group, separable versus algebraic closure, Tau Ceti's local-field package on a
finite `k`, gq2's `chiCyc` as Tau Ceti's `localCyclotomicCharacter`); `CohomologyDict.lean` (A2:
gq2's explicit `H⁰/H¹/H²`, restriction, cups and Kummer classes versus Tau Ceti's continuous
cohomology); `ProPDict.lean` (P1: pro-`p` groups, free profinite groups, presentations, `ℤ̂`, `D₀`,
`Δ`).  B6 and B9 add `DualizingGroup.lean` and `StiefelWhitneyDict.lean`.

**Assembly and capstones.** `GQ2.TauCetiBridge.tauCetiInputs : LiteratureInputs`
(`GQ2/TauCeti/Instance.lean`) bundles the nine adapters; `GQ2.tauCetiLiteratureInputs` in
`TauCetiInstance.lean` is the instance, replacing the axiom-backed one.  The legacy capstones keep
their statements and now print exactly the standard three: `GQ2.main_presentation_literal` (Γ_A),
`GQ2.main_presentation_literal_roe_unconditional` (Γ_R), `GQ2.main_presentation_literal_roe`,
`GQ2.SectionTen.eq_154`, `GQ2.eq_154_R`, `GQ2.SectionTen.main_surjection_count'`,
`GQ2.main_surjection_count_R`, `GQ2.admissibleCountR_eq_admissibleCount`.  Four further capstones
in `GQ2/TauCeti/Main.lean` take the Tau Ceti bundle explicitly and do not depend on instance
selection: `GQ2.main_presentation_literal_tauceti`, `GQ2.main_presentation_literal_roe_tauceti`,
`GQ2.main_surjection_count_tauceti`, `GQ2.main_surjection_count_R_tauceti`.  The
explicit-hypothesis (`_of_inputs`) capstones are unchanged.

**Mechanical checks.** `scripts/check_axioms.sh` (census `EXPECTED_AXIOMS=0`; check 5 audits every
legacy capstone at exactly the standard three, with twin pairs identical, plus the four Tau Ceti
capstones; check 7 runs `GQ2/TauCetiAxiomAudit.lean`); `GQ2/AxiomLedger.lean` (at C2 it scanned
7486 declarations under `GQ2`, all at the standard three, with empty gap map and ALARM and 12
capstones certified); `GQ2/PalomarAxiomAudit.lean`; `GQ2/TauCetiAxiomAudit.lean`.  The legacy
Comparator pair (`Challenge`/`Solution`, `comparator-config.json`) now permits only the standard
three axioms.  The Palomar pair (`comparator-config-palomar.json`), which takes the literature
inputs as an explicit hypothesis, is unchanged.

**Still open.** Owner gate G2 decides whether to keep or retire the legacy `Challenge`/`Solution`
pair (`Challenge.lean`'s docstring still mentions the nine axioms, pending G2).  The B3c adapter
carries private copies of P1 dictionary pieces (dedupe pending).  `scripts/AxiomClosureProbe.lean`
and `docs/axiom-closure.md` still describe the nine axioms.  Many gq2 source docstrings, including
the per-declaration docstrings kept in `TauCetiInstance.lean` (for example "The B5 axiom"), still
call the nine inputs axioms.

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
Since 2026-10-17 every active entry (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) also has a **Proved
via Tau Ceti** bullet: the Tau Ceti source declaration(s) and module, the gq2 adapter (namespace
`GQ2.TauCetiBridge`) and its file and landing commit, and the conventions the adapter reconciles.
In every case the legacy name now lives in `GQ2/Foundations/TauCetiInstance.lean`, with its
statement unchanged.
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
- **Lean.** `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` (an axiom until
  2026-10-17; now a theorem in `GQ2/Foundations/TauCetiInstance.lean`).
- **Proved via Tau Ceti.** Source: `TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup`
  (module `TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup`) at `K = ℚ_[2]`; its
  proof produces a `([K:ℚ_p]+2)`-tuple of generators, the (7.4.1) bound.  Adapter:
  `absGalQ2_isTopologicallyFinitelyGenerated_tauceti`, `GQ2/TauCeti/B1.lean` (`a5ccd575`).
  Conventions: none to reconcile; Tau Ceti's finite-generation predicate is not exposed, so it is
  unfolded through its `_iff` lemma.
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
  table (`docs/orchestration/review-packet.md` §2).  `GQ2.dyadicOrientation` was an axiom until
  2026-10-17; it is now a `noncomputable def` in `GQ2/Foundations/TauCetiInstance.lean`.
- **B3c proved via Tau Ceti.** Sources: `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`
  (module `TauCeti.NumberTheory.LocalField.ProP.RatPadic`): an isomorphism `G_ℚ₂(2) ≃ₜ* D₀` along
  which the standard orientation of `D₀` pulls back to the cyclotomic orientation, which is
  surjective; and `TauCeti.standardD0Orientation_d0A/_d0S/_d0Y`
  (`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation`), the values `−1, 1, (−3)⁻¹`.
  So the three bundled parts above (the values, the cyclotomic compatibility through the quotient
  map, the normalized isomorphism) all come from Tau Ceti.  Adapter: `dyadicOrientation_tauceti`,
  `GQ2/TauCeti/B3c.lean` (`b80367b3`).  Conventions: the two maximal pro-2 quotients of `G_ℚ₂` are
  identified (the same `proPKernel`).  gq2's `D₀` is the maximal pro-2 quotient of the profinite
  presentation, Tau Ceti's `demushkinD0` the pro-2 presentation; the relators agree, `A²S⁴[S,Y]`
  with the same commutator convention `[x,y] = x⁻¹y⁻¹xy`, so no inverse is inserted.  `chiTwo` is
  Tau Ceti's `cyclotomicOrientation` transported (both sides use Mathlib's cyclotomic character,
  neither inverted).  The adapter keeps private copies of some P1 dictionary pieces (dedupe
  pending).
- **Used at.** Lemma 3.4 → Prop 1.1.

#### B3 addendum — "B-Lab", the `Γ_R` classification instance  ✅ **NOT AN AXIOM — proved in-repo 2026-07-26**

*Added at ticket L6.  Reviewers arriving from the README's "exact inputs" pointer: this is the one
input the `Γ_R` (Roe-candidate) route ever needed beyond the nine census axioms, and it is **not**
one of them — it is a theorem.  The census is **9 before and after**.  (Since 2026-10-17 the
census is 0: the nine are themselves proved via Tau Ceti, §T.)*

- **The statement.** `GQ2.BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean`, `section Draft`) is exactly
  the *uniqueness half of B3, at the single instance `G := D_R`*:

  > if `D_R` is Demushkin at `p = 2` with `demushkinRank = 3` and `demushkinQ = 2`, and carries a
  > continuous **surjective** Labute orientation `χ : D_R →* ℤ₂ˣ`, then
  > `Nonempty (ContinuousMulEquiv D_R D₀)`.

  Here `D_R` is the pro-2 quotient of the Roe candidate `Γ_R` (⟦lem:pro2word⟧) and
  `D₀ = ⟨A,S,Y | A²S⁴[S,Y]⟩` is B3's dyadic normal form.  It is the note's Cor. 3.4
  ⟦cor:abstractD0⟧.
- **Decision history.**  Ticket R14 would have added it as a **tenth axiom**.  The owner
  **declined** (2026-07-25): it was carried instead as an explicit theorem binder
  `(hBLab : BLabHypothesis)` on the `Γ_R` capstones, so that the conditionality was visible in the
  statement rather than hidden in `Axioms.lean`.  The L-campaign then **discharged** it
  (2026-07-26) as
  ```lean
  theorem GQ2.Roe.Labute.bLab : BLabHypothesis   -- GQ2/Roe/Labute/Assembly.lean
  ```
  `#print axioms GQ2.Roe.Labute.bLab` = `[propext, Classical.choice, Quot.sound]` — **the standard
  three exactly, zero census axioms, no `sorryAx`**.  In particular the proof does *not* route
  through B3c: the orientation data it uses comes from the `Γ_R`/`D_R` presentation side (`chiR`,
  `chiD0pres`), not from `GQ2.dyadicOrientation`.
- **Why this is a discharge and not a citation.**  The proof does not invoke Labute's Theorem 8
  uniqueness statement at all.  It re-runs the classification *for this instance* by a
  two-central-tower argument: continuous surjections are built **in both directions** level by
  level along the tower `λ_k`, and the profinite Hopfian property upgrades the resulting pair of
  epis to an isomorphism.  Chain, with the campaign that produced each piece:

  | layer | Lean | campaign / plan |
  |---|---|---|
  | λ-tower (two-central series, cofinality, openness) | `GQ2/Roe/Labute/TwoCentralTower.lean` | L2 · [`labute-plan.md`](orchestration/labute-plan.md), [`labute-l1-design.md`](orchestration/labute-l1-design.md) |
  | levelwise triple sets, defect calculus, base case `k₀ = 3` | `GQ2/Roe/Labute/Levelwise.lean` | L3/L4a |
  | **span theorem** `Z_k = Im d̄ + two generator-power tails` | `GQ2/Roe/Labute/SpanFoundation.lean`, `GradedLie/{SpanIdentities,SpanStep,SpanBase,SpanAssembly}.lean` | **GL-campaign** · [`span-gradedlie-plan.md`](orchestration/span-gradedlie-plan.md) |
  | **stage lemma** (SL1 separation + SL2 lifting), both directions | `GQ2/Roe/Labute/StageLemma.lean` | **SL-campaign** · [`sl-campaign-plan.md`](orchestration/sl-campaign-plan.md), [`sl1-numerics.md`](orchestration/sl1-numerics.md) |
  | assembly: König/Cantor limit + profinite Hopfian endgame | `GQ2/Roe/Labute/Assembly.lean`, `GQ2/Reconstruction.lean` | L5 |

  The off-Lean de-risking spike that shaped the argument — including the **falsification** of the
  naive stage lemma and its repair by the χ-congruence invariant `P` — is
  [`labute-spike.md`](orchestration/labute-spike.md); the per-ticket record of the whole campaign
  (LS, L1–L6, GL-A…E, SL0–SL1-L) is the board `docs/orchestration/roe-tickets.md`.  One deviation
  worth a reviewer's eye: SL1 was ultimately proved not by the spike's ±1-character derivations
  (which do **not** descend) but by the repository's own Labute-orientation machinery
  (`isLabuteOrientation_chiR`, tickets R9/R11) — see the SL1-L row of the board.
- **The classification instance itself, unconditionally** (stress example, `Assembly.lean`):
  feeding `bLab` its four antecedents `isDemushkin_DR`, `demushkinRank_DR`, `demushkinQ_DR`
  (R10/R12/R13) and the surjective Labute orientation `χ_R` (R11) gives
  `Nonempty (ContinuousMulEquiv D_R D₀)` with **std-3 exactly** (independently re-`#print`ed at L6).
  So the `D_R ≅ D₀` identification is now a theorem of this repository over Mathlib alone.
- **Consequence — the unconditional capstone.**  `GQ2.main_presentation_literal_roe_unconditional`
  (`GQ2/Roe/Main.lean`) is `Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)` with **no hypotheses**,
  and printed, until the Tau Ceti discharge, exactly `std-3 + the nine census axioms` — *the same
  twelve names as the `Γ_A` capstone `GQ2.main_presentation_literal`*.  Since ticket C2
  (2026-10-17) both print exactly the standard three, and the Tau Ceti route has its own copy,
  `GQ2.main_presentation_literal_roe_tauceti` (`GQ2/TauCeti/Main.lean`).  Mechanically enforced by
  `scripts/check_axioms.sh` check 5 (the corollary is in `AUDIT_DECLS`) and by
  `GQ2/AxiomLedger.lean`'s terminal certificate.  Nothing in §B or §D below changes: the `Γ_R`
  route widened the trust base by nothing at all.

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
- **Lean.** Schematic at the freeze (CFT provides abstract class-formation reciprocity
  `reciprocityIso`/`localInv`, but not the specific local Artin map `ℚ₂ˣ → G^{ab}`; `LocalCFT/` is
  early).  Stated since as the bundle `GQ2.localReciprocity : LocalReciprocity`
  (`GQ2/Reciprocity.lean`): `recip : ℚ₂ˣ →* G_ℚ₂^{ab}` continuous with dense range, the unramified
  coordinate `ν_ur` (normalized geometrically: `ν_ur(rec 2) = −1`), norm reciprocity for finite
  abelian layers, and the cyclotomic clauses `χ_cyc(rec u) = u⁻¹`, `χ_cyc(rec 2) = 1`.  An axiom
  until 2026-10-17; now a `noncomputable def` in `GQ2/Foundations/TauCetiInstance.lean`.
- **Proved via Tau Ceti.** Sources (namespace `TauCeti.ClassFieldTheory`): `artinMap`,
  `continuous_artinMap`, `denseRange_artinMap`, `artinMap_restrict`
  (`TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap`); `unramifiedCoordinate_artinMap`
  (`…Local.Unramified`); `localArtinMap_eq_zero_iff` (`…Local.Reciprocity`);
  `localCyclotomicCharacter_artinMap_padic` (`…Local.ExplicitCyclotomicSymbol.ArtinMap`) and
  `localCyclotomicCharacter_artinMap_padic_uniformizer` (`…Local.Cyclotomic`).  Adapter:
  `localReciprocity_tauceti`, `GQ2/TauCeti/B5.lean` (`a395ed6b`, `8a6d969b`).  Conventions: `recip`
  is Tau Ceti's Artin map with no cast, and both are arithmetic (a uniformizer goes to arithmetic
  Frobenius).  gq2's `ν_ur` is geometric, so `nu_ur` is the **inverse** of the `ℤ₂`-reduction of Tau
  Ceti's arithmetic `unramifiedCoordinate`.  Norm reciprocity goes through Tau Ceti's finite-layer
  `localArtinMap`, with gq2's `normSubgroup L` equal to Tau Ceti's `normGroup`.
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
  `GQ2.tateDualityAt` (an axiom until 2026-10-17; now a `noncomputable def` in
  `GQ2/Foundations/TauCetiInstance.lean`) quantifies over such `G`, gated by an open topological
  embedding `G ↪ G_ℚ₂` with finite-index image
  (identity for `G = G_ℚ₂`, subgroup inclusion for `G = G_K`).  The old `ℚ₂`-only
  `GQ2.tateDuality : TateDuality n` is now an in-repo `def` = the `G = G_ℚ₂` member (no consumer
  churn: `TateDuality n := TateDualityAt G_ℚ₂ n`).  **Census unchanged** (2026-07-06) — one axiom,
  base-generalized in place (the B9/B11 2026-07-03 pattern).  (Same continuous-cohomology encoding
  decisions as before; Mathlib/CFT lack the continuous duality package, so until the Tau Ceti
  discharge the perfectness was asserted, not derived.)
- **Proved via Tau Ceti.** Sources: `TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed`
  (module `TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Perfect`) for perfectness, and
  `TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed` (`TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity`)
  for `inv`.  Adapter: `tateDualityAt_tauceti`, `GQ2/TauCeti/B6.lean` with
  `GQ2/TauCeti/DualizingGroup.lean` (`f8676d25`).  Conventions: `DualizingGroup.lean` turns the gate
  `IsLocalDualizingGroup G n` into a finite `K/ℚ₂`, an isomorphism `G ≃ₜ*` Tau Ceti's absolute
  Galois group of `K`, and an equivariant identification of `μₙ`.  gq2's explicit `H⁰/H¹/H²` are
  compared with Tau Ceti's continuous cohomology through the A2 dictionary.  gq2's dual
  `MuDual n M = Hom(M, μₙ)` (conjugation action) is Tau Ceti's `tateDual`, and the transported gq2
  cup pairings are Tau Ceti's `tateDualityPairing`.  gq2's `inv` is not normalized (the bundle asserts
  existence only), so any isomorphism supplied by `h2MuEquivZMod_mixed` serves.
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
- **Lean.** Schematic at the freeze (same continuous-cohomology gap as B6).  Stated since as
  `GQ2.Foundations.absGalQ2_localEulerCharacteristic`: for every finite discrete `G_ℚ₂`-module
  `M : Type*`, `H⁰, H¹, H²` (the repository's explicit continuous cohomology `GQ2.ContCoh`) are
  finite and `#H¹ = #H⁰ · #H² · 2^{v₂(#M)}`; conventions in `GQ2/EulerCharacteristic.lean`.  An
  axiom until 2026-10-17; now a theorem in `GQ2/Foundations/TauCetiInstance.lean`.
- **Proved via Tau Ceti.** Sources: `TauCeti.ClassFieldTheory.eulerCharacteristic_mixed` (module
  `TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem`, Tate's formula) and
  `TauCeti.ClassFieldTheory.finite_H` (`TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo`,
  finiteness in degrees `≤ 2`).  Adapter: `absGalQ2_localEulerCharacteristic_tauceti`,
  `GQ2/TauCeti/B7.lean` (`ea16f29b`).  Conventions: `M` becomes a Tau Ceti coefficient object
  `GalRep (#M) ℚ_[2]` through its `ZMod (#M)`-module structure, and the cardinalities move through
  the A2 comparison equivalences.  Tau Ceti's theorem lives in universe 0, so the adapter covers
  `M : Type` only; the legacy `M : Type*` statement is recovered by transporting `M` to a copy on
  `Fin (Nat.card M)` (`GQ2.TauCetiBridge.localEulerCharacteristic_of_type`, in
  `TauCetiInstance.lean`).
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
- **Lean.** Schematic in its literal form (no étale/anabelian `π₁` in Mathlib).  Stated since in
  group-theoretic form as `GQ2.peripheralCyclotomicAction : PeripheralCyclotomicAction`
  (`GQ2/PeripheralAction.lean`): on `Δ = maxPro2(FreeProfinite (Fin 2))` with peripheral generators
  `P, T, C`, for every `u ∈ ℤ₂ˣ` a continuous automorphism `aut u` with `aut u (X) = c_X⁻¹ X^{ι u} c_X`
  (`ι : ℤ₂ˣ → ℤ̂` an exponent embedding carried by the bundle, pinned by `ι 1 = ω₂` and 2-adic
  component `u`); the deviation from the literal `π₁` statement is flagged there.  An axiom until 2026-10-17; now a `noncomputable def` in
  `GQ2/Foundations/TauCetiInstance.lean`.
- **Proved via Tau Ceti.** Source: `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two`
  (module `TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic`): for a marked free
  pro-2 group of rank two and `u ∈ ℤ₂ˣ`, a continuous automorphism carrying `P, T, C` to conjugates
  of their `u`-th 2-adic powers, with the conjugator of `P` equal to `1`.  This is a statement about
  free pro-2 groups, i.e. the group-theoretic form gq2 states, for every unit `u`.  Adapter:
  `peripheralCyclotomicAction_tauceti`, `GQ2/TauCeti/B8.lean` (`6f68cfe3`), through the P1
  dictionary (`Δ ≃ₜ*` Tau Ceti's `freeProP 2 (Fin 2)`).  Conventions: to meet the two pinning
  conditions on `ι`, the adapter takes `ι u = ω₂ · s(u)`, with `s(u)` the profinite integer
  whose 2-adic component is `u` and whose odd components are `1` (the plan's "trivial odd part" was
  not provable, since gq2 never shows that the odd components of `ω₂` vanish).  Then gq2's
  `x ^ᶻ ι u` on `Δ` is Tau Ceti's `padicPow x u`, and `cP u := 1`.
- **Used at.** Lemma 3.6.

### B9. Relative Stiefel–Whitney (Evens–Kahn) identity  🟡 schematic · **RESTATED 2026-07-24 (B9-A flip)**
- **Statement.** The **relative Stiefel–Whitney identity** at the quadratic-form level: for a
  quadratic extension `L = k(δ)/k` of a finite dyadic base (`δ² = d ∈ kˣ`) and *arbitrary*
  `a ∈ Lˣ`,
  `w(Tr_{L/k}⟨a⟩) = w(Tr_{L/k}⟨1⟩)·(1 + cor_{L/k}[a] + N^{Ev}_{L/k}[a])`  in degrees ≤ 2,
  where `w₁ ∈ H¹(G_k, 𝔽₂)` and `w₂ ∈ H²(G_k, 𝔽₂)` are the Stiefel–Whitney classes **defined on
  isometry classes** of nondegenerate binary quadratic forms over `k` (not on fixed diagonal
  representatives).  Componentwise:
  * degree 1: `w₁(Tr⟨a⟩) = w₁(Tr⟨1⟩) + cor[a]`;
  * degree 2: `w₂(Tr⟨a⟩) = w₂(Tr⟨1⟩) + w₁(Tr⟨1⟩) ⌣ cor[a] + N^{Ev}[a]`.

  This is Kahn Th. 2 at the rank-1 form `⟨a⟩`, expanded via Evens Th. 1 / Kozlowski Thm 1.1 at
  index 2 — now checkable against the source *without* the Lemma 6.16 diagonalization scoping.
  (Since the 2026-07-24 B9-A flip this is the B9 leaf; the earlier composite statement — eq. (111)
  at the Lemma 6.16 diagonalizations — is the *derived* form recorded under **Lean** below.)
- **Citation** (precise; verified against the provided PDFs — unchanged by the flip):
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
- **Lean.** `GQ2.relativeStiefelWhitney_dyadic` (the B9 leaf since 2026-07-24; an axiom in
  `GQ2/Foundations/Axioms.lean` until 2026-10-17, now a theorem in
  `GQ2/Foundations/TauCetiInstance.lean`).
  The Stiefel–Whitney classes `swOne k` and `swTwo k htriv` are now **genuine Lean definitions on
  isometry classes** of binary quadratic forms (`GQ2/StiefelWhitney.lean`, on Mathlib
  `QuadraticForm ↥k V` with `QuadraticMap.Equivalent`), evaluated on the twisted trace forms
  `Tr_{k(δ)/k}⟨a⟩`/`Tr_{k(δ)/k}⟨1⟩` of `GQ2/TraceForm.lean`.  **Delzant well-definedness is proved**
  (`swOne_well_defined`, `swTwo_well_defined` — sorry-free, std-3): the degree-1 case is discriminant
  invariance; the degree-2 case is parametrized by the B11a norm criterion as an explicit hypothesis
  `hnorm` (the Q2 firewall — `GQ2/StiefelWhitney.lean` stayed strictly upstream of the axiom file, so
  it takes the criterion as a hypothesis rather than importing it), discharged from
  `hilbertSymbol_normCriterion_finiteDyadic` at the flip site.  Still marked 🟡 because the underlying
  continuous cohomology and SW-class machinery are the repository's own `ContCoh`/`StiefelWhitney`
  layer — Mathlib has neither (as for B6's `ContCoh` encoding).
  - **Derived form (was the pre-flip B9).** The previous composite B9 statement — eq. (111) at the
    fixed Lemma 6.16 diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr⟨1⟩ ≃ ⟨2, 2d⟩`, with
    `w₁⟨x,y⟩ = [x]+[y]` and `w₂⟨x,y⟩ = [x] ⌣ [y]` — is now the same-name **theorem**
    `GQ2.evensKahn_dyadic` (`GQ2/Foundations/Interfaces.lean` since the 2026-07-27 axioms/derived
    split; its proof consumes B11a), **byte-identical** to the pre-flip axiom so **no consumer changed** (the
    B7′/B11b/B12/B13 flip pattern).  It is proved by `evensKahn_dyadic_of_rsw`
    (`GQ2/EvensKahnDerived.lean`) from `relativeStiefelWhitney_dyadic` together with B11a: the
    proved trace-form diagonalizations and `swOne_diag`/`swTwo_diag` rewrite the abstract identity
    into the Kummer-class form.  Its footprint at the flip was
    `#print axioms = {relativeStiefelWhitney_dyadic, hilbertSymbol_normCriterion_finiteDyadic, + std-3}`.
    It now takes its inputs through `[LiteratureInputs]` (explicit dependencies: the B9 and B11a
    fields) and its `#print axioms` is the standard three; since ticket C2 both fields are proved
    via Tau Ceti.
    Census **9 → 9**, user-approved 2026-07-24 (B9-A board, `docs/orchestration/b9a-tickets.md`,
    T5 gate; plan `docs/orchestration/b9a-proof-plan.md`).
  - **Deviations** (flagged, unchanged by the flip): truncation to degrees ≤ 2; `N^{Ev}` *defined*
    by the two-point graph cocycle (98) (`evensNormH2`, Lemma 6.13); finite dyadic base; `hdeg`
    (`[k(δ):k] = 2`) carried redundantly (provable from `hidx`/`hUo` via `finrank_quadExt_eq_two`)
    so the statement is locally Kahn's `L/k` setting, per the owner's Q1 decision.
    ~~Delzant well-definedness absorbed into the diagonalization scoping~~ — **REMOVED by the flip**:
    well-definedness of `w₁`/`w₂` is now *proved*, not scoped away.
- **Proved via Tau Ceti.** Sources: `TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer`
  (module `TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer`) and
  `TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer`
  (`TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension`).  Adapter:
  `relativeStiefelWhitney_dyadic_tauceti`, `GQ2/TauCeti/B9.lean`, with the dictionary
  `GQ2/TauCeti/StiefelWhitneyDict.lean` (`47477175`).  Conventions: gq2's `swOne`/`swTwo` are read
  off at a chosen unit diagonalization of `Tr⟨1⟩` and of `Tr⟨a⟩`, and these diagonalizations feed
  Tau Ceti's two diagonal-presentation theorems.  The resulting identities over Tau Ceti's
  `Gal(kˢᵉᵖ/k)` are pulled back along A1's `fixingEquivAbsGal` with A2's `cont1F2`/`cont2F2`, which
  match Kummer classes, `cor`, the Evens norm and cups term by term.  The adapter does not use B11a
  (no `hnorm`).
- **Used at.** §6 (Lemmas 6.13 (Evens norm normalization), 6.16 (deep-unit Evens norm)), through the
  derived `evensKahn_dyadic`; the Shapiro–corestriction of Lemma 6.15 is Kahn Th. 2's Shapiro case.

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

#### B10. Oriented tame quotient of `G_ℚ₂` (Iwasawa; oriented form B10′ since 2026-07-06)  ✅ faithful · composite
- **Statement.** A closed normal pro-2 subgroup `W ≤ G_ℚ₂` (wild inertia) with
  `G_ℚ₂/W ≅ T_tame = ⟨σ, τ ∣ τ^σ = τ²⟩_prof`, oriented against local reciprocity (B5): the
  unramified coordinate `ν_t` satisfies `ν_t(tameF(rec u)) = 1` for units `u` and
  `ν_t(tameF(rec 2)) = ztwoOne⁻¹` (arithmetic Frobenius, geometric coordinate).
- **Citation.** NSW (7.5.3) (Iwasawa) with (7.5.2), wild inertia pro-`p` (Serre *LF* Ch. IV);
  orientation clauses Serre *LF* Ch. XIII §4 Prop. 13 and its corollary, with Neukirch ANT
  Ch. V (1.2) / NSW (7.1.2)(i) for units being norms in unramified extensions.  Verification record
  in §E.
- **Lean.** `GQ2.tameQuotient : OrientedTameQuotient localReciprocity` (bundle in
  `GQ2/TameQuotient.lean`, with the NSW convention notes, `σ ↦ σ⁻¹`).  Flagged deviation: `W` is
  characterized, not constructed, and its maximality (paper Lemma 3.3) is not asserted; the
  orientation clauses are pinned to the B5 constant.  An axiom until 2026-10-17; now a
  `noncomputable def` in `GQ2/Foundations/TauCetiInstance.lean`.
- **Proved via Tau Ceti.** Sources: `TauCeti.wildInertiaSubgroup`, `TauCeti.isProP_wildInertiaSubgroup`
  (module `TauCeti.NumberTheory.LocalField.WildInertia`), `TauCeti.tameQuotientGeometricEquiv`,
  `TauCeti.iwasawaCoordinateGeometric` (`TauCeti.NumberTheory.LocalField.Tame.Geometric`), and,
  for the orientation, B5's Artin-map facts.  Adapter: `tameQuotient_tauceti`, `GQ2/TauCeti/B10.lean`
  (`a2c2b6ea`), oriented against the B5 adapter's reciprocity datum.  Conventions: the witness `W`
  is Tau Ceti's wild inertia subgroup (the statement still asserts only existence).  `equiv` is Tau
  Ceti's geometric Iwasawa isomorphism followed by an identification with gq2's `T_tame`; the
  relators match (`γ⁻¹τγ(τ^q)⁻¹` with `q = 2`), and both sides' `σ` is geometric Frobenius.  Tau
  Ceti's coordinate is arithmetic, so gq2's `ν_t` is the **inverse** of its `ℤ₂`-reduction.  Both
  orientation clauses follow from one lift lemma through B5's `unramifiedCoordinate_artinMap`
  (valuation `0` at units, `1` at `2`).
- **Used at.** Prop 3.2 (local side); Prop 3.14 / Cor. 3.12 (the "same natural unramified
  character").

#### B11a. Dyadic Hilbert-symbol norm criterion over finite bases  ✅ faithful
- **Statement.** For `k/ℚ₂` finite and `a, b ∈ kˣ`: `[a] ∪ [b] = 0` in `H²(G_k, 𝔽₂)` iff `b` is a
  norm from `k(√a)`, iff `b = x² − a y²` for some `x, y ∈ k` (for `a` a square the norm form is
  universal, so no non-square hypothesis is needed).
- **Citation.** Serre *LF* Ch. XIV §2, Proposition 4(iii) (the symbol vanishes iff the second
  entry is a norm), with Proposition 5 (the symbol is the cup product); over `ℚ_p` also CiA
  Ch. III §1.1 Prop. 1.  Line-checked by P-20, with the 2026-07-06 numbering correction, in §E.
- **Lean.** `GQ2.hilbertSymbol_normCriterion_finiteDyadic`, the cup of the repository's Kummer
  classes `kummerClassK`, with the norm condition encoded as the norm form `b = x² − a y²`.  It is
  consumed together with the in-repo B11b theorem through `dyadicNormCriterion`
  (`GQ2/Foundations/Interfaces.lean`).  An axiom until 2026-10-17; now a theorem in
  `GQ2/Foundations/TauCetiInstance.lean`.
- **Proved via Tau Ceti.** Source: `TauCeti.cup_kummerClass_eq_zero_iff` (module
  `TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm`) at `K = ↥k`; it holds for any field in
  which `2` is invertible, so no local hypothesis is used.  Adapter:
  `hilbertSymbol_normCriterion_finiteDyadic_tauceti`, `GQ2/TauCeti/B11a.lean` (`230647d9`).
  Conventions: gq2's Kummer classes and cup are carried to Tau Ceti's by A2's `cont2F2` (an
  additive equivalence, so it reflects `0`) and its cup and Kummer rules at A1's
  `fixingEquivAbsGal k`.
- **Used at.** §6.3 (displays (93)/(94), Lemma 6.16), and the Delzant well-definedness layer behind
  B9's derived form `evensKahn_dyadic`.

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
"Prop 3.2 → B5" predates the B10 census decision.  These footprints were computed while the leaves
were axioms.  Since ticket C2 (2026-10-17) every node's `#print axioms` is exactly the standard
three, so they are now a record of which leaves each node consumes, not of what it is trusted on.

**Interpreting the footprints.**  The descriptions below record field-level literature
dependencies.  Generic declarations receive those inputs through `[LiteratureInputs]`, so their
`#print axioms` output contains only the standard three.  Until ticket C2, legacy wrappers selected
the provider assembled from all nine literature axioms and therefore printed all nine; since C2
they select `GQ2.tauCetiLiteratureInputs`, assembled from the nine Tau Ceti adapters, and print
the standard three.  `GQ2/AxiomLedger.lean` reports the declarations carrying `LiteratureInputs`
(its explicit-input inventory); its legacy-axiom map `bAxioms` is empty since C2.

**B9-A footprint note (added 2026-07-24).**  After the B9-A flip the `B9` entries in the "reduces
to" column and in the dependency chain below are consumed through the *derived* theorem
`evensKahn_dyadic`, whose `#print axioms` was then `{relativeStiefelWhitney_dyadic (B9),
hilbertSymbol_normCriterion_finiteDyadic (B11a), + std-3}`.  So every §6 node that consumed B9
(Lemmas 6.13, 6.16, and via them Thm 4.2) now surfaces the pair **{B9 = `relativeStiefelWhitney_dyadic`,
B11a}** in its footprint — the extra B11a co-dependence coming from the Delzant well-definedness
layer that the derivation traverses (plan node N2, `docs/orchestration/b9a-proof-plan.md`).  Those
nodes already consumed B11a independently at `lemma_6_16`, so the whole-library census is unchanged.
(Since C2 neither name is an axiom, and these nodes print the standard three.)

Internal dependency chain feeding **Thm 4.2** (paper App. D), all *paper* lemmas resting on §B:
5.7/5.8 (Stokes) → 5.10 (Fox–Heisenberg chain map); 5.11/5.13 → 5.15 (elementary-module duality, uses
B6); 6.13 → Evens normalization (B9); 6.15 → 6.17 (deep-half vanishing); 6.8 → 6.9 (ramified Gauss
sign, B7′/B9); 6.16 → 6.18 (local ramified hyperbolicity, B7′); 6.21 → `B/T ≅ V⋊C` split; 8.6 →
half-torsor count; 8.9 (closed recursion (136)–(142)) → Thm 4.2.

---

## D. Status summary

Since 2026-10-17 "proved via Tau Ceti" in the Lean column means: the legacy name is a theorem or
definition in `GQ2/Foundations/TauCetiInstance.lean` whose body is the named adapter in
`GQ2/TauCeti/` (§T); until then those entries read "axiom".  The ✅/🟡 marks still classify the
statement's encoding (legend at the top).

| leaf | precise citation | conf. | Lean |
|---|---|---|---|
| B1  `G_ℚ₂` top. f.g. | **NSW (7.4.1)** (`N+2` generators; valid at `p=2`) | ✅ **verified** | ✅ **proved via Tau Ceti** (`B1.lean`) |
| B2  2-adic cyclotomic surjective | Washington, *Cyclotomic Fields*, **Ch. 2 Thm 2.5** | ✅ **verified** | ❌ **deleted 2026-07-09** (unused) |
| B3  Demushkin classification | **Labute [2] Thm 8** (`D₀` at `d=1`) & **Thm 4 case (2)** | ✅ **verified** | 🟡; B3c form **proved via Tau Ceti** (`B3c.lean`) |
| B4  `G_ℚ₂(2)` is rank-3 Demushkin | **NSW (7.5.11)(ii)** (rank `N+2=3`); Serre [3]; Labute [2] | ✅ **verified** | ❌ **deleted 2026-07-10** (unused; B3c subsumes a marked B4) |
| B5  local reciprocity for `ℚ₂` | **NSW (7.1.1)/(7.1.5)** (class formation); Serre *LF* XI–XII | ✅ **verified** | 🟡 **proved via Tau Ceti** (`B5.lean`) |
| B5-K  marked local reciprocity over finite `K/ℚ₂` (AX3; `dyadic` branch) | **NSW Ch. I §5, Ch. VII §7.1** (functoriality); Serre *LF* **XI §3** | ⏳ **targets owner-approved 2026-07-29; PDFs unverified** (clause-level source audit 2026-09-17: [`dyadic/w361-axiom-source-verification.md`](dyadic/w361-axiom-source-verification.md)) | 🟡 **proved via Tau Ceti** (`B5K.lean`, `GaloisDictK.lean`; ticket C1' of [`dyadic/tauceti-discharge-plan.md`](dyadic/tauceti-discharge-plan.md), 2026-10-17); axiom from 2026-07-29 (census 9→10, gate G-AX) |
| B6  local Tate duality (all finite `k/ℚ₂`) | **NSW (7.2.6) "Tate Duality"**; Serre *GC* II §5.2; Milne I.2.1; induced Hilbert nondeg.: **FV IV §5 (5.1)(6)/(5.2)**, O'Meara **63:13** | ✅ **verified** | 🟡 **proved via Tau Ceti** (`B6.lean`, `DualizingGroup.lean`) |
| B7  local Euler characteristic | **NSW (7.3.1) (Tate)** `χ=‖a‖`; Serre *GC* II §5.7; Milne I.2.8 | ✅ **verified** | 🟡 **proved via Tau Ceti** (`B7.lean`) |
| B7′ dyadic Hilbert symbol | **Serre *Course in Arithmetic* Ch. III §1.2 Thm 1** (`ε,ω`: Ch. II §3.3) | ✅ **verified** | ✅ **proved** (2026-07-09) |
| B8  Galois action on `π₁(ℙ¹∖{0,1,∞})` | **Stix [8] §3.3 + Def 37** (Deligne MSRI 16: classical origin) | ✅ **verified** | ✅ **proved via Tau Ceti** (bundle; `B8.lean`) |
| B9  relative Stiefel–Whitney (`relativeStiefelWhitney_dyadic`; **restated 2026-07-24**, `evensKahn_dyadic` now the derived theorem) | **Evens [9] §§4–5 Thm 1**; **Kahn [10] Thm 1–3**; **Kozlowski [11] Thm 1.1** (Guillot [6]: background only) | ✅ **verified** | 🟡 **proved via Tau Ceti** (SW classes in-repo; `B9.lean`, `StiefelWhitneyDict.lean`) |
| B10 tame quotient of `G_ℚ₂` (**oriented**, B10′ since 2026-07-06) | **NSW (7.5.3) (Iwasawa)** with (7.5.2); Serre *LF* Ch. IV (wild pro-`p`); orientation clauses: **Serre *LF* XIII §4 Prop. 13 + cor.** (units ↦ inertia, prime ↦ Frobenius) + **Neukirch ANT V (1.2)** / NSW (7.1.2)(i) (units are unramified norms) | ✅ **verified** | ✅ **proved via Tau Ceti** (bundle; `B10.lean`) |
| B10-K oriented tame quotient of `G_K` at `q_K` (AX4; `dyadic` branch) | **NSW Ch. VII §7.5 (7.5.3)/(7.5.2)** (Iwasawa); Serre *LF* **Ch. IV**; **Ch. XIII §4 Prop. 13 + cor.** | ⏳ **targets owner-approved 2026-07-29; PDFs unverified** (clause-level source audit 2026-09-17: [`dyadic/w361-axiom-source-verification.md`](dyadic/w361-axiom-source-verification.md)) | ✅ **proved via Tau Ceti** (bundle; `B10K.lean`, `GaloisDictK.lean`; ticket C1', 2026-10-17); axiom from 2026-07-29 (census 10→11, gate G-AX) |
| B11a dyadic norm criterion (finite `k/ℚ₂`) | **Serre *LF* XIV §2 Prop. 4(iii)** with Prop. 5 (symbol = cup); over `ℚ_p` CiA III §1.1 Prop. 1 | ✅ **line-checked** (P-20) | ✅ **proved via Tau Ceti** (`B11a.lean`) |
| — RZ Hopfian | RZ [4], Prop. 2.5.2 | **confirmed** | ✅ **proved** |
| — Schur–Zassenhaus | Mathlib | — | ✅ **proved** |
| — B-Lab (`Γ_R` instance of B3: `D_R ≅ D₀`) | **not cited** — declined as an axiom 2026-07-25, proved in-repo instead (two-central tower + Hopfian) | — | ✅ **proved** (2026-07-26, `GQ2.Roe.Labute.bLab`, std-3; see the B3 addendum) |

(`✅ verified` = checked against the cited source PDF; audit copies are not vendored in this
repository. `quoted` = taken from the paper's own citation; `confirmed` = checked against a
reliable secondary source; `~` = identification made without the primary source to hand.)

**Bottom line for review.** Until 2026-10-17 the whole theorem rested on **nine** active
classical interfaces, stated as axioms (B1, B3c, B5–B11a — B10 added post-kickoff by the P-06
census decision, B11–B13 by the P-15/P-23/P-15f1 census decisions; **B12 discharged in-repo as a same-name std-3 theorem and the
unused B2 deleted**, B12-board census flip, user-approved 2026-07-09; **B7′, B13, and B11b likewise
discharged in-repo** (B13 a same-name `noncomputable def` over the `UnitFiltrationTop`/`Counts`
lane; B11b a same-name theorem over the norm-form engine `UnramifiedQuadraticNorms`/`TeichmullerLift`;
the never-consumed **B4 deleted 2026-07-10** (user-approved; census 10 → 9, citation record in its §B4 above),
so `dyadicNormCriterion` rests on B11a alone), B7′-, B13-, and B11b-board census flips,
user-approved 2026-07-09; **B9 restated in place 2026-07-24 as the relative Stiefel–Whitney
identity `relativeStiefelWhitney_dyadic`, its former composite statement now the derived theorem
`evensKahn_dyadic` — B9-A board, census-neutral**); of the two
finite-group inputs that would also have appeared (RZ Hopfian, Schur–Zassenhaus) both are already
proved.  The later `Γ_R` ("Replacement theorem") campaign needed **one** further classical-looking
input, the B3 classification at the instance `D_R`; it was **declined as a tenth axiom** and
**proved in-repo** instead (2026-07-26 — see the B3 addendum above), so the nine were the
whole trust base beyond the standard three for *both* candidate groups.  **Since ticket C2
(2026-10-17) all nine are proved via Tau Ceti and the census is 0**: for both candidate groups the
trust base is Lean's standard three axioms plus Tau Ceti's proofs at revision `706344c35` (§T).
The active declarations are faithful project interfaces over the repository's encodings;
B3c, B5, B8, B9, and B10 are composite interfaces whose cited ingredients require the explicit
normalization/dictionary steps documented in their sections, rather than verbatim statements of a
single published theorem.  Those statements are unchanged by the discharge: Tau Ceti proves
exactly them, through the adapters' conventions recorded in each §B entry.

---

## E. Verification status (against cited source PDFs; audit copies not vendored)

This audit checks that each leaf's statement matches the cited theorem.  It was done while the
leaves were axioms.  Since the Tau Ceti discharge the proofs rest on Tau Ceti rather than on these
citations; the citations now document which published theorem each Tau Ceti proof establishes.

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
Schur–Zassenhaus) are proved in the formalization.  Of the fifteen historical leaves, B12, B7′,
B13, and B11b were discharged in-repo and the never-consumed B2 and B4 deleted (2026-07-09/10),
leaving nine axioms.  On 2026-10-17 (ticket C2) those nine were proved via Tau Ceti, and **none
remains an axiom** (census 0).
