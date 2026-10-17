# Trust boundary for the dyadic campaign (ramified-`i` case) — census and residual surface

> **Status (2026-10-17): census 0; the two `K`-level inputs are proved via Tau Ceti.** On this
> branch the census went 11 → 2 → 0 in the dyadic Tau Ceti discharge
> ([plan](tauceti-discharge-plan.md), [board](tauceti-discharge-tickets.md),
> [recon memo](tauceti-discharge-recon.md)). Ticket T0 merged the ℚ₂ discharge, so the nine ℚ₂
> rows of §B became theorems or definitions proved from Tau Ceti
> ([`../literature-axioms.md`](../literature-axioms.md) §T): census 11 → 2. Ticket C1' did the
> same for the last two rows: census 2 → 0. **B5-K** `GQ2.markedRecipAt` and **B10-K**
> `GQ2.orientedTameQuotientAt` are now `noncomputable def`s in
> `GQ2/Foundations/TauCetiInstance.lean`, with statements byte-identical to the deleted axioms.
> Their bodies are the adapters `GQ2/TauCeti/B5K.lean` and `GQ2/TauCeti/B10K.lean`, built on the
> `K`-level dictionary `GQ2/TauCeti/GaloisDictK.lean` and proved from
> [Tau Ceti](https://github.com/TauCetiProject/TauCeti) at revision `706344c35`.
> `GQ2/Foundations/Axioms.lean` is deleted. The trust base of every dyadic statement, the W361
> endpoint included, is now Lean's standard three axioms plus Tau Ceti's proofs (§W361.0). The
> measured sets of §W361.1 and §A, the eleven-row census of §B and the checklist of §D are kept
> as the record of the period when these inputs were axioms (gate G-AX 2026-07-29 to
> 2026-10-17). They are superseded and have not been rewritten.

**Current general endpoint (W361, 2026-09-17): see §W361 immediately below.**
The older §§A–D are preserved as the AS5/frozen-quadratic audit snapshot, not as
the binder or axiom inventory of the new general theorem. In particular, the
canonical W361 endpoint does consume `markedRecipAt` and `orientedTameQuotientAt`.

**Purpose.**  This document is the dyadic campaign's counterpart of
[`docs/literature-axioms.md`](../literature-axioms.md), written for the owner's **G3 census
sign-off**.  It answers, in one place: *what exactly is assumed, where, when the final
ramified-`i` theorem `GQ2.Dyadic.ramifiedI_candidate_equiv_galK` (and each instance headline)
is accepted?*  Three layers, kept strictly separate:

* **§A — the measured axiom surface**: `#print axioms` (via the same `collectAxioms` walk
  `scripts/check_axioms.sh` check 5 uses), measured 2026-08-02 on branch `dyadic-as5` at the
  tree containing all AS-wave landings.  These sets are frozen into check 5's dyadic block
  (`scripts/check_axioms.sh`, `AUDIT_DYADIC`), so growth fails the gate mechanically.
* **§B — the axiom census (11)**: one row per `axiom` declaration in
  `GQ2/Foundations/Axioms.lean`, with its literature citation and its role in the dyadic tree.
  *(Since 2026-10-17 the file is deleted and the census is 0. §B's status note and the last
  column of its `K`-side table record how the rows are proved via Tau Ceti.)*
* **§C — the residual hypothesis-binder surface**: everything the theorems *quantify over*
  rather than assume.  Binders contribute **nothing** to an axiom print; they are the honest
  "givens" a caller must supply, and this section enumerates all of them with provenance and
  discharge status.  **The nine campaign obligations live here and never in §B** (board
  protocol; `scripts/check_dyadic.sh` D2 enforces it textually).

**Citation-status discipline** (owner ruling G-AX Q7, 2026-07-29): the two K-side axiom rows
(B5-K, B10-K) historically carried citations **UNVERIFIED against source PDFs** — the owner
approved the citation *targets* without a detail-check. Those historical annotations and
approval records are preserved below. The W361 [clause-level source audit](w361-axiom-source-verification.md)
now records the primary pages actually checked and the remaining composite translations;
it does not authorize a blanket "entire bundle verified" label. The nine ℚ₂-side rows keep the verification markers they already
have in `docs/literature-axioms.md` (many are `[✓ source-audited]` from the T-20/B9-A passes);
those markers are *quoted*, not re-audited here. *(Since 2026-10-17 no row's proof rests on its
citation: all eleven are proved via Tau Ceti. As for the nine ℚ₂ rows
(`docs/literature-axioms.md` §E), the citations and their verification status now record which
published theorem the Tau Ceti proof establishes. The UNVERIFIED annotations on B5-K and B10-K
are historical.)*

---

## W361. Current general fully marked endpoint

The public entry point is
[`GQ2/Dyadic/GeneralMain.lean`](../../GQ2/Dyadic/GeneralMain.lean).
It exports
`GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI`, proved in
[`FieldFamilySpliceMarkedCanonical.lean`](../../GQ2/Dyadic/Instances/FieldFamilySpliceMarkedCanonical.lean).
The statement takes a finite intermediate field `K/ℚ₂` and
`RI : RamifiedIData K`. It returns an actual source word at degree `[K : ℚ₂]`,
its complete corrected `WordCertificateRN`, a core realization, and one continuous
group isomorphism to `GalK K` with tame, maximal-pro-two, cyclotomic, and **full
two-adic** unramified compatibility. The generic bundled endpoint is
`FieldFamilySpliceMarkedFinal.hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange`
in [the marked assembly module](../../GQ2/Dyadic/Instances/FieldFamilySpliceMarkedFinal.lean).

This covers every degree and every selected family **within the standing
ramified-`i` scope**. It does not assert `RamifiedIData K` for every finite K.
The odd-degree corollary discharges this hypothesis by the existing norm
obstruction; it is not a restriction of the main endpoint to odd degrees.

### W361.0 Trust base since 2026-10-17

The endpoint `GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI` now rests on
Lean's standard three axioms (`propext`, `Classical.choice`, `Quot.sound`) plus Tau Ceti's proofs
at revision `706344c35` (`706344c35426d3df6931a2457271dceb3f9ac507`, pinned in `lakefile.toml`).
Its proof still uses the nine inputs listed in §W361.1 by name. All nine are now theorems or
definitions proved from Tau Ceti, so none of them appears in its axiom print. The seven ℚ₂ inputs
among them are proved by the adapters of the ℚ₂ campaign, merged here at ticket T0 (map:
[`../literature-axioms.md`](../literature-axioms.md) §T). The two `K`-level inputs are proved by
ticket C1':

| input | legacy name (`noncomputable def` in `GQ2/Foundations/TauCetiInstance.lean`) | adapter, file | Tau Ceti source at `↥K` (main declarations) |
| --- | --- | --- | --- |
| B5-K (AX3) | `GQ2.markedRecipAt K : Dyadic.MarkedRecip localReciprocity K` | `TauCetiBridge.markedRecipAt_tauceti`, `GQ2/TauCeti/B5K.lean`, on the dictionary `GQ2/TauCeti/GaloisDictK.lean` | `TauCeti.ClassFieldTheory.artinMap` with `continuous_artinMap`, `denseRange_artinMap`, `unramifiedCoordinate_artinMap`, and `artinMap_norm` (norm functoriality at `(ℚ₂, ↥K)`). The `ki_unramified` clause uses inertia ⊆ `ker ν_ur` (`unramifiedCoordinate_mk_eq_one_iff`) with `map_inertiaSubgroup_le_fixingSubgroup_iff` and `isUnramified_iff_normalizedValuation_comp_unitsMap_surjective`. |
| B10-K (AX4) | `GQ2.orientedTameQuotientAt K FF : Dyadic.OrientedTameQuotientK (markedRecipAt K) FF` | `TauCetiBridge.orientedTameQuotientAt_tauceti`, `GQ2/TauCeti/B10K.lean` | `TauCeti.wildInertiaSubgroup` (normal, closed, `isProP_wildInertiaSubgroup`) and `tameQuotientGeometricEquiv` with `exists_isArithFrobeniusLift`, `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top`, `iwasawaCoordinateGeometric_tameQuotientGeometricEquiv`. These go through the generic gq2 identification `iwasawaGeometricEquivTq : IwasawaGroupGeometric L ≃ₜ* Tq q` for `#𝓀[L] = q`. |

No Tau Ceti lemma was missing. The gaps were gq2-side lemmas, now in `GaloisDictK.lean` and the
two adapters:

- the norm ↔ valuation bridge on `↥K`;
- the topology comparison `localTopology_eq`;
- the residue count `#𝓀[↥K] = 2 ^ FF.f`;
- the closed-subgroup lemma for `ℤ₂` behind the level `r`;
- unramified ⇒ equal norm value groups;
- `IwasawaGroupGeometric ≃ₜ* Tq q`.

The recon memo [`tauceti-discharge-recon.md`](tauceti-discharge-recon.md) has the clause-by-clause
translation.

The mechanical checks are in `scripts/check_axioms.sh`:

- Checks 1 and 3 require census 0 (`EXPECTED_AXIOMS=0`, no `axiom` declaration in the library).
- Check 5b pins the endpoint, `GQ2.markedRecipAt`, `GQ2.orientedTameQuotientAt` and the seventeen
  older dyadic capstones of §A at exactly the standard three.
- Check 8 runs `GQ2/DyadicTauCetiAxiomAudit.lean`. It re-checks the two inputs and the endpoint at
  exactly the standard three in the environment of the whole dyadic tree. It also fails if that
  environment contains an axiom constant beyond Lean's own.

The trust-base change is the one owner gate G0 (2026-10-16) accepted for the ℚ₂ campaign: from
"cited theorems, stated in this repository as axioms" to "Tau Ceti's proofs of them". The dyadic
discharge plan, approved at gate G0' (2026-10-17), applies the same change to the two `K`-level
inputs. Tau Ceti is machine-written, and its own CI enforces zero sorries and an axiom allowlist.

**What did not change.** The eleven statements are byte-identical to the former axioms, so the
endpoint's statement and scope are as in §W361 and §W361.2. It still takes `RamifiedIData K` and
does not assert it for every finite `K`. It still runs on the flexible construction's words, not
the frozen M-word presentation. What changed is why the inputs hold.

### W361.1 Exact measured axiom sets

*Superseded 2026-10-17 (§W361.0): these sets were measured on 2026-09-17, at census 11. The
environment of the dyadic tree now contains no axiom constant beyond Lean's own. Every declaration
below therefore prints at most the standard three, and the endpoint prints exactly the standard
three (check 5b and check 8). The table and the paragraphs after it are kept as the historical
measurement.*

These are the default-limit `#print axioms` sets of the actual new declarations,
not a union guessed from their imported files. `std-3` means `propext`,
`Classical.choice`, and `Quot.sound`; B-labels remain those of historical §B.

| New declaration | Exact axiom set |
| --- | --- |
| `FieldFamilySpliceMarkedFinal.hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange` | std-3 ∪ {B1, B6, B7, B8, B9, B11a} |
| `FieldFamilySpliceMarkedCanonical.hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters` | std-3 ∪ {B1, B6, B7, B8, B9, B11a} |
| `FieldFamilySpliceMarkedCanonical.hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI` | std-3 ∪ {B1, B5, B5-K, B6, B7, B8, B9, B10-K, B11a} |
| `FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI` | the same std-3 plus nine set |
| `FieldFamilySpliceMarkedCanonical.hasSelectedFullyMarkedFlexibleAssemblyRN_oddDegree` | the same std-3 plus nine set |

Spelled out, the bare field endpoint's nine nonstandard names are:

- `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`;
- `GQ2.localReciprocity`;
- `GQ2.markedRecipAt`;
- `GQ2.tateDualityAt`;
- `GQ2.Foundations.absGalQ2_localEulerCharacteristic`;
- `GQ2.peripheralCyclotomicAction`;
- `GQ2.relativeStiefelWhitney_dyadic`;
- `GQ2.orientedTameQuotientAt`;
- `GQ2.hilbertSymbol_normCriterion_finiteDyadic`.

The generic-bundle endpoint omits precisely `localReciprocity`, `markedRecipAt`,
and `orientedTameQuotientAt`: it is supplied the corresponding bundles instead.
The bare wrapper invokes those established producers. **No new axiom is added**;
the foundational declaration census remains eleven, while this endpoint uses nine
of them (plus std-3). This is not a standard-three-only theorem of local fields.
The old Q2 and frozen-row prints in §A have not been changed by this new endpoint.

The new concrete pair/mobile splice certificates, generic tame-marked reconstruction,
and abstract character-calibration lemmas are standard-three. The canonical shared
field packet `compatibleRamifiedDataAt_of_norm_reciprocity` is a theorem from the
existing bundles and Tate duality; the formerly carried signed-Frobenius,
relative-norm, and odd-degree proof premises are not new axioms or remaining inputs
to the general field endpoint.

### W361.2 What is fixed and what is existential

The actual source word, core, degree, `nuP`, and certificate survive marking
calibration definitionally. Only the **existential realization** of the core in
the field's maximal pro-two quotient is calibrated to the reconstructed tame-marked
equivalence. This gives the literal pro-two squares on the same equivalence.
It is not a claim that reconstruction preserves any arbitrarily prescribed prior
realization pointwise.

The cyclotomic character is fixed using the original realization **before**
reconstruction: `AlignedMarkedFieldEquiv` retains that original character, and
`alignedRealization_chi_eq_original` proves that calibration does not change it.
`chiCycKTwo_characteristic_ramifiedI` supplies the needed intrinsic character
rigidity for all selected families. Thus cyclotomic compatibility is not obtained
by silently defining a new character after choosing the isomorphism.

The words are those carried by the flexible construction. M0 may use the new
promoted-handle pair splice; Mpc uses the normalized mobile tame splice. This
does **not** prove the universal old frozen M-word presentation. The historical
`GQ2/Dyadic/Main.lean` remains the frozen-quadratic entry point; `GeneralMain.lean`
is the additive general endpoint, with the changed-word qualification explicit.

### W361.3 Citation and acceptance status

*(2026-10-17: the formal axioms this section refers to no longer exist. B5-K and B10-K are proved
via Tau Ceti (§W361.0). The source audit below is now a record of which published statements the
Tau Ceti proofs establish. The owner gate G3 remains open.)*

This section records new proof/axiom measurements, not a new owner G-AX or G3
approval. The original refresh did not verify literature. The subsequent
[W361 source audit](w361-axiom-source-verification.md) now verifies the principal
AX3/AX4 primary-source statements and explains the finite-r and K(i) derivations;
it also flags the old AX3 proposal's overbroad `1+8Ztwo` claim. It leaves the
formal axioms, historical annotations, and approvals unchanged. Existing
source-audited markers on other rows are preserved, not independently
re-certified here.

The remaining specification and release work is recorded in
[w361-completion-audit.md](w361-completion-audit.md): revised M-word/source/marking
statements, the distinction between required marking corrections and stronger
historical stabilizer lifts, actual splice-word TeX/hash and certificate artifacts,
fresh integrated checks, and owner G3 sign-off. The old hash manifest and older
seventeen-capstone audit do not by themselves audit the new words or new headlines.

---

## A. The measured axiom surface

*Superseded 2026-10-17: these sets were measured on 2026-08-02, at census 11. Ticket T0 (census
11 → 2) set every row of check 5b's `AUDIT_DYADIC` block to exactly the standard three, which the
T1 gate run confirmed. Ticket C1' (census 2 → 0) added `GQ2.markedRecipAt`,
`GQ2.orientedTameQuotientAt` and the W361 endpoint to the block, also at exactly the standard
three. The `n = 1` twin pairs still print identically to the ℚ₂ capstone, which is now also at
the standard three. The tables and the invariants of §A.3 below are the historical
measurement.*

Abbreviations: **std-3** = `propext`, `Classical.choice`, `Quot.sound`.  B-labels as in §B.
Measurement: `collectAxioms`, sorted, at commit `482f89b` (`dyadic-as5`); the raw lists are
reproduced in check 5's `AUDIT_DYADIC` block, which re-measures them on every gate run.

### A.1 The final theorem and its assembly (new in AS5, `GQ2/Dyadic/Main.lean`)

| Declaration | Measured axiom set |
|---|---|
| `GQ2.Dyadic.ramifiedI_candidate_equiv_galK` (**the final ramified-`i` theorem**) | std-3 ∪ {B1, B6, B7, B9, B11a} |
| `GQ2.Dyadic.rowEquiv_sqrtNegTwo` | std-3 ∪ {B1, B6, B7, B9, B11a} |
| `GQ2.Dyadic.rowEquiv_sqrtTwo` / `_sqrtFive` / `_sqrtTen` / `_sqrtNegTen` | std-3 ∪ {B1, B6, B7} (all four identical) |
| `GQ2.Dyadic.candidate_equiv_galK_of_frozenRow_certificates` (uniform certificate gate) | std-3 ∪ {B1, B6, B7} |
| `GQ2.Dyadic.wordCertificate_nonempty_lSq` | std-3 ∪ {B3c, B5, B8} |
| `GQ2.Dyadic.wordCertificate_nonempty_sqrtNegTwo` | **exactly std-3** |
| `GQ2.Dyadic.lRow_candidate_equiv_absGalQ2` (`n = 1` endpoint re-export) | std-3 ∪ {B1, B3c, B5, B6, B7, B8, B9, B10, B11a} — **byte-identical to `GQ2.main_presentation_literal_roe_unconditional`** |
| audit layer (`frozenQuadRow_branch_cases`, `no_frozen_Npc`, `no_frozen_L`, `FrozenQuadRow.branch_valid`, `branch_compatible`, `sqrtNegTen_branch_eq_branchSqrtNegTen`) | exactly std-3 |

The final theorem's set is **exactly the union of the six instance headlines' sets** — the
assembly added nothing.  ⚠ Note for G3: `ramifiedI_candidate_equiv_galK` prints the *pilot's*
set because the pilot row is one of its five cases; the four `M`-row cases alone sit at the
strictly smaller std-3 ∪ {B1, B6, B7}.

### A.2 The instance headlines and the `n = 1` routes (upstream, re-measured at this tree)

| Declaration | Measured axiom set |
|---|---|
| `GQ2.Dyadic.SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` (pilot headline) | std-3 ∪ {B1, B6, B7, B9, B11a} |
| `GQ2.Dyadic.Instances.candidate_equiv_galK_sqrtTwo` / `_sqrtFive` / `_sqrtTen` / `_sqrtNegTen` | std-3 ∪ {B1, B6, B7} (all four identical) |
| `GQ2.Dyadic.candidate_equiv_galK_of_supply` (ASK's packet-Thm-1.1-at-`K`) | std-3 ∪ {B1, B6, B7} |
| `GQ2.Dyadic.QTwo.candidateGroup_lSq_equiv_absGalQ2` (n=1 route 1, via the frozen capstone) | the frozen ℚ₂ 9-set (= A.1's `lRow…` row) |
| `GQ2.Dyadic.QTwo.candidateGroup_lSq_equiv_absGalQ2_via_sourcesN` (route 2, via the dyadic recursion) | the frozen ℚ₂ 9-set |
| `GQ2.Dyadic.candidateGroup_lSq_equiv_absGalQ2_via_wordCertificate` (route 3, via the `WordCertificate`) | the frozen ℚ₂ 9-set |
| `GQ2.Dyadic.SqrtNeg2.sqrtNegTwoWordCertificate` (the pilot certificate) | **exactly std-3** |
| `GQ2.Dyadic.wordCertificateLSq` (the `n = 1` certificate) | std-3 ∪ {B3c, B5, B8} (= `sourceR_N`'s set — packaging cost zero) |

All three `n = 1` routes print **byte-identically** to
`GQ2.main_presentation_literal_roe_unconditional` (verified in the same probe run).

### A.3 Global invariants (measured, and gate-enforced)

* **B5-K and B10-K appear in no historical §A print above.** At that snapshot they entered only through the
  *types* of the arithmetic-bundle binders (`B : MarkedRecip Rec K`,
  `FF : DyadicUnitFiltration K`, `T : OrientedTameQuotientK B FF`) that every K-side statement
  quantifies over; the axioms exist so that a caller *can* produce such bundles at a concrete
  `K` (see §B rows B5-K/B10-K and §C.0). The W361 canonical wrappers now invoke those
  producers, so both appear in the new bare field endpoint's print (§W361.1).
* **No `sorryAx` anywhere**; zero sorries repo-wide (check 2, allowlist empty).
* **Census = 11** (`EXPECTED_AXIOMS`, check 3); the frozen ℚ₂ capstone audit (check 5's
  original block) is untouched and still passes with its 9-set byte-identical.
  *(Superseded: census 2 from T0, 0 from C1', 2026-10-17. Check 5's ℚ₂ capstones and every check-5b
  row are now at exactly the standard three.)*

---

## B. The axiom census (11 rows)

**Status (2026-10-17): none of the eleven rows is an axiom.** `GQ2/Foundations/Axioms.lean` is
deleted, and every name below is a theorem or definition in `GQ2/Foundations/TauCetiInstance.lean`
proved from Tau Ceti at revision `706344c35`, with its statement byte-identical to the former
axiom:

- the nine ℚ₂ rows since ticket T0 (census 11 → 2). Their adapters are those of the ℚ₂ campaign,
  `GQ2/TauCeti/{B1,B3c,B5,B6,B7,B8,B9,B10,B11a}.lean`, listed in `docs/literature-axioms.md` §T;
- the two `K`-level rows since ticket C1' (census 2 → 0), shown in the second table below.

The citation and role columns are unchanged, as the record of the axiom period.

The Lean names below are the exact `axiom` declarations in `GQ2/Foundations/Axioms.lean`
(the only file allowed to contain them — check 1).  "Dyadic role" states where the axiom
enters *this* campaign's tree; "print appearances" is measured (§A).

### The nine ℚ₂-side axioms (frozen; citations per `docs/literature-axioms.md`, markers quoted)

| # | Lean axiom | Statement (one line) | Citation (status as recorded in `literature-axioms.md`) | Dyadic role |
|---|---|---|---|---|
| B1 | `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | `G_ℚ₂` is topologically finitely generated (`[K:ℚ_p]+2` generators) | NSW Ch. VII §7.4, Thm (7.4.1) `[✓ source-audited]` | feeds SD3's reconstruction through `AbsGalQ2`-anchored layers; in every K-side headline print |
| B3c | `GQ2.dyadicOrientation` | composite orientation interface: Labute's rank-3 dyadic Demushkin normal form + canonical character | Labute, Canad. J. Math. 19 (1967), Thm 8 (§5) + Thm 4 case (2) `[✓ verified in the provided source]`; attributed to Serre | ℚ₂ capstone census only — enters the dyadic tree through the three `n = 1` routes, **not** through any K-side headline |
| B5 | `GQ2.localReciprocity` | local reciprocity `ℚ₂ˣ → G_ℚ₂^{ab}` (dense, Frobenius-normalized) | NSW Ch. VII §7.1, (7.1.1)/(7.1.5) `[✓ verified in the provided NSW]`; Serre LF Part IV | as B3c; also the `Rec : LocalReciprocity` *slot* every `MarkedRecip` bundle refers to |
| B6 | `GQ2.tateDualityAt` | local Tate duality bundle at any open finite-index local `G ↪ G_ℚ₂` (base-generalized 2026-07-06) | NSW Ch. VII §7.2, Thm (7.2.6) `[✓ verified]`; Serre GC II §5.2 Thm 2 `[✓]`; FV IV §5 for the Hilbert-pairing content `[✓]` | **the K-side workhorse**: `FieldData.tateDualityGalK K` = this axiom at `G_K`; in every K-side headline print |
| B7 | `GQ2.Foundations.absGalQ2_localEulerCharacteristic` | local Euler–Poincaré characteristic (`χ(k,A) = ‖#A‖_k`) | NSW Ch. VII §7.3, Thm (7.3.1) `[✓ verified]`; Serre GC II §5.7 Thm 5 `[✓]` | `absGalK_localEulerCharacteristic` and LG5's Euler clause; in every K-side headline print |
| B8 | `GQ2.peripheralCyclotomicAction` | outer Galois action on `π₁^{pro-2}(ℙ¹∖{0,1,∞})`, cyclotomic on peripheral inertia | Stix, ASPM 63 (2012), §3.3 + Def. 37 `[✓ verified]` (origin: Deligne, MSRI 16 (1989)) | ℚ₂ capstone census only — through the `n = 1` routes |
| B9 | `GQ2.relativeStiefelWhitney_dyadic` | relative Stiefel–Whitney (Evens–Kahn) identity, quadratic-form level (B9-A restatement 2026-07-24) | Evens, Trans. AMS 108 (1963), Thm 1 `[✓]`; Kahn, Invent. Math. 78 (1984), Thms 1–3 `[✓]`; Kozlowski, Proc. AMS 91 (1984), Thm 1.1 (corroborating) | CB-DET's K-side determinant bridge (`affineDeterminant_galK`) consumes it (via B11a); hence in the **pilot** headline print (where `KSupply.determinant` is discharged) but **not** in the `M`-row prints (where `determinant` is still carried inside the `KS` binder) |
| B10 | `GQ2.tameQuotient` | oriented tame quotient of `G_ℚ₂` (`G/W ≅ T₂`, orientation clauses) | NSW (7.5.3)/(7.5.2); Serre LF XIII §4 Prop. 13 + corollary | ℚ₂ capstone census only — through the `n = 1` routes; the K-side analogue is B10-K |
| B11a | `GQ2.hilbertSymbol_normCriterion_finiteDyadic` | Hilbert-symbol norm criterion over finite dyadic fields | Serre LF XIV §2, Props. 4(iii), 5, 7(iii) | with B9 inside CB-DET's bridge; in the pilot headline print, not the `M`-row prints |

*(B2, B4, B7′, B11b, B12, B13 were discharged or deleted before this campaign — history in
`literature-axioms.md` and the check-3 census comment.  There is no ℚ₂-side row they occupy.)*

### The two K-side inputs (axioms from gate G-AX, 2026-07-29, census 9 → 11; proved via Tau Ceti since ticket C1', 2026-10-17, census 2 → 0)

| # | Lean name (axiom until 2026-10-17) | Statement (one line) | Citation — **UNVERIFIED** (owner Q7: targets approved, PDFs not checked; historical, see the W361 [source audit](w361-axiom-source-verification.md)) | Dyadic role | Lean status since 2026-10-17 |
|---|---|---|---|---|---|
| B5-K | `GQ2.markedRecipAt` | for every finite `K/ℚ₂` (as `IntermediateField ℚ_[2] ℚ̄₂`): a `MarkedRecip Rec K` — marked local reciprocity with full `ℤ₂`-valued `ν_ur^K`, unit/uniformizer normalization, norm functoriality, `ki_unramified` clause | NSW (7.1.1)/(7.1.5) at base `K`; Serre LF Ch. XI §3 (norm functoriality), Ch. XIII §4 Prop. 13 + corollary (unit normalization); cyclotomic-tower ramification Serre LF Ch. IV / NSW VII §7.5 — **all UNVERIFIED** (proposal `docs/dyadic/ax3-proposal.md` §6) | **producer of the `B` binder.** Absent from the historical §A headline prints; consumed by the W361 canonical bare-field endpoints (§W361.1). | **Proved via Tau Ceti** (ticket C1'). It is a `noncomputable def` in `GQ2/Foundations/TauCetiInstance.lean` whose body is `TauCetiBridge.markedRecipAt_tauceti K` (`GQ2/TauCeti/B5K.lean`, on `GQ2/TauCeti/GaloisDictK.lean`). Sources: Tau Ceti's local class field theory at `↥K` (`artinMap`, `unramifiedCoordinate`, `artinMap_norm`, inertia ⊆ `ker ν_ur` through `map_inertiaSubgroup_le_fixingSubgroup_iff`; §W361.0). Prints exactly the standard three (check 5b, check 8). |
| B10-K | `GQ2.orientedTameQuotientAt` | for every finite `K/ℚ₂` with a `MarkedRecip` and a `DyadicUnitFiltration`: an `OrientedTameQuotientK B FF` — `G_K/W_K ≅ T_{q_K}` with orientation clauses at `q_K = 2^{f_K}` | NSW (7.5.3) (Iwasawa) at base `K`, with (7.5.2); Serre LF Ch. IV (wild part), Ch. XIII §4 Prop. 13 (orientation) — **all UNVERIFIED** (proposal `docs/dyadic/ax4-proposal.md` §§5–6) | **producer of the `T` binder** (`FieldInputs.T`). Absent from the historical §A headline prints; consumed by the W361 canonical bare-field endpoints (§W361.1). | **Proved via Tau Ceti** (ticket C1'). It is a `noncomputable def` in `GQ2/Foundations/TauCetiInstance.lean` whose body is `TauCetiBridge.orientedTameQuotientAt_tauceti K FF` (`GQ2/TauCeti/B10K.lean`). Sources: Tau Ceti's `wildInertiaSubgroup` at `↥K` and the geometric Iwasawa presentation, through `tameQuotientGeometricEquiv` and gq2's `iwasawaGeometricEquivTq : IwasawaGroupGeometric ↥K ≃ₜ* Tq q` (§W361.0). Prints exactly the standard three (check 5b, check 8). |

⚠ **The soundness-critical parametrization** (AX4 Q2, owner-confirmed): B10-K is quantified
over the `DyadicUnitFiltration` bundle `FF`, so `q_K` enters as `qOf K FF = 2^{FF.f}` — the
axiom cannot be instantiated at a wrong residue degree without supplying a wrong filtration,
which B13's discharged theorem prevents at ℚ₂ and AS-F must respect at literal `K`.
*(Since 2026-10-17 the parametrization is also what the proof uses. B10K.lean identifies Tau
Ceti's relator at `Nat.card 𝓀[↥K]` with gq2's at `qOf K FF` through A1-K's
`natCard_residueField_eq_two_pow : #𝓀[↥K] = 2 ^ FF.f`.)*

---

## C. The residual hypothesis-binder surface (complete enumeration)

Everything below is a **binder** — it appears in a theorem's *statement*, contributes nothing
to `#print axioms`, and must be supplied by whoever instantiates the theorem.  G3 signs
knowing this list is the *entire* distance between the landed statements and packet Thm 1.1's
prose form.  Layout: one subsection per layer, innermost (per-row) last.  Every field named
here carries a provenance docstring at its declaration site (`GQ2/Dyadic/Main.lean` §3, the
instance files, `KSupply.lean`).

### C.0 The arithmetic-bundle binders (every K-side statement)

| Binder | Type | Producer | Notes |
|---|---|---|---|
| `K` | `IntermediateField ℚ_[2] ℚ̄₂` + `[FiniteDimensional ℚ_[2] K]` | caller (AS-F probing literal fields) | **superseded 2026-08-02 (AS-F/AS-F2 — see §C.7)**: concrete quadratic fields now exist (`Fields.quadField a = ℚ_[2]⟮√a⟯`; rows `KSqrtNegTwo` … `KSqrtNegTen`) and four rows carry literal instantiations printing byte-identically to their parametrized parents; the parametrized-over-`K` headlines remain the primary form |
| `Rec` | `LocalReciprocity` | B5 (`GQ2.localReciprocity`) or abstract | slot only |
| `B` | `MarkedRecip Rec K` | **B5-K** at a literal `K`; abstract otherwise | not consumed as an axiom by the historical §A headlines; invoked by the W361 canonical wrappers |
| `FF` | `DyadicUnitFiltration K` | B13's discharged construction at ℚ₂; caller at `K` | fixes `q_K = qOf K FF` |
| `T` | `OrientedTameQuotientK B FF` | **B10-K** at a literal `K`; abstract otherwise | = `FieldInputs.T` |

*(2026-10-17: the producers named in this table are no longer axioms. `localReciprocity` (B5),
`markedRecipAt` (B5-K) and `orientedTameQuotientAt` (B10-K) are definitions proved from Tau
Ceti (§B, §W361.0). The rows still describe binders: a historical headline that quantifies over
`B` and `T` still does so.)*

### C.1 Row-independent field-side inputs (`GQ2.Dyadic.FieldInputs`, packet §12)

| Field | Content | Status / discharge path |
|---|---|---|
| `params`, `params_n`, `params_qK` | F1's `(n, f, q_K)` package pinned to the slot (`n = 2`, `q_K = qOf K FF`) | data; at a literal quadratic `K`, `paramsRamifiedQuadratic` / the `q_K = 4` package (F1) with `rfl` pins |
| `ramified` | the standing ramified-`i` hypothesis, spelled `∀ δi, δi² = −1 → ¬ HasEqualNormValueGroups K δi` (AX3 Q4 ruling; **never through `qK`** — `ℚ₂(√5)` has `q_K = 4` yet `i ∉ K`) | the campaign's defining hypothesis; a caller proves it per field |
| `ramifiedData` | LG5's ramified-marking input in the `hcert` shape `local_gauss_K` consumes | intended constructor `ramifiedCertificateOfSubtype` (LG5), whose binder list is the actual arithmetic content |
| *(discharged, no longer binders)* | `2 ≤ q_K`, `Even q_K`, `hqK` | `two_le_qOf`/`even_qOf` (ASK §5) discharge the first two; AS5's assembly consumes the headlines at `q := qOf K FF`, `hqK := rfl`, so **no `hqK` pin survives in the final theorem** |

### C.2 The pilot row (`ℚ₂(√−2)`, compact `N`): `GQ2.Dyadic.ResidualSqrtNegTwo`

The deepest-discharged row: `KSupply` is *built* (`sqrtNegTwoKSupply`), the marked-core
composite is written down (MC-N's `marked_matching_certificate_KN` consumed), and CB-DET's
`affineDeterminant_galK` discharges `KSupply.determinant`.  What remains:

| Field | Layer | Provenance / discharge path |
|---|---|---|
| `hdeg` | pin | `[K : ℚ₂] = 2`; AS-F at a literal field |
| `fLab` | **G-Lab pack** | the Labute/Demushkin identification `D_N(2,0) ≅ G_K(2)` — obligation **MC-N**'s per-core hypothesis state (gate G-Lab, plan A3); never an axiom |
| `piAb`, `hpiAb`, `hpiNu` | **G-Lab pack** | the abelianization slot — **AS2's discovered missing datum**: `toAbK` does *not* factor through `G_K(2)` (the abelianization is not pro-2), so the composite needs the pro-2 direct-factor inclusion as data.  Dischargeable later by a small direct-factor lemma (owner-visible queue item (e)) |
| `horient` | **G-Lab pack** | packet §7's orientation datum |
| `hScal` | **G-Lab pack** | MC-N's `NScalingHypothesis 2 0` (the M-side analogue `MMixHypothesis` would enter only via a future M-row composite; see C.3) |
| `hpair` | **G-Lab pack** | marked-data pair-unimodularity |
| `hexact` | **ASK carried leaf 2** | `ExactLiftingSemantics` at `G_K` — `KSupply.lean` §6 item 2 (ℚ₂ ancestors: `MStageCount.liftsOver_card_local`, `lemma_8_6_local`, `RStageLocal.stageR136_local`); natural first targets since both inputs (`absGalK_localEulerCharacteristic`, `tateDualityGalK`) exist at `K` |
| `hstokes` | **ASK carried leaf 3** | `StokesDualityCertificate` at `G_K` — `KSupply.lean` §6 item 3; right shape = a Γ-generic `prop_5_16` over a `TateDualityG Γ 2` bundle + Euler-char hypothesis (ASK's design note), **not** a K-clone |

**[W82-HOUSE, as of `a45bc557`: those two rows are SUPERSEDED, and this matters here more than
anywhere else, because this file is the trust boundary a reviewer reads.**  Both are theorems
at `G_K`, neither by a clone:

| binder | status at this tree | supplier |
|---|---|---|
| `hstokes` | **theorem**, hypothesis `hdeg` only | `stokesDualityCertificate_galK` (`Instances/KAnalytic.lean:82`), over `Count/LocalDuality.lean`'s `Γ`-generic layer.  The "right shape" this row predicted is what was built |
| `hexact` | **one named `Prop`**, `askCStageVanishing` | `liftsOver_card_galK`, `lem86_galK_of_noDescent`, `correctedRStageSemantics_galK` give `ExactLiftingSemanticsRN` at every degree; the frozen bundle differs by the equation-(136) coefficient and `askC_exactLifting_iff_stageVanishing` makes the two the same statement at `2 ≤ n` |

Neither supplier introduces an axiom: measured, `askC_stokes_galK` is std-3 plus `tateDualityAt`
(B6) plus `absGalQ2_localEulerCharacteristic` (B7), and `askC_halfTorsor_galK` is std-3 plus B6
plus `absGalQ2_isTopologicallyFinitelyGenerated` (B1) and **no B7**.  So the trust boundary does
not move; what moves is the residual surface.  ⚠ One thing a reviewer should be told and this
file does not yet say: `askC_isEmpty_boundaryLifts_of_exactLifting` derives from the *frozen*
field, at `2 ≤ n`, that `G_K` admits no boundary-framed surjection onto any marked target with
nontrivial Frattini block.  So `hexact` as currently spelled is a strong assertion about `G_K`,
not a routine counting binder, and the recommended repair is the statement change to
`ExactLiftingSemanticsRN` (`docs/dyadic/w81-ask-note.md` §3.1).  Row `hdet` below is unaffected
and remains the largest genuinely unowned residual.]**
| `hsimp` | **candidate residual** | per-simple-module Stokes duality (`PilotHsimp`) — **owner ruling B1/Q3: stays a hypothesis binder, never an axiom**; feeds every count-lane payload (CB-5 §5, `hsepN_marking`) |
| `hsplit`, `hZcount` | **candidate residual** | `stageR136`'s recursion-side inputs (`PilotStageSep`/`PilotStageZ`), verbatim `blockStageR136K`'s open inputs — owner-visible queue item (b) |
| `hdet` | **candidate residual** ⚠⚠ | `PilotDet` — the candidate-side Gauss-`Z` clauses.  **The largest single residual**: the CB lane's "clause list COMPLETE" is 9-of-11 clause *suppliers* — CB1's priced candidate-side gauss tickets (~1900 ln) were **never opened**; CB-DET is K-side only.  The missing lane is the Hessian ⇒ `GaussZResidueK` bridge over WN0-c's landed word-side layer.  Owner-visible queue item (a) |

### C.3 The four `M` rows (`√2`, `√5`, `√10`, `√−10`): `GQ2.Dyadic.ResidualSqrt{Two,Five,Ten,NegTen}`

Shallower-discharged than the pilot (AS3 took `KSupply` wholesale; no M-row analogue of
`sqrtNegTwoKSupply` exists yet — writing one would consume MC-M's certificate and surface
`MMixHypothesis` the way the pilot surfaced `NScalingHypothesis`):

| Field | Layer | Provenance / discharge path |
|---|---|---|
| `nuP`, `hnuSigma`, `hnuWild`, `hnuP` | ν-binders | the abstract slot's ν-normalization, F3's `prop_3_4_three` conditions through AS3's dictionaries (`MCompactCore`/`MProcyclicCore`).  ⚠ **ticket AS3-b is discharging these in flight** (satisfiability witness via the `maxProPQuotient` commutativity lemma).  *If AS3-b merges first*: the binders likely remain in the headline signatures with in-tree witnesses making them dischargeable — update this row to "witnessed (AS3-b), binder retained" and nothing else changes; *if it does not merge*: satisfiability is hand-verified only (AS3's report) |
| `exactLifting`, `stokes`, `scalar`, `determinant` | **the four analytic clauses** | AS1 divergence 4: the branch lanes closed Fox rows / Stokes endpoints / scalar Grams / Hessian certificates, but the certificate ⇒ **count** bridges have no owner.  See C.4 for the per-clause ledger |
| `KS : KSupply T 2 core hP nuP SN` | **ASK's package, carried whole** | its own carried leaves (`KSupply.lean` §6): the pro-2 block `pro2`/`hpro2`/`ker_pro2`/`nu_compat` (= the marked-core composite, **owed by the M-row analogue of AS2's §6**, consuming MC-M's `marked_matching_certificate_KM`), `exactLifting`/`stokes` (= C.2's `hexact`/`hstokes` at the M cores), and `determinant` (dischargeable by CB-DET's `affineDeterminant_galK` — done in-tree at the pilot; at the M rows left to the caller) |

### C.4 The clause-discharge ledger (what would close C.2/C.3's candidate-side clauses)

Recorded once, from `CertificateMain.lean`'s obligation inventory + the WMP/WW4 rows; every
item is a *proof* obligation (binder or future theorem), never an axiom:

* **`hsimp`** — per-simple-module Stokes duality; carried by all five branches (the eight
  AS3 fold-ins land its per-row payloads at `T` and `Vmod`; the pilot's two land via
  CB-6/CB-5).  Owner-ruled binder.
* **Fox ⇒ `#LiftsOver`** (exactLifting): ℚ₂ ancestor `GQ2/MStageCount.lean` +
  `GQ2/RadicalEdge/`; no general-`K` owner.
* **duality ⇒ count** (stokes): plus WW4 gap item 3 (per-χ shifts), the cited gate-F
  witness, and P4's central clause per module (not expressible at the `PWord` layer).
* **Gram ⇒ `#Hom`** (scalar): candidate side only — the arithmetic side is **proved**
  (ASK's `card_hom_zmodTwo_galK`, `ScalarHilbertCertificate` at `G_K`).
* **Hessian ⇒ `GaussZResidueK`** (determinant) ⚠⚠: the never-opened CB1 gauss lane (= C.2's
  `hdet` caveat); additionally WW4 gap item 5 (`HessRelZTarget` needs the unowned
  `NpcJet ↔ WordCoh` bridge), **L has no `HessianCertificate` at all** (endpoint `qDouble`),
  and **`Mpc.hlinrow` is closed only at `√−10`** (no `√10` twin — the two procyclic fields
  sit at different depths; not a `WordCertificate` field, so the inventory stands).

### C.5 The `n = 1` row: **no residual surface**

`lRow_candidate_equiv_absGalQ2` (all three routes) and `wordCertificateLSq` are
**unconditional**: no hypothesis binders, no instance binders beyond file-local topology
instances.  B-Lab is the proved `GQ2.Roe.Labute.bLab`.  This row is what the campaign's
"recovers the ℚ₂ theorem" claim rests on, and it is closed.

### C.6 The `Npc` shape: **no instance at all** (the recorded gap)

`GQ2.Dyadic.no_frozen_Npc` is a theorem: no frozen row is on the procyclic-`N` shape.  The
frozen word and its certificate layers exist (`Words/Npc.lean`, WNP lanes, the corrected
cross-operator theorem `npc_cross_operators`); missing are a `CoreReindex` dictionary, a
`WordCertificate` constructor, and any frozen field on the row.  The packet's fully general
"every branch" statement is exactly this far from the landed
`ramifiedI_candidate_equiv_galK`.  (AS3's related finding also stands: the procyclic-`M`
dictionary needs `η = 1` — a `.hat`-display instance needs a new construction or an
η̂-invertibility hypothesis.)

### C.7 The literal fields: four headlines, instantiated (tickets AS-F, AS-F2)

`GQ2/Dyadic/Instances/Fields.lean` builds `ℚ₂(√a) = ℚ_[2]⟮√a⟯` inside `ℚ̄₂` as a literal
`IntermediateField`, and with it the campaign's five rows `KSqrtNegTwo`, `KSqrtTwo`,
`KSqrtFive`, `KSqrtTen`, `KSqrtNegTen`.  ⚠ **This supersedes C.0's "no concrete field object
exists in the repo" note**, which was accurate when §C was written and no longer is; the rest of
the C.0 table stands unchanged — `B`, `FF` and `T` are still binders at every row, including the
literal ones.

Four headlines are now stated at a **literal** field, with every field-arithmetic binder
discharged from that field's own arithmetic and nothing else:

| Literal theorem (`GQ2.Dyadic.Fields.…`) | Parent | Measured axiom set |
|---|---|---|
| `sqrtNegTwo_candidate_equiv_galK_literal` (AS-F) | `SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` | std-3 ∪ {B1, B6, B7, B9, B11a} |
| `candidate_equiv_galK_sqrtTwo_literal` (AS-F2) | `Instances.candidate_equiv_galK_sqrtTwo_nonvacuous` | std-3 ∪ {B1, B6, B7} |
| `candidate_equiv_galK_sqrtTen_literal` (AS-F2) | `Instances.candidate_equiv_galK_sqrtTen_nonvacuous` | std-3 ∪ {B1, B6, B7} |
| `candidate_equiv_galK_sqrtNegTen_literal` (AS-F2) | `Instances.candidate_equiv_galK_sqrtNegTen_nonvacuous` | std-3 ∪ {B1, B6, B7} |

Every print is **byte-identical to its parent's** (§A.2).  Specializing to a literal field costs
no axiom, and in particular introduces neither B5-K nor B10-K, so §A.3's global invariant is
untouched.  The three AS-F2 rows take AS3-b's `_nonvacuous` corollaries as parents, so their
ν-binders (C.3, row 1) are already gone before specialization.

**What this is evidence for.**  AS-F's finding, confirmed at three further rows by AS-F2: the
binders a literal field can discharge are exactly `hdeg`, `params`/`params_qK`, `ramified`, and
— at the `M` rows — the pin `hqK`, which also makes the *conclusion* literal (`candidateGroup
2 2 R`, with no `qOf` left in it).  **Nothing else in a headline moved.**  The residual surface
at a literal `K` is therefore not "arithmetic that has not been done yet": it is exactly the
Galois/CFT layer — `ramifiedData` (C.1) together with the AX3/AX4 bundles `B` and `T`, i.e.
B5-K and B10-K, local class field theory over a general local base, which Mathlib does not
have.  That is the owner-approved endstate of the census (§B, gate G-AX), and these four
theorems are the first *measured* evidence for it rather than an argument for it.
*(Superseded 2026-10-17: that layer is now supplied by Tau Ceti's local class field theory at
`↥K`, which proves B5-K and B10-K (ticket C1', census 0; §B, §W361.0). Mathlib still does not
have it.)*

⚠ One asymmetry worth recording: the three AS-F2 rows consume **no `hdeg`**.  The pilot builds
its own `KSupply` (`sqrtNegTwoKSupply hdeg …`) and so carries `hdeg : finrank ℚ_[2] K = 2` as a
binder (C.2, row 1); the `M`-row headlines carry `KSupply` itself as a binder (C.3, row 3), so
the degree enters only inside a package nobody has built yet.  `Fields.finrank_KSqrtTwo`,
`finrank_KSqrtTen` and `finrank_KSqrtNegTen` are proved and waiting: whoever writes the `M`-row
`KSupply` producer consumes them then, with no change to the four statements above.

---

## D. Historical AS5 G3 checklist

This is the preserved AS5 checklist. For the new general endpoint use §W361 and
the completion audit; this historical list is not a recorded W361 owner approval.
*(Items 1 and 2 are superseded as of 2026-10-17: census 0, and every check-5b print at exactly the
standard three, as described in the status note at the top and §W361.0.)*

1. **Census 11** (§B): 9 frozen ℚ₂ + B5-K + B10-K; `EXPECTED_AXIOMS = 11`; K-side citations
   remain UNVERIFIED per Q7; no obligation appears as an axiom (D2 guard green).
2. **Measured prints** (§A): final theorem = std-3 ∪ {B1, B6, B7, B9, B11a}; `M`-rows and
   the uniform gate = std-3 ∪ {B1, B6, B7}; `n = 1` = the frozen ℚ₂ 9-set byte-identical to
   the capstone; certificates at std-3 (pilot) and std-3 ∪ {B3c, B5, B8} (`n = 1`); B5-K and
   B10-K in **none of those historical prints**. All of these are check-5 entries (`AUDIT_DYADIC`), so any
   growth fails `scripts/check_axioms.sh` mechanically.
3. **The residual surface** (§C) is the complete distance to packet Thm 1.1's prose form:
   bundles (C.0), packet §12 inputs (C.1), the pilot's 14 named binders (C.2), the M rows'
   ν-binders + four clauses + carried `KSupply` (C.3), the clause ledger (C.4), zero at
   `n = 1` (C.5), and the `Npc` gap (C.6).
4. **Known in-flight change**: AS3-b (ν-witnesses + core hoist + a docstring fix) — C.3's
   ν-row is written to be updated either way; the core hoist preserves fully-qualified names,
   so §A/§B are unaffected.
