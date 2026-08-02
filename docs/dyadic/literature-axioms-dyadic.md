# Trust boundary for the dyadic campaign (ramified-`i` case) — census and residual surface

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
* **§C — the residual hypothesis-binder surface**: everything the theorems *quantify over*
  rather than assume.  Binders contribute **nothing** to an axiom print; they are the honest
  "givens" a caller must supply, and this section enumerates all of them with provenance and
  discharge status.  **The nine campaign obligations live here and never in §B** (board
  protocol; `scripts/check_dyadic.sh` D2 enforces it textually).

**Citation-status discipline** (owner ruling G-AX Q7, 2026-07-29): the two K-side axiom rows
(B5-K, B10-K) carry citations **UNVERIFIED against source PDFs** — the owner approved the
citation *targets* without a detail-check, and the house "verified against PDFs" phrasing must
not be written for them.  The nine ℚ₂-side rows keep the verification markers they already
have in `docs/literature-axioms.md` (many are `[✓ source-audited]` from the T-20/B9-A passes);
those markers are *quoted*, not re-audited here.

---

## A. The measured axiom surface

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

* **B5-K and B10-K appear in NO print above.**  They enter the development only through the
  *types* of the arithmetic-bundle binders (`B : MarkedRecip Rec K`,
  `FF : DyadicUnitFiltration K`, `T : OrientedTameQuotientK B FF`) that every K-side statement
  quantifies over; the axioms exist so that a caller *can* produce such bundles at a concrete
  `K` (see §B rows B5-K/B10-K and §C.0).
* **No `sorryAx` anywhere**; zero sorries repo-wide (check 2, allowlist empty).
* **Census = 11** (`EXPECTED_AXIOMS`, check 3); the frozen ℚ₂ capstone audit (check 5's
  original block) is untouched and still passes with its 9-set byte-identical.

---

## B. The axiom census (11 rows)

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

### The two K-side axioms (added at gate G-AX, 2026-07-29; census 9 → 11)

| # | Lean axiom | Statement (one line) | Citation — **UNVERIFIED** (owner Q7: targets approved, PDFs not checked) | Dyadic role |
|---|---|---|---|---|
| B5-K | `GQ2.markedRecipAt` | for every finite `K/ℚ₂` (as `IntermediateField ℚ_[2] ℚ̄₂`): a `MarkedRecip Rec K` — marked local reciprocity with full `ℤ₂`-valued `ν_ur^K`, unit/uniformizer normalization, norm functoriality, `ki_unramified` clause | NSW (7.1.1)/(7.1.5) at base `K`; Serre LF Ch. XI §3 (norm functoriality), Ch. XIII §4 Prop. 13 + corollary (unit normalization); cyclotomic-tower ramification Serre LF Ch. IV / NSW VII §7.5 — **all UNVERIFIED** (proposal `docs/dyadic/ax3-proposal.md` §6) | **producer of the `B` binder.**  Consumed by *no* theorem in the tree today (measured: appears in no print).  Its purpose is instantiation: a caller at a literal `K` uses it to supply `B : MarkedRecip Rec K` |
| B10-K | `GQ2.orientedTameQuotientAt` | for every finite `K/ℚ₂` with a `MarkedRecip` and a `DyadicUnitFiltration`: an `OrientedTameQuotientK B FF` — `G_K/W_K ≅ T_{q_K}` with orientation clauses at `q_K = 2^{f_K}` | NSW (7.5.3) (Iwasawa) at base `K`, with (7.5.2); Serre LF Ch. IV (wild part), Ch. XIII §4 Prop. 13 (orientation) — **all UNVERIFIED** (proposal `docs/dyadic/ax4-proposal.md` §§5–6) | **producer of the `T` binder** (`FieldInputs.T`).  Same posture: appears in no print; exists for instantiation at a literal `K` (ticket AS-F's lane) |

⚠ **The soundness-critical parametrization** (AX4 Q2, owner-confirmed): B10-K is quantified
over the `DyadicUnitFiltration` bundle `FF`, so `q_K` enters as `qOf K FF = 2^{FF.f}` — the
axiom cannot be instantiated at a wrong residue degree without supplying a wrong filtration,
which B13's discharged theorem prevents at ℚ₂ and AS-F must respect at literal `K`.

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
| `B` | `MarkedRecip Rec K` | **B5-K** at a literal `K`; abstract otherwise | never consumed as an axiom by the landed theorems |
| `FF` | `DyadicUnitFiltration K` | B13's discharged construction at ℚ₂; caller at `K` | fixes `q_K = qOf K FF` |
| `T` | `OrientedTameQuotientK B FF` | **B10-K** at a literal `K`; abstract otherwise | = `FieldInputs.T` |

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

⚠ One asymmetry worth recording: the three AS-F2 rows consume **no `hdeg`**.  The pilot builds
its own `KSupply` (`sqrtNegTwoKSupply hdeg …`) and so carries `hdeg : finrank ℚ_[2] K = 2` as a
binder (C.2, row 1); the `M`-row headlines carry `KSupply` itself as a binder (C.3, row 3), so
the degree enters only inside a package nobody has built yet.  `Fields.finrank_KSqrtTwo`,
`finrank_KSqrtTen` and `finrank_KSqrtNegTen` are proved and waiting: whoever writes the `M`-row
`KSupply` producer consumes them then, with no change to the four statements above.

---

## D. What G3 signs

1. **Census 11** (§B): 9 frozen ℚ₂ + B5-K + B10-K; `EXPECTED_AXIOMS = 11`; K-side citations
   remain UNVERIFIED per Q7; no obligation appears as an axiom (D2 guard green).
2. **Measured prints** (§A): final theorem = std-3 ∪ {B1, B6, B7, B9, B11a}; `M`-rows and
   the uniform gate = std-3 ∪ {B1, B6, B7}; `n = 1` = the frozen ℚ₂ 9-set byte-identical to
   the capstone; certificates at std-3 (pilot) and std-3 ∪ {B3c, B5, B8} (`n = 1`); B5-K and
   B10-K in **no** print.  All of these are now check-5 entries (`AUDIT_DYADIC`), so any
   growth fails `scripts/check_axioms.sh` mechanically.
3. **The residual surface** (§C) is the complete distance to packet Thm 1.1's prose form:
   bundles (C.0), packet §12 inputs (C.1), the pilot's 14 named binders (C.2), the M rows'
   ν-binders + four clauses + carried `KSupply` (C.3), the clause ledger (C.4), zero at
   `n = 1` (C.5), and the `Npc` gap (C.6).
4. **Known in-flight change**: AS3-b (ν-witnesses + core hoist + a docstring fix) — C.3's
   ν-row is written to be updated either way; the core hoist preserves fully-qualified names,
   so §A/§B are unaffected.
