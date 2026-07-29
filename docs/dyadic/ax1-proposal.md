# AX1 — general-`K` topological finite generation: statement design + census memo

**Ticket AX1** (board `docs/dyadic/tickets.md`, lane AX; plan `docs/dyadic/plan.md` §4 row AX1).
**Status: memo only.**  No Lean landed, no census touched, no board edit.  The AX protocol is
*memo → owner sign-off (**G-AX**) → census flip using the b9a checklist template*
(`docs/orchestration/b9a-tickets.md`); until sign-off, consumers bind the statement as an explicit
hypothesis (§5 below gives the exact binder).

Extends census leaf **B1** `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`
(`GQ2/Foundations/Axioms.lean:97`) from `ℚ₂` to every finite `K/ℚ₂`.

---

## 0. Headline recommendation

> **Do not add an axiom.  The general-`K` statement is a *theorem* over B1.**

The statement designed in §1 was **proved in a scratch experiment** (§3): it follows from B1 plus
Mathlib's Schreier lemma (`Subgroup.exists_finset_card_le_mul`) and the fact that a dense subgroup
of a topological group meets an open subgroup densely.  Verified with
`lake env lean` against the main checkout at `master d0714a7`:

```
'absGalK_isTopologicallyFinitelyGenerated' depends on axioms:
  [propext, Classical.choice, Quot.sound, Foundations.absGalQ2_isTopologicallyFinitelyGenerated]
```

Consequences for **G-AX**:

| route | census | ℚ₂ capstone axiom prints | verdict |
|---|---|---|---|
| **D — derive** (recommended) | **9 → 9**, B1 untouched | byte-identical (nothing changes) | **recommended** |
| R — replace B1 by the general axiom | 9 → 9, B1 re-derived as a same-name theorem | one line changes in every ℚ₂ capstone | fallback, if the owner prefers a direct NSW-at-`K` citation |
| A — add alongside B1 | 9 → **10** | byte-identical | only if the owner also rejects R's print churn *and* route D |

So G-AX's real question is not "which flip?" but **"is the derivation acceptable, or does the owner
want the general statement to be a *citation* (NSW 7.4.1 is stated for every `p`-adic local field)
rather than a *consequence* of the `ℚ₂` citation plus profinite Schreier?"**  §4 gives the
replace-vs-add analysis for the branch where the answer is "citation".

Everything below is written so that either answer is executable: §1's statement is the same text
whether it becomes an `axiom` or a `theorem`.

---

## 1. The proposed Lean statement

### 1.1 Primary form (the one SD/AS need)

House style follows **B9** `relativeStiefelWhitney_dyadic` and **B11a**
`hilbertSymbol_normCriterion_finiteDyadic` (`GQ2/Foundations/Axioms.lean:266,368`), which are the
two existing census leaves quantified over a general finite dyadic base — same binder shape, same
`fixingSubgroup` spelling for `G_K`:

```lean
axiom absGalK_isTopologicallyFinitelyGenerated
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k] :
    ∃ s : Finset ↥k.fixingSubgroup,
      (Subgroup.closure (s : Set ↥k.fixingSubgroup)).topologicalClosure = ⊤
```

*(Under route D the first line is `theorem absGalK_isTopologicallyFinitelyGenerated`, the rest is
identical; the theorem does **not** live in `GQ2/Foundations/Axioms.lean`, which has been
axioms-only since 2026-07-27 — see §3.4 for placement.)*

**Verified**: this elaborates as written (no instance friction, no `change`/`show` needed) —
`lake env lean` on a scratch file importing `GQ2.Foundations.Axioms`.

Name: `absGalK_…` parallels `absGalQ2_…` and is readable at the call site.  A house alternative is
the B9/B11a suffix convention `…_finiteDyadic`; the `K`-form is preferred because `K` is this
campaign's standing name for the general base.  Namespace `GQ2.Foundations`, like B1 and B7.

### 1.2 Encoding notes

* **`G_K` as `↥k.fixingSubgroup`.**  This *is* the repo's representation of the absolute Galois
  group of a finite dyadic field: `IntermediateField.fixingSubgroup` of
  `k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])` with `[FiniteDimensional ℚ_[2] k]`,
  as in B9 (`GQ2/Foundations/Axioms.lean:267,276`), B11a (`:369-370`),
  `hilbertSymbol_dyadic`/`kummerClassK_surjective`/`dyadicUnitFiltration`
  (`GQ2/Foundations/Interfaces.lean:173,275,311`) — 534 occurrences of `fixingSubgroup` in `GQ2/`.
  The ambient group is `AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]`, i.e.
  `Kummer.GaloisGroup ℚ_[2]` (`GQ2/Kummer.lean:68`, a reducible `abbrev`), definitionally
  `GQ2.AbsGalQ2` (`GQ2/Statement.lean:40`) — the coercion is used silently across the repo
  (`GQ2/InvolutionSplice.lean:147`).
* **Raw `∃`-form, not `GQ2.IsTopologicallyFinGen`.**  The repo *has* the predicate
  (`GQ2/FinitelyGenerated.lean:42`, definitionally the same `∃`), but that file publicly imports
  `GQ2.GammaA`; using it in the axiom file would drag the candidate-group construction into the
  transitive imports of `GQ2/Foundations/Axioms.lean`, whose stated discipline is that its imports
  are "exactly the statement vocabulary an auditor must read" (`Axioms.lean:23-27`).  B1 has the
  raw form for the same reason.  Downstream files may of course phrase it with the predicate.
* **`Finset`, not `Set … Finite`.**  Matches B1 and every consumer.
* No `[CompactSpace]`/`[TotallyDisconnectedSpace]` binders are needed on `↥k.fixingSubgroup`:
  the statement mentions only `Subgroup.closure` and `Subgroup.topologicalClosure`.

### 1.3 Decision: bare finite generation, **not** the `n+2` bound

Rejected sharper form (recorded so the decision is auditable):

```lean
-- NOT proposed
∃ s : Finset ↥k.fixingSubgroup, s.card ≤ Module.finrank ℚ_[2] ↥k + 2 ∧
  (Subgroup.closure (s : Set ↥k.fixingSubgroup)).topologicalClosure = ⊤
```

Reasons, in order of weight:

1. **No consumer wants it.**  `GQ2.reconstruction` takes `hPfg`/`hQfg` in the bare shape
   (`GQ2/Reconstruction.lean:402-403`), as do `reconstruction_of_equinum` (`:354`),
   `finite_continuousMonoidHom` (`:59`), `profinite_hopfian` (`:79`), `main_presentation`'s
   `hfgΓ`/`hfgG` (`GQ2/Statement.lean:93-94`) and the record field `SourceData.tfg`
   (`GQ2/SourceData.lean:127`).  Nothing in the library or the packet ever reads a generator count.
2. **A cardinality clause is a strictly stronger assumption bought for nothing** — exactly the kind
   of surplus content the adversarial-axioms review penalizes (`docs/adversarial-axioms-review.md`).
3. **The bare form is derivable, the bounded form is not** (§3): profinite Schreier from B1 gives
   `d(G_K) ≤ 1 + [K:ℚ₂]·(d(G_{ℚ₂}) − 1)`, and since B1's Lean statement records *no* numeric bound
   for `ℚ₂` at all, no bound survives.  Choosing the bounded form would forfeit route D and force an
   axiom.
4. **B1's own precedent**: the `N+2` bound lives in B1's *docstring prose* ("in fact by
   `[K : ℚ_p] + 2` elements"), never in its Lean statement.  §6's docstring keeps that convention.

---

## 2. Citation block

**Faithfulness class: direct classical theorem** (the class of B1, B6, B7 — see
`GQ2/Foundations/Axioms.lean:55-59`).  There are no encoding choices beyond the repo's standard
`fixingSubgroup` representation of `G_K`, and no composition of separate published facts: the Lean
statement is the cited theorem with its quantitative bound weakened away.

* **Primary — NSW [1], Ch. VII §7.4, Theorem (7.4.1).**  For every `p`-adic local field `k`,
  `G_k` is generated (topologically) by `N+2` elements, `N = [k : ℚ_p]`.  The theorem is stated for
  arbitrary `p`-adic `k`, so it applies verbatim at `p = 2` and at **every** finite `K/ℚ₂` — this
  is the same "the citation was always base-general, only the Lean encoding was not" situation as
  the 2026-07-06 base-generalization of **B6** (`docs/literature-axioms.md` §E: "the theorem is
  stated there for arbitrary `p`-adic `k`, so the base-generalization of the Lean encoding to all
  finite `k/ℚ₂` is census-neutral").
* **Weaker alternative — Jannsen, *Invent. Math.* 70 (1982), Satz 3.2 and Lemma 3.3**, giving the
  `N+3` bound, which would also suffice (it too implies the bare Lean statement).
* **Not** NSW (7.5.14): its surrounding subsection assumes `p ≠ 2`
  (`docs/literature-axioms.md` §B1, §E).
* Verified against the cited PDFs at the time of the B1 audit; the audit copies are not vendored in
  this repository.  This memo adds no new source audit — the general-`K` reading is the *same
  sentence* of NSW (7.4.1) that B1 already cites, read without specializing `k`.

Route-D remark on citations: if the statement lands as a theorem, the trust boundary still contains
exactly one literature input for it (B1 = NSW 7.4.1 at `ℚ₂`), and the derivation's extra ingredient
(Schreier for profinite groups) is *proved in-repo* over Mathlib, not cited — the same pattern as
`GQ2.profinite_hopfian` (RZ Prop. 2.5.2, proved rather than assumed; `docs/literature-axioms.md`
§A).

---

## 3. Prior question: the statement is derivable from B1 (verified)

### 3.1 The mathematics

`G_K = k.fixingSubgroup` is an **open** subgroup of `G_{ℚ₂}` (finite `k/ℚ₂`), and `G_{ℚ₂}` is
compact.  Then:

> **Profinite Nielsen–Schreier.**  If a compact topological group `G` is topologically generated by
> a finite set and `H ≤ G` is open, then `H` is topologically generated by a finite set.

*Proof.*  Let `D = ⟨s⟩` be the (abstract) subgroup generated by a finite topological generating set;
`D` is dense.  `H` is open of finite index (compactness), so `H ∩ D` has finite index in `D`, and
`D` is an abstractly finitely generated group, so `H ∩ D` is abstractly finitely generated by
**Schreier's lemma**.  Finally `H ∩ D` is dense in `H`: `H` is open, so every nonempty open subset
of `H` is open in `G` and therefore meets `D`.  A finite abstract generating set of `H ∩ D` is thus
a finite topological generating set of `H`. ∎

### 3.2 The Lean proof (compiles, sorry-free)

```lean
/-- **Profinite Nielsen–Schreier.**  An open subgroup of a topologically finitely generated
compact topological group is topologically finitely generated. -/
theorem topologicallyFG_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (hG : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    ∃ t : Finset H, (Subgroup.closure (t : Set H)).topologicalClosure = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := hG
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set D := Subgroup.closure (s : Set G) with hD
  have hDdense : Dense (D : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  haveI hDfg : Group.FG ↥D := (Group.fg_iff_subgroup_fg D).mpr ⟨s, hD.symm⟩
  obtain ⟨S, hS⟩ := hDfg.1
  obtain ⟨T, -, hT⟩ := Subgroup.exists_finset_card_le_mul (H.subgroupOf D) hS
  let φ : ↥(H.subgroupOf D) →* ↥H :=
    { toFun := fun x => ⟨((x : ↥D) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrange : φ.range = D.subgroupOf H := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (x : ↥D).2
    · intro hy
      exact ⟨⟨⟨(y : G), hy⟩, y.2⟩, rfl⟩
  have hdense : Dense ((D.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    hDdense.preimage hH.isOpenMap_subtype_val
  refine ⟨T.image φ, ?_⟩
  have hclos : Subgroup.closure ((T.image φ : Finset ↥H) : Set ↥H) = D.subgroupOf H := by
    rw [Finset.coe_image, ← MonoidHom.map_closure, hT, ← MonoidHom.range_eq_map, hrange]
  rw [hclos]
  refine SetLike.ext' ?_
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top]
  exact dense_iff_closure_eq.mp hdense

/-- **AX1**, derived. -/
theorem absGalK_isTopologicallyFinitelyGenerated
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k] :
    ∃ s : Finset ↥k.fixingSubgroup,
      (Subgroup.closure (s : Set ↥k.fixingSubgroup)).topologicalClosure = ⊤ := by
  refine topologicallyFG_of_isOpen
    (G := AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]) ?_
    k.fixingSubgroup k.fixingSubgroup_isOpen
  exact GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated
```

Mathlib inputs (all present in the pinned mathlib): `Subgroup.exists_finset_card_le_mul`
(`Mathlib/GroupTheory/Schreier.lean:132`), `Subgroup.quotient_finite_of_isOpen`
(`Mathlib/Topology/Algebra/OpenSubgroup.lean:287`), `Subgroup.finiteIndex_of_finite_quotient`,
`Subgroup.instFiniteIndex_subgroupOf` (`Mathlib/GroupTheory/Index.lean:773`),
`Group.fg_iff_subgroup_fg`, `Dense.preimage` (`Mathlib/Topology/Maps/Basic.lean:518`),
`IsOpen.isOpenMap_subtype_val`, `IntermediateField.fixingSubgroup_isOpen`
(`Mathlib/FieldTheory/KrullTopology.lean:173`), and `CompactSpace Gal(ℚ̄₂/ℚ₂)` from
`InfiniteGalois` (`Mathlib/FieldTheory/Galois/Profinite.lean:329`).

### 3.3 Gotchas found while checking (for whoever lands this)

* Extra imports beyond `GQ2.Foundations.Axioms` are required:
  `Mathlib.GroupTheory.Schreier`, `Mathlib.FieldTheory.KrullTopology`,
  `Mathlib.FieldTheory.Galois.Profinite`.
* **Instance-path friction between `GQ2.AbsGalQ2` and `AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]]
  AlgebraicClosure ℚ_[2]`.**  The two types are definitionally equal, but their `TopologicalSpace`
  instances arrive by different paths (`Field.instIsTopologicalGroupAbsoluteGaloisGroup …` vs
  `instIsTopologicalGroupAlgEquiv …`).  Passing B1 as a *term-mode* argument to a `{G : Type*}`
  lemma at the `≃ₐ` spelling makes typeclass resolution fail on `IsTopologicalGroup Gal(ℚ̄₂/ℚ₂)`;
  the fix is to fix `G` first and discharge B1 with `refine … ?_` + `exact` (as above), i.e. force
  the defeq check into the *argument*, not into instance synthesis.  Same trap in the reverse
  direction (§4.4).  This is the reason the ℚ₂ files carry local `CompactSpace`/
  `TotallyDisconnectedSpace` instances declared via `change` (`GQ2/PresentationLiteral.lean:33-40`).
* `Subgroup.instIsTopologicalGroupSubtypeMem` resolves fine under `#synth` but failed inside a proof
  term in one experiment; state any transport lemma over an **abstract** `G` with explicit instance
  binders (as `topologicallyFG_of_isOpen` and §4.4's `fg_of_top_subgroup` do) and the problem
  disappears.

### 3.4 If route D is taken: placement and ticketing

* **Not** in `GQ2/Foundations/Axioms.lean` (axioms-only) and **not** in `GQ2/FinitelyGenerated.lean`
  (frozen ℚ₂ path, plan A6 — generalize by new files).
* Proposed new leaf `GQ2/Dyadic/FinitelyGeneratedK.lean`, namespace `GQ2.Dyadic`, `module`-style
  (its imports are `GQ2.Foundations.Axioms` + Mathlib, none of the §8/§9 plain-import stack, so the
  R31a module rule is satisfied).
* Contents: `topologicallyFG_of_isOpen` (generic, Mathlib-shaped — a candidate for upstreaming),
  `absGalK_isTopologicallyFinitelyGenerated`, and the §4.4 `k = ⊥` sanity instance as a regression
  showing B1 is recovered.
* Suggested follow-up ticket **AX1-b** (opus; files owned: that one file).  The orchestrator owns
  the board and the `GQ2.lean` import line — this memo does not create the ticket.

---

## 4. Relationship to B1: replace, or add?

### 4.1 B1 consumer inventory (grep at `dyadic-ax`, forked from `master d0714a7`)

**Term-level uses of `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`: 6 occurrences in
4 Lean files, inside 6 declarations.**

| file:line | enclosing declaration | role |
|---|---|---|
| `GQ2/ThmFourTwo.lean:122` | `mStage_lane` (`:104`, private) | `hfgF` — the `G_{ℚ₂}` side of the §9 induction |
| `GQ2/ThmFourTwo.lean:310` | `rStage_lane` (`:290`, private) | same |
| `GQ2/SectionTenSources.lean:110` | `eq_154` | `card_contSurj_eq` at `boundaryMapsWitness.bF` |
| `GQ2/PresentationLiteral.lean:50` | `main_presentation_literal` | `hfgG` of `main_presentation` |
| `GQ2/Roe/Main.lean:494` | `eq_154_R` | `card_contSurj_eq` at `bF` |
| `GQ2/Roe/Main.lean:545` | `main_presentation_literal_roe` | `hfgG` |

Plus one **name quote** (not a use): `GQ2/AxiomLedger.lean:53` (`bAxioms`, compile-time census
check).  Note the asymmetry that matters for SD-n: at `ThmFourTwo.lean:118-122` the **A-side**
finite generation comes from the record field `S.tfg` (`GQ2/SourceData.lean:127`) while the
**B-side** hard-codes B1 — the "`G_{ℚ₂}` slot is pinned" observation of `recon/sd-survey.md` §3.

Infrastructure pins of the *name* (all must move together in any flip): `scripts/check_axioms.sh:42`
(`AUDIT_EXPECTED_AXIOMS`), `scripts/axiom_closure.py:19` (`BTAG`),
`scripts/AxiomClosureProbe.lean:24` (`censusAxioms`), `comparator-config.json:12`
(`permitted_axioms`), `formalization.yaml:52,69,117`.  Prose/doc references:
`docs/literature-axioms.md:82` (§B1) + §D row + §E bullet, `docs/axiom-closure.md:19,236`,
`docs/orchestration/STATUS.md:36`, `docs/orchestration/review-packet.md:63`,
`GQ2/Foundations.lean:19`, `atlas-audit.md:51`, `atlas-audit-roe.md:63`, `Challenge.lean:42-45`
(prose "census of 9", no name list).

### 4.2 Is B1 the `k = ℚ₂` case of the new statement?

**Yes mathematically**, at `k = (⊥ : IntermediateField ℚ_[2] ℚ̄₂)`:
`IntermediateField.fixingSubgroup_bot` (Mathlib, `@[simp]`) gives `⊥.fixingSubgroup = ⊤`, and
`↥(⊤ : Subgroup G) ↠ G` is a continuous surjection, so
`GQ2.IsTopologicallyFinGen.of_surjective` (`GQ2/FinitelyGenerated.lean:50`) transports the witness.

**Not literally**, in Lean: B1 is typed at `AbsGalQ2` (instances via
`Field.absoluteGaloisGroup`), the general statement at a subgroup of the `≃ₐ` spelling, so the
identification is a (short) proof, not `rfl` — see §3.3 and §4.4.

### 4.3 The two precedents

* **B6 base-generalization (2026-07-06)** — `tateDuality` (at `G_{ℚ₂}`) *replaced* by
  `tateDualityAt` over every local dualizing group; census-neutral; the base member kept its public
  name as an in-repo definition (`GQ2/Foundations/Interfaces.lean`).  This is AX1's exact shape.
* **B9-A flip (2026-07-24)** — axiom replaced, the old name re-derived as a same-name theorem,
  census 9 → 9, consumers untouched (`docs/orchestration/b9a-tickets.md` T5/T6).

Both say: when the citation was always base-general, **generalize the leaf in place, keep the old
name as a derived declaration, keep the census constant.**

### 4.4 Cost of the replacement glue (verified)

B1 comes back in ~10 lines, provided the transport is stated over an abstract `G` (§3.3):

```lean
theorem fg_of_top_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : H = ⊤)
    (h : ∃ t : Finset ↥H, (Subgroup.closure (t : Set ↥H)).topologicalClosure = ⊤) :
    ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤ :=
  GQ2.IsTopologicallyFinGen.of_surjective H.subtype continuous_subtype_val
    (fun g => ⟨⟨g, by rw [hH]; exact Subgroup.mem_top g⟩, rfl⟩) h

theorem absGalQ2_isTopologicallyFinitelyGenerated :   -- B1, same name, now a theorem
    ∃ s : Finset GQ2.AbsGalQ2,
      (Subgroup.closure (s : Set GQ2.AbsGalQ2)).topologicalClosure = ⊤ := by
  refine fg_of_top_subgroup (G := AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
    (H := (⊥ : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])).fixingSubgroup)
    IntermediateField.fixingSubgroup_bot ?_
  exact absGalK_isTopologicallyFinitelyGenerated ⊥
```

Checked in a scratch file (with the general statement stubbed as a local `axiom`):
`#print axioms` = std-3 + that stub, i.e. the recovery adds nothing.  Caveat: the B1 replacement
would have to live in `GQ2/Foundations/Interfaces.lean` (the house location for "formerly an axiom,
now a same-name construction", `Axioms.lean:46-53`), and that file must then reach
`IsTopologicallyFinGen.of_surjective` or inline its two-line proof — `GQ2/FinitelyGenerated.lean`
publicly imports `GQ2.GammaA`, so **inline it** rather than import.

### 4.5 Recommendation, and the census delta

1. **Primary: route D — neither replace nor add. Census 9 → 9, B1 unchanged.**  The general
   statement lands as a theorem (§3.4).  Merge gate 8 ("audited ℚ₂ capstones print byte-identical
   axiom sets", plan §7) is satisfied trivially, the master-facing artifacts
   (`comparator-config.json`, `formalization.yaml`, `Challenge.lean` prose) are untouched, and the
   trust boundary does not grow — the *strongest* possible outcome of an AX ticket.
2. **If the owner wants a citation rather than a derivation: route R (replace). Census 9 → 9.**
   Reasons to prefer R over A: NSW (7.4.1) is *already* the general theorem, so B1 is redundant the
   moment the general leaf exists, and this repo deletes redundant leaves (B2 and B4 were deleted
   precisely for being implied/unused, `docs/literature-axioms.md` §B2/§B4); the B6 and B9-A
   precedents both replaced in place; and A leaves the census carrying two axioms for one theorem,
   which the review packet's classification table would have to explain.
   **Cost to be flagged to the owner up front:** every audited ℚ₂ capstone's `#print axioms` gains
   `absGalK_…` and loses `absGalQ2_…`, so plan §7 gate 8 must be re-baselined in the same commit
   ("byte-identical modulo the documented B1 ↦ AX1 leaf rename"), and `comparator-config.json`'s
   `permitted_axioms` — an externally published pair — changes.  Because `master` is meant to stay
   ℚ₂-only until G3, **route R should be executed on `dyadic` and re-confirmed at G3**, not
   back-ported early.
3. **Route A (add, census 9 → 10)** is the choice only if the owner wants both a citation *and*
   zero churn in the ℚ₂ prints.  It is the only route that changes `EXPECTED_AXIOMS`.  Its cost is a
   permanently redundant census entry (B1 becomes a corollary of AX1 by §4.4), which should then be
   scheduled for collapse at G3.

---

## 5. Consumers in the dyadic campaign, and the interim binder

### 5.1 Where the statement is needed

| lane / ticket | consumer | shape |
|---|---|---|
| **SD3** (`GQ2/Dyadic/ThmFourTwoN.lean`) | the two-sided degree-`n` induction: the `G_K` side of `mStage_lane`/`rStage_lane` currently reads B1 (`GQ2/ThmFourTwo.lean:122,310`) | as a **record field** — see §5.2 |
| **SD2** (`GQ2/Dyadic/SourceDataN.lean`) | the `G_K`-side record needs a `tfg` field mirroring `SourceData.tfg` (`GQ2/SourceData.lean:127`) | record field |
| **AS1** (`GQ2/Dyadic/CertificateMain.lean`) | packet Thm 1.1: `… ⇒ Nonempty (ContinuousMulEquiv (candidateGroup K R) G_K)` calls `GQ2.reconstruction`, whose `hQfg` is the `G_K` side (`GQ2/Reconstruction.lean:403`) | explicit binder or the theorem |
| **AS2/AS3/AS4/AS5** | each field instance instantiates AS1 | inherited |
| **LG lane** | **not needed.**  No file in the local-Gauss stack consumes B1 (see §4.1's complete list); LG's general-`K` needs are the Euler characteristic (AX2) and `Finite (H¹(G_K, 𝔽₂))` (`Shapiro.finite_H1_open`, `GQ2/Shapiro/Finiteness.lean:262`), not finite generation | — |
| **MC lane** | not needed (the cores are presented pro-2 groups; their topological generation is `dr_topGen`-style, proved) | — |

### 5.2 Interim binder spelling (use this until G-AX closes)

Loose binder, for AS1-style consumers — name `hfgK`, mirroring `main_presentation`'s `hfgG`
(`GQ2/Statement.lean:94`):

```lean
variable (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]

theorem foo
    (hfgK : ∃ s : Finset ↥k.fixingSubgroup,
      (Subgroup.closure (s : Set ↥k.fixingSubgroup)).topologicalClosure = ⊤) : … := …
```

For SD2/SD3 the binder should **not** be loose: make it a field of the `G_K`-side source record,
byte-for-byte the shape of `SourceData.tfg` (`GQ2/SourceData.lean:124-128`), so the degree-`n`
two-sided theorem takes it exactly the way the A-side already does:

```lean
  /-- **(ii.1) topological finite generation** of the source group. -/
  tfg : ∃ s : Finset (Γ : Type),
    (Subgroup.closure (s : Set (Γ : Type))).topologicalClosure = ⊤
```

This is the campaign-preferred interim state (plan §0.1 "explicit hypothesis binders"), and under
route D it is also the **permanent** state: the field is discharged at instantiation time by
`absGalK_isTopologicallyFinitelyGenerated k`, with no census consumption at all.

---

## 6. Draft docstring (paste-ready for `GQ2/Foundations/Axioms.lean`, route R/A only)

```lean
/-! ## B1′ — topological finite generation over a general finite dyadic base -/

/-- **[Classical — B1′.]** The absolute Galois group `G_K = Gal(ℚ̄₂/K)` of a finite extension
`K/ℚ₂` is *topologically finitely generated* (in fact by `[K : ℚ₂] + 2` elements).  This is the
input `hfgK` that the degree-`n` reconstruction (`GQ2/Dyadic/CertificateMain.lean`) and the
`G_K` side of the two-sided source induction (`GQ2/Dyadic/ThmFourTwoN.lean`) feed to
`GQ2.reconstruction`; `K` is represented as usual by
`k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])` with `G_K = k.fixingSubgroup`.

Citation: NSW [1], Ch. VII §7.4, Theorem (7.4.1) — for every `p`-adic local field `k`,
`G_k` is generated by `N+2` elements (`N = [k : ℚ_p]`).  The theorem is stated for arbitrary
`p`-adic `k`, so it is the direct source for the statement below at every finite `K/ℚ₂` (the
`ℚ₂` instance is the former B1).  Jannsen, *Invent. Math.* 70 (1982), Satz 3.2 and Lemma 3.3,
gives the weaker `N+3` bound, which would also suffice.  NSW (7.5.14) is not the right citation:
its surrounding subsection assumes `p ≠ 2`.  Verified against the cited PDFs; the audit copies
are not vendored in this repository.

This is a genuine, faithful Lean statement: it is exactly the topological-finite-generation
predicate used throughout `Reconstruction.lean`, with the generator bound weakened away (no
consumer reads it).  The `ℚ₂` member is recovered at `k = ⊥` (`GQ2/Foundations/Interfaces.lean`,
`absGalQ2_isTopologicallyFinitelyGenerated`).  Paper: ⟦dyadic note, Thm 1.1 / §12 local
inputs — tag TBD⟧; ℚ₂ antecedent: Lemma 2.5 (the `hfgG` input to the reconstruction argument).
`docs/literature-axioms.md` B1; `docs/dyadic/ax1-proposal.md`. -/
axiom absGalK_isTopologicallyFinitelyGenerated
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k] :
    ∃ s : Finset ↥k.fixingSubgroup,
      (Subgroup.closure (s : Set ↥k.fixingSubgroup)).topologicalClosure = ⊤
```

Under **route D** the same prose becomes the theorem's docstring in
`GQ2/Dyadic/FinitelyGeneratedK.lean`, with the citation paragraph replaced by: *"NSW (7.4.1)
states this directly for every `p`-adic local field; we do not consume the general citation — the
statement is derived from its `ℚ₂` instance (B1) by profinite Schreier, so the trust boundary is
unchanged."*

---

## 7. Census-flip checklist (b9a template instantiation)

The b9a T5 checklist (`docs/orchestration/b9a-tickets.md` "T5 execution checklist") in three
variants, one per route.  All of them are **single atomic commits** on `dyadic-ax` (or a fresh lane
branch), path-limited, followed by an orchestrator merge; none touches the board.

### Route D (recommended) — no census flip

1. New file `GQ2/Dyadic/FinitelyGeneratedK.lean` (§3.4) with `topologicallyFG_of_isOpen`,
   `absGalK_isTopologicallyFinitelyGenerated`, and the `k = ⊥` regression.  Apache header, namespace
   `GQ2.Dyadic`, `module` style.
2. `EXPECTED_AXIOMS` **unchanged (9)**; `AUDIT_EXPECTED_AXIOMS` unchanged; `AxiomLedger.bAxioms`
   unchanged; `formalization.yaml` / `comparator-config.json` unchanged.
3. `#print axioms GQ2.Dyadic.absGalK_isTopologicallyFinitelyGenerated` must print exactly
   `[propext, Classical.choice, Quot.sound, GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated]`
   — record the output in the commit message.
4. Gates: full build green; `scripts/check_axioms.sh` passes (checks 1–5 untouched); zero sorries.
5. Docs: one row in AS5's `docs/dyadic/literature-axioms-dyadic.md` under the "discharged in-repo"
   convention used for B7′/B11b/B12/B13 (`docs/literature-axioms.md` §B7′ etc.), stating that
   general-`K` finite generation is **proved**, not assumed.  AX1's board row closes as
   *"no axiom needed — discharged"*.
6. G-AX becomes a **no-op sign-off**: the owner records that no census change was required.

### Route R (replace; census 9 → 9)

1. Move the §1.1 statement into `GQ2/Foundations/Axioms.lean` as the B1′ `axiom` with the §6
   docstring; **delete** the old B1 `axiom`; update the file's module docstring — the census bullet
   list (`Axioms.lean:31-44`) and the three-class list (`:55-59`, B1′ stays in *direct classical
   theorems*).
2. Same commit: `GQ2/Foundations/Interfaces.lean` gains the same-name **theorem**
   `absGalQ2_isTopologicallyFinitelyGenerated` (§4.4 glue, inlined — do **not** import
   `GQ2.FinitelyGenerated`), so all six consumers of §4.1 compile untouched.
3. Same commit, name pins: `GQ2/AxiomLedger.lean:53` (B1 ↦ new name),
   `scripts/check_axioms.sh:42` (`AUDIT_EXPECTED_AXIOMS` line swap; `EXPECTED_AXIOMS` stays **9**),
   `scripts/AxiomClosureProbe.lean:24`, `scripts/axiom_closure.py:19`,
   `comparator-config.json:12`, `formalization.yaml:52,69,117`.
4. Gates before merge: full `lake build` green; `lake env lean GQ2/AxiomLedger.lean` — certificate
   shows B1 = the new declaration, ALARM empty, gap map empty; `scripts/check_axioms.sh` passes
   (check 5 now compares against the swapped `AUDIT_EXPECTED_AXIOMS`); zero sorries; the Γ_A/Γ_R
   twin pairs still print identically.
5. **Plan amendment in the same commit**: `docs/dyadic/plan.md` §7 gate 8 re-baselined to
   "byte-identical modulo the documented B1 ↦ B1′ rename", with a pointer here; orchestrator log
   entry recording that `comparator-config.json` (a published artifact) changed.
6. Docs sweep (may be a follow-up commit, b9a T6 pattern): `docs/literature-axioms.md` §B1 rewritten
   (general base, `ℚ₂` member now derived), §D row, §E bullet, the "Bottom line" paragraph;
   `docs/axiom-closure.md` regenerated via `scripts/axiom_closure.sh`;
   `docs/orchestration/STATUS.md:36`, `docs/orchestration/review-packet.md:63`,
   `GQ2/Foundations.lean:19`; `Challenge.lean`'s prose count stays 9.

### Route A (add; census 9 → 10)

Steps 1–6 of route R, minus the Interfaces re-derivation, plus:
`EXPECTED_AXIOMS` **9 → 10** (`scripts/check_axioms.sh:27`, with the census-history comment
extended in the house style of that line); `AUDIT_EXPECTED_AXIOMS`, `comparator-config.json` and
`formalization.yaml` **unchanged** (the new leaf must never appear in a ℚ₂ capstone print — if it
does, the flip is wrong); `AxiomLedger.bAxioms`, `AxiomClosureProbe.censusAxioms` and
`axiom_closure.py:BTAG` gain a tenth entry labelled `B1′`; `Challenge.lean:42-45` prose
"census of 9" → "10"; `docs/literature-axioms.md` gains a §B1′ subsection and a §D row, and the
"nine" counts throughout §D become "ten".

---

## 8. Questions for the owner at G-AX

1. **Derivation or citation?**  Route D proves the statement from B1 (verified).  Is that
   acceptable, or do you want the general-`K` fact to enter as its own NSW (7.4.1) citation?
   *(Recommendation: route D — smaller trust base, zero churn.)*
2. If citation: **replace (R, census-neutral, ℚ₂ prints change one line) or add (A, census 10, ℚ₂
   prints frozen)?**  *(Recommendation: R, per the B6 and B9-A precedents.)*
3. Route D creates a new file outside the AX lane's remit.  Should it be ticketed as **AX1-b** in
   lane F (`GQ2/Dyadic/FinitelyGeneratedK.lean`), or folded into SD2's file ownership?
4. `topologicallyFG_of_isOpen` is Mathlib-shaped and Mathlib-free of GQ2 content — worth an
   upstream PR (`Mathlib/Topology/Algebra/OpenSubgroup.lean` or next to Schreier), or keep local?

---

### Appendix — verification log

All checks run with `cd ~/claude/gq2-lean && lake env lean <scratch file>` (main checkout,
`master d0714a7`, per the wave-1 protocol note on the board); nothing was written to any tracked
file.

| check | result |
|---|---|
| §1.1 statement elaborates (`:= by sorry`) | ✅ only the expected `declaration uses 'sorry'` warning |
| §3.2 derivation compiles | ✅ sorry-free |
| `#print axioms absGalK_isTopologicallyFinitelyGenerated` | `[propext, Classical.choice, Quot.sound, Foundations.absGalQ2_isTopologicallyFinitelyGenerated]` |
| §4.4 B1 recovery compiles (general statement stubbed) | ✅ sorry-free |
| `#print axioms b1_of_general` | `[propext, absGalK_… (stub), Classical.choice, Quot.sound]` |
| `#synth` of the four instances of §3.3 | ✅ all four resolve standalone |
