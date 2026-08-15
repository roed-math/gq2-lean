# W74-HOUSE: the critical-path trace, round 10 + the background sweep applied, and watch round 11

Lane `claude/w74-house`, base `4fff1592`, cache at `608d3ded`.
Verification of record: `scripts/mirror.sh` (sweep, check).  **No `lake` command was run**, and
`check_dyadic.sh` was not run either (wave 73 established that its default path invokes
`lake env lean` twice through `check_axioms.sh`).

## Headline

**Ticket 1.**  The dependency memo is `docs/dyadic/w74-critical-path.md`, summarised in §1 below.
Two results worth the orchestrator's attention:

> **The `alpha = 1` even stratum is OFF the critical path, and the conclusion is stronger than
> the briefing's.**  The `alpha = 1` point is not merely unused: it is **provably outside the
> standing ramified-`i` hypothesis**, by three committed statements and no unproved input.  I
> composed them and ran `mirror.sh check`: both compositions elaborate and print std-3.  But the
> briefing's *reason* is not the tree's, and is weaker — see §1.3, three corrections.
>
> **The pilot row is one producer-generation behind.**  `ResidualSqrtNegTwo` carries three fields
> (`piAb`, `hpiAb`, `hpiNu`) that exist only because `SqrtNeg2.lean` calls the *abelianization*
> producer `marked_matching_certificate_KN`.  `LabuteInterface.lean:67`'s
> `marked_matching_certificate_KTwoN` needs none of them, and its orientation clause is exactly
> the shape the even route produces.  Statement change, so reported and not made.

**Ticket 2.**  All **38** reported findings applied or adjudicated: round 10's 29 (batch A) and
the nine background-sweep findings (batch B).  Every one re-verified against the Lean or the git
history before applying.  **All nine of batch B checked out**, three with corrections to the
finding itself (§3).  Batch A's applications are tabulated in §2.

**Ticket 3.**  Watch round 11 over the wave-73 landings: **N findings** (see §4).

**Ticket 4.**  The two `q`s: §5.

---

## 1.  Ticket 1: the critical-path trace

Full memo: `docs/dyadic/w74-critical-path.md`.  What follows is the part the orchestrator needs
in one screen; the memo carries the field-by-field tables and every citation.

### 1.1  The shape

`ramifiedI_candidate_equiv_galK` (`Main.lean:670`) is one `cases` over `FrozenQuadRow` onto five
`rowEquiv_*` theorems, each of which is one instance headline re-read off the record.  There is
**no derivation between the records and the conclusion**, so the critical path is exactly
`FieldInputs` (6 fields) plus the five records: the pilot's 13, and 17 leaves per `M` row (9
fields, of which `KS : KSupply` expands to 9 more).  Recounted at this tree.

The five row cores are `DN 2 0`, `DM 3 0`, `DM 2 0`, `DMpc 2 1 0`, `DMpc 2 1 1`.  **Every row is
at `alpha >= 2` and at handle count `h = 0`.**  That single fact does most of the work below.

### 1.2  (a) Who owes what

Four workstreams.  Condensed:

| workstream | fields it owes | where |
| --- | --- | --- |
| **classification** (even route at even degree, sq/graded route at odd) | pilot `fLab`/`horient`/`hpair` (+ `piAb`/`hpiAb`/`hpiNu`); `KSupply.pro2`/`hpro2`/`ker_pro2`/`nu_compat` | 7 + 4 |
| **ASK** (`KSupply.lean`) | `hexact`/`hstokes` on the pilot; `exactLifting`/`stokes`/`determinant` inside each `KSupply` | 2 + 3 |
| **candidate-side clauses** | pilot `hsimp`/`hsplit`/`hZcount`/`hdet`; each `M` row's `exactLifting`/`stokes`/`scalar`/`determinant` and its `nuP` block | 4 + 8 |
| **already proved / pins** | `T`, `params*`, `ramifiedData`, `hdeg`, `hhom` | |

`ramified` is not on any workstream's list: it is the hypothesis that *selects* `K`.

### 1.3  (b) The `alpha = 1` decision — the orchestrator's conclusion is right, its reason is not

**Mechanically**: `GQ2.Dyadic.Main`'s transitive import closure is **427 of 930** `GQ2` modules,
and it contains none of `EvenStratumPoint`, `EvenStratumFrame`, `EvenStratumShift`,
`NFrameAlphaOne`, `EvenAlphaOne`, or any `SqCore/Graded*` module (68 of them).  That settles
"consume" literally but not usefully, since the records are hypotheses the classification
workstreams exist to discharge from outside.

**Mathematically**, and this is the real answer: a ramified-`i` field is **never** on the third
stratum, so the `alpha = 1` point is outside `FieldInputs.ramified` outright.  Three committed
statements:

1. `evenUnram_imChiN_eq_prin_iff` (`EvenUnramified.lean:236`) at `a = 1, alpha = 2`:
   `imChiN 1 = evenRangePrin 2`.
2. `evenUnram_range_eq_of_oriented` (`:117`) + `range_chiN` (`OrientationCorrection.lean:209`):
   an oriented equivalence with `chiN 1 h` forces `range chiCycKTwo = evenRangePrin 2`.
3. `evenRangeF_hasEqualNormValueGroups_of_range_eq_prin` (`EvenRangeModelFields.lean:890`),
   docstring *"The third stratum is exactly the unramified one"*: that range gives
   `HasEqualNormValueGroups K deltaI` for **every** `deltaI` — the literal negation of `ramified`.

I composed these into `w74_orientedN_one_forces_unramified` and
`w74_ramified_excludes_alphaOne` and ran `scripts/mirror.sh check`.  Both elaborate; both print
`[propext, Classical.choice, Quot.sound]`.  The check file is a lane artefact and was **not**
added to the tree (plan A6 freeze; the three sibling lanes own this wave's new modules).

**Three corrections to the briefing:**

* **(i) The `demushkinQ` route is conditional, the stratum route is not.**
  `demushkinQ (D_N 1 h) = 4` is unconditional (`NFrameAlphaOne.lean:614`), but
  `demushkinQ (G_K(2)) = 2` at a ramified-`i` field is **not**: `EvenDemushkinQ.lean:149` carries
  `hrecip : Function.Injective (proTwoReciprocityToTopAb B)`, completed-reciprocity injectivity,
  itself unproved.  So the briefing's argument buys the conclusion on credit; §1.3's does not.
* **(ii) "forcing `i ∈ K`" is not a tree implication.**  `EvenUnramified.lean:429`-`432` records
  explicitly that this direction *"is not available and is not true"*: a `K` with `K(i)/K`
  unramified quadratic has `i ∉ K`.  The tree has `i ∈ K ⟹ stratum` and `stratum ⟹ unramified`;
  the composite that matters never passes through `i ∈ K`.
* **(iii) `alpha = 1` is an `N`-only phenomenon.**  At `alpha = 1` the `M` row has
  `demushkinQ = 2`, the *same* as a ramified-`i` field (`EvenForwardRouteSkeleton.lean:85`-`87`),
  so the `q`-invariant argument does not exclude the `M` branch there at all.  What excludes it
  is `evenUnram_isEmpty_orientedM`: `imChiM a` contains `-1` and `evenRangePrin alpha` omits it.

**Verdict: the `alpha = 1` work is classification-completeness, and can be scheduled as such.**
Two caveats.  It remains load-bearing for the *paper*: `evenUnram_classification_conclusion_false`
(`EvenUnramified.lean:361`) shows the ramification binder on `parityFinal_evenClassification` is
necessary, and the stratum work is what locates that boundary.  And the same argument retires the
`alpha >= 3` third stratum too, so the programme's remaining value is entirely at the one
surviving point.

### 1.4  (c) The honest remaining-work list

A preliminary that changes how the list reads: **"close every record at every ramified-`i` `K`"
is not achievable and should not be the goal.**  `fLab`/`horient`/`hpair` and
`KSupply.pro2`/`hpro2`/`ker_pro2`/`nu_compat` *assert* that `G_K(2)` is the row's specific core at
the row's specific `(alpha, h)`.  No theorem supplies those at an arbitrary ramified-`i` `K`,
because such a `K` of the wrong degree or branch is not that row's field.  The achievable goal is:
close every record at every ramified-`i` `K` **that the row's branch identification places on that
row**.  Eight items:

1. **The branch identification per field**, `range chiCycKTwo = imChiN alpha` (resp. `imChiM`).
   The even route's output is *existential* (`parityFinal_evenClassification`: `∃ alpha >= 2`,
   `M ∨ N`); this is what pins it to the row.  `parityFinal_orientedEquivN_sqrtNegTwo`
   (`EvenParityModel.lean:257`) already takes it as `hrange`.  **Smallest genuinely-open item;
   gates all five rows.**
2. **The `KTwoN`/`KTwoM` adapter** into the two record spellings (§1.2 headline).  A restatement,
   not open mathematics — but until it exists the even route's output does not typecheck in.
3. `ExactLiftingSemantics` at `galKProfinite K` — `KSupply.lean:256`-`260` narrows this to **one
   existential**, the `K` analogue of `RadicalEdgeLocal.exists_good_twist`.
4. `StokesDualityCertificate` at `galKProfinite K`.
5. `AffineDeterminantCertificate` at `galKProfinite K` — the **LG5 ⇒ `GaussZResidueK` bridge**.
   ⚠⚠ `KSupply.lean` is explicit that this has **no `K` clone** and that inlining a hypothesis
   named after LG5 would have hidden the gap.
6. The four candidate-side analytic clauses at `GammaR` (AS1 divergence 4).  Uniform in the row,
   so four statements, not sixteen.
7. The pilot's four named residuals: `hsimp`, `hsplit`, `hZcount`, `hdet` (⚠⚠, no supplier lane).
8. The `nuP` block for the four `M` rows (ticket AS3-b) — a build, not a proof.

**Sharpest single item: 5 / `hdet`.**  The Gauss-`Z` determinant residue is the only place where
*both* sides of the two-sided architecture are carried and neither has a supplier lane.

**Explicitly not on the list**, and worth saying out loud: the `alpha = 1` stratum;
`SqClassClearingSupply h k` at any class and `SqLamMarkTransitivity h` at any `h >= 1` (the
frozen table is `h = 0` on `M`/`N` cores, while the `Sq` core serves the `L` row / odd degree,
whose certificate is already unconditional); and `demushkinQ (G_K(2)) = 2` as such, which is a
hypothesis of the superseded `abstractEquiv_KTwoN/M` adapters (`LabuteInterface.lean:200`) and not
of the even route.
