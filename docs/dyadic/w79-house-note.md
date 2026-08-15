# W79-HOUSE: the √5 row closed, the determinant bridge found, and watch round 16

Lane `claude/w79-house`, base `527adf51`, cache at umbrella 4350 jobs green.
Verification of record: `scripts/mirror.sh` (`sweep`, `check`).  **No `lake` command was run**;
`scripts/check_dyadic.sh`, `scripts/check_axioms.sh` and `scripts/check_ledger.sh` were not run.

## Headline

**Ticket 1.**  `fieldUni_TwoIsUniformizer KSqrtFive` is **discharged**.  One new module,
`GQ2/Dyadic/Instances/FieldSqrtFiveUnramified.lean`, nine declarations, nine pins, and the eight
arithmetic ones are all at `propext, Classical.choice, Quot.sound`: **the discharge costs no
axiom**.  `ℚ₂(√5)` now has a clause-free branch datum, so **three** of the five frozen quadratic
rows carry nothing.

**Ticket 2.**  Scoping `hdet` turned up a correction rather than a brief.  **Critical-path item
5, the LG5 ⇒ `GaussZResidueK` bridge, has had a `K` clone since 2026-08-01.**
`GQ2/Dyadic/GaussZ/FinalDK.lean` is registered at `GQ2.lean:585` and its §8 acceptance `example`
produces `KSupply.determinant`'s field type on the nose.  What is owed there is wiring.  The
genuinely unowned Gauss-`Z` obligation is the **candidate** side, `SqrtNeg2.PilotDet`, which the
memo lists separately as item 7, and it is materially cheaper than the L-row precedent for a
reason nothing in the docs states: **every one of the five frozen rows is at degree `n = 2`, so
`(-1)^n = +1` and the ramified and unramified clauses have the same target value.**

**Ticket 3.  Two HIGH findings, and both are the same defect wave 78 named.**

1. **Wave 78's vacuity list of five is incomplete: there is a sixth, and it was the one a reader
   meets first.**  `gBase_joinBase_of_residual` is vacuous at *both* ends and was missed at all
   three of its marking sites, including its own ⭐⭐⭐ docstring, which still says wave 75's
   first named input "is discharged by" the brackets.  Applied.
2. **The absorption note's "all have depth-3 analogues" is FALSE**, and a sibling was being asked
   to rely on it.  The three ingredients it *names* check out; every ingredient carrying T2, the
   kill, is hardcoded at depth 2.  Applied as a reconciliation on the note's forward-looking item.

On the named checks: `gAbs_supply_four` is **exactly** `SqClassClearingSupply h 4` with no hidden
binder; the unimod note's byte-identical axiom claim is **exactly right**, seven elements, same
order, zero difference in either direction.

**Ticket 4.  The W80 queue is not what wave 78 predicted, and the staleness rule earned its keep
twice in this lane.**  All three siblings moved during the wave, and at report time
`claude/w79-depth3` **refutes `GDecideBaseThree`** and `claude/w79-extract` **proves
`GJoinSeparationAll`**.  The second reverses wave 78's advice; the first would have made my own
Ticket-3 annotation false within the hour, and I amended it before committing.

---

## Ticket 1: `fieldUni_TwoIsUniformizer KSqrtFive`, discharged

### 1.1  The answer, and it was provable with committed pieces

New module `GQ2/Dyadic/Instances/FieldSqrtFiveUnramified.lean`, prefix `fieldFive`, 9
declarations, 9 `#print axioms`, no `sorry`, no new axiom, no `native_decide`, no
`maxHeartbeats`, no `maxRecDepth`, no line over 100 characters, no em-dash.
`scripts/mirror.sh check`: **OK**.

```
fieldFive_twoIsUniformizer   : fieldUni_TwoIsUniformizer KSqrtFive
fieldFive_genAsmBranch_sqrtFive :
  ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0      (no clause)
```

The wave-78 note scoped this as "small, self-contained" and priced it as
"`v₂(t² − 5u²)` is always even, because `t'² − 5u'² = −4 mod 8` at units".  That pricing is
right about the arithmetic and **wrong about where the work is**: the mod-`8` step is four lines,
and the load-bearing question was whether the tree could get from the spectral norm on `ℚ̄₂` to
the field norm at all.  It can, and the bridge is not in `Fields.lean`:

| piece | where | what it gives |
| --- | --- | --- |
| `norm_algebra_eq_norm_pow_finrank` | `GQ2/Dyadic/OddDegreeRamifiedI.lean:33` | `‖N_{K/ℚ₂}(z)‖ = ‖z‖^{[K:ℚ₂]}`, **with no `IsGalois` hypothesis** |
| `evenPolish_norm_quadElt` | `GQ2/Dyadic/Instances/EvenRangePolish.lean:188` | `N(t + u√a) = t² − a u²`, for `a` a non-square and `u ≠ 0` |
| `exists_repr` | `GQ2/Dyadic/Instances/Fields.lean:328` | every `z ∈ ℚ₂(√a)` is `t + u√a` |
| `not_isSquare_five` | `Fields.lean:150` | the same mod-`8` `decide`, one step earlier |
| `norm_two_alg` | `Fields.lean:613` | `‖(2 : ℚ̄₂)‖ = ‖(2 : ℚ₂)‖` |

So the missing arithmetic was one lemma wide, not one file wide.

### 1.2  The argument, and the one place it nearly went wrong

The content is that **the value group does not grow**: `‖z‖ ∈ ‖ℚ₂ˣ‖` for every `z ∈ ℚ₂(√5)`, so
there is nothing strictly between `‖2‖` and `1` for `‖z‖` to be, which is exactly
`fieldUni_TwoIsUniformizer`.

⚠ **The obvious route is false and I took the wrong one first.**  At the four *ramified* rows
`Fields.lean` §4 proves `‖x + y√a‖ = max ‖x‖ ‖y√a‖` from the parity separation, and the
temptation is to expect `{1, √5}` to be an orthogonal basis at `a = 5` too.  It is not:
`N(1 + √5) = −4`, so `‖1 + √5‖ = 1/2 < 1 = max(‖1‖, ‖√5‖)`.  The ring of integers is
`ℤ₂[(1 + √5)/2]`, not `ℤ₂[√5]`, precisely because `5 ≡ 1 (mod 4)`.  This is the same fact that
`Fields.lean` §4's `Odd a.valuation` hypothesis is protecting, seen from the other side, and any
lane re-deriving §4 at `a = 5` will hit it.

The route that works goes through the norm form, and factors as:

* `fieldFive_exists_sq_sub_five`: for **every** `s : ℚ_[2]`, `‖s² − 5‖ = ‖d‖²` for some `d ≠ 0`.
  Three cases and only the middle one is arithmetic: `d = 1` below `1` (the constant wins),
  `d = s` above (the square wins), and `d = 2` at a unit, because `s² − 5 = (s² − 1) − 4` with
  `‖s² − 1‖ ≤ ‖8‖ < ‖4‖`.
* `fieldFive_sq_sub_one_le_eight`: `‖s² − 1‖ ≤ 2^{−3}` at a unit, by `decide` over `ZMod 8` in
  the idiom of `Fields.norm_sub_one_le_norm_two`.
* `fieldFive_exists_sq`: divide by `u`, and `‖t² − 5u²‖ = ‖u·d‖²`.
* `fieldFive_norm_quadElt`: `N(t + u√5) = t² − 5u²` **with no `u ≠ 0`**, the committed statement
  extended across the boundary it excludes (at `u = 0` the element is a scalar and
  `Algebra.norm_algebraMap` gives `t²`, which is what the formula reads).
* Assembly: `‖z‖² = ‖N(z)‖ = ‖c‖²` with `c ∈ ℚ₂`, so `‖z‖ = ‖c‖`, and `ℚ₂`'s value group is
  discrete at the top (`fieldFive_norm_le_two`).

That the unit case answers `‖2‖²` and not `‖2‖` is the whole of unramifiedness: one full step of
the value group, not the half step a ramified field produces.

### 1.3  Pins, and what the row costs now

| declaration | axioms |
| --- | --- |
| `fieldFive_norm_five`, `_norm_two_zpow`, `_norm_le_two`, `_sq_sub_one_le_eight`, `_exists_sq_sub_five`, `_exists_sq`, `_norm_quadElt`, **`_twoIsUniformizer`** | the standard three |
| `fieldFive_genAsmBranch_sqrtFive` | the standard three, `peripheralCyclotomicAction`, and the even route's endpoint set (`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, `Foundations.absGalQ2_localEulerCharacteristic`) |

The row theorem's set is **exactly** wave 78's `fieldUni_genAsmBranch_sqrtTwo` set, verified by
print: discharging the clause added nothing, as removing it did not.

⚠ **Not registered.**  `GQ2.lean` is off-limits to this lane, so the module has no importer.
Registration is an owner or orchestrator step.

---

## Ticket 2: `hdet`, scoped, with a correction to the item above it

### 2.1  ⚠⚠ HIGH: critical-path item 5 double-counts a discharged obligation

`docs/dyadic/w74-critical-path.md:283-286`, verbatim:

> 5. `AffineDeterminantCertificate (galKProfinite K) ...`, the **LG5 ⇒ `GaussZResidueK` bridge**,
>    i.e. the (83)-evaluation rung from an Arf/zero-count statement to `GaussZResidueK`.
>    `KSupply.lean` is explicit that this has **no `K` clone** and that inlining a hypothesis named
>    after LG5 would have hidden the gap.  ⚠⚠

**The `K` clone exists.**  Verified directly, not taken on report:

* `GQ2/Dyadic/GaussZ/FinalDK.lean` exists and is registered at `GQ2.lean:585`;
* it carries `gaussZResidueDK_unramified` (`:553`), `gaussZResidueDK_ramified` (`:710`), the
  instance-path firewall `boundaryMapSub` (`:888`) and the headline `affineDeterminant_galK`
  (`:902`), the last stated at an arbitrary open `U ≤ AbsGalQ2` of index `n`, not at a fixed `K`;
* its §8 `Acceptance` block (`:975-1002`) contains an `example` whose statement is
  `AffineDeterminantCertificate (galKProfinite K) n (qOf K FF) P nuP SN T.tameFK pro2 (fun g => T.compatF_K pro2 nuP nu_compat g) (smulZmod2GalK K)`,
  i.e. `KSupply.determinant`'s field type (`KSupply.lean:317`) character for character, and it is
  discharged by one call to `affineDeterminant_galK`.

The source of the error is a docstring that ticket CB-DET did not edit when it landed the clone.
`GQ2/Dyadic/Instances/KSupply.lean:88`, verbatim:

> `GaussZResidueK`, whose `ℚ₂` ancestor is `GQ2/GaussZ/FinalD.lean` and which has no `K` clone.

From there it propagated to `GeneralAssembly.lean:255` ("The LG5 ⇒ `GaussZResidueK` rung has no
`K` clone and no owner lane") and `:284` ("No `K` clone of the LG5 ⇒ `GaussZResidueK` rung"), and
thence into the memo, `w74-house-note.md:157` and `w78-house-note.md:393`.  **All three Lean
sites annotated**, comment-only, with the as-of convention.  The `.md` notes are dated records
and are left; the memo's item 5 is an owner edit and is raised here.

This is `w78-house-note.md` §3.2's own rule, in the mirror image: *after a refutation lands, mark
every consumer* has a twin, **after a discharge lands, unmark every site that called it open**.
New-files-only protocol produces both.

⚠ Also corrected at `KSupply.lean`: §6 item 4 cites this file's own `determinant` field at
`:293`; it is at `:317`.

### 2.2  What `hdet` actually demands

`hdet` has six load-bearing sites (the other ~68 tree hits are local `have hdet :` binders and
`hdetect`/`hdetector` names).  The record field, `GQ2/Dyadic/Main.lean:381`, verbatim:

```lean
  /-- ⚠⚠ Candidate-side residual: the Gauss-`Z` clauses (no supplier lane; CB 9-of-11). -/
  hdet : SqrtNeg2.PilotDet (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
```

with binders also at `Main.lean:743`, `Instances/SqrtNeg2.lean:898` (consumed as
`determinant := hdet` at `:915`), `:1054`, and `Instances/Fields.lean:723`.  The four `M` rows
spell the same obligation inline rather than through a named `Prop` (`Main.lean:414`, `:458`,
`:503`, `:548`).

`PilotDet` (`Instances/SqrtNeg2.lean:886`) is
`AffineDeterminantCertificate (pilotGamma q) 2 q pilotP pilotNuP (standardNumerics 2) ...` with
`pilotGamma q := GammaR 2 q pilotW`.  Unfolded through `CertificateMain.lean:328` it is two
clauses, each over 17 binders plus a `{H,E,Y}` type/instance block, concluding
`GaussZResidueK (sourceBoundaryMapK tame pro2 compat) F (blockEnrichmentDK ...) l h (SN.gaussUnram m)`
and its ramified twin.  `GaussZResidueK` itself is at
`GQ2/Dyadic/Recursion/Phase140Assembly.lean:106`.

The `ℚ₂` ancestor `GQ2/GaussZ/FinalD.lean` is 364 lines and 4 declarations, of which the two
twins `gaussZResidueD_local_unramified` (`:107`) and `_ramified` (`:241`) are ~130 lines each and
~95% identical; roughly 50 lines per twin are `letI`/`haveI` re-keying of one module across six
syntactic spellings.  Portability is good: `GQ2/GaussZ/**` and `GQ2/Dyadic/GaussZ/**` contain no
`native_decide`, no `maxHeartbeats`, no `sorry` and no `axiom`, and all 18 `decide` calls are
two-element `ZMod 2` checks.  `maxHeartbeats` does appear 17 times in the candidate-side L lane,
up to `2400000`, which is the elaboration cost of the 17-binder clause shape; a pilot clone should
budget for it.

### 2.3  The lane brief

**The right precedent is not a `K`-clone at all.**  It is
`GQ2/Dyadic/Instances/GammaLDeterminant*.lean`, seven files and 2646 lines, which closes the same
`AffineDeterminantCertificate` for the L row over the same carrier shape `GammaR n q W`.  This is
a **word-side port**, not an arithmetic-side retype like `KSupply`/`galKProfinite`/`chiCycKTwo`.

From `GammaLDeterminantBridge.lean`, six pieces port **verbatim** (they are already stated over an
arbitrary `Gamma`): `SourceWordPhaseComparison` (`:56`), `.finsum_eq_gaussSum` (`:68`),
`WordPhaseResidueK` (`:88`), `sourceGauss_eq_of_wordPhase` (`:107`),
`gaussZResidueK_of_wordPhase` (`:124`), `gaussZResidueK_of_hessian` (`:159`).  Two retype
mechanically: `DeterminantWordPhaseSupply` (`:232`, ~65 lines) and
`affineDeterminantCertificate_of_wordPhaseSupply` (`:296`, ~40 lines), the latter with exactly one
substitution, `hZcard_of_uniformPushed` replaced by `SqrtNeg2.sqrtNegTwo_hZcard`
(`SqrtNeg2.lean:777`), which the existing `hsimp` binder already supplies.

**The pilot is materially cheaper than L, and the largest reason is not recorded anywhere.**

* **No Arf dichotomy.**  `standardNumerics n` (`Recursion/Numerics.lean:84-85`) has
  `gaussUnram m = (-1)^n · 2^{nm}` and `gaussRam m = 2^{nm}`.  The pilot is at `n = 2`, so
  `(-1)^n = +1` and **both clauses target `2^{2m}`**: one uniform proof, ignoring
  `hunram`/`hram`, discharges both.  L is odd degree, which is exactly why it needed
  `LRamifiedSourceArfSupply` and a 633-line `RamifiedData` file.  **This holds at all five frozen
  rows**, every one of which is at `n = 2 + 2·0`.
* **The word side is already certified and pins the same `+` value.**
  `GQ2/Dyadic/Certificates/N0.lean` carries `compactN_certificate` (`Word/Hessian.lean:662`),
  `nCompact_word_eq_certQ` (`:950`), `nCompact_G0` (`:1024`) and
  `sqrtNegTwo_gauss_degree_two` (`:1048`).  L has no `HessianCertificate` at all
  (`CertificateMain.lean:402`), which is why its lane built two phase models from scratch.
* **`hfinite` is free** from the existing `hsimp` binder.

**The one genuine obligation** is a single `SourceWordPhaseComparison` for the compact-`N` word at
`α = 2, h = 0`: a bijection `(VCocycle DD ρ ⧸ vCobRange DD ρ) ≃ V × V` together with
`QZeroBar DD ρ htriv x = plusFormD q q (e x)` pointwise.  `GammaLDeterminantHeadPhase.lean` (337
lines) is the template and looks marking-generic; a lane should check whether it retypes before
reproving.

| sub-obligation | kind | size |
| --- | --- | --- |
| wire `affineDeterminant_galK` into `KSupply.determinant` / `GenAsmRowResidual.determinant`, fix the stale docstrings | **mechanical**, closes memo item 5 as stated | half a wave |
| retype `DeterminantWordPhaseSupply` + the certificate producer at `pilotGamma q` | mechanical | ~120 lines |
| **the `SourceWordPhaseComparison` at compact-`N`** | **new mathematics.  This is the real `hdet`.** | ~400-600 lines, 12-20 decls |
| the `Mpc` rows' word-side equation | new mathematics, harder, **not** `hdet` | separate ticket |

Estimate for `hdet` proper: one file, ~15-25 declarations, ~550-750 lines, **1 to 1.5 waves**,
against L's 2646 for the same target.  Follow-on, near-free once the pilot exists:
`compactM_P1_certificate` *is* `compactN_certificate` (`Word/Hessian.lean:677-681`), so the two
`M0` rows should follow.

**Two traps to broadcast**, both recorded by CB-DET: the `ContinuousSMul ↥U (MuN 2)` instance-path
failure (name the `DistribMulAction`/`ContinuousSMul` pair as local instances and pass explicitly,
`FinalDK.lean:930-940`), and the `ProfiniteGrp`-bundled-topology poisoning that `boundaryMapSub`
(`:888`) firewalls.

Nothing on this rung is genuinely `ℚ₂`-only, and a pilot lane inherits `FinalDK`'s generic re-cut
by import (`GammaLDeterminantBridge.lean:8` already imports it).

---

## Ticket 3: watch round 16

### 3.1  Staleness, run first, and run **again** at report time

**(a) The sibling readings, taken at 08:27 rather than at lane start.**  Wave 78's §3.1(a)
diagnosed a house note that recorded a sibling module as unwritten three minutes after it merged,
and added the rule *re-read sibling modules at merge time, not at lane start*.  This lane ran that
check twice, and both readings changed:

| branch | at lane start (08:05) | at report time (08:27) |
| --- | --- | --- |
| `claude/w79-depth3` | `527adf51`, no commits | `74d01ee9`, **"refute the depth-3 base and the whole layer ladder"** |
| `claude/w79-extract` | `527adf51`, no commits | `c58e9729`, three commits |
| `claude/w79-mpc` | `527adf51`, no commits | `89ca7aa7`, two commits |

None of the three sibling modules exists at this lane's tree.  §4 reports them from their
branches, at those hashes, and says so at every claim.

**(b) ⚠⚠ The rule caught one of my own edits.**  Ticket 3(e) below adds a clause to
`GDecideBaseThree`'s docstring, and the clause I wrote said the `Prop` is **open**.  That was true
at `527adf51` and false on a sibling branch by the time I committed.  Amended before the commit
to say "open at this tree" with the in-flight refutation named, its branch, its hash, and the
consequence for `gAbs_markTransitivity_of_baseThree`.  **A house lane annotating a `Prop`'s status
is exactly as exposed to sibling drift as a house lane reading a sibling module**, and that is a
second clause the rule needs: *re-check any status word you write, at commit time*.

### 3.2  ⚠⚠ HIGH, check (e): the vacuity list is five and the answer is six

Wave 78 marked `GJoinBase h` and `GBaseResidual h` as refuted at four sites and named five
now-vacuous ⭐⭐⭐ theorems.  Enumerating every theorem in the tree that takes either as a
hypothesis gives **six**:

| # | theorem | file:line | marked before this lane? |
| --- | --- | --- | --- |
| 1 | `gJoin_defectVanishing_of_base` | `GradedUniformJoin.lean:1023` | yes |
| 2 | `gJoin_supply_of_base` | `GradedUniformJoin.lean:1037` | yes |
| 3 | `gJoin_markTransitivity_of_base` | `GradedUniformJoin.lean:1044` | yes, **but see §3.3** |
| 4 | **`gBase_joinBase_of_residual`** | **`GradedJoinBase.lean:649`** | **NO, at three sites** |
| 5 | `gBase_markTransitivity_of_residual` | `GradedJoinBase.lean:654` | yes |
| 6 | `gBase_supply_of_residual` | `GradedJoinBase.lean:659` | yes |

The miss is visible in the wording of both markers.  `GradedJoinBase.lean:637`, verbatim:

> ⚠⚠ **FALSE at every `h`**, as of `e6bbd2b9`: `gDecide_not_baseResidual`
> (`SqCore/GradedBaseDecide.lean`).  **The two composites below are vacuous.**

There are **three** theorems below.  `gBase_joinBase_of_residual` is the primary implication, not
a composite, so "the two composites" excludes it by construction.  The module header repeats the
same pair (`:94`, "So `gBase_markTransitivity_of_residual` and `gBase_supply_of_residual` below
are **vacuous**").

And it is the worst one to miss, because it is **vacuous at both ends**: wave 77 refuted its
hypothesis (`gDecide_not_baseResidual`) *and* its conclusion (`gDecide_not_joinBase`), and its own
⭐⭐⭐ docstring (`:643-644`) reads:

> **`GJoinBase h` from the residual.**  Wave 75's first named input is discharged by the
> `2 + 2h` brackets `⁅⁅x₁, letter⁆, x₁⁆` with content, at every selected marking.

Nothing is discharged.  **Applied**, comment-only, at three sites: the `GBaseResidual` marker
(two composites to three theorems, named), the theorem's own docstring (a ⚠⚠ "vacuous at both
ends" block), and the module header (a second amendment, which also supersedes the header's own
"is **discharged by**" sentence at `:70-71`, the one sentence wave 78's marker left standing).

### 3.3  ⚠ MEDIUM, check (e): a marked-refuted `Prop` still called an open item

`GradedUniformJoin.lean:1041-1043`, verbatim, thirty lines below wave 78's own marker on the same
`Prop`:

> ⭐⭐⭐ **The `h ≥ 1` residual, from three named inputs.**  Two of them are wave 74's own
> open items (the depth-`2` base and the knob realizability); the third is the `𝔽₂`
> bookkeeping of §7.

The depth-`2` base is `GJoinBase h`, which is refuted, not open.  This is the half-a-fix pattern
exactly: definition marked, consumer docstring not.  **Applied**, with the correction that one
input is open, the live route being `gJoin_markTransitivity_of_vanishing`.

### 3.4  ⚠⚠ HIGH, check (a): the absorption note's depth-generality claim

`docs/dyadic/w78-absorb-note.md:128-130`, verbatim:

> The ingredients that made depth 2 work all have depth-3 analogues in the tree
> (`gTower_decomp` is level-free, `gJoin_knob_dvd`/`gJoin_bundle_dvd` are depth-general,
> the corrected rows are depth-free)

The three **named** ingredients verify:

* `gTower_decomp` (`GradedUniformTower.lean:340`) is universally quantified in `k` with only
  `hk : 1 ≤ k`; the section contributes no hidden binder.  TRUE, with the mild qualification that
  it carries the standard `hsigma`/`hx0` marking hypotheses, which a depth-3 lane carries anyway.
* `gJoin_knob_dvd` (`GradedUniformJoin.lean:509`) and `gJoin_bundle_dvd` (`:523`) carry no depth
  literal and no `hk`; at `k := 1` they give the `2^4` bound depth 3 needs.  TRUE.
* The corrected-row **objects** (`gAbsRowS`, `gAbsRowX`, `gAbs_delta_eichU/V`, `gAbs_rowS_pivot`,
  the four `gAbs_row*_eich*`) carry no depth index.  TRUE as stated about the objects.

**The umbrella "all" is FALSE.**  The three named items are all T1/knob-side; every ingredient
carrying **T2, the kill**, is hardcoded at depth 2 and has no depth-3 analogue in the tree:

1. `gAbs_reach_le_layerDvd` (`GradedAbsorption.lean:332`) and its row instances (`:351`, `:355`)
   are at the literal `2` in both indices, and are the only three
   `gTowerReach _ ≤ gJoinLayerDvd _` statements in the tree.
2. `gAbs_xOne_tower_dvd` (`:308`) **exports `2^3`, one bit too weak**.  Depth 3 uses exponent
   `2^3·a` and `gJoinLayerDvd _ 3` demands `2^4`; instantiating at `a := 2a` still gives `2^3`.
   The `2^4` *is* proved, as the internal `have hall` at `:311-326`, and never exported.
   `gJoin_delta_zpow` is no escape: it wants `chiSq h x = 1` and `χ(x̃₁) ≡ −1 (mod 8)`.
3. `gAbs_kill_mid` (`:1224`) / `gAbs_kill_last` (`:1246`) bake in `2^3 ∣ ·` and `2^2·unit`;
   depth 3 needs `2^4` and `2^3·unit`.  Same for `gAbs_unit_mul_dvd` (`:1202`) and
   `gAbs_four_unit_not_dvd` (`:1211`).
4. The coker readings (`gAbs_delta_B_rowS` `:440`, `_B_rowX` `:449`, `_C_rowX` `:456`,
   `_C_rowS` `:465`) read the depth-2 elements `gAbsB`/`gAbsC`.  The depth-3 coker the note posits
   at `:116-117` has no reading lemma at all.

Related, and the same defect seen from the note's side: `:71-72`'s "in fact `16`-divisible" (and
`GradedAbsorption.lean:306`) is true of the proof and **not of the exported statement**.

Two things are **better** than the note says, and were relayed: the knob half is already packaged
depth-generally as `gJoin_knob_le_layerDvd` (`GradedUniformJoin.lean:596`), and the Eichler-tower
half genuinely is depth-free via `gJoin_zpow_vanish` (`:327`).

**Applied** as a ⚠⚠ reconciliation block on `w78-absorb-note.md`'s §"What W79 needs" item 1.  A
lane note is a dated record and this lane does not rewrite one, but that item is the note's
**forward-looking queue** and a sibling was acting on it during the wave, so the correction
belongs where the sibling reads it and not only here.

⚠ **Superseded within the wave, and the resolution is the honest one to record.**
`claude/w79-depth3` at `74d01ee9` does exactly the hoist item 2 above prices: `gDeep_xOne_tower_dvd`
is the depth-general `x̃₁`-tower lemma and `gDeep_reach_le_layerDvd` the depth-general kernel.  So
the blocker was real and is already cleared on a branch.  The reconciliation stands as a record of
what the note claimed against what the tree carried.

### 3.5  Check (b): `gAbs_supply_four` against `SqClassClearingSupply h 4`

**TRUE, exactly.**  `GradedAbsorption.lean:1400-1402`, verbatim:

```lean
theorem gAbs_supply_four (HV : GAbsVanishingTwo h) (HR : GTowerKnobRealizable h) :
    SqClassClearingSupply h 4 :=
  gJoin_supply_of_chiSupply (gAbs_chiSupply_four HV HR)
```

The section-variable trap was checked specifically, since it is the campaign's classic near-miss:
the file has no top-level `variable`, section `Reseed` (`:1328`) contributes exactly
`variable {h : ℕ}` (`:1330`), and the `variable (h) in` at `:1332` scopes to the next declaration
only.  Fully elaborated the theorem is `{h : ℕ} (HV) (HR)` and nothing else.  No instance binder,
no extra implicit, no hidden hypothesis.  The conclusion is literally `SqClassClearingSupply h 4`
(`GradedLimit.lean:236`), not a variant `Prop`, not `GJoinChiSupply`, not a restricted marking:
the route runs through the **stronger** `GJoinChiSupply h 4` and `gJoin_supply_of_chiSupply` drops
its extra `chiSq` clause.

`GAbsVanishingTwo` (`:1336`) was compared binder by binder against `GJoinDefectVanishing`
(`GradedUniformJoin.lean:191`) at `k = 2` and is exactly that instance, as `:1333` claims.

`scripts/mirror.sh check GQ2/Dyadic/SqCore/GradedAbsorption.lean`: exit 0, **103 pins printed**,
zero errors, zero warnings, zero sorries; 103 declarations and 103 pins, an exact bijection; all
std-3 except `gAbs_pow_combine` at `propext, Quot.sound`.  Everything the note's §1 claims about
its own hygiene reproduces.

The other five headline lines of the note's code block were checked too.  Three are exact
(`gAbs_leftover_decomp`, `gAbs_vanishingTwo_of_sep`, `gAbs_markTransitivity_of_baseThree`); two
are cosmetic renderings rather than statements (`gAbs_layer_wide`'s "`=`" is the *definition* of
`gAbsWide`, and `gAbs_zero_reader_reach` presents `e₁ = e₂ = 0` as a hypothesis when it is an
internal step, and drops three binders).  Recorded, not applied: a note's display line is not a
docstring.

⚠ LOW, worth stating because it affects how the result reads.  `GAbsVanishingTwo h` opens
`∀ nu' (j : Fin h)`, so it is vacuous at `h = 0` outright, and so is `SqClassClearingSupply 0 4`.
`gAbs_supply_four` at `h = 0` therefore carries no content.  That is not a defect (the target is
the `h ≥ 1` residual), but the note's "at `h = 0` ... a theorem outright" phrasing reads as an
achievement of the mechanism rather than an empty index.

### 3.6  Check (c): the byte-identical axiom sets, machine-checked

**Claim 2 is exactly right**, and this is the one that mattered.  Both prints, in full:

```
fieldUni_genAsmBranch_sqrtNegTwo : [propext, Classical.choice,
  hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, Quot.sound,
  Foundations.absGalQ2_isTopologicallyFinitelyGenerated,
  Foundations.absGalQ2_localEulerCharacteristic]
fieldId_genAsmBranch_sqrtNegTwo  : [ ... the same seven, in the same order ]
```

Seven elements each, identical as sets and as printed order, zero difference in either direction.
"Removing the clause added nothing" is exact.  Claim 3 also verifies: `fieldUni_genAsmBranch_sqrtTwo`
and `_sqrtFive_of_unramified` each carry those seven plus `peripheralCyclotomicAction`, and
`fieldId_genAsmBranch_sqrtTwo` carries the same eight, so the `M`/`N` split is unchanged.

⚠ **MEDIUM-LOW on claim 1, and it is a quantifier rather than a set.**  All 23 declarations the
note's parenthetical enumerates do print exactly the standard three.  But the note opens "Every
level statement", and the module's §6 is worse (`FieldUnimodularity.lean:720`, "Everything about
the **level** ... is at the standard three"), because three declarations whose conclusion is
literally `B.r = 0` sit outside the parenthetical and print **seven** each:
`fieldUni_level_zero_of_hpivot_sqrt{Five,Ten,NegTen}`.  The four extras come from the chosen
equivalence `fieldId_chosenEquivM_*`, not from the level argument, so the note's follow-on
sentence "the arithmetic discharged here costs **no** axiom" stays true.  **Annotated** at the
module; the note is a dated record and is left.

### 3.7  Check (d): identity headlines over containments

**Both new modules walked declaration by declaration.**  Clean counts, because a check that
reports only hits is not a check: `FieldUnimodularity.lean`, 49 declarations, 43 docstrings, **28
bold headlines checked**, ~19 identity- or unconditionality-flavoured; `GradedAbsorption.lean`,
103 declarations, 70 docstrings, **35 bold headlines checked** plus 9 section headers, ~24
identity-flavoured.  **63 headlines, 7 mismatches.**  Several are notably careful:
`gAbs_reach_le_layerDvd` says "lies in" over a `≤`, `fieldUni_level_zero_of_pivotM` says "forces"
over a `→`, and `gAbs_B_notMem_reach` really does carry no `hsigma`/`hx0`, so its unqualified
"no marking selection" is earned.

Four applied, all comment-only, all in `FieldUnimodularity.lean`:

1. **`:463`**, verbatim: `/-- **`√a` is a uniformizer of `ℚ₂(√a)`**, packaged for
   `nu_ur_recip_of_decomp`. -/`.  The statement is `‖√a‖ < 1` **only**, the first of the two
   halves of the B13 uniformizer spec; the maximality half is `fieldUni_rootUnit_max` at `:470`,
   which has no docstring at all.  The file elsewhere knows this: `:384-386` correctly calls
   `fieldUni_sqrtIn_max` "the **second half** of the B13 uniformizer spec", and §4 puts the same
   headline on the maximality `Prop` for `2`, which is the correct placement.  Annotated.
2. **`:680`, `:688`, `:695`**: "it **is** the level equation" over three one-directional
   statements `hpivot → B.r = 0`.  Annotated with the `forces` idiom the same file uses at `:125`,
   and noting the converse is one application of `fieldUni_pivotM_of_level_zero` away and simply
   not stated.  Nothing downstream turns on it: §5's vacuity argument uses only the forward
   direction.
3. **`:36-37`** (module header): "**on any `M0` or `N0` row the residual clause is exactly
   `B.r = 0`**" drops the two qualifiers the same docstring carried correctly twelve lines
   earlier.  The `iff`s hold at `α ≥ 2` **and `h = 0`**.  Annotated.
4. **`:251-252`**: "the only inputs are the degree pin, the oriented equivalence and `B.r = 0`"
   omits `halpha : 2 ≤ alpha`, which `hdeg` does not imply.  Four inputs, three named.  Annotated.
   The `N0` twin enumerates nothing and is clean.

Three found in `GradedAbsorption.lean` and **reported, not applied**, because the module landed
last wave and its lane is the right owner of a retitle:

* `:649-653`, `⭐⭐ **The Eichler bracket squares reach unconditionally**`: the statement is a
  general lemma about any `t` with **three** genuine hypotheses (`hadm`, `hfar`, `htow`), not the
  marking conditions the file's "unconditionally" idiom elides elsewhere.  The earned
  "unconditionally" already sits correctly on `gAbs_eichU_triple_mem` at `:690`.
* `:615`, "The Eichler-cleared letters are `γ₁`-elements": the statement is
  `∀ x : DSq h, x ∈ twoCentralSeries (DSq h) 1`, i.e. every element.  An **under**-claim, harmless
  for soundness, but the name `gAbs_mem_one` matches the statement and the docstring does not.
* `:1147-1149`, "the exact unconditional content of the depth-2 base": substantively earned, but
  by three declarations rather than this one (`gAbs_layer_wide` plus `gAbs_B_notMem_reach` and
  `gAbs_C_notMem_reach` at `:1301`, `:1310`).  Borderline; reported for completeness.

### 3.8  Check (e), the rest: what came back clean

* **No live theorem anywhere in the tree depends on any of the six vacuous ones.**  Traced: the
  only consumers of `gJoin_supply_of_base` / `gJoin_markTransitivity_of_base` are inside the two
  vacuous `gBase_*_of_residual` composites, and `GradedAbsorption.lean` deliberately routes around
  them through `gJoin_supply_of_vanishing` / `gJoin_markTransitivity_of_vanishing`.  No
  contamination.
* No `variable` binder anywhere introduces either refuted `Prop` implicitly, so the six are the
  complete set.
* All 37 `.md` hits on the four grep subjects are in **dated lane notes**, none in a
  forward-looking queue.  `owner-items-2026-08-05.md` was checked specifically: its live wave-78
  block reads correctly ("the sole layer-side one being the depth-3 base"), and the "single
  depth-2 base" phrasing at `:100` is inside the dated `## Status at wave 74` block.
  `w74-critical-path.md` has no relevant hits.
* Wave 78's fixes at `GradedJoinBase.lean:86-89` and `GradedUniformJoin.lean:973-982` are good:
  each quotes the superseded sentence and scopes what the refutation does **not** settle.
* `GradedAbsorption.lean:12` and `GradedBaseDecide.lean:9-31` both present the refuted `Prop`s as
  refuted.  Correct.
* One nit **applied**: `GradedBaseDecide.lean:570` names `GJoinBase` in `GDecideBaseThree`'s
  docstring 36 lines after refuting it, with no clause distinguishing the two.  Clause added, and
  then amended per §3.1(b).

---

## Ticket 4 (report only): the W80 queue

**Everything in §4.1 is read from unmerged sibling branches at the hashes given, at 08:27.  Re-read
at merge time.  Nothing here is a tree fact.**

### 4.1  What each sibling leaves

**`claude/w79-depth3` at `74d01ee9`** (2 commits, `GQ2/Dyadic/SqCore/GradedDepthThree.lean`, 253
lines, prefix `gDeep`).  ⚠⚠ **A refutation, not a discharge, and it is larger than its ticket.**

```
gDeep_not_layerReach     (k) (nu') : ¬ GTowerLayerReach h nu' (k + 2)   -- EVERY depth, EVERY marking
gDeep_not_layerReach_three  (nu') : ¬ GTowerLayerReach h nu' 3
gDeep_not_baseThree               : ¬ GDecideBaseThree h                -- every h, no hypotheses
```

The witness is `gAbsB h ^ 2^k`, exactly row-trivial in `γ_{k+3}`, reading `2^{k+2}·unit` at the
corrected `σ`-row while the depth-`(k+2)` reach reads `2^{k+3}`-divisibly.  If this stands, then:

* **wave 78's re-seeded reduction loses its sole layer-side input**, and
  `gAbs_markTransitivity_of_baseThree` (`GradedAbsorption.lean:1438`) becomes the **seventh**
  vacuous ⭐⭐⭐ theorem, needing the same marker §3.2 applied to the sixth.  The standing
  checklist item fires again the moment this merges.
* The route is not "raise the depth".  `gDeep_not_layerReach` kills the ladder at *every* depth,
  so a wave-80 lane must not queue "the depth-4 base" as the successor.  What survives is the
  supply itself: `SqClassClearingSupply h k` and `limFinal_markTransitivity_iff` are untouched by
  a layer refutation, exactly as they were by the depth-2 one.
* The lane also did the hoist §3.4 item 2 priced (`gDeep_xOne_tower_dvd` depth-general, and
  `gDeep_reach_le_layerDvd` at `k + 2`), which is reusable regardless of the refutation.

**`claude/w79-extract` at `c58e9729`** (3 commits, `SqCore/GradedExtraction.lean`, 555 lines,
prefix `gExt`).  ⚠⚠ **`gExt_separationAll (h : ℕ) : GJoinSeparationAll h` is proved outright**,
via `gExt_towerSeparation : GJoinTowerSeparation h nu' k` at every `k` and every marking, from the
handle-tower words `gExtWordU`/`gExtWordV` and their row readings.  This **inverts wave 78's
§4.3 twice over**: that section said separation "has no live consumer at all" and advised against
it; a lane took it and closed it.

**`claude/w79-mpc` at `89ca7aa7`** (2 commits, `Instances/MpcCertificate.lean`, 513 lines, prefix
`mpcCert`).  The `Mpc` marked-core certificate producer, which the tree had for no shape, plus
`mpcCert_genAsmBranch_sqrtTen` and `_sqrtNegTen`.  That is `w78-unimod-note.md` §6 item 2, the
"genuine gap that wave 77's framing hid", closed in one wave.

### 4.2  The flagship scoreboard

**Selector side, the five frozen quadratic rows.**  With this lane's Ticket 1 and, subject to
merge, `w79-mpc`:

| row | pres | branch datum | clause |
| --- | --- | --- | --- |
| `ℚ₂(√−2)` | `N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | **none** (W78) |
| `ℚ₂(√2)` | `M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | **none** (W78) |
| `ℚ₂(√5)` | `M0 2 0` | **`fieldFive_genAsmBranch_sqrtFive`** | **none** (this lane) |
| `ℚ₂(√10)` | `Mpc 2 1 false 1` | `mpcCert_genAsmBranch_sqrtTen` | per `MpcRowData_sqrtTen`, unmerged |
| `ℚ₂(√−10)` | `Mpc 2 1 true 1` | `mpcCert_genAsmBranch_sqrtNegTen` | likewise |

So the selector half of the general statement is closed at three rows unconditionally and, subject
to merge and to reading `MpcRowData_*`, addressed at the other two on the row the frozen table
actually names.  **A W80 lane should check what `MpcRowData_sqrtTen` unfolds to**; this lane did
not, since the module is unmerged.

**Record side.**  `w74-critical-path.md`'s eight items, updated:

* **Group A**: A1 discharged at all five rows.  A2 discharged on the general-record path, untouched
  on `Main.lean`'s; wave 78's §3.4 adjudication stands and is still an owner call.  ⚠ Neither
  closes the `α` pin at a general ramified-`i` `K`.
* **Group B, ASK at `G_K`**: items 3 and 4 unchanged and unowned.  **Item 5 is not open**: see
  §2.1.  What is owed is the wiring, which is half a wave and which no lane has been asked for.
* **Group C, CAND**: item 6 (four certificate-to-count bridges at `GammaR n q word`) is a uniform
  residual on four even rows.  Item 7's `hsimp`/`hsplit`/`hZcount` unchanged; **`hdet` is scoped in
  §2.3 and is dispatchable**.  Item 8's `nuP` build unchanged.
* **The sharpest item on the list is now `hdet` alone**, and it is smaller than the memo implies,
  for the `n = 2` reason in §2.3.

**Graded side.**  Subject to the two unmerged refutation/discharge pairs: the layer ladder is dead
at every depth, separation is proved, `GTowerKnobRealizable h` remains the live interface (wave
78's §4.3 was right about realizability and wrong about separation), and
`SqClassClearingSupply h k` is where it has been since wave 67.  **The W80 question is what
replaces the layer route**, not which depth to try next.

### 4.3  The owner items

* **The plan-A6 freeze on `GQ2/Roe/*`** is still open, carried from round 11 through W75 §8 item
  6, W76 §4.4, W77 §4.5, W78 §4.4 and this round.  Untouched here:
  `git diff --name-only 527adf51..HEAD` returns zero paths under `GQ2/Roe/`.  **The oldest live
  owner item in the campaign, and now the only one with no motion in five rounds.**
* **The 100-character question.**  Still no policy.  This lane held to 100 and added none: the
  three over-length lines in files it edited (`GeneralAssembly.lean:386`,
  `KSupply.lean:28`, `:275`) are all pre-existing and were verified against `527adf51`.  The
  wave-77 field lane's two over-length lines are still there.  The state is unchanged from wave
  78's description, which called it worse than when it was minor.
* **The pilot-record call** (`527adf51`, "surface the pilot-record call") is unchanged by this
  lane; §2.1 sharpens what it costs, since the ASK side of the pilot record is closer to done than
  the memo says and the CAND side is the real remainder.
* **Registration**: `GQ2/Dyadic/Instances/FieldSqrtFiveUnramified.lean` needs an import line.
  `GQ2.lean` is off-limits to this lane.
* **Two corrections for the owner's own dated blocks**, not edited here: `w74-critical-path.md`'s
  item 5 and its `:95` table row both say the LG5 bridge has no `K` clone (§2.1); and wave 78's
  "Group A is now empty of open mathematics" qualification is still outstanding in
  `owner-items-2026-08-05.md`.
* **New standing-checklist clause**, from §3.1(b): *re-check any status word you write (open,
  refuted, discharged) at commit time, not at lane start.*  A house lane's own annotations drift
  exactly as fast as the sibling modules it reads, and this round produced an instance.

---

## Verification record

* Lane `claude/w79-house`, base `527adf51`.  **Three commits**, all path-limited, the last of them
  the one that sets this figure.  **Not pushed.**
* **No `lake` command was run.**  `scripts/mirror.sh sweep` once at lane start (**5903
  artifacts**), then `check` on every edited file after every edit.  All green, no error, no
  warning, no sorry:

  ```
  GQ2/Dyadic/Instances/FieldSqrtFiveUnramified.lean  OK  (9 pins printed, new)
  GQ2/Dyadic/SqCore/GradedUniformJoin.lean           OK
  GQ2/Dyadic/SqCore/GradedJoinBase.lean              OK
  GQ2/Dyadic/SqCore/GradedBaseDecide.lean            OK  (twice: after the clause, after §3.1(b))
  GQ2/Dyadic/Instances/KSupply.lean                  OK
  GQ2/Dyadic/GeneralAssembly.lean                    OK
  GQ2/Dyadic/Instances/FieldUnimodularity.lean       OK
  ```

  `GQ2/Dyadic/SqCore/GradedAbsorption.lean` was `check`ed read-only for §3.5 and not edited.
* **Comment-only discipline, verified mechanically.**  Every edited pre-existing `.lean` file was
  comment-stripped (nested block comments, docstrings and line comments removed, string literals
  respected, whitespace collapsed) and compared against `527adf51`:

  ```
  GQ2/Dyadic/SqCore/GradedUniformJoin.lean       IDENTICAL
  GQ2/Dyadic/SqCore/GradedJoinBase.lean          IDENTICAL
  GQ2/Dyadic/SqCore/GradedBaseDecide.lean        IDENTICAL
  GQ2/Dyadic/Instances/KSupply.lean              IDENTICAL
  GQ2/Dyadic/GeneralAssembly.lean                IDENTICAL
  GQ2/Dyadic/Instances/FieldUnimodularity.lean   IDENTICAL
  ```

  So no statement, term, binder, name or proof changed in any pre-existing file.  The lane's only
  non-comment content is the new module.
* `GQ2.lean` was not touched.  Nothing under `GQ2/Roe/` was touched (plan A6).  None of
  `SqCore/GradedDepthThree.lean`, `Instances/MpcCertificate.lean`, `SqCore/GradedExtraction.lean`
  was created or touched; none exists at this tree.
* No line over 100 **characters** was added to any Lean file (measured in codepoints: `awk 'length'`
  counts bytes here and reports false positives on every line with `⁅` or `ℚ`).  No em-dash was
  added to any file.

## Files touched

**Lean (7):** `Dyadic/Instances/FieldSqrtFiveUnramified.lean` (**new**, the only non-comment
content); and comment-only at `Dyadic/SqCore/GradedJoinBase.lean`,
`Dyadic/SqCore/GradedUniformJoin.lean`, `Dyadic/SqCore/GradedBaseDecide.lean`,
`Dyadic/Instances/KSupply.lean`, `Dyadic/GeneralAssembly.lean`,
`Dyadic/Instances/FieldUnimodularity.lean`.

**Docs (2):** `w79-house-note.md` (new); `w78-absorb-note.md` (§3.4's reconciliation block).
