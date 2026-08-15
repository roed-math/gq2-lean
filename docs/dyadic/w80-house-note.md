# W80-HOUSE: watch round 17, the `hdet` lane brief, and the W81 queue

**Lane W80-HOUSE, branch `claude/w80-house`, base `4f30776b`.**  Standing verification lane.
Comment-only edits to five existing files, one new report.  No `lake` command was run; no new
declaration, no `sorry`, no axiom, no statement changed anywhere.

Verification of record: `scripts/mirror.sh sweep` at lane start (5923 artifacts), then
`scripts/mirror.sh check` on each of the five edited files after the edit.  All five `OK`, zero
errors, zero warnings.

Commit: `a08e046f` (the annotation sweep).

**Line-number convention.**  Every `file:line` below is at the base `4f30776b`, i.e. where the
text was when it was read.  This lane's own comment-only edits shift some of those lines
downward in the five files it touched; the declaration names are stable and are the thing to
grep for.

---

## Headline

**Wave 79's refutation landed and its own instruction was carried out on one module out of
four.**  `gDeep_not_baseThree` and `gDeep_not_layerReach` merged at `9fb4869b`.  The
merge-time annotation (`bddf838b`) marked the section header of `GradedExtraction.lean` and
nothing else.  Left unmarked: the three `gAbs_*_of_baseThree` composites, the
`GDecideBaseThree` definition (whose own W79-HOUSE clause said the refutation was **in flight
and unmerged** and named exactly what to do if it landed), `gDecide_layerReach_of_baseAt`,
`gDecide_tower_of_baseThree`, the `GTowerLayerReach` definition and the seven theorems that
hypothesise it, and **two docstrings inside the annotated module itself** that still said
"the OPEN depth-3 base".  All marked here.

**The refutation is also wider in kind than the vacuity list records.**  Before wave 79 the
layer statement was refuted at ONE marking (`gDecideNu h`) and ONE depth (`k = 2`).
`gDeep_not_layerReach` refutes it at every depth and every marking, which turns the whole
`gTower_*_step` family of `GradedUniformTower.lean` from "conditional on an open input" into
"vacuous".  That family was not in any previous wave's count.

**Second finding, for the sibling building on it this wave.**  The extract note's repair
sentence names ONE clearing step (`gTower_clear_step`) where there are FOUR, three of which
are on the live route and the named one is on none of them; and "preserved by
`gTower_clear_step`" is a fact about that lemma's PROOF, not about its statement, which
existentially quantifies the corrected dressing and records nothing of its shape.  Details in
§1.2, and the W80-XFREE lane's own first commit already has the right invariant, so what this
correction changes is the list of lemmas that must be re-proved with it.

---

## Ticket 1: watch round 17

### 1.0  Staleness, run first

* Base `4f30776b` is the tip of `dyadic` in the main clone at lane start and at report time.
* Four W80 worktrees exist, all created at `4f30776b`: `w80-house` (this lane), `w80-rowdata`,
  `w80-uniform`, `w80-xfree`.  Nothing has merged to `dyadic` this wave.
* **Sibling readings, at the hashes given, unmerged, not tree facts.  Re-read at merge time.**
  `claude/w80-xfree` at `b731f241` (1 commit); `claude/w80-uniform` at `5f0ec1e1` (1 commit,
  module opened only); `claude/w80-rowdata` at `74cdc896` (3 commits, and see §3.1 - one of
  them takes a queue item this note would otherwise have proposed).
* The three sibling-owned paths (`SqCore/GradedUniformGen.lean`, `SqCore/GradedXFree.lean`,
  `Instances/MpcRowData.lean`) were not created or touched here.
* The wave-79 landings named in the ticket are all present at their cited lines:
  `GradedDepthThree.lean` (57651 bytes), `GradedExtraction.lean` (37112), `MpcCertificate.lean`,
  `FieldSqrtFiveUnramified.lean`, and the four w79 notes.

### 1.1  ⚠⚠ HIGH, check (f): the vacuity sweep, and it is a third of a fix

The merge annotation `bddf838b` is comment-only and correct as far as it goes.  Grepping the
subjects gives the full consumer set.  **Consumers of `GDecideBaseThree h`:**

| # | theorem | file:line (pre-edit) | marked at the merge? |
| --- | --- | --- | --- |
| 1 | `gDecide_tower_of_baseThree` | `GradedBaseDecide.lean:600` | no |
| 2 | `gAbs_defectVanishing_of_baseThree` | `GradedAbsorption.lean:1407` | **no** |
| 3 | `gAbs_supply_of_baseThree` | `GradedAbsorption.lean:1430` | **no** |
| 4 | `gAbs_markTransitivity_of_baseThree` | `GradedAbsorption.lean:1438` | **no** |
| 5 | `gExt_defectVanishing_of_baseThree` | `GradedExtraction.lean:536` | yes (section header) |
| 6 | `gExt_supply_of_baseThree` | `GradedExtraction.lean:541` | header yes, **docstring no** |
| 7 | `gExt_markTransitivity_of_baseThree` | `GradedExtraction.lean:549` | header yes, **doc no** |

**Consumers of `GTowerLayerReach h nu' k` at `2 ≤ k`**, every one of which is now vacuous at
every marking and every depth and none of which was marked: `gTower_comm_adm_step`
(`GradedUniformTower.lean:1209`), `gTower_comm_tower_step` (`:1229`), `gTower_sq_step`
(`:1251`), `gTower_comm_step` (`:1291`), `gTower_full_layer_step` (`:1335`),
`gTower_layerReach_step` (`:1580`, ⭐⭐⭐), `gTower_layerReach_of_base` (`:1592`, ⭐⭐⭐),
`gDecide_layerReach_of_baseAt` (`GradedBaseDecide.lean:590`, ⭐⭐).  Also
`gBase_layerReach_of_xOneTriple` (`GradedJoinBase.lean:633`), whose CONCLUSION is now refuted
at every marking rather than at one.

Verbatim, `GradedBaseDecide.lean:574-581`, the W79-HOUSE clause on `GDecideBaseThree`:

> `GDecideBaseThree` is the depth-`3` analogue.  It is **open at this tree** [...] but ⚠⚠ **a
> refutation is IN FLIGHT and unmerged** [...] Do not restart this `Prop` as a lane target
> without checking whether that branch landed; if it did,
> `gAbs_markTransitivity_of_baseThree` (`SqCore/GradedAbsorption.lean`) becomes vacuous and
> needs the same marker the two `gBase_*_of_residual` composites carry.

It landed.  "Open at this tree" and "IN FLIGHT and unmerged" are both false at `4f30776b`, and
the instruction the clause gives was not followed.  **Correction applied**, comment-only, at
nine sites across five files: the `GDecideBaseThree` definition, `gDecide_layerReach_of_baseAt`,
`gDecide_tower_of_baseThree`, the `GradedAbsorption` §8 header and its three composites, and
the `GTowerLayerReach` definition (which covers the whole `gTower_*_step` family by reference,
naming each member, rather than eight separate markers on machinery a reader meets through the
`Prop`).

Verbatim, `GradedExtraction.lean:540`, twenty-one lines BELOW the merge marker that says the
base is refuted:

> ⭐⭐ **The per-class supply from two inputs**: the OPEN depth-3 base and the extraction.

and `:547-548`:

> The middle one is now a theorem (`gExt_separationAll`), so the odd route hangs on the
> depth-3 base and the extraction only.

The odd route does not hang on the depth-3 base; that base is false.  **This is the half-a-fix
pattern occurring inside the module that carries the fix**, which is the sharpest form the
wave-78 rule has taken so far.  Both corrected.

The recurring shape, stated once for the standing checklist: **a marker on a section header
does not mark the declarations in the section.**  Wave 78 marked a definition and missed the
consumers; wave 79 marked a header and missed the docstrings under it.  A grep of the subject
name is the only reliable sweep, and it takes one command.

### 1.2  ⚠⚠ HIGH, check (b): the `x₁`-freeness entry points, for the lane building on them now

`docs/dyadic/w79-extract-note.md:151-153`, verbatim:

> So the W80 shape is: carry an `x_1`-freeness clause on the dressing through
> `SqClassClearingSupply` (it is preserved by `gTower_clear_step`, whose correction is a
> `gamma_k`-element, and it holds at the class-3 base) [...]

**Truth at `bridgeDress`: CONFIRMED, at the cited line.**  `GradedBridge.lean:340` defines

```lean
noncomputable def bridgeDress : (DSq h : Type) :=
  zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j)) (bridgeRowV nu' j) *
      zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxV j)) (bridgeRowU nu' j) *
    zpowZtwo (isProP_DSq h) (sqPivot h) (-(2 * bridgeRowU nu' j * bridgeRowV nu' j))
```

and `sqPivot h = sqMixPivotElem h sqPivotExp = dsqSigma h * (x₀^c)⁻¹`
(`Certificate.lean:169`, `MarkedCore/Certificate.lean:909`), so all three factors are powers of
letters other than `x₁`.  The pivot factor is additionally an even power and so dies mod `γ₂`
anyway.  `bridgeTuple` (`GradedBridge.lean:353`) puts `bridgeDress` on slots `0` and `1` and `1`
elsewhere, and it is the witness of BOTH class-three suppliers, `sqClassThree_supply`
(`:649`) and `gJoin_chiSupply_three` (`GradedUniformJoin.lean:226`).  Nothing to correct.

**Preservation: the claim is true of the proof and NOT available from the statement, and it
names the wrong lemma.**  Two separate problems.

(i) `gTower_clear_step` (`GradedUniformTower.lean:1732`) concludes

```lean
    ∃ a' : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a' i) = 1) ∧ (∀ i, nu' (a' i) = 1) ∧
        SqModTwoIndep (sqArbFrame h nu' j a') ∧
          sqRelWord (sqArbFrame h nu' j a') ∈ twoCentralSeries (DSq h : Type) (k + 2)
```

The witness the proof supplies is `fun i => a i * d i` with `d i ∈ twoCentralSeries _ k`, so the
clause IS preserved by the construction.  But the existential records nothing about `a'`, so a
lane that applies the lemma as a black box gets no clause back.  Every one of these step
lemmas has to be **re-proved** with the clause threaded, not applied.  The same holds one level
up: `SqClassClearingSupply` and `GJoinChiSupply` are themselves existentials in `a`.

(ii) There are FOUR clearing steps, and `gTower_clear_step` is on none of the live routes:

| lemma | file:line | on the live route? |
| --- | --- | --- |
| `gTower_clear_step` | `GradedUniformTower.lean:1732` | **no**, superseded by the join version |
| `gJoin_clear_step` | `GradedUniformJoin.lean:233` | yes, the `∀ k` route |
| `gAbs_clear_step_two` | `GradedAbsorption.lean:1366` | yes, rung 2 of the class-5 chain |
| `gDeep_clear_step_three` | `GradedDepthThree.lean:997` | yes, rung 3 of the class-5 chain |

The live class-5 chain is `gJoin_chiSupply_three` (base, `bridgeTuple`) then
`gAbs_clear_step_two` then `gDeep_clear_step_three` then `gJoin_supply_of_chiSupply`, inside
`gDeep_chiSupply_five` (`GradedDepthThree.lean:1025`).  The live all-classes route is
`gJoin_supply_of_vanishing` (`GradedUniformJoin.lean:260`) over `gJoin_clear_step`.

**So the minimum x₁-free re-proof set is**: an x₁-free `GJoinChiSupply`, then x₁-free variants
of `gJoin_clear_step`, `gAbs_clear_step_two`, `gDeep_clear_step_three`,
`gJoin_supply_of_vanishing`, `gDeep_chiSupply_five` and `gDeep_supply_five`, plus the weakened
`GTowerKnobRealizable` itself and `gDeep_defectVanishing_of_kills` /
`gDeep_markTransitivity_of_kills` if the endpoint is to be reached.  Patching
`gTower_clear_step` and `gTower_supply_of_vanishing` is wasted work: they are the superseded
pair.

The W80-XFREE lane's own first commit (`b731f241`, unmerged) already has the right invariant:
`gXfSpan h := gTowerFar h ⊔ twoCentralSeries (DSq h) 2`, a subgroup, with `gXf_free_mul_gamma`
stated abstractly at any `k ≥ 2` and `gXf_bridgeTuple_free` as the base.  Both of the note's
mathematical claims hold.  What this correction changes is only the target list.

### 1.3  ⚠ MEDIUM, check (e): headline claims stronger than their statements

Ranked; all verified against the Lean at the line given.

**(a) `GradedExtraction.lean:46`**, module docstring, verbatim:

> Everything in this file is unconditional.

False of §5 and §6.  §5's three composites carry `GDecideBaseThree h` and
`GTowerKnobRealizable h`; every substantive §6 dressing lemma carries `hk : 2 ≤ k`
(`gExt_comm_dress`, `gExt_dress_handles`, `gExt_dress_full`, `gExt_dress_move`,
`gExt_frame_move`).  The sentence is about the separation, which is genuinely unconditional.
**Corrected**, scoped.

**(b) `GradedDepthThree.lean:704-706`**, verbatim:

> This is the REFUTED `GTowerLayerReach h ν' 3` with the squared two-class coker adjoined: the
> exact unconditional content of the depth-3 base.

Two errors in one sentence.  `gDeep_layer_wide` carries `hsigma`/`hx0`; `GTowerLayerReach h nu' k`
(`GradedUniformTower.lean:1123`) carries **no** marking selection at all, so the object being
widened is the body of `GDecideBaseThree h`, not `GTowerLayerReach`.  And "the exact content"
claims an identity where the conclusion is `levelMk _ 5 g ∈ gDeepWide h nu'`, a membership in a
join: an upper bound.  Minimality is proved generator by generator
(`gDeep_B_sq_notMem_reach`, `gDeep_C_sq_notMem_reach`), not for the span.  **Corrected.**

**(c) `GradedDepthThree.lean:100-101`**, verbatim:

> **The `x̃₁`-tower at depth `k + 2` reads `2^{k+3}`-divisibly at every row** (in fact
> `2^{k+4}`-divisibly)

The conclusion is `(2 : ℤ_[2]) ^ (k + 3) ∣ …`.  The `k+4` bound is a local `have` inside the
proof and is deliberately weakened on the last line by `pow_dvd_pow`.  A caller citing the
parenthetical does not get it.  **Corrected**, noting where the sharp form lives.

**(d) `MpcCertificate.lean:45, 47, 49, 53`**, verbatim at `:53`:

> The three "iff"s are the content of `MpcMarkedData`, §2's named clause.

No `Iff` is proved in the file.  `mpcCert_markedMatching` consumes `MpcMarkedData` as a
hypothesis: the "if" halves only.  The nearest formalized necessity is
`mpcCert_level_le_of_pivot` / `mpcCert_level_le_of_certificate`, which conclude `B.r ≤ r` and say
nothing about the `D̄` and `B̄` residues.  The next paragraph of the same docstring is careful
and correct ("The three congruences do not follow from the level alone"), which is why this is
medium and not high.  **Reported, not edited** (`Instances/MpcRowData.lean`'s owner is a
sibling this wave and the two files are read together).

**(e) `MpcCertificate.lean:513-514`**, verbatim:

> at `B.r = 1` the procyclic certificate is the only marked-core certificate available on an
> `M`-family row.

`mpcCert_isEmpty_certificateM_of_level` proves that the COMPACT certificate is uninhabited when
`B.r ≠ 0`.  That the procyclic one is inhabited at `B.r = 1` is exactly what `MpcRowData_*`
assumes; and no third type is excluded.  **Reported, not edited**, same reason.

**(f) `GradedDepthThree.lean:514`**, verbatim: "**The depth-3 layer lands in the widened full
reach**, unconditionally".  `gDeep_zLayer_le_wideFull` carries `hsigma`/`hx0`.  The word means
"with no layer-statement input" throughout this file, and the file also uses "No marking
selection is needed" at `:209` for a statement that genuinely has none, so the two senses sit
forty lines apart.  **Reported, not edited**: the §1.3(b) marker on the same usage covers the
reading.

**`FieldSqrtFiveUnramified.lean` is clean.**  Every docstring matches its statement, including
the two most at risk: `:93-95` keeps its inequality form explicitly rather than converting to a
non-membership, and `:207-208`'s headline matches `fieldUni_TwoIsUniformizer` as defined at
`FieldUnimodularity.lean:593`.  `:51-55` carries an explicit Scope block confining the
general-`K` `Prop` to `KSqrtFive`.

### 1.4  Check (a): the depth-3 note's two cost claims, both CONFIRMED

`docs/dyadic/w79-depth3-note.md` §2, verbatim:

> all six families of the `γ₄/γ₅` generation record (`cfiveSpan_zLayer_le_gens_dsq`, the
> level-5 record wave 78 priced as "the bulk"; it was already in the tree from waves 72-73, so
> the port cost nothing)

True on every clause.  `cfiveSpan_zLayer_le_gens_dsq` is at
`GradedClassFiveKnob.lean:788`, introduced by `ed3f3daf` ("run the reduction a second time,
down to six families over Q5", 2026-08-12) on `claude/w72-five`.  `GradedDepthThree.lean`
imports exactly one module, `GQ2.Dyadic.SqCore.GradedAbsorption`, and the record is reachable
through `GradedAbsorption → GradedUniformJoin → GradedUniformTower → GradedClassFiveJoin →
GradedClassFiveKnob`, so no import was added and no port was written.  It is used once, at
`GradedDepthThree.lean:519`.

> The γ₃-analogues of the `gThreeFour` kit the ticket priced were NOT needed:
> `gTower_sq_congr`/`gTower_reach_step`/`gTower_commHom_span` are depth-general already

True.  `gThreeFour` occurs 0 times in `GradedDepthThree.lean` (the kit is in
`GradedClassFourKnob.lean` and `GradedClassFourDefect.lean`).  The three named depth-general
lemmas are used 4, 1 and 1 times respectively, and `gTower_decomp` once.  The only `cfour`/
`cfive` names the module touches are `cfourId_modTwoIndep_mul`, `cfour_commP_mem_two`,
`cfiveSpan_sq_mem_lambdaTwo`, `cfiveSpan_zLayer_le_gens_dsq`, `cfive_commP_mem_succ`.

### 1.5  Check (c): the near-miss check on `gDeep_supply_five`, CLEAN

`GradedDepthThree.lean:1039-1041`:

```lean
theorem gDeep_supply_five (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) :
    SqClassClearingSupply h 5 :=
  gJoin_supply_of_chiSupply (gDeep_chiSupply_five hsep HR)
```

The conclusion is `SqClassClearingSupply h 5` on the nose, not a variant and not a
`χ`-carrying cousin.  `gJoin_supply_of_chiSupply` (`GradedUniformJoin.lean:218`) is the honest
forgetful step: `GJoinChiSupply h k` is `SqClassClearingSupply h k` plus `∀ i, chiSq h (a i) = 1`
and the proof drops that conjunct and nothing else.  The two hypotheses are both real and both
open (`GJoinSeparationAll h` is a theorem since `gExt_separationAll`, so in effect only
`GTowerKnobRealizable h` is carried; the note's headline table states both, correctly).  No
near miss.

### 1.6  Check (d): the `Mpc` marking match at rows 4 and 5, CONFIRMED

`docs/dyadic/w79-mpc-note.md` §4, verbatim:

> the committed producers are `Instances.Sqrt10.*` and `Instances.SqrtNeg10.*` [...] which
> consume **`mpcNu α r p`** as their `ν_P`.  That is the same marking this lane's branch datum
> installs in `GenAsmBranch.nuP`, so the two halves compose at those rows without a
> translation step.

Checked end to end.  The producer installs `nuP := mpcNu α r pp hα1`
(`MpcCertificate.lean:415`), instantiated at `α = 2`, `r = 1`, `pp = p false 1` resp.
`p true 1` (`:539`, `:547`).  `p ε r = epsVal ε * 2 ^ (r - 1)` (`Parameters.lean:462`) with
`epsVal false = 0` and `epsVal true = 1` by `rfl` (`:503-504`), so `p false 1 = 0` and
`p true 1 = 1` definitionally.  The candidate side uses `mpcNu 2 1 0 alpha_valid`
(`Sqrt10.lean:153`) and `mpcNu 2 1 1 alpha_valid` (`SqrtNeg10.lean:113`).  Same marking, same
arguments.

The carrier types also agree, which the note asserts and does not cite: `Sqrt10.core := DM 2 0`
(`Sqrt10.lean:127`) and `genAsm_core_sqrt{Ten,NegTen} : genAsmCore (.Mpc 2 1 ε .one 0) =
Instances.Sqrt{10,Neg10}.core := rfl` (`GeneralAssembly.lean:427`, `:435`).  So "compose without
a translation step" is checkable and checks out, though it is not itself a theorem anywhere and
nothing in the tree performs the composition.

---

## Ticket 2 (report-only): the candidate-`hdet` lane brief, dispatchable as W81

Refines `docs/dyadic/w79-house-note.md` §2.3.  Everything below is verified at this tree.

### 2.1  The target, exactly

```lean
def PilotDet (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) : Prop :=
  AffineDeterminantCertificate (pilotGamma q) 2 q pilotP pilotNuP (standardNumerics 2)
    (tameOfSpec 2 q pilotW (pilotTameSpec hq0 hqe)) (pilotPro2 hq0 hqe)
    (pilotCompat hq0 hqe) (scalarActionZmodTwo ((pilotGamma q : Type)))
```

`Instances/SqrtNeg2.lean:886`, with `pilotGamma q := GammaR 2 q pilotW`.  Unfolded through
`CertificateMain.lean:328` it is two clauses concluding `GaussZResidueK … (SN.gaussUnram m)` and
its ramified twin.  Scope: **one file, one lane.**

### 2.2  The one genuine obligation, named precisely

A `SourceWordPhaseComparison` for the compact-`N` word at `α = 2, h = 0`.  Its type, verbatim,
`GQ2/Dyadic/Instances/GammaLDeterminantBridge.lean:56`:

```lean
structure SourceWordPhaseComparison
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} (DD : DescData D)
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    (rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M))
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    (W : Type) [Fintype W] (Q : W → ZMod 2) where
  phaseEquiv : (VCocycle DD rho ⧸ vCobRange DD rho) ≃ W
  phase_eq : ∀ x, QZeroBar DD rho htriv x = Q (phaseEquiv x)
```

Two fields.  At the pilot, `Gamma := pilotGamma q`, `W := V × V`, and `Q := plusFormD q q`,
which is the `Q`-parameter of `compactN_certificate` (`Word/Hessian.lean:662`) and is pinned to
the frozen word by `nCompact_word_eq_certQ` (`Certificates/N0.lean:950`).

**Its `ℚ₂` ancestor is not a structure.**  On the `ℚ₂` side the same step is a rewrite,
`QZeroBar_eq_Q0loc` (`GQ2/GaussZ/Local.lean:172`), applied at `FinalD.lean:224` and `:350`.  The
`Γ`-generic clone of that rewrite already exists: `QZeroBar_eq_Q0locG`
(`GQ2/Dyadic/GaussZ/FinalDK.lean:248`).  **A W81 lane must not try to reuse it.**  It needs
`TateDualityG Γ 2` (`GQ2/TateDuality.lean:208`: the invariant map `H²(G, μₙ) ≃ ℤ/n` plus three
perfectness statements), which is an arithmetic input the candidate word group `GammaR 2 q
pilotW` does not have and should not be given.  That is precisely why the candidate side needs
the word-phase route and the `K` side does not, and it is the load-bearing reason the L lane
invented the structure.  Stating it up front should save a lane a false start.

### 2.3  The no-Arf simplification, with the lemmas it rests on

`standardNumerics n` (`Recursion/Numerics.lean:84-85`):

```lean
  gaussUnram := fun m => (-1) ^ n * 2 ^ (n * m)
  gaussRam   := fun m => 2 ^ (n * m)
```

At `n = 2`, `(-1)^2 = 1`, so the two targets are the same integer and one proof discharges both
clauses, ignoring the `hunram`/`hram` split.  This is what makes the pilot cheaper than L, which
is at odd degree and therefore needed `LRamifiedSourceArfSupply` and a 633-line
`GammaLDeterminantRamifiedData.lean`.

**The two lemmas this rests on do not exist yet and are one line each.**  The tree has only the
`n = 1` pair, `standardNumerics_one_gaussUnram` (`Numerics.lean:109`) and
`standardNumerics_one_gaussRam` (`:116`), both explicitly flagged in their own docstrings as
"**not** `rfl`".  W81 owes the `n = 2` analogues:

```lean
theorem standardNumerics_two_gaussUnram (m : ℕ) : (standardNumerics 2).gaussUnram m = 2 ^ (2 * m)
theorem standardNumerics_two_gaussRam   (m : ℕ) : (standardNumerics 2).gaussRam   m = 2 ^ (2 * m)
```

and the corollary that the two agree.  `Recursion/Numerics.lean` is not sibling-owned.

**The `n = 2` fact covers all five frozen rows.**  `SelectedPresentation.degree`
(`SelectedWords.lean:54`) sends `.N0 _ h`, `.M0 _ h` and `.Mpc _ _ _ _ h` to `2 + 2*h`, and the
five frozen rows are `.N0 2 0`, `.M0 3 0`, `.M0 2 0`, `.Mpc 2 1 false .one 0`,
`.Mpc 2 1 true .one 0`, all at `h = 0`.  Only `.L h` is at odd degree `2h + 1`, and it is not
among them.

### 2.4  The acceptance test

**`hdet` discharges no field of `GenAsmRowResidual` and no field of `KSupply`.**  Naming this
exactly matters, because §2.1 of the wave-79 note is about a different obligation with a
similar name.  Precisely:

* `GenAsmRowResidual.determinant` (`GeneralAssembly.lean:294`) and `KSupply.determinant` are the
  **arithmetic-side** Gauss-`Z` clauses at `galKProfinite K`.  Those are supplied by
  `affineDeterminant_galK` (`GaussZ/FinalDK.lean:902`) and only need wiring, which a sibling has
  already taken this wave (§3.1).
* `PilotDet` is the **candidate-side** clause at `pilotGamma q`.  It discharges
  `ResidualSqrtNegTwo.hdet` (`Main.lean:381`), and through
  `sqrtNegTwoWordCertificate` (`Instances/SqrtNeg2.lean:898`, consumed as `determinant := hdet`
  at `:915`) it feeds `GenAsmRowResidual.cand` at the `N0 2 0` row, which is a whole
  `WordCertificate` and has three further binders (`hsimp`, `hsplit`, `hZcount`) that this lane
  does not touch.

So the acceptance test for W81 is: **`ResidualSqrtNegTwo` loses its `hdet` field**, and the
producer `Main.lean:742-746` loses its `hdet` argument.  Binder sites to update:
`Main.lean:381`, `:743`, `Instances/SqrtNeg2.lean:898`, `:1054`, `Instances/Fields.lean:723`.
The four `M` rows spell the same obligation inline (`Main.lean:414`, `:458`, `:503`, `:548`) and
follow near-free, because `compactM_P1_certificate` **is** `compactN_certificate`
(`Word/Hessian.lean:677-681`, the body is one application).

### 2.5  Sizing, unchanged from wave 79 and re-checked

Six pieces of `GammaLDeterminantBridge.lean` port verbatim (`:56`, `:68`, `:88`, `:107`,
`:124`, `:159`); two retype (`:232`, `:296`).  `GQ2/GaussZ/**` and `GQ2/Dyadic/GaussZ/**` carry
no `native_decide`, no `maxHeartbeats`, no `sorry`, no `axiom`.  Estimate stands: one file,
~15-25 declarations, ~550-750 lines, 1 to 1.5 waves, against L's 2646 lines for the same
target.  The two CB-DET traps to broadcast are unchanged (`ContinuousSMul ↥U (MuN 2)`
instance-path failure, and the `ProfiniteGrp`-bundled-topology poisoning that `boundaryMapSub`
firewalls, `FinalDK.lean:888`, `:930-940`).

---

## Ticket 3 (report-only): the W81 queue

**Sibling readings below are from unmerged branches at the hashes given.  Re-read at merge
time; none of it is a tree fact.**

### 3.1  What each sibling leaves, per outcome

**`claude/w80-xfree` at `b731f241`** (1 commit, `SqCore/GradedXFree.lean`, 150 lines, prefix
`gXf`).  Has the invariant and its two structural facts: `gXfSpan h := gTowerFar h ⊔ γ₂` (a
subgroup, so preservation is `Subgroup.mul_mem`), `gXf_free_mul_gamma` at any `k ≥ 2`, and
`gXf_bridgeTuple_free` as the class-three base.

* *If it lands with the recursion threaded*: `GTowerKnobRealizable` can be weakened by the
  clause and the far-slot change of basis becomes triangular, which is the only known repair of
  wave 79's quantifier finding.  W81 then owes the extraction proper on `gExt_frame_move`.
* *If it lands with the invariant only*: still worth having, but the seven re-proofs of §1.2
  are the whole remaining cost and W81 should be dispatched with that list, not with the extract
  note's one-lemma sentence.
* *Risk to flag*: the note's "preserved by `gTower_clear_step`" invites patching the superseded
  pair.  §1.2 has the correct target list.

**`claude/w80-uniform` at `5f0ec1e1`** (1 commit, module opened only).  Target is the uniform
generation record, Labute's Lemma 3 shadow at every weight.

* *If it lands*: it closes `GDeepKillAt h k` for all `k` through the T1/T2 induction already in
  `GradedDepthThree.lean`, and the odd route reduces to separation (a theorem) plus extraction.
  That is the single largest item on the graded side.
* *If it does not*: the per-level fallback is rung 4, which needs a level-6 generation record
  that does not exist in the tree (level 4 has three families, `cfourCmp_zLayer_le_gens`; level 5
  six, `cfiveSpan_zLayer_le_gens`; level 6 nothing).  W81 should NOT queue "the depth-4 base":
  `gDeep_not_layerReach` kills the layer statement at every depth, so only the kill ladder is
  live.

**`claude/w80-rowdata` at `8712e942`** (4 commits, `Instances/MpcRowData.lean`, 472 lines,
prefix `mpcRow`; it advanced between the §1.0 reading and this one, which is itself the
staleness lesson).  Three things, and the second was not on any queue:

* `mpcRow_level_le_one_quadField` and the two field instances: `B.r ≤ 1` at both procyclic
  quadratic fields, from `2 = u·π²` at a ramified quadratic field.  That is **half** of the
  `B.r = 1` conjunct of `MpcRowData_sqrt{Ten,NegTen}`; the reverse inequality and the three
  residues remain.
* `mpcRow_determinant_of_bridge`, `mpcRow_kSupply_of_counting`,
  `mpcRow_genAsmRowResidual_of_counting`: **the wiring of `affineDeterminant_galK` into
  `KSupply.determinant` and `GenAsmRowResidual.determinant`.**  This is critical-path item 5 as
  corrected by wave 79 §2.1, and it was explicitly recorded there as "half a wave and which no
  lane has been asked for".  If it merges, **item 5 closes** and the only remaining Gauss-`Z`
  obligation in the campaign is the candidate side, i.e. Ticket 2.
* A fourth commit, `8712e942`, takes the `ε = false` reduction that `w79-mpc-note.md` §3 named
  as "available but not taken": the `D̄` congruence free at `p = 0`, which would drop
  `MpcRowData_sqrtTen` from three clauses to two.  Read at the hash only; not audited here.

### 3.2  The odd-route endgame checklist, if both critical lanes land

Assume `claude/w80-uniform` closes `GDeepKillAt h k` for all `k ≥ 2` and `claude/w80-xfree`
delivers a clause under which `GTowerKnobRealizable h` is provable.  What stands between the
tree and `SqLamMarkTransitivity h` is then exactly:

1. `GJoinSeparationAll h` - **already a theorem**, `gExt_separationAll` (unconditional, every
   `h`, every `k`, every marking).  Nothing owed.
2. `GDeepKillAt h k` for `k ≥ 2` - rungs 2 and 3 are theorems (`gDeep_killAt_two`,
   `gDeep_killAt_three`); the uniform lane owes `k ≥ 4`.
3. `GTowerKnobRealizable h`, or its x₁-free weakening - the xfree lane, plus the seven re-proofs
   of §1.2 to make the weakening consumable.
4. `gDeep_defectVanishing_of_kills` then `gDeep_markTransitivity_of_kills`
   (`GradedDepthThree.lean:964`) - **already theorems**, and they are the endpoint composite.
   `gJoin_markTransitivity_of_vanishing` routes through `limFinal_markTransitivity`
   (`GradedLimit.lean:321`), which consumes `∀ k, SqClassClearingSupply h k`.

So the endgame is items 2 and 3, and nothing else.  Item 1 is closed and item 4 is closed.

**Behind it, what the odd side discharges: NO field of `GenAsmRowResidual`.**  This is worth
stating flatly because the phrasing "the odd route's residual" invites the opposite reading.
`SqLamMarkTransitivity h` feeds `genAsm_oddResidual_gives_mix` (`GeneralAssembly.lean:613`),
which produces `SqHandleMixFixesCore h c`, which is the `hMix` binder of
`genAsm_branch_of_oddSq` (`:621`) and `genAsm_branch_of_oddSq_canonical` (`:650`).  Those
produce a **branch datum**, `∃ G : GenAsmBranch K B, G.pres = .L h`.  That is the SELECTOR half.
What remains at the `L` row after `SqLamMarkTransitivity h` is:

* selector side: the degree pin, the oriented equivalence `D_sq h ≃ G_K(2)`, and the two `ν`
  normalizations at `σ` and `x₀` (the marking binders are discharged at the canonical `lNu h`);
* residual side: all four `GenAsmRowResidual` fields, untouched.  And the `cand` field is worse
  at `L` than anywhere else: `GeneralAssembly.lean:279`'s table row records **no producer over
  `D_sq h` at any parameters** for the `L` row, where `M0` has one at free `(α, h)` and `N0` and
  `Mpc` have one at fixed parameters.

### 3.3  The flagship scoreboard

**Selector side, five frozen quadratic rows** (tree facts at `4f30776b`):

| row | pres | branch datum | carried `Prop` |
| --- | --- | --- | --- |
| `ℚ₂(√−2)` | `N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | none |
| `ℚ₂(√2)` | `M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | none |
| `ℚ₂(√5)` | `M0 2 0` | `fieldFive_genAsmBranch_sqrtFive` | none |
| `ℚ₂(√10)` | `Mpc 2 1 false .one 0` | `mpcCert_genAsmBranch_sqrtTen` | `MpcRowData_sqrtTen` |
| `ℚ₂(√−10)` | `Mpc 2 1 true .one 0` | `mpcCert_genAsmBranch_sqrtNegTen` | `MpcRowData_sqrtNegTen` |

Three rows unconditional, two carrying one self-contained arithmetic `Prop` each.  Both `Prop`s
unfold to `B.r = 1 ∧ MpcMarkedData 2 1 (p ε 1) (ν_ur ∘ e)` (`MpcCertificate.lean:525`, `:530`),
i.e. the level plus three congruences at `C̄₀`, `D̄`, `B̄`.  Wave 79 §4.2 asked a W80 lane to check
what they unfold to; done, and `claude/w80-rowdata` is attacking the level half.

**Graded side.**  Layer route dead at every depth and every marking.  Separation is a theorem.
Per-class supply is a theorem through class 5 (`gAbs_supply_four`, `gDeep_supply_five`),
conditional on `GTowerKnobRealizable h` alone.  Residual starts at class 6, or at the kill
ladder if the uniform lane lands.

**Record side**, `w74-critical-path.md`'s eight items: item 5 is not open (wave 79 §2.1) and is
being wired this wave (§3.1); `hdet` is Ticket 2 and dispatchable; items 3, 4, 6, 8 unchanged
and unowned.

### 3.4  The owner items

* **The plan-A6 freeze on `GQ2/Roe/*`.**  Still open, carried from round 11 through six
  successive rounds.  `git diff --name-only 4f30776b..HEAD -- GQ2/Roe/` returns zero paths from
  this lane.  **Now the only owner item with no motion in six rounds.**
* **The 100-character question.**  Still no policy.  This lane held to 100 and added none: every
  line added here is under 100 characters measured in characters, not bytes, which is the
  measurement that matters given how much unicode the graded files carry.  (A byte-based check
  reports one false positive at 105 on a line containing `⁅⁅x₁,σ⁆,x₁⁆`.  If a policy is ever
  written, it should say which.)
* **The pilot-record call.**  Sharpened by Ticket 2: the acceptance test is now stated as a
  concrete edit to `ResidualSqrtNegTwo` (drop `hdet`) rather than as a `Prop` to be proved
  somewhere, and the arithmetic half of the same rung is being closed by a sibling this wave.
  After `hdet`, `ResidualSqrtNegTwo` carries three candidate-side binders, not four.
* **Registration.**  `GQ2/Dyadic/Instances/FieldSqrtFiveUnramified.lean` was registered at the
  wave-79 merge; `GradedDepthThree.lean` and `GradedExtraction.lean` likewise (`be9a40fd`,
  `293c3998`).  Nothing outstanding from wave 79.  Three new modules will need it at the wave-80
  merge.
* **Standing-checklist clause, from §1.1**: *a marker on a section header does not mark the
  declarations in the section.*  Grep the subject name; it is one command and it has now caught
  a miss in three consecutive rounds.

---

## Verification record

* `scripts/mirror.sh sweep`: 5923 artifacts into the lane mirror, exit 0.
* `scripts/mirror.sh check` after the edits, all `OK`, zero errors, zero warnings:
  `GradedBaseDecide.lean`, `GradedAbsorption.lean`, `GradedUniformTower.lean`,
  `GradedDepthThree.lean`, `GradedExtraction.lean`.
* No `lake` command was run.  No `sorry`, no axiom, no `native_decide`, no `maxHeartbeats`, no
  `maxRecDepth` added.  No statement changed: the diff is docstrings and module prose only.
* No em dashes.  No line over 100 characters.
* `GQ2.lean` untouched.  `GQ2/Roe/*` untouched.  The three sibling-owned paths untouched.

## Files touched

* `GQ2/Dyadic/SqCore/GradedBaseDecide.lean` - three markers (the `GDecideBaseThree` definition,
  `gDecide_layerReach_of_baseAt`, `gDecide_tower_of_baseThree`).
* `GQ2/Dyadic/SqCore/GradedAbsorption.lean` - four markers (§8 header and the three
  `_of_baseThree` composites).
* `GQ2/Dyadic/SqCore/GradedUniformTower.lean` - one marker on the `GTowerLayerReach` definition,
  naming the seven theorems it makes vacuous and the five statements it does not touch.
* `GQ2/Dyadic/SqCore/GradedExtraction.lean` - three markers (the module docstring's
  unconditionality sentence, and the two `_of_baseThree` docstrings the merge marker missed).
* `GQ2/Dyadic/SqCore/GradedDepthThree.lean` - two scope corrections (`gDeep_layer_wide`,
  `gDeep_xOne_tower_dvd`).
* `docs/dyadic/w80-house-note.md` - this report.
