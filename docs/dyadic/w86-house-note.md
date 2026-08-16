# W86-HOUSE lane note (watch round 23)

Standing verification lane. Base `f0de6ad5`, `dyadic`'s tip at lane start. Mirror swept at start
(6018 artifacts). Scoreboard run before the round, after each stage of the tool fix, and at
close; all four captured. Six commits: one tooling change in `scripts/scoreboard.sh`, the rest
comment-only in `GQ2/` plus frozen-note annotations. Every edited Lean module re-elaborates green
against the mirror: `Instances/CanonicalRecords.lean`, `Instances/MpcPairings.lean`,
`Instances/SqrtNeg2.lean`, `Instances/MpcWord.lean`, `Instances/MpcBuild.lean`,
`Instances/RecordBlocks.lean`, `SqCore/GradedRowMove.lean`. `GQ2.lean` and `GQ2/Roe/*` untouched,
checked by `git diff f0de6ad5 HEAD` on both paths (empty).

**⚠ BASE STALENESS AT CLOSE.** `dyadic` advanced to `0a479c6e` between this lane's last commit
and its close, merging two siblings, W86-PHASE (`Instances/WordPhase.lean`) and W86-LADDER5
(`Instances/MpcLadder.lean`). Both are files this lane was told not to touch, and it did not.
Every finding below was re-checked against `0a479c6e` and, at the last, against `aa31e767`; §0 records what moved. Nothing in this
note is stated as of the merged tree except where §0 says so.

**The round's headline is that the blind spot fired a THIRD time, and the fix is now structural.**
Ticket 1's change to the scoreboard exposed it in the act: on wave 85's own three landings the
board was undercounting four producer sets at once, the worst by a factor of 2.5. And on the very
next merge the fix earned itself: **neither wave-86 sibling registered its module** (§0.1).
Second in severity: the tree states a refutation route for `MpcPivShift 2` that it does not have.
This round found it in two places in `Instances/MpcBuild.lean`; by close it had propagated into a
third module as a headline (§0.2) and into a fourth site written during this lane's close (§0.4).

---

## 0 What the mid-round merge changed

Two siblings merged at `0a479c6e` after this lane's last code commit. Both bear on findings
below, one confirming and one superseding.

### 0.1 HIGH, NEW: neither wave-86 module is registered in `GQ2.lean`

`git diff f0de6ad5 0a479c6e -- GQ2.lean` is **empty**, and nothing else in that range imports the
new files. So `GQ2/Dyadic/Instances/MpcLadder.lean` (773 lines) and
`GQ2/Dyadic/Instances/WordPhase.lean` (1033 lines) are OUTSIDE `import GQ2`'s transitive closure:
invisible to every consumer, to `Main.lean`, to the umbrella build, and to this board's producer
scans. 2171 lines of wave-86 mathematics that no `import GQ2` consumer can reach.

This is the first live test of Ticket 1's registration scan and it fires correctly: the board run
on the merged tree will print them under `OUTSIDE the umbrella`, next to `GQ2/AxiomLedger.lean`
which is outside by necessity. Note the shape of the campaign's learning curve here: wave 85's
recorded lesson was "add the SCOREBOARD ROW in the same wave", the narrower version of the real
lesson, and both wave-86 lanes missed the wider one. With the scan in place the board now says so
without anyone remembering to look.

**Fix: two `import` lines in `GQ2.lean`.** Owner's, since `GQ2.lean` is not this lane's to edit.

### 0.2 §3.1 is CONFIRMED and has propagated, not superseded

W86-LADDER5's headline is "the M6 engine is an iff at every class", which sounded like it might
supply the missing direction. It does not. `mpcLad_eq_empty_of_no_supply` is titled
**"⭐⭐ THE REFUTATION ROUTE, NOW REACHABLE BY THE ENGINE"** and closes "which is the shape wave 84
named as the only admissible negative claim". The theorem is exactly right, concluding
`mpcWordSet (j+2) = ∅`; the headline inherits wave 85's inversion, since an empty rung refutes
the ANSATZ and not `MpcPivShift 2`. Checked on the merged tree: `MpcLadder.lean` mentions
`MpcPivShift` three times, of which one is a theorem, `mpcLad_shift_of_exists_supply`, in the
sufficiency direction. There is still no `MpcPivShift 2 → _` anywhere, so there is still no
exhaustiveness of the ansatz among the markings of `mpcOrb_shift_iff_marking`, so there is still
no refutation route. Three modules now say otherwise. Recorded at `MpcBuild.lean` with the
pointer; the `MpcLadder.lean` site is a sibling's and is left for its owner.

### 0.3 §3.6 is PART-SUPERSEDED, and the annotation was amended before close

`mpcLad_nonempty_iff` makes the rung an iff: a class-`(j+2)` solution exists exactly when SOME
class-`(j+1)` solution has one-step supply, the forward direction being the identity move on the
solution itself. So the engine IS complete over rungs, and a supply failure proved over the whole
class-`(j+1)` solution set does empty the rung. The caveat I carried to `mpcBld_step` is
therefore correct only at a SINGLE quadruple from `0a479c6e` onward; the annotation was rewritten
to say so and to point at `mpcLad_nonempty_iff`, rather than left to go stale on the merge. This
is the one place in this round where a wave-85 gap I recorded was closed by a wave-86 sibling.

### 0.4 A FOURTH site of the inversion, added by `aa31e767` itself, and one merge conflict

`dyadic` advanced a second time during this lane's close, to `aa31e767`, "annotate the wave-85
sites superseded by W86-PHASE and W86-LADDER5". It annotates two of the same files this lane
annotated, and its `mpcBld_shift_of_full_supply` block says
`mpcLad_eq_empty_of_no_supply` "gives the refutation route this paragraph says does not exist".

That block is right about the premise it corrects and repeats the inversion in the same
sentence. It is right that the caution's premise is false as written: `mpcWordSet` is antitone, a
class-`(j+2)` solution IS a class-`(j+1)` solution, and it is the identity move from itself, so
"need not be a `λ_j`-move away from one" does not hold. It is wrong that what results is a
refutation ROUTE: what `mpcLad_eq_empty_of_no_supply` concludes is `mpcWordSet (j+2) = ∅`, and
the step from there to `¬ MpcPivShift 2` is the missing one (§0.2, §3.1). So the count is four
sites across three modules, and the newest was written after the correction.

**The merge conflict, characterised.** `git merge-tree HEAD aa31e767` conflicts in exactly one
file, `GQ2/Dyadic/Instances/MpcBuild.lean`; `Instances/RecordBlocks.lean` auto-merges (their
hunks are at §4 and §5, this lane's at `recBl_mCand_stokes`). The conflict is at
`mpcBld_shift_of_full_supply`'s docstring, where both sides append a block after the same
sentence.

**Resolution: keep both blocks, `aa31e767`'s first and this lane's second**, because they correct
different halves of the same paragraph and this lane's is the narrower claim: theirs corrects the
premise (antitonicity, identity move), this lane's corrects the conclusion (an empty rung refutes
the ansatz, not `MpcPivShift 2`). Taking either alone leaves the paragraph half wrong, and taking
them in the other order leaves the file asserting the refutation route and then denying it. One
sentence in `aa31e767`'s block should also lose the words "the refutation route this paragraph
says does not exist" in favour of "the empty rung this paragraph names", which is what its own
theorem gives.

### 0.5 What did not move

`§3.2` (`mpcBld_shift_of_bracket_supply`'s over-strong hypothesis) stands: `MpcLadder.lean` adds
`mpcLad_shift_of_exists_supply`, a strictly weaker ask than either wave-85 form, but it does not
restate the wave-85 theorem, so the statement-versus-headline gap at that declaration is
unchanged. Owner item 9 stands, and is now arguably better served by deprecating the theorem in
favour of `mpcLad_shift_of_exists_supply` than by weakening it. Everything in §1, §2, §3.3 to
§3.5 and §3.7 is untouched by the merge; §4's ladder table is superseded on the `M6` side only in
that the sharp form is now `mpcLad_shift_of_exists_supply`, at the same class five.

---

## 1 Ticket 1: the scoreboard structural fix

### 1.1 What changed

The probe now does `import GQ2` and nothing else, and the registration check is folded into the
same file. Three consequences, all measured.

**(a) The blind spot is gone as a mechanism, and it had fired again.** The board's `prod` rows
scan the environment; while the probe imported the ROWS' modules, every producer count was a
function of which modules the rows happened to reach. Re-running with the umbrella import, on the
same tree, at the same commit:

| target | board printed | true | what was invisible |
| --- | --- | --- | --- |
| `MpcPivShift` | 4 | **10** | six `Instances.MpcBld.*` producers |
| `GClearModelMove` | 4 | **8** | four `SqCore.gRow_*` producers |
| `SqNuOrientedClearAtUnitPivot` | 6 | **8** | `gRow_clearing_of_forall_class{,_four}` |
| `SqMarkedForwardSupply` | 16 | **17** | `gRow_supply_of_forall_class` |

Wave 84 patched the first firing with a row; wave 85 patched the second with four rows and one
new `prod` row; the third firing happened anyway, because the patch does not generalise and wave
85 landed three more modules. No row of the current table names anything in
`Instances/MpcBuild.lean` or `SqCore/GradedRowMove.lean`, and their producers are now counted.
That is the ticket's verification condition, met without a per-row declaration list.

**(b) It is FASTER, not slower.** The ticket anticipated a cost. There is none, because the
registration probe already paid the umbrella import and is now the same file:

| | probe A | probe B | wall clock |
| --- | --- | --- | --- |
| before | 26 row modules | `import GQ2` | **101.6s** |
| after | one probe, `import GQ2` | (merged) | **52.0s** |

Subsequent runs at 30.3s and 28.7s with a warm mirror. The producer folds over the full umbrella
environment cost nothing measurable next to the import that was already being paid twice.

**(c) The registration check now scans every module on disk, not the rows'.** This was necessary
to make the new blind-spot wording true. A scan seeded from the rows cannot catch a module no row
reaches, which is exactly the case it exists for. It now enumerates `GQ2/**/*.lean` from the
filesystem (963 modules) and checks each against `import GQ2`'s transitive closure. Emitting one
Lean statement per module blows the elaborator's heartbeat limit at this repository's size, which
is how I wrote it first; it is one string-membership pass instead, and the cost is unmeasurable.

**The result: exactly one module under `GQ2/` is outside the umbrella, `GQ2/AxiomLedger.lean`.**
That one cannot be registered, because it does `import GQ2` itself and registering it would be a
cycle; `scripts/check_ledger.sh` exists for precisely that reason. The board derives the reason by
reading the file rather than asserting it, so the line stays honest if the situation changes.

**(d) A MISSING row now prints whether its module is outside the umbrella.** The one real cost of
the change is that a declaration outside the umbrella reports MISSING where it used to report
EXISTS. That is the correct reading, since no consumer can use it either, but it is a new way to
be misread, so the row says which.

The blind-spot entry now reads "producers in modules OUTSIDE THE UMBRELLA, and only those", with
the history kept and the lesson replaced: a row is still how a NAMED declaration gets on the
board; it is no longer what makes a module's producers countable.

### 1.2 One defect this fix does not cover, found while measuring

The `## OWNER ITEMS` section prints `numbered items in it 0`. It greps the latest house note for
a `^#+ +Owner items` heading and counts `^[0-9]+\.` lines under it; `w85-house-note.md` states its
nine items in a bolded sentence inside §3 rather than under a heading, so the count came out zero
against a true nine, and has done for a wave. Not fixed in the script, because the fix that
matters is on the note side and this note takes it: the "Owner items" section below is a heading of
that shape with a numbered list, so the next run reads it. Worth knowing that this line is a heading-shape check,
not an inventory.

---

## 2 Ticket 2: the stale annotations

### 2(a) HIGH: `CanonicalRecords.lean` reading 3, and reading 2 as well

The ticket named reading 3. Reading 2 turned out to be stale on the same axis and by the same
wave, so both are superseded.

**Reading 3.** The `⚠⚠` W84-HOUSE block saying "`ℚ₂(√−10)` has no tied statement at this tree" is
false since `8c0aab35`, which added `∧ HEq G.nuP (mpcNu 2 1 (p true 1) _)` to
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift`'s conclusion and deleted the `Exists.imp`. Marked
`⚠ SUPERSEDED` in place per the file's convention, with a W86-HOUSE block as of `f0de6ad5`.
Reading 3 as originally written is correct again.

**Reading 2**, not in the ticket: its W85-HOUSE block says the honest uniformity claim is SUCCESS
AT ONE ROW IS SUCCESS AT THREE, because `MProcyclicExact` has no `exactLiftingRN_unconditional`,
and names that as the wave-85 ticket. It landed, in the same wave, as
`RecordBlocks.recBl_mpc_exactLiftingRN`. The count goes back to **four**, with a different caveat
from the old one (§2(d) below).

### 2(b) MEDIUM: `MpcPairings.lean:72`

Verified stale and superseded. Precisely: "`RamifiedNormalPairingSeparates` is not here" is still
literally true, the theorem being in another file; what is superseded is the obstruction
paragraph, which reads as a statement of what is open. It diagnosed correctly ("a fully general
commutator law is needed first", with the eight-term centre value displayed), that law was built
the same day as `MpcRamifiedPairing.heisCommR_general`, and
`MpcRamifiedRow.ramifiedNormalPairingSeparates` has been a theorem for nine waves, binding
`1 ≤ alpha` and nothing else, for every display. Annotated with the pointer and with what remains
genuinely conditional there, which is the display package and not the pairing.

### 2(c) MEDIUM: `SqrtNeg2.lean:893`, partly stale as the ticket said, and I can say which part

Three claims in one ⚠ paragraph; two are stale and one is exact.

* "the Hessian ⇒ `GaussZResidueK` bridge does not [exist]" is **stale**:
  `GammaLDeterminantBridge.gaussZResidueK_of_wordPhase` is that bridge and both candidate-side
  determinant producers run on it.
* "no candidate-side supplier **in the repository**" **over-scopes**. A producer scan for
  `AffineDeterminantCertificate` returns 17, of which two are candidate-side at a `Γ_R` carrier:
  `LSquare.affineDeterminantCertificate_of_wordPhaseSupply` and wave 85's
  `recBl_mCand_determinant_of_wordPhaseSupply`. Neither DISCHARGES the two Gauss-`Z` clauses,
  both trade them for a word-phase supply, so the paragraph's spirit survives; its letter denies
  their existence.
* The claim **at this row is exact**. There is no `recBl_nCand_determinant_*` and no other
  producer at `nCompactW`, so `PilotDet` and the `genCertN` spelling's `determinant` clause are
  both unsupplied. Annotated as scoped to `nCompactW`, `mpcW`, `npcW`.

### 2(d) HIGH: the "class four" sweep, six definitely-stale sites in two clusters

`mpcBld_nonempty_four` moves the `M6` residue to class five. Two independent "class four" stories
run in this campaign and must not be conflated: the `Mpc`/`MpcPivShift`/`mpcWordSet` story, which
moved, and the graded `SqCore` story (`gRowSet`, `gRow_nonempty_of_le_three`), which did not.
Everything I touched is in the first, or is a cross-reference from the second into the first.

**Cluster A, cross-references from the row-move story into the M6 story.** Three sites say the
row-move residue starts at class four, "the same threshold as the `M6` ladder". The body is
correct and untouched; the appositive is wrong. It was **already wrong when written**:
`Instances/MpcBuild.lean` merged into `dyadic` at `ee22161b`, before the rowmove branch merged at
`ac2bca44`. Corrected at `SqCore/GradedRowMove.lean` module doc item 5 and at
`gRow_pair_of_forall_class_four`, and annotated in the frozen `docs/dyadic/w85-rowmove-note.md`.
The two ladders are one rung apart, and that is now the interesting comparison.

**Cluster B, `MpcWord.lean`'s own prose, four sites.** `MpcBuild` imports `MpcWord`, so this
module cannot name the theorem that supersedes it; a module-doc block does the work, plus three
local pointers. What each site needed differed and is recorded per site: §7's header and
`mpcWord_mem_three`'s docstring assert "the first class that can obstruct is class four", which is
now false; the module doc's "off-tree exact `𝔽₂` computation ... (class four is killed by
`s = t = commP D̄ B̄`)" is no longer off-tree at class four and still is at five and six; and
`mpcWord_shift_of_forall_class_four`'s "⭐ THE RESIDUE, EXACTLY" keeps its theorem, which is still
true and is what the sharp form is proved through, and loses only the superlative.

Also annotated: `docs/dyadic/w84-word-note.md` §9 item 2 ("Formalize class four") is DONE, with
exactly the witness it specified, which retroactively dates that note's three present-tense
class-four claims.

### 2(e) LOW: one site W84-HOUSE named as wrong and nobody ever corrected

`docs/dyadic/w83-records-note.md` §0 was one of three sites W84-HOUSE listed as asserting the
opposite of its finding. The other two were corrected; this one was not, so a reader following the
pointer landed on an unannotated site. It is now correct again by wave 85, but its reasoning never
was: "routes through site 5 and **therefore** does carry `mpcNu`" is the non-sequitur W84-HOUSE
identified. Annotated with that history rather than left to read as vindicated.

---

## 3 Ticket 3: watching round 23, ranked by severity

### 3.1 HIGH: `MpcBuild.lean` claims a refutation route for `MpcPivShift 2` that the tree does not have

Two sites, and the error is logical rather than factual, which is why it survived a lane note and
a merge.

`mpcBld_shift_of_bracket_supply`'s docstring: "Read contrapositively with wave 84's
`mpcWord_shift_of_forall_class`, a *proven empty* solution set at one class would refute `M6`."
That theorem is `(∀ k, (mpcWordSet k).Nonempty) → MpcPivShift 2`. Its contrapositive is
`¬ MpcPivShift 2 → ∃ k, mpcWordSet k = ∅`, which is the direction wave 84 states correctly and
which this sentence needs the **converse** of. Getting from an empty rung to a refutation requires
`MpcPivShift 2 → ∀ k, (mpcWordSet k).Nonempty`, i.e. that the ansatz is exhaustive among the
markings. The tree does not have it, and the shapes do not match:
`MpcOrbit.mpcOrb_shift_iff_marking` characterises `MpcPivShift 2` by an arbitrary four-letter
marking `(a, b, c, d)` with the four χ-values, the generation clause and the row shift, while
`mpcWordSet` fixes `(Ā·B̄⁻⁴·s, B̄·t, B̄²·C̄₀·m, D̄·n)` with corrections in `mpcWordFrat ⊓ ker χ_M`.
Nothing forces a marking into that shape.

The sentence IS sound on the other reading of "M6", the ansatz itself: a solution of the identity
lies in every `mpcWordSet k`, so an empty rung refutes the ansatz. W85-HOUSE §2.5 flagged that
"M6" has two readings and checked the CONTRAPOSITIVE sound in both, which it is; this is a
different sentence and is sound in one.

`mpcBld_shift_of_full_supply`'s closing sentence has the same clause ("the refutation route
remains wave 84's, a proven empty `mpcWordSet k`") attached to a caution that is otherwise exactly
right. Both corrected in place.

**The consequence worth carrying forward:** the tree has NO route to refuting `MpcPivShift 2`
through this ladder, only a route to refuting this ansatz, and the two are not known to be the
same question. `SqCore/GradedRowMove.lean` states the analogous claim in the correct direction, so
the two modules disagree; the row-move side is the one to copy.

### 3.2 HIGH: `mpcBld_shift_of_bracket_supply`'s hypothesis is stronger than its headline

Elaborated, `H` is `∀ j, 3 ≤ j → ∀ g ∈ λ_{j+1}, ∃ u v, ... g * ⁅Ā,u⁆ * ⁅C̄₀,v⁆ ∈ λ_{j+2}`: every
element of the layer must be clearable, which is surjectivity of the two-bracket map onto
`λ_{j+1}/λ_{j+2}`. The docstring advertises "the defect of a class-`(j+1)` solution can be
cleared", which is `mpcBld_shift_of_full_supply`'s hypothesis, quantified over
`p ∈ mpcWordSet (j+1)`. The proof consumes `H` only at the defect, so the gap is in the statement.

This is the misleading direction: a hypothesis is an ask, so an over-strong `H` makes the theorem
weaker than advertised, and a builder who can clear defects but not the whole layer would think
this theorem serves. It does not; `mpcBld_shift_of_full_supply` does, and says so at its own site.
Recorded at the theorem. **Owner item, one line of Lean:** weaken `H` to quantify over
`p ∈ mpcWordSet (j + 1)` and its relator membership, which the proof already instantiates it at.

### 3.3 MEDIUM: the tie's `HEq` conjunct verified against its consumers, and the fifth row assembles

The wave-85 m6build lane described an off-tree probe. Reproduced from scratch rather than trusted,
and it elaborates.

    canRec_rowResidual_of_tied (mpcPiv_genAsmBranch_sqrtNegTen_of_shift hshift B) F cand
      askExactLifting askStokes
      : ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0 ∧
          Nonempty (GenAsmRowResidual G F.T)

The shapes match exactly: `canRec_rowResidual_of_tied`'s first binder is
`∃ G, G.pres = row ∧ HEq G.nuP nu0` and the theorem now concludes in that shape, at
`nu0 := mpcNu 2 1 (p true 1) _`. Explicit binders are the four frozen rows' five (`B`, `F`,
`cand`, `askExactLifting`, `askStokes`) plus `MpcPivShift 2`.

**One correction to the m6build note's account.** It reports the axiom set as "exactly the four
frozen record blocks' set". Measured: `std-3 + hilbertSymbol_normCriterion_finiteDyadic,
peripheralCyclotomicAction, relativeStiefelWhitney_dyadic, tateDualityAt,
absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic`. That is the `√2`,
`√5` and `√10` rows' set exactly, and the `√−2` row's set **plus** `peripheralCyclotomicAction`;
the `√−2` row does not carry that pin. Three of the four, not four.

So what keeps the fifth row out of `CanonicalRecords` is now neither the tie nor the transport: it
is `MpcPivShift 2`, plus a `cand` and the two `ASK` blocks at that carrier. Recorded at the site.

### 3.4 MEDIUM: `gRow_pair_of_forall_class_four`'s binders, the near-miss check

The reduction is sound at every point the campaign has previously got this wrong.

* **Directedness is not inverted.** `gRowSet_antitone (hkk : k' ≤ k) : gRowSet h A B k ⊆ gRowSet h
  A B k'`, so higher `k` is a smaller set, and `max k k'` is the correct witness for a downward
  directed family.
* **The bounded half is a theorem, not a vacuity.** `gRow_nonempty_of_le_three` covers `k ≤ 3` on
  the unit locus, and `by_cases hk : 4 ≤ k` dispatches to it in the negative branch, so no bounded
  range of `k` makes the hypothesis vacuous or the criterion trivial.
* **Separation is used and not assumed away.** `lim_iInf_twoCentralSeries h` reduces the
  intersection over all `k` to `⊥`; there is no inverse-limit step.
* **`hAB` is load bearing in both halves**, not only in the `k ≤ 3` dispatch: `gRow_modTwoIndep
  hAB` is what keeps the corrected frame spanning `H_1`.

Two things the module says about it that its statement does not:

* the module doc's summary of `gRow_pair_of_forall_class` **drops the unit-locus binder**, which
  the declaration's own docstring carries. Corrected;
* "⭐ The residue, exactly" is sufficiency only; no converse `GRowPair h A B → ∀ k ≥ 4, ...` exists,
  and none is claimed in the body. Left alone: the campaign uses "residue exactly" for "this is
  all that is left to prove", and the body sentence is exact. Recorded here so a later lane does
  not read necessity into it.

Worth noting the asymmetry with the `M6` ladder, since §3.1 turns on it: the row-move side DOES
have a genuine converse, `gRow_pair_of_modelMove`, at the move level, so the pair target is
provably exactly as strong as the model move plus λ-preservation. The `M6` side has no converse at
any level below `mpcOrb_shift_iff_marking`, whose right-hand side is much wider than the ansatz.

### 3.5 MEDIUM: `recBl_minimalBlock_isEmpty_of_nilpotent` against "datumRho dead"

The claimed consequence holds, and is if anything understated.

`recBl_minimalBlock_isEmpty_of_nilpotent [Group.IsNilpotent Y] (L : Subgroup Y) : IsEmpty
(MinimalBlock L)` carries **no** finiteness: `[Finite Y]` is not auto-included, checked by
`#check`. So §2's "no nilpotent `Y` admits one, for any marked kernel `L`" is exact, and holds for
any nilpotent group whatever. `_of_isPGroup` does carry `[Finite Y]`, needed for `IsPGroup`.

The types line up with the refutation handle: `rowCl_mCand_isEmpty_boundaryLifts` binds
`{Blk : SectionSeven.MinimalBlock T.LY}` for `T : MarkedTarget H E Y`, so a refutation through
that theorem must exhibit a block, and over a nilpotent `Y` there is none to exhibit.

The `datumRho` half checked to the end, including the cross-namespace step the prose glides over.
`Base` and `datum` are global (`GQ2/CardH2GammaA.lean`), so `Base ⧸ datum.M` is one group shared
by every `datumRho` in the tree, `MCompact.datumRho` (`M0Exact.lean`) included; `datumQuot_sq` is
proved in `SqrtNeg2.lean` about that same global quotient. The composition elaborates at std-3:

    recBl_minimalBlock_isEmpty_of_sq SqrtNeg2.datumQuot_sq L
      : IsEmpty (SectionSeven.MinimalBlock L)   for L : Subgroup (Base ⧸ datum.M)

So `datumRho` is dead exactly as claimed. The module's own "a narrowing, not a discharge" is the
right reading and is stated.

### 3.6 MEDIUM: the increment engine's sufficiency caveat is at one site of four

Ticket 3(e). On the `M6` ladder the caveat is stated once, at `mpcBld_shift_of_full_supply`: a
class-`(j+2)` solution need not be a `λ_j`-move away from a class-`(j+1)` one, so a walk that
exhausts every increment at depth `j` has not shown the rung unreachable. It was **absent** at
`mpcBld_step`, which is the site a builder reaches first, and **contradicted** at
`mpcBld_shift_of_bracket_supply` (§3.1). Carried to `mpcBld_step`; the contradiction corrected.

`mpcBldIncr`'s "the *whole* effect of a `λ_j`-move on the four corrections" is completeness over
MOVES, which is proved and is a different statement from completeness over solutions. Distinguished
at the site.

On the row-move ladder there is no increment engine to caveat: `SqCore/GradedRowMove.lean` has no
`_incr_` declarations, its low rungs are outright theorems (`gRow_relWord_mem_two`,
`gRow_relWord_bare_mem_three`), and its contrapositive is stated in the correct direction.

### 3.7 LOW: headline against statement on the three new modules

`SqCore/GradedRowMove.lean`: core headlines check out. `gRow_relWord_mem_two` really is at every
marking with no unit locus; `gRow_nonempty_of_le_three` really carries it; the `_of_forall_class_four`
family really consumes only `k ≥ 4`; `gRow_supply_of_forall_class` and
`gRow_candidateEquiv_of_forall_class` land where advertised. Three items fixed or recorded: the
dropped unit-locus binder (§3.4); the **axiom hygiene paragraph omits a third set**, `gRow_pair_zero`
being a §7 declaration that prints std-3 + `{dyadicOrientation, peripheralCyclotomicAction}` rather
than std-3 or the seam's four (§9's pin list has it right; the summary skips it), corrected; and
"the committed class-two balance is subsumed one rung up", which compares `PivotCoreMoves`'
lower-central computation in `F/γ₃` with a two-central conclusion in `λ₃`. Since `γ₃ ⊆ λ₃` the Lean
conclusion sits at the coarser quotient and does not imply the prose finding; it is stronger in
another respect, needing no corrections. Left as a recorded item rather than edited, because the
docstring already names the metric difference and the right repair is a sentence its author should
choose.

`Instances/MpcBuild.lean`: §3.1, §3.2 and §3.6 above, plus two name slips in the module doc's
widened bullet, both corrected: `mpcBld_shift_of_forall_class_five` is the NARROW criterion (its
hypothesis is over `mpcWordSet`; the widened one is `mpcBld_wide_shift_of_forall_class_five`, over
`mpcBldSet`), and `mpcBld_wide_nonempty_four` does not exist, the declaration being
`mpcBld_wide_nonempty_of_le_four`. The widening's mathematics is right: `mpcWordSet k ⊆ mpcBldSet k`
(`mpcBld_wordSet_subset`), so the widened hypothesis is weaker and the widened criterion stronger.
Only "strictly more room at every rung" over-reads, the proved inclusion `mpcWordCorr ≤ mpcBldCorrW`
being non-strict. INFO: the §6 pin list is complete (48 declarations, 48 lines) but not in
declaration order, `mpcBld_incr_head` and `mpcBld_incr_pivot` being listed after `mpcBld_letC_corr_mem`.

`Instances/RecordBlocks.lean`: headlines check out, and the module handles the trap this ticket
flagged. Its §1 states the display-package caveat prominently and correctly, names `MpcDisplayFor η`
as the carrier, and adds that `1 ≤ r` is not free; `recBl_mpc_exactLiftingRN`'s elaborated signature
matches. One LOW corrected: `recBl_mCand_stokes`'s "unconditionally at `2 ≤ α`" also binds `q ≠ 0`
and `Even q`, as does `MCompact.uniformPushedHsimp` (`Even q`); nothing is owed at either frozen
`M0` row and §5 spells the three out, so the shorthand is a grep hazard rather than an error.
INFO: one `set_option linter.unusedVariables false in` at `recBlWordPhaseSupply`, declared and
justified in the module's own axiom-audit prose. No `maxHeartbeats` in any of the three modules.

---

## 4 Ticket 4: the endgame board

Read off the closing scoreboard, which is the corrected one, at tree `15af487a`.

**The odd route.** The chain is unchanged and every link is a theorem:
`GClearModelMove → SqNuOrientedClearAtUnitPivot → SqMarkedForwardSupply → GenAsmBranch .L h → the
general theorem`. What changed this round is visibility, not mathematics: the seam now shows **17**
producers, the clearing **8**, the row-plane move **8**.

Ladder status, the ticket's question. **Neither ladder's rungs have moved off wave 85's landing,
and the two are one rung apart:**

| ladder | low rungs proved | residue starts at | sharp form |
| --- | --- | --- | --- |
| row move (`gRowSet`) | `k ≤ 3` on the unit locus | **class four** | `gRow_clearing_of_forall_class_four` |
| `M6` (`mpcWordSet`) | `k ≤ 4` | **class five** | `mpcBld_shift_of_forall_class_five` |

The odd route's open item is the row-plane family `∀ (a, b)` on the unit locus,
`GClearModelMove h a b` at `h ≥ 1`. Its eight producers are four from wave 84
(`gClear_modelMove_one_zero` free, `gClear_modelMove_zero` at `h = 0` only riding B3c + B8, and
`_of_families` / `_of_ray` trading it for the two open one-parameter families) and four from wave
85 (`gRow_modelMove_of_forall_class{,_four}`, `gRow_modelMove_of_pair`,
`gRow_modelMove_of_ray_pairs`). Nothing at `h ≥ 1` moves rows unconditionally. The distance is one
per-class ladder at `k ≥ 4`.

**The record blocks per row.** Four rows, and after this round's check the residue is uniform
across all **four** again, not three, subject to the display package on the `Mpc` row:

| row | analytic residue |
| --- | --- |
| `M0 3 0`, `M0 2 0` | `exactLifting` = `askCStageVanishing` at `Γ_R`; `scalar` and `stokes` theorems; `determinant` = word-phase supply |
| `N0 2 0` | the same equivalence and `scalar`; `stokes` and `determinant` not transcribed |
| `Mpc 2 1 false 1 0` | the same equivalence, **new this wave**, given the display package |

Each of the four still carries `MarkedRecip`, `GenAsmFieldInputs`, `WordCertificate`,
`ExactLiftingSemantics` and `StokesDualityCertificate`. The `N0` twins of the wave-85 `stokes` and
`determinant` are the cheapest ticket on the board: three inputs exist
(`Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis`, `NCompact.uniformPushedHsimp`, and the
`M` proofs to transcribe), and it would put three of the four rows on one footing.

**The fifth row.** `ℚ₂(√−10)` is tied now (§3.3) and the transport accepts it. What it needs is
`MpcPivShift 2`, plus a `cand` and the two `ASK` blocks at `mpcW 2 1 (p true 1) 0`. The board shows
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift` carrying `MpcPivShift` and `MarkedRecip`, and the
unconditional sibling still untied, deliberately, at the transported marking.

**The even route.** One surviving point, unchanged since wave 74 and untouched by waves 84, 85 or
this round: `Hfam` (`EvenRouteFinalFamily{N,M} h K`), proved equivalent to the even classification
at that field by `hfamFinal_family{N,M}_iff_orientedEquiv`, so it can be neither refuted without
refuting the classification there nor discharged by soft means. Arithmetic form
`EvenFamParitySupply{N,M}`.

**Registration.** 963 modules under `GQ2/`; one outside the umbrella, `GQ2/AxiomLedger.lean`, which
cannot be inside it (§1.1).

---

## Owner items

**Nine standing, one discharged this wave, two opened.** None takeable by a comment-only lane; all
are statement changes or policy calls. Items 1 to 8 are the wave-84 list with its item 8 discharged
and renumbered, so the inherited count is EIGHT, not the nine carried since wave 83; items 9 and 10 are new this round.

1. **ASK restatement.** Restate the row records against `ExactLiftingSemanticsRN`, or prove
   `askCStageVanishing`. Unchanged, and `rowCl_rn_both_carriers_sqrtFive` still supports it at both
   carriers.
2. **Pilot spelling.** Unchanged. The concrete consumer list is W85-HOUSE §2.3; retiring it means
   dropping four fields from `Main.ResidualSqrtNegTwo` and re-proving `rowEquiv_sqrtNegTwo` off
   `genCertNWordCertificateCanonical`.
3. **The A6 freeze** (`GQ2/Roe/*`): **thirteen** review rounds without motion. `git diff f0de6ad5
   HEAD` on `GQ2/Roe/` and on `GQ2.lean` is empty for this lane, checked. The board's machine
   substitute: last commit `4341a1a3`, 2026-08-10, comment-only; **14** house notes added since.
4. **Line length.** Policy call still owed. Not re-measured this round.
5. **The forgotten marking.** Now **two** sites, not three: `genAsm_branch_of_evenN` and
   `genAsm_branch_of_evenM` (`GeneralAssembly.lean`, the free-`h` even producers, which is why the
   free-`h` shape lemmas of `CanonicalRecords` have no supplier at `h ≠ 0`). The `√−10` site was
   item 8 and is discharged.
6. **`askCStageVanishing`: fact or wrong ask?** Unchanged, and still the sharpest open item on the
   arithmetic side. Wave 85's §2 narrowing (no nilpotent target carries a refuting frame, §3.5) is
   a narrowing of the refutation route, not progress on the question.
7. **The `hclear` re-cut.** `GammaLOddDegreeBridgePivot`'s consumers take `hclear` and `hsupply`;
   since `oddFrame_supply` derives the supply from the clearing, they should take `hclear` alone.
   Unchanged.
8. **The two-idiom split on the `L` row.** The odd chain drops the marking while
   `LRowCand.lCandBranch` rebuilds the datum definitionally to get it back. A design question.
9. **NEW: weaken `mpcBld_shift_of_bracket_supply`'s hypothesis** to the per-solution form the
   docstring advertises and the proof uses (§3.2). One line of Lean, but a statement change.
   As of `0a479c6e` the better disposition may be to deprecate it in favour of
   `MpcLadder.mpcLad_shift_of_exists_supply`, which is weaker than either wave-85 form.
10. **NEW, at `0a479c6e`, and the cheapest on the list: register the two wave-86 modules.**
   `GQ2/Dyadic/Instances/MpcLadder.lean` and `GQ2/Dyadic/Instances/WordPhase.lean` are outside
   `import GQ2`'s closure (§0.1), so 2171 lines of wave-86 mathematics are invisible to every
   consumer. Two `import` lines in `GQ2.lean`, which no lane may edit.

**Discharged this wave:** wave-84 item 8, tie the `√−10` shift statement. Taken by W85-M6BUILD at
`8c0aab35` under an orchestrator edit grant, verified here end to end (§3.3).

**Not opened as owner items, recorded for a lane that wants them:** the two candidate additions
W85-HOUSE left standing (five `omit`s in `OddFrame.lean`; stating the joint-surjectivity-free
strengthening at `gClear_clearing_of_model`), and this round's §3.7 "subsumed one rung up" sentence.

---

## 6 What this lane did not do

No statement changed anywhere in `GQ2/`; every tree edit is a comment. `GQ2.lean` and `GQ2/Roe/*`
untouched, checked. The sibling-owned files `SqCore/GradedRowLadder.lean`,
`Instances/MpcLadder.lean` and `Instances/WordPhase.lean` were neither created nor touched; none
exists at this tree. No `lake` command was run; verification is `scripts/mirror.sh check` and
`scripts/scoreboard.sh` throughout, plus four off-tree probes in the scratchpad (the fifth-row
assembly, the `Mpc` equivalence, the `datumRho` block, and a producer scan for
`AffineDeterminantCertificate`), none of which is in the tree. Frozen lane notes were annotated
with dated supersession blocks rather than rewritten. `MpcPivShift 2`, `askCStageVanishing`, the
model moves and the `N0` Stokes and determinant twins were not attempted. The one behaviour change
outside the tree is `scripts/scoreboard.sh`, §1.
