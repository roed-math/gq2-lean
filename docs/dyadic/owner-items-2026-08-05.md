# Owner decision items — wave 37 (2026-08-05)

## Status at wave 67 (2026-08-11)

**Open, still yours (unchanged):** the standing items below.  Nothing new needs a decision.

**For orientation, the wave's two headlines.**  First: the inverse-limit step of the
`h >= 1` residual is now committed mathematics.  `SqLamMarkTransitivity h` is proved
EQUIVALENT to the family of per-class clearing statements (`GradedLimit.lean`, all std-3,
classes `k <= 2` discharged), so the campaign's last deep question is no longer "find the
pro-2 limit argument" but "prove the class-k graded step for k >= 3", which is exactly
where the instrumentation (containment identity, Fox-form identification, exact lattices,
census) is concentrated.  Second: `Q2(sqrt -2)` is closed UNCONDITIONALLY (the per-field
range identity is now a theorem there, the first computed cyclotomic range at a named even
field), `Q2(sqrt 2)` closes over one base reciprocity bundle, and the range identity lost
its ramification hypothesis entirely.  Final state after the docs pass `aed31eb8`: 4316
jobs green, census 11, zero sorries, capstones frozen.

## Status at wave 66 (2026-08-11)

**Open, still yours (unchanged):** the standing items below.  Nothing new needs a decision.

**For orientation, the wave's headline:** the even route is now closed as mathematics at
even degree.  The parity supply named at wave 65 is proved at EVERY even-degree field on
both branches (the odd route's parity pigeonhole was degree-agnostic all along), so Hfam is
a theorem there with no range or ramification binder, the even classification holds at
every even-degree ramified-i field over the reciprocity bundle, and Q2(sqrt -2) and
Q2(sqrt 2) are the first even fields ever closed (branch-pinned over the per-field range
identity `hrange`, which is local class field theory the campaign has always measured and
never computed in-tree; that computation is now the last even item with a route).  On the
h >= 1 side the census endgame closed: unconditional kills at all 67 points, horn 2 refuted
at the eighteen knob-free points, and the gauge proved unnecessary for the census.  The
wave-60/61 legality points were refuted rather than instantiated (wave 64's own unread
table already said so).  Final state after the docs pass `c3c62654`: 4314 jobs green,
census 11, zero sorries, capstones frozen.

## Status at wave 65 (2026-08-11)

**Open, still yours (unchanged):** the standing items below.  Nothing new needs a decision.

**For orientation, the wave's headline:** the ticket held for Fable through eleven waves is
settled, and the answer is structural.  `Hfam` is constructed outright on both model cores
(census-free), and at every real field it is proved EQUIVALENT to the even oriented
equivalence itself, so the even route's last carried supply was the classification one
station earlier.  The honest remaining content of the whole even route is one arithmetic
statement per branch, `EvenFamParitySupply` (mod-2 twisted-cocycle surjectivity, higher
Kummer theory), proved equivalent to the endpoint, with two attack routes named in
`docs/dyadic/w65-hfam-note.md`.  On the `h >= 1` side: class five is now the SHARP top
class at which the sigma separation forces a handle (class six refuted by mechanism); the
census criterion's horn 1 is closed with its recorded form corrected (the census verdict
now needs only achievability); the force lattice bounds are exact with a decidable
achievability test.  Final state `c98a85db`: 4310 jobs green, census 11, zero sorries,
capstones frozen.  The wave also retired all 25 audited commentary defects from wave 64
(comment-only edits, code proved byte-identical).

Six items surfaced during the wave. Item 1 is a genuine mathematical constraint on the
general-`K` program and needs a decision; items 2–6 are statement or documentation defects
with recommended fixes. Nothing here blocks the odd-degree L row, which is now unconditional
on the forward side.

## Status at wave 64 (2026-08-11)

**The four stubborn markings are closed.** They have been on this list since wave 61, when we
could only measure them. Wave 62 failed and diagnosed why; wave 63 showed the diagnosis was aimed
at the wrong object and removed the real obstacle; this wave discharged the one arithmetic
identity that was left. So a measurement we have carried for three waves is now a theorem, in both
of its halves. The lane checked the join three independent ways before claiming it, which I asked
for because a mistake there would have silently turned four conditional theorems into false
unconditional ones.

**A second long-standing question also closed, and in a better form than we asked for.** We wanted
to know whether the class-five separation needs a handle. It does, and the proof needs none of the
technical side conditions we expected to have to carry. The mechanism is clean enough to be worth
stating plainly: the response we care about is built out of nine lower rows of an underlying word,
and in the no-handle case that word is the relator itself, so all nine vanish at once. A
by-product is that we now have closed formulas for all fifteen rows of that word for the first
time, which will pay off again one class up.

**The verification lane had its best wave.** It resolved a question I had left explicitly open and
flagged as unresolved rather than guessed at, and the answer was the unwelcome one: a new witness
built last wave inherits the same weakness as the old one, because it reuses the same slot. A
second lane reached the same conclusion independently by a different route, so I am confident in
it. The same lane audited our lattice bounds and found two that are not as sharp as they could be
- and then did the analysis that actually matters, showing that neither is used anywhere to argue
that a possibility survives, so this is an opportunity rather than a defect.

**Twelve places where our own commentary overstated what we had proved.** Two of them were
licensing conclusions the proofs do not support, including one where the file's own contents
refute the sentence in its header. All twelve are fixed, in a separate pass that changed prose
only and proved mechanically that no theorem, proof or axiom line moved. I want to flag the
pattern rather than the instances: this is the second wave running in which the tree's commentary,
not its mathematics, was the thing that was wrong, and the failure is always the same shape - a
computation on a few cases described as a property of the general object.

**On models.** Opus only throughout, and the Fable-scoped ticket skipped rather than converted, as
you asked. `Hfam`, and with it the entire even route, is untouched by this wave as well.

Nothing here needs a decision from you. Items 1 and 6 below are unchanged and the d-1 question
stays parked.

## Status at wave 63 (2026-08-11)

**Two routes we had been carrying as open are now closed, and one of them was closed by finding
out that a thing we believed was simply not true.** Last wave I reported that the gamma-2 route
was closed in its parity form. I sent a lane to try the remaining form of it, phrased on
centrality rather than on parity. That form is not merely unprovable, it is false: at the very
point our committed exclusions are stated at, there is a legitimate dressing that kills the frame
outright. So the route is refuted by counterexample rather than left undecided, and we will not
return to it. Nothing we have published is affected, and the lane proved that rather than
asserting it.

**The correction is the part worth your attention.** Wave 62 reported that both of our committed
class-five witnesses were blind to the handle-block instrument. They are not. That claim came
from computing the instrument on two pairs of elements and then describing the result as a
property of the points; a third pair, never computed, is live at both of them. The four theorems
involved are all true as written, so nothing in the library is wrong, but a paragraph of
commentary was wrong and it had already sent one of this wave's four lanes off on a charter built
on it. I caught it when the lane that found it landed, relayed the correction to the affected
lane while it was still working, and had that lane's write-up reconciled before merging it. The
lane also left two small tools that make the whole class of claim safe to state in future.

**The four stubborn markings moved a long way, though they are still not proved.** For two waves
they have resisted, and last wave we diagnosed the resistance as the forcing needing to read a
lattice too finely for our language. That diagnosis turns out to have been about the wrong object:
the standard technique for bounding these lattices drags in a larger subgroup that is not actually
needed, and all three impossibility measurements were about that larger subgroup. Removing it
lands the exact bound at all four markings. What remains is one arithmetic identity, measured
exhaustively on the relevant set and reduced to bookkeeping with two routes written out. I expect
a later wave to finish it. The general tool that came out of this is likely to be worth more than
the four markings themselves.

**On models.** You asked for Opus only and for the Fable-scoped ticket to be skipped rather than
converted. It was skipped. `Hfam`, and with it the entire even route, is untouched by this wave
and still waiting.

Nothing here needs a decision from you. Items 1 and 6 below are unchanged, and the d-1 question
stays parked.

## Status at wave 62 (2026-08-10)

**The route I said last wave was cheap to widen is closed, and that is the wave's most useful
result.** I sent a lane to search for a binder point where three specific channels are even,
which would have widened the exclusion a full filtration step using theorems we already had.
There is no such point: the channel functional and the separation bit turn out to be the same
functional over the two-element field, so even channels force an even residue. That is now a
theorem rather than a failed search, so we will not spend another wave looking. A conditional
widening did land, covering half the achievable lattice.

**Two audits found their predecessors incomplete.** The migration onto the sharp stage-four line
was recorded last wave as covering two statements; it is fourteen, because a file that landed in
the same wave carried the same condition in twelve more places. And the mod-two candidate we
recorded as holding at none of 1650 markings now has its explanation: it implies the parity line,
so it could never have separated anything.

**One lane did not achieve its target and said so.** I sent it to prove the four markings that
separate two conditions, and it proved a related separation at a different witness that sits
outside the relevant family. The four are still measured, not proved. What it did do is diagnose
exactly why they resist, which tells the next attempt what will not work, and it verified the
four are real rather than a census artefact.

**A caveat on something I reported last wave.** The handle-count instrument is now an invariant
of the group rather than of a marking, which is a genuine generalisation. But the datum it
supplies is equivalent to the hypothesis it replaces, so it buys a reformulation rather than
strength, and no committed statement can drop anything because of it. I would rather correct
that now than have it read as more than it is.

Final state `10201fa4`: 4293 jobs green, census 11, zero sorries, capstones frozen, all gates
passing. Progress estimate about 92 to 94 percent, flat: the wave closed a route, generalised an
instrument and corrected two accounts, but did not move either route's remaining input. The even
route is untouched and still stands on `Hfam` alone.

## Status at wave 61 (2026-08-10)

**The `h >= 1` route now has the statement it has been building toward.** At every handle
count, for an honest continuous homomorphism and an honest frame, the forced dressing is
excluded against achievable stage-four refinements, with no achievability convention, no
legality hypothesis and no column hypothesis. Unconditional and at the level of homomorphisms,
in one theorem. That was the thing wave 60 left in two halves.

**The step we had been dreading turned out easy.** The transport one level wider is proved at
every handle count over any ring, and the quadratic block we expected to fight is even on the
achievable lattice, so the transport is affine mod two. I had told you last wave that this
would be the genuinely hard one; it was not, and the reason is specific rather than lucky.
It is not yet an exclusion, and the lane was clear about that: the surviving channels are live,
and the experiment that would widen the exclusion is now named and cheap.

**Three corrections and one closed door**, all from lanes doing their assigned work.

The soundness condition we carry at the wider level is merely sufficient, which is the third
such finding in three waves, but this time the sharp line stopped being a parity condition
altogether. One level out a dressing can move rows that the mod-two reading cannot see, so the
real criterion is that the shift act centrally. Four markings separate the two, where a row
moves by an even amount that is invisible mod two and decisive over the eight-element ring;
those four are measured, not yet proved.

Wave 60's class-five sharp line has a limitation I should flag: the point that witnessed it
does not survive one step wider, so that line is correct at its own level and is not a general
criterion.

And the handle block, which we proved visible two waves ago and had never used, turns out to
see nothing about the handle letters that we could not already see. That closes a direction I
would otherwise have spent a wave on. It does see the handle count, which is a small new
instrument with no soundness cost.

Final state `62fce996`: 4289 jobs green, census 11, zero sorries, capstones frozen, all gates
passing. Progress estimate about 92 to 94 percent. The even route is untouched and still
stands on `Hfam` alone.

## Status at wave 60 (2026-08-10)

**The class-five exclusion is now unconditional**, at exactly the scope the class-four one
enjoys, and the class-five forcing now holds for continuous homomorphisms rather than for
marking tuples. Those were the two things the `h >= 1` route was missing after last wave.

Two accounting notes worth your eye, since both correct things I have told you.

First, last wave's reason for deferring the wider translation identity was wrong in a useful
direction. We expected its defect shifts to be quadratic; they are affine, because the
relevant commutator subgroup vanishes one class up. The identity was therefore strictly
easier than the class-four version it imitates, not harder. Wave 59's obstruction also turned
out to be one coordinate wide, closed by a single extra evenness hypothesis.

Second, both soundness conditions we have been carrying, at class four and at class five,
are now known to be merely sufficient, and both sharp lines are characterised in both
directions. Class four's needs two covectors, class five's needs three, the difference being
that the sigma term is free at class four and live at class five. At class four every
committed point is now proved at its weakest condition. I should temper something I wrote
last wave: I said several points need only half the carried hypothesis, which is true, but
per achievable move only five of eleven actually halve. The uniform gain is per pair of moves,
where four conditions collapse to one, and the migrated statements also stop depending on the
achievability convention entirely.

There is a genuinely pleasant sub-result: at wave 59's own witness point the old condition and
the sharp line coincide, so nothing we published there was weaker than it looked. Only the
general reading was wrong.

Final state `5effc4e8`: 4285 jobs green, census 11, zero sorries, capstones frozen, all gates
passing. Progress estimate about 91 to 93 percent. The even route is untouched and still
stands on `Hfam` alone, which remains the one thing held for a Fable wave.

## Status at wave 59 (2026-08-10)

**The sigma residual we have carried since wave 51 is discharged.** The forced dressing that
class four reads as invisible is now excluded at class five, at every handle count, with both
class-four quotients trivial at both dressings so the separation is genuinely class-five. The
lane also volunteered a scope limit the reconnaissance had not stated, and it matters: the
exclusion holds against stage-five refinements and is FALSE one filtration step wider, where a
triple commutator of the point's own letters kills the dressed frame. The committed class-four
point has no such hole, so this statement is genuinely weaker than the class-four model it
imitates. Closing that gap is the top of the next wave.

**The class-five defect landed, and with it the reason two carriers had deferred it.** The
handle block stops being a sum over handles at class four, because a cross-handle pairing
appears that is order-dependent, so the closed form everyone was implicitly looking for could
never have existed. The same work discharged class four's own deferral as a corollary. This
unblocks class-five containment and transport, which previously could not even be stated.

**Two things I told you last wave are corrected, and both were caught by the lanes sent to
build on them rather than by an auditor.** First, the invisibility result is slot-local: the
handle block is invisible at class five at the committed sigma slot, and visible at class five
one trivial letter away, so last wave's class-eight forecast was never general. Second, and
more useful: the frame invariant we have been carrying for class-four soundness was never the
sharp line. The sharp condition is now characterised in both directions, and several of our
committed points need only half the hypothesis we carry. The composite I reported last wave,
that two live blocks outside the invariant break the forcing, is false; what breaks it is an
odd handle pairing, and three points carrying the identical odd block split two-to-one on
whether the forcing holds.

I would rather report this pattern than hide it: three waves running, the lane dispatched to
extend a result has been the thing that found the result overstated. That is the check working
where I want it, inside the work rather than after it. It also means our published claims have
been running slightly ahead of our proofs for several waves, and the corrections have all
narrowed scope rather than overturned mathematics.

Final state `2513bd0a`: 4281 jobs green, census 11, zero sorries, capstones frozen, all gates
passing. Progress estimate about 90 to 92 percent. The even route is untouched and still
stands on `Hfam` alone.

## Status at wave 58 (2026-08-10)

**The even route's public face is finished.** Its carried set is published in final form:
`Hfam` on each branch at every depth, plus the degree identity and the branch identification.
Nothing else, no stratum split, both branches symmetric in fields and binders, and the route's
status is a single named theorem (`evenRouteFinal_status`) with three concrete field models
behind it. That theorem is what the paper's even sections should quote. The retracted wave-56
structures now carry retractions in their own docstrings so nobody quotes them by accident.

**On the `h >= 1` route the class-five machinery exists.** The carrier is complete with its
hom layer, and the long-deferred sigma residual OPENS there: the forcing that class four reads
as identically zero becomes visible at class five, with an explicit witness whose only odd
datum is a matrix entry the class-four carrier does not have. Proving it is one new lemma plus
two decision steps, and the census for the lemma is already run. That is the top of the next
wave.

**Two corrections, both caught inside the wave that created the risk.** First, wave 57's
soundness result for a live handle block is a statement about ONE handle; at two handles the
relator controls only their product, both can be odd, and there is an achievable move that
breaks the forcing's shape. The honest form is that a live block inside the frame invariant is
harmless and two outside it are not, so anything we publish about class-four soundness at
positive handle count must carry that invariant. Second, and more subtle: one lane proved the
handle block's invisibility mechanism breaks at class five, another measured that the block
still stays invisible there for a different, arithmetic reason. Both are right. The statement
we are entitled to is that the structural cancellation ends at class five but arithmetic keeps
the block invisible through class seven, with the first opening at class eight. Neither lane's
headline alone would have been correct to publish.

I mention the second one because it is the check I instituted after last wave's failure doing
exactly what it was meant to do, for the second wave running. Two lanes of one wave can each
be right while their composition is wrong, and the close now checks for that before anything
is written down.

**Scoping correction, added during wave 59.** The invisibility statement above is now a
theorem, but only at the committed sigma slot, and the class-eight forecast inherits that
scope. The step it rests on turned out to be slot-local: the general row carries a term the
abelian rows do not control, and at a slot one trivial letter away from the committed one
there is a certified relator-killing marking whose block is odd and visible at class five,
with the selection bit separating it. So the honest statement is that the block is invisible
at class five at the committed slot and visible at class five away from it. That is better
news than it sounds for the `h >= 1` route, since visibility is what the route wants; it just
does not come from where we thought.

Final state `5ee25049`: 4277 jobs green, census 11, zero sorries, capstones frozen, all gates
passing at every station; about 5800 new lines of Lean this wave, every declaration pinned,
no census axiom newly consumed. Progress estimate about 89 to 91 percent. The even route did
not move, since its single input is untouched; what moved is the other route.

## Status at wave 57 (2026-08-10)

**The decisive question came back proved, and the even route is now down to one input.**

Last wave I told you the even route's only live supply was `EvenClimbResidualSupply`, and
that proving or refuting it would decide the route. It is proved, and in the form that
removes it rather than merely discharging it: on both branches, at every depth, it is
EQUIVALENT to the derivation-family supply, so `Hfam` alone delivers it. The supply is not
carried any more. `Hup`, the flip supplies and the neutral supply are off the route entirely,
and no live endpoint needs any of them.

So the even route now carries exactly one input, `Hfam`, on both branches at every depth,
and it is the item I have been holding for a Fable wave. The route stands or falls on it.

The mechanism is worth one sentence because it is the nicest thing this campaign has found in
a while: the object that killed the flip architecture, a one-bit character functional, is the
same object that shows the architecture was never needed, because every exponent sum of an
even relator is even and that puts the stage defect on the functional's trivial side, where
the two spans agree.

**Also good: both branches have honest field models again.** The N branch lost its witness
last wave when I found its field sat on the refuted stratum. It has a new one: the Eisenstein
quartic `x^4 + 4x^2 + 2`, with irreducibility, degree and the branch criterion's field side
all proved in Lean rather than measured, and degree four shown minimal for such a field.
Neither new model consumes the reciprocity axiom that an earlier audit flagged as never
constructed, which is a small tightening of the foundations.

**A correction, and it is the third in three waves.** The structures I reported last wave as
"corrected and minimal" are unusable, and the paper must not quote them. They kept one field
that a sibling lane in the same wave refuted at every depth, two commits later; the two lanes
never met in the import graph. Two lanes this wave found it independently. I have retracted
it in the log and above. All three of these were caught by lanes whose job was to look rather
than to build, which is why I now spend one lane per wave that way, and I have added a
structural check for the specific failure: a wave's own landings must be checked against each
other before anything built from them is published.

**On the `h >= 1` route.** All four selected rows at class four are now covered at every
handle count. And a class-four point with a live handle block exists for the first time, with
a sharp negative attached: the handle block can be live but is provably invisible to the
class-four forcing, so its information cannot be seen below class five. That locates what
remains on this route precisely.

Final state `4875ca1c`: 4273 jobs green, census 11, zero sorries, capstones frozen, all gates
passing at every station. Progress estimate about 88 to 90 percent, up sharply and honestly:
the even route's input list went from two named supplies to one, and that one was already the
known frontier.

## Status at wave 56 (2026-08-10)

**The wave-55 retraction got worse before it got better, and it ends better. Please read
this block rather than the wave-55 one; it supersedes it.**

Wave 55 told you the digit-flip supply fails at `alpha = 2`. Two things are now known.
First, `alpha = 2` is not a corner case: the range identity produces it generically. The
criterion is proved (`alpha >= 3` exactly when `sqrt 2` lies in `K`, a codimension-one
condition), and an exact census over the in-class fields of degree up to six finds 101 of
113 at `alpha = 2`, including four of the five quadratic ones; odd degree forces it. One of
our two pilot fields is on that side, which makes one of the non-vacuity witnesses I
reported last wave a vacuous theorem.

Second, and worse before better: the flip supply is false not just at `alpha = 2` but at
EVERY depth, on both branches, and so is `Hup`. Wave 55 read the requirement as satisfiable
above `alpha = 2` using a generic bound; the sharper bound needed to settle it has been in
our own tree for several waves, and with it the argument closes everywhere. The margin is
one binary digit, and it is exactly the digit a square costs. So the whole flip architecture,
which is how the even route has been organised for three waves, is dead.

**Why the route survives anyway.** The refutation is narrow in a way that matters: it kills
supplies demanding a sharp digit at one coordinate of a correction whose shift word is
trivial, and the climb never asks for that. `Hup` was only ever a sufficient condition for
what the climb actually consumes, being a span equality where one element in the span
suffices. Both endpoints are re-cut onto that weaker supply, `EvenClimbResidualSupply`,
which carries one hypothesis beyond the arithmetic binders and which nothing in the tree
refutes. The even route now has one live supply per branch at every depth, plus `Hfam`.
Proving or refuting it is the single decisive question, and it is the top of the next wave.
If it fails, the even route as architected is closed rather than re-cut, and I will tell you
so plainly.

**On the `h >= 1` route, only good news.** Three of the four selected rows at class four are
now covered at every handle count (the cleared row is still at one handle; I wrote "all four"
here first and the next wave's audit caught it), the doubly-uncleared row turned out not to
be obstructed, and the class-four obstruction now holds over the honest commutator image
rather than an over-approximation, so last wave's exhaustive corner verdict is certified in
its own terms.

**Correction to the sentence that stood here, and it matters for the paper.** I wrote that
the paper-facing structures were corrected and minimal. They are not usable, and the paper
must not quote them. The corrected structures kept one field, the coordinate-`0` flip demand,
which a sibling lane in the same wave refuted at every depth two commits later; the two lanes
never met in the import graph. Composed, they make the "corrected" list hold exactly where it
is vacuous and false everywhere else. Two wave-57 lanes found this independently. What
replaces it is better: the endpoint now holds over the single residual supply alone, with no
reciprocity bundle, no ramification datum and no sign condition, at every depth. This is the
third time in three waves that a claim of mine outran its proof, and all three were caught by
lanes whose job was to look rather than to build.

**A process note I think you should see.** This is the second wave running in which a claim
outran its proof. Wave 55's drift was between prose and Lean; this wave's was inside the
Lean, where a sharper bound we already owned would have refuted a route we spent a wave
building on. The standing check is now doctrine: whenever a bound is used to conclude that a
possibility survives, verify it is the sharpest bound the tree already owns. I have also
started spending one lane per wave on verification rather than construction, which is what
caught both.

Final state `84fa2e5f`: 4269 jobs green, census 11, zero sorries, capstones frozen, all
gates passing at every station. Progress estimate about 84 to 86 percent, essentially flat
against last wave despite a lot of proof landing, because the route being measured was
replaced by a shorter one whose single input is not yet proved.

## Status at wave 55 (2026-08-10)

**Read this first: a wave-55 lane refuted an input the even route depends on, and part of
what I reported to you at wave 54 is now known to be vacuous.** The digit-flip supply is
FALSE at `alpha = 2` (`evenFlip_not_flipSupply_two`, machine-checked, with the mechanism
identified: coordinate `0` is the only one whose row is not a bracket, so a trivial shift
word forces a congruence that contradicts the demand exactly when `alpha = 2`). Because
wave 53 proved `Hup` EQUIVALENT to that supply, `Hup` is false at `alpha = 2` on both
branches too, and the `alpha = 2` stratum endpoints of waves 53 and 54 have unsatisfiable
hypotheses. Concretely: what I told you at wave 54 as "both branches carry two inputs at
every `alpha >= 2`" is true only for `alpha >= 3`.

The same lane also found the paired-move identity I reported last wave as the sole
remaining demand for one slot is itself FALSE, computed its exact defect, and proved a
hypothesis-free repair. With the repair, every flip coordinate EXCEPT `0` is now a theorem
on both branches, so at `alpha >= 3` the even route's flip demand is one coordinate rather
than a family. That is a real advance and it arrived in the same lane as the refutation.

Where that leaves the even route, stated honestly: proved for `alpha >= 3` modulo the
single coordinate `0`, and open at `alpha = 2`. The campaign owes one of two things at
`alpha = 2`, and I have made this the top item of the next wave: either a route that does
not go through flips, or a proof that the range identity never produces `alpha = 2`, in
which case the stratum is empty and nothing is lost. I do not yet know which is true.


**The rest of wave 55, briefly.** The uncleared row at class four is solved, and the sigma
forcing now runs there on the frame itself with two hypotheses removed rather than
discharged; the structural reason wave 54 could not reach it is now understood (the two
handle letters swap roles with the row type). That lane also produced the campaign's first
class-four forcing whose soundness quantifies over the group rather than over a generating
model. On the `h >= 1` route the residual corner census is now a theorem rather than a
measurement. The instance refactor is complete (31 of 35 copies gone), and a duplicate
declaration we had recorded as harmless turned out to be import-order dependent, meaning the
tree contained a genuine ambiguity about which proof was in force; it is resolved.

Final state `f8be7209`: 4264 jobs green, census 11, zero sorries, capstones frozen, all
gates passing at every station.

**My progress estimate goes DOWN this wave, from about 87 to 89 percent to about 85 to 87.**
A stratum previously counted as proved is now known not to be. I would rather the number
move backwards honestly than hold still.

**Open, still yours (unchanged):** section 1 (the `q = 4` ramified Arf sign; recommendation
stands: option 3) and item 6's `alpha = 1` even cores.

**Also this wave:** an adversarial audit of the whole even endpoint chain found it sound
(no vacuity of the wave-52 kind, every composition link present with the correct per-`K`
quantifier shape, no circularity, census exactly 11) and committed field-level models
showing both branch endpoints are satisfiable at concrete fields. Note that the audit's
verdict was explicitly conditional on the two named supplies, which is precisely the gap
the flip refutation then found; the two results are consistent, and the pairing of a
verification lane with a construction lane is what caught it. On the `h >= 1` route, wave
54's exhaustive corner census is now a theorem rather than a measurement.

## Status at wave 54 (2026-08-10)

**Retired this wave:** the Bockstein identity I flagged last wave for a sanity check is now
a theorem, proved group-generically, and it came in cheaper than the route we had recorded.
We had justified the `Z/4` lift by a procyclicity argument; the proof needs none of it.
Writing `u^2 - 1 = 2^(alpha+1) x`, the cofactor is additive once read mod 4, because
`4` divides `2^(alpha+1)`. No logarithm, no topological generator, no filtration. The
Hilbert-symbol route we also considered is written up in the file with a full sketch and is
strictly more expensive in census terms, so we did not take it. Nothing needs your review
here; I am recording it because you asked to see that one identity.

**The even route is now symmetric and minimal.** Both branches carry the same two SUPPLIES
at every `alpha >= 2`: `Hfam`, and the digit-flip supply. Discharged: the stage base on both
branches, the frame form of the ramified-`i` binder, and the M-side isotropy. The M slot-2
flip is a theorem and is out of the carried set; slot 3 is reduced to one commutator
identity. For the paper: the carried inputs are now published as Lean structures
(`EvenRouteCarried{N,M,NTwo,MTwo}`) rather than described in prose, so the even sections can
quote a machine-checked list rather than a narrative one.

I audited that claim adversarially before writing more on top of it, and I got three
sentences of it wrong the first time; the corrections are worth your eye since this is the
paragraph the paper's even sections will lean on. The reciprocity bundle is dropped from the
stratum endpoints but is still carried by both per-field endpoints. What fell of the
ramified-`i` binder is its frame form, not the ramification hypothesis itself. And the
published `EvenRouteCarriedM` still has three fields rather than two: it carries the isotropy
input even though that input is now a theorem, because the lane that proved it and the lane
that published the structure never met in the import graph. The mathematics is as claimed;
the structure needs a one-field re-cut, which I have queued. The audit found no vacuity of
the kind that bit us at wave 52, every composition link present with the correct per-`K`
quantifier shape, no circularity, and the axiom census exactly 11. Its note is
`docs/dyadic/w55-audit-note.md`, and it also committed field-level models witnessing that
both branch endpoints are satisfiable at concrete fields.

**The `h >= 1` route's corner question is closed.** Last wave's containment file recorded
certain binder corners as provable dead ends and named the `gamma_2` transport as the
sharpest open step. Both records are now updated: those are dead ends of the ENGINE, not of
the tower, and the transport is a mod-two affine phenomenon rather than the quadratic one we
expected. Three new moves raise corner coverage from `16384` to `97280` of `131072`, and the
remaining `33792` are exhaustively certified dead, so no corner is left open. The class-four
results have also been transported to the level of continuous homomorphisms, which is the
form the endgame needs.

**Two long-rolling tickets were refuted rather than done,** both with evidence. The
unramified-branch rewire has no second half; the phrase "first half" in a wave-51 commit is
what kept it on the board for three waves, and each remaining hand-proved row is provably
not a duplicate. And our instance-dedup backlog entry had the wrong inventory (35 copies
over 11 files, not 32 over 12), because the counting grep missed this repository's
`public import` form.

Final state `b25e530b`: 4260 jobs green, census 11, zero sorries, capstones frozen; five
lanes, five successes, all gates passing at every station.

## Status at wave 53 (2026-08-09)

**Open, still yours (unchanged):** section 1 (the `q = 4` ramified Arf sign; recommendation
stands: option 3) and item 6's `alpha = 1` even cores.

**Orientation for the paper, new this wave:** the even route's input list shrank twice.
`Hup` is no longer an opaque hypothesis: its natural route is refuted outright
(machine-checked on both branches; the truth stratum and the need stratum are disjoint),
and `Hup` itself is machine-checked EQUIVALENT to a concrete one-digit flip supply
(`EvenDigitFlipSupply`), with one M-branch slot already a theorem.  On the M side the
stage base is discharged, traded for the ramified-`i` binder plus one isotropy equation
per field, proved necessary and proved at `alpha = 2`; the whole `alpha >= 3` case is one
missing Bockstein lemma (`x cup x = 0` on classes lifting to `Z/4`, equivalently
`(-1, u_mu)_K = 1`).  If you want to sanity-check one thing mathematically this wave, that
identity is the one; it is classical and we expect it to be routine.

**Landed this wave (headlines):** the relator containment theorem at class four
(`SqCore/GradedContainFour.lean`: the K-dressed frame's defect at a relator-solution is a
pure dressing artefact and the committed engine kills it; zero census axioms); the sigma
slot opened at class four (`SqCore/GradedSigmaFour.lean`: three live channels, an exact
selection bit with soundness a theorem, the residual forcing precisely located at class
five); the M frame re-cut onto the deep seam (`Instances/StageAbstractionEvenFrameDeep
.lean`: the gap is one binary digit carried by a depth-`alpha` generalisation of Serre's
omega); the Hup settlement (`Instances/StageAbstractionEvenDigit.lean`); and the `d - 1`
cokernel block explained by measurement (`docs/dyadic/w53-dcut-note.md`: it is the
full-domain cokernel, generic in the relator, dual to the Frobenius-image components,
1279 scored assertions with zero failures).

**A correction you should know about:** the wave-52 vanish note's section 1.4 claimed the
graded Fox form is onto the full layer; wave 53's sweeps found that claim false and its
kernel numbers unreproducible.  The note is corrected in place with the original preserved
for the record; nothing else in the note depended on it, and the corrected bookkeeping is
strictly better (it settles the corank at every level in one stroke once the elementary
statement in the w53 note is proved).

Final state `51735536`: 4256 jobs green, census 11, zero sorries, capstones frozen; five
lanes, five first-pass successes, no storms, no salvage.

## Status at wave 52 (2026-08-09)

**Open, still yours (unchanged):** §1 (the `q = 4` ramified Arf sign; recommendation stands:
option 3) and item 6's `α = 1` even cores.

**Decision-adjacent, new this wave, for orientation before the paper's even sections:** the
W51 even endpoints were found VACUOUS as stated, machine-checked: a uniform-in-`K` range
hypothesis at fixed `α` is inconsistent (odd-degree `K` has full cyclotomic range;
`rangeFinal_uniform_Hrange_imChiN_absurd`).  The honest, and now committed, endpoint shape
is per-`K` with an existential `α ≥ 2` (`evenPerK_orientedEquivN/M` in
`Instances/StageAbstractionEvenPerK.lean`), with six of the former named hypotheses
discharged outright (the range identity, both mod-8 seams, the corrected deep row seam, the
model Demushkin package, fin-gen, and the rank identity) and only the stage base plus the
two honest frontier inputs (`Hfam`, `Hup`) carried.  On the `α = 2` stratum even the base
discharges, leaving exactly the odd route's two-input shape.  The paper's even sections
should be drafted against this per-`K` existential quantifier shape.

**Landed this wave:** the range identity itself, as a theorem with zero census axioms
(`Instances/EvenCyclotomicRange.lean`: `range chiCycKTwo = imChi{M,N} α`, branch decided by
`−1` membership, even-degree hypothesis unnecessary, odd degree recovering the committed
surjectivity); the corank vanishing explained in three layers (`SqCore/GradedVanish.lean` +
`docs/dyadic/w52-vanish-note.md`: the dressing defect IS the graded Fox form, two of the
`d + 1` cokernel functionals canonical and proved, and the containment measured to be
THIS-RELATOR-SPECIFIC while the corank is generic, so the identity to prove is now located
at class four); the class-four stage engine (`SqCore/GradedFour.lean` + `GradedLift.lean`:
the `U₅` carrier, the translation identity, the two-regime completion collapsed by parity
with a genuinely new surjective regime, the whole-binder witness with the new `i`-row
residue, and the reusable `LiftStep` schema); the first EV-3f boundary discharged and the
second refuted-and-relocated to a one-digit character-depth demand
(`StageAbstractionEvenDerivKer/EvenRawToBracket/EvenClimbFinal.lean`); the even model
Demushkin package tightened (`Instances/EvenDemushkin.lean`, six hypotheses to five, the
`α`-threshold separation machine-checked); and the consolidation batch (general-level pivot
machinery hoisted upstream, the owed `dn_torsionGen_sq` at its honest `2 ≤ α` threshold,
the depth-necessity pin making `s = α − 1` zero-slack a theorem, the even cup-transport
clone `Instances/EvenModelCupForm.lean`, and two stale-reference repairs).  Final state
`9375e108`: 4252 jobs green, census 11, zero sorries, capstones frozen.

**Process note you may care about:** the wave survived a mid-wave orchestrator handoff (the
prior session hit its usage limit with two agents in flight; the takeover prompt plus
salvage commits lost zero lines) and, later, several hours of kernel file-table exhaustion
caused by an unrelated parallel mathlib build on the same machine; all failures were
environmental, none mathematical.

## Status at wave 51 (2026-08-08)

**Open, still yours (unchanged):** §1 (the `q = 4` ramified Arf sign; recommendation stands:
option 3) and item 6's `α = 1` even cores.  New for orientation, not decision: the wave found
genuine even-degree structure at `α = 2` (both bridge tables' ω entries are α-dependent and
nonzero exactly at `α = 2`; on the M row no ω scalar exists there at all, machine-checked,
resolved by a new Witt-transitivity layer; on the N row `α = 2` gives the first genuinely
non-surjective character satisfying the committed sharp seam).  Worth a summary before the
paper's even sections are drafted.

**Landed this wave:** the containment identity on the whole binder with unconditional
bit-zero existence (`SqCore/GradedContain.lean`); the σ-slot slice-blindness diagnosis with
the off-gauge separation escape (`SqCore/GradedSigma.lean`); the class-6 corank verdict
(still `d + 1`) with the class-5 grid exhaustive and a new mod-2 parity structure
(`docs/dyadic/w51-class6-note.md`); both frame existences sharp
(`Nonempty (MFrame α h)` iff `α ≥ 1`, `Nonempty (NFrame α h)` iff `α ≥ 2`, three regimes)
with frame-free `demushkinQ` values; the δ-row Fox layer with the first unramified hat row;
and the entire EV-3 board: the even oriented-equivalence endpoints exist with axiom prints
identical to the odd route, behind six named hypotheses (two scoped ~650-line boundaries
remain inside EV-3f; the load-bearing arithmetic seam is now the range identity
`range chiCycKTwo = imChi{N,M} α`).  Final state `48589bd5`: 4242 jobs green, census 11,
zero sorries, capstones frozen.

## Status at wave 50 (2026-08-07)

**Open, still yours:** §1 (the `q = 4` ramified Arf sign — the recommendation stands: option 3,
restrict the even determinant lane to odd `f` now and ticket the sign-corrected general form)
and item 6's `α = 1` even cores (deliberately unasserted; both cores leave the shared Gram).

**Resolved this wave:** §1b (nesting — resolved earlier by W42-NEST/W42-BUNDLE, see the updates
below); item 2 (`LRamifiedSourceArfSupply` now binds the consumer's full tail — `m`, `hcard`,
`l`, `hl`, `hram` — since no in-repo lemma derives even-dimensionality from `Nonsingular`; the
producer hookup is `lRamifiedSourceArfSupply_pow`); item 3 (`NLabHypothesis` carries the
canonicity guard as a *parameter* mirroring `MLabHypothesis`'s, with `noCanonicityGuard` and
`nonempty_equiv_DM_DN_of_unguarded_nLabHypothesis` committing the refutation that forced it);
item 4 (the graph-data records and their `_of_graphData` theorems plus the two `PhaseModel`
consumers are deprecation-marked at the head-factored replacements); item 5 (supersession
banner on `labute-interface-status.md`; four fictitious citations fixed, two beyond the memo's
count; `norm_two_lt_one'` de-privatized and its downstream duplicate deleted); item 6a (the
general-`h` `M`-frame exists — `MarkedCore/MFrame.lean`, `demushkinQ_DM_mFrame`, α-free with
`α = 0` proved empty, and the item-3 counterexample now costs one frame at every handle count);
item 6c (the `mpcW` jet layer at general `h` — `Instances/MpcJetGeneral.lean`, including a
second-order value for the hash-pinned one-handle certificate).

New this wave, for orientation rather than decision: the class-three *selection* is a computable
parity with an iff-characterization and an explicit completion move (`GradedSelect.lean` §5–§7,
`docs/dyadic/w50-selection-note.md`), and the Magma depth sweep found zero infeasibility with
class 3–4 exhaustive at `h = 1` (`docs/dyadic/w50-depth-sweep.md`); the sweep's
codimension-`(d+1)` containment identity is proposed as the next Lean target on the `h ≥ 1`
route. The even forward route now has its generic stage layer and the EV-3 ticket board
(`docs/dyadic/ev4b-stage-abstraction.md`); one committed Prop (`SharpExactLevelFibreLiftSupply`)
was found false at even degree and replaced by a row-target-relative form.

## 1. DECISION: the ramified Arf conclusion is false at even residue degree

**Finding.** The determinant analysis' ramified branch concludes `Arf(q̄_U) = 0`. That
conclusion holds at residue cardinality `q = 2^f` **only when `f` is odd**. At `q = 4` it is
false, with an explicit counterexample: `C = D₅` acting on `V = 𝔽₁₆` with `t = ·ζ₅` and
`s = Frob²`, `q̄(x) = Tr(c x⁵)` for `c ∉ 𝔽₄`. There `V^U = 𝔽₄` has four elements rather than
the predicted two, `rank(1+U) = 2 ≢ s_V`, and Wall's formula gives `Arf(q̄_U) = 1`. The
witness was verified twice by independent routes (the rank formula, and directly via
`q̄_U = q̄ + ℓ`). The general count is

    #V^U = 2^(gcd(deg P, F·ω) · s_V),

whose exponent is odd exactly when `F` is odd.

**Impact.** None on the L row: odd degree forces `f` odd, and
`wordCertificateRN_lSq_pow` is stated with `Odd f`, so the L certificate is unconditional
on its whole branch. The **even rows** are affected, since they admit even residue degree.

*Narrowing (added 2026-08-06).* The even rows' **Stokes** lane is unaffected: the compact-M
ramified branch was closed without consuming any Arf sign (the pairing separates primal from
dual coordinates and never evaluates a quadratic form), and a sweep of the even Stokes
branches found no place where the wrong sign could be inherited. The exposure is confined to
the even rows' **determinant** residues, which are not yet built — so the decision below can
be taken when that lane opens, not before.

**Options.**

1. **Restrict the even-row program to `f` odd.** Cheapest; leaves the even rows' general
   statement incomplete at even residue degree.
2. **Carry the corrected Gauss sign** `(−1)^(gcd(deg P, F·ω) + 1)` through §6 and the
   determinant bridge. More work, and it changes displayed statements in the paper's §6.
3. Split: prove the even rows at `f` odd now, open a separate ticket for the sign-corrected
   general form.

**Recommendation:** option 3 — it unblocks the even rows immediately and isolates the sign
work, which is a self-contained §6 revision.

## 1b. DECISION: the general-K route's axiom print is not nested in the ℚ₂ capstone's

*(added 2026-08-06)*

The odd-degree endpoint reached through the new general-`K` machine, specialized to
`[K:ℚ₂] = 1`, was intended as an independent check on the whole construction: its axiom print
should ideally be a subset of the frozen ℚ₂ capstone's. It is **not** — the two are
incomparable:

* the new route **carries** `markedRecipAt` (general-`K` marked reciprocity), which the capstone
  does not;
* the new route **avoids** `dyadicOrientation` (B3c), `peripheralCyclotomicAction` (B8) and
  `tameQuotient`, which the capstone uses;
* six census members are shared.

Two of the three absences are explained and benign: `tameQuotient` arrives as the hypothesis
`T : OrientedTameQuotientK B FF` rather than from the axiom, and the frame lane reaches the
pro-2 block without the rank-three certificate where B3c and B8 live.

The live question is `markedRecipAt`. **Options:** (a) accept the incomparable print and drop
the "independent check" framing; (b) route the ℚ₂ instantiation's marked reciprocity through
`localReciprocity` directly, restoring nesting; (c) prove the ℚ₂ specialization of
`markedRecipAt` from `localReciprocity` once, which would make every general-`K` endpoint nest
at `[K:ℚ₂] = 1`.

**Recommendation:** (c) if it is cheap — it is the version that makes the check meaningful for
*all* future general-`K` endpoints, not just this one — otherwise (a), stated plainly in the
paper rather than silently.

*Update 2026-08-06:* the degree-one endpoint is now unconditional
(`NuAdapted.gammaR_lSq_equiv_galK_degreeOne`) and its verified root-level print is std-3 +
{B1, B3c, B5, B5-K, B6, B7, B8, B9, B11a}. Two of the three axioms the route previously avoided
came back — `dyadicOrientation` (B3c) and `peripheralCyclotomicAction` (B8) — because the two
pivot subgroups are built from `prop_3_8_lift` (B8) and the Labute-orientation transport (B3c).
So the print is now the capstone's nine plus `markedRecipAt`, and the nesting question reduces
to that single axiom exactly as stated above. A **cheap follow-up** exists if you want the
footprint split: the *translation* family can be made axiom-free via `thetaEquiv`
(`thetaHom : A ↦ A^{S^b}, S ↦ S, Y ↦ Y·S^b` preserves `d0Word` on the nose, verified by hand),
while the `u`-scaling is genuinely where B8 sits.

### Update 2026-08-06 (W42-NEST): §1b is **resolved** — B5-K was plumbing, and the check now nests

**Measurement.** `markedRecipAt` is **not mathematically load-bearing** anywhere on the
degree-one path. Of the 64 367 declarations in the milestone's reachable closure, exactly
**three** apply the axiom, and all three apply it at the *ambient* field `K`, as the argument of
a lemma that is generic in the bundle and prints the standard three:

| consumer | applies | the generic lemma's binder |
| --- | --- | --- |
| `oddDegreeGalKSq_allStagePrimitiveResidualVanishing` (`…LabuteVariableStageTwo.lean:117`) | `chiCycKTwo_surjective_of_odd_finrank K (markedRecipAt K) hodd` | `{R : LocalReciprocity} (B : MarkedRecip R K)` |
| `nonempty_orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply` (`…FieldRigidity.lean:316`) | `SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply (markedRecipAt K) hodd` | same |
| `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` (`…LabuteFrattiniFrame.lean:940,951`) | both, plus `cyclotomicModEightOmegaClassKTwo_ne_zero (markedRecipAt K) hodd` | same |

(`EvenDemushkinQ.lean:178-180` is the fourth call site in the tree and is **not** reachable from
the odd-degree route.) So B5-K's entire contribution here is surjectivity of `chiCycKTwo` at odd
degree, which the caller's own `B : MarkedRecip Rec K` supplies at std-3. B5 comes along only
because `markedRecipAt`'s *type* mentions `localReciprocity`.

Two of the three consumers simply never took a bundle binder; the third cannot, because
`OddDegreeSqCyclotomicFrattiniFrameSupply`
(`GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean:168`) quantifies over **every** `K`
internally, so no `K`-indexed bundle is in scope.

**Result.** `GQ2/Dyadic/Instances/DegreeOneNesting.lean` re-derives the forward route with the
bundle threaded (the committed proofs verbatim, `(markedRecipAt K)` → `B`) and reaches
`Nesting.gammaR_lSq_equiv_galK_degreeOne_nested_unconditional`, which has **exactly the
committed milestone's type** (pinned by two `example`s) and whose verified root-level print is

    std-3 + {B1, B3c, B6, B7, B8, B9, B11a}

i.e. the frozen `ℚ₂` capstone's nine **minus** `localReciprocity` (B5) and `tameQuotient` (B10) —
a **strict subset**. The degree-one check therefore nests.

On independence, measured rather than asserted: the new endpoint depends on **none** of
`main_presentation_literal_roe{,_unconditional}`, `main_presentation_literal`,
`Dyadic.QTwo.candidateGroup_lSq_equiv_absGalQ2`, `candidate_equiv_absoluteGalois`,
`Roe.gammaR_lSq_equiv_roe`, `eq_154_R`, so it is not circular against the theorem it checks. It
*does* depend on `GQ2.Roe.Labute.bLab` — but so does the committed milestone, by the same route
(the two pivot subgroups at `h = 0`), so that is not a difference between the two.

Per-headline prints, all measured at the root:

| declaration | print (beyond std-3) |
| --- | --- |
| `Nesting.allStagePrimitiveResidualVanishing_of_markedRecip` | B1 |
| `Nesting.orientedEquiv_of_oddDegree_of_base` | B1, B6, B7 |
| `Nesting.exists_cupAdaptedFrattiniFrame_of_markedRecip` | B1, B6, B7, B11a |
| `Nesting.sqCyclotomicStageTuple_levelThree_of_markedRecip` | B1, B6, B7, B11a |
| `Nesting.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_nested` | B1, B6, B7, B9, B11a |
| `Nesting.gammaR_lSq_equiv_galK_degreeOne_nested_unconditional` | B1, B3c, B6, B7, B8, B9, B11a |
| *(for comparison)* `NuAdapted.gammaR_lSq_equiv_galK_degreeOne` | B1, B3c, B5, **B5-K**, B6, B7, B8, B9, B11a |
| *(for comparison)* `main_presentation_literal_roe_unconditional` | B1, B3c, B5, B6, B7, B8, B9, B10, B11a |

B3c and B8 are inherited exactly as the previous update explains (the two pivot subgroups); they
are *inside* the nine, so they do not affect nesting.

**Two side findings worth recording.**

1. The corrected (W41) routes were already B5-K-free — `…oddDegree_of_orientedClearAtUnitPivot`,
   `…_of_subgroups_of_markedSupply`, `…_of_subgroups_of_presentation` and the grand assembly's
   own `LSquare.gammaR_lSq_equiv_galK_degreeOne` all print std-3 + {B1, B6, B7, B9, B11a}. The
   axiom survived only on the *unconditional* milestone, which still routes through
   `…_of_orientedClear` → `orientedEquiv_of_oddDegree`.
2. A `B5-K`-free degree-one route already existed:
   `nonempty_orientedEquiv_bot_of_forwardStageRigidity` (the `K = ⊥` route), print
   std-3 + {B1, B3c, B6, B7}. It is not circular against the ℚ₂ presentation theorem either —
   but it gets its level-three stage base from `sqCyclotomicStageTuple_bot_three_nonempty`, i.e.
   by transporting the `D₀` classification of `G_ℚ₂(2)` itself, so it does not exercise the
   general-`K` frame construction at degree one. The new route builds that base through the
   machine (§0 of `DegreeOneNesting.lean`), which is what makes it a check on the machine. Both
   statements are honest; they test different things, and the memo's framing should say which.

**Recommended follow-up (not done — outside W42-NEST's file ownership).** Make the threading
durable in place and delete the duplicate: give `OddDegreeSqCyclotomicFrattiniFrameSupply` a
bundle binder (`∀ K [insts] {R} (B : MarkedRecip R K), Odd … → ∃ F, F.IsCupAdapted`), replace the
five `(markedRecipAt K)` occurrences at `…LabuteVariableStageTwo.lean:117`,
`…FieldRigidity.lean:316` and `…LabuteFrattiniFrame.lean:940,951` (plus the supply's own
signature) by that binder, and thread `B` through the nine downstream statements
(`oddDegree_sqCyclotomicStageTuple_levelThree`,
`nonempty_orientedEquiv_oddDegree_of_{stageBase_and_actualDefectSupply,
stageBase_and_primitiveResidualVanishing, kernelAdaptedSupply, family_of_cubicNeutralDamage,
cubicNeutralDamage}`, `nonempty_orientedEquiv_oddDegree`, `orientedEquiv_of_oddDegree`, and the
`NuAdapted` `…_of_orientedClear` trio). Each is a one-line signature change; the proofs are
unchanged. That drops B5-K and B5 from **every** general-`K` odd-degree endpoint, not only at
degree one, and lets `DegreeOneNesting.lean` §0 (a 131-line verbatim duplicate kept only as the
demonstrator) be deleted. Census stays at 11; B5-K remains live on the even/boundary lanes.

## 2. `LRamifiedSourceArfSupply` is missing a hypothesis

`GQ2/Dyadic/Instances/GammaLDeterminantResidue.lean:44` quantifies over every block, level
and lift with **no ramification hypothesis**, while its only consumer
(`wordPhaseResidueK_ramified_lSq`) supplies one. In an unramified block the descended source
form has `Arf = 1`, so the literal statement is unprovable. The `hram`-conditioned form is
what is actually built and consumed (`lRamifiedSourceArf_blockK`).

**Recommended fix:** add `hram` to the binder list; `lRamifiedSourceArf_blockK` then produces
the supply verbatim.

## 3. `NLabHypothesis` is false-shaped

`GQ2/Dyadic/MarkedCore/N.lean:1306` has no canonicity guard, unlike its `M` twin. `DM α h`
satisfies **every** clause of `NLabHypothesis α h` (Demushkin, rank `coreRank h`, `q = 2`, and
a continuous character whose range is exactly `imChiN α` — `chiNOnDM`), so the hypothesis
forces `DM α h ≅ DN α h`, which is false: `imChiM α ≠ imChiN α` is now an unconditional
theorem (`EvenNLabWitness.lean`, α ≥ 2). A literal `¬ NLabHypothesis` needs canonicity of the
orientation, precisely the clause the binder drops.

**Recommended fix:** add the canonicity guard the `M` binder carries, or retire the binder —
the even-row route decided this wave (clone the L forward-generator architecture) does not use
it at all.

## 4. Superseded records to deprecate

`LUnramifiedGraphData` / `LRamifiedGraphData` (`GammaLDeterminantUnramified.lean:34`,
`GammaLDeterminantRamified.lean:37`) and their two `_of_graphData` theorems are stated one
level too high: their lower-marking conditions are equations in `DD.C0`, which at
`blockEnrichmentDK` force the whole C-stage to be procyclic (`yc_procyclic_of_c0_graphData`).
The head-factored replacements supersede them.

## 5. Documentation drift

* `docs/dyadic/followup/labute-interface-status.md` — its central finding (the Labute
  hypotheses conclude *unoriented* equivalences and are therefore insufficient) is superseded
  by `OrientationCorrection.lean:456,468,563,584`, which supply the oriented forms; and its
  "remaining invariant" list is off the forward path entirely after this wave.
* Two docstrings miscite `Kummer.kummerCocycleFun_root_indep`; the real name is
  `GQ2.kcf_root_indep'`.
* `HilbertLedger.norm_two_lt_one'` is `private` and was re-proved downstream; de-privatizing
  removes the duplication.

## 6. Small tickets worth opening

* **`MFrame` at general `h`.** `demushkinQ (DM α h) = 2` exists only at `h = 0` and only from
  an `MDecomposition α`, with no producer. The `N`-side template (`N.lean:176–337`) transfers
  almost verbatim; only the torsion generator changes, to `t = Ā·C̄₀^(2^(α−1))`. This would
  make the item-3 counterexample unconditional at every handle count.
* **`α = 1` even cores.** Everything even in this wave assumes `α ≥ 2` (at `α = 1` both cores
  leave the shared Gram). Whether the `α = 1` cores are Demushkin is open and deliberately
  unasserted.
* **`mpcW` Hessian/jet layer** at general `h` (the `npcW` analogue landed this wave).

### Update 2026-08-06 (W42-BUNDLE): the recommended follow-up is **done**, and the *committed milestone itself* now nests

The threading above was carried out in place.  `OddDegreeSqCyclotomicFrattiniFrameSupply`
(`GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean`) now carries
`{R : LocalReciprocity} (_B : MarkedRecip R K)` after its instance binders, and `B` is threaded
through sixteen downstream statements.  Every change is a signature change; **no proof body
changed except by substituting `B` for `(markedRecipAt K)`**, so W42-NEST's "plumbing, not
mathematics" reading is confirmed.

Measured at the root (a file importing `GQ2`), before → after:

| declaration | before | after |
| --- | --- | --- |
| `NuAdapted.gammaR_lSq_equiv_galK_degreeOne` (**the committed milestone**) | B1, B3c, **B5**, **B5-K**, B6, B7, B8, B9, B11a | **B1, B3c, B6, B7, B8, B9, B11a** |
| `Nesting.gammaR_lSq_equiv_galK_degreeOne_nested_unconditional` | B1, B3c, B6, B7, B8, B9, B11a | unchanged |
| `NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear` | B1, **B5**, **B5-K**, B6, B7, B9, B11a | B1, B6, B7, B9, B11a |
| `NuAdapted.gammaR_lSq_equiv_galK_degreeOne_of_pivotMoves` | B1, **B5**, **B5-K**, B6, B7, B9, B11a | B1, B6, B7, B9, B11a |
| `gammaR_lSq_equiv_galK_oddDegree_of_jointClearing` | B1, **B5**, **B5-K**, B6, B7, B9, B11a | B1, B6, B7, B9, B11a |
| `orientedEquiv_of_oddDegree`, `nonempty_orientedEquiv_oddDegree` and its eight `_of_…` variants | B1, **B5**, **B5-K**, B6, B7, B11a | B1, B6, B7, B11a |
| `oddDegreeSqCyclotomicFrattiniFrameSupply_holds`, `…_of_presentingFrame`, `oddDegree_sqCyclotomicStageTuple_levelThree` | B1, **B5**, **B5-K**, B6, B7, B11a | B1, B6, B7, B11a |
| `oddDegreeGalKSq_allStagePrimitiveResidualVanishing` | B1, **B5**, **B5-K** | B1 |
| `main_presentation_literal_roe_unconditional` (frozen `ℚ₂`) | B1, B3c, B5, B6, B7, B8, B9, B10, B11a | unchanged |
| `gammaR_lSq_equiv_galK_oddDegree` (grand assembly) | B1, B6, B7, B9, B11a | unchanged |

So **§1b's option (c) is realized**: B5-K and B5 are off *every* general-`K` odd-degree endpoint,
not only at degree one, and the milestone's print is now literally equal to the nesting check's —
a strict subset of the frozen nine (it misses `localReciprocity` and `tameQuotient`).  The
duplicate §0 of `DegreeOneNesting.lean` is deleted and §6 calls
`oddDegree_sqCyclotomicStageTuple_levelThree` directly; the file's headline keeps the committed
milestone's type (§7's two `example`s still pin it) and its print is unchanged.

Deliberately **not** threaded, to keep their statements exactly as committed (their prints are
unchanged, so nothing regressed):

* `exists_presentingFrame_oddDegree` and `exists_cupAdapted_presentingFrame_oddDegree` — their
  content is that a presenting frame exists *with no hypothesis*, so they instantiate
  `markedRecipAt K` themselves;
* `nonempty_orientedEquiv_bot_of_kernelAdaptedSupply` and
  `nonempty_orientedEquiv_bot_of_primitiveResidualVanishing` — the two `K = ⊥` full-circle
  regressions, which instantiate `markedRecipAt ⊥`.

Threading the bundle into those four is a one-line change each if the owner prefers the smaller
footprint over the hypothesis-free statement.  Census unchanged at **11**; B5-K stays live on the
even/boundary lanes.
