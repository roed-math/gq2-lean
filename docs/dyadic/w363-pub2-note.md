# W363-PUB2 lane note: the six missing L/N exporters

**Status: staged proposal only. Nothing in this lane is owner adoption, acceptance,
census amendment, appendix migration, or release authorization.** Staged artifacts are
proposals. No frozen identifier or hash is changed, no historical verification report is
relabelled as current, and no universal frozen-M placement claim is made or revived.

Worktree `cla/worktrees/w363-pub2`, branch `claude/w363-pub2`, base `b87bfa06`,
Lean 4.31.0-rc2. The frozen `generated/appendix/*.tex`, `generated/hash-manifest.json`,
`GQ2.lean`, every module under `GQ2/`, `scripts/w361_check_staged.sh` and
`scripts/w362_check_ln_staged.sh` are out of scope and byte-identical to `b87bfa06`.
No `lake` invocation at any point in this lane.

## The ticket

`docs/dyadic/w362-pub-note.md` section T2.d lists six ledger items that have a Lean source
(its T1.a table) but no generated display, each naming an exporter that does not exist in
this tree. This lane writes them.

---

## T0. The result in one table

Per item: does a generated display now exist, and **what kind of claim** does its Lean
bridge make? The kind matters more than the count, because the six items are not in the
same state and a uniform "exporter exists" row would hide that.

| Item | Display | Bridge kind | Strength |
|---|---|---|---|
| 1 exact syntax tree | W361 | exported tree + hash | pre-existing |
| 2 two specializations | **not yet** | measured, see T4.b | |
| **3 evaluated Fox Jacobian** | **`w363_ln_input_export.lean` + `w363_ln_input_tex.py`** | 9 rows `record_target` (`rfl` against the record's own field), 5 rows `denotation_theorem` (driver states it, proved from the tree's lemmas) | **the same strength as items 4 and 5** |
| 4, 5 operations, normal matrix | W362 | `rfl` record fields | pre-existing |
| **6 Stokes chain identity** | **`w363_ln_stokes_export.lean` + `w363_ln_stokes_tex.py`** | wiring, clause structure, `rfl` numerics; field binding is `field_statement_identity`, Npc is `degree_normalized_field` | **weaker than items 3, 4 and 5, and the artifact says so** |
| 7 extraspecial Hessian | **not yet** | measured, see T4.a | |
| 8 quadratic normal form | **not yet** | measured, see T4.a | |
| 9 affine phase-cover | **not yet** | measured, see T4.c | |
| 10 hashes | W361/W362 | hashes | pre-existing |

Two of the six named exporters now exist. The other four are measured in T4, which is the
part of this note an owner should read before assuming the remaining work is uniform.

---

## T1. Item 3, the evaluated Fox Jacobian

`scripts/w363_ln_input_export.lean` is an exporter driver with a global `main`, so it stays
outside `GQ2.lean` like the W361 and W362 export executables. It serializes ledger item 3
for the **same seven sectors** that `scripts/w362_ln_fox_export.lean` serializes items 4 and
5 for, so the three items can be read side by side: item 3 is the two-row Jacobian before
any operation, items 4 and 5 are the operations and the reduced target.

### T1.a Nothing is retyped

Item 3 is already concrete Lean data, exactly as items 4 and 5 were. The evaluated rows are
`FoxRowNormalForm` values over `FoxCoeff` trees, and for **nine of the fourteen** rows they
are literally the `target` field of an existing `FoxRowCertificate` whose `colOps` is empty,
i.e. of a record that certifies the evaluated Fox derivative of the actual word with nothing
applied to it. Those nine are bound by `rfl` signature theorems:

```text
lSqUnramWild_target        LSq.lSqWildRowCertUnram        lSqWildRow h
lSqRamWild_target          LSq.lSqWildRowCertRam          lSqWildRow h
lSqScalarWild_target       LSq.lSqWildRowCertSplit        FoxRowNormalForm.single tau
nCompactUnramWild_target   nCompactWildRowCertUnram       nCompactWildRow h
nCompactRamWild_target     nCompactWildRowCertRam         nCompactWildRow h
nCompactUnramTame_target   tameRowCertUnram               tameUnramRow (2+2h)
npcUnramWild_target        Npc.npcWildRowCertUnram        Npc.npcWildRow h r
npcRamWild_target          Npc.npcWildRowCertRam          Npc.npcWildRow h r
npcUnramTame_target        Npc.npcTameRowCertUnram        Npc.tameUnramRow (2+2h)
```

with a `*_colOps = []` twin for each, because "no operation has been applied" is part of
what makes the target the *input* row.

### T1.b The five rows that are not record targets, and why

The tree carries a tame-row `FoxRowCertificate` only at the unramified sectors of N0 and
Npc. **The L family has none at any sector**, and **no family has one at the ramified
sector**, where the tame row is `tameRow n q` and enters through `foxD_tameRelW_of_tameRel`
inside the two-row `verifies` block. So five of the fourteen rows have no record to be the
target of. For those the driver states the denotation theorem itself, at general `n`, proved
from the existing `foxD_tameRelW_*` and `*_toHom_apply` lemmas exactly as the existing
records prove theirs:

```text
tameUnramInput_denote      L unramified and L scalar tame rows
tameRamInput_denote        L ramified and N0 ramified tame rows
npcTameRamInput_denote     Npc ramified tame row
npcTameUnramInput_denote   stated for completeness; the Npc unramified tame row uses the record
```

The artifact records which kind each row is, in a `bridge_kind` field, and the validator
**refuses a relabelling in either direction**: a `denotation_theorem` row may not be
presented as a `record_target`, and a `record_target` row may not be downgraded. The count
nine and five is taken from the generated JSON, not by hand.

### T1.c The universal-row structure is exported, not described

One formal row per family carries the opaque projector atom `P`, and the branch is a
*specialization* of that one row, not a second row: `P` maps to the identity at the
unramified and scalar sectors and to zero at the ramified sectors. The driver exports the
projector value per sector and binds it by `rfl` to `splitEnd` / `ramifiedEnd`, which are
`toEnd t 1` and `toEnd t 0`. So the rendered ramified sector prints the same universal row
as the unramified one, followed by `(Pi=0)`, which is what the Lean actually says.

### T1.d What the rendered rows say

Produced from the records, not transcribed from them:

| Sector | Tame input row | Wild input row |
|---|---|---|
| L unramified | `S^-1 a_tau` | `Pi a_tau + (S^-1 + Pi) a_x0`, at `Pi = I` |
| L ramified | universal tame row | the same row at `Pi = 0`, i.e. `S^-1 a_x0` |
| L scalar | `S^-1 a_tau` | `I a_tau` |
| N0 unramified | `S^-1 a_tau` | `Pi a_tau + (S^-1 + Pi) a_x2`, at `Pi = I` |
| N0 ramified | universal tame row | the same row at `Pi = 0` |
| Npc unramified | `S^-1 a_tau` | `Pi a_tau + (A^-1 + I) a_x0 + (S^-2^r + Pi) a_x2`, at `Pi = I` |
| Npc ramified | universal tame row | the same row at `Pi = 0` |

The universal tame row prints as `S^-1 . (T - I) a_sigma + (S^-1 - N_q(T)) a_tau` with
`N_q(T)` the literal left-nested `normCoeff` sum, the same spelling W362 records for item 5.

These agree with items 4 and 5 in a way worth stating, because it is a check across two
independently generated artifacts rather than a restatement. At L unramified the item-4
operation is `R2 <- R2 + S R1`; applying it to the item-3 rows above gives
`a_tau + (I + S^-1) a_x0 + S S^-1 a_tau = (I + S^-1) a_x0` in characteristic two, which is
item 5's recorded reduced target `(I - S^-1) a_x0`. The same composition works at N0 and at
Npc. **This check is done by reading, not by the checker**: no script verifies it, because
doing so needs the characteristic-two step, and the exporters deliberately carry no
coefficient module.

### T1.e A third naming trap

`Certificates.Npc.tameRelW` is a **second declaration** of the tame relator, distinct from
`Certificates.tameRelW`, same spelling in a different namespace. The Npc denotation theorems
must be stated over the Npc one or the rewrite does not fire. This cost a probe iteration
and joins the two traps w362-pub-note T1.a records.

---

## T2. Item 6, the Stokes chain

`scripts/w363_ln_stokes_export.lean` plus `scripts/w363_ln_stokes_tex.py`, six artifacts at
the same parameters.

### T2.a The measurement this lane owes on item 6

**Item 6 is not like items 3, 4 and 5, and an exporter cannot make it so.**
`StokesDualityCertificate` is a `Prop`: a four-fold conjunction of universally quantified
counting and separation statements over types that do not exist until a recursion frame is
supplied. There is no matrix, no chain complex object and no coefficient tree to serialize.
The driver invents none. What it serializes is the part of item 6 that genuinely is data:

* the **wiring**: which declaration proves the chain, which record consumes it, in which
  field, and at which degree;
* the **clause structure**: the four conjuncts in the conjunction's own order, each with its
  role, and which two of them carry a count;
* the **numeric multipliers the counting clauses assert**, which are literal exponents of
  the `standardNumerics` record, bound by `rfl`:
  `tMult |T| = |T|^(n+1)` and `h1Mult |V| = |V|^n`.

The clause statements themselves stay where W362 put them, in the packet's stored proofs
transcript. Every artifact says so in its own `warning` field, which the validator requires
to be present and nonempty.

### T2.b Proof irrelevance: what a field binding certifies

`StokesDualityCertificate` is a `Prop` and Lean has definitional proof irrelevance, so
`record.stokes = producer` is `rfl` for **any** producer whose type is the field's type.
The binding therefore certifies a **statement identity**: the producer proves exactly the
statement the record's `stokes` field demands, at the record's own parameters. It does
**not** certify that the record was built from that proof term, and nothing in the artifact
should be read as saying so.

This is why the item-6 bridge kind is `field_statement_identity` and deliberately **not**
the `record_target` that items 3, 4 and 5 use for a genuine data field. Treating the two as
the same strength of claim would be the exact error the readiness note warns about, and the
validator refuses a relabelling in either direction.

### T2.c The Npc degree

The Npc producer `npcCand_stokes` is stated at degree `2*h+2`; the record's `stokes` field
is at `2+2*h`. Those two spellings **agree at every numeric instance**, so the exported
degrees look equal at `h = 0` and at `h = 3`, but they are **not definitionally equal at a
variable `h`**, and the record's own field is filled by a tactic block that rewrites along
the equality. The Npc binding kind is therefore `degree_normalized_field`, it names the
normalization theorem, and the driver carries `npcStokes_typeNormalization`, which proves
that the two chain statements are the same `Prop` once the degree is normalized. That is the
Npc analogue of the two `rfl` bindings, and it is a different thing from them.

| Family | Producer | Consumer record, field `stokes` | Binding kind |
|---|---|---|---|
| L | `LSquare.stokesDualityCertificate_of_actionImage` | `LSquare.wordCertificateRN_lSq_of_actionImage` | `field_statement_identity` (`rfl`) |
| N0 | `Instances.WordPhase.wPh_nCand_stokes` | `Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN` | `field_statement_identity` (`rfl`) |
| Npc | `Instances.NpcCandidateStokes.npcCand_stokes` | `Instances.NpcCandidateRN.npcWordCertificateRN_of_determinant` | `degree_normalized_field` |

The L and N0 producers are written as direct terms in their records; the Npc one is not.
`wordCertificateRN_lSq_pow` and `_qOf`, which w362-pub-note T1.a names as the L carriers,
are specializations of `wordCertificateRN_lSq_of_actionImage`, which is where the field is
literally written, so that is what the binding names.

---

## T3. What was staged, and the check

New files, all under `scripts/w363_*` and `generated/general-ln-certificate-staged/`:

| File | What it is |
|---|---|
| `scripts/w363_ln_input_export.lean` | item 3 exporter driver, 27 axiom pins, all standard three or less |
| `scripts/w363_ln_input_tex.py` | item 3 validator, renderer, generator, checker; self-test 48 |
| `scripts/w363_ln_stokes_export.lean` | item 6 exporter driver, 7 axiom pins, all standard three or less |
| `scripts/w363_ln_stokes_tex.py` | item 6 validator, renderer, generator, checker; self-test 51 |
| `scripts/w363_check_ln_staged.sh` | runs `w362_check_ln_staged.sh` unchanged, then the new checks |
| 12 artifacts x 3 files | `*.input.{json,tex,provenance.json}`, `*.stokes.{json,tex,provenance.json}` |

Parameters, chosen to match the W362 Fox artifacts exactly so the items can be read
together: `L h0 q2`, `L h4 q2`, `N0 h0 q2`, `N0 h3 q2`, `Npc h0 q2 r1`, `Npc h3 q2 r2`.
Three sit at the frozen L/N appendix parameters and three sit beyond them.

`scripts/w363_check_ln_staged.sh` extends the W362 script the way the W362 script extends the
W361 one: it runs it unchanged, first, and adds. Neither the W361 nor the W362 check script
is modified, and neither is `scripts/w362_ln_certificate_packet.py`.

### Verification record

`bash scripts/w363_check_ln_staged.sh` from the worktree root, against the shared campaign
cache at Lean 4.31.0-rc2, **exit 0**, 4 minutes 42 seconds. No `lake` invocation. It
reproduces, in order, `W361_STAGED_CHECK_PASS`, then every W362 line with **every recorded
hash identical to the value in w362-pub-note**, including the six Fox hashes and the six
packet hashes, then:

```text
LN_INPUT_SELF_TEST_PASS|48
LN_STOKES_SELF_TEST_PASS|51
STAGED_LN_INPUT_CHECK|Lean-replayed|L-input-h0-q2|fe015c8a...
STAGED_LN_INPUT_CHECK|Lean-replayed|L-input-h4-q2|98495974...
STAGED_LN_INPUT_CHECK|Lean-replayed|N0-input-h0-q2|5d939687...
STAGED_LN_INPUT_CHECK|Lean-replayed|N0-input-h3-q2|7c859f7d...
STAGED_LN_INPUT_CHECK|Lean-replayed|Npc-input-h0-q2-r1|e838c51b...
STAGED_LN_INPUT_CHECK|Lean-replayed|Npc-input-h3-q2-r2|f1e45d5d...
STAGED_LN_STOKES_CHECK|Lean-replayed|L-stokes-h0-q2|cfca77c1...
STAGED_LN_STOKES_CHECK|Lean-replayed|L-stokes-h4-q2|4b3210d2...
STAGED_LN_STOKES_CHECK|Lean-replayed|N0-stokes-h0-q2|fd1f94c2...
STAGED_LN_STOKES_CHECK|Lean-replayed|N0-stokes-h3-q2|eef6d9d9...
STAGED_LN_STOKES_CHECK|Lean-replayed|Npc-stokes-h0-q2-r1|0c7552df...
STAGED_LN_STOKES_CHECK|Lean-replayed|Npc-stokes-h3-q2-r2|a7de4aa6...
W363_LN_STAGED_CHECK_PASS (staged proposals only: not owner approval, not a manifest entry, not a gate)
```

**The frozen hashes still reproduce.** The three frozen word hashes that w362-pub-note T3.a
fact 4 identifies as the single most important fact for the decision (`d129037c...` for
`rawLsq_n1`, `a940b6ad...` for `rawNCompact_alpha2_h0`, `08b7742c...` for
`rawNpc_a2_r1_eta1_1_h0`) are carried by the W362 packets, which this run replays unchanged
and byte for byte.

What this run does **not** establish, unchanged from W362: it is not a fresh full-repository
build, not a transitive build attestation, and not a hash-gate run. The probe imports
existing olean artifacts, so the direct-source provenance sidecars do not prove that those
bytes produced those artifacts.

---

## T4. The four remaining items, measured

This is the part of the ticket that says: if an item's Lean source turns out not to state
what a display needs, record the exact gap. Here is that record, read from the sources.

### T4.a Items 7 and 8 are parameterized over data the lane may not select

Item 7's carriers (`LSqStokes.hessRelZ_lSq`, `hessRelZ_nCompact`,
`hessRelZ_npcW_evenPhiNormal`, `hessRelZ_npcW_evenTwistedNormal`) are **theorems**, not
records with data fields. Each states an identity of the shape

```text
hessRelZ (mark) (kappa0Cocycle dat hdat) E E2 w
  = q(leading slot) + polar q (slot, slot') + sum over j of polar q (u_j, v_j)
```

at an arbitrary marking and resolver, with one slot hypothesised zero (`x0` for L, `x2` for
N0). There is nothing to serialize by `rfl`. A display is still reachable, by a route item 6
could not use: the driver can **restate the identity in the shape it serializes and
discharge it by the existing theorem**, so a wrong transcription cannot compile. That is a
third bridge kind, weaker than `record_target` and stronger than prose, and it is the honest
shape for item 7. It is not written in this lane.

Item 8's carriers (`LHessianCertificates.unramifiedHessian` / `.ramifiedHessian`,
`CompactNHessianCertificates.*`, `NpcHessianCertificates.npcUnramifiedHeadHessian`,
`nonempty_npcRamifiedHeadHessian`, `NpcUnramifiedComparison.wPnpcPhiCoordsEquiv`) are
records of type `SourceOddHessian`, and they take a descent datum `DD`, a factor set `base`,
a projection `pi`, a module `DD.Vmod` with its topology and action, a simplicity hypothesis
and a cardinality `Nat.card DD.Vmod = 2^(2m)`. **A `rfl` signature theorem against such a
record requires instantiating all of it, which means selecting a coefficient module, which
this lane is forbidden to do.** A signature theorem quantified over all of them is possible
and would carry the record's existence, not its content.

The content of item 8 that *is* data is the **Gauss sign and exponent** those two records
establish on the way: `gaussSum(lSqWallHandlePhase ...) = (-1) * 2^(m*(2h+1))` unramified
and `= (+1) * 2^(m*(2h+1))` ramified. Those appear inside the two proofs as a `have`, not as
named standalone theorems, so an exporter would have to name them first. **That is a
concrete, small piece of Lean work, and it is the thing to do before writing item 8's
exporter**, not after.

### T4.b Item 2 is data-shaped and is the best of the four

`Words.pro2_nCompact` states that the pro-2 specialization of the compact-N word **is an
explicit `PWord`**:

```text
pro2 (nCompactW alpha h) = prodList [ x0^(2+2^alpha), [x0,x1], (x2^sigma)^-1,
                                      prodList [x2, 1], handlesW h ]
```

and `Words.Npc.pro2_npcW` is its procyclic twin. The L side is different:
`eval_pro2_lSqW_eq_sqRelWord` lands on `SqCore.sqRelWord` read through a letter
correspondence, not on an explicit list. So item 2's pro-2 half is a serializable syntax
tree of exactly the kind item 1 already renders at N0 and Npc, and a driver can export the
*value* `pro2 w` rather than a transcription of it; at L it is a different shape and needs
its own treatment. The tame half is the `tameSpecialization` field of the word certificate
records, which is the item-6 situation again: a field whose binding is a statement identity.

**Item 2 is therefore the most valuable of the four remaining, and it splits three ways:
genuine data at N0 and Npc, a correspondence at L, and a field binding for the tame half.**
A single uniform item-2 display would hide that split.

One caution for whoever writes it: item 2 is also the item that carries the **standing-axiom
class**. The three field-selection adapters
`FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_{l,n0,npc}` are not standard-three,
they carry four documented standing inputs each, and W362 pinned them in their own class and
printed their full axiom list. Any item-2 exporter must keep them in that class and must not
fold them into a standard-three count.

### T4.c Item 9 is item 6 again, with the multipliers this lane deliberately left out

`AffineDeterminantCertificate` is, like `StokesDualityCertificate`, a `Prop` defined by a
conjunction of quantified clauses, consumed as the `determinant` field of the same word
certificate records. It has **two** clauses, not four: an unramified Gauss residue clause
using `SN.gaussUnram m` and a ramified one using `SN.gaussRam m`. So the item-9 exporter is
the item-6 exporter with a different clause table and a different multiplier pair,
`gaussUnram m = (-1)^n * 2^(n*m)` and `gaussRam m = 2^(n*m)`.

**This lane left those two multipliers out of the item-6 artifact on purpose**: they are
item 9's numerics, not item 6's, and item 6 exports only the `tMult` and `h1Mult` its own
clauses use. An item-9 exporter should export them with `rfl` bridges of the same shape, and
will have to carry a **sign** as well as an exponent, which the item-6 multiplier record
does not.

### T4.d The honest summary of the remaining work

w362-pub-note T2.d said the six names are "exactly the size of the remaining publication
work for the L/N families". After writing two of them, that is **half right**. The remaining
four are not four more of the same:

1. **Item 2** is largely data and should be written next.
2. **Item 9** is a known shape, item 6's, and is cheap.
3. **Item 7** needs a restatement-style bridge, a kind no exporter in the tree uses yet.
4. **Item 8** needs *Lean work first*: the Gauss sign and exponent must be named as
   standalone theorems before an exporter can cite them, and a full `rfl` binding to its
   records is out of reach without selecting a coefficient module.

---

## T5. Packets

The six W362 packets are **not regenerated in this lane**, and they still carry their
original TODO text for items 3 and 6, which now names exporters that exist. This is a known
staleness and it is deliberate: regenerating them means either modifying
`scripts/w362_ln_certificate_packet.py`, which changes the recorded W362 packet hashes, or
adding a second composer that owns the same paths, which w362-pub-note T3.a fact 6 rules
out. **Which of those two the packets take is an owner decision**, number 13 below. Until it
is taken, the W362 packets and the W363 artifacts are two separate staged sets, both checked
by `scripts/w363_check_ln_staged.sh`, and the packets' item 3 and item 6 TODO text should be
read as "no display *in this packet*", not as "no display anywhere".

Note for that decision: the W362 packet hashes are **not frozen identifiers**. W362's own
note calls them "a locator", says each packet's `.files.json` is the authority for its own
files, and recomputes the packet hash on every check. The frozen identifiers are the three
word hashes in T3, and those are untouched either way.

## T6. Owner decisions this lane adds

The twelve in w362-pub-note T3.c stand unchanged. This lane adds:

13. Whether the W362 packets are regenerated to carry the new item 3 and item 6 displays,
    and if so by modifying the W362 composer (which changes its recorded packet hashes, none
    of which is a frozen identifier) or by a new composer with its own paths.
14. Whether a `field_statement_identity` bridge is acceptable in a published appendix at
    all, given that proof irrelevance makes it a statement-level and not a proof-level
    claim, or whether item 6 must instead be published as checked declarations the way W362
    published it.
15. Whether the restatement-style bridge sketched in T4.a for item 7 is acceptable, since no
    exporter in the tree uses that kind yet.
16. Whether the Gauss sign and exponent for item 8 may be named as new standalone theorems
    in a module under `GQ2/`, which is outside every exporter lane's mandate as currently
    drawn.
17. Whether `scripts/w363_check_ln_staged.sh` is folded into the W361 or W362 script or into
    `scripts/check_dyadic.sh`, and at which gate number. This lane left both earlier scripts
    unmodified so that the recorded W361 and W362 check semantics did not change.

## What this lane deliberately did not do

* It did not modify `generated/hash-manifest.json`, any `generated/appendix/*.tex`,
  `GQ2.lean`, any module under `GQ2/`, `scripts/w361_check_staged.sh`,
  `scripts/w362_check_ln_staged.sh`, `scripts/w362_ln_certificate_packet.py`, or
  `scripts/check_dyadic.sh`.
* It did not run `lake` in any form.
* It did not relabel any staged artifact as adopted, and every artifact it wrote embeds
  `status: "STAGED"` with a validator that refuses any other value.
* It did not treat `RawWord.shadow` as W361's semantic `tameShadow`.
* It did not select a coefficient module, marking, field, resolver, `eta` or source
  certificate in any exporter.
