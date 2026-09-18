# W366-GAUSSEXPORT: wiring item 8's normal-form display rows to the named Gauss theorems

**Status: staged proposal only. Nothing in this lane is owner adoption, acceptance, census
amendment, appendix migration, or release authorization.** Staged artifacts are proposals.
No frozen identifier or hash is changed, no historical verification report is relabelled as
current, and no universal frozen-M placement claim is made or revived.

Worktree `cla/worktrees/w366-gaussexport`, branch `claude/w366-gaussexport`, base `9dd8a307`,
Lean 4.31.0-rc2.  No `lake` invocation at any point in this lane.  Verified byte-identical to
`9dd8a307`: `generated/hash-manifest.json`, every `generated/appendix/*.tex`, `GQ2.lean`,
every module under `GQ2/`, `scripts/check_dyadic.sh`, `scripts/w361_check_staged.sh`,
`scripts/w362_check_ln_staged.sh`, `scripts/w363_check_ln_staged.sh`,
`scripts/w362_ln_certificate_packet.py`, every W361/W362/W363 driver and generator, and every
W361/W362/W363 staged artifact including all six certificate packets.

## The ticket, and the result

`docs/dyadic/w363-pub2-note.md` T6 left ledger item 8 split: its **coordinate** half binds at
`record_target` against the change of variables' own `Equiv` fields, and its **normal-form**
half was `named_but_unbound`, because the Gauss sign and exponent the normal-form records
establish on the way appeared only as a `have` inside two proofs.  Naming them was owner
decision 16.  `docs/dyadic/w365-gauss-note.md` named them, in
`GQ2/Dyadic/Instances/GaussPhaseValues.lean`.  **This lane wires the five item-8 sector rows
to those theorems**, and regenerates item 8 whole, both halves, beside each of the six W362
packets, without touching the W362 composer or any packet hash.

---

## T1. What was staged

Four new files under `scripts/w366_*` and 36 new artifact files in
`generated/general-ln-certificate-staged/`.  Nothing else was created or modified.

| file | role |
|---|---|
| `scripts/w366_ln_gauss_export.lean` | the driver: 11 signature theorems plus `exportMain`, and the serialization |
| `scripts/w366_ln_gauss_tex.py` | the generator: validates and renders the serialization, 63 self-test assertions |
| `scripts/w366_ln_item8_overlay.py` | the **second composer**: the item-8 overlays, 56 self-test assertions |
| `scripts/w366_check_ln_staged.sh` | the extended check, which runs `w363_check_ln_staged.sh` unchanged first |

Parameters, chosen to match the W362 Fox and W363 item artifacts exactly so that all the
items read together: `L h0 q2`, `L h4 q2`, `N0 h0 q2`, `N0 h3 q2`, `Npc h0 q2 r1`,
`Npc h3 q2 r2`.

### T1.a The driver, and the two bridge kinds inside one artifact

`scripts/w366_ln_gauss_export.lean` serializes, per item-8 sector row, three things, and
**they do not all carry the same kind**.  The artifact keeps them apart and the validator
refuses a relabelling in either direction.

* **The printed sign and the printed exponent: `record_target`.**  Six theorems,
  `lUnramSign`, `lUnramDegree`, `lRamSign`, `lRamDegree`, `compactSign`, `compactDegree`,
  each `rfl` against a field of `GaussValCell`, which is data with explicit fields.  A
  seventh, `cellValue`, pins that the displayed integer is those two fields and nothing else:
  `c.value m = c.sign * 2 ^ (m * c.degree)`, by `rfl`.  This is the same strength as item 8's
  coordinate half and as items 3, 4 and 5.
* **The value equation: `restated_identity`.**  Four theorems, `lUnramValue`, `lRamValue`,
  `compactValue`, `npcValue`, each restating `gaussSum <endpoint> = (<cell>).value m` through
  the named cell and discharged by the tree's own theorem from `GaussPhaseValues`.  **A wrong
  cell does not compile.**  This is kind 3 of the PUB2 taxonomy, the kind item 7 and item 2's
  pro-2 half already use.

The `L` rows are quantified over `Bg`, `D`, `DD`, `Cbar`, the factor set, the projection and
the representation, at exactly the hypotheses `GaussPhaseValues` takes: **no coefficient
module is selected**, so the driver stays inside the PUB2 scope rule.

Every pin is standard three or less.  `#print axioms` for all twelve declarations:

```text
lUnramSign lUnramDegree lRamSign lRamDegree compactSign compactDegree   no axioms
cellValue                                                              propext
lUnramValue lRamValue compactValue npcValue exportMain                  standard three
```

Those twelve are the eleven theorems and `exportMain`, which is the W363 driver convention:
the serialization helpers (`schema`, `bracket`, `optString`, `rowJson`, `lRows`, `n0Rows`,
`npcRows`, `payload`, `envelope`, the namespace-prefix and note strings) are all inside
`exportMain`'s transitive closure, so the `exportMain` pin covers every one of them and an
axiom hiding in a helper could not escape it.

Zero errors and zero warnings under `bash scripts/w361_lean_runner.sh
scripts/w366_ln_gauss_export.lean`.  No `sorry`, no `native_decide`, no new axiom, no
resource option, no `set_option` of any kind.  The driver carries a global `main` and stays
outside `GQ2.lean`, like every W361/W362/W363 export executable.

### T1.b What the validator refuses

The generator recomputes rather than trusts.  Beyond the usual envelope and hash checks it
refuses, each with its own self-test mutation:

* a `sign_binding` other than `record_target`, in **either** direction, and a `value_binding`
  other than `restated_identity`: the two halves of a cell do not carry the same kind, and
  neither may be promoted or demoted;
* a `record_binding` other than `named_but_unbound`: **naming is not binding**, and the
  normal-form records are still unreachable;
* **an invented record route for the exponent.**  `degree_record_route` must be `null` in
  every row, because no named `baseDim` theorem exists anywhere in the tree;
* **an invented second sign route.**  Only the two `L` rows have one; a `second_sign_route`
  added to an `N0` or `Npc` row, or removed from an `L` row, is refused;
* a printed sign or printed exponent that is not the row's own.  Both are recomputed: the
  sign from the row, the exponent from the handle rank, `2h+1` at `L` and `2h+2` at the three
  even-degree rows.  `sign=True` is refused too, since `bool` is not `int` here.

### T1.c The overlay's before column is per family

The overlay pins item 8's binding kinds before and after, and **the `before` column is a
function of the family, not a constant**.  W365 corrected w363-pub2-note on exactly this
point: the `L` rows' printed sign already had a `record_target` route through the pre-existing
`LHessianCertificates.unramifiedHessian_baseSign` and `.ramifiedHessian_baseSign`, so a
uniform `named_but_unbound` before column would repeat the overstatement W365 found.  For `L`
this lane therefore adds a **second, independent** route to the display cell, which a
validator may check agrees with the first; for `N0` and `Npc` it adds the first.  A constant
`sign_route_note` carries the caveat, the validator refuses to let it be dropped, and it
refuses an `L` overlay carrying the `N0` table or the reverse.

### T1.d The packets: an OVERLAY, not a regeneration. Which, and why

**This lane produces `packet-*.item8-w366.tex` overlays.  It does not produce a separate
`packets-w366/` set, and it does not regenerate the W362 packets.**

W363-PUB2 T9 declined to regenerate them because doing so means either modifying
`scripts/w362_ln_certificate_packet.py`, which changes its recorded packet hashes, or adding
a second composer that owns the same paths, which w362-pub-note T3.a fact 6 rules out.  The
overlay honours both constraints at once: it owns paths **no other producer writes**
(`*.item8-w366.{json,tex,provenance.json}`), the W362 check globs only `*.packet.json` and the
four files each packet's own manifest covers, so the overlay files are invisible to it, and
the W362 composer is not imported for anything except its `digest`.

The overlay is not a copy.  For each packet it

1. reads the packet, **re-derives the packet's recorded hash** from the packet's stored
   payload through the W362 composer's own `digest`, and pins it.  If a packet is ever
   regenerated underneath the overlay, the check fails and names it;
2. reads the packet's own item-8 title, paragraphs, references and TODO.  **Nothing is
   retyped**;
3. re-renders **both halves** of item 8 from validated artifact JSON, the coordinate half
   through `w363_ln_coordinate_tex.render_tex` and the normal-form half through
   `w366_ln_gauss_tex.render_tex`, rather than copying the generated `.tex` bytes;
4. prints the before/after binding-kind table of T3 below, and the residual TODOs;
5. re-derives its whole payload on every check, so a drift in the packet, in either artifact,
   or in the overlay's own text is refused.

The packet's own text still carries its original item-8 TODO, because the packet is not
edited.  The overlay says so in its own `warning` field: the two files are to be read
together, and **whether the packets are instead regenerated in place remains W363-PUB2 owner
decision 13**, untouched by this lane.

---

## T2. The extended check

`scripts/w366_check_ln_staged.sh` extends the W363 script exactly the way the W363 script
extends the W362 one and the W362 script extends the W361 one: it runs it unchanged, first,
and adds.  None of the three earlier check scripts is modified, and neither is
`scripts/w362_ln_certificate_packet.py`.

### Verification record

`bash scripts/w366_check_ln_staged.sh` from the worktree root, against the shared campaign
cache at Lean 4.31.0-rc2, **exit 0**, 7 minutes 56 seconds (476 s).  No `lake` invocation.  It
reproduces, in order:

```text
W361_STAGED_CHECK_PASS (not owner approval or a transitive fresh-build certificate)
W362_LN_STAGED_CHECK_PASS (staged proposals only: ...)
W363_LN_STAGED_CHECK_PASS (staged proposals only: ...)
W366_LN_STAGED_CHECK_PASS (staged proposals only: ...)
```

**Every W362 hash reproduces exactly the value w362-pub-note and w363-pub2-note record.**  The
six Fox hashes `8100f623 2dc399b5 ede1c9b7 7a280f1c 066b3a46 eb4ee748` and the six packet
hashes `7f19d17e f98de22b 1bb59b94 b54126b5 6cf3a39e 97d13c27`.  **So the frozen word hashes
still reproduce**: `d129037c...` for `rawLsq_n1`, `a940b6ad...` for `rawNCompact_alpha2_h0`
and `08b7742c...` for `rawNpc_a2_r1_eta1_1_h0`.

**Every W363 hash reproduces exactly the value w363-pub2-note T7 records**, all 36, including
the six `coordinate` hashes `352edf53 4d1b5d25 0cd8d35d ca71e4ef afcd8f62 8ce388d9` that item
8's other half depends on.

The 12 new hashes, first eight hex digits, in check order:

```text
gauss    L-h0 bf76ea80  L-h4 8bed0292  N0-h0 f7c643df  N0-h3 d90b2433  Npc-h0 8abe7ce5  Npc-h3 b23d4953
overlay  L-h0 804d90c8  L-h4 89277470  N0-h0 0211b5d7  N0-h3 2fd8c30d  Npc-h0 d00c9413  Npc-h3 e9552408
```

Each overlay line also prints the packet hash it pins, followed by `unchanged`:

```text
STAGED_LN_ITEM8_OVERLAY_CHECK|packet-L-h0|804d90c8...|packet 7f19d17e... unchanged
```

Self-tests: `LN_GAUSS_SELF_TEST_PASS|63` and `LN_ITEM8_OVERLAY_SELF_TEST_PASS|56`.  All six
gauss artifacts are `Lean-replayed`, i.e. the driver is recompiled and its bytes compared, not
merely re-read.  The overlay check is deliberately not Lean-replayed: it has no Lean of its
own, and everything it could replay is replayed by the two checks it sits behind.

Verified separately, by `git diff` against `9dd8a307`: the lane's diff is **100% additions**.
No existing file in the repository is modified by any of the six commits.

What this run does **not** establish, unchanged from W362 and W363: it is not a fresh
full-repository build, not a transitive build attestation, and not a hash-gate run.  The probe
imports existing olean artifacts, so the direct-source provenance sidecars do not prove that
those bytes produced those artifacts.

---

## T3. The per-item table, and item 8's binding kinds before and after

### T3.a The ten-item table

w363-pub2-note T0's table with item 8 updated.  **Only item 8 changed**; every other row is
reproduced unchanged and is not re-verified here beyond the check in T2 replaying it.

| Item | Exporter | Bridge kind of its display | Changed here |
|---|---|---|---|
| 1 exact syntax tree | W361 | exported tree plus hash | no |
| 2 two specializations | W363 | pro-2 `restated_identity`; tame `field_statement_identity` | no |
| 3 evaluated Fox Jacobian | W363 | 9 rows `record_target`, 5 rows `denotation_theorem` | no |
| 4, 5 operations, normal matrix | W362 | `rfl` record fields | no |
| 6 Stokes chain identity | W363 | `field_statement_identity`; Npc `degree_normalized_field` | no |
| 7 extraspecial Hessian | W363 | `restated_identity` | no |
| **8 quadratic normal form** | W363 **+ W366** | coordinate half `record_target`; **sign and exponent `record_target`, value equation `restated_identity`**; records `named_but_unbound` | **yes** |
| 9 affine phase-cover | W363 | `field_statement_identity` | no |
| 10 hashes | W361/W362 | hashes | no |

Item 8 now carries **three** of the five PUB2 kinds at once, which no other item does.  That
is the reason the artifact keeps them in separate fields rather than reporting one kind per
item: a single "item 8 is `record_target`" line would be false about the value equation, and a
single "item 8 is `named_but_unbound`" line would be false about everything except the
records.

### T3.b Item 8's cells, before and after

`before` is the state at base `9dd8a307`, i.e. after W365 named the theorems but before any
exporter cited them.  **The `before` column is per family and deliberately not uniform**, and
the overlay pins it that way: W365 corrected PUB2 on exactly this point, and repeating the
uniform label would repeat the overstatement W365 found.

| item-8 cell | before | after | carrier of the `after` |
|---|---|---|---|
| the change of variables, 8 bindings | `record_target` | `record_target`, unchanged | the `Equiv`'s own `toFun` and `invFun` |
| the printed Gauss sign, **L** rows | `record_target` (via `_baseSign`) | `record_target`, now **two independent routes** | `GaussValCell.sign` by `rfl`, plus `unramifiedHessian_baseSign` / `ramifiedHessian_baseSign` |
| the printed Gauss sign, **N0 and Npc** rows | `named_but_unbound` | `record_target` | `GaussValCell.sign`, by `rfl` |
| the printed Gauss exponent, all 5 rows | `named_but_unbound` | `record_target` | `GaussValCell.degree`, by `rfl` |
| the Gauss value equation, all 5 rows | `named_but_unbound` | `restated_identity` | `lUnramValue`, `lRamValue`, `compactValue`, `npcValue` |
| the displayed integer's shape | nothing at all | `record_target` | `cellValue`: `c.value m = c.sign * 2 ^ (m * c.degree)`, by `rfl` |
| `SourceOddHessian`, `SourceCompactHessian`, `SourceWallHessian` | `named_but_unbound` | `named_but_unbound`, **unchanged** | nothing reaches them |

### T3.c The five rows, and what each one binds

| row | endpoint | cell | sign | exponent | value equation | second sign route |
|---|---|---|---|---|---|---|
| `graph_normal_form_unramified` | `LSquare.lSqWallHandlePhase` | `gaussValLUnramCell` | `-1` | `2h+1` | `gaussValLUnramifiedCell` | `LHessianCertificates.unramifiedHessian_baseSign` |
| `graph_normal_form_ramified` | `LSquare.lSqWallHandlePhase` | `gaussValLRamCell` | `+1` | `2h+1` | `gaussValLRamifiedCell` | `LHessianCertificates.ramifiedHessian_baseSign` |
| `compact_normal_form` | `WordPhase.wPhCompactWallHandlePhase` | `gaussValCompactCell` | `+1` | `2h+2` | `gaussValCompactCellEq` | **none** |
| `unramified_full_offset` | `WordPhaseWallHandleCertificates.wallHandlePhase` | `gaussValCompactCell` | `+1` | `2h+2` | `gaussValNpcCellEq` | **none** |
| `ramified_full_offset` | `WordPhaseWallHandleCertificates.wallHandlePhase` | `gaussValCompactCell` | `+1` | `2h+2` | `gaussValNpcCellEq` | **none** |

Three cells, five rows: the two `L` branches differ in sign because `2h+1` is odd, and the
three even-degree rows share one cell because at even degree the unramified and the ramified
target are the same integer.  The compact-`M` rows, which item 8 does not list but which share
the compact endpoint, are served by the same cell.

### T3.d The cells that still cannot bind: explicit named TODOs

Each of these is carried in the artifacts themselves, not only here, and each has a validator
mutation that refuses to let it be quietly filled in with an invented name.

1. **`GQ2.Dyadic.Instances.NpcHessianCertificates.nonempty_npcRamifiedHeadHessian` is a
   `Nonempty`, not a record value.**  The `ramified_full_offset` row's Gauss cell is supplied
   by the endpoint theorem `gaussValNpcCellEq`, which is fine and is what the row binds, but
   **that row can never gain a second `record_target` route through its own record**, because
   there is no record to project: `Nonempty` carries no field.  This is the one cell in item 8
   whose second route is blocked by the **shape of its carrier** and not by a missing lemma,
   and adding a `baseSign` theorem to `NpcHessianCertificates` would not unblock it.
2. **No named `baseDim` theorem exists anywhere in the tree**, so the printed exponent has no
   record-field route in **any** of the five rows: every `degree_record_route` is `null`, and
   the validator refuses a non-null value.  Supplying one is four small
   `... .affinePhase.baseDim = ...` `rfl` theorems in the three certificate modules, which no
   exporter lane may add.  W365's residual item 5 stands: anyone adding them should check
   `LBoundaryHessianCertificates` first for the spelling the boundary lane expects.
3. **No named `baseSign` theorem exists outside `L`.**  The fact does hold by `rfl` at N0 and
   Npc, and is supplied inline as a `rfl` argument to `gaussSum_pi_of_baseSign_one` at
   `GQ2/Dyadic/Certificates/N0.lean:1044` and `GQ2/Dyadic/Certificates/Npc.lean:1570`, but an
   inline argument is not a citable declaration, so those three rows have one route and not
   two.
4. **The normal-form records themselves stay `named_but_unbound`.**  `SourceOddHessian`,
   `SourceCompactHessian` and `SourceWallHessian` are still unreachable without instantiating
   a coefficient module, which no exporter lane may do.  What changed is that the Gauss cells
   **no longer have to wait for them**: they are supplied by theorems about the *endpoint
   phase function*, which is quantified over the coefficient group.  That is why one artifact
   carries two kinds for one displayed number.

---

## A correction to w365-gauss-note

**w365-gauss-note "What remains" item 1 is already closed at this base.**  It says
`GaussPhaseValues.lean` "is not in `GQ2.lean`" and calls adding the import the only thing
standing between those theorems and a gated build.  At base `9dd8a307` the import is present:
`GQ2.lean:891`, added by commit `a2995b54 register GaussPhaseValues`.  So the module is in the
build graph, the theorems this lane cites are gate-reachable, and **this lane did not need to
edit `GQ2.lean` and did not**.

W365's "What remains" item 2, that no exporter cites the theorems, is what this lane closed.

---

## What remains

1. **Owner decision 16 can now be answered on its whole question.**  W365 answered the narrow
   half, the naming.  This lane answers the other half: an exporter does cite them, the cells
   bind at `record_target`, and the value equation binds at `restated_identity`.  What
   decision 16 does **not** cover, and what is still open, is the `named_but_unbound` status
   of the records themselves.
2. **Owner decision 13 is untouched.**  The overlay is a deliberate third option beside the
   two PUB2 T9 named: it neither modifies the W362 composer nor owns a path the composer
   writes.  If the owner instead regenerates the packets in place, the overlays become
   redundant and their check will *fail loudly* rather than silently agree, because each pins
   the packet hash it was built against.  That is the intended behaviour, but it means the
   overlays must be regenerated or removed in the same change.
3. **Owner decision 17 gains a fourth script.**  `scripts/w366_check_ln_staged.sh` is now the
   outermost of four nested opt-in checks.  Folding them is still an owner decision and this
   lane left all three earlier scripts unmodified.
4. **A second route for the exponent, and for the N0 and Npc signs**, is the next small piece
   of Lean: four `baseDim` `rfl` theorems and two or three `baseSign` ones, in modules under
   `GQ2/`, which no exporter lane may touch.  The exporter side is ready for them: the
   `degree_record_route` and `second_sign_route` fields exist, are `null`, and are validated.
5. **What this run does not establish**, unchanged from W362 and W363: it is not a fresh
   full-repository build, not a transitive build attestation, and not a hash-gate run.  The
   probe imports existing olean artifacts, so the direct-source provenance sidecars do not
   prove that those bytes produced those artifacts.

## What this lane deliberately did not do

* It did not modify `generated/hash-manifest.json`, any `generated/appendix/*.tex`,
  `GQ2.lean`, any module under `GQ2/`, `scripts/check_dyadic.sh`,
  `scripts/w361_check_staged.sh`, `scripts/w362_check_ln_staged.sh`,
  `scripts/w363_check_ln_staged.sh`, `scripts/w362_ln_certificate_packet.py`, any other W361,
  W362 or W363 driver or generator, or any W361/W362/W363 staged artifact.
* It did not regenerate a packet, rewrite a packet file, or recompute a packet hash into a new
  value.  It reproduced all six and pinned them.
* It did not run `lake` in any form.
* It did not relabel any staged artifact as adopted: every artifact embeds `status: "STAGED"`
  with a validator that refuses any other value.
* It did not select a coefficient module, marking, field, resolver, `eta` or source
  certificate: every signature theorem is quantified over them.
* It did not present the value equation as a record target, or the records as bound.
