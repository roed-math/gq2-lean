# W363-PUB2 lane note: the six missing L/N exporters

**Status: staged proposal only. Nothing in this lane is owner adoption, acceptance,
census amendment, appendix migration, or release authorization.** Staged artifacts are
proposals. No frozen identifier or hash is changed, no historical verification report is
relabelled as current, and no universal frozen-M placement claim is made or revived.

Worktree `cla/worktrees/w363-pub2`, branch `claude/w363-pub2`, base `b87bfa06`,
Lean 4.31.0-rc2. Verified byte-identical to `b87bfa06`: `generated/hash-manifest.json`,
every `generated/appendix/*.tex`, `GQ2.lean`, every module under `GQ2/`,
`scripts/w361_check_staged.sh`, `scripts/w362_check_ln_staged.sh`,
`scripts/w362_ln_certificate_packet.py`, `scripts/check_dyadic.sh`, and every W362 staged
artifact. No `lake` invocation at any point in this lane.

## The ticket, and the result

`docs/dyadic/w362-pub-note.md` section T2.d lists six ledger items that have a Lean source
(its T1.a table) but no generated display, each naming an exporter that **does not exist in
this tree**. **All six now exist**, with six artifacts each, and one extended check runs all
of them at exit 0.

---

## T0. The result in one table

The count is the least interesting part. What an owner needs is **what kind of claim each
display's Lean bridge makes**, because the six items are not in the same state and a uniform
"exporter exists" row would hide that. Five distinct bridge kinds occur; T1 orders them.

| Item | Exporter written here | Bridge kind of its display | Strength |
|---|---|---|---|
| 1 exact syntax tree | W361 | exported tree plus hash | pre-existing |
| **2 two specializations** | `w363_ln_specialization_*` | pro-2 half `restated_identity`; tame half `field_statement_identity` | **splits: see T5** |
| **3 evaluated Fox Jacobian** | `w363_ln_input_*` | 9 rows `record_target`, 5 rows `denotation_theorem` | **same as items 4, 5** |
| 4, 5 operations, normal matrix | W362 | `rfl` record fields | pre-existing |
| **6 Stokes chain identity** | `w363_ln_stokes_*` | `field_statement_identity`; Npc `degree_normalized_field` | **weakest of the six** |
| **7 extraspecial Hessian** | `w363_ln_hessian_*` | `restated_identity` | middle |
| **8 quadratic normal form** | `w363_ln_coordinate_*` | coordinate half `record_target`; records `named_but_unbound` | **splits: see T6** |
| **9 affine phase-cover** | `w363_ln_cover_*` | `field_statement_identity` | same as item 6 |
| 10 hashes | W361/W362 | hashes | pre-existing |

---

## T1. The five bridge kinds, strongest first

This is the part to read before deciding what may be published. Every artifact carries its
own bridge kind in a machine-checked field, and **every validator refuses a relabelling in
either direction**: a weaker bridge cannot be presented as a stronger one, and a stronger one
cannot be quietly downgraded.

1. **`record_target`.** The serialized value is definitionally the field of an existing
   record, by `rfl`. Items 3, 4, 5 and item 8's coordinate half. This is the only kind where
   the display *is* the Lean data.
2. **`denotation_theorem`.** No record carries the value, so the driver states the
   denotation itself and proves it from the tree's lemmas, exactly as the neighbouring
   records prove theirs. Five rows of item 3.
3. **`restated_identity`.** The carrier is a theorem, not a record. The driver restates the
   identity through a named decomposition and discharges the restatement by the tree's own
   theorem, so **a wrong decomposition does not compile**. Item 7, and item 2's pro-2 half.
4. **`field_statement_identity`.** The carrier is a `Prop` field of a record. Lean has
   definitional proof irrelevance, so `record.field = producer` is `rfl` for *any* producer
   whose type is the field's type. What is certified is that the producer proves **exactly
   the statement the field demands, at the record's own parameters** -- and **not** that the
   record was built from that proof term. Items 6 and 9, and item 2's tame half.
5. **`named_but_unbound`.** A declaration is named and nothing is claimed about it. Item 8's
   normal-form records. **Naming is not binding**, and the validator enforces that the label
   stays.

One kind is not on the list because no exporter here uses it: nothing in this lane
substitutes a formula for a value the Lean does not state. Where a display genuinely needed
something the Lean does not carry, the artifact says so in its own `warning` field, which
every validator requires to be present and nonempty.

---

## T2. Item 3, the evaluated Fox Jacobian

`scripts/w363_ln_input_export.lean` serializes item 3 for the **same seven sectors** that
`scripts/w362_ln_fox_export.lean` serializes items 4 and 5 for, so the three items read side
by side: item 3 is the two-row Jacobian before any operation, items 4 and 5 are the
operations and the reduced target.

### T2.a Nothing is retyped

Item 3 is already concrete Lean data, exactly as items 4 and 5 were: `FoxRowNormalForm`
values over `FoxCoeff` trees. For **nine of the fourteen** rows they are literally the
`target` field of an existing `FoxRowCertificate` whose `colOps` is empty, i.e. of a record
that certifies the evaluated Fox derivative of the actual word with nothing applied to it:

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

### T2.b The five rows that are not record targets, and why

The tree carries a tame-row `FoxRowCertificate` only at the unramified sectors of N0 and
Npc. **The L family has none at any sector**, and **no family has one at the ramified
sector**, where the tame row is `tameRow n q` and enters through `foxD_tameRelW_of_tameRel`
inside the two-row `verifies` block. For those five the driver states the denotation theorem
itself, at general `n`, proved from the existing `foxD_tameRelW_*` and `*_toHom_apply`
lemmas: `tameUnramInput_denote` (L unramified and scalar), `tameRamInput_denote` (L and N0
ramified), `npcTameRamInput_denote` (Npc ramified). The nine/five count is taken from the
generated JSON, not by hand.

### T2.c The universal-row structure is exported, not described

One formal row per family carries the opaque projector atom `P`, and the branch is a
*specialization* of that one row, not a second row: `P` maps to the identity at the
unramified and scalar sectors and to zero at the ramified sectors. The driver exports the
projector per sector and binds it by `rfl` to `splitEnd` / `ramifiedEnd`, which are
`toEnd t 1` and `toEnd t 0`. So the rendered ramified sector prints the same universal row as
the unramified one, followed by `(Pi=0)`, which is what the Lean says.

| Sector | Tame input row | Wild input row |
|---|---|---|
| L unramified | `S^-1 a_tau` | `Pi a_tau + (S^-1 + Pi) a_x0`, at `Pi = I` |
| L ramified | universal tame row | the same row at `Pi = 0`, i.e. `S^-1 a_x0` |
| L scalar | `S^-1 a_tau` | `I a_tau` |
| N0 unramified | `S^-1 a_tau` | `Pi a_tau + (S^-1 + Pi) a_x2`, at `Pi = I` |
| N0 ramified | universal tame row | the same row at `Pi = 0` |
| Npc unramified | `S^-1 a_tau` | `Pi a_tau + (A^-1 + I) a_x0 + (S^-2^r + Pi) a_x2`, at `Pi = I` |
| Npc ramified | universal tame row | the same row at `Pi = 0` |

The universal tame row prints as `S^-1 . (T - I) a_sigma + (S^-1 - N_q(T)) a_tau`, with
`N_q(T)` the literal left-nested `normCoeff` sum, the same spelling W362 records for item 5.

### T2.d A cross-check between two independently generated artifacts

At L unramified the item-4 operation is `R2 <- R2 + S R1`; applying it to the item-3 rows
gives `a_tau + (I + S^-1) a_x0 + S S^-1 a_tau = (I + S^-1) a_x0` in characteristic two, which
is item 5's recorded reduced target `(I - S^-1) a_x0`. The same composition works at N0 and
Npc. **This check is done by reading, not by the checker**: no script verifies it, because
doing so needs the characteristic-two step and the exporters deliberately carry no
coefficient module.

---

## T3. Item 6, the Stokes chain, and item 9, the phase cover

These two are the same shape and are best read together. Both carriers are `Prop`s defined by
a conjunction of universally quantified clauses, consumed as a field of the same word
certificate records. There is no matrix, chain complex object or coefficient tree to
serialize, and neither driver invents one. Each serializes the part that genuinely is data:
the wiring, the clause structure, and the `standardNumerics` multipliers its own clauses
assert, bound by `rfl`.

**The multipliers are split between the two items on purpose.** Item 6 exports `tMult` and
`h1Mult`, which its four clauses use; item 9 exports `gaussUnram` and `gaussRam`, which its
two clauses use. Neither exports the other's.

| | item 6, Stokes | item 9, phase cover |
|---|---|---|
| clauses | 4: T-cocycle count, separation, nondegeneracy, V-cocycle count | 2: unramified and ramified Gauss residue |
| multipliers | `tMult T = T^(n+1)`, `h1Mult V = V^n` | `gaussUnram m = (-1)^n 2^(nm)`, `gaussRam m = 2^(nm)` |
| sign | none | yes, and it follows from the degree parity alone |
| field | `stokes` | `determinant` |

**The Gauss sign is computed, not asserted.** It is `-1` for L, whose degree `2h+1` is odd,
and `+1` for N0 and Npc, whose degree `2+2h` is even. The exporter computes it from the `rfl`
formula and the validator recomputes it, so an independently asserted sign is refused.

### T3.a Proof irrelevance: what a field binding certifies

Both certificates are `Prop`s, so `record.field = producer` is `rfl` for **any** producer
whose type is the field's type. The binding certifies a **statement identity**, not proof
identity. This is why the bridge kind is `field_statement_identity` and deliberately not the
`record_target` that items 3, 4, 5 and item 8's coordinate half use. Treating the two as the
same strength of claim would be the exact error the readiness note warns about.

### T3.b The Npc degree, in item 6 but not in item 9

The Npc Stokes producer `npcCand_stokes` is stated at degree `2*h+2`; the record's `stokes`
field is at `2+2*h`. Those spellings **agree at every numeric instance**, so the exported
degrees look equal at `h = 0` and `h = 3`, but they are **not definitionally equal at a
variable `h`**, and the record's field is filled by a tactic block that rewrites along the
equality. The Npc Stokes binding kind is therefore `degree_normalized_field`, it names the
normalization theorem, and the driver carries `npcStokes_typeNormalization` proving the two
chain statements are the same `Prop` after normalization. **Item 9 needs none of this**:
there, producer and record field are both at `2+2h`.

### T3.c Where the proof comes from is a separate axis

Item 9 records it separately from the bridge kind, in a `supply` field, because they are
different questions. At N0 and Npc the `determinant` field is filled by a theorem of the
tree. At L it is filled from a **field of an analytic-leaves record supplied as a
parameter**, and the theorem behind that field, `determinantResidue_lSq_pow`, is available
only at `q = 2^f` with `f` odd, which is a narrower scope than the `alpha` and `q` conditions
the even families use. The L supply route is `analytic_leaves_record_field`; N0's and Npc's
is `theorem`.

---

## T4. Item 7, the extraspecial Hessian

Item 7's carriers are theorems with real algebraic shape but no record, so the driver
restates each identity through a named decomposition and discharges it by the tree's own
theorem:

```text
hessShape leading cross planes = leading + cross + sum over j of planes j
```

A wrong decomposition does not compile, so what is certified is the decomposition and its
three subterms. The human labels for those subterms are prose, and the artifact says so.

**The content worth publishing is what the four identities do not share**, and the validator
pins the hypothesis list per sector so a sector cannot silently lose or gain one:

| Sector | Leading term | Vanishing slot | Extra input |
|---|---|---|---|
| L | quadratic value at `x1` | `x0` | none: resolver-immune |
| N0 | quadratic value at `x0` | `x2` | `2 <= alpha`, once, through the leading-power law |
| Npc unramified | named diagonal | **none**, full offset | residue pin `E(omega2) = e` with `e = 1 mod 4` |
| Npc ramified | named diagonal | **none**, full offset | `q` quadratic, `u` odd-order fixed-point-free, resolver lifts |

Binding to the full-offset theorems is deliberate. w362-pub-note T3.c decision 11 warns that
the older Gate-E slice with an invertible `Lc` must not be displayed as the completed
normal-coordinate proof; the artifact says that in its own text.

---

## T5. Item 2, the two specializations

Item 2 splits and the split is the content, so the artifact keeps the halves apart and pins
both kinds.

**The pro-2 half** is a syntactic identity between `PWord` values, restated as a factor list
and discharged by the tree's own theorem. N0 and Npc each have a whole-word equation
(`pro2_nCompact`, `pro2_npcW`). **L does not**: the tree states the core list
(`pro2_lSqCore`) and the evaluated form (`eval_pro2_lSqW`) but no whole-word syntactic
equation, so the driver assembles one from the core list and a one-line handle-tail lemma,
and the artifact names the assembly rather than presenting it as the tree's own.

**What Gate C keeps is displayed, not silently expanded.** The pro-2 map removes `tau` and
collapses every `omega2` power; it does **not** collapse the profinite `eta-hat` power or the
integer `2^r` conjugator at Npc, and the Npc correction block stays folded in the tree's own
statement. The factor descriptors say so. The handle tail's description is computed from the
rank, so it says EMPTY at rank zero, which is the certificate's own convention and not a
simplification.

**The tame half** is a `Prop` carried as the `tameSpecialization` field of the word
certificate record, so its binding is a statement identity, kind 4 above.

**The standing-axiom class is untouched.** Item 2 is also where the three field-selection
adapters `FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_{l,n0,npc}` are pinned. Those
are **not** standard-three: each carries four documented standing arithmetic and reciprocity
inputs, and W362 pins them in their own class and prints their full axiom list. Nothing in
this lane touches them, nothing weakens that class, and every item-2 artifact says so in its
own `warning` field.

---

## T6. Item 8, the change of variables, and a correction to this lane's own measurement

**An earlier revision of this note said item 8 was out of reach without Lean work first.
That is true of half of item 8 and false of the other half**, and the half that is reachable
turned out to carry the strongest bridge of the four items written after T1. The correction
is recorded here rather than silently dropped.

**The change of variables is data.** It is a genuine `Equiv` with an explicit `toFun` and
`invFun`, so the eight bindings are `rfl` against the `Equiv`'s own fields: `record_target`
strength. All four sectors share one handle regrouping, `Fin h x Fin 2 -> A` to
`Fin h -> A x A` through `finTwoProdAddEquiv`. What differs is the head:

| Sector | Equiv | Head coordinates | Head transform |
|---|---|---|---|
| L | `LSquare.lSqPhaseCoordsEquiv` | 1 | identity: a rebracketing |
| N0 | `WordPhaseModel.wPmCompactCoordsEquiv` | 2 | identity: a rebracketing |
| Npc unramified | `NpcUnramifiedComparison.wPnpcPhiCoordsEquiv` | 2 | `c0` to `Phi c0` |
| Npc ramified | `NpcRamifiedComparisonBase.wPnpcRamifiedCoordsEquiv` | 2 | `c0` to `Phi c0` |

**So only the two Npc sectors are a change of variables in the ledger item's sense**; the
other two are rebracketings, and the artifact says which is which. The inverse applies
`Phi.symm`, which is why the operator has to be an equivalence and not merely a map.

**What remains out of reach** is the quadratic normal form record itself, `SourceOddHessian`.
The declarations that build it (`LHessianCertificates.unramifiedHessian` and
`.ramifiedHessian`, `CompactNHessianCertificates.*`, `NpcHessianCertificates.*`) take a
descent datum, a factor set, a projection, a coefficient module with its topology and action,
a simplicity hypothesis and a cardinality. **A `rfl` signature theorem against one requires
instantiating all of it, which means selecting a coefficient module, which this lane is
forbidden to do.** Those records are named with the bridge kind `named_but_unbound`.

The piece of item 8 that is data but not yet reachable is the **Gauss sign and exponent**
those records establish on the way: `gaussSum(lSqWallHandlePhase ...) = (-1) * 2^(m*(2h+1))`
unramified and `= (+1) * 2^(m*(2h+1))` ramified. Those appear inside the two proofs as a
`have`, not as named standalone theorems, so an exporter cannot cite them. **Naming them as
standalone theorems in a module under `GQ2/` is the next piece of work on item 8**, and it is
outside every exporter lane's mandate as currently drawn: owner decision 16.

---

## T7. What was staged, and the check

Thirteen new files under `scripts/w363_*`, and 108 new artifact files (36 artifacts times
three) in `generated/general-ln-certificate-staged/`. Nothing else was created or modified.

| Item | Driver | Generator | Axiom pins | Self-test |
|---|---|---|---|---|
| 2 | `w363_ln_specialization_export.lean` | `w363_ln_specialization_tex.py` | 8 | 47 |
| 3 | `w363_ln_input_export.lean` | `w363_ln_input_tex.py` | 27 | 48 |
| 6 | `w363_ln_stokes_export.lean` | `w363_ln_stokes_tex.py` | 7 | 51 |
| 7 | `w363_ln_hessian_export.lean` | `w363_ln_hessian_tex.py` | 6 | 49 |
| 8 | `w363_ln_coordinate_export.lean` | `w363_ln_coordinate_tex.py` | 9 | 43 |
| 9 | `w363_ln_cover_export.lean` | `w363_ln_cover_tex.py` | 7 | 53 |

Every pin is standard three or less. Every driver carries a global `main` and stays outside
`GQ2.lean`, like the W361 and W362 export executables.

Parameters, chosen to match the W362 Fox artifacts exactly so all the items read together:
`L h0 q2`, `L h4 q2`, `N0 h0 q2`, `N0 h3 q2`, `Npc h0 q2 r1`, `Npc h3 q2 r2`. Three sit at
the frozen L/N appendix parameters and three sit beyond them.

`scripts/w363_check_ln_staged.sh` extends the W362 script the way the W362 script extends the
W361 one: it runs it unchanged, first, and adds. Neither earlier check script is modified,
and neither is `scripts/w362_ln_certificate_packet.py`.

### Verification record

`bash scripts/w363_check_ln_staged.sh` from the worktree root, against the shared campaign
cache at Lean 4.31.0-rc2, **exit 0**, 7 minutes 28 seconds. No `lake` invocation. It
reproduces `W361_STAGED_CHECK_PASS`, then every W362 line, then Lean-replays all 36 new
artifacts, then `W363_LN_STAGED_CHECK_PASS`.

**Every W362 hash reproduces exactly the value recorded in w362-pub-note**: the six Fox
hashes `8100f623 2dc399b5 ede1c9b7 7a280f1c 066b3a46 eb4ee748` and the six packet hashes
`7f19d17e f98de22b 1bb59b94 b54126b5 6cf3a39e 97d13c27`. **The frozen word hashes therefore
still reproduce**: `d129037c...` for `rawLsq_n1`, `a940b6ad...` for `rawNCompact_alpha2_h0`
and `08b7742c...` for `rawNpc_a2_r1_eta1_1_h0`, which w362-pub-note T3.a fact 4 identifies as
the single most important fact for the decision, are carried by the W362 packets, which this
run replays unchanged and byte for byte.

The 36 new hashes, first eight hex digits, in check order:

```text
specialization  L-h0 2ee6bc2b  L-h4 1e30c529  N0-h0 5b5bbd16  N0-h3 8c67b447  Npc-h0 38aa6ef3  Npc-h3 694ef474
input           L-h0 fe015c8a  L-h4 98495974  N0-h0 5d939687  N0-h3 7c859f7d  Npc-h0 e838c51b  Npc-h3 f1e45d5d
stokes          L-h0 cfca77c1  L-h4 4b3210d2  N0-h0 fd1f94c2  N0-h3 eef6d9d9  Npc-h0 0c7552df  Npc-h3 a7de4aa6
hessian         L-h0 a52160a6  L-h4 f24f6977  N0-h0 39707fd4  N0-h3 3f6e174e  Npc-h0 1cfb9416  Npc-h3 71d0969a
coordinate      L-h0 352edf53  L-h4 4d1b5d25  N0-h0 0cd8d35d  N0-h3 ca71e4ef  Npc-h0 afcd8f62  Npc-h3 8ce388d9
cover           L-h0 3de8a619  L-h4 0b3a205f  N0-h0 6ba7ab4c  N0-h3 c70080a0  Npc-h0 fdd7bca1  Npc-h3 72b4cd15
```

What this run does **not** establish, unchanged from W362: it is not a fresh full-repository
build, not a transitive build attestation, and not a hash-gate run. The probe imports
existing olean artifacts, so the direct-source provenance sidecars do not prove that those
bytes produced those artifacts.

---

## T8. Naming traps found on the way

w362-pub-note T1.a records two. This lane adds two more, both of which cost a probe
iteration:

3. **`Certificates.Npc.tameRelW` is a second declaration of the tame relator**, distinct from
   `Certificates.tameRelW`, same spelling in a different namespace. The Npc denotation
   theorems must be stated over the Npc one or the rewrite does not fire.
4. **`wPmCompactCoordsEquiv` has an `m` in its name and lives in `WordPhaseModel`, but it is
   what the compact-`N` data uses.** The name does not say which family uses it.

Both are instances of the same lesson the W362 note drew: citing a declaration by its file
name, or by the family its name suggests, does not give its Lean name or its user.

---

## T9. Packets

The six W362 packets are **not regenerated in this lane**, and they still carry their
original TODO text for items 2, 3, 6, 7, 8 and 9, which now names exporters that exist. This
is a known staleness and it is deliberate: regenerating them means either modifying
`scripts/w362_ln_certificate_packet.py`, which changes the recorded W362 packet hashes, or
adding a second composer that owns the same paths, which w362-pub-note T3.a fact 6 rules out.
**Which of those two the packets take is an owner decision**, number 13 below. Until it is
taken, the W362 packets and the W363 artifacts are two separate staged sets, both checked by
`scripts/w363_check_ln_staged.sh`, and the packets' TODO text for those six items should be
read as "no display *in this packet*", not as "no display anywhere".

Note for that decision: the W362 packet hashes are **not frozen identifiers**. W362's own
note calls them "a locator", says each packet's `.files.json` is the authority for its own
files, and recomputes the packet hash on every check. The frozen identifiers are the three
word hashes in T7, and those are untouched either way.

## T10. Owner decisions this lane adds

The twelve in w362-pub-note T3.c stand unchanged. This lane adds five:

13. Whether the W362 packets are regenerated to carry the six new displays, and if so by
    modifying the W362 composer (which changes its recorded packet hashes, none of which is a
    frozen identifier) or by a new composer with its own paths.
14. **Whether a `field_statement_identity` bridge is publishable at all.** Proof irrelevance
    makes it a statement-level and not a proof-level claim. It is the bridge kind of item 6,
    item 9 and item 2's tame half, so this decision governs three of the six new displays.
15. Whether the `restated_identity` kind is acceptable, since no exporter in the tree used it
    before this lane. It governs item 7 and item 2's pro-2 half.
16. Whether the Gauss sign and exponent for item 8's normal-form half may be named as new
    standalone theorems in a module under `GQ2/`, which is outside every exporter lane's
    mandate as currently drawn. Until that is done, item 8's normal-form records stay
    `named_but_unbound`.
17. Whether `scripts/w363_check_ln_staged.sh` is folded into the W361 or W362 script or into
    `scripts/check_dyadic.sh`, and at which gate number. This lane left both earlier scripts
    unmodified so that the recorded W361 and W362 check semantics did not change.

## What this lane deliberately did not do

* It did not modify `generated/hash-manifest.json`, any `generated/appendix/*.tex`,
  `GQ2.lean`, any module under `GQ2/`, `scripts/w361_check_staged.sh`,
  `scripts/w362_check_ln_staged.sh`, `scripts/w362_ln_certificate_packet.py`,
  `scripts/check_dyadic.sh`, or any W362 staged artifact. Verified by diff against `b87bfa06`.
* It did not run `lake` in any form.
* It did not relabel any staged artifact as adopted, and every artifact it wrote embeds
  `status: "STAGED"` with a validator that refuses any other value.
* It did not treat `RawWord.shadow` as W361's semantic `tameShadow`.
* It did not select a coefficient module, marking, field, resolver, `eta` or source
  certificate in any exporter: every signature theorem is quantified over them.
* It did not weaken the standing-axiom class of the three field-selection adapters, and it
  did not fold them into any standard-three count.
