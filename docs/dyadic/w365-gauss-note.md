# W365-GAUSS: the Gauss sign and exponent as standalone theorems

Lane opened against base `ab26b51d`, branch `claude/w365-gauss`.  One new module,
`GQ2/Dyadic/Instances/GaussPhaseValues.lean`.  No existing module was edited and `GQ2.lean` was
not touched; the two `L` facts are re-proved from the producers the two Hessian proofs use,
not extracted by editing them.

## What the ticket asked for, and what turned out to be true

`docs/dyadic/w363-pub2-note.md` item 8 records that the Gauss sign and exponent the
normal-form records establish on the way,

```
gaussSum (lSqWallHandlePhase ...) = (-1) * 2 ^ (m * (2 * h + 1))    unramified
gaussSum (lSqWallHandlePhase ...) = (+1) * 2 ^ (m * (2 * h + 1))    ramified
```

"appear inside the two proofs as a `have`, not as named standalone theorems, so an exporter
cannot cite them", and makes naming them owner decision 16.

That is right about the two equations.  Three things around it are not what the ticket
assumed, and the lane records them rather than quietly working around them.

**1. The `L` sign was already citable, as a record field.**
`LHessianCertificates.unramifiedHessian_baseSign` and `.ramifiedHessian_baseSign` are already
standalone theorems, `... .affinePhase.baseSign = -1` and `= 1`, both by `rfl`, and both
quantified over the coefficient module rather than instantiating one.  So the *sign* half of
the `L` display cell has had a `record_target` binding all along.  PUB2's
`named_but_unbound` label is accurate about the *record* `SourceOddHessian`, which nothing
binds; it overstates the gap for the sign.

**2. No exponent was ever named, anywhere.**  `PhaseCoverCertificate.baseDim` carries it, but
there is no `_baseDim` theorem for any of item 8's four sectors (a tree-wide grep for named
`baseDim` lemmas finds only `Word/Hessian.lean:endpoint_card`, which is about a cardinality,
not about a display cell).  The exponent is the genuinely missing half, in every sector.

**3. The compact sectors were not missing their value; they were missing its shape.**
`Instances.WordPhase.wPh_compactWallHandlePhase_gaussSum_standardRam` and its `Unram` twin are
already standalone theorems, with `Certificates.nCompact_handle_form_gaussSum` underneath as
the form-level statement and `WordPhaseCompactMHandleBoundary.wPcM_compactWallHandlePhase_gaussSum`
on top as the compact-`M` spelling (that one is literally the `standardRam` theorem under
another name).  `Instances.WordPhase.wPh_gaussUnram_eq_gaussRam_of_even` is also already there.
What none of them gives is the sign and the exponent as separate printed numbers: they land on
`(standardNumerics n).gaussRam m`, which hides the sign inside a `SourceNumerics` field.
**So T2 named only the display shape, and this note says so rather than claiming a new value.**

**4. The `Npc` sector was in the same position, from a different theorem.**  Its records are
`SourceWallHessian`, whose endpoint is
`Instances.WordPhaseWallHandleCertificates.wallHandlePhase d0 q h`, and its value is
`gaussSum_wallHandlePhase`, stated as `(Fintype.card V) ^ (h + 1)`.  That carries the sign
only implicitly too.  The lane added the display shape at `Fintype.card V = 2 ^ (2 * m)`,
which also shows the `Npc` sector prints the **same cell** as the two compact sectors.

## The display cell

```
structure GaussValCell where
  sign : ℤ
  degree : ℕ

def GaussValCell.value (c : GaussValCell) (m : ℕ) : ℤ := c.sign * 2 ^ (m * c.degree)
```

Three constants: `gaussValLUnramCell h = ⟨-1, 2*h+1⟩`, `gaussValLRamCell h = ⟨1, 2*h+1⟩`,
`gaussValCompactCell h = ⟨1, 2*h+2⟩`.  The six projection lemmas
(`gaussValLUnramCell_sign` and siblings) are `rfl`, so a driver binds the **printed sign** and
the **printed exponent** at `record_target` strength, and binds the equation itself by
restating it through the cell, which is `restated_identity`.  There is one compact cell and
not two because at even degree the two targets are the same integer.

## T1. The `L` sector

Six theorems, three per branch, all quantified over `Bg`, `D`, `DD`, `Cbar`, the factor set,
the projection and the representation.  **No coefficient module is selected**, so an exporter
lane under the PUB2 scope rule can cite them.

| name | statement |
| --- | --- |
| `gaussValLUnramifiedStandard` | `gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h) = (standardNumerics (2*h+1)).gaussUnram m` |
| `gaussValLUnramifiedDisplay` | `... = (-1 : ℤ) * 2 ^ (m * (2*h+1))` |
| `gaussValLUnramifiedCell` | `... = (gaussValLUnramCell h).value m` |
| `gaussValLRamifiedStandard` | `gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h) = (standardNumerics (2*h+1)).gaussRam m` |
| `gaussValLRamifiedDisplay` | `... = (1 : ℤ) * 2 ^ (m * (2*h+1))` |
| `gaussValLRamifiedCell` | `... = (gaussValLRamCell h).value m` |

`headOperator` is `LHessianCertificates.headOperator rho pi`, the literal operator the two
records use, not a normalized stand-in.  The `Display` rows are verbatim the `have hwhole` of
`LHessianCertificates.unramifiedHessian` and `.ramifiedHessian`.

Hypotheses, unramified: the section's `base`, `hbase`, `pi`, `hpi`, `hf`, `hm`, `hcompat`,
plus `hsimple : IsSimpleModTwo (gamma h q) DD.Vmod`, `hqe : Even q`, `1 ≤ m`,
`Nat.card DD.Vmod = 2 ^ (2*m)` and `G : LUnramifiedHeadData rho pi`.  Ramified: the same
section hypotheses, plus `[Finite Cbar]`, `hqe`, `Nat.card DD.Vmod = 2 ^ (2*m)`,
`G : LRamifiedHeadData rho pi` and `S : LRamifiedSourceArfData rho _ hcompat`.  These are
exactly the hypotheses the two record producers already take: nothing was added and nothing
was dropped.  `1 ≤ m` appears on the unramified side only, which is where the Arf computation
needs it.

The proofs re-run the two producers
(`sourceWordPhaseComparison_of_lSqUnramifiedHead` + `lSqUnramifiedPhaseModel_of_headData`;
`ramifiedHeadComparison` + `lSqRamifiedPhaseModel_of_headData`) and transport through
`LHessianCertificates.gauss_eq_of_same_source`, which is the same route the `have`s take.

## T2. The compact and `Npc` sectors

| name | statement |
| --- | --- |
| `gaussValCompactDisplay` | `gaussSum (wPhCompactWallHandlePhase q h) = (1 : ℤ) * 2 ^ (m * (2*h+2))` |
| `gaussValCompactCellEq` | `... = (gaussValCompactCell h).value m` |
| `gaussValCompactDisplayUnram` | `... = (standardNumerics (2*h+2)).gaussUnram m` |
| `gaussValNpcDisplay` | `gaussSum (wallHandlePhase d0 q h) = (1 : ℤ) * 2 ^ (m * (2*h+2))` |
| `gaussValNpcCellEq` | `... = (gaussValCompactCell h).value m` |

All five are quantified over `V` and the forms, with `IsQuadraticFp2`, `Nonsingular` and
`Fintype.card V = 2 ^ (2*m)`; the `Npc` pair also takes `IsQuadraticFp2 d0` and is independent
of `d0` otherwise.  `gaussValCompactDisplayUnram` is a one-line restatement of an existing
theorem and is here only so that the unramified compact row has a name on the same page as
the others; it claims nothing new.

## T3. Item 8's display cells and their suppliers

The exporter driver `scripts/w363_ln_coordinate_export.lean` emits four sectors.  Each would
gain a Gauss sign cell and a Gauss exponent cell.  This is where each cell now comes from.

| item-8 sector | endpoint phase | sign cell | exponent cell | value equation |
| --- | --- | --- | --- | --- |
| `graph_normal_form`, unramified (`L`) | `lSqWallHandlePhase DD.qbar (headOperator rho pi) h` | `gaussValLUnramCell_sign` (`-1`) | `gaussValLUnramCell_degree` (`2h+1`) | `gaussValLUnramifiedDisplay` / `gaussValLUnramifiedCell` |
| `graph_normal_form`, ramified (`L`) | same | `gaussValLRamCell_sign` (`+1`) | `gaussValLRamCell_degree` (`2h+1`) | `gaussValLRamifiedDisplay` / `gaussValLRamifiedCell` |
| `compact_normal_form` (`N0`), both branches | `wPhCompactWallHandlePhase DD.qbar h` | `gaussValCompactCell_sign` (`+1`) | `gaussValCompactCell_degree` (`2h+2`) | `gaussValCompactDisplay` / `gaussValCompactCellEq` |
| `unramified_full_offset` (`Npc`) | `wallHandlePhase d0 DD.qbar h` | `gaussValCompactCell_sign` | `gaussValCompactCell_degree` | `gaussValNpcDisplay` / `gaussValNpcCellEq` |
| `ramified_full_offset` (`Npc`) | same | `gaussValCompactCell_sign` | `gaussValCompactCell_degree` | `gaussValNpcDisplay` / `gaussValNpcCellEq` |

The compact-`M` rows, which item 8 does not list but which share the compact endpoint, are
served by the same three compact declarations.

**Bridge kinds.**  Each cell splits into two bindings, and they do not get the same kind.

* **The sign cell and the exponent cell: `record_target`.**  Both are `rfl` against a field
  of `GaussValCell`, which is data with explicit fields, exactly as item 8's coordinate half
  is `rfl` against the `Equiv`'s own fields.  This is the strongest kind in the PUB2
  taxonomy.
* **The value equation: `restated_identity`.**  The carrier is a theorem, not a record.  A
  driver restates `gaussSum <endpoint> = (<cell>).value m` through the named cell and
  discharges the restatement by the tree's own theorem, so a wrong cell does not compile.
  That is kind 3 of the taxonomy, the kind item 7 and item 2's pro-2 half already use.
* **`record_target` is also available for the `L` sign by a second, independent route**, via
  the pre-existing `LHessianCertificates.unramifiedHessian_baseSign` and
  `.ramifiedHessian_baseSign`.  Two independent `record_target` bindings for one displayed
  number is a stronger position than item 8 has anywhere else, and a driver may want to bind
  both and let the validator check that they agree.
* **The normal-form records stay `named_but_unbound`.**  This lane does not change that.
  `SourceOddHessian`, `SourceCompactHessian` and `SourceWallHessian` are still unreachable
  without instantiating a coefficient module, which no exporter lane may do.  What changed is
  that the Gauss cells no longer have to wait for the records: they are now supplied by
  theorems about the *endpoint phase function*, which is quantified over the coefficient
  group, so the cells and the record carry different kinds in the same artifact.

**So owner decision 16 can be answered on its narrow question** (the naming is done, in one
module, under `GQ2/`, without editing anything), while the separate question it bundles, the
`named_but_unbound` status of the records themselves, is unchanged and still open.

## Pins

Every declaration in the module, with `#print axioms` run in the file.  **No standing input
of any kind appears.**  Nothing here carries a field-selection adapter, a reciprocity input
or any project axiom: the split is entirely inside the standard three.

| declaration | pin |
| --- | --- |
| `GaussValCell`, `.mk`, `.sign`, `.degree` | none |
| `GaussValCell.value` | `propext` |
| `gaussValLUnramCell`, `gaussValLRamCell`, `gaussValCompactCell` | none |
| the six `*_sign` / `*_degree` lemmas | none |
| `gaussValLUnramifiedStandard`, `...Display`, `...Cell` | standard three |
| `gaussValLRamifiedStandard`, `...Display`, `...Cell` | standard three |
| `gaussValCompactDisplay`, `gaussValCompactCellEq`, `gaussValCompactDisplayUnram` | standard three |
| `gaussValNpcDisplay`, `gaussValNpcCellEq` | standard three |

"standard three" is `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no
`native_decide`, no new axiom, no resource option, no `set_option` of any kind in the module.
Checked with `bash scripts/w361_lean_runner.sh GQ2/Dyadic/Instances/GaussPhaseValues.lean`:
zero errors and zero warnings.

## What remains

1. **The module is not in `GQ2.lean`.**  The lane was forbidden to edit it, so
   `GaussPhaseValues.lean` is verified against the shared cache but is not yet in the build
   graph.  Adding the import is a one-line owner action and is the only thing standing between
   these theorems and a gated build.
2. **No exporter cites them yet.**  `scripts/w363_ln_coordinate_export.lean` was not modified.
   Wiring the five sector rows to the cells above is a separate exporter lane, and it changes
   the item-8 artifact hashes.
3. **The `Npc` ramified record is `nonempty_npcRamifiedHeadHessian`**, a `Nonempty`, not a
   record value.  Its Gauss cell is supplied here by the endpoint theorem, which is fine, but
   a driver cannot get a second `record_target` route for that sector the way it can for `L`.
4. **The exponent has no record-field route in any sector**, because no `baseDim` theorem
   exists anywhere in the tree.  If the owner wants two independent bindings for the exponent
   as well, that is four small `rfl` theorems (`.affinePhase.baseDim = ...`) in the three
   certificate modules, which this lane was not allowed to add.
5. **`LBoundaryHessianCertificates` already consumes the two `_baseSign` theorems** (lines 171
   and 208).  Anyone adding `baseDim` theorems should check there first for the spelling the
   boundary lane expects.
