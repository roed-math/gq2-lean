# W366-HOUSE lane note

Wave 366, housekeeping lane. Branch `claude/w366-house`, base `9dd8a307`.
Date: 2026-09-18.

Remit: watch 27 (T1), the decision's consequences in the docs corpus (T2), the
handoff's post-decision repairs (T3), the scoreboard baseline (T4).

Out of remit this lane: `GQ2.lean` and every Lean module; `docs/dyadic/refs/*`,
`w361-completion-audit.md`, `w364-proof-packet-amendment-mc.md`,
`w364-acceptance-readiness-mc.md` (APPLY lane); `generated/` and
`scripts/w366_*` (GAUSSEXPORT lane).

## T4, baseline

Run at the lane's own HEAD `2c2107da` (branch `claude/w366-house`), generated
2026-09-18 00:28, through the shared cache
(`GQ2_MIR=/Users/roed/claude/cla/work/main-build-cache/lib/lean`).

**The `--raw` flag does not produce these two sections.** `scripts/scoreboard.sh:1515`
returns immediately after `cat`-ing the probe records, so FROZEN ROWS and OWNER ITEMS
exist only in the formatted report. The board below is the formatted run of the same
script, same environment; no `lake`, no `check_dyadic.sh`.

**The shared-cache caveat still applies**, and W362-HOUSE and W364-HOUSE both recorded
it. The cache describes whatever the main clone last built, not this lane's base. This
lane changes no `.lean` file at all, so no row's binder count, axiom footprint or import
closure can differ between the cache's tree and this one.

### FROZEN ROWS

```
  Q2(v-2)  .N0 2 0               EXISTS   GQ2.Dyadic.FieldUnimod.fieldUni_genAsmBranch_sqrtNegTwo
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v2)   .M0 3 0               EXISTS   GQ2.Dyadic.FieldUnimod.fieldUni_genAsmBranch_sqrtTwo
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v5)   .M0 2 0               EXISTS   GQ2.Dyadic.FieldSqrtFive.fieldFive_genAsmBranch_sqrtFive
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v10)  .Mpc F                EXISTS   GQ2.Dyadic.Instances.MpcNorm.mpcNorm_genAsmBranch_sqrtTen
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) .Mpc T                EXISTS   GQ2.Dyadic.Instances.MpcNorm.mpcNorm_genAsmBranch_sqrtNegTen_of_pivot
      carries 2  : MarkedRecip, Exists
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) via shift             EXISTS   GQ2.Dyadic.Instances.MpcPiv.mpcPiv_genAsmBranch_sqrtNegTen_of_shift
      carries 2  : MpcPivShift, MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) untied                EXISTS   GQ2.Dyadic.Instances.MpcPiv.mpcPiv_genAsmBranch_sqrtNegTen
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  v-10 residue = word prob       EXISTS   GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_iff_marking
      carries NOTHING (no explicit binder)
      axioms     : std-3
  v-10 finite-class route        EXISTS   GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four
      carries 1  : (function)
      axioms     : std-3
  v-10 residual move             producers: 15   [MpcPivShift]
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_bracket_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class_five
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_full_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_word
        carries 14 : carrier, carrier, carrier, carrier, mem, mem, mem, mem, Eq, Eq, Eq, Eq, (function), Eq
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_wide_shift_of_forall_class_five
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcLad.mpcLad_shift_of_exists_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcMk.mpcMk_pivShift
        carries NOTHING            axioms: std-3
      GQ2.Dyadic.Instances.MpcMk.mpcMk_shift_of_fullSupply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcMk.mpcMk_shift_of_good_four
        carries 2  : MpcMkGood, (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_of_marking
        carries 7  : Eq, Eq, Eq, Eq, Eq, Eq, (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcSx.mpcSx_shift_of_marked_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_word
        carries 14 : carrier, carrier, carrier, carrier, mem, mem, mem, mem, Eq, Eq, Eq, Eq, (function), Eq
        axioms     : std-3
  v-10 initial-relator absorption EXISTS   GQ2.Dyadic.Instances.MpcMk.mpcMk_initialRelatorAbsorption
      carries 2  : Nat, le
      axioms     : std-3
  v-10 pivot shift theorem       EXISTS   GQ2.Dyadic.Instances.MpcMk.mpcMk_pivShift
      carries NOTHING (no explicit binder)
      axioms     : std-3
```

All twelve frozen rows EXIST; the residual-move row has 15 producers. No row changed
against the W364-HOUSE baseline.

### OWNER ITEMS

```
  owner memo (AUTHORITY)   docs/dyadic/owner-items-2026-08-05.md
    latest status block    ## Status at wave 362 (2026-09-17)
    count it asserts       7   (PROSE, off "N items await you")
  latest house note        docs/dyadic/w366-house-note.md
    owner-items heading    NOT FOUND in it (so no count; this is the
                           signal, not a zero)
  memo vs note             NOT COMPARED (one side is missing above)
  status of each item      UNVERIFIED (prose; not machine-checkable)
```

**The memo's count was stale and is finding H1 below.** The board read **7** because the
wave-362 status block still said "Seven items await you" after the owner decided item 4
and did item 5 on 2026-09-18. Expected after the decisions: **5**. Fixed in this lane;
the board re-reads 5 once the memo's headline is corrected.

The "NOT FOUND" line against this note is the board's own signal, not a defect in it:
this note had no owner-items heading when the baseline ran. One is supplied below, so
the next board run compares two numbers instead of one.

## T1, watch 27

(pending)

## T2, the decision's consequences

(pending)

## T3, the handoff

(pending)

## Sites the APPLY lane must handle

(pending)
