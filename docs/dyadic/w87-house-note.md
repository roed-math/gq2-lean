# W87-HOUSE lane note (watch round 24)

Base `1541635f`, branch `claude/w87-house`. Verification is `scripts/mirror.sh` and
`scripts/scoreboard.sh` only; no `lake` command was run in this lane.

Round 24 watches the wave-86 landings: `SqCore/GradedRowLadder.lean`,
`Instances/MpcLadder.lean`, `Instances/WordPhase.lean`, the four wave-86 merges, the
annotation commits `aa31e767` and `1d286428`, and the notes `w86-house-note.md`,
`w86-ladder4-note.md`, `w86-ladder5-note.md`, `w86-phase-note.md`.

---

## 0 The baseline board (T3)

`scripts/scoreboard.sh` at `1541635f`, FROZEN ROWS block, elaborated this round. This is the
wave-87 baseline; a later wave that wants to know whether a row moved compares against it and
does not read a table anyone maintained by hand.

```
## FROZEN ROWS
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
  v-10 residual move             producers: 11   [MpcPivShift]
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
      GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_of_marking
        carries 7  : Eq, Eq, Eq, Eq, Eq, Eq, (function)
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
```

Two readings worth carrying:

* `MpcPivShift` now shows **11** producers. Wave 85's board printed 1 against a true 4 because
  the probe imported only the rows' modules; wave 86 put the probe on the umbrella and wave 86's
  own `MpcLad.mpcLad_shift_of_exists_supply` is visible here without a row naming it. The
  structural fix is doing what it was built for.
* REGISTRATION at this base reports **966** modules on disk and exactly one outside the
  umbrella, `GQ2.AxiomLedger`, which imports `GQ2` itself and so cannot be registered. The two
  wave-86 modules that W86-HOUSE flagged are in, landed by `ed382b2e`.

---

## 1 Findings, ranked

(Filled in below as the round proceeds.)

---

## Owner items

(Filled in at close.)
