/-
Landing check for the dyadic Tau Ceti discharge (tickets A1-K, B5-K, B10-K): the two `K`-level
inputs, as landed in `GQ2/TauCeti/B5K.lean` and `GQ2/TauCeti/B10K.lean`, are axiom-clean, and the
import closure of `GQ2.TauCeti.B10K` contains neither the census-axiom file
`GQ2/Foundations/Axioms.lean` nor any legacy input name.  Scratch file, outside every
`lean_lib`; run it with `tools.sh chk` or `lake env lean` from the worktree root (see `README.md`).
-/
import GQ2.TauCeti.B10K

open Lean Elab Command

#check @GQ2.TauCetiBridge.markedRecipAt_tauceti
#check @GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti
#check @GQ2.TauCetiBridge.markedRecipAt_tauceti_recip

-- The two prints, plain, then pinned with `#guard_msgs` (which fails on any other axiom list).
#print axioms GQ2.TauCetiBridge.markedRecipAt_tauceti
#print axioms GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti

/-- info: 'GQ2.TauCetiBridge.markedRecipAt_tauceti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GQ2.TauCetiBridge.markedRecipAt_tauceti

/-- info: 'GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti

/- The import-closure check: no forbidden module is loaded and no legacy input name (the nine
`ℚ₂` names of `GQ2/Foundations/TauCetiInstance.lean`, the two census axioms of
`GQ2/Foundations/Axioms.lean`, the `LiteratureInputs` instance) is in the environment. -/
#eval show CommandElabM Unit from do
  let env ← getEnv
  let forbiddenModules : List Name :=
    [`GQ2.Foundations.Axioms, `GQ2.Foundations.AxiomInstance, `GQ2.Foundations.Interfaces,
      `GQ2.Foundations.TauCetiInstance, `GQ2.Prop32]
  let legacyNames : List Name :=
    [`GQ2.markedRecipAt, `GQ2.orientedTameQuotientAt, `GQ2.localReciprocity, `GQ2.tameQuotient,
      `GQ2.tateDualityAt, `GQ2.peripheralCyclotomicAction, `GQ2.relativeStiefelWhitney_dyadic,
      `GQ2.hilbertSymbol_normCriterion_finiteDyadic, `GQ2.dyadicOrientation,
      `GQ2.absGalQ2_isTopologicallyFinitelyGenerated, `GQ2.absGalQ2_localEulerCharacteristic,
      `GQ2.tauCetiLiteratureInputs]
  let loaded := forbiddenModules.filter fun m => env.header.moduleNames.contains m
  let present := legacyNames.filter env.contains
  logInfo m!"modules in the closure: {env.header.moduleNames.size}; \
    forbidden modules loaded: {loaded}; legacy names present: {present}"
  unless loaded.isEmpty && present.isEmpty do
    throwError "import-closure check FAILED"
