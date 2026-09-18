/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.GeneralMain

/-!
An additive exact-footprint audit for the new general endpoint. This does not change the
frozen Q2 capstone census or the historical dyadic gate. Run using the same verified Lean
search path as the build, or `lake env lean scripts/w361_general_axiom_audit.lean`.

Every name is resolved in the elaborated environment, and any extra OR missing dependency
fails the audit. In particular no `sorryAx`, new arithmetic axiom, or reduction oracle can
pass by being hidden in a private dependency.
-/

open Lean

private def standardAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private def suppliedFieldAxioms : List Name := standardAxioms ++
  [``GQ2.hilbertSymbol_normCriterion_finiteDyadic,
   ``GQ2.peripheralCyclotomicAction,
   ``GQ2.relativeStiefelWhitney_dyadic,
   ``GQ2.tateDualityAt,
   ``GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated,
   ``GQ2.Foundations.absGalQ2_localEulerCharacteristic]

private def canonicalFieldAxioms : List Name := suppliedFieldAxioms ++
  [``GQ2.localReciprocity, ``GQ2.markedRecipAt, ``GQ2.orientedTameQuotientAt]

private def expectedFootprints : List (Name × List Name) :=
  [ (``GQ2.exists_contSurj_of_allowed_levels, standardAxioms)
  , (``GQ2.exists_contSurj_over_of_quotient_lifts, standardAxioms)
  , (``GQ2.nonempty_markedEquiv_of_quotient_lifts, standardAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedFinal.alignedRealization_chi_eq_original,
      standardAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedFinal.hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange,
      suppliedFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters,
      suppliedFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI,
      canonicalFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.hasSelectedFullyMarkedFlexibleAssemblyRN_oddDegree,
      canonicalFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI,
      canonicalFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal.nonempty_selectedWordMarkedFieldData_of_matchesRange,
      suppliedFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal.nonempty_selectedWordMarkedFieldData_ramifiedI,
      canonicalFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal.nonempty_selectedWordMarkedFieldData_oddDegree,
      canonicalFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange,
      suppliedFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_canonicalParameters,
      suppliedFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI,
      canonicalFieldAxioms)
  , (``GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_oddDegree,
      canonicalFieldAxioms) ]

run_cmd do
  let env ← getEnv
  for (decl, expected) in expectedFootprints do
    unless env.contains decl do
      throwError "general endpoint audit: missing declaration {decl}"
    let actual ← collectAxioms decl
    let extra := actual.filter (fun ax => !expected.contains ax)
    let missing := expected.filter (fun ax => !actual.contains ax)
    unless extra.isEmpty && missing.isEmpty do
      throwError "general endpoint audit: {decl}\nextra: {extra}\nmissing: {missing}"
    IO.println s!"GENERAL_AXIOMS_OK|{decl}|{actual.size}"
  IO.println s!"GENERAL_AXIOM_AUDIT_PASS|{expectedFootprints.length}"
