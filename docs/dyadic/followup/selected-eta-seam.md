# The selected-word / arbitrary-unit seam

The R5 constructor table in `GQ2.Dyadic.SelectedWords` is intentionally frozen.  Its `Npc` and
`Mpc` rows contain concrete display data (`EtaData` and `EtaDisplay`), whereas `BranchData` stores
an arbitrary unit of `Z_2`.  These are not interchangeable types: `EtaData` is a rational
numerator/denominator presentation, and there is no reason that every 2-adic unit should have
such a presentation.

`GQ2.Dyadic.SelectedEta` adds a sound interface without changing any selected relator:

* `EtaData.RepresentsUnit` says that a rational display evaluates to the underlying 2-adic unit.
* `EtaDisplay.RepresentsUnit` says that an `Mpc` exponent display denotes `etaHatZ` of that unit.
* `NpcDisplayFor` and `MpcDisplayFor` package these equations together with the well-formedness
  assumptions already required by the selected constructors.
* `BranchData.DisplayFor` asks for exactly the appropriate package on the two eta-bearing rows.
* `SelectedPresentation.ofBranch` consumes that package and returns an existing R5 constructor.
* `npcWUnit` and `mpcWUnit` are semantic word constructors defined for every 2-adic unit, whether
  or not a finite display is available.

The comparison strength is branch- and display-dependent:

| case | proved comparison |
|---|---|
| compatible `Npc` rational display | literal `PWord` equality |
| compatible `Mpc` display (`one`, `lit`, or `hat`) | equality after every profinite marking/evaluation; equality of the free relator, relator set, closed normal subgroup, `NR`, `GammaBare`, and `GammaR` |
| compatible `Mpc` genuine `.hat` display | literal `PWord` equality |
| arbitrary unit with no finite display | semantic word exists; no selected displayed word is manufactured |

The weaker general `Mpc` statement is necessary.  `PWord` records whether a power was written as
an integer power or a profinite power, so `.one`, `.lit k`, and `.hat n d` can evaluate to the same
group element without being the same syntax tree.  The present development therefore keeps three
claims separate:

1. a display denotes a chosen 2-adic unit;
2. two displayed words have equal evaluations under every marking;
3. two words are literally equal as `PWord` syntax.

The presentation upgrade is now formalized.  `gammaRelators_eq_of_freeMarking_eval_eq` isolates
the exact invariant: equality at the tautological marking of the free profinite group.  Universal
evaluation equality implies that single equality immediately.  The successive theorems identify
the relator set, its closed normal closure, the class of admissible finite quotients, the
intersection `NR`, and both presentation objects.  In particular,
`SelectedPresentation.GammaR_word_ofBranch_Mpc` says that a selected compatible `Mpc` display
presents the same corrected admissible-limit group as the arbitrary-unit semantic word.

This does **not** identify the syntax trees, nor does it manufacture a finite display for every
unit.  Likewise, the inverse-power step suggested by the informal paper is not yet formalized: the
current `Zhat` API exposes the additive profinite exponent group, but not enough
multiplicative/composition structure to prove that powering by the exponent attached to an
arbitrary 2-adic unit is an automorphism with the expected inverse.

Consequently this seam is total at the semantic-word level and honest at the selected-display
level.  It now completely discharges presentation invariance **conditional on a compatible
display**; the display-existence and arithmetic/classification steps of the paper's full
arbitrary-unit presentation conjecture remain open.
