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
| compatible `Mpc` display (`one`, `lit`, or `hat`) | equality after every profinite marking/evaluation |
| compatible `Mpc` genuine `.hat` display | literal `PWord` equality |
| arbitrary unit with no finite display | semantic word exists; no selected displayed word is manufactured |

The weaker general `Mpc` statement is necessary.  `PWord` records whether a power was written as
an integer power or a profinite power, so `.one`, `.lit k`, and `.hat n d` can evaluate to the same
group element without being the same syntax tree.  The present development therefore keeps three
claims separate:

1. a display denotes a chosen 2-adic unit;
2. two displayed words have equal evaluations under every marking;
3. two words are literally equal as `PWord` syntax.

No theorem in this layer upgrades (2) to equivalence of pro-2 presentations.  That would require a
separate invariance theorem saying that replacing a relator by a universally equal evaluation
preserves the relevant closed normal subgroup/presentation.  Likewise, the inverse step suggested
by the informal paper is not yet formalized: the current `Zhat` API exposes the additive profinite
exponent group, but not enough multiplicative/composition structure to prove that powering by the
exponent attached to an arbitrary 2-adic unit is an automorphism with the expected inverse.

Consequently this seam is total at the semantic-word level and honest at the selected-display
level, but it is not yet a proof of the paper's full arbitrary-unit presentation conjecture.
