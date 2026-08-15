# W84-CLEAR lane note

Lane target: `gClear_clearing (h) : SqNuOrientedClearAtUnitPivot h`, the odd route's last item,
or the honest reduction. Module: `GQ2/Dyadic/SqCore/GradedClearing.lean` (prefix `gClear`),
green against the mirror at base `45f9c42d`. No sorry, no new axiom, no native_decide.

## Verdict up front

The unconditional clearing did NOT land, and the gap is NOT packaging. What landed is a
reduction that removes the marking quantifier from the residual: the clearing at every
jointly-surjective unit-pivot marking follows, through the wave-80 closure alone, from the
clearing at the EXPLICIT two-parameter family of model markings `nuSqOf h a b` (trivial handle
rows, forced x1-row). The residual is now a row-plane statement with no `forall nu'` in it.

## What the elaboration found (T-zero, the briefing's first question)

`gOdd_nuClear` and `gOdd_lamNuClear` are the clearing at markings whose two core rows are
EXACTLY `(1, 0)` (the selected fiber). The target Prop quantifies over markings with a UNIT
pivot row `d = nu'(sigma) - c0 nu'(x0)`, i.e. arbitrary rows `(a, b)` with `a - c0 b` a unit.
The conclusion parts are identical (`gOdd_markedMatching` vs the Prop's existential); the whole
distance is the two core rows. So the gap is exactly "move the rows", which is what the two
committed pivot families (`SqPivotTranslation`, `SqPivotScaling`) were for. Nothing at
`h >= 1` in the tree moves rows: the W81 oddid caution was right about that half, and the
h = 0 instances ride the arithmetic affine family of `D_0` (axioms B8 + B3c), which has no
`h >= 1` analogue.

## The engine that landed: `gClear_transport` (std-3)

For every marking `nu'` with unit pivot row `d`, rows `(a, b)`:

1. The committed lambda-twist `nuTwist nu' d^-1 b = d^-1 (nu' - b lambda)` (`HandleEichler`
   section 2) is a SELECTED marking, because the pivot is lambda-trivial: its rows are exactly
   `(1, 0)`. This is `nuTwist_sigma_eq_one` / `nuTwist_x0_eq_zero`, committed since the
   FixesCore era.
2. Wave 80's `gOdd_lamNuClear` corrects the twist onto `nu_sq` by an automorphism `u`
   preserving the FUNCTIONAL lambda on the nose (not merely mod 2).
3. Untwisting along the same `u` is legal because `u` preserves lambda exactly:
   `nu' o u = d nu_sq + b lambda`, and that combination IS the model marking `nuSqOf h a b`
   (`gClear_nuSqOf_eq_twist`, a `dsq_hom_ext` computation).

So `nu' o u = nuSqOf h a b` with `u` chi-preserving: every unit-pivot marking is
chi-equivalent to the model marking carrying its own rows. The wave-80 dividend DOES reach
arbitrary unit-pivot markings; what it cannot do is move the rows themselves.

## The residual: `GClearModelMove h a b`

`exists Psi chi-preserving with (nuSqOf h a b)(Psi sigma) = 1 and (nuSqOf h a b)(Psi x0) = 0`,
asked only on the unit locus `IsUnit (a - c0 b)`. Two rows, one explicit marking, no handle
clause, no marking binder. `gOdd_markedMatching` upgrades the two rows to the full correction
(`gClear_modelMove_full`), and:

- `gClear_clearing_of_model : (forall a b on the unit locus, GClearModelMove h a b) ->
  SqNuOrientedClearAtUnitPivot h` (std-3).
- `gClear_modelMove_of_ray`: the two one-parameter rays `GClearModelTranslate h c` (rows
  `(1 + c0 c, c)`) and `GClearModelScale h d` (rows `(d, 0)`, `d` a unit) generate the whole
  unit locus, via the rescaling identity `gClear_nuSqOf_smul` (the `s = 0` lambda-twist).
- `gClear_modelMove_of_families`: the committed families restrict to the model moves (one
  `sqCoreRows_of_pivotMove` application), so the new residual is weaker than every committed
  ask. `gClear_clearing_of_families` closes the clearing from the two families ALONE: the
  committed producer's `hfix` binder is wave 80's `gOdd_pivotFix`, discharged. Two binders
  against three, and the survivors consumed only at model markings.
- `gClear_modelMove_zero` / `gClear_clearing_zero`: the h = 0 instances from the committed
  degree-one seeds (std-3 + {dyadicOrientation, peripheralCyclotomicAction}); the new route
  reproves `oddFrame_clearAtUnitPivot_zero`'s statement end to end.

## The seam (acceptance composition)

`gClear_supply_of_model`, `gClear_supply_of_ray`: the row-plane family implies
`SqMarkedForwardSupply B h` at every `[K : Q2] = 2h + 1` through `oddFrame_supply`.
`gClear_branchL_of_model` gives the L-row branch datum; `gClear_candidateEquiv_of_model` gives
the general theorem at odd degree needing exactly `GenAsmFieldInputs` + `GenAsmRowResidual`.
All print std-3 + {hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
Foundations.absGalQ2_isTopologicallyFinitelyGenerated,
Foundations.absGalQ2_localEulerCharacteristic}; localReciprocity and markedRecipAt are binders
(`Rec`, `B`), not axioms, in these conditional forms.

## What W85 needs

`GClearModelTranslate h c` and `GClearModelScale h d` at `h >= 1`: the first row-moving
automorphisms the model side would ever produce. Assets the reduction has bought them:

- The instances are at SINGLE explicit markings. `nuSqOf h a b` kills every handle letter and
  (like any marking) the closed derived subgroup, and lambda kills the handle letters too, so
  correction words may now draw on the ENTIRE handle block plus commutators; the uniform
  moves' corrections had to be invisible to every marking (derived subgroup plus torsion
  only). The sign row costs nothing for automorphisms (`sqSign_of_aut`).
- The frame form (`DsqDemushkin` section 6b, `sqAutOfMark` + `sqSurjective_of_gens_mem_range`)
  removes the inverse-word and composition-identity burden: one relator-killing frame with
  generators in its range, lambda-rows standard, and the two nu-rows.
- The class-two balance (`PivotCoreMoves` module docstring) shows no obstruction on the unit
  locus, and pins the leading x1-slot correction.
- The determinant necessity is known at the family level
  (`isUnit_sqPivotDet_of_sqPivotCoreMove`). Whether the unit locus is necessary for the
  MODEL-MARKING move (sharpness of `GClearModelMove`'s hypothesis) was not settled here; the
  parity engine does not transfer verbatim because the weak move leaves handle rows free.

## Pins (all verified at gen time)

std-3: `GClearModelMove`, `gClear_modelMove_one_zero`, `gClear_nuSqOf_eq_twist`,
`gClear_transport`, `gClear_modelMove_full`, `gClear_clearing_of_model`,
`GClearModelTranslate`, `GClearModelScale`, `gClear_nuSqOf_smul`, `gClear_modelMove_of_ray`,
`gClear_modelMove_of_families`, `gClear_clearing_of_families`.
std-3 + {dyadicOrientation, peripheralCyclotomicAction}: `gClear_modelMove_zero`,
`gClear_clearing_zero`.
std-3 + {B11a, B7, two Foundations census members}: `gClear_supply_of_model`,
`gClear_branchL_of_model`, `gClear_candidateEquiv_of_model`, `gClear_supply_of_ray`.
