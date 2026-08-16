# W89-UNIFORM note: the odd route closes uniformly

Base `7e7179e5`, branch `dyadic`, completed 2026-08-16.  Verification used the campaign
mirror first, followed by the full umbrella and strict ledger gate.

## Result

`GQ2/Dyadic/SqCore/GradedRowUniform.lean` now proves every row-ladder rung on the whole unit
locus, uniformly in the class.  The chain is:

1. `gUni_knob_cost` realizes every knob-span defect as one admissible engine cost.
2. `gUni_step` climbs from a solution in class `j + 1` to one in class `j + 2` for `j ≥ 3`.
3. `gUni_nonempty` inducts from wave 87's class-four theorem and fills every class.
4. `gUni_pair` realizes every unit-locus row pair.
5. `gUni_clearing` proves `SqNuOrientedClearAtUnitPivot h` for every `h`, with no binder.

The field-facing consequences are also named in the module:

* `gUni_supply` proves `SqMarkedForwardSupply B h` at every odd degree with no clearing
  hypothesis.
* `gUni_gammaR_lSq_equiv_galK` reaches the public `Γ_L` equivalence with neither a clearing
  nor a supply hypothesis.

This discharges the last model-side input on the general odd-degree route.  It does not close
the compact determinant data, the `MpcPivShift 2` selector, or the parked even route.

## Axiom and honesty audit

Every public declaration in the module has an in-file `#print axioms` pin.  The construction
through `gUni_clearing` prints standard three or a subset.  `gUni_supply` adds the four
standing odd-seam census axioms.  `gUni_gammaR_lSq_equiv_galK` additionally carries the
standing `relativeStiefelWhitney_dyadic` input.  There is no `sorry`, new axiom,
`native_decide`, or heartbeat override.

The W88 partial-salvage notice remains in the module as a dated historical record and is
immediately superseded by a W89 status paragraph.  No negative statement was strengthened:
the unrestricted layer claim stays false, and the knob/cost identification is asserted only
on the unit locus where it is proved.

## Verification

* `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedRowUniform`: pass.
* `scripts/mirror.sh check GQ2/Dyadic/SqCore/GradedRowUniform.lean`: pass.
* `bash scripts/scoreboard.sh`: pass; `gUni_clearing` carries nothing and `gUni_supply`
  carries only the bundle, filtration, and degree equation.
* `lake build GQ2`: pass, 4,382 jobs.
* `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: pass, 34,302 tracked declarations,
  0 `sorryAx` dependents, 0 unknown non-standard uses, and 0 terminal violations.
