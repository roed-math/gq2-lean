# W98: honest ramified compact-M graph data

Date: 2026-08-16

## Result

The handle-free ramified compact-M Hessian now reaches the graph-trace and normal-form layers
needed by the source comparison.  No square-power action or per-letter vanishing premise is
used.

`GQ2/Dyadic/Instances/KappaResolverTransport.lean` proves that a surjection from a finite
source group onto the semidirect head base transports the source exponent to a correct
constant resolver on the kappa-zero central extension.  The central `ZMod 2` fibre supplies
the only extra factor two, so no exponent-two hypothesis on the module is needed.

`GQ2/Dyadic/Instances/WordPhaseCompactMRamifiedData.lean` then provides:

* the natural ramified head phase `q c1 + polar q c0 c1`;
* its direct Hessian evaluation from W96;
* direct, projected, and surjective-head QZero graph-trace endpoints;
* closedness and uniqueness of the handle-free compact normal cochain for the ramified Fox
  row.

## Honest projection boundary

The projected endpoint keeps the trace resolver tied to

```text
omega2Exp(4 * exponent(SemiProd DD.C0 DD.Vmod)),
```

the source used by the graph trace.  It assumes only that projected wild heads are trivial,
the projected `tau` head has odd order and acts fixed-point-freely, and the factor set
transports through the head projection.  The surjective variant discharges resolver
correctness using the new transport theorem.

This matters because boundary wild heads need not be trivial in `DD.C0`; they become trivial
only after projection to the faithful tame head.  A direct-head shortcut would not close the
actual boundary.

## Remaining packaging

The complete source-comparison proof is known in scratch, but its monolithic constructor
exceeds the default elaboration heartbeat limit.  It is intentionally deferred to a smaller
second module rather than adding an option override.  No mathematical hypothesis is missing.

## Verification surface

All eight graph-data declarations and the resolver transport theorem use only `propext`,
`Classical.choice`, and `Quot.sound`.  The modules introduce no axiom, `sorry`,
`native_decide`, or option override.
