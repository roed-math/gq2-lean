# W95: sparse Lean certificate for the M6 sixth rung

Date: 2026-08-16

## Result

`GQ2/Dyadic/Instances/MpcMarkedSixCertificate.lean` records the 18-factor natural certificate
found by W94 and proves every carrier and depth obligation using the existing Lean calculus.

The four explicit correction words have seven, five, two, and four factors.  The head,
`Bbar`, and `Dbar` corrections lie in `mpcSxKill 4`; the pivot correction lies in
`mpcMkPivotKill 4`.  They therefore form an unconditional `MpcMkFullMove 4`.

## Exact residual

The sole remaining finite calculation is named `MpcMkC6CertificateKill`:

```text
levelMk (D_M 2 0) 6
  (defect(W5) * increment(us, ut, um, un)) = 1.
```

This is a proposition definition only.  It is not asserted, axiomatized, or stored as an
unproved structure field.  From a proof of that equality the module derives
`MpcMkFullSupply 4 mpcFvW5` and the exact `j = 4` existential consumed by the ladder.

Thus the formal sixth-rung blocker is no longer an unspecified search or carrier question.
It is one concrete quotient equality whose truth is independently certified by both exact
Magma scripts from W94.  Proving the equality in Lean still requires a class-six collection
or finite-quotient reflection argument absent from the current tree.

## Uniform route

The exact marked cost image at class six has corank five.  Four coordinate Fox derivations
give only a necessary envelope of codimension at most four, so cost-image equality with that
envelope is impossible.

The narrow sufficient uniform statement is propagation for the actual defect family: if a
class has a solution whose top defect lies in its fiberwise marked cost range, then the next
class has such a solution.  The existing `j = 3` theorem and this explicit `j = 4` certificate
are the base cases; the missing theorem is the restricted propagation step for `j >= 4`.

## Verification surface

All twelve declarations are standard-three: `propext`, `Classical.choice`, and `Quot.sound`.
The module introduces no axiom, `sorry`, `native_decide`, or option override.
