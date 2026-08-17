# W187: the relative signed Frobenius boundary

W186 identifies the absolute residue Galois group and the absolute quotient by canonical inertia
with `Zhat`. W187 restricts that coordinate to a finite dyadic field `K`.

The canonical map `absoluteResidueCoordinateK : GalK K -> Zhat` has kernel exactly
`absoluteInertiaK`. Consequently canonical inertia is closed without any hypothetical field-side
coordinate, and the quotient by actual inertia embeds continuously into `Zhat`. Its image is
closed, and `absoluteUnramifiedCoordinateKEquivRange` is the continuous equivalence from the
actual quotient to that closed image.

The remaining comparison with an `OrientedTameQuotientK` is now one exact equation. If `f` is the
residue degree, `OrientedAbsoluteResidueFrobeniusCompatibility` states

```text
absolute square-Frobenius coordinate = (abstract tame coordinate)^(-f).
```

The minus sign is forced by conventions: the abstract tame generator is geometric, while square
Frobenius on the residue field is arithmetic. This equation implies that full abstract tame
inertia acts trivially on the absolute residue field. It therefore produces
`AbsoluteResidueCompatibleOrientedTameQuotientK` and the full `CompatibleResidueLiftAt` packet.

All thirteen public declarations in
`RamifiedCertificateRelativeFrobeniusCompatibility.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The remaining residue theorem is no longer quotient topology, absolute residue Galois theory, or
kernel closedness. It is precisely the signed relative Frobenius equation above. The existing AX4
interface determines only its maximal pro-two projection and does not prove the prime-to-two
coordinate. The anchored norm side remains the separate full-inertia unit refinement and
unit-spectral reciprocity problem.

Verification passes the 4,534-job build, fresh 1,122-module scoreboard, and full ledger gate over
45,182 tracked declarations, with zero `sorryAx` dependencies, zero unknown non-standard axiom
uses, and zero terminal violations.
