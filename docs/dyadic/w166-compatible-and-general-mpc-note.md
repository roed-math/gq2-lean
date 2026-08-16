# W166: compatibility-aware ramified data and general Mpc realization

Wave 166 converts two broad residual packets into their exact local inputs and
closes the algebraic part of the arbitrary-h Mpc field realization.

## Full general-h Mpc correction

`MpcGeneralHandleCertificate` composes W165's scaled handle clearing with the
existing exact rank-four moves.  `markedMatching_of_scaling` reaches the full
arbitrary-display marking `mpcNuPadic`; `certificate_of_oriented` packages the
result as the corrected general-h certificate.  Both retain an explicit
`MScalingHypothesis` and the scaled C-pivot row and use only the standard three
axioms.

`MpcGeneralHandleFamily` then reads the selected `.Mpc` branch data.  The exact
level supplies the filtration condition, `IsEtaFor` supplies the D residue,
and the `lambda(-1)` row supplies the B residue.  Consequently
`certificate_of_familySelection` and `realization_of_familySelection` retain
only:

1. an oriented equivalence;
2. a scaling face;
3. the transported C-pivot at level `r`.

The convenience theorem using the repository's canonical scaling witness
records its inherited `peripheralCyclotomicAction` dependency separately; the
explicit-scaling route remains standard-three.

## Projected unramified Mpc data

`MpcUnramifiedProjectedData` proves that resolver lifting descends through a
surjective projected action.  For every selected display it constructs the
source resolved-family row at the honest exponent, identifies the projected
pivot with sigma, and transports fixed-point-freeness from the projected odd
head.  Thus the sole first-order premise left visible in W165's unramified
comparison is now supplied by the projected boundary data.  The QZero and
boundary-supply assembler remain a separate next step.

## Compatibility-aware odd-L ramified data

The legacy `ramifiedData` interface quantifies over unrelated finite maps.
`RamifiedCertificateCompatible` instead assumes the actual factorization

```text
rho g = c (tame g).
```

Surjectivity of `tame` selects a canonical lift of the tame involution and the
factorization proves its required image equation.  The corrected
`CompatibleRamifiedData` packet therefore retains exactly two arithmetic
atoms at W165's anchored field:

1. residue-triviality of that selected lift;
2. `InvolutionFieldPackage`.

No legacy API is weakened or silently assumed.  The next odd-L step is to
thread this compatibility-aware packet through the actual local-Gauss and
final reconstruction consumers.

## Verification

All public declarations compile at the default heartbeat limit.  The explicit
Mpc and compatibility interfaces use only `propext`, `Classical.choice`, and
`Quot.sound`; certificate builders inherit only the already declared
`tateDualityAt`, and the canonical-scaling convenience theorem separately
exposes `peripheralCyclotomicAction`.
