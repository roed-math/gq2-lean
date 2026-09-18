# W361: original Hessian and phase-cover records at arbitrary handle rank

This is a checked compositional certificate artifact, not an assertion that the
owner has approved replacing the old acceptance-ledger appendices. It preserves
the actual corrected/spliced M words; it proves no equality with a frozen M word.

## What is now packaged

`Instances/WordPhaseCompactCertificates.lean` constructs the original
`PhaseCoverCertificate` for

```
Q(c0,c1,(uj,vj)) = q(c0) + Bq(c0,c1) + sum_j Bq(uj,vj).
```

Its head inclusions are literally `j0(v)=((v,0),0)` and
`j1(v)=((0,v),0)`. The diagonal is `dat.f(v,v)`, using the actual factor-set
identity, not just an equality of polar forms. If `#V=2^d`, the record has
`baseDim=(h+1)*d`, `baseSign=1`, cardinality `2^(2*(h+1)*d)` and Gauss sum
`2^((h+1)*d`. Every handle is present; there is no rank bound.

An additive `SourceWordPhaseComparison` becomes an F2-linear change of variables
with exactly the same forward and inverse maps. The source quotient's F2 module
structure is derived locally from exponent two, and its coefficient dimension
is derived from finite F2 cardinality. No module, cardinality, normal-form,
quadratic-identity or Gauss-value hypothesis is added to the word-specific
comparison.

`sourceCompactHessianOfComparison` then constructs the original
`HessianCertificate`, not a replacement record. Its source quadratic form is
the actual descended phase `QZeroBar DD rho htriv` on
`VCocycle DD rho / vCobRange DD rho`. Thus the word tie is the existing full
source phase comparison, including its quadratic diagonal. This is not an
identity on arbitrary unreduced generator cochains.

## Actual M word adapters

`Instances/TameSpliceHessianCertificates.lean` provides:

| API | Actual source and branch |
| --- | --- |
| `pairUnramifiedHessian` | The normalized, prime-to-two-corrected pair splice |
| `nonempty_mobileUnramifiedHessian` | The corrected mobile splice at every level, power, semantic unit and handle rank |
| `tameSpliceRamifiedHessian` | The common compact-template ramified splice, including its additive head swap |
| `pairRamifiedHessian` | The actual pair word, discharging its Stokes supply, specialization and endpoint inputs |
| `mobileRamifiedHessian` | The actual mobile word, discharging the same structural inputs |

These retain the existing projected-boundary/action hypotheses. The pair source
still has a selected handle `j : Fin h`; the mobile source includes `h=0`.
The concrete source supplies use the established `alpha >= 2` assumption.
The mobile unramified producer returns `Nonempty` because its existing additive
phase-comparison producer is existential. It does not assume a new comparison.

## Arbitrary quadratic diagonal

`Instances/WordPhaseWallHandleCertificates.lean` retains a literal quadratic
diagonal `d0`, replacing only the first term by `d0(c0)`. It proves the full
polar formula with head blocks

```
[[B_d0, B_q], [B_q, 0]]
```

and one `[[0,B_q],[B_q,0]]` block per handle. Quadraticity of `d0` and `q`, and
nonsingularity of `q`, imply nonsingularity of the complete form without any
nonsingularity condition on `d0`. Its Gauss sum is still `#V^(h+1)`.

`wallHandlePhaseCover` is the original phase-cover record with diagonal `d0`;
`sourceWallHessianOfComparison` is the original source Hessian record from a
full additive comparison to this literal form. These generic records are ready
for the full-offset Npc diagonals; the actual Npc additive comparisons are a
separate module and must be applied before claiming a concrete Npc record.

## Verification and scope

The three modules compile with default Lean options. All 18 printed public
pins use exactly `propext`, `Classical.choice`, and `Quot.sound`. No axiom,
placeholder, option change, source-certificate weakening, class enumeration or
finite-exponent approximation was introduced. Compiled `.olean` files are generated in the
shared build cache; source-only umbrella verification remains a separate parent
integration check.

The basis-independent explicit polar matrix and inverse are recorded separately
in `WordPhasePolarNormal`; the actual full Fox row reductions and polynomial
pivot inverses are separate compositional artifacts. The present records add
the missing original-record packaging, rather than claiming those separate
matrices alone establish a quadratic identity.
