# W361: original L phase-cover and Hessian records, uniformly in h

This additive packaging concerns the actual improved source `GammaL = GammaR(lSqW h)`.
It neither changes that word nor introduces a rank bound, fixture, finite-exponent
approximation, new axiom or new certificate hypothesis. It is a staged
compositional artifact; approval of a replacement publication/acceptance-appendix
format is still a separate owner decision.

## The odd head is not the even compact head

The actual complete normal form is

```
Q(v,(uj,vj)) = qDouble(q,U)(v) + sum_j Bq(uj,vj),
qDouble(q,U)(v) = q(v) + Bq(v,Uv).
```

The head has one copy of `V`, not two. Its polar operator relative to `Bq` is
literally `J = 1 + U + U^-1`. At a source representation, `U` is exactly the
inverse action of the projected sigma raised to the existing uniform exponent
`omega2Exp (4 * exponent (SemiProd DD.C0 DD.Vmod))`. The ramified case does not
replace this operator by the identity.

`WordPhaseOddCertificates.wallPolarEquiv` has forward map
`v ↦ v + U v + U.symm v`. Its inverse is the inverse of this literal additive
map. Bijectivity follows uniformly from the existing two-power-period argument
(`onePlusUUsq_injective`) and finiteness. This is an exact inverse witness, but
not yet a displayed finite-polynomial formula for the inverse.

The two edge maps in the original phase-cover record are

```
j0(v) = (v,0),       j1(w) = (J^-1 w,0).
```

Consequently `polar Q (j0 v) (j1 w) = Bq(v,w) = dat.f(v,w)+dat.f(w,v)`, while
`Q(j0 v) = qDouble(q,U)(v)`. The diagonal is retained literally, not inferred
from the polar form. The complete polar matrix relative to coordinatewise `Bq`
has head block `J` and one swap block per handle. Full quadraticity and
nonsingularity are proved for every `h`, including zero.

## Signs and original records

If `#V = 2^(2m)`, the original `PhaseCoverCertificate` has
`baseDim = m*(2h+1)`. Its signed Gauss value is
`epsilon * 2^(m*(2h+1))`; the generic record does not force a positive sign.

The concrete original `HessianCertificate` endpoints are:

| Endpoint in `Instances/LHessianCertificates.lean` | Literal `baseSign` |
| --- | --- |
| `unramifiedHessian` | `-1` |
| `ramifiedHessian` | `+1` |

The two `*_baseSign` theorems check these fields by reflexivity. In the
unramified Arf-one case the fixed Wall operator gives the original quadratic
head and its negative Gauss sign, not the positive compact-M sign.

The concrete adapters recover their signed head Gauss value from the already
completed L branch phase model by exact reindexing between two comparisons of
the same source phase and cancellation of the positive handle factor. Thus no
new Arf, Gauss-value, normal-form or phase-identity premise is introduced.

The ramified adapter retains the existing `LRamifiedSourceArfData` parameter of
the old ramified head-data phase-model API. It does not assert that this datum is
automatic for arbitrary standalone representations. Existing campaign boundary
producers discharge it in their own scope.

## Actual coordinate maps and retained premises

`Instances/LPhaseAdditiveNormal.lean` proves additivity of the same actual
coordinate equivalences used by both branches. The unramified theorem applies
to `sourceWordPhaseComparison_of_lSqUnramifiedHead` itself. The ramified theorem
uses the existing actual action-source H1 equivalence and the proved projected
pointwise phase identity; it does not assume a new phase identity. The normal
maps, quotient map, normal-class inverse and handle rebracketing are all additive.

`sourceOddHessianOfComparison` promotes these maps to F2-linear equivalences
without changing their forward or inverse functions. Its source form is
`QZeroBar` on `VCocycle / vCobRange`, not arbitrary unreduced generator cochains.

Both concrete adapters retain the existing head projection, factor-set descent,
action compatibility and branch-data hypotheses. Unramified additionally uses
the old simplicity, positive half-dimension and cardinality inputs; ramified
uses the old finite head, cardinality and source Arf datum. Exponent two is
derived from the actual `DescData`. The two-power period of `U` is proved before
projection from the actual finite `DD.C0`, so no extra finite-head hypothesis is
introduced in the unramified adapter.

## Verification

The three new modules are `WordPhaseOddCertificates`, `LPhaseAdditiveNormal`,
and `LHessianCertificates`. All 23 printed public pins use exactly `propext`,
`Classical.choice`, and `Quot.sound`; compilation uses default Lean options.
They have no placeholders or option declarations. Shared-cache compilation is
separate from the parent-owned fresh source-only umbrella check.

The remaining artifact-level limitation here is the absence of a displayed
finite-polynomial formula for `J^-1`. The original record already contains a
checked inverse with a literal forward operator and exact edge maps. This note
does not conflate that fact with owner approval of the staged ledger format.
