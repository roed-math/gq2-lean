# W361 common even-phase polar normal certificate

## Scope

`Instances/WordPhasePolarNormal.lean` is an additive, basis-independent certificate for the
already defined phase `WordPhase.wPhCompactWallHandlePhase q h`. It does not modify any source
certificate, claim a new source-to-phase equality, or assert owner approval to replace the old
ledger appendices. It is a staged compositional acceptance artifact to be combined with the
existing exact phase-comparison theorems.

Write `B(v,w) = polar q v w` and

```
Q(c0,c1,(uj,vj)j) = q(c0) + B(c0,c1) + Σj B(uj,vj).
```

The complete reduced polar form is

```
B(c0,d0) + B(c0,d1) + B(c1,d0)
  + Σj [B(uj,vj') + B(vj,uj')].
```

Thus its head is `[[B,B],[B,0]]`, every handle is `[[0,B],[B,0]]`, and all off-block
entries vanish. This retains the quadratic head term: it does not incorrectly call Q a sum
of purely hyperbolic quadratic functions.

## Explicit matrix and inverse

The literal finite coefficient matrix is `reducedCoefficientMatrix h`, indexed by
`Fin 2 ⊕ (Fin h × Fin 2)`: the two head coordinates, then both coordinates of each handle.
Each scalar coefficient multiplies B; no basis of V or identification of B with the identity
matrix is assumed. `polar_compactPhase_reducedMatrix` proves equality with its full double
matrix sum, not merely a nonsingularity statement.

```
headMatrix        = [[1,1],[1,0]]
headInverseMatrix = [[0,1],[1,1]]       over F₂
handleMatrix      = [[0,1],[1,0]]      = its inverse.
```

`reducedInverseMatrix h` is the corresponding block-diagonal inverse. The two theorems
`reducedCoefficientMatrix_mul_inverse` and `reducedInverseMatrix_mul_coefficient` check both
full products uniformly in h, including h=0.

Relative to the coordinatewise B-pairing, the polar operator is the explicit additive
equivalence

```
J(c0,c1,(uj,vj)j) = (c0+c1,c0,(vj,uj)j),
J⁻¹(d0,d1,(aj,bj)j) = (d1,d0-d1,(bj,aj)j).
```

`polarBlockEquiv` includes both inverse identities. The factorization theorem is
`polar_compactPhase_eq_coordinatePairing`; `coordinatePairing_eq_polar_inverse` gives the
inverse form of that identity. The inverse uses subtraction on an arbitrary additive group;
on an exponent-two group this is addition, agreeing with the displayed F₂ inverse block.

## Nonsingularity and trust

`coordinatePairing_left_eq_zero` tests one coordinate at a time and uses only nonsingularity
of B. `nonsingular_compactPhase` then uses J's injectivity. `isQuadratic_compactPhase` derives
quadraticity from the explicit biadditive polar expression.

The hypotheses are only an additive commutative group V and `IsQuadraticFp2 q`; nonsingularity
additionally requires `Nonsingular q`. No basis, finite V, cardinality, positive handle count,
word-specific condition, or new arithmetic premise is introduced. All theorem pins are at
most the standard three axioms. Compilation uses default Lean settings, with no new axioms,
placeholders, options, or numerical rank bound.

The existing `WordPhase.wPh_compactWallHandlePhase_gaussSum_standardRam` and unramified twin
remain the separate checked Gauss-value endpoints. This polar certificate does not silently
replace their cardinality hypotheses or the semantic QZero-to-Q comparisons.
