# W361 ramified Fox matrix elimination

Status: additive, checked compositional certificate artifact. This does not assert owner
approval of a replacement ledger appendix, alter a source certificate, or replace a
full-differential statement by a kernel-only claim.

## Actual matrix and explicit invertible operations

Write S and T for the sigma and tau actions on the finite additive coefficient group A.
The actual ramified differential of the compact-template splice is

| Row / column | sigma | tau | x2 | every other wild column |
| --- | --- | --- | --- | --- |
| tame | U = S⁻¹(T−1) | L = S⁻¹−N_q(T) | 0 | 0 |
| word | 0 | 0 | D = −S⁻¹ | 0 |

Here `N_q(T) a = sum_{i=0}^{q-1} T^i a`; the order of composition in U is retained.
T fixed-point-free and A finite make T−1 invertible. The sigma action need not be trivial,
fixed-point-free, or have trivial two-primary part.

`SigmaRamifiedFoxElimination.columnShear U L` is the domain additive equivalence

```
x_sigma := x_sigma - U⁻¹(L x_tau),
x_tau   := x_tau,
x_wild  := x_wild.
```

Its inverse uses `+ U⁻¹(L x_tau)`. `rowScaling U D` applies U⁻¹ and D⁻¹ to the two rows;
its inverse applies U and D. The pivot definitions include

```
U⁻¹ = (T−1)⁻¹ S,
D⁻¹ = −S.
```

The checked all-cochain equation is

```
rowScaling U D (d (columnShear U L x)) = [x_sigma, x_x2].
```

Thus the reduced matrix has two identity pivots at sigma and x2, with every other column
zero. The generic theorem is `reduced_rows_of_ramified`; `reduced_rows_of_action_row`
substitutes the literal U,L,D action operators. `kernel_columnShear_iff` is a consequence,
not the premise used to infer matrix equality.

## Bridge to the actual words

`Instances/TameSpliceRamifiedFoxNormal.lean` uses the established equality of complete
differentials `heisD1_tameSplice_mCompact_ramified_of_projected`. Its
`tameSplice_ramified_rows` exposes the literal full row, and
`tameSplice_ramified_reducedFox` applies the explicit operations.

The hypotheses remain visible:

- finite acting groups C,D and finite exponent-two additive A;
- a surjective projection pi:C→D compatible with the two actions;
- wild generators map to one in D (they need not be one in C);
- the actual tame relation at nonzero even q;
- tau is fixed-point-free on A and its omega-two part acts trivially;
- the structural source R tame-specializes and has the pinned Stokes endpoint.

The resolver is exactly the coefficient-independent pinned family at `4 * exponent C`.
The word is the actual `tameSplice R (mCompactW alpha h)`, including normalization and
prime-to-two correction when R is one of the selected structural words.

`pairSplice_ramified_reducedFox` and `mobileSplice_ramified_reducedFox` discharge the
structural specialization/endpoint inputs for the actual pair and mobile constructors.
They are uniform in alpha, all handles, the selected pair handle, and the mobile r,p and
arbitrary two-adic unit. Pair has j:Fin h; mobile includes h=0. Their alpha≥1 hypothesis
belongs to the source constructor. No hU/hD premise is needed for these first-jet identities;
the stronger source-certificate hypotheses are not being removed from their own theorems.

## Verification

Both modules compile warning-free at default settings. All fourteen printed pins are at
most the standard three axioms. No new axiom, placeholder, option override, finite-rank
enumeration, or frozen-word equality was introduced. Existing unramified Fox files were
imported for the reusable action equivalence but not edited.
