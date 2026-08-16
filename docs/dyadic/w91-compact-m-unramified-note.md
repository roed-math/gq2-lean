# W91: compact-M unramified determinant data

Date: 2026-08-16

## Result

The compact-M determinant route is now closed through the source-to-word phase comparison in
the unramified `P = 1` branch.  The boundary theorem lands directly on the handle-free form
`plusFormD qbar qbar` on `Vmod × Vmod`.

This is not yet a branch-free determinant supply.  The honest ramified `P = 0` branch needs
one new full-word Hessian theorem described below.

## Construction

`GQ2/Dyadic/Instances/WordPhaseCompactMData.lean` combines three existing layers:

* the word-generic compact trace seam;
* the shared compact unramified Fox row and normal-form assembler;
* `MCompact.hessRelZ_mCompact_P1_plusForm`, the honest-resolver Hessian endpoint.

The head theorem exposes the weakest extra second-order input precisely: the image of `sigma`
raised to the compact trace resolver must act trivially.  This differs from the first-order
condition that `powOmega2 sigma` acts trivially.

`GQ2/Dyadic/Instances/WordPhaseCompactMUnramifiedBoundary.lean` derives both conditions at an
arbitrary unramified boundary lift.  The tame head is cyclic on `sigma`; simplicity makes
`sigma` fixed-point free and kills its two-primary action.  A generic resolver-transport lemma
moves this action statement through the faithful head quotient at the exact semidirect-product
exponent.  The resulting comparison is then reindexed across the unique `Fin 0` coordinate.

The main endpoints are:

* `wPcM_QZero_eq_compactWallPhase_P1_of_headMark`;
* `wPcMComparison_unramifiedP1_of_headPhase`;
* `wPcM_resolver_smul_of_powOmega2`;
* `wPcMComparison_boundary_unramifiedP1`.

All are standard-three.

## Why the old ramified P0 assembler does not close the branch

`M0Assembly.hessRelZ_mCompact_P0` assumes two statements that are unavailable at an honest
ramified boundary:

* the `sigma` two-primary action is trivial, although the legitimate fixed-point-free
  order-three example over the two-dimensional `F2` module has nontrivial `sigma` action;
* every lifted `(x_i tau)` omega2 block is individually trivial.

The second statement is false under the otherwise expected finite, elementary, equivariant,
fixed-point-free, and global-resolver hypotheses.  A checked finite model with `C = C3`,
`V = F2^2`, the order-three fixed-point-free action, the opposite invariant factor set,
`s = 1`, and global resolver value `9` has nonzero central charge for the lifted `x_0 tau`
block.  Thus adding the separate `sigma` premise would still not justify the per-letter
shortcut.

The existing ramified mixed-Heisenberg theorem avoids this problem by canceling the central
charges only after the whole compact-M word is assembled.

## Exact remaining theorem

The required replacement is the kappa-zero/Hessian analogue of that full-word cancellation.
At handle count zero it should prove

```text
hessRelZ (hessMark s u ![c0, c1, 0]) (kappa0Cocycle dat hdat)
  E E2 (mCompactW alpha 0)
    = q c1 + polar q c0 c1
```

under the finite elementary-module hypotheses, fixed-point-free `u`, trivial action by
`powOmega2 u`, and the four honest resolver-lift conditions.  It must not assume trivial
`powOmega2 s` action or per-letter central-charge vanishing.  Proving this quadratic-shadow
bridge is the remaining compact-M analytic obligation.

No new axiom, `sorry`, `native_decide`, or option override is introduced in this wave.
