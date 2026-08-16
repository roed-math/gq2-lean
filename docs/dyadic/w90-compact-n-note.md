# W90: compact-N determinant data

Date: 2026-08-16

## Result

`GQ2/Dyadic/Instances/WordPhaseCompactNData.lean` discharges the branch-free determinant
supply for the compact `N` family.  The frozen `sqrt(-2)` acceptance theorem now takes only
the two pre-existing coefficient-stage vanishing statements.  It no longer takes a
determinant supply binder.

## Construction

The source comparison is built at every boundary lift by splitting on the action of tame
inertia at the faithful head quotient.

* In the unramified branch, tame inertia dies at the head.  The head is cyclic on `sigma`,
  simplicity and nontriviality make `sigma` fixed-point free, and
  `wPmCompactPhaseComparison_of_headPhase` applies.
* In the ramified branch, the normality and odd order of the tame inertia subgroup make
  `tau` fixed-point free while its `omega2`-part acts trivially.  The shared ramified Fox row
  gives the same two-head-coordinate normal form.  The generic normal-form assembler then
  produces the comparison.
* Both branches use `wPs_wPmCompactHeadPhase_of_headFactorization`, so the endpoint in each
  case is exactly `wPhCompactWallHandlePhase`.

The boundary theorem packages the head factorization, wild-letter death, simplicity, and
the action dichotomy.  `wPcN_branchFreeSupply` then combines the comparison with the existing
Gauss sum calculation for the even endpoint form.

## New endpoints

* `wPcNComparison_unramifiedHead`
* `wPcN_compactNormal_closed_ramified`
* `wPcN_compactNormalForm_ramified`
* `wPcNComparison_ramifiedHead`
* `wPcNComparison_boundary`
* `wPcN_branchFreeSupply`
* `wPcN_candidate_equiv_galK_sqrtNegTwo`

The first six declarations are standard-three.  The frozen row endpoint has exactly the
same arithmetic axiom set as its former branch-free-binder parent.

## Remaining compact work

The two compact `M` rows still need the corresponding data package.  Their unramified branch
uses the `P = 1` Hessian endpoint.  Their ramified branch requires the `P = 0` block-swapped
endpoint together with a coordinate swap in the phase normal form.  That is the next wave.
