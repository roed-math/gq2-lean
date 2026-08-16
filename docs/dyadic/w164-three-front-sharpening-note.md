# W164: three-front generic-family sharpening

This wave advances all three remaining generic-family fronts with kernel-checked, bounded
results.

## Compact-M pivot: full automorphism no-go

`M0C0PivotAutomorphism.lean` upgrades W163's cup-level obstruction to actual continuous
automorphisms of `DM alpha h`.  The transported presentation gives an automorphic obstruction
functional; uniqueness of the injective map from degree-two cohomology to `F2` proves invariance
of the full even cup form.  Independently, `mChi_row_extract` proves that a `chiM`-preserving
automorphism preserves the full additive D-coordinate.

The D-character is the cup-dual of canonical C0.  Combining these facts proves
`isUnit_dmC_aut_iff`: the C0 value of every 2-adic marking is a unit before an oriented
automorphism exactly when it is a unit afterward.  `no_oriented_dmC_unitizer` is the direct
no-go.  The selected general-h M0 pivot therefore cannot be normalized away by any oriented
continuous automorphism, not merely by the previously audited Eichler shear.

## Odd L: clearing reduced to the true two-row input

`GammaLOddNuRowsFinal.lean` uses the already-landed general-h theorem `gOdd_nuClear` to prove
that `SqNuForwardSupply` is equivalent to the older full supply packet.  The new final endpoint
`gammaR_lSq_equiv_galK_oddDegree_of_nuRows_final` needs only the two sigma/x0 marking rows,
besides the ordinary tame/field inputs and universal ramified-data packet.  The old explicit
clearing, frame, cup, and relator binders are not active residuals.

## Uniform Mpc: arbitrary-h ramified phase layer

`MpcHandlePhaseData.lean` constructs resolved families for both scaled-pivot rows, packages the
arbitrary-h compact normal forms, transports the word lift, and proves the honest ramified
compact-wall phase for arbitrary display parameters.  Its comparison theorem reduces the
ramified source comparison to the projected head-phase equality.

The remaining uniform Mpc analytic atom is now specifically the unramified arbitrary-display,
general-h QZero formula.  Existing unramified Hessian results cover only the frozen
`eta = one`, `h = 0` lane.

All new public declarations have the standard three foundational axioms, except the odd field
endpoint which inherits only the already-recorded general-assembly arithmetic foundations.
