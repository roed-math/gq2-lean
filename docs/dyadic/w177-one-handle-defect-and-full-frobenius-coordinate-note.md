# W177: one-handle defect and the full Frobenius coordinate

W177 makes the first nontrivial general-h Mpc case and the abstract full-unramified quotient
completely explicit.  It introduces no axiom and no downstream analytic premise.

## The one-handle Mpc defect

`MpcGeneralHandleDefectAbsorption` computes how a left correction `d -> z*d` changes the compact
core word.  The multiplier is exactly `conjP (commP c z) d`.  Since the standard core word in
`DM alpha h` is the inverse handle word, the missing stabilization equation is now the explicit
nonabelian equality recorded by `MpcStandardDDefectAbsorption`.

At `h=1`, `MpcOneHandleDDefectAbsorption` specializes its target to the inverse commutator of the
single standard handle pair.  The module proves that this datum gives
`MpcStandardHandleExtension` and hence `MpcPivShiftH 2 1`.  It also proves
`mRelWord_mulEquiv_eq_one_iff`: a uniform same-h automorphism cannot turn a nontrivial full
relator defect into one, so the required correction genuinely acts on the lifted core marking.

## The full unramified coordinate

`RamifiedCertificateQurZhatFrobeniusComparison` constructs an unconditional continuous
equivalence

`qurQEquivZhat q : QurQ q ~= Zhat`,

normalized by `qSigmaQ -> 1`.  The theorem `maxProPMk_qurQEquivZhat_qMkQ` identifies `nuTq`
exactly with the pro-2 projection of this full coordinate.  This formally explains the W176
information gap: AX4 controls the pro-2 shadow but not the odd-primary unramified coordinate.

The remaining field datum is `AbsoluteUnramifiedFrobeniusCoordinate T`: a continuous
equivalence from the canonical quotient by absolute inertia to `Zhat`, satisfying one commuting
coordinate square with `T.tameFK`.  It constructs the W176 quotient comparison, the canonical
full-inertia containment, and `CompatibleResidueLiftAt`.

Both modules compile at default limits.  Every public declaration uses at most `propext`,
`Classical.choice`, and `Quot.sound`.
