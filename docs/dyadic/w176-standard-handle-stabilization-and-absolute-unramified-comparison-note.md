# W176: standard-handle stabilization and absolute unramified comparison

W176 replaces two broad construction requests by exact algebraic interfaces.  It does not add
an analytic, determinant, or corrected-RN premise.

## Standard-handle stabilization

`MpcGeneralHandleStandardStabilization` constructs the canonical surjection

`dmForgetHandles alpha h : DM alpha h -> DM alpha 0`.

It retains the four core generators, kills all handles, and preserves `chiM`.  The direction is
important: there is no canonical section sending the compact core letters back to the standard
general-h core letters, because the latter core word is cancelled by the nontrivial handle block.

`MpcStandardHandleExtension` is the exact missing lift datum.  It asks for four lifts of a compact
shift witness whose core word equals the general-h core word, whose adjoining standard handles
topologically generate, and whose C row is the universal odd `C + 2 B` row.
`mpcPivShiftH_of_standardHandleExtension` turns this datum into the full relator marking, and
`MpcPivShiftStandardStabilization alpha h` packages the assertion uniformly over compact shift
witnesses.  Since the compact alpha-two shift is already proved,
`mpcPivShiftH_two_of_standardStabilization` leaves only this stabilization theorem at arbitrary
handle count.

## Absolute unramified quotient comparison

`RamifiedCertificateAbsoluteUnramifiedQuotientComparison` defines the canonical quotient of
`GalK K` by the pullback of `absoluteInertiaSubgroup`.  The substantive comparison datum
`OrientedAbsoluteUnramifiedQuotientComparison T` is a commuting group equivalence

`QurQ (qOf K FF) ~= GalK K / absoluteInertiaK`.

It carries `qMkQ (T.tameFK g)` to the canonical quotient class of `g`.  From this datum the module
proves the pointwise inertia equivalence, equality of the two kernel subgroups, the W175 canonical
full-inertia comparison, and `CompatibleResidueLiftAt`.

The base AX4 interface cannot construct this equivalence: its orientation and density clauses
identify only the 2-primary coordinate `nuTq`, while Mathlib's residue-action API supplies the
canonical kernel but no comparison with the abstract `QurQ` quotient.

## Compact-M audit

The selected M0 witness contains the cyclotomic splitting and level arithmetic but no cup or
pivot placement.  Consequently the exact W174 boundary is unchanged: identify transported D
with the filtration-uniformizer Kummer class and prove the single uniformizer Artin value.

Both W176 modules compile at default heartbeat and recursion limits.  Every public declaration
uses only `propext`, `Classical.choice`, and `Quot.sound`.
