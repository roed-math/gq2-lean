# W296: the general Mpc tower closes the pivot shift

W296 supersedes the one-handle class-seven calculation as the Mpc pivot frontier.  The
class-seven modules remain useful finite diagnostics, but no class-specific statement is used
by the final proof.

The new marked finite-stage argument works for every `alpha >= 2` and every handle count.  It
reduces an arbitrary correction to active canonical tower brackets.  Even tower coefficients
move one level deeper, odd coefficients reduce to the canonical tower, and the existing
variable-rank square identity propagates the result through all higher rungs.  At the sole
base rung, two marked commutator corrections and one parameterized Jacobi identity cover every
active generator uniformly.  There is no enumeration of nilpotency classes or handle ranks.

The public endpoint
`MpcGeneralTowerFinal.mpcPivShiftH_all alpha h halpha` proves `MpcPivShiftH alpha h` for all
`2 <= alpha` and all `h`.  Its axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`.

For a family-selected epsilon-true Mpc branch, the exact `B` row combines with this uniform
shift to give the exact `C` pivot.  Consequently
`MpcGeneralTowerFinal.mpcRowResidualRN_of_familySelection_true` supplies the corrected RN
residual in arbitrary degree and handle count; its only surviving field-side premise is the
oriented presentation equivalence.  No shift, scaling, pivot, determinant, level, residue, or
display premise remains.

This does not assert the separate generic epsilon-false field-placement statement: there the
selected `B` row is one level deeper and cannot change the divided `C` digit.  That is a
field-orientation issue, not a remaining nilpotency-class calculation and not a limitation of
the uniform pivot theorem.
