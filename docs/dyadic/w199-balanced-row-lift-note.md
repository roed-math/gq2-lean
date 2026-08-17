# W199: balanced row lifts and Frattini independence

W198 rules out the final fixed-`C`, one-slot repair of the one-handle stabilization problem.
W199 turns to the honest balanced multi-slot inverse limit and separates its linear conditions
from the genuinely nonabelian relator defect.

`MpcBalancedRowLift.lean` proves three unconditional results.  First,
`exists_rowCorrectedLift` clears both handle coordinates of any lift of the compact pivot row
without changing its handle-forgetting image.  The remaining abelian discrepancy has order
two, hence every continuous `ℤ₂`-valued character kills it; the corrected lift therefore has
the universal `C + 2 B` row.  Second, `oneHandleModTwoIndep_of_fibers` proves that four lifts of
an automorphic compact basis, together with the standard handle pair, remain independent
modulo every index-two open normal subgroup.  Such a quotient kills the handles and factors
through handle-forgetting, where the compact automorphism forces it to be trivial.  Third,
`exists_oneHandleBalancedSeed` packages the fibre equations, universal row, and Frattini
condition into one balanced point.

All three public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.  No
finite-level relator lift is asserted.  The sole remaining one-handle input is now exactly the
last clause of `oneHandleBalancedSet`: for every depth, jointly choose the seed so that its
nonabelian relator defect lies in the requested lower-central term.  The landed compactness
theorem already turns those per-depth choices into an exact marking and `MpcPivShiftH 2 1`.
