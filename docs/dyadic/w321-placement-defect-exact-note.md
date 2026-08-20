# W321: the exact residual obstruction is pivot placement

W321 combines two general facts: every canonical selected M row has an intrinsic exact mobile
pivot, and W320 identifies corrected-RN residual existence with the canonical boundary.  It
therefore proves

`HasSelectedRowResidualRN B FF S ↔ ¬ CanonicalPivotPlacementDefectBoundary B S`

for the canonical range-based selection.

The new defect is false by definition on the already closed L, N0, Npc, and epsilon-true Mpc
rows.  On M0 and epsilon-false Mpc it says exactly that an exact cyclotomic-kernel value exists
but cannot be placed on the distinguished `C` coordinate.  Pivot existence is already closed;
canonical placement is the whole remaining even-family problem.

This is a general all-degree statement.  It also makes clear why further isolated nilpotency
class computations are not the critical path: they cannot change the field-side placement
defect.
