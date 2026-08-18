# W253: four elementary-dual coordinate equations

W253 expands the W252 span-annihilation condition into exactly four equations.  An ambient
`ZMod 2`-functional annihilates the direct coordinate span if and only if it kills every
value of the A, B, C, and D shift families separately.

The direct successor therefore exists exactly when every functional satisfying those four
row equations kills the target.  Failure is witnessed by one functional satisfying all four
equations but taking value one on the target.  Uniform target vanishing again implies
`MpcPivShiftH 2 1`.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  This wave does not
assert vanishing; it exposes the exact four finite-linear equations to compute.
