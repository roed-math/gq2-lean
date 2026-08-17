# W205: the balanced four-core shift

W204 expresses the one-handle climb as a five-factor finite-quotient shift. The apparent
fifth slot is redundant: the balanced `z` and `d` factors enter the corrected marking only
through the single `D` correction

`d^-1 * e_z * d * e_d`.

`MpcBalancedCoreShift` packages four independent core corrections, with both handle
corrections trivial. All four rows lie in `lambda_(k-1)` and in the handle-forgetting kernel;
the `C` row is additionally killed by every continuous `Z_2`-valued character.

The maps `coreCorrectionToBalanced` and `balancedCorrectionToCore` prove both directions.
The forward map takes `e_z=1`. The reverse map combines `e_z` with `e_d`; normality of the
two-central series preserves its depth, and the handle-forgetting equation is preserved
exactly. The theorem `nonempty_coreShiftCorrection_iff_shiftCorrection` therefore proves
that the four-slot formulation loses no solutions.

Consequently `OneHandleBalancedCoreShiftSupply` is equivalent to the W204 supply, and
`mpcPivShiftH_two_one_of_balancedCoreShift` is its final conditional consumer. The remaining
problem is now a constrained four-core-row image problem for the already identified
`evenRawDbarWord`; there is no independent `z` direction left to analyze.

Every declaration has exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`. No reachability assertion is assumed.
