# W208: the finite four-core range problem

W207 packages the one-handle correction as four finite constrained coordinates. W208 gives
that source its coordinatewise group structure and proves that the stage shift is a group
homomorphism

`OneHandleBalancedCoreLevelCorrection k -> zLayer (DM 2 1) k`

for every `k >= 3`. The proof embeds the constrained source into the existing raw depth
corrections and applies the established `evenRawDepthShiftHom` factorization.

For every balanced point, `balancedCorrectedRelator_mem_twoCentralSeries` puts the inverse
current relator in the same central layer. The theorem
`exists_levelCorrection_iff_target_mem_range` then identifies the W207 finite word equation
with membership of that target in the range of the finite shift homomorphism.

Thus `OneHandleBalancedCoreRangeSupply` is exactly equivalent to the prior finite-equation
supply, and `mpcPivShiftH_two_one_of_balancedCoreRange` is its final consumer. The remaining
mathematics is a constrained finite range/spanning statement. Representative lifting,
inverse-limit compactness, generation, nonlinear correction packaging, and target layer
membership have all been discharged.

Every declaration has exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`.
