# W200: the balanced one-handle base stage

W199 constructs a one-handle balanced seed satisfying its four forgetful-fibre equations,
kernel equation, universal `C + 2 B` row, and mod-two independence.  W200 proves that the
remaining relator-defect condition is automatic through the Frattini stage.

`MpcBalancedBase.mWord_mem_two` observes that every `M₂` core word is a product of squares
and commutators, hence lies in `λ₂`.  Normality of the lower 2-central series then gives
`oneHandleDDefect_mem_two` for arbitrary five-tuples, including the conjugated correction and
the inverse standard handle commutator.  Combining this universal fact with W199's seed yields
`oneHandleBalancedSet_nonempty_of_le_two`: every balanced finite set at depth `k ≤ 2` is
nonempty.

All three declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`.  The first
unresolved finite stage is now depth three, where the defect is measured in the elementary
graded layer `λ₂/λ₃`.  No fixed-`C` surjectivity premise is reintroduced.
