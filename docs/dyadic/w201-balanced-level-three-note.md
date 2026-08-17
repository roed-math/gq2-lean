# W201: the balanced level-three cup boundary

W200 makes the balanced one-handle construction automatic through `λ₂`.  W201 identifies the
first informative defect class in `λ₂/λ₃` with the intrinsic even cup form.

`MpcBalancedLevelThree.mRelWord_mem_three_of_cupAdapted` feeds a cup-adapted rank-six marking
into the existing generic level-three transgression theorem, proving that its full `M₂`
relator lies in `λ₃`.  `oneHandleDDefect_eq_conj_relWord` then identifies the balanced defect
as a conjugate of that full relator.  Hence `oneHandleDDefect_mem_three_of_cupAdapted` and
`oneHandleBalancedSet_three_nonempty_of_cupAdaptedSeed` close the depth-three condition from a
single finite datum, `OneHandleCupAdaptedSeed`.

All declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`.  Existence of a
cup-adapted seed is not asserted: it is now the precise finite linear problem at the first
nontrivial stage.  Neither disproved fixed-`C` bracket-surjectivity premise is used.
