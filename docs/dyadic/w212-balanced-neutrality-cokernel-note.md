# W212: splitting the relative and neutral-C obstructions

W212 refines W211's finite cokernel into two honest stages. In the relaxed span, all four
core coordinates range over the ordinary handle-relative layer. The new
`oneHandleBalancedCoreRelativeShiftCRelaxed` has the same `[p,D]` formula as the constrained
`C` row, but it does not require the representative `p` to vanish under every continuous
`Z_2`-valued character.

The original four-coordinate span is contained in this relaxed span. The first finite
cokernel therefore asks whether the four ordinary relative rows cover the current target.
Once that holds, `OneHandleBalancedCoreNeutralityCokernel` quotients the relaxed span by the
original constrained span and measures only the extra neutral-`C` requirement.

Uniformly, `coordinateSpanSupply_iff_relative_and_neutrality` proves that W210's exact supply
is equivalent to ordinary-relative coordinate coverage together with vanishing of this
second neutral-`C` obstruction. Thus a future calculation can attack the two genuinely
different issues separately without claiming that an unrestricted raw correction recovers
either constraint.

Every public declaration has exactly the standard axiom set `propext`, `Classical.choice`,
and `Quot.sound`.
