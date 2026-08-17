# W215: the residual C-versus-ABD interaction

W215 identifies the interaction kernel introduced in W214. Define the other-coordinate span
using the constrained `A`, `B`, and `D` shift ranges. The original constrained span is
exactly this `ABD` span plus the neutral `C` range.

An ordinary relative `C` class belongs to
`oneHandleBalancedCoreNeutralityInteractionSource` when its relaxed `C` shift lies in the
`ABD` span. After quotienting the source by genuinely neutral `C` representatives, the
image of this relation source is exactly W214's interaction kernel. The reverse inclusion
uses a neutral representative to remove the neutral-`C` component of any constrained-span
decomposition.

Accordingly, `oneHandleBalancedCoreNeutralityCokernelEquivInteraction` identifies the W212
neutrality cokernel with the relative-`C`-mod-neutral source modulo the image of literal
`C`-versus-`ABD` relations. The open finite problem is now whether those relations cover the
particular target class; no vanishing or surjectivity of the relation source is asserted.

Every public declaration has exactly the standard axiom set `propext`, `Classical.choice`,
and `Quot.sound`.
