# W347: transport the full pro-2 core to the strict-handle source

W346 identified the correct general source shape by exchanging the complete pairs
`(sigma,x₂) ↔ (U_j,V_j)`.  W347 proves that exchange is an involutive Nielsen
transformation at the pro-2 presentation level and transports the complete
`CorePresentation` of `DM alpha h` to the pair-promoted word.

The transported marking is explicit:

- the new `sigma` maps to the chosen handle generator `U_j`;
- the displaced `U_j` wild letter maps to the old distinguished generator `C`;
- the old `x₂` letter maps to the paired handle generator `V_j`.

Thus the strict handle pivot is in exactly the right place for the normalized unramified
head.  The module packages the remaining pro-2 condition as
`HeadHandlePairWildNormalized`: every transported wild row must vanish.  Together with the
unit promoted handle row, this produces `headHandlePairFlexibleCore`, the complete table-free
pro-2 packet used by the general corrected assembly.

This is uniform in `alpha` and the handle count.  It introduces no class bound, finite-stage
assumption, or field-specific row.  It also makes the next seam honest: the displaced old
`C` row and the other transported wild rows must be normalized exactly; level divisibility
alone is insufficient.

All public theorem pins use exactly `propext`, `Classical.choice`, and `Quot.sound`.
