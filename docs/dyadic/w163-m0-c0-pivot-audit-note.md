# W163: compact-M `C0` pivot obstruction

The remaining general-h compact-M field premise is constrained by a genuine mod-two cup
invariant.

The landed even cup form pairs canonical `C0` with the `D` character.  Therefore any cup isometry
fixing that character fixes the `C0` coordinate of every covector.  In particular, it cannot add a
handle coordinate to `C0`.

The tempting local symplectic shear confirms the obstruction: adding `U_j` to `C0` requires adding
`D` to the companion `V_j`.  For `alpha >= 2`, the compact-M orientation detects every nonzero
`D` coordinate, and no `B`/sign correction can make the companion row orientation-trivial.

The five theorems in `M0C0PivotAudit.lean` formalize this cup-level no-go with the standard three
axioms.  They deliberately do not claim a full group-automorphism theorem.  The repository still
lacks the adapter sending a continuous automorphism of `DM alpha h` to its displayed mod-two
character pullback together with cup naturality and orientation preservation.

Thus W159's canonical `C0` pivot cannot be removed by an oriented Eichler normalization of the
kind used for compact N/Npc.  A different field realization or genuinely new structural input is
required.
