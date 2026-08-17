# W214: the source quotient of the neutral-C obstruction

W214 separates two effects still combined in W213's relaxed `C`-row map. The finite source
`OneHandleRelativeCModuloNeutral` is the group of ordinary handle-relative `C` classes
modulo classes with an exact representative killed by every continuous `Z_2`-valued
character.

The relaxed `C` shift agrees with the constrained `C` shift on every genuinely neutral
class. Consequently the W213 map descends to
`oneHandleBalancedCoreNeutralitySourceFactor`, and this descended map remains surjective.
Its kernel is characterized exactly by membership of the relaxed `C` shift in the full
constrained coordinate span.

Finally, `oneHandleBalancedCoreNeutralityCokernelEquiv` applies the first isomorphism theorem:
the W212 neutrality cokernel is the `C`-mod-neutral source quotient by this residual
coordinate-interaction kernel. This is an exact finite description, not a claim that either
the source quotient or the interaction kernel vanishes.

Every public declaration has exactly the standard axiom set `propext`, `Classical.choice`,
and `Quot.sound`.
