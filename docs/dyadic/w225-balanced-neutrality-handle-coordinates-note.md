# W225: unique handle-coordinate normal form

W225 turns W224's abstract equivalence with `(ZMod 4)^2` into a coordinate API for the
remaining CABD problem.

The map `oneHandleRelativeCCoordinates` is surjective and has exactly the image of the exact
row-neutral relative source as its kernel.  The chosen class `oneHandleDeepRelativeClass`
realizes every digit pair, and `existsUnique_deepRelativeClass_mod_neutral` says that every
ordinary relative class has a unique such representative modulo neutral classes.

Consequently equality in `OneHandleRelativeCModuloNeutral` is precisely equality of the two
`ZMod 4` digits.  The endpoint
`neutralityObstruction_eq_one_iff_CABD_coordinates` rewrites the remaining obstruction as the
literal CABD central-layer equation together with those two prescribed finite coordinates.
It does not assert that the central-layer equation is solvable.
