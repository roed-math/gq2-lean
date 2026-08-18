# W263 — the exact one-handle direct rank recurrence

A direct point already lying at depth `k + 1` has the trivial correction at depth `k`.
Conversely, every depth-`k` correction produces a point at depth `k + 1`.  W263 combines
these directions to identify nonemptiness of the next finite stage exactly with the existence
of one correctable point in the current stage.

Using the finite transpose results, the same recurrence is equivalent to the existence of a
current point whose augmented rank does not jump, and to the existence of four scalar bidual
row coefficients for the current target.  Hence selectable correction, selectable equal
finranks, selectable row coefficients, and the original direct successor supply are all
equivalent.  The remaining finite theorem is now exactly to prevent the one-bit rank jump at
one point on each nonempty rung; no universal assertion about every point is required.
