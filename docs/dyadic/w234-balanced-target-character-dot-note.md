# W234: balanced target-character dot products

W233 replaced each abstract neutrality-cokernel character by a pair of coefficients in
`(ZMod 4)²`. W234 removes the remaining complex-valued character evaluation.

For a digit pair `(x,y)` and coefficients `(a,b)`, the associated plane character is the
primitive mod-four character evaluated at `a*x + b*y`. It is therefore one exactly when this
dot product is zero. The finite target obstruction now says directly that some `(a,b)`
annihilates every CABD interaction row but has nonzero dot product with the selected target.

The exact equivalence with failure of constrained coordinate coverage, and hence with
pointwise next-stage emptiness, is preserved. This makes the obstruction a finite scalar
linear-algebra problem: sixteen coefficient pairs acting on a sixteen-element digit plane.
It does not assert that a detecting pair exists uniformly.
