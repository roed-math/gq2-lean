# W133: unramified Npc full-offset Hessian

The arbitrary-unit procyclic-N word is now evaluated at the actual unramified normal
coordinates, without the obsolete `x2 = 0` restriction.

- The delta, `d`, and `e` correction blocks vanish at an honest unramified resolver.
- The inverse boundary conjugate contributes exactly the missing polar cross term.
- The complete word evaluation and Hessian split into a one-variable head diagonal, the
  operator-twisted cross term, and the standard hyperbolic handle tail.

Every exported declaration uses exactly the standard three axioms.  The remaining analytic
task is now sharply one-dimensional: prove that `npcUnramifiedDiagonal` is quadratic, identify
its standard form, and evaluate its Gauss sum.
