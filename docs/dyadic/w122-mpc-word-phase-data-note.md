# W122: pp-zero Mpc projected-head phase data

Both handle-free `pp = 0` Mpc head regimes now reach the same plus-form phase.

- In the unramified regime, the projected tau and wild heads are trivial and the sigma resolver
  action feeds the exact unramified Hessian evaluation.
- In the ramified regime, the projected tau head has odd order and acts fixed-point freely.  A
  surjective semidirect projection transports the resolver needed by the honest ramified Hessian.

The module also packages the corresponding first-order normal forms and exports unramified and
ramified `SourceWordPhaseComparison` constructors.  All five headline declarations use exactly
the standard three axioms.  The remaining sqrt(10) work is the boundary branch split and its
determinant consumer.
