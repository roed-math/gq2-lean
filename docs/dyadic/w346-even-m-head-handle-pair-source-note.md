# W346: promote the complete strict handle pair

W345 moved the tame head `sigma` into a selected handle `U_j`.  Its structural audit exposed
that a head-only exchange crosses the partners: the compact-M core pair becomes `(U_j,x₂)` and
the selected handle becomes `(sigma,V_j)`.

W346 makes the uniform correction by exchanging the complete pairs
`(sigma,x₂) ↔ (U_j,V_j)`.  The resulting `headHandlePairCompactW` satisfies:

- `tameSpecializes_headHandlePairCompactW`: the usual tame quotient survives;
- `eval_pro2_headHandlePairCompactW`: the selected handle pair is exactly the compact-M core
  pair, and the former core pair becomes that handle factor;
- `headHandlePairSwap_not_preserves_wild`: the construction is genuinely outside the
  tame/wild-preserving equivalence class excluded by W343.

The theorem pins are exactly `propext`, `Classical.choice`, and `Quot.sound`.

This identifies the correct general positive-handle source shape.  The remaining work is not
another pair-placement calculation: it is to prove the exact-lifting, Stokes/scalar, and
determinant certificate for this pair-promoted source family.
