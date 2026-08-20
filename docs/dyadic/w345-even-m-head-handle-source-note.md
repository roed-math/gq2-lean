# W345: a uniform strict-handle even-M source

W343–W344 show that an obstructed selected even-M field cannot be repaired by changing the
word, presentation, or boundary while retaining a source equivalent to the standard compact-M
candidate.  The obstruction is uniformly supported on a positive handle plane.

W345 introduces `headHandleCompactW alpha j`.  It exchanges the tame head `sigma` with the
first letter `handleU j` of a chosen handle pair inside the compact-M wild word, while leaving
the ambient tame relation unchanged.

Three structural facts are now proved uniformly for every positive handle count:

- `tameSpecializes_headHandleCompactW` shows that the new word still has the ordinary tame
  quotient;
- `eval_pro2_headHandleCompactW` computes its pro-2 relation with `handleU j` in the compact-M
  distinguished `C` slot and the old tame head in the corresponding handle commutator;
- `headHandleSwap_not_preserves_wild` proves that the exchange crosses the tame/wild partition,
  so it is not an admissible relabeling back to the old candidate and is not covered by W343.

All three public theorem pins are exactly `propext`, `Classical.choice`, and `Quot.sound`.

This is deliberately a structural source theorem, not yet a corrected certificate.  The next
general task is to reconstruct exact lifting, Stokes/scalar, and the affine determinant for the
head-handle source.  Those fields cannot be transported from the standard compact-M source;
they must be proved for this genuinely new family.
