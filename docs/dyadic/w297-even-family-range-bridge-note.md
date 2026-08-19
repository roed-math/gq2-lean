# W297: intrinsic range bridges for the even families

W297 addresses the common field-orientation seam rather than another nilpotency class.  The
family selector contains the marked rows needed to choose a word, but its family parameter is
not definitionally identified with the actual cyclotomic image.  The new
`EvenFamilyRangeBridge.lean` makes the missing comparison precise and consumes it uniformly.

On the N side, the selected value `nUnit alpha` is itself `-1 mod 4`.  Consequently its
membership supplies the non-principal residue class needed by the general closed-subgroup
classification; no separate ramification hypothesis for `K(i)/K` remains.  If `-1` is absent
from the actual cyclotomic image, depth rigidity forces the range to be exactly `imChiN alpha`.
The resulting oriented presentation feeds both the arbitrary-h N0 residual and the arbitrary-h,
arbitrary-display Npc residual.

On the M side, the selected rows force the actual range to be `imChiM beta` for some
`beta <= alpha`.  Thus the current selector witness can honestly name a depth deeper than the
actual range.  `MFamilyDepthSharp` is the exact one-row repair: depth two is automatically
sharp, while at larger depth absence of `mUnit (alpha - 1)` forces `beta = alpha`.  This produces
the selected M0 orientation and, combined with W296's all-degree/all-handle pivot tower, the
epsilon-true Mpc corrected RN residual.

Both tests are exact, not merely sufficient.  Under the selected rows,
`range_eq_imChiN_iff_neg_one_notMem` identifies the N range precisely when `-1` is absent, and
`range_eq_imChiM_iff_marked_sharp` identifies the M range precisely when the adjacent-depth test
holds.  Thus any remaining selector work must prove these intrinsic field conditions; it cannot
be repaired by another presentation-class computation.

The range identities themselves have only the standard three axioms.  The oriented and RN
consumers inherit the already-established even-classification and assembly axioms and add none.
No fixed field, alpha, handle count, or nilpotency class occurs in the proof.

The remaining even field issues are now cleanly separated from presentation theory:

- N families need the intrinsic branch separator `-1 notin range(chi)`;
- M families need the adjacent-depth sharpness test;
- selected M0 still needs its intrinsic C-pivot value;
- positive-level epsilon-false Mpc still needs the divided C-digit placement at general handle
  count.
