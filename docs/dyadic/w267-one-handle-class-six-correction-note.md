# W267 — the explicit one-handle class-six correction

The handle-relative residual isolated in W266 is now cancelled inside Lean.  The correction
multiplies the four compact factors by two copies of an explicit relator consequence `X` and
one copy of an explicit consequence `Y`; the remaining three factors are one.  These new
factors lie at depth four, preserve the cyclotomic and distinguished rows, and leave the two
handle letters fixed.

The cancellation does not trust the external sparse search that found the pattern.  The
weighted checker now has a relation-free deep-model semantics, and the prefix, low, relation,
and final trace modules replay all 65 rows without using a relator rule.  Their universal
endpoint proves that the certificate word times the displayed relation product is one in any
deep model.  The new correction module separately proves that its stage shift is exactly that
relation product in `D_M(2,1)/lambda_6`.

Consequently `oneHandleW5ClassSixCorrection` is an explicit `OneHandleDirectCorrection`,
`oneHandleW5Correctable` discharges the W265 interface, and `oneHandleDirectSet_six_nonempty`
advances the concrete one-handle ladder through class six.  The one-handle lane is therefore
not stalled; its next finite task is the class-seven correction from this explicit sixth-stage
marking.  This result does not yet assert the all-stage successor supply or an arbitrary-handle
`MpcPivShiftH`.
