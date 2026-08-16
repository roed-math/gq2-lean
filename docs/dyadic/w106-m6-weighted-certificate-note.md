# Wave 106: concrete M6 reflection bridges

Wave 106 connects the checked class-six word language to the exact closed defect and sparse
four-slot increment already present in the M6 ladder.

The checker gains three unconditional free-group collection identities: commutator over a
product in either slot, and square of a product with all correction commutators retained.
Their cases are proved inside `Deriv.sound`; they do not trust an external normalizer.

`MpcC6WeightedCertificate.lean` reflects the four closed defect factors and both correction
blocks into `CWord`.  `eval_closedDefect` identifies the reflected term with the existing
`mpcSx_w5_defect` value, while `eval_sparseIncrement` identifies the correction term with the
exact `mpcBldIncr` built from `mpcMkC6Us`, `Ut`, `Um`, and `Un`.

The combined `certificateWord` evaluates to defect times increment, and
`certificateKill_iff_checkedWord` proves that the sole open class-six certificate is
equivalent to reducing this word to one in `dmModel`.  The equality itself remains open.
Its raw syntactic depth is three, so a trace must expose the cancellations that raise the
survivor to class five before depth-six deletion can finish it.
