# W170: uniformizers, filtered digits, and tame inertia

W170 advances the three residual general-family fronts without weakening any endpoint or
introducing a new assumption into a previously closed theorem.

## Compact M: the pivot as two Kummer identifications

`M0FieldPivotUniformizer` proves that a filtration uniformizer is not a norm from any genuine
unramified quadratic extension of a finite dyadic field.  Equivalently, the Kummer class of an
unramified quadratic extension cups nontrivially with the uniformizer class.  This removes the
odd-degree restriction from the earlier special value at `2`.

The module also proves that the compact-M and Frattini-frame copies of the mod-two unramified
character agree.  Consequently the intrinsic M0 pivot follows from exactly two arithmetic
identifications:

1. the transported distinguished D character is the Kummer class of the filtration uniformizer;
2. the field marking is the Kummer class of an unramified quadratic extension.

`m0RowResidualRN_of_familySelection_of_uniformizerD` is the resulting selected corrected-RN
consumer.  These two identifications remain arithmetic input; W170 does not infer them from
level zero alone.

## Mpc: when the next filtered digit is forced

`MpcFieldPivotDigitProducer` proves that the W169 digit is one exactly when the distinguished C
value is not divisible one layer deeper.  Exact kernel attainment plus a sufficiently deep B
row forces this digit.  In field language, `lambdaAt (-1) = 0` supplies the required B condition.

The selected consequence is sharp.  Every rank-four `epsilon = false` Mpc selection has digit
one for every oriented equivalence.  Conversely, the W169 counterexample also satisfies the
complete `epsilon = true`, `r = 1` level, B-residue, and D-residue schema while its digit is zero.
Thus the true branch still requires a genuinely filtered orbit or field-compatibility theorem;
the ordinary selector rows do not imply it.

## Odd L: residue inertia and the involution norm atom

`RamifiedCertificateResidueInertia` reduces the compatible residue-lift packet to the natural
field statement that the kernel of `nuTq q` acts trivially on the absolute residue field.  A
single absolute residue-trivial tame-tau lift then works for every anchored kernel.  The module
also formalizes a `q = 4` counterexample: a surjection `Tq 4 -> C3` gives a faithful ramified
action, kills every commutator, and has tame-tau order `q - 1`.  Hence finite faithful action
data cannot replace the residue-inertia theorem.

`AnchoredInvolutionNormOddness` constructs the canonical anchored tame-inertia field and proves
all remaining norm matching from odd ramification index of that field.  The full compatible
equal-norm packet is now reduced to the explicit field assertion
`AnchoredTameInertiaOddDataAt`.  Existing APIs prove the analogous absolute-Q2 fact but do not
yet supply this K-relative oddness.

## Verification

All four modules compile at default heartbeat and recursion limits.  Every newly introduced
structural declaration uses only `propext`, `Classical.choice`, and `Quot.sound`; the M0
cup/Hilbert consumers inherit only the existing Hilbert-symbol and Tate-duality foundations,
and the selected M0 residual inherits the existing peripheral-action input.  No `sorry`, new
axiom, native decision procedure, or option override is used.
