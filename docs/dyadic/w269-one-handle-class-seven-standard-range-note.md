# W269 — the standard class-seven relative range

The W268 relative shift no longer depends on the accumulated W4/W5/W6 marking.  Every W6
letter differs from the corresponding standard generator by an element of `lambda_2`, while
every class-seven correction factor has depth five.  Their bracket lies in `lambda_7` and
therefore vanishes in the level-seven quotient.  The theorem
`oneHandleW6RelativeShiftHom_eq_standard` makes the resulting homomorphisms literally equal.

The standard source splits into four coordinates.  Its range is exactly the join of four
explicit rows:

* `A` sends `x` to `x^2 [x,A] [x,B]`;
* `B` sends `x` to `[x,A]`;
* the character-neutral `C` coordinate sends `x` to `[x,D]`;
* `D` sends `x` to `[x,C]`.

Thus `relativeCorrectable_iff_standard_target_mem_coordinateSpan` removes every expanded W6
word from the remaining calculation.  It asks only whether the inverse lifted residual lies
in this four-row subgroup of the relative central layer.

The literal standard marking is also a balanced point, so the established generic cokernel
machinery applies to these rows without identifying the W268 target with a balanced target.
That distinction matters: the balanced target assumes an exact compact automorphism, whereas
the W268 lift is only a class-seven compact correction.  Relaxing just the character-neutral
condition on the `C` source gives an ordinary relative span.  The theorem
`relativeCorrectable_iff_relaxed_and_neutrality` splits the last condition exactly into:

1. ordinary relative coverage of the W268 target; and
2. vanishing of the finite quotient measuring whether the `C` representative can be chosen
   character-neutral.

No coverage or vanishing claim is smuggled into this wave.  The next proof task is the first
ordinary-relative obstruction; only after it vanishes does the smaller neutral-`C` quotient
become relevant.
