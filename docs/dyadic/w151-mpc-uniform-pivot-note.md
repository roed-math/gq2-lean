# W151: uniform marked supply, pivot shift, and sqrt(-10)

The procyclic-M marked ladder is now complete at every rung.  This closes `MpcPivShift 2` and the
last frozen quadratic field endpoint.

The induction uses a strengthened state `MpcMkMarkedGood`.  The older `MpcMkGood` existential
forgets whether its chosen head correction is marked, so it is not an honest induction invariant.
`MpcMkMarkedGood` retains exactly that datum, holds at the class-five base, and is preserved by
`mpcMkAdvance`.

At each successor:

1. W149 supplies head completion;
2. M-frame head reflection gives full source exactness;
3. the secondary Hall residual lies in the corrected five-carrier kernel; and
4. source exactness puts it in the successor marked-cost range.

This proves `mpcMk_exists_fullSupply` for every `j >= 3` and hence
`mpcMk_pivShift : MpcPivShift 2`, all with only the standard three axioms.

The field-facing wrappers then export the tied canonical sqrt(-10) branch and the premise-free
corrected RN endpoint `mpcMk_candidate_equiv_galKRN_sqrtNegTen`.  They inherit only the already
established field-side foundation axioms and add none.

The authoritative scoreboard now records the pivot-shift theorem directly and classifies the
sqrt(-10) endpoint as closed.  All five frozen quadratic corrected RN endpoints are therefore
closed.
