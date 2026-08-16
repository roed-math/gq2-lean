# W134: corrected delta-D obstruction for uniform M6

The marked-carrier obstruction model is now corrected in Lean.

- The canonical M-frame supplies a continuous additive `D`-coordinate and its finite top digit.
- Every marked cost has zero `D`-digit, and marked-head neutrality is preserved by recursive
  advances.
- The actual secondary defect lies in the corrected five-carrier kernel: the three crossed
  derivations, `nu`, and `deltaD`.
- Membership in this corrected kernel yields the already-proved unrestricted four-slot cost
  witness.

The earlier cyclotomic vanishing remains true as an additional necessary condition, but it is
not a carrier-annihilator coordinate.  Exact finite calculations verify the corrected source
equation in rungs 2, 3, and 4; the all-degree mixed-source exactness theorem remains open and is
not assumed.  All twenty exported declarations use exactly the standard three axioms.
