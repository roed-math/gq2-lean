# W335: elementary profinite Nielsen transformations

W335 begins the constructive half of the changed-word even-M route with uniform
presentation infrastructure.

`GammaRPWordNielsenElementary` extends the syntactic Nielsen API by:

* relabeling the whole alphabet by an equivalence;
* reversing and composing inverse substitution pairs;
* proving inverse cancellation on every reflected word; and
* replacing one generator by its product with an arbitrary profinite power of a
  distinct generator, with an explicit inverse substitution.

The last operation also has a `ℤ₂` specialization through `padicOmega2`.  Its proof
uses the group law of profinite exponents directly, so it introduces no artificial
additivity hypothesis for the componentwise `padicOmega2` construction.

Every declaration has the standard trust base.  Nothing in the module is tied to a
nilpotency class, a frozen quadratic row, or even to the M family.  The next task is to
compose these transformations into the uniform field normal form promised by W334:
move the intrinsic mobile handle pivot into the analytic core coordinates while
transporting the defining word at the same time.
