# W328: general Nielsen transport for corrected presentations

W328 supplies the presentation-theoretic bridge left open by W327.  It is uniform in the
degree, residue cardinality, word, and pro-2 core.

An `AdmissibleFreeNielsenEquiv` is an invertible continuous transformation of the free
profinite alphabet that kills the two target relators in both directions and satisfies the
restricted wild-core clauses required by the corrected definition of `GammaR`.  Its forward
and backward maps descend through `gammaLift` and assemble to
`AdmissibleFreeNielsenEquiv.gammaEquiv`.

The stronger, more concrete `WildPreservingFreeNielsenEquiv` replaces the two quantified
finite-quotient clauses by generator-level membership in the normal closure of the wild
letters.  `wildCore_of_generator_images` proves that this control is sufficient: every finite
image is a subgroup of the target presentation's certified finite 2-group wild core.

Finally, `NielsenBoundaryRows` reduces W327's tame and pro-2 commuting squares to the marked
alphabet.  `BoundaryCompatibleWordEquivRN.ofNielsen` combines those rows with the descended
equivalence.  Together with W324--W327 this means that a mobile-pivot word now needs only an
invertible wild-preserving free transformation, two relator checks in each direction, and two
finite generator tables.  Exact lifting, Stokes, scalar counts, determinants, reconstruction,
and the general-K equivalence are then inherited without any branch-specific analytic proof.

All public declarations print exactly the standard trust base
`[propext, Classical.choice, Quot.sound]`.
