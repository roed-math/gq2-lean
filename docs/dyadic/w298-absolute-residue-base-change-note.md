# W298: absolute-residue reciprocity by base change

W298 removes a per-field premise from the general odd-degree endpoint.  The new predicate
`AbsoluteResidueBaseReciprocityLaw R` states the full absolute-residue normalization once over
`Q_2`.  It is intentionally a full `Zhat` statement: the existing pro-2 normalization does not
determine its odd-primary coordinates.

The theorem `v2_normUnitsK_eq_f_mul_dyadicValuation` proves, for every finite extension
`K/Q_2` and without a normality hypothesis,

`v_2(N_{K/Q_2}(x)) = f_K * v_K(x)`.

Combining this with `MarkedRecip.norm_compat` gives
`absoluteResidueLocalReciprocityLaw_of_base`: the single base law transports to the full
absolute-residue reciprocity law at every finite dyadic `K`.

Finally, `gammaR_lSq_equiv_galK_oddDegree_of_baseReciprocity` feeds that transport into the
uniform odd-degree reconstruction.  Its remaining arithmetic inputs are now:

- the one base-`Q_2` absolute-residue reciprocity law;
- the abstract tame local-reciprocity law for the selected oriented tame quotient; and
- equal norm-value groups for the compatible anchored involution fields.

The stronger
`gammaR_lSq_equiv_galK_oddDegree_of_baseAndUnitReciprocity` removes the last per-action item.
The abstract tame law supplies full-inertia control of reciprocity units, and the single
field-level `AnchoredUnitSpectralReciprocity K B FF` then produces equal norm-value groups for
every compatible anchored involution field.  Its arithmetic boundary is therefore exactly one
base-`Q_2` residue law, one abstract tame law at `K`, and one relative unit-reciprocity law at
`K`.

The first three declarations in the module use only `propext`, `Classical.choice`, and
`Quot.sound`.  The final endpoint inherits the existing Hilbert, Stiefel--Whitney, Tate-duality,
finite-generation, and Euler-characteristic axioms and adds none.  No presentation class,
family parameter, or handle count occurs in the base-change argument.
