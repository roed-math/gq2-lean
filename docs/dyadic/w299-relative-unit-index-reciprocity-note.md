# W299: relative unit-index reciprocity for the uniform odd endpoint

W299 keeps the campaign on the general odd-degree problem.  The earlier
`AnchoredUnitSpectralReciprocity` was deliberately independent of the tame quotient and hence
quantified over arbitrary finite group homomorphisms.  That is stronger than the determinant
consumer needs.

For every compatible use, the defining subgroup of the anchored tame-inertia field contains
the commutator subgroup of `G_K`.  The proof uses the canonical identification
`Tq / inertiaPartQ = Zhat`: the full unramified quotient is procyclic, so every compatible
anchored field is a finite abelian Galois extension of `K`.

The new `RelativeUnitIndexReciprocity B FK` is therefore the conventional and sufficient
local-CFT input.  It states uniformly for every finite abelian layer `L/K` that the image of
spectral units under marked reciprocity has cardinality `e(L/K)`.  This is the direct relative
analogue of the already proved base-field theorem `UnitNormIndex.card_unitImage_eq_e`.

If all reciprocity units fix such a layer, its unit image is trivial; the cardinality theorem
then forces `e(L/K)=1`.  Applying this to every compatible anchored field proves
`AnchoredTameInertiaRelativeUnramifiedDataAt` and hence the required involution norm packet.
The final theorem
`gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeUnitIndex` now assumes only:

- the single base-`Q_2` absolute-residue reciprocity law;
- the full abstract tame local-reciprocity law at `K`; and
- the standard relative finite-abelian unit-index theorem at `K`.

No per-action spectral hypothesis, presentation family, nilpotency class, or handle count
remains.  All bridge declarations have only `propext`, `Classical.choice`, and `Quot.sound`;
the final equivalence inherits the campaign's established field-theoretic axioms and adds none.

The remaining arithmetic task is now a standard interface theorem: derive
`RelativeUnitIndexReciprocity` from full relative finite-layer norm reciprocity over `K`.  The
current `MarkedRecip` bundle intentionally omits that theorem, and its existing pro-`2` kernel
interface is insufficient for finite abelian layers with odd-primary unramified components.
