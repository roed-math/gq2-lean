# W352: general Stokes invariance under Nielsen substitutions

W352 proves that Stokes duality is invariant under every invertible substitution of a free
generator alphabet.  The proof is independent of rank, presentation, branch, coefficient, and
nilpotency class.  First jets are transported by additive equivalences; the central discrepancy
of a substituted Heisenberg lift telescopes to a mod-two exponent character and vanishes at a
Stokes endpoint.

The result is exposed both for free-group words and for resolved `PWord` substitutions.  As an
immediate application, the simultaneous wild shear used in the general even-M normalization is
Stokes-invariant at every finite level.  Thus the wild normalization is no longer part of the
remaining analytic residue.

The head-handle pair exchange is deliberately not claimed as a corollary.  It crosses the
tame/wild partition: the intrinsic tame relator is kept on `sigma`, whereas relabeling the
compact presentation would move it to the promoted handle.  The exact remaining general seam is
therefore the rank-uniform Stokes calculation for this exchanged two-relator row, followed by
the already-isolated prime-to-two tame correction.  No class-specific computation is involved.

The first-order calculation is now complete uniformly.  The pair-swapped word's Fox derivative
is the compact derivative in transported coordinates, and the transported handle block has
exactly one surviving term, `a(x₂) - sigma⁻¹ • a(x₂)`.  All other handle planes cancel without
any rank restriction.  Weakening the compact Fox engine from all-wild triviality to the three
core letters then gives both exact rows:

* on an unramified elementary module, the pair source is
  `a(tau) + a(x₂) - sigma⁻¹ • a(x₂)`;
* on a ramified elementary module, it is
  `-a(V_j) + a(x₂) - sigma⁻¹ • a(x₂)`.

Thus the two branches have complementary unit pivots at every rank.  The remaining analytic
work is one rank-uniform normal-coordinate and second-order pairing calculation for these rows,
followed by the already-isolated wild-shear and prime-to-two transports.
