# W186: the absolute residue Galois group is Zhat

W185 proved that the canonical absolute residue action is surjective. W186 now constructs the
normalized profinite coordinate on its target.

Let `k0` be the two-element residue field and `kbar2` the residue field of the valuation ring in
the algebraic closure of `Q2`. Profinite exponentiation of square Frobenius defines

```text
zhatToAbsoluteResidueGal : Zhat -> Gal(kbar2/k0).
```

Surjectivity follows from finite-field Frobenius generation and the normal finite-intermediate-
field basis of the Krull topology. For injectivity, each finite quotient in the profinite
completion defining `Zhat` is identified with the Galois group of a finite residue extension of
the same degree. Restricting the global square Frobenius recovers the finite Frobenius generator,
so equality of global actions forces equality in every completion component.

The resulting continuous equivalence is normalized by

```text
absoluteResidueGalEquivZhat absoluteResidueFrobenius = Zhat.ofInt 1.
```

Combining it with the surjective canonical residue action and its exact kernel gives

```text
(Gal(AlgebraicClosure Q2/Q2) / absoluteInertiaSubgroup) =_topological_group Zhat.
```

The public quotient coordinate is `absoluteInertiaQuotientEquivZhat`. All twelve public
declarations in `RamifiedCertificateAbsoluteResidueZhat.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

This closes the absolute residue-field Galois theory and its quotient topology. The remaining
Odd-L residue seam is genuinely relative: construct the commuting comparison between this
canonical absolute Frobenius coordinate and the `qurQEquivZhat` coordinate attached to an
`OrientedTameQuotientK`. The anchored involution norm side remains the separate full-inertia unit
refinement and unit-spectral reciprocity problem.

Verification passes the 4,533-job build, fresh 1,121-module scoreboard, and full ledger gate over
45,157 tracked declarations.
