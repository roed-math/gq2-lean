# W197: the odd-L endpoint from the reciprocity laws

W195 and W196 replace the residue/tame unit and uniformizer interfaces by two all-elements laws
on `K×`.  W197 carries those laws through the compatible ramified-certificate pipeline.

`compatibleRamifiedDataAt_of_reciprocityLaws` takes exactly:

- `AbsoluteResidueLocalReciprocityLaw B FF`;
- `AbstractTameLocalReciprocityLaw T`; and
- `AnchoredInvolutionEqualNormValueGroupsAt` for the compatible finite action.

It derives the signed relative Frobenius comparison, hence the full-inertia containment and
compatible residue lift, and combines that with the anchored equal-norm theorem to construct the
complete compatible ramified-data packet.

`LSquare.gammaR_lSq_equiv_galK_oddDegree_of_reciprocityLaws` feeds this packet into the existing
uniform odd-degree reconstruction.  Its public arithmetic boundary is precisely the two local
reciprocity laws and anchored equal norm-value groups.  Clearing, marked-core realization,
residue-lift selection, full-inertia comparison, coordinate normalization, Gauss sums, and the
determinant no longer appear as premises.

The packet constructor depends on the standard three axioms plus the existing `tateDualityAt`.
The final endpoint inherits exactly the established odd-`L` arithmetic census and adds no new
axiom dependency.

Verification on 2026-08-17:

- `lake build GQ2`: 4,544 jobs completed successfully;
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: 45,247 tracked declarations, no `sorryAx`
  dependencies, no unknown non-standard axioms, and no terminal-certificate violations;
- `bash scripts/scoreboard.sh --raw`: 1,132 imported modules and no stale umbrella imports.
