# W361 audit: what full marked reconstruction still requires

Date: 2026-09-17. Independent lane: `raw_pairing`.

## Conclusion

The existing fixed-frame exact-image theorem does not by itself assert preservation of the
chosen complete maximal pro-two map. It fixes the tame quotient and an elementary abelian
decoration of that map. There is now a checked structural route toward a stronger theorem:
every minimal nonscalar wild block is killed by every two-group quotient. Consequently the
full prescribed pro-two map survives each nonterminal quotient step. A checked restricted
M-stage fibration retains the old fiber multiplicity exactly.

The complete refined induction has **not** been proved by this lane. In particular, the
current abstract source record stores the R-stage count after aggregation; the stronger
restricted result must be obtained from the concrete pointwise inputs, not inferred from
equality of unrestricted totals.

An existential presentation can instead choose its core realization to match the pro-two
map induced by a tame-compatible equivalence, if all realization conditions are proved for
that choice. This changes the selected realization. It is not preservation of an arbitrary
previously specified one. That alternative is now checked in `FieldFamilySpliceAlignedFinal`;
the independent audit, including the characteristic-orientation check, is recorded in
`w361-aligned-marking-audit.md`.

## Exact existing interfaces

`Recursion/Frame.lean` defines `BoundaryFrameK` using a finite tame quotient
`alpha : Tq q → H` and `psiBar : P → E`, where `E` is commutative and has exponent two.
`IsBoundaryLiftK` imposes only

```
piY ∘ f = alpha ∘ tame,
thetaY ∘ f = psiBar ∘ pro2.
```

`ThmFourTwoRN.thm_4_2_of_sourcesRN` compares the corresponding exact-image counts.
Its existing reconstruction corollary returns `ContinuousMulEquiv`, without equations for
either source boundary map. The new `GQ2/MarkedReconstruction.lean` correctly retains any
finite-level constraints that are supplied; its nonempty-allowed-level premise still has to
be proved for the desired full boundary, and is not supplied by the old unmarked theorem.

This distinction is already visible in the written packet:

- `dyadic-presentations-formalization-proof.tex`, Theorem `thm:certificate-main`, claims
  identification of the tame quotient, maximal pro-two quotient, orientation and full
  geometric unramified character.
- The proof cited there passes through `thm:source-abstract`, whose actual concluding
  statements are equality of unrestricted finite-surjection counts and an abstract
  topological group isomorphism.
- `CertificateMain.candidate_equiv_absoluteGalois` faithfully exposes the weaker formal
  conclusion and does not contain a hidden full-boundary compatibility theorem.

## Why an automatic upgrade is unjustified

Suppose `u : P ≃ P` preserves `nuP` and acts trivially on every elementary abelian quotient.
Replacing `pro2` by `u ∘ pro2` does not change any existing frame equation. In particular,
these equations cannot directly distinguish a prescribed higher pro-two coordinate from
its `u`-twist.

This observation is **not** a counterexample to full marked reconstruction for the actual
certified source groups. Those groups might have a theorem lifting every relevant
automorphism of `P` to a tame-preserving source automorphism. No such theorem is supplied by
the existing aggregate count corollary, and no claim that it is false is made here.

## Checked new structural bridge

New module: `GQ2/SectionSeven/ProTwoKernel.lean`.

For a finite group `Y`, an existing `MinimalBlock L`, any group `Q`, any
`hQ : IsPGroup 2 Q`, and any homomorphism `f : Y →* Q`, the theorem

```
MinimalBlock.le_ker_of_isPGroup B hQ f : B.K ≤ f.ker
```

has no extra tame-head, rank, class, surjectivity or Frattini hypothesis. The target `Q`
need not even be finite. The proof is short:

1. The existing odd-order moving-element theorem produces an odd-order `y` acting
   nontrivially on the simple chief factor `P/S`.
2. A map to a two-group kills `y`.
3. Set `X = ker f ∩ K`. The chief dichotomy says `X S = S` or `X S = P`.
4. The first option would make `y` act trivially on `K S/S = P/S`, contradiction.
5. The second option and minimality force `X = K`.

Further checked declarations are:

- `MinimalBlock.subgroup_le_ker_of_isPGroup`, for every `N ≤ K`, hence in particular
  `N = Phi(K)`;
- `MinimalBlock.le_proPKernel`, with arbitrary topology on the finite source;
- `MinimalBlock.existsUnique_factor_of_isPGroup`, proving that quotienting by a normal
  `N ≤ K` preserves the **entire** homomorphism into `Q`, uniquely.

All four declarations compile at default limits and print only the standard three axioms.

## Checked decoration and fiber layers

New module: `GQ2/Dyadic/Recursion/ProTwoDecoration.lean`.

The additive predicate `RespectsProTwo pro2 psi theta f` means
`theta (f gamma) = psi (pro2 gamma)` for every `gamma`; `Q` is not required to be elementary
abelian. `ProTwoBoundaryLiftsK` and `proTwoExactImageCountK` retain the old boundary equation
and add this condition.

For a recursion frame, `proTwoThetaC RF hQ theta` is the unique descended decoration on
`C = Y/K`; `proTwoThetaB` is its pullback to `B = Y/Phi(K)`. Checked evaluation identities
show both pull back to the original `theta`.

The checked transport lemmas are:

- `respectsProTwo_iff_of_over`: every lift over one fixed lower map has exactly the lower
  map's full-Q compatibility condition;
- `respectsProTwo_liftBK_iff`: projection from `Y` to `B` preserves that condition;
- `respectsProTwo_cover_iff`: on a central-cover fiber, use the inherited decoration
  `theta ∘ p`, so imposing the condition does not remove any lifts in that fiber.

All ten declarations compile at default limits with only the standard three axioms.

New module: `GQ2/Dyadic/Recursion/ProTwoRestrictedFibers.lean`.

`mStage_proTwo_restricted_fibration_card` proves

```
# {m : Gamma → B | boundary(m), C-onto(m), full-Q-compatible(m)}
  = mult * # {rho : Gamma ↠ C | boundary(rho), full-Q-compatible(rho)}.
```

Its sole multiplicity input is the old pointwise statement
`forall rho, Nat.card (LiftsOverK RF b F rho) = mult`. The proof constructs the actual
restricted projection fibration and identifies each fiber with the existing unrestricted
`LiftsOverK` fiber. It does not infer fiberwise equality from an aggregate equation.
It compiles at default limits with only the standard three axioms.

## Remaining refined-induction work

There is a finite and concrete proof-engineering route, but not a one-line application of
the existing capstone:

1. **M-stage image partition:** restrict the image-stratum bijections used by
   `mStage_partitionK`, with each stratum carrying `thetaB ∘ subtype`. The checked fibration
   above supplies its left side. The subgroup-size induction measure is unchanged.
2. **Central-cover partitions:** restrict Lemma 8.3 with the cover decoration pulled back
   from its base. `respectsProTwo_cover_iff` shows the scalar lift torsor still has its full
   cardinality. The same holds for the phase-cover counts.
3. **R-stage (136):** replay its obstruction Fourier identity on the subtype of lower
   lifts satisfying the fixed Q condition. The fiber cardinalities are unchanged, by
   `respectsProTwo_liftBK_iff`.
4. **Remaining closed equations:** restrict the sums in (137)--(140), retaining the
   original pointwise lifting, half-torsor and Gauss leaves. Their numerical coefficients
   and target cardinality bounds are unchanged.
5. **Terminal scalar lane:** the proof of `qliftsK_equiv_commonLiftsK` already factors each
   source map through its supplied maximal pro-two map. Retain the individual resulting
   `P → Q_terminal` map instead of summing all of them, and impose the further full-Q
   condition there. The existing theorem's conclusion is only a cardinal equality; its
   underlying equivalence is constructed internally, so an additive exposed/refined
   version is needed.
6. **Strong induction and compactness:** compare the restricted counts, obtain compatible
   finite-quotient surjections, and apply the new allowed-level marked reconstruction.

### Important source-record loss of information

`SourceDataRN.exactLifting.2.2` is the already-aggregated equation (136). It does **not** store
the pointwise R-obstruction lifting criterion or individual R-cocycle torsor cardinalities.
Therefore replacing every count by a restricted count in the existing proof and reusing
that field would be invalid.

The concrete lower API is visible in `stageR136_ofRSepDataCoeffK`: it consumes
`hsep_hom` (obstruction zero gives a homomorphic lift) and
`hZcount : forall f0, Nat.card (RCocycle RF f0) = z`, then derives the aggregate identity.
`hfib_holdsCoeffK` identifies the individual lifting fibers from these inputs. A full
refined theorem must either take these pointwise source supplies explicitly or prove them
again for the actual word/field sources. The current new modules do neither silently.

No new analytic obstruction was found in this audit. Nevertheless, these restricted
partitions, the strengthened source interface, and the final induction still need actual
Lean proofs before claiming fixed-input full-core compatibility.
