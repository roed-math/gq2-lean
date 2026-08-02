# Maximal-pro-2 cohomology follow-up

Date: 2026-08-02

Scope: transfer the field-side mod-2 cohomology of `G_K` to its maximal pro-2 quotient
`G_K(2) = maxProPQuotient 2 (GalK K)`, as required before applying a general Demushkin/Labute
classification theorem.

## 1. Landed in this track

The degree-one comparison is no longer a blocker.

`GQ2/MaxProPCohomology.lean` proves the general statement for a profinite group `G`, a trivial
coefficient module `M`, and a pro-`p` target `Multiplicative M`:

```lean
noncomputable def maxProPH1EquivOfTrivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    H1 (maxProPQuotient p G) M ≃+ H1 G M
```

The proof is direct and does not use a cardinality argument:

1. `H1equivZ1OfTrivial` identifies `H¹` with `Z¹` because `B¹ = 0`.
2. A trivial-action cocycle `z : Z1 G M` is packaged as a continuous homomorphism
   `G → Multiplicative M`.
3. `maxProPHomEquiv hM` factors that homomorphism uniquely through `G(p)`.
4. The factor is converted back to a cocycle.

The computation theorem

```lean
theorem maxProPH1EquivOfTrivial_apply ... (x : H1 (maxProPQuotient p G) M) :
  maxProPH1EquivOfTrivial hM htrivG htrivQ x =
    inf1 (maxProPMk p G) actionCompat x
```

proves that the equivalence is the existing inflation map, rather than an unrelated chosen
equivalence.

`GQ2/Dyadic/MaxProTwoCohomology.lean` specializes this to `G_K` and `ZMod 2`:

```lean
def h1MaxProTwoEquivGalK :
    H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃+ H1 (GalK K) (ZMod 2)

theorem card_H1_zmodTwo_maxProTwoGalK :
    Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) =
      2 ^ (Module.finrank ℚ_[2] K + 2)
```

It also proves the source-naturality statement needed for the cup form:

```lean
theorem inf2_trivialCupPairing_maxProPMk_galK
    (x y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
  inf2 (maxProPMk 2 (GalK K)) actionCompat
      (trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) smul_zmod2 x y) =
    trivialCupPairing 2 (GalK K) (htriv_galK K)
      (h1MaxProTwoEquivGalK x) (h1MaxProTwoEquivGalK y)
```

This is proved on cocycle representatives.  No new axiom, `sorry`, or finite computation is
used.

## 2. Correction to the earlier follow-up plan

`glab-ksupply-plan.md` proposed a general equivalence

```lean
H2 (maxProPQuotient 2 G) (ZMod 2) ≃+ H2 G (ZMod 2).
```

That is too strong as the first general theorem.  The standard low-degree statement for the
maximal pro-`p` quotient is:

- inflation is an isomorphism on `H¹(-, 𝔽_p)`;
- inflation is injective on `H²(-, 𝔽_p)`.

For `G = G_K`, the field-side facts make the injection an isomorphism afterwards: local duality
gives `#H²(G_K, 𝔽₂) = 2`, while cup naturality and the nondegenerate field-side cup form
produce a nonzero class in the image.  Thus the correct order is **H² injection → field-specific
H² equivalence**, not a general H²-equivalence theorem.

## 3. The next missing theorem

The exact next public target should be the following specialization (with the displayed
`actionCompat` expanded in the actual declaration as in the landed H¹ theorem):

```lean
theorem injective_inf2_maxProPMk_zmodTwo
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    [DistribMulAction (maxProPQuotient 2 G) (ZMod 2)]
    [ContinuousSMul (maxProPQuotient 2 G) (ZMod 2)]
    (htrivG : ∀ g m, g • m = m)
    (htrivQ : ∀ g m, g • m = m) :
    Function.Injective
      (inf2 (maxProPMk 2 G)
        (fun g m => (htrivQ (maxProPMk 2 G g) m).trans (htrivG g m).symm))
```

Neither `GQ2/Cohomology.lean` nor vendored Mathlib currently contains the continuous
Hochschild–Serre five-term sequence needed to obtain this in one line.  The existing
`H2comap`/`inf2` APIs define the map, but do not prove its injectivity.

### Recommended proof decomposition

1. Prove that a continuous, `G`-conjugation-invariant character
   `proPKernel 2 G → Multiplicative (ZMod 2)` is zero.  Its kernel is normal in `G`; a
   nonzero character would produce a further pro-2 quotient of `G`, contradicting the defining
   minimality of `proPKernel 2 G`.
2. Prove the low-degree inflation kernel calculation directly on continuous cocycles.  If the
   inflation of `z : Z2 (G(2)) 𝔽₂` is `d¹ψ`, restrict `ψ` to the pro-2 kernel.  Step 1 kills
   the resulting invariant character, after which a normalized `ψ` descends through
   `maxProPMk`; the descended cochain witnesses that `z` was already a coboundary.
3. Package the result as injectivity of `inf2`.  Keep the direct cocycle theorem private unless
   it exposes a clean reusable signature.

This is a moderate infrastructure ticket, not merely a rewrite.  If a reusable continuous
five-term sequence is desired elsewhere, it may be worth building that instead, but it is a
larger project than the specialized cocycle proof.

## 4. Consequences immediately after H² injectivity

The next declarations should be field-specific:

```lean
noncomputable def h2MaxProTwoEquivGalK :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃+ H2 (GalK K) (ZMod 2)

theorem h2MaxProTwoEquivGalK_apply (z) :
    h2MaxProTwoEquivGalK (K := K) z =
      inf2 (maxProPMk 2 (GalK K)) actionCompat z

theorem card_H2_zmodTwo_maxProTwoGalK :
    Nat.card (H2 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2

theorem isDemushkin_maxProTwoGalK :
    IsDemushkin 2 (maxProPQuotient 2 (GalK K))

theorem demushkinRank_maxProTwoGalK :
    demushkinRank 2 (maxProPQuotient 2 (GalK K)) =
      Module.finrank ℚ_[2] K + 2
```

Proof dependencies are already present apart from H² injectivity:

- `isProP_maxProPQuotient` supplies the pro-2 clause;
- `card_H1_zmodTwo_maxProTwoGalK` supplies finite `H¹` and the rank;
- `FieldData.card_H2_zmodTwo` supplies the two-element target `H²`;
- `FieldData.nondegFp2_cupFormK` supplies field-side nondegeneracy;
- `h1MaxProTwoEquivGalK` lifts both cup inputs;
- `inf2_trivialCupPairing_maxProPMk_galK` transfers the cup value.

The H² injection then bounds source `H²` by two elements, and a nonzero lifted cup class
shows it has at least two.  This yields the field-specific H² equivalence and all Demushkin
clauses.

## 5. What still remains for the conjectural presentation

Completing the cohomological transfer proves that `G_K(2)` is a Demushkin group of the expected
rank.  It does not by itself identify the exact marked presentation.

The remaining independent tracks are:

1. compute `demushkinQ` of `G_K(2)` from the 2-primary torsion in local reciprocity (the
   ramification of `K(i)/K` is relevant here);
2. identify the canonical orientation with the descended cyclotomic character
   `chiCycKTwo` and compute its image;
3. prove the general Labute classification theorem needed by `MLabHypothesis` /
   `NLabHypothesis` (the repository currently stores these as explicit hypotheses);
4. use the descended unramified mark `nuUrKTwo` and the marked-core correction theorems to
   obtain the presentation with the required marking.

Thus there is a reasonable route from the current formalization.  The immediate cohomological
mountain has been reduced to one honest theorem, H²-inflation injectivity; after it, the main
mathematics shifts to the general Labute classification and the arithmetic identification of
`q` and the orientation image.
