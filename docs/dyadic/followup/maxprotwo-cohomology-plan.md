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

## 3. Degree-two injectivity has landed

`GQ2/MaxProPCohomology.lean` now proves the general low-degree statement:

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

The proof does not add a Hochschild–Serre axiom or a five-term-sequence API.  Instead it works
directly with continuous cocycles:

1. normalize a representative `z : Z2 (G(2)) (ZMod 2)`;
2. form its continuous central extension `G(2) ×_z ZMod 2`;
3. prove directly from open normal subgroups that this extension is pro-2;
4. turn a coboundary for the inflated cocycle into a continuous homomorphism from `G` to the
   extension;
5. factor that homomorphism through `G(2)` and read its fibre coordinate as the cochain showing
   that `z` was already a coboundary.

The auxiliary `NormZ2` and `CentExt` constructions are collected in
`GQ2.MaxProPH2Inflation`.  No new axiom, `sorry`, or finite computation is used.

`GQ2/Dyadic/MaxProTwoCohomology.lean` provides the field-specific map and theorem:

```lean
def h2InflationGalK :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) →+
      H2 (GalK K) (ZMod 2)

theorem h2InflationGalK_injective :
    Function.Injective (h2InflationGalK (K := K))
```

## 4. Next consequences and the current elaboration blocker

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

The mathematical proof dependencies are now present:

- `isProP_maxProPQuotient` supplies the pro-2 clause;
- `card_H1_zmodTwo_maxProTwoGalK` supplies finite `H¹` and the rank;
- `FieldData.card_H2_zmodTwo` supplies the two-element target `H²`;
- `FieldData.nondegFp2_cupFormK` supplies field-side nondegeneracy;
- `h1MaxProTwoEquivGalK` lifts both cup inputs;
- `inf2_trivialCupPairing_maxProPMk_galK` transfers the cup value.

The H² injection bounds source `H²` by two elements, and a nonzero lifted cup class shows it has
at least two.  This yields the field-specific H² equivalence and all Demushkin clauses.

The immediate formal blocker is an instance-path mismatch, not a missing theorem.  Under the
richer import closure of `MaxProTwoCohomology`, the field-side theorems elaborate over the literal
subtype `↥K.fixingSubgroup`, while the transfer API is stated for the abbreviation `GalK K`.
Lean does not currently identify the resulting `H2` types because their inferred coefficient and
cohomology instance paths differ.  A clean next ticket is therefore either:

```lean
noncomputable def h2GalKFieldDataEquiv :
    H2 (GalK K) (ZMod 2) ≃+ H2 ↥K.fixingSubgroup (ZMod 2)
```

with computation lemmas sufficient to transport cup products, or a small instance firewall /
refactor that makes the two types definitionally equal.  Once that bridge is available,
`FieldData.card_H2_zmodTwo`, `FieldData.nondegFp2_cupFormK`, cup naturality, and the injectivity
proved here give the declarations listed above without further cohomological infrastructure.

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
