# The `q = 2` input for ramified `K(i)/K`: checked status and proof DAG

Date: 2026-08-02

## Result of the audit

The desired invariant is expressible, and its intended statement is:

```lean
theorem demushkinQ_maxProTwoGalK_of_ramifiedI
    {deltaI : AlgebraicClosure ℚ_[2]} (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2
```

The single-witness hypothesis above is sufficient for every consequence currently used.  The
campaign-wide record spells the same condition uniformly as

```lean
ramified : ∀ deltaI, deltaI ^ 2 = -1 →
  ¬ HasEqualNormValueGroups K deltaI
```

in `FieldInputs` and `DyadicLocalInput`.

The theorem is **not yet proved**.  The completion campaign has now removed the purely
group-theoretic part of the obstruction: maximal pro-`p` quotient commutes with topological
abelianization, the repository has a concrete pro-`p` completion model, and dense marked
reciprocity extends to a continuous surjection onto `(G_K(2))^ab`.  What remains is arithmetic:
the present `MarkedRecip` fields do not identify the kernel of that surjection or the torsion of
its target with the 2-primary roots of unity of `K`.  Therefore deriving `q = 2` merely from the
cyclotomic image, residue cardinality, or the mod-2 Demushkin form would still be an unsupported
proxy.

In particular, the two unrelated uses of the letter `q` must remain separate:

* `qOf K FF = 2 ^ FF.f` is the residue-field cardinality;
* `demushkinQ G = Nat.card {x : topAbelianization G // IsOfFinOrder x}` counts torsion
  elements of the topological abelianization.

## What is now proved

The cohomological part is complete at the current head:

```lean
isDemushkin_maxProTwoGalK :
  IsDemushkin 2 (maxProPQuotient 2 (GalK K))

demushkinRank_maxProTwoGalK :
  demushkinRank 2 (maxProPQuotient 2 (GalK K)) =
    Module.finrank ℚ_[2] K + 2
```

Ramified `K(i)/K` already has the following honest consequences.

```lean
kappaK_ne_zero_of_ramified :
  deltaI ^ 2 = -1 → ¬ HasEqualNormValueGroups K deltaI →
  FieldData.kappaK K ≠ 0

twoPowerRoot_eq_one_or_neg_one_of_ramifiedI :
  deltaI ^ 2 = -1 → ¬ HasEqualNormValueGroups K deltaI →
  x ^ (2 ^ n) = 1 → x = 1 ∨ x = -1

twoPowerRootsEquivZModTwo_of_ramifiedI :
  deltaI ^ 2 = -1 → ¬ HasEqualNormValueGroups K deltaI →
  TwoPowerRoots K ≃ ZMod 2

natCard_twoPowerRoots_of_ramifiedI :
  deltaI ^ 2 = -1 → ¬ HasEqualNormValueGroups K deltaI →
  Nat.card (TwoPowerRoots K) = 2

exists_maxProTwo_inertia_chi_modFour_ne_one_of_ramifiedI :
  MarkedRecip R K → deltaI ^ 2 = -1 →
  ¬ HasEqualNormValueGroups K deltaI →
  ∃ q : maxProPQuotient 2 (GalK K),
    nuUrKTwo B q = 1 ∧
    PadicInt.toZModPow 2 (((chiCycKTwo q : ℤ_[2]ˣ) : ℤ_[2])) ≠ 1
```

The group/completion bridge is now also formalized:

```lean
maxProPTopAbEquiv (p : ℕ) (G : Type) :
  maxProPQuotient p (topAbelianization G) ≃ₜ*
    topAbelianization (maxProPQuotient p G)

proPCompletion (p : ℕ) (A : Type) [Group A] : ProfiniteGrp

proPCompletionLift_surjective_of_denseRange
    (hP : IsProP p P) (f : ContinuousMonoidHom A P) (hf : DenseRange f) :
  Function.Surjective (proPCompletionLift hP f.toMonoidHom)

proTwoReciprocityToTopAb (B : MarkedRecip R K) :
  ContinuousMonoidHom (proPCompletion 2 ((↥K)ˣ))
    (topAbelianization (maxProPQuotient 2 (GalK K)))

proTwoReciprocityToTopAb_surjective (B : MarkedRecip R K) :
  Function.Surjective (proTwoReciprocityToTopAb B)
```

The first equivalence is the abstract identity `(G^ab)(p) ≃ (G(p))^ab`.  The last theorem
uses exactly the `MarkedRecip.continuous_recip` and `denseRange_recip` fields plus compactness;
it makes no kernel claim.

The inertia theorem above is the exact contrapositive of `MarkedRecip.ki_unramified`, lifted through
`G_K → G_K^ab` and descended through `G_K → G_K(2)`.  It says that pro-2 inertia acts
nontrivially on fourth roots of unity.  It does not assert that its witness has finite order.

## Why the existing interfaces stop short

`MarkedRecip R K` supplies

```lean
recip : (↥K)ˣ →* GalKab K
denseRange_recip : DenseRange recip
```

and the marked characters `chiCycKAb` and `nu_ur`.  Density is now used to prove the completed
map `proTwoReciprocityToTopAb` is surjective, but it does not identify that map's kernel.
`DyadicUnitFiltration` supplies a uniformizer and
the cardinalities of successive unit-filtration quotients; it does not yet supply the power-map
or logarithmic structure needed to split the completed principal units into a torsion part and a
free `ℤ₂` part.

The `K = ℚ₂` proof in `SectionThree.lean` cannot simply be reused.  It proves an explicit
equivalence

```lean
topAbelianization D0 ≃ₜ* Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])
```

after establishing the field-specific square-class generation by `{-4, 2, -3}` and explicit
cyclotomic/unramified coordinates.  The arbitrary-`K` repository has the square-class count but
not an explicit square-class basis or an analogous integral coordinate equivalence.

## Exact missing theorem DAG

The direct local-reciprocity route should land the following interfaces in order.

```text
ramified K(i)/K
      |
      +--> no 2-power roots in K except +/-1               [proved]
      |
      +--> nontrivial mod-4 cyclotomic action on inertia    [proved]

dense local reciprocity + completion/maximal-pro-2 universal properties
      |
      v
pro-2 completion(Kˣ) ↠ topAb(G_K(2))                       [proved]
      |
      v
completed reciprocity is injective / exact kernel theorem        [missing]
      |
      v
torsion(topAb(G_K(2))) ≃ μ_{2∞}(K)                         [missing]
      |
      +--> torsion ≃ {±1}                                  [uses proved root lemma]
      v
Nat.card torsion = 2
      |
      v
demushkinQ (G_K(2)) = 2
```

A completion-level equivalence would still be useful, but is strictly stronger than what
density proves:

```lean
noncomputable def proTwoReciprocityEquiv
    (B : MarkedRecip R K) :
  proPCompletion 2 ((↥K)ˣ) ≃ₜ*
    topAbelianization (maxProPQuotient 2 (GalK K))
```

The source model is no longer missing: it is `proPCompletion 2 ((↥K)ˣ)`, the maximal
pro-2 quotient of Mathlib's profinite completion.  The forward map and its surjectivity are
`proTwoReciprocityToTopAb` and `proTwoReciprocityToTopAb_surjective`.  Proving the displayed
equivalence now means proving injectivity, which requires an arithmetic kernel theorem not
contained in `MarkedRecip`.

The minimum missing theorem can avoid exposing that model.  The checked target type
`TwoPowerRoots K` is already defined as `{x : K // ∃ n, x ^ (2 ^ n) = 1}`:

```lean
noncomputable def torsionTopAbMaxProTwoGalKEquiv
    (B : MarkedRecip R K) :
  {g : topAbelianization (maxProPQuotient 2 (GalK K)) // IsOfFinOrder g} ≃
  TwoPowerRoots K
```

After that equivalence, the final proof is only the definition and the already-proved root
cardinality theorem:

```lean
theorem demushkinQ_maxProTwoGalK_of_ramifiedI ... :
  demushkinQ (maxProPQuotient 2 (GalK K)) = 2 := by
  rw [demushkinQ, Nat.card_congr (torsionTopAbMaxProTwoGalKEquiv B),
    natCard_twoPowerRoots_of_ramifiedI hdeltaI hram]
```

An alternative Bockstein route is mathematically plausible: for a finitely generated
Demushkin pro-2 group, nonzero Bockstein should force the torsion order to be exactly `2`.
That route is not shorter in the present library.  It would require a formal Bockstein, its
identification with the cup-square characteristic vector `kappaK`, and a structure theorem for
finitely generated abelian pro-2 groups relating Bockstein to `demushkinQ`.  None of those three
bridges currently exists.

## Recommended next ticket split

1. ~~Define the pro-2 completion model and prove its universal property.~~ Done in
   `GQ2.ProPAbelianization`.
2. ~~Generalize the quotient/abelianization construction to `K` and construct the completed
   reciprocity map.~~ Done, with surjectivity, in `GQ2.Dyadic.ProTwoReciprocity`.
3. Prove the missing arithmetic kernel/injectivity theorem for completed reciprocity.  This may
   be packaged as the full local-CFT completion isomorphism or as a field-specific kernel result.
4. Extend `DyadicUnitFiltration` with the eventual squaring/logarithm theorem for principal
   units, then prove the torsion/free decomposition of completed `Kˣ`.
5. Combine the torsion equivalence with
   `twoPowerRoot_eq_one_or_neg_one_of_ramifiedI` and close the `Nat.card` computation.

This route is non-circular: it proves `q = 2` before invoking any `MLabHypothesis`,
`NLabHypothesis`, or future oriented Labute classification theorem whose antecedents already
include `demushkinQ G = 2`.
