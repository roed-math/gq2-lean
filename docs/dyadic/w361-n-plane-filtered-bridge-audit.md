# W361 — N-plane filtered bridges and remaining stage obligation

Historical audit snapshot at 2026-09-17 15:57 UTC. The filtered-group results
audited below do not by themselves discharge `NPlaneScalingHypothesis`.
Subsequently, the integrated ambient free-basis construction and
`nPlaneScalingHypothesis_general` have discharged that hypothesis uniformly
for `alpha >= 2` and every handle rank. See `w361-n-general-scaling-audit.md`
and `w361-final-verification.md` for the later proof and current verification
status. Neither this audit nor the subsequent proof constitutes owner approval
of a changed specification or a release.

## Independently checked modules

Fresh default Lean checks were run against the campaign dependency cache,
with no options, placeholder axioms, or admitted proofs. These are source
checks, not a claim of a fresh rebuild of every dependency.

| Module | Public pins | Result |
|---|---:|---|
| `MarkedCore/NPlaneCompactness.lean` | 12 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneFilteredDerivative.lean` | 12 | Warning-free; subsets of the standard three |
| `Roe/Labute/MixedPowerCongruence.lean` | 8 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneMixedGroupKernel.lean` | 4 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneFilteredDerivativeLinear.lean` | 6 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneKernelTuple.lean` | 6 | Warning-free; subsets of the standard three |
| `MarkedCore/FreeNOrientation.lean` | 7 | Warning-free; standard three axioms |
| `MarkedCore/FreeProTwoUnitPower.lean` | 12 | Warning-free; standard three axioms |
| `MarkedCore/ProTwoRowCorrection.lean` | 4 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneKernelTupleDerivative.lean` | 2 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneKernelDiagonal.lean` | 7 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneCorrectionKernel.lean` | 7 | Warning-free; standard three axioms |
| `ProTwoFiniteProduct.lean` | 2 | Warning-free; standard three axioms |
| `MarkedCore/FreeProTwoFiniteProduct.lean` | 2 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneRowRefinement.lean` | 2 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneRelativeRefinement.lean` | 1 | Warning-free; standard three axioms |
| `MarkedCore/FreeProTwoBasisCorrection.lean` | 7 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneFreeStageTransfer.lean` | 5 | Warning-free; standard three axioms |
| `MarkedCore/NPlaneUnrestrictedReduction.lean` | 3 | Warning-free; standard three axioms |

The standard three are `propext`, `Classical.choice`, and `Quot.sound`.
The two newly authored modules in this lane, `MarkedCore/NPlaneOrdinaryHead.lean`
and `MarkedCore/NPlaneFilteredSlack.lean`, each also compile warning-free,
have five public standard-three pins, and have cached object files. They
are not described as independently authored reviews of themselves.
The additionally authored `MarkedCore/NPlaneFilteredSlots.lean` has eleven
warning-free public pins, all subsets of the standard three, and is cached.

## What the statements actually give

1. **Compactness is an exact reduction.**
   `nPlaneScalingHypothesis_iff_stages` equates the strong scaling claim
   with nonempty exact-row upstairs stage sets at every depth. Each stage
   already has simultaneous integral rows for every ordinary character,
   exact orientation, and generation modulo the Frattini subgroup. Only
   its relator equation is approximate. Closedness and nested compactness
   yield one tuple, and finite-generation/Hopfian arguments give an actual
   automorphism. No compatible choice of finite-stage witnesses is assumed.
   Nonemptiness has **not** thereby been proved.

2. **The derivative is for the literal N word.**
   `nFiltered_nRelWord` is an identity in `Q_(k+1)`, for `k >= 3`,
   `alpha >= 2`, and corrections in the image of `lambda_(k-1)`.
   Its head contribution is
   `t0^2 [t0,m0] [t0,m1] [t1,m0]`, not merely the paired brackets.
   The remaining core and all handles retain the repository's fixed order.
   Centrality of the derivative factors justifies their rearrangement.
   The source-group compact, Hausdorff, and totally disconnected assumptions
   are explicit in this module. There is no derivative-surjectivity claim.

3. **The exceptional mixed-power term is retained at every depth.**
   `commP_pow_two_level` proves, for arbitrary topological groups and `m >= 1`,

   ```text
   [v^(2^m),g] = [v,g]^(2^m) [[v,g],v]^(2^(m-1))  in Q_(m+3).
   ```

   The inverse-first commutator convention gives the displayed factor order.
   `commP_pow_two_level_of_mem` separately proves power/bracket compatibility
   above degree one. These are actual quotient identities; they are not
   an implicitly constructed graded Lie ring or a restricted-image theorem.

4. **The extra head digit comes from the actual ordinary row.**
   `nRelWord_correction_ordinary_row` derives

   ```text
   f(r(y*t) target^-1) = (2+2^alpha) f(t0)
   ```

   in additive notation, assuming only `f(r(y)) = f(target)`.
   For `alpha >= 2`, the coefficient is exactly twice a unit. Thus defect
   membership in `lambda_(k+2)` implies `2^k | f(t0)`.
   `exists_freeTwo_nHead_characterZero_same_class` applies the already
   proved exact coordinate-removal construction, yielding an ordinary-
   character-zero representative in the same filtered class. The threshold
   matters: at `alpha = 1`, the head exponent is four, not twice a unit.

5. **Representative replacement preserves the same relator stage.**
   `nRelWord_correction_level_congr` needs only `alpha >= 1` and pointwise
   `t_i^-1 t'_i in lambda_k`. It proves equality of the actual relator
   values in `Q_(k+1)` for arbitrary original and correction tuples.
   `nRelWord_correction_defect_mem_iff` keeps the identical target word.
   Its proof is the pure group fact that central involutions leave an
   even-exponent head and every commutator unchanged. No lower-depth
   membership, compactness, pro-two, or finite-generation premise is needed.

6. **The initial free substitution and orientation condition are concrete.**
   `freeTwoUnitPowerEquiv` has the explicit inverse using the reciprocal
   two-adic unit. For a selected slot other than zero, its N-relator error
   lies in `lambda_3` and vanishes under every homomorphism to an abelian
   group, not only under mod-two characters. Orientation preservation of
   the substitution requires that the selected slot is not one; the
   intended slot two meets both exclusions. For `alpha >= 2`,
   `freeNOrientation_eq_one_iff` identifies the orientation kernel with
   the exact zero ordinary coordinate at slot one, using the proved
   injectivity of powering by `nUnit alpha`. It does not use an assumed
   logarithm or a silently invertible orientation scalar.

7. **The actual indexed derivative-kernel adapter is now checked.**
   `nFilteredDerivative_mul` handles arbitrary products of correction
   tuples, with no disjoint-support condition. Combined with the actual
   single-slot formula and the uniform mixed group identity,
   `nPlaneKernelTuple_filteredDerivative` proves that the literal five-
   increment tuple is in the derivative kernel in `Q_(n+4)`.
   Its only slot exclusions are `i != 0` and `v != 1`. Every tuple entry
   is in `lambda_(n+2)`, including when slots coincide. The full literal
   relator congruence is `nPlaneKernelTuple_nRelWord`, for `alpha >= 2`,
   and needs no assumption that the old relator already vanishes.

8. **Finite exact-row interpolation is proved under explicit witnesses.**
   `exists_closedSubgroup_same_rows` constructs arbitrary two-adic powers
   and an ordered finite product of diagonal witnesses in a supplied closed
   subgroup of a compact Hausdorff totally disconnected pro-two group.
   The scale at a row may be zero; nonzero or unit scales are not assumed.
   `exists_closedSubgroup_rowZero_same_coset` then removes all those rows
   exactly. Neither theorem silently constructs the relevant N derivative-
   kernel subgroup, its witnesses, or their diagonal matrix at a moving
   marking. Normality of the supplied subgroup is not required.
   The two `_fintype` wrappers now construct their enumeration by
   `Fintype.equivFin`; arbitrary finite product-indexed row families are
   supported without a supplied enumeration or another mathematical premise.

9. **The diagonal witnesses are for the actual current marking.**
   `nPlaneKernelTuple_coordinate_diagonal` assumes explicit current rows
   `coord_j(y_v) = if j=v then u_v else 0`, with `u_v` a unit. It proves
   the exact coefficient `2^(n+1)*u_v` at the selected slot-coordinate
   pair and zero elsewhere. The initial unit-power marking is proved to
   have precisely these rows, including the `kappa` weight at the scaled
   generator. `nPlaneKernelTuple_current_orientation` also accepts the
   actual current orientation profile explicitly. Neither result claims
   that a subsequent unconstructed stage already preserves that profile.

10. **The correction kernel is a genuine closed subgroup.**
    `nPlaneCorrectionKernel k hk m` consists of actual group tuples of
    depth `k-1` with derivative one. The group laws follow from checked
    multiplicativity, without imposing disjoint supports. The uniform
    kernel tuples belong to it. `isClosed_nPlaneCorrectionKernel` uses
    the literal `alpha=2` relator-error preimage, thereby avoiding a
    hidden quotient-separation premise; the derivative is independent
    of `alpha >= 2`. `nRelWord_defect_mul_correctionKernel_iff` proves
    that multiplying any depth-correct correction tuple by this subgroup
    preserves the same next-level target defect, even when that first
    correction is not itself in the kernel.

11. **The finite all-row assembly is now an actual theorem.**
    `exists_nPlane_rowZero_same_kernelCoset` uses all slot-coordinate pairs
    as its finite row index. At `i != 0`, `v != 1`, its diagonal scale is
    `2^(n+1)*u_v` and its witness is the actual kernel tuple. At excluded
    pairs the scale is zero and the witness is the identity. Exact zero
    head rows and exact orientation justify the excluded zero rows;
    filtration depth itself supplies divisibility at the other rows.
    The tuple group's pro-two property is proved by
    `isProTwo_freeN_tuple`, not left as an additional hypothesis.
    The result preserves depth `lambda_(n+2)` and the literal relator
    value in `Q_(n+4)` while killing every coordinate. The companion
    `exists_nPlane_characterZero_refinement` derives exact vanishing of
    every continuous ordinary character and of the canonical orientation.
    The proof does not require the kernel witnesses themselves to have
    the current marking's canonical orientation profile: all output
    coordinates, including the orientation coordinate, vanish exactly.

12. **The head cleanup and row interpolation have been composed.**
    `exists_nPlane_relative_correction` in `NPlaneRelativeRefinement`
    takes an existing correction `t`, the current unit-diagonal marking,
    exact equality `f(r(y)) = f(target)` for every continuous ordinary
    character, depth `t_i in lambda_(n+2)`, exact orientation zero for
    `t`, and improved defect `r(y*t) target^-1 in lambda_(n+4)`.
    It removes the head's rows within its `lambda_(n+2)/lambda_(n+3)`
    class, uses slack invariance, and applies the actual all-row result.
    The output has the same depth, exact zero orientation and all ordinary
    rows, and the same target-defect bound. In particular, the current
    relator/target ordinary-row equality is an explicit premise, not a
    consequence asserted for an arbitrary target.

13. **Basis persistence and the DN stage adapter are checked.**
    `exists_freeTwoBasisCorrection` shows that right correction of an actual
    free basis by arbitrary `lambda_2` elements gives another actual free
    basis. It uses the pro-two Frattini criterion and profinite Hopficity,
    with no row, orientation, or relator condition. Separately,
    `nPlaneStageSet_of_free_exact_stage` takes a supplied free automorphism,
    its exact canonical orientation equations, exact slot-two unit-scaled
    coordinate diagonal, and its literal relator defect in `lambda_k`.
    It yields the exact DN stage at level `k`. The canonical projection is
    proved surjective and orientation-compatible; all ordinary DN rows
    are derived by free-coordinate factorization, and the automorphism
    supplies the required generation. This adapter has no alpha restriction
    and does not supply the free stages themselves.

14. **The final conditional induction is now checked.**
    `exists_nFree_exact_stage` starts with the actual unit-power free basis,
    iterates the supplied unrestricted corrections, refines each one, and
    preserves exact diagonal rows and the original orientation. The new
    basis at each step is an actual continuous free automorphism. Its
    error has depth `n+3`. Combining this with quotient transport and the
    previously checked compactness theorem proves
    `nPlaneScalingHypothesis_of_unrestrictedStageSupply` for `alpha >= 2`.
    Its premise `NUnrestrictedStageSupply alpha h` remains explicit.

## Exact remaining mathematical seam

The sole unproved input to the new sufficient reduction is the uniform
nonempty derivative-fiber assertion `NUnrestrictedStageSupply alpha h`.
Its exact content is: for every `n` and every actual free automorphism
preserving the canonical orientation, if its literal N-relator error has
depth `n+3`, there is a correction tuple in `lambda_(n+2)`, with each entry
in the orientation kernel, whose improved error has depth `n+4`.
It assumes no ordinary-row restrictions on that correction. The kernel
vectors and closed-kernel interpolation do **not** prove this range assertion.

This supply ranges over all such orientation-preserving free automorphisms,
not just the diagonal ones used by the constructed induction. Therefore the
checked result is a **sufficient implication**, not a claimed equivalence
between this supply and strong N scaling. The older exact-stage compactness
criterion remains an equivalence. Neither criterion has a producer of its
remaining existence premise in this package.

The current-marking invariant must still be carried through that assembly:
the row of a kernel witness is `2^(n+1) f(y_v)`, with the actual diagonal
unit, not implicitly the row of an unchanged free generator. The new
diagonal module handles the algebra under the precise invariant, and
proves it at the initial tuple. The relative refinement now supplies
exact zero rows on its output correction; the final conditional induction
now carries those invariants at every depth, and the stage adapter is checked.
The finite all-row construction described in
item 11 is proved, no longer merely a proposed implementation.

The actual kernel proof now avoids a global mixed-Lie construction: it
uses `SqCore.GradedGammaThreeFour.gThreeFour_jacobi` at `Q_4`, followed
by uniform square transport. It does not misapply that file's stronger
universal-centrality helper at higher quotients. No finite list of
nilpotency classes is proposed here.

## Frozen-source necessary-condition and registration recheck

A further read-only check of the frozen combined reduction found no
ordinary-row or orientation contradiction in its proposed sufficient
input, in the theorem's stated range `alpha >= 2`:

- For an arbitrary current free automorphism, the ordinary row of its
  relator defect is `(2+2^alpha) (f(e(a))-f(a))`. Membership of that defect
  in `lambda_(n+3)` forces `2^(n+1)` to divide the head-row difference,
  because the head exponent is twice a unit. That is precisely the row
  divisibility available in corrections of depth `lambda_(n+2)`, not an
  incompatible extra digit. This check uses the general divisibility and
  actual word-row identities; it is not a derivative-image proof.
- Exact orientation preservation fixes the ordinary b-coordinate. The
  checked `freeNRelatorDefect_crossed` also kills the actual defect under
  every crossed-lift homomorphism with the canonical orientation as base.
  Thus this necessary annihilation condition is available, not silently
  presumed. Its sufficiency for the required filtered image remains open.

Fresh elaboration of `scripts/w361_artifact_axiom_audit.lean` against the
campaign cache reports `ARTIFACT_AXIOM_AUDIT_PASS|504`: all 504 names exist,
are unique, and have no axioms beyond the standard three. In particular,
all 26 public pins from the final eight row-interpolation, product,
row-refinement, relative-refinement, basis, stage-transfer and reduction
modules are registered. Standard-three certification of the implication
does not turn its explicit `NUnrestrictedStageSupply` premise into a theorem.

The audit's 69 imports all belong to the 1,531-module source umbrella
closure. The five new executable exporters (`GeneralTemplateExport`,
`GeneralTemplateLNExport`, `GeneralFoxTemplateExport`,
`GeneralPhaseTemplateExport`, `GeneralPhaseCoverTemplateExport`) are
intentionally outside that umbrella, and each imports only umbrella
libraries. The older `Word.Export` library remains inside. This checks
registration and source connectivity, not completion of the concurrently
running hardened fresh build or acceptance of the staged publication format.

The checked pin-list source hash is
`50004e2a7892819bcb10a02b0d87ef183ed1dfe67b65cef9cf6d95458566fdc1`;
the checked umbrella source hash is
`a0b42684fe7013429152004045590346c7fd94543fa1971a17ccaf8ad96b19e7`.

## Reviewed source hashes

```text
NPlaneCompactness       e06f5c52d0dd55eadda71da741d2d0eb1eab50090dbcd2b103d4bfd83364da39
NPlaneFilteredDerivative 18153e02f78a9cb01eeb35f084c05bda1bfc667f9da72009226be14ad962e78b
MixedPowerCongruence    eec5e1be558379ba8c1045ddc45310c4ecc703485da84dec3a6f130aa22f600b
NPlaneOrdinaryHead      7b87aa049120fb7747d6e4c341afd9d818bf97db43ccb57c69e880066b6ea26f
NPlaneFilteredSlack     ec0e42db3a66d6a0e8ac3f8e91f9fd1051c44231858aa93ad3034075226b2853
NPlaneMixedGroupKernel  9b6274e27220368177e946702d40814ab7a0c2b2a8cddb3ef96ea8d44c530e13
NPlaneFilteredSlots     76bec316acee501224b662f13cc509d6f2c5b49facf70174f351c18526a64376
NPlaneFilteredDerivativeLinear eab85dfe52502f3940c8ef2c157ee13c1ff5d22442fda246af9b878a4e394159
NPlaneKernelTuple       84b420f8c4a9876d25ab3c10c28805b38d60a1b8226c24641c06cd0049601cf4
FreeNOrientation        abba5ab2e44a3e0fd20a14deefd2aa8d452ce223437a0a8df83e9838cca0b5f8
FreeProTwoUnitPower     09c3930f97467638a7c7e10792a0103fc5faef132a8af08129bf5f055e6b291f
ProTwoRowCorrection     1ecdf93feaaab966c58bb482ce8f01904d908249890c1a5a6f01d00ba1c1399e
NPlaneKernelTupleDerivative 2bcaad5ab129083b847b30e36291a1dfac64554498acf0c7a5475e02993a73af
NPlaneKernelDiagonal    6f338275e03d9e29a4e57c308259e62b01dde2ce5a2f37537483c0cba81db482
NPlaneCorrectionKernel  dae2c8148c56062fd78b6d156792a8b86e1a064e0e41cbc39cae4bbeb771b070
ProTwoFiniteProduct     056e93ffb4c6b941f0eb99b185b8f793d5d4b58d9824d907ffe94f9fedc565cf
FreeProTwoFiniteProduct 321955c5e38afd7665e4de5cf408a42c08fab14e46b271cdd71be04812ea238b
NPlaneRowRefinement     198b96f527b020a4d1d587da7e1f79a722e4cc580157625a097d91788cfe34f2
NPlaneRelativeRefinement 9109ba2ba87f04c9909aa4555ecf99881334c28610495c85a31de61c6a3e73f8
FreeProTwoBasisCorrection 539e4e5ee14dedcdcc2bef5189db9474196ca76d676b470de2effe262e84b62a
NPlaneFreeStageTransfer 766cbe7cd458d4dfa42c218e9b11a6067b2c62e97f3bdc92eac23dbc7f1463ff
NPlaneUnrestrictedReduction dbf3b81229f1646e4c678482ed8ab1cb9ab369aa81825123a198eac05990b907
```
