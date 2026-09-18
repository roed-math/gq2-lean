# W361 independent final-endpoint scope audit

2026-09-17. Read-only review of the public capstone and its source/certificate/
marking interpretation. **No approval, migration, or unchanged-plan completion
is asserted.** `GeneralMain.lean` and `FieldFamilySpliceOriginalMarked.lean`
were freshly re-elaborated at default Lean limits: both exited zero without
warnings, with the axiom sets below.

Final read-only recheck at 2026-09-17 15:43 UTC: `GeneralMain.lean` again
freshly elaborated without warnings. The preferred original-marked endpoint
still has exactly the standard three plus the nine listed inherited axioms.
The exact existential word/profile/certificate and marking types were reread;
none acquires an optional `NPlaneScalingHypothesis` or finite-stage research
premise from the later N-plane work. This is not a claim that the final
whole-tree fresh build or staged artifact verification has finished.

```text
GeneralMain.lean SHA-256:
acc6e448524c7b04323ecc2f47228937a159ca0ae1ac088878bba20255cc8fa7
Instances/FieldFamilySpliceOriginalMarked.lean SHA-256:
863366197c10abfe460056b4225d6b8a5add76c0ff99bb33d3539579873ed190
```

## Exact theorem, with the existential order exposed

The declaration exported by `GQ2/Dyadic/GeneralMain.lean` is
`GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI` (the module
name is not an additional Lean namespace).

For **every** finite intermediate field `K` of the fixed algebraic closure of
`Q₂` and **every supplied** `RI : RamifiedIData K`, form the canonical `B`,
filtration `FF`, finite parameter bundle, oriented tame bundle `T`, and the
range-based selected branch `S`. The conclusion is, in order:

```text
∃ G : GenAsmFlexibleBranch K B,
  G.degree = S.semantic.degree ∧ SelectedWordProfile FF S G ∧
  ∃ cert : GenAsmFlexibleRowResidualRN FF G,
    Nonempty (AlignedMarkedFieldEquiv G cert.cand T).
```

`G.hdeg` also gives `G.degree = [K:Q₂]`. This is a theorem for all ranks and
selected families, not a finite field/example list. It does not quantify over
an arbitrary prescribed word, selected handle, source marking, or realization
and promise to preserve it. The supplied-bundle and matching-range variants
make the corresponding earlier choices explicit; the bare variant discharges
topology and parameter producers internally.

`RamifiedIData` is literally a square root `deltaI` of `-1` together with
`¬ HasEqualNormValueGroups K deltaI`. It is the standing ramified-`i` restriction,
not a premise proved for every finite dyadic field. Fields containing `i` and
the unramified-`i` case are not newly covered. The odd-degree corollary supplies
RI by an existing uniform theorem.

## What is retained, and what is not

The source is the actual `GammaR G.degree (qOf K FF) G.word`. Its profile in
`FieldFamilySpliceSelectedWord.lean` retains:

| Selected family | Exact retained source profile |
|---|---|
| L, N0, Npc | Exact degree, literal heterogeneous equality of the word with `selectedPresentation S`.word, and exact canonical core equality. |
| M0 | Either that canonical word/core profile, **or** an actual `headHandlePairSpliceW` with selected `j : Fin h`, exact core and `nuP`, and `nuP(U_j)=1`. |
| Mpc | Actual mobile corrected tame splice, with selected discrete `alpha,r,epsilon,h`; exact core and `nuP`; an actual unit `etaD` equal to the D-coordinate; and `etaD = eta + 2^r*w` for some `w : Z₂`. |

For the canonical L/N alternative the profile does not additionally assert
equality of `G.nuP` with a separately named canonical character; the actual
surjective `G.nuP` and its marked realization are carried by `G` itself. The
splice alternatives explicitly identify that character too. An arbitrary
two-adic `etaD` is not silently replaced by a chosen rational display or by
the selected residue representative `eta` as an exact equality.

`cert.cand` is a complete **`WordCertificateRN`**, not an assumed residual
proposition: it carries tame specialization, the pro-two presented core/map,
its exact maximal-pro-two kernel and surjectivity, compatibility, finite
generation, corrected exact lifting, full Stokes duality, scalar Hilbert data,
the affine determinant, and tame/wild facts. Its determinant is on the same
literal tame/pro-two maps. `WordCertificateRN.toSourceRN` produces the actual
candidate `SourceDataRN`. No word-specific Stokes, determinant, norm packet,
or matrix/phase assumption is an input to this final theorem.

Choose the one `M : AlignedMarkedFieldEquiv G cert.cand T` supplied by the
conclusion and put `e=M.equiv`, `p=cert.cand.pro2`, `r₀=G.realization.equiv`,
`A₁=alignedRealization …`, and `r₁=A₁.equiv`. On **that same** `e`, all `g` satisfy:

```text
T.tameFK (e g) = tameOfSpec … g
maxProPMk 2 (GalK K) (e g) = r₁ (p g)
A₁.pro2 (e g) = p g
chiCycK K (e g) = chiCycKTwo (r₀ (p g))
B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (p g)).
```

Here `A₁.pro2` is the aligned realization's field-to-core map.
The original character `chiCycKTwo ∘ r₀` is fixed **before** reconstruction.
`alignedRealization_chi_eq_original`, using
`FieldCyclotomicCharacteristic.chiCycKTwo_characteristic_ramifiedI`, proves that
calibration preserves it. It is not defined afterward by pulling back along
`e`. In contrast, the literal pro-two square uses **r₁**, not r₀. The theorem
does not assert `r₁=r₀`. `M.branch` changes only this realization; word, core,
degree, full `nuP`, certificate, and selected profile are unchanged.

“Full unramified character” here means the entire **Z₂-valued** character,
not merely mod two. `ztwoIota` is the continuous equivalence from `Ztwo` to
`Multiplicative Z₂`; the displayed equation is not a separate choice of a
full Zhat Frobenius lift. This matches plan §7(6).

## Trust boundary confirmed by fresh axiom prints

The canonical capstone has standard three plus exactly:

```text
hilbertSymbol_normCriterion_finiteDyadic
localReciprocity
markedRecipAt
orientedTameQuotientAt
peripheralCyclotomicAction
relativeStiefelWhitney_dyadic
tateDualityAt
Foundations.absGalQ2_isTopologicallyFinitelyGenerated
Foundations.absGalQ2_localEulerCharacteristic
```

The supplied-bundle/matching-range/canonical-parameter versions have standard
three plus the other six: they omit `localReciprocity`, `markedRecipAt`, and
`orientedTameQuotientAt` from their axiom footprint because those bundles are
inputs. These are inherited standing inputs, not new W361 word/presentation
axioms. Source-only standard-three certificates do not make the field endpoint
axiom-free; verifying primary-source citations does not remove these axioms.

## Mathematical frontier versus acceptance work

**For the theorem just stated, relative to this trust boundary, no remaining
mathematical premise was found.** In particular the all-family selected source,
shared field data, RN comparison, tame-marked reconstruction, induced pro-two
alignment, and original-character compatibility are actually composed in its
proof. This is stronger than the older abstract-isomorphism endpoint.

That does not settle every stronger historical formulation:

- The universal old **frozen M-word** claim is not this theorem. Its replacement
  by explicit pair/mobile splice constructors is a change of mathematical
  statement requiring owner/editorial adoption, not a missing equality one
  may silently infer. Existing separately proved frozen special cases remain.
- **16:47 UTC update:** the required primitive-row N correction is now joined
  by unconditional strong `NPlaneScalingHypothesis`, arbitrary integral plane
  GL2 lifting, and `nStabParam_fullFrame_lift_general`. The latter realizes
  every admissible `NStabParam` on the full canonical abelianization, including
  torsion, with identity handle columns, uniformly for alpha >= 2 and all h.
  The production proofs are independently checked, standard-three only; their
  final source-bound build and replay status is tracked in
  `w361-final-verification.md`: all 1,541 modules and the complete source-bound
  replay passed, followed by an independent post-replay content recheck.
  This closes the former stage and torsion-row gaps for that precise family.
  It does not by itself lift every arbitrary handle-mixing automorphism of
  the full invariant triple. That wider reduction remains separate under the
  original packet wording. Likewise, required M matching is not unrestricted
  canonical-pivot transitivity or every originally proposed pure Nielsen lift.
- Requiring pointwise preservation of an arbitrary preassigned realization,
  extending to non-RI fields, or eliminating the inherited field axioms would
  be genuinely stronger projects, not hidden premises of the current result.
- The corrected RN interface changes the general R-fibre coefficient to
  `zRN = SN.tMult(|R|)*|D_R| = |R|^(n+1)*|D_R|`; degree one recovers the frozen
  coefficient by `zRN_standard_one`. “The induction is unchanged” needs the
  amendment's qualification. This correction is already proved, not pending.
- The completed Npc Hessian route uses full-offset normal coordinates and an
  arbitrary quadratic head diagonal. It must not be replaced in publication
  by an unconditional inverse-`Lc`/zero-offset slice claim. The old slice is
  valid only with its own hypotheses; the new actual-boundary records are
  already available.

## Comparison with the readiness/map documents

The theorem-level qualifications in `w361-acceptance-readiness.md` and
`w361-compositional-certificate-map.md` are sound: RI, changed words, actual unit
congruence, existential realization, full quadratic phase, and inherited axioms
are retained. **No stronger fixed-realization or frozen-M assertion was found
in the public capstone documentation.**

The earlier word-only artifact-status observations have been superseded, and
the readiness/map documents now describe the synchronized ten-item packets.
The tree contains typed `GeneralFoxTemplate`, `GeneralPhaseTemplate`,
`GeneralPhaseCoverTemplate`, corresponding renderers, actual-boundary Hessian
records for pair/mobile and L/N, and `w361_certificate_packet.py` with staged
combined packet JSON, proof probes, and ten-section TeX. All 29 PDF pages have
passed visual QA. Earlier “still to emit” statements are historical inventories,
not current proof gaps. Final synchronized-source verification is tracked
separately in `w361-final-verification.md`; visual QA alone does not establish it.

Actual remaining acceptance work is:

1. Approve the precise amended theorem/MC targets, RN explanation, new word
   names, full-offset Npc interpretation, and symbolic binding/display contract.
2. Finish and independently check the chosen final synchronized artifact set,
   including L/N publication treatment. The five frozen appendix skeletons
   still have **40 actual item-2–9 TODO invocations**; new pair/mobile packets
   do not automatically fill or approve those legacy files. A theorem-reference
   probe plus AST replay is not a claim that every sentence or coordinate map
   in a hand-authored appendix is itself generated syntax.
3. Run the accepted gate on one final source/toolchain/artifact snapshot, with
   clean full build, axiom/sorry checks, unchanged Q₂ capstone footprints,
   degree-one RN regression, and the corrected sqrt(-10) branch. Do not relabel
   an earlier successful snapshot as this final release check.
4. Obtain the owner-authorized paper/packet/census updates and G3 decision.
   The historical blanket `1+8 Z₂ ⊆ I` prose also needs its already documented
   general-degree correction; it is not a field of the current axiom bundle.

These are not newly discovered Stokes or determinant gaps. Nor can a passing
staged hash checker, or the present theorem's proof, substitute for explicit
acceptance of the revised mathematical target and publication format.
