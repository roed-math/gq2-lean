# Owner decision items — wave 37 (2026-08-05)

Six items surfaced during the wave. Item 1 is a genuine mathematical constraint on the
general-`K` program and needs a decision; items 2–6 are statement or documentation defects
with recommended fixes. Nothing here blocks the odd-degree L row, which is now unconditional
on the forward side.

## 1. DECISION: the ramified Arf conclusion is false at even residue degree

**Finding.** The determinant analysis' ramified branch concludes `Arf(q̄_U) = 0`. That
conclusion holds at residue cardinality `q = 2^f` **only when `f` is odd**. At `q = 4` it is
false, with an explicit counterexample: `C = D₅` acting on `V = 𝔽₁₆` with `t = ·ζ₅` and
`s = Frob²`, `q̄(x) = Tr(c x⁵)` for `c ∉ 𝔽₄`. There `V^U = 𝔽₄` has four elements rather than
the predicted two, `rank(1+U) = 2 ≢ s_V`, and Wall's formula gives `Arf(q̄_U) = 1`. The
witness was verified twice by independent routes (the rank formula, and directly via
`q̄_U = q̄ + ℓ`). The general count is

    #V^U = 2^(gcd(deg P, F·ω) · s_V),

whose exponent is odd exactly when `F` is odd.

**Impact.** None on the L row: odd degree forces `f` odd, and
`wordCertificateRN_lSq_pow` is stated with `Odd f`, so the L certificate is unconditional
on its whole branch. The **even rows** are affected, since they admit even residue degree.

*Narrowing (added 2026-08-06).* The even rows' **Stokes** lane is unaffected: the compact-M
ramified branch was closed without consuming any Arf sign (the pairing separates primal from
dual coordinates and never evaluates a quadratic form), and a sweep of the even Stokes
branches found no place where the wrong sign could be inherited. The exposure is confined to
the even rows' **determinant** residues, which are not yet built — so the decision below can
be taken when that lane opens, not before.

**Options.**

1. **Restrict the even-row program to `f` odd.** Cheapest; leaves the even rows' general
   statement incomplete at even residue degree.
2. **Carry the corrected Gauss sign** `(−1)^(gcd(deg P, F·ω) + 1)` through §6 and the
   determinant bridge. More work, and it changes displayed statements in the paper's §6.
3. Split: prove the even rows at `f` odd now, open a separate ticket for the sign-corrected
   general form.

**Recommendation:** option 3 — it unblocks the even rows immediately and isolates the sign
work, which is a self-contained §6 revision.

## 1b. DECISION: the general-K route's axiom print is not nested in the ℚ₂ capstone's

*(added 2026-08-06)*

The odd-degree endpoint reached through the new general-`K` machine, specialized to
`[K:ℚ₂] = 1`, was intended as an independent check on the whole construction: its axiom print
should ideally be a subset of the frozen ℚ₂ capstone's. It is **not** — the two are
incomparable:

* the new route **carries** `markedRecipAt` (general-`K` marked reciprocity), which the capstone
  does not;
* the new route **avoids** `dyadicOrientation` (B3c), `peripheralCyclotomicAction` (B8) and
  `tameQuotient`, which the capstone uses;
* six census members are shared.

Two of the three absences are explained and benign: `tameQuotient` arrives as the hypothesis
`T : OrientedTameQuotientK B FF` rather than from the axiom, and the frame lane reaches the
pro-2 block without the rank-three certificate where B3c and B8 live.

The live question is `markedRecipAt`. **Options:** (a) accept the incomparable print and drop
the "independent check" framing; (b) route the ℚ₂ instantiation's marked reciprocity through
`localReciprocity` directly, restoring nesting; (c) prove the ℚ₂ specialization of
`markedRecipAt` from `localReciprocity` once, which would make every general-`K` endpoint nest
at `[K:ℚ₂] = 1`.

**Recommendation:** (c) if it is cheap — it is the version that makes the check meaningful for
*all* future general-`K` endpoints, not just this one — otherwise (a), stated plainly in the
paper rather than silently.

*Update 2026-08-06:* the degree-one endpoint is now unconditional
(`NuAdapted.gammaR_lSq_equiv_galK_degreeOne`) and its verified root-level print is std-3 +
{B1, B3c, B5, B5-K, B6, B7, B8, B9, B11a}. Two of the three axioms the route previously avoided
came back — `dyadicOrientation` (B3c) and `peripheralCyclotomicAction` (B8) — because the two
pivot subgroups are built from `prop_3_8_lift` (B8) and the Labute-orientation transport (B3c).
So the print is now the capstone's nine plus `markedRecipAt`, and the nesting question reduces
to that single axiom exactly as stated above. A **cheap follow-up** exists if you want the
footprint split: the *translation* family can be made axiom-free via `thetaEquiv`
(`thetaHom : A ↦ A^{S^b}, S ↦ S, Y ↦ Y·S^b` preserves `d0Word` on the nose, verified by hand),
while the `u`-scaling is genuinely where B8 sits.

### Update 2026-08-06 (W42-NEST): §1b is **resolved** — B5-K was plumbing, and the check now nests

**Measurement.** `markedRecipAt` is **not mathematically load-bearing** anywhere on the
degree-one path. Of the 64 367 declarations in the milestone's reachable closure, exactly
**three** apply the axiom, and all three apply it at the *ambient* field `K`, as the argument of
a lemma that is generic in the bundle and prints the standard three:

| consumer | applies | the generic lemma's binder |
| --- | --- | --- |
| `oddDegreeGalKSq_allStagePrimitiveResidualVanishing` (`…LabuteVariableStageTwo.lean:117`) | `chiCycKTwo_surjective_of_odd_finrank K (markedRecipAt K) hodd` | `{R : LocalReciprocity} (B : MarkedRecip R K)` |
| `nonempty_orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply` (`…FieldRigidity.lean:316`) | `SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply (markedRecipAt K) hodd` | same |
| `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` (`…LabuteFrattiniFrame.lean:940,951`) | both, plus `cyclotomicModEightOmegaClassKTwo_ne_zero (markedRecipAt K) hodd` | same |

(`EvenDemushkinQ.lean:178-180` is the fourth call site in the tree and is **not** reachable from
the odd-degree route.) So B5-K's entire contribution here is surjectivity of `chiCycKTwo` at odd
degree, which the caller's own `B : MarkedRecip Rec K` supplies at std-3. B5 comes along only
because `markedRecipAt`'s *type* mentions `localReciprocity`.

Two of the three consumers simply never took a bundle binder; the third cannot, because
`OddDegreeSqCyclotomicFrattiniFrameSupply`
(`GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean:168`) quantifies over **every** `K`
internally, so no `K`-indexed bundle is in scope.

**Result.** `GQ2/Dyadic/Instances/DegreeOneNesting.lean` re-derives the forward route with the
bundle threaded (the committed proofs verbatim, `(markedRecipAt K)` → `B`) and reaches
`Nesting.gammaR_lSq_equiv_galK_degreeOne_nested_unconditional`, which has **exactly the
committed milestone's type** (pinned by two `example`s) and whose verified root-level print is

    std-3 + {B1, B3c, B6, B7, B8, B9, B11a}

i.e. the frozen `ℚ₂` capstone's nine **minus** `localReciprocity` (B5) and `tameQuotient` (B10) —
a **strict subset**. The degree-one check therefore nests.

On independence, measured rather than asserted: the new endpoint depends on **none** of
`main_presentation_literal_roe{,_unconditional}`, `main_presentation_literal`,
`Dyadic.QTwo.candidateGroup_lSq_equiv_absGalQ2`, `candidate_equiv_absoluteGalois`,
`Roe.gammaR_lSq_equiv_roe`, `eq_154_R`, so it is not circular against the theorem it checks. It
*does* depend on `GQ2.Roe.Labute.bLab` — but so does the committed milestone, by the same route
(the two pivot subgroups at `h = 0`), so that is not a difference between the two.

Per-headline prints, all measured at the root:

| declaration | print (beyond std-3) |
| --- | --- |
| `Nesting.allStagePrimitiveResidualVanishing_of_markedRecip` | B1 |
| `Nesting.orientedEquiv_of_oddDegree_of_base` | B1, B6, B7 |
| `Nesting.exists_cupAdaptedFrattiniFrame_of_markedRecip` | B1, B6, B7, B11a |
| `Nesting.sqCyclotomicStageTuple_levelThree_of_markedRecip` | B1, B6, B7, B11a |
| `Nesting.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_nested` | B1, B6, B7, B9, B11a |
| `Nesting.gammaR_lSq_equiv_galK_degreeOne_nested_unconditional` | B1, B3c, B6, B7, B8, B9, B11a |
| *(for comparison)* `NuAdapted.gammaR_lSq_equiv_galK_degreeOne` | B1, B3c, B5, **B5-K**, B6, B7, B8, B9, B11a |
| *(for comparison)* `main_presentation_literal_roe_unconditional` | B1, B3c, B5, B6, B7, B8, B9, B10, B11a |

B3c and B8 are inherited exactly as the previous update explains (the two pivot subgroups); they
are *inside* the nine, so they do not affect nesting.

**Two side findings worth recording.**

1. The corrected (W41) routes were already B5-K-free — `…oddDegree_of_orientedClearAtUnitPivot`,
   `…_of_subgroups_of_markedSupply`, `…_of_subgroups_of_presentation` and the grand assembly's
   own `LSquare.gammaR_lSq_equiv_galK_degreeOne` all print std-3 + {B1, B6, B7, B9, B11a}. The
   axiom survived only on the *unconditional* milestone, which still routes through
   `…_of_orientedClear` → `orientedEquiv_of_oddDegree`.
2. A `B5-K`-free degree-one route already existed:
   `nonempty_orientedEquiv_bot_of_forwardStageRigidity` (the `K = ⊥` route), print
   std-3 + {B1, B3c, B6, B7}. It is not circular against the ℚ₂ presentation theorem either —
   but it gets its level-three stage base from `sqCyclotomicStageTuple_bot_three_nonempty`, i.e.
   by transporting the `D₀` classification of `G_ℚ₂(2)` itself, so it does not exercise the
   general-`K` frame construction at degree one. The new route builds that base through the
   machine (§0 of `DegreeOneNesting.lean`), which is what makes it a check on the machine. Both
   statements are honest; they test different things, and the memo's framing should say which.

**Recommended follow-up (not done — outside W42-NEST's file ownership).** Make the threading
durable in place and delete the duplicate: give `OddDegreeSqCyclotomicFrattiniFrameSupply` a
bundle binder (`∀ K [insts] {R} (B : MarkedRecip R K), Odd … → ∃ F, F.IsCupAdapted`), replace the
five `(markedRecipAt K)` occurrences at `…LabuteVariableStageTwo.lean:117`,
`…FieldRigidity.lean:316` and `…LabuteFrattiniFrame.lean:940,951` (plus the supply's own
signature) by that binder, and thread `B` through the nine downstream statements
(`oddDegree_sqCyclotomicStageTuple_levelThree`,
`nonempty_orientedEquiv_oddDegree_of_{stageBase_and_actualDefectSupply,
stageBase_and_primitiveResidualVanishing, kernelAdaptedSupply, family_of_cubicNeutralDamage,
cubicNeutralDamage}`, `nonempty_orientedEquiv_oddDegree`, `orientedEquiv_of_oddDegree`, and the
`NuAdapted` `…_of_orientedClear` trio). Each is a one-line signature change; the proofs are
unchanged. That drops B5-K and B5 from **every** general-`K` odd-degree endpoint, not only at
degree one, and lets `DegreeOneNesting.lean` §0 (a 131-line verbatim duplicate kept only as the
demonstrator) be deleted. Census stays at 11; B5-K remains live on the even/boundary lanes.

## 2. `LRamifiedSourceArfSupply` is missing a hypothesis

`GQ2/Dyadic/Instances/GammaLDeterminantResidue.lean:44` quantifies over every block, level
and lift with **no ramification hypothesis**, while its only consumer
(`wordPhaseResidueK_ramified_lSq`) supplies one. In an unramified block the descended source
form has `Arf = 1`, so the literal statement is unprovable. The `hram`-conditioned form is
what is actually built and consumed (`lRamifiedSourceArf_blockK`).

**Recommended fix:** add `hram` to the binder list; `lRamifiedSourceArf_blockK` then produces
the supply verbatim.

## 3. `NLabHypothesis` is false-shaped

`GQ2/Dyadic/MarkedCore/N.lean:1306` has no canonicity guard, unlike its `M` twin. `DM α h`
satisfies **every** clause of `NLabHypothesis α h` (Demushkin, rank `coreRank h`, `q = 2`, and
a continuous character whose range is exactly `imChiN α` — `chiNOnDM`), so the hypothesis
forces `DM α h ≅ DN α h`, which is false: `imChiM α ≠ imChiN α` is now an unconditional
theorem (`EvenNLabWitness.lean`, α ≥ 2). A literal `¬ NLabHypothesis` needs canonicity of the
orientation, precisely the clause the binder drops.

**Recommended fix:** add the canonicity guard the `M` binder carries, or retire the binder —
the even-row route decided this wave (clone the L forward-generator architecture) does not use
it at all.

## 4. Superseded records to deprecate

`LUnramifiedGraphData` / `LRamifiedGraphData` (`GammaLDeterminantUnramified.lean:34`,
`GammaLDeterminantRamified.lean:37`) and their two `_of_graphData` theorems are stated one
level too high: their lower-marking conditions are equations in `DD.C0`, which at
`blockEnrichmentDK` force the whole C-stage to be procyclic (`yc_procyclic_of_c0_graphData`).
The head-factored replacements supersede them.

## 5. Documentation drift

* `docs/dyadic/followup/labute-interface-status.md` — its central finding (the Labute
  hypotheses conclude *unoriented* equivalences and are therefore insufficient) is superseded
  by `OrientationCorrection.lean:456,468,563,584`, which supply the oriented forms; and its
  "remaining invariant" list is off the forward path entirely after this wave.
* Two docstrings miscite `Kummer.kummerCocycleFun_root_indep`; the real name is
  `GQ2.kcf_root_indep'`.
* `HilbertLedger.norm_two_lt_one'` is `private` and was re-proved downstream; de-privatizing
  removes the duplication.

## 6. Small tickets worth opening

* **`MFrame` at general `h`.** `demushkinQ (DM α h) = 2` exists only at `h = 0` and only from
  an `MDecomposition α`, with no producer. The `N`-side template (`N.lean:176–337`) transfers
  almost verbatim; only the torsion generator changes, to `t = Ā·C̄₀^(2^(α−1))`. This would
  make the item-3 counterexample unconditional at every handle count.
* **`α = 1` even cores.** Everything even in this wave assumes `α ≥ 2` (at `α = 1` both cores
  leave the shared Gram). Whether the `α = 1` cores are Demushkin is open and deliberately
  unasserted.
* **`mpcW` Hessian/jet layer** at general `h` (the `npcW` analogue landed this wave).
