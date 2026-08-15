# W82-CAND lane note

Lane target: the L-row `WordCertificate` at free handle count, the last CAND producer hole.
New module: `GQ2/Dyadic/Instances/LRowCand.lean`, prefix `lCand`, 27 declarations, all pinned in
the file with the measured honest split. Base `a45bc557`; module gen'd green against the mirror.
No new axiom, no sorry, no native_decide, no heartbeat or recursion options.

## The finding that shaped the lane

Wave 76 recorded the L row at `h >= 1` as "new mathematics, not plumbing", on the ground that
the `h = 0` closure works by transporting `Main.lean`'s `wordCertificate_nonempty_lSq` off `Pi`
and there is no `Pi_h` to transport from at higher handle count.

**The diagnosis named the wrong route.** The transport route is indeed unavailable at `h >= 1`,
but it is not the only route and it is not the one the other rows use. `M0` and `N0` build the
certificate directly out of a `Count.CorePresentation`, and

> `Instances.LSquareCore.lCorePresentation h : CorePresentation (2*h+1) (lSqW h) (D_sq h)`

has existed at **every** `h` since the Cores layer landed (`Instances/Cores.lean:146`), together
with its canonical `Ztwo` normalization `lNu h` and both normalization clauses `lNu_sigma` /
`lNu_wild`, also at every `h`. Everything else the record's non-analytic fields need is likewise
already free in `h`: `Count.tameSpecializes_lSq`, `Count.hwild_lSq`,
`Words.LSq.eval_pro2_lSqW_eq_sqRelWord`, `Count.gammaR_topologicallyFinitelyGenerated`,
`Count.htame_of_tameSpecializes`.

So the hole was plumbing after all, and it was one module wide.

A second, smaller finding fell out of the binder audit: the L row's Gate-C headline
`eval_pro2_lSqW_eq_sqRelWord` is stated with **no `T2Space` binder**, which is exactly the
record's binder list, so `coreRel`/`proTwoWord` are one-liners here. The N row needed a
re-derivation in `GeneralCertificates` §6 precisely because its named form
`eval_pro2_nCompact_reindex` carries `[T2Space G]` (verified at `Count/ProTwo.lean:592`).

## What landed

§1, the seven row-specific non-analytic fields at free `h`: `lCandCoreRel`, `lCandProTwoWord`,
`lCandTameSpecializes`, `lCandPro2`, `lCand_ker_pro2`, `lCandPro2_surjective`, `lCandCompat`.
The remaining six proved fields (`tfg`, `smulZmod2`, `contSMulZmod2`, `htriv`, `htame`, `hwild`)
are generic in `(n, q, R)` and are filled inline in §2.

§2, the producer:

- **`lCand_wordCertificate (h q : N) (hq0 : q != 0) (hqe : Even q) ... `** at an arbitrary
  `Ztwo` normalization of the core: **thirteen of the seventeen fields proved**, the four
  analytic clauses (`exactLifting`, `stokes`, `scalar`, `determinant`) carried as explicit
  arguments at exactly the record's types. This is the posture `MCompactCore.mWordCertificate`
  and `genCertNWordCertificate` stand in.
- `lCand_wordCertificateCanonical`: the same at `lNu h`, with all three marking binders
  discharged, so the producer takes free `(h, q)`, the two `q`-conditions and the four clauses
  and nothing else.
- `lCandNu_surjective`, and the four row pins `lCand_row_degree` / `_word` / `_core` /
  `_isProP`, all `rfl` against `SelectedPresentation.L h` and `genAsmCore`.

No `alpha`, no `1 <= alpha`, no `2 <= alpha`: unlike the M template the L row has no threshold
hypothesis anywhere in its chain.

§3, the `h = 0` regression against the committed endpoint:

- `lCand_zero_coreRel : lCandCoreRel 0 = QTwo.coreRelLSq` by `rfl`, and `lCand_zero_proTwoWord`
  likewise. The word-layer fields recover the committed `n = 1` ones on the nose.
- `lCand_zero_nonempty`: `genCert_wordCertificate_nonempty_L_zero` typechecks directly against
  the producer's target type at `h = 0`, so the degree, word, core and `IsProP` witness have not
  drifted.

§4, the feed into the general assembly:

- `lCandBranch`: the odd route's canonical branch datum rebuilt as a **definition** rather than
  the existential `genAsm_branch_of_oddSq_canonical` returns, so `nuP` is definitionally `lNu h`.
  `lCandBranch_exists` recovers the existential, so nothing is lost.
- **`lCandCand`**: a term of *exactly* the type of `GenAsmRowResidual.cand` over that datum,
  from the four analytic clauses. The elaborator is the acceptance check.
- `lCandRowResidual`: the whole `GenAsmRowResidual`, from three ASK clauses at `G_K` and four
  CAND clauses at `Gamma_R`.

§5, the odd row from the seam alone:

- `lCandBranchOfSupply`: the branch datum from `LSquare.SqMarkedForwardSupply B h` and the
  degree pin (the handle-mix binder is `SqCore.gOdd_pivotFix h`, free in `h` since wave 80),
  with `lCandBranchOfSupply_nuP : ... = lNu h` by `rfl`.
- **`lCand_oddRow_of_supply`**: the general theorem's conclusion on the `L h` row from the seam,
  the field inputs, three ASK clauses and four CAND clauses, at **every** handle count.

## What the odd rows of the general theorem now need, in total

1. **The selector**: the wave-81 seam `LSquare.SqMarkedForwardSupply B h`. Discharged at
   `h = 0` (`oddId_markedSupply_degreeOne`); open at `h >= 1`, where every producer in the tree
   consumes frame data (the wave-81 note inventories the three).
2. **`GenAsmFieldInputs`**: structural, row-independent, `n`-free.
3. **Three ASK clauses** at `G_K`: `exactLifting`, `stokes`, `determinant`. `KSupply`'s business,
   not this lane's; the wave-79 house note records that the determinant rung already has its `K`
   clone (`affineDeterminant_galK`) and is a wiring job.
4. **Four CAND clauses** at `Gamma_R (2h+1) q_K (lSqW h)`: `exactLifting`, `stokes`, `scalar`,
   `determinant`. This is the honest residue of the CAND field after the lane, and it is the
   same residue the `M0` and `N0` rows carry, so it is now uniform across all three
   `CorePresentation`-backed rows.

⚠ **[W83-HOUSE, as of `23041e0f`: the `M0` half is right, the `N0` half is not, so "uniform
across all three" overstates it.**  Elaborated explicit binders, four producers side by side:

* `MCompactCore.mWordCertificate`, `MProcyclicCore.mpcWordCertificate`,
  `genCertNpcWordCertificate` and this lane's `lCand_wordCertificateCanonical` all carry the
  four bundles verbatim: `ExactLiftingSemantics`, `StokesDualityCertificate`,
  `ScalarHilbertCertificate`, `AffineDeterminantCertificate`;
* `SqrtNeg2.sqrtNegTwoWordCertificate` carries `PilotHsimp`, `PilotStageSep`, `PilotStageZ`,
  `PilotDet`.  Only `PilotDet` is one of the four (it **is**
  `AffineDeterminantCertificate ... (pilotGamma q) ...`).  `PilotHsimp` is a per-simple-module
  `StokesDuality` statement, i.e. an *input* to the count rather than the count, and
  `PilotStageSep` / `PilotStageZ` are `stageR136`'s two recursion-side residues.

So the `√−2` row's residue is **strictly narrower** and lives one layer below the others': three
of its four sit under the bundles that `M0`, `Mpc`, `Npc` and `L` still carry whole.  A lane
that reads the two as interchangeable will price the `N0` row wrong in either direction.  The
uniform claim is true across **`M0`, `Mpc`, `Npc` and `L`** (four rows, not three), which is the
correct form of the statement and is what `GeneralAssembly.lean`'s constructor table now says.
`scripts/scoreboard.sh` prints this split by elaboration.]**

Item 5 on the pre-lane list, "a `WordCertificate` over `D_sq h` with no producer at free `h`",
is gone. `oddId_candidate_equiv_galK_of_supply`'s docstring still says
"which has no producer at free `h` in this tree"; that sentence is now stale, and a housekeeping
lane should mark it, as should `GeneralAssembly`'s constructor table row
"`L h` | none over `D_sq h`".

## The refuted hypothesis

The lane brief suggested the wave-80/81 odd machinery might discharge the recursion-side clauses
that were the `n = 1` proof's hard part. **It does not, and cannot as stated.** `gOdd_certificate`
produces a `MarkedCoreCertificateSq h chiG nuG`, whose five fields are `abstractEquiv`,
`orientation`, `correction`, `correction_chi`, `correction_nu`; `oddId_supply_iff_certificate`
relates the seam to `Nonempty (MarkedCoreCertificateKTwoSq B h)`, the same record at the two
canonical characters. Not one field of either is a `WordCertificate` field. The odd supply is
consumed by the **selector** (item 1 above), which is a different field of the general assembly
from `CAND`. §4 and §5 make the separation checkable rather than asserted: the seam enters
through `lCandBranchOfSupply`'s arguments and the analytic clauses enter through `lCandCand`'s,
and no argument of either is derivable from the other.

## Axioms: 27 pins, and one finding

25 of the 27 print at most the std-3 set `propext, Classical.choice, Quot.sound`;
`lCand_row_degree` prints none at all. That covers the producer, the canonical form, the whole
`GenAsmRowResidual` feed and the branch datum: **building the L-row certificate out of the core
presentation, and placing `K` on the row, introduce no campaign axiom.**

`lCand_oddRow_of_supply` adds `tateDualityAt`,
`Foundations.absGalQ2_isTopologicallyFinitelyGenerated` and
`Foundations.absGalQ2_localEulerCharacteristic`, exactly `genAsm_candidate_equiv_galK`'s pin,
inherited and nothing more.

The finding: **`lCand_zero_nonempty` is wider than the free-`h` producer.** It adds
`dyadicOrientation`, `localReciprocity` and `peripheralCyclotomicAction`, and they come from the
*committed* `h = 0` closure, not from this module: `genCert_wordCertificate_nonempty_L_zero`
transports off `Pi` through `genAsm_nonempty_equiv_L_core_piBd`, which is where those three
enter. So the free-`h` core-presentation route is **strictly narrower in axioms** than the
`h = 0` transport route it generalizes.

## Two cautions for W83

1. **The `h = 0` closure and the canonical producer are at different markings.** The committed
   `genCert_wordCertificate_nonempty_L_zero` lives at `genCertLNu = nu_2 . genCertLEquiv`, the
   transported `Pi` marking, and `GeneralCertificates` §5's own docstring records that this is
   not claimed to be `lNu 0` and that no comparison is available at this tree. Consequently an
   *unconditional* certificate at `lNu 0` is **not** available even at `h = 0`, and the `h = 0`
   case of `lCand_wordCertificateCanonical` still asks for its four clauses. Anyone reading the
   two as the same object will be wrong.
2. **The existential branch producers drop the marking.** `genAsm_branch_of_oddSq_canonical` and
   `oddId_genAsmBranch_L_of_supply` both return `exists G, G.pres = .L h`, which forgets
   `G.nuP = lNu h`, and the `cand` field is stated at `G.nuP`. That is why §4 rebuilds the datum
   as a definition. The same forgetting affects the four even-row producers
   (`genAsm_branch_of_evenN`, `genAsm_branch_of_evenM`, and the `fieldId_genAsmBranch_*`
   family); a housekeeping lane strengthening those existentials to carry the marking would let
   `genCertNWordCertificateCanonical` and the M-row canonical producer reach their `cand` fields
   the same way.

## Registration

The module is **not** registered in `GQ2.lean`; the lane brief assigns housekeeping to a sibling.
`GQ2/Dyadic/Instances/LRowCand.lean` imports `GQ2.Dyadic.GeneralCertificates` and
`GQ2.Dyadic.SqCore.GradedOddClose` (the second only for `gOdd_pivotFix` in §5).
