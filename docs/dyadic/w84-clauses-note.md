# W84-CLAUSES lane note

Lane targets: (T1) the four analytic clauses at one tied row's candidate carrier, (T2) the ASK
coefficient, (T3, stretch) the pilot's four. Base `45f9c42d`; one new module
`GQ2/Dyadic/Instances/RowClauses.lean`, prefix `rowCl`, 24 declarations, all pinned in the file
with the measured split. No sorry, no new axiom, no `native_decide`, no heartbeat or recursion
option, no em-dash. Nothing else in the tree was edited, so nothing else needs regeneration; the
module and its `#print axioms` block regenerate green against the mirror.

## §0 The headline, and the correction it makes to the brief

The brief said the residue at the three non-pilot rows is "the four analytic clauses at the
candidate carrier plus two ASK blocks", and that `CertificateMain.lean`'s own docstring calls
`ExactLiftingSemantics` at `GammaR n q word` "genuinely unowned, and that is AS1 divergence 4".

**That is out of date at two of the four clauses, and the way it is out of date changes the
shape of the whole question.**

1. `MCompact.exactLiftingRN_unconditional` (`Instances/EvenMRamifiedPairing.lean:175`) proves the
   **corrected** bundle at `GammaR (2+2h) q (mCompactW α h)` from `2 ≤ α`, `q ≠ 0`, `Even q` and
   nothing else. Its `N` twin `NCompact.exactLiftingRN_unconditional`
   (`Instances/N0M0CompactBranches.lean:250`) does the same at `nCompactW`. Both frozen `M0` rows
   and the `N0` row are at `α ≥ 2`.
2. Therefore the *frozen* clause at those carriers is not an analytic obligation at all. It is
   the (136) coefficient, and by the carrier-free form of wave 81's argument it is **equivalent
   to `askCStageVanishing` at that carrier**.

So the row record does not carry an arithmetic residue and a separate candidate-side residue. It
carries **one statement twice**, at two different groups: `askCStageVanishing (galKProfinite K)`
and `askCStageVanishing (GammaR n q_K word)`. Neither wave 81 (which owned only the arithmetic
carrier) nor W83-RECORDS (which read the clause list off the certificate producers) could see
this, because seeing it requires lifting wave 81's equivalence off `G_K` and then noticing that
the candidate side already has the corrected bundle it needs.

## §1 Ticket T1: the four clauses at `M0 2 0` (`ℚ₂(√5)`)

`mCompactW 2 0` is `Instances.Sqrt5.word`; the carrier is `GammaR 2 q_K (mCompactW 2 0)`.

| clause | before this lane | after, and by what |
| --- | --- | --- |
| `exactLifting` | open, "genuinely unowned" | **`askCStageVanishing` at `Γ_R`**, an equivalence, no side condition (`rowCl_mCand_exactLifting_iff`) |
| `scalar` | open | **discharged, unconditionally** (`rowCl_mCand_scalar`) |
| `stokes` | open | **open**; the lane did not narrow it |
| `determinant` | open | **open**; no candidate-side Gauss-`Z` supplier exists anywhere outside the `L` row |

Two of the four close. The two that do not are named in the module as open, with what is missing.

**What `scalar` cost.** `ScalarHilbertCertificate` is `#Hom_c(Γ, 𝔽₂) = SN.homScalar` together
with `#H²(Γ, 𝔽₂) = 2`. The second half was already `MCompact.cardH2_of_uniformPushed`. The first
half **had never been stated at the `M` candidate**: no file in `namespace GQ2.Dyadic.MCompact`
mentions `homCard`. It is `Count.homCard_field_goal` fed the handle-uniform datum surjection
`MCompact.datumRho`, the same surjection `cardH2` already uses, plus the uniform Heisenberg
resolver. Thirteen lines, std-3. This is the compact-`M` twin of
`LSquare.homCard_of_uniformPushed`, which the `L` row has had since `GammaLAnalyticLeaves`; the
`M` row simply never got it. Same story on the `N` side (`rowCl_nCand_homCard_of_uniformPushed`).

**Why `stokes` was not attempted.** The `L` row's four Stokes conjuncts
(`GammaLAnalyticLeaves.lean`, 470 lines, `maxHeartbeats 1200000` on one of them) and the pilot's
four (`SqrtNeg2.lean:608-825`) are each a file's worth of instance plumbing over
`Count.tcocycle_cardN`/`hZcardN`/`hsepN`/`hpartialN`. That is a lane, not a section, and it is
the obvious W85 ticket: the generic suppliers are ready and the `M` row's resolver package is
exactly the one they need.

**Why `determinant` was not attempted.** `SqrtNeg2.lean:893`'s own docstring is still accurate:
the two `GaussZResidueK` clauses "have no candidate-side supplier in the repository". The one
candidate-side producer in the tree is `LSquare.affineDeterminantCertificate_of_wordPhaseSupply`
(`GammaLDeterminantBridge.lean:296`), whose `DeterminantWordPhaseSupply` is word-agnostic in its
statement even though only an `L` instance ships. That is the template, and it is a second W85
ticket.

## §2 The uniformity claim: three rows, not four

W83-RECORDS reading 2 said "the residue is uniform across the four rows". Checked:

* the clause **shapes** are uniform, yes;
* the **reductions** are not automatic, because they run on each branch's own resolver package;
* `M0 3 0` (`ℚ₂(√2)`, `α = 3`) and `N0 2 0` (`ℚ₂(√−2)`, `α = 2`) get the identical treatment,
  and §4 of the module states it at the `N` twin;
* **`Mpc 2 1 false 1 0` (`ℚ₂(√10)`) does not.** `MProcyclicExact` has no
  `exactLiftingRN_unconditional`; its corrected bundle still carries a `Hsimp`-family hypothesis.

So the honest form is **success at one row is success at three**, and the three are the two `M0`
rows and the `N0` row. The `Mpc` row's missing unconditional corrected bundle is a third W85
ticket, and it is a small one: `NpcUnramifiedScalar.uniformPushedHsimp` already exists at
`2 ≤ α` on the procyclic `N` side, so the pattern is in the tree.

## §3 Ticket T2: the ASK coefficient

**Not decided, and the lane says so.** Deciding `askCStageVanishing` still needs a concrete frame
with `1 < #R` and a nonempty `BoundaryLiftsK`, which is a construction (`MarkedTarget`,
`MinimalBlock`, `BoundaryFrameK`, a boundary-framed surjection), not a lemma application.
W81-ASK's §5 said the same and blamed the arithmetic layer for owning no frames.

What changed is that the refutation handle is now **at a carrier where the frames are
constructible**. `rowCl_isEmpty_boundaryLifts_of_exactLifting` is wave 81's
`askC_isEmpty_boundaryLifts_of_exactLifting` at an arbitrary topologically finitely generated
carrier, and `rowCl_mCand_isEmpty_boundaryLifts` puts it at `Γ_R`, where
`tfg_of_isAdmissibleMarkedPresentation` supplies the finiteness and where the branch lanes build
frames for a living. One boundary-framed surjection of the candidate group onto a marked target
with a nontrivial Frattini block refutes the row's `exactLifting` clause outright. That is the
sharpest W85 ticket in this note.

**The owner call has its answer regardless.** `rowCl_rn_both_carriers_sqrtFive` proves the
corrected bundle at **both** of the row's carriers with no residue on either: at `G_K` by
`askC_exactLiftingRN_galK`, at `Γ_R` by `MCompact.exactLiftingRN_unconditional`. So the entire
cost of the frozen spelling at this row is two instances of one coefficient `Prop`, and the RN
spelling has neither. The coefficient question is not a fact about `ℚ₂(√5)`, about `G_K`, or
about the candidate group; it is a property of the frozen (136) coefficient. W81-ASK's
recommendation to restate the records against `ExactLiftingSemanticsRN` is the answer, and it is
now supported on both sides rather than one.

## §4 Ticket T3: the pilot, and why `PilotHsimp` is the wrong target

The brief called `PilotHsimp` "the one-binder-high-leverage item". It is not, and the reason is
visible once §2 of the module is in place.

`PilotStageZ q` (`SqrtNeg2.lean:474`) is `#RCocycle (blockFrameImpl T Blk hE2) f₀ = RF.zR`: the
**frozen** coefficient, verbatim, at every frame. So the pilot's three recursion residues are
downstream of exactly the question T2 asks. `rowCl_pilot_stageVanishing` proves that
`PilotHsimp ∧ PilotStageSep ∧ PilotStageZ` implies `askCStageVanishing` at the pilot carrier, and
`rowCl_pilot_isEmpty_boundaryLifts` that they imply the same emptiness.

Meanwhile the pilot carrier `pilotGamma q` is `NCompact.gamma 2 0 q`, so §4 of the module gives
the corrected bundle there with **no** residue and the scalar clause free. The row also has a
second committed `CAND` producer, `genCertNWordCertificateCanonical`, which W83-RECORDS already
routes through (`canRec_candN`, `canRec_rowResidual_N0_of_analytic`).

**Conclusion: the pilot spelling is strictly dominated.** Everything `sqrtNegTwoWordCertificate`
buys, the `genCertN` spelling buys with two fewer residues and no coefficient condition. Work on
`PilotHsimp` is work on the worse of two routes to the same row. `PilotDet` is untouched and
remains genuinely open, but it is the same `determinant` gap as §1's, not a pilot-specific one.

## §5 What landed, with names

* **§1 of the module**, carrier-free (all std-3): `rowCl_exactLifting_of_stageVanishing`,
  `rowCl_stageVanishing_of_exactLifting`, `rowCl_exactLifting_iff_stageVanishing`,
  `rowCl_exactImageCount_eq_zero_of_exactLifting`, `rowCl_isEmpty_boundaryLifts_of_exactLifting`.
* **§2**, the compact-`M` candidate: `rowCl_mCand_exactLiftingRN`,
  `rowCl_mCand_exactLifting_iff`, `rowCl_mCand_tfg`, `rowCl_mCand_isEmpty_boundaryLifts`,
  `rowCl_scalar_standard_congr`, `rowCl_mCand_homCard_of_uniformPushed`, `rowCl_mCand_scalar`.
* **§4**, the compact-`N` twin: `rowCl_nCand_exactLiftingRN`, `rowCl_nCand_tfg`,
  `rowCl_nCand_exactLifting_iff`, `rowCl_nCand_homCard_of_uniformPushed`, `rowCl_nCand_scalar`.
* **§3**, the row: `rowCl_equiv_of_rowResidual` (row-generic), `rowCl_hdeg_sqrtFive`,
  `rowCl_rowResidual_sqrtFive`, `rowCl_candidate_equiv_galK_sqrtFive`,
  `rowCl_rn_both_carriers_sqrtFive`.
* **§5**, the pilot: `rowCl_pilot_stageVanishing`, `rowCl_pilot_isEmpty_boundaryLifts`.
* **§6**, 24 pins.

### The acceptance statement

`rowCl_candidate_equiv_galK_sqrtFive` is `genAsm_candidate_equiv_galK`'s conclusion at
`ℚ₂(√5)`: the candidate group over the `M0 2 0` word at `q_K` presents `G_{ℚ₂(√5)}`, given four
binders, namely `stokes` and `determinant` at `Γ_R` and `askCStageVanishing` at each of the two
carriers. Compare `canRec_rowResidual_sqrtFive` (whole `CAND` certificate plus two `ASK` blocks)
and `canRec_analytic_sqrtFive` (four analytic clauses plus two `ASK` blocks).

### Axioms: 24 pins

* **std-3 on twenty**: all of the module's §1, §2, §4, §5, plus `rowCl_scalar_standard_congr` and
  `rowCl_hdeg_sqrtFive`. *Measuring* the row's analytic residue costs no campaign axiom at all.
* **`{tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
  absGalQ2_localEulerCharacteristic}`** on `rowCl_equiv_of_rowResidual` (from
  `genAsm_candidate_equiv_galK`) and `rowCl_rn_both_carriers_sqrtFive` (from
  `askC_exactLiftingRN_galK`).
* **that set plus `{hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction,
  relativeStiefelWhitney_dyadic}`** on `rowCl_rowResidual_sqrtFive` and
  `rowCl_candidate_equiv_galK_sqrtFive`. This is **exactly** W83-RECORDS' §5 union set, term for
  term: reducing four of the row's six obligations adds no axiom to the row's record.

## §6 Housekeeping owed, and W85's queue

1. `GQ2/Dyadic/Instances/RowClauses.lean` is **not registered** in `GQ2.lean` (the lane may not
   edit it). It imports `GQ2.Dyadic.Instances.CanonicalRecords`,
   `GQ2.Dyadic.Instances.AskCounting` and `GQ2.Dyadic.Instances.EvenMRamifiedPairing`, and should
   be registered after all three.
2. **`CertificateMain.lean:185`'s status line for `ExactLiftingSemantics` is stale.** It says
   "at the candidate carrier `GammaR n q word`: **genuinely unowned**, and that is AS1 divergence
   4". At the compact `M` and `N` carriers with `2 ≤ α` the corrected bundle is a theorem and the
   frozen one is equivalent to `askCStageVanishing`; the Fox-to-count sentence is about a gap the
   RN route does not have. A housekeeping lane should correct it in place.
3. **W83-RECORDS' reading 2** ("the residue is uniform across the four rows") should be narrowed
   to three, per §2 above.
4. **W83-HOUSE S3's conclusion is confirmed and can be sharpened.** The pilot's residue is indeed
   not the uniform four; §4 above adds that it is strictly worse, so the correction should carry
   the recommendation to route the `√−2` row through `canRec_candN` rather than
   `canRec_candPilot`.

**W85 tickets, in the order the note recommends:**

* **W85-A (sharpest).** Build one frame at a compact candidate carrier: a `MarkedTarget` with
  `1 < #Blk.frattiniK`, a `BoundaryFrameK`, and a nonempty `BoundaryLiftsK`. That refutes the
  row's frozen `exactLifting` clause and `askCStageVanishing` at that carrier, and settles the
  owner call by counterexample rather than by recommendation. `MCompact.datumRho` is a
  handle-uniform surjection onto a nontrivial finite 2-group and is the natural starting point.
* **W85-B.** The four Stokes conjuncts at the compact `M` (and `N`) candidate, mirroring
  `GammaLAnalyticLeaves`. Generic suppliers: `Count.tcocycle_cardN`, `hZcardN`, `hsepN`,
  `hpartialN`, or `KAnalytic.stokesDualityCertificate_of_localDualityG` if the row's duality
  package can be built.
* **W85-C.** The candidate-side determinant, following
  `LSquare.affineDeterminantCertificate_of_wordPhaseSupply` and `WordPhaseResidueK`.
* **W85-D (small).** `MProcyclicExact.exactLiftingRN_unconditional`, which brings the `√10` row
  into §2's treatment and makes the uniformity claim true at all four rows.
