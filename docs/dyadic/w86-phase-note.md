# W86-PHASE: the word-phase supply at the compact rows

Lane note for `claude/w86-phase`, based on `f0de6ad5`.  Ticket source:
`docs/dyadic/w85-blocks-note.md` §7 items 1 and 2.  One new module,
`GQ2/Dyadic/Instances/WordPhase.lean` (prefix `wPh`), 26 declarations, 22 of them std-3.
Nothing outside that module and this note is touched.

Both tickets landed, and T2 landed with a **correction to its own statement**: the even-degree
supply is one computation, not two.

---

## §1 The per-row table, read off the Lean

| clause | `M0 2 0` (`√5`) | `M0 3 0` (`√2`) | `N0 2 0` (`√−2`) | `Mpc 2 1 false 1 0` (`√10`) |
| --- | --- | --- | --- | --- |
| `exactLifting` at `Γ_R` | `askCStageVanishing` | same | same | same (W85 §2) |
| `scalar` at `Γ_R` | theorem | theorem | theorem | theorem |
| `stokes` at `Γ_R` | theorem (W85 §3) | theorem (W85 §3) | **theorem, `wPh_nCand_stokes`** | open |
| `determinant` at `Γ_R` | `wPhBranchFreeSupply` | same | **`wPhBranchFreeSupply`** | open |
| `ASK` `exactLifting` at `G_K` | `askCStageVanishing` | same | same | same |
| `ASK` `stokes` at `G_K` | theorem | theorem | theorem | theorem |
| acceptance statement | `wPh_candidate_equiv_galK_sqrtFive_branchFree` | not instantiated | **`wPh_candidate_equiv_galK_sqrtNegTwo_branchFree`** | not instantiated |

Three of the four rows now sit on the same two-item residual: **one word-phase supply, shared
across rows, and two instances of one coefficient `Prop`.**  The fourth row is unchanged; this
lane did not work it.

The `M0 3 0` (`√2`) row inherits every clause because W85-BLOCKS' §3 and §5 are stated at general
`(α, h, q)`, but its acceptance statement was never instantiated and this lane did not do it
either.  It is a transcription of the module's §7 with `canRec_rowResidual_sqrtTwo`, and is the
cheapest thing left on the board.

---

## §2 T1: the `N` twins  (module §1, §2, §3)

W85-BLOCKS said the `N0` twin is "mechanical, all three inputs exist".  Both halves of that are
right, and one binder is not.

* `Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis` exists
  (`Instances/N0M0UniformHeisenbergResolver.lean:51`), but **it takes `1 ≤ α` and the `M` twin
  does not**.  So the four `N` conjuncts carry `1 ≤ α` where their `M` twins carry it only on
  `hpartial`.  It is free at `2 ≤ α`, which is where the rows sit, and `wPh_nCand_stokes` is
  unconditional there.
* `NCompact.uniformPushedHsimp` (`N0M0CompactBranches.lean:243`) is unconditional at `2 ≤ α`,
  `Even q`, exactly like the `M` one.
* `NCompact.degree` and `NCompact.cardH2_of_uniformPushed` are the identical statements.
  `NCompact.datumRho_surjective` needs strictly **less** than its `M` twin: no `1 ≤ α`.

Landed: `wPh_nCand_tcocycle`, `wPh_nCand_hsep`, `wPh_nCand_hrsep`, `wPh_nCand_hpartial`,
`wPh_nCand_hZcard`, packed as `wPh_nCand_stokes_of_uniformPushed` and then `wPh_nCand_stokes`;
`wPhWordPhaseSupplyN` and `wPh_nCand_determinant_of_wordPhaseSupply`.  No raised heartbeats on
any of them, as on the `M` side.

**The `√−2` row was not in the tree in reduced form.**  `RowClauses` §4 states the `N` clause
lemmas and asserts the `N0 2 0` row "gets the identical treatment", but never instantiates it;
`CanonicalRecords.canRec_rowResidual_sqrtNegTwo` carries the whole `CAND` certificate as one
binder.  `wPh_rowResidual_sqrtNegTwo` and `wPh_candidate_equiv_galK_sqrtNegTwo` are the
instantiation.

**Trap check.**  No declaration in the module takes a `TateDualityG`, a `LocalEulerChar` or a
`RamifiedCertificate`; the determinant route is `LSquare.gaussZResidueK_of_wordPhase`, which
takes no duality input.  The duality-carrying clone `affineDeterminant_galK` is not reused.

---

## §3 T2: the even-degree wall-handle phase  (module §4)

W85-BLOCKS §5's diagnosis was that the `L` producers run through
`lSqWallHandlePhase_gaussSum_standard{Unram,Ram}`, "which exist only at odd degree `2h + 1`",
that the compact word "offers only the unsigned magnitude", and that "there are no even-degree
sign pins".  The first is right.  The other two are not, and the reason matters.

### The correction: one value, not two

`standardNumerics n` has `gaussUnram m = (-1)^n · 2^(n·m)` and `gaussRam m = 2^(n·m)`.  At even
`n` these are the same integer.  Landed as `wPh_gaussUnram_eq_gaussRam_of_even`, with the sign
collapse `wPh_neg_one_pow_even` that W85-BLOCKS §5 named as absent from the tree
(`Even.neg_one_pow`, "never used anywhere under `GQ2/`").

So W85-BLOCKS §5's "two even-degree wall-handle phase computations" is **one computation consumed
twice**, and the branch hypotheses `hunram`/`hram` of `recBlWordPhaseSupply` carry no information
about the target.

This is not a numerical coincidence.  The odd endpoint's head is a Wall doubling `qDouble q U`,
and the unramified branch has to prove `arf q = 1` for it (`arf_eq_one_of_zeroCount_sub`) to get
the minus sign.  The even endpoint's head is `plusFormD qbar qbar`, whose second slot is a full
polar character sum, so it is split and its Arf invariant is `0` on **both** branches.  There is
no even-degree analogue of the Arf lemma, and none is needed.

### The pin that did exist

`Certificates.nCompact_handle_form_gaussSum` (`Certificates/N0.lean:1067`) is a **signed**
`h`-handle endpoint value, `2^(d·(h+1))`, and its proof is pure form theory (`gaussSum_plusFormD`
plus `gaussSum_pi_sum`); it takes no word and no handle datum, so it serves both compact rows.
W85-BLOCKS §5 consulted `mCompact_gauss_pow` (the unsigned magnitude) and did not see it.  At
`Fintype.card V = 2^(2·m)` it lands exactly on `(standardNumerics (2h+2)).gaussRam m`.

Landed on top of it: `wPhCompactWallHandlePhase` (the even endpoint form, a `plusFormD` head on
two coordinates plus `h` hyperbolic planes, against the odd form's Wall head on one) and both
`SourceNumerics` spellings of its value, `wPh_compactWallHandlePhase_gaussSum_standardRam` and
`…Unram`.  Neither takes an Arf hypothesis or a Wall operator; both odd twins take both.

---

## §4 T2: the reduction  (module §5, §6, §7)

`wPhBranchFreeSupply n nuP tame pro2 compat` is `recBlWordPhaseSupply`'s clause with the branch
hypothesis deleted and the `gaussRam` target, stated at an **arbitrary** `Gam : ProfiniteGrp` and
an arbitrary degree.  W85-BLOCKS §5 is right that `DeterminantWordPhaseSupply` cannot be
instantiated at a compact word because the word is in the types of its fields; the fix is to make
`tame` and `pro2` parameters, which is what this definition does.  Then:

* `wPh_recBlWordPhaseSupply_of_branchFree` and `wPh_wordPhaseSupplyN_of_branchFree`: **both**
  compact rows' supplies follow from the one statement;
* `wPh_candidate_equiv_galK_sqrtFive_branchFree` and
  `wPh_candidate_equiv_galK_sqrtNegTwo_branchFree`: the two acceptance statements now take
  literally the same determinant binder.

| | odd (`L`) row | even compact rows, before | after |
| --- | --- | --- | --- |
| clauses to supply | 2, different targets | 2, assumed different | **1** |
| branch hypothesis used | yes (`hunram` gives `arf = 1`) | assumed yes | **no** |
| endpoint value | `lSqWallHandlePhase_gaussSum_standard*` | absent | `wPh_compactWallHandlePhase_gaussSum_standard*` |
| endpoint form | Wall head + `h` planes | absent | `wPhCompactWallHandlePhase` |
| phase comparison | `sourceWordPhaseComparison_of_lSqUnramifiedHead` | absent | **still absent** |

---

## §5 The named gap, and why it is the last one

`wPhCompactPhaseModel` is the whole residual: per boundary lift, a `SourceWordPhaseComparison`
against §3's endpoint form.  `wPh_branchFree_of_phaseModel` discharges everything else: the model
type, the form, and the Gauss value, whose two hypotheses are the `DescData` fields `hquad` and
`hns` and whose third is the supply's own `hcard`.

What building it needs, checked against the tree:

| `L` ingredient | compact counterpart |
| --- | --- |
| `lSqPhaseNormal h` (normal cochain coordinates) | **none** |
| `heisD1_lSqPhaseNormal_eq_zero_unramified` (`d¹`-closed) | **none** |
| `lSqFam_unramified_phaseNormalForm` (unique mod `d⁰`) | **none** |
| `sourceWordPhaseComparison_of_lSqHeadNormalForm` (assembler) | stated at `lSqW`/`lSqFam`, not reusable |

`grep` for `phaseNormalForm` and `PhaseNormal` across `GQ2/` returns `lSq` hits only.  So the gap
is one named object: **the compact word's `d¹`-closed cochains are, modulo `d⁰`, two free head
coordinates and `h` handle pairs.**  §3's correction makes that object simpler than its odd
counterpart, not harder: no Wall operator built from the `sigma`-image, and no branch split.

⚠ **[W87-NORMAL, as of the wave-87 merge: the three "none" rows are FALSE; the grep measured
the naming.**  The counterparts exist as `evenNormal` (`N0RamifiedStokes.lean:73`),
`heisD1_evenNormal_eq_zero_of_unramified_row` and `evenNormalForm_of_unramified_row`
(`N0M0UnramifiedStokes.lean:318`, `:331`), stated for any family with the shared unramified Fox
row, hence serving both compact words; the predicted object in bold above is exactly
`evenNormal`, already proved at general `h`.  The assembler row is true of the declaration only;
its proof is word-generic and `wPmPhaseComparison_of_normalForm` (`WordPhaseModel.lean`)
restates it with the phase formula as the single analytic hypothesis.  The residual after
W87-NORMAL is the trace seam alone [W88-SEAM: landed at both words, and the head phase
discharged at `N`; the remaining distance is the compact twin of the two branch-split
determinant-data files, see the w87-normal note's W88 annotation]: one compact twin of
`lWordH2TraceEquiv`
(`LScalarTrace.lean:253`), the same object for both compact words.  See
`docs/dyadic/w87-normal-note.md`.]

---

## §6 Axioms

26 declarations pinned in the file.

* **22 std-3**; `wPh_even_two_mul_add_two` pins `propext` alone.  The entire even-degree phase
  layer and the entire reduction are std-3.
* **4 with campaign axioms**, all row statements.  The three `√−2` ones carry
  `{tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
  absGalQ2_localEulerCharacteristic, hilbertSymbol_normCriterion_finiteDyadic,
  relativeStiefelWhitney_dyadic}`; `wPh_candidate_equiv_galK_sqrtFive_branchFree` carries that
  set plus `peripheralCyclotomicAction`, term for term the set already on
  `RecordBlocks.recBl_candidate_equiv_galK_sqrtFive` (checked directly against the Lean, not
  taken from the note).  **Restating the determinant binder over `wPhBranchFreeSupply` is
  axiom-neutral.**

The five-versus-six between the two rows is **not** new: `CanonicalRecords.lean`'s pin prose
already records that `canRec_branch_sqrtNegTwo` carries the four-axiom even-route endpoint set
and that the other three branch data carry that set plus `peripheralCyclotomicAction`.  What this
lane adds is that the gap survives to the row conclusion.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no recursion options.  The only
option set is `linter.unusedVariables`, on the three supply/model definitions, for the reason
`LSquare`'s own structure sets it.

---

## §7 What W87 should pick up

1. **The compact phase normal form**, i.e. `wPhCompactPhaseModel`.  §5 says exactly what it is
   and what has to be built.  This is now the single largest analytic item on three of the four
   rows, and after §3 it is a branch-free statement.
2. **The `√2` row's acceptance statement**, `M0 3 0`.  Every clause is already general in
   `(α, h, q)`; the instantiation is the module's §7 with `canRec_rowResidual_sqrtTwo`.  Cheap.
3. **The `Mpc` row's `stokes` and `determinant`.**  Untouched by this lane and by W85.
4. **Housekeeping this lane could not do** (it may not edit existing modules):
   * `RecordBlocks.lean` §4's "the even-degree sign pins do not exist" and "two even-degree
     wall-handle phase computations" are both superseded by this lane's §4; and its claim that
     the compact word "offers only the unsigned magnitude" overlooked
     `Certificates.nCompact_handle_form_gaussSum`.
   * W85-BLOCKS' own §5 and §7 item 2 need the same correction.
   * `RowClauses.lean` §4's "`N0 2 0` gets the identical treatment" is now instantiated and can
     point at `wPh_candidate_equiv_galK_sqrtNegTwo`.
   * `GQ2/Dyadic/Instances/WordPhase.lean` needs registering in `GQ2.lean`, after
     `GQ2.Dyadic.Instances.RecordBlocks` and `…N0M0CompactBranches`.
   * W85's own housekeeping list (`MpcPairings.lean:72`, `SqrtNeg2.lean:893`) is still open.
