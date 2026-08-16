# W87-NORMAL: the compact phase normal form

Lane note for `claude/w87-normal`, based on `1541635f`.  Ticket source:
`docs/dyadic/w86-phase-note.md` §7 items 1 and 2, on top of
`GQ2/Dyadic/Instances/WordPhase.lean` (`wPh`).  One new module,
`GQ2/Dyadic/Instances/WordPhaseModel.lean` (prefix `wPm`), 17 declarations, 15 of them std-3.
Nothing outside that module and this note is touched.

Both tickets landed.  T2 landed with a **correction to the ticket's own premise**: the three
compact ingredients W86-PHASE §5 recorded as absent from the tree are all present, under
different names, and the fourth is reusable after all.

---

## §1 T1: the `ℚ₂(√2)` row  (module §1)

`M0 3 0`.  Every clause `RowClauses`, `RecordBlocks` and `WordPhase` prove is stated at general
`(α, h, q)`, so the row is a transcription at `α = 3`, `h = 0`.  It went through on the first
pass with no new lemma.

Landed: `wPm_hdeg_sqrtTwo`, `wPm_rowResidual_sqrtTwo`,
`wPm_candidate_equiv_galK_sqrtTwo_branchFree`.

The row's binder list is now `wPhBranchFreeSupply (2 * 0 + 2) …` plus `askCStageVanishing` at
each of the two carriers, and the supply binder is **literally the one the `√5` and `√−2` rows
take**: all three compact rows sit at `h = 0`, hence at degree `2`, hence at one statement.

**Axiom-neutrality, checked directly against the Lean and not against any note.**
`canRec_rowResidual_sqrtTwo` (`Instances/CanonicalRecords.lean:576`), the row's prior statement,
pins std-3 plus
`{hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction,
relativeStiefelWhitney_dyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
absGalQ2_localEulerCharacteristic}`.  Both new row statements pin **that set, term for term**.
So discharging the row's `stokes` and `scalar` clauses and reducing its `determinant` clause to
the branch-free supply adds no axiom to the row's record.  (The `√2` row costs six campaign
axioms, like `√5`; the `√−2` pilot costs five.  That five-versus-six is `CanonicalRecords`' own
recorded gap, not a finding of this lane.)

---

## §2 T2: the per-ingredient table, corrected  (module §2, §3)

W86-PHASE §5 gives this table and reports "none" three times:

| `L` ingredient | W86-PHASE §5's compact counterpart |
| --- | --- |
| `lSqPhaseNormal h` (normal cochain coordinates) | **none** |
| `heisD1_lSqPhaseNormal_eq_zero_unramified` (`d¹`-closed) | **none** |
| `lSqFam_unramified_phaseNormalForm` (unique mod `d⁰`) | **none** |
| `sourceWordPhaseComparison_of_lSqHeadNormalForm` (assembler) | stated at `lSqW`/`lSqFam`, not reusable |

The evidence given for the three "none"s is that "`grep` for `phaseNormalForm` and
`PhaseNormal` across `GQ2/` returns `lSq` hits only".  **That grep measured the naming.**  The
compact objects are named `even…`, not `…PhaseNormal…`, and all three exist:

| `L` ingredient | compact counterpart, with location |
| --- | --- |
| `lSqPhaseNormal h` | `evenNormal h` (`Instances/N0RamifiedStokes.lean:73`) |
| `heisD1_lSqPhaseNormal_eq_zero_unramified` | `heisD1_evenNormal_eq_zero_of_unramified_row` (`Instances/N0M0UnramifiedStokes.lean:318`) |
| `lSqFam_unramified_phaseNormalForm` | `evenNormalForm_of_unramified_row` (`Instances/N0M0UnramifiedStokes.lean:331`) |
| `sourceWordPhaseComparison_of_lSqHeadNormalForm` | `wPmPhaseComparison_of_normalForm` (this module, §2) |

Two things are worth saying about the first three.

* `evenNormal h d₀ d₁ z` is exactly the object W86-PHASE §5 predicted would have to be built:
  `σ`, `τ` and `x₂` vanish, `x₀` and `x₁` are free, and the handles carry `z`, i.e. "the compact
  word's `d¹`-closed cochains are, modulo `d⁰`, two free head coordinates and `h` handle pairs".
  It is proved at general `h`, and its two theorems are stated for an arbitrary relator family
  with the shared unramified Fox row, so **they serve both compact words at once**
  (`heisD1_nCompactFam_unramified_apply`, `heisD1_mCompactFam_unramified_apply`, same file).
* The one genuine mismatch was bracketing: the Stokes files carry handles as `Fin h × Fin 2 → A`
  and W86-PHASE §4's endpoint form wants `Fin h → A × A`.  `wPmCompactCoordsEquiv` and
  `wPmCompactPhaseNormal` are that rebracketing, the even twin of `lSqPhaseCoordsEquiv` /
  `lSqPhaseNormal`, with two head coordinates in place of one.  Landed with the five readback
  lemmas, `wPm_heisD1_compactPhaseNormal_eq_zero` and `wPm_compactPhaseNormalForm`.

### The assembler transposes

W86-PHASE §6 is right that `sourceWordPhaseComparison_of_lSqHeadNormalForm` is stated at
`LSquare.gamma h q`, `lSqW h` and `lSqFam h q e`, so it cannot be instantiated at a compact
word.  That is a fact about the declaration, not about its proof.  Reading the proof, the word
enters in exactly two places:

* the **plumbing** is already word-generic: `sourceQuotientH1Equiv` (arbitrary `Gamma`),
  `Count.h1Equiv_gammaR_range` and `h1Equiv_gammaR_range_H1mk` (arbitrary `n`, `q`, word `R`,
  relator family `w`), `Count.toZ1w_surjective`, `isAdmissibleMarkedPresentation_gammaR`, and
  `stokesNormalEquiv`;
* the **mathematics** is word-specific: `QZero_eq_lSqWallHandlePhase_of_headMark`, which says
  what the source phase of a cocycle *in normal coordinates* is.

`wPmPhaseComparison_of_normalForm` is that construction restated at an arbitrary `n`, `q`, word
`Rw` and family `w`, with the normal coordinates and the phase formula as parameters:

```
hphase : ∀ (p : W) (c : VCocycle DD rho),
  (fun i ↦ c.c (gammaGen n q Rw i)) = normal p → QZero DD rho c = Q p
```

is its only analytic hypothesis.  It is std-3 and it is not a re-export: the L declaration is
untouched.

---

## §3 The residual after this lane  (module §4)

`wPmCompactPhaseComparison_of_headPhase` is the compact-`N` twin of
`LSquare.sourceWordPhaseComparison_of_lSqUnramifiedHead`.  Every hypothesis it carries beyond
the odd producer's own is discharged from the tree:

| input | at the odd row | at the compact-`N` row |
| --- | --- | --- |
| resolver | `lUniform_wordLift_resolver` | `Count.resolvesAt_nCompactFam` at `omega2Exp (4 · exponent DD.C0)` |
| Fox row | inside `heisD1_lSqPhaseNormal_eq_zero_unramified` | `heisD1_nCompactFam_unramified_apply` |
| relator death | `lower_rel` | same, word-generic |
| normal coordinates | `lSqPhaseNormal` | `wPmCompactPhaseNormal` (§2) |
| `d¹`-closed | `heisD1_lSqPhaseNormal_eq_zero_unramified` | `wPm_heisD1_compactPhaseNormal_eq_zero` |
| unique mod `d⁰` | `lSqFam_unramified_phaseNormalForm` | `wPm_compactPhaseNormalForm` |
| assembler | `sourceWordPhaseComparison_of_lSqHeadNormalForm` | `wPmPhaseComparison_of_normalForm` |
| **phase identity** | `QZero_eq_lSqWallHandlePhase_of_headMark` | **`wPmCompactHeadPhase`, open** |

So the residual is one named `Prop`, and it is strictly smaller than `wPhCompactPhaseModel`:
that asked for a `SourceWordPhaseComparison` per boundary lift; this asks only for the value of
`QZero` on cocycles already known to sit in normal coordinates.

Note what does **not** appear in the compact producer and does appear in both odd twins: no Arf
hypothesis, no Wall operator built from the `sigma`-image, no branch split.  That is W86-PHASE
§4's correction showing up in the shape of the residual rather than in its prose.

### The phase *value* is not the gap

`wPm_hessRelZ_nCompact_eq_compactWallHandlePhase` closes the half of `wPmCompactHeadPhase` that
looked like the hard half.  `Certificates.hessRelZ_nCompact` (`Certificates/N0.lean:873`)
evaluates the frozen compact-`N` word at the graph-type marking to

```
q(x₀) + b_q(x₀, x₁) + Σ_j b_q(u_j, v_j),
```

at general `(α, h)` and for every resolver, and `plusFormD q q (a, b) = q a + b_q(a, b)`, so at
§2's normal coordinates that value **is** `wPhCompactWallHandlePhase q̄ h` on the nose.  The
theorem is std-3 and the whole content was already in the tree.

What is left in `wPmCompactHeadPhase` is therefore only the **trace seam**: the compact twin of
`LSquare.QZero_eq_lUniform_graphHessianTrace` (`Instances/GammaLGraphHessian.lean:244`), which
says `QZero DD rho c = hessRelZ(tameRelW) + hessRelZ(word)` at the graph marking, plus the
tame-relator death and the mark identification that the odd head producer does with
`kappa0Cocycle_comap_semiProdProjHom` (word-generic) and `hessRelZ_comap` (word-generic).

### What the trace seam needs, exactly

Its proof consumes three word-specific inputs.  Checked across the whole tree:

1. `lUniform_wordLift_resolver` -- **present** for both compact words.  The uniform-level
   theorems `Count.resolvesAt_{n,m}CompactFam_uniformHeis`
   (`Instances/N0M0UniformHeisenbergResolver.lean:38, 91`) land in `HeisLift A C`, which is
   strictly stronger; the `WordLift` form is one `ResolvesAt.pullback` along
   `Count.heisPrim` away, an idiom already used inline in about ten places.  The module's §4
   takes the direct route through `Count.resolvesAt_nCompactFam`.
2. `isOmega2Only_lSq` -- **present**: `Words.isOmega2Only_nCompact` (`Words/N0.lean:233`) and
   `Words.MCompact.isOmega2Only_mCompact` (`Words/M0.lean:390`).  `kappa0_resolvedAt_uniform`
   (`GammaLGraphHessian.lean:207`) already takes any `IsOmega2Only` word, so this feeds
   straight in.
3. `lUniform_scalarH2WordFlexible_surjective_of_actionImage`
   (`Instances/GammaLScalarH2Surjectivity.lean:84`) -- **absent**, and this is the whole gap.
   It supplies the additive orientation `H2 Γ (ZMod 2) ≃+ ZMod 2` that turns `iotaB` into the
   word trace.  Its two factors split as:
   * `lScalarModuleH2EquivFlexible_of_surjective`, whose engine
     `Count.globalModuleH2WordFlexible` (`Count/HTwoModuleFlexible.lean:494`) **is** fully
     word-generic;
   * `lWordH2TraceEquiv` (`Instances/LScalarTrace.lean:253`), which is **not**: its bijectivity
     runs through `lScalarTauBasis` and `lSq_heisD1_tauColumn`, the `(1,1)` `tau`-column fact for
     the `L` family, and no other word in the tree has ever been given a scalar word trace
     (`wordH2Trace`, `wordH2Trace_injective_of_pairColumn` and `lScalarTauBasis` occur in
     `LScalarTrace.lean` only).

   The compact raw material for a `lWordH2TraceEquiv` twin exists and is unwired:
   `heisD1_nCompactFam_tauRow_of_split` and `heisD1_mCompactFam_tauRow_of_split`
   (`Instances/N0M0ScalarStokes.lean:534, 565`) are the compact `tau`-column facts, and the
   card-2 input is `NCompact.cardH2_of_uniformPushed` / `MCompact.cardH2_of_uniformPushed`
   (`Instances/N0M0PushedHsimp.lean:210, 721`), whose hypotheses are already discharged
   unconditionally at `2 ≤ α`, `Even q` by `NCompact.uniformPushedHsimp` /
   `MCompact.uniformPushedHsimp`.

So the honest measure of the remaining analytic distance is: **one scalar word-trace equivalence
at the compact family.**  That is a smaller and much more concrete object than "a
`SourceWordPhaseComparison` per boundary lift", and it is the same object for both compact words.

⚠ **[W88-SEAM, as of the wave-88 merge: the equivalence LANDED at both words**
(`wPs{N,M}CompactWordH2TraceEquiv`, all std-3), by a stronger route than mapped here (the whole
scalar `d¹` of either compact family is `x ↦ (x_τ, x_τ)`), and `wPmCompactHeadPhase` is
DISCHARGED at the `N` word (`wPs_wPmCompactHeadPhase_of_headFactorization`).  Two of this
section's readings corrected: `cardH2_of_uniformPushed` feeds the ORIENTATION, not the trace
(surjectivity is the explicit `(z,0)` representative), and the head phase does not follow from
the seam alone (it costs the head factorization plus `π(rho0(xᵢ)) = 1`, exactly the odd twin's
hypotheses, supplied by the producer).  This paragraph's "smaller than a
`SourceWordPhaseComparison` per boundary lift" remains true but is no longer the endgame
measure: with the seam landed, the remaining distance to `wPhCompactPhaseModel` is exactly the
compact twin of the odd side's TWO BRANCH-SPLIT DATA FILES
(`GammaLDeterminant{Unramified,Ramified}Data.lean`, 530 + 633 lines), a wave-sized
construction whose every analytic input is now in the tree; the compact-`M` head phase
additionally needs the `M` twin of the Hessian evaluation (blocked by the `h = 0`-only
branch-split endpoints, not by the `M0Assembly` import).  See `docs/dyadic/w88-seam-note.md`.]

---

## §4 Scope limits, stated plainly

* `wPmCompactHeadPhase` and `wPmCompactPhaseComparison_of_headPhase` are stated at the
  **compact-`N`** word only.  The compact-`M` twin needs `hessRelZ_mCompact_P1_plusForm` /
  `hessRelZ_mCompact_P0_swapForm` (`Certificates/M0Assembly.lean:577, 589`), and
  `Certificates.M0Assembly` is **not** in `GQ2.Dyadic.Instances.WordPhase`'s import closure
  (it is in `GQ2.lean` at line 282).  A compact-`M` twin therefore needs either a new import
  edge or a different home module.  This lane did not add one.
* `wPhCompactPhaseModel` itself is **not** discharged.  It quantifies over every boundary lift
  with no marking hypotheses; §4's producer, like its odd twin, takes the three head-marking
  conditions (`htauAct`, `hwildAct`, `hsfpf`).  Supplying those from a branch hypothesis is the
  step `GammaLDeterminantUnramifiedData` performs on the odd side and this lane did not.
* Nothing here touches the `Mpc` row, and nothing here touches the coefficient `Prop`.

---

## §5 Axioms

17 declarations pinned in the file.

* **15 std-3** (`propext`, `Classical.choice`, `Quot.sound`): all of §2, §3 and §4, that is the
  word-generic assembler, the compact normal coordinates and their two theorems, the compact
  comparison producer, and the endpoint-value identification.  **The entire T2 layer is std-3.**
* **2 with campaign axioms**, both `√2` row statements (`wPm_rowResidual_sqrtTwo`,
  `wPm_candidate_equiv_galK_sqrtTwo_branchFree`), carrying std-3 plus the six-axiom set already
  on `canRec_rowResidual_sqrtTwo`.  §1 records the direct check.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no recursion options, and no
`set_option` of any kind.  The odd-degree originals this module's §2 transposes do raise
heartbeats (`sourceWordPhaseComparison_of_lSqHeadNormalForm` carries `1600000`,
`sourceWordPhaseComparison_of_lSqUnramifiedHead` carries `1600000`); the word-generic transposition
elaborates inside the default budget, and so does everything else here.

**Trap check.**  No declaration in the module takes a `TateDualityG`, a `LocalEulerChar` or a
`RamifiedCertificate`; the duality-carrying determinant clone `affineDeterminant_galK` is not
reused, and the determinant route is `WordPhase`'s, which takes no duality input.  The signed
endpoint `Certificates.nCompact_handle_form_gaussSum` is consulted through `WordPhase` §4 rather
than any unsigned magnitude.

---

## §6 What W88 should pick up

1. **The scalar word trace at the compact family.**  §3 says exactly what it is: a
   `WordH2 c (nCompactFam α h q e) (ZMod 2) ≃+ ZMod 2`, built the way `lWordH2TraceEquiv` is
   built, from `heisD1_nCompactFam_tauRow_of_split` and `NCompact.cardH2_of_uniformPushed`.
   Everything downstream of it -- the scalar orientation, the graph-Hessian trace, and hence
   `wPmCompactHeadPhase` -- is transposition, and the phase value at the end is already proved
   (`wPm_hessRelZ_nCompact_eq_compactWallHandlePhase`).
2. **The compact-`M` twin** of §4, once the import question in §4 is settled.
3. **The head-marking hypotheses**, i.e. the step from §4's producer to `wPhCompactPhaseModel`
   at a branch, mirroring `GammaLDeterminantUnramifiedData`.
4. **Housekeeping this lane could not do** (it may not edit existing modules):
   * `GQ2/Dyadic/Instances/WordPhase.lean` §5 and §6, and `docs/dyadic/w86-phase-note.md` §5,
     state that the three normal-form ingredients have no compact counterpart.  §2 above
     supersedes that; the grep they rest on searched for the `L` naming.
   * `WordPhase.lean` §6's "None of the three has a compact-word counterpart anywhere in the
     tree" and its parenthetical about `phaseNormalForm`/`PhaseNormal` need the same correction.
   * `GQ2/Dyadic/Instances/WordPhaseModel.lean` needs registering in `GQ2.lean`, after
     `GQ2.Dyadic.Instances.WordPhase`.
   * W86-PHASE's own §7 item 2 (the `√2` acceptance statement) is now closed by §1 and can point
     at `wPm_candidate_equiv_galK_sqrtTwo_branchFree`.
   * W85's housekeeping list (`MpcPairings.lean:72`, `SqrtNeg2.lean:893`) is still open.
