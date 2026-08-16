# W88-SEAM: the trace seam

Lane note for `claude/w88-seam`, based on `ad8c2b62`.  Ticket source:
`docs/dyadic/w87-normal-note.md` §6 items 1 and 2, on top of
`GQ2/Dyadic/Instances/WordPhaseModel.lean` (`wPm`).  One new module,
`GQ2/Dyadic/Instances/WordPhaseSeam.lean` (prefix `wPs`), 34 declarations, **all std-3**.
Nothing outside that module and this note is touched.

**T1 landed at both compact words.  T2 landed at the compact-`N` word, including
`wPmCompactHeadPhase` itself.  T3 does not fire, and §4 below says exactly why.**

The lane also carries **two corrections** to the ticket's own premises, both in §5.

---

## §1 T1: the compact word trace  (module §1, §2, §2b, §3)

W87 §6 item 1 asked for `WordH2 c (nCompactFam α h q e) (ZMod 2) ≃+ ZMod 2`, built the way
`LSquare.lWordH2TraceEquiv` is built, from `heisD1_nCompactFam_tauRow_of_split` and
`NCompact.cardH2_of_uniformPushed`.

It landed, at **both** words and in a stronger form than asked.

* `wPsWordH2TraceEquiv` (module §1) is the `L`-free statement: *any* two-relator word whose
  scalar `d¹` hits the column `(1,1)` has scalar word `H²` of order two, with the coordinate
  sum as the isomorphism.  `LSquare.wordH2Trace_injective_of_pairColumn` was already
  word-generic, and surjectivity is the representative `(z, 0)`, so nothing had to be reproved.
  `LSquare.lWordH2TraceEquiv` is the `L` instance of this; that declaration is untouched.
* `wPs_heisD1_{n,m}CompactFam_tauColumn` (module §2) is the ticket's named route: the
  completely-split hypotheses of `heisD1_{n,m}CompactFam_tauRow_of_split`
  (`Instances/N0M0ScalarStokes.lean:534, 565`) cost nothing at scalar coefficients, because
  every action of any group on `𝔽₂` is trivial (`GQ2.ResidueLift.htriv_zmod2`, already in the
  tree).
* `wPsNCompactWordH2TraceEquiv`, `wPsMCompactWordH2TraceEquiv` (module §3) are the two traces.

**`cardH2_of_uniformPushed` is not needed for the trace itself.**  W87 §6 item 1 lists it as an
input; it is not one.  The trace's surjectivity is the explicit representative `(z, 0)`, exactly
as in the `L` original.  The card-2 count is needed one station later, for the *orientation*
(§2 below), and it is used there.

### The pin the ticket did not expect to lose (module §2b)

The named raw material is stated only at the uniform exponent `omega2Exp (4 · exponent C)` and
only at a `Marking` into a finite group.  Both pins come off, by an argument that never touches
a branch word:

* the resolved **tame** row has traced mod-2 exponent vector equal to the `tau` indicator at
  *every* resolver value, as soon as `q` is even (`wPs_toAdd_heisEps_tameRelW`, degree- and
  word-generic);
* `IsStokesEndpoint` says the two rows sum to zero, so in characteristic two the **wild** row
  equals the tame one (`wPs_toAdd_heisEps_{n,m}CompactFam`), using
  `nCompact_isStokesEndpoint` / `MCompact.mCompact_isStokesEndpoint` as they stand.

Consequences: `wPs_heisEps_{n,m}CompactFam_eq_of_odd` (the compact twin of
`LSquare.lSqFam_heisEps_eq_of_odd`, which the flexible resolver system needs), and
`wPs_heisD1_zmod2_{n,m}CompactFam_apply`: **the whole scalar `d¹` of either compact family is
`x ↦ (x_τ, x_τ)`**, at every odd resolver, every marking, and no finiteness on the target.

---

## §2 T2 at the compact-`N` word  (module §4, §5, §6, §7)

The chain, in the order it was built.  Every step other than the two named in §1 was already
word-generic in the tree; the lane had to supply only the exponent invariance and the trace.

| station | `L` original | this module |
| --- | --- | --- |
| flexible resolver system | `lScalarFlexibleResolverSystem` | `wPsNCompactScalarFlexibleResolverSystem` |
| scalar `H²` word map | `lScalarH2WordFlexible` (+`_mk`, `_injective`) | `wPsNCompactScalarH2WordFlexible` (+`_mk`, `_injective`) |
| surjectivity | `lUniform_scalarH2WordFlexible_surjective_of_actionImage` | `wPsNCompactScalarH2WordFlexible_surjective` |
| orientation `H² ≃+ 𝔽₂` | `lScalarH2TraceEquiv_of_surjective` (+`_mk`) | `wPsNCompactScalarH2TraceEquiv_of_surjective` (+`_mk`) |
| **the trace seam** | `QZero_eq_lUniform_graphHessianTrace` | **`wPs_QZero_eq_nCompact_graphHessianTrace`** |
| tame death at a graph mark | `hessRelZ_tameRelW_lSqHessMark_eq_zero` | `wPs_hessRelZ_tameRelW_hessMark_eq_zero` |
| head-factored phase | `QZero_eq_lSqWallHandlePhase_of_headMark` | `wPs_QZero_eq_compactWallHandlePhase_of_headMark` |
| the residual `Prop` | (`L` has no such wrapper) | **`wPs_wPmCompactHeadPhase_of_headFactorization`** |

The engine `Count.globalModuleH2WordFlexible` (`Count/HTwoModuleFlexible.lean:494`), the
admissibility `Count.isAdmissibleMarkedPresentation_gammaR`, the wild-level condition
`Count.hwildLevel_gammaR` (`Count/Variation.lean:114`), the resolver
`Count.resolvesAt_nCompactFam` (`Count/Presentation.lean:684`),
`Count.kappa0_resolvedAt_uniform`, `moduleObsFun_eq_hessRelZ_of_normalized_pullback`,
`LSquare.semiProdProjHom`, `LSquare.kappa0Cocycle_comap_semiProdProjHom` and `hessRelZ_comap`
were all reused unchanged.  The `H²` count on the continuous side is
`NCompact.cardH2_of_uniformPushed` fed by `NCompact.uniformPushedHsimp`
(`Instances/N0M0CompactBranches.lean:243`), **unconditional at `2 ≤ α`, `Even q`** as W87 §3
said.  No Tate duality, no Euler characteristic, no ramified certificate enters any of it.

So `wPmCompactHeadPhase DD rho` is a theorem, given the head factorization.  W87 §3's
"everything downstream is transposition" is confirmed.

---

## §3 T2 at the compact-`M` word  (module §8)

§4, §5 and §6 transpose to compact `M` **with no new mathematical input**: §2b already covers
both words, and `Count.resolvesAt_mCompactFam` (`Count/Frozen.lean:221`),
`Words.MCompact.isOmega2Only_mCompact` (`Words/M0.lean:390`),
`MCompact.cardH2_of_uniformPushed` (`Instances/N0M0PushedHsimp.lean:721`) and
`MCompact.uniformPushedHsimp` (`Instances/EvenMRamifiedPairing.lean:170`) are the four `M`
twins.  `wPs_QZero_eq_mCompact_graphHessianTrace` is the compact-`M` trace seam.  The `M` word
does not even need `1 ≤ α` for its endpoint condition.

### The exact missing input for a compact-`M` head phase

§7 does **not** transpose, and W87 §4's import question is not the reason.  The obstacle is
mathematical, and it is one named theorem:

> the `M` twin of `WordPhaseModel.wPm_hessRelZ_nCompact_eq_compactWallHandlePhase`, i.e. a
> general-`h`, branch-uniform identification of
> `hessRelZ (Certificates.hessMark s u ·) (kappa0Cocycle dat hdat) E E₂ (mCompactW α h)`
> with `wPhCompactWallHandlePhase q h`.

What exists instead (`Certificates/M0Assembly.lean:577, 589`) is
`MCompact.hessRelZ_mCompact_P1_plusForm` and `MCompact.hessRelZ_mCompact_P0_swapForm`, and
those are three steps short of it:

1. both are stated at **`h = 0`** (their proofs close the handle sum with `Fin.sum_univ_zero`);
2. they are **two branches**, `P = 1` giving `plusFormD q q (c₀, c₁)` and `P = 0` giving
   `q c₁ + b_q(c₀, c₁)`, whereas the compact-`N` endpoint is one value at every `(s, u)`;
3. each carries its own extra hypothesis on top of `hS₂ : (s ^ E omega2) • w = w`: `e % 4 = 1`
   for `P = 1`, a per-letter `omega2`-power condition `hP0` for `P = 0`.

The general-`h` predecessors `hessRelZ_mCompact_P1_res` / `hessRelZ_mCompact_P0`
(`M0Assembly.lean:545, 518`) carry the same two-branch split and the same hypotheses, so
lifting (1) alone does not settle it.  `Certificates.M0Assembly` is importable from this
module (no cycle: it is a `Certificates` file), so the import is **not** the blocker; the
branch uniformity is.

---

## §4 Why T3 does not fire, precisely

T3 asked to discharge `wPhCompactPhaseModel`, hence `wPhBranchFreeSupply` via
`wPh_branchFree_of_phaseModel`, hence the determinant binder at the three `h = 0` rows.

`wPhCompactPhaseModel` (`Instances/WordPhase.lean:911`) quantifies over **every** boundary lift
`rho : BoundaryLiftsK …` at every marked target, minimal block and boundary frame, and demands
a `SourceWordPhaseComparison` with **no marking hypothesis and no branch hypothesis at all**.
The producer that consumes this lane's work,
`WordPhaseModel.wPmCompactPhaseComparison_of_headPhase`, takes six such conditions
(`hcompat`, `hA2`, `hwildTwo`, `htauAct`, `hwildAct`, `hsfpf`), and §7's head phase adds the
head factorization (`base`, `π`, `hpi`, `hf`, `hm`) and `hwildHead`.  Nothing in the block
enrichment supplies them for free.

Supplying them is exactly W87 §6 item 3, and on the odd side it is not a tail: it is
`GammaLDeterminantUnramifiedData.lean` (530 lines) plus `GammaLDeterminantRamifiedData.lean`
(633 lines), **branch-split into unramified and ramified**, each branch supplying the marking
conditions from its own hypothesis.  `wPhCompactPhaseModel` asks for the branch-free version of
that.  That is a wave, not a lane tail, and this lane did not attempt it.

**The honest measure of the remaining distance at the compact-`N` row is therefore: one
compact analogue of the two odd determinant-data files, and nothing else.**  Every analytic
input those files would consume is now in the tree.

---

## §5 Two corrections to the ticket's premises

Both are corrections to W87's note, not to the Lean.

1. **`wPmCompactHeadPhase` is not what the trace seam alone proves.**  W87 §3 records the
   residual as "only the trace seam", and §4 separately lists the head-marking hypotheses as a
   different item.  Those are the same item: `wPmCompactHeadPhase` as literally stated carries
   **no** condition on `rho0`, so it does not follow from the seam.  Its odd twin
   `QZero_eq_lSqWallHandlePhase_of_headMark` carries a head factorization and
   `π (rho0 (x_i)) = 1`, and no argument in the odd route removes them; none does at the
   compact word either.  Module §7 states this in the file, and
   `wPs_wPmCompactHeadPhase_of_headFactorization` produces `wPmCompactHeadPhase` **given**
   those inputs, so the `Prop` itself is discharged at exactly the cost the odd route pays.
2. **`cardH2_of_uniformPushed` is not an input to the word trace** (§1 above).  It is an input
   to the orientation, one station later.

Neither correction changes any landed statement; both change what a reader would expect to
have to build.

---

## §6 What W89 should pick up

1. **The compact branch data.**  §4: the compact analogue of
   `GammaLDeterminantUnramifiedData` + `GammaLDeterminantRamifiedData`, i.e. the step from
   `wPmCompactPhaseComparison_of_headPhase` + `wPs_wPmCompactHeadPhase_of_headFactorization` to
   `wPhCompactPhaseModel` at a branch.  This is the whole of what stands between this lane and
   the determinant binder at the three `h = 0` rows.
2. **The compact-`M` Hessian endpoint.**  §3: the branch-uniform, general-`h` `M` twin of
   `wPm_hessRelZ_nCompact_eq_compactWallHandlePhase`.  With it, module §8 plus a transcription
   of §7 gives the compact-`M` head phase immediately.
3. **Housekeeping this lane may not do** (it may not edit existing modules):
   * `GQ2/Dyadic/Instances/WordPhaseSeam.lean` needs registering in `GQ2.lean`, after
     `GQ2.Dyadic.Instances.WordPhaseModel`.
   * `docs/dyadic/w87-normal-note.md` §3 lists `NCompact.cardH2_of_uniformPushed` as an input
     to the word trace; §1 above supersedes that.  Its §3 also says the residual is "only the
     trace seam"; §5 item 1 above supersedes that.
   * W87's own §6 item 1 is now closed by module §1 to §3, and item 2's stated blocker (the
     `M0Assembly` import) is not the real one; §3 above names the real one.
   * W87's §6 item 4 list (the `WordPhase.lean` §5/§6 and `w86-phase-note.md` §5 corrections,
     and the `WordPhaseModel` registration) is still open, as is W85's
     (`MpcPairings.lean:72`, `SqrtNeg2.lean:893`).

---

## §7 Axioms

34 declarations pinned in the file.

* **34 std-3** (`propext`, `Classical.choice`, `Quot.sound`).  **The honest split has one
  bucket**: no declaration in this module carries a campaign axiom.  In particular the two
  compact word traces, the two orientations, both trace seams and the compact-`N` head phase
  are all axiom-neutral, exactly like their `L` originals.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no recursion options, and no
`set_option` of any kind.  Every declaration elaborates inside the default budget, including
the two trace seams; the odd original `QZero_eq_lUniform_graphHessianTrace` does not raise
heartbeats either, though the head-phase and comparison declarations it feeds
(`QZero_eq_lSqWallHandlePhase_of_headMark`,
`sourceWordPhaseComparison_of_lSqHeadNormalForm`) carry `1600000`.

**Trap check.**  No declaration in the module takes a `TateDualityG`, a `LocalEulerChar` or a
`RamifiedCertificate`.  The Tate-duality route to the same cardinality
(`LSquare.lScalarH2_card_eq_wordH2_of_tateDuality`,
`LSquare.lScalarModuleH2EquivFlexible_of_tateDuality`) was deliberately not used: the word
trace is built from the explicit `tau` column and the count from
`{N,M}Compact.uniformPushedHsimp`, so both sides are duality-free.

**Verification of record.**  `scripts/mirror.sh sweep`, then
`scripts/mirror.sh gen GQ2.Dyadic.Instances.WordPhaseSeam`, then
`scripts/mirror.sh check GQ2/Dyadic/Instances/WordPhaseSeam.lean`.  No `lake` command was run.
