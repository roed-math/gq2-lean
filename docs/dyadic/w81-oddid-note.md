# W81-ODDID lane note

Lane target: the oriented identification at the odd slot, the one remaining structural input
of `genAsm_branch_of_oddSq_canonical` (`GQ2/Dyadic/GeneralAssembly.lean:653`). New module:
`GQ2/Dyadic/Instances/OddIdentification.lean`, prefix `oddId`, 16 declarations, all pinned in
the file with the measured honest split. Base `6f2916f3`; module gen'd green against the
mirror. No new axiom, no sorry, no native_decide; `B` is a binder in every pin.

## The finding that shaped the lane

The briefing's target decomposes, and the tree had already split it:

1. **The oriented equivalence ALONE is free.** `LSquare.nonempty_orientedEquiv_oddDegree`
   (`Instances/GammaLSylowPreimageFieldLabuteCubicNeutral.lean`) produces
   `OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo)` at every odd-degree `K` over a marked
   bundle and nothing else, at census {B1, B6, B7, B11a}. So "produce `e`" was already a
   theorem, and no Demushkin classification input is needed for it (the forward stage route
   replaces it).
2. **What is NOT free is the pair of selected nu-rows AT the equivalence.** The pivot-row
   parity is an invariant of the target (`SqCore/PivotClimb.lean` section 9), and rows do not
   follow from orientation (`GammaLSylowPreimagePivotNu.lean` section 5 refutation). The
   honest seam is P3's existing named Prop `LSquare.SqMarkedForwardSupply B h` = some oriented
   equivalence carrying `nu(f sigma) = 1`, `nu(f x0) = 0`. That Prop IS the briefing's target
   triple `(e, hsigma, hx0)`; the lane adopted it rather than minting a new name.

## What landed (all in `Instances/OddIdentification.lean`)

Section 1, the free half:
- `oddId_orientedEquiv`: the equivalence at explicit `h` (`[K : Q2] = 2h + 1`).

Section 2, the seam and its wave-80 collapse:
- `oddId_certificate_of_supply`, `oddId_supply_iff_certificate`: the seam is EXACTLY the
  L-row marked-core certificate, both directions, with the pre-W80 handle-stratum side binder
  deleted (`gOdd_pivotFix` pays it at every `h`). std-3.
- `oddId_orientedEquiv_withRows_of_supply`: the seam repackaged as the consumer's literal
  triple. std-3.
- `oddId_markedSupply_of_presentation`: producer at every odd degree from the stage lane's
  frame residual `MarkedFrame.SqCupAdaptedFramePresentation K`. Every `h >= 1` producer in
  the tree consumes frame data of this kind; the docstring inventories them.
- `oddId_markedSupply_degreeOne`: at `[K : Q2] = 1` the seam is a THEOREM
  (`sqNuOrientedClear_zero` through the oriented bridge).

Section 3, the consumer corollary (T3):
- `oddId_genAsmBranch_L_of_supply`: seam implies `exists G : GenAsmBranch K B, G.pres = .L h`.
  std-3: the join itself is axiom-free.
- `oddId_genAsmBranch_L_of_presentation`: the same over the frame residual.
- `oddId_genAsmBranch_L_degreeOne`: the n = 1 branch datum as a THEOREM (acceptance floor).
  Census {B1, B3c, B6, B7, B8, B11a}, a strict subset of the frozen degree-one milestone's
  seven (no B9, no B5, no B5-K).
- `oddId_candidate_equiv_galK_of_supply`: the full chain: over the seam, what the general
  theorem still needs at odd degree is exactly `GenAsmFieldInputs` (structural) plus
  `GenAsmRowResidual` (exactLifting, stokes, determinant, cand). Census {B1, B6, B7}.

Section 4, the invariants (T1):
- `oddId_chiCycKTwo_surjective` / `oddId_range_chiCycKTwo`: FULL cyclotomic image at odd
  degree (no odd analogue of the even range dichotomy). Theorems at {B1, B6, B7, B11a}.
- `oddId_demushkinRank`: `demushkinRank 2 (G_K(2)) = [K : Q2] + 2`, by `H1congrGroup`
  transport into `dsq_demushkinRank`. Same census.
- `oddId_demushkinQ_congr` (std-3, generic): `demushkinQ` transports along any continuous
  equivalence; `oddId_demushkinQ_eq_model`: `demushkinQ (G_K(2)) = demushkinQ (D_sq h)`.
- `oddId_torsionPremise_iff_model`: THE RELOCATION. `MaxProTwoAbTorsionGeneratedByFieldRoots B`
  (DemushkinQRamifiedI's per-field local-CFT torsion premise) is equivalent, at every
  odd-degree `K` at handle count `h`, to the single field-free statement
  `demushkinQ (D_sq h) = 2`, which `SqCore/DsqDemushkin.lean` records as absent from the tree.

## Where the seam sits now

One Prop at `h >= 1`: `SqMarkedForwardSupply B h`, equivalently (exactly) the L-row
certificate, equivalently the branch datum's classification input. Its only non-circular
producers consume frame data; the cheapest is the halved relator clause
`SqCupAdaptedFrameRelator K` (`GammaLSqCupAdaptedFrameGeneration.lean`, generation clause is
already a theorem, level-three shadow already a theorem, gap entirely above level three).

## What W82 needs

1. **The seam at `h >= 1`**: discharge `SqCupAdaptedFrameRelator K` (the improved relator
   vanishes on cup-adapted Frattini frames above level three), OR produce a row-marked
   presenting frame directly (`sqMarkedForwardSupply_of_presentingFrame` shape). Note the
   wave-80 dividend applies on the model side only; the two rows are arithmetic and the
   pivot-parity obstruction says no model-side statement can supply them.
2. **`demushkinQ (D_sq h) = 2`**: one abelianization-frame computation on `D_sq h`
   (pattern: `demushkinQ_DR` at rank 3, `NFrameModel4` at alpha = 1). Discharges the
   arithmetic torsion premise at every odd-degree field at once via
   `oddId_torsionPremise_iff_model`, and completes the odd invariant triple.
3. **Beyond the branch**: the general theorem's `GenAsmRowResidual` at the L row (ASK
   exactLifting + stokes wiring, the determinant wiring flagged by W79-HOUSE as existing but
   unwired, and the CAND `WordCertificate` over `D_sq h`, which has no producer at free `h`).
