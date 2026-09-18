# W362-PUB lane note: the general L/N certificate presentation

**Status: staged proposal only. Nothing in this lane is owner adoption, acceptance,
census amendment, appendix migration, or release authorization.** Staged artifacts are
proposals. No frozen identifier or hash is changed, no historical verification report is
relabelled as current, and no universal frozen-M placement claim is made or revived.

Worktree `cla/worktrees/w362-pub`, branch `claude/w362-pub`, base `6770a87e`,
Lean 4.31.0-rc2. The frozen `generated/appendix/*.tex`, `generated/hash-manifest.json`,
`GQ2.lean` and every existing Lean module are out of scope and untouched.

Ledger reference: `docs/dyadic/refs/dyadic-presentations-formalization-ledger.md` section 7,
whose ten items are

1 exact syntax tree; 2 the two specialization reductions; 3 evaluated Fox Jacobian;
4 invertible row/column operations; 5 reduced normal matrix; 6 Stokes chain identity;
7 extraspecial Hessian; 8 change of variables to quadratic normal form;
9 affine phase-cover certificate; 10 hash tying the generated TeX to the Lean syntax tree.

---

## T1. Ten-item inventory, verified against the tree

Three columns per item: **Lean source** (a declaration that actually proves or carries the
item's content, with `file:line` as of `6770a87e`), **generator** (an executable that emits a
synchronized artifact for that item), **neither**.

Two facts verified directly, not taken from the docs:

* `generated/general-ln-template-staged/` holds exactly six L/N specimens
  (`L-h0`, `L-h4`, `N0-alpha5-h3`, `Npc-alpha2-r1-h0-num1-den1`,
  `Npc-alpha3-r2-h3-num3-den9`, `Npc-alpha3-r2-h3-num-3-den9`), each as
  `.ln.json` + `.tex` + `.provenance.json`. Each `.tex` contains item 1 (the rendered
  canonical tree) and item 10 (the `% ast-hash` and `% envelope-hash` trailers) and
  **nothing else**. They are word displays, not ten-item appendices.
* `generated/appendix/` holds exactly five skeletons, each with **nine** textual
  occurrences of `dyadicAppendixTODO`: one is the `\newcommand` usage note in the
  preamble comment, eight are real invocations. Five files times eight is the recorded
  **40 invocations**. In every one of the five, items 1 and 10 are filled and items 2-9
  are the eight TODO slots. This distribution is identical across all five files.

### T1.a Lean sources by family (uniform in the handle rank unless noted)

| Item | L (odd degree) | N0 (compact) | Npc (procyclic) |
|---|---|---|---|
| 1 | `Words.LSq.rawLsq` `GQ2/Dyadic/Words/L.lean:268`; `Words.LSq.lSqW` `:232`; bridge `GeneralTemplateLN.denote_canon_rawLsq` `GQ2/Dyadic/Word/GeneralTemplateLNCanonical.lean:35` | `Words.rawNCompact` `GQ2/Dyadic/Words/N0.lean:131`; `Words.nCompactW` `:115`; bridge `denote_canon_rawNCompact` `GeneralTemplateLNCanonical.lean:40` | `Words.Npc.rawNpc` `GQ2/Dyadic/Words/Npc.lean:237`; `Words.Npc.npcW` `:206`; `SelectedEta.npcWUnit` `GQ2/Dyadic/SelectedEta.lean:188`; bridges `denote_canon_rawNpc` `:46` and `denote_canon_rawNpc_display` `:52` |
| 2 | `eval_pro2_lSqW_eq_sqRelWord` `Words/L.lean:680`; `lCanonicalTameSpecialization` `Instances/GammaLReconstruction.lean:54`; carried by `wordCertificateRN_lSq_pow` `Instances/GammaLSourceArfGeneral.lean:527` and `wordCertificateRN_lSq_qOf` `Instances/GammaLOddDegreeGrandAssembly.lean:124` | `pro2_nCompact` `Words/N0.lean:361`; `eval_pro2_nCompact` `:378`; `genCertNProTwoWord` `GeneralCertificates.lean:451`; `genCertNTameSpecializes` `:478`; carried by `wPcNWordCertificateRN` `Instances/WordPhaseCompactNFinal.lean:58` | `eval_pro2_npcW` `Words/Npc.lean:686`; `NpcCore.npcProTwoWordUnit` `Instances/NpcCore.lean:434`; `npcWUnit_eq_display` `SelectedEta.lean:194`; carried by `npcWordCertificateRN` `Instances/NpcDeterminantFinal.lean:83` |
| 3 | `Certificates.LSq.foxD_lSq_unram` `Certificates/LFox.lean:451`, `foxD_lSq_ram` `:473` | `Certificates.foxD_nCompact_unram` `Certificates/N0Fox.lean:352`, `foxD_nCompact_ram` `:378` | `Certificates.Npc.foxD_npc_unram` `Certificates/NpcFox.lean:825`, `foxD_npc_ram` `:850` |
| 4 | `lSqJacobianCertUnram` `Certificates/LJacobian.lean:53` (`rowOps := nCompactUnramOps`), `lSqJacobianCertRam` `:107` (`colOps := lSqRamOps` `:46`), `lSqJacobianCertScalar` `:150` (`rowOps` inline) | `nCompactJacobianCertUnram` `Certificates/N0Fox.lean:921` (`nCompactUnramOps` `:801`), `nCompactJacobianCertRam` `:961` (`nCompactRamOps` `:806`) | `npcJacobianCertUnram` `Certificates/NpcFox.lean:1538` (`npcUnramOps` `:1408`), `npcJacobianCertRam` `:1585` (`npcRamOps` `:1414`) |
| 5 | `lSqUnramNormalForm` `LJacobian.lean:38`, `lSqRamNormalForm` `:42`, scalar target inline at `:157` | `nCompactUnramNormalForm` `N0Fox.lean:788`, `nCompactRamNormalForm` `:794` | targets inline in the two records (`NpcFox.lean:1547`, `:1594`), built from `tameUnramRow` `:1270`, `tameRow` `:1278`, `npcBlockRow`, `FoxRowNormalForm.single` |
| 6 | `stokesDualityCertificate_of_actionImage`, consumed as the `stokes` field at `Instances/GammaLReconstruction.lean:117` | `wPh_nCand_stokes` `Instances/WordPhase.lean:401`, consumed at `WordPhaseCompactNFinal.lean:75` | `stokes` field of `npcWordCertificateRN_of_determinant`, reached through `npcAffineDeterminantCertificate` `NpcDeterminantFinal.lean:61` |
| 7 | `Certificates.LSqStokes.hessRelZ_lSq` `Certificates/L.lean:1372` | `Certificates.hessRelZ_nCompact` `Certificates/N0.lean:873` | `hessRelZ_npcW_evenPhiNormal` `Instances/NpcUnramifiedFullOffsetHessian.lean:234`; `hessRelZ_npcW_evenTwistedNormal` `Instances/NpcRamifiedFullOffsetHessian.lean:372` |
| 8 | `LHessianCertificates.unramifiedHessian` `:129`, `.ramifiedHessian` `:156` | `CompactNHessianCertificates.compactNUnramifiedHessian` `:88`, `.compactNRamifiedHessian` `:101` | `NpcHessianCertificates.npcUnramifiedHeadHessian` `:24`, `nonempty_npcRamifiedHeadHessian` `:148`; coordinate change `NpcUnramifiedComparison.wPnpcPhiCoordsEquiv` `:48` |
| 9 | `LBoundaryHessianCertificates.lBoundaryHessian` `:32`; determinant `determinantResidue_lSq_pow` `GammaLSourceArfGeneral.lean:499` via `lSquareAnalyticLeavesRN_pow` `:515` | `CompactNBoundaryHessianCertificates.compactNBoundaryHessian` `:35`; determinant `wPcN_affineDeterminantCertificate` `WordPhaseCompactNFinal.lean:35` | `NpcBoundaryHessianCertificates.npcBoundaryHessian` `:131`; determinant `npcAffineDeterminantCertificate` `NpcDeterminantFinal.lean:61` |
| 10 | `Export.canonicalJson` / `astHash` via `GQ2/Dyadic/Word/GeneralTemplateLNExport.lean` | same | same, with `EtaData.canonicalEtaHat_toZhat` behind `denote_canon_rawNpc_display` |

Every cell above is a **Lean source**. So for L, N0 and Npc **no ledger item lacks a Lean
source**. What is missing everywhere except items 1 and 10 is a *generator*.

### T1.b Generators, before this lane

| Item | Generator that emits a synchronized L/N artifact |
|---|---|
| 1 | `scripts/w361_general_ln_word_tex.py` + `GQ2/Dyadic/Word/GeneralTemplateLNExport.lean`. Covers all three families at every parameter. |
| 10 | same pair (`word_hash`, `template_hash`, `.provenance.json`). |
| 2, 3, 6, 7, 8, 9 | **none.** |
| 4, 5 | **none before this lane.** Added by T2 below. |

The W361 Fox/phase/cover generators are **not** reusable as they stand:
`scripts/w361_general_fox_tex.py`, `_phase_tex.py`, `_cover_tex.py` read
`GQ2/Dyadic/Word/GeneralFoxTemplateExport.lean`,
`GeneralPhaseTemplateExport.lean` and `GeneralPhaseCoverTemplateExport.lean`, whose payloads
are pair/mobile-splice specific. `foxTemplatePayload` declares
`application_scope = "Actual pair/mobile splice certificates ..."` and names
`..._pair_signature` / `..._mobile_signature` as its certificate bridges. There is no L/N
profile in `GeneralFoxTemplate` and no L/N binding in `TameSpliceFoxTemplateBinding`.
Reusing those renderers for L/N would be exactly the substitution the readiness note
forbids.

### T1.c Per-artifact status

Six legacy L/N specimens, `generated/general-ln-template-staged/`:

| Artifact | Items present in the artifact | Items with a Lean source but no artifact content |
|---|---|---|
| `L-h0`, `L-h4` | 1, 10 | 2-9 |
| `N0-alpha5-h3` | 1, 10 | 2-9 |
| `Npc-alpha2-r1-h0-num1-den1` | 1, 10 (+ exact `NpcDisplayFor` unit bridge) | 2-9 |
| `Npc-alpha3-r2-h3-num3-den9` | 1, 10 | 2-9 |
| `Npc-alpha3-r2-h3-num-3-den9` | 1, 10 | 2-9 |

Five TODO-bearing skeletons, `generated/appendix/`:

| Skeleton | Branch | 1 | 10 | 2-9 | Lean sources for 2-9 |
|---|---|---|---|---|---|
| `rawLsq_n1.tex` | L, `h = 0` | filled | filled | 8 TODO | all present (T1.a, L column) |
| `rawNCompact_alpha2_h0.tex` | N0, `alpha=2, h=0` | filled | filled | 8 TODO | all present (T1.a, N0 column) |
| `rawNpc_a2_r1_eta1_1_h0.tex` | Npc, `alpha=2, r=1, eta=1, h=0` | filled | filled | 8 TODO | all present (T1.a, Npc column) |
| `rawMCompact_alpha2_h0_q2.tex` | M0 (frozen word) | filled | filled | 8 TODO | Fox: `mCompactJacobianCertUnram` `Certificates/M0Fox.lean:1267`, `_Ram` `:1310`, `foxD_mCompact_unram` `:789`. Certificate: `EvenMChangedWordCertificate.mCompactWordCertificateRN_of_boundary` `:44`, `MCompactFlexibleCertificate.mCompactWordCertificateRN_flexible` `:67`. |
| `rawMpcSqrtNeg10.tex` | Mpc (frozen word) | filled | filled | 8 TODO | Certificate: `MpcCandidateRN.mpcWordCertificateRN_of_determinant` `:91`, `MpcFlexibleCertificate.mpcWordCertificateRN_flexible` `:89`. **No** `mpcJacobianCertUnram`/`_Ram` and **no** `foxD_mpc_unram` exists; the Mpc Fox items 3-5 have no family-named Lean record in this tree. |

The two M rows are outside this lane's mandate and are recorded only so the "five
skeletons" count is honest. In particular the four staged pair/mobile packets in
`generated/general-certificate-staged/` are packets for the **changed** promoted-pair /
mobile-splice source, not for the frozen `rawMCompact_alpha2_h0_q2` or `rawMpcSqrtNeg10`
words; they do not fill these two skeletons and must not be presented as doing so.

### T1.d The one thing T1 changes about the received picture

The docs say the L/N gap is "publication/interface, not a missing Lean phase proof". T1
confirms that, and sharpens it: the gap is **exactly one missing exporter layer**, not eight
missing proofs. Items 4 and 5 in particular are already *concrete Lean data*
(`FoxRowOp`/`FoxColOp` lists and `FoxNormalForm` records built from `FoxCoeff` trees), so
they can be serialized rather than retyped. That is what T2 does.

