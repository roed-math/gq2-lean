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
| 1 | `Words.LSq.rawLsq` `GQ2/Dyadic/Words/L.lean:268`; `Words.LSq.lSqW` `:232`; bridge `GeneralTemplateLN.denote_canon_rawLsq` `GQ2/Dyadic/Word/GeneralTemplateLNCanonical.lean:35` | `Words.rawNCompact` `GQ2/Dyadic/Words/N0.lean:131`; `Words.nCompactW` `:115`; bridge `denote_canon_rawNCompact` `GeneralTemplateLNCanonical.lean:40` | `Words.Npc.rawNpc` `GQ2/Dyadic/Words/Npc.lean:237`; `Words.Npc.npcW` `:206`; `Words.Npc.npcWUnit` `GQ2/Dyadic/SelectedEta.lean:188`; bridges `denote_canon_rawNpc` `:46` and `denote_canon_rawNpc_display` `:52` |
| 2 | `eval_pro2_lSqW_eq_sqRelWord` `Words/L.lean:680`; `lCanonicalTameSpecialization` `Instances/GammaLReconstruction.lean:54`; carried by `wordCertificateRN_lSq_pow` `Instances/GammaLSourceArfGeneral.lean:527` and `wordCertificateRN_lSq_qOf` `Instances/GammaLOddDegreeGrandAssembly.lean:124` | `pro2_nCompact` `Words/N0.lean:361`; `eval_pro2_nCompact` `:378`; `genCertNProTwoWord` `GeneralCertificates.lean:451`; `genCertNTameSpecializes` `:478`; carried by `wPcNWordCertificateRN` `Instances/WordPhaseCompactNFinal.lean:58` | `eval_pro2_npcW` `Words/Npc.lean:686`; `Instances.NProcyclicCore.npcProTwoWordUnit` `Instances/NpcCore.lean:434`; `Words.Npc.npcWUnit_eq_display` `SelectedEta.lean:194`; carried by `npcWordCertificateRN` `Instances/NpcDeterminantFinal.lean:83` |
| 3 | `Certificates.LSq.foxD_lSq_unram` `Certificates/LFox.lean:451`, `foxD_lSq_ram` `:473` | `Certificates.foxD_nCompact_unram` `Certificates/N0Fox.lean:352`, `foxD_nCompact_ram` `:378` | `Certificates.Npc.foxD_npc_unram` `Certificates/NpcFox.lean:825`, `foxD_npc_ram` `:850` |
| 4 | `lSqJacobianCertUnram` `Certificates/LJacobian.lean:53` (`rowOps := nCompactUnramOps`), `lSqJacobianCertRam` `:107` (`colOps := lSqRamOps` `:46`), `lSqJacobianCertScalar` `:150` (`rowOps` inline) | `nCompactJacobianCertUnram` `Certificates/N0Fox.lean:921` (`nCompactUnramOps` `:801`), `nCompactJacobianCertRam` `:961` (`nCompactRamOps` `:806`) | `npcJacobianCertUnram` `Certificates/NpcFox.lean:1538` (`npcUnramOps` `:1408`), `npcJacobianCertRam` `:1585` (`npcRamOps` `:1414`) |
| 5 | `lSqUnramNormalForm` `LJacobian.lean:38`, `lSqRamNormalForm` `:42`, scalar ops and target inline at `LJacobian.lean:155`, `:157` | `nCompactUnramNormalForm` `N0Fox.lean:788`, `nCompactRamNormalForm` `:794` | targets inline in the two records (`NpcFox.lean:1545`, `:1593`), built from `tameUnramRow` `:1270`, `tameRow` `:1278`, `npcBlockRow` `:1260`, `FoxRowNormalForm.single` `Word/FoxCert.lean:585` |
| 6 | `LSquare.stokesDualityCertificate_of_actionImage` `Instances/GammaLAnalyticLeaves.lean:390`, consumed as the `stokes` field at `Instances/GammaLReconstruction.lean:117` | `wPh_nCand_stokes` `Instances/WordPhase.lean:401`, consumed at `WordPhaseCompactNFinal.lean:75` | `NpcCandidateStokes.npcCand_stokes` `:358`, consumed as the `stokes` field of `NpcCandidateRN.npcWordCertificateRN_of_determinant` `:63` |
| 7 | `Certificates.LSqStokes.hessRelZ_lSq` `Certificates/L.lean:1372` | `Certificates.hessRelZ_nCompact` `Certificates/N0.lean:873` | `hessRelZ_npcW_evenPhiNormal` `Instances/NpcUnramifiedFullOffsetHessian.lean:234`; `hessRelZ_npcW_evenTwistedNormal` `Instances/NpcRamifiedFullOffsetHessian.lean:372` |
| 8 | `LHessianCertificates.unramifiedHessian` `:129`, `.ramifiedHessian` `:156` | `CompactNHessianCertificates.compactNUnramifiedHessian` `:88`, `.compactNRamifiedHessian` `:101` | `NpcHessianCertificates.npcUnramifiedHeadHessian` `:24`, `nonempty_npcRamifiedHeadHessian` `:148`; coordinate change `NpcUnramifiedComparison.wPnpcPhiCoordsEquiv` `:48` |
| 9 | `LBoundaryHessianCertificates.lBoundaryHessian` `:32`; determinant `determinantResidue_lSq_pow` `GammaLSourceArfGeneral.lean:499` via `lSquareAnalyticLeavesRN_pow` `:515` | `CompactNBoundaryHessianCertificates.compactNBoundaryHessian` `:35`; determinant `wPcN_affineDeterminantCertificate` `WordPhaseCompactNFinal.lean:35` | `NpcBoundaryHessianCertificates.npcBoundaryHessian` `:131`; determinant `npcAffineDeterminantCertificate` `NpcDeterminantFinal.lean:61` |
| 10 | `Export.canonicalJson` / `astHash` via `GQ2/Dyadic/Word/GeneralTemplateLNExport.lean` | same | same, with `EtaData.canonicalEtaHat_toZhat` behind `denote_canon_rawNpc_display` |

Every cell above is a **Lean source**. So for L, N0 and Npc **no ledger item lacks a Lean
source**. What is missing everywhere except items 1 and 10 is a *generator*.

Two naming traps were found while checking these, and both cost a probe iteration:
`Instances/NpcCore.lean` declares in namespace `Instances.NProcyclicCore`, not `NpcCore`,
and `npcWUnit` / `npcWUnit_eq_display` live in `Words.Npc` although their file is
`SelectedEta.lean`. Citing a declaration by its file name does not give its Lean name.

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


---

## T2. What was staged

New directory `generated/general-ln-certificate-staged/`, plus four new scripts. Nothing
outside that directory, `scripts/w362_*` and this note was created or modified; the frozen
`generated/appendix/*.tex`, `generated/hash-manifest.json`, `GQ2.lean`, every existing Lean
module and `scripts/w361_check_staged.sh` are byte-identical to `6770a87e`.

### T2.a The one new piece of Lean: an exporter driver, not a library module

`scripts/w362_ln_fox_export.lean` is an exporter driver with a global `main`, so it stays
outside `GQ2.lean` like the other W361 export executables. It serializes ledger items 4 and 5
for the **seven existing** L/N0/Npc `FoxCertificate` sectors.

The point of the driver is that it does not retype a matrix. Items 4 and 5 are already
concrete Lean data (`List (FoxRowOp S)`, `List (FoxColOp X S)`, and a `FoxNormalForm`
built from `FoxCoeff` trees), so the driver serializes the values and carries **21 `rfl`
signature theorems** proving that what it serialized is definitionally the corresponding
field of the actual record:

```text
lSqUnram_rowOps/_colOps/_target        lSqJacobianCertUnram
lSqRam_rowOps/_colOps/_target          lSqJacobianCertRam
lSqScalar_rowOps/_colOps/_target       lSqJacobianCertScalar
nCompactUnram_rowOps/_colOps/_target   nCompactJacobianCertUnram
nCompactRam_rowOps/_colOps/_target     nCompactJacobianCertRam
npcUnram_rowOps/_colOps/_target        npcJacobianCertUnram
npcRam_rowOps/_colOps/_target          npcJacobianCertRam
```

Three sector values are spelled inline inside their records (`lSqJacobianCertScalar`'s row
op and target, and both Npc targets). The driver gives those four values names
(`lSqScalarOps`, `lSqScalarNormalForm`, `npcUnramNormalForm`, `npcRamNormalForm`) and binds
them by the same `rfl` theorems, so naming them does not weaken the tie. Twenty-six axiom
pins are recorded in the driver, all standard three or less; the four new data definitions
print `[]`, `[]`, `[propext]` and `[propext, Quot.sound]`.

The W361 Fox/phase/cover generators were **not** reused. Their Lean payload is
pair/mobile-splice specific: `foxTemplatePayload` declares
`application_scope = "Actual pair/mobile splice certificates ..."` and names
`..._pair_signature` / `..._mobile_signature` as its bridges. Pointing them at L/N would have
substituted one family's symbolic profile for another's, which is exactly what the readiness
note forbids.

### T2.b What the exported rows actually say

The rendered output agrees with the analytic descriptions recorded in
`w361-l-n-certificate-readiness.md` section 3. Here it is produced from the records rather
than transcribed from them, so the agreement is a check and not a restatement:

| Sector | Ordered operations | Reduced target |
|---|---|---|
| L unramified | `R2 <- R2 + S R1` | `S^-1 a_tau` over `(I - S^-1) a_x0` |
| L ramified | scale col `x0` by `S`, carried inverse `S^-1` | universal tame row over `I a_x0` |
| L scalar | `R2 <- R2 - I R1` | `I a_tau` over `0` |
| N0 unramified | `R2 <- R2 + S R1` | `S^-1 a_tau` over `(I - S^-1) a_x2` |
| N0 ramified | scale col `x2` by `S`, carried inverse `S^-1` | universal tame row over `I a_x2` |
| Npc unramified | `R2 <- R2 + S R1` | `S^-1 a_tau` over `(A^-1 + I) a_x0 + (I + S^-2^r) a_x2` |
| Npc ramified | scale col `x2` by `S^2^r` (carried inverse `S^-2^r`), then clear `x0` | universal tame row over `I a_x2` |

The universal tame row prints as
`S^-1 . (T - I) a_sigma + (S^-1 - N_q(T)) a_tau`, with `N_q(T)` the literal left-nested
`normCoeff` sum, not a re-spelled closed form. The Npc unramified row stops at its two
blocks and no unit claim is generated for either.

The L unramified pivot is at `x0`, **not** at the even families' `x2` slot, and the L scalar
sector degenerates visibly to `tau` over zero rather than to two independent pivots. Both
were checks worth having in a generated artifact rather than in prose.

### T2.c The ten-item packets

`scripts/w362_ln_certificate_packet.py` composes packets. Per item the state is explicit,
because the ten items are genuinely not in the same state:

| Item | State | Source |
|---|---|---|
| 1 | generated display | `w361_general_ln_word_tex` + `GeneralTemplateLNExport.lean` |
| 2, 3, 6, 7, 8, 9 | checked declarations + stored transcript; **no display** | the probe |
| 4, 5 | generated display | `w362_ln_fox_tex` + `w362_ln_fox_export.lean` |
| 10 | generated hashes | word hash, Fox hash, packet hash, provenance |

"Checked declarations" is a real check, not a citation: the probe proves each named
declaration exists, has at most `[propext, Classical.choice, Quot.sound]`, and prints its
elaborated statement; `check` compares the stored transcript against a fresh replay. The
probe pins 27 declarations for L, 27 for N0 and 33 for Npc.

**The standing-axiom class.** The field-selection adapters
`FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_l`, `_n0` and `_npc` are **not**
standard-three. Each carries exactly four documented standing inputs:
`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
`absGalQ2_isTopologicallyFinitelyGenerated` and `absGalQ2_localEulerCharacteristic`. The
probe prints their full axiom list instead of gating them, and every packet says so in
item 2. Standard-three analytic word certificates do not make the field theorem axiom-free,
and folding these three into the standard-three count would have been the exact error the
readiness note warns about.

Staged packets, all passing full Lean replay. Three sit at exactly the parameters the
frozen L/N appendix skeletons use, and three sit beyond them, so the set is not a fixture
battery in disguise:

| Packet | Word | Packet hash (first 16) |
|---|---|---|
| `packet-L-h0` | `lSqW 0`, the frozen L appendix rank | `7f19d17e089e5601` |
| `packet-L-h4` | `lSqW 4`, beyond the frozen rank | `f98de22bb3784b27` |
| `packet-N0-alpha2-h0` | `nCompactW 2 0`, the frozen N0 appendix parameters | `1bb59b9410e1575a` |
| `packet-N0-alpha5-h3` | `nCompactW 5 3`, beyond them | `b54126b5b0eb3d05` |
| `packet-Npc-alpha2-r1-h0-num1-den1` | `npcW 2 1 0 (1/1)`, the frozen Npc appendix display | `6cf3a39e763ab22c` |
| `packet-Npc-alpha3-r2-h3-num3-den9` | `npcW 3 2 3 (3/9)`, a nonreduced odd display | `97d13c271280afd5` |

The hashes above are a locator. Each packet's `.files.json` is the authority for its own
four files, and the packet hash is recomputed on every check.

`scripts/w362_ln_certificates.tex` is a review wrapper, modelled on
`scripts/w361_staged_certificates.tex`, that `\input`s the six generated appendices. It
compiles with `pdflatex` to a 28-page document with **zero LaTeX errors and zero overfull
boxes**, which is the reason item 1 emits the word exporter's displayed equations as LaTeX
rather than dumping its file into a `verbatim` block: verbatim cannot wrap, and the Npc word
at rank three overflowed the text block by 573pt. The wrapper is a reading aid; no PDF is
committed, and the wrapper is not an appendix, a gate, or an approval.

---

### T2.d The honest TODO list

Six of the ten items have no generated display. Each packet states this in the section
itself and names the exporter declaration that would supply one and that **does not exist
in this tree**:

| Item | Named missing exporter |
|---|---|
| 2 two specializations | `GQ2.Dyadic.W362LNSpecialization.specializationTemplate` |
| 3 evaluated Fox Jacobian | `GQ2.Dyadic.W362LNFox.inputRowsTemplate` |
| 6 Stokes chain identity | `GQ2.Dyadic.W362LNStokes.chainTemplate` |
| 7 extraspecial Hessian | `GQ2.Dyadic.W362LNPhase.hessianTemplate` |
| 8 quadratic normal form | `GQ2.Dyadic.W362LNPhase.coordinateTemplate` |
| 9 affine phase-cover | `GQ2.Dyadic.W362LNCover.phaseCoverTemplate` |

These six names are **proposals for work not done**, not references to existing code. Two
further TODOs are recorded:

* item 4 in every packet: the 21 `rfl` signature theorems live in the exporter driver, which
  has no olean and therefore cannot be cited by the declaration probe. They are checked only
  by the Fox replay, which recompiles the driver;
* item 5 in the Npc packets: the two surviving unramified blocks are not certified units, and
  no generated unit claim is produced for them.

The reason items 2, 3 and 6 to 9 lack displays is **not** a missing proof. T1 established
that each has a Lean source. It is the missing exporter layer, and the six names above are
exactly the size of the remaining publication work for the L/N families.

---

## T3. Proposal: how the staged L/N packets would enter the manifest and appendix contract

**This is a proposal, not an adoption.** Nothing below is done, and none of it is an owner
ruling, a census amendment, a gate change, or a release step. Its purpose is to make the
decision concrete enough to be taken or refused.

### T3.a Facts that constrain any route (verified, not quoted)

1. `generated/hash-manifest.json` has five entries with the fields
   `appendix, branch, interchange, latex, lean{declaration, hash_constant, module}, name,
   source, word_hash`, plus the top-level `ast_schema_version`, `generator`, `hash_rule`,
   `manifest_version`. Its `hash_rule` is the S1.1 canonical-JSON sha256.
2. Merge gate 7 is the D4 extension point: `python3 scripts/dyadic_word_tex.py check`. It
   compares the `% ast-hash` trailer of each declared entry's generated TeX against that
   entry's Lean `hash_constant`. It reads only those five entries.
3. Four of the five `lean.declaration` values (`rawLsq_n1`, `rawMCompact_alpha2_h0_q2`,
   `rawNCompact_alpha2_h0`, `rawNpc_a2_r1_eta1_1_h0`) are **instance labels, not Lean
   declarations**; only `rawMpcSqrtNeg10` is also a real definition. The corresponding
   `_astHash` constants all exist, and `#eval Export.assertAstHash` guards pin exactly
   `rawLsq 0`, `rawNCompact 2 0` and `rawNpc 2 1 0 1 1`. Any new entry must decide which of
   these two things its `declaration` field names.
4. **The staged packets at the frozen parameters carry the frozen word hashes.** Checked
   directly against the manifest, by replaying the exporter and comparing:
   `packet-L-h0` has word hash `d129037c...`, identical to `rawLsq_n1`;
   `packet-N0-alpha2-h0` has `a940b6ad...`, identical to `rawNCompact_alpha2_h0`;
   `packet-Npc-alpha2-r1-h0-num1-den1` has `08b7742c...`, identical to
   `rawNpc_a2_r1_eta1_1_h0`. So entering the parameter-matched packets changes **no** frozen
   identifier or hash. This is the single most important fact for the decision.
5. Every staged artifact embeds `status: "STAGED"`, and every validator **refuses** any other
   value. Adoption cannot be performed by editing that string.
6. `generated/appendix/*.tex` is generated by `scripts/dyadic_word_tex.py`. The staged
   `.appendix.tex` files are produced by a different generator in a different format. Two
   generators cannot own the same path.

### T3.b Three routes

**Route A, minimal: fill the three L/N skeletons in place, leave the manifest alone.**
For each of `rawLsq_n1.tex`, `rawNCompact_alpha2_h0.tex` and `rawNpc_a2_r1_eta1_1_h0.tex`,
replace the items 4 and 5 `dyadicAppendixTODO` slots with the corresponding staged Fox
display, and re-point the items 2, 3, 6, 7, 8 and 9 slots at their checked declarations
while keeping them marked TODO. The manifest is untouched: same names, same `word_hash`,
same `hash_constant`, gate 7 unchanged. Recorded TODO invocations for those three files drop
from 24 to 18, and the remaining 18 gain declaration pointers. A parameter-matched packet
already exists for each of the three.
*Cost:* `dyadic_word_tex.py` must learn to emit those two slots, or the two generators must
be composed. *Benefit:* no schema change, no new frozen constant, no gate change.

**Route B, full: add parameterized packet entries to the manifest.**
Add a new entry kind carrying `packet`, `packet_hash`, structural parameters and the two
template hashes, alongside the existing fixture entries. This is the only route that covers
the non-frozen ranks (`L h=4`, `N0 alpha=5 h=3`, `Npc alpha=3 r=2 h=3`).
*Cost:* three things the current contract does not have. (i) A parameterized entry has no
Lean `hash_constant`, so gate 7 must either gain new `_astHash` constants in a Lean module
inside `GQ2.lean`, or be extended to run the exporter, which makes the gate non-hermetic and
slower. (ii) `source` currently means a selection-freeze row plus a vendored certificate id;
a rank-4 L packet is not a freeze row and needs a different, owner-defined provenance value.
(iii) `manifest_version` and `ast_schema_version` would both need a decision.

**Route C, cite-only: keep the packets staged and reference them.**
The proof packet and appendix narrative cite `generated/general-ln-certificate-staged/`
as staged supporting material, with no manifest entry and no gate coverage. This is the
status quo plus a citation.
*Cost:* the artifacts stay outside every gate, so drift is caught only by whoever runs
`scripts/w362_check_ln_staged.sh` by hand.

A defensible combination is A for the three frozen rows and C for the non-frozen ranks,
deferring B until items 2, 3 and 6 to 9 have exporters; but that is a recommendation, not a
decision, and the lane does not take it.

### T3.c Owner decisions this proposal depends on

Every one of these is an owner decision. None is implied by anything in this lane.

1. Whether the staged L/N packet format is accepted as the L/N presentation at all, or
   whether an explicitly approved equivalent presentation supersedes it.
2. Which route (A, B, C, or a combination) the three frozen L/N rows take, and whether the
   non-frozen ranks are covered at all.
3. Whether a ten-item appendix may be published with six items carried by checked
   declarations and stored transcripts rather than by a generated display, or whether the six
   named exporters must be written first.
4. Whether `generated/appendix/*.tex` may be regenerated by a second generator, or whether
   the new displays must be folded into `scripts/dyadic_word_tex.py`.
5. If Route B: the new manifest entry schema, the `manifest_version` bump, the meaning of
   `source` for a parameterized entry, and whether `lean.declaration` names a declaration or
   an instance label.
6. If Route B: whether gate 7 gains new Lean `_astHash` constants (new frozen constants
   inside `GQ2.lean`) or instead runs the exporter (a non-hermetic, slower gate).
7. How a staged artifact is promoted at all, given that `status: "STAGED"` is embedded and
   every validator refuses another value: by a schema version bump, by a separate adopted
   copy, or by re-pointing the refusal.
8. Whether `scripts/w362_check_ln_staged.sh` is folded into `scripts/w361_check_staged.sh`
   or into `scripts/check_dyadic.sh`, and at which gate number. This lane deliberately left
   both of those files unmodified so that the recorded W361 check semantics did not change.
9. Whether the parameter choice `q = 2` in the Fox artifacts is the right published instance,
   and which ranks and structural parameters the published set should contain.
10. The treatment of the two M skeletons, which this lane did not touch: the four staged
    pair/mobile packets are packets for the changed promoted-pair/mobile-splice source and do
    **not** fill `rawMCompact_alpha2_h0_q2.tex` or `rawMpcSqrtNeg10.tex`.
11. Whether the Npc item 7 correction is made in the authoritative packet: the completed
    proof is the full-offset route, and the old Gate-E slice with an invertible `Lc` must not
    be displayed as the completed normal-coordinate proof. The staged packets already state
    the correction; adopting it in the authoritative text is a separate owner act.
12. Release gating as a whole: adoption, appendix migration, census approval and
    merge/release authorization all remain outside this lane.

### T3.d What this lane deliberately did not do

* It did not modify `generated/hash-manifest.json`, any `generated/appendix/*.tex`,
  `GQ2.lean`, any existing Lean module, `scripts/w361_check_staged.sh`, or
  `scripts/check_dyadic.sh`.
* It did not relabel any historical verification report as current, and it recorded no
  universal frozen-M placement claim.
* It did not treat `RawWord.shadow` as W361's semantic `tameShadow`, and it treats no
  matching declaration name as a word-identity proof.
* It did not run `lake` in any form.
