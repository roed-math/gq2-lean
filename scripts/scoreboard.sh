#!/usr/bin/env bash
# ============================================================================
# scripts/scoreboard.sh -- THE MACHINE-CHECKED CAMPAIGN SCOREBOARD
#
# Read-only.  Prints the campaign's load-bearing status facts by ELABORATING
# them, not by reading a table somebody maintained by hand.  Nothing here is
# wired into any gate; lanes and the orchestrator run it to see where the
# campaign stands without trusting a note.
#
# WHY THIS EXISTS
#
#   Hand-written status tables in this campaign have gone stale at their own
#   base six times (W78 through W83 house notes).  The failure is always the
#   same shape: a note asserts "X is open" or "row R carries clause C", the
#   theorem that refutes it predates the note, and no reader re-elaborates.
#   Every fact this script prints is re-derived from the imported environment
#   on each run.  The probe also checks that environment against every direct
#   source import in GQ2.lean, so a stale umbrella olean makes the board
#   UNVERIFIED instead of silently producing stale rows.
#
# RUNNING
#
#   bash scripts/scoreboard.sh            full board
#   bash scripts/scoreboard.sh --raw      the probe's records, unformatted
#
#   Needs the same shared olean cache `scripts/mirror.sh` needs; run
#   `scripts/mirror.sh sweep` first if the cache has advanced.  After changing
#   direct imports in GQ2.lean, also run `scripts/mirror.sh gen GQ2`.  A missed
#   umbrella regeneration is detected and reported as STALE_UMBRELLA.  The
#   board invokes `mirror.sh check` on ONE generated probe and no `lake`
#   command.
#
# ----------------------------------------------------------------------------
# HOW TO ADD A ROW
#
# Add one line to the ROWS table below.  Four fields, `|`-separated:
#
#     GROUP|LABEL|KIND|DECLARATION-NAME
#
#   GROUP  the section it prints under.  A new group name creates a new
#          section, in first-appearance order.
#   LABEL  free text, printed verbatim in the left column.
#   KIND   `decl` or `prod` (below).
#   DECLARATION-NAME  the SHORT name, exactly as it appears after
#          `theorem`/`def`/`abbrev`/`structure` in the source.  The script
#          finds the file, reconstructs the fully-qualified name from the
#          namespace stack, and derives the module to import.  Do NOT write a
#          module, a namespace, a file path or a line number: those are the
#          things that rot.
#
#   KIND `decl` reports, for that one declaration:
#          * EXISTS / MISSING (elaborated, not grepped);
#          * its EXPLICIT binders' types -- i.e. exactly the clauses a caller
#            must supply.  Instance-implicit and implicit binders are dropped;
#          * its axiom census, as `std-3` plus the non-standard names.
#
#          Read the "carries" column as "what a caller must hand this
#          declaration".  For a `theorem` those are its hypotheses; for a
#          `def _ : Prop` they are the `Prop`'s own parameters, which is why
#          e.g. `askCStageVanishing` reports four.  `--raw` prints the full
#          pretty-printed binder types behind the head symbols.
#
#   KIND `prod` reports EVERY declaration in the `GQ2` root whose conclusion
#          has that name as its head constant -- i.e. every producer of that
#          `Prop`/type in the tree -- each with its explicit binders.  This is
#          the row type that catches "no theorem in this tree produces X":
#          the machine enumerates the producers, so the claim cannot be made
#          against a stale memory of the tree.  The scan runs against the
#          UMBRELLA environment (see "THE PROBE" below), so it does NOT depend
#          on which modules the rows happen to name.
#
# WHAT THIS SCRIPT WILL NOT DO
#
#   It carries NO hand-maintained facts: no clause lists, no axiom tags, no
#   "open/closed" verdicts, no line numbers, no counts.  Where a fact cannot
#   be machine-checked cheaply it prints UNVERIFIED and, next to it, the
#   nearest thing that CAN be checked.  Do not "fix" an UNVERIFIED by writing
#   the answer in here; either make it checkable or leave it.
#
# ----------------------------------------------------------------------------
# THE OWNER-ITEMS CONTRACT  (W87-HOUSE)
#
# The OWNER ITEMS section is the one place this board reads PROSE, because
# owner items are prose and there is nothing in the environment to elaborate.
# It therefore does not certify a count; it reads two files that each assert
# one, prints both, and prints whether they agree.  A disagreement is the
# product, not a failure.
#
#   AUTHORITY  `docs/dyadic/owner-items-*.md`, the owner's own memo (newest by
#              name if the glob ever matches more than one, and it says so).
#              Contract: status blocks newest-first, each headed
#                  `## Status at wave N (YYYY-MM-DD)`
#              and the newest block containing, in bold, the phrase
#                  `**<Word> items await you**`
#              with the count as an English number word (one..twenty).  The
#              word is mapped, never parsed; an unmapped word prints
#              UNVERIFIED rather than a guess.
#
#   ARTIFACT   the highest-numbered `docs/dyadic/wNN-house-note.md`.  Contract:
#              a heading matching, case-insensitively, an optional section
#              number, an optional leading "The", then "Owner items", with any
#              trailing gloss after a colon; the items are the lines under it
#              beginning `N.` up to the next heading.
#
# WHY BOTH.  A house note is FROZEN at its lane's close, so an item discharged
# after that close still counts in the note.  That is not hypothetical: wave
# 86's note listed ten items, the tenth being "register the two wave-86
# modules", which `ed382b2e` then discharged, and the wave-86 memo block
# accordingly says nine.  Reading only the note prints the pre-discharge
# number; reading only the memo hides which item moved.
#
# WHY TOLERANT.  Until W87 this section matched `^#+ +Owner items` against the
# note alone.  Six of the ten house notes w77..w86 do not meet that shape
# ("### 4.5  The owner items", "## OWNER ITEMS", "## 4  Owner items: nine
# standing", and w85 with no such heading at all), and the strict match
# reported the miss as the number 0 -- indistinguishable from a note that
# genuinely lists no items.  The board printed `numbered items in it  0` for
# waves 84 and 85 and no reader queried it.  A missing heading now prints as
# NOT FOUND, with the heading it did match echoed back so the reader can see
# what was counted.
#
# DO NOT respond to a DISAGREE line by editing a number into this script.
# ============================================================================
set -uo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
WT=${GQ2_WT:-$(dirname "$HERE")}
MIRROR=$HERE/mirror.sh
RAW=0
[ "${1:-}" = "--raw" ] && RAW=1

# ----------------------------------------------------------------------------
# THE ROWS.  Declaration names only.  See "HOW TO ADD A ROW" above.
# ----------------------------------------------------------------------------
ROWS=$(cat <<'TABLE'
FROZEN ROWS|Q2(v-2)  .N0 2 0|decl|fieldUni_genAsmBranch_sqrtNegTwo
FROZEN ROWS|Q2(v2)   .M0 3 0|decl|fieldUni_genAsmBranch_sqrtTwo
FROZEN ROWS|Q2(v5)   .M0 2 0|decl|fieldFive_genAsmBranch_sqrtFive
FROZEN ROWS|Q2(v10)  .Mpc F|decl|mpcNorm_genAsmBranch_sqrtTen
FROZEN ROWS|Q2(v-10) .Mpc T|decl|mpcNorm_genAsmBranch_sqrtNegTen_of_pivot
FROZEN ROWS|Q2(v-10) via shift|decl|mpcPiv_genAsmBranch_sqrtNegTen_of_shift
FROZEN ROWS|Q2(v-10) untied|decl|mpcPiv_genAsmBranch_sqrtNegTen
FROZEN ROWS|v-10 residue = word prob|decl|mpcOrb_shift_iff_marking
FROZEN ROWS|v-10 finite-class route|decl|mpcWord_shift_of_forall_class_four
FROZEN ROWS|v-10 residual move|prod|MpcPivShift
FROZEN ROWS|v-10 initial-relator absorption|decl|mpcMk_initialRelatorAbsorption
FROZEN ROWS|v-10 pivot shift theorem|decl|mpcMk_pivShift
LEGACY RECORDS (COMPAT ONLY)|Q2(v-2)  .N0 2 0|decl|canRec_rowResidual_sqrtNegTwo
LEGACY RECORDS (COMPAT ONLY)|Q2(v2)   .M0 3 0|decl|canRec_rowResidual_sqrtTwo
LEGACY RECORDS (COMPAT ONLY)|Q2(v5)   .M0 2 0|decl|canRec_rowResidual_sqrtFive
LEGACY RECORDS (COMPAT ONLY)|Q2(v10)  .Mpc F|decl|canRec_rowResidual_sqrtTen
LEGACY RECORDS (COMPAT ONLY)|the tied transport|decl|canRec_rowResidual_of_tied
LEGACY RECORDS (COMPAT ONLY)|v5 cand clause = coeff|decl|rowCl_mCand_exactLifting_iff
LEGACY RECORDS (COMPAT ONLY)|v-2 cand clause = coeff|decl|rowCl_nCand_exactLifting_iff
CORRECTED RN RECORDS|N0 certificate (all a,h)|decl|wPcNWordCertificateRN
CORRECTED RN RECORDS|M0 certificate (from supply)|decl|wPcMWordCertificateRN_of_supply
CORRECTED RN ANALYTIC|M0 affine determinant (all a,h)|decl|wPcMAffineDeterminantCertificate_handles
CORRECTED RN RECORDS|M0 certificate (all a,h)|decl|wPcMWordCertificateRN_handles
CORRECTED RN ANALYTIC|M0 arbitrary-h ramified head phase|decl|wPcM_QZero_eq_ramifiedHandlePhase_of_headMark
CORRECTED RN ANALYTIC|M0 arbitrary-h unramified comparison|decl|wPcMComparison_unramifiedHead_handles
CORRECTED RN ANALYTIC|M0 arbitrary-h ramified comparison|decl|wPcMComparison_ramifiedHead_handles
CORRECTED RN ANALYTIC|M0 arbitrary-h branch-free supply|decl|wPcM_branchFreeSupply_handles
CORRECTED RN RECORDS|Mpc certificate (from determinant)|decl|mpcWordCertificateRN_of_determinant
CORRECTED RN ANALYTIC|Npc branch-free supply (all a,r,h)|decl|wPnpc_branchFreeSupply
CORRECTED RN ANALYTIC|Npc affine determinant (selected eta)|decl|npcAffineDeterminantCertificate
CORRECTED RN RECORDS|Npc certificate (all a,r,h; selected eta)|decl|npcWordCertificateRN
CORRECTED RN TIED|N0 residual (all a,h)|decl|wPcN_rowResidualRN_of_tied
CORRECTED RN TIED|N0 endpoint (all a,h)|decl|wPcN_candidate_equiv_galKRN_of_tied
CORRECTED RN SELECTOR CLOSED|N0 general-h level-zero realization|decl|markedCoreRealizationN_of_level_zero_general
CORRECTED RN SELECTOR CLOSED|N0 selected tied branch (oriented)|decl|n0GenAsmBranch_of_familySelection_tied
CORRECTED RN SELECTOR CLOSED|N0 selected RN residual (oriented)|decl|n0RowResidualRN_of_familySelection
CORRECTED RN TIED|M0 residual (all a,h)|decl|wPcM_rowResidualRN_of_tied
CORRECTED RN TIED|M0 endpoint (all a,h)|decl|wPcM_candidate_equiv_galKRN_of_tied
CORRECTED RN SELECTOR BOUNDARY|M0 level-zero chi-kernel unit|decl|mChiKerUnimodular_of_level_zero_general
CORRECTED RN SELECTOR BOUNDARY|M0 selected tied branch (needs C0 pivot)|decl|m0GenAsmBranch_of_familySelection_tied
CORRECTED RN SELECTOR BOUNDARY|M0 selected RN residual (needs C0 pivot)|decl|m0RowResidualRN_of_familySelection
CORRECTED RN SELECTOR BOUNDARY|M0 C0 cup-isometry obstruction|decl|no_c0_handle_mix_of_evenCup_isometry
CORRECTED RN SELECTOR BOUNDARY|M0 companion orientation obstruction|decl|no_chi_trivial_companion_d_one
CORRECTED RN SELECTOR BOUNDARY|M0 C0 unit invariant under oriented automorphisms|decl|isUnit_dmC_aut_iff
CORRECTED RN SELECTOR BOUNDARY|M0 no oriented C0 unitizer|decl|no_oriented_dmC_unitizer
CORRECTED RN SELECTOR BOUNDARY|M0 intrinsic field pivot condition|decl|M0FieldPivotUnit
CORRECTED RN SELECTOR BOUNDARY|M0 selected residual from intrinsic pivot|decl|m0RowResidualRN_of_familySelection_of_fieldPivot
CORRECTED RN SELECTOR BOUNDARY|M0 intrinsic pivot cup characterization|decl|m0FieldPivotUnit_iff_cup
CORRECTED RN SELECTOR BOUNDARY|M0 selected level and pivot cup audit|decl|m0_familySelection_level_and_pivot_iff_cup
CORRECTED RN SELECTOR BOUNDARY|M0 pivot as a quadratic norm obstruction|decl|exists_kummerRepresentatives_m0FieldPivot
CORRECTED RN SELECTOR BOUNDARY|M0 uniformizer not a norm from unramified quadratic|decl|not_normForm_piUnitK_of_unramified
CORRECTED RN SELECTOR BOUNDARY|M0 explicit uniformizer-Kummer packet|decl|M0UniformizerKummerData
CORRECTED RN SELECTOR BOUNDARY|M0 selected residual from D and unramified Kummer classes|decl|m0RowResidualRN_of_familySelection_of_uniformizerD
CORRECTED RN SELECTOR BOUNDARY|M0 pivot from uniformizer D and Artin-Kummer|decl|m0FieldPivotUnit_of_uniformizerD_of_artin
CORRECTED RN SELECTOR BOUNDARY|M0 selected residual from uniformizer D and Artin-Kummer|decl|m0RowResidualRN_of_familySelection_of_uniformizerD_artin
CORRECTED RN SELECTOR BOUNDARY|M0 pointwise uniformizer Artin residual|decl|M0UniformizerArtinCompatibility
CORRECTED RN SELECTOR BOUNDARY|M0 selected residual from pointwise Artin value|decl|m0RowResidualRN_of_familySelection_of_uniformizerD_artinValue
CORRECTED RN SELECTOR BOUNDARY|M0 pivot iff pointwise Artin value|decl|m0FieldPivotUnit_iff_uniformizerArtinValue
CORRECTED RN SELECTOR BOUNDARY|M0 transported D character is intrinsic|decl|m0FieldDCharacter_congr_oriented
CORRECTED RN SELECTOR BOUNDARY|M0 intrinsic uniformizer D placement|decl|M0UniformizerDPlacement
CORRECTED RN SELECTOR AUDIT|M0 transported D equals deep cyclotomic class|decl|m0FieldDCharacter_eq_evenDeepDigitChar
CORRECTED RN SELECTOR AUDIT|M0 depth-two placement iff 2/pi is square|decl|m0UniformizerDPlacement_two_iff_squareClass
CORRECTED RN SELECTOR AUDIT|M0 depth-two placement forces odd ramification|decl|odd_ramificationIndex_of_uniformizerTwoSquareClass
CORRECTED RN SELECTOR AUDIT|M0 selected depth-two odd-residue placement no-go|decl|not_m0UniformizerDPlacement_two_of_familySelection_odd_residue
CORRECTED RN SELECTOR AUDIT|M0 even-e unramified norm form represents 2|decl|exists_normForm_two_of_unramified_even_ramification
CORRECTED RN SELECTOR AUDIT|M0 selected depth-two odd-residue pivot no-go|decl|not_m0FieldPivotUnit_two_of_familySelection_odd_residue
CORRECTED RN SELECTOR BOUNDARY|M0 selected residual from intrinsic uniformizer data|decl|m0RowResidualRN_of_familySelection_of_intrinsic_uniformizer_data
CORRECTED RN SELECTOR BOUNDARY|M0 Artin value as exact quadratic non-norm|decl|exists_kummerRepresentative_m0UniformizerArtinBoundary
CORRECTED RN SELECTOR BOUNDARY|M0 Artin value from unramified Kummer realization|decl|m0UniformizerArtinCompatibility_of_nuUrUnramifiedKummerClass
CORRECTED RN SELECTOR BOUNDARY|M0 mod-two descent in odd residue degree|decl|redTwo_nuUr_restrict_of_odd_residueDegree
CORRECTED RN SELECTOR BOUNDARY|M0 sqrt(-3) preserves values in odd residue degree|decl|hasEqualNormValueGroups_of_sq_eq_neg_three_of_odd_residueDegree
CORRECTED RN SELECTOR BOUNDARY|M0 selected residual in odd residue degree|decl|m0RowResidualRN_of_familySelection_of_oddResidueDegree
CORRECTED RN TIED|Mpc residual (from determinant)|decl|mpcRowResidualRN_of_tied_determinant
CORRECTED RN TIED|Mpc endpoint (from determinant)|decl|mpc_candidate_equiv_galKRN_of_tied_determinant
CORRECTED RN ANALYTIC|Mpc arbitrary-h ramified compact phase|decl|hessRelZ_mpcW_ramified_compactPhase
CORRECTED RN ANALYTIC|Mpc ramified comparison from projected head phase|decl|comparison_ramified_of_headPhase_handles
CORRECTED RN ANALYTIC|Mpc arbitrary-h unramified compact phase|decl|hessRelZ_mpcW_unramified_compactPhase
CORRECTED RN ANALYTIC|Mpc unramified comparison from scaled head phase|decl|exists_comparison_unramified_of_headPhase_handles
CORRECTED RN SELECTOR BOUNDARY|Mpc scaled general-h handle correction|decl|exists_scaled_handle_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc general-h tied branch from certificate|decl|genAsmBranch_of_certificate
CORRECTED RN SELECTOR BOUNDARY|Mpc full general-h correction from scaling|decl|markedMatching_of_scaling
CORRECTED RN SELECTOR BOUNDARY|Mpc family certificate from C pivot and scaling|decl|certificate_of_familySelection
CORRECTED RN SELECTOR BOUNDARY|Mpc selected realization from C pivot and scaling|decl|realization_of_familySelection
CORRECTED RN ANALYTIC|Mpc projected display FPF resolved row|decl|exists_resolvedFamily_unramified_smul_row_fpf_of_projected
CORRECTED RN ANALYTIC|Mpc projected unramified QZero|decl|wPmpc_QZero_eq_unramifiedCompactPhase_of_projectedHeadMark
CORRECTED RN ANALYTIC|Mpc projected unramified comparison|decl|exists_comparison_unramified_of_projectedHead_handles
CORRECTED RN ANALYTIC|Mpc projected ramified QZero|decl|wPmpc_QZero_eq_ramifiedCompactPhase_of_projectedHeadMark
CORRECTED RN ANALYTIC|Mpc projected ramified comparison|decl|exists_comparison_ramified_of_projectedHead_handles
CORRECTED RN ANALYTIC|Mpc arbitrary-display boundary comparison|decl|wPmpcComparison_boundary_handles
CORRECTED RN ANALYTIC|Mpc arbitrary-display branch-free supply|decl|wPmpc_branchFreeSupply_handles
CORRECTED RN ANALYTIC|Mpc arbitrary-display affine determinant|decl|mpcAffineDeterminantCertificate_display
CORRECTED RN RECORDS|Mpc arbitrary-display certificate from determinant|decl|mpcWordCertificateRN_of_display_determinant
CORRECTED RN RECORDS|Mpc arbitrary-display certificate|decl|mpcWordCertificateRN_of_display
CORRECTED RN SELECTOR BOUNDARY|Mpc selected tied branch from C pivot and scaling|decl|mpcGenAsmBranch_of_familySelection_tied
CORRECTED RN SELECTOR BOUNDARY|Mpc selected RN residual from determinant|decl|mpcRowResidualRN_of_familySelection
CORRECTED RN SELECTOR BOUNDARY|Mpc selected RN residual (C pivot and scaling)|decl|mpcRowResidualRN_of_familySelection_closed
CORRECTED RN SELECTOR BOUNDARY|Mpc selected RN residual (canonical scaling)|decl|mpcRowResidualRN_of_familySelection_canonicalScaling
CORRECTED RN SELECTOR BOUNDARY|Mpc exact pivot has zero ordinary cup|decl|mpcPivotCupValue_eq_zero_of_exactPivot
CORRECTED RN SELECTOR BOUNDARY|Mpc exact pivot iff filtered digit|decl|mpcExactPivot_iff_filteredPivotDigit
CORRECTED RN SELECTOR BOUNDARY|Mpc selected level and filtered pivot audit|decl|mpc_familySelection_level_exact_and_pivot_iff_digit
CORRECTED RN SELECTOR BOUNDARY|Mpc exact-level counterexample to C pivot|decl|mpcFilteredLevelCounterexample_not_exactPivot
CORRECTED RN SELECTOR BOUNDARY|Mpc filtered digit iff not one level deeper|decl|mpcFilteredPivotDigit_eq_one_iff_not_deeper
CORRECTED RN SELECTOR CLOSED|Mpc epsilon-false rank-four digit|decl|mpc_familySelection_false_rankFour_digit_all
CORRECTED RN SELECTOR CLOSED|Mpc epsilon-false rank-four residual|decl|mpcRowResidualRN_of_familySelection_false_rankFour
CORRECTED RN SELECTOR BOUNDARY|Mpc epsilon-true full-schema counterexample|decl|mpcFilteredLevelCounterexample_true_selector_schema
CORRECTED RN SELECTOR BOUNDARY|Mpc epsilon-true exact B row|decl|mpc_familySelection_true_rankFour_B_exact
CORRECTED RN SELECTOR BOUNDARY|Mpc epsilon-true exact kernel from B square|decl|mpc_familySelection_true_rankFour_B_sq_exactKernel
CORRECTED RN SELECTOR BOUNDARY|Mpc epsilon-true digit-or-odd-shear criterion|decl|mpc_familySelection_true_rankFour_exists_digit_iff
CORRECTED RN SELECTOR CLOSED|Mpc epsilon-true adjusted digit|decl|mpc_familySelection_true_rankFour_exists_digit
CORRECTED RN SELECTOR CLOSED|Mpc epsilon-true exact pivot|decl|mpc_familySelection_true_rankFour_exists_exactPivot
CORRECTED RN SELECTOR CLOSED|Mpc epsilon-true rank-four residual|decl|mpcRowResidualRN_of_familySelection_true_rankFour
CORRECTED RN SELECTOR BOUNDARY|Mpc general-h odd-shear shift|decl|MpcPivShiftH
CORRECTED RN SELECTOR CLOSED|Mpc rank-four general shift|decl|mpcPivShiftH_two_zero
CORRECTED RN SELECTOR BOUNDARY|Mpc general-h epsilon-true residual from shift|decl|mpcRowResidualRN_of_familySelection_true_of_shiftH
CORRECTED RN SELECTOR BOUNDARY|Mpc unit scaling preserves exact pivot|decl|exactPivot_comp_iff_of_unit_C
CORRECTED RN SELECTOR BOUNDARY|Mpc existing clear monoid fixes C|decl|dmClearAutsWide_fixes_C
CORRECTED RN SELECTOR BOUNDARY|Mpc shift lies outside existing clear monoid|decl|not_shiftRow_of_mem_dmClearAutsWide
CORRECTED RN SELECTOR BOUNDARY|Mpc general-h shift iff full relator marking|decl|mpcPivShiftH_iff_marking
CORRECTED RN SELECTOR BOUNDARY|Mpc standard-handle extension|decl|MpcStandardHandleExtension
CORRECTED RN SELECTOR BOUNDARY|Mpc compact shift stabilization|decl|MpcPivShiftStandardStabilization
CORRECTED RN SELECTOR BOUNDARY|Mpc general-h shift from standard stabilization|decl|mpcPivShiftH_of_standardStabilization
CORRECTED RN SELECTOR BOUNDARY|Mpc standard D-defect absorption|decl|MpcStandardDDefectAbsorption
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle D-defect absorption|decl|MpcOneHandleDDefectAbsorption
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift from defect absorption|decl|mpcPivShiftH_two_one_of_compact_DDefectAbsorption
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle equation-only absorption|decl|MpcOneHandleDAbsorbable
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle lift-choice obstruction|decl|exists_nonabsorbable_with_same_lift_gen_row
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced finite-class one-handle shift|decl|mpcPivShiftH_two_one_of_balanced_forall_class
CORRECTED RN SELECTOR BOUNDARY|Mpc fixed-C full bracket surjectivity is false|decl|not_fixedCRelativeBracketSurjective
CORRECTED RN SELECTOR BOUNDARY|Mpc fixed-C neutral bracket residual|decl|FixedCRelativeNeutralBracketSurjective
CORRECTED RN SELECTOR AUDIT|Mpc fixed-C neutral bracket surjectivity is uniformly false|decl|not_fixedCRelativeNeutralBracketSurjective
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced fixed-C neutral absorber|decl|oneHandleDAbsorbable_of_balanced_fixedC_neutral
CORRECTED RN SELECTOR CLOSED|Mpc one-handle universal row lift|decl|exists_rowCorrectedLift
CORRECTED RN SELECTOR CLOSED|Mpc one-handle fibre Frattini independence|decl|oneHandleModTwoIndep_of_fibers
CORRECTED RN SELECTOR CLOSED|Mpc one-handle balanced seed|decl|exists_oneHandleBalancedSeed
CORRECTED RN SELECTOR CLOSED|Mpc one-handle core word starts in lambda2|decl|mWord_mem_two
CORRECTED RN SELECTOR CLOSED|Mpc one-handle defect starts in lambda2|decl|oneHandleDDefect_mem_two
CORRECTED RN SELECTOR CLOSED|Mpc balanced finite sets nonempty through depth two|decl|oneHandleBalancedSet_nonempty_of_le_two
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle cup-adapted seed|decl|OneHandleCupAdaptedSeed
CORRECTED RN SELECTOR CLOSED|Mpc cup-adapted relator vanishes through depth three|decl|mRelWord_mem_three_of_cupAdapted
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced depth-three set (from cup-adapted seed)|decl|oneHandleBalancedSet_three_nonempty_of_cupAdaptedSeed
CORRECTED RN SELECTOR CLOSED|Mpc one-handle cup-adapted seed exists|decl|exists_oneHandleCupAdaptedSeed
CORRECTED RN SELECTOR CLOSED|Mpc balanced finite set nonempty through depth three|decl|oneHandleBalancedSet_three_nonempty
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced multi-slot climb supply|decl|OneHandleBalancedClimbSupply
CORRECTED RN SELECTOR CLOSED|Mpc balanced one-step climb|decl|oneHandleBalancedSet_succ_of_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from balanced climb)|decl|mpcPivShiftH_two_one_of_balancedClimb
CORRECTED RN SELECTOR CLOSED|Mpc balanced correction shift equals even raw word|decl|oneHandleBalancedRelatorShift_eq_evenRawDbarWord
CORRECTED RN SELECTOR CLOSED|Mpc balanced shift iff nonlinear correction|decl|nonempty_shiftCorrection_iff_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced finite-quotient shift supply|decl|OneHandleBalancedShiftSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from finite-quotient shift)|decl|mpcPivShiftH_two_one_of_balancedShift
CORRECTED RN SELECTOR CLOSED|Mpc balanced five-factor to four-core shift equivalence|decl|nonempty_coreShiftCorrection_iff_shiftCorrection
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced constrained four-core shift supply|decl|OneHandleBalancedCoreShiftSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from four core rows)|decl|mpcPivShiftH_two_one_of_balancedCoreShift
CORRECTED RN SELECTOR CLOSED|Mpc exact relative representative lift|decl|exists_exact_relativeRepresentative
CORRECTED RN SELECTOR CLOSED|Mpc relative layer equals exact-kernel image|decl|oneHandleRelativeLambdaImage_eq_exactImage
CORRECTED RN SELECTOR CLOSED|Mpc relative-layer exact representative iff|decl|mem_oneHandleRelativeLambdaImage_iff_exists_exact
CORRECTED RN SELECTOR CLOSED|Mpc finite four-core correction type|decl|OneHandleBalancedCoreLevelCorrection
CORRECTED RN SELECTOR CLOSED|Mpc group correction iff finite four-core equation|decl|nonempty_coreShiftCorrection_iff_exists_levelCorrection
CORRECTED RN SELECTOR BOUNDARY|Mpc finite constrained four-core supply|decl|OneHandleBalancedCoreLevelSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from finite four-core equation)|decl|mpcPivShiftH_two_one_of_balancedCoreLevel
CORRECTED RN SELECTOR CLOSED|Mpc finite four-core shift homomorphism|decl|oneHandleBalancedCoreLevelShiftHom
CORRECTED RN SELECTOR CLOSED|Mpc finite equation iff target lies in range|decl|exists_levelCorrection_iff_target_mem_range
CORRECTED RN SELECTOR BOUNDARY|Mpc finite four-core range supply|decl|OneHandleBalancedCoreRangeSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from finite four-core range)|decl|mpcPivShiftH_two_one_of_balancedCoreRange
CORRECTED RN SELECTOR CLOSED|Mpc finite shift lands in relative central layer|decl|oneHandleBalancedCoreRelativeShiftHom
CORRECTED RN SELECTOR CLOSED|Mpc balanced relator target is handle-relative|decl|oneHandleBalancedCoreRelativeTarget
CORRECTED RN SELECTOR BOUNDARY|Mpc relative finite target-range supply|decl|OneHandleBalancedCoreRelativeRangeSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc relative finite surjectivity supply|decl|OneHandleBalancedCoreRelativeSurjectiveSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from relative surjectivity)|decl|mpcPivShiftH_two_one_of_balancedRelativeSurjective
CORRECTED RN SELECTOR CLOSED|Mpc relative shift range equals four-coordinate span|decl|oneHandleBalancedCoreRelativeShift_range_eq_coordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc four constrained coordinate row formulas|decl|oneHandleBalancedCoreRelativeShiftA_apply
CORRECTED RN SELECTOR BOUNDARY|Mpc four-coordinate target-span supply|decl|OneHandleBalancedCoreCoordinateSpanSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from coordinate span)|decl|mpcPivShiftH_two_one_of_balancedCoordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc constrained coordinate span lies in raw shift span|decl|oneHandleBalancedCoreCoordinateAmbientSpan_le_rawShiftSpan
CORRECTED RN SELECTOR CLOSED|Mpc finite balanced coordinate cokernel|decl|OneHandleBalancedCoreCoordinateCokernel
CORRECTED RN SELECTOR BOUNDARY|Mpc balanced coordinate obstruction vanishing|decl|OneHandleBalancedCoreCoordinateObstructionVanishing
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle shift (from coordinate obstruction)|decl|mpcPivShiftH_two_one_of_balancedCoordinateObstruction
CORRECTED RN SELECTOR CLOSED|Mpc relaxed relative C-row formula|decl|oneHandleBalancedCoreRelativeShiftCRelaxed_apply
CORRECTED RN SELECTOR CLOSED|Mpc constrained span lies in relaxed relative span|decl|oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
CORRECTED RN SELECTOR BOUNDARY|Mpc ordinary-relative coordinate coverage|decl|OneHandleBalancedCoreRelativeCoordinateSpanSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc neutral-C obstruction vanishing|decl|OneHandleBalancedCoreNeutralityObstructionVanishing
CORRECTED RN SELECTOR CLOSED|Mpc coordinate supply iff relative plus neutral|decl|coordinateSpanSupply_iff_relative_and_neutrality
CORRECTED RN SELECTOR CLOSED|Mpc neutral quotient generated by relaxed C|decl|oneHandleBalancedCoreNeutralityClassHom_surjective
CORRECTED RN SELECTOR CLOSED|Mpc relaxed C class kernel criterion|decl|oneHandleBalancedCoreNeutralityClassHom_eq_one_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc neutral obstruction as one C class|decl|neutralityObstruction_eq_one_iff_exists_relativeC_kernel
CORRECTED RN SELECTOR CLOSED|Mpc relative C modulo neutral source|decl|OneHandleRelativeCModuloNeutral
CORRECTED RN SELECTOR CLOSED|Mpc C-mod-neutral source surjects|decl|oneHandleBalancedCoreNeutralitySourceFactor_surjective
CORRECTED RN SELECTOR BOUNDARY|Mpc C-mod-neutral interaction kernel|decl|oneHandleBalancedCoreNeutralitySourceFactor_eq_one_iff
CORRECTED RN SELECTOR CLOSED|Mpc neutrality cokernel exact source quotient|decl|oneHandleBalancedCoreNeutralityCokernelEquiv
CORRECTED RN SELECTOR CLOSED|Mpc constrained span equals ABD plus neutral C|decl|oneHandleBalancedCoreCoordinateSpan_eq_other_sup_C
CORRECTED RN SELECTOR CLOSED|Mpc interaction kernel equals C-versus-ABD image|decl|oneHandleBalancedCoreNeutralityInteraction_range_eq
CORRECTED RN SELECTOR BOUNDARY|Mpc finite C-versus-ABD relation source|decl|oneHandleBalancedCoreNeutralityInteractionSource
CORRECTED RN SELECTOR CLOSED|Mpc neutrality cokernel modulo C-versus-ABD|decl|oneHandleBalancedCoreNeutralityCokernelEquivInteraction
CORRECTED RN SELECTOR CLOSED|Mpc interaction source iff literal CABD equation|decl|mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc target neutralization by literal CABD equation|decl|neutralityObstruction_eq_one_iff_CABD
CORRECTED RN SELECTOR CLOSED|Mpc CABD square-commutator expansion|decl|balancedCABD_eq_iff_expanded
CORRECTED RN SELECTOR BOUNDARY|Mpc expanded neutral-C target equation|decl|neutralityObstruction_eq_one_iff_expanded_CABD
CORRECTED RN SELECTOR CLOSED|Mpc multiplicative CABD defect row|decl|oneHandleBalancedCABDDefect
CORRECTED RN SELECTOR CLOSED|Mpc CABD equation as additive zero row|decl|balancedCABD_eq_iff_addRow_eq_zero
CORRECTED RN SELECTOR BOUNDARY|Mpc additive CABD solution kernel|decl|oneHandleBalancedCABDAddKernel
CORRECTED RN SELECTOR CLOSED|Mpc combined CABD finite system|decl|oneHandleBalancedCABDAddSystem
CORRECTED RN SELECTOR CLOSED|Mpc combined CABD literal range criterion|decl|mem_oneHandleBalancedCABDSystem_range_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc neutrality as additive target-in-range|decl|neutralityObstruction_eq_one_iff_mem_CABDAddSystem_range
CORRECTED RN SELECTOR CLOSED|Mpc CABD source exponent four|decl|oneHandleBalancedCABDData_four_nsmul
CORRECTED RN SELECTOR CLOSED|Mpc CABD ZMod-four linear system|decl|oneHandleBalancedCABDZModFourSystem
CORRECTED RN SELECTOR BOUNDARY|Mpc neutrality as ZMod-four target-in-range|decl|neutralityObstruction_eq_one_iff_mem_CABDZModFourSystem_range
CORRECTED RN SELECTOR CLOSED|Mpc finite ZMod-four CABD cokernel|decl|OneHandleBalancedCABDZModFourCokernel
CORRECTED RN SELECTOR CLOSED|Mpc canonical linear CABD obstruction|decl|oneHandleBalancedCABDZModFourObstruction
CORRECTED RN SELECTOR BOUNDARY|Mpc neutrality as linear obstruction vanishing|decl|neutralityObstruction_eq_one_iff_CABDZModFourObstruction_eq_zero
CORRECTED RN SELECTOR CLOSED|Mpc row neutrality iff abelian square one|decl|mem_oneHandleRowKer_iff_abMk_sq_eq_one
CORRECTED RN SELECTOR CLOSED|Mpc relative row neutrality iff abelianization trivial|decl|mem_oneHandleRowKer_iff_abMk_eq_one_of_forget
CORRECTED RN SELECTOR CLOSED|Mpc neutral relative source as abelianization kernel|decl|oneHandleNeutralRelativeLambdaImage_eq_abMkKernel
CORRECTED RN SELECTOR CLOSED|Mpc neutral source equals handle-digit kernel|decl|oneHandleRelativeUVLevel_ker_eq_neutralRange
CORRECTED RN SELECTOR CLOSED|Mpc C-mod-neutral source equals handle-digit range|decl|oneHandleRelativeCModuloNeutralEquivUVRange
CORRECTED RN SELECTOR CLOSED|Mpc C-mod-neutral source is ZMod-four squared|decl|oneHandleRelativeCModuloNeutralEquivZModFourSq
CORRECTED RN SELECTOR CLOSED|Mpc C-mod-neutral source has cardinality sixteen|decl|natCard_oneHandleRelativeCModuloNeutral
CORRECTED RN SELECTOR CLOSED|Mpc handle-coordinate kernel equals neutral range|decl|oneHandleRelativeCCoordinates_ker_eq_neutralRange
CORRECTED RN SELECTOR CLOSED|Mpc unique deep-handle normal form|decl|existsUnique_deepRelativeClass_mod_neutral
CORRECTED RN SELECTOR BOUNDARY|Mpc CABD obstruction in explicit handle coordinates|decl|neutralityObstruction_eq_one_iff_CABD_coordinates
CORRECTED RN SELECTOR CLOSED|Mpc neutrality cokernel is coordinate-interaction quotient|decl|oneHandleBalancedCoreNeutralityCokernelEquivCoordinates
CORRECTED RN SELECTOR CLOSED|Mpc neutrality cokernel order divides sixteen|decl|natCard_oneHandleBalancedCoreNeutralityCokernel_dvd_sixteen
CORRECTED RN SELECTOR BOUNDARY|Mpc neutrality vanishes iff its digit pair is an interaction row|decl|neutralityObstruction_eq_one_iff_coordinateInteraction
CORRECTED RN SELECTOR CLOSED|Mpc digit plane generated by standard U and V rows|decl|coordinateSubgroup_eq_top_iff_generators
CORRECTED RN SELECTOR BOUNDARY|Mpc interaction fills digit plane iff two CABD equations|decl|oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_top_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle pivot from relative coverage and two digit equations|decl|mpcPivShiftH_two_one_of_balancedRelative_and_coordinateGenerators
CORRECTED RN SELECTOR CLOSED|Mpc parity image fills iff full digit image fills|decl|oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc parity interaction supply|decl|OneHandleBalancedCoreNeutralityParitySupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle pivot from relative coverage and parity|decl|mpcPivShiftH_two_one_of_balancedRelative_and_parity
CORRECTED RN SELECTOR CLOSED|Mpc parity plane detected by three scalar characters|decl|paritySubgroup_eq_top_iff_characterMaps
CORRECTED RN SELECTOR CLOSED|Mpc parity failure iff a scalar annihilates every CABD row|decl|oneHandleBalancedCoreNeutralityParityRow_ne_top_iff_scalarAnnihilator
CORRECTED RN SELECTOR BOUNDARY|Mpc three-character neutrality supply|decl|OneHandleBalancedCoreNeutralityCharacterSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle pivot from relative coverage and characters|decl|mpcPivShiftH_two_one_of_balancedRelative_and_characters
CORRECTED RN SELECTOR CLOSED|Mpc next balanced stage iff one selected target is covered|decl|oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
CORRECTED RN SELECTOR BOUNDARY|Mpc selected coordinate-span supply|decl|OneHandleBalancedCoreCoordinateSelectableSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc selected relative and three-character supply|decl|OneHandleBalancedCoreRelativeCharacterSelectableSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle pivot from selected character points|decl|mpcPivShiftH_two_one_of_selectableCharacters
CORRECTED RN SELECTOR CLOSED|Mpc target vanishing iff every cokernel character kills it|decl|targetCharacterVanishing_iff_coordinateSpan
CORRECTED RN SELECTOR BOUNDARY|Mpc target-character selectable supply|decl|OneHandleBalancedCoreTargetCharacterSelectableSupply
CORRECTED RN SELECTOR CLOSED|Mpc target-character selection iff balanced successor|decl|targetCharacterSelectableSupply_iff_successor
CORRECTED RN SELECTOR BOUNDARY|Mpc one-handle pivot from target characters|decl|mpcPivShiftH_two_one_of_targetCharacters
CORRECTED RN SELECTOR CLOSED|Mpc target detected iff selected coordinate failure|decl|targetCharacterDetected_iff_not_coordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc next-stage emptiness iff pointwise character obstruction|decl|oneHandleBalancedSet_succ_empty_iff_pointwise_characterObstruction
CORRECTED RN SELECTOR CLOSED|Mpc mod-four plane characters have two coefficients|decl|exists_eq_oneHandleZModFourPlaneCharacter
CORRECTED RN SELECTOR BOUNDARY|Mpc finite target-coefficient detector|decl|OneHandleBalancedCoreTargetCoefficientDetected
CORRECTED RN SELECTOR CLOSED|Mpc coefficient detector iff character detector|decl|targetCoefficientDetected_iff_characterDetected
CORRECTED RN SELECTOR CLOSED|Mpc coefficient detector iff selected coordinate failure|decl|targetCoefficientDetected_iff_not_coordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc next-stage emptiness iff pointwise coefficient obstruction|decl|oneHandleBalancedSet_succ_empty_iff_pointwise_coefficientObstruction
CORRECTED RN SELECTOR CLOSED|Mpc plane character equals primitive character of dot product|decl|oneHandleZModFourPlaneCharacter_eq_zmod_dot
CORRECTED RN SELECTOR CLOSED|Mpc plane character is one iff dot product vanishes|decl|oneHandleZModFourPlaneCharacter_eq_one_iff_dot_eq_zero
CORRECTED RN SELECTOR BOUNDARY|Mpc finite target dot-product detector|decl|OneHandleBalancedCoreTargetDotDetected
CORRECTED RN SELECTOR CLOSED|Mpc dot detector iff selected coordinate failure|decl|targetDotDetected_iff_not_coordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc next-stage emptiness iff pointwise dot obstruction|decl|oneHandleBalancedSet_succ_empty_iff_pointwise_dotObstruction
CORRECTED RN SELECTOR CLOSED|Mpc nonzero mod-four coefficients split into nine directions|decl|nonzero_coefficients_classification
CORRECTED RN SELECTOR BOUNDARY|Mpc finite nine-direction target detector|decl|OneHandleBalancedCoreTargetDirectionCaseDetected
CORRECTED RN SELECTOR CLOSED|Mpc nine-direction detector iff selected coordinate failure|decl|targetDirectionCaseDetected_iff_not_coordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc next-stage emptiness iff pointwise nine-direction obstruction|decl|oneHandleBalancedSet_succ_empty_iff_pointwise_directionCaseObstruction
CORRECTED RN SELECTOR CLOSED|Mpc parity target nonmembership iff one of three characters detects|decl|parityTarget_not_mem_iff_directionCharacter
CORRECTED RN SELECTOR CLOSED|Mpc even direction detector iff target parity misses interaction range|decl|parityDirectionDetected_iff_targetParity_not_mem
CORRECTED RN SELECTOR BOUNDARY|Mpc primitive order-four target case|decl|OneHandleBalancedCoreTargetPrimitiveCaseDetected
CORRECTED RN SELECTOR BOUNDARY|Mpc parity-visible target case|decl|OneHandleBalancedCoreTargetParityCaseDetected
CORRECTED RN SELECTOR CLOSED|Mpc selected coordinate failure iff primitive or parity case|decl|target_not_coordinateSpan_iff_primitive_or_parity
CORRECTED RN SELECTOR BOUNDARY|Mpc selected target parity coverage|decl|OneHandleBalancedCoreTargetParityCovered
CORRECTED RN SELECTOR CLOSED|Mpc target parity coverage is lift-independent|decl|targetParityCovered_preimage_iff
CORRECTED RN SELECTOR CLOSED|Mpc parity case iff target parity coverage fails|decl|targetParityCaseDetected_iff_not_parityCovered
CORRECTED RN SELECTOR CLOSED|Mpc coordinate failure iff primitive or parity coverage fails|decl|target_not_coordinateSpan_iff_primitive_or_not_parityCovered
CORRECTED RN SELECTOR CLOSED|Mpc canonical target parity cokernel|decl|OneHandleBalancedCoreTargetParityCokernel
CORRECTED RN SELECTOR CLOSED|Mpc canonical target parity obstruction|decl|oneHandleBalancedCoreTargetParityObstruction
CORRECTED RN SELECTOR CLOSED|Mpc parity obstruction is independent of the chosen lift|decl|oneHandleBalancedCoreTargetParityObstruction_eq_mk_of_factor
CORRECTED RN SELECTOR CLOSED|Mpc target parity coverage iff obstruction vanishes|decl|targetParityCovered_iff_obstruction_eq_one
CORRECTED RN SELECTOR CLOSED|Mpc coordinate failure iff primitive or parity obstruction|decl|target_not_coordinateSpan_iff_primitive_or_parityObstruction
CORRECTED RN SELECTOR CLOSED|Mpc parity character value is lift-independent|decl|targetParityCharacter_eq_of_factor_eq
CORRECTED RN SELECTOR BOUNDARY|Mpc target parity character compatibility|decl|OneHandleBalancedCoreTargetParityCharacterCompatible
CORRECTED RN SELECTOR CLOSED|Mpc parity obstruction iff one of three characters detects|decl|targetParityObstruction_ne_one_iff_characterDetected
CORRECTED RN SELECTOR CLOSED|Mpc parity coverage iff all three characters are compatible|decl|targetParityCovered_iff_characterCompatible
CORRECTED RN SELECTOR CLOSED|Mpc coordinate failure iff primitive or parity character|decl|target_not_coordinateSpan_iff_primitive_or_characterDetected
CORRECTED RN SELECTOR CLOSED|Mpc selected target ordinary-C representative|decl|oneHandleBalancedCoreTargetCRepresentative
CORRECTED RN SELECTOR CLOSED|Mpc target parity character equals explicit C coordinates|decl|targetParityCharacter_eq_CRepresentative
CORRECTED RN SELECTOR BOUNDARY|Mpc three scalar target CABD implications|decl|OneHandleBalancedCoreTargetParityCABDCompatible
CORRECTED RN SELECTOR CLOSED|Mpc parity coverage iff scalar CABD compatibility|decl|targetParityCovered_iff_CABDCompatible
CORRECTED RN SELECTOR BOUNDARY|Mpc six primitive target CABD implications|decl|OneHandleBalancedCoreTargetPrimitiveCABDCompatible
CORRECTED RN SELECTOR CLOSED|Mpc primitive detection iff primitive CABD failure|decl|targetPrimitiveCaseDetected_iff_not_CABDCompatible
CORRECTED RN SELECTOR CLOSED|Mpc target span iff nine scalar CABD implications|decl|target_mem_coordinateSpan_iff_parity_and_primitive_CABD
CORRECTED RN SELECTOR BOUNDARY|Mpc stagewise nine-CABD selectable supply|decl|OneHandleBalancedCoreTargetCABDSelectableSupply
CORRECTED RN SELECTOR CLOSED|Mpc successor iff a nine-CABD target exists|decl|oneHandleBalancedSet_succ_nonempty_iff_exists_targetCABD
CORRECTED RN SELECTOR CLOSED|Mpc nine-CABD supply iff coordinate supply|decl|targetCABDSelectableSupply_iff_coordinateSelectableSupply
CORRECTED RN SELECTOR CLOSED|Mpc nine-CABD supply gives every finite stage|decl|oneHandleBalancedSet_nonempty_all_of_targetCABDSelectable
CORRECTED RN SELECTOR CLOSED|Mpc nine-CABD supply gives one-handle shift|decl|mpcPivShiftH_two_one_of_targetCABDSelectable
CORRECTED RN SELECTOR BOUNDARY|Mpc literal one-of-nine CABD target detector|decl|OneHandleBalancedCoreTargetCABDDetected
CORRECTED RN SELECTOR CLOSED|Mpc CABD detection iff nine-check failure|decl|targetCABDDetected_iff_not_compatible
CORRECTED RN SELECTOR CLOSED|Mpc successor failure iff pointwise CABD obstruction|decl|oneHandleBalancedSet_succ_empty_iff_pointwise_CABDObstruction
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W4 relator lies in lambda four|decl|oneHandleW4Mark_relator_mem_four
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W4 marking is mod-two independent|decl|oneHandleW4Mark_modTwoIndep
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W4 marking topologically generates|decl|oneHandleW4Mark_topGen
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W4 marking preserves chi|decl|oneHandleW4Mark_chi
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W4 marking has C plus two B row|decl|oneHandleW4Mark_C_row
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W4 static seed packet|decl|oneHandleW4Mark_seed
CORRECTED RN SELECTOR CLOSED|Mpc direct one-handle fourth stage is nonempty|decl|oneHandleDirectSet_four_nonempty
CORRECTED RN SELECTOR CLOSED|Mpc direct one-handle stages are closed|decl|oneHandleDirectSet_isClosed
CORRECTED RN SELECTOR CLOSED|Mpc direct finite stages give one-handle shift|decl|mpcPivShiftH_two_one_of_direct_finite_stages
CORRECTED RN SELECTOR BOUNDARY|Mpc direct one-handle successor supply|decl|OneHandleDirectSuccessorSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct successor gives every finite stage|decl|oneHandleDirectSet_nonempty_all
CORRECTED RN SELECTOR CLOSED|Mpc direct successor gives one-handle shift|decl|mpcPivShiftH_two_one_of_direct_successor
CORRECTED RN SELECTOR BOUNDARY|Mpc direct four-core correction|decl|OneHandleDirectCorrection
CORRECTED RN SELECTOR CLOSED|Mpc direct relator shift formula|decl|oneHandleDirectRelatorShift_eq
CORRECTED RN SELECTOR CLOSED|Mpc direct correction preserves independence|decl|oneHandleDirectModify_modTwoIndep
CORRECTED RN SELECTOR CLOSED|Mpc direct correction produces successor|decl|OneHandleDirectCorrection.toSuccessor
CORRECTED RN SELECTOR BOUNDARY|Mpc direct correction supply|decl|OneHandleDirectCorrectionSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct correction supply gives shift|decl|mpcPivShiftH_two_one_of_direct_correctionSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct chi-neutral finite coordinate image|decl|oneHandleDirectLambdaImage
CORRECTED RN SELECTOR CLOSED|Mpc direct finite four-coordinate source|decl|OneHandleDirectLevelCorrection
CORRECTED RN SELECTOR CLOSED|Mpc direct correction iff finite equation|decl|nonempty_directCorrection_iff_exists_levelCorrection
CORRECTED RN SELECTOR CLOSED|Mpc direct finite crossed-derivation homomorphism|decl|oneHandleDirectLevelShiftHom
CORRECTED RN SELECTOR CLOSED|Mpc direct correction iff target in finite range|decl|nonempty_directCorrection_iff_target_mem_range
CORRECTED RN SELECTOR BOUNDARY|Mpc direct finite range supply|decl|OneHandleDirectFiniteRangeSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct finite range gives shift|decl|mpcPivShiftH_two_one_of_directFiniteRange
CORRECTED RN SELECTOR CLOSED|Mpc direct finite range equals four-row span|decl|oneHandleDirectLevelShift_range_eq_coordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc direct A square-and-two-brackets row|decl|oneHandleDirectShiftA_apply
CORRECTED RN SELECTOR CLOSED|Mpc direct B bracket row|decl|oneHandleDirectShiftB_apply
CORRECTED RN SELECTOR CLOSED|Mpc direct C bracket row|decl|oneHandleDirectShiftC_apply
CORRECTED RN SELECTOR CLOSED|Mpc direct D bracket row|decl|oneHandleDirectShiftD_apply
CORRECTED RN SELECTOR BOUNDARY|Mpc direct four-row coordinate span supply|decl|OneHandleDirectCoordinateSpanSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct coordinate span gives shift|decl|mpcPivShiftH_two_one_of_directCoordinateSpan
CORRECTED RN SELECTOR CLOSED|Mpc direct coordinate cokernel is finite|decl|oneHandleDirectCoordinateCokernel_finite
CORRECTED RN SELECTOR CLOSED|Mpc direct obstruction vanishes iff target is spanned|decl|oneHandleDirectCoordinateObstruction_eq_one_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc direct finite obstruction vanishing|decl|OneHandleDirectCoordinateObstructionVanishing
CORRECTED RN SELECTOR CLOSED|Mpc direct obstruction vanishing gives shift|decl|mpcPivShiftH_two_one_of_directCoordinateObstruction
CORRECTED RN SELECTOR CLOSED|Mpc direct characters vanish iff correction exists|decl|directTargetCharacterVanishing_iff_nonempty_correction
CORRECTED RN SELECTOR CLOSED|Mpc direct detecting character iff no correction|decl|directTargetCharacterDetected_iff_no_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc direct target-character vanishing supply|decl|OneHandleDirectTargetCharacterVanishingSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct target characters give shift|decl|mpcPivShiftH_two_one_of_directTargetCharacters
CORRECTED RN SELECTOR CLOSED|Mpc direct cokernel has exponent two|decl|oneHandleDirectCoordinateCokernel_add_self
CORRECTED RN SELECTOR CLOSED|Mpc direct F2 dual vanishing iff correction exists|decl|directTargetF2Vanishing_iff_nonempty_correction
CORRECTED RN SELECTOR CLOSED|Mpc direct F2 detector iff no correction|decl|directTargetF2Detected_iff_no_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc direct F2 target-vanishing supply|decl|OneHandleDirectTargetF2VanishingSupply
CORRECTED RN SELECTOR CLOSED|Mpc direct F2 dual gives shift|decl|mpcPivShiftH_two_one_of_directTargetF2
CORRECTED RN SELECTOR CLOSED|Mpc ambient F2 vanishing iff correction exists|decl|directTargetAmbientF2Vanishing_iff_nonempty_correction
CORRECTED RN SELECTOR CLOSED|Mpc ambient F2 detector iff no correction|decl|directTargetAmbientF2Detected_iff_no_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc ambient F2 target-vanishing supply|decl|OneHandleDirectTargetAmbientF2VanishingSupply
CORRECTED RN SELECTOR CLOSED|Mpc ambient F2 dual gives shift|decl|mpcPivShiftH_two_one_of_directTargetAmbientF2
CORRECTED RN SELECTOR CLOSED|Mpc four coordinate rows equal span annihilation|decl|coordinateRowsAnnihilate_iff_spanAnnihilates
CORRECTED RN SELECTOR CLOSED|Mpc coordinate F2 vanishing iff correction exists|decl|directTargetCoordinateF2Vanishing_iff_nonempty_correction
CORRECTED RN SELECTOR CLOSED|Mpc coordinate F2 detector iff no correction|decl|directTargetCoordinateF2Detected_iff_no_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc coordinate F2 target-vanishing supply|decl|OneHandleDirectTargetCoordinateF2VanishingSupply
CORRECTED RN SELECTOR CLOSED|Mpc coordinate F2 dual gives shift|decl|mpcPivShiftH_two_one_of_directTargetCoordinateF2
CORRECTED RN SELECTOR CLOSED|Mpc direct transpose kernel equals four equations|decl|coordinateTranspose_eq_zero_iff_rowsAnnihilate
CORRECTED RN SELECTOR CLOSED|Mpc transpose target vanishing iff correction exists|decl|directTargetTransposeVanishing_iff_nonempty_correction
CORRECTED RN SELECTOR CLOSED|Mpc transpose detector iff no correction|decl|directTargetTransposeDetected_iff_no_correction
CORRECTED RN SELECTOR BOUNDARY|Mpc transpose target-vanishing supply|decl|OneHandleDirectTargetTransposeVanishingSupply
CORRECTED RN SELECTOR CLOSED|Mpc transpose target vanishing gives shift|decl|mpcPivShiftH_two_one_of_directTargetTranspose
CORRECTED RN SELECTOR CLOSED|Mpc augmented transpose kernel lies in row kernel|decl|augmentedTranspose_ker_le_coordinateTranspose_ker
CORRECTED RN SELECTOR CLOSED|Mpc augmented kernel equality iff correction exists|decl|nonempty_directCorrection_iff_augmentedTranspose_ker_eq
CORRECTED RN SELECTOR CLOSED|Mpc strict augmented kernel detects failure|decl|directTargetTransposeDetected_iff_ker_lt
CORRECTED RN SELECTOR BOUNDARY|Mpc augmented-transpose kernel supply|decl|OneHandleDirectAugmentedTransposeKernelSupply
CORRECTED RN SELECTOR CLOSED|Mpc augmented-transpose kernels give shift|decl|mpcPivShiftH_two_one_of_augmentedTransposeKernels
CORRECTED RN SELECTOR CLOSED|Mpc augmented kernel equality iff equal cardinality|decl|augmentedTranspose_ker_eq_iff_card_eq
CORRECTED RN SELECTOR CLOSED|Mpc direct correction iff equal kernel cardinalities|decl|nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq
CORRECTED RN SELECTOR CLOSED|Mpc unequal kernel cardinalities detect failure|decl|directTargetTransposeDetected_iff_kernelCard_ne
CORRECTED RN SELECTOR BOUNDARY|Mpc augmented-transpose rank supply|decl|OneHandleDirectAugmentedTransposeRankSupply
CORRECTED RN SELECTOR CLOSED|Mpc augmented-transpose ranks give shift|decl|mpcPivShiftH_two_one_of_augmentedTransposeRanks
CORRECTED RN SELECTOR CLOSED|Mpc augmented image rank equals nullity criterion|decl|augmentedTranspose_rangeCard_eq_iff_kernelCard_eq
CORRECTED RN SELECTOR CLOSED|Mpc direct correction iff equal image ranks|decl|nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq
CORRECTED RN SELECTOR CLOSED|Mpc unequal image ranks detect failure|decl|directTargetTransposeDetected_iff_rangeCard_ne
CORRECTED RN SELECTOR BOUNDARY|Mpc augmented-transpose image-rank supply|decl|OneHandleDirectAugmentedTransposeImageRankSupply
CORRECTED RN SELECTOR CLOSED|Mpc augmented image ranks give shift|decl|mpcPivShiftH_two_one_of_augmentedTransposeImageRanks
CORRECTED RN SELECTOR CLOSED|Mpc coordinate transpose image cardinality from finrank|decl|coordinateTranspose_rangeCard_eq_pow_rank
CORRECTED RN SELECTOR CLOSED|Mpc augmented transpose image cardinality from finrank|decl|augmentedTranspose_rangeCard_eq_pow_rank
CORRECTED RN SELECTOR CLOSED|Mpc direct correction iff equal finranks|decl|nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc unequal finranks detect failure|decl|directTargetTransposeDetected_iff_finrank_ne
CORRECTED RN SELECTOR BOUNDARY|Mpc augmented-transpose finrank supply|decl|OneHandleDirectAugmentedTransposeFinrankSupply
CORRECTED RN SELECTOR CLOSED|Mpc augmented finranks give shift|decl|mpcPivShiftH_two_one_of_augmentedTransposeFinranks
CORRECTED RN SELECTOR CLOSED|Mpc coordinate rank is at most augmented rank|decl|coordinateTransposeRank_le_augmentedTransposeRank
CORRECTED RN SELECTOR CLOSED|Mpc augmented rank rises by at most one|decl|augmentedTransposeRank_le_coordinateTransposeRank_add_one
CORRECTED RN SELECTOR CLOSED|Mpc augmented rank has zero-or-one jump|decl|augmentedTransposeRank_eq_or_eq_add_one
CORRECTED RN SELECTOR CLOSED|Mpc direct obstruction iff rank jumps by one|decl|directTargetTransposeDetected_iff_finrank_jump_one
CORRECTED RN SELECTOR CLOSED|Mpc target row span iff direct correction|decl|targetRowSpan_iff_nonempty_directCorrection
CORRECTED RN SELECTOR CLOSED|Mpc target row span iff no rank jump|decl|targetRowSpan_iff_no_finrank_jump
CORRECTED RN SELECTOR CLOSED|Mpc target outside row span iff obstruction|decl|directTargetTransposeDetected_iff_not_rowSpan
CORRECTED RN SELECTOR BOUNDARY|Mpc direct target row-span supply|decl|OneHandleDirectTargetRowSpanSupply
CORRECTED RN SELECTOR CLOSED|Mpc target row-span supply gives shift|decl|mpcPivShiftH_two_one_of_targetRowSpan
CORRECTED RN SELECTOR CLOSED|Mpc scalar row coefficients iff row span|decl|targetRowCoefficients_iff_rowSpan
CORRECTED RN SELECTOR CLOSED|Mpc scalar row coefficients iff correction|decl|targetRowCoefficients_iff_nonempty_directCorrection
CORRECTED RN SELECTOR CLOSED|Mpc scalar row coefficients iff no rank jump|decl|targetRowCoefficients_iff_no_finrank_jump
CORRECTED RN SELECTOR BOUNDARY|Mpc direct target row-coefficient supply|decl|OneHandleDirectTargetRowCoefficientSupply
CORRECTED RN SELECTOR CLOSED|Mpc target row coefficients give shift|decl|mpcPivShiftH_two_one_of_targetRowCoefficients
CORRECTED RN SELECTOR BOUNDARY|Mpc selectable direct correction supply|decl|OneHandleDirectSelectableCorrectionSupply
CORRECTED RN SELECTOR CLOSED|Mpc selectable correction gives direct successor|decl|directSuccessorSupply_of_selectableCorrectionSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc selectable zero-finrank-jump supply|decl|OneHandleDirectSelectableFinrankSupply
CORRECTED RN SELECTOR BOUNDARY|Mpc selectable row-coefficient supply|decl|OneHandleDirectSelectableRowCoefficientSupply
CORRECTED RN SELECTOR CLOSED|Mpc selectable row coefficients iff finranks|decl|selectableRowCoefficientSupply_iff_selectableFinrankSupply
CORRECTED RN SELECTOR CLOSED|Mpc selectable row coefficients give shift|decl|mpcPivShiftH_two_one_of_selectableRowCoefficients
CORRECTED RN SELECTOR CLOSED|Mpc next direct stage iff some point corrects|decl|oneHandleDirectSet_succ_nonempty_iff_exists_correction
CORRECTED RN SELECTOR CLOSED|Mpc next direct stage iff some rank jump vanishes|decl|oneHandleDirectSet_succ_nonempty_iff_exists_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc next direct stage iff some row coefficients exist|decl|oneHandleDirectSet_succ_nonempty_iff_exists_rowCoefficients
CORRECTED RN SELECTOR CLOSED|Mpc selectable correction iff direct successor|decl|selectableCorrectionSupply_iff_successorSupply
CORRECTED RN SELECTOR CLOSED|Mpc selectable finranks iff direct successor|decl|selectableFinrankSupply_iff_successorSupply
CORRECTED RN SELECTOR CLOSED|Mpc selectable row coefficients iff direct successor|decl|selectableRowCoefficientSupply_iff_successorSupply
CORRECTED RN SELECTOR CLOSED|Mpc explicit one-handle W4 correction|decl|oneHandleW4Correction
CORRECTED RN SELECTOR CLOSED|Mpc direct one-handle fifth stage is nonempty|decl|oneHandleDirectSet_five_nonempty
CORRECTED RN SELECTOR CLOSED|Mpc W4 direct augmented rank does not jump|decl|oneHandleW4Mark_augmentedTranspose_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc W4 direct target row coefficients|decl|oneHandleW4Mark_targetRowCoefficients
CORRECTED RN SELECTOR CLOSED|Mpc exact one-handle W5 class-six defect|decl|oneHandleW5Mark_defect_six
CORRECTED RN SELECTOR CLOSED|Mpc W5 correction target is explicit|decl|oneHandleW5_target_value
CORRECTED RN SELECTOR CLOSED|Mpc W5 correctability iff no rank jump|decl|oneHandleW5Correctable_iff_finrank_eq
CORRECTED RN SELECTOR BOUNDARY|Mpc W5-to-W6 correction interface|decl|OneHandleW5Correctable
CORRECTED RN SELECTOR CLOSED|Mpc lifted compact C6 factors are legal|decl|oneHandleC6Factors_depth
CORRECTED RN SELECTOR CLOSED|Mpc lifted compact C6 relator forgets to zero|decl|dmForgetHandles_oneHandleC6Relator_mem
CORRECTED RN SELECTOR CLOSED|Mpc lifted C6 residual lies in relative layer|decl|oneHandleC6Residual_mem_relativeLayer
CORRECTED RN SELECTOR CLOSED|Mpc compact C6 candidate kills iff residual vanishes|decl|oneHandleC6CertificateKill_iff_residual_eq_one
CORRECTED RN SELECTOR BOUNDARY|Mpc compact-lift one-handle C6 certificate|decl|OneHandleC6CertificateKill
CORRECTED RN SELECTOR CLOSED|Mpc relation-free C6 certificate cancellation|decl|eval_certificateWord_mul_relationProduct_eq_one_noRel
CORRECTED RN SELECTOR CLOSED|Mpc explicit one-handle W5-to-W6 correction|decl|oneHandleW5ClassSixCorrection
CORRECTED RN SELECTOR CLOSED|Mpc one-handle W5 marking is correctable|decl|oneHandleW5Correctable
CORRECTED RN SELECTOR CLOSED|Mpc direct one-handle sixth stage is nonempty|decl|oneHandleDirectSet_six_nonempty
CORRECTED RN SELECTOR CLOSED|Mpc exact one-handle W6 class-seven defect|decl|oneHandleW6Mark_defect_seven
CORRECTED RN SELECTOR CLOSED|Mpc compact W6 marking has class-seven supply|decl|compactC7_fullSupply
CORRECTED RN SELECTOR CLOSED|Mpc class-seven pivot factor lifts to one handle|decl|exists_oneHandlePivotLift
CORRECTED RN SELECTOR CLOSED|Mpc class-seven compact correction lifts to one handle|decl|exists_oneHandleC7RelativeLift
CORRECTED RN SELECTOR CLOSED|Mpc lifted class-seven defect is purely relative|decl|OneHandleC7RelativeLift.residual_mem_relativeLayer
CORRECTED RN SELECTOR BOUNDARY|Mpc W6-to-W7 relative residual criterion|decl|oneHandleW6Correctable_iff_relativeResidual
CORRECTED RN SELECTOR BOUNDARY|Mpc W6-to-W7 finite relative range criterion|decl|oneHandleW6Correctable_iff_exists_relativeCorrectable
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 relative shift homomorphism|decl|oneHandleW6RelativeShiftHom
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 relative target range membership|decl|relativeCorrectable_iff_target_mem_range
CORRECTED RN SELECTOR CLOSED|Mpc W6 relative shift is standard-base shift|decl|oneHandleW6RelativeShiftHom_eq_standard
CORRECTED RN SELECTOR CLOSED|Mpc W6 relative range is four standard rows|decl|oneHandleStandardRelativeShift_range_eq_coordinateSpan
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 relative target is relaxed coverage plus neutral C|decl|relativeCorrectable_iff_relaxed_and_neutrality
CORRECTED RN SELECTOR CLOSED|Mpc W6 ordinary relative span has four F2 rows|decl|standardRelativeRowsAnnihilate_iff_spanAnnihilates
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 ordinary relative target transpose|decl|standardRelativeTargetTransposeVanishing_iff_target_mem_relaxed
CORRECTED RN SELECTOR CLOSED|Mpc W6 ordinary relative target vanishing iff equal kernels|decl|standardRelativeTargetTransposeVanishing_iff_ker_eq
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 ordinary relative target iff no F2 rank jump|decl|standardRelativeTarget_mem_relaxed_iff_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc W6 ordinary relative augmented rank has two cases|decl|standardRelativeAugmentedRank_eq_or_eq_add_one
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 ordinary relative failure iff one-bit rank jump|decl|standardRelativeTargetDetected_iff_rankJump_one
CORRECTED RN SELECTOR CLOSED|Mpc W6 ordinary relative span iff literal row equation|decl|standardRelativeTarget_mem_relaxed_iff_rowEquation
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 ordinary relative rank jump zero iff row equation|decl|standardRelativeRankJump_zero_iff_rowEquation
CORRECTED RN SELECTOR CLOSED|Mpc W6 relative target changes by standard shift under relift|decl|relativeTarget_eq_standardShift_inv_mul
CORRECTED RN SELECTOR CLOSED|Mpc W6 relative rank jump is lift-independent over compact packet|decl|relativeRankJump_eq_of_compactFactors_eq
CORRECTED RN SELECTOR CLOSED|Mpc W6 relaxed obstruction descends to compact factors mod lambda7|decl|relativeObstruction_eq_of_sameCompactLevelSeven
CORRECTED RN SELECTOR CLOSED|Mpc W6 row equation descends to compact factors mod lambda7|decl|relativeRowEquation_iff_of_sameCompactLevelSeven
CORRECTED RN SELECTOR CLOSED|Mpc W6 finite compact obstruction-value set|decl|compactPacketObstructionValues
CORRECTED RN SELECTOR BOUNDARY|Mpc W6 finite compact identity-value criterion|decl|one_mem_compactPacketObstructionValues_iff
CORRECTED RN SELECTOR CLOSED|Mpc class-seven compact packet has fixed raw cost|decl|compactRawCost_eq_defect
CORRECTED RN SELECTOR CLOSED|Mpc class-seven compact packet differences lie in cost kernel|decl|compactRawDifference_mem_costKernel
CORRECTED RN SELECTOR CLOSED|Mpc class-seven compact-kernel connecting hom|decl|oneHandleCompactConnectingHom
CORRECTED RN SELECTOR CLOSED|Mpc class-seven packet obstruction cocycle|decl|relativeObstruction_eq_connecting_inv_mul
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven connecting-hom triviality|decl|OneHandleCompactConnectingTrivial
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven compact-kernel range coverage|decl|OneHandleCompactKernelCovered
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting trivial iff range covered|decl|compactConnectingTrivial_iff_range_le_relaxed
CORRECTED RN SELECTOR CLOSED|Mpc class-seven finite connecting-value set|decl|compactConnectingValues
CORRECTED RN SELECTOR CLOSED|Mpc class-seven compact-kernel F2 transpose|decl|oneHandleCompactKernelTranspose
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven connecting transpose vanishing|decl|OneHandleCompactKernelTransposeVanishing
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting trivial iff transpose kernels equal|decl|compactConnectingTrivial_iff_transpose_ker_eq
CORRECTED RN SELECTOR CLOSED|Mpc class-seven compact augmented transpose rank|decl|oneHandleCompactAugmentedTransposeRank
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting trivial iff transpose ranks equal|decl|compactConnectingTrivial_iff_transpose_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc class-seven packet obstructions lie in connecting coset|decl|compactPacketObstructionValues_subset_connectingCoset
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven connecting-image realization at a lift|decl|OneHandleCompactConnectingRealizedAt
CORRECTED RN SELECTOR CLOSED|Mpc class-seven packet set equals coset iff image realized|decl|compactPacketObstructionValues_eq_connectingCoset_iff
CORRECTED RN SELECTOR CLOSED|Mpc class-seven every connecting value is legally realized|decl|compactConnectingRealizedAt
CORRECTED RN SELECTOR CLOSED|Mpc class-seven packet obstruction set is connecting coset|decl|compactPacketObstructionValues_eq_connectingCoset
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven solvability iff reference obstruction in connecting image|decl|ordinaryRelativeSolvable_iff_obstruction_mem_connectingValues
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting-image F2 transpose|decl|oneHandleCompactConnectingImageTranspose
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven connecting-target transpose vanishing|decl|OneHandleCompactConnectingTargetTransposeVanishing
CORRECTED RN SELECTOR CLOSED|Mpc class-seven solvability iff connecting-target transpose kernels equal|decl|ordinaryRelativeSolvable_iff_connectingTarget_ker_eq
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting-image transpose rank|decl|oneHandleCompactConnectingImageTransposeRank
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting-target augmented rank|decl|oneHandleCompactConnectingTargetAugmentedTransposeRank
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven solvability iff connecting-target ranks equal|decl|ordinaryRelativeSolvable_iff_connectingTarget_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting-target rank has two cases|decl|connectingTargetAugmentedRank_eq_or_eq_add_one
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven connecting-target one-bit failure certificate|decl|connectingTargetDetected_iff_rankJump_one
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven finite compact-kernel full solution|decl|OneHandleCompactKernelFullSolution
CORRECTED RN SELECTOR CLOSED|Mpc class-seven finite full solution iff W6 correctable|decl|compactKernelFullSolutions_nonempty_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven finite connecting fiber|decl|compactConnectingFiber
CORRECTED RN SELECTOR CLOSED|Mpc class-seven connecting fiber nonempty iff ordinary solvable|decl|compactConnectingFiber_nonempty_iff
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven finite full correction candidates|decl|compactFullCorrectionCandidates
CORRECTED RN SELECTOR CLOSED|Mpc class-seven full candidate set nonempty iff W6 correctable|decl|compactFullCorrectionCandidates_nonempty_iff
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral connecting hom|decl|oneHandleCompactNeutralConnectingHom
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven finite neutral connecting values|decl|compactNeutralConnectingValues
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven full solvability iff neutral value lies in image|decl|oneHandleW6Correctable_iff_neutrality_mem_connectingValues
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral-image F2 transpose|decl|oneHandleCompactNeutralImageTranspose
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven neutral-target transpose vanishing|decl|OneHandleCompactNeutralTargetTransposeVanishing
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven full solvability iff neutral transpose kernels equal|decl|oneHandleW6Correctable_iff_neutralTarget_ker_eq
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral-image transpose rank|decl|oneHandleCompactNeutralImageTransposeRank
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral-target augmented rank|decl|oneHandleCompactNeutralTargetAugmentedTransposeRank
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven full solvability iff neutral-target ranks equal|decl|oneHandleW6Correctable_iff_neutralTarget_finrank_eq
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral-target rank has two cases|decl|neutralTargetAugmentedRank_eq_or_eq_add_one
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven neutral-target one-bit failure certificate|decl|neutralTargetDetected_iff_rankJump_one
CORRECTED RN SELECTOR CLOSED|Mpc class-seven standard neutral target is a parity quotient|decl|oneHandleC7StandardNeutralityParityFactor_surjective
CORRECTED RN SELECTOR CLOSED|Mpc class-seven standard neutral target has at most four elements|decl|natCard_oneHandleC7StandardNeutralityCokernel_le_four
CORRECTED RN SELECTOR CLOSED|Mpc class-seven standard neutral target has F2-rank at most two|decl|oneHandleC7StandardNeutralityFinrank_le_two
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral-image transpose rank is at most two|decl|neutralImageTransposeRank_le_two
CORRECTED RN SELECTOR CLOSED|Mpc class-seven augmented transpose rank is at most two|decl|neutralTargetAugmentedTransposeRank_le_two
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven full solvability from neutral-image rank two|decl|oneHandleW6Correctable_of_neutralImageTransposeRank_eq_two
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral target exact parity quotient|decl|oneHandleC7StandardNeutralityCokernelEquivParity
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral/parity-interaction cardinal product|decl|natCard_standardNeutrality_mul_parityInteraction_eq_four
CORRECTED RN SELECTOR BOUNDARY|Mpc class-seven neutral target trivial iff parity row fills plane|decl|oneHandleC7StandardNeutralityCokernel_trivial_iff_parityRow_range_eq_top
CORRECTED RN SELECTOR CLOSED|Mpc class-seven standard parity-interaction rank|decl|oneHandleC7StandardParityInteractionRank
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral plus parity-interaction ranks equal two|decl|standardNeutralityFinrank_add_parityInteractionRank
CORRECTED RN SELECTOR CLOSED|Mpc class-seven neutral-image rank bounded by neutral-target rank|decl|neutralImageTransposeRank_le_standardNeutralityFinrank
CORRECTED RN SELECTOR CLOSED|Mpc parity-covered coordinate failure iff primitive case|decl|target_not_coordinateSpan_iff_primitive_of_parityCovered
CORRECTED RN TIED|Npc residual (from determinant)|decl|npcRowResidualRN_of_tied_determinant
CORRECTED RN TIED|Npc endpoint (from determinant)|decl|npc_candidate_equiv_galKRN_of_tied_determinant
CORRECTED RN SELECTOR BOUNDARY|Npc tied branch (needs realization)|decl|familyNpc_branch_of_realization_tied
CORRECTED RN SELECTOR BOUNDARY|Npc realization (oriented + row data)|decl|npcMarkedCoreRealization_of_oriented
CORRECTED RN SELECTOR BOUNDARY|Npc realization (family + primitive plane)|decl|npcMarkedCoreRealization_of_familySelection
CORRECTED RN SELECTOR BOUNDARY|Npc primitive plane from exact level|decl|exists_dnPlanePrimitive_of_level_exact
CORRECTED RN SELECTOR BOUNDARY|Npc selected tied branch (needs primitive plane)|decl|npcGenAsmBranch_of_familySelection_tied
CORRECTED RN SELECTOR BOUNDARY|Npc selected RN residual (needs primitive plane)|decl|npcRowResidualRN_of_familySelection
CORRECTED RN SELECTOR CLOSED|Npc primitive oriented frame|decl|exists_orientedEquiv_npcPlanePrimitive
CORRECTED RN SELECTOR CLOSED|Npc selected tied branch|decl|npcGenAsmBranch_of_familySelection_tied_exactLevel
CORRECTED RN SELECTOR CLOSED|Npc selected RN residual|decl|npcRowResidualRN_of_familySelection_exactLevel
CORRECTED RN CLOSED ROWS|Q2(v-2) residual|decl|wPcN_rowResidualRN_sqrtNegTwo
CORRECTED RN CLOSED ROWS|Q2(v-2) endpoint|decl|wPcN_candidate_equiv_galKRN_sqrtNegTwo
CORRECTED RN CLOSED ROWS|Q2(v2) residual|decl|wPcM_rowResidualRN_sqrtTwo
CORRECTED RN CLOSED ROWS|Q2(v2) endpoint|decl|wPcM_candidate_equiv_galKRN_sqrtTwo
CORRECTED RN CLOSED ROWS|Q2(v5) residual|decl|wPcM_rowResidualRN_sqrtFive
CORRECTED RN CLOSED ROWS|Q2(v5) endpoint|decl|wPcM_candidate_equiv_galKRN_sqrtFive
CORRECTED RN CLOSED ROWS|Q2(v10) endpoint|decl|mpcSqrtTen_candidate_equiv_galKRN
CORRECTED RN CLOSED ROWS|Q2(v-10) endpoint|decl|mpcMk_candidate_equiv_galKRN_sqrtNegTen
ODD SEAM|the seam Prop|decl|SqMarkedForwardSupply
ODD SEAM|every seam producer|prod|SqMarkedForwardSupply
ODD SEAM|seam = marked-core cert|decl|oddId_supply_iff_certificate
ODD SEAM|seam = one cup-adapted frame|decl|oddSeam_supply_iff_cupAdaptedFrame
ODD SEAM|seam = the full marking|decl|oddSeam_supply_iff_fullMarking
ODD SEAM|halved relator clause|prod|SqCupAdaptedFrameRelator
ODD SEAM|frame presentation clause|prod|SqCupAdaptedFramePresentation
ODD SEAM|clearing = row-plane family|decl|gClear_clearing_of_model
ODD SEAM|model clearing clause|prod|SqNuOrientedClearAtUnitPivot
ODD SEAM|row-plane move clause|prod|GClearModelMove
ODD SEAM|seam = clearing instance|decl|oddFrame_supply_iff_clearInstance
ODD SEAM|q-invariant of D_sq h|decl|oddSeam_demushkinQ_DSq
ODD SEAM|odd oriented equivalence|decl|nonempty_orientedEquiv_oddDegree
ODD FINAL|full nu supply iff two rows|decl|sqNuForwardSupply_iff_full
ODD FINAL|odd endpoint from two nu rows|decl|gammaR_lSq_equiv_galK_oddDegree_of_nuRows_final
ODD FINAL|odd endpoint from compatible ramified data|decl|gammaR_lSq_equiv_galK_oddDegree_compatible
ODD SEAM|closed corrected RN endpoint|decl|gUni_gammaR_lSq_equiv_galK
ODD RAMIFIED DATA|canonical anchored splitting field|decl|anchoredSplitField
ODD RAMIFIED DATA|certificate from anchored lift and involution packet|decl|ramifiedCertificateOfAnchoredSplit
ODD RAMIFIED DATA|compatibility-aware ramified packet|decl|CompatibleRamifiedData
ODD RAMIFIED DATA|compatible packet from two anchored atoms|decl|compatibleRamifiedData_of_anchoredResidual
ODD RAMIFIED DATA|instance-aware compatible packet|decl|CompatibleRamifiedDataAt
ODD RAMIFIED DATA|compatible residue-trivial lift residual|decl|CompatibleResidueLiftAt
ODD RAMIFIED DATA|anchored involution-field residual|decl|AnchoredInvolutionFieldDataAt
ODD RAMIFIED DATA|instance-aware packet from exact residuals|decl|compatibleRamifiedDataAt_of_residuals
ODD RAMIFIED DATA|residue lift from detected commutators|decl|compatibleResidueLiftAt_of_detected_commutators
ODD RAMIFIED DATA|residue lift at qK=2|decl|compatibleResidueLiftAt_of_qK_eq_two
ODD RAMIFIED DATA|residue lift from absolute tame inertia|decl|compatibleResidueLiftAt_of_inertia
ODD RAMIFIED DATA|q4 detected-commutator no-go|decl|no_tqFourPin_detected_commutator
ODD RAMIFIED DATA|unramified-kernel residue-action residual|decl|NuUrAbsoluteResidueKernelAt
ODD RAMIFIED DATA|residue lift from unramified-kernel residue action|decl|compatibleResidueLiftAt_of_nuUrKernel
ODD RAMIFIED DATA|full-inertia residue-action residual|decl|TameFullInertiaAbsoluteResidueTrivialAt
ODD RAMIFIED DATA|residue lift from full tame inertia|decl|compatibleResidueLiftAt_of_fullInertia
ODD RAMIFIED DATA|selected tau odd-root residual|decl|TameTauFixesOddRootsLiftAt
ODD RAMIFIED DATA|2-primary kernel is larger than full inertia|decl|ker_nuTq_not_le_inertiaPartQ
ODD RAMIFIED DATA|full inertia iff qMkQ-kernel|decl|tame_mem_inertiaPartQ_iff_qMkQ_eq_one
ODD RAMIFIED DATA|odd-root action factors through qMkQ|decl|OddRootActionFactorsThroughQurAt
ODD RAMIFIED DATA|residue lift from qMkQ action factorization|decl|compatibleResidueLiftAt_of_oddRootActionFactorsThroughQur
ODD RAMIFIED DATA|canonical absolute residue action|decl|absoluteResidueAction
ODD RAMIFIED DATA|absolute inertia iff residue trivial|decl|mem_absoluteInertiaSubgroup_iff_isResidueTrivial_bot
ODD RAMIFIED DATA|oriented full tame inertia containment|decl|OrientedFullTameInertiaLiesInAbsoluteInertiaAt
ODD RAMIFIED DATA|residue lift from canonical absolute inertia|decl|compatibleResidueLiftAt_of_orientedFullTameInertiaInAbsoluteInertia
ODD RAMIFIED DATA|residue-compatible oriented tame quotient|decl|AbsoluteResidueCompatibleOrientedTameQuotientK
ODD RAMIFIED DATA|compatible gamma endpoint from residue-compatible tame quotient|decl|gammaR_lSq_equiv_galK_oddDegree_of_absoluteResidueCompatible
ODD RAMIFIED DATA|absolute unramified quotient comparison|decl|OrientedAbsoluteUnramifiedQuotientComparison
ODD RAMIFIED DATA|full tame kernel equals absolute inertia|decl|fullTameInertia_comap_eq_absoluteInertiaK
ODD RAMIFIED DATA|residue lift from quotient comparison|decl|compatibleResidueLiftAt
ODD RAMIFIED DATA|full unramified quotient is Zhat|decl|qurQEquivZhat
ODD RAMIFIED DATA|nuTq is the pro-two projection|decl|maxProPMk_qurQEquivZhat_qMkQ
ODD RAMIFIED DATA|absolute unramified Frobenius coordinate|decl|AbsoluteUnramifiedFrobeniusCoordinate
ODD RAMIFIED DATA|absolute residue field algebraic over F2|decl|absoluteResidueField_isAlgebraic
ODD RAMIFIED DATA|finite residue Frobenius powers generate|decl|finiteResidue_frobeniusPowers_bijective
ODD RAMIFIED DATA|absolute residue field algebraically closed|decl|absoluteResidueField_isAlgClosed
ODD RAMIFIED DATA|absolute residue field is algebraic closure|decl|absoluteResidueField_isAlgClosure
ODD RAMIFIED DATA|global absolute residue square Frobenius|decl|absoluteResidueFrobenius
ODD RAMIFIED DATA|absolute residue action exact kernel|decl|absoluteResidueAlgAction_ker
ODD RAMIFIED DATA|absolute residue quotient equals action image|decl|absoluteInertiaQuotientEquivResidueRange
ODD RAMIFIED DATA|absolute residue surjectivity iff finite lifts|decl|absoluteResidueAlgAction_surjective_iff_finite_lifts
ODD RAMIFIED DATA|absolute residue square Frobenius lift|decl|AbsoluteResidueFrobeniusLift
ODD RAMIFIED DATA|absolute residue surjectivity iff Frobenius lift|decl|absoluteResidueAlgAction_surjective_iff_frobeniusLift
ODD RAMIFIED DATA|absolute residue Frobenius iff odd-root squaring|decl|squaresOddRootsOfUnity_iff_residueFrobenius
ODD RAMIFIED DATA|finite odd cyclotomic Frobenius locus|decl|oddRootFrobeniusSet
ODD RAMIFIED DATA|global odd-root Frobenius iff finite levels|decl|exists_squaresOddRoots_iff_finite_cyclotomic_lifts
ODD RAMIFIED DATA|global odd-root Frobenius iff local minpolys|decl|exists_squaresOddRoots_iff_minpoly_square
ODD RAMIFIED DATA|absolute norm valuation ring is Henselian|decl|absoluteNormInteger_henselianLocalRing
ODD RAMIFIED DATA|primitive odd root is conjugate to its square|decl|primitiveOddRoot_isConjRoot_square
ODD RAMIFIED DATA|global odd-root Frobenius exists|decl|exists_squaresOddRootsOfUnity
ODD RAMIFIED DATA|absolute residue action is surjective|decl|absoluteResidueAlgAction_surjective
ODD RAMIFIED DATA|Zhat to absolute residue Galois map|decl|zhatToAbsoluteResidueGal
ODD RAMIFIED DATA|Zhat generates absolute residue Galois|decl|zhatToAbsoluteResidueGal_surjective
ODD RAMIFIED DATA|Zhat faithfully acts by residue Frobenius|decl|zhatToAbsoluteResidueGal_injective
ODD RAMIFIED DATA|absolute residue Galois equivalence with Zhat|decl|absoluteResidueGalEquivZhat
ODD RAMIFIED DATA|absolute residue Frobenius coordinate|decl|absoluteResidueGalEquivZhat_frobenius
ODD RAMIFIED DATA|absolute inertia quotient equals residue Galois|decl|absoluteInertiaQuotientEquivResidueGal
ODD RAMIFIED DATA|absolute inertia quotient coordinate with Zhat|decl|absoluteInertiaQuotientEquivZhat
ODD RAMIFIED DATA|absolute residue coordinate restricted to GalK|decl|absoluteResidueCoordinateK
ODD RAMIFIED DATA|restricted absolute coordinate exact kernel|decl|absoluteResidueCoordinateK_ker
ODD RAMIFIED DATA|canonical GalK inertia is closed|decl|absoluteInertiaK_isClosed_unconditional
ODD RAMIFIED DATA|actual unramified quotient coordinate|decl|absoluteUnramifiedCoordinateK
ODD RAMIFIED DATA|actual unramified quotient coordinate injective|decl|absoluteUnramifiedCoordinateK_injective
ODD RAMIFIED DATA|actual unramified coordinate closed image|decl|absoluteUnramifiedCoordinateK_range_isClosed
ODD RAMIFIED DATA|actual unramified quotient equals coordinate image|decl|absoluteUnramifiedCoordinateKEquivRange
ODD RAMIFIED DATA|relative signed Frobenius square|decl|OrientedAbsoluteResidueFrobeniusCompatibility
ODD RAMIFIED DATA|residue lift from relative Frobenius square|decl|OrientedAbsoluteResidueFrobeniusCompatibility.compatibleResidueLiftAt
ODD RAMIFIED DATA|absolute residue coordinate on GalKab|decl|absoluteResidueCoordinateKAb
ODD RAMIFIED DATA|abstract tame coordinate on GalKab|decl|orientedTameQurCoordinateKAb
ODD RAMIFIED DATA|relative Frobenius reciprocity rows|decl|RelativeFrobeniusReciprocityRows
ODD RAMIFIED DATA|relative Frobenius square iff reciprocity rows|decl|orientedAbsoluteResidueFrobeniusCompatibility_iff_rows
ODD RAMIFIED DATA|absolute residue unit-inertia residual|decl|AbsoluteResidueUnitInertia
ODD RAMIFIED DATA|relative Frobenius uniformizer row|decl|RelativeFrobeniusUniformizerRow
ODD RAMIFIED DATA|relative Frobenius split into unit and uniformizer|decl|orientedAbsoluteResidueFrobeniusCompatibility_iff_unit_uniformizer
ODD RAMIFIED DATA|absolute uniformizer Frobenius normalization|decl|AbsoluteResidueUniformizerNormalization
ODD RAMIFIED DATA|abstract geometric uniformizer normalization|decl|AbstractTameUniformizerNormalization
ODD RAMIFIED DATA|relative Frobenius reduced to uniformizer|decl|orientedAbsoluteResidueFrobeniusCompatibility_iff_uniformizer
ODD RAMIFIED DATA|relative Frobenius from full normalizations|decl|orientedAbsoluteResidueFrobeniusCompatibility_of_normalizations
ODD RAMIFIED AUDIT|Zhat maximal pro-two projection noninjective|decl|maxProPMk_zhat_not_injective
ODD RAMIFIED AUDIT|geometric pro-two target has distinct Zhat lifts|decl|exists_distinct_lifts_ztwoOne_inv
ODD RAMIFIED DATA|Zhat equality from pro-two and remaining finite rows|decl|zhat_eq_iff_maxProTwo_and_nonProTwoRows
ODD RAMIFIED DATA|abstract uniformizer iff non-pro-two finite rows|decl|abstractTameUniformizerNormalization_iff_nonProTwoRows
ODD RAMIFIED DATA|abstract geometric uniformizer row in QurQ|decl|AbstractTameUniformizerQurRow
ODD RAMIFIED DATA|full abstract normalization iff QurQ row|decl|abstractTameUniformizerNormalization_iff_qurRow
ODD RAMIFIED DATA|actual uniformizer action is residue Frobenius|decl|AbsoluteResidueUniformizerFrobeniusRow
ODD RAMIFIED DATA|full actual normalization iff Frobenius row|decl|absoluteResidueUniformizerNormalization_iff_frobeniusRow
ODD RAMIFIED DATA|relative comparison from natural uniformizer rows|decl|orientedAbsoluteResidueFrobeniusCompatibility_of_uniformizerRows
ODD RAMIFIED DATA|absolute-residue local reciprocity law|decl|AbsoluteResidueLocalReciprocityLaw
ODD RAMIFIED DATA|absolute reciprocity iff unit and Frobenius rows|decl|absoluteResidueLocalReciprocityLaw_iff_rows
ODD RAMIFIED DATA|relative comparison from field reciprocity law|decl|orientedAbsoluteResidueFrobeniusCompatibility_of_localReciprocityLaw
ODD RAMIFIED DATA|abstract tame local reciprocity law|decl|AbstractTameLocalReciprocityLaw
ODD RAMIFIED DATA|abstract reciprocity iff unit and geometric rows|decl|abstractTameLocalReciprocityLaw_iff_rows
ODD RAMIFIED DATA|relative comparison from both reciprocity laws|decl|orientedAbsoluteResidueFrobeniusCompatibility_of_reciprocityLaws
ODD RAMIFIED DATA|compatible packet from reciprocity laws and equal norms|decl|compatibleRamifiedDataAt_of_reciprocityLaws
CORRECTED RN CONDITIONAL ROWS|odd L endpoint from reciprocity laws and equal norms|decl|gammaR_lSq_equiv_galK_oddDegree_of_reciprocityLaws
ODD RAMIFIED DATA|canonical anchored involution field|decl|anchoredInvolutionField
ODD RAMIFIED DATA|anchored equal-norm residual|decl|AnchoredInvolutionEqualNormValueGroupsAt
ODD RAMIFIED DATA|involution packet from equal norms|decl|anchoredInvolutionFieldDataAt_of_equalNormValueGroups
ODD RAMIFIED DATA|canonical anchored tame-inertia field|decl|anchoredTameInertiaField
ODD RAMIFIED DATA|equal norms from odd tame-inertia index|decl|anchoredInvolutionEqualNormValueGroupsAt_of_oddTameInertia
ODD RAMIFIED DATA|relative odd tame-inertia residual|decl|AnchoredTameInertiaRelativeOddDataAt
ODD RAMIFIED DATA|equal norms from relative odd tame-inertia index|decl|anchoredInvolutionEqualNormValueGroupsAt_of_relativeOddTameInertia
ODD RAMIFIED DATA|anchored tame-inertia visible range index|decl|anchoredTameInertiaField_fixing_index_eq_relIndex_range
ODD RAMIFIED DATA|relative ramification divides visible range index|decl|anchoredTameInertiaField_relE_dvd_relIndex_range
ODD RAMIFIED DATA|odd tame-range index residual|decl|AnchoredTameInertiaOddRangeIndexAt
ODD RAMIFIED DATA|equal norms from odd tame-range index|decl|anchoredInvolutionEqualNormValueGroupsAt_of_oddTameRangeIndex
ODD RAMIFIED DATA|prescribed quotient kills full inertia|decl|inertiaPartQ_le_comap_zpowers_tqTau
ODD RAMIFIED DATA|tame unit full-inertia refinement|decl|TameUnitInertiaRefinement
ODD RAMIFIED DATA|prescribed relative-unramified residual|decl|AnchoredTameInertiaRelativeUnramifiedDataAt
ODD RAMIFIED DATA|relative unramified iff spectral equal norms|decl|anchoredTameInertiaRelativeUnramifiedDataAt_iff_equalNormValues
ODD RAMIFIED DATA|equal norms from prescribed unramified field|decl|anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified
ODD RAMIFIED DATA|unit spectral reciprocity residual|decl|AnchoredUnitSpectralReciprocity
ODD RAMIFIED DATA|instance-aware full-inertia unit refinement|decl|TameUnitInertiaRefinementAt
ODD RAMIFIED DATA|prescribed unramified field from spectral reciprocity|decl|anchoredTameInertiaRelativeUnramifiedDataAt_of_unitSpectralReciprocity
ODD RAMIFIED DATA|equal norms from unit spectral reciprocity|decl|anchoredInvolutionEqualNormValueGroupsAt_of_unitSpectralReciprocity
ODD RAMIFIED DATA|compatible ramified Gauss residue|decl|gaussZResidueDK_ramified_compatible
ODD RAMIFIED DATA|compatible affine determinant|decl|affineDeterminant_galK_compatible
LEGACY ASK (COMPAT ONLY)|frozen: surviving Prop|decl|askCStageVanishing
LEGACY ASK (COMPAT ONLY)|frozen <-> stageVanishing|decl|askC_exactLifting_iff_stageVanishing
LEGACY ASK (COMPAT ONLY)|corrected RN at G_K|decl|exactLiftingSemanticsRN_galK
LEGACY ASK (COMPAT ONLY)|stokes at G_K|decl|stokesDualityCertificate_galK
LEGACY ASK (COMPAT ONLY)|determinant at G_K|decl|affineDeterminant_galK
LEGACY ASK (COMPAT ONLY)|scalar at G_K|decl|scalarHilbert_galK
LEGACY CAND RECORDS (COMPAT ONLY)|M0 a h|decl|mWordCertificate
LEGACY CAND RECORDS (COMPAT ONLY)|Mpc a r p q|decl|mpcWordCertificate
LEGACY CAND RECORDS (COMPAT ONLY)|N0 a h|decl|sqrtNegTwoWordCertificate
LEGACY CAND RECORDS (COMPAT ONLY)|Npc a r h q|decl|genCertNpcWordCertificate
LEGACY CAND RECORDS (COMPAT ONLY)|L h|decl|lCand_wordCertificateCanonical
TABLE
)

# ----------------------------------------------------------------------------
# Resolution: short name -> file, module, fully-qualified name.
# The namespace stack is reconstructed by tracking namespace/section open and
# close, so nested namespaces resolve correctly and no namespace is written
# down anywhere in this file.
# ----------------------------------------------------------------------------
NSAWK=$(cat <<'AWKEOF'
BEGIN { top = 0 }
{
  if (NR == TARGETLINE) {
    pfx = ""
    for (i = 1; i <= top; i++) if (kind[i] == "ns") pfx = pfx stack[i] "."
    print pfx NAME
    exit
  }
}
/^namespace[ \t]+[A-Za-z_]/ { top++; stack[top] = $2; kind[top] = "ns"; next }
/^(noncomputable[ \t]+)?section([ \t]+[A-Za-z_][A-Za-z0-9_.]*)?[ \t]*$/ {
  n = ($1 == "noncomputable") ? $3 : $2
  top++; stack[top] = (n == "" ? "<anon>" : n); kind[top] = "sec"; next
}
/^end([ \t]+[A-Za-z_][A-Za-z0-9_.]*)?[ \t]*$/ {
  n = $2
  if (n == "") { if (top > 0) top-- }
  else { while (top > 0 && stack[top] != n) top--; if (top > 0) top-- }
  next
}
AWKEOF
)

resolve() {  # $1 = short name; echoes "module<TAB>fullname" or nothing
  local short=$1 hit file line full mod
  hit=$(grep -rn -m1 \
    "^\(theorem\|lemma\|def\|abbrev\|structure\|noncomputable def\|opaque\)[ ]$short\b" \
    "$WT/GQ2" --include='*.lean' 2>/dev/null | head -1)
  [ -z "$hit" ] && return 0
  file=${hit%%:*}
  line=${hit#*:}; line=${line%%:*}
  full=$(awk -v TARGETLINE="$line" -v NAME="$short" "$NSAWK" "$file")
  mod=${file#"$WT"/}
  mod=${mod%.lean}
  mod=${mod//\//.}
  printf '%s\t%s\n' "$mod" "$full"
}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# The direct source imports are the freshness witness for the umbrella olean.
# If even one is absent from `import GQ2`'s environment, every row and producer
# count is potentially stale and the report must not present it as verified.
awk '/^import[ \t]+/ {
    for (i = 2; i <= NF; i++) {
      if ($i ~ /^--/) break
      print $i
    }
  }' "$WT/GQ2.lean" | sort -u > "$TMP/directimports"

# Resolve every row once into the probe's request list.
declare -a REQ=()
while IFS='|' read -r grp lab kind short; do
  [ -z "${grp:-}" ] && continue
  r=$(resolve "$short")
  if [ -z "$r" ]; then
    REQ+=("$grp|$lab|$kind|$short|-|-")
  else
    REQ+=("$grp|$lab|$kind|$short|${r%%$'\t'*}|${r#*$'\t'}")
  fi
done <<< "$ROWS"

# EVERY module under GQ2/, from the filesystem, for the registration scan.  Not
# the rows' modules: the point of the scan is to catch a module NO row reaches,
# so deriving its input from the rows would defeat it.
find "$WT/GQ2" -name '*.lean' |
  sed -e "s|^$WT/||" -e 's|\.lean$||' | tr '/' '.' | sort > "$TMP/allmods"
split -l 64 "$TMP/allmods" "$TMP/allmods.chunk."

# ----------------------------------------------------------------------------
# THE PROBE.  Types, explicit binders, axiom censuses, producer scans and the
# registration check, all in ONE file, all against the UMBRELLA environment.
#
# `import GQ2` and nothing else.  This is structural, not cosmetic.  A `prod`
# scan reads the ENVIRONMENT; while the probe imported the rows' own modules,
# every producer count was a function of which modules the rows happened to
# reach, so a module reached by no row was invisible and the count printed
# silently low.  That fired on wave 84 (MpcPivShift) and again on wave 85
# (three counts at once).  Importing the umbrella makes the environment
# exactly what an `import GQ2` consumer sees, so the only producer this board
# can now miss is one in a module the umbrella does not import -- which is
# precisely what the REGISTRATION section flags, in the same environment.
#
# Consequence to read correctly: a row whose declaration lives OUTSIDE the
# umbrella now reports MISSING rather than EXISTS.  That is the intended
# reading (no `import GQ2` consumer can use it either), and the row prints the
# registration verdict for its module alongside so the two are never confused.
# ----------------------------------------------------------------------------
{
  echo 'import GQ2'
  cat <<'LEAN'
open Lean Elab Command Meta

partial def sbStrip : Expr → Expr
  | .forallE _ _ b _ => sbStrip b
  | e => e

def sbFlat (s : String) : String :=
  " ".intercalate ((s.replace "\n" " ").splitOn " " |>.filter (· ≠ ""))

/-- The head symbol of a binder type: what KIND of thing the caller must supply.
Never unfolds, so a clause abbreviation reports under its own name. -/
def sbHead (e : Expr) : String :=
  match e with
  | .forallE .. => "(function)"
  | _ => match e.getAppFn with
         | .const c _ => c.getString!
         | .sort _ => "Sort"
         | _ => "?"

/-- The EXPLICIT binders of `n`, i.e. what a caller must supply: head symbols
(the readable column) paired with the full pretty-printed types (`--raw`). -/
def sbExplicit (n : Name) : MetaM (Array String × Array String) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut heads : Array String := #[]
    let mut full : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .default then
        heads := heads.push (sbHead d.type)
        full := full.push (sbFlat (toString (← ppExpr d.type)))
    return (heads, full)

def sbStd : List Name := [`propext, `Classical.choice, `Quot.sound]

def sbAxioms (n : Name) : CoreM String := do
  let ax ← Lean.collectAxioms n
  let extra := ax.toList.filter (fun a => !(sbStd.contains a))
  let base := if ax.toList.any (fun a => sbStd.contains a) then "std-3" else "none"
  if extra.isEmpty then return base
  return base ++ " + " ++ ", ".intercalate (extra.map (fun a => a.getString!))

/-- `Array.contains` is recursive and the umbrella now has more modules than
Lean's default recursion depth.  Search fixed shallow slices instead. -/
def sbModulePresent (a : Array String) (m : String) : Bool :=
  (a.extract 0 256).contains m ||
  (a.extract 256 512).contains m ||
  (a.extract 512 768).contains m ||
  (a.extract 768 1024).contains m ||
  (a.extract 1024 1280).contains m ||
  (a.extract 1280 1536).contains m ||
  (a.extract 1536 1792).contains m ||
  (a.extract 1792 2048).contains m ||
  (a.extract 2048 2304).contains m ||
  (a.extract 2304 2560).contains m ||
  (a.extract 2560 2816).contains m ||
  (a.extract 2816 3072).contains m ||
  (a.extract 3072 3328).contains m ||
  (a.extract 3328 3584).contains m ||
  (a.extract 3584 3840).contains m ||
  (a.extract 3840 4096).contains m ||
  (a.extract 4096 4352).contains m ||
  (a.extract 4352 4608).contains m ||
  (a.extract 4608 4864).contains m ||
  (a.extract 4864 5120).contains m ||
  (a.extract 5120 5376).contains m ||
  (a.extract 5376 5632).contains m ||
  (a.extract 5632 5888).contains m ||
  (a.extract 5888 6144).contains m ||
  (a.extract 6144 6400).contains m ||
  (a.extract 6400 6656).contains m ||
  (a.extract 6656 6912).contains m ||
  (a.extract 6912 7168).contains m ||
  (a.extract 7168 7424).contains m ||
  (a.extract 7424 7680).contains m ||
  (a.extract 7680 7936).contains m ||
  (a.extract 7936 8192).contains m

def sbRender (tag : String) (n : Name) : CommandElabM Unit := do
  if !(← getEnv).contains n then
    IO.println s!"SB|{tag}|MISSING||||"
    return
  let (heads, full) ← liftTermElabM <| sbExplicit n
  let ax ← liftCoreM <| sbAxioms n
  IO.println s!"SB|{tag}|EXISTS|{heads.size}|{", ".intercalate heads.toList}\
|{ax}|{" ;; ".intercalate full.toList}"

def sbProducers (env : Environment) (target : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n ci =>
    if n.getRoot != `GQ2 || n.isInternalDetail then acc else
    match (sbStrip ci.type).getAppFn with
    | .const t _ => if t == target then acc.push n else acc
    | _ => acc
LEAN
  i=0
  rowchunk=0
  for rec in "${REQ[@]}"; do
    if [ "$rowchunk" = "0" ]; then
      echo 'run_cmd do'
      echo '  let env ← getEnv'
    fi
    i=$((i + 1))
    kind=$(echo "$rec" | cut -d'|' -f3)
    full=$(echo "$rec" | cut -d'|' -f6)
    if [ "$full" = "-" ]; then
      echo "  IO.println \"SB|$i|UNRESOLVED|||||\""
    elif [ "$kind" = "prod" ]; then
      cat <<PROD
  if !env.contains \`$full then
    IO.println "SB|$i|MISSING|||||"
  else
    let ps := sbProducers env \`$full
    IO.println s!"SB|$i|EXISTS|{ps.size}|producers|||"
    for p in ps.qsort (fun a b => a.toString < b.toString) do
      sbRender s!"$i.{p}" p
PROD
    else
      echo "  sbRender \"$i\" \`$full"
    fi
    rowchunk=$((rowchunk + 1))
    [ "$rowchunk" = "48" ] && rowchunk=0
  done
  # Registration, in the same environment: a module NOT in `import GQ2`'s
  # transitive closure is a module no consumer can see.  Every module under
  # GQ2/ is checked in bounded command chunks.  One monolithic interpreted
  # loop crossed Lean's default recursion depth at 1067 modules; one command
  # per module previously crossed the heartbeat limit.  Bounded commands
  # avoid both failure modes without an option override.
  echo '  let sbPresent := env.header.moduleNames.map (·.toString)'
  printf '  let sbDirect := "'
  tr '\n' ' ' < "$TMP/directimports"
  printf '"\n'
  cat <<'FRESH'
  let sbDirectMods := ((sbDirect.splitOn " ").filter (· ≠ "")).toArray
  for m in sbDirectMods do
    if !sbModulePresent sbPresent m then IO.println s!"STALE_UMBRELLA|{m}"
FRESH
  # Reset the command elaborator between bounded source-module chunks.
  for part in "$TMP"/allmods.chunk.*; do
    echo 'run_cmd do'
    echo '  let env ← getEnv'
    echo '  let sbPresent := env.header.moduleNames.map (·.toString)'
    while IFS= read -r mod; do
      printf '  if !sbModulePresent sbPresent "%s" then IO.println "OUTSIDE|%s"\n' \
        "$mod" "$mod"
    done < "$part"
  done
  printf 'run_cmd do IO.println "SCANNED|%s"\n' \
    "$(wc -l < "$TMP/allmods" | tr -d ' ')"
} > "$TMP/probe.lean"

bash "$MIRROR" check "$TMP/probe.lean" > "$TMP/out" 2> "$TMP/err"
RC=$?
STALE=0
if [ "$RC" = "0" ] && grep -q '^STALE_UMBRELLA|' "$TMP/out"; then
  STALE=1
fi

if [ "$RAW" = "1" ]; then
  cat "$TMP/out"
  [ "$STALE" = "1" ] && exit 3
  exit "$RC"
fi

# ----------------------------------------------------------------------------
# Report.
# ----------------------------------------------------------------------------
HEAD=$(cd "$WT" && git log -1 --format='%h %ad' --date=short 2>/dev/null)
BR=$(cd "$WT" && git branch --show-current 2>/dev/null)

echo "======================================================================="
echo " GQ2 DYADIC CAMPAIGN SCOREBOARD"
echo " tree $HEAD   branch $BR   generated $(date '+%Y-%m-%d %H:%M')"
echo " every EXISTS / binder / axiom line below was elaborated by this run"
echo "======================================================================="

if [ "$RC" != "0" ]; then
  echo
  echo "!! the probe did not elaborate; every row below is UNVERIFIED"
  sed -n '1,20p' "$TMP/err"
elif [ "$STALE" = "1" ]; then
  echo
  echo "!! STALE_UMBRELLA: source GQ2.lean directly imports modules absent"
  echo "   from the imported GQ2 environment; every row below is UNVERIFIED"
  grep '^STALE_UMBRELLA|' "$TMP/out" | sed 's/^/   /'
  echo "   remedy: scripts/mirror.sh gen GQ2"
fi

lastgrp=""
i=0
for rec in "${REQ[@]}"; do
  i=$((i + 1))
  grp=$(echo "$rec" | cut -d'|' -f1)
  lab=$(echo "$rec" | cut -d'|' -f2)
  kind=$(echo "$rec" | cut -d'|' -f3)
  short=$(echo "$rec" | cut -d'|' -f4)
  mod=$(echo "$rec" | cut -d'|' -f5)
  full=$(echo "$rec" | cut -d'|' -f6)
  if [ "$grp" != "$lastgrp" ]; then
    echo
    echo "## $grp"
    lastgrp=$grp
  fi
  if [ "$STALE" = "1" ]; then
    printf '  %-30s UNVERIFIED (STALE_UMBRELLA)\n' "$lab"
    continue
  fi
  line=$(grep -m1 "^SB|$i|" "$TMP/out" 2>/dev/null)
  if [ -z "$line" ]; then
    printf '  %-30s UNVERIFIED (probe produced no record)\n' "$lab"
    continue
  fi
  st=$(echo "$line" | cut -d'|' -f3)
  cnt=$(echo "$line" | cut -d'|' -f4)
  heads=$(echo "$line" | cut -d'|' -f5)
  ax=$(echo "$line" | cut -d'|' -f6)
  if [ "$st" != "EXISTS" ]; then
    # The probe sees only the umbrella, so a MISSING row is either a name that
    # is not in the tree or a name in a module the umbrella does not reach.
    # Print which, rather than leaving the reader to guess.
    if grep -qx "OUTSIDE|$mod" "$TMP/out" 2>/dev/null; then
      printf '  %-30s %s   [%s; its module %s is OUTSIDE the umbrella]\n' \
        "$lab" "$st" "$short" "$mod"
    else
      printf '  %-30s %s   [%s]\n' "$lab" "$st" "$short"
    fi
    continue
  fi
  if [ "$kind" = "prod" ]; then
    printf '  %-30s producers: %s   [%s]\n' "$lab" "$cnt" "$short"
    grep "^SB|$i\." "$TMP/out" 2>/dev/null |
      while IFS='|' read -r _ tag _ c h a _; do
        printf '      %s\n' "${tag#*.}"
        if [ "$c" = "0" ]; then
          printf '        carries NOTHING            axioms: %s\n' "$a"
        else
          printf '        carries %-2s : %s\n' "$c" "$h"
          printf '        axioms     : %s\n' "$a"
        fi
      done
  else
    printf '  %-30s EXISTS   %s\n' "$lab" "$full"
    if [ "$cnt" = "0" ]; then
      printf '      carries NOTHING (no explicit binder)\n'
    else
      printf '      carries %-2s : %s\n' "$cnt" "$heads"
    fi
    printf '      axioms     : %s\n' "$ax"
  fi
done

echo
echo "## REGISTRATION (EVERY module under GQ2/, against \`import GQ2\`)"
if [ "$RC" != "0" ]; then
  echo "  UNVERIFIED (the probe did not elaborate)"
  sed -n '1,10p' "$TMP/err"
elif [ "$STALE" = "1" ]; then
  echo "  UNVERIFIED (STALE_UMBRELLA; run scripts/mirror.sh gen GQ2)"
else
  SCANNED=$(grep -m1 '^SCANNED|' "$TMP/out" | cut -d'|' -f2)
  printf '  modules on disk under GQ2/   %s\n' "${SCANNED:-UNVERIFIED}"
  n=0
  while IFS='|' read -r _ m; do
    [ -z "${m:-}" ] && continue
    n=$((n + 1))
    # A module that itself does `import GQ2` CANNOT be registered: that is a
    # cycle, not an oversight.  Derived by reading the file, not asserted here.
    f=$WT/$(echo "$m" | tr '.' '/').lean
    if [ -f "$f" ] && grep -qx 'import GQ2' "$f"; then
      printf '  OUTSIDE the umbrella         %s   (it imports GQ2 itself:\n' "$m"
      printf '%s\n' "                               registering it would cycle)"
    else
      printf '  OUTSIDE the umbrella         %s\n' "$m"
    fi
  done < <(grep '^OUTSIDE|' "$TMP/out")
  [ "$n" = "0" ] && echo "  OUTSIDE the umbrella         none"
  echo "  (outside = not in \`import GQ2\`'s transitive closure, so invisible"
  echo "   to every consumer AND to the producer scans above.  This is now the"
  echo "   board's only blind spot, and this line is the check for it.)"
fi

echo
echo "## OWNER ITEMS"
# See "THE OWNER-ITEMS CONTRACT" in the header for what this section reads and
# why it reads two files instead of one.  Neither number below is verified; both
# are counted off prose, and the row exists to make them face each other.

# ---- the authority: the owner memo, newest status block first ----
MEMO=$(cd "$WT" && ls docs/dyadic/owner-items-*.md 2>/dev/null | sort | tail -1)
MEMON=$(cd "$WT" && ls docs/dyadic/owner-items-*.md 2>/dev/null | wc -l | tr -d ' ')
MCOUNT=""
MBLOCK=""
if [ -n "$MEMO" ] && [ -f "$WT/$MEMO" ]; then
  MBLOCK=$(grep -m1 '^## Status at wave ' "$WT/$MEMO" 2>/dev/null)
  if [ -n "$MBLOCK" ]; then
    # The first "N items await you" phrase at or after that heading.  The memo
    # writes the count as an English word, so it is mapped, not parsed as a
    # number; an unmapped word prints as UNVERIFIED rather than as a guess.
    MWORD=$(awk '/^## Status at wave /{f++} f==1 && /items await you/ {
        for (i = 1; i <= NF; i++)
          if ($i ~ /^\*\*[A-Za-z]+$/) { print tolower(substr($i, 3)); exit }
        exit
      }' "$WT/$MEMO")
    MCOUNT=$(awk -v w="$MWORD" 'BEGIN {
        n = split("zero one two three four five six seven eight nine ten eleven twelve \
thirteen fourteen fifteen sixteen seventeen eighteen nineteen twenty", a, /[ \t\n]+/)
        for (i = 1; i <= n; i++) if (a[i] == w) { print i - 1; exit }
      }')
  fi
fi
if [ -z "$MEMO" ]; then
  echo "  owner memo (AUTHORITY)   NOT FOUND (docs/dyadic/owner-items-*.md)"
else
  printf '  owner memo (AUTHORITY)   %s\n' "$MEMO"
  [ "$MEMON" != "1" ] &&
    printf '    !! %s memos match the glob; the newest by name was read\n' "$MEMON"
  if [ -z "$MBLOCK" ]; then
    echo "    latest status block    NOT FOUND (no '## Status at wave N' heading)"
  else
    printf '    latest status block    %s\n' "$MBLOCK"
    if [ -n "$MCOUNT" ]; then
      printf '    count it asserts       %s   (PROSE, off "N items await you")\n' "$MCOUNT"
    else
      echo "    count it asserts       UNVERIFIED (no 'N items await you' phrase"
      echo "                           in that block, or its number word is unmapped)"
    fi
  fi
fi

# ---- the lane artifact: the latest house note ----
NOTE=$(cd "$WT" && ls docs/dyadic/w*-house-note.md 2>/dev/null |
  sed 's/.*\/w\([0-9]*\)-house-note.md/\1 &/' | sort -n | tail -1 | cut -d' ' -f2)
NCOUNT=""
NHEAD=""
if [ -n "$NOTE" ] && [ -f "$WT/$NOTE" ]; then
  # Deliberately TOLERANT: case-insensitive, an optional section number, an
  # optional leading "The", an optional trailing ": ..." gloss.  The strict
  # match this replaces scored zero on six of the last ten house notes and said
  # so as "0" rather than as "not found"; see the header.
  NHEAD=$(grep -n -m1 -E '^#+[ \t]+([0-9]+(\.[0-9]+)*[ \t]+)?(The[ \t]+)?[Oo][Ww][Nn][Ee][Rr][ \t]+[Ii][Tt][Ee][Mm][Ss]' \
    "$WT/$NOTE" 2>/dev/null)
  if [ -n "$NHEAD" ]; then
    NCOUNT=$(awk -v start="${NHEAD%%:*}" 'NR > start && /^#/ {exit}
      NR > start && /^[0-9]+\./ {c++} END {print c + 0}' "$WT/$NOTE")
  fi
fi
if [ -z "$NOTE" ]; then
  echo "  latest house note        NOT FOUND (docs/dyadic/w*-house-note.md)"
else
  printf '  latest house note        %s\n' "$NOTE"
  if [ -z "$NHEAD" ]; then
    echo "    owner-items heading    NOT FOUND in it (so no count; this is the"
    echo "                           signal, not a zero)"
  else
    printf '    owner-items heading    line %s: %s\n' "${NHEAD%%:*}" "${NHEAD#*:}"
    printf '    numbered items under   %s\n' "$NCOUNT"
  fi
fi

# ---- the comparison, which is the whole point of printing both ----
if [ -n "$MCOUNT" ] && [ -n "$NCOUNT" ]; then
  if [ "$MCOUNT" = "$NCOUNT" ]; then
    printf '  memo and note AGREE      %s\n' "$MCOUNT"
  else
    printf '  !! memo and note DISAGREE  memo %s, note %s.  The memo is the\n' \
      "$MCOUNT" "$NCOUNT"
    echo "                             owner's record and the note is frozen at"
    echo "                             its own close, so a note item discharged"
    echo "                             after that close still counts in the note."
    echo "                             Read both; this board decides neither."
  fi
else
  echo "  memo vs note             NOT COMPARED (one side is missing above)"
fi
echo "  status of each item      UNVERIFIED (prose; not machine-checkable)"

echo
echo "## THE A6 FREEZE (GQ2/Roe/)"
ROECOMMIT=$(cd "$WT" && git log -1 --format='%h %ad  %s' --date=short -- GQ2/Roe/ 2>/dev/null)
ROESINCE=$(cd "$WT" && git log --format='%H' -- GQ2/Roe/ 2>/dev/null | head -1)
NOTESINCE=$(cd "$WT" && git log --diff-filter=A --format='%H' \
  "$ROESINCE"..HEAD -- 'docs/dyadic/w*-house-note.md' 2>/dev/null | wc -l | tr -d ' ')
printf '  last commit touching it  %s\n' "${ROECOMMIT:-none}"
printf '  house notes added since  %s\n' "$NOTESINCE"
echo "  review rounds frozen     UNVERIFIED (the campaign counts from the A6"
echo "                           adoption wave, which is not recorded in git)"

echo
echo "## WHAT THIS BOARD CANNOT SEE"
echo "  * whether a clause a row CARRIES is discharged somewhere else in the"
echo "    tree at the same instantiation: only the binder is machine-checked."
echo "  * whether a producer's conclusion is at the row's CANONICAL marking;"
echo "    \`GenAsmBranch\` does not pin \`nuP\` (GeneralAssembly.lean, W82-PIVOT)."
echo "  * STRENGTH.  The carries column counts binders, and fewer binders is"
echo "    not a weaker hypothesis: sqNuOrientedClearAtUnitPivot_of_pivotMoves"
echo "    carries 2 against _of_families' 3, and is the STRONGER ask (the whole"
echo "    unit-determinant pivot family, against two one-parameter ones)."
echo "  * producers in modules OUTSIDE THE UMBRELLA, and only those.  The probe"
echo "    imports \`GQ2\` and nothing else, so a \`prod\` scan sees every module"
echo "    in that import's transitive closure, whether or not any row names a"
echo "    declaration in it.  A module OUTSIDE the closure is still invisible"
echo "    to the scan -- but it is invisible to every consumer too, and the"
echo "    REGISTRATION section above enumerates the whole of GQ2/ from disk,"
echo "    so it names any such module rather than leaving it unremarked."
echo "    HISTORY, because this was the board's one standing defect and the"
echo "    fix is structural (W86-HOUSE), not another row: while the probe"
echo "    imported the ROWS' modules, the counts were a function of which"
echo "    modules the rows happened to reach.  (1) W84-HOUSE found the board"
echo "    printing \`producers: 0\` for MpcPivShift while wave 83's"
echo "    MpcOrb.mpcOrb_shift_of_marking produced it.  (2) W85-HOUSE found it"
echo "    printing 1 for MpcPivShift against a true 4, 3 for"
echo "    SqNuOrientedClearAtUnitPivot against a true 6, and 14 for"
echo "    SqMarkedForwardSupply against a true 16, because wave 84's own three"
echo "    modules were reached by no row.  Both were patched by adding rows;"
echo "    the patch does not generalise and wave 85 landed three more modules,"
echo "    so the import set is now the umbrella.  A row is still the way to"
echo "    put a NAMED declaration on the board; it is no longer what makes a"
echo "    module's producers countable."
echo "  * producers stated in a shape other than the head.  \`prod\` matches the"
echo "    conclusion's HEAD constant, so a theorem concluding \`A <-> P ...\`,"
echo "    \`Nonempty (P ...)\` or a structure field of type \`P ...\` is NOT"
echo "    counted.  mpcOrb_shift_iff_marking is such a statement.  Read"
echo "    \`producers: 0\` as \"nothing concludes it directly\", never as"
echo "    \"nothing in the tree bears on it\"."
echo "  * prose.  Every headline, table and inventory in the tree and in"
echo "    docs/dyadic/ is outside this tool and stales on its own."
