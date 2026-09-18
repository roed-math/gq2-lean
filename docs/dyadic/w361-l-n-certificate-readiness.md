# W361 — uniform L/N certificate and publication audit

**Status: staged, read-only audit of the existing proof producers, 2026-09-17.**
This is not an amendment of the selection freeze, a generated appendix, or an approval of a
new certificate format. It audits whole families, not the finite fixture battery. The target
is the ten-item standard in `refs/dyadic-presentations-formalization-ledger.md` §7 and
`plan.md` §7(7). The selected field endpoint retains the ramified-`i` hypothesis; this document
does not broaden its field scope.

**15:44 UTC artifact refresh:** `GeneralTemplateLNCanonical.lean` now proves
canonical serialization/denotation for these legacy words without changing the
old grammar. A separate exporter and renderer supply six staged L/N0/exactly
displayed-Npc word specimens, with 39 tests and strong Lean replay passing.
These are word displays, not full ten-item L/N packets; the five frozen appendices
and their 40 TODO invocations are untouched. See `w361-general-ln-export.md`.

## 1. Bottom line and exact parameter coverage

The completed L, N0, and Npc source theorems already produce genuine `WordCertificateRN`
records, including full affine determinant clauses. Their generic analytic endpoints were
rechecked with the default Lean runner during this audit and print exactly
`[propext, Classical.choice, Quot.sound]`:

| Family | Actual word and uniform certificate producer | Scope, not a fixture assertion |
|---|---|---|
| L | `Words.LSq.lSqW h`; `LSquare.wordCertificateRN_lSq_pow` in `Instances/GammaLSourceArfGeneral.lean` | Every `h`; `q = 2^f` with **`Odd f`**. The final producer is not stated for arbitrary even `q`. |
| N0 | `Words.nCompactW alpha h`; `WordPhaseCompactNFinal.wPcNWordCertificateRN` | Every `h`, `2 ≤ alpha`, `q ≠ 0`, `Even q`. |
| Npc | `Words.Npc.npcWUnit alpha r h eta`; `NpcDeterminantFinal.npcWordCertificateRN` | Every `r,h`, `2 ≤ alpha`, `q ≠ 0`, `Even q`, and **`d : NpcDisplayFor eta`**. Selected procyclic branches additionally have `1 ≤ r`. |

The field-selection adapters are already present: `FieldFamilyCampaignBoundary` has
`hasSelectedRowResidualRN_l`, `_n0`, and `_npc`; the even adapters use
`FieldFamilySelectionRangeFinal.n0RowResidualRN_of_familySelection_matchesRange` and its Npc
analogue. The L adapter proves the required odd residue degree from the selected odd field
degree. Thus an old intermediate `hplane` assumption in `NpcFamilyFinal` is not a remaining
final assumption: `NpcPlanePrimitiveField` and the range wrapper discharge it.

Two qualifications are essential:

* `NpcDisplayFor eta` means an odd rational `EtaData` represents `eta` **exactly**, not merely
  modulo `2^r`. `npcWUnit_eq_display` then proves literal word equality.
  `SemanticSelected.exists_displayedEtaLift_of_not_even` chooses an integral lift of the
  required residue, with its display. It does **not** prove that every externally prescribed
  `2`-adic unit has a finite rational display. The selected-field theorem is unrestricted by
  this choice; a bare all-external-units display/export theorem would be a different assertion.
* Standard-three analytic word certificates do not make the field theorem axiom-free.
  Field arithmetic/reciprocity hypotheses and inherited axioms remain as documented in
  `literature-axioms-dyadic.md`; none was added by this audit.

## 2. Literal words, specialization, and resolver scope

Use the existing semantic constructors without changing associations or replacing them by
their simplified displays. Write `H_h` for the handle product in the appropriate alphabet.

* L is the **square-core** word
  `(x0^sigma)^-1 (x0^-3 tau)^omega2 x1^2 [x1,x1^sigma2] H_h`, at degree `2h+1`.
  It is not the retired collector word. `Words/L.lean` proves
  `eval_pro2_lSqW_eq_sqRelWord` for all `h`; the `h=0` value agrees with the existing Roe
  relator. `lCanonicalTameSpecialization` supplies the actual tame specialization.
* N0 is `x0^(2+2^alpha) [x0,x1] (x2^sigma)^-1 (x2 tau)^omega2 H_h`, at degree `2+2h`.
  The conjugator is **sigma**, not sigma2. `Words/N0.lean` has `pro2_nCompact` and
  `eval_pro2_nCompact`; the final certificate uses `genCertNTameSpecializes` and
  `genCertNProTwoWord` at every rank.
* Npc has `A=sigma^etahat`, `B=sigma^(2^r)`,
  `delta0=(x0 tau)^omega2 x0^-1`,
  `D=delta0^A (delta0 delta0^A)^(B^-1)`, and correction `[D,x1]`, in the unchanged
  `Words.Npc.npcW` constructor. `eval_pro2_npcW` proves that the correction disappears in
  the pro-2 specialization. `NpcCore.npcProTwoWordUnit` and the candidate certificate
  supply the semantic arbitrary-displayed-unit specialization and actual tame map.

L and N0 are omega2-only words. Npc is **not** omega2-only; the genuine eta exponent must
not be replaced by the omega resolver. `Count/Frozen.lean` defines `npcResolver N d` with
separate values at omega2 and `d.toZhat`; its resolution and endpoint theorems feed the later
phase and Stokes proofs. `Count/Resolve.lean` even contains a failed-resolution witness for
the obsolete constant-resolver approach. Expressions below using `A` mean its actual
resolved action `S^(E d.toZhat)`, not an independently guessed scalar.

## 3. Fox matrices: genuine existing reflected records

Let `S,T` be the sigma/tau actions on a finite elementary-two coefficient module, with wild
actions trivial. Let `N_q(T)=1+T+...+T^(q-1)`. The universal tame row, under the actual tame
relation, is

`S^-1(T-1) a_sigma + (S^-1-N_q(T)) a_tau`.

When tau acts trivially and `q` is even this is `S^-1 a_tau`. In the ramified formulas tau is
fixed-point-free and its omega2 part acts trivially. The rows are identities on **all
cochains**, not just the cocycle kernel. Every handle column vanishes at first order.

| Family | Unramified wild row | Ramified wild row |
|---|---|---|
| L | `a_tau + (1+S^-1) a_x0` | `S^-1 a_x0` |
| N0 | `a_tau + (1-S^-1) a_x2` | `-S^-1 a_x2` |
| Npc | `(A^-1-1) a_x0 + a_tau + (1-B^-1) a_x2` | `(A^-1-1) a_x0 - B^-1 a_x2` |

The precise APIs are `Certificates.LSq.foxD_lSq_unram/ram`,
`Certificates.foxD_nCompact_unram/ram`, and
`Certificates.Npc.foxD_npc_unram/ram`. The N rows only need `1 ≤ alpha` for their parity
calculation; this does not weaken the final certificate's `2 ≤ alpha` requirement.

N0 already has full **two-row `FoxCertificate` records**:

* `nCompactJacobianCertUnram`: row operation `wild += S*tame`, leaving pivots
  `S^-1` on tau and `1-S^-1` on x2.
* `nCompactJacobianCertRam`: scale the x2 column by `S`, with carried inverse `S^-1`;
  the wild row becomes the x2 unit pivot, leaving the universal tame row intact.

Npc likewise has `npcJacobianCertUnram` and `npcJacobianCertRam` for all parameters. The
unramified operation is the same row addition, leaving **two** blocks
`A^-1+1` and `1+B^-1`. The ramified record's `npcRamOps` carries the scale by `B`, inverse
`B^-1`, and the x0-clearing transvection; its replay gives the x2 unit pivot. Read operation
composition in the record's convention, not from an unverified prose ordering.

The Npc unramified symbolic record intentionally stops at two blocks. It does not certify
that either block is a unit in the unrestricted operator algebra. The exact finite-module
tests are `isUnit_x0Block_iff` and `isUnit_x2Block_iff`; the eventual faithful boundary proof
derives its stronger action conditions. No class-by-class computation is needed.

L's original records in `Certificates/LFox.lean` are **`FoxRowCertificate`**, including
`lSqWildRowCertUnram`, `_Ram`, `_Split`, and `lSqWildRowPivotCert`. The last uses a
tau/x0 transvection to reduce the single wild row. It is not a two-row reduction: the
column operation also affects the tame row of a full matrix.

**Checked W361 closure:** the additive `Certificates/LJacobian.lean` now supplies the full
original-format records `lSqJacobianCertUnram`, `lSqJacobianCertRam`, and
`lSqJacobianCertScalar`, uniformly in `h`, with the literal `lSqW h` and supplied `E,E2` in
their result types. Independent read-through and fresh axiom prints confirm standard-three
for all three. Unramified uses `wild += S*tame`, with target blocks `S^-1` at tau and
`1-S^-1` at **x0**; sigma fixed-point-freeness is not required for this equality. Ramified
scales **x0** by `S` with carried inverse `S^-1`, retaining the universal tame row and an x0
unit pivot. It requires the actual tame relation, tau fixed-point-freeness, and trivial
tau-omega2 action, but no wild-relator death. Scalar subtracts the tame row and has the
literal target `(tau,0)` under trivial generator actions and even `q`. No assumed matrix
identity is an input. Thus the L two-row packaging gap is closed, not merely anticipated.

Scalar degeneracy must remain visible: if all actions are trivial, the two rows reduce to
tau/tau, not to two independent pivots. More generally, the simple-module branch matrices
are not one identical diagonal matrix for every reducible coefficient module.

## 4. Hessians: the completed Npc proof does not use the old slice as its normal form

Use the full extraspecial factor set `(f,m)` and quadratic refinement `q_V`, not just its
polar form `B_V`. All ranks have genuine evaluated word identities:

* `Certificates.LSqStokes.hessRelZ_lSq` at `x0=0` is
  `q_V(c1)+B_V(c1,U c1)+sum_j B_V(u_j,v_j)`, with `U=(S^E(omega2))^-1`.
  This is the Wall head `qDouble q_V U`, not the compact N plus form.
  `GammaLUnramifiedPhase.lSqWallHandlePhase` and the ramified graph-phase modules transport
  it to actual source classes. L's Gauss sign needs the action/Arf argument; the final
  `GammaLSourceArfGeneral` endpoint closes it at the stated odd residue degree.
* `Certificates.hessRelZ_nCompact` at `x2=0` is
  `q_V(c0)+B_V(c0,c1)+sum_j B_V(u_j,v_j)` for `2 ≤ alpha`.
  `WordPhaseCompactNData.wPcNComparison_unramifiedHead`, `_ramifiedHead`, and
  `wPcN_branchFreeSupply` connect this to the actual source quotient at every `h`.
* The old `Certificates.Npc.npcHessianCertificate` is a genuine original record, but on the
  **two-coordinate Gate-E slice**. It takes quadraticity of `npcQ0`, a two-sided inverse of
  `Lc=A^-1+B+BA^-1`, and a cardinality witness. `npc_word_eq_certQ` is the corresponding
  `h=0`, `x2=0` word equation. The general handle identity also exists. These premises
  cannot silently be deleted: `pin_lcOp_zero` is a checked zero-operator example at `r=0`.

The completed Npc determinant follows a different, stronger full-offset route:

1. **Unramified:** `NpcUnramifiedFullOffsetHessian.hessRelZ_npcW_evenPhiNormal` uses the
   genuine cocycle coordinate `x2=Phi(c0)`, giving
   `d_un(c0)+B_V(c1,Phi(c0))+sum B_V(u_j,v_j)`.
   `Phi` solves `(1-B^-1)Phi(c0)=(A^-1-1)c0`.
   `NpcUnramifiedComparison.wPnpcPhiCoordsEquiv` changes the first coordinate by the
   proved additive equivalence `Phi`; `NpcUnramifiedDiagonal` proves quadraticity of the
   resulting diagonal. The fixed-point-free power conditions are derived at the actual
   boundary in `NpcBoundaryFinal`, not retained in its final supply.
2. **Ramified:** `NpcRamifiedFullOffsetHessian.hessRelZ_npcW_evenTwistedNormal` uses
   `x2=B(A^-1-1)c0`. The actual cross term is `B_V(c1,A^-1 c0)`, because
   `twistedBoundary_add_lc` proves `B(A^-1-1)+Lc=A^-1` in characteristic two.
   Thus the cross-coordinate change is invertible with no inverse-Lc hypothesis.
   `NpcRamifiedDiagonal` proves the full diagonal is quadratic, including its omega/power
   charge; `NpcRamifiedComparison` connects the result to source classes.

Both branches therefore reach `wPnpcWallHandlePhase d0 q_V h` with a proved quadratic
`d0`, followed by a uniform Gauss calculation. The old generated Npc item 8 asks for the
Gate-E polynomial with an invertible `Lc`; displaying that as the **actual completed
normal-coordinate proof** would be misleading. This is a required content correction,
not merely a missing TeX transcription. The old slice calculation remains valid in its
stated scope.

## 5. Original record interface versus completed affine proof

`Word/Hessian.lean` defines `HessianCertificate` with a **linear** change of variables,
quadraticity, nonsingularity, and an attached `PhaseCoverCertificate`. The latter includes
cardinality/Gauss data **and** `polar_id`/`kappa_id` tying the endpoint to the factor set.
An ordinary equivalence preserving values suffices for Gauss sums but is not automatically
a linear change of variables or a polar congruence.

The older original records are `compactN_certificate` (the two-coordinate N0 head) and
`npcHessianCertificate` (the qualified old Npc head). `nCompact_word_gaussSum` consumes the
former at `h=0`. Full-handle phase formulas and final full affine determinant certificates
are proved separately. **Subsequent W361 closure:** the original all-rank source records
now exist in `CompactNHessianCertificates`, `NpcHessianCertificates`, and
`LHessianCertificates`. Each retains the actual comparison map, proved additive and then
F2-linear, plus the full quadratic identity and original affine-phase fields. Npc uses
the full-offset d0; L uses its actual qDouble/graph operator, not a plus-form substitution.
L's unramified and ramified signs remain minus and plus respectively.

`CompactNBoundaryHessianCertificates.compactNBoundaryHessian` and
`NpcBoundaryHessianCertificates.npcBoundaryHessian` derive all head-sector premises at
every actual relevant boundary lift. The latter retains the old uniform-Hsimp input
(already supplied for the selected exact displays); its d0 remains explicit/existential,
not falsely identified with qbar. Independent default compiles and axiom checks pass.
L's head adapters retain exactly the existing head-model/SourceArfData inputs.
`LBoundaryHessianCertificates.lBoundaryHessian` now derives those inputs at the
actual relevant boundary, for q=2^f with odd f, and returns the original record
with both precise sign equivalences. Its default compile and standard-three
axiom check pass. Thus the named boundary-record packaging task is closed too.

The arbitrary-diagonal polar matrix is now explicitly `[[L,1],[1,0]]`, inverse
`[[0,1],[1,-L]]`, with swapped handles; `WordPhaseWallHandlePolarInverse` constructs L
from finite nonsingular duality. For the odd L head, `WordPhaseOddPolynomialInverse`
proves the finite inverse of J=1+U+U^-1 under the existing two-power action period:
`J^-1=J^(2^k-1)=sum(i<2^k)(U+U^-1)^i`. Neither matrix identity discards the quadratic
diagonal or determines its Gauss sign by polarization alone.

## 6. Ten-item compositional appendix inventory

| Ledger item | Uniform proof content available | Still needed for acceptance publication |
|---|---|---|
| 1. Exact tree | `rawLsq`, `rawNCompact`, `rawNpc`; semantic constructors above | Synchronized all-parameter display and exact source binding. |
| 2. Two specializations | Pro-2 and actual tame producers; included in each `WordCertificateRN` | Generate reductions for the generic word, with exact core and marking, not just a fixture. |
| 3. Fox Jacobian | All-cochain rows in §3 | Print both rows and coefficient hypotheses, distinguishing scalar/simple profiles. |
| 4. Invertible operations | Full L/N0/Npc operation lists/inverses, including new `LJacobian` | Generate the actual lists and their replay references. |
| 5. Reduced matrix | Actual L/N0/Npc `FoxCertificate.target` | Do not replace Npc's honest two-block stop by a uniform false unit claim. |
| 6. Stokes | Generic word-chain identity and each final certificate's `stokes`; action-image/dévissage modules discharge all coefficients | Display chain maps/resolver and connect them to the literal word. |
| 7. Extraspecial Hessian | All-rank full-value formulas in §4, including diagonal charges | Generate those actual formulas; retain factor-set `m`, not just the polar matrix. |
| 8. Quadratic change | Actual all-rank original source Hessian records, with linear coordinate maps and full phase | Generate these records and correct Npc's requested endpoint. |
| 9. Affine cover | Complete `AffineDeterminantCertificate` for each family; all-rank original Hessian records include phase-cover fields | Synchronize their exact fields and actual-boundary hypotheses. A base Gauss sign alone is insufficient. |
| 10. Same-tree hash | Legacy fixture hashes plus newly checked uniform factory-denotation bridges | Generated proof/word synchronization, not an extrapolation from sample hashes. |

At audit time `generated/appendix/rawLsq_n1.tex`, `rawNCompact_alpha2_h0.tex`, and
`rawNpc_a2_r1_eta1_1_h0.tex` each still have all eight TODO slots for items 2–9. These files
are not evidence that the formal analytic proofs are absent; conversely their word hashes
do not fill those slots.

The historical denotation bridge was fixture-only: four L pins (`h=0,1,2,3`), four N0 pins,
and seven Npc pins. The old comments in `Words/N0.lean` and `Words/Npc.lean` disclaim an
`h`-generic theorem, but this described proof availability, not a semantic obstruction.
**Checked W361 closure:** `Word/GeneralTemplateLN.lean` now proves `denote_rawLsq` for all
`h`, `denote_rawNCompact` for all `alpha,h`, and `denote_rawNpc` for all
`alpha,r,h,num,den`, in namespace `GQ2.Dyadic.GeneralTemplateLN`. Its
`denote_rawNpc_display` ties an exact `NpcDisplayFor` to the actual `npcWUnit`; the companion
well-formedness theorem uses the display's oddness fields. The generic handle-expander proof
preserves the existing ordered interpreter and factories, including L's rank-zero convention.
An independent default compile exits 0 with all ten pins standard-three. No old factory,
fixture, hash, or generated artifact was changed. This closes the uniform denotation gap;
it does not generate the missing appendix sections or create an all-parameter numeric hash.

## 7. Verification and remaining decisions

Fresh default checks, all exit 0:

* `Instances/GammaLSourceArfGeneral.lean`;
* `Instances/WordPhaseCompactNFinal.lean`;
* `Instances/NpcDeterminantFinal.lean`;
* `Word/GeneralTemplateLN.lean`, plus a scratch import printing all three new
  `Certificates/LJacobian.lean` sector records' axioms.

Their generic determinant/word-certificate pins are standard-three. This is not a fresh full
repository or hash-gate run. Generic factory-denotation replay and L two-row certificate
packaging are now checked, as are the subsequent all-rank original Hessian/phase records.
The remaining work is specific: correct Npc full-offset text in the authoritative
packet with owner authority; generate synchronized L/N sections;
and final build/hash/trust-boundary review. Adoption of the staged amendment, migration of
the generated appendices, census approval, and merge/release authorization remain owner
decisions. None is asserted here.
