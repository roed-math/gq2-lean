# W79-MPC: the certificate producer the procyclic rows never had

Lane W79-MPC, ticket `docs/dyadic/w78-unimod-note.md` §6 item 2.  Produced against tree
`527adf51` on branch `claude/w79-mpc`, shared cache at the wave-78 umbrella (4350 jobs).
Verification of record: `scripts/mirror.sh` (sweep, check, gen).  **No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/MpcCertificate.lean`, declaration prefix `mpcCert`
(namespace `GQ2.Dyadic.Instances.MpcCert`).  Nothing else was touched.

---

## 1.  The headline

**The `Mpc` producer exists now, both fields land on the row `Main.lean` assigns them, and the
gap that made it necessary was one line of a definition, not a missing theory.**

`GeneralAssembly.genAsmCore` sends `.Mpc α r ε η h` to `DM α h`: the procyclic row's core is
*the same group* as the compact row's, and `LabuteInterface.BranchData.CoreCertificate` gives
the two rows the same certificate type.  What is different is the **marking**.  The branch
datum's `nuP` field at a procyclic row is `MProcyclicCore.mpcNu α r p`, whose ν-exponent vector

    (ν(μ₃), ν(μ₂), ν(μ₁), ν(μ₀)) = (1, s, p, −m·s),   s = 2^r,  p = ε·2^{r−1},  m = 2^{α−1}

carries `s = 2^r` at the boundary letter `C̄₀`, where the compact marking `nuM` carries `1`.  A
`MarkedCoreCertificateM` is *by definition* a normalization of the transported marking to `nuM`,
whose `C̄₀`-value is a unit, and wave 78's `fieldUni_pivotM_iff_level_zero` proved that being a
unit is the same thing as `B.r = 0`.  So:

> **No `MarkedCoreCertificateM` can exist at a field of level `r ≥ 1`.**

That is the sharp form of wave 78 §2.3's finding.  Wave 77's `fieldId_genAsmBranch_sqrt{Ten,
NegTen}` are not merely on the wrong row; the certificate type they produce is uninhabited at
those fields.  The fix is a certificate against `mpcNu`, which is `MarkedCoreCertificateMpc`.

## 2.  T1: the producer

`mpcCert_markedMatching` (§3 of the module) is the level-`r` analogue of MC5's
`mMarkedMatching`, and it runs on **exactly** the committed correction moves, in the same order
as `mMixHypothesis_of_scaling`.  Nothing new about `D_M` was needed:

| move | tree name | what it does | what it needs |
| --- | --- | --- | --- |
| M3 | `mScalingHypothesis_zero` (a theorem at `h = 0`) | scales `ν'(C̄₀)` by any unit | `v₂(ν'(C̄₀)) = r` |
| M2 | `dmTauDEquiv` (exact) | shifts `ν'(D̄)` by multiples of `ν'(C̄₀)` | `ν'(D̄) ≡ 1 (mod 2^r)` |
| M5 | `mMixFamily_coreMix` (exact, `α ≥ 2`) | shifts `ν'(B̄)` by multiples of the same pivot | `ν'(B̄) ≡ p (mod 2^r)` |
| (none) | `nu_dmA_eq` | forces the `Ā`-row to `−2^{α−1}·2^r` | nothing |

The forced `Ā`-row lands on `−m·s`, which is `mpcNuExp` slot `0` **on the nose**; that is the
one place where the design of `mpcNu` and the design of the `M`-frame have to agree, and they
do.  Handles are absent (`h = 0`), so there is no handle step.

The three right-hand-column conditions are collected as `MpcMarkedData α r p ν'`.  At `r = 0`
the first is `IsUnit (ν'(C̄₀))`, i.e. the committed `hpivot`, and the other two are vacuous
(`2^0 ℤ₂ = ℤ₂`), so this is the honest generalization of the compact clause.

**The point that makes the proof work.**  M3 says nothing about the `B̄` and `D̄` rows, so
applying it first could in principle destroy the two congruences.  It does not, and the reason
is the level: for a χ-preserving `Ψ` the ratio `Ψ g · g⁻¹` lies in `ker χ_M`, so `ν'` moves every
value only inside `ν'(ker χ) ⊆ 2^r ℤ₂` (`mpcCert_shift_mem`).  Residues modulo `2^r` are
therefore invariants of the whole χ-preserving action, and the algorithm may normalize the rows
in any order.  This is also why the level has to be carried as a hypothesis of the reduction and
not only at the field: it is what makes the other clauses stable.

Landed, in order: `mpcCert_nuMpc` and its four rows; `MpcChiKerLevel`, `MpcMarkedData`,
`mpcCert_shift_mem`, `mpcCert_dm{D,B}_shift`; `mpcCert_markedMatching`;
`MarkedCoreCertificateMpc`, `mpcCert_marked_matching_certificate_Mpc`;
`MarkedCoreCertificateKTwoMpc`, **`mpcCert_marked_matching_certificate_KTwoMpc`** (the
declaration the ticket asked for); `mpcCert_realization`,
**`mpcCert_genAsmBranch_of_orientedMpc`**.

### 2.1  What the level does *not* give, and why that is a finding

At `r = 0` the tree gets the pivot clause free from the level: `isUnit_nu_dmC_of_chiKer` is an
equivalence at rank four.  **At `r ≥ 1` the analogue is false**, and this lane's reading of the
frame is why.  On `DM α 0` a marking is its triple `(ν'(B̄), ν'(C̄₀), ν'(D̄))` (`mNu_frame`), the
available moves scale the second by units and shift the first and third by multiples of it, so
three separate quantities are invariant: the 2-adic **valuation** of `ν'(C̄₀)`, and the residues
of `ν'(B̄)` and `ν'(D̄)` modulo it.  The level `ν'(ker χ) = 2^r ℤ₂` pins none of them
individually.  A marking with `v₂(ν'(C̄₀)) = r + 1` and `ν'(B̄)` of valuation `r − 1` has level
`r` and is *not* equivalent to `mpcNu α r p`; so does one with `ν'(D̄)` even at `r = 1`.

So the procyclic rows genuinely need more field-side arithmetic than the compact rows did, and
the amount is exactly three congruences.  Their shapes are not arbitrary:
`FieldBranchSelector.Matches` at an `.Mpc β r ε η` row asks for `r = Q.r`, for
`negOneVal = ε·2^{r−1} (mod 2^r)`, and for `IsEtaFor Q.datum u η`.  The `B̄` congruence is the
second of those read on the core (`χ_M(B̄) = −1`, so `B̄` is the `−1` letter), and the `D̄`
congruence is the marking half of the third (`D̄` is the χ-generator).  The selector and the
marked core are asking the same three questions.

### 2.2  Necessity, proved

Two directions were landed so the row shape is not merely assumed:

* `mpcCert_level_le_of_pivot`: the pivot clause forces `B.r ≤ r`.  (`C̄₀ ∈ ker χ_M`, so
  `nu_ker_chi_le` puts its transported value in `2^{B.r} ℤ₂`, and a value of valuation exactly
  `r` cannot be more divisible.)  At `r = 0` this reads `B.r = 0` and recovers wave 78's
  `fieldUni_level_zero_of_pivotM`.
* `mpcCert_level_le_of_certificate`: **the certificate alone** forces `B.r ≤ r`, with no clause
  carried, because the corrected image of `C̄₀` lies in `ker χ_cyc` and carries `2^r` on the
  nose.

Both at the standard three axioms.  The reverse inequality is not a theorem about the
certificate (the level can be smaller than the row's `r` only if the field sits on a different
row), and it is part of what the per-field `Prop` asserts.

## 3.  T2: the two fields

Wave 77's range identities `fieldId_hrange_sqrt{Ten,NegTen}` are untouched by wave 78's
correction, and `fieldId_chosenEquivM_sqrt{Ten,NegTen}` supply the oriented equivalences.  With
those plus §2:

* **`mpcCert_genAsmBranch_sqrtTen`**: `∃ G : GenAsmBranch KSqrtTen B, G.pres = .Mpc 2 1 false .one 0`,
  over `MpcRowData_sqrtTen B`;
* **`mpcCert_genAsmBranch_sqrtNegTen`**: `∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0`,
  over `MpcRowData_sqrtNegTen B`.

Both over the field's own `MarkedRecip` bundle and the standing instance binders, on the rows
`Main.lean:136-137` and `GeneralAssembly.genAsm_core_sqrt{Ten,NegTen}` assign, with `p false 1 = 0`
and `p true 1 = 1`.  The marking triple is discharged at the row's own canonical marking
(`mpcNu_surjective`, and the `ztwoIota` seam is `rfl`), so nothing about `nuP` is carried.

**The one named `Prop` per field** is

    MpcRowData_sqrtTen B    :=  B.r = 1  ∧  MpcMarkedData 2 1 (p false 1) (ν_ur ∘ e_sqrtTen)
    MpcRowData_sqrtNegTen B :=  B.r = 1  ∧  MpcMarkedData 2 1 (p true 1)  (ν_ur ∘ e_sqrtNegTen)

i.e. the level plus the three congruences, at wave 77's chosen equivalence.  The tree carries
none of it: wave 78 §2.3's two arguments for `B.r = 1` are hand computations that were never
formalized, and §2.1 above shows the residues are independent of the level in any case.  The
`B.r = 1` conjunct alone would not suffice.

**Reduction available but not taken.**  At the `ε = false` row (`ℚ₂(√10)`, `p = 0`) the `D̄`
congruence should follow from the other two plus surjectivity of the transported marking: with
`ν'(C̄₀)` even and `ν'(B̄)` even, only `ν'(D̄)` can be odd.  Making that a theorem needs "the image
of a continuous marking is the closed subgroup generated by its values at the marked
generators", which the tree does not state; it is a clean follow-up that would shrink `ℚ₂(√10)`'s
`Prop` from three clauses to two.

## 4.  T3: the selector scoreboard, all five quadratic rows

What the **selector half** (the branch datum) of the general statement now costs, per row.  This
is the whole selector side; the residual `GenAsmRowResidual` blocks are separate and are listed
after the table.

| row | field | `pres` | branch datum | carried |
| --- | --- | --- | --- | --- |
| 1 | `ℚ₂(√−2)` | `.N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | **nothing** |
| 2 | `ℚ₂(√2)` | `.M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | **nothing** |
| 3 | `ℚ₂(√5)` | `.M0 2 0` | `fieldUni_genAsmBranch_sqrtFive_of_unramified` | `fieldUni_TwoIsUniformizer KSqrtFive` (one Prop) |
| 4 | `ℚ₂(√10)` | `.Mpc 2 1 false .one 0` | `mpcCert_genAsmBranch_sqrtTen` | `MpcRowData_sqrtTen` (one Prop) |
| 5 | `ℚ₂(√−10)` | `.Mpc 2 1 true .one 0` | `mpcCert_genAsmBranch_sqrtNegTen` | `MpcRowData_sqrtNegTen` (one Prop) |

**Total: three `Prop`s over five rows, and each is a self-contained arithmetic statement about
one field.**  None is a classification hypothesis, none is a marked-core hypothesis, and none is
about the general theory.  Row 3's `fieldUni_TwoIsUniformizer KSqrtFive` is wave 78's, a
sibling's / follow-up territory: it is `∀ z ∈ K, z ≠ 0, ‖z‖ < 1 → ‖z‖ ≤ ‖2‖` at `ℚ₂(√5)`, and
wave 78 §6 item 1 records the intended proof (`t² − 5u²` has even valuation, because
`t'² − 5u'² ≡ −4 (mod 8)` at units).  It is **not** built here.

Rows 4 and 5 are new: before this lane they had no branch-datum route at all, since their `M0`
route was the wrong row and its clause unsatisfiable.

### What remains beyond the selector

Unchanged by this lane, and the same at every row (wave 78 §4):

* **ASK**, the arithmetic counting pack at `galKProfinite K`: `exactLifting`, `stokes`,
  `determinant` (the Gauss-`Z` residue, still with no `K` clone and no owner lane).  Ledger field
  5 stays discharged by `KSupply.scalarHilbert_galK`.
* **CAND**, the candidate-side `WordCertificate` over the row's own slot.  At rows 4 and 5 the
  committed producers are `Instances.Sqrt10.*` and `Instances.SqrtNeg10.*`, built on
  `mpcCorePresentationUnit` / `mpcCompat` / `mpcTameSpecializes`, which consume **`mpcNu α r p`**
  as their `ν_P`.  That is the same marking this lane's branch datum installs in `GenAsmBranch.nuP`,
  so the two halves compose at those rows without a translation step.

## 5.  Axiom pins

Recorded in the module's §7, one line per declaration, measured against the mirror.  Three sets,
all already committed; this lane introduces no axiom.

* **The standard three** on §1, §2, the realization, the level transport, and both necessity
  directions.  The frame and bundle arithmetic costs no axiom.
* **Plus `peripheralCyclotomicAction`** on `mpcCert_markedMatching` and everything downstream.
  The single source is `MScaling.mScalingHypothesis_zero`, the M3 row; wave 78's `M`-row data
  carry the same axiom, so the procyclic route adds nothing there.
* **Plus the even route's endpoint set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on the two field rows, through
  `fieldId_chosenEquivM_sqrt{Ten,NegTen}`.  This set appears already in the *statements* of the
  two named `Prop`s, because the clause is asserted at wave 77's chosen equivalence.

So `mpcCert_genAsmBranch_sqrt{Ten,NegTen}` sit at **exactly** the axiom set of wave 77's
`fieldId_genAsmBranch_sqrt{Ten,NegTen}`: moving the two fields off the vacuous `M0` row and onto
the row they belong on costs no axiom.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 6.  What is next

1. **The three `Prop`s.**  `fieldUni_TwoIsUniformizer KSqrtFive` (wave 78's, already ticketed)
   and `MpcRowData_sqrt{Ten,NegTen}`.  The latter two are genuine local arithmetic: the level
   `B.r = 1` (wave 78 §2.3 gives two proofs, both hand computations; the norm one,
   `(2, ±10)₂ = −1`, looks the more formalizable) and the three residues of `ν_ur` at the images
   of `C̄₀`, `D̄` and `B̄`.
2. **The `ε = false` reduction** of §3, which would drop `ℚ₂(√10)` to two clauses: it needs the
   image of a continuous marking to be the closed subgroup generated by the generator values.
3. **A general-`h` procyclic dictionary**, if any future row needs one: `Instances/Cores.lean`
   §9 records that `MProcyclicCore` is built at `h = 0` only, and this lane inherits that
   restriction (`MarkedCoreCertificateMpc` is stated at `h = 0`).  No frozen instance needs it.
4. **Wave 77's §5/§7 and wave 78's §2.3 can now be closed out** on the two procyclic rows: the
   successor producer they both point at exists, and the rows are `.Mpc 2 1 ε .one 0`.
