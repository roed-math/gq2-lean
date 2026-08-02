/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Branches
import GQ2.Dyadic.Instances.SqrtNeg2
import GQ2.Dyadic.Instances.Sqrt2
import GQ2.Dyadic.Instances.Sqrt5
import GQ2.Dyadic.Instances.Sqrt10
import GQ2.Dyadic.Instances.SqrtNeg10
import GQ2.Dyadic.Instances.QTwo
import GQ2.Dyadic.SelectedWords
import GQ2.Dyadic.SemanticSelected
import GQ2.Dyadic.SourceTransport

/-!
# The final ramified-`i` theorem  (dyadic campaign, ticket AS5)

**Packet "Formal completion criterion"** (`dyadic-presentations-formalization-proof.tex`, the
theorem closing its remaining-inventory section): *"Apply \cref{thm:certificate-main} branch by
branch.  Proposition \ref{prop:sign-excluded} shows that the listed branches exhaust the
ramified-`i` case."*  This file is that application, stated over what the campaign actually
landed: the **frozen quadratic table** (`FrozenQuadRow`, §1 — the five rows of
`artifacts/reports/selection-freeze.md` §§1–5 at their frozen parameters), the per-row supplied
data (§3, the honest residual surface), the five per-row theorems and their assembly (§4–§5),
the certificate-uniformity theorem (§6), and the `n = 1` recovery of the `ℚ₂` theorem (§7).

## The statement landscape, and the recorded deltas against the packet

The packet's final theorem quantifies over **every** ramified-`i` `K`, with the branch shapes
`L`, compact/procyclic `N`, compact/procyclic `M` exhausting the case (packet Prop. 8.1 = F4's
`MarkedSplitting.classification_of_even`; five-shape exhaustiveness = F4's
`branchData_five_rows`).  The landed form differs in four ways, all deliberate and all visible
in the statements below rather than hidden (board rule: follow the LANDED spellings and record
the delta):

1. **Parameters are frozen, not generic.**  The instance headlines exist at the five frozen
   parameter rows (`N₀` at `α = 2`; `M₀` at `α = 3` and `α = 2`; `M_pc` at
   `(α, r, ε, η) = (2, 1, ε, 1)` for both signs `ε`) plus `n = 1`.  The final theorem therefore
   quantifies over `FrozenQuadRow`, and §2 records — as *theorems* — exactly which of F4's five
   constructor shapes the table realizes (`frozen_realizes_N0`/`_M0`/`_Mpc_both_signs`) and
   which it does not (`no_frozen_Npc`, `no_frozen_L`).
2. ⚠ **The procyclic-`N` shape (`Npc`) has NO instance** — `no_frozen_Npc` is a theorem, not a
   footnote.  Its frozen word exists (`GQ2/Dyadic/Words/Npc.lean`, certificate
   `N-noncompact-alpha2-r1-eta1_1-h0-v001`), its certificate layers landed (WNP lanes), but no
   `CoreReindex` dictionary and no `WordCertificate` constructor exist for it (AS3 built the
   compact-`M` and procyclic-`M` dictionaries; the procyclic-`N` one has no owner), and no
   quadratic field among the frozen five is on that row.  A packet-faithful "every branch"
   statement is therefore **not provable from the landed pieces**; this file states the
   provable frozen-table form and flags the gap here and on the board.
3. **`K` is supplied, not constructed.**  No concrete field object `ℚ₂(√−2)` etc. exists in
   the repository (ticket AS-F is probing literal instantiation); every statement is honestly
   parametrized over a `K` carrying the row's arithmetic through the binders
   (`hqK`-style pins live inside the per-row residual records).
4. **The `L` row enters at `n = 1` only, and its conclusion is `AbsGalQ2`.**  The `L` shape is
   the odd-degree branch; the frozen quadratic table is even-degree (`Compatible`, F1).  Its
   landed instance is the `n = 1` recovery (§7): three unconditional routes to
   `Γ_{L_sq,1} ≅ G_ℚ₂`, re-exported here as `lRow_candidate_equiv_absGalQ2`.

## The honest residual surface

The final theorem's hypotheses are the per-row records of §3, whose fields are **exactly** the
campaign's named residual binders — nothing is repackaged into an opaque certificate, so the
`G3` census sign-off can read the trust boundary off the structure fields:

* `FieldInputs` (row-independent): the arithmetic bundles' tame quotient `T` (AX4's B10-K
  enters only through this binder's *type*), packet §12's `params`/`ramified`/`ramifiedData`.
* `ResidualSqrtNegTwo` (pilot, compact `N`): the G-Lab pack (`fLab`, `piAb`/`hpiAb`/`hpiNu`,
  `horient`, `hScal`, `hpair`), ASK's carried leaves (`hexact`/`hstokes`), the candidate-side
  residuals (`hsimp`, `hsplit`/`hZcount`, `hdet`), and the degree pin `hdeg`.
* `ResidualSqrtTwo`/`…Five`/`…Ten`/`…NegTen` (`M` rows): the ν-normalization
  (`nuP`/`hnuSigma`/`hnuWild`/`hnuP`), the four analytic clauses (AS1 divergence 4), and the
  whole `KSupply` (whose own carried leaves are `KSupply.lean` §6).

The complete enumeration with provenance and literature citations is
`docs/dyadic/literature-axioms-dyadic.md` (the trust-boundary document, same ticket).

## Axiom posture

No axiom, no `sorry`, no `decide` is introduced here; the census stays at **11**.  Every
theorem inherits exactly its cited inputs' sets (measured per-headline in the trust-boundary
document): the five-row assembly prints the union of the instance headlines' sets — std-3 ∪
{B1, B6, B7, B9, B11a} — and the `n = 1` re-export prints the frozen `ℚ₂` capstone census.
B5-K/B10-K appear in **no** print: they enter only through the bundle *binders*
(`MarkedRecip`/`OrientedTameQuotientK`) a caller must supply.

## Sources

Packet §1 (Thm. 1.1 `thm:certificate-main`), §8 (Prop. 8.1 `prop:sign-excluded`, Cor. 8.2
`cor:minus10`), §12, and the closing "Formal completion criterion"; ledger §5.3, §7; freeze
report `general_2adic/artifacts/reports/selection-freeze.md` §§1–5 (vendored envelope copies:
`docs/dyadic/words/`); board `docs/dyadic/tickets.md` rows AS2–AS5, F4.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The frozen quadratic table

The five rows of the selection freeze, as one index type.  `branch` sends each row to its F4
branch datum (`BranchData`), `word` to its frozen word, `core` to its presented pro-2 core.
The values are the instance files' own pins, cited — nothing is re-derived. -/

/-- **The frozen quadratic table** — the five rows of
`artifacts/reports/selection-freeze.md` §§2–5 at their frozen parameters, one constructor per
landed instance file.  (The freeze's row §1, type `L`, is odd-degree and lives at `n = 1`;
see §7.) -/
inductive FrozenQuadRow : Type
  /-- `ℚ₂(√−2)`: compact `N`, `α = 2` — the pilot (AS2, `Instances/SqrtNeg2.lean`). -/
  | sqrtNegTwo
  /-- `ℚ₂(√2)`: compact `M`, `α = 3` (AS3, `Instances/Sqrt2.lean`). -/
  | sqrtTwo
  /-- `ℚ₂(√5)`: compact `M`, `α = 2`, `q_K = 4` (AS3, `Instances/Sqrt5.lean`). -/
  | sqrtFive
  /-- `ℚ₂(√10)`: procyclic `M`, `(α, r, ε, η) = (2, 1, 0, 1)` (AS3, `Instances/Sqrt10.lean`). -/
  | sqrtTen
  /-- `ℚ₂(√−10)`: procyclic `M`, `(α, r, ε, η) = (2, 1, 1, 1)` — packet Cor. 8.2
  (AS3, `Instances/SqrtNeg10.lean`). -/
  | sqrtNegTen
  deriving DecidableEq

namespace FrozenQuadRow

/-- The F4 branch datum of a frozen row (F1's `BranchData`, packet §8 vocabulary). -/
noncomputable def branch : FrozenQuadRow → BranchData
  | .sqrtNegTwo => .N0 2
  | .sqrtTwo => .M0 3
  | .sqrtFive => .M0 2
  | .sqrtTen => .Mpc 2 1 false 1
  | .sqrtNegTen => .Mpc 2 1 true 1

/-- The frozen word of a row (`n = 2` alphabet; the instance files' own pins). -/
noncomputable def word : FrozenQuadRow → PWord (Generator 2)
  | .sqrtNegTwo => Count.pilotW
  | .sqrtTwo => Instances.Sqrt2.word
  | .sqrtFive => Instances.Sqrt5.word
  | .sqrtTen => Instances.Sqrt10.word
  | .sqrtNegTen => Instances.SqrtNeg10.word

/-- The same frozen row, routed through the R5 constructor table.  In particular the two
procyclic rows use `Mpc.mpcW`, never the retired sign/relative-norm presentations. -/
noncomputable def selectedPresentation : FrozenQuadRow → SelectedPresentation
  | .sqrtNegTwo => .N0 2 0
  | .sqrtTwo => .M0 3 0
  | .sqrtFive => .M0 2 0
  | .sqrtTen => .Mpc 2 1 false .one 0
  | .sqrtNegTen => .Mpc 2 1 true .one 0

/-- Every frozen quadratic presentation has degree two when read through the constructor table. -/
@[simp] theorem selectedPresentation_degree (r : FrozenQuadRow) :
    r.selectedPresentation.degree = 2 := by
  cases r <;> rfl

/-- **Constructor-table regression.**  Selecting a frozen row through the general R5 table
returns definitionally the exact word already used by its proved instance theorem. -/
@[simp] theorem selectedPresentation_word_eq (r : FrozenQuadRow) :
    r.selectedPresentation.wordAt 2 (selectedPresentation_degree r) = r.word := by
  cases r <;> rfl

/-- The odd-degree base regression: the table selects the stabilized square-commutator word,
not the collector retained in the source paper as a safety net. -/
@[simp] theorem selectedPresentation_L_zero_word :
    (SelectedPresentation.L 0).word = Words.LSq.lSqW 0 := rfl

/-- The frozen row routed through the total semantic constructor table.  Unlike
`selectedPresentation`, this construction does not store rational display syntax. -/
noncomputable def semanticPresentation (r : FrozenQuadRow) : SemanticPresentation :=
  SemanticPresentation.ofBranch 0 r.branch

/-- Every frozen semantic presentation has the same degree two as its displayed counterpart. -/
@[simp] theorem semanticPresentation_degree (r : FrozenQuadRow) :
    r.semanticPresentation.degree = 2 := by
  cases r <;> rfl

/-- **Semantic constructor-table regression.**  On every frozen quadratic row, the total
arbitrary-unit selector defines exactly the already-frozen corrected presentation.  The
comparison is at `GammaR`: on the procyclic `M` rows the semantic word deliberately uses
`profPow`, whereas the frozen display word uses its finite syntax. -/
@[simp] theorem semanticPresentation_GammaR_eq (r : FrozenQuadRow) (q : ℕ) :
    GammaR 2 q (r.semanticPresentation.wordAt 2 (semanticPresentation_degree r)) =
      GammaR 2 q r.word := by
  cases r with
  | sqrtNegTwo => rfl
  | sqrtTwo => rfl
  | sqrtFive => rfl
  | sqrtTen =>
      change GammaR 2 q (Words.Mpc.mpcWUnit 2 1 0 1 0) =
        GammaR 2 q (Words.Mpc.mpcW 2 1 0 .one 0)
      exact Words.Mpc.GammaR_mpcWUnit_eq_display 2 1 0 0 q MpcDisplayFor.one
  | sqrtNegTen =>
      change GammaR 2 q (Words.Mpc.mpcWUnit 2 1 1 1 0) =
        GammaR 2 q (Words.Mpc.mpcW 2 1 1 .one 0)
      exact Words.Mpc.GammaR_mpcWUnit_eq_display 2 1 1 0 q MpcDisplayFor.one

/-- The odd-degree base regression for the total table. -/
@[simp] theorem semanticPresentation_L_zero_word :
    (SemanticPresentation.ofBranch 0 .L).word = Words.LSq.lSqW 0 := rfl

/-- The presented pro-2 core of a row (MC2's `DN`/`DM` at the row's `(α, h)`). -/
noncomputable def core : FrozenQuadRow → ProfiniteGrp
  | .sqrtNegTwo => SqrtNeg2.pilotP
  | .sqrtTwo => Instances.Sqrt2.core
  | .sqrtFive => Instances.Sqrt5.core
  | .sqrtTen => Instances.Sqrt10.core
  | .sqrtNegTen => Instances.SqrtNeg10.core

/-- Every frozen core is pro-2 (MC2's `isProP_DN`/`isProP_DM` at the row's pins). -/
noncomputable def coreIsProP : (r : FrozenQuadRow) → IsProP 2 ((r.core : ProfiniteGrp) : Type)
  | .sqrtNegTwo => isProP_DN 2 0
  | .sqrtTwo => isProP_DM 3 0
  | .sqrtFive => isProP_DM 2 0
  | .sqrtTen => isProP_DM 2 0
  | .sqrtNegTen => isProP_DM 2 0

/-- Every frozen branch datum is valid (F1's `Valid`: `2 ≤ α`, and `1 ≤ r` on procyclic
rows). -/
theorem branch_valid : ∀ r : FrozenQuadRow, r.branch.Valid
  | .sqrtNegTwo => le_refl 2
  | .sqrtTwo => Nat.le_succ 2
  | .sqrtFive => le_refl 2
  | .sqrtTen => ⟨le_refl 2, le_refl 1⟩
  | .sqrtNegTen => ⟨le_refl 2, le_refl 1⟩

/-- Every frozen branch datum is an even row, hence degree-compatible with every even-degree
field-parameter package (F1's `Compatible` is exactly the parity condition). -/
theorem branch_compatible (r : FrozenQuadRow) (P : FieldParameters) (hP : Even P.n) :
    Compatible P r.branch := by
  cases r <;> simpa [branch, Compatible] using hP

/-- **Merge gate 9, restated at the table**: the `ℚ₂(√−10)` row is F4's packet-Cor.-8.2 datum
`branchSqrtNegTen = .Mpc 2 1 true 1` — the procyclic parameters `(r, ε, η) = (1, 1, 1)`. -/
theorem sqrtNegTen_branch_eq_branchSqrtNegTen :
    FrozenQuadRow.sqrtNegTen.branch = branchSqrtNegTen := rfl

end FrozenQuadRow

/-! ## §2 The table audited against F4's exhaustiveness

Packet Prop. 8.1 (F4) says the five constructor shapes of `BranchData` exhaust the ramified-`i`
case (`branchData_five_rows`), the sign-Frobenius row being excluded
(`MarkedSplitting.classification_of_even`).  The theorems below record — positively and
negatively — which shapes the frozen table realizes.  The two negative statements are the
honest ones: they are what separates the landed final theorem from the packet's fully general
one (module docstring, deltas 2 and 4). -/

section Audit

/-- Every frozen row is on one of F4's five constructor shapes — the table is inside the
exhaustive classification (`branchData_five_rows` at the five pins). -/
theorem frozenQuadRow_branch_cases (r : FrozenQuadRow) :
    r.branch = .L ∨ (∃ α, r.branch = .N0 α) ∨ (∃ α rr η, r.branch = .Npc α rr η) ∨
      (∃ α, r.branch = .M0 α) ∨ (∃ α rr ε η, r.branch = .Mpc α rr ε η) :=
  branchData_five_rows r.branch

/-- The compact-`N` shape is realized by the frozen table (the pilot row). -/
theorem frozen_realizes_N0 : ∃ r : FrozenQuadRow, r.branch = .N0 2 := ⟨.sqrtNegTwo, rfl⟩

/-- The compact-`M` shape is realized at both frozen `α` values. -/
theorem frozen_realizes_M0 :
    (∃ r : FrozenQuadRow, r.branch = .M0 3) ∧ ∃ r : FrozenQuadRow, r.branch = .M0 2 :=
  ⟨⟨.sqrtTwo, rfl⟩, ⟨.sqrtFive, rfl⟩⟩

/-- The procyclic-`M` shape is realized at **both** sign values — the table-level echo of F4's
`eps_both_occur` (draft §7.3's `ℚ₂(√10)` has `ε = 0`, packet Cor. 8.2's `ℚ₂(√−10)` has
`ε = 1`). -/
theorem frozen_realizes_Mpc_both_signs :
    (∃ r : FrozenQuadRow, r.branch = .Mpc 2 1 false 1) ∧
      ∃ r : FrozenQuadRow, r.branch = .Mpc 2 1 true 1 :=
  ⟨⟨.sqrtTen, rfl⟩, ⟨.sqrtNegTen, rfl⟩⟩

/-- ⚠ **The procyclic-`N` shape is NOT realized by the frozen table** — the honest negative
result (module docstring, delta 2).  The `Npc` word and its certificate layers exist
(`Words/Npc.lean`, the WNP lanes); what does not exist is a `CoreReindex` dictionary and a
`WordCertificate` constructor for the shape, nor a frozen quadratic field on the row.  The
packet's "every branch" final theorem is exactly this theorem away from the landed one. -/
theorem no_frozen_Npc (r : FrozenQuadRow) (α rr : ℕ) (η : ℤ_[2]ˣ) :
    r.branch ≠ .Npc α rr η := by
  cases r <;> simp [FrozenQuadRow.branch]

/-- The `L` shape is not on the quadratic table either — it is the odd-degree branch, landed
at `n = 1` (§7), where its conclusion is `G_ℚ₂` rather than a supplied `G_K`. -/
theorem no_frozen_L (r : FrozenQuadRow) : r.branch ≠ .L := by
  cases r <;> simp [FrozenQuadRow.branch]

end Audit

/-! ## §3 The supplied per-row data

The record fields below are **verbatim** the instance headlines' binder lists — the campaign's
named residual surface, with provenance per field.  `FieldInputs` is the row-independent
field-side block (packet §12); the five `Residual*` records are the per-row blocks.  Nothing
here is new data: a `(FieldInputs, Residual*)` pair is exactly the argument list of the
corresponding instance headline, re-bound so that one branch-cased theorem can quantify over
"the supplied per-branch data" (board row AS5). -/

section Supply

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)

/-- **The row-independent field-side inputs** (packet §12 at a supplied `K`).

* `T` — AX4's oriented tame quotient *bundle* (B10-K enters only through this binder's type;
  the axiom `orientedTameQuotientAt` is never consumed by the theorems below).
* `params`/`params_n`/`params_qK` — F1's `(n, f, q_K)` package pinned to the quadratic slot.
* `ramified` — the standing ramified-`i` branch condition, in AX3-Q4's field language
  (`¬ HasEqualNormValueGroups`, never spelled through `qK`).
* `ramifiedData` — LG5's ramified-marking arithmetic input, in the `hcert` shape
  `local_gauss_K` consumes (constructor: `ramifiedCertificateOfSubtype`). -/
structure FieldInputs where
  /-- AX4's oriented tame quotient of `G_K` at `q_K` (bundle, not axiom). -/
  T : OrientedTameQuotientK B FF
  /-- F1's field-parameter package for `K`. -/
  params : FieldParameters
  /-- The slot's degree is `2` (quadratic table). -/
  params_n : params.n = 2
  /-- The slot's tame modulus is the residue cardinality `q_K = 2^f`. -/
  params_qK : params.qK = qOf K FF
  /-- The standing ramified-`i` hypothesis (AX3 memo Q4 field-language spelling). -/
  ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi
  /-- LG5's ramified-marking input (packet §12). -/
  ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq params.qK) D)
    (rho : ContinuousMonoidHom ↥(GalKsub K) D),
    (∃ v : V, c (tqTau params.qK) • v ≠ v) →
      Nonempty (RamifiedCertificate params (GalKsub K) V c rho)

/-- **The pilot row's residual data** (`ℚ₂(√−2)`, compact `N`, `α = 2`) — verbatim the binder
list of `SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` minus the `FieldInputs` block.

Provenance per field (the trust boundary; see also
`docs/dyadic/literature-axioms-dyadic.md`): `hdeg` the degree pin; `fLab` the N-Lab
Demushkin-classification identification (gate G-Lab, obligation MC-N's per-core hypothesis
state); `piAb`/`hpiAb`/`hpiNu` the abelianization slot AS2 discovered missing from the
marked-core composite (`toAbK` does not factor through `G_K(2)`); `horient` packet §7's
orientation datum; `hScal` MC-N's `NScalingHypothesis`; `hpair` marked-data
pair-unimodularity; `hexact`/`hstokes` ASK's carried leaves 2–3 (`KSupply.lean` §6); `hsimp`
the per-simple-module Stokes duality (owner ruling B1/Q3: hypothesis binder, never axiom);
`hsplit`/`hZcount` the `stageR136` recursion-side residues; `hdet` ⚠⚠ the candidate-side
Gauss clauses, whose supplier lane was never opened (CB caveat, 9-of-11). -/
structure ResidualSqrtNegTwo : Type 1 where
  /-- Degree pin `[K : ℚ₂] = 2`. -/
  hdeg : Module.finrank ℚ_[2] K = 2
  /-- G-Lab pack: the Labute/Demushkin identification of `G_K(2)` with the compact-`N` core. -/
  fLab : ContinuousMulEquiv ((DN 2 0) : Type) ((maxProPQuotient 2 (GalK K)) : Type)
  /-- G-Lab pack: the abelianization slot (AS2's discovered datum). -/
  piAb : ((maxProPQuotient 2 (GalK K)) : Type) →* GalKab K
  /-- The abelianization slot is continuous. -/
  hpiAb : Continuous piAb
  /-- ν-compatibility of the abelianization slot. -/
  hpiNu : ∀ g : GalK K, B.nu_ur (piAb (maxProPMk 2 (GalK K) g)) = B.nu_ur (toAbK K g)
  /-- G-Lab pack: packet §7's orientation datum. -/
  horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x
  /-- G-Lab pack: MC-N's scaling hypothesis. -/
  hScal : NScalingHypothesis 2 0
  /-- G-Lab pack: marked-data pair-unimodularity. -/
  hpair : IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnSigma 2 0)))))
    ∨ IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnX2 2 0)))))
  /-- ASK carried leaf: the `G_K`-side exact-lifting clauses. -/
  hexact : ExactLiftingSemantics (galKProfinite K) 2 (qOf K FF) SqrtNeg2.pilotP
    SqrtNeg2.pilotNuP (standardNumerics 2)
  /-- ASK carried leaf: the `G_K`-side Stokes clauses. -/
  hstokes : StokesDualityCertificate (galKProfinite K) 2 (qOf K FF) SqrtNeg2.pilotP
    SqrtNeg2.pilotNuP (standardNumerics 2) (smulZmod2GalK K)
  /-- Candidate-side residual: per-simple-module Stokes duality (`hsimp`). -/
  hsimp : SqrtNeg2.PilotHsimp (qOf K FF)
  /-- Candidate-side residual: the `stageR136` separation input. -/
  hsplit : SqrtNeg2.PilotStageSep (qOf K FF)
  /-- Candidate-side residual: the `stageR136` count input. -/
  hZcount : SqrtNeg2.PilotStageZ (qOf K FF)
  /-- ⚠⚠ Candidate-side residual: the Gauss-`Z` clauses (no supplier lane; CB 9-of-11). -/
  hdet : SqrtNeg2.PilotDet (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)

/-- **The `ℚ₂(√2)` row's residual data** (compact `M`, `α = 3`) — verbatim the binder list of
`Instances.candidate_equiv_galK_sqrtTwo` at `q := q_K` minus the `FieldInputs` block.

Fields: the ν-normalization (`nuP`/`hnuSigma`/`hnuWild`/`hnuP` — F3's `prop_3_4_three`
conditions read through AS3's `MCompactCore` dictionary; satisfiability hand-verified,
Lean witness = ticket AS3-b), the four analytic clauses (AS1 divergence 4: the
certificate ⇒ count bridges have no owner), and ASK's whole arithmetic package `KS`
(its own carried leaves: `KSupply.lean` §6). -/
structure ResidualSqrtTwo (T : OrientedTameQuotientK B FF) : Type 1 where
  /-- The abstract slot's ν-marking on the row's core `D_M(3,0)`. -/
  nuP : ContinuousMonoidHom ((Instances.Sqrt2.core : ProfiniteGrp) : Type) Ztwo
  /-- ν-normalization at `σ`. -/
  hnuSigma : nuP ((Instances.MCompactCore.mCorePresentation 3 0
    Instances.Sqrt2.alpha_valid).mark .sigma) = ztwoOne
  /-- ν-normalization at the wild letters. -/
  hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
    nuP ((Instances.MCompactCore.mCorePresentation 3 0
      Instances.Sqrt2.alpha_valid).mark (.wild j)) = 1
  /-- ν is onto. -/
  hnuP : Function.Surjective nuP
  /-- Analytic clause (ledger §5.2 field 3) at the row's candidate group. -/
  exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.word)
    (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.core nuP (standardNumerics (2 + 2 * 0))
  /-- Analytic clause (ledger §5.2 field 4). -/
  stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.word)
    (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.core nuP (standardNumerics (2 + 2 * 0))
    (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 5). -/
  scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.word)
    (2 + 2 * 0) (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 6), at the row's tame/pro-2 legs. -/
  determinant : AffineDeterminantCertificate
    (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.word) (2 + 2 * 0) (qOf K FF)
    Instances.Sqrt2.core nuP (standardNumerics (2 + 2 * 0))
    (tameOfSpec (2 + 2 * 0) (qOf K FF) Instances.Sqrt2.word
      (Instances.MCompactCore.mTameSpecializes 3 0 (qOf K FF) (qOf_ne_zero K FF)
        (even_qOf K FF)))
    (Instances.MCompactCore.mPro2 3 0 (qOf K FF) Instances.Sqrt2.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF))
    (Instances.MCompactCore.mCompat 3 0 (qOf K FF) Instances.Sqrt2.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF)
      (Instances.MCompactCore.mTameSpecializes 3 0 (qOf K FF) (qOf_ne_zero K FF)
        (even_qOf K FF)) nuP hnuSigma hnuWild)
    (scalarActionZmodTwo _)
  /-- ASK's arithmetic package (its carried leaves: `KSupply.lean` §6). -/
  KS : KSupply T (2 + 2 * 0) Instances.Sqrt2.core (isProP_DM 3 0) nuP
    (standardNumerics (2 + 2 * 0))

/-- **The `ℚ₂(√5)` row's residual data** (compact `M`, `α = 2`, `q_K = 4`) — verbatim the
binder list of `Instances.candidate_equiv_galK_sqrtFive` at `q := q_K` minus the
`FieldInputs` block.  Same shape as `ResidualSqrtTwo` at `α = 2`; see there for field
provenance. -/
structure ResidualSqrtFive (T : OrientedTameQuotientK B FF) : Type 1 where
  /-- The abstract slot's ν-marking on the row's core `D_M(2,0)`. -/
  nuP : ContinuousMonoidHom ((Instances.Sqrt5.core : ProfiniteGrp) : Type) Ztwo
  /-- ν-normalization at `σ`. -/
  hnuSigma : nuP ((Instances.MCompactCore.mCorePresentation 2 0
    Instances.Sqrt5.alpha_valid).mark .sigma) = ztwoOne
  /-- ν-normalization at the wild letters. -/
  hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
    nuP ((Instances.MCompactCore.mCorePresentation 2 0
      Instances.Sqrt5.alpha_valid).mark (.wild j)) = 1
  /-- ν is onto. -/
  hnuP : Function.Surjective nuP
  /-- Analytic clause (ledger §5.2 field 3). -/
  exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.word)
    (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.core nuP (standardNumerics (2 + 2 * 0))
  /-- Analytic clause (ledger §5.2 field 4). -/
  stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.word)
    (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.core nuP (standardNumerics (2 + 2 * 0))
    (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 5). -/
  scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.word)
    (2 + 2 * 0) (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 6). -/
  determinant : AffineDeterminantCertificate
    (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.word) (2 + 2 * 0) (qOf K FF)
    Instances.Sqrt5.core nuP (standardNumerics (2 + 2 * 0))
    (tameOfSpec (2 + 2 * 0) (qOf K FF) Instances.Sqrt5.word
      (Instances.MCompactCore.mTameSpecializes 2 0 (qOf K FF) (qOf_ne_zero K FF)
        (even_qOf K FF)))
    (Instances.MCompactCore.mPro2 2 0 (qOf K FF) Instances.Sqrt5.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF))
    (Instances.MCompactCore.mCompat 2 0 (qOf K FF) Instances.Sqrt5.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF)
      (Instances.MCompactCore.mTameSpecializes 2 0 (qOf K FF) (qOf_ne_zero K FF)
        (even_qOf K FF)) nuP hnuSigma hnuWild)
    (scalarActionZmodTwo _)
  /-- ASK's arithmetic package. -/
  KS : KSupply T (2 + 2 * 0) Instances.Sqrt5.core (isProP_DM 2 0) nuP
    (standardNumerics (2 + 2 * 0))

/-- **The `ℚ₂(√10)` row's residual data** (procyclic `M`, `(α, r, ε) = (2, 1, 0)`) —
verbatim the binder list of `Instances.candidate_equiv_galK_sqrtTen` at `q := q_K` minus
the `FieldInputs` block.  Procyclic twin of `ResidualSqrtTwo` through AS3's
`MProcyclicCore` dictionary (η enters as the `.one` display; AS3's finding: the dictionary
needs `η = 1`). -/
structure ResidualSqrtTen (T : OrientedTameQuotientK B FF) : Type 1 where
  /-- The abstract slot's ν-marking on the row's core `D_M(2,0)`. -/
  nuP : ContinuousMonoidHom ((Instances.Sqrt10.core : ProfiniteGrp) : Type) Ztwo
  /-- ν-normalization at `σ`. -/
  hnuSigma : nuP ((Instances.MProcyclicCore.mpcCorePresentation 2 1 0
    Instances.Sqrt10.alpha_valid).mark .sigma) = ztwoOne
  /-- ν-normalization at the wild letters. -/
  hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
    nuP ((Instances.MProcyclicCore.mpcCorePresentation 2 1 0
      Instances.Sqrt10.alpha_valid).mark (.wild j)) = 1
  /-- ν is onto. -/
  hnuP : Function.Surjective nuP
  /-- Analytic clause (ledger §5.2 field 3). -/
  exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.word)
    (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.core nuP (standardNumerics (2 + 2 * 0))
  /-- Analytic clause (ledger §5.2 field 4). -/
  stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.word)
    (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.core nuP (standardNumerics (2 + 2 * 0))
    (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 5). -/
  scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.word)
    (2 + 2 * 0) (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 6). -/
  determinant : AffineDeterminantCertificate
    (GammaR (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.word) (2 + 2 * 0) (qOf K FF)
    Instances.Sqrt10.core nuP (standardNumerics (2 + 2 * 0))
    (tameOfSpec (2 + 2 * 0) (qOf K FF) Instances.Sqrt10.word
      (Instances.MProcyclicCore.mpcTameSpecializes 2 1 0 (qOf K FF)
        Instances.Sqrt10.alpha_valid (qOf_ne_zero K FF) (even_qOf K FF)))
    (Instances.MProcyclicCore.mpcPro2 2 1 0 (qOf K FF) Instances.Sqrt10.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF))
    (Instances.MProcyclicCore.mpcCompat 2 1 0 (qOf K FF) Instances.Sqrt10.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF)
      (Instances.MProcyclicCore.mpcTameSpecializes 2 1 0 (qOf K FF)
        Instances.Sqrt10.alpha_valid (qOf_ne_zero K FF) (even_qOf K FF))
      nuP hnuSigma hnuWild)
    (scalarActionZmodTwo _)
  /-- ASK's arithmetic package. -/
  KS : KSupply T (2 + 2 * 0) Instances.Sqrt10.core (isProP_DM 2 0) nuP
    (standardNumerics (2 + 2 * 0))

/-- **The `ℚ₂(√−10)` row's residual data** (procyclic `M`, `(α, r, ε) = (2, 1, 1)` — packet
Cor. 8.2's parameters) — verbatim the binder list of
`Instances.candidate_equiv_galK_sqrtNegTen` at `q := q_K` minus the `FieldInputs` block. -/
structure ResidualSqrtNegTen (T : OrientedTameQuotientK B FF) : Type 1 where
  /-- The abstract slot's ν-marking on the row's core `D_M(2,0)`. -/
  nuP : ContinuousMonoidHom ((Instances.SqrtNeg10.core : ProfiniteGrp) : Type) Ztwo
  /-- ν-normalization at `σ`. -/
  hnuSigma : nuP ((Instances.MProcyclicCore.mpcCorePresentation 2 1 1
    Instances.SqrtNeg10.alpha_valid).mark .sigma) = ztwoOne
  /-- ν-normalization at the wild letters. -/
  hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
    nuP ((Instances.MProcyclicCore.mpcCorePresentation 2 1 1
      Instances.SqrtNeg10.alpha_valid).mark (.wild j)) = 1
  /-- ν is onto. -/
  hnuP : Function.Surjective nuP
  /-- Analytic clause (ledger §5.2 field 3). -/
  exactLifting : ExactLiftingSemantics
    (GammaR (2 + 2 * 0) (qOf K FF) Instances.SqrtNeg10.word) (2 + 2 * 0) (qOf K FF)
    Instances.SqrtNeg10.core nuP (standardNumerics (2 + 2 * 0))
  /-- Analytic clause (ledger §5.2 field 4). -/
  stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.SqrtNeg10.word)
    (2 + 2 * 0) (qOf K FF) Instances.SqrtNeg10.core nuP (standardNumerics (2 + 2 * 0))
    (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 5). -/
  scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) (qOf K FF) Instances.SqrtNeg10.word)
    (2 + 2 * 0) (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _)
  /-- Analytic clause (ledger §5.2 field 6). -/
  determinant : AffineDeterminantCertificate
    (GammaR (2 + 2 * 0) (qOf K FF) Instances.SqrtNeg10.word) (2 + 2 * 0) (qOf K FF)
    Instances.SqrtNeg10.core nuP (standardNumerics (2 + 2 * 0))
    (tameOfSpec (2 + 2 * 0) (qOf K FF) Instances.SqrtNeg10.word
      (Instances.MProcyclicCore.mpcTameSpecializes 2 1 1 (qOf K FF)
        Instances.SqrtNeg10.alpha_valid (qOf_ne_zero K FF) (even_qOf K FF)))
    (Instances.MProcyclicCore.mpcPro2 2 1 1 (qOf K FF) Instances.SqrtNeg10.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF))
    (Instances.MProcyclicCore.mpcCompat 2 1 1 (qOf K FF) Instances.SqrtNeg10.alpha_valid
      (qOf_ne_zero K FF) (even_qOf K FF)
      (Instances.MProcyclicCore.mpcTameSpecializes 2 1 1 (qOf K FF)
        Instances.SqrtNeg10.alpha_valid (qOf_ne_zero K FF) (even_qOf K FF))
      nuP hnuSigma hnuWild)
    (scalarActionZmodTwo _)
  /-- ASK's arithmetic package. -/
  KS : KSupply T (2 + 2 * 0) Instances.SqrtNeg10.core (isProP_DM 2 0) nuP
    (standardNumerics (2 + 2 * 0))

/-- The per-row supplied data, as one dependent family over the frozen table: the pilot row
carries its G-Lab/ASK/candidate-residual record, the four `M` rows their
ν/clauses/`KSupply` records. -/
def RowResidual (T : OrientedTameQuotientK B FF) : FrozenQuadRow → Type 1
  | .sqrtNegTwo => ResidualSqrtNegTwo K B FF
  | .sqrtTwo => ResidualSqrtTwo K B FF T
  | .sqrtFive => ResidualSqrtFive K B FF T
  | .sqrtTen => ResidualSqrtTen K B FF T
  | .sqrtNegTen => ResidualSqrtNegTen K B FF T

end Supply

/-! ## §4 The five per-row theorems

Each is the corresponding instance headline consumed at `q := q_K`, `hqK := rfl`, with the
supplied data read off the §3 records.  Stated standalone (never packed — AS2's measured
divergence trap) so that each can be audited and `#print axioms`-measured on its own. -/

section RowTheorems

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- The pilot row of the assembly: `Γ_{R_{N,2,0}} ≅ G_K` from the supplied data
(`SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` re-read off the §3 records). -/
theorem rowEquiv_sqrtNegTwo (F : FieldInputs K B FF) (S : ResidualSqrtNegTwo K B FF) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) FrozenQuadRow.sqrtNegTwo.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  SqrtNeg2.sqrtNegTwo_candidate_equiv_galK F.T S.hdeg S.fLab S.piAb S.hpiAb S.hpiNu
    S.horient S.hScal S.hpair S.hexact S.hstokes S.hsimp S.hsplit S.hZcount S.hdet
    F.params F.params_n F.params_qK F.ramified F.ramifiedData

/-- The `ℚ₂(√2)` row of the assembly (`Instances.candidate_equiv_galK_sqrtTwo` at
`q := q_K`). -/
theorem rowEquiv_sqrtTwo (F : FieldInputs K B FF) (S : ResidualSqrtTwo K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) FrozenQuadRow.sqrtTwo.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  Instances.candidate_equiv_galK_sqrtTwo (T := F.T) (q := qOf K FF) rfl S.nuP S.hnuSigma
    S.hnuWild S.hnuP S.exactLifting S.stokes S.scalar S.determinant S.KS F.params
    F.params_n F.params_qK F.ramified F.ramifiedData

/-- The `ℚ₂(√5)` row of the assembly (`Instances.candidate_equiv_galK_sqrtFive` at
`q := q_K`). -/
theorem rowEquiv_sqrtFive (F : FieldInputs K B FF) (S : ResidualSqrtFive K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) FrozenQuadRow.sqrtFive.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  Instances.candidate_equiv_galK_sqrtFive (T := F.T) (q := qOf K FF) rfl S.nuP S.hnuSigma
    S.hnuWild S.hnuP S.exactLifting S.stokes S.scalar S.determinant S.KS F.params
    F.params_n F.params_qK F.ramified F.ramifiedData

/-- The `ℚ₂(√10)` row of the assembly (`Instances.candidate_equiv_galK_sqrtTen` at
`q := q_K`). -/
theorem rowEquiv_sqrtTen (F : FieldInputs K B FF) (S : ResidualSqrtTen K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) FrozenQuadRow.sqrtTen.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  Instances.candidate_equiv_galK_sqrtTen (T := F.T) (q := qOf K FF) rfl S.nuP S.hnuSigma
    S.hnuWild S.hnuP S.exactLifting S.stokes S.scalar S.determinant S.KS F.params
    F.params_n F.params_qK F.ramified F.ramifiedData

/-- The `ℚ₂(√−10)` row of the assembly (`Instances.candidate_equiv_galK_sqrtNegTen` at
`q := q_K`; merge gate 9's procyclic `(1, 1, 1)` parameters, §1's
`sqrtNegTen_branch_eq_branchSqrtNegTen`). -/
theorem rowEquiv_sqrtNegTen (F : FieldInputs K B FF) (S : ResidualSqrtNegTen K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) FrozenQuadRow.sqrtNegTen.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  Instances.candidate_equiv_galK_sqrtNegTen (T := F.T) (q := qOf K FF) rfl S.nuP S.hnuSigma
    S.hnuWild S.hnuP S.exactLifting S.stokes S.scalar S.determinant S.KS F.params
    F.params_n F.params_qK F.ramified F.ramifiedData

end RowTheorems

/-! ## §5 The final ramified-`i` theorem -/

section Final

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **The final ramified-`i` theorem** (packet "Formal completion criterion", landed form).

For a supplied ramified-`i` field `K` (arithmetic bundles `B`, `FF`; the ramified-`i`
condition is `F.ramified`), **every row of the frozen quadratic table** presents `G_K`:

`Γ_{R_r} = ⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ^{q_K}, R_r = 1, ⟪x₀,x₁,x₂⟫ pro-2⟩_prof ≅ G_K`

given the row's supplied data — `F` the row-independent packet-§12 block, `S` the row's
residual record (§3; the campaign's complete named residual surface).  The proof is the
packet's instruction executed literally: *apply the certificate-main theorem branch by
branch* — one case per frozen row, each case one instance headline.  F4's Prop. 8.1
(`branchData_five_rows`, `classification_of_even`) governs the table's audit in §2:
the realized shapes are `N0`/`M0`/`Mpc` (both signs), the `L` shape is the `n = 1` route
(§7), and the `Npc` shape is **not** covered (`no_frozen_Npc` — the recorded delta from the
packet's fully general statement).

The conclusion's word `r.word` is definitionally the instance file's frozen word, so this
statement is exactly the five instance headlines under one quantifier — nothing is
re-derived, and the axiom print is the union of theirs. -/
theorem ramifiedI_candidate_equiv_galK (r : FrozenQuadRow) (F : FieldInputs K B FF)
    (S : RowResidual K B FF F.T r) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) r.word : ProfiniteGrp) : Type) (GalK K)) := by
  cases r with
  | sqrtNegTwo => exact rowEquiv_sqrtNegTwo F S
  | sqrtTwo => exact rowEquiv_sqrtTwo F S
  | sqrtFive => exact rowEquiv_sqrtFive F S
  | sqrtTen => exact rowEquiv_sqrtTen F S
  | sqrtNegTen => exact rowEquiv_sqrtNegTen F S

end Final

/-! ## §6 Certificate uniformity

CB-TRN's log promised that "AS5's uniform story is now executable": all rows — the five
quadratic ones and `n = 1` — enter the assembly through the **same** `WordCertificate`
interface.  The two theorems below are that story as Lean statements.

* `candidate_equiv_galK_of_frozenRow_certificates`: ONE row-uniform theorem, no case
  split — a `WordCertificate` over the row's slot plus a `KSupply` plus packet §12 gives
  `Γ_{R_r} ≅ G_K`, uniformly in `r` (it is AS1's `candidate_equiv_absoluteGalois` through
  ASK's `candidate_equiv_galK_of_supply`, instantiated at the table's slot functions).
* the certificate stock, per row (what is *true* today, not more):
  the `L` slot's certificate is **unconditional** (`wordCertificateLSq`, CB-TRN);
  the pilot slot's is `sqrtNegTwoWordCertificate` given the four named candidate residuals
  (AS2 — every other field landed);
  the four `M` slots' are `Instances.*.wordCertificate` given the four analytic clauses
  (AS3 — 13 of 17 fields proved per row, the clauses as binders).
-/

section Uniformity

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **The uniform interface theorem**: every frozen row reaches `Γ_{R_r} ≅ G_K` through the
single `WordCertificate`/`KSupply` gate — one statement, no case analysis, uniform in the
row.  This is the campaign's uniformity result made executable; the per-row content of §4
is exactly the *construction* of `W` from each row's named residuals. -/
theorem candidate_equiv_galK_of_frozenRow_certificates (r : FrozenQuadRow)
    {T : OrientedTameQuotientK B FF}
    (nuP : ContinuousMonoidHom ((r.core : ProfiniteGrp) : Type) Ztwo)
    (hnuP : Function.Surjective nuP)
    (W : WordCertificate 2 (qOf K FF) r.word r.core r.coreIsProP nuP (standardNumerics 2))
    (KS : KSupply T 2 r.core r.coreIsProP nuP (standardNumerics 2))
    (params : FieldParameters) (params_n : params.n = 2)
    (params_qK : params.qK = qOf K FF)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D]
      [Finite D] (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 2 (qOf K FF) r.word : ProfiniteGrp) : Type) (GalK K)) :=
  candidate_equiv_galK_of_supply W KS params params_n params_qK ramified ramifiedData hnuP

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The `L` slot's certificate is **unconditional** — the `n = 1` `WordCertificate`
(CB-TRN's `wordCertificateLSq`; B-Lab = the proved `GQ2.Roe.Labute.bLab`). -/
theorem wordCertificate_nonempty_lSq :
    Nonempty (WordCertificate 1 2 (Words.LSq.lSqW 0) PiBd SectionThree.piBd_isProP nuTwo
      (standardNumerics 1)) :=
  ⟨wordCertificateLSq⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The pilot slot's certificate, given the row's four named candidate-side residuals
(AS2's `sqrtNegTwoWordCertificate` — every other field is landed mathematics). -/
theorem wordCertificate_nonempty_sqrtNegTwo {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (hsimp : SqrtNeg2.PilotHsimp q) (hsplit : SqrtNeg2.PilotStageSep q)
    (hZcount : SqrtNeg2.PilotStageZ q) (hdet : SqrtNeg2.PilotDet q hq0 hqe) :
    Nonempty (WordCertificate 2 q Count.pilotW SqrtNeg2.pilotP (isProP_DN 2 0)
      SqrtNeg2.pilotNuP (standardNumerics 2)) :=
  ⟨SqrtNeg2.sqrtNegTwoWordCertificate hq0 hqe hsimp hsplit hZcount hdet⟩

end Uniformity

/-! ## §7 The `L` row: the `n = 1` recovery, re-exported

The `L` shape's landed instance is the odd-degree base case `n = 1`, where the conclusion
is the frozen `ℚ₂` theorem itself.  Three independent unconditional routes exist; the
re-export below fixes the campaign's `n = 1` endpoint name next to the quadratic table's,
so the two final statements sit in one file.  (Its `#print axioms` is the frozen `ℚ₂`
capstone census — byte-identical to `GQ2.main_presentation_literal_roe_unconditional`'s.) -/

section LRow

/-- **The `L`-row endpoint** — `Γ_{L_sq,1} ≅ G_ℚ₂`, unconditional.  Route: AS4's
`QTwo.candidateGroup_lSq_equiv_absGalQ2` (via the frozen `ℚ₂` capstone).  The other two
unconditional routes to the same statement are `QTwo.candidateGroup_lSq_equiv_absGalQ2_via_sourcesN`
(via the dyadic recursion at `n = 1`) and `candidateGroup_lSq_equiv_absGalQ2_via_wordCertificate`
(via the `n = 1` `WordCertificate`, CB-TRN) — three proofs, one statement, all printing the
same census. -/
theorem lRow_candidate_equiv_absGalQ2 :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup 1 2 (Words.LSq.lSqW 0) : ProfiniteGrp) : Type) AbsGalQ2) :=
  QTwo.candidateGroup_lSq_equiv_absGalQ2

end LRow

end GQ2.Dyadic
