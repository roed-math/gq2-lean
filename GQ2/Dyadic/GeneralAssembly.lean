/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.LabuteInterface
import GQ2.Dyadic.Main

/-!
# The general-degree assembly statement  (dyadic campaign, lane W75-STATE)

`GQ2/Dyadic/Main.lean` states the campaign's final theorem
(`ramifiedI_candidate_equiv_galK`) over the **frozen quadratic table**: five rows, all at
`n = 2`, all at handle count `h = 0`, all at `α ≥ 2`.  The campaign's actual goal is the
`n`-free statement.  This module states that goal, so that the distance between the committed
tree and the goal is a checkable Lean object rather than prose.

## What is and is not claimed here

**Nothing in this module proves the general theorem.**  The general theorem is *stated*, and
its obligations are *named record fields*.  The one thing that is proved outright is the
assembly step: that the obligations, once supplied, compose to the conclusion
(`genAsm_candidate_equiv_galK`).  That is exactly the status of `Main.lean` §6's
`candidate_equiv_galK_of_frozenRow_certificates` at the quadratic slot, lifted off `n = 2`.

The honest reading of every `structure` below: a field is an obligation the campaign owes, or
a selector that places `K` on the family member.  §2 separates the two, following
`docs/dyadic/w74-critical-path.md` §3's preliminary, which is the reason the separation exists:

> "Close every record at every ramified-`i` `K`" is not achievable, and should not be a goal.
> The records are not all obligations; some of them *select* `K`.

## The shape

The general branch datum is **not** new: `SelectedPresentation`
(`GQ2/Dyadic/SelectedWords.lean`) is already the R5 constructor table at free `(α, r, ε, η, h)`,
with `degree` and `word` at that degree.  §1 adds the missing third column, the presented
pro-`2` core, and the degree-parity coherence: `2*h+1` on the `L` row through `D_sq`, `2+2*h`
on the four even rows through `D_N`/`D_M`.  §2 is the selector/obligation split, §3 the
statement, §4 the reconciliation against `Main.lean`'s five records.

## Sources

`docs/dyadic/w74-critical-path.md` (the anatomy of the quadratic path: the records, the
obligations-versus-selectors split, the eight-item closing list, the `KTwoN` finding);
`GQ2/Dyadic/Main.lean` §§3-7; `GQ2/Dyadic/Instances/KSupply.lean` §§4-6;
`GQ2/Dyadic/Instances/Cores.lean` (the general-`(α, h)` core presentations and word
certificates).
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The general branch datum: the third column of the constructor table

`SelectedPresentation` supplies the degree and the word at every `(α, r, ε, η, h)`.  What it
does not supply is the presented pro-`2` core that the certificate interface pairs the word
with.  `genAsmCore` is that column, read off the core-presentation layer
(`GQ2/Dyadic/Instances/Cores.lean`, `GQ2/Dyadic/Instances/NpcCore.lean`): the procyclic rows
share the compact rows' cores, and the `L` row's is the square-commutator core `D_sq`. -/

section Column

/-- **The presented pro-`2` core of a selected presentation.**  `L` takes the
square-commutator core `D_sq h` (`lCorePresentation h : CorePresentation (2*h+1) (lSqW h)
(DSq h)`); the two `N` rows take `D_N α h` (`nCorePresentation`, `npcCorePresentationUnit`);
the two `M` rows take `D_M α h` (`mCorePresentation`, `mpcCorePresentation` — both branches
present the *same* core, the dictionaries differ). -/
noncomputable def genAsmCore : SelectedPresentation → ProfiniteGrp
  | .L h => SqCore.DSq h
  | .N0 alpha h => DN alpha h
  | .Npc alpha _ h _ => DN alpha h
  | .M0 alpha h => DM alpha h
  | .Mpc alpha _ _ _ h => DM alpha h

/-- Every core in the table is pro-`2` (MC2's `isProP_DN`/`isProP_DM`, SqCore's
`isProP_DSq`). -/
noncomputable def genAsmCoreIsProP :
    (S : SelectedPresentation) → IsProP 2 ((genAsmCore S : ProfiniteGrp) : Type)
  | .L h => SqCore.isProP_DSq h
  | .N0 alpha h => isProP_DN alpha h
  | .Npc alpha _ h _ => isProP_DN alpha h
  | .M0 alpha h => isProP_DM alpha h
  | .Mpc alpha _ _ _ h => isProP_DM alpha h

/-- The handle count of a selected presentation (the `h` stored in every constructor: it is
what controls the generator alphabet). -/
def genAsmHandles : SelectedPresentation → ℕ
  | .L h => h
  | .N0 _ h => h
  | .Npc _ _ h _ => h
  | .M0 _ h => h
  | .Mpc _ _ _ _ h => h

/-- `true` exactly on the four even rows (`Parameters.lean`'s `BranchData.isEven`, read on the
displayed table). -/
def genAsmIsEven : SelectedPresentation → Bool
  | .L _ => false
  | _ => true

/-- **Degree parity, `L` side**: the odd row's degree is `1 + 2h`, `h` the handle count, and
its core is the square-commutator core `D_sq h` at that same `h`. -/
theorem genAsm_degree_odd :
    (S : SelectedPresentation) → genAsmIsEven S = false →
      S.degree = 1 + 2 * genAsmHandles S
  | .L h, _ => by simp [SelectedPresentation.degree, genAsmHandles, Nat.add_comm]

/-- **Degree parity, even side**: every non-`L` row's degree is `2 + 2h`, and its core is
`D_N`/`D_M` at that same `h`. -/
theorem genAsm_degree_even :
    (S : SelectedPresentation) → genAsmIsEven S = true →
      S.degree = 2 + 2 * genAsmHandles S
  | .N0 _ _, _ => rfl
  | .Npc _ _ _ _, _ => rfl
  | .M0 _ _, _ => rfl
  | .Mpc _ _ _ _ _, _ => rfl

/-- The degree of a selected presentation is odd on the `L` row and even on the other four:
this is `Parameters.lean`'s `Compatible` predicate, read on the displayed table. -/
theorem genAsm_degree_parity (S : SelectedPresentation) :
    if genAsmIsEven S then Even S.degree else Odd S.degree := by
  cases S with
  | L h => simp [genAsmIsEven, SelectedPresentation.degree]
  | N0 _ h => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩
  | Npc _ _ h _ => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩
  | M0 _ h => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩
  | Mpc _ _ _ _ h => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩

end Column

/-! ## §2 The selector / obligation split

`Main.lean`'s five records mix two kinds of field.  Some are **obligations**: statements the
campaign owes at every field on the row.  Others are **selectors**: they assert that `G_K(2)`
*is* this row's core at this row's parameters, which no theorem can supply at an arbitrary
ramified-`i` `K` because a `K` of the wrong degree or the wrong branch is simply not on the
row.  The critical-path memo counts seven selector fields in the pilot record
(`hdeg`, `fLab`, `piAb`, `hpiAb`, `hpiNu`, `horient`, `hpair`).

Here the two are separate types.  `GenAsmBranch` is the selector; `GenAsmRowResidual` is the
obligation surface; `GenAsmFieldInputs` is the row-independent field-side block, `n`-free.

The selector is carried in the **direct `G_K(2)` spelling** (`MarkedCoreRealization`, whose
`nu_equiv` clause is stated at `nuUrKTwo B` on `maxProPQuotient 2 (GalK K)`), not in the
pilot's abelianization spelling.  That is the memo's §1.5 finding acted on: the even route
delivers `OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))`, which unpacks to
the `marked_matching_certificate_KTwoN` clause and not to the pilot's, and the three
abelianization fields `piAb`/`hpiAb`/`hpiNu` do not exist in this spelling at all. -/

section Split

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)

/-- **The row-independent field-side inputs, `n`-free** — `Main.lean`'s `FieldInputs` with
`params_n : params.n = 2` replaced by `params_n : params.n = n`.  Every other field is already
degree-free and is reproduced verbatim; in particular `ramified` is the standing hypothesis
that *selects* `K` and is never to be discharged. -/
structure GenAsmFieldInputs (n : ℕ) where
  /-- AX4's oriented tame quotient of `G_K` at `q_K` (bundle, not axiom). -/
  T : OrientedTameQuotientK B FF
  /-- F1's field-parameter package for `K`. -/
  params : FieldParameters
  /-- The slot's degree is the family member's degree (`2` in the frozen table). -/
  params_n : params.n = n
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

/-- **The general branch datum**: the family member `K` sits on, together with the
identification that places it there.

* `pres` — the R5 constructor-table row at free `(α, r, ε, η, h)`.  It carries the branch
  (`L`/`N0`/`Npc`/`M0`/`Mpc`), the parameters, the handle count, the degree, and the word.
* `hdeg` — degree coherence: `[K : ℚ₂]` is the row's degree, hence `1 + 2h` odd on the `L` row
  and `2 + 2h` even on the other four (`genAsm_degree_odd`, `genAsm_degree_even`).
* `nuP`/`hnuP` — the core's `Ztwo` marking.  Not an obligation: it is a *construction*, landed
  at `lNu h`, `mNu α h`, `mpcNu α r p` (the memo's item 8), with surjectivity from
  `dmNu_surjective`-style arguments.
* `realization` — the classification output in the direct `G_K(2)` spelling: a continuous
  equivalence `core ≃ G_K(2)` whose `Ztwo` coordinate is the canonical unramified character.
  This single field is what the pilot record spends six fields on, and it is exactly what
  `KSupply.ofMarkedCoreRealization` consumes.

⚠ **Not an obligation record.**  A `GenAsmBranch` is a *hypothesis about which family member
`K` is*, and no theorem produces one at an arbitrary ramified-`i` `K`. -/
structure GenAsmBranch where
  /-- The R5 constructor-table row: branch, parameters, handle count, degree, word. -/
  pres : SelectedPresentation
  /-- Degree coherence: `[K : ℚ₂]` is the row's degree. -/
  hdeg : Module.finrank ℚ_[2] K = pres.degree
  /-- The core's `Ztwo` marking (a construction, not an obligation). -/
  nuP : ContinuousMonoidHom ((genAsmCore pres : ProfiniteGrp) : Type) Ztwo
  /-- The marking is onto (landed at every canonical marking). -/
  hnuP : Function.Surjective nuP
  /-- **The classification selector**, `KTwoN`/`KTwoM`/`KTwoSq` spelling: `core ≃ G_K(2)`,
  `Ztwo`-compatibly. -/
  realization : MarkedCoreRealization (K := K) (B := B) (genAsmCore pres) nuP

variable {K B FF}

namespace GenAsmBranch

variable (G : GenAsmBranch K B)

/-- The degree of the row `K` sits on. -/
abbrev degree : ℕ := G.pres.degree

/-- The frozen word of the row `K` sits on. -/
noncomputable abbrev word : PWord (Generator G.degree) := G.pres.word

/-- The presented pro-`2` core of the row `K` sits on. -/
noncomputable abbrev core : ProfiniteGrp := genAsmCore G.pres

/-- The core is pro-`2`. -/
theorem coreIsProP : IsProP 2 ((G.core : ProfiniteGrp) : Type) := genAsmCoreIsProP G.pres

/-- The pro-`2` coordinate `G_K ↠ core` induced by the selector — the composite
`G_K ↠ G_K(2) ≃ core`.  This is `KSupply`'s `pro2` field, *derived* rather than assumed. -/
noncomputable abbrev pro2 : ContinuousMonoidHom (GalK K) G.core := G.realization.pro2

end GenAsmBranch

/-- **The general residual record**: what the campaign owes at every ramified-`i` `K` that the
branch datum places on the row.  Two blocks, following the critical-path memo's taxonomy.

**ASK** (`GQ2/Dyadic/Instances/KSupply.lean`), the arithmetic counting pack at the carrier
`galKProfinite K`, field names taken from the committed `KSupply`:

* `exactLifting` — ledger field 3 at `G_K`: `#LiftsOver`, the half-torsor count, stage (136).
  The `ℚ₂` ancestors are `liftsOver_card_local` and `lemma_8_6_local`; `KSupply.lean` narrows
  the second to one existential, the `K` analogue of `half_torsor_local`.
* `stokes` — ledger field 4 at `G_K`: `tcocycle_card`, separation, nondegeneracy, `#Z¹(V)`.
* `determinant` — ledger field 6 at `G_K`: the Gauss-`Z` residue at both heads.  ⚠⚠ The
  LG5 ⇒ `GaussZResidueK` rung has no `K` clone and no owner lane.

Ledger field 5 (`ScalarHilbertCertificate` at `G_K`) is **absent by design**: `KSupply.lean`
§3 proves it (`scalarHilbert_galK`), and the proof is `n`-free, so it stays discharged here.
The `hdeg`/`hhom` pins are absent too: `hdeg` moved to the branch datum where it belongs (it is
a selector), and `hhom` is `rfl` at `standardNumerics` in every degree.

**CAND**, the candidate-side clause layer at the general candidate carrier: one field, the
`WordCertificate` over the row's own slot.  It is carried whole rather than split into the four
analytic clauses because the four-clause producers are per-branch and do not exist on every
row; see §4 for exactly which rows have one. -/
structure GenAsmRowResidual (G : GenAsmBranch K B) (T : OrientedTameQuotientK B FF) where
  /-- **ASK, ledger field 3** at `G_K`. -/
  exactLifting : ExactLiftingSemantics (galKProfinite K) G.degree (qOf K FF) G.core G.nuP
    (standardNumerics G.degree)
  /-- **ASK, ledger field 4** at `G_K`. -/
  stokes : StokesDualityCertificate (galKProfinite K) G.degree (qOf K FF) G.core G.nuP
    (standardNumerics G.degree) (smulZmod2GalK K)
  /-- **ASK, ledger field 6** at `G_K`.  ⚠⚠ No `K` clone of the LG5 ⇒ `GaussZResidueK` rung. -/
  determinant : AffineDeterminantCertificate (galKProfinite K) G.degree (qOf K FF) G.core
    G.nuP (standardNumerics G.degree) T.tameFK G.pro2
    (fun g => T.compatF_K G.pro2 G.nuP G.realization.nu_compat g) (smulZmod2GalK K)
  /-- **CAND**: the candidate-side certificate over the row's own slot. -/
  cand : WordCertificate G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
    (standardNumerics G.degree)

end Split

/-! ## §3 The general-degree statement

The `n`-free analogue of `Main.lean`'s `ramifiedI_candidate_equiv_galK`.  Two forms: the
classification-facing one, whose selector is the `KTwoN`-spelled equivalence, and the
supply-facing one, which is `Main.lean` §6's row-uniform theorem lifted off `n = 2` and onto
the whole constructor table.

Neither theorem proves anything new.  Both are the assembly step: `candidate_equiv_galK_of_supply`
(`KSupply.lean:451`, already `n`-free) at the general slot.  What is new is that the slot is
now free and the obligations are named. -/

section Statement

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **The supply-facing general theorem** — `Main.lean` §6's
`candidate_equiv_galK_of_frozenRow_certificates` with the frozen quadratic table replaced by
the whole R5 constructor table at free `(α, r, ε, η, h)`, and `n = 2` replaced by the row's own
degree.  One statement, no case analysis, uniform in the row *and* in the degree. -/
theorem genAsm_candidate_equiv_galK_of_supply (S : SelectedPresentation)
    {T : OrientedTameQuotientK B FF}
    (nuP : ContinuousMonoidHom ((genAsmCore S : ProfiniteGrp) : Type) Ztwo)
    (hnuP : Function.Surjective nuP)
    (W : WordCertificate S.degree (qOf K FF) S.word (genAsmCore S) (genAsmCoreIsProP S) nuP
      (standardNumerics S.degree))
    (KS : KSupply T S.degree (genAsmCore S) (genAsmCoreIsProP S) nuP
      (standardNumerics S.degree))
    (F : GenAsmFieldInputs K B FF S.degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup S.degree (qOf K FF) S.word : ProfiniteGrp) : Type) (GalK K)) :=
  candidate_equiv_galK_of_supply W KS F.params F.params_n F.params_qK F.ramified
    F.ramifiedData hnuP

/-- **The general-degree final theorem** (the `n`-free analogue of
`ramifiedI_candidate_equiv_galK`).

For a finite `K/ℚ₂` carrying the ramified-`i` hypothesis (`F.ramified`) and a branch datum `G`
placing `K` on a member of the R5 family — its degree, its `(α, h)` or `h`, its branch and
sign, and the identification of `G_K(2)` with that member's core — the candidate group at
`q_K` over the member's word presents `G_K`, given the general residual record:

`Γ_{R_S} = ⟨σ, τ, x₀ … x_n ∣ τ^σ = τ^{q_K}, R_S = 1, ⟪x⟫ pro-2⟩_prof ≅ G_K`.

⚠ **This is a statement, not a closed result.**  Every genuinely open item is a field of
`GenAsmRowResidual` or a field of `GenAsmFieldInputs`; nothing here is claimed proved that is
not.  What the proof *does* is the assembly: the branch datum's `realization` supplies
`KSupply`'s four pro-`2` data fields (`KSupply.ofMarkedCoreRealization`, already committed) and
the residual supplies its three clause fields, after which `candidate_equiv_galK_of_supply`
closes.  §4 reconciles the record field by field against `Main.lean`'s five. -/
theorem genAsm_candidate_equiv_galK (G : GenAsmBranch K B)
    (F : GenAsmFieldInputs K B FF G.degree) (S : GenAsmRowResidual G F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsm_candidate_equiv_galK_of_supply G.pres G.nuP G.hnuP S.cand
    (KSupply.ofMarkedCoreRealization G.hdeg rfl G.realization S.exactLifting S.stokes
      S.determinant) F

end Statement

/-! ## §4 Reconciliation against the committed quadratic statement

Three things are checked here, in order.

**4.1 The frozen table is inside the general table.**  Ten `rfl`s: each frozen row's word and
core are *definitionally* the general table's at the row's pin.  Consequently the general
theorem's conclusion at that pin is literally the committed `rowEquiv_*` conclusion, which
§4.2 exhibits by proving the general-shaped statement with the committed theorem.

**4.2 The record map.**  Field by field (the table is repeated in
`docs/dyadic/w75-state-note.md`):

| `Main.lean` field | general counterpart |
| --- | --- |
| `FieldInputs.T`/`params`/`params_qK`/`ramified`/`ramifiedData` | same, verbatim |
| `FieldInputs.params_n : params.n = 2` | `GenAsmFieldInputs.params_n : params.n = n` |
| pilot `hdeg`, `M`-row `KSupply.hdeg` | `GenAsmBranch.hdeg`, at the row's own degree |
| pilot `fLab`/`horient`/`hpair` | `GenAsmBranch.realization` (one field) |
| pilot `piAb`/`hpiAb`/`hpiNu` | **retired** — the abelianization slot exists only in the
  older `marked_matching_certificate_KN` spelling |
| `KSupply.pro2`/`hpro2`/`ker_pro2`/`nu_compat` | **derived** from `GenAsmBranch.realization` |
| `KSupply.hhom` | **retired** — `rfl` at `standardNumerics` in every degree |
| `KSupply.exactLifting`/`stokes`/`determinant` | `GenAsmRowResidual.exactLifting`/`stokes`/`determinant` |
| pilot `hexact`/`hstokes` | the same two ASK fields |
| pilot `hsimp`/`hsplit`/`hZcount`/`hdet` | inside `GenAsmRowResidual.cand` |
| `M`-row `exactLifting`/`stokes`/`scalar`/`determinant` | inside `GenAsmRowResidual.cand` |
| `M`-row `nuP`/`hnuSigma`/`hnuWild`/`hnuP` | `GenAsmBranch.nuP`/`hnuP` plus the branch's own
  core dictionary (the normalization clauses are inputs to the per-branch certificate
  producers, not to the assembly) |

**4.3 The classification join.**  What the two classification routes discharge, stated. -/

/-! ### 4.1 The frozen table is inside the general table -/

section FrozenContainment

/-- The general table's `N0 2 0` row carries the pilot's frozen word. -/
theorem genAsm_word_sqrtNegTwo :
    (SelectedPresentation.N0 2 0).word = FrozenQuadRow.sqrtNegTwo.word := rfl

/-- …and the pilot's presented core. -/
theorem genAsm_core_sqrtNegTwo : genAsmCore (.N0 2 0) = SqrtNeg2.pilotP := rfl

/-- The general table's `M0 3 0` row carries `ℚ₂(√2)`'s frozen word. -/
theorem genAsm_word_sqrtTwo :
    (SelectedPresentation.M0 3 0).word = FrozenQuadRow.sqrtTwo.word := rfl

/-- …and its presented core. -/
theorem genAsm_core_sqrtTwo : genAsmCore (.M0 3 0) = Instances.Sqrt2.core := rfl

/-- The general table's `M0 2 0` row carries `ℚ₂(√5)`'s frozen word. -/
theorem genAsm_word_sqrtFive :
    (SelectedPresentation.M0 2 0).word = FrozenQuadRow.sqrtFive.word := rfl

/-- …and its presented core. -/
theorem genAsm_core_sqrtFive : genAsmCore (.M0 2 0) = Instances.Sqrt5.core := rfl

/-- The general table's `Mpc 2 1 false .one 0` row carries `ℚ₂(√10)`'s frozen word. -/
theorem genAsm_word_sqrtTen :
    (SelectedPresentation.Mpc 2 1 false .one 0).word = FrozenQuadRow.sqrtTen.word := rfl

/-- …and its presented core. -/
theorem genAsm_core_sqrtTen :
    genAsmCore (.Mpc 2 1 false .one 0) = Instances.Sqrt10.core := rfl

/-- The general table's `Mpc 2 1 true .one 0` row carries `ℚ₂(√−10)`'s frozen word. -/
theorem genAsm_word_sqrtNegTen :
    (SelectedPresentation.Mpc 2 1 true .one 0).word = FrozenQuadRow.sqrtNegTen.word := rfl

/-- …and its presented core. -/
theorem genAsm_core_sqrtNegTen :
    genAsmCore (.Mpc 2 1 true .one 0) = Instances.SqrtNeg10.core := rfl

/-- Every frozen row's degree is the general table's `2 + 2*0`. -/
theorem genAsm_degree_frozen (r : FrozenQuadRow) : r.selectedPresentation.degree = 2 :=
  FrozenQuadRow.selectedPresentation_degree r

end FrozenContainment

/-! ### 4.2 The committed rows prove the general-shaped conclusion

Each statement below is the conclusion of `genAsm_candidate_equiv_galK` at the row's pin,
proved by the committed `rowEquiv_*` theorem.  That the committed proof term typechecks against
the general-shaped statement is the check: the general statement does not drift from the
landed one at the quadratic slot. -/

section FrozenRows

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- Pilot row, general-shaped conclusion. -/
theorem genAsm_rowEquiv_sqrtNegTwo (F : FieldInputs K B FF) (S : ResidualSqrtNegTwo K B FF) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.N0 2 0).degree (qOf K FF)
        (SelectedPresentation.N0 2 0).word : ProfiniteGrp) : Type) (GalK K)) :=
  rowEquiv_sqrtNegTwo F S

/-- `ℚ₂(√2)` row, general-shaped conclusion. -/
theorem genAsm_rowEquiv_sqrtTwo (F : FieldInputs K B FF) (S : ResidualSqrtTwo K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 3 0).degree (qOf K FF)
        (SelectedPresentation.M0 3 0).word : ProfiniteGrp) : Type) (GalK K)) :=
  rowEquiv_sqrtTwo F S

/-- `ℚ₂(√5)` row, general-shaped conclusion. -/
theorem genAsm_rowEquiv_sqrtFive (F : FieldInputs K B FF) (S : ResidualSqrtFive K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 2 0).degree (qOf K FF)
        (SelectedPresentation.M0 2 0).word : ProfiniteGrp) : Type) (GalK K)) :=
  rowEquiv_sqrtFive F S

/-- `ℚ₂(√10)` row, general-shaped conclusion. -/
theorem genAsm_rowEquiv_sqrtTen (F : FieldInputs K B FF) (S : ResidualSqrtTen K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 false .one 0).degree (qOf K FF)
        (SelectedPresentation.Mpc 2 1 false .one 0).word : ProfiniteGrp) : Type) (GalK K)) :=
  rowEquiv_sqrtTen F S

/-- `ℚ₂(√−10)` row, general-shaped conclusion. -/
theorem genAsm_rowEquiv_sqrtNegTen (F : FieldInputs K B FF)
    (S : ResidualSqrtNegTen K B FF F.T) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 true .one 0).degree (qOf K FF)
        (SelectedPresentation.Mpc 2 1 true .one 0).word : ProfiniteGrp) : Type) (GalK K)) :=
  rowEquiv_sqrtNegTen F S

end FrozenRows

end GQ2.Dyadic
