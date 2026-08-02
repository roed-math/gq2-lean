/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.KSupply
import GQ2.Dyadic.Instances.Cores
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.Count.Routine
import GQ2.Dyadic.Count.WildDischarge
import GQ2.Dyadic.Count.Marking
import GQ2.Dyadic.Count.Frozen

/-!
# The `ℚ₂(√2)` instance  (dyadic campaign, tickets AS3, AS3-b)

**Selection-freeze row 4** at its `α = 3` instance: `K = ℚ₂(√2)` is ramified quadratic, so
`n = [K : ℚ₂] = 2`, `f = 1`, `q_K = 2`, and the frozen branch word is `mCompactW 3 0` with
`m = 2^{α−1} = 4` (`Words/M0.lean`, certificate `M-compact-alpha3-h0-q2-v001`).

This file carries the `√2` **row** only: §1 the frozen parameters and the row's word
certificate, §2 the field's headlines (packet Thm 1.1 at `K`, conditional and non-vacuous).

The compact-`M` *branch* layer that produces them — `MCompactCore`, generic in `(α, h, q)`: the
alphabet ↔ core dictionary (`CoreReindex`), the `CorePresentation` it produces, the
`WordCertificate` producer that leaves exactly AS1's four analytic clauses open, the `ν_P`
witness, and the two `hsimp` fold-ins — was built by AS3 in this file and **hoisted by AS3-b**
to `GQ2/Dyadic/Instances/Cores.lean` §4–§7 (a pure move; every fully-qualified name unchanged).
`√5` (`GQ2/Dyadic/Instances/Sqrt5.lean`) consumes the same namespace, with `α` and `q` the only
differences.

## What is **not** proved here, and why — AS1's divergence 4, unchanged

`WordCertificate` has four analytic clause fields (`exactLifting`, `stokes`, `scalar`,
`determinant`) whose producers do not exist at the candidate carrier — AS1's divergence 4,
restated by AS4 (`GQ2/Dyadic/Instances/QTwo.lean`).  `Cores.lean` §6's producer therefore takes
those four as **explicit arguments**, and the field headline (§2) takes
them plus a `KSupply` (ASK's own carried record).  Every *other* field of both records is
supplied here or upstream.  No `sorry`, and no clause is assumed that the landed stack proves.

The inventory at `(n, q, R) = (2, 2, mCompactW 3 0)`:

| `WordCertificate` field | status |
|---|---|
| `tameSpecialization` | **proved** (`Count.tameSpecializes_mCompact`) |
| `coreRel`, `proTwoWord` | **proved** (`Cores.lean` §4, from WM0-a's `eval_pro2_mCompact`) |
| `pro2`, `ker_pro2`, `hpro2`, `compat` | **proved** — that dictionary + `Count.CorePresentation` |
| `tfg` | **proved** (`Count.gammaR_topologicallyFinitelyGenerated`) |
| `smulZmod2`, `contSMulZmod2`, `htriv` | **proved** (`scalarActionZmodTwo` &c.) |
| `htame` | **proved** (`Count.htame_of_tameSpecializes`) |
| `hwild` | **proved** (`Count.hwild_mCompact`) |
| `exactLifting`, `stokes`, `scalar`, `determinant` | ⚠ **argument** — AS1 divergence 4 |

`hnuSigma`/`hnuWild` (F3's `prop_3_4_three` normalization of `ν_P` against the *dictionary's*
marking) are arguments too; they are conditions on the abstract slot `(P, ν_P)`, exactly as in
`Count.PilotN.n_exists_proTwo`, and `Cores.lean` §5 spells out what they say about `dmGen`.
**They are also satisfied**: that section's `mNu`/`mNu_sigma`/`mNu_wild`/`mNu_surjective`
(AS3-b) build the witness `ν(μ₂) = 1, ν(μ₀) = −m`, so §2 carries a second headline
`candidate_equiv_galK_sqrtTwo_nonvacuous` with all four `ν`-binders discharged.

## Numeric leaves

**Nothing in this file reads a count.**  No `Nat.card`, no exponent constant and no
`SourceNumerics` *value* is written anywhere: the numerics enter only as the opaque parameter
`SN`, and §2 instantiates it at `standardNumerics 2` by name, never by its formula.  CB-SG's
exponent warning (`2^{d·v₂(#A)}` versus `2^{v₂(#A)}`) therefore has nothing to bite on here.

## Regression cross-checks against the freeze (not proofs)

`Words/M0.lean`'s F5 rows record `d = 2 ⇒ M(α = 3, r = 0)`, `m = 4`, `q_K = 2`, epimorphism
counts `(S₃, D₈, A₄) = (6, 1568, 120)`, certificate `M-compact-alpha3-h0-q2-v001`, AST digest
`0209b708538277e0…`.  `Sqrt2.sqrtTwoRow` pins the `(α, h, level)` triple against WM0-a's own
`branchData_sqrtTwo` and `mOf 3 = 4` (§1); the harness numbers are **cited only**, and no proof in
this file depends on them.

## Axioms

`sorry`-free.  No new axiom, no `decide`, no `native_decide`.  §1 prints exactly the standard
three; **both** of §2's headlines print std-3 **plus exactly `{B1, B6, B7}`** — ASK's surface —
and in particular **no B5-K and no B10-K**.  Measured, not budgeted; per-declaration prints are
in the ticket reports.
-/

namespace GQ2.Dyadic.Instances

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore GQ2.SectionEight
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Count.PilotN TameSpec
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Instances.NuWitness

/-! ## §1 The `ℚ₂(√2)` row

`α = 3`, `h = 0`, `m = 4`, `q_K = 2`, `n = 2`; selection-freeze row 4, certificate
`M-compact-alpha3-h0-q2-v001`. -/

namespace Sqrt2

open MCompactCore

/-- The frozen branch word of `ℚ₂(√2)`. -/
noncomputable abbrev word : PWord (Generator (2 + 2 * 0)) := mCompactW 3 0

/-- The standard core of the row: `D_M` at `α = 3`, rank `4`. -/
noncomputable abbrev core : ProfiniteGrp := DM 3 0

/-- `2 ≤ α = 3` — F1/F4's validity condition, and `1 ≤ α` for WM0-a's pro-`2` comparison. -/
theorem alpha_valid : (1 : ℕ) ≤ 3 := by omega

/-- **The frozen row data**, pinned against WM0-a's own `branchData_sqrtTwo`: the compact-`M`
branch datum at `α = 3` is valid, sits at level `r = 0`, and its half-period is `m = 4`. -/
theorem sqrtTwoRow :
    (BranchData.M0 3).Valid ∧ (BranchData.M0 3).level = 0 ∧ mOf 3 = 4 :=
  ⟨branchData_sqrtTwo.1, branchData_sqrtTwo.2, rfl⟩

/-- **The row's `ν_P`** — `MCompactCore`'s witness at `(α, h) = (3, 0)`.  It is what makes §2's
`candidate_equiv_galK_sqrtTwo_nonvacuous` a theorem with no `ν`-binders. -/
noncomputable abbrev nu : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo :=
  mNu 3 0 alpha_valid

/-- The tame modulus of `ℚ₂(√2)`: the field is **ramified** quadratic, so `f = 1` and
`q_K = 2`.  ⚠ Never read the branch condition off `q_K` — FD2's erratum: `q_K` is the residue
cardinality, and `ℚ₂(√5)` has `q_K = 4` with `i ∉ K` all the same. -/
theorem qK_hyps : (2 : ℕ) ≠ 0 ∧ Even (2 : ℕ) := ⟨two_ne_zero, even_two⟩

/-- **The `√2` word certificate**, modulo AS1's four analytic clauses. -/
noncomputable abbrev wordCertificate
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mCorePresentation 3 0 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mCorePresentation 3 0 alpha_valid).mark (.wild j)) = 1)
    {SN : SourceNumerics (2 + 2 * 0)}
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core nuP SN
      (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core
      nuP SN (tameOfSpec (2 + 2 * 0) 2 word (mTameSpecializes 3 0 2 two_ne_zero even_two))
      (mPro2 3 0 2 alpha_valid two_ne_zero even_two)
      (mCompat 3 0 2 alpha_valid two_ne_zero even_two
        (mTameSpecializes 3 0 2 two_ne_zero even_two) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * 0) 2 word core (isProP_DM 3 0) nuP SN :=
  mWordCertificate 3 0 2 alpha_valid two_ne_zero even_two nuP hnuSigma hnuWild exactLifting
    stokes scalar determinant

end Sqrt2

/-! ## §2 Packet Theorem 1.1 at `ℚ₂(√2)`

ASK's `candidate_equiv_galK_of_supply` at the `√2` row.  The `q`-side hypotheses `2 ≤ q_K` and
`Even q_K` are discharged inside it from B13's residue degree; the tame modulus enters through
the row pin `hqK : qOf K FF = q`, which the caller instantiates at `q = 2` for `√2`
(`ℚ₂(√2)/ℚ₂` is ramified, so `f = 1` and `q_K = 2`; §1's `qK_hyps`).

⚠ **A finding worth recording**: the tame modulus is *not* what distinguishes `√2` from `√10`,
and it is not what makes the theorem `√2`'s.  Both have `q_K = 2`; what pins the field is the
**word** — `α = 3` here, the procyclic row there.  `q_K` is genuinely load-bearing only against
`√5` (`q_K = 4`), and even there it moves no word hash (WM0-a's "five instances, four trees"). -/

section Main

open Sqrt2 MCompactCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
  {T : OrientedTameQuotientK B FF}

/-- **Packet Theorem 1.1 at `K = ℚ₂(√2)`.**

`⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ², R_{M,0}(α=3) = 1, ⟪x₀,x₁,x₂⟫ pro-2⟩_prof ≅ G_K`.

The hypothesis list is exactly the campaign's residue at this row and nothing more:

* `hqK` — the arithmetic pin `q_K = q`, instantiated at `q = 2` (ramified quadratic);
* `nuP`, `hnuSigma`, `hnuWild`, `hnuP` — the abstract slot's `ν`-normalization, F3's
  `prop_3_4_three` conditions read through `Cores.lean` §4's dictionary;
* the four analytic clauses — AS1 divergence 4, candidate side;
* `KS : KSupply …` — ASK's arithmetic package, whose own eleven carried leaves are listed in
  `GQ2/Dyadic/Instances/KSupply.lean` §6;
* `params`, `ramified`, `ramifiedData` — packet §12's standard local inputs.

Nothing is assumed that the landed stack proves. -/
theorem candidate_equiv_galK_sqrtTwo {q : ℕ} (hqK : qOf K FF = q)
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mCorePresentation 3 0 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mCorePresentation 3 0 alpha_valid).mark (.wild j)) = 1)
    (hnuP : Function.Surjective nuP)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nuP (standardNumerics (2 + 2 * 0)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nuP (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nuP (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q word
        (mTameSpecializes 3 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)))
      (mPro2 3 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mCompat 3 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mTameSpecializes 3 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)) nuP hnuSigma
        hnuWild)
      (scalarActionZmodTwo _))
    (KS : KSupply T (2 + 2 * 0) core (isProP_DM 3 0) nuP (standardNumerics (2 + 2 * 0)))
    (params : FieldParameters) (params_n : params.n = 2 + 2 * 0)
    (params_qK : params.qK = q)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    Nonempty (ContinuousMulEquiv ((candidateGroup (2 + 2 * 0) q word : Type)) (GalK K)) := by
  subst hqK
  exact candidate_equiv_galK_of_supply
    (mWordCertificate 3 0 (qOf K FF) alpha_valid (qOf_ne_zero K FF) (even_qOf K FF) nuP
      hnuSigma hnuWild exactLifting stokes scalar determinant)
    KS params params_n params_qK ramified ramifiedData hnuP

/-- **Packet Theorem 1.1 at `K = ℚ₂(√2)`, with the `ν`-normalization discharged** (ticket AS3-b).

The same conclusion as `candidate_equiv_galK_sqrtTwo`, at the *concrete* `ν_P = Sqrt2.nu`: the
four binders `nuP`, `hnuSigma`, `hnuWild`, `hnuP` are gone from the statement, so the abstract
slot `(P, ν_P)` is demonstrably inhabited at this row and the headline cannot be vacuous through
it.  What remains is exactly AS1's divergence 4 (the four analytic clauses), ASK's `KSupply`, and
packet §12's standard local inputs. -/
theorem candidate_equiv_galK_sqrtTwo_nonvacuous {q : ℕ} (hqK : qOf K FF = q)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nu (standardNumerics (2 + 2 * 0)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nu (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nu (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q word
        (mTameSpecializes 3 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)))
      (mPro2 3 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mCompat 3 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mTameSpecializes 3 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)) nu
        (mNu_sigma 3 0 alpha_valid) (mNu_wild 3 0 alpha_valid))
      (scalarActionZmodTwo _))
    (KS : KSupply T (2 + 2 * 0) core (isProP_DM 3 0) nu (standardNumerics (2 + 2 * 0)))
    (params : FieldParameters) (params_n : params.n = 2 + 2 * 0)
    (params_qK : params.qK = q)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    Nonempty (ContinuousMulEquiv ((candidateGroup (2 + 2 * 0) q word : Type)) (GalK K)) :=
  candidate_equiv_galK_sqrtTwo hqK nu (mNu_sigma 3 0 alpha_valid) (mNu_wild 3 0 alpha_valid)
    (mNu_surjective 3 0 alpha_valid) exactLifting stokes scalar determinant KS params params_n
    params_qK ramified ramifiedData

omit [FiniteDimensional ℚ_[2] ↥K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The `√2` row's `κ_K ≠ 0`.**  The standing ramified-`i` binder forces the even-degree head
`[[1,1],[1,0]]` (FD2), through AS1's `kappaK_ne_zero_of_ramified`.  Recorded at the row because
`n = 2` is even and the row is therefore in FD2's non-alternating branch, not WL-c's. -/
theorem kappaK_ne_zero_sqrtTwo {δi : ℚ̄₂} (hδ : δi ^ 2 = -1)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi) :
    FieldData.kappaK K ≠ 0 :=
  kappaK_ne_zero_of_ramified hδ (ramified δi hδ)

end Main

end GQ2.Dyadic.Instances
