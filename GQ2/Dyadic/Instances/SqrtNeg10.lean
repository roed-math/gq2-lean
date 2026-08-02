/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.Sqrt10

/-!
# The `ℚ₂(√−10)` instance — **merge gate 9**  (dyadic campaign, tickets AS3, AS3-b)

**Selection-freeze row 5** at its `ε = 1` instance: `K = ℚ₂(√−10)`, `n = [K : ℚ₂] = 2`,
`q_K = 2`, and the frozen branch word is `mpcW 2 1 1 .one 0` — `(α, r, ε, η) = (2, 1, 1, 1)`,
so `s = 2^r = 2`, `p = ε·2^{r−1} = 1`, `m = 2^{α−1} = 2` (`Words/Mpc.lean`, certificate
`M-procyclic-alpha2-r1-eps1-eta1-h0-q2-v001`, digest `55b24a4b141274bc…`).

## Merge gate 9, consumed rather than re-proved

The gate is the statement that **`ℚ₂(√−10)` is carried by the frozen *procyclic* row `(1,1,1)`,
not by a sign row** — packet Cor. 8.2, with packet Prop. 8.1 saying the sign row does not exist
under ramified `i` (an even `η` is impossible).  WMP-d closed it; this file is a *consumer*.
Concretely, what the gate buys here is that `word` below is `mpcW 2 1 1 .one 0` and nothing
else: no field-specific relative-norm word, no sign-row branch, and therefore no second
`WordCertificate` producer.  `Words/Mpc.lean`'s `branchData_sqrtNeg10` is the pin, and
`sqrtNegTenRow` (§1) restates it at this row so the consumption is checkable.

The retired alternative is recorded, because "retired to regression-only" is a status and not an
absence: draft §7.4's field-specific relative-norm word for `√−10` is F5 row **B1**
(`rel_minus10_relative_norm`), its hat map is *not* an `Sh_M` value, and R4's riding decision
keeps it unfrozen (`MINUS_TEN_VARIANT`).  Nothing here refers to it.

## The one place `√−10` is *deeper* than `√10`

`Certificates/MpcStokes.lean` closes `hlinrow` — the linear copy's Fox row at σ-free offsets,
the last open input of `mpcProductRowCert` — **only at this instance**: `sqrtNeg10_hlinrow` and
the assembled `sqrtNeg10ProductCert` are stated at `(α, r, p) = (2, 1, 1)`, i.e. exactly the
`√−10` parameters, and there is no `√10` twin.  §3's closing note records the pointer so the
asymmetry is visible from the instance file and not only from the certificate file's docstring.  ⚠ It is *not*
a `WordCertificate` field: it is an ingredient of the still-unowned certificate ⇒ count bridge,
so it does not change this file's inventory — but it does mean the two procyclic fields sit at
different depths, and `√−10` is the deeper one.

## Inventory

Identical to `√10`'s: thirteen `WordCertificate` fields proved through `MProcyclicCore`
(`GQ2/Dyadic/Instances/Cores.lean` §8–§11), four — `exactLifting`, `stokes`, `scalar`,
`determinant` — arguments (AS1 divergence 4).  The only parameter that changes is `p : 0 ↦ 1`.

## `r ≥ 1`

Discharged as at `√10`, by the frozen `level = 1` (`r_pos`).  WNP-c's dichotomy — the corrected
cross operator is identically zero at `r = 0` (`A = B = g`, `g² + g + 1 = 0`) and invertible at
`r = 1` — therefore never meets its degenerate case at either AS3 procyclic row.

## Numeric leaves

**Nothing in this file reads a count.**  `standardNumerics 2` is named, never unfolded; `s 1 = 2`,
`p true 1 = 1`, `m 2 = 2` are word parameters, not counts.

## Regression cross-checks against the freeze (not proofs)

`L = 67` (flat in `α`), max product arity 2, certificate digest `55b24a4b141274bc…`, F5 counts
`(S₃, D₈, A₄) = (6, 1568, 120)` — the same triple as `√10`, because no `2`-group sees the
`σ`-versus-`σ₂` distinction.  All cited; no proof here depends on any of them.

## Axioms

`sorry`-free, no new axiom, no `decide`.  The row lemmas print the standard three; **both**
headlines — the conditional one and AS3-b's `_nonvacuous` corollary — print std-3 +
`{B1, B6, B7}`, ASK's surface, with **no B5-K and no B10-K**.
-/

namespace GQ2.Dyadic.Instances

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore GQ2.SectionEight
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc TameSpec
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open MProcyclicCore

/-! ## §1 The `ℚ₂(√−10)` row -/

namespace SqrtNeg10

/-- The frozen branch word of `ℚ₂(√−10)`: the `ε = 1` procyclic row, `(r, ε, η) = (1, 1, 1)`. -/
noncomputable abbrev word : PWord (Generator (2 + 2 * 0)) := mpcW 2 1 1 .one 0

/-- The standard core of the row: `D_M` at `α = 2`, rank `4` — the same core as `√10`. -/
noncomputable abbrev core : ProfiniteGrp := DM 2 0

theorem alpha_valid : (1 : ℕ) ≤ 2 := by omega

/-- **Merge gate 9, at the instance**: `ℚ₂(√−10)` is the procyclic row `(r, ε, η) = (1, 1, 1)`
(packet Cor. 8.2), a valid branch datum with `level = 1`, `s = 2` and `p = 1`.  Pinned against
WMP-a's own `branchData_sqrtNeg10`; the gate itself is WMP-d's and is **consumed**, not
re-proved. -/
theorem sqrtNegTenRow :
    (BranchData.Mpc 2 1 true 1).Valid ∧ (BranchData.Mpc 2 1 true 1).level = 1 ∧
      (BranchData.Mpc 2 1 true 1).sVal = 2 ∧ (BranchData.Mpc 2 1 true 1).pVal = 1 :=
  branchData_sqrtNeg10

/-- **WNP-c's `r ≥ 1` side condition, discharged at this row.**  See `Sqrt10.r_pos` for the
statement of the dichotomy this avoids; the frozen row has `level = 1`. -/
theorem r_pos : 1 ≤ (BranchData.Mpc 2 1 true 1).level := by
  rw [show (BranchData.Mpc 2 1 true 1).level = 1 from rfl]

/-- The tame modulus of `ℚ₂(√−10)`: `q_K = 2`. -/
theorem qK_hyps : (2 : ℕ) ≠ 0 ∧ Even (2 : ℕ) := ⟨two_ne_zero, even_two⟩

/-- **The row's `ν_P`** — `MProcyclicCore`'s witness at `(α, r, p) = (2, 1, 1)`; the same term as
`√10`'s with `p : 0 ↦ 1`, which is the only slot of the exponent vector that moves between the
two procyclic rows (ticket AS3-b). -/
noncomputable abbrev nu : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo :=
  mpcNu 2 1 1 alpha_valid

/-- **The two procyclic rows differ in exactly one word parameter.**  `√10` is `ε = 0` (`p = 0`,
the `B`-letter collapses to the bare `x₁`) and `√−10` is `ε = 1` (`p = 1`, `B = x₁σ`); everything
else — `α`, `r`, the `η` display, the handle count, `q_K`, and the core `D_M` — agrees.  Recorded
because it is the entire Lean-side content of "the two procyclic AS3 fields". -/
theorem procyclic_pair :
    word = mpcW 2 1 1 .one 0 ∧ Sqrt10.word = mpcW 2 1 0 .one 0 ∧
      GQ2.Dyadic.p true 1 = 1 ∧ GQ2.Dyadic.p false 1 = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [GQ2.Dyadic.p, epsVal]

/-- **The `√−10` word certificate**, modulo AS1's four analytic clauses.  Instantiation only:
`MProcyclicCore.mpcWordCertificate` at `(α, r, p, q) = (2, 1, 1, 2)`. -/
noncomputable abbrev wordCertificate
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mpcCorePresentation 2 1 1 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mpcCorePresentation 2 1 1 alpha_valid).mark (.wild j)) = 1)
    {SN : SourceNumerics (2 + 2 * 0)}
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core nuP SN
      (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core
      nuP SN
      (tameOfSpec (2 + 2 * 0) 2 word
        (mpcTameSpecializes 2 1 1 2 alpha_valid qK_hyps.1 qK_hyps.2))
      (mpcPro2 2 1 1 2 alpha_valid qK_hyps.1 qK_hyps.2)
      (mpcCompat 2 1 1 2 alpha_valid qK_hyps.1 qK_hyps.2
        (mpcTameSpecializes 2 1 1 2 alpha_valid qK_hyps.1 qK_hyps.2) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * 0) 2 word core (isProP_DM 2 0) nuP SN :=
  mpcWordCertificate 2 1 1 2 alpha_valid qK_hyps.1 qK_hyps.2 nuP hnuSigma hnuWild exactLifting
    stokes scalar determinant

end SqrtNeg10

/-! ## §2 Packet Theorem 1.1 at `ℚ₂(√−10)` -/

section Main

open SqrtNeg10

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
  {T : OrientedTameQuotientK B FF}

/-- **Packet Theorem 1.1 at `K = ℚ₂(√−10)` — the merge-gate-9 field.**

`⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ², R_{M,pc}(α=2, r=1, ε=1) = 1, ⟪x₀,x₁,x₂⟫ pro-2⟩_prof ≅ G_K`.

The candidate group is built from the **frozen procyclic word** — gate 9's content — and the
hypothesis list is `√10`'s with `p : 0 ↦ 1`. -/
theorem candidate_equiv_galK_sqrtNegTen {q : ℕ} (hqK : qOf K FF = q)
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mpcCorePresentation 2 1 1 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mpcCorePresentation 2 1 1 alpha_valid).mark (.wild j)) = 1)
    (hnuP : Function.Surjective nuP)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core nuP
      (standardNumerics (2 + 2 * 0)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core nuP
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core
      nuP (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q word
        (mpcTameSpecializes 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)))
      (mpcPro2 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mpcCompat 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mpcTameSpecializes 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _))
    (KS : KSupply T (2 + 2 * 0) core (isProP_DM 2 0) nuP (standardNumerics (2 + 2 * 0)))
    (params : FieldParameters) (params_n : params.n = 2 + 2 * 0) (params_qK : params.qK = q)
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
    (mpcWordCertificate 2 1 1 (qOf K FF) alpha_valid (qOf_ne_zero K FF) (even_qOf K FF) nuP
      hnuSigma hnuWild exactLifting stokes scalar determinant)
    KS params params_n params_qK ramified ramifiedData hnuP

/-- **Packet Theorem 1.1 at `K = ℚ₂(√−10)`, with the `ν`-normalization discharged**
(ticket AS3-b) — the merge-gate-9 field, at the concrete `ν_P = SqrtNeg10.nu`. -/
theorem candidate_equiv_galK_sqrtNegTen_nonvacuous {q : ℕ} (hqK : qOf K FF = q)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core nu
      (standardNumerics (2 + 2 * 0)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core nu
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core
      nu (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q word
        (mpcTameSpecializes 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)))
      (mpcPro2 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mpcCompat 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mpcTameSpecializes 2 1 1 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)) nu (mpcNu_sigma 2 1 1 alpha_valid)
        (mpcNu_wild 2 1 1 alpha_valid))
      (scalarActionZmodTwo _))
    (KS : KSupply T (2 + 2 * 0) core (isProP_DM 2 0) nu (standardNumerics (2 + 2 * 0)))
    (params : FieldParameters) (params_n : params.n = 2 + 2 * 0) (params_qK : params.qK = q)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    Nonempty (ContinuousMulEquiv ((candidateGroup (2 + 2 * 0) q word : Type)) (GalK K)) :=
  candidate_equiv_galK_sqrtNegTen hqK nu (mpcNu_sigma 2 1 1 alpha_valid)
    (mpcNu_wild 2 1 1 alpha_valid) (mpcNu_surjective 2 1 1 alpha_valid) exactLifting stokes
    scalar determinant KS params params_n params_qK ramified ramifiedData

omit [FiniteDimensional ℚ_[2] ↥K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The `√−10` row's `κ_K ≠ 0`** — from the standing ramified-`i` binder through FD2. -/
theorem kappaK_ne_zero_sqrtNegTen {δi : ℚ̄₂} (hδ : δi ^ 2 = -1)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi) :
    FieldData.kappaK K ≠ 0 :=
  kappaK_ne_zero_of_ramified hδ (ramified δi hδ)

end Main

/-! ## §3 The two `hsimp` fold-ins at the `√−10` row, and the `hlinrow` handle -/

section Hsimp

variable {C : Type*} [Group C] [Finite C] {e : ℕ}

/-- **`√−10` fold-in (a)** — the `T`-payload `Count.hsepN_marking` /
`Count.hsep_field_goal_marking` consume, at the gate-9 parameters. -/
theorem sqrtNegTen_stokesDuality_T (t : Marking (2 + 2 * 0) C) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * 0) 2) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) SqrtNeg10.word = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (mpcFam 2 1 1 0 2 e .one) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) [DistribMulAction C (Additive ↥D.T)] :
    StokesDuality ⇑t (mpcFam 2 1 1 0 2 e .one) (Additive ↥D.T) :=
  mpcStokesDuality_T t SqrtNeg10.alpha_valid SqrtNeg10.qK_hyps.2 he hrt hrw hsimp D

/-- **`√−10` fold-in (b)** — the `Vmod`-payload `Count/Marking.lean` §5 consumes
(`isRightSeparating_vmod_mpcFam`'s `hsd` binder), at the gate-9 parameters. -/
theorem sqrtNegTen_isSelfDualN_Vmod (t : Marking (2 + 2 * 0) C) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * 0) 2) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) SqrtNeg10.word = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (mpcFam 2 1 1 0 2 e .one) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} (DD : DescData D) [DistribMulAction C DD.Vmod]
    (hr : ∀ k, FreeGroup.lift ⇑t (mpcFam 2 1 1 0 2 e .one k) = 1) :
    IsSelfDualN (2 * 0 + 2) ⇑t (mpcFam 2 1 1 0 2 e .one) DD.Vmod :=
  mpcIsSelfDualN_Vmod t SqrtNeg10.alpha_valid SqrtNeg10.qK_hyps.2 he hrt hrw hsimp DD hr

end Hsimp

/-! ### The `hlinrow` handle — documentation only

`Certificates/MpcStokes.lean`'s `MProcyclic.sqrtNeg10_hlinrow` and the assembled
`MProcyclic.sqrtNeg10ProductCert` (with `sqrtNeg10ProductCert_target`: target `mpcLinRow 1 1 0`,
no column operations) are stated at **these** parameters and have no `√10` twin.  They are
deliberately *not* re-exported here: their binder list (`π`, `V`, `t`, `E`, `E₂`, `hV₂`, `hwild`,
`hτfpf`, `hTodd`) belongs to the certificate ⇒ count bridge, which has no owner, and a wrapper
would only duplicate it.  The pointer is the deliverable; see the module docstring. -/

end GQ2.Dyadic.Instances
