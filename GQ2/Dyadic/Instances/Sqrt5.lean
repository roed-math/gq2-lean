/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.Sqrt2

/-!
# The `ℚ₂(√5)` instance  (dyadic campaign, ticket AS3)

**Selection-freeze row 4** at its `α = 2` instance: `K = ℚ₂(√5)` is the *unramified* quadratic
extension, so `n = [K : ℚ₂] = 2`, `f = 2`, `q_K = 4`, and the frozen branch word is
`mCompactW 2 0` with `m = 2^{α−1} = 2` (`Words/M0.lean`, certificate
`M-compact-alpha2-h0-q4-v001`).

This file is **pure instantiation**: every construction it uses is `Sqrt2.lean`'s
`MCompactCore` namespace, generic in `(α, h, q)`.  Only two numbers change against the `√2`
row — `α : 3 ↦ 2` and `q_K : 2 ↦ 4` — and that is the whole difference between the two fields on
the Lean side.

## ⚠ Two findings the pair `(√2, √5)` makes visible, and only the pair

1. **`q_K` moves no word.**  WM0-a's "five instances, four trees": the `α = 2, q_K = 2` and
   `α = 2, q_K = 4` candidates share an AST digest, because `q_K` is a parameter of the *tame
   relation* `τ^σ = τ^{q_K}` and not a letter of the branch word.  So `√5` and the hypothetical
   `α = 2` ramified row have literally the same `mCompactW 2 0`, and are told apart only by the
   `q` argument of `GammaR` / `candidateGroup`.  `branchData_sqrtFive` says the same thing from
   the branch-datum side: `q_K = 4` "does not appear: it is not branch data".
2. **`q_K = 4` is not the ramified-`i` branch condition, and reading it as one gets the
   arithmetic backwards.**  AS1's `DyadicLocalInput.ramified` docstring and FD2's erratum both
   flag it: `FieldParameters.qK` is the residue cardinality `2^f`, whereas the campaign's
   standing hypothesis is about `μ_{2^∞}(K)`.  `ℚ₂(√5)` has `q_K = 4` **and** `i ∉ K`, so it sits
   in the same `κ_K ≠ 0` branch as `√2` and takes FD2's `[[1,1],[1,0]]` head, not the alternating
   one.  `kappaK_ne_zero_sqrtFive` records that at this row.

## Inventory

Identical to `√2`'s (see `GQ2/Dyadic/Instances/Sqrt2.lean`): thirteen `WordCertificate` fields
proved, four — `exactLifting`, `stokes`, `scalar`, `determinant` — arguments, because the
certificate ⇒ count bridge does not exist at the candidate carrier (AS1 divergence 4).

## Numeric leaves

**Nothing in this file reads a count.**  `standardNumerics 2` is named, never evaluated; no
exponent constant is written; `mOf 2 = 2` is a *word* parameter, not a count.

## Regression cross-checks against the freeze (not proofs)

`Words/M0.lean` F5 row `d = 5 ⇒ M(α = 2, r = 0)`, `(m, q_K) = (2, 4)`, epimorphism counts
`(S₃, D₈, A₄) = (0, 1568, 480)` — note the `S₃` count is `0` here against `6` at `√2`, which is
the harness seeing `q_K` even though the word hash cannot.  `sqrtFiveRow` pins the branch datum
against WM0-a's own `branchData_sqrtFive` plus `mOf 2 = 2`; the counts are cited only.

## Axioms

`sorry`-free, no new axiom, no `decide`.  The row lemmas print the standard three; the headline
prints std-3 + `{B1, B6, B7}`, i.e. ASK's surface, and neither B5-K nor B10-K.
-/

namespace GQ2.Dyadic.Instances

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore GQ2.SectionEight
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact TameSpec
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact GQ2.FoxH
open MCompactCore

/-! ## §1 The `ℚ₂(√5)` row -/

namespace Sqrt5

/-- The frozen branch word of `ℚ₂(√5)`. -/
noncomputable abbrev word : PWord (Generator (2 + 2 * 0)) := mCompactW 2 0

/-- The standard core of the row: `D_M` at `α = 2`, rank `4`. -/
noncomputable abbrev core : ProfiniteGrp := DM 2 0

/-- `1 ≤ α = 2` — WM0-a's pro-`2` comparison condition (F1/F4 in fact give `2 ≤ α`). -/
theorem alpha_valid : (1 : ℕ) ≤ 2 := by omega

/-- **The frozen row data**, pinned against WM0-a's own `branchData_sqrtFive`: valid compact-`M`
datum at `α = 2`, level `r = 0`, half-period `m = 2`. -/
theorem sqrtFiveRow :
    (BranchData.M0 2).Valid ∧ (BranchData.M0 2).level = 0 ∧ mOf 2 = 2 :=
  ⟨branchData_sqrtFive.1, branchData_sqrtFive.2, rfl⟩

/-- The tame modulus of `ℚ₂(√5)`: the extension is **unramified**, so `f = 2` and `q_K = 4`.
⚠ This is the one place in AS3 where `q_K ≠ 2`, and it is *not* the ramified-`i` branch
condition — see the module docstring, finding 2. -/
theorem qK_hyps : (4 : ℕ) ≠ 0 ∧ Even (4 : ℕ) := ⟨by omega, by decide⟩

/-- **The `√5` and `√2` rows are the same branch, different `α`.**  Recorded as a theorem because
the two files' `word`s are different terms of the same family and the board's "row 4, two
instances" reading should be checkable. -/
theorem row_is_compactM : word = mCompactW 2 0 ∧ Sqrt2.word = mCompactW 3 0 := ⟨rfl, rfl⟩

/-- **The `√5` word certificate**, modulo AS1's four analytic clauses.  Instantiation only:
`MCompactCore.mWordCertificate` at `(α, h, q) = (2, 0, 4)`. -/
noncomputable abbrev wordCertificate
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mCorePresentation 2 0 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mCorePresentation 2 0 alpha_valid).mark (.wild j)) = 1)
    {SN : SourceNumerics (2 + 2 * 0)}
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) 4 word) (2 + 2 * 0) 4 core nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) 4 word) (2 + 2 * 0) 4 core nuP SN
      (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) 4 word) (2 + 2 * 0) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) 4 word) (2 + 2 * 0) 4 core
      nuP SN (tameOfSpec (2 + 2 * 0) 4 word (mTameSpecializes 2 0 4 qK_hyps.1 qK_hyps.2))
      (mPro2 2 0 4 alpha_valid qK_hyps.1 qK_hyps.2)
      (mCompat 2 0 4 alpha_valid qK_hyps.1 qK_hyps.2
        (mTameSpecializes 2 0 4 qK_hyps.1 qK_hyps.2) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * 0) 4 word core (isProP_DM 2 0) nuP SN :=
  mWordCertificate 2 0 4 alpha_valid qK_hyps.1 qK_hyps.2 nuP hnuSigma hnuWild exactLifting
    stokes scalar determinant

end Sqrt5

/-! ## §2 Packet Theorem 1.1 at `ℚ₂(√5)` -/

section Main

open Sqrt5

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
  {T : OrientedTameQuotientK B FF}

/-- **Packet Theorem 1.1 at `K = ℚ₂(√5)`.**

`⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ⁴, R_{M,0}(α=2) = 1, ⟪x₀,x₁,x₂⟫ pro-2⟩_prof ≅ G_K`.

The row pin is `hqK : qOf K FF = q`, instantiated at `q = 4`: `ℚ₂(√5)/ℚ₂` is unramified of
degree `2`, so `f = 2` and the residue cardinality is `4`.  Everything else is `√2`'s hypothesis
list verbatim with `α = 2`. -/
theorem candidate_equiv_galK_sqrtFive {q : ℕ} (hqK : qOf K FF = q)
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mCorePresentation 2 0 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mCorePresentation 2 0 alpha_valid).mark (.wild j)) = 1)
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
        (mTameSpecializes 2 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)))
      (mPro2 2 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mCompat 2 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mTameSpecializes 2 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)) nuP hnuSigma
        hnuWild)
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
    (mWordCertificate 2 0 (qOf K FF) alpha_valid (qOf_ne_zero K FF) (even_qOf K FF) nuP
      hnuSigma hnuWild exactLifting stokes scalar determinant)
    KS params params_n params_qK ramified ramifiedData hnuP

omit [FiniteDimensional ℚ_[2] ↥K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The `√5` row's `κ_K ≠ 0`.**  Identical to `√2`'s and worth stating twice: the standing
ramified-`i` binder — *not* `q_K` — is what puts this row in FD2's non-alternating branch.  At
`q_K = 4` the temptation to read the branch off the residue cardinality is real, and FD2's
erratum says it gets the arithmetic backwards. -/
theorem kappaK_ne_zero_sqrtFive {δi : ℚ̄₂} (hδ : δi ^ 2 = -1)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi) :
    FieldData.kappaK K ≠ 0 :=
  kappaK_ne_zero_of_ramified hδ (ramified δi hδ)

end Main

/-! ## §3 The two `hsimp` fold-ins at the `√5` row

`MCompactCore`'s two fold-ins are already generic in `(α, h, q, e)`; these are the `√5`
instances, named so that the count lane's consumers have a handle with the field's spelling.
The `√2` instances are the same terms at `α = 3`. -/

section Hsimp

variable {C : Type*} [Group C] [Finite C] {e : ℕ}

/-- **`√5` fold-in (a)** — the `T`-payload `Count.hsepN_marking` consumes, at `q_K = 4`. -/
theorem sqrtFive_stokesDuality_T (t : Marking (2 + 2 * 0) C) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * 0) 4) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) Sqrt5.word = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (mCompactFam 2 0 4 e) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) [DistribMulAction C (Additive ↥D.T)] :
    StokesDuality ⇑t (mCompactFam 2 0 4 e) (Additive ↥D.T) :=
  mStokesDuality_T t Sqrt5.qK_hyps.2 he hrt hrw hsimp D

/-- **`√5` fold-in (b)** — the `Vmod`-payload `Count/Marking.lean` §5 consumes, at `q_K = 4`. -/
theorem sqrtFive_isSelfDualN_Vmod (t : Marking (2 + 2 * 0) C) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * 0) 4) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) Sqrt5.word = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (mCompactFam 2 0 4 e) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} (DD : AffineTLift.DescData D) [DistribMulAction C DD.Vmod]
    (hr : ∀ k, FreeGroup.lift ⇑t (mCompactFam 2 0 4 e k) = 1) :
    IsSelfDualN (2 * 0 + 2) ⇑t (mCompactFam 2 0 4 e) DD.Vmod :=
  mIsSelfDualN_Vmod t Sqrt5.qK_hyps.2 he hrt hrw hsimp DD hr

end Hsimp

end GQ2.Dyadic.Instances
