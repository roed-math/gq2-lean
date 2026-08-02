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
import GQ2.Dyadic.Certificates.MpcStokes

/-!
# The `ℚ₂(√10)` instance, and the procyclic-`M` instantiation layer  (dyadic campaign, AS3)

**Selection-freeze row 5** at its `ε = 0` instance: `K = ℚ₂(√10)`, `n = [K : ℚ₂] = 2`,
`q_K = 2`, and the frozen branch word is `mpcW 2 1 0 .one 0` — `(α, r, ε, η) = (2, 1, 0, 1)`,
so `s = 2^r = 2`, `p = ε·2^{r−1} = 0`, `m = 2^{α−1} = 2` (`Words/Mpc.lean`, certificate
`M-procyclic-alpha2-r1-eps0-eta1-h0-q2-v001`).

As with the compact pair, this file carries **two** things:

* **§1–§4, `MProcyclicCore`** — the procyclic-`M` branch layer, generic in `(α, r, p, q)` at the
  `η = 1` display and `h = 0`: the alphabet ↔ core dictionary, the `CorePresentation`, and the
  `WordCertificate` producer.  `√−10` (`GQ2/Dyadic/Instances/SqrtNeg10.lean`) consumes it
  unchanged at `p = 1`.  ⚠ **branch machinery — should be hoisted**, see the note below.
  §5 carries the two `hsimp` fold-ins, also branch-generic.
* **§6–§7** — the `√10` row: frozen parameters and packet Thm 1.1 at `K`.

## The dictionary, and why it does not factor the way the compact one does

`Sqrt2.lean`'s compact-`M` dictionary is the compact-`N` letter table plus a *core-side* change
of variable, so it factors through `Count.PilotN.nReindex`.  The procyclic dictionary does not,
and the reason is structural rather than incidental:

```
compact  M :  (μ₀, μ₁, μ₂, μ₃) = (x₀⁻¹σ^{-m},  x₁,        σ,        x₂)
procyclic M:  (μ₀, μ₁, μ₂, μ₃) = (x₀⁻¹C₀^{-m}, x₁σ^p,     C₀ = x₂σ^s, σ^{η̂})
```

`σ` sits at core slot **2** in the compact row and at slot **3** in the procyclic row, and slot 2
carries the *twisted* boundary letter `C₀`.  So the two rows put `σ` and `x₂` in opposite slots;
no relabelling of the compact table produces the procyclic one, and the dictionary has to be
built from scratch (§1).  This is the same "σ-offset convention"
the WMP lane recorded as forcing a 4×4 Gram against the compact 5×5 — the two facts have one
cause, and it is visible here at the level of the dictionary.

**Invertibility needs `η = 1`.**  Core slot 3 is `σ^{η̂}`, so recovering `σ` from a core marking
means inverting a `ℤ̂`-power.  At the frozen displays that is free — both AS3 procyclic rows have
`η = 1`, i.e. `EtaDisplay.one`, whose `zhat` is `Zhat.ofInt 1` — but it is **not** available at a
general `.hat num den` display, where `σ^{η̂}` generates a proper closed subgroup of `⟨σ⟩` in
general.  §1's `mpcReindex` is therefore stated at `EtaDisplay.one` and this is a genuine
limitation, recorded rather than papered over: a `.hat`-display procyclic instance would need a
different construction (or an `η̂`-invertibility hypothesis).  ⚠ **Finding, for the board.**

## `r ≥ 1` at the frozen procyclic rows

WNP-c's finding — that the corrected cross operator `L_c`'s kernel dichotomy *turns on* `r`, is
identically zero at `r = 0` (where `A = B = g` with `g² + g + 1 = 0`) and invertible at `r = 1`,
and that `r ≥ 1` is precisely the side condition the cross-operator layer deliberately does not
consume — is discharged at both AS3 procyclic rows by inspection of the frozen parameters:
**both are `r = 1`** (`Words/Mpc.lean`'s `branchData_sqrtNeg10` and `branchData_sqrt10`, whose
`level` field is `1`).  §6's `sqrtTenRow` states it as a theorem so the discharge is checkable
and not a remark, and `r_pos` is the named handle.  Note this is a *parameter* fact, not a
mathematical one: nothing here re-derives `L_c`'s dichotomy, and nothing here needs to — the
degenerate `r = 0` row simply is not among the six frozen procyclic instances.

## What is **not** proved here — and one asymmetry between the two procyclic fields

The four analytic `WordCertificate` clauses are arguments, exactly as in the compact lane (AS1
divergence 4).  In addition, and specific to this branch:

⚠ **`Mpc.hlinrow` is closed only at `√−10`.**  `Certificates/MpcStokes.lean` carries
`sqrtNeg10_hlinrow` and the assembled `sqrtNeg10ProductCert` at `(α, r, p) = (2, 1, 1)`; there is
**no `√10` twin**, so the `ε = 0` row's linear-copy Fox row at σ-free offsets remains an input to
`mpcProductRowCert`.  That does not block this file — `hlinrow` is not a `WordCertificate` field,
it is an ingredient of the (still unowned) certificate ⇒ count bridge — but it means the two
procyclic fields are **not** at the same depth, and `√10` is the shallower one.  AS1's own
docstring predicted this ("`Mpc.hlinrow` at general `(α, r, p, η)` was closed ONLY at `√−10`").

## Numeric leaves

**Nothing in this file reads a count.**  No `Nat.card`, no exponent constant, no `SourceNumerics`
value: `standardNumerics 2` is named, never unfolded.  `s 1 = 2`, `m 2 = 2`, `p false 1 = 0` are
*word* parameters (`GQ2/Dyadic/Parameters.lean`), not counts.

## Regression cross-checks against the freeze (not proofs)

`Words/Mpc.lean` records for this row: `L = 64` (against `67` at `ε = 1`), certificate
`M-procyclic-alpha2-r1-eps0-eta1-h0-q2-v001`, and F5 row **B2** — draft §7.3's field-specific
`R₁₀` (marking `ν(a,b,c,d) = (−4,0,2,1)`) agrees with the frozen row pointwise on every harness
target but is **not** the frozen spelling; epimorphism counts `(S₃, D₈, A₄) = (6, 1568, 120)`,
the same as `√−10`, because no `2`-group sees `σ` versus `σ₂` and `A₄` needs a genuine
epimorphism enumeration.  All cited; no proof here depends on any of it.

## Axioms

`sorry`-free, no new axiom, no `decide`.  §1–§6 print exactly the standard three; §7's headline
prints std-3 + `{B1, B6, B7}` (ASK's surface) — no B5-K, no B10-K.  Measured, not budgeted.

## ⚠ Orchestrator note

`MProcyclicCore` (§1–§5) is branch machinery and belongs beside `Count.PilotN` and the compact-`M`
layer, not in an instance file; it lives here only because AS3 owns four files.
`SqrtNeg10.lean` imports this module solely to reach it.
-/

namespace GQ2.Dyadic.Instances

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore GQ2.SectionEight
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count.PilotN TameSpec
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Instances.NuWitness

/-! ## §6 The `ℚ₂(√10)` row

`(α, r, ε, η) = (2, 1, 0, 1)`, `h = 0`, `s = 2`, `p = 0`, `m = 2`, `q_K = 2`, `n = 2`. -/

namespace Sqrt10

open MProcyclicCore

/-- The frozen branch word of `ℚ₂(√10)`: the `ε = 0` procyclic row. -/
noncomputable abbrev word : PWord (Generator (2 + 2 * 0)) := mpcW 2 1 0 .one 0

/-- The standard core of the row: `D_M` at `α = 2`, rank `4`. -/
noncomputable abbrev core : ProfiniteGrp := DM 2 0

theorem alpha_valid : (1 : ℕ) ≤ 2 := by omega

/-- **The frozen row data**, pinned against WMP-a's own `branchData_sqrt10`: a valid procyclic
datum at `(α, r, ε) = (2, 1, false)` with `p = 0`, and `s 1 = 2`, `m 2 = 2`. -/
theorem sqrtTenRow :
    (BranchData.Mpc 2 1 false 1).Valid ∧ (BranchData.Mpc 2 1 false 1).pVal = 0 ∧
      s 1 = 2 ∧ m 2 = 2 :=
  ⟨branchData_sqrt10.1, branchData_sqrt10.2, rfl, rfl⟩

/-- **WNP-c's `r ≥ 1` side condition, discharged at this row by inspection of the freeze.**

The corrected cross operator's kernel dichotomy turns on `r`: identically zero at `r = 0` (where
`A = B = g` and `g² + g + 1 = 0`), invertible at `r = 1`.  The frozen `√10` row has `level = 1`,
so the degenerate case does not arise here.  This is a *parameter* discharge — it re-derives
nothing about `L_c`; it records that the `r = 0` row is not among the frozen instances. -/
theorem r_pos : 1 ≤ (BranchData.Mpc 2 1 false 1).level := by
  rw [show (BranchData.Mpc 2 1 false 1).level = 1 from rfl]

/-- The tame modulus of `ℚ₂(√10)`: `q_K = 2`. -/
theorem qK_hyps : (2 : ℕ) ≠ 0 ∧ Even (2 : ℕ) := ⟨two_ne_zero, even_two⟩

/-- **The row's `ν_P`** — `MProcyclicCore`'s witness at `(α, r, p) = (2, 1, 0)`; it is what makes
§7's `candidate_equiv_galK_sqrtTen_nonvacuous` a theorem with no `ν`-binders (ticket AS3-b). -/
noncomputable abbrev nu : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo :=
  mpcNu 2 1 0 alpha_valid

end Sqrt10

/-! ## §7 Packet Theorem 1.1 at `ℚ₂(√10)` -/

section Main

open Sqrt10 MProcyclicCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
  {T : OrientedTameQuotientK B FF}

/-- **Packet Theorem 1.1 at `K = ℚ₂(√10)`.**

`⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ², R_{M,pc}(α=2, r=1, ε=0) = 1, ⟪x₀,x₁,x₂⟫ pro-2⟩_prof ≅ G_K`.

The hypothesis list is the procyclic twin of `√2`'s, with `hqK` instantiated at `q = 2`. -/
theorem candidate_equiv_galK_sqrtTen {q : ℕ} (hqK : qOf K FF = q)
    (nuP : ContinuousMonoidHom ((core : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mpcCorePresentation 2 1 0 alpha_valid).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mpcCorePresentation 2 1 0 alpha_valid).mark (.wild j)) = 1)
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
        (mpcTameSpecializes 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)))
      (mpcPro2 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mpcCompat 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mpcTameSpecializes 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
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
    (mpcWordCertificate 2 1 0 (qOf K FF) alpha_valid (qOf_ne_zero K FF) (even_qOf K FF) nuP
      hnuSigma hnuWild exactLifting stokes scalar determinant)
    KS params params_n params_qK ramified ramifiedData hnuP

/-- **Packet Theorem 1.1 at `K = ℚ₂(√10)`, with the `ν`-normalization discharged**
(ticket AS3-b).

The procyclic twin of `candidate_equiv_galK_sqrtTwo_nonvacuous`: the four binders `nuP`,
`hnuSigma`, `hnuWild`, `hnuP` are gone, at the concrete `ν_P = Sqrt10.nu`. -/
theorem candidate_equiv_galK_sqrtTen_nonvacuous {q : ℕ} (hqK : qOf K FF = q)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core nu
      (standardNumerics (2 + 2 * 0)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core nu
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0) q core
      nu (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q word
        (mpcTameSpecializes 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)))
      (mpcPro2 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mpcCompat 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mpcTameSpecializes 2 1 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF)
          (hqK ▸ even_qOf K FF)) nu (mpcNu_sigma 2 1 0 alpha_valid)
        (mpcNu_wild 2 1 0 alpha_valid))
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
  candidate_equiv_galK_sqrtTen hqK nu (mpcNu_sigma 2 1 0 alpha_valid)
    (mpcNu_wild 2 1 0 alpha_valid) (mpcNu_surjective 2 1 0 alpha_valid) exactLifting stokes
    scalar determinant KS params params_n params_qK ramified ramifiedData

omit [FiniteDimensional ℚ_[2] ↥K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The `√10` row's `κ_K ≠ 0`** — as at every `M`/`N` row, from the standing ramified-`i`
binder through FD2 (`n = 2` is even, so the head is `[[1,1],[1,0]]`). -/
theorem kappaK_ne_zero_sqrtTen {δi : ℚ̄₂} (hδ : δi ^ 2 = -1)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi) :
    FieldData.kappaK K ≠ 0 :=
  kappaK_ne_zero_of_ramified hδ (ramified δi hδ)

end Main

end GQ2.Dyadic.Instances
