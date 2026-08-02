/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.KSupply
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

/-! ## §1 The procyclic-`M` alphabet ↔ core dictionary (at `η = 1`)

`Words/Mpc.lean`'s `eval_pro2_mpcW` reads the pro-`2` boundary as
`mWord α A B C₀ D · handleWord …` with `A = x₀⁻¹(x₂σ^s)^{-m}`, `B = x₁σ^p`, `C₀ = x₂σ^s`,
`D = σ^{η̂}`.  The letter table below is built from scratch — see the module docstring for why it
cannot be the compact one relabelled. -/

namespace MProcyclicCore

variable {G : Type*} [Group G]

/-! ### The dictionary is built at `h = 0`

Both AS3 procyclic rows are `h = 0` (`Words/Mpc.lean`'s `rawMpcSqrt10 = rawMpc 2 1 0 .one 0`
and `rawMpcSqrtNeg10 = rawMpc 2 1 1 .one 0`), so the dictionary is stated there.  That is not
only a convenience: at `h = 0` the core index type `Fin (coreRank 0)` is `Fin 4` on the nose and
the alphabet index type is `Fin 3`, so every `Fin` numeral reduces and the four `CoreReindex`
obligations are `fin_cases` plus `group`.  At symbolic `h` the same statements are blocked on
`(k : Fin (2 + 2h + 1)).val = k % (2h + 3)`, which does not reduce — the compact lane escapes
that only because it factors through `nReindex`, whose index lemmas were already paid for.
⚠ **Recorded for the board**: a general-`h` procyclic dictionary is a real (if routine) extra
cost, and no frozen instance needs it. -/

/-- **The procyclic-`M` core marking of an alphabet marking**, at the display `η = 1` and
`h = 0`: `(A, B, C₀, D) = (x₀⁻¹C₀^{-m}, x₁σ^p, x₂σ^s, σ)`.  Stated with no topological
hypotheses, so `WordCertificate.coreRel` can be built from it. -/
def mpcCoreMark (α r pp : ℕ) (t : Marking (2 + 2 * 0) G) : Fin (coreRank 0) → G :=
  ![(t.x 0)⁻¹ * ((t.x 2 * t.σ ^ s r) ^ m α)⁻¹, t.x 1 * t.σ ^ pp, t.x 2 * t.σ ^ s r, t.σ]

/-- **The inverse dictionary.**  `σ` is read off core slot `3` — which is exactly where `η = 1`
is used (`σ^{η̂} = σ`); `x₀, x₁, x₂` are then untwisted against it. -/
def mpcOfCore (α r pp : ℕ) (c : Fin (coreRank 0) → G) : Marking (2 + 2 * 0) G :=
  Marking.ofLetters (c 3) 1 ![(c 0 * c 2 ^ m α)⁻¹, c 1 * (c 3 ^ pp)⁻¹, c 2 * (c 3 ^ s r)⁻¹]

section Accessors

variable (α r pp : ℕ) (t : Marking (2 + 2 * 0) G) (c : Fin (coreRank 0) → G)

@[simp] theorem mpcCoreMark_zero :
    mpcCoreMark α r pp t 0 = (t.x 0)⁻¹ * ((t.x 2 * t.σ ^ s r) ^ m α)⁻¹ := rfl
@[simp] theorem mpcCoreMark_one : mpcCoreMark α r pp t 1 = t.x 1 * t.σ ^ pp := rfl
@[simp] theorem mpcCoreMark_two : mpcCoreMark α r pp t 2 = t.x 2 * t.σ ^ s r := rfl
@[simp] theorem mpcCoreMark_three : mpcCoreMark α r pp t 3 = t.σ := rfl

@[simp] theorem mpcOfCore_sigma : (mpcOfCore α r pp c).σ = c 3 := rfl
@[simp] theorem mpcOfCore_tau : (mpcOfCore α r pp c).τ = 1 := rfl
@[simp] theorem mpcOfCore_x_zero : (mpcOfCore α r pp c).x 0 = (c 0 * c 2 ^ m α)⁻¹ := rfl
@[simp] theorem mpcOfCore_x_one : (mpcOfCore α r pp c).x 1 = c 1 * (c 3 ^ pp)⁻¹ := rfl
@[simp] theorem mpcOfCore_x_two : (mpcOfCore α r pp c).x 2 = c 2 * (c 3 ^ s r)⁻¹ := rfl

end Accessors

/-- Core-index case split at `h = 0`: `coreRank 0 = 4`. -/
theorem coreIdx_cases (i : Fin (coreRank 0)) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hlt : (i : ℕ) < 4 := by have := i.isLt; simpa only [coreRank] using this
  interval_cases hv : (i : ℕ)
  exacts [Or.inl (Fin.ext (by rw [hv]; rfl)), Or.inr (Or.inl (Fin.ext (by rw [hv]; rfl))),
    Or.inr (Or.inr (Or.inl (Fin.ext (by rw [hv]; rfl)))),
    Or.inr (Or.inr (Or.inr (Fin.ext (by rw [hv]; rfl))))]

/-- Alphabet wild-index case split at `h = 0`: `2 + 2·0 + 1 = 3`. -/
theorem wildIdx_cases (j : Fin (2 + 2 * 0 + 1)) : j = 0 ∨ j = 1 ∨ j = 2 := by
  have hlt : (j : ℕ) < 3 := j.isLt
  interval_cases hv : (j : ℕ)
  exacts [Or.inl (Fin.ext (by rw [hv]; rfl)), Or.inr (Or.inl (Fin.ext (by rw [hv]; rfl))),
    Or.inr (Or.inr (Fin.ext (by rw [hv]; rfl)))]

theorem mpcCoreMark_mpcOfCore (α r pp : ℕ) (c : Fin (coreRank 0) → G) :
    mpcCoreMark α r pp (mpcOfCore α r pp c) = c := by
  funext i
  obtain rfl | rfl | rfl | rfl := coreIdx_cases i
  · rw [mpcCoreMark_zero, mpcOfCore_x_zero, mpcOfCore_x_two, mpcOfCore_sigma]; group
  · rw [mpcCoreMark_one, mpcOfCore_x_one, mpcOfCore_sigma]; group
  · rw [mpcCoreMark_two, mpcOfCore_x_two, mpcOfCore_sigma]; group
  · rw [mpcCoreMark_three, mpcOfCore_sigma]

theorem mpcOfCore_mpcCoreMark (α r pp : ℕ) (t : Marking (2 + 2 * 0) G) (ht : t.τ = 1) :
    mpcOfCore α r pp (mpcCoreMark α r pp t) = t := by
  ext g
  cases g with
  | sigma =>
    show (mpcOfCore α r pp (mpcCoreMark α r pp t)).σ = t.σ
    rw [mpcOfCore_sigma, mpcCoreMark_three]
  | tau => exact ht.symm
  | wild j =>
    show (mpcOfCore α r pp (mpcCoreMark α r pp t)).x j = t.x j
    obtain rfl | rfl | rfl := wildIdx_cases j
    · rw [mpcOfCore_x_zero, mpcCoreMark_zero, mpcCoreMark_two]; group
    · rw [mpcOfCore_x_one, mpcCoreMark_one, mpcCoreMark_three]; group
    · rw [mpcOfCore_x_two, mpcCoreMark_two, mpcCoreMark_three]; group

theorem map_mpcCoreMark {H : Type*} [Group H] {F : Type*} [FunLike F G H] [MonoidHomClass F G H]
    (f : F) (α r pp : ℕ) (t : Marking (2 + 2 * 0) G) (k : Fin (coreRank 0)) :
    f (mpcCoreMark α r pp t k) = mpcCoreMark α r pp (t.map ⇑f) k := by
  obtain rfl | rfl | rfl | rfl := coreIdx_cases k
  · rw [mpcCoreMark_zero, mpcCoreMark_zero]
    simp only [Marking.map_σ, Marking.map_x, map_mul, map_inv, map_pow]
  · rw [mpcCoreMark_one, mpcCoreMark_one]
    simp only [Marking.map_σ, Marking.map_x, map_mul, map_pow]
  · rw [mpcCoreMark_two, mpcCoreMark_two]
    simp only [Marking.map_σ, Marking.map_x, map_mul, map_pow]
  · rw [mpcCoreMark_three, mpcCoreMark_three, Marking.map_σ]

theorem map_mpcOfCore {H : Type*} [Group H] {F : Type*} [FunLike F G H] [MonoidHomClass F G H]
    (f : F) (α r pp : ℕ) (c : Fin (coreRank 0) → G) (g : Generator (2 + 2 * 0)) :
    f (mpcOfCore α r pp c g) = mpcOfCore α r pp (fun k => f (c k)) g := by
  cases g with
  | sigma => rfl
  | tau => exact map_one f
  | wild j =>
    show f ((mpcOfCore α r pp c).x j) = (mpcOfCore α r pp fun k => f (c k)).x j
    obtain rfl | rfl | rfl := wildIdx_cases j
    · rw [mpcOfCore_x_zero, mpcOfCore_x_zero]; simp only [map_inv, map_mul, map_pow]
    · rw [mpcOfCore_x_one, mpcOfCore_x_one]; simp only [map_mul, map_inv, map_pow]
    · rw [mpcOfCore_x_two, mpcOfCore_x_two]; simp only [map_mul, map_inv, map_pow]

/-- **The procyclic-`M` dictionary**, at the display `η = 1` and `h = 0`. -/
noncomputable def mpcReindex (α r pp : ℕ) : CoreReindex (2 + 2 * 0) (Fin (coreRank 0)) where
  toCore := fun t => mpcCoreMark α r pp t
  ofCore := fun c => mpcOfCore α r pp c
  ofCore_tau := fun _ => rfl
  toCore_ofCore := fun c => mpcCoreMark_mpcOfCore α r pp c
  ofCore_toCore := fun t ht => mpcOfCore_mpcCoreMark α r pp t ht
  toCore_nat := fun f t k => map_mpcCoreMark f α r pp t k
  ofCore_nat := fun f c g => map_mpcOfCore f α r pp c g

/-! ## §2 The two word-level fields -/

/-- **`WordCertificate.coreRel` at the procyclic-`M` row.** -/
def mpcCoreRel (α r pp : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * 0) G) : G :=
  mRelWord α (mpcCoreMark α r pp t)

/-- **`WordCertificate.proTwoWord` at the procyclic-`M` row**, i.e. WMP-a's Gate-C headline
`eval_pro2_mpcW_zero` (`GQ2/Dyadic/Words/Mpc.lean`) read through §1's dictionary.  The `η = 1`
step is `Zhat.ofInt 1` followed by `zpow_one` — the one place the display's invertibility is
used. -/
theorem mpcProTwoWord (α r pp : ℕ) (hα : 1 ≤ α) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking (2 + 2 * 0) G) :
    t.eval (pro2 (mpcW α r pp .one 0)) = mpcCoreRel α r pp G t := by
  rw [eval_pro2_mpcW_zero hα r pp .one t]
  show _ = mRelWord α (mpcCoreMark α r pp t)
  rw [mRelWord, show handleWord (fun j : Fin 0 => mpcCoreMark α r pp t (handleIdxU j))
      (fun j : Fin 0 => mpcCoreMark α r pp t (handleIdxV j)) = 1 from rfl, mul_one]
  rw [mpcCoreMark_zero, mpcCoreMark_one, mpcCoreMark_two, mpcCoreMark_three]
  simp only [EtaDisplay.zhat, zpowHat_ofInt, zpow_one]

/-- The same statement in the shape `CorePresentation.ofPresentedBy` consumes. -/
theorem eval_pro2_mpcW_reindex (α r pp : ℕ) (hα : 1 ≤ α) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * 0) G) :
    t.eval (pro2 (mpcW α r pp .one 0)) = (mNatWord α 0).ev ((mpcReindex α r pp).toCore t) :=
  mpcProTwoWord α r pp hα G t

/-- **The procyclic-`M` core presentation.**  Same core `D_M` as the compact row — both branches
specialize to `MarkedCore.mWord` — with §1's dictionary in place of the compact one. -/
noncomputable def mpcCorePresentation (α r pp : ℕ) (hα : 1 ≤ α) :
    CorePresentation (2 + 2 * 0) (mpcW α r pp .one 0) (DM α 0) :=
  CorePresentation.ofPresentedBy (isProP_DM α 0) (presentedBy_DM α 0) (dm_relation α 0)
    (mpcReindex α r pp) (fun t => eval_pro2_mpcW_reindex α r pp hα t)

/-- The dictionary sends `σ` to core generator **`3`** — not `2`, as in the compact row.  This is
the σ-offset convention, at the level of the marking, and it is why the procyclic Gram is 4×4
against the compact 5×5. -/
@[simp] theorem mpcCorePresentation_mark_sigma (α r pp : ℕ) (hα : 1 ≤ α) :
    (mpcCorePresentation α r pp hα).mark .sigma = dmGen α 0 3 := rfl

/-- …and the wild letters to the untwisted core generators: `x₀ ↦ (μ₀μ₂^m)⁻¹`, `x₁ ↦ μ₁μ₃^{-p}`,
`x₂ ↦ μ₂μ₃^{-s}`.  This is what `hnuWild` below is a condition on. -/
@[simp] theorem mpcCorePresentation_mark_wild (α r pp : ℕ) (hα : 1 ≤ α) (j : Fin (2 + 2 * 0 + 1)) :
    (mpcCorePresentation α r pp hα).mark (.wild j) = (mpcOfCore α r pp (dmGen α 0)).x j := rfl

/-! ## §3 The four pro-`2` fields -/

section ProTwo

/-- **`WordCertificate.pro2`.** -/
noncomputable def mpcPro2 (α r pp q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR (2 + 2 * 0) q (mpcW α r pp .one 0)) : Type)
      ((DM α 0 : ProfiniteGrp) : Type) :=
  CorePresentation.coreHom (mpcCorePresentation α r pp hα) hq0 hqe

/-- **`WordCertificate.ker_pro2`.** -/
theorem ker_mpcPro2 (α r pp q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    (mpcPro2 α r pp q hα hq0 hqe).toMonoidHom.ker
      = proPKernel 2 ((GammaR (2 + 2 * 0) q (mpcW α r pp .one 0)) : Type) :=
  CorePresentation.ker_coreHom (mpcCorePresentation α r pp hα) hq0 hqe

/-- **`WordCertificate.hpro2`.** -/
theorem mpcPro2_surjective (α r pp q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (mpcPro2 α r pp q hα hq0 hqe) :=
  CorePresentation.coreHom_surjective (mpcCorePresentation α r pp hα) hq0 hqe

/-- **`WordCertificate.tameSpecialization` at the procyclic-`M` row.**  ⚠ This is the branch
whose Gate-B line genuinely needs `1 ≤ α` (CB-0's note: "the only branch needing `1 ≤ α`"). -/
theorem mpcTameSpecializes (α r pp q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes (2 + 2 * 0) q (mpcW α r pp .one 0) :=
  Count.tameSpecializes_mpcW hq0 hqe hα r pp .one 0

/-- **`WordCertificate.compat`**, against F3b's `tameOfSpec`. -/
theorem mpcCompat (α r pp q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes (2 + 2 * 0) q (mpcW α r pp .one 0))
    (nuP : ContinuousMonoidHom ((DM α 0 : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mpcCorePresentation α r pp hα).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mpcCorePresentation α r pp hα).mark (.wild j)) = 1)
    (g : ((GammaR (2 + 2 * 0) q (mpcW α r pp .one 0)) : Type)) :
    nuTq q (tameOfSpec (2 + 2 * 0) q (mpcW α r pp .one 0) hspec g)
      = nuP (mpcPro2 α r pp q hα hq0 hqe g) :=
  CorePresentation.nu_compat_coreHom (mpcCorePresentation α r pp hα) hq0 hqe hspec nuP
    hnuSigma hnuWild g

end ProTwo

/-! ## §4 The procyclic-`M` word certificate, modulo AS1's four analytic clauses -/

section Certificate

/-- **The procyclic-`M` word certificate** at the display `η = 1`, `h = 0`.  Thirteen of the
seventeen fields proved; the four arguments are AS1's analytic clauses at exactly the record's
types. -/
noncomputable def mpcWordCertificate (α r pp q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 + 2 * 0)}
    (nuP : ContinuousMonoidHom ((DM α 0 : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mpcCorePresentation α r pp hα).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * 0 + 1),
      nuP ((mpcCorePresentation α r pp hα).mark (.wild j)) = 1)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * 0) q (mpcW α r pp .one 0))
      (2 + 2 * 0) q (DM α 0) nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * 0) q (mpcW α r pp .one 0)) (2 + 2 * 0) q
      (DM α 0) nuP SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q (mpcW α r pp .one 0)) (2 + 2 * 0) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q (mpcW α r pp .one 0))
      (2 + 2 * 0) q (DM α 0) nuP SN
      (tameOfSpec (2 + 2 * 0) q (mpcW α r pp .one 0) (mpcTameSpecializes α r pp q hα hq0 hqe))
      (mpcPro2 α r pp q hα hq0 hqe)
      (mpcCompat α r pp q hα hq0 hqe (mpcTameSpecializes α r pp q hα hq0 hqe) nuP hnuSigma
        hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * 0) q (mpcW α r pp .one 0) (DM α 0) (isProP_DM α 0) nuP SN where
  tameSpecialization := mpcTameSpecializes α r pp q hα hq0 hqe
  coreRel := mpcCoreRel α r pp
  proTwoWord := fun G _ _ _ _ _ t => mpcProTwoWord α r pp hα G t
  pro2 := mpcPro2 α r pp q hα hq0 hqe
  ker_pro2 := ker_mpcPro2 α r pp q hα hq0 hqe
  hpro2 := mpcPro2_surjective α r pp q hα hq0 hqe
  compat := mpcCompat α r pp q hα hq0 hqe (mpcTameSpecializes α r pp q hα hq0 hqe) nuP
    hnuSigma hnuWild
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLifting
  stokes := stokes
  scalar := scalar
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_mpcW _

end Certificate

/-! ## §5 The two `hsimp` fold-ins, procyclic-`M` row

The procyclic twins of `MCompactCore`'s pair, through WMP-c's `mpc_stokesDuality`
(`Certificates/MpcStokes.lean:447`), whose `hsimp` slot is verbatim AS1's. -/

section Hsimp

variable {C : Type*} [Group C] [Finite C] {α r pp q e : ℕ}

/-- **Fold-in (a): the `T`-payload**, in the shape `Count.hsepN_marking` /
`hsep_field_goal_marking` consume. -/
theorem mpcStokesDuality_T (t : Marking (2 + 2 * 0) C) (hα : 1 ≤ α) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * 0) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp .one 0) = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (mpcFam α r pp 0 q e .one) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) [DistribMulAction C (Additive ↥D.T)] :
    StokesDuality ⇑t (mpcFam α r pp 0 q e .one) (Additive ↥D.T) :=
  mpc_stokesDuality t hα hq he hrt hrw hsimp _ (Count.radT_add_self D)

/-- **Fold-in (b): the `Vmod`-payload**, in the shape `Count/Marking.lean` §5 consumes
(`isRightSeparating_vmod_mpcFam`'s `hsd` binder). -/
theorem mpcIsSelfDualN_Vmod (t : Marking (2 + 2 * 0) C) (hα : 1 ≤ α) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * 0) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp .one 0) = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (mpcFam α r pp 0 q e .one) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} (DD : DescData D) [DistribMulAction C DD.Vmod]
    (hr : ∀ k, FreeGroup.lift ⇑t (mpcFam α r pp 0 q e .one k) = 1) :
    IsSelfDualN (2 * 0 + 2) ⇑t (mpcFam α r pp 0 q e .one) DD.Vmod :=
  Count.isSelfDualN_of_stokesDuality (Count.nCompact_degree 0)
    (mpc_stokesDuality t hα hq he hrt hrw hsimp _ (Vmod_exp2 DD)) hr
    (mpc_isStokesEndpoint hα hq he)

end Hsimp

end MProcyclicCore

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

omit [FiniteDimensional ℚ_[2] ↥K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The `√10` row's `κ_K ≠ 0`** — as at every `M`/`N` row, from the standing ramified-`i`
binder through FD2 (`n = 2` is even, so the head is `[[1,1],[1,0]]`). -/
theorem kappaK_ne_zero_sqrtTen {δi : ℚ̄₂} (hδ : δi ^ 2 = -1)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi) :
    FieldData.kappaK K ≠ 0 :=
  kappaK_ne_zero_of_ramified hδ (ramified δi hδ)

end Main

end GQ2.Dyadic.Instances
