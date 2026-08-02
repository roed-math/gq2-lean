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

/-!
# The `ℚ₂(√2)` instance, and the compact-`M` instantiation layer  (dyadic campaign, ticket AS3)

**Selection-freeze row 4** at its `α = 3` instance: `K = ℚ₂(√2)` is ramified quadratic, so
`n = [K : ℚ₂] = 2`, `f = 1`, `q_K = 2`, and the frozen branch word is `mCompactW 3 0` with
`m = 2^{α−1} = 4` (`Words/M0.lean`, certificate `M-compact-alpha3-h0-q2-v001`).

This file carries **two** things, and the split matters for the orchestrator:

* **§1–§4, `MCompactCore`** — the compact-`M` *branch* layer, generic in `(α, h, q)`: the
  alphabet ↔ core dictionary (`CoreReindex`), the `CorePresentation` it produces, and the
  `WordCertificate` producer that leaves exactly AS1's four analytic clauses open.  `√5`
  (`GQ2/Dyadic/Instances/Sqrt5.lean`) consumes this namespace unchanged; only `α` and `q` differ.
  ⚠ **This layer is not `√2`-specific and should be hoisted** — see the orchestrator note at the
  bottom of the module docstring.
* **§5–§7** — the `√2` row proper: the frozen parameters, the field's headline (packet Thm 1.1 at
  `K`), and the two `hsimp` fold-ins.

## What was missing and is built here (the ticket's real content)

`Count/ProTwo.lean` §6 states the per-branch cost of the pro-`2` bridge exactly: *"the only
per-branch work left is the **dictionary** between the alphabet `{σ, τ, x₀, …, x_n}` and the
core's index type"*, i.e. one `CoreReindex`.  Before this file the repository had **one**, for
compact `N` (`Count.PilotN.nReindex`); the compact-`M` and procyclic-`M` rows had none, so
`WordCertificate.pro2` / `.ker_pro2` / `.hpro2` / `.compat` were unreachable at all four AS3
fields.  §1 builds the compact-`M` dictionary, and it costs far less than the memo's
"80–150 lines per branch" estimate because of one observation:

> **the compact-`M` letter table *is* the compact-`N` letter table.**  Both cores have rank
> `4 + 2h` with `σ` at index 2, the wild letters at `0, 1, 3` and the handle pairs at
> `4 + 2j, 5 + 2j`.  The only difference is that slot `0` carries the *twisted* letter
> `A₀ = x₀⁻¹σ^{-m}` rather than the bare `x₀`.

So the dictionary factors as `nReindex` conjugated by a triangular change of variable on the
core marking, `mTwist`/`mUntwist` (§1), and the four `CoreReindex` round-trip/naturality
obligations reduce to `nReindex`'s own plus two one-line group identities.  This factorization
is reusable: every branch whose twist is a *core-side* change of variable can take it.

## What is **not** proved here, and why — AS1's divergence 4, unchanged

`WordCertificate` has four analytic clause fields (`exactLifting`, `stokes`, `scalar`,
`determinant`) whose producers do not exist at the candidate carrier — AS1's divergence 4,
restated by AS4 (`GQ2/Dyadic/Instances/QTwo.lean`, "⚠ What blocks the last two rows").  §4's
producer therefore takes those four as **explicit arguments**, and the field headline (§6) takes
them plus a `KSupply` (ASK's own carried record).  Every *other* field of both records is
supplied here or upstream.  No `sorry`, and no clause is assumed that the landed stack proves.

The inventory at `(n, q, R) = (2, 2, mCompactW 3 0)`:

| `WordCertificate` field | status |
|---|---|
| `tameSpecialization` | **proved** (`Count.tameSpecializes_mCompact`) |
| `coreRel`, `proTwoWord` | **proved** (§2, from WM0-a's `eval_pro2_mCompact`) |
| `pro2`, `ker_pro2`, `hpro2`, `compat` | **proved** — §1's dictionary + `Count.CorePresentation` |
| `tfg` | **proved** (`Count.gammaR_topologicallyFinitelyGenerated`) |
| `smulZmod2`, `contSMulZmod2`, `htriv` | **proved** (`Count.trivialSMulZmodTwo` &c.) |
| `htame` | **proved** (`Count.htame_of_tameSpecializes`) |
| `hwild` | **proved** (`Count.hwild_mCompact`) |
| `exactLifting`, `stokes`, `scalar`, `determinant` | ⚠ **argument** — AS1 divergence 4 |

`hnuSigma`/`hnuWild` (F3's `prop_3_4_three` normalization of `ν_P` against the *dictionary's*
marking) are arguments too; they are conditions on the abstract slot `(P, ν_P)`, exactly as in
`Count.PilotN.n_exists_proTwo`, and §3 spells out what they say about `dmGen`.

## Numeric leaves

**Nothing in this file reads a count.**  No `Nat.card`, no exponent constant and no
`SourceNumerics` *value* is written anywhere: the numerics enter only as the opaque parameter
`SN`, and §6 instantiates it at `standardNumerics 2` by name, never by its formula.  CB-SG's
exponent warning (`2^{d·v₂(#A)}` versus `2^{v₂(#A)}`) therefore has nothing to bite on here.

## Regression cross-checks against the freeze (not proofs)

`Words/M0.lean`'s F5 rows record `d = 2 ⇒ M(α = 3, r = 0)`, `m = 4`, `q_K = 2`, epimorphism
counts `(S₃, D₈, A₄) = (6, 1568, 120)`, certificate `M-compact-alpha3-h0-q2-v001`, AST digest
`0209b708538277e0…`.  §5's `sqrtTwoRow` pins the `(α, h, level)` triple against WM0-a's own
`branchData_sqrtTwo` and `mOf 3 = 4`; the harness numbers are **cited only**, and no proof in
this file depends on them.

## Axioms

`sorry`-free.  No new axiom, no `decide`, no `native_decide`.  §1–§4 print the standard three;
§6's headline prints std-3 plus whatever `KSupply` and AS1's assembly carry (B1/B6/B7 through
ASK).  Per-declaration prints are in the ticket report.

## ⚠ Orchestrator note

`MCompactCore` (§1–§4) is branch machinery, not instance machinery, and belongs next to
`Count.PilotN` in `GQ2/Dyadic/Count/ProTwo.lean` (or in a new `GQ2/Dyadic/Instances/Cores.lean`).
It lives here only because AS3 owns four files and may not create a fifth; `Sqrt5.lean` imports
this module solely to reach it.  Hoisting is a pure move — nothing in §1–§4 mentions `√2`.
-/

namespace GQ2.Dyadic.Instances

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore GQ2.SectionEight
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Count.PilotN TameSpec
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact

/-! ## §1 The compact-`M` alphabet ↔ core dictionary

`Words/M0.lean`'s `eval_pro2_mCompact` reads the pro-`2` boundary of the compact-`M` word as
`MarkedCore.mWord α A₀ x₁ σ x₂ · handleWord …` with `A₀ = x₀⁻¹σ^{-m}`.  Against
`MarkedCore.mRelWord α μ = mWord α (μ 0) (μ 1) (μ 2) (μ 3) · handleWord …` that is the compact-`N`
letter table `nIdx` with slot `0` replaced by `A₀`; so the dictionary is `nReindex` composed with
the core-side change of variable below. -/

namespace MCompactCore

variable {G : Type*} [Group G]

/-- **The compact-`M` twist**: `μ₀ ↦ μ₀⁻¹ μ₂^{-m}`, identity on every other slot.  Applied to
the compact-`N` core marking `i ↦ t (nIdx h i)` it produces exactly the marking
`eval_pro2_mCompact` evaluates `mRelWord` at. -/
def mTwist (α h : ℕ) (c : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  fun i => if (i : ℕ) = 0 then (c i)⁻¹ * c 2 ^ (-(mOf α : ℤ)) else c i

/-- **The inverse change of variable**: `μ₀ ↦ (μ₀ μ₂^{m})⁻¹`. -/
def mUntwist (α h : ℕ) (c : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  fun i => if (i : ℕ) = 0 then (c i * c 2 ^ (mOf α : ℤ))⁻¹ else c i

theorem mTwist_apply_ne (α h : ℕ) (c : Fin (coreRank h) → G) {i : Fin (coreRank h)}
    (hi : (i : ℕ) ≠ 0) : mTwist α h c i = c i := if_neg hi

theorem mUntwist_apply_ne (α h : ℕ) (c : Fin (coreRank h) → G) {i : Fin (coreRank h)}
    (hi : (i : ℕ) ≠ 0) : mUntwist α h c i = c i := if_neg hi

theorem coreIdx_two_ne_zero (h : ℕ) : ((2 : Fin (coreRank h)) : ℕ) ≠ 0 := by
  rw [coreVal_two]; omega

@[simp] theorem mTwist_two (α h : ℕ) (c : Fin (coreRank h) → G) :
    mTwist α h c 2 = c 2 := mTwist_apply_ne α h c (coreIdx_two_ne_zero h)

@[simp] theorem mUntwist_two (α h : ℕ) (c : Fin (coreRank h) → G) :
    mUntwist α h c 2 = c 2 := mUntwist_apply_ne α h c (coreIdx_two_ne_zero h)

@[simp] theorem mTwist_one (α h : ℕ) (c : Fin (coreRank h) → G) :
    mTwist α h c 1 = c 1 := mTwist_apply_ne α h c (by rw [coreVal_one]; omega)

@[simp] theorem mTwist_three (α h : ℕ) (c : Fin (coreRank h) → G) :
    mTwist α h c 3 = c 3 := mTwist_apply_ne α h c (by rw [coreVal_three]; omega)

@[simp] theorem mTwist_handleIdxU (α h : ℕ) (c : Fin (coreRank h) → G) (j : Fin h) :
    mTwist α h c (handleIdxU j) = c (handleIdxU j) :=
  mTwist_apply_ne α h c (by rw [handleIdxU_val]; omega)

@[simp] theorem mTwist_handleIdxV (α h : ℕ) (c : Fin (coreRank h) → G) (j : Fin h) :
    mTwist α h c (handleIdxV j) = c (handleIdxV j) :=
  mTwist_apply_ne α h c (by rw [handleIdxV_val]; omega)

@[simp] theorem mTwist_zero (α h : ℕ) (c : Fin (coreRank h) → G) :
    mTwist α h c 0 = (c 0)⁻¹ * c 2 ^ (-(mOf α : ℤ)) := if_pos (coreVal_zero h)

@[simp] theorem mUntwist_zero (α h : ℕ) (c : Fin (coreRank h) → G) :
    mUntwist α h c 0 = (c 0 * c 2 ^ (mOf α : ℤ))⁻¹ := if_pos (coreVal_zero h)

theorem mTwist_mUntwist (α h : ℕ) (c : Fin (coreRank h) → G) :
    mTwist α h (mUntwist α h c) = c := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by rw [h0, coreVal_zero])
    subst hi
    rw [mTwist_zero, mUntwist_zero, mUntwist_two, inv_inv]
    group
  · rw [mTwist_apply_ne _ _ _ h0, mUntwist_apply_ne _ _ _ h0]

theorem mUntwist_mTwist (α h : ℕ) (c : Fin (coreRank h) → G) :
    mUntwist α h (mTwist α h c) = c := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by rw [h0, coreVal_zero])
    subst hi
    rw [mUntwist_zero, mTwist_zero, mTwist_two]
    group
  · rw [mUntwist_apply_ne _ _ _ h0, mTwist_apply_ne _ _ _ h0]

/-- Both changes of variable commute with any monoid hom — the naturality input for the two
`CoreReindex` naturality fields.  Stated at `MonoidHomClass` so that the `ContinuousMonoidHom`
the structure's fields quantify over is passed unbundled (the `.toMonoidHom` spelling is defeq
but *not* at `instances` transparency, AS4-b's friction). -/
theorem map_mTwist {H : Type*} [Group H] {F : Type*} [FunLike F G H] [MonoidHomClass F G H]
    (f : F) (α h : ℕ) (c : Fin (coreRank h) → G) :
    (fun i => f (mTwist α h c i)) = mTwist α h (fun i => f (c i)) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · rw [show mTwist α h c i = (c i)⁻¹ * c 2 ^ (-(mOf α : ℤ)) from if_pos h0,
      show mTwist α h (fun i => f (c i)) i = (f (c i))⁻¹ * (f (c 2)) ^ (-(mOf α : ℤ)) from
        if_pos h0, map_mul, map_inv, map_zpow]
  · rw [mTwist_apply_ne _ _ _ h0,
      show mTwist α h (fun i => f (c i)) i = f (c i) from if_neg h0]

theorem map_mUntwist {H : Type*} [Group H] {F : Type*} [FunLike F G H] [MonoidHomClass F G H]
    (f : F) (α h : ℕ) (c : Fin (coreRank h) → G) :
    (fun i => f (mUntwist α h c i)) = mUntwist α h (fun i => f (c i)) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · rw [show mUntwist α h c i = (c i * c 2 ^ (mOf α : ℤ))⁻¹ from if_pos h0,
      show mUntwist α h (fun i => f (c i)) i = (f (c i) * (f (c 2)) ^ (mOf α : ℤ))⁻¹ from
        if_pos h0, map_inv, map_mul, map_zpow]
  · rw [mUntwist_apply_ne _ _ _ h0,
      show mUntwist α h (fun i => f (c i)) i = f (c i) from if_neg h0]

/-- **The compact-`M` dictionary.**  `nReindex` conjugated by the triangular change of variable
of this section: the letter table is compact-`N`'s, slot `0` carries `A₀ = x₀⁻¹σ^{-m}`. -/
noncomputable def mReindex (α h : ℕ) : CoreReindex (2 + 2 * h) (Fin (coreRank h)) where
  toCore := fun t => mTwist α h ((nReindex h).toCore t)
  ofCore := fun m => (nReindex h).ofCore (mUntwist α h m)
  ofCore_tau := fun m => (nReindex h).ofCore_tau (mUntwist α h m)
  toCore_ofCore := fun m => by
    rw [(nReindex h).toCore_ofCore (mUntwist α h m), mTwist_mUntwist]
  ofCore_toCore := fun t ht => by
    rw [mUntwist_mTwist, (nReindex h).ofCore_toCore t ht]
  toCore_nat := fun f t k => by
    have hnat : (fun i => f ((nReindex h).toCore t i)) = (nReindex h).toCore (t.map ⇑f) :=
      funext fun i => (nReindex h).toCore_nat f t i
    calc f (mTwist α h ((nReindex h).toCore t) k)
        = mTwist α h (fun i => f ((nReindex h).toCore t i)) k :=
          congrFun (map_mTwist f α h ((nReindex h).toCore t)) k
      _ = mTwist α h ((nReindex h).toCore (t.map ⇑f)) k := by rw [hnat]
  ofCore_nat := fun f m g => by
    rw [(nReindex h).ofCore_nat f (mUntwist α h m) g]
    exact congrArg (fun c => (nReindex h).ofCore c g) (map_mUntwist f α h m)

/-- The compact-`M` core marking of an alphabet marking, in closed form and with **no**
topological hypotheses — which is what lets `WordCertificate.coreRel` (whose binder list has no
`T2Space`) be stated with it. -/
def mCoreMark (α h : ℕ) {G : Type*} [Group G] (t : Marking (2 + 2 * h) G) :
    Fin (coreRank h) → G :=
  mTwist α h (fun i => t (nIdx h i))

/-- **`WordCertificate.coreRel` at the compact-`M` row.** -/
def mCoreRel (α h : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G) : G :=
  mRelWord α (mCoreMark α h t)

/-- **`WordCertificate.proTwoWord` at the compact-`M` row**, i.e. WM0-a's Gate-C headline
(`GQ2/Dyadic/Words/M0.lean:648`) read through §1's dictionary, at every handle count.  `1 ≤ α` is
genuine — WM0-a's own note: the third factor is `σ₂^{2m}` and `2m = 2^α` fails at `α = 0`. -/
theorem mProTwoWord (α h : ℕ) (hα : 1 ≤ α) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mCompactW α h)) = mCoreRel α h G t := by
  rw [eval_pro2_mCompact hα t]
  show _ = mRelWord α (mTwist α h (fun i => t (nIdx h i)))
  simp only [mRelWord, mTwist_zero, mTwist_one, mTwist_two, mTwist_three, mTwist_handleIdxU,
    mTwist_handleIdxV, nIdx_zero, nIdx_one, nIdx_two, nIdx_three, nIdx_handleIdxU,
    nIdx_handleIdxV, Marking.apply_sigma]

/-- The same statement in the shape `CorePresentation.ofPresentedBy` consumes. -/
theorem eval_pro2_mCompact_reindex (α h : ℕ) (hα : 1 ≤ α) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mCompactW α h)) = (mNatWord α h).ev ((mReindex α h).toCore t) :=
  mProTwoWord α h hα G t

/-- **The compact-`M` core presentation.**  Inputs, all landed: `isProP_DM`, `presentedBy_DM`
(`MarkedCore/Certificate.lean:292`), `dm_relation`, and §1's dictionary against WM0-a's
`eval_pro2_mCompact`.  Note that `presentedBy_DM`/`dm_relation` are used, **not**
`markedRelator_DM`, so no `MMixHypothesis` and no Labute input is inherited — only WM0-a's own
`1 ≤ α`. -/
noncomputable def mCorePresentation (α h : ℕ) (hα : 1 ≤ α) :
    CorePresentation (2 + 2 * h) (mCompactW α h) (DM α h) :=
  CorePresentation.ofPresentedBy (isProP_DM α h) (presentedBy_DM α h) (dm_relation α h)
    (mReindex α h) (fun t => eval_pro2_mCompact_reindex α h hα t)

/-- The dictionary sends `σ` to core generator `2` — the slot `mWord`'s third letter occupies. -/
@[simp] theorem mCorePresentation_mark_sigma (α h : ℕ) (hα : 1 ≤ α) :
    (mCorePresentation α h hα).mark .sigma = dmGen α h 2 :=
  congrArg (dmGen α h) (Fin.ext (by rw [coreVal_two]; rfl))

/-- …and the wild letters to the *untwisted* core generators: `x₀ ↦ (μ₀ μ₂^{m})⁻¹` and
`x_j ↦ μ_{nWildIdx j}` for `j ≥ 1`.  This is what `hnuWild` below is a condition on. -/
@[simp] theorem mCorePresentation_mark_wild (α h : ℕ) (hα : 1 ≤ α)
    (j : Fin (2 + 2 * h + 1)) :
    (mCorePresentation α h hα).mark (.wild j) = mUntwist α h (dmGen α h) (nWildIdx h j) := rfl

/-! ## §3 The four pro-`2` fields

`Count.CorePresentation`'s bridge at §1's presentation.  Nothing branch-specific survives: the
`ℚ₂` ancestor is `GQ2.Roe.exists_pro2R`, which carries `BLabHypothesis`; this does not.

All parameters are explicit: `h` occurs in these statements only inside `GammaR`/`DM`, so with it
implicit the elaborator cannot solve for it at a use site such as
`Function.Surjective (mPro2 …)`. -/

section ProTwo

/-- **`WordCertificate.pro2`.** -/
noncomputable def mPro2 (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR (2 + 2 * h) q (mCompactW α h)) : Type)
      ((DM α h : ProfiniteGrp) : Type) :=
  CorePresentation.coreHom (mCorePresentation α h hα) hq0 hqe

/-- **`WordCertificate.ker_pro2`.** -/
theorem ker_mPro2 (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    (mPro2 α h q hα hq0 hqe).toMonoidHom.ker
      = proPKernel 2 ((GammaR (2 + 2 * h) q (mCompactW α h)) : Type) :=
  CorePresentation.ker_coreHom (mCorePresentation α h hα) hq0 hqe

/-- **`WordCertificate.hpro2`.** -/
theorem mPro2_surjective (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (mPro2 α h q hα hq0 hqe) :=
  CorePresentation.coreHom_surjective (mCorePresentation α h hα) hq0 hqe

/-- **`WordCertificate.tameSpecialization` at the compact-`M` row** (CB-0's branch line). -/
theorem mTameSpecializes (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes (2 + 2 * h) q (mCompactW α h) :=
  Count.tameSpecializes_mCompact hq0 hqe α h

/-- **`WordCertificate.compat`**, against F3b's `tameOfSpec`.  The two `ν_P` conditions are F3's
`prop_3_4_three` normalization *at the dictionary's marking*; §1's two `mark` lemmas say what
they are in terms of `dmGen`. -/
theorem mCompat (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes (2 + 2 * h) q (mCompactW α h))
    (nuP : ContinuousMonoidHom ((DM α h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mCorePresentation α h hα).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1),
      nuP ((mCorePresentation α h hα).mark (.wild j)) = 1)
    (g : ((GammaR (2 + 2 * h) q (mCompactW α h)) : Type)) :
    nuTq q (tameOfSpec (2 + 2 * h) q (mCompactW α h) hspec g)
      = nuP (mPro2 α h q hα hq0 hqe g) :=
  CorePresentation.nu_compat_coreHom (mCorePresentation α h hα) hq0 hqe hspec nuP hnuSigma
    hnuWild g

end ProTwo

/-! ## §4 The compact-`M` word certificate, modulo AS1's four analytic clauses

Every field the landed stack proves is filled; `exactLifting`, `stokes`, `scalar` and
`determinant` are arguments, because the certificate ⇒ count bridge does not exist at the
candidate carrier (AS1 divergence 4).  This is the exact posture `KSupply` takes on the
arithmetic side, and it is what keeps the gap countable rather than hidden. -/

section Certificate

/-- **The compact-`M` word certificate.**  Thirteen of the seventeen fields are proved; the four
arguments are AS1's analytic clauses, stated at exactly the record's types (so that the elaborator
is the acceptance check — `determinant` depends on `tameSpecialization`, `pro2` and `compat`, and
only typechecks if this file's terms sit at the field's type). -/
noncomputable def mWordCertificate (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 + 2 * h)}
    (nuP : ContinuousMonoidHom ((DM α h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((mCorePresentation α h hα).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1),
      nuP ((mCorePresentation α h hα).mark (.wild j)) = 1)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (mCompactW α h))
      (2 + 2 * h) q (DM α h) nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) q
      (DM α h) nuP SN (Count.trivialSMulZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) SN
      (Count.trivialSMulZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (mCompactW α h))
      (2 + 2 * h) q (DM α h) nuP SN
      (tameOfSpec (2 + 2 * h) q (mCompactW α h) (mTameSpecializes α h q hq0 hqe))
      (mPro2 α h q hα hq0 hqe)
      (mCompat α h q hα hq0 hqe (mTameSpecializes α h q hq0 hqe) nuP hnuSigma hnuWild)
      (Count.trivialSMulZmodTwo _)) :
    WordCertificate (2 + 2 * h) q (mCompactW α h) (DM α h) (isProP_DM α h) nuP SN where
  tameSpecialization := mTameSpecializes α h q hq0 hqe
  coreRel := mCoreRel α h
  proTwoWord := fun G _ _ _ _ _ t => mProTwoWord α h hα G t
  pro2 := mPro2 α h q hα hq0 hqe
  ker_pro2 := ker_mPro2 α h q hα hq0 hqe
  hpro2 := mPro2_surjective α h q hα hq0 hqe
  compat := mCompat α h q hα hq0 hqe (mTameSpecializes α h q hq0 hqe) nuP hnuSigma hnuWild
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := Count.trivialSMulZmodTwo _
  contSMulZmod2 := Count.trivialContSMulZmodTwo _
  htriv := Count.trivialHtrivZmodTwo _
  exactLifting := exactLifting
  stokes := stokes
  scalar := scalar
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_mCompact _

end Certificate

/-! ## §5 The two `hsimp` fold-ins, compact-`M` row

Each frozen row carries a single per-simple-module Stokes-duality hypothesis `hsimp`
(`Certificates/M0.lean:833`), carried by all five closers and discharged by none; the owner's
ruling is that it stays an **explicit hypothesis binder**, never an axiom.  What AS3 owes is the
book-keeping: the two shapes the count lane's consumers actually ask for.

Both are one application of WM0-b's `mCompact_stokesDuality` at a different coefficient module,
and both are *derivations from `hsimp`*, not new assumptions. -/

section Hsimp

universe u

variable {C : Type*} [Group C] [Finite C] {α h q e : ℕ}

/-- **Fold-in (a): the `T`-payload**, in the shape `Count.hsepN_marking` / `hsep_field_goal_marking`
consume (`Count/Marking.lean:387,498` — the binder `hd : StokesDuality cM w (Additive ↥D.T)`).

`2`-torsion of `Additive ↥D.T` is a theorem (`Count.radT_add_self`), so the only inputs beyond
`hsimp` are the row's own gate-level relator values. -/
theorem mStokesDuality_T (t : Marking (2 + 2 * h) C) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h) = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (mCompactFam α h q e) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) [DistribMulAction C (Additive ↥D.T)] :
    StokesDuality ⇑t (mCompactFam α h q e) (Additive ↥D.T) :=
  mCompact_stokesDuality t hq he hrt hrw hsimp _
    (Count.radT_add_self D)

/-- **Fold-in (b): the `Vmod`-payload**, in the shape `Count/Marking.lean` §5 consumes
(`isRightSeparating_vmod_mCompactFam`'s binder
`hsd : IsSelfDualN n c (mCompactFam α h q (omega2Exp (vmodLevel DD))) DD.Vmod`).

Two steps: `hsimp` gives `StokesDuality` at `DD.Vmod` (whose `2`-torsion is `Count.Vmod_exp2`),
then CB-S's `isSelfDualN_of_stokesDuality` promotes it, at the degree bookkeeping
`Count.nCompact_degree` — which is the *alphabet's* degree lemma, shared by every rank-`(4+2h)`
row, not a compact-`N` fact. -/
theorem mIsSelfDualN_Vmod (t : Marking (2 + 2 * h) C) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h) = 1)
    (hsimp : ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (mCompactFam α h q e) V)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} (DD : DescData D) [DistribMulAction C DD.Vmod]
    (hr : ∀ k, FreeGroup.lift ⇑t (mCompactFam α h q e k) = 1) :
    IsSelfDualN (2 * h + 2) ⇑t (mCompactFam α h q e) DD.Vmod :=
  Count.isSelfDualN_of_stokesDuality (Count.nCompact_degree h)
    (mCompact_stokesDuality t hq he hrt hrw hsimp _ (Vmod_exp2 DD))
    hr (mCompact_isStokesEndpoint hq he)

end Hsimp

end MCompactCore

/-! ## §6 The `ℚ₂(√2)` row

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
      (Count.trivialSMulZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) SN
      (Count.trivialSMulZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) 2 word) (2 + 2 * 0) 2 core
      nuP SN (tameOfSpec (2 + 2 * 0) 2 word (mTameSpecializes 3 0 2 two_ne_zero even_two))
      (mPro2 3 0 2 alpha_valid two_ne_zero even_two)
      (mCompat 3 0 2 alpha_valid two_ne_zero even_two
        (mTameSpecializes 3 0 2 two_ne_zero even_two) nuP hnuSigma hnuWild)
      (Count.trivialSMulZmodTwo _)) :
    WordCertificate (2 + 2 * 0) 2 word core (isProP_DM 3 0) nuP SN :=
  mWordCertificate 3 0 2 alpha_valid two_ne_zero even_two nuP hnuSigma hnuWild exactLifting
    stokes scalar determinant

end Sqrt2

/-! ## §7 Packet Theorem 1.1 at `ℚ₂(√2)`

ASK's `candidate_equiv_galK_of_supply` at the `√2` row.  The `q`-side hypotheses `2 ≤ q_K` and
`Even q_K` are discharged inside it from B13's residue degree; the tame modulus enters through
the row pin `hqK : qOf K FF = q`, which the caller instantiates at `q = 2` for `√2`
(`ℚ₂(√2)/ℚ₂` is ramified, so `f = 1` and `q_K = 2`; §5's `qK_hyps`).

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
  `prop_3_4_three` conditions read through §1's dictionary;
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
      q core nuP (standardNumerics (2 + 2 * 0)) (Count.trivialSMulZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (Count.trivialSMulZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * 0) q word) (2 + 2 * 0)
      q core nuP (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q word
        (mTameSpecializes 3 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)))
      (mPro2 3 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF))
      (mCompat 3 0 q alpha_valid (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)
        (mTameSpecializes 3 0 q (hqK ▸ qOf_ne_zero K FF) (hqK ▸ even_qOf K FF)) nuP hnuSigma
        hnuWild)
      (Count.trivialSMulZmodTwo _))
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
