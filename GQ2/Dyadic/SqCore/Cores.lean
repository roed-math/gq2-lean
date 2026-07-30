/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.Cores
public import GQ2.Roe.ChiR

@[expose] public section

/-!
# The stabilized square-commutator core `D_sq`: word, presentation, characters

**Ticket SQ2** of the dyadic campaign (lane SQ), implementing the SQ1 design memo
`docs/dyadic/sq-design.md` §4.1.  At gate R2 the owner selected `L_sq`, the **stabilized
square-commutator** family, as the primary word candidate; its degree-`n = 2h+1` pro-2 core is
(memo §1.1, harness `~/claude/general_2adic/dyadic_search/families/q2.py:414`
`pro2_core_square_commutator`)

```
C_sq(h) = (x₀^σ)⁻¹ · x₀⁻³ · x₁² · [x₁, x₁^σ]  ·  ∏_{j=1}^{h} [x_{2j}, x_{2j+1}]
          └──────────────── the rank-3 core ────────────────┘  └── handle block ──┘
```

on `sqRank h = 3 + 2h` generators, with the repo conventions `x ^ g = g⁻¹xg` (`GQ2.conjP`) and
`[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`).

## The headline of the lane

The rank-3 core **is** `GQ2.drWord` (`GQ2/Roe/DRPresentation.lean:83`), the core of the frozen
Roe development's `D_R`, *letter for letter* — same four factors, same order, same conventions
(memo §1.2, V1).  So `sqWord_eq_drWord` holds **by `rfl`**, `sqRelator_zero : sqRelator 0 =
drRelator`, and `dsq_zero : DSq 0 = DR`.  Every rank-3 datum of the `L_sq` core — the Hensel
orientation `Z³+2Z²+1`, the frame `ℤ/2·t ⊕ ℤ₂σ̄ ⊕ ℤ₂x̄₀`, the cup Gram
`[[0,1,0],[1,0,0],[0,0,1]]`, the full `ℤ₂` unramified marking, and the Labute classification
instance `GQ2.Roe.Labute.bLab` — is therefore *cited*, not reproved; see
`GQ2/Dyadic/SqCore/Rank3.lean` (ticket SQ3) for the assembled rank-3 marked core.

## Contents

* **§1 The word shapes.**  `sqWord` (spelled to be *definitionally* `drWord`), the handle
  indices `sqHandleIdxU/V`, the full degree-`n` relator shape `sqRelWord` on a marking
  `Fin (sqRank h) → G`, naturality (`map_sqWord`, `map_sqRelWord`), and the abelian collapse
  `sqWord_comm : sqWord s x y = (x⁴)⁻¹y²` — i.e. the relation vector `ρ_sq = −4x̄₀ + 2x̄₁`
  (memo §1.3).
* **§2 The presented core `DSq h`.**  Built through MC2's *generic* presentation layer
  (`presPro2`, `presGen`, `presPro2_topGen`, `presPro2_hom_ext`, `presLiftHom`) — the same
  encoding `maxProPQuotient 2 (profinitePresentation {r})` that `GQ2/Roe/DRPresentation.lean`
  uses for `D_R`, which is exactly what makes §4's bridge an `rfl`.  Marked generators
  `sqGen`/`dsqSigma`/`dsqX0`/`dsqX1`, the relation `dsq_relation`, topological generation
  `dsq_topGen`, hom-extensionality `dsq_hom_ext`, universal property `sqLiftHom` and the
  dedicated generator-value simp lemma `sqLiftHom_gen`.
* **§3 The standard marking and the two characters.**  `sqMark` (three core values, `1` on
  every handle letter — MC2's `coreMark` pattern) with its five value lemmas and
  `sqRelWord_sqMark`; then

  ```
  χ_sq(σ, x₀, x₁) = (S, X, Y)          -- the Hensel-root values of `GQ2/Roe/ChiR.lean`
  ν_sq(σ, x₀, x₁) = (1, 0, 0)          -- packet normalisation, NO forced row
  ```

  h-generically, with `1`/`0` on every handle letter, and the eight generator-value lemmas.
* **§4 The bridge to `D_R`.**  `sqRelator_zero`, `dsq_zero : DSq 0 = DR`, and the
  consumer-facing equivalence `dsqEquivDR`.

## Rank parameterisation (deviation from the memo's `n`, recorded)

The memo writes `C_sq(h)` in degree `n = 2h+1` with `n + 2 = 3 + 2h` generators.  As in MC2
(`GQ2/Dyadic/MarkedCore/Cores.lean` §"Rank parameterisation") we carry the **handle count**
`h : ℕ` and set `sqRank h = 3 + 2h`, so the indices `0, 1, 2` never wrap and `Fin (sqRank h)`'s
numerals are available for every `h`.

## `χ_sq(σ) ≠ 1` — the `C_mark = 3` content (memo V5/V6, risk R1)

Unlike the collector and unlike `L_tw`, the marked letter `σ` of this core carries the **deep**
orientation value `χ_sq(σ) = S ≡ 13 (16)`, of infinite order (`chiSq_sigma` below;
`GQ2/Roe/OrientationRoot.lean:194`).  The S2.4 memo's blanket "`χ(σ) = 1` for type `L`" is
therefore false here, and the χ-trivial subspace of the `L_sq` frame is a rank-1 free
`ℤ₂`-module *transverse* to `σ̄` rather than `⟨σ̄⟩` — recorded for MC5's handle analysis
(sq-design.md §7.1 R1, §7.4(1)), not patched in this lane.

## Axiom hygiene

Everything in this file prints at **std-3** (`propext`, `Classical.choice`, `Quot.sound`): no
census axiom is reachable from the h-generic layer, so MC5 can consume `chiSq`/`nuSq` without
dragging B3c/B8 into the rank-four lane (memo §5.3).  The census axioms enter only in SQ3's
discharge chain.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The word shape -/

section Words

variable {G : Type*} [Group G]

/-- **The square-commutator core word shape** `(x₀^σ)⁻¹ · x₀⁻³ · x₁² · [x₁, x₁^σ]` (memo §1.1,
harness `q2.py:414`), as a word in any group with the repo conventions `x ^ g = g⁻¹xg`
(`conjP`) and `[x,y] = x⁻¹y⁻¹xy` (`commP`).

Spelled to be **definitionally** `GQ2.drWord` (`GQ2/Roe/DRPresentation.lean:83`): the
identification of this core with the core of the frozen `D_R` is the whole point of the lane
(memo V1), and `sqWord_eq_drWord` records it by `rfl`. -/
def sqWord (s x y : G) : G := (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)

/-- **The identification** (memo §1.2, V1): the `L_sq` rank-3 core word *is* the frozen
`drWord`, letter for letter — factor by factor `Inverse(Conjugate(X0, SIGMA))`, `X0^{-3}`,
`X1^2`, `Commutator(X1, Conjugate(X1, SIGMA))` against `(conjP x s)⁻¹`, `(x ^ 3)⁻¹`, `y ^ 2`,
`commP y (conjP y s)`. -/
theorem sqWord_eq_drWord (s x y : G) : sqWord s x y = drWord s x y := rfl

end Words

/-! ### The generator index type

`sqRank h = 3 + 2h` is the memo's `n + 2` at `n = 2h + 1`: three core letters `σ, x₀, x₁`
followed by `h` handle pairs `(x_{2j}, x_{2j+1})` at indices `(3 + 2j, 4 + 2j)`. -/

/-- The rank of the degree-`n = 2h+1` square-commutator core: the memo's `n + 2 = 3 + 2h`. -/
def sqRank (h : ℕ) : ℕ := 3 + 2 * h

instance instNeZeroSqRank (h : ℕ) : NeZero (sqRank h) := ⟨by simp [sqRank]⟩

@[simp] theorem sqRank_zero : sqRank 0 = 3 := rfl

/-- The first letter of the `j`-th handle pair: index `3 + 2j`. -/
def sqHandleIdxU {h : ℕ} (j : Fin h) : Fin (sqRank h) :=
  ⟨3 + 2 * j, by have := j.isLt; simp only [sqRank]; omega⟩

/-- The second letter of the `j`-th handle pair: index `4 + 2j`. -/
def sqHandleIdxV {h : ℕ} (j : Fin h) : Fin (sqRank h) :=
  ⟨4 + 2 * j, by have := j.isLt; simp only [sqRank]; omega⟩

section RelWord

variable {G : Type*} [Group G] {h : ℕ}

/-- **The full degree-`n` relator shape**: the core word on `σ, x₀, x₁` times the `h`
hyperbolic handles `∏_{j<h}[x_{3+2j}, x_{4+2j}]` (MC2's `handleWord`). -/
def sqRelWord (m : Fin (sqRank h) → G) : G :=
  sqWord (m 0) (m 1) (m 2) *
    handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))

/-- At `h = 0` the relator shape is the bare rank-3 core word. -/
theorem sqRelWord_zero (m : Fin (sqRank 0) → G) : sqRelWord m = sqWord (m 0) (m 1) (m 2) := by
  rw [sqRelWord, handleWord_zero, mul_one]

end RelWord

/-! ### Naturality -/

section Naturality

variable {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]

/-- Naturality of the core word (the `map_drWord` clone, and literally that theorem). -/
theorem map_sqWord (φ : F) (s x y : G) : φ (sqWord s x y) = sqWord (φ s) (φ x) (φ y) :=
  map_drWord φ s x y

/-- Naturality of the full relator shape (the `map_mRelWord` clone). -/
theorem map_sqRelWord {h : ℕ} (φ : F) (m : Fin (sqRank h) → G) :
    φ (sqRelWord m) = sqRelWord (fun i => φ (m i)) := by
  rw [sqRelWord, map_mul, map_sqWord, map_handleWord, sqRelWord]

end Naturality

/-! ### Abelian collapse

Both commutators die, and the surviving relation vector is `ρ_sq = −4x̄₀ + 2x̄₁` (memo §1.3;
the frozen `drWord_comm`, `GQ2/Roe/DRPresentation.lean:97`).  Smith normal form over `ℤ₂` then
gives the frame `ℤ/2·t ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₀` with `t = x̄₁ − 2x̄₀`; see `SqDecomposition` in
`GQ2/Dyadic/SqCore/Rank3.lean`. -/

section Abelian

variable {G : Type*} [CommGroup G] {h : ℕ}

/-- **Abelian collapse of the core word**: `ρ_sq = −4x̄₀ + 2x̄₁`. -/
theorem sqWord_comm (s x y : G) : sqWord s x y = (x ^ 4)⁻¹ * y ^ 2 := drWord_comm s x y

/-- **Abelian collapse of the full relator**: the handles contribute nothing. -/
theorem sqRelWord_comm (m : Fin (sqRank h) → G) :
    sqRelWord m = ((m 1) ^ 4)⁻¹ * (m 2) ^ 2 := by
  rw [sqRelWord, sqWord_comm, handleWord_comm, mul_one]

end Abelian

/-! ## §2 The presented core `D_sq`

Built through MC2's **generic** presentation layer (`GQ2/Dyadic/MarkedCore/Cores.lean` §3.1):
`presPro2 r = maxProPQuotient 2 (profinitePresentation {r})` is the *same* encoding as
`DR = maxProPQuotient 2 DRFull`, which is what makes §4's bridge definitional. -/

/-- The relator of the degree-`n = 2h+1` square-commutator core, as a word in the free
profinite group on `Fin (sqRank h)`. -/
noncomputable def sqRelator (h : ℕ) : FreeProfiniteGroup (Fin (sqRank h)) :=
  sqRelWord fun i => FreeProfiniteGroup.of i

/-- **`D_{sq,h}`**: the pro-2 group `⟨σ, x₀, x₁, x₂, …, x_{2h+1} | C_sq(h)⟩` of rank
`sqRank h = 3 + 2h` (the memo's `n + 2`). -/
noncomputable def DSq (h : ℕ) : ProfiniteGrp := presPro2 (sqRelator h)

/-- The marked generators of `D_sq`. -/
noncomputable def sqGen (h : ℕ) (i : Fin (sqRank h)) : DSq h := presGen (sqRelator h) i

/-- The marked letter `σ` (index `0`). -/
noncomputable def dsqSigma (h : ℕ) : DSq h := sqGen h 0

/-- The wild letter `x₀` (index `1`). -/
noncomputable def dsqX0 (h : ℕ) : DSq h := sqGen h 1

/-- The wild letter `x₁` (index `2`). -/
noncomputable def dsqX1 (h : ℕ) : DSq h := sqGen h 2

/-- `D_sq` is pro-2. -/
theorem isProP_DSq (h : ℕ) : IsProP 2 (DSq h : Type) := isProP_presPro2 _

/-- The relator already dies in the *full* profinite presentation. -/
private theorem sqFull_relation (h : ℕ) :
    sqRelWord (fun i => quotientMk (relatorSubgroup {sqRelator h})
      (FreeProfiniteGroup.of i)) = 1 := by
  have hr := relator_quotientMk_eq_one {sqRelator h} rfl
  rw [sqRelator, map_sqRelWord] at hr
  exact hr

/-- **The relation holds in `D_sq`.** -/
theorem dsq_relation (h : ℕ) : sqRelWord (sqGen h) = 1 := by
  have key := map_sqRelWord (maxProPMk 2 (profinitePresentation {sqRelator h}))
    (fun i => quotientMk (relatorSubgroup {sqRelator h}) (FreeProfiniteGroup.of i))
  rw [sqFull_relation, map_one] at key
  exact key.symm

/-- **Topological generation of `D_sq`** (the `dr_topGen`/`dm_topGen` pattern). -/
theorem dsq_topGen (h : ℕ) :
    (Subgroup.closure (Set.range (sqGen h))).topologicalClosure = ⊤ :=
  presPro2_topGen _

/-- **Hom-extensionality for `D_sq`** (the `dr_hom_ext`/`dm_hom_ext` pattern). -/
theorem dsq_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    {h : ℕ} (φ ψ : ContinuousMonoidHom (DSq h : Type) A)
    (hgen : ∀ i, φ (sqGen h i) = ψ (sqGen h i)) : φ = ψ :=
  presPro2_hom_ext _ φ ψ hgen

section Lifts

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `D_sq`** (MC2's `mLiftHom` clone through the generic
`presLiftHom`): a marking of a pro-2 group killing the relator word classifies a continuous
hom `D_sq → H`. -/
noncomputable def sqLiftHom (h : ℕ) (hH : IsProP 2 H) (m : Fin (sqRank h) → H)
    (hrel : sqRelWord m = 1) : ContinuousMonoidHom (DSq h : Type) H :=
  presLiftHom (sqRelator h) hH m (by
    have hm : (fun i => (freeHomFin m) (FreeProfiniteGroup.of i)) = m :=
      funext (freeHomFin_of m)
    rw [sqRelator, map_sqRelWord, hm]
    exact hrel)

/-- The dedicated generator-value simp lemma.  **Required** (memo §5.2 finding 1): `rw [chiSq]`
cannot rewrite under the `ContinuousMonoidHom` coercion, so the eight value lemmas of §3 go
through this wrapper and `Eq.trans`, exactly as MC2's `mLiftHom_gen` does. -/
@[simp] theorem sqLiftHom_gen (h : ℕ) (hH : IsProP 2 H) (m : Fin (sqRank h) → H)
    (hrel : sqRelWord m = 1) (i : Fin (sqRank h)) :
    sqLiftHom h hH m hrel (sqGen h i) = m i := presLiftHom_gen _ _ _ _ _

end Lifts

/-! ## §3 The standard marking, and the characters `χ_sq`, `ν_sq` -/

/-! ### Index arithmetic for `Fin (sqRank h)` -/

theorem sqVal_zero (h : ℕ) : ((0 : Fin (sqRank h)) : ℕ) = 0 := by
  show 0 % sqRank h = 0
  exact Nat.zero_mod _

theorem sqVal_one (h : ℕ) : ((1 : Fin (sqRank h)) : ℕ) = 1 := by
  show 1 % sqRank h = 1
  exact Nat.mod_eq_of_lt (by simp only [sqRank]; omega)

theorem sqVal_two (h : ℕ) : ((2 : Fin (sqRank h)) : ℕ) = 2 := by
  show 2 % sqRank h = 2
  exact Nat.mod_eq_of_lt (by simp only [sqRank]; omega)

theorem sqHandleIdxU_val {h : ℕ} (j : Fin h) :
    ((sqHandleIdxU j : Fin (sqRank h)) : ℕ) = 3 + 2 * j := rfl

theorem sqHandleIdxV_val {h : ℕ} (j : Fin h) :
    ((sqHandleIdxV j : Fin (sqRank h)) : ℕ) = 4 + 2 * j := rfl

/-- **The standard marking shape**: three core values, `1` on every handle letter (MC2's
`coreMark` pattern).  Every character of this core built below has this shape — the handle
lemma `commP_wordLift_one`/`handleWord_wordLift_one` forces `χ ≡ 1` there. -/
def sqMark {G : Type*} [Group G] {h : ℕ} (a b c : G) : Fin (sqRank h) → G :=
  fun i =>
    if (i : ℕ) = 0 then a else
    if (i : ℕ) = 1 then b else
    if (i : ℕ) = 2 then c else 1

section SqMark

variable {G : Type*} [Group G] {h : ℕ} (a b c : G)

@[simp] theorem sqMark_zero : (sqMark (h := h) a b c) 0 = a := by
  simp only [sqMark, sqVal_zero]
  norm_num

@[simp] theorem sqMark_one : (sqMark (h := h) a b c) 1 = b := by
  simp only [sqMark, sqVal_one]
  norm_num

@[simp] theorem sqMark_two : (sqMark (h := h) a b c) 2 = c := by
  simp only [sqMark, sqVal_two]
  norm_num

@[simp] theorem sqMark_handleU (j : Fin h) : sqMark a b c (sqHandleIdxU j) = 1 := by
  simp only [sqMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem sqMark_handleV (j : Fin h) : sqMark a b c (sqHandleIdxV j) = 1 := by
  simp only [sqMark, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The full relator on a standard marking is the bare core word: the handles are trivial. -/
theorem sqRelWord_sqMark : sqRelWord (sqMark (h := h) a b c) = sqWord a b c := by
  rw [sqRelWord, sqMark_zero, sqMark_one, sqMark_two,
    handleWord_of_one _ _ (fun j => sqMark_handleU a b c j)
      (fun j => sqMark_handleV a b c j), mul_one]

end SqMark

/-! ### The canonical orientation `χ_sq`

The `C_mark = 3` coordinate (memo §1.4), h-generically.  The three core values are the
**Hensel-root** orientation data of `GQ2/Roe/ChiR.lean` — `X` the unique root of `Z³+2Z²+1` in
`ℤ₂` (`rootXUnit`), `S·(X²+X+1) = −X³` (`SvalUnit`), `Y = −X²` (`YvalUnit`), with
`X ≡ 5`, `S ≡ 13`, `Y ≡ 7 (16)`.  No closed form exists: the cubic is irreducible over `ℚ`. -/

/-- **`χ_sq : D_sq → ℤ₂ˣ`**, the canonical Labute orientation of the square-commutator core:
generator values `(σ, x₀, x₁) ↦ (S, X, Y)` and `1` on every handle letter.  The relator dies by
the abelian collapse `(X⁴)⁻¹Y² = 1`, i.e. the character relation `Y² = X⁴`
(`GQ2.Roe.YvalUnit_sq_eq`). -/
noncomputable def chiSq (h : ℕ) : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
  sqLiftHom h isProP_two_unitsPadicInt (sqMark SvalUnit rootXUnit YvalUnit) (by
    rw [sqRelWord_sqMark]
    show drWord SvalUnit rootXUnit YvalUnit = 1
    rw [drWord_comm, YvalUnit_sq_eq, inv_mul_cancel])

/-- **`ν_sq : D_sq → ℤ₂`**, the **full `ℤ₂`-valued** unramified marking: packet normalisation
`ν(σ) = 1`, `ν(x_i) = 0`, and — unlike `ν_M` — **no forced row**, since the abelianized relation
`−4x̄₀ + 2x̄₁ = 0` involves only wild letters (memo §1.5).  Merge gate 6 ("mod-2 is not enough")
is therefore met at rank 3 without further work.

Target `Multiplicative ℤ_[2]`, to which the packet's `Ztwo` is continuously isomorphic by
`ztwoEquivPadic` (`GQ2/ZtwoPowering.lean:302`) — the same target MC2 adopted for `ν_M`/`ν_N`. -/
noncomputable def nuSq (h : ℕ) : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt
    (sqMark (ofAdd (1 : ℤ_[2])) (ofAdd 0) (ofAdd 0)) (by
      rw [sqRelWord_sqMark]
      show sqWord (ofAdd (1 : ℤ_[2])) (ofAdd 0) (ofAdd 0) = 1
      rw [sqWord_comm]
      simp)

/-- `χ_sq(σ) = S`, the deep Hensel value — **not `1`** (memo V5/V6, risk R1). -/
@[simp] theorem chiSq_sigma (h : ℕ) : chiSq h (dsqSigma h) = SvalUnit :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqMark_zero _ _ _)

/-- `χ_sq(x₀) = X`, the Hensel root of `Z³+2Z²+1`. -/
@[simp] theorem chiSq_x0 (h : ℕ) : chiSq h (dsqX0 h) = rootXUnit :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqMark_one _ _ _)

/-- `χ_sq(x₁) = Y = −X²`. -/
@[simp] theorem chiSq_x1 (h : ℕ) : chiSq h (dsqX1 h) = YvalUnit :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqMark_two _ _ _)

/-- `χ_sq ≡ 1` on the first letter of every handle pair (S2.4 §1.1, and forced by the handle
lemma). -/
@[simp] theorem chiSq_handleU (h : ℕ) (j : Fin h) :
    chiSq h (sqGen h (sqHandleIdxU j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleU _ _ _ j)

/-- `χ_sq ≡ 1` on the second letter of every handle pair. -/
@[simp] theorem chiSq_handleV (h : ℕ) (j : Fin h) :
    chiSq h (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleV _ _ _ j)

/-- `ν_sq(σ) = 1`: the packet normalisation of the marked letter. -/
@[simp] theorem nuSq_sigma (h : ℕ) : nuSq h (dsqSigma h) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqMark_zero _ _ _)

/-- `ν_sq(x₀) = 0`. -/
@[simp] theorem nuSq_x0 (h : ℕ) : nuSq h (dsqX0 h) = ofAdd (0 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqMark_one _ _ _)

/-- `ν_sq(x₁) = 0`.  With `ν_sq(x₀) = 0` this is the *free* consistency check on the frame's
torsion generator: `ν(t) = ν(x̄₁) − 2ν(x̄₀) = 0`, as it must be (`t` is torsion, `ℤ₂` is
torsion-free) — and it needs no forced row. -/
@[simp] theorem nuSq_x1 (h : ℕ) : nuSq h (dsqX1 h) = ofAdd (0 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqMark_two _ _ _)

/-- `ν_sq ≡ 0` on the first letter of every handle pair. -/
@[simp] theorem nuSq_handleU (h : ℕ) (j : Fin h) :
    nuSq h (sqGen h (sqHandleIdxU j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleU _ _ _ j)

/-- `ν_sq ≡ 0` on the second letter of every handle pair. -/
@[simp] theorem nuSq_handleV (h : ℕ) (j : Fin h) :
    nuSq h (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleV _ _ _ j)

/-! ## §4 The bridge: at `h = 0` the presented core **is** `D_R`

The punchline of the lane (memo V1, §1.2, spike clauses (b1)–(b4)).  `presPro2` and `DR` are
the same encoding of a one-relator pro-2 group, and by §1 the relators are equal, so the two
`ProfiniteGrp`s are *equal*, not merely isomorphic.

**Consumer guidance** (memo risk R3): `dsq_zero` is an `Eq` of `ProfiniteGrp`, so transporting
along it needs `▸`/`cast`.  Use **`dsqEquivDR`** instead — it is the only sanctioned
consumer-facing form, and it confines the `cast` to this one declaration.  Accordingly SQ3
states every rank-3 fact directly about the frozen `DR` names. -/

/-- At `h = 0` the relator **is** the frozen `drRelator` (`GQ2/Roe/DRPresentation.lean`). -/
theorem sqRelator_zero : sqRelator 0 = drRelator := by
  rw [sqRelator, sqRelWord_zero]; rfl

/-- **`DSq 0 = DR`**: the `L_sq` rank-3 presented pro-2 core is the frozen Roe core.

Proof note (memo §5.2 finding 2): the rewrite must stop at `sqRelator_zero` and finish by
`rfl`.  Continuing with `rw [presPro2, DR, DRFull]` fails — "Failed to rewrite using equation
theorems for `DRFull`", `DRFull` being a `noncomputable def` in a `module` file. -/
theorem dsq_zero : DSq 0 = DR := by
  rw [DSq, sqRelator_zero]; rfl

/-- The underlying types agree, so every `D_R` fact transports. -/
theorem dsq_zero_type : (DSq 0 : Type) = (DR : Type) := by rw [dsq_zero]

/-- **The MC5-facing equivalence `D_sq(0) ≅ D_R`** — the *only* sanctioned consumer-facing form
of `dsq_zero` (memo risk R3(i)). -/
noncomputable def dsqEquivDR : ContinuousMulEquiv (DSq 0 : Type) (DR : Type) :=
  dsq_zero ▸ ContinuousMulEquiv.refl _

end SqCore

end Dyadic

end GQ2
