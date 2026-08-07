/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.ArbFrames

/-!
# W46 — the marking builder, and the handle-commutator form of the one-handle equation

Two things.  §1 removes the `h = 1` restriction from `ArbFrames` §6 by building the missing
marking; §3 rewrites the surviving word equation as a **commutator equation**, and §4 records
what the class-two balance says about it.

## Headline 1 — the clearing scheme *is* the residual, at every `h`

`ArbFrames` §6 could only state `sqClearingStep_one_iff` at one handle, because the converse
`SqLamMarkTransitivity h → SqClearingStep h` needs a marking with **one handle zeroed** and the
rest left alone, and no builder for such a marking existed.  §1 builds it:

```text
sqNuRows h ρ  : the marking with core rows (1, 0, 0) and handle rows read off ρ
sqNuClear h ν' j = sqNuRows h (ν'-rows, with handle j set to 0)
```

The relator dies for *any* `ρ` — the abelian collapse of `sqRelWord` is `(m₁⁴)⁻¹m₂²`, which the
core rows `(ν(x₀), ν(x₁)) = (0, 0)` kill outright, and the handle letters never enter it.  So the
handle rows of a marking are **completely free**, and the converse is two applications of
transitivity composed:

```text
sqClearingStep_iff             : SqClearingStep h ↔ SqLamMarkTransitivity h
sqArbRelWord_iff_lamMarkTransitivity : SqArbRelWord h ↔ SqLamMarkTransitivity h
```

⭐ At every `h`, not just `h = 1`.  Combined with `ArbFrames`' `sqArbRelWord_iff_clearingStep`
this closes the loop: the arbitrary-dressing word equation, the clearing scheme and the residual
are one statement.

⭐ The builder is also **exhaustive**: `nu_eq_sqNuRows_of_selected` says every selected marking
*is* a row vector, so `sqLamMarkTransitivity_iff_rows` re-poses the residual as a statement about
`Fin (sqRank h) → ℤ₂` with no quantifier over abstract characters left.

## Headline 2 — the one-handle equation is a commutator equation

The frames of `SqClearingStep` need move only the two letters of the handle being cleared.  For
such a frame the relator identity is not a word equation at all — the core word and the other
handles cancel verbatim against `dsq_relation`, and what is left is

```text
sqRelWord (sqCommFrame h j p q) = 1  ↔  ⁅p, q⁆ = ⁅u_j, v_j⁆        (`sqRelWord_sqCommFrame_iff`)
```

an **exact** `iff`, at every `h` and every handle.  So the core-fixed part of the clearing scheme
is: *write the `j`-th handle commutator as a commutator of two elements of `ker λ ∩ ker ν'`*
(`SqHandleComm`, `sqClearingStep_of_handleComm`).  Rows are free (both letters lie in
`ker λ ∩ ker ν'` by hypothesis), and mod-2 independence is free as soon as the two letters differ
from the cleared letters `U`, `V` by elements of the Frattini set §2 — the set swallowed by every
index-two open normal subgroup, which by `ArbFrames` §1 contains every square and every
commutator.

## ⚠ Headline 3 — the core **must** move: the class-two obstruction to `SqHandleComm`

`SqHandleComm h` is *sufficient* (§3) but it is **not** satisfiable at a marking with an odd
handle row.  The computation is the class-two balance of `docs/dyadic/eichler-reduction-note.md`,
run for the frame that fixes the core.

⭐ **This whole headline is now machine-checked** in `SqCore/GradedTwo.lean` (W47).  The closed
form of the relator in a class-two test group is `SqHeis.sqRelWord_c` / `sqHeisDefect`, the gate
that turns the balance into a computation is `sqHeisBalance`, and the forcing of the `x₀`-slot
below is `sqArbFrame_x0_dressing_forced`.  Read the two ⚠ notes there before reusing the prose
here: the realizability parity (which is why the gate runs over `ℤ/4` and not `ℤ/2`) and the
`x₁ = x₀²` gauge (see the ⚠ at the end of the ⭐ paragraph below).

Write `A = D_sq(h)^ab`; the plain lower central series has

```text
gr₂ = γ₂/γ₃ ≅ Λ²A          (A = ℤ₂σ̄ ⊕ ℤ₂x̄₀ ⊕ (ℤ/2)t̄ ⊕ ⊕ⱼ(ℤ₂ūⱼ ⊕ ℤ₂v̄ⱼ), t̄ = x̄₁ − 2x̄₀)
```

— the relator's abelian vector `−4x̄₀ + 2x̄₁` contributes only the relations `r ∧ A`, and
`Λ²(F^ab)/(r ∧ F^ab) = Λ²A`.  Now `K := ker λ ∩ ker ν'` inside `A` is spanned by the cleared
classes `Ū = ū_j − t·w̄`, `V̄ = v̄_j − s·w̄` (`t = ν'(u_j)`, `s = ν'(v_j)`, `w̄ = σ̄ − c₀x̄₀` the
pivot), the other handles and `t̄`; and `(λ, ν')` is **unimodular** on the complement
`P = ⟨w̄, x̄₀⟩` — its matrix is `!![0, 1; 1, 0]` — so `A = K ⊕ P` and `Λ²K ↪ Λ²A` is a direct
summand.  For `p, q ∈ ker λ ∩ ker ν'` the class-two term of `⁅p,q⁆` is `p̄ ∧ q̄ ∈ Λ²K`, while

```text
ū_j ∧ v̄_j = Ū ∧ V̄ + s·(Ū ∧ w̄) − t·(V̄ ∧ w̄) ,
```

whose `K ⊗ P`-component is `s·(Ū ∧ w̄) − t·(V̄ ∧ w̄)`.  Hence `⁅p,q⁆ = ⁅u_j,v_j⁆` forces
**`s = t = 0`**: the handle was already clear.  ⚠ So `SqHandleComm h` is false for `h ≥ 1`, and
§3's reduction has a false hypothesis — exactly like `LamFrames`' `SqEichRelWord`.  It is kept
because the `iff` is the honest statement of what a core-fixing frame must do, and because the
obstruction says precisely what a *working* frame must do instead.

⭐ **What the same computation says about the general frame.**  Dress the slots as `ArbFrames`
does, `m i = base i · a i` with `a i ∈ ker λ ∩ ker ν'`.  The class-two defect of the undressed
frame is `Δ₀ = −s·(Ū ∧ w̄) + t·(V̄ ∧ w̄)`, in `K ⊗ P`, and the only dressing that reaches the
`w̄`-column of `K ⊗ P` is the one on the **`x₀`-slot**: it enters through `⁅x₀a₁, σa₀⁆⁻¹`, whose
class-two term contains `−ā₁ ∧ σ̄ = −ā₁ ∧ w̄ − c₀·ā₁ ∧ x̄₀`, while `ā₀` pairs only against `x̄₀`
and `ā₃`, `ā₄` land in `Λ²K`.  Balancing the `w̄`-column gives

```text
ā₁ = −s·Ū + t·V̄        (up to the overall sign of the ⁅·,·⁆⁻¹ convention; ⟨w̄⟩ ∩ K = 0)
```

— a **forced, non-zero** value, and the remaining columns (`x̄₀` against `K`, and `Λ²K`) are then
free in `ā₀` and in `(ā₃, ā₄)`.  That is the sense in which the class-two balance is now
under-determined: it fixes one dressing and leaves three.

⚠ **Read "one of four forced, three free" as "in the `x₁ = x₀²` gauge".**  The frame has *five*
slots; the abelian row only gives `ā₂ = 2ā₁ + τ` with `2τ = 0`, and when `τ = t̄` the square
`(a₂a₁⁻²)²` contributes `−Δ₀` to the very same `w̄`-column, leaving a second branch `ā₁ = 0`.
The forcing as displayed holds exactly when `a₂ = a₁²` — which every Eichler family satisfies,
its `x₁`-slot weight being literally `2e'`.  This is `sqArbFrame_x0_dressing_forced` and the ⚠
gauge note in `SqCore/GradedTwo.lean` §6.

⚠ Note what the forced value is:
the `x₀`-slot must be dressed by the **handle** letters `U^{−s}V^{t}`, not the handles by the
core.  Every refuted family dressed only *with* `U` and `V` and so could meet this (the two-letter
family `sqEichFrameUV` does, at `(f', e') = (−s, t)`); the `V`-power families of `LamFrames` §2
and §5 cannot, which re-derives their class-two rigidity from the balance rather than from a
homomorphism.

⚠ **Index convention when reading the source note.**  `docs/dyadic/eichler-reduction-note.md` is
the source for the class-two balance, and its "class-two balance (do not re-derive)" section is
correct — with the dictionary that its `a₀` is the **`x₀`**-slot weight and its `a₁` the
`σ`-slot weight (it indexes a dressing by the *letter's* subscript, `ArbFrames` by the *slot's*
position), so its forced `a₀ = −k` is exactly the `ā₁` forcing above.  Its final section, "The
residual search", used to recommend the two-slot `(σ, u)` scaffold and a word-level
`SqEichlerSeed`; both are refuted, by this balance and by `SqCore/EichRefutation.lean`.  That
section has since been rewritten (2026-08-07) to point at `SqArbRelWord h`, and the note now
carries both warnings itself.

## Contents

* **§1** `sqRowMark`, `sqNuRows`, `sqNuClear`, `sqClearingStep_iff` at every `h`, and the row
  classification `nu_eq_sqNuRows_of_selected` / `sqLamMarkTransitivity_iff_rows`;
* **§2** `SqFrattini`, the set swallowed by every index-two open normal subgroup;
* **§3** `sqCommFrame`, `sqRelWord_sqCommFrame_iff`, `SqHandleComm` and its clearing step;
* **§4** stress pins, **§5** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The marking builder

A marking of `D_sq h` is a tuple killing `sqRelWord`, and in an abelian target the relator
collapses to `(m₁⁴)⁻¹·m₂²` (`sqRelWord_comm`): the handle letters do not appear.  So the handle
rows of a `ℤ₂`-marking are **unconstrained**, and prescribing them is a definition rather than a
theorem. -/

section MarkingBuilder

variable {h : ℕ} {rho : Fin (sqRank h) → ℤ_[2]}

variable (h rho) in
/-- **The mark with prescribed handle rows**: core rows `(1, 0, 0)` and the `i`-th handle row
`ρ i`.  `sqMark (ofAdd 1) (ofAdd 0) (ofAdd 0)` is the case `ρ = 0`. -/
noncomputable def sqRowMark : Fin (sqRank h) → Multiplicative ℤ_[2] :=
  fun i =>
    if (i : ℕ) = 0 then ofAdd (1 : ℤ_[2]) else
    if (i : ℕ) = 1 then ofAdd (0 : ℤ_[2]) else
    if (i : ℕ) = 2 then ofAdd (0 : ℤ_[2]) else ofAdd (rho i)

@[simp] theorem sqRowMark_zero : sqRowMark h rho 0 = ofAdd (1 : ℤ_[2]) := by
  simp only [sqRowMark, sqVal_zero]
  norm_num

@[simp] theorem sqRowMark_one : sqRowMark h rho 1 = ofAdd (0 : ℤ_[2]) := by
  simp only [sqRowMark, sqVal_one]
  norm_num

@[simp] theorem sqRowMark_two : sqRowMark h rho 2 = ofAdd (0 : ℤ_[2]) := by
  simp only [sqRowMark, sqVal_two]
  norm_num

/-- Off the three core indices the mark is the prescribed row. -/
theorem sqRowMark_of_three {i : Fin (sqRank h)} (hi : 3 ≤ (i : ℕ)) :
    sqRowMark h rho i = ofAdd (rho i) := by
  simp only [sqRowMark]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The relator dies for every row vector.**  The abelian collapse is `(m₁⁴)⁻¹m₂²`, and both
core rows are `0`. -/
theorem sqRelWord_sqRowMark : sqRelWord (sqRowMark h rho) = 1 := by
  rw [sqRelWord_comm, sqRowMark_one, sqRowMark_two]
  simp

variable (h rho) in
/-- **The marking with prescribed handle rows** `ρ`, and the P3-selected core rows. -/
noncomputable def sqNuRows : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt (sqRowMark h rho) sqRelWord_sqRowMark

@[simp] theorem sqNuRows_sigma : sqNuRows h rho (dsqSigma h) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 0).trans sqRowMark_zero

@[simp] theorem sqNuRows_x0 : sqNuRows h rho (dsqX0 h) = ofAdd (0 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 1).trans sqRowMark_one

@[simp] theorem sqNuRows_x1 : sqNuRows h rho (dsqX1 h) = ofAdd (0 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 2).trans sqRowMark_two

theorem sqNuRows_gen_of_three {i : Fin (sqRank h)} (hi : 3 ≤ (i : ℕ)) :
    sqNuRows h rho (sqGen h i) = ofAdd (rho i) :=
  (sqLiftHom_gen _ _ _ _ i).trans (sqRowMark_of_three hi)

@[simp] theorem sqNuRows_handleU (j : Fin h) :
    sqNuRows h rho (sqGen h (sqHandleIdxU j)) = ofAdd (rho (sqHandleIdxU j)) :=
  sqNuRows_gen_of_three (by rw [sqHandleIdxU_val]; omega)

@[simp] theorem sqNuRows_handleV (j : Fin h) :
    sqNuRows h rho (sqGen h (sqHandleIdxV j)) = ofAdd (rho (sqHandleIdxV j)) :=
  sqNuRows_gen_of_three (by rw [sqHandleIdxV_val]; omega)

variable (h) in
/-- The row vector of `ν'` with the `j`-th handle's two rows replaced by `0`. -/
noncomputable def sqClearRows (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h) : Fin (sqRank h) → ℤ_[2] :=
  fun i =>
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then 0 else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then 0 else toAdd (nu' (sqGen h i))

variable (h) in
/-- ⭐ **The marking-builder**: `ν'` with handle `j` cleared and every other row untouched.
This is the marking `SqClearingStep` asks a clearing automorphism to produce, and its existence
is what `ArbFrames` §6 was missing at `h ≥ 2`. -/
noncomputable def sqNuClear (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h) : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqNuRows h (sqClearRows h nu' j)

variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

@[simp] theorem sqNuClear_sigma : sqNuClear h nu' j (dsqSigma h) = ofAdd (1 : ℤ_[2]) :=
  sqNuRows_sigma

@[simp] theorem sqNuClear_x0 : sqNuClear h nu' j (dsqX0 h) = ofAdd (0 : ℤ_[2]) :=
  sqNuRows_x0

@[simp] theorem sqNuClear_handleU_self :
    sqNuClear h nu' j (sqGen h (sqHandleIdxU j)) = 1 := by
  rw [sqNuClear, sqNuRows_handleU]
  simp only [sqClearRows]
  exact ofAdd_zero

@[simp] theorem sqNuClear_handleV_self :
    sqNuClear h nu' j (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [sqNuClear, sqNuRows_handleV]
  simp [sqClearRows, sqHandleIdxU_val, sqHandleIdxV_val]

theorem sqNuClear_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sqNuClear h nu' j (sqGen h (sqHandleIdxU j')) = nu' (sqGen h (sqHandleIdxU j')) := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  rw [sqNuClear, sqNuRows_handleU]
  simp only [sqClearRows, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), ofAdd_toAdd]

theorem sqNuClear_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sqNuClear h nu' j (sqGen h (sqHandleIdxV j')) = nu' (sqGen h (sqHandleIdxV j')) := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  rw [sqNuClear, sqNuRows_handleV]
  simp only [sqClearRows, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), ofAdd_toAdd]

/-- ⭐ **The converse of `sqLamMarkTransitivity_of_clearingStep`, at every `h`.**  Correct `ν'`
onto `ν_sq` and correct the one-handle-cleared marking `sqNuClear h ν' j` onto `ν_sq` too; the
composite `Ψ₁ ∘ Ψ₂⁻¹` carries `ν'` onto `sqNuClear h ν' j`, which is exactly the five clauses of a
clearing step. -/
theorem sqClearingStep_of_lamMarkTransitivity (H : SqLamMarkTransitivity h) :
    SqClearingStep h := by
  intro nu' j hsigma hx0
  obtain ⟨Ψ₁, hlam₁, hval₁⟩ := H nu' hsigma hx0
  obtain ⟨Ψ₂, hlam₂, hval₂⟩ := H (sqNuClear h nu' j) sqNuClear_sigma sqNuClear_x0
  have hkey : ∀ x, nu' (Ψ₁ (Ψ₂.symm x)) = sqNuClear h nu' j x := by
    intro x
    rw [hval₁]
    have := hval₂ (Ψ₂.symm x)
    rw [Ψ₂.apply_symm_apply] at this
    exact this.symm
  have hlam : ∀ x, nuLam h (Ψ₁ (Ψ₂.symm x)) = nuLam h x := by
    intro x
    rw [hlam₁]
    have := hlam₂ (Ψ₂.symm x)
    rw [Ψ₂.apply_symm_apply] at this
    exact this.symm
  refine ⟨Ψ₂.symm.trans Ψ₁, hlam, ?_, ?_, ?_, ?_, fun j' hjj => ⟨?_, ?_⟩⟩
  · exact (hkey _).trans sqNuClear_sigma
  · exact (hkey _).trans sqNuClear_x0
  · exact (hkey _).trans sqNuClear_handleU_self
  · exact (hkey _).trans sqNuClear_handleV_self
  · exact (hkey _).trans (sqNuClear_handleU_ne hjj)
  · exact (hkey _).trans (sqNuClear_handleV_ne hjj)

/-- ⭐⭐ **The clearing scheme is the residual, at every handle count.**  `ArbFrames`'
`sqClearingStep_one_iff` is the case `h = 1`. -/
theorem sqClearingStep_iff : SqClearingStep h ↔ SqLamMarkTransitivity h :=
  ⟨sqLamMarkTransitivity_of_clearingStep, sqClearingStep_of_lamMarkTransitivity⟩

/-- ⭐⭐ **…and so is the arbitrary-dressing word equation**, at every handle count.
`ArbFrames`' `sqArbRelWord_one_iff` is the case `h = 1`. -/
theorem sqArbRelWord_iff_lamMarkTransitivity : SqArbRelWord h ↔ SqLamMarkTransitivity h :=
  sqArbRelWord_iff_clearingStep.trans sqClearingStep_iff

/-- ⭐ **Every selected marking *is* a row vector.**  A `ℤ₂`-marking is determined by its values
on the generators (`dsq_hom_ext`), the selected core rows are `(1, 0)`, and the `x₁`-row is forced
to `2·ν'(x₀) = 0`.  So `sqNuRows` is not one family of markings among many — it is all of them. -/
theorem nu_eq_sqNuRows_of_selected
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' = sqNuRows h fun i => toAdd (nu' (sqGen h i)) := by
  refine dsq_hom_ext _ _ fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show nu' (dsqSigma h) = sqNuRows h _ (dsqSigma h)
    rw [hsigma, sqNuRows_sigma]
  · show nu' (dsqX0 h) = sqNuRows h _ (dsqX0 h)
    rw [hx0, sqNuRows_x0]
  · show nu' (dsqX1 h) = sqNuRows h _ (dsqX1 h)
    rw [sqNuRows_x1]
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nu_dsqX1 nu', hx0]
    simp
  · exact ((sqNuRows_handleU j').trans (ofAdd_toAdd _)).symm
  · exact ((sqNuRows_handleV j').trans (ofAdd_toAdd _)).symm

/-- ⭐ **The residual, quantified over a `ℤ₂`-vector.**  Since every selected marking is a row
vector, `SqLamMarkTransitivity h` is a statement about `Fin (sqRank h) → ℤ₂` — no quantifier over
abstract characters survives, and the three core coordinates of the vector are never read. -/
theorem sqLamMarkTransitivity_iff_rows :
    SqLamMarkTransitivity h ↔
      ∀ rho : Fin (sqRank h) → ℤ_[2],
        ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
          (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ ∀ x, sqNuRows h rho (Ψ x) = nuSq h x := by
  constructor
  · exact fun H rho => H (sqNuRows h rho) sqNuRows_sigma sqNuRows_x0
  · intro H nu' hsigma hx0
    have heq := nu_eq_sqNuRows_of_selected nu' hsigma hx0
    obtain ⟨Ψ, hlam, hval⟩ := H fun i => toAdd (nu' (sqGen h i))
    exact ⟨Ψ, hlam, fun x => (DFunLike.congr_fun heq (Ψ x)).trans (hval x)⟩

end MarkingBuilder

/-! ## §2 The Frattini set

The elements swallowed by **every** index-two open normal subgroup.  By `ArbFrames` §1 that set
contains every square, every commutator and every even `ℤ₂`-power, and by construction a slot may
be multiplied by one of its members without disturbing `SqModTwoIndep`. -/

section Frattini

variable {h : ℕ}

variable (h) in
/-- **The Frattini set of `D_sq h`**: the elements lying in every index-two open normal
subgroup.  (Dually, the elements dying in `H₁ = D_sq h ⧸ [G,G]G²`.) -/
def SqFrattini : Set (DSq h : Type) :=
  {x | ∀ M : OpenNormalSubgroup (DSq h : Type), M.toSubgroup.index = 2 → x ∈ M.toSubgroup}

theorem one_mem_sqFrattini : (1 : (DSq h : Type)) ∈ SqFrattini h := fun M _ => M.toSubgroup.one_mem

theorem mul_mem_sqFrattini {x y : (DSq h : Type)} (hx : x ∈ SqFrattini h)
    (hy : y ∈ SqFrattini h) : x * y ∈ SqFrattini h :=
  fun M hM => M.toSubgroup.mul_mem (hx M hM) (hy M hM)

theorem inv_mem_sqFrattini {x : (DSq h : Type)} (hx : x ∈ SqFrattini h) : x⁻¹ ∈ SqFrattini h :=
  fun M hM => M.toSubgroup.inv_mem (hx M hM)

/-- **Every square is Frattini.** -/
theorem sq_mem_sqFrattini (x : (DSq h : Type)) : x ^ 2 ∈ SqFrattini h :=
  fun _ hM => sq_mem_of_index_two hM x

/-- **Every commutator is Frattini.** -/
theorem commP_mem_sqFrattini (x y : (DSq h : Type)) : commP x y ∈ SqFrattini h :=
  fun _ hM => commP_mem_of_index_two hM x y

/-- **Every even `ℤ₂`-power is Frattini.** -/
theorem zpowZtwo_mem_sqFrattini (x : (DSq h : Type)) {k : ℤ_[2]} (hk : (2 : ℤ_[2]) ∣ k) :
    zpowZtwo (isProP_DSq h) x k ∈ SqFrattini h :=
  fun _ hM => zpowZtwo_mem_of_even (isProP_DSq h) hM x hk

end Frattini

/-! ## §3 The handle-commutator frame

A clearing step only has to move the two letters of the handle it clears.  For such a frame the
relator identity is not a word equation: everything except the `j`-th handle commutator cancels
against `dsq_relation`, and what is left is an **exact** commutator equation. -/

section CommFrame

variable {h : ℕ} {j : Fin h} {p q : (DSq h : Type)}

variable (h j p q) in
/-- **The handle-commutator frame**: the standard generating tuple with the two letters of
handle `j` replaced by `p` and `q`. -/
noncomputable def sqCommFrame : Fin (sqRank h) → (DSq h : Type) :=
  fun i =>
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then p else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then q else
    sqGen h i

@[simp] theorem sqCommFrame_handleU : sqCommFrame h j p q (sqHandleIdxU j) = p := by
  simp only [sqCommFrame]
  simp

@[simp] theorem sqCommFrame_handleV : sqCommFrame h j p q (sqHandleIdxV j) = q := by
  simp only [sqCommFrame, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  simp

theorem sqCommFrame_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sqCommFrame h j p q (sqHandleIdxU j') = sqGen h (sqHandleIdxU j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqCommFrame, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]

theorem sqCommFrame_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sqCommFrame h j p q (sqHandleIdxV j') = sqGen h (sqHandleIdxV j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqCommFrame, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]

theorem sqCommFrame_core {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    sqCommFrame h j p q i = sqGen h i := by
  simp only [sqCommFrame, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]

@[simp] theorem sqCommFrame_zero : sqCommFrame h j p q 0 = dsqSigma h :=
  sqCommFrame_core (by rw [sqVal_zero]; omega)

@[simp] theorem sqCommFrame_one : sqCommFrame h j p q 1 = dsqX0 h :=
  sqCommFrame_core (by rw [sqVal_one]; omega)

@[simp] theorem sqCommFrame_two : sqCommFrame h j p q 2 = dsqX1 h :=
  sqCommFrame_core (by rw [sqVal_two]; omega)

/-- The handle commutators of the frame agree with the standard ones away from `j`. -/
private theorem sqCommFrame_comm_ne {j' : Fin h} (hne : j' ≠ j) :
    commP (sqCommFrame h j p q (sqHandleIdxU j')) (sqCommFrame h j p q (sqHandleIdxV j'))
      = commP (sqGen h (sqHandleIdxU j')) (sqGen h (sqHandleIdxV j')) := by
  rw [sqCommFrame_handleU_ne hne, sqCommFrame_handleV_ne hne]

private theorem sqCommFrame_gen_zero : sqCommFrame h j p q 0 = sqGen h 0 :=
  sqCommFrame_core (by rw [sqVal_zero]; omega)

private theorem sqCommFrame_gen_one : sqCommFrame h j p q 1 = sqGen h 1 :=
  sqCommFrame_core (by rw [sqVal_one]; omega)

private theorem sqCommFrame_gen_two : sqCommFrame h j p q 2 = sqGen h 2 :=
  sqCommFrame_core (by rw [sqVal_two]; omega)

/-- The relator of the handle-commutator frame, split at handle `j`. -/
private theorem sqRelWord_sqCommFrame_split :
    sqRelWord (sqCommFrame h j p q)
      = sqWord (sqGen h 0) (sqGen h 1) (sqGen h 2) *
          (handlePrefix (fun j' => sqGen h (sqHandleIdxU j'))
              (fun j' => sqGen h (sqHandleIdxV j')) (j : ℕ) * commP p q *
            handleSuffix (fun j' => sqGen h (sqHandleIdxU j'))
              (fun j' => sqGen h (sqHandleIdxV j')) ((j : ℕ) + 1)) := by
  have hpre : handlePrefix (fun j' => sqCommFrame h j p q (sqHandleIdxU j'))
      (fun j' => sqCommFrame h j p q (sqHandleIdxV j')) (j : ℕ)
      = handlePrefix (fun j' => sqGen h (sqHandleIdxU j'))
          (fun j' => sqGen h (sqHandleIdxV j')) (j : ℕ) :=
    handlePrefix_congr _ fun i hi =>
      sqCommFrame_comm_ne (h := h) (j := j) (p := p) (q := q) (j' := i)
        (fun hc => absurd hi (by rw [hc]; omega))
  have hsuf : handleSuffix (fun j' => sqCommFrame h j p q (sqHandleIdxU j'))
      (fun j' => sqCommFrame h j p q (sqHandleIdxV j')) ((j : ℕ) + 1)
      = handleSuffix (fun j' => sqGen h (sqHandleIdxU j'))
          (fun j' => sqGen h (sqHandleIdxV j')) ((j : ℕ) + 1) :=
    handleSuffix_congr _ fun i hi =>
      sqCommFrame_comm_ne (h := h) (j := j) (p := p) (q := q) (j' := i)
        (fun hc => absurd hi (by rw [hc]; omega))
  rw [sqRelWord, sqCommFrame_gen_zero, sqCommFrame_gen_one, sqCommFrame_gen_two,
    handleWord_split _ _ j, sqCommFrame_handleU, sqCommFrame_handleV, hpre, hsuf]

/-- ⭐ **The relator identity of a core-fixing frame is a commutator equation** — an exact `iff`,
at every `h` and every handle. -/
theorem sqRelWord_sqCommFrame_iff :
    sqRelWord (sqCommFrame h j p q) = 1 ↔
      commP p q = commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) := by
  have hstd : sqRelWord (sqGen h) = sqWord (sqGen h 0) (sqGen h 1) (sqGen h 2) *
      (handlePrefix (fun j' => sqGen h (sqHandleIdxU j'))
          (fun j' => sqGen h (sqHandleIdxV j')) (j : ℕ) *
        commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) *
        handleSuffix (fun j' => sqGen h (sqHandleIdxU j'))
          (fun j' => sqGen h (sqHandleIdxV j')) ((j : ℕ) + 1)) := by
    rw [sqRelWord, handleWord_split _ _ j]
  rw [sqRelWord_sqCommFrame_split]
  constructor
  · intro hone
    have hz := hone.trans (hstd.symm.trans (dsq_relation h)).symm
    exact mul_left_cancel (mul_right_cancel (mul_left_cancel hz))
  · intro heq
    rw [heq, ← hstd]
    exact dsq_relation h

/-- The λ-row of the handle-commutator frame, from the two letters' `λ`-triviality. -/
theorem sqCommFrame_nuLam (hp : nuLam h p = 1) (hq : nuLam h q = 1) (i : Fin (sqRank h)) :
    nuLam h (sqCommFrame h j p q i) = nuLam h (sqGen h i) := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqCommFrame_core (by rw [sqVal_zero]; omega)]
  · rw [sqCommFrame_core (by rw [sqVal_one]; omega)]
  · rw [sqCommFrame_core (by rw [sqVal_two]; omega)]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqCommFrame_handleU, hp, nuLam_handleU]
    · rw [sqCommFrame_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqCommFrame_handleV, hq, nuLam_handleV]
    · rw [sqCommFrame_handleV_ne hjj]

/-- **Mod-2 independence of the handle-commutator frame**, from the Frattini criterion: it is
enough that the two letters differ from the cleared letters `U`, `V` by Frattini elements. -/
theorem sqCommFrame_modTwoIndep
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (hp : (sqEichU h nu' j)⁻¹ * p ∈ SqFrattini h)
    (hq : (sqEichV h nu' j)⁻¹ * q ∈ SqFrattini h) : SqModTwoIndep (sqCommFrame h j p q) := by
  intro M hM
  by_contra hc
  have hslot : ∀ i, sqCommFrame h j p q i ∈ M.toSubgroup :=
    fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hsig : dsqSigma h ∈ M.toSubgroup := by
    have := hslot 0; rwa [sqCommFrame_zero] at this
  have hx0 : dsqX0 h ∈ M.toSubgroup := by
    have := hslot 1; rwa [sqCommFrame_one] at this
  have hpiv : sqPivot h ∈ M.toSubgroup := sqPivot_mem_of_index_two hM hsig hx0
  -- `U` and `V` are in `M`, because `p` and `q` are and the difference is Frattini
  have hU : sqEichU h nu' j ∈ M.toSubgroup := by
    have hpm : p ∈ M.toSubgroup := by
      have := hslot (sqHandleIdxU j); rwa [sqCommFrame_handleU] at this
    have hid : sqEichU h nu' j = p * ((sqEichU h nu' j)⁻¹ * p)⁻¹ := by group
    rw [hid]
    exact M.toSubgroup.mul_mem hpm (M.toSubgroup.inv_mem (hp M hM))
  have hV : sqEichV h nu' j ∈ M.toSubgroup := by
    have hqm : q ∈ M.toSubgroup := by
      have := hslot (sqHandleIdxV j); rwa [sqCommFrame_handleV] at this
    have hid : sqEichV h nu' j = q * ((sqEichV h nu' j)⁻¹ * q)⁻¹ := by group
    rw [hid]
    exact M.toSubgroup.mul_mem hqm (M.toSubgroup.inv_mem (hq M hM))
  have hgenU : sqGen h (sqHandleIdxU j) ∈ M.toSubgroup := by
    rw [← pivotPow_mul_sqEichU (h := h) (nu' := nu') (j := j)]
    exact M.toSubgroup.mul_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _) hU
  have hgenV : sqGen h (sqHandleIdxV j) ∈ M.toSubgroup := by
    rw [← sqEichV_mul_pivotPow (h := h) (nu' := nu') (j := j)]
    exact M.toSubgroup.mul_mem hV (zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _)
  obtain ⟨i, hi⟩ := exists_sqGen_notMem M hM
  refine hi ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact hsig
  · exact hx0
  · have := hslot 2; rwa [sqCommFrame_two] at this
  · by_cases hjj : j' = j
    · subst hjj; exact hgenU
    · have := hslot (sqHandleIdxU j'); rwa [sqCommFrame_handleU_ne hjj] at this
  · by_cases hjj : j' = j
    · subst hjj; exact hgenV
    · have := hslot (sqHandleIdxV j'); rwa [sqCommFrame_handleV_ne hjj] at this

/-- **The clearing step from a handle-commutator solution.** -/
theorem sqCommStep {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (hplam : nuLam h p = 1) (hqlam : nuLam h q = 1)
    (hpnu : nu' p = 1) (hqnu : nu' q = 1)
    (hindep : SqModTwoIndep (sqCommFrame h j p q))
    (hcomm : commP p q = commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j))) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
          nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
            ∀ j' : Fin h, j' ≠ j →
              nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j')) := by
  have hrel : sqRelWord (sqCommFrame h j p q) = 1 := sqRelWord_sqCommFrame_iff.mpr hcomm
  have hsurj := sqLiftHom_surjective_of_modTwoIndep hrel hindep
  refine ⟨sqAutOfMark hrel hsurj, fun x => ?_, ?_, ?_, ?_, ?_, fun j' hjj => ⟨?_, ?_⟩⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel hsurj)) = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel hsurj (sqGen h i)) = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, sqCommFrame_nuLam hplam hqlam]
    exact DFunLike.congr_fun hext x
  · show nu' (sqAutOfMark hrel hsurj (sqGen h 0)) = ofAdd (1 : ℤ_[2])
    rw [sqAutOfMark_gen, sqCommFrame_zero, hsigma]
  · show nu' (sqAutOfMark hrel hsurj (sqGen h 1)) = ofAdd (0 : ℤ_[2])
    rw [sqAutOfMark_gen, sqCommFrame_one, hx0]
  · rw [sqAutOfMark_gen, sqCommFrame_handleU, hpnu]
  · rw [sqAutOfMark_gen, sqCommFrame_handleV, hqnu]
  · rw [sqAutOfMark_gen, sqCommFrame_handleU_ne hjj]
  · rw [sqAutOfMark_gen, sqCommFrame_handleV_ne hjj]

/-- **The handle-commutator identity**: at every selected marking and every handle, the handle's
commutator is a commutator of two elements of `ker λ ∩ ker ν'` differing from the cleared letters
by Frattini elements.

⚠ **This is false for `h ≥ 1`** — see Headline 3: the class-two balance of a core-fixing frame
forces both handle rows of `ν'` to vanish already.  It is kept because
`sqRelWord_sqCommFrame_iff` is an `iff`, so this *is* what a core-fixing frame must supply, and
its failure is the precise reason the `x₀`-slot has to be dressed. -/
def SqHandleComm (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ p q : (DSq h : Type), nuLam h p = 1 ∧ nuLam h q = 1 ∧ nu' p = 1 ∧ nu' q = 1 ∧
        (sqEichU h nu' j)⁻¹ * p ∈ SqFrattini h ∧ (sqEichV h nu' j)⁻¹ * q ∈ SqFrattini h ∧
          commP p q = commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j))

/-- The handle-commutator identity supplies a clearing step. -/
theorem sqClearingStep_of_handleComm (H : SqHandleComm h) : SqClearingStep h := by
  intro nu' j hsigma hx0
  obtain ⟨p, q, hplam, hqlam, hpnu, hqnu, hpf, hqf, hcomm⟩ := H nu' j hsigma hx0
  exact sqCommStep hsigma hx0 hplam hqlam hpnu hqnu
    (sqCommFrame_modTwoIndep hpf hqf) hcomm

/-- …and hence the residual, at every `h`. -/
theorem sqLamMarkTransitivity_of_handleComm (H : SqHandleComm h) : SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_clearingStep (sqClearingStep_of_handleComm H)

end CommFrame

/-! ## §4 Stress pins -/

section StressTests

/-- Stress: the marking builder is not vacuous — the zero row vector is the standard marking. -/
example (h : ℕ) : sqNuRows h 0 (dsqSigma h) = ofAdd (1 : ℤ_[2]) := sqNuRows_sigma

/-- Stress: the handle rows really are free — any `ℤ₂`-vector is realized. -/
example (h : ℕ) (rho : Fin (sqRank h) → ℤ_[2]) (j : Fin h) :
    sqNuRows h rho (sqGen h (sqHandleIdxU j)) = ofAdd (rho (sqHandleIdxU j)) :=
  sqNuRows_handleU j

/-- Stress: at `h = 0` the clearing scheme is the residual, which is a theorem there. -/
example : SqClearingStep 0 := sqClearingStep_iff.mpr sqLamMarkTransitivity_zero

/-- Stress: the standard marking is its own row vector, so the classification is not vacuous. -/
example (h : ℕ) : nuSq h = sqNuRows h fun i => toAdd (nuSq h (sqGen h i)) :=
  nu_eq_sqNuRows_of_selected _ (nuSq_sigma h) (nuSq_x0 h)

/-- Stress: the row form of the residual is a statement about `Fin (sqRank h) → ℤ₂` alone. -/
example (h : ℕ) (H : SqLamMarkTransitivity h) (rho : Fin (sqRank h) → ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ ∀ x, sqNuRows h rho (Ψ x) = nuSq h x :=
  sqLamMarkTransitivity_iff_rows.mp H rho

/-- Stress: the equivalence chain closes at every `h` — the three named statements agree. -/
example (h : ℕ) : SqArbRelWord h ↔ SqClearingStep h := sqArbRelWord_iff_clearingStep

example (h : ℕ) : SqClearingStep h ↔ SqLamMarkTransitivity h := sqClearingStep_iff

/-- Stress: the trivial handle-commutator solution at the standard marking — the standard
letters themselves. -/
example (h : ℕ) (j : Fin h) : sqRelWord (sqCommFrame h j (sqGen h (sqHandleIdxU j))
    (sqGen h (sqHandleIdxV j))) = 1 := sqRelWord_sqCommFrame_iff.mpr rfl

/-- Stress: the commutator equation is exactly the relator identity, both ways. -/
example (h : ℕ) (j : Fin h) (p q : (DSq h : Type)) (hrel : sqRelWord (sqCommFrame h j p q) = 1) :
    commP p q = commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) :=
  sqRelWord_sqCommFrame_iff.mp hrel

/-- Stress: the Frattini set swallows the pivot's even powers, so a slot may be dressed by one
without any mod-2 cost. -/
example (h : ℕ) (k : ℤ_[2]) : zpowZtwo (isProP_DSq h) (sqPivot h) (2 * k) ∈ SqFrattini h :=
  zpowZtwo_mem_sqFrattini _ ⟨k, rfl⟩

/-- Stress: the handle stratum, at every unit exponent, from the handle-commutator identity. -/
example (h : ℕ) {c : ℤ_[2]} (hc : IsUnit c) (hh : 0 < h) (H : SqHandleComm h) :
    SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (sqLamMarkTransitivity_of_handleComm H)

end StressTests

/-! ## §5 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable. -/

section AxiomPins

#print axioms sqRowMark
#print axioms sqRowMark_zero
#print axioms sqRowMark_one
#print axioms sqRowMark_two
#print axioms sqRowMark_of_three
#print axioms sqRelWord_sqRowMark
#print axioms sqNuRows
#print axioms sqNuRows_sigma
#print axioms sqNuRows_x0
#print axioms sqNuRows_x1
#print axioms sqNuRows_gen_of_three
#print axioms sqNuRows_handleU
#print axioms sqNuRows_handleV
#print axioms sqClearRows
#print axioms sqNuClear
#print axioms sqNuClear_sigma
#print axioms sqNuClear_x0
#print axioms sqNuClear_handleU_self
#print axioms sqNuClear_handleV_self
#print axioms sqNuClear_handleU_ne
#print axioms sqNuClear_handleV_ne
#print axioms sqClearingStep_of_lamMarkTransitivity
#print axioms sqClearingStep_iff
#print axioms sqArbRelWord_iff_lamMarkTransitivity
#print axioms nu_eq_sqNuRows_of_selected
#print axioms sqLamMarkTransitivity_iff_rows
#print axioms SqFrattini
#print axioms one_mem_sqFrattini
#print axioms mul_mem_sqFrattini
#print axioms inv_mem_sqFrattini
#print axioms sq_mem_sqFrattini
#print axioms commP_mem_sqFrattini
#print axioms zpowZtwo_mem_sqFrattini
#print axioms sqCommFrame
#print axioms sqCommFrame_handleU
#print axioms sqCommFrame_handleV
#print axioms sqCommFrame_handleU_ne
#print axioms sqCommFrame_handleV_ne
#print axioms sqCommFrame_core
#print axioms sqCommFrame_zero
#print axioms sqCommFrame_one
#print axioms sqCommFrame_two
#print axioms sqRelWord_sqCommFrame_iff
#print axioms sqCommFrame_nuLam
#print axioms sqCommFrame_modTwoIndep
#print axioms sqCommStep
#print axioms SqHandleComm
#print axioms sqClearingStep_of_handleComm
#print axioms sqLamMarkTransitivity_of_handleComm

end AxiomPins

end SqCore

end Dyadic

end GQ2
