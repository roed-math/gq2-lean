/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.SqCore.HandleMixFixesCore

/-!
# The `L_sq` Eichler family: parameter reduction, absorption calculus, and the seed interface

**Lane SQ, the P2 residue.**  `GQ2/Dyadic/SqCore/HandleMixFixesCore.lean` isolated the whole
`L_sq` handle stratum in the single family `SqHandleEichler h c` — one χ-preserving
automorphism per `(handle index, 2-adic parameter)`, shifting the `u_j`-row by `k·ν'(w)`
against the χ-trivial pivot `w = σ·x₀^{−c}`, with the `v_j`-row hypothesis making the forced
core compensation (a multiple of `v̄_j`) invisible.  This file **reduces** that family in three
independent directions, so that what remains is a single word-level seed per handle:

1. **Parameter reduction** (§1).  The moves compose: the pivot row is itself preserved by
   every move (it is a function of the σ- and `x₀`-rows, which the moves fix), so the
   `(j, k₁)`- and `(j, k₂)`-moves chain to the `(j, k₁+k₂)`-move — `sqEichlerMoveAt_add`.
   Since every non-unit of `ℤ₂` is `1 + (unit)`, the full 2-adic family follows from its
   **unit slice** (`sqHandleEichler_of_unit_moves`).  No `θ_w`-conjugation, no `SL₂ = E₂`
   bookkeeping, no compactness: the additive closure replaces memo §5.2's rescaling argument
   at this seam.

2. **Absorption calculus** (§2).  The free identity `sq_absorb` shows the `L_sq` relator
   survives a σ-slot/`u_j`-slot substitution as soon as the **core defect** it creates is the
   `handlePrefix`-conjugate of a single `[v_j, ρ]`-commutator — the exact analogue of HM2's
   mixing identity `commP_handleMixD_mul`, but posed with the defect as the interface (the
   `L_sq` core does not decompose into HM2's `W·[c,d]` shape; see the walls below).  §2 also
   pins the defect of the τ-move the memo excludes (`τ_a(k) : σ ↦ x₁^k·σ`, "does NOT fix `W`"):
   `sqWord_tau_sigma_defect` computes it *exactly* — a single `s`-conjugated commutator
   `[x₁^k, x₀]^σ` — so a future mechanism knows the precise word it must absorb.

3. **The seed interface** (§3–§4).  `SqEichlerSeed h c j k` packages the residual word-level
   input as data: two substitution quadruples for the **four-slot** scaffold `sqEichlerSub`
   (`σ ↦ σ·β₁`, `x₀ ↦ x₀·β₀`, `x₁ ↦ x₁·β₂`, `u_j ↦ ρ·u_j`, all other letters fixed), each
   killing the relator, inverse to each other on generators, with the `β`'s χ-trivial and
   `ν'`-invisible (given the `v_j`-row hypothesis) and `ρ` χ-trivial of `ν'`-row `k·ν'(w)`.
   `sqEichlerMoveAt_of_seed` turns a seed into the `(j,k)`-move; `sqHandleEichler_of_seeds`
   assembles `SqHandleEichler h c` from seeds on the unit slice alone.  Four slots are not a
   convenience but a **necessity**: the class-two balance computed in §3 shows a scaffold
   fixing the `x₀`- and `x₁`-slots is unsatisfiable at every unit parameter, with the forced
   first-order classes `β̄₁ = −k(2+c)v̄_j`, `β̄₀ = −k·v̄_j`, `β̄₂ = −2k·v̄_j`.

## The walls, sharpened (recorded findings)

The predecessor file recorded two walls against porting HM2's `Φ_j` letter-for-letter (word
shape, and χ-nontriviality of every core letter).  The analysis behind this file sharpens
both into basis-independent obstructions, which is *why* the interface below is posed at the
defect/seed level rather than as a decomposition:

* **Evenness.**  The abelianized `L_sq` relator is `2t̄` (`t = x̄₁ − 2x̄₀`), so in **every**
  topological basis of the ambient free pro-2 group every letter-degree of the relator is
  even.  A mechanism whose moved letter occurs exactly once is impossible in any coordinates.
* **Syllable count.**  HM2's mechanism needs the moved letter to occur exactly twice, as the
  two slots of one commutator (`W·[c,d]·ζ·[u,v]` with `d ∉ W`).  In the given letters the
  reduced `L_sq` core has **six** σ-syllables (four after cyclic reduction), and the natural
  2-adic changes of variables tried by hand (`σ' = σ·x₀^{−c}`, `t = x₁·x₀^{−2}`, conjugated
  re-markings) do not reach two: the candidate `σ' = σ·x₀^{−c}` *does* make the pivot a letter
  with `[σ', x₀]`-material exposed — `(x₀^σ)⁻¹x₀⁻³ = [σ,x₀]x₀⁻⁴` and `x₀^{±c}` commutes with
  `x₀`, so the re-marked relator collapses partially — but the `x₀^{±c}`-dressings trapped
  between the `x₁`-letters leave nine `x₀`-syllables, and the `x₁²`-factor blocks the
  `x₁`-slot by evenness.  So the change of variables alone does not produce HM2's shape, and
  the residual word problem is genuinely a search (the spike solved the easier collector case
  by machine search over reduced words, `handlemixlift-spike.md` §4.1).
* **All three core slots must move** (the §3 class-two balance).  Against the graded Lie ring
  of `D_sq`, the `[v̄_j, σ̄]`-coordinate of the class-two defect of a slot substitution can be
  cancelled by no available relation, forcing the `x₀`-slot to shift by `−k·v̄_j` — and then
  the degree-one and remaining degree-two coordinates force the `σ`- and `x₁`-slots too.
  This kills the two-slot (σ, `u_j`) ansatz outright and quantifies the frame analysis
  recorded in `HandleMixFixesCore`'s §5 docstring ("the Eichler unipotent must shift the core
  plane by a multiple of `v̄_j`"): the shift is on *all three* core slots, with coefficients
  `−k(2+c), −k, −2k`.
* **What survives.**  The absorption interface of §2 is exactly what any solution must
  produce, and it is *weaker* than HM2's on-the-nose fixing: the relator only needs to die in
  `D_sq` (conjugate defects suffice), and the two-sided compensation may use the trailing
  handle blocks.  The parameter reduction of §1 means the seed need only be found at unit
  parameters, where the frame analysis (mod-2 cup form) places no parity obstruction.

## Contents

* **§1** `SqEichlerMoveAt` (the per-handle slice), `sqEichlerMoveAt_zero`, the composition law
  `sqEichlerMoveAt_add`, the unit-slice reductions `sqEichlerMoveAt_of_units` and
  `sqHandleEichler_of_unit_moves`;
* **§2** the absorption identity `sq_absorb`, and the exact τ-defect
  `sqWord_tau_sigma_defect`;
* **§3** the two-slot scaffold `sqEichlerSub` with its value lemmas and the structural
  splitting `sqRelWord_sqEichlerSub`, plus the defect-route discharge
  `sqRelWord_sqEichlerSub_eq_one`;
* **§4** `SqEichlerSeed` and the productions `sqEichlerMoveAt_of_seed`,
  `sqHandleEichler_of_seeds`;
* **§5** stress pins, **§6** committed axiom prints.

## Axiom hygiene

Every declaration prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no census
axiom is reachable (the file consumes only the h-generic `χ_sq`/`ν_sq` layer, HM1's word
calculus, and `HandleMixFixesCore`).  Census unchanged at **11**.  §6 commits the prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The per-handle slice, and the parameter reduction

`SqHandleEichler h c` quantifies over `(j, k, ν')` jointly.  Slicing off `(j, k)` exposes the
composition law: because every move fixes the σ- and `x₀`-rows, it fixes the **pivot row**
`ν'(w) = ν'(σ) − c·ν'(x₀)` (`toAdd_nu_sqMixPivotElem`), and because it fixes every `v`-row it
preserves the `v_j`-row hypothesis.  So moves at `k₁` and `k₂` compose to the move at
`k₁ + k₂` — the 2-adic parameter is generated by its unit slice. -/

section Slice

/-- **The `(j, k)`-slice of `SqHandleEichler`**: the single Eichler move at handle `j` with
2-adic parameter `k`.  `SqHandleEichler h c` is definitionally `∀ j k`, this slice. -/
def SqEichlerMoveAt (h : ℕ) (c : ℤ_[2]) (j : Fin h) (k : ℤ_[2]) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (sqGen h (sqHandleIdxV j)) = 1 →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x)
          ∧ nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
          ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
          ∧ toAdd (nu' (Ψ (sqGen h (sqHandleIdxU j))))
              = toAdd (nu' (sqGen h (sqHandleIdxU j))) + k * toAdd (nu' (sqMixPivotElem h c))
          ∧ (∀ i : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV i)))
              = nu' (sqGen h (sqHandleIdxV i)))
          ∧ (∀ i : Fin h, i ≠ j → nu' (Ψ (sqGen h (sqHandleIdxU i)))
              = nu' (sqGen h (sqHandleIdxU i)))

/-- The slice is definitionally faithful: `SqHandleEichler` **is** the family of slices. -/
theorem sqHandleEichler_iff_moveAt (h : ℕ) (c : ℤ_[2]) :
    SqHandleEichler h c ↔ ∀ (j : Fin h) (k : ℤ_[2]), SqEichlerMoveAt h c j k := Iff.rfl

/-- At parameter `0` the identity is a move: every row condition is trivial. -/
theorem sqEichlerMoveAt_zero (h : ℕ) (c : ℤ_[2]) (j : Fin h) : SqEichlerMoveAt h c j 0 := by
  intro nu' _
  refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl, rfl, rfl, ?_, fun _ => rfl, fun _ _ => rfl⟩
  rw [zero_mul, add_zero]
  rfl

/-- **The composition law**: Eichler moves at the same handle add in the parameter.  The two
transport facts making the chain work are that each move preserves the `v_j`-row hypothesis
(its `v`-rows are fixed) and the pivot row (a function of the fixed σ- and `x₀`-rows). -/
theorem sqEichlerMoveAt_add {h : ℕ} {c : ℤ_[2]} {j : Fin h} {k₁ k₂ : ℤ_[2]}
    (H₁ : SqEichlerMoveAt h c j k₁) (H₂ : SqEichlerMoveAt h c j k₂) :
    SqEichlerMoveAt h c j (k₁ + k₂) := by
  intro nu' hv
  obtain ⟨Ψ₁, hchi₁, hs₁, hx₁, hu₁, hV₁, hU₁⟩ := H₁ nu' hv
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₁) with hmudef
  have hmuv : mu (sqGen h (sqHandleIdxV j)) = 1 := by
    show nu' (Ψ₁ (sqGen h (sqHandleIdxV j))) = 1
    rw [hV₁ j, hv]
  obtain ⟨Ψ₂, hchi₂, hs₂, hx₂, hu₂, hV₂, hU₂⟩ := H₂ mu hmuv
  have hmupiv : toAdd (mu (sqMixPivotElem h c)) = toAdd (nu' (sqMixPivotElem h c)) := by
    rw [toAdd_nu_sqMixPivotElem mu c, toAdd_nu_sqMixPivotElem nu' c,
      show mu (dsqSigma h) = nu' (Ψ₁ (dsqSigma h)) from rfl, hs₁,
      show mu (dsqX0 h) = nu' (Ψ₁ (dsqX0 h)) from rfl, hx₁]
  refine ⟨Ψ₂.trans Ψ₁, fun x => (hchi₁ (Ψ₂ x)).trans (hchi₂ x), ?_, ?_, ?_, ?_, ?_⟩
  · show mu (Ψ₂ (dsqSigma h)) = nu' (dsqSigma h)
    rw [hs₂]
    exact hs₁
  · show mu (Ψ₂ (dsqX0 h)) = nu' (dsqX0 h)
    rw [hx₂]
    exact hx₁
  · show toAdd (mu (Ψ₂ (sqGen h (sqHandleIdxU j))))
      = toAdd (nu' (sqGen h (sqHandleIdxU j))) + (k₁ + k₂) * toAdd (nu' (sqMixPivotElem h c))
    rw [hu₂, hmupiv,
      show toAdd (mu (sqGen h (sqHandleIdxU j)))
        = toAdd (nu' (Ψ₁ (sqGen h (sqHandleIdxU j)))) from rfl, hu₁]
    ring
  · intro i
    show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))
    rw [hV₂ i]
    show nu' (Ψ₁ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))
    exact hV₁ i
  · intro i hi
    show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
    rw [hU₂ i hi]
    show nu' (Ψ₁ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
    exact hU₁ i hi

/-- A non-unit of `ℤ₂` is `1` plus a unit — the decomposition driving the unit-slice
reduction. -/
theorem isUnit_sub_one_of_not_isUnit {k : ℤ_[2]} (hk : ¬ IsUnit k) : IsUnit (k - 1) := by
  have hdvd : (2 : ℤ_[2]) ∣ k := by
    by_contra hnd
    exact hk (isUnit_of_not_two_dvd hnd)
  rw [isUnit_iff_not_two_dvd]
  rintro ⟨t, ht⟩
  obtain ⟨s, hs⟩ := hdvd
  exact not_isUnit_two
    (isUnit_of_dvd_unit ⟨s - t, by linear_combination hs - ht⟩ isUnit_one)

/-- **The parameter reduction**: moves on the unit slice generate all 2-adic parameters
(`0` is the identity, a unit is a unit, and an even parameter is `1 + unit`). -/
theorem sqEichlerMoveAt_of_units {h : ℕ} {c : ℤ_[2]} {j : Fin h}
    (H : ∀ k : ℤ_[2], IsUnit k → SqEichlerMoveAt h c j k) (k : ℤ_[2]) :
    SqEichlerMoveAt h c j k := by
  by_cases hk : IsUnit k
  · exact H k hk
  · by_cases hk0 : k = 0
    · rw [hk0]
      exact sqEichlerMoveAt_zero h c j
    · have hsum := sqEichlerMoveAt_add (H 1 isUnit_one) (H (k - 1)
        (isUnit_sub_one_of_not_isUnit hk))
      have hrw : 1 + (k - 1) = k := by ring
      rwa [hrw] at hsum

/-- **The residual obligation, reduced to the unit slice**: `SqHandleEichler h c` follows from
the per-handle Eichler moves at *unit* parameters alone. -/
theorem sqHandleEichler_of_unit_moves {h : ℕ} {c : ℤ_[2]}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → SqEichlerMoveAt h c j k) :
    SqHandleEichler h c :=
  fun j k => sqEichlerMoveAt_of_units (H j) k

end Slice

/-! ## §2 The absorption calculus

The interface any word-level mechanism must meet.  `sq_absorb` is the `L_sq` mirror of HM2's
mixing identity `commP_handleMixD_mul`, posed defect-first: if the substituted core word
differs from the original by the `p`-conjugate of a single `[v, ρ]`-commutator, then the
`u`-slot correction `u ↦ ρ·u` restores the whole relator, with the trailing block untouched.
The engine is `[v,ρ]·[ρ,v] = 1` after the `u`-conjugation — no commuting hypotheses at all. -/

section Absorption

variable {G : Type*} [Group G]

/-- **The absorption identity.**  If the substituted core word `W'` differs from the original
core word `W` by the `p`-conjugate of a single `[v,ρ]`-commutator pushed through `u`, then the
`u`-slot correction `u ↦ ρ·u` restores the relator shape on the nose.  The engine is
`[v,ρ]·[ρ,v] = 1` after the `u`-conjugation — no commuting hypotheses at all.  Stated with the
core words abstract, so it serves every slot pattern of the §3 scaffold at once. -/
theorem sq_absorb (W' W u v p t ρ : G)
    (hd : W' = W * (p * conjP (commP v ρ) u * p⁻¹)) :
    W' * (p * commP (ρ * u) v * t) = W * (p * commP u v * t) := by
  rw [hd]
  simp only [commP, conjP]
  group

end Absorption

section TauDefect

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]

/-- A 2-adic self-power passes through its own conjugation slot: `y^{y^k·s} = y^s`. -/
theorem conjP_zpowZtwo_self_mul (hP : IsProP 2 P) (y s : P) (k : ℤ_[2]) :
    conjP y (zpowZtwo hP y k * s) = conjP y s := by
  have hswap : (zpowZtwo hP y k)⁻¹ * y = y * (zpowZtwo hP y k)⁻¹ :=
    ((commute_zpowZtwo_self hP y k).inv_left).eq
  simp only [conjP, mul_inv_rev]
  rw [mul_assoc s⁻¹ (zpowZtwo hP y k)⁻¹ y, hswap]
  group

/-- **The exact defect of the excluded transvection** `τ_a(k) : σ ↦ x₁^k·σ` (memo §5.1's ✗
row, quantified): the `L_sq` core word moves by exactly one `σ`-conjugated commutator,
`sqWord (x₁^k·σ) = [x₁^k, x₀]^σ · sqWord σ`.  The `[x₁, x₁^σ]`-factor is blind to the move
(`conjP_zpowZtwo_self_mul`); only the `(x₀^σ)⁻¹`-factor sees it. -/
theorem sqWord_tau_sigma_defect (hP : IsProP 2 P) (s x y : P) (k : ℤ_[2]) :
    sqWord (zpowZtwo hP y k * s) x y
      = conjP (commP (zpowZtwo hP y k) x) s * sqWord s x y := by
  simp only [sqWord]
  rw [conjP_zpowZtwo_self_mul hP y s k]
  simp only [commP, conjP]
  group

end TauDefect

/-! ## §3 The four-slot substitution scaffold

The shape every Eichler discharge must take on the `L_sq` marking: right factors on the three
core slots (`σ ↦ σ·β₁`, `x₀ ↦ x₀·β₀`, `x₁ ↦ x₁·β₂`) and a left factor on the `u_j`-slot
(`u_j ↦ ρ·u_j`), every other letter fixed.

**Why four slots** (the class-two balance — a finding of this file).  In the graded Lie ring
of `D_sq` the class-two defect of a slot substitution must vanish, and the relations available
in degree two are only the relator's quadratic form and the 2-divisible family
`2[t̄, ḡ] ≡ 0` (`t = x̄₁ − 2x̄₀`) — neither touches the `[v̄_j, σ̄]`-coordinate.  Computing the
defect of the substitution above against the site/suffix classes of the `L_sq` relator gives,
with `β̄₁ = a₁v̄_j`, `β̄₀ = a₀v̄_j`, `β̄₂ = a₂v̄_j`, `ρ̄ = k(σ̄ − c·x̄₀) + a_u·v̄_j`
(the row/χ constraints pin the `β`'s to `v̄_j`-multiples mod torsion):

```text
[v̄,σ̄] : −a₀ − k = 0            [v̄,x̄₀] : a₁ + 10a₀ + kc + 4m = 0
[v̄,x̄₁] : −8a₀ + a₂ − 2m = 0    degree 1 : −4a₀ + 2a₂ = 0
```

(`m` the coefficient of the relation `2[t̄, v̄_j]`), forced solution `a₀ = −k`, `a₂ = −2k`,
`m = 3k`, `a₁ = −k(2 + c)`, first order.  So the `x₀`-slot **must** move (by `−k·v̄_j`) for
every odd `k` — a two-slot scaffold fixing `x₀` and `x₁` literally is unsatisfiable at every
unit parameter, which sharpens `HandleMixFixesCore`'s wall 2: not only is no core *letter*
clear-blind, no core *slot* can stay still.  The `v_j`-slot, by contrast, never needs to move
(`a_v = 0` solves), matching the `v`-rows-fixed clause of the target statement. -/

section Scaffold

variable {h : ℕ}

/-- `Fin (sqRank h)` numeral discrimination: `1 ≠ 0`. -/
theorem sqFin_one_ne_zero (h : ℕ) : (1 : Fin (sqRank h)) ≠ 0 :=
  Fin.ne_of_val_ne (by rw [sqVal_one, sqVal_zero]; omega)

/-- `Fin (sqRank h)` numeral discrimination: `2 ≠ 0`. -/
theorem sqFin_two_ne_zero (h : ℕ) : (2 : Fin (sqRank h)) ≠ 0 :=
  Fin.ne_of_val_ne (by rw [sqVal_two, sqVal_zero]; omega)

/-- `Fin (sqRank h)` numeral discrimination: `2 ≠ 1`. -/
theorem sqFin_two_ne_one (h : ℕ) : (2 : Fin (sqRank h)) ≠ 1 :=
  Fin.ne_of_val_ne (by rw [sqVal_two, sqVal_one]; omega)

/-- **The four-slot Eichler substitution scaffold**: `σ ↦ σ·β₁`, `x₀ ↦ x₀·β₀`,
`x₁ ↦ x₁·β₂`, `u_j ↦ ρ·u_j`, every other letter fixed. -/
noncomputable def sqEichlerSub (h : ℕ) (j : Fin h) (β₁ β₀ β₂ ρ : (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  Function.update (Function.update (Function.update (Function.update (sqGen h)
      0 (dsqSigma h * β₁)) 1 (dsqX0 h * β₀)) 2 (dsqX1 h * β₂))
    (sqHandleIdxU j) (ρ * sqGen h (sqHandleIdxU j))

variable (j : Fin h) (β₁ β₀ β₂ ρ : (DSq h : Type))

@[simp] theorem sqEichlerSub_zero : sqEichlerSub h j β₁ β₀ β₂ ρ 0 = dsqSigma h * β₁ := by
  rw [sqEichlerSub,
    Function.update_of_ne (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_zero]; omega))),
    Function.update_of_ne (Ne.symm (sqFin_two_ne_zero h)),
    Function.update_of_ne (Ne.symm (sqFin_one_ne_zero h)),
    Function.update_self]

@[simp] theorem sqEichlerSub_one : sqEichlerSub h j β₁ β₀ β₂ ρ 1 = dsqX0 h * β₀ := by
  rw [sqEichlerSub,
    Function.update_of_ne (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_one]; omega))),
    Function.update_of_ne (Ne.symm (sqFin_two_ne_one h)),
    Function.update_self]

@[simp] theorem sqEichlerSub_two : sqEichlerSub h j β₁ β₀ β₂ ρ 2 = dsqX1 h * β₂ := by
  rw [sqEichlerSub,
    Function.update_of_ne (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_two]; omega))),
    Function.update_self]

@[simp] theorem sqEichlerSub_handleU_self :
    sqEichlerSub h j β₁ β₀ β₂ ρ (sqHandleIdxU j) = ρ * sqGen h (sqHandleIdxU j) := by
  rw [sqEichlerSub, Function.update_self]

theorem sqEichlerSub_handleU_of_ne {i : Fin h} (hi : i ≠ j) :
    sqEichlerSub h j β₁ β₀ β₂ ρ (sqHandleIdxU i) = sqGen h (sqHandleIdxU i) := by
  rw [sqEichlerSub, Function.update_of_ne (fun hc => hi (sqHandleIdxU_injective hc)),
    Function.update_of_ne (sqHandleIdxU_ne_of_val_lt i (by rw [sqVal_two]; omega)),
    Function.update_of_ne (sqHandleIdxU_ne_of_val_lt i (by rw [sqVal_one]; omega)),
    Function.update_of_ne (sqHandleIdxU_ne_of_val_lt i (by rw [sqVal_zero]; omega))]

@[simp] theorem sqEichlerSub_handleV (i : Fin h) :
    sqEichlerSub h j β₁ β₀ β₂ ρ (sqHandleIdxV i) = sqGen h (sqHandleIdxV i) := by
  rw [sqEichlerSub, Function.update_of_ne (Ne.symm (sqHandleIdxU_ne_sqHandleIdxV j i)),
    Function.update_of_ne (sqHandleIdxV_ne_of_val_lt i (by rw [sqVal_two]; omega)),
    Function.update_of_ne (sqHandleIdxV_ne_of_val_lt i (by rw [sqVal_one]; omega)),
    Function.update_of_ne (sqHandleIdxV_ne_of_val_lt i (by rw [sqVal_zero]; omega))]

/-- **Structure of the substituted relator**: core word at `(σβ₁, x₀β₀, x₁β₂)`, then the
handle block split at `j` with the `u_j`-slot moved (HM2's `handleWord_update_split`). -/
theorem sqRelWord_sqEichlerSub :
    sqRelWord (sqEichlerSub h j β₁ β₀ β₂ ρ)
      = sqWord (dsqSigma h * β₁) (dsqX0 h * β₀) (dsqX1 h * β₂)
        * (handlePrefix (fun i => sqGen h (sqHandleIdxU i))
              (fun i => sqGen h (sqHandleIdxV i)) (j : ℕ)
          * commP (ρ * sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j))
          * handleSuffix (fun i => sqGen h (sqHandleIdxU i))
              (fun i => sqGen h (sqHandleIdxV i)) ((j : ℕ) + 1)) := by
  have hU : (fun i => sqEichlerSub h j β₁ β₀ β₂ ρ (sqHandleIdxU i))
      = Function.update (fun i => sqGen h (sqHandleIdxU i)) j
          (ρ * sqGen h (sqHandleIdxU j)) := by
    funext i
    by_cases hij : i = j
    · subst hij
      rw [sqEichlerSub_handleU_self, Function.update_self]
    · rw [sqEichlerSub_handleU_of_ne j β₁ β₀ β₂ ρ hij, Function.update_of_ne hij]
  have hV : (fun i => sqEichlerSub h j β₁ β₀ β₂ ρ (sqHandleIdxV i))
      = fun i => sqGen h (sqHandleIdxV i) := by
    funext i
    exact sqEichlerSub_handleV j β₁ β₀ β₂ ρ i
  rw [sqRelWord, hU, hV, sqEichlerSub_zero, sqEichlerSub_one, sqEichlerSub_two,
    handleWord_update_split]

/-- The relator of the *unmoved* marking, split at handle `j` — the right-hand side the
absorption lands on. -/
theorem sqRelWord_gen_resplit (h : ℕ) (j : Fin h) :
    sqWord (dsqSigma h) (dsqX0 h) (dsqX1 h)
      * (handlePrefix (fun i => sqGen h (sqHandleIdxU i))
            (fun i => sqGen h (sqHandleIdxV i)) (j : ℕ)
        * commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j))
        * handleSuffix (fun i => sqGen h (sqHandleIdxU i))
            (fun i => sqGen h (sqHandleIdxV i)) ((j : ℕ) + 1)) = 1 := by
  have hsplit := handleWord_split (fun i => sqGen h (sqHandleIdxU i))
    (fun i => sqGen h (sqHandleIdxV i)) j
  rw [← hsplit]
  exact dsq_relation h

/-- **The defect-route discharge**: if the core defect of the three-slot core substitution is
the `handlePrefix`-conjugate of `[v_j, ρ]^{u_j}`, the four-slot substitution kills the
relator.  This is the single named word identity the whole handle stratum now rests on. -/
theorem sqRelWord_sqEichlerSub_eq_one
    (hd : sqWord (dsqSigma h * β₁) (dsqX0 h * β₀) (dsqX1 h * β₂)
      = sqWord (dsqSigma h) (dsqX0 h) (dsqX1 h)
        * (handlePrefix (fun i => sqGen h (sqHandleIdxU i))
              (fun i => sqGen h (sqHandleIdxV i)) (j : ℕ)
          * conjP (commP (sqGen h (sqHandleIdxV j)) ρ) (sqGen h (sqHandleIdxU j))
          * (handlePrefix (fun i => sqGen h (sqHandleIdxU i))
              (fun i => sqGen h (sqHandleIdxV i)) (j : ℕ))⁻¹)) :
    sqRelWord (sqEichlerSub h j β₁ β₀ β₂ ρ) = 1 := by
  rw [sqRelWord_sqEichlerSub, sq_absorb (sqWord (dsqSigma h * β₁) (dsqX0 h * β₀) (dsqX1 h * β₂))
    (sqWord (dsqSigma h) (dsqX0 h) (dsqX1 h))
    (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j))
    (handlePrefix (fun i => sqGen h (sqHandleIdxU i))
      (fun i => sqGen h (sqHandleIdxV i)) (j : ℕ))
    (handleSuffix (fun i => sqGen h (sqHandleIdxU i))
      (fun i => sqGen h (sqHandleIdxV i)) ((j : ℕ) + 1)) ρ hd]
  exact sqRelWord_gen_resplit h j

end Scaffold

/-! ## §4 The seed, and the productions

`SqEichlerSeed` is the residual word-level obligation as *data*: the two-slot substitution,
its inverse substitution, and the four value facts (`β`, `ρ` χ-trivial; `β` row-invisible and
`ρ` of row `k·ν'(w)` against every marking meeting the `v_j`-row hypothesis).  A seed yields
the `(j,k)`-move by the `sqParamEquiv` assembly pattern: `sqLiftHom` on each substitution,
`dsq_leftInverse` on the generator checks, `continuousMulEquivOfBijective` to close. -/

section Seed

variable {h : ℕ}

/-- **The Eichler seed at `(h, c, j, k)`** — the single residual word-level input for the
`(j,k)`-move, as data.  `beta1`/`beta0`/`beta2`/`rho` drive the four-slot substitution
`σ ↦ σ·β₁`, `x₀ ↦ x₀·β₀`, `x₁ ↦ x₁·β₂`, `u_j ↦ ρ·u_j`; the `Inv` quadruple drives its
inverse; the two `rel_*` fields kill the relator (use `sqRelWord_sqEichlerSub_eq_one`); the
two `comp_*` fields verify the inverse on generators; the value fields feed χ-preservation
and the row conditions.  The §3 class-two balance predicts the leading classes
`β̄₁ = −k(2+c)·v̄_j`, `β̄₀ = −k·v̄_j`, `β̄₂ = −2k·v̄_j`, `ρ̄ = k·w̄ + a_u·v̄_j`; the `x₁`-slot
carries **no** `ν`-field because the target statement does not constrain the `x₁`-row (the
forced row makes it automatic). -/
structure SqEichlerSeed (h : ℕ) (c : ℤ_[2]) (j : Fin h) (k : ℤ_[2]) where
  /-- The σ-slot correction word (a `v̄_j`-class, `−k(2+c)` at first order). -/
  beta1 : (DSq h : Type)
  /-- The `x₀`-slot correction word (a `v̄_j`-class, `−k` at first order — the slot the
  class-two balance forces to move). -/
  beta0 : (DSq h : Type)
  /-- The `x₁`-slot correction word (a `v̄_j`-class, `−2k` at first order). -/
  beta2 : (DSq h : Type)
  /-- The `u_j`-slot shift word (of class `k·w̄` up to `v̄_j`). -/
  rho : (DSq h : Type)
  /-- The σ-slot word of the inverse substitution. -/
  beta1Inv : (DSq h : Type)
  /-- The `x₀`-slot word of the inverse substitution. -/
  beta0Inv : (DSq h : Type)
  /-- The `x₁`-slot word of the inverse substitution. -/
  beta2Inv : (DSq h : Type)
  /-- The `u_j`-slot word of the inverse substitution. -/
  rhoInv : (DSq h : Type)
  /-- The forward substitution kills the relator. -/
  rel_fwd : sqRelWord (sqEichlerSub h j beta1 beta0 beta2 rho) = 1
  /-- The backward substitution kills the relator. -/
  rel_bwd : sqRelWord (sqEichlerSub h j beta1Inv beta0Inv beta2Inv rhoInv) = 1
  /-- Forward after backward is the identity on generators. -/
  comp_fwd : ∀ i, sqLiftHom h (isProP_DSq h) (sqEichlerSub h j beta1 beta0 beta2 rho) rel_fwd
      (sqEichlerSub h j beta1Inv beta0Inv beta2Inv rhoInv i) = sqGen h i
  /-- Backward after forward is the identity on generators. -/
  comp_bwd : ∀ i, sqLiftHom h (isProP_DSq h)
      (sqEichlerSub h j beta1Inv beta0Inv beta2Inv rhoInv) rel_bwd
      (sqEichlerSub h j beta1 beta0 beta2 rho i) = sqGen h i
  /-- The σ-correction is χ-trivial. -/
  chi_beta1 : chiSq h beta1 = 1
  /-- The `x₀`-correction is χ-trivial. -/
  chi_beta0 : chiSq h beta0 = 1
  /-- The `x₁`-correction is χ-trivial. -/
  chi_beta2 : chiSq h beta2 = 1
  /-- The `u_j`-shift is χ-trivial. -/
  chi_rho : chiSq h rho = 1
  /-- The σ-correction is invisible to every marking meeting the `v_j`-row hypothesis. -/
  nu_beta1 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' beta1 = 1
  /-- The `x₀`-correction is invisible to every such marking. -/
  nu_beta0 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' beta0 = 1
  /-- The `u_j`-shift has row exactly `k·ν'(w)` against every such marking. -/
  nu_rho : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (sqGen h (sqHandleIdxV j)) = 1 →
        toAdd (nu' rho) = k * toAdd (nu' (sqMixPivotElem h c))

variable {c k : ℤ_[2]} {j : Fin h}

/-- The forward substitution of a seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqEichlerSeed.hom (S : SqEichlerSeed h c j k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqEichlerSub h j S.beta1 S.beta0 S.beta2 S.rho) S.rel_fwd

/-- The backward substitution of a seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqEichlerSeed.homInv (S : SqEichlerSeed h c j k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqEichlerSub h j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv)
    S.rel_bwd

@[simp] theorem SqEichlerSeed.hom_gen (S : SqEichlerSeed h c j k) (i : Fin (sqRank h)) :
    S.hom (sqGen h i) = sqEichlerSub h j S.beta1 S.beta0 S.beta2 S.rho i :=
  sqLiftHom_gen _ _ _ _ _

@[simp] theorem SqEichlerSeed.homInv_gen (S : SqEichlerSeed h c j k) (i : Fin (sqRank h)) :
    S.homInv (sqGen h i) = sqEichlerSub h j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv i :=
  sqLiftHom_gen _ _ _ _ _

/-- **The seed's automorphism**: the forward substitution is a continuous automorphism of
`D_sq`, with the backward substitution as two-sided inverse. -/
noncomputable def SqEichlerSeed.equiv (S : SqEichlerSeed h c j k) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  continuousMulEquivOfBijective S.hom (Function.bijective_iff_has_inverse.mpr
    ⟨S.homInv,
      dsq_leftInverse S.homInv S.hom fun i => by rw [S.hom_gen]; exact S.comp_bwd i,
      dsq_leftInverse S.hom S.homInv fun i => by rw [S.homInv_gen]; exact S.comp_fwd i⟩)

@[simp] theorem SqEichlerSeed.equiv_gen (S : SqEichlerSeed h c j k) (i : Fin (sqRank h)) :
    S.equiv (sqGen h i) = sqEichlerSub h j S.beta1 S.beta0 S.beta2 S.rho i :=
  S.hom_gen i

/-- **Seed to move**: a seed at `(h, c, j, k)` realizes the `(j, k)`-Eichler move. -/
theorem sqEichlerMoveAt_of_seed (S : SqEichlerSeed h c j k) : SqEichlerMoveAt h c j k := by
  intro nu' hv
  refine ⟨S.equiv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hext : (chiSq h).comp (autHom S.equiv) = chiSq h := by
      refine dsq_hom_ext _ _ fun i => ?_
      show chiSq h (S.equiv (sqGen h i)) = chiSq h (sqGen h i)
      rw [S.equiv_gen]
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
      · rw [sqEichlerSub_zero, map_mul, S.chi_beta1, mul_one]
        rfl
      · rw [sqEichlerSub_one, map_mul, S.chi_beta0, mul_one]
        rfl
      · rw [sqEichlerSub_two, map_mul, S.chi_beta2, mul_one]
        rfl
      · by_cases hjj : j' = j
        · subst hjj
          rw [sqEichlerSub_handleU_self, map_mul, S.chi_rho, one_mul]
        · rw [sqEichlerSub_handleU_of_ne j S.beta1 S.beta0 S.beta2 S.rho hjj]
      · rw [sqEichlerSub_handleV]
    exact fun x => DFunLike.congr_fun hext x
  · show nu' (S.equiv (sqGen h 0)) = nu' (dsqSigma h)
    rw [S.equiv_gen, sqEichlerSub_zero, map_mul, S.nu_beta1 nu' hv, mul_one]
  · show nu' (S.equiv (sqGen h 1)) = nu' (dsqX0 h)
    rw [S.equiv_gen, sqEichlerSub_one, map_mul, S.nu_beta0 nu' hv, mul_one]
  · rw [S.equiv_gen, sqEichlerSub_handleU_self, map_mul, toAdd_mul, S.nu_rho nu' hv]
    ring
  · intro i
    rw [S.equiv_gen, sqEichlerSub_handleV]
  · intro i hi
    rw [S.equiv_gen, sqEichlerSub_handleU_of_ne j S.beta1 S.beta0 S.beta2 S.rho hi]

/-- **The assembly**: seeds on the unit slice alone discharge the whole residual
obligation. -/
theorem sqHandleEichler_of_seeds {h : ℕ} {c : ℤ_[2]}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → Nonempty (SqEichlerSeed h c j k)) :
    SqHandleEichler h c :=
  sqHandleEichler_of_unit_moves fun j k hk => (H j k hk).elim fun S =>
    sqEichlerMoveAt_of_seed S

/-! ### Certificate-facing corollaries

The two reductions composed with `HandleMixFixesCore`'s
`sqHandleMixFixesCore_of_eichler`: the whole `L_sq` handle stratum, on unit moves or on
seeds alone. -/

/-- The one-binder handle stratum `SqHandleMixFixesCore`, from unit moves alone. -/
theorem sqHandleMixFixesCore_of_unit_moves {h : ℕ} {c : ℤ_[2]}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → SqEichlerMoveAt h c j k) :
    SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_eichler (sqHandleEichler_of_unit_moves H)

/-- The one-binder handle stratum `SqHandleMixFixesCore`, from seeds alone. -/
theorem sqHandleMixFixesCore_of_seeds {h : ℕ} {c : ℤ_[2]}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → Nonempty (SqEichlerSeed h c j k)) :
    SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_eichler (sqHandleEichler_of_seeds H)

end Seed

/-! ## §5 Stress pins

`h = 1` (the smallest instance with a handle) and the parameter arithmetic, per the lane
idiom: a later reshaping cannot silently become vacuous. -/

section StressTests

/-- The slice is faithful at one handle. -/
example (c : ℤ_[2]) :
    SqHandleEichler 1 c ↔ ∀ (j : Fin 1) (k : ℤ_[2]), SqEichlerMoveAt 1 c j k :=
  sqHandleEichler_iff_moveAt 1 c

/-- The zero-parameter move at one handle, at the canonical exponent. -/
example : SqEichlerMoveAt 1 sqPivotExp 0 0 := sqEichlerMoveAt_zero 1 sqPivotExp 0

/-- The parameter decomposition pin: `2 = 1 + 1` chains two unit moves. -/
example {c : ℤ_[2]} (H : SqEichlerMoveAt 1 c 0 1) : SqEichlerMoveAt 1 c 0 2 := by
  have h2 := sqEichlerMoveAt_add H H
  norm_num at h2
  exact h2

/-- The unit-slice reduction at one handle, at the canonical exponent. -/
example (H : ∀ (j : Fin 1) (k : ℤ_[2]), IsUnit k → SqEichlerMoveAt 1 sqPivotExp j k) :
    SqHandleEichler 1 sqPivotExp :=
  sqHandleEichler_of_unit_moves H

/-- Seeds at one handle produce the full family. -/
example (H : ∀ (j : Fin 1) (k : ℤ_[2]), IsUnit k → Nonempty (SqEichlerSeed 1 sqPivotExp j k)) :
    SqHandleEichler 1 sqPivotExp :=
  sqHandleEichler_of_seeds H

/-- The scaffold fixes the `v_j`-slot literally, at one handle — the slot the class-two
balance says never needs to move. -/
example (β₁ β₀ β₂ ρ : (DSq 1 : Type)) :
    sqEichlerSub 1 0 β₁ β₀ β₂ ρ (sqHandleIdxV 0) = sqGen 1 (sqHandleIdxV 0) :=
  sqEichlerSub_handleV 0 β₁ β₀ β₂ ρ 0

end StressTests

/-! ## §6 Axiom pins

Committed prints for the headline declarations: the whole file is **std-3**, with no census
axiom reachable.  Census unchanged at **11**. -/

section AxiomPins

#print axioms sqEichlerMoveAt_add
#print axioms sqHandleEichler_of_unit_moves
#print axioms sq_absorb
#print axioms sqWord_tau_sigma_defect
#print axioms sqRelWord_sqEichlerSub_eq_one
#print axioms sqEichlerMoveAt_of_seed
#print axioms sqHandleEichler_of_seeds
#print axioms sqHandleMixFixesCore_of_seeds

end AxiomPins

end SqCore

end Dyadic

end GQ2
