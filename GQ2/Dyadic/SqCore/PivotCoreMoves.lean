/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.JointClearing

/-!
# The pivot core family: its group law, the exact locus it occupies, and the seed interface

`SqCore/JointClearing.lean` reduced the oriented clearing residual `SqNuOrientedClear h` to the
two-parameter family `SqPivotCoreMove h m k` (plus, at `h ≥ 1`, the banked handle stratum and
one handle-to-core transfer per handle).  This file settles everything about that family that
is settleable without a word-level construction, and states the construction that remains.

## Contents

* **§1** `sqPivotDet m k = 1 + m − k·c₀`, the abelianized determinant, with
  `isUnit_sqPivotDet_iff : IsUnit (sqPivotDet m k) ↔ 2 ∣ m − k`.  The unit locus is a
  **parity** condition on `(m, k)`, and — see §4 — it is exactly the mod-two cup-form
  condition.
* **§2 The group law.**  `sqPivotCoreMove_comp` composes the `(m₁,k₁)`- and `(m₂,k₂)`-moves
  into the `(m₁ + m₂D₁, k₁ + k₂D₁)`-move, `D₁ = sqPivotDet m₁ k₁`, and
  `sqPivotDet_comp` shows determinants **multiply**.  In the coordinates `(D, k)` this is the
  affine group law `(D₁,k₁)·(D₂,k₂) = (D₁D₂, k₁ + k₂D₁)`, i.e. the family is
  `ℤ₂ˣ ⋉ ℤ₂ = Aff(ℤ₂)` — no Steinberg relation is needed, the group is metabelian.
* **§3 Two generators.**  `sqPivotCoreMove_of_translation_scaling`: every move with unit
  determinant is *one* translation followed by *one* scaling,

  ```text
  translation  Tr(c) = S(c·c₀, c)     (D = 1)     w ↦ w,    x₀ ↦ x₀·w^c,  x₁ ↦ x₁·w^{2c}
  scaling      Sc(a) = S(a − 1, 0)    (D = a)     w ↦ w^a,  x₀ ↦ x₀,      x₁ ↦ x₁
  ```

  where the displayed action is on the χ-trivial pivot `w = σ·x₀^{−c₀}`; both are literal
  one-parameter subgroups (`sqPivotTranslation_comp`, `sqPivotScaling_comp`), so the residual is
  two `sqParamEquiv`-shaped families rather than a two-parameter search.
* **§4 The determinant condition is necessary** (`isUnit_sqPivotDet_of_sqPivotCoreMove`): if the
  `(m,k)`-move exists at *any* handle count then `1 + m − k·c₀` is a unit.  So the family
  occupies **exactly** the affine group and the hypothesis of `sqCoreRows_of_pivotMove` is not an
  artifact.  The proof is the `chiSq² = X^{2λ}` parity engine of `JointClearing` §3 run at the
  standard marking, with the witness element `Ψ⁻¹(w)`: it is χ-trivial because `Ψ` preserves
  `χ_sq`, and its `ν_sq∘Ψ`-row is `1`.
* **§5** `toAdd_nu_aut_dsqX1`: the `x₁`-row of *any* automorphism realizing the move shifts by
  exactly `2k·ν'(w)` — the forced row `ν(x₁) = 2ν(x₀)` does the work, which is the precise sense
  in which the `x₁`-exponent `2k` "preserves the relator vector `x̄₁ − 2x̄₀`".
* **§6 The seed interface.**  `sqPivotSub` (the three-slot scaffold `σ ↦ σ·w^m·β₁`,
  `x₀ ↦ x₀·w^k·β₀`, `x₁ ↦ x₁·w^{2k}·β₂`, handle letters fixed), `SqPivotSeed h m k` as data, and
  `sqPivotCoreMove_of_seed`.  The seed's χ- and ν-fields ask the three corrections to be
  invisible to `χ_sq` **and to every** `ℤ₂`-marking, which is exactly the constraint a *uniform*
  `Ψ` faces (see the balance below).
* **§7** the assemblies `sqNuOrientedClear_zero_of_families` (the `h = 0` milestone shape) and
  `sqNuOrientedClear_of_families`, **§8** stress pins, **§9** axiom pins.

## The class-two balance of the pivot family (a finding of this file)

Write `W = σ⁻¹x₀σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ]`, i.e. `W = [σ,x₀]·x₀⁻⁴·x₁²·[x₁,[x₁,σ]]`, and compute in
`F/γ₃` for the free pro-2 group `F` on `σ, x₀, x₁` (the handle block is inert under this
family).  With `e₁ = [σ,x₀]`, `e₂ = [σ,x₁]`, `e₃ = [x₀,x₁]` and `w = σx₀^{−c}`:

```text
W               ≡ x₀⁻⁴x₁²·e₁
W(σw^m, x₀w^k, x₁w^{2k}) ≡ x₀⁻⁴x₁²·e₁^{D+10k}·e₂^{−6k}·e₃^{6kc}          (D = 1+m−kc)
defect          = (m − kc + 10k)·e₁ − 6k·e₂ + 6kc·e₃
```

and `⟨⟨W⟩⟩ ∩ γ₂F` reduces mod `γ₃F` to the span of `[−4x̄₀+2x̄₁, ḡ]`, namely
`ℤ₂(4e₁ − 2e₂) + ℤ₂(2e₃) ⊆ 2·γ₂F/γ₃F`.  Two consequences, both recorded because they shape the
remaining search:

1. **The three corrections are forced into the derived subgroup.**  A correction `β` must satisfy
   `χ_sq(β) = 1`; and `ν'(β) = 0` for the given marking.  On `D^ab = ℤ/2·t ⊕ ℤ₂σ̄ ⊕ ℤ₂x̄₀` one has
   `ker χ_sq = ℤ₂·w̄` (the torsion `t` has `χ_sq(t) = −1`), so as soon as `ν'(w)` is a unit the two
   conditions leave only `β̄ = 0`.  Hence no `β` contributes at class two through its degree-one
   part, and the `σ`-slot contributes nothing at all (`σ` has exponent sum `0` in `W`).
2. **What survives is exactly the determinant condition.**  The `x₀`- and `x₁`-slot corrections
   enter the class-two balance only through `β₀^{−4}` and `β₂^{2}`, i.e. through `−4β̄₀ + 2β̄₂`
   with `β̄₀, β̄₂` free in `γ₂F/γ₃F`.  So the balance is solvable iff the defect is even, i.e. iff
   `m − kc ≡ 0 (mod 2)`, i.e. iff `m ≡ k (mod 2)`, i.e. **iff `sqPivotDet m k` is a unit** —
   the same locus §4 proves necessary.  There is therefore **no class-two obstruction** anywhere
   on the determinant locus, and no refutation is available at this depth; at first order the
   `x₁`-slot correction is pinned to `β̄₂ = −5k·e₁ + 3k·e₂ − 3kc·e₃` modulo the span (take
   `β̄₀ = 0`), which is the leading datum a search should seed with.

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

/-! ## §1 The determinant of the pivot family -/

section Determinant

/-- **The abelianized determinant** of the pivot core move at `(m, k)`: the move sends the
core rows `(a, b)` to `(a + m·d, b + k·d)` with `d = a − c₀·b`, so the pivot row itself is
scaled by `1 + m − k·c₀`. -/
noncomputable def sqPivotDet (m k : ℤ_[2]) : ℤ_[2] := 1 + m - k * sqPivotExp

@[simp] theorem sqPivotDet_zero : sqPivotDet 0 0 = 1 := by
  rw [sqPivotDet]; ring

@[simp] theorem sqPivotDet_scaling (a : ℤ_[2]) : sqPivotDet (a - 1) 0 = a := by
  rw [sqPivotDet]; ring

@[simp] theorem sqPivotDet_translation (c : ℤ_[2]) : sqPivotDet (c * sqPivotExp) c = 1 := by
  rw [sqPivotDet]; ring

/-- **The unit locus is a parity condition**: `1 + m − k·c₀` is a unit exactly when `m` and `k`
have the same parity, `c₀` being a unit. -/
theorem isUnit_sqPivotDet_iff (m k : ℤ_[2]) :
    IsUnit (sqPivotDet m k) ↔ (2 : ℤ_[2]) ∣ m - k := by
  obtain ⟨e, he⟩ := two_dvd_sub_of_isUnit isUnit_sqPivotExp isUnit_one
  constructor
  · intro hu
    by_contra hc
    obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hc) isUnit_one
    exact (isUnit_iff_not_two_dvd.mp hu) ⟨1 + q - k * e, by
      rw [sqPivotDet]; linear_combination hq - k * he⟩
  · rintro ⟨u, hu⟩
    refine isUnit_iff_not_two_dvd.mpr fun hc => ?_
    obtain ⟨p, hp⟩ := hc
    exact (isUnit_iff_not_two_dvd.mp isUnit_one) ⟨p - u + k * e, by
      rw [sqPivotDet] at hp; linear_combination hp - hu + k * he⟩

end Determinant

/-! ## §2 The group law: the family is `Aff(ℤ₂)` -/

section GroupLaw

variable {h : ℕ}

/-- The identity is the move at `(0, 0)`. -/
theorem sqPivotCoreMove_zero : SqPivotCoreMove h 0 0 := by
  intro nu'
  refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl, ?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · show toAdd (nu' (dsqSigma h)) = _
    ring
  · show toAdd (nu' (dsqX0 h)) = _
    ring

/-- **The composition law.**  Running the `(m₁,k₁)`-move and then the `(m₂,k₂)`-move realizes
the `(m₁ + m₂D₁, k₁ + k₂D₁)`-move, where `D₁ = sqPivotDet m₁ k₁` is the factor by which the
first move scales the pivot row. -/
theorem sqPivotCoreMove_comp {m₁ k₁ m₂ k₂ : ℤ_[2]}
    (H₁ : SqPivotCoreMove h m₁ k₁) (H₂ : SqPivotCoreMove h m₂ k₂) :
    SqPivotCoreMove h (m₁ + m₂ * sqPivotDet m₁ k₁) (k₁ + k₂ * sqPivotDet m₁ k₁) := by
  intro nu'
  obtain ⟨Ψ₁, hchi₁, hs₁, hx₁, hU₁, hV₁⟩ := H₁ nu'
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₁) with hmudef
  have hmupiv : toAdd (mu (sqPivot h))
      = sqPivotDet m₁ k₁ * toAdd (nu' (sqPivot h)) := by
    show toAdd (nu' (Ψ₁ (sqPivot h))) = _
    rw [toAdd_aut_sqPivot, hs₁, hx₁, sqPivotDet, toAdd_nu_sqPivot]
    ring
  obtain ⟨Ψ₂, hchi₂, hs₂, hx₂, hU₂, hV₂⟩ := H₂ mu
  refine ⟨Ψ₂.trans Ψ₁, fun x => ?_, ?_, ?_, fun j => ?_, fun j => ?_⟩
  · show chiSq h (Ψ₁ (Ψ₂ x)) = chiSq h x
    rw [hchi₁, hchi₂]
  · show toAdd (mu (Ψ₂ (dsqSigma h))) = _
    rw [hs₂, hmupiv, show toAdd (mu (dsqSigma h)) = toAdd (nu' (Ψ₁ (dsqSigma h))) from rfl, hs₁]
    ring
  · show toAdd (mu (Ψ₂ (dsqX0 h))) = _
    rw [hx₂, hmupiv, show toAdd (mu (dsqX0 h)) = toAdd (nu' (Ψ₁ (dsqX0 h))) from rfl, hx₁]
    ring
  · show mu (Ψ₂ (sqGen h (sqHandleIdxU j))) = _
    rw [hU₂ j]
    exact hU₁ j
  · show mu (Ψ₂ (sqGen h (sqHandleIdxV j))) = _
    rw [hV₂ j]
    exact hV₁ j

/-- **Determinants multiply**: the group law of §2 is the affine one, `(D, k)`-coordinates. -/
theorem sqPivotDet_comp (m₁ k₁ m₂ k₂ : ℤ_[2]) :
    sqPivotDet (m₁ + m₂ * sqPivotDet m₁ k₁) (k₁ + k₂ * sqPivotDet m₁ k₁)
      = sqPivotDet m₁ k₁ * sqPivotDet m₂ k₂ := by
  simp only [sqPivotDet]
  ring

end GroupLaw

/-! ## §3 Two one-parameter generators -/

section Generators

variable {h : ℕ}

/-- **The scaling subfamily** `Sc(a)`: on the χ-trivial pivot it is `w ↦ w^a`, with `x₀` and
`x₁` fixed.  Its determinant is `a`. -/
def SqPivotScaling (h : ℕ) (a : ℤ_[2]) : Prop := SqPivotCoreMove h (a - 1) 0

/-- **The translation subfamily** `Tr(c)`: on the χ-trivial pivot it is `w ↦ w`,
`x₀ ↦ x₀·w^c`, `x₁ ↦ x₁·w^{2c}`.  Its determinant is `1`. -/
def SqPivotTranslation (h : ℕ) (c : ℤ_[2]) : Prop := SqPivotCoreMove h (c * sqPivotExp) c

/-- The scalings compose multiplicatively — a one-parameter subgroup over `ℤ₂ˣ`. -/
theorem sqPivotScaling_comp {a₁ a₂ : ℤ_[2]} (H₁ : SqPivotScaling h a₁)
    (H₂ : SqPivotScaling h a₂) : SqPivotScaling h (a₁ * a₂) := by
  have H : SqPivotCoreMove h (a₁ - 1 + (a₂ - 1) * sqPivotDet (a₁ - 1) 0)
      (0 + 0 * sqPivotDet (a₁ - 1) 0) := sqPivotCoreMove_comp H₁ H₂
  rw [sqPivotDet_scaling] at H
  have hm : a₁ - 1 + (a₂ - 1) * a₁ = a₁ * a₂ - 1 := by ring
  have hk : (0 : ℤ_[2]) + 0 * a₁ = 0 := by ring
  rw [hm, hk] at H
  exact H

/-- The translations compose additively — a one-parameter subgroup over `ℤ₂`. -/
theorem sqPivotTranslation_comp {c₁ c₂ : ℤ_[2]} (H₁ : SqPivotTranslation h c₁)
    (H₂ : SqPivotTranslation h c₂) : SqPivotTranslation h (c₁ + c₂) := by
  have H : SqPivotCoreMove h
      (c₁ * sqPivotExp + c₂ * sqPivotExp * sqPivotDet (c₁ * sqPivotExp) c₁)
      (c₁ + c₂ * sqPivotDet (c₁ * sqPivotExp) c₁) := sqPivotCoreMove_comp H₁ H₂
  rw [sqPivotDet_translation] at H
  have hm : c₁ * sqPivotExp + c₂ * sqPivotExp * 1 = (c₁ + c₂) * sqPivotExp := by ring
  have hk : c₁ + c₂ * 1 = c₁ + c₂ := by ring
  rw [hm, hk] at H
  exact H

/-- **Two generators suffice.**  Every pivot core move is one translation followed by one
scaling: `S(m, k) = Sc(D) ∘ Tr(k)` with `D = sqPivotDet m k`.  So the whole two-parameter family
reduces to the two one-parameter subgroups of §3. -/
theorem sqPivotCoreMove_of_translation_scaling (m k : ℤ_[2])
    (htr : SqPivotTranslation h k) (hsc : SqPivotScaling h (sqPivotDet m k)) :
    SqPivotCoreMove h m k := by
  have htr' : SqPivotCoreMove h (k * sqPivotExp) k := htr
  have hsc' : SqPivotCoreMove h (sqPivotDet m k - 1) 0 := hsc
  have H := sqPivotCoreMove_comp htr' hsc'
  rw [sqPivotDet_translation] at H
  have hm : k * sqPivotExp + (sqPivotDet m k - 1) * 1 = m := by
    rw [sqPivotDet]; ring
  have hk : k + 0 * 1 = k := by ring
  rw [hm, hk] at H
  exact H

end Generators

/-! ## §4 The determinant condition is necessary

The family occupies exactly the affine group: outside the unit locus there is **no**
χ-preserving automorphism with the prescribed rows, at any handle count.  The engine is
`JointClearing` §3 (`χ_sq² = X^{2λ}`), evaluated at the standard marking. -/

section Necessity

variable {h : ℕ}

/-- **Necessity of the determinant condition.**  If the `(m,k)`-pivot move exists then
`1 + m − k·c₀` is a unit.  Run the move at the standard marking `ν_sq`, whose pivot row is `1`
and whose handle rows vanish; the transported marking `μ = ν_sq ∘ Ψ` then has generator rows
`(1 + m, k, 2k, 0, …, 0)`.  If the determinant were even, `1 + m` and `k` would share a parity,
and in either case `μ` would be congruent modulo `2` either to `0` or to the χ-exponent row `λ`
on every generator — impossible at the χ-trivial element `Ψ⁻¹(w)`, whose `μ`-row is `1`. -/
theorem isUnit_sqPivotDet_of_sqPivotCoreMove {m k : ℤ_[2]}
    (H : SqPivotCoreMove h m k) : IsUnit (sqPivotDet m k) := by
  obtain ⟨Ψ, hchi, hs, hx, hU, hV⟩ := H (nuSq h)
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    (nuSq h).comp (autHom Ψ) with hmudef
  have hpiv : toAdd (nuSq h (sqPivot h)) = 1 := by rw [nuSq_sqPivot, toAdd_ofAdd]
  have hmus : toAdd (mu (sqGen h 0)) = 1 + m := by
    show toAdd (nuSq h (Ψ (dsqSigma h))) = 1 + m
    rw [hs, hpiv, nuSq_sigma, toAdd_ofAdd]
    ring
  have hmux : toAdd (mu (sqGen h 1)) = k := by
    show toAdd (nuSq h (Ψ (dsqX0 h))) = k
    rw [hx, hpiv, nuSq_x0, toAdd_ofAdd]
    ring
  have hmux1 : toAdd (mu (sqGen h 2)) = 2 * k := by
    show toAdd (mu (dsqX1 h)) = 2 * k
    rw [toAdd_nu_dsqX1 mu]
    show 2 * toAdd (mu (sqGen h 1)) = 2 * k
    rw [hmux]
  have hmuU : ∀ j : Fin h, toAdd (mu (sqGen h (sqHandleIdxU j))) = 0 := by
    intro j
    show toAdd (nuSq h (Ψ (sqGen h (sqHandleIdxU j)))) = 0
    rw [hU j, nuSq_handleU, toAdd_one]
  have hmuV : ∀ j : Fin h, toAdd (mu (sqGen h (sqHandleIdxV j))) = 0 := by
    intro j
    show toAdd (nuSq h (Ψ (sqGen h (sqHandleIdxV j)))) = 0
    rw [hV j, nuSq_handleV, toAdd_one]
  have hchig : chiSq h (Ψ.symm (sqPivot h)) = 1 := by
    have hh := hchi (Ψ.symm (sqPivot h))
    rw [Ψ.apply_symm_apply, chiSq_sqPivot] at hh
    exact hh.symm
  have hmug : toAdd (mu (Ψ.symm (sqPivot h))) = 1 := by
    show toAdd (nuSq h (Ψ (Ψ.symm (sqPivot h)))) = 1
    rw [Ψ.apply_symm_apply, nuSq_sqPivot, toAdd_ofAdd]
  by_contra hcon
  obtain ⟨p, hp⟩ : (2 : ℤ_[2]) ∣ sqPivotDet m k := by
    by_contra hc
    exact hcon (isUnit_iff_not_two_dvd.mpr hc)
  rw [sqPivotDet] at hp
  by_cases hkpar : (2 : ℤ_[2]) ∣ k
  · obtain ⟨t, ht⟩ := hkpar
    have hgen : ∀ i, (2 : ℤ_[2]) ∣ toAdd (mu (sqGen h i)) := by
      intro i
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨p + t * sqPivotExp, by rw [hmus]; linear_combination hp + sqPivotExp * ht⟩
      · exact ⟨t, by rw [hmux]; exact ht⟩
      · exact ⟨2 * t, by rw [hmux1, ht]⟩
      · exact ⟨0, by rw [hmuU j]; ring⟩
      · exact ⟨0, by rw [hmuV j]; ring⟩
    have hbad := two_dvd_toAdd_of_gen mu hgen (Ψ.symm (sqPivot h))
    rw [hmug] at hbad
    exact (isUnit_iff_not_two_dvd.mp isUnit_one) hbad
  · obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hkpar) isUnit_one
    have hgen : ∀ i, (2 : ℤ_[2]) ∣ toAdd (mu (sqGen h i)) - toAdd (nuLam h (sqGen h i)) := by
      intro i
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · refine ⟨p + sqPivotExp * q, ?_⟩
        rw [hmus, show sqGen h 0 = dsqSigma h from rfl, nuLam_sigma, toAdd_ofAdd]
        linear_combination hp + sqPivotExp * hq
      · refine ⟨q, ?_⟩
        rw [hmux, show sqGen h 1 = dsqX0 h from rfl, nuLam_x0, toAdd_ofAdd]
        linear_combination hq
      · refine ⟨2 * q, ?_⟩
        rw [hmux1, show sqGen h 2 = dsqX1 h from rfl, nuLam_x1, toAdd_ofAdd]
        linear_combination 2 * hq
      · exact ⟨0, by rw [hmuU j, nuLam_handleU, toAdd_one]; ring⟩
      · exact ⟨0, by rw [hmuV j, nuLam_handleV, toAdd_one]; ring⟩
    obtain ⟨r, hr⟩ := two_dvd_toAdd_sub_of_gen mu (nuLam h) hgen (Ψ.symm (sqPivot h))
    obtain ⟨l, hl⟩ := two_dvd_toAdd_nuLam_of_chiSq_eq_one hchig
    exact (isUnit_iff_not_two_dvd.mp isUnit_one) ⟨r + l, by linear_combination hr + hl - hmug⟩

/-- The move exists only on the parity locus `m ≡ k (mod 2)`. -/
theorem two_dvd_sub_of_sqPivotCoreMove {m k : ℤ_[2]} (H : SqPivotCoreMove h m k) :
    (2 : ℤ_[2]) ∣ m - k :=
  (isUnit_sqPivotDet_iff m k).mp (isUnit_sqPivotDet_of_sqPivotCoreMove H)

end Necessity

/-! ## §5 The `x₁`-row is forced -/

section ForcedRow

variable {h : ℕ}

/-- **The `x₁`-exponent `2k` is not a choice.**  For *any* automorphism realizing the `(m,k)`
core rows against a marking, the `x₁`-row moves by exactly `2k·ν'(w)` — the forced row
`ν(x₁) = 2ν(x₀)` of the improved relator does it, with no hypothesis on `Ψ` beyond being a
continuous endomorphism.  This is the precise content of "`2k` is the exponent preserving the
relator vector `x̄₁ − 2x̄₀`". -/
theorem toAdd_nu_aut_dsqX1 (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) {k : ℤ_[2]}
    (hx : toAdd (nu' (Ψ (dsqX0 h))) = toAdd (nu' (dsqX0 h)) + k * toAdd (nu' (sqPivot h))) :
    toAdd (nu' (Ψ (dsqX1 h)))
      = toAdd (nu' (dsqX1 h)) + 2 * k * toAdd (nu' (sqPivot h)) := by
  have hone := toAdd_nu_dsqX1 (nu'.comp (autHom Ψ))
  have htwo := toAdd_nu_dsqX1 nu'
  rw [show ((nu'.comp (autHom Ψ)) (dsqX1 h)) = nu' (Ψ (dsqX1 h)) from rfl,
    show ((nu'.comp (autHom Ψ)) (dsqX0 h)) = nu' (Ψ (dsqX0 h)) from rfl, hx] at hone
  rw [hone, htwo]
  ring

end ForcedRow

/-! ## §6 The seed interface

The word-level residual, as data.  The scaffold dresses the three core letters by powers of the
χ-trivial pivot together with one correction each, and fixes every handle letter literally —
the shape §4 shows is forced on the abelianization. -/

section Scaffold

variable {h : ℕ}

/-- **The three-slot pivot substitution scaffold**: `σ ↦ σ·w^m·β₁`, `x₀ ↦ x₀·w^k·β₀`,
`x₁ ↦ x₁·w^{2k}·β₂`, every handle letter fixed. -/
noncomputable def sqPivotSub (h : ℕ) (m k : ℤ_[2]) (β₁ β₀ β₂ : (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  Function.update (Function.update (Function.update (sqGen h)
      0 (dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) m * β₁))
      1 (dsqX0 h * zpowZtwo (isProP_DSq h) (sqPivot h) k * β₀))
      2 (dsqX1 h * zpowZtwo (isProP_DSq h) (sqPivot h) (2 * k) * β₂)

variable (m k : ℤ_[2]) (β₁ β₀ β₂ : (DSq h : Type))

@[simp] theorem sqPivotSub_zero : sqPivotSub h m k β₁ β₀ β₂ 0
    = dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) m * β₁ := by
  rw [sqPivotSub, Function.update_of_ne (Ne.symm (sqFin_two_ne_zero h)),
    Function.update_of_ne (Ne.symm (sqFin_one_ne_zero h)), Function.update_self]

@[simp] theorem sqPivotSub_one : sqPivotSub h m k β₁ β₀ β₂ 1
    = dsqX0 h * zpowZtwo (isProP_DSq h) (sqPivot h) k * β₀ := by
  rw [sqPivotSub, Function.update_of_ne (Ne.symm (sqFin_two_ne_one h)), Function.update_self]

@[simp] theorem sqPivotSub_two : sqPivotSub h m k β₁ β₀ β₂ 2
    = dsqX1 h * zpowZtwo (isProP_DSq h) (sqPivot h) (2 * k) * β₂ := by
  rw [sqPivotSub, Function.update_self]

@[simp] theorem sqPivotSub_handleU (i : Fin h) :
    sqPivotSub h m k β₁ β₀ β₂ (sqHandleIdxU i) = sqGen h (sqHandleIdxU i) := by
  rw [sqPivotSub, Function.update_of_ne (sqHandleIdxU_ne_of_val_lt i (by rw [sqVal_two]; omega)),
    Function.update_of_ne (sqHandleIdxU_ne_of_val_lt i (by rw [sqVal_one]; omega)),
    Function.update_of_ne (sqHandleIdxU_ne_of_val_lt i (by rw [sqVal_zero]; omega))]

@[simp] theorem sqPivotSub_handleV (i : Fin h) :
    sqPivotSub h m k β₁ β₀ β₂ (sqHandleIdxV i) = sqGen h (sqHandleIdxV i) := by
  rw [sqPivotSub, Function.update_of_ne (sqHandleIdxV_ne_of_val_lt i (by rw [sqVal_two]; omega)),
    Function.update_of_ne (sqHandleIdxV_ne_of_val_lt i (by rw [sqVal_one]; omega)),
    Function.update_of_ne (sqHandleIdxV_ne_of_val_lt i (by rw [sqVal_zero]; omega))]

/-- At the trivial parameters and trivial corrections the scaffold is the standard marking. -/
theorem sqPivotSub_id : sqPivotSub h 0 0 1 1 1 = sqGen h := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [sqPivotSub_zero, zpowZtwo_zero_exp, mul_one, mul_one]
    rfl
  · rw [sqPivotSub_one, zpowZtwo_zero_exp, mul_one, mul_one]
    rfl
  · rw [sqPivotSub_two, mul_zero, zpowZtwo_zero_exp, mul_one, mul_one]
    rfl
  · rw [sqPivotSub_handleU]
  · rw [sqPivotSub_handleV]

end Scaffold

section Seed

variable {h : ℕ}

/-- **The pivot seed at `(h, m, k)`** — the residual word-level input, as data.  `beta1`,
`beta0`, `beta2` drive the three-slot scaffold; `inv` is *any* marking inverting it on
generators; the three χ-fields and the three ν-fields say the corrections are invisible to
`χ_sq` and to every `ℤ₂`-marking, i.e. that they lie in the closed derived subgroup — the exact
constraint a uniform correction faces (module docstring, balance item 1). -/
structure SqPivotSeed (h : ℕ) (m k : ℤ_[2]) where
  /-- The `σ`-slot correction word. -/
  beta1 : (DSq h : Type)
  /-- The `x₀`-slot correction word. -/
  beta0 : (DSq h : Type)
  /-- The `x₁`-slot correction word (the slot the class-two balance pins first). -/
  beta2 : (DSq h : Type)
  /-- The inverse substitution, as a marking. -/
  inv : Fin (sqRank h) → (DSq h : Type)
  /-- The forward substitution kills the relator. -/
  rel_fwd : sqRelWord (sqPivotSub h m k beta1 beta0 beta2) = 1
  /-- The inverse substitution kills the relator. -/
  rel_inv : sqRelWord inv = 1
  /-- Forward after backward is the identity on generators. -/
  comp_fwd : ∀ i, sqLiftHom h (isProP_DSq h) (sqPivotSub h m k beta1 beta0 beta2) rel_fwd
      (inv i) = sqGen h i
  /-- Backward after forward is the identity on generators. -/
  comp_bwd : ∀ i, sqLiftHom h (isProP_DSq h) inv rel_inv
      (sqPivotSub h m k beta1 beta0 beta2 i) = sqGen h i
  /-- The `σ`-correction is χ-trivial. -/
  chi_beta1 : chiSq h beta1 = 1
  /-- The `x₀`-correction is χ-trivial. -/
  chi_beta0 : chiSq h beta0 = 1
  /-- The `x₁`-correction is χ-trivial. -/
  chi_beta2 : chiSq h beta2 = 1
  /-- The `σ`-correction is invisible to every marking. -/
  nu_beta1 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]), nu' beta1 = 1
  /-- The `x₀`-correction is invisible to every marking. -/
  nu_beta0 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]), nu' beta0 = 1
  /-- The `x₁`-correction is invisible to every marking. -/
  nu_beta2 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]), nu' beta2 = 1

variable {m k : ℤ_[2]}

/-- The forward substitution of a pivot seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqPivotSeed.hom (S : SqPivotSeed h m k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqPivotSub h m k S.beta1 S.beta0 S.beta2) S.rel_fwd

/-- The inverse substitution of a pivot seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqPivotSeed.homInv (S : SqPivotSeed h m k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) S.inv S.rel_inv

@[simp] theorem SqPivotSeed.hom_gen (S : SqPivotSeed h m k) (i : Fin (sqRank h)) :
    S.hom (sqGen h i) = sqPivotSub h m k S.beta1 S.beta0 S.beta2 i :=
  sqLiftHom_gen _ _ _ _ _

@[simp] theorem SqPivotSeed.homInv_gen (S : SqPivotSeed h m k) (i : Fin (sqRank h)) :
    S.homInv (sqGen h i) = S.inv i :=
  sqLiftHom_gen _ _ _ _ _

/-- **The pivot seed's automorphism.** -/
noncomputable def SqPivotSeed.equiv (S : SqPivotSeed h m k) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  continuousMulEquivOfBijective S.hom (Function.bijective_iff_has_inverse.mpr
    ⟨S.homInv,
      dsq_leftInverse S.homInv S.hom fun i => by rw [S.hom_gen]; exact S.comp_bwd i,
      dsq_leftInverse S.hom S.homInv fun i => by rw [S.homInv_gen]; exact S.comp_fwd i⟩)

@[simp] theorem SqPivotSeed.equiv_gen (S : SqPivotSeed h m k) (i : Fin (sqRank h)) :
    S.equiv (sqGen h i) = sqPivotSub h m k S.beta1 S.beta0 S.beta2 i :=
  S.hom_gen i

/-- **Seed to move**: a pivot seed at `(h, m, k)` realizes the `(m,k)`-pivot core move. -/
theorem sqPivotCoreMove_of_seed (S : SqPivotSeed h m k) : SqPivotCoreMove h m k := by
  intro nu'
  refine ⟨S.equiv, ?_, ?_, ?_, fun j => ?_, fun j => ?_⟩
  · have hext : (chiSq h).comp (autHom S.equiv) = chiSq h := by
      refine dsq_hom_ext _ _ fun i => ?_
      show chiSq h (S.equiv (sqGen h i)) = chiSq h (sqGen h i)
      rw [S.equiv_gen]
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [sqPivotSub_zero, map_mul, map_mul, S.chi_beta1, mul_one,
          map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_sqPivot,
          zpowZtwo_one_base, mul_one]
        rfl
      · rw [sqPivotSub_one, map_mul, map_mul, S.chi_beta0, mul_one,
          map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_sqPivot,
          zpowZtwo_one_base, mul_one]
        rfl
      · rw [sqPivotSub_two, map_mul, map_mul, S.chi_beta2, mul_one,
          map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_sqPivot,
          zpowZtwo_one_base, mul_one]
        rfl
      · rw [sqPivotSub_handleU]
      · rw [sqPivotSub_handleV]
    exact fun x => DFunLike.congr_fun hext x
  · have hval : nu' (S.equiv (sqGen h 0))
        = nu' (dsqSigma h) * nu' (zpowZtwo (isProP_DSq h) (sqPivot h) m) := by
      rw [S.equiv_gen, sqPivotSub_zero, map_mul, map_mul, S.nu_beta1 nu', mul_one]
    show toAdd (nu' (S.equiv (sqGen h 0))) = _
    rw [hval, toAdd_mul, toAdd_map_zpowZtwo (isProP_DSq h) nu' (sqPivot h) m]
  · have hval : nu' (S.equiv (sqGen h 1))
        = nu' (dsqX0 h) * nu' (zpowZtwo (isProP_DSq h) (sqPivot h) k) := by
      rw [S.equiv_gen, sqPivotSub_one, map_mul, map_mul, S.nu_beta0 nu', mul_one]
    show toAdd (nu' (S.equiv (sqGen h 1))) = _
    rw [hval, toAdd_mul, toAdd_map_zpowZtwo (isProP_DSq h) nu' (sqPivot h) k]
  · rw [S.equiv_gen, sqPivotSub_handleU]
  · rw [S.equiv_gen, sqPivotSub_handleV]

end Seed

/-! ## §7 The assemblies -/

section Assembly

/-- **The `h = 0` milestone shape.**  At `h = 0` the handle stratum is empty, so the two
one-parameter families of §3 *alone* discharge the oriented clearing residual. -/
theorem sqNuOrientedClear_zero_of_families
    (htr : ∀ c : ℤ_[2], SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 0 a) : SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_pivotMoves fun m k hunit =>
    sqPivotCoreMove_of_translation_scaling m k (htr k) (hsc _ hunit)

/-- The same at every handle count, over the banked handle stratum and the transfers. -/
theorem sqNuOrientedClear_of_families {h : ℕ} (hfix : SqHandleMixFixesCore h sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling h a)
    (hmixU : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxU j))
    (hmixV : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxV j)) : SqNuOrientedClear h :=
  sqNuOrientedClear_of_moves hfix
    (fun m k hunit => sqPivotCoreMove_of_translation_scaling m k (htr k) (hsc _ hunit))
    hmixU hmixV

/-- Seeds on the two generating families discharge the residual at `h = 0`. -/
theorem sqNuOrientedClear_zero_of_seeds
    (htr : ∀ c : ℤ_[2], Nonempty (SqPivotSeed 0 (c * sqPivotExp) c))
    (hsc : ∀ a : ℤ_[2], IsUnit a → Nonempty (SqPivotSeed 0 (a - 1) 0)) :
    SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_families
    (fun c => (htr c).elim fun S => sqPivotCoreMove_of_seed S)
    (fun a ha => (hsc a ha).elim fun S => sqPivotCoreMove_of_seed S)

end Assembly

/-! ## §8 Stress pins -/

section StressTests

/-- The two subfamilies sit at the advertised determinants. -/
example (a c : ℤ_[2]) : sqPivotDet (a - 1) 0 = a ∧ sqPivotDet (c * sqPivotExp) c = 1 :=
  ⟨sqPivotDet_scaling a, sqPivotDet_translation c⟩

/-- The identity move is in the family, at determinant `1`. -/
example : SqPivotCoreMove 1 0 0 ∧ IsUnit (sqPivotDet 0 0) :=
  ⟨sqPivotCoreMove_zero, by rw [sqPivotDet_zero]; exact isUnit_one⟩

/-- Composition at one handle, spelled at the determinant level. -/
example (m₁ k₁ m₂ k₂ : ℤ_[2]) (H₁ : SqPivotCoreMove 1 m₁ k₁) (H₂ : SqPivotCoreMove 1 m₂ k₂) :
    SqPivotCoreMove 1 (m₁ + m₂ * sqPivotDet m₁ k₁) (k₁ + k₂ * sqPivotDet m₁ k₁) :=
  sqPivotCoreMove_comp H₁ H₂

/-- The determinant locus is exactly the parity locus, and it is forced. -/
example (m k : ℤ_[2]) (H : SqPivotCoreMove 0 m k) : (2 : ℤ_[2]) ∣ m - k :=
  two_dvd_sub_of_sqPivotCoreMove H

/-- The move at `(1, 0)` needs `2 ∣ 1`, so it does **not** exist: the parity locus is a genuine
restriction, not a bookkeeping hypothesis. -/
example : ¬ SqPivotCoreMove 0 1 0 := fun H =>
  (isUnit_iff_not_two_dvd.mp isUnit_one) (by simpa using two_dvd_sub_of_sqPivotCoreMove H)

/-- The scaffold at trivial data is the standard marking, so the seed family is non-vacuous in
shape. -/
example : sqPivotSub 1 0 0 1 1 1 = sqGen 1 := sqPivotSub_id

/-- A seed produces the move. -/
example (S : SqPivotSeed 1 0 0) : SqPivotCoreMove 1 0 0 := sqPivotCoreMove_of_seed S

/-- The `h = 0` milestone, spelled over the two families. -/
example (htr : ∀ c : ℤ_[2], SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 0 a) : SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_families htr hsc

end StressTests

/-! ## §9 Axiom pins -/

section AxiomPins

#print axioms sqPivotDet
#print axioms isUnit_sqPivotDet_iff
#print axioms sqPivotCoreMove_zero
#print axioms sqPivotCoreMove_comp
#print axioms sqPivotDet_comp
#print axioms sqPivotScaling_comp
#print axioms sqPivotTranslation_comp
#print axioms sqPivotCoreMove_of_translation_scaling
#print axioms isUnit_sqPivotDet_of_sqPivotCoreMove
#print axioms two_dvd_sub_of_sqPivotCoreMove
#print axioms toAdd_nu_aut_dsqX1
#print axioms sqPivotSub_zero
#print axioms sqPivotSub_id
#print axioms SqPivotSeed.equiv_gen
#print axioms sqPivotCoreMove_of_seed
#print axioms sqNuOrientedClear_zero_of_families
#print axioms sqNuOrientedClear_of_families
#print axioms sqNuOrientedClear_zero_of_seeds

end AxiomPins

end SqCore

end Dyadic

end GQ2
