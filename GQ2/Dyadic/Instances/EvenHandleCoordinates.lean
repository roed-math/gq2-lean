/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.LHandleCoordinates
import GQ2.Dyadic.Certificates.M0

/-!
# Core and handle coordinates for the even-degree alphabet

`LHandleCoordinates` splits the odd alphabet `Generator (2h + 1)` into its four-letter
degree-one core and `h` ordered handle pairs.  The two compact even rows live on
`Generator (2 + 2h)`, whose wild letters are `x₀, x₁, x₂` followed by the same `h` handle
pairs at indices `3 + 2j` and `4 + 2j`.  This file records the corresponding decomposition

`Generator (2 + 2h) ≃ Generator 2 ⊕ (Fin h × Fin 2)`

together with the core marking, the core restriction of an offset vector, and the additive
coordinate equivalence.  The handle-side factor is the *same* `Fin h × Fin 2` the odd row uses,
so `lSqHandleHyperbolicAddEquiv` and the middle-stabilization machinery apply unchanged.

The last section supplies the missing per-family Stokes pairing bridge for the compact-`M` row,
the twin of `Certificates.heisEta1_nCompactFam_apply`.
-/

namespace GQ2.Dyadic.EvenCore

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates

/-! ## The core embedding -/

/-- The degree-`2` alphabet inside the degree-`2 + 2h` one: `σ ↦ σ`, `τ ↦ τ`, `x_i ↦ x_i`
for `i < 3`. -/
def coreEmbed (h : ℕ) : Generator 2 → Generator (2 + 2 * h)
  | .sigma => .sigma
  | .tau => .tau
  | .wild i => coreLetter h i

@[simp] theorem coreEmbed_sigma (h : ℕ) : coreEmbed h .sigma = .sigma := rfl
@[simp] theorem coreEmbed_tau (h : ℕ) : coreEmbed h .tau = .tau := rfl
@[simp] theorem coreEmbed_wild (h : ℕ) (i : Fin 3) :
    coreEmbed h (.wild i) = coreLetter h i := rfl

/-- At `h = 0` the embedding is the identity: the degree-`2` alphabet is its own core. -/
theorem coreEmbed_zero : coreEmbed 0 = id := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => exact congrArg Generator.wild (Fin.ext rfl)

theorem coreEmbed_injective (h : ℕ) : Function.Injective (coreEmbed h) := by
  intro g₁ g₂ hg
  cases g₁ <;> cases g₂ <;>
    simp_all [coreEmbed, coreLetter, Generator.wild.injEq, Fin.ext_iff]

/-- No handle letter is in the image of the core embedding — the `u`-half. -/
theorem coreEmbed_ne_handleU {h : ℕ} (g : Generator 2) (j : Fin h) :
    coreEmbed h g ≠ handleU j := by
  cases g with
  | sigma => simp [coreEmbed, handleU]
  | tau => simp [coreEmbed, handleU]
  | wild i =>
      have hi := i.isLt
      simp only [coreEmbed_wild, coreLetter, handleU, ne_eq, Generator.wild.injEq, Fin.ext_iff]
      omega

/-- No handle letter is in the image of the core embedding — the `v`-half. -/
theorem coreEmbed_ne_handleV {h : ℕ} (g : Generator 2) (j : Fin h) :
    coreEmbed h g ≠ handleV j := by
  cases g with
  | sigma => simp [coreEmbed, handleV]
  | tau => simp [coreEmbed, handleV]
  | wild i =>
      have hi := i.isLt
      simp only [coreEmbed_wild, coreLetter, handleV, ne_eq, Generator.wild.injEq, Fin.ext_iff]
      omega

variable {h : ℕ} {C : Type*}

/-- The even-degree marking restricted to the core letters — a genuine degree-`2` marking. -/
def coreMarking (t : Marking (2 + 2 * h) C) : Marking 2 C := ⟨fun g => t (coreEmbed h g)⟩

@[simp] theorem coreMarking_apply (t : Marking (2 + 2 * h) C) (g : Generator 2) :
    coreMarking t g = t (coreEmbed h g) := rfl

@[simp] theorem coreMarking_sigma (t : Marking (2 + 2 * h) C) :
    (coreMarking t).σ = t.σ := rfl

@[simp] theorem coreMarking_tau (t : Marking (2 + 2 * h) C) :
    (coreMarking t).τ = t.τ := rfl

@[simp] theorem coreMarking_x (t : Marking (2 + 2 * h) C) (i : Fin 3) :
    (coreMarking t).x i = t (coreLetter h i) := rfl

/-- Restriction of an offset vector along the core embedding — the map that forgets exactly the
`2h` handle coordinates. -/
def coreRestrict (h : ℕ) (V : Type*) [AddCommGroup V] :
    ((Generator (2 + 2 * h) → V) →+ (Generator 2 → V)) :=
  AddMonoidHom.mk' (fun a => a ∘ coreEmbed h) fun _ _ => rfl

@[simp] theorem coreRestrict_apply {V : Type*} [AddCommGroup V]
    (a : Generator (2 + 2 * h) → V) (g : Generator 2) :
    coreRestrict h V a g = a (coreEmbed h g) := rfl

@[simp] theorem coreRestrict_coreLetter {V : Type*} [AddCommGroup V]
    (a : Generator (2 + 2 * h) → V) (i : Fin 3) :
    coreRestrict h V a (.wild i) = a (coreLetter h i) := rfl

@[simp] theorem coreRestrict_sigma {V : Type*} [AddCommGroup V]
    (a : Generator (2 + 2 * h) → V) : coreRestrict h V a .sigma = a .sigma := rfl

@[simp] theorem coreRestrict_tau {V : Type*} [AddCommGroup V]
    (a : Generator (2 + 2 * h) → V) : coreRestrict h V a .tau = a .tau := rfl

/-- The core marking inherits the wild-triviality hypothesis. -/
theorem coreMarking_hwild [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (i : Fin (2 + 1)) (v : V) : (coreMarking t).x i • v = v := by
  rw [coreMarking_x]
  exact hwild _ v

/-! ## The alphabet decomposition -/

/-- Split the `2h + 3` wild indices into the three core indices and `h` ordered pairs. -/
def wildEquiv (h : ℕ) : Fin (2 + 2 * h + 1) ≃ Fin 3 ⊕ (Fin h × Fin 2) :=
  (finCongr (by omega)).trans <|
    finSumFinEquiv.symm.trans <|
      (Equiv.refl (Fin 3)).sumCongr finProdFinEquiv.symm

@[simp] theorem wildEquiv_zero (h : ℕ) :
    wildEquiv h ⟨0, by omega⟩ = Sum.inl 0 := by
  rw [wildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 + 2 * h + 1 = 3 + h * 2 by omega)) ⟨0, by omega⟩
      = Fin.castAdd (h * 2) (0 : Fin 3) := by apply Fin.ext; rfl
  rw [hc]
  rfl

@[simp] theorem wildEquiv_one (h : ℕ) :
    wildEquiv h ⟨1, by omega⟩ = Sum.inl 1 := by
  rw [wildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 + 2 * h + 1 = 3 + h * 2 by omega)) ⟨1, by omega⟩
      = Fin.castAdd (h * 2) (1 : Fin 3) := by apply Fin.ext; rfl
  rw [hc]
  rfl

@[simp] theorem wildEquiv_two (h : ℕ) :
    wildEquiv h ⟨2, by omega⟩ = Sum.inl 2 := by
  rw [wildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 + 2 * h + 1 = 3 + h * 2 by omega)) ⟨2, by omega⟩
      = Fin.castAdd (h * 2) (2 : Fin 3) := by apply Fin.ext; rfl
  rw [hc]
  rfl

@[simp] theorem wildEquiv_handleU {h : ℕ} (j : Fin h) :
    wildEquiv h ⟨3 + 2 * (j : ℕ), by omega⟩ = Sum.inr (j, 0) := by
  rw [wildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 + 2 * h + 1 = 3 + h * 2 by omega))
        ⟨3 + 2 * (j : ℕ), by omega⟩ = Fin.natAdd 3 (finProdFinEquiv (j, 0)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
  rw [hc]
  simp

@[simp] theorem wildEquiv_handleV {h : ℕ} (j : Fin h) :
    wildEquiv h ⟨4 + 2 * (j : ℕ), by omega⟩ = Sum.inr (j, 1) := by
  rw [wildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 + 2 * h + 1 = 3 + h * 2 by omega))
        ⟨4 + 2 * (j : ℕ), by omega⟩ = Fin.natAdd 3 (finProdFinEquiv (j, 1)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  rw [hc]
  simp

/-- The even alphabet is its degree-`2` core plus the ordered handle coordinates. -/
def alphabetEquiv (h : ℕ) :
    Generator (2 + 2 * h) ≃ Generator 2 ⊕ (Fin h × Fin 2) :=
  (Generator.equivSum (2 + 2 * h)).trans <|
    ((Equiv.refl Bool).sumCongr (wildEquiv h)).trans <|
      (Equiv.sumAssoc Bool (Fin 3) (Fin h × Fin 2)).symm |>.trans <|
        (Generator.equivSum 2).symm.sumCongr (Equiv.refl _)

@[simp] theorem alphabetEquiv_core (h : ℕ) (g : Generator 2) :
    alphabetEquiv h (coreEmbed h g) = Sum.inl g := by
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => fin_cases i <;> rfl

@[simp] theorem alphabetEquiv_handleU {h : ℕ} (j : Fin h) :
    alphabetEquiv h (handleU j) = Sum.inr (j, 0) := by
  change Sum.map (Generator.equivSum 2).symm id
    ((Equiv.sumAssoc Bool (Fin 3) (Fin h × Fin 2)).symm
      (Sum.inr (wildEquiv h ⟨3 + 2 * (j : ℕ), by omega⟩))) = _
  rw [wildEquiv_handleU]
  rfl

@[simp] theorem alphabetEquiv_handleV {h : ℕ} (j : Fin h) :
    alphabetEquiv h (handleV j) = Sum.inr (j, 1) := by
  change Sum.map (Generator.equivSum 2).symm id
    ((Equiv.sumAssoc Bool (Fin 3) (Fin h × Fin 2)).symm
      (Sum.inr (wildEquiv h ⟨4 + 2 * (j : ℕ), by omega⟩))) = _
  rw [wildEquiv_handleV]
  rfl

/-- Additive core/handle coordinates on even-degree offset vectors.  Its handle factor is the
same `Fin h × Fin 2` the odd row uses, so the hyperbolic handle equivalence and the
middle-stabilization transport apply verbatim. -/
def coreHandleAddEquiv (h : ℕ) (A : Type*) [AddCommGroup A] :
    (Generator (2 + 2 * h) → A) ≃+ (Generator 2 → A) × (Fin h × Fin 2 → A) :=
  (AddEquiv.arrowCongr (alphabetEquiv h) (AddEquiv.refl A)).trans
    (sumArrowAddEquiv (Generator 2) (Fin h × Fin 2) A)

@[simp] theorem coreHandleAddEquiv_fst (h : ℕ) (A : Type*) [AddCommGroup A]
    (x : Generator (2 + 2 * h) → A) :
    (coreHandleAddEquiv h A x).1 = coreRestrict h A x := by
  funext g
  change x ((alphabetEquiv h).symm (Sum.inl g)) = x (coreEmbed h g)
  congr 1
  apply (alphabetEquiv h).injective
  rw [(alphabetEquiv h).apply_symm_apply, alphabetEquiv_core]

@[simp] theorem coreHandleAddEquiv_snd_zero (h : ℕ) (A : Type*) [AddCommGroup A]
    (x : Generator (2 + 2 * h) → A) (j : Fin h) :
    (coreHandleAddEquiv h A x).2 (j, 0) = x (handleU j) := by
  change x ((alphabetEquiv h).symm (Sum.inr (j, 0))) = _
  congr 1
  apply (alphabetEquiv h).injective
  rw [(alphabetEquiv h).apply_symm_apply, alphabetEquiv_handleU]

@[simp] theorem coreHandleAddEquiv_snd_one (h : ℕ) (A : Type*) [AddCommGroup A]
    (x : Generator (2 + 2 * h) → A) (j : Fin h) :
    (coreHandleAddEquiv h A x).2 (j, 1) = x (handleV j) := by
  change x ((alphabetEquiv h).symm (Sum.inr (j, 1))) = _
  congr 1
  apply (alphabetEquiv h).injective
  rw [(alphabetEquiv h).apply_symm_apply, alphabetEquiv_handleV]

end GQ2.Dyadic.EvenCore

namespace GQ2.Dyadic.Certificates.MCompact

open GQ2 GQ2.FoxH GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Certificates

variable {C : Type*} [Group C]

/-- **The traced Stokes pairing of the compact-`M` family** is the sum of the two second-order
values: the twin of `Certificates.heisEta1_nCompactFam_apply`, and the bridge every
`heisEta1`-level compact-`M` calculation has to go through. -/
theorem heisEta1_mCompactFam_apply {α h q e : ℕ} {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) :
    heisEta1 ⇑t (mCompactFam α h q e) x y
      = (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
          (tameRelW (2 + 2 * h) q)).z
        + (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two, mCompactFam_zero, mCompactFam_one,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

end GQ2.Dyadic.Certificates.MCompact
