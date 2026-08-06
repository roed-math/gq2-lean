/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Stokes

/-!
# Pure-base Heisenberg lifts, and the one-sided commutator law

The trivial-base toolkit of `GQ2/Dyadic/Word/Stokes.lean` (`heisPow_of_trivial`,
`heisCommR_of_trivial`, `heisConjR_of_trivial`) is what every *unramified* second-order row runs
on.  A ramified row cannot use all of it: on a ramified simple module `powOmega2 t.σ` need not
act trivially, so the `σ₂`-twisted letters of the compact-`M` word have a genuinely
nontrivially-acting base.

Two replacements are enough, and neither needs a power law for a moving base.

* **Pure-base lifts.**  A letter whose *offsets* vanish contributes `⟨0,0,0,g⟩`, and those form
  the image of a monoid hom `heisPure : C →* H(A) ⋊ C`.  So every `σ₂`-power in the word is
  second-order invisible as soon as the offsets vanish at `σ` — no hypothesis on how `σ₂` acts.
  This is what replaces the `hS₂` discipline of `Certificates.MCompact`.
* **The one-sided commutator law.**  `[p, r]` with only `r`'s base acting trivially is no longer
  jet-zero: its jet is the coboundary `r.a − p.g⁻¹·r.a`, and its central value acquires the two
  extra terms `r.l(r.a) + r.l(p.g·r.a)` over the two-sided law.  Both are what carry the
  compact-`M` row's `x₁`-diagonal.

The last lemma is the bookkeeping normalizer: a `ℤ`-power of a single group element pairing a
twisted functional against a twisted vector collapses to the difference of the exponents.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-! ## Pure-base lifts -/

/-- **The pure-base lift** `g ↦ ⟨0, 0, 0, g⟩`: a genuine monoid hom, because all three offset
coordinates of the Heisenberg product are `C`-twisted sums that vanish on zero offsets. -/
def heisPure : C →* HeisLift A C where
  toFun g := ⟨0, 0, 0, g⟩
  map_one' := rfl
  map_mul' g g' := by
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show (0 : A) = 0 + g • (0 : A)
      rw [smul_zero, add_zero]
    · show (0 : ElemDual A) = 0 + g • (0 : ElemDual A)
      rw [smul_zero, add_zero]
    · show (0 : ZMod 2) = 0 + 0 + (0 : ElemDual A) (g • (0 : A))
      rw [smul_zero, ElemDual.zero_apply, add_zero, add_zero]

@[simp] theorem heisPure_a (g : C) : (heisPure (A := A) g).a = 0 := rfl

@[simp] theorem heisPure_l (g : C) : (heisPure (A := A) g).l = 0 := rfl

@[simp] theorem heisPure_z (g : C) : (heisPure (A := A) g).z = 0 := rfl

@[simp] theorem heisPure_g (g : C) : (heisPure (A := A) g).g = g := rfl

/-- A pure-base lift is jet-zero, so it never contributes a cross term. -/
theorem heisPure_mem_jetZero (g : C) : heisPure (A := A) g ∈ heisJetZero A C := ⟨rfl, rfl⟩

variable {X : Type*}

/-- A letter with **vanishing offsets** denotes a pure-base lift. -/
theorem heisEvalZ_gen_of_offsets_zero (μ : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : X) (hx : x i = 0) (hy : y i = 0) :
    heisEvalZ μ x y E E₂ (.gen i) = heisPure (μ i) := by
  rw [heisEvalZ_gen, hx, hy]
  rfl

/-- Pure-base denotations are closed under `ℤ`-powers, with the power taken in `C`. -/
theorem heisEvalZ_zpow_of_pure (μ : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (u : PWord X) (g : C)
    (hu : heisEvalZ μ x y E E₂ u = heisPure g) (k : ℤ) :
    heisEvalZ μ x y E E₂ (.zpow u k) = heisPure (g ^ k) := by
  rw [heisEvalZ_zpow, hu, map_zpow]

/-- Pure-base denotations are closed under the profinite power, with the resolved exponent
taken in `C`. -/
theorem heisEvalZ_profPow_of_pure (μ : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (u : PWord X) (g : C)
    (hu : heisEvalZ μ x y E E₂ u = heisPure g) (γ : Zhat) :
    heisEvalZ μ x y E E₂ (.profPow u γ) = heisPure (g ^ E γ) := by
  rw [heisEvalZ_profPow, hu, map_zpow]

/-- Conjugation of pure-base lifts is pure. -/
theorem heisPure_conjR (g s : C) :
    conjR (heisPure (A := A) g) (heisPure s) = heisPure (conjR g s) := by
  rw [conjR, conjR, ← map_inv, ← map_mul, ← map_mul]

/-- The base of a `HeisLift` denotation is the plain integer-exponent denotation. -/
theorem heisEvalZ_g (μ : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    (heisEvalZ μ x y E E₂ w).g = PWord.evalZ μ E E₂ w :=
  PWord.map_evalZ (HeisLift.gHom (A := A) (C := C)) (heisGen μ x y) E E₂ w

/-! ## Products with a trivially-acting left factor -/

/-- Multiplying by a pure-base lift on the left twists the jet and leaves the centre alone. -/
theorem heisPure_mul (g : C) (q : HeisLift A C) :
    heisPure g * q = ⟨g • q.a, g • q.l, q.z, g * q.g⟩ := by
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show (0 : A) + g • q.a = g • q.a
    rw [zero_add]
  · show (0 : ElemDual A) + g • q.l = g • q.l
    rw [zero_add]
  · show (0 : ZMod 2) + q.z + (0 : ElemDual A) (g • q.a) = q.z
    rw [ElemDual.zero_apply, zero_add, add_zero]

/-- The Heisenberg product rule when the **left** factor's base acts trivially: jets add and the
centre picks up the single cross term `p.l(q.a)`. -/
theorem heisMul_of_trivial_left (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    p * q = ⟨p.a + q.a, p.l + q.l, p.z + q.z + p.l q.a, p.g * q.g⟩ := by
  have hpD : ∀ lam : ElemDual A, p.g • lam = lam := smul_elemDual_of_trivial hp
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show p.a + p.g • q.a = _
    rw [hp]
  · show p.l + p.g • q.l = _
    rw [hpD]
  · show p.z + q.z + p.l (p.g • q.a) = _
    rw [hp]

/-- **The four-factor product law** for lifts whose first three bases act trivially: the jets add
and the centre is the sum of the four charges plus the six ordered cross pairings.  This is the
shape of the compact-`M` correction block `E_m^rev`. -/
theorem heisMul_four_of_trivial (p₁ p₂ p₃ p₄ : HeisLift A C)
    (h₁ : ∀ a : A, p₁.g • a = a) (h₂ : ∀ a : A, p₂.g • a = a) (h₃ : ∀ a : A, p₃.g • a = a) :
    (p₁ * (p₂ * (p₃ * p₄))).a = p₁.a + (p₂.a + (p₃.a + p₄.a)) ∧
      (p₁ * (p₂ * (p₃ * p₄))).l = p₁.l + (p₂.l + (p₃.l + p₄.l)) ∧
      (p₁ * (p₂ * (p₃ * p₄))).z = p₁.z + p₂.z + p₃.z + p₄.z
        + (p₁.l p₂.a + p₁.l p₃.a + p₁.l p₄.a + p₂.l p₃.a + p₂.l p₄.a + p₃.l p₄.a) := by
  rw [heisMul_of_trivial_left p₃ p₄ h₃, heisMul_of_trivial_left p₂ _ h₂,
    heisMul_of_trivial_left p₁ _ h₁]
  refine ⟨rfl, rfl, ?_⟩
  show p₁.z + (p₂.z + (p₃.z + p₄.z + p₃.l p₄.a) + p₂.l (p₃.a + p₄.a))
      + p₁.l (p₂.a + (p₃.a + p₄.a)) = _
  rw [map_add, map_add, map_add]
  abel

/-- **The compact-`M` five-factor central rule.**  Factor `3` is pure with base `s`, factor `4`
is pure with a trivially-acting base and factor `2` acts trivially; factor `1`'s base is
arbitrary.  So the last two factors enter with prefix weight `s`, and only two cross terms
survive. -/
theorem heisMul_five_z (p₁ p₂ p₃ p₄ p₅ : HeisLift A C) (s : C)
    (h₃ : p₃ = heisPure s) (h₄ : p₄.a = 0 ∧ p₄.l = 0 ∧ p₄.z = 0)
    (h₄g : ∀ a : A, p₄.g • a = a) (h₂g : ∀ a : A, p₂.g • a = a) :
    (p₁ * (p₂ * (p₃ * (p₄ * p₅)))).z
      = p₁.z + p₂.z + p₅.z + p₂.l (s • p₅.a) + p₁.l (p₁.g • (p₂.a + s • p₅.a)) := by
  obtain ⟨h₄a, h₄l, h₄z⟩ := h₄
  have h45 : p₄ * p₅ = ⟨p₅.a, p₅.l, p₅.z, p₄.g * p₅.g⟩ := by
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show p₄.a + p₄.g • p₅.a = _
      rw [h₄a, h₄g, zero_add]
    · show p₄.l + p₄.g • p₅.l = _
      rw [h₄l, smul_elemDual_of_trivial h₄g, zero_add]
    · show p₄.z + p₅.z + p₄.l (p₄.g • p₅.a) = _
      rw [h₄z, h₄l, ElemDual.zero_apply, zero_add, add_zero]
  rw [h45, h₃, heisPure_mul, heisMul_of_trivial_left _ _ h₂g, HeisLift.mul_z]
  show p₁.z + (p₂.z + p₅.z + p₂.l (s • p₅.a))
      + p₁.l (p₁.g • (p₂.a + s • p₅.a)) = _
  abel

/-- Composing two `ℤ`-powers of one group element on a module. -/
theorem zpow_smul_zpow_smul (c : C) (i j : ℤ) (v : A) :
    c ^ i • (c ^ j • v) = c ^ (i + j) • v := by
  rw [← mul_smul, ← zpow_add]

/-! ## The one-sided commutator law -/

/-- **The commutator of a lift with a trivial-base lift.**  Only the *right* factor's base is
assumed to act trivially; the left one may act arbitrarily.  Then

`[p, r] = ⟨r.a − p.g⁻¹·r.a, r.l − p.g⁻¹·r.l, r.l(r.a) + p.l(r.a) + r.l(p.a) + r.l(p.g·r.a)⟩`,

a coboundary jet and a central value with **two more terms** than the two-sided law
`heisCommR_of_trivial`.  No `2`-torsion hypothesis: the central slot is `ZMod 2` already, and the
offset cancellations are exact. -/
theorem heisCommR_of_trivial_right (p r : HeisLift A C) (hr : ∀ a : A, r.g • a = a) :
    commR p r = ⟨r.a - p.g⁻¹ • r.a, r.l - p.g⁻¹ • r.l,
      r.l r.a + p.l r.a + r.l p.a + r.l (p.g • r.a), commR p.g r.g⟩ := by
  have hri : ∀ a : A, r.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hr a).symm
  have hrD : ∀ lam : ElemDual A, r.g • lam = lam := smul_elemDual_of_trivial hr
  have hriD : ∀ lam : ElemDual A, r.g⁻¹ • lam = lam := smul_elemDual_of_trivial hri
  rw [commR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hri, smul_neg, inv_smul_smul]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hriD, smul_neg, inv_smul_smul]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.inv_z,
      HeisLift.inv_a, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hri, hriD, smul_neg, inv_smul_smul]
    simp only [ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply, map_neg,
      inv_inv, smul_inv_smul]
    generalize p.z = c₁
    generalize r.z = c₂
    generalize p.l p.a = c₃
    generalize r.l r.a = c₄
    generalize p.l r.a = c₅
    generalize r.l p.a = c₆
    generalize r.l (p.g • r.a) = c₇
    generalize p.l (p.g • r.a) = c₈
    revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈
    decide
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-! ## The exponent normalizer -/

/-- Pairing a `c^i`-twisted functional against a `c^j`-twisted vector reads off the difference
of the exponents.  Every atom of the compact-`M` ramified row is normalized by this. -/
theorem elemDual_zpow_smul_apply (lam : ElemDual A) (c : C) (i j : ℤ) (v : A) :
    ((c ^ i) • lam) ((c ^ j) • v) = lam ((c ^ (j - i)) • v) := by
  rw [ElemDual.smul_apply, ← mul_smul, ← zpow_neg, ← zpow_add, neg_add_eq_sub]

@[inherit_doc elemDual_zpow_smul_apply]
theorem elemDual_zpow_smul_apply_right (lam : ElemDual A) (c : C) (i : ℤ) (v : A) :
    ((c ^ i) • lam) v = lam ((c ^ (-i)) • v) := by
  rw [ElemDual.smul_apply, ← zpow_neg]

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

open GQ2.Dyadic

#print axioms heisPure
#print axioms heisEvalZ_gen_of_offsets_zero
#print axioms heisEvalZ_zpow_of_pure
#print axioms heisEvalZ_profPow_of_pure
#print axioms heisPure_conjR
#print axioms heisEvalZ_g
#print axioms heisPure_mul
#print axioms heisMul_of_trivial_left
#print axioms heisMul_four_of_trivial
#print axioms heisMul_five_z
#print axioms zpow_smul_zpow_smul
#print axioms heisCommR_of_trivial_right
#print axioms elemDual_zpow_smul_apply
#print axioms elemDual_zpow_smul_apply_right

end AxiomAudit
