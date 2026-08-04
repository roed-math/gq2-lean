/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.FieldData
import GQ2.Dyadic.MarkedMaxProTwo
import GQ2.Dyadic.Count.Scalar

/-!
# The mod-four cyclotomic character is the Kummer class of minus one

The Labute vector in the local cup--Bockstein identity is
`kappaK K = kummerClassK K (-1)`.  The higher-stage construction, by contrast, is oriented by
the `2`-adic cyclotomic character.  This file proves the missing degree-one bridge: reducing the
cyclotomic character modulo four and recording whether its value is `1` or `-1` gives exactly
the Kummer cocycle of `-1`.

This is a theorem about Mathlib's actual cyclotomic character, not an arithmetic interface.  The
pointwise proof applies `cyclotomicCharacter.spec` to the canonical square root of `-1`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The unique nontrivial character `(Z/4)^× → 𝔽₂`, in multiplicative spelling. -/
def unitsModFourParity : (ZMod 4)ˣ →* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' u v := by
    fin_cases u <;> fin_cases v <;> decide

theorem unitsModFour_eq_one_or_neg_one (u : (ZMod 4)ˣ) : u = 1 ∨ u = -1 := by
  fin_cases u <;> decide

/-- Reduction modulo four followed by the parity character, as a continuous character of
`2`-adic units. -/
def padicUnitsModFourParity : ContinuousMonoidHom ℤ_[2]ˣ (Multiplicative (ZMod 2)) where
  toMonoidHom := unitsModFourParity.comp
    (Units.map (PadicInt.toZModPow (p := 2) 2).toMonoidHom)
  continuous_toFun := by
    apply (continuous_of_discreteTopology (f := unitsModFourParity)).comp
    let hmod : Continuous (PadicInt.toZModPow (p := 2) 2) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow 2 T
    exact Units.continuous_iff.mpr
      ⟨hmod.comp Units.continuous_val,
        hmod.comp (Units.continuous_val.comp continuous_inv)⟩

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The mod-four reduction of the cyclotomic character on `G_K`. -/
def chiCycKModFour : GalK K →* (ZMod 4)ˣ :=
  (Units.map (PadicInt.toZModPow (p := 2) 2).toMonoidHom).comp (chiCycK K)

/-- Additive cocycle function underlying the mod-four cyclotomic sign. -/
def cyclotomicModFourCocycleFun (g : GalK K) : ZMod 2 :=
  Multiplicative.toAdd (unitsModFourParity (chiCycKModFour g))

/-- The mod-four cyclotomic sign as a continuous mod-two character. -/
def cyclotomicModFourCharacterK :
    ContinuousMonoidHom (GalK K) (Multiplicative (ZMod 2)) :=
  padicUnitsModFourParity.comp (chiCycKCont (K := K))

@[simp] theorem cyclotomicModFourCharacterK_apply (g : GalK K) :
    Multiplicative.toAdd (cyclotomicModFourCharacterK g) =
      cyclotomicModFourCocycleFun g := rfl

/-- Pointwise bridge: the mod-four cyclotomic sign is the Kummer cocycle of `-1`. -/
theorem cyclotomicModFourCocycleFun_eq_kummerNegOne (g : GalK K) :
    cyclotomicModFourCocycleFun g =
      Kummer.kummerCocycleFun
        (sqrtCl (((-1 : (↥K)ˣ) : ↥K) : ℚ̄₂))
        (show Kummer.GaloisGroup ℚ_[2] from g.1) := by
  let alpha : ℚ̄₂ := sqrtCl (((-1 : (↥K)ˣ) : ↥K) : ℚ̄₂)
  let u : (ZMod 4)ˣ := chiCycKModFour g
  let gg : Kummer.GaloisGroup ℚ_[2] :=
    (show Field.absoluteGaloisGroup ℚ_[2] from g.1)
  let gr : ℚ̄₂ ≃+* ℚ̄₂ :=
    MulSemiringAction.toRingAut (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ℚ̄₂ gg
  change Multiplicative.toAdd (unitsModFourParity u) =
    Kummer.kummerCocycleFun alpha gg
  have halpha2 : alpha ^ 2 = -1 := by
    simpa [alpha] using sqrtCl_sq (((-1 : (↥K)ˣ) : ↥K) : ℚ̄₂)
  have halpha4 : alpha ^ (2 ^ 2) = 1 := by
    change alpha ^ 4 = 1
    calc
      alpha ^ 4 = (alpha ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [halpha2]
      _ = 1 := by norm_num
  have hspec := cyclotomicCharacter.spec 2 gr alpha halpha4
  have hchi : (cyclotomicCharacter ℚ̄₂ 2) gr = chiCycK K g := by
    rfl
  have huval : (u : ZMod 4) =
      PadicInt.toZModPow 2
        (((cyclotomicCharacter ℚ̄₂ 2) gr : ℤ_[2]ˣ) : ℤ_[2]) := by
    rfl
  have hspec' : gr alpha = alpha ^ (u : ZMod 4).val := by
    rw [huval, hchi]
    exact hspec
  rcases unitsModFour_eq_one_or_neg_one u with hu | hu
  · have hfix : gg • alpha = alpha := by
      change gr alpha = alpha
      rw [hspec', hu]
      change alpha ^ 1 = alpha
      rw [pow_one]
    rw [Kummer.kummerCocycleFun_eq0 hfix]
    simp [unitsModFourParity, hu]
  · have hneg : gg • alpha = -alpha := by
      change gr alpha = -alpha
      rw [hspec', hu]
      change alpha ^ 3 = -alpha
      calc
        alpha ^ 3 = alpha ^ 2 * alpha := by ring
        _ = -alpha := by rw [halpha2]; ring
    have hk := Kummer.kummerCocycleFun_eq1
      (a := (-1 : ℚ_[2]ˣ)) (α := alpha) (by simpa using halpha2) hneg
    rw [hk]
    have hne : (-1 : (ZMod 4)ˣ) ≠ 1 := by decide
    simp [unitsModFourParity, hu, hne]

/-- The cohomology class of the mod-four cyclotomic sign. -/
noncomputable def cyclotomicModFourClassK : H1 (GalK K) (ZMod 2) :=
  H1mk _ _ (Count.homEquivZ1 (cyclotomicModFourCharacterK (K := K)))

/-- Cohomological bridge: the mod-four cyclotomic class is the Labute/Kummer vector `[-1]`. -/
theorem cyclotomicModFourClassK_eq_kappaK :
    cyclotomicModFourClassK (K := K) = FieldData.kappaK K := by
  unfold cyclotomicModFourClassK FieldData.kappaK kummerClassK
  congr 1
  apply Subtype.ext
  funext g
  exact cyclotomicModFourCocycleFun_eq_kummerNegOne g

#print axioms cyclotomicModFourCocycleFun_eq_kummerNegOne
#print axioms cyclotomicModFourClassK_eq_kappaK

end


end GQ2.Dyadic
