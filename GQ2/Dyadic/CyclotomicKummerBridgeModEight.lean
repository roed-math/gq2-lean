import GQ2.Dyadic.CyclotomicKummerBridge
import GQ2.HilbertSymbolDyadic

/-!
# The independent mod-eight cyclotomic row is the Kummer class of two

The improved square constructor table needs two mod-`2` shadows of the cyclotomic character.
The mod-four shadow is `[-1]`; this file proves that Serre's second residue character
`omega(u) = (u^2-1)/8 (mod 2)` is exactly the Kummer class `[2]`.  Its values on the four
unit residues are `0,1,1,0` at `1,3,5,7`, respectively, so it is the row which reads `1` on
both improved generators with value `5`, and `0` on the generator with value `7`.

The proof uses an actual eighth root of unity `zeta`, observes that
`alpha = zeta + zeta^-1` is a square root of `2`, and dispatches the four possible exponents
in `Gal(Q_2(zeta_8)/Q_2)`.  No presentation, orientation equivalence, or desired field
classification is imported.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 ContCoh
open GQ2.HilbertSymbol

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Serre's `omega` residue character, bundled on `(Z/8)^x`. -/
def unitsModEightOmega : (ZMod 8)ˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (omegaResidue (u : ZMod 8))
  map_one' := by decide
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    exact omegaResidue_mul_of_isUnit u.isUnit v.isUnit

private theorem unitsModEight_val_eq (u : (ZMod 8)ˣ) :
    (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 3 ∨
      (u : ZMod 8) = 5 ∨ (u : ZMod 8) = 7 := by
  have hu : IsUnit (u : ZMod 8) := u.isUnit
  revert hu
  generalize (u : ZMod 8) = r
  revert r
  decide

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- Mod-eight reduction of the cyclotomic character on `G_K`. -/
def chiCycKModEight : GalK K →* (ZMod 8)ˣ :=
  (Units.map (PadicInt.toZModPow (p := 2) 3).toMonoidHom).comp (chiCycK K)

/-- The additive cocycle function underlying the independent mod-eight cyclotomic row. -/
def cyclotomicModEightOmegaCocycleFun (g : GalK K) : ZMod 2 :=
  Multiplicative.toAdd (unitsModEightOmega (chiCycKModEight g))

/-- Pointwise bridge: the mod-eight `omega` row is the Kummer cocycle of `2`. -/
theorem cyclotomicModEightOmegaCocycleFun_eq_kummerTwo (g : GalK K) :
    cyclotomicModEightOmegaCocycleFun g =
      Kummer.kummerCocycleFun
        (sqrtCl (((twoUnit K : (K)ˣ) : K) : ℚ̄₂))
        (show Kummer.GaloisGroup ℚ_[2] from g.1) := by
  let iota : ℚ̄₂ := sqrtCl (-1)
  let zeta : ℚ̄₂ := sqrtCl iota
  let alpha : ℚ̄₂ := zeta + zeta⁻¹
  let beta : ℚ̄₂ := sqrtCl (((twoUnit K : (K)ˣ) : K) : ℚ̄₂)
  let u : (ZMod 8)ˣ := chiCycKModEight g
  let gg : Kummer.GaloisGroup ℚ_[2] :=
    (show Field.absoluteGaloisGroup ℚ_[2] from g.1)
  let gr : ℚ̄₂ ≃+* ℚ̄₂ :=
    MulSemiringAction.toRingAut (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ℚ̄₂ gg
  change Multiplicative.toAdd (unitsModEightOmega u) =
    Kummer.kummerCocycleFun beta gg
  have hiota2 : iota ^ 2 = -1 := by simpa [iota] using sqrtCl_sq (-1 : ℚ̄₂)
  have hiota0 : iota ≠ 0 := by
    intro h
    rw [h] at hiota2
    norm_num at hiota2
  have hzeta2 : zeta ^ 2 = iota := by simpa [zeta] using sqrtCl_sq iota
  have hzeta4 : zeta ^ 4 = -1 := by
    calc
      zeta ^ 4 = (zeta ^ 2) ^ 2 := by ring
      _ = -1 := by rw [hzeta2, hiota2]
  have hzeta0 : zeta ≠ 0 := by
    intro h
    rw [h] at hzeta2
    norm_num at hzeta2
    exact hiota0 hzeta2.symm
  have hzeta8 : zeta ^ (2 ^ 3) = 1 := by
    change zeta ^ 8 = 1
    calc
      zeta ^ 8 = (zeta ^ 4) ^ 2 := by ring
      _ = 1 := by rw [hzeta4]; norm_num
  have halpha2 : alpha ^ 2 = 2 := by
    have hiotainv : iota⁻¹ = -iota := by
      apply (mul_left_cancel₀ hiota0)
      rw [mul_inv_cancel₀ hiota0]
      rw [mul_neg, show iota * iota = iota ^ 2 by ring, hiota2]
      ring
    have hzetainv2 : zeta⁻¹ ^ 2 = -iota := by
      rw [inv_pow, hzeta2, hiotainv]
    dsimp [alpha]
    rw [add_sq, hzeta2, hzetainv2]
    rw [mul_assoc, mul_inv_cancel₀ hzeta0, mul_one]
    ring
  have hbeta2 : beta ^ 2 = 2 := by
    rw [show beta = sqrtCl ((((twoUnit K : (K)ˣ) : K) : ℚ̄₂)) from rfl,
      sqrtCl_sq]
    change (((2 : K) : ℚ̄₂)) = 2
    exact map_ofNat (algebraMap K ℚ̄₂) 2
  have hspec := cyclotomicCharacter.spec 2 gr zeta hzeta8
  have hchi : (cyclotomicCharacter ℚ̄₂ 2) gr = chiCycK K g := by rfl
  have huval : (u : ZMod 8) =
      PadicInt.toZModPow 3
        (((cyclotomicCharacter ℚ̄₂ 2) gr : (PadicInt 2)ˣ) : PadicInt 2) := by rfl
  have hspec' : gr zeta = zeta ^ (u : ZMod 8).val := by
    rw [huval, hchi]
    exact hspec
  have hcocycle_eq : Kummer.kummerCocycleFun beta gg =
      Kummer.kummerCocycleFun alpha gg := by
    exact congrFun (GQ2.kcf_root_indep' (by rw [hbeta2, halpha2])) gg
  let twoQ : ℚ_[2]ˣ := Units.mk0 2 two_ne_zero
  have halpha2Q : alpha ^ 2 = algebraMap ℚ_[2] ℚ̄₂ (twoQ : ℚ_[2]) := by
    rw [show algebraMap ℚ_[2] ℚ̄₂ (twoQ : ℚ_[2]) = 2 by
      change algebraMap ℚ_[2] ℚ̄₂ 2 = 2
      exact map_ofNat (algebraMap ℚ_[2] ℚ̄₂) 2]
    exact halpha2
  have hzeta3 : zeta ^ 3 = -zeta⁻¹ := by
    apply (mul_left_cancel₀ hzeta0)
    rw [mul_neg, mul_inv_cancel₀ hzeta0]
    calc
      zeta * zeta ^ 3 = zeta ^ 4 := by ring
      _ = -1 := hzeta4
  have hzeta5 : zeta ^ 5 = -zeta := by
    calc
      zeta ^ 5 = zeta ^ 4 * zeta := by ring
      _ = -zeta := by rw [hzeta4]; ring
  have hzeta7 : zeta ^ 7 = zeta⁻¹ := by
    apply (mul_left_cancel₀ hzeta0)
    rw [mul_inv_cancel₀ hzeta0]
    calc
      zeta * zeta ^ 7 = zeta ^ 8 := by ring
      _ = 1 := hzeta8
  rw [hcocycle_eq]
  rcases unitsModEight_val_eq u with hu | hu | hu | hu
  · have hfix : gg • alpha = alpha := by
      change gr alpha = alpha
      dsimp [alpha]
      rw [map_add, map_inv₀, hspec', hu]
      rw [show (1 : ZMod 8).val = 1 by decide]
      simp
    rw [Kummer.kummerCocycleFun_eq0 hfix]
    change omegaResidue (u : ZMod 8) = 0
    rw [hu, omegaResidue_table.1]
  · have hneg : gg • alpha = -alpha := by
      change gr alpha = -alpha
      dsimp [alpha]
      rw [map_add, map_inv₀, hspec', hu]
      rw [show (3 : ZMod 8).val = 3 by decide, hzeta3]
      simp
    rw [Kummer.kummerCocycleFun_eq1
      (a := twoQ) halpha2Q hneg]
    change omegaResidue (u : ZMod 8) = 1
    rw [hu, omegaResidue_table.2.1]
  · have hneg : gg • alpha = -alpha := by
      change gr alpha = -alpha
      dsimp [alpha]
      rw [map_add, map_inv₀, hspec', hu]
      rw [show (5 : ZMod 8).val = 5 by decide, hzeta5]
      ring
    rw [Kummer.kummerCocycleFun_eq1
      (a := twoQ) halpha2Q hneg]
    change omegaResidue (u : ZMod 8) = 1
    rw [hu, omegaResidue_table.2.2.1]
  · have hfix : gg • alpha = alpha := by
      change gr alpha = alpha
      dsimp [alpha]
      rw [map_add, map_inv₀, hspec', hu]
      rw [show (7 : ZMod 8).val = 7 by decide, hzeta7]
      rw [inv_inv]
      ring
    rw [Kummer.kummerCocycleFun_eq0 hfix]
    change omegaResidue (u : ZMod 8) = 0
    rw [hu, omegaResidue_table.2.2.2]

/-- Reduction modulo eight followed by `omega`, as a continuous character of `2`-adic units. -/
def padicUnitsModEightOmega :
    ContinuousMonoidHom (PadicInt 2)ˣ (Multiplicative (ZMod 2)) where
  toMonoidHom := unitsModEightOmega.comp
    (Units.map (PadicInt.toZModPow (p := 2) 3).toMonoidHom)
  continuous_toFun := by
    apply (continuous_of_discreteTopology (f := unitsModEightOmega)).comp
    let hmod : Continuous (PadicInt.toZModPow (p := 2) 3) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow 3 T
    exact Units.continuous_iff.mpr
      ⟨hmod.comp Units.continuous_val,
        hmod.comp (Units.continuous_val.comp continuous_inv)⟩

/-- The independent mod-eight row as a continuous character of `G_K`. -/
def cyclotomicModEightOmegaCharacterK :
    ContinuousMonoidHom (GalK K) (Multiplicative (ZMod 2)) :=
  padicUnitsModEightOmega.comp (chiCycKCont (K := K))

@[simp] theorem cyclotomicModEightOmegaCharacterK_apply (g : GalK K) :
    Multiplicative.toAdd (cyclotomicModEightOmegaCharacterK g) =
      cyclotomicModEightOmegaCocycleFun g := rfl

/-- The `H^1` class of the independent mod-eight cyclotomic row. -/
noncomputable def cyclotomicModEightOmegaClassK : H1 (GalK K) (ZMod 2) :=
  H1mk _ _ (Count.homEquivZ1 (cyclotomicModEightOmegaCharacterK (K := K)))

/-- Cohomological bridge: the independent mod-eight cyclotomic row is `[2]`. -/
theorem cyclotomicModEightOmegaClassK_eq_kummerTwo :
    cyclotomicModEightOmegaClassK (K := K) = kummerClassK K (twoUnit K) := by
  unfold cyclotomicModEightOmegaClassK kummerClassK
  congr 1
  apply Subtype.ext
  funext g
  exact cyclotomicModEightOmegaCocycleFun_eq_kummerTwo g

/-- The two cyclotomic rows are orthogonal for the local cup form. -/
theorem cupFormK_cyclotomicModEightOmega_modFour
    [FiniteDimensional ℚ_[2] K] :
    FieldData.cupFormK K (cyclotomicModEightOmegaClassK (K := K))
      (cyclotomicModFourClassK (K := K)) = 0 := by
  rw [cyclotomicModEightOmegaClassK_eq_kummerTwo,
    cyclotomicModFourClassK_eq_kappaK]
  unfold FieldData.cupFormK FieldData.kappaK
  rw [← map_zero (FieldData.invGalK K)]
  congr 1
  exact cup_two_neg_one K (FieldData.smul_zmodTwo_galK K)

section MaxProTwo

variable [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
variable [DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2)]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)]

/-- The independent mod-eight row, formed directly on `G_K(2)`. -/
def cyclotomicModEightOmegaCharacterKTwo :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
  padicUnitsModEightOmega.comp (chiCycKTwo (K := K))

/-- Its degree-one class on `G_K(2)`. -/
noncomputable def cyclotomicModEightOmegaClassKTwo :
    H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  H1mk _ _ (Count.homEquivZ1 (cyclotomicModEightOmegaCharacterKTwo (K := K)))

/-- Inflation identifies the directly descended mod-eight class with `[2]` on `G_K`. -/
theorem h1MaxProTwoEquivGalK_cyclotomicModEightOmegaClassKTwo :
    h1MaxProTwoEquivGalK (K := K) (cyclotomicModEightOmegaClassKTwo (K := K)) =
      cyclotomicModEightOmegaClassK (K := K) := by
  rw [h1MaxProTwoEquivGalK_apply]
  unfold cyclotomicModEightOmegaClassKTwo cyclotomicModEightOmegaClassK
  rw [inf1_H1mk]
  congr 1

end MaxProTwo

#print axioms cyclotomicModEightOmegaCocycleFun_eq_kummerTwo
#print axioms cyclotomicModEightOmegaClassK_eq_kummerTwo
#print axioms cupFormK_cyclotomicModEightOmega_modFour
#print axioms h1MaxProTwoEquivGalK_cyclotomicModEightOmegaClassKTwo

end
end GQ2.Dyadic
