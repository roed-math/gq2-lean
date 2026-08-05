/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageDerivationCocycle
import GQ2.Dyadic.FiniteTwoLocalReciprocityHigherKummerExact

/-!
# The χ-twisted higher Kummer cocycle on `G_K(2)`

The twisted-cocycle parity supply asks, at every stage `k ≥ 3`, for continuous χ-twisted
one-cocycles `G_K(2) → ℤ/2^(k+1)` with prescribed value parities.  χ-factoring cocycles are
parity-locked, so the construction must be genuinely Kummer-theoretic.  This file builds the
cocycles from `2^N`-th roots of field elements:

* `muNDlog`: a primitive `2^N`-th root of unity `ζ` identifies `μ_{2^N} ≅ ℤ/2^N`
  additively; under this discrete log the Galois action on roots of unity becomes
  multiplication by the mod-`2^N` cyclotomic character (`muNDlog_smul` — Mathlib's
  `cyclotomicCharacter.spec` is the definitional input);
* `chiTwistedKummerFun`: for `a ∈ Kˣ` with a chosen `2^N`-th root `α`, the discrete log of
  the higher Kummer cocycle `g ↦ g(α)/α`.  It satisfies the χ-twisted cocycle identity
  (`chiTwistedKummerFun_mul`) and is continuous, and its mod-`2` reduction is the classical
  quadratic Kummer sign of `a` (`chiTwistedKummerFun_parity`): `α^(2^(N-1))` is a square
  root of `a`, and `ζ^(2^(N-1)) = -1`;
* `chiTwistedKummerHom`: the cocycle and the mod-`2^N` cyclotomic shadow assemble into a
  continuous homomorphism into the finite lift group `WL N`, which factors through the
  maximal pro-2 quotient because `WL N` is a finite 2-group (`chiTwistedKummerDescent`).
  The descended offset is a continuous χ-twisted one-cocycle on `G_K(2)` in the sense of
  the parity supply (`isChiTwistedCocycle_chiTwistedKummerDescent`), whose values on
  classes from `G_K` are the field-level values (`chiTwistedKummerDescent_u_mk`).

The parity prescription itself — choosing `a` with prescribed Kummer signs at the stage
lifts — is the next file's dual-basis argument.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Arithmetic helpers -/

/-- Divisibility by two in `ℤ/2^N` is parity of the value. -/
theorem stageKummer_two_dvd_iff {N : ℕ} (hN : 1 ≤ N) (w : ZMod (2 ^ N)) :
    (2 : ZMod (2 ^ N)) ∣ w ↔ 2 ∣ w.val := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [ZMod.val_mul 2 y, Nat.dvd_mod_iff (dvd_pow_self 2 (by omega : N ≠ 0))]
    have h2 : (2 : ZMod (2 ^ N)).val = 2 % 2 ^ N := by
      rw [show (2 : ZMod (2 ^ N)) = ((2 : ℕ) : ZMod (2 ^ N)) by push_cast; rfl,
        ZMod.val_natCast]
    exact Dvd.dvd.mul_right
      (by rw [h2, Nat.dvd_mod_iff (dvd_pow_self 2 (by omega : N ≠ 0))]) _
  · rintro ⟨t, ht⟩
    refine ⟨(t : ZMod (2 ^ N)), ?_⟩
    have hw : ((w.val : ℕ) : ZMod (2 ^ N)) = w := ZMod.natCast_rightInverse w
    rw [← hw, ht]
    push_cast
    ring

/-- Fixing one square root of an element is fixing any other. -/
theorem stageKummer_fix_transfer {x y : ℚ̄₂} (h : x ^ 2 = y ^ 2)
    (γ : Kummer.GaloisGroup ℚ_[2]) : γ • x = x ↔ γ • y = y := by
  have hfac : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · rw [sub_eq_zero.mp h']
  · have hxy : x = -y := by linear_combination h'
    subst hxy
    rw [smul_neg, neg_inj]

/-- The vanishing dichotomy of the mod-2 Kummer sign cocycle. -/
theorem stageKummer_kummerCocycleFun_eq_zero_iff (x : ℚ̄₂)
    (γ : Kummer.GaloisGroup ℚ_[2]) :
    Kummer.kummerCocycleFun x γ = 0 ↔ γ • x = x := by
  unfold Kummer.kummerCocycleFun
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false one_ne_zero h

/-- Extensionality for `μ_{2^N}` through the underlying unit. -/
theorem stageKummer_muN_ext {N : ℕ} {x y : MuN (2 ^ N)}
    (h : (x.toMul : ℚ̄₂ˣ) = (y.toMul : ℚ̄₂ˣ)) : x = y :=
  Additive.toMul.injective (Subtype.ext h)

/-! ## The discrete log on `μ_{2^N}` -/

section Dlog

variable {N : ℕ} {zu : ℚ̄₂ˣ} (hzu : IsPrimitiveRoot zu (2 ^ N))

/-- **The discrete log.**  A primitive `2^N`-th root of unity identifies the additive
`μ_{2^N}` with `ℤ/2^N`. -/
def muNDlog : MuN (2 ^ N) ≃+ ZMod (2 ^ N) :=
  ((hzu.zmodEquivZPowers).trans
    (MulEquiv.toAdditive (MulEquiv.subgroupCongr hzu.zpowers_eq))).symm

theorem muNDlog_symm_natCast (m : ℕ) :
    (((muNDlog hzu).symm (m : ZMod (2 ^ N))).toMul : ℚ̄₂ˣ) = zu ^ m := by
  show ((((hzu.zmodEquivZPowers).trans
    (MulEquiv.toAdditive (MulEquiv.subgroupCongr hzu.zpowers_eq)))
      (m : ZMod (2 ^ N))).toMul : ℚ̄₂ˣ) = zu ^ m
  rw [AddEquiv.trans_apply, hzu.zmodEquivZPowers_apply_coe_nat]
  rfl

/-- The defining property of the discrete log: every element of `μ_{2^N}` is the
`ζ`-power by its logarithm. -/
theorem muNDlog_toMul (x : MuN (2 ^ N)) :
    (x.toMul : ℚ̄₂ˣ) = zu ^ ((muNDlog hzu) x).val := by
  conv_lhs => rw [show x = (muNDlog hzu).symm
    ((((muNDlog hzu) x).val : ℕ) : ZMod (2 ^ N)) by
      rw [ZMod.natCast_rightInverse _, AddEquiv.symm_apply_apply]]
  exact muNDlog_symm_natCast hzu _

end Dlog

/-! ## The χ-twist of the Galois action under the discrete log -/

section Twist

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
variable {N : ℕ} {zu : ℚ̄₂ˣ} (hzu : IsPrimitiveRoot zu (2 ^ N))

include hzu in
/-- The Galois action on a primitive `2^N`-th root of unity is the `2^N`-th power of the
cyclotomic character: Mathlib's `cyclotomicCharacter.spec`, read at the unit level. -/
theorem stageKummer_units_cyc (g : ↥(K.fixingSubgroup)) :
    g • zu = zu ^ (PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2])).val := by
  apply Units.ext
  have hzuF : IsPrimitiveRoot (zu : ℚ̄₂) (2 ^ N) := IsPrimitiveRoot.coe_units_iff.mpr hzu
  have hspec := cyclotomicCharacter.spec 2
    (MulSemiringAction.toRingAut (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ℚ̄₂
      (show Field.absoluteGaloisGroup ℚ_[2] from (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)))
    (zu : ℚ̄₂) hzuF.pow_eq_one
  have hchi : (cyclotomicCharacter ℚ̄₂ 2)
      (MulSemiringAction.toRingAut (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ℚ̄₂
        (show Field.absoluteGaloisGroup ℚ_[2] from (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂))) =
      chiCycK K g := rfl
  rw [hchi] at hspec
  calc ((g • zu : ℚ̄₂ˣ) : ℚ̄₂)
      = (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ((zu : ℚ̄₂)) := rfl
    _ = (zu : ℚ̄₂) ^ (PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2])).val := hspec
    _ = ((zu ^ (PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2])).val : ℚ̄₂ˣ) : ℚ̄₂) :=
        (Units.val_pow_eq_pow_val _ _).symm

include hzu in
/-- **The χ-equivariance of the discrete log**: the Galois action on `μ_{2^N}` becomes
multiplication by the mod-`2^N` cyclotomic character. -/
theorem muNDlog_smul (g : ↥(K.fixingSubgroup)) (x : MuN (2 ^ N)) :
    muNDlog hzu (g • x) =
      PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2]) * muNDlog hzu x := by
  set c : ZMod (2 ^ N) := PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2]) with hc
  have key : (g • x : MuN (2 ^ N)) = (muNDlog hzu).symm (c * muNDlog hzu x) := by
    apply stageKummer_muN_ext
    calc ((g • x : MuN (2 ^ N)).toMul : ℚ̄₂ˣ)
        = (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) • (x.toMul : ℚ̄₂ˣ) := rfl
      _ = (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) • (zu ^ ((muNDlog hzu) x).val) := by
          rw [muNDlog_toMul hzu x]
      _ = ((g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) • zu) ^ ((muNDlog hzu) x).val := by rw [smul_pow']
      _ = (zu ^ c.val) ^ ((muNDlog hzu) x).val := by
          rw [show (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) • zu = g • zu from rfl,
            stageKummer_units_cyc hzu g]
      _ = zu ^ (c.val * ((muNDlog hzu) x).val) := by rw [← pow_mul]
      _ = (((muNDlog hzu).symm (c * (muNDlog hzu) x)).toMul : ℚ̄₂ˣ) := by
          rw [show c * (muNDlog hzu) x =
              ((c.val * ((muNDlog hzu) x).val : ℕ) : ZMod (2 ^ N)) by
            push_cast
            rw [ZMod.natCast_rightInverse _, ZMod.natCast_rightInverse _]]
          exact (muNDlog_symm_natCast hzu _).symm
  rw [key, AddEquiv.apply_symm_apply]

end Twist

/-! ## The χ-twisted higher Kummer cocycle on `G_K` -/

section Cocycle

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
variable {N : ℕ} {zu : ℚ̄₂ˣ} (hzu : IsPrimitiveRoot zu (2 ^ N))
  (a : (↥K)ˣ) {alpha : ℚ̄₂ˣ} (halpha : alpha ^ 2 ^ N = unitInQbar (K := K) a)

/-- **The χ-twisted higher Kummer cocycle** of `a` at the root `α`: the discrete log of
`g ↦ g(α)/α`. -/
def chiTwistedKummerFun (g : ↥(K.fixingSubgroup)) : ZMod (2 ^ N) :=
  muNDlog hzu (rootRatio (2 ^ N) a alpha halpha g)

include hzu halpha in
/-- The χ-twisted cocycle identity. -/
theorem chiTwistedKummerFun_mul (g h' : ↥(K.fixingSubgroup)) :
    chiTwistedKummerFun hzu a halpha (g * h') = chiTwistedKummerFun hzu a halpha g +
      PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2]) *
        chiTwistedKummerFun hzu a halpha h' := by
  unfold chiTwistedKummerFun
  rw [rootRatio_cocycle, map_add, muNDlog_smul hzu]

include hzu halpha in
theorem chiTwistedKummerFun_one : chiTwistedKummerFun hzu a halpha 1 = 0 := by
  unfold chiTwistedKummerFun
  have h0 : rootRatio (2 ^ N) a alpha halpha 1 = 0 := by
    apply stageKummer_muN_ext
    show ((1 : ↥(K.fixingSubgroup)) • alpha) * alpha⁻¹ = ((0 : MuN (2 ^ N)).toMul : ℚ̄₂ˣ)
    rw [one_smul, mul_inv_cancel]
    rfl
  rw [h0, map_zero]

include hzu halpha in
theorem chiTwistedKummerFun_continuous : Continuous (chiTwistedKummerFun hzu a halpha) :=
  continuous_of_discreteTopology.comp (rootRatio_continuous (2 ^ N) a alpha halpha)

include hzu halpha in
/-- **The parity dictionary**: the parity of the twisted cocycle at `g` is the classical
mod-2 Kummer sign of `a` at `g` — the `2^(N-1)`-th power of `α` is a square root of `a`,
and `ζ^(2^(N-1)) = -1`. -/
theorem chiTwistedKummerFun_parity (hN : 1 ≤ N) (g : ↥(K.fixingSubgroup)) :
    (2 : ZMod (2 ^ N)) ∣ chiTwistedKummerFun hzu a halpha g ↔
      Kummer.kummerCocycleFun (sqrtCl (((a : ↥K) : ℚ̄₂)))
        (g : Kummer.GaloisGroup ℚ_[2]) = 0 := by
  set γ : Kummer.GaloisGroup ℚ_[2] := (g : Kummer.GaloisGroup ℚ_[2])
  set m : ℕ := (chiTwistedKummerFun hzu a halpha g).val with hm
  have hga : g • alpha = zu ^ m * alpha := by
    have h1 : ((rootRatio (2 ^ N) a alpha halpha g).toMul : ℚ̄₂ˣ) = zu ^ m :=
      muNDlog_toMul hzu _
    have h2 : ((rootRatio (2 ^ N) a alpha halpha g).toMul : ℚ̄₂ˣ) =
        (g • alpha) * alpha⁻¹ := rfl
    rw [h2] at h1
    calc g • alpha = (g • alpha) * alpha⁻¹ * alpha := by group
      _ = zu ^ m * alpha := by rw [h1]
  have hzuF : IsPrimitiveRoot (zu : ℚ̄₂) (2 ^ N) := IsPrimitiveRoot.coe_units_iff.mpr hzu
  have hneg : (zu : ℚ̄₂) ^ 2 ^ (N - 1) = -1 := by
    have hsplit : 2 ^ N = 2 ^ (N - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    exact (hzuF.pow (by positivity) hsplit).eq_neg_one_of_two_right
  set beta : ℚ̄₂ˣ := alpha ^ 2 ^ (N - 1) with hbeta
  have hbsq : ((beta : ℚ̄₂)) ^ 2 = ((a : ↥K) : ℚ̄₂) := by
    have h1 : (beta : ℚ̄₂) ^ 2 = ((alpha ^ 2 ^ N : ℚ̄₂ˣ) : ℚ̄₂) := by
      rw [hbeta]
      push_cast
      rw [← pow_mul, ← pow_succ]
      congr 2
      omega
    rw [h1, halpha]
    rfl
  have hgb : γ • ((beta : ℚ̄₂)) = (-1 : ℚ̄₂) ^ m * (beta : ℚ̄₂) := by
    have h3 : ((g • beta : ℚ̄₂ˣ) : ℚ̄₂) = (((zu ^ 2 ^ (N - 1)) ^ m : ℚ̄₂ˣ) : ℚ̄₂) * beta := by
      rw [show g • beta = (zu ^ 2 ^ (N - 1)) ^ m * beta by
        rw [hbeta, smul_pow', hga, mul_pow, ← pow_mul, ← pow_mul,
          mul_comm m (2 ^ (N - 1))]]
      push_cast
      ring
    have h4 : (((zu ^ 2 ^ (N - 1)) ^ m : ℚ̄₂ˣ) : ℚ̄₂) = (-1 : ℚ̄₂) ^ m := by
      push_cast
      rw [hneg]
    rw [← h4]
    exact h3
  have hbne : ((beta : ℚ̄₂)) ≠ -((beta : ℚ̄₂)) := by
    intro h
    have h2 : (2 : ℚ̄₂) * (beta : ℚ̄₂) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact two_ne_zero h'
    · exact beta.ne_zero h'
  have hfixb : γ • ((beta : ℚ̄₂)) = (beta : ℚ̄₂) ↔ 2 ∣ m := by
    constructor
    · intro hfix
      by_contra hodd
      rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow] at hgb
      rw [hgb] at hfix
      exact hbne (by linear_combination -hfix)
    · intro hdvd
      rw [(even_iff_two_dvd.mpr hdvd).neg_one_pow, one_mul] at hgb
      exact hgb
  have htrans : sqrtCl (((a : ↥K) : ℚ̄₂)) ^ 2 = ((beta : ℚ̄₂)) ^ 2 := by
    rw [sqrtCl_sq]
    exact hbsq.symm
  rw [stageKummer_kummerCocycleFun_eq_zero_iff, stageKummer_two_dvd_iff hN, ← hm,
    stageKummer_fix_transfer htrans γ]
  exact hfixb.symm

end Cocycle

/-! ## Assembly into the finite lift group and descent to `G_K(2)` -/

section Descent

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- `WL N` is a finite 2-group: `|ℤ/2^N| · |(ℤ/2^N)ˣ| = 2^N · 2^(N-1)`. -/
private theorem stageKummer_isPGroup_WL {N : ℕ} (hN : 1 ≤ N) : IsPGroup 2 (WL N) := by
  have hcard : Nat.card (WL N) = 2 ^ (N + (N - 1)) := by
    have h1 : Nat.card (WL N) = Nat.card (ZMod (2 ^ N)) * Nat.card ((ZMod (2 ^ N))ˣ) := by
      rw [Nat.card_congr (WordLift.equivProd (A := ZMod (2 ^ N)) (C := (ZMod (2 ^ N))ˣ)),
        Nat.card_prod]
    have h2 : Nat.card (ZMod (2 ^ N)) = 2 ^ N := by
      simp [Nat.card_eq_fintype_card]
    have h3 : Nat.card ((ZMod (2 ^ N))ˣ) = 2 ^ (N - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    rw [h1, h2, h3, ← pow_add]
  exact IsPGroup.of_card hcard

variable {N : ℕ} {zu : ℚ̄₂ˣ} (hzu : IsPrimitiveRoot zu (2 ^ N))
  (a : (↥K)ˣ) {alpha : ℚ̄₂ˣ} (halpha : alpha ^ 2 ^ N = unitInQbar (K := K) a)

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- The next-precision cyclotomic shadow has open value fibres on `G_K`. -/
theorem stageKummer_chiShadow_fibre_isOpen (c : (ZMod (2 ^ N))ˣ) :
    IsOpen {g : GalK K |
      Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g) = c} := by
  have hmod : Continuous (PadicInt.toZModPow (p := 2) N) := by
    rw [continuous_def]
    intro T _
    exact isOpen_preimage_toZModPow N T
  have hset : {g : GalK K |
      Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g) = c} =
      (fun g : GalK K ↦ PadicInt.toZModPow N ((chiCycK K g : ℤ_[2]ˣ) : ℤ_[2])) ⁻¹'
        {(c : ZMod (2 ^ N))} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h]
      rfl
    · intro h
      apply Units.ext
      rw [← h]
      rfl
  rw [hset]
  exact ((hmod.comp (Units.continuous_val.comp (continuous_chiCycK K))).isOpen_preimage
    _ (isOpen_discrete _))

/-- **The lift-group assembly**: the twisted Kummer cocycle and the mod-`2^N` cyclotomic
shadow form a continuous homomorphism `G_K → WL N`. -/
def chiTwistedKummerHom : ContinuousMonoidHom (GalK K) (WL N) where
  toFun g := ⟨chiTwistedKummerFun hzu a halpha g,
    Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g)⟩
  map_one' := by
    refine WordLift.ext ?_ ?_
    · show chiTwistedKummerFun hzu a halpha 1 = 0
      exact chiTwistedKummerFun_one hzu a halpha
    · show Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K 1) = 1
      rw [map_one, map_one]
  map_mul' g h' := by
    refine WordLift.ext ?_ ?_
    · rw [WordLift.mul_u]
      show chiTwistedKummerFun hzu a halpha (g * h') =
        chiTwistedKummerFun hzu a halpha g +
          Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g) •
            chiTwistedKummerFun hzu a halpha h'
      rw [Units.smul_def, smul_eq_mul, Units.coe_map]
      exact chiTwistedKummerFun_mul hzu a halpha g h'
    · rw [WordLift.mul_g]
      show Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K (g * h')) = _
      rw [map_mul, map_mul]
  continuous_toFun := by
    rw [continuous_discrete_rng]
    intro b
    have hset : (fun g : GalK K ↦
        (⟨chiTwistedKummerFun hzu a halpha g,
          Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g)⟩ : WL N)) ⁻¹' {b} =
        chiTwistedKummerFun hzu a halpha ⁻¹' {b.u} ∩
          {g : GalK K |
            Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g) = b.g} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hEq
        exact ⟨congrArg WordLift.u hEq, congrArg WordLift.g hEq⟩
      · rintro ⟨h1, h2⟩
        exact WordLift.ext h1 h2
    rw [hset]
    exact (((chiTwistedKummerFun_continuous hzu a halpha).isOpen_preimage
        _ (isOpen_discrete _)).inter (stageKummer_chiShadow_fibre_isOpen (K := K) b.g))

/-- **The descent**: the lift-group hom factors through the maximal pro-2 quotient. -/
def chiTwistedKummerDescent (hN : 1 ≤ N) :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (WL N) :=
  (maxProPHomEquiv (isProP_of_isPGroup (stageKummer_isPGroup_WL hN))).symm
    (chiTwistedKummerHom hzu a halpha)

omit [T2Space (GalK K)] in
@[simp] theorem chiTwistedKummerDescent_mk (hN : 1 ≤ N) (g : GalK K) :
    chiTwistedKummerDescent hzu a halpha hN (maxProPMk 2 (GalK K) g) =
      chiTwistedKummerHom hzu a halpha g :=
  maxProPHomEquiv_symm_apply_maxProPMk _ _ g

omit [T2Space (GalK K)] in
/-- The descended hom is χ-shadowed over the descended cyclotomic character. -/
theorem isChiShadowDeriv_chiTwistedKummerDescent (hN : 1 ≤ N) :
    IsChiShadowDeriv (chiCycKTwo (K := K)) (chiTwistedKummerDescent hzu a halpha hN) := by
  intro q
  obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 (GalK K)) q
  show (chiTwistedKummerDescent hzu a halpha hN (maxProPMk 2 (GalK K) g)).g = _
  rw [chiTwistedKummerDescent_mk]
  show Units.map (PadicInt.toZModPow N).toMonoidHom (chiCycK K g) =
    Units.map (PadicInt.toZModPow N).toMonoidHom
      (chiCycKTwo (K := K) (maxProPMk 2 (GalK K) g))
  rw [chiCycKTwo_maxProPMk]

omit [T2Space (GalK K)] in
/-- **The descended offset is a continuous χ-twisted one-cocycle on `G_K(2)`.** -/
theorem isChiTwistedCocycle_chiTwistedKummerDescent (hN : 1 ≤ N) :
    IsChiTwistedCocycle (chiCycKTwo (K := K)) N
      (fun q ↦ (chiTwistedKummerDescent hzu a halpha hN q).u) :=
  isChiTwistedCocycle_of_isChiShadowDeriv
    (isChiShadowDeriv_chiTwistedKummerDescent hzu a halpha hN)

omit [T2Space (GalK K)] in
/-- The descended offsets on classes from `G_K` are the field-level cocycle values. -/
theorem chiTwistedKummerDescent_u_mk (hN : 1 ≤ N) (g : GalK K) :
    (chiTwistedKummerDescent hzu a halpha hN (maxProPMk 2 (GalK K) g)).u =
      chiTwistedKummerFun hzu a halpha g := by
  rw [chiTwistedKummerDescent_mk]
  rfl

end Descent

#print axioms muNDlog_smul
#print axioms chiTwistedKummerFun_mul
#print axioms chiTwistedKummerFun_parity
#print axioms chiTwistedKummerHom
#print axioms isChiTwistedCocycle_chiTwistedKummerDescent
#print axioms chiTwistedKummerDescent_u_mk

end

end GQ2.Dyadic.LSquare
