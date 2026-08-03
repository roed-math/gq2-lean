/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.SelectedEta
import GQ2.Dyadic.Words.Npc

/-!
# The procyclic-`N` core dictionary at an arbitrary selected unit

This file constructs the alphabet/core dictionary and `CorePresentation`, uniformly in the
handle count, for every selected unit `eta : Z_2^*` carrying its compatible display:

```text
(mu0, mu1, mu2, mu3, handles)
  = (x0, sigma, x1 * sigma^(2^r), x2, handles).
```

The construction factors through the compact-`N` dictionary and a triangular change of core
generators.  Recovering `sigma` from `sigma^etaHat` is done only where the universal property
actually needs it: in pro-2 groups, using `Z_2`-powering by `eta⁻¹`.  The bridge
`zpowHat_etaHatZ_eq_zpowZtwo` proves that the semantic profinite exponent is exactly this
`Z_2`-power.  The original `eta = 1` dictionary remains below as a regression endpoint.

No lower bound on `alpha` or `r` is needed here.  This is group-presentation plumbing only.
-/

namespace GQ2.Dyadic.Instances

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Count.PilotN

namespace NProcyclicCore

/-! ## The arbitrary-unit pro-2 powering seam -/

/-- On an element killed by `2^k`, `Z_2`-powering is evaluation at the standard residue
modulo `2^k`.  This is the all-level form of `SectionThree.zpowZtwo_of_sq_eq_one`. -/
private theorem zpowZtwo_eq_pow_toZModPow {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (k : ℕ) (hx : x ^ (2 ^ k) = 1) (u : ℤ_[2]) :
    zpowZtwo hP x u = x ^ (PadicInt.toZModPow k u).val := by
  have h := zpowZtwoHom_unique hP (φ := powZModTwoHom x k hx)
    (continuous_powZModTwoHom x k hx) u
  have hone : powZModTwoHom x k hx (Multiplicative.ofAdd (1 : ℤ_[2])) = x := by
    show x ^ (PadicInt.toZModPow k (Multiplicative.ofAdd (1 : ℤ_[2])).toAdd).val = x
    rw [show (Multiplicative.ofAdd (1 : ℤ_[2])).toAdd = (1 : ℤ_[2]) from rfl, map_one]
    by_cases hk : k = 0
    · have hx1 : x = 1 := by simpa [hk] using hx
      simp [hx1]
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr hk), pow_one]
  rw [hone] at h
  exact h.symm

/-- The semantic lift `padicOmega2 u` acts on a pro-2 group by ordinary `Z_2`-powering.

This is the missing bridge behind the arbitrary-unit `Npc` dictionary.  Its proof is quotientwise:
at every finite pro-2 quotient the element has `2`-power order, so both sides use the same
`toZModPow` residue. -/
theorem zpowHat_padicOmega2_eq_zpowZtwo {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) :
    x ^ᶻ padicOmega2 u = zpowZtwo hP x u := by
  apply mul_inv_eq_one.mp
  refine eq_one_of_forall_mem_openNormalSubgroup fun U => ?_
  let q : ContinuousMonoidHom P (P ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  haveI : DiscreteTopology (P ⧸ U.toSubgroup) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hpre : (QuotientGroup.mk : P → P ⧸ U.toSubgroup) ⁻¹' {1}
        = (U.toSubgroup : Set P) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
        QuotientGroup.eq_one_iff]
    rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
    exact U.isOpen'
  haveI : Finite (P ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  have hQU : IsProP 2 (P ⧸ U.toSubgroup) := isProP_of_isPGroup (hP U)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (hP U)) (q x)
  have heq : q (x ^ᶻ padicOmega2 u) = q (zpowZtwo hP x u) := by
    by_cases hk0 : k = 0
    · have hqx : q x = 1 := orderOf_eq_one_iff.mp (by simpa [hk0] using hk)
      rw [map_zpowHat, zpowHat_padicOmega2, hqx, one_pow,
        map_zpowZtwo hP hQU, hqx, zpowZtwo_one_base]
    · have hpow : (q x) ^ (2 ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
      have homega : omega2Exp (2 ^ k) = 1 := by
        have hfac : (2 ^ k).factorization 2 = k := by
          rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
        have hpos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
        have hlt : (1 : ℕ) < 2 ^ k := Nat.one_lt_two_pow_iff.mpr hk0
        rw [omega2Exp]
        simp only [hfac, if_neg hk0, Nat.div_self hpos, one_pow, Nat.mod_eq_of_lt hlt]
      have hleft : q (x ^ᶻ padicOmega2 u) =
        (q x) ^ (PadicInt.toZModPow k u).val := by
        rw [map_zpowHat, zpowHat_padicOmega2, hk, padicOmega2Exp,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, homega, mul_one]
      have hright : q (zpowZtwo hP x u) =
        (q x) ^ (PadicInt.toZModPow k u).val := by
        rw [map_zpowZtwo hP hQU]
        exact zpowZtwo_eq_pow_toZModPow hQU (q x) k hpow u
      exact hleft.trans hright.symm
  have hone : q ((x ^ᶻ padicOmega2 u) * (zpowZtwo hP x u)⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  have hone' : (((x ^ᶻ padicOmega2 u) * (zpowZtwo hP x u)⁻¹ : P) :
      P ⧸ U.toSubgroup) = 1 := by
    change q ((x ^ᶻ padicOmega2 u) * (zpowZtwo hP x u)⁻¹) = 1
    exact hone
  exact (QuotientGroup.eq_one_iff _).mp hone'

/-- On pro-2 groups the semantic exponent `etaHatZ eta` is exactly `eta`-powering. -/
theorem zpowHat_etaHatZ_eq_zpowZtwo {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (eta : ℤ_[2]) :
    x ^ᶻ etaHatZ eta = zpowZtwo hP x eta := by
  rw [etaHatZ, zpowHat_mul, zpowHat_ofInt, zpow_one,
    zpowHat_padicOmega2_eq_zpowZtwo hP]
  calc
    x * zpowZtwo hP x (eta - 1) =
        zpowZtwo hP x 1 * zpowZtwo hP x (eta - 1) := by rw [zpowZtwo_one_exp]
    _ = zpowZtwo hP x (1 + (eta - 1)) := (zpowZtwo_add hP x 1 (eta - 1)).symm
    _ = zpowZtwo hP x eta := by congr 2; ring

/-! ## The `eta = 1` exponent -/

private theorem padicOmega2_zero : padicOmega2 (0 : ℤ_[2]) = 1 := by
  apply Subtype.ext
  funext H
  simp [padicOmega2, padicOmega2Exp]
  rfl

/-- The frozen syntactic display `<1,1>` denotes the ordinary exponent `1` in `Zhat`. -/
theorem etaDataOne_toZhat : (EtaData.mk 1 1).toZhat = Zhat.ofInt 1 := by
  rw [EtaData.toZhat]
  have hpadic : (EtaData.mk 1 1).toPadic = 1 := by
    rw [EtaData.toPadic]
    have hinv : PadicInt.inv (1 : ℤ_[2]) = 1 := by
      simpa using PadicInt.mul_inv (z := (1 : ℤ_[2])) (norm_one : ‖(1 : ℤ_[2])‖ = 1)
    simp only [Int.cast_one, hinv, mul_one]
  rw [hpadic, etaHatZ, sub_self, padicOmega2_zero, mul_one]

/-- Profinite powering at the display `<1,1>` is the identity. -/
@[simp] theorem zpowHat_etaDataOne {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (x : G) :
    x ^ᶻ (EtaData.mk 1 1).toZhat = x := by
  rw [etaDataOne_toZhat, zpowHat_ofInt, zpow_one]

/-! ## The triangular core change of variables -/

variable {G : Type*} [Group G]

/-- Forward core twist at `eta = 1`: swap the old `sigma` into slot `1`, and put
`x1 * sigma^(2^r)` in slot `2`. -/
def npcTwistOne (r h : ℕ) (c : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  fun i => if (i : ℕ) = 1 then c 2
    else if (i : ℕ) = 2 then c 1 * c 2 ^ ((2 : ℤ) ^ r)
    else c i

/-- Inverse triangular core twist at `eta = 1`. -/
def npcUntwistOne (r h : ℕ) (c : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  fun i => if (i : ℕ) = 1 then c 2 * c 1 ^ (-((2 : ℤ) ^ r))
    else if (i : ℕ) = 2 then c 1
    else c i

theorem npcTwistOne_apply_ne (r h : ℕ) (c : Fin (coreRank h) → G) {i : Fin (coreRank h)}
    (h1 : (i : ℕ) ≠ 1) (h2 : (i : ℕ) ≠ 2) : npcTwistOne r h c i = c i := by
  simp only [npcTwistOne, if_neg h1, if_neg h2]

theorem npcUntwistOne_apply_ne (r h : ℕ) (c : Fin (coreRank h) → G) {i : Fin (coreRank h)}
    (h1 : (i : ℕ) ≠ 1) (h2 : (i : ℕ) ≠ 2) : npcUntwistOne r h c i = c i := by
  simp only [npcUntwistOne, if_neg h1, if_neg h2]

@[simp] theorem npcTwistOne_zero (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcTwistOne r h c 0 = c 0 :=
  npcTwistOne_apply_ne r h c (by rw [coreVal_zero]; omega) (by rw [coreVal_zero]; omega)

@[simp] theorem npcTwistOne_one (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcTwistOne r h c 1 = c 2 := by
  rw [npcTwistOne, if_pos (coreVal_one h)]

@[simp] theorem npcTwistOne_two (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcTwistOne r h c 2 = c 1 * c 2 ^ ((2 : ℤ) ^ r) := by
  rw [npcTwistOne, if_neg (by rw [coreVal_two]; omega), if_pos (coreVal_two h)]

@[simp] theorem npcTwistOne_three (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcTwistOne r h c 3 = c 3 :=
  npcTwistOne_apply_ne r h c (by rw [coreVal_three]; omega) (by rw [coreVal_three]; omega)

@[simp] theorem npcTwistOne_handleIdxU (r h : ℕ) (c : Fin (coreRank h) → G) (j : Fin h) :
    npcTwistOne r h c (handleIdxU j) = c (handleIdxU j) :=
  npcTwistOne_apply_ne r h c (by rw [handleIdxU_val]; omega) (by rw [handleIdxU_val]; omega)

@[simp] theorem npcTwistOne_handleIdxV (r h : ℕ) (c : Fin (coreRank h) → G) (j : Fin h) :
    npcTwistOne r h c (handleIdxV j) = c (handleIdxV j) :=
  npcTwistOne_apply_ne r h c (by rw [handleIdxV_val]; omega) (by rw [handleIdxV_val]; omega)

@[simp] theorem npcUntwistOne_one (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcUntwistOne r h c 1 = c 2 * c 1 ^ (-((2 : ℤ) ^ r)) := by
  rw [npcUntwistOne, if_pos (coreVal_one h)]

@[simp] theorem npcUntwistOne_two (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcUntwistOne r h c 2 = c 1 := by
  rw [npcUntwistOne, if_neg (by rw [coreVal_two]; omega), if_pos (coreVal_two h)]

theorem npcTwistOne_npcUntwistOne (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcTwistOne r h (npcUntwistOne r h c) = c := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
    subst hi
    rw [npcTwistOne_one, npcUntwistOne_two]
  · by_cases h2 : (i : ℕ) = 2
    · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
      subst hi
      rw [npcTwistOne_two, npcUntwistOne_one, npcUntwistOne_two]
      group
    · rw [npcTwistOne_apply_ne _ _ _ h1 h2, npcUntwistOne_apply_ne _ _ _ h1 h2]

theorem npcUntwistOne_npcTwistOne (r h : ℕ) (c : Fin (coreRank h) → G) :
    npcUntwistOne r h (npcTwistOne r h c) = c := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
    subst hi
    rw [npcUntwistOne_one, npcTwistOne_two, npcTwistOne_one]
    group
  · by_cases h2 : (i : ℕ) = 2
    · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
      subst hi
      rw [npcUntwistOne_two, npcTwistOne_one]
    · rw [npcUntwistOne_apply_ne _ _ _ h1 h2, npcTwistOne_apply_ne _ _ _ h1 h2]

theorem map_npcTwistOne {H : Type*} [Group H] {F : Type*} [FunLike F G H]
    [MonoidHomClass F G H] (f : F) (r h : ℕ) (c : Fin (coreRank h) → G) :
    (fun i ↦ f (npcTwistOne r h c i)) = npcTwistOne r h (fun i ↦ f (c i)) := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · simp only [npcTwistOne, if_pos h1]
  · by_cases h2 : (i : ℕ) = 2
    · simp only [npcTwistOne, if_neg h1, if_pos h2, map_mul, map_zpow]
    · simp only [npcTwistOne, if_neg h1, if_neg h2]

theorem map_npcUntwistOne {H : Type*} [Group H] {F : Type*} [FunLike F G H]
    [MonoidHomClass F G H] (f : F) (r h : ℕ) (c : Fin (coreRank h) → G) :
    (fun i ↦ f (npcUntwistOne r h c i)) = npcUntwistOne r h (fun i ↦ f (c i)) := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · simp only [npcUntwistOne, if_pos h1, map_mul, map_zpow]
  · by_cases h2 : (i : ℕ) = 2
    · simp only [npcUntwistOne, if_neg h1, if_pos h2]
    · simp only [npcUntwistOne, if_neg h1, if_neg h2]

/-! ## The arbitrary-unit triangular dictionary on pro-2 groups -/

section UnitTwist

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- Forward `Npc` core twist for an arbitrary selected unit. -/
noncomputable def npcTwistUnit (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) : Fin (coreRank h) → P :=
  fun i ↦ if (i : ℕ) = 1 then zpowZtwo hP (c 2) (eta : ℤ_[2])
    else if (i : ℕ) = 2 then c 1 * c 2 ^ ((2 : ℤ) ^ r)
    else c i

/-- Inverse `Npc` twist: recover the alphabet `sigma` by the `eta⁻¹`-power. -/
noncomputable def npcUntwistUnit (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) : Fin (coreRank h) → P :=
  let s := zpowZtwo hP (c 1) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
  fun i ↦ if (i : ℕ) = 1 then c 2 * s ^ (-((2 : ℤ) ^ r))
    else if (i : ℕ) = 2 then s
    else c i

@[simp] theorem npcTwistUnit_one (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcTwistUnit hP eta r h c 1 = zpowZtwo hP (c 2) (eta : ℤ_[2]) := by
  rw [npcTwistUnit, if_pos (coreVal_one h)]

@[simp] theorem npcTwistUnit_two (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcTwistUnit hP eta r h c 2 = c 1 * c 2 ^ ((2 : ℤ) ^ r) := by
  rw [npcTwistUnit, if_neg (by rw [coreVal_two]; omega), if_pos (coreVal_two h)]

theorem npcTwistUnit_apply_ne (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) {i : Fin (coreRank h)}
    (h1 : (i : ℕ) ≠ 1) (h2 : (i : ℕ) ≠ 2) : npcTwistUnit hP eta r h c i = c i := by
  simp only [npcTwistUnit, if_neg h1, if_neg h2]

@[simp] theorem npcTwistUnit_zero (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) : npcTwistUnit hP eta r h c 0 = c 0 :=
  npcTwistUnit_apply_ne hP eta r h c (by rw [coreVal_zero]; omega)
    (by rw [coreVal_zero]; omega)

@[simp] theorem npcTwistUnit_three (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) : npcTwistUnit hP eta r h c 3 = c 3 :=
  npcTwistUnit_apply_ne hP eta r h c (by rw [coreVal_three]; omega)
    (by rw [coreVal_three]; omega)

@[simp] theorem npcTwistUnit_handleIdxU (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) (j : Fin h) :
    npcTwistUnit hP eta r h c (handleIdxU j) = c (handleIdxU j) :=
  npcTwistUnit_apply_ne hP eta r h c (by rw [handleIdxU_val]; omega)
    (by rw [handleIdxU_val]; omega)

@[simp] theorem npcTwistUnit_handleIdxV (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) (j : Fin h) :
    npcTwistUnit hP eta r h c (handleIdxV j) = c (handleIdxV j) :=
  npcTwistUnit_apply_ne hP eta r h c (by rw [handleIdxV_val]; omega)
    (by rw [handleIdxV_val]; omega)

@[simp] theorem npcUntwistUnit_one (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcUntwistUnit hP eta r h c 1 =
      c 2 * zpowZtwo hP (c 1) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ (-((2 : ℤ) ^ r)) := by
  simp only [npcUntwistUnit]
  rw [if_pos (coreVal_one h)]

@[simp] theorem npcUntwistUnit_two (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcUntwistUnit hP eta r h c 2 =
      zpowZtwo hP (c 1) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
  simp only [npcUntwistUnit]
  rw [if_neg (by rw [coreVal_two]; omega), if_pos (coreVal_two h)]

theorem npcUntwistUnit_apply_ne (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) {i : Fin (coreRank h)}
    (h1 : (i : ℕ) ≠ 1) (h2 : (i : ℕ) ≠ 2) : npcUntwistUnit hP eta r h c i = c i := by
  simp only [npcUntwistUnit, if_neg h1, if_neg h2]

theorem zpowZtwo_unit_inv_cancel (hP : IsProP 2 P) (x : P) (eta : ℤ_[2]ˣ) :
    zpowZtwo hP (zpowZtwo hP x (eta : ℤ_[2])) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = x := by
  rw [zpowZtwo_zpowZtwo, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    zpowZtwo_one_exp]

theorem zpowZtwo_inv_unit_cancel (hP : IsProP 2 P) (x : P) (eta : ℤ_[2]ˣ) :
    zpowZtwo hP (zpowZtwo hP x ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) (eta : ℤ_[2]) = x := by
  rw [zpowZtwo_zpowZtwo, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    zpowZtwo_one_exp]

theorem npcTwistUnit_npcUntwistUnit (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcTwistUnit hP eta r h (npcUntwistUnit hP eta r h c) = c := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
    subst hi
    rw [npcTwistUnit_one, npcUntwistUnit_two, zpowZtwo_inv_unit_cancel]
  · by_cases h2 : (i : ℕ) = 2
    · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
      subst hi
      rw [npcTwistUnit_two, npcUntwistUnit_one, npcUntwistUnit_two]
      group
    · rw [npcTwistUnit_apply_ne _ _ _ _ _ h1 h2,
        npcUntwistUnit_apply_ne _ _ _ _ _ h1 h2]

theorem npcUntwistUnit_npcTwistUnit (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcUntwistUnit hP eta r h (npcTwistUnit hP eta r h c) = c := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
    subst hi
    rw [npcUntwistUnit_one, npcTwistUnit_two, npcTwistUnit_one,
      zpowZtwo_unit_inv_cancel]
    group
  · by_cases h2 : (i : ℕ) = 2
    · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
      subst hi
      rw [npcUntwistUnit_two, npcTwistUnit_one, zpowZtwo_unit_inv_cancel]
    · rw [npcUntwistUnit_apply_ne _ _ _ _ _ h1 h2,
        npcTwistUnit_apply_ne _ _ _ _ _ h1 h2]

theorem map_npcTwistUnit {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)
    (eta : ℤ_[2]ˣ) (r h : ℕ) (c : Fin (coreRank h) → P) :
    (fun i ↦ f (npcTwistUnit hP eta r h c i)) =
      npcTwistUnit hQ eta r h (fun i ↦ f (c i)) := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · simp only [npcTwistUnit, if_pos h1, map_zpowZtwo hP hQ]
  · by_cases h2 : (i : ℕ) = 2
    · simp only [npcTwistUnit, if_neg h1, if_pos h2, map_mul, map_zpow]
    · simp only [npcTwistUnit, if_neg h1, if_neg h2]

theorem map_npcUntwistUnit {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)
    (eta : ℤ_[2]ˣ) (r h : ℕ) (c : Fin (coreRank h) → P) :
    (fun i ↦ f (npcUntwistUnit hP eta r h c i)) =
      npcUntwistUnit hQ eta r h (fun i ↦ f (c i)) := by
  funext i
  by_cases h1 : (i : ℕ) = 1
  · simp only [npcUntwistUnit, if_pos h1, map_mul, map_zpow, map_zpowZtwo hP hQ]
  · by_cases h2 : (i : ℕ) = 2
    · simp only [npcUntwistUnit, if_neg h1, if_pos h2, map_zpowZtwo hP hQ]
    · simp only [npcUntwistUnit, if_neg h1, if_neg h2]

/-- Alphabet marking to standard `D_N` core coordinates, specialized to pro-2 groups. -/
noncomputable def npcToCoreUnit (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (t : Marking (2 + 2 * h) P) : Fin (coreRank h) → P :=
  npcTwistUnit hP eta r h ((nReindex h).toCore t)

/-- Standard `D_N` core coordinates to the arbitrary-unit `Npc` alphabet marking. -/
noncomputable def npcOfCoreUnit (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) : Marking (2 + 2 * h) P :=
  (nReindex h).ofCore (npcUntwistUnit hP eta r h c)

@[simp] theorem npcOfCoreUnit_tau (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) : (npcOfCoreUnit hP eta r h c).τ = 1 :=
  (nReindex h).ofCore_tau _

theorem npcToCoreUnit_ofCore (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) :
    npcToCoreUnit hP eta r h (npcOfCoreUnit hP eta r h c) = c := by
  rw [npcToCoreUnit, npcOfCoreUnit, (nReindex h).toCore_ofCore,
    npcTwistUnit_npcUntwistUnit]

theorem npcOfCoreUnit_toCore (hP : IsProP 2 P) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (t : Marking (2 + 2 * h) P) (ht : t.τ = 1) :
    npcOfCoreUnit hP eta r h (npcToCoreUnit hP eta r h t) = t := by
  rw [npcOfCoreUnit, npcToCoreUnit, npcUntwistUnit_npcTwistUnit,
    (nReindex h).ofCore_toCore t ht]

end UnitTwist

/-! ## Dictionary, relation transport, and core presentation -/

/-- The arbitrary-unit semantic `Npc` word reads as the standard `N` relator after the
pro-2-specialized dictionary. -/
theorem npcProTwoWordUnit (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta)
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP 2 P)
    (t : Marking (2 + 2 * h) P) :
    t.eval (pro2 (npcWUnit alpha r h eta)) =
      nRelWord alpha (npcToCoreUnit hP eta r h t) := by
  rw [npcWUnit_eq_display alpha r h d, eval_pro2_npcW,
    EtaData.toZhat_eq_etaHatZ d.represents, zpowHat_etaHatZ_eq_zpowZtwo hP]
  show _ = nRelWord alpha
    (npcTwistUnit hP eta r h (fun i ↦ t (nIdx h i)))
  simp only [nRelWord, npcTwistUnit_zero, npcTwistUnit_one, npcTwistUnit_two,
    npcTwistUnit_three, npcTwistUnit_handleIdxU, npcTwistUnit_handleIdxV,
    nIdx_zero, nIdx_one, nIdx_two, nIdx_three, nIdx_handleIdxU, nIdx_handleIdxV,
    Marking.apply_sigma]

theorem npcToCoreUnit_nat {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] (hP : IsProP 2 P) (hQ : IsProP 2 Q)
    (f : ContinuousMonoidHom P Q) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (t : Marking (2 + 2 * h) P) :
    (fun i ↦ f (npcToCoreUnit hP eta r h t i)) =
      npcToCoreUnit hQ eta r h (t.map ⇑f) := by
  rw [npcToCoreUnit, npcToCoreUnit]
  calc
    (fun i ↦ f (npcTwistUnit hP eta r h ((nReindex h).toCore t) i)) =
        npcTwistUnit hQ eta r h (fun i ↦ f ((nReindex h).toCore t i)) :=
      map_npcTwistUnit hP hQ f eta r h _
    _ = npcTwistUnit hQ eta r h ((nReindex h).toCore (t.map ⇑f)) := by
      congr 1

theorem npcOfCoreUnit_nat {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] (hP : IsProP 2 P) (hQ : IsProP 2 Q)
    (f : ContinuousMonoidHom P Q) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) (g : Generator (2 + 2 * h)) :
    f (npcOfCoreUnit hP eta r h c g) =
      npcOfCoreUnit hQ eta r h (fun i ↦ f (c i)) g := by
  rw [npcOfCoreUnit, npcOfCoreUnit, (nReindex h).ofCore_nat]
  exact congrArg (fun m ↦ (nReindex h).ofCore m g)
    (map_npcUntwistUnit hP hQ f eta r h c)

/-- Naturality needed for uniqueness into an arbitrary profinite codomain.  The source is pro-2,
but the target need not be: rewrite its `Z_2`-power as the semantic `Zhat`-power first. -/
theorem npcTwistUnit_hom_eq {P A : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A]
    [TotallyDisconnectedSpace A] (hP : IsProP 2 P)
    (phi psi : ContinuousMonoidHom P A) (eta : ℤ_[2]ˣ) (r h : ℕ)
    (c : Fin (coreRank h) → P) (hc : ∀ i, phi (c i) = psi (c i)) :
    ∀ i, phi (npcTwistUnit hP eta r h c i) =
      psi (npcTwistUnit hP eta r h c i) := by
  intro i
  by_cases h1 : (i : ℕ) = 1
  · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
    subst hi
    rw [npcTwistUnit_one, ← zpowHat_etaHatZ_eq_zpowZtwo hP,
      map_zpowHat, map_zpowHat, hc]
  · by_cases h2 : (i : ℕ) = 2
    · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
      subst hi
      rw [npcTwistUnit_two, map_mul, map_mul, map_zpow, map_zpow, hc, hc]
    · rw [npcTwistUnit_apply_ne _ _ _ _ _ h1 h2]
      exact hc i

/-- The procyclic-`N` core presentation for an arbitrary selected unit and every handle count. -/
noncomputable def npcCorePresentationUnit (alpha r h : ℕ) (eta : ℤ_[2]ˣ)
    (d : NpcDisplayFor eta) :
    CorePresentation (2 + 2 * h) (npcWUnit alpha r h eta) (DN alpha h) where
  isProP := isProP_DN alpha h
  mark := npcOfCoreUnit (isProP_DN alpha h) eta r h (dnGen alpha h)
  mark_tau := npcOfCoreUnit_tau _ _ _ _ _
  rel := by
    rw [npcProTwoWordUnit alpha r h eta d (isProP_DN alpha h),
      npcToCoreUnit_ofCore, dn_relation]
  liftHom := fun hQ t _ hrel ↦
    (presentedBy_DN alpha h).liftHom hQ (npcToCoreUnit hQ eta r h t) (by
      change nRelWord alpha (npcToCoreUnit hQ eta r h t) = 1
      rw [← npcProTwoWordUnit alpha r h eta d hQ]
      exact hrel)
  liftHom_mark := fun hQ t ht hrel g ↦ by
    rw [npcOfCoreUnit_nat (isProP_DN alpha h) hQ]
    have hpt : (fun i ↦ (presentedBy_DN alpha h).liftHom hQ
        (npcToCoreUnit hQ eta r h t) (by
          change nRelWord alpha (npcToCoreUnit hQ eta r h t) = 1
          rw [← npcProTwoWordUnit alpha r h eta d hQ]
          exact hrel) (dnGen alpha h i)) = npcToCoreUnit hQ eta r h t := by
      funext i
      exact (presentedBy_DN alpha h).liftHom_mark hQ (npcToCoreUnit hQ eta r h t) _ i
    rw [hpt, npcOfCoreUnit_toCore _ _ _ _ t ht]
  hom_ext := fun phi psi heq ↦ (presentedBy_DN alpha h).hom_ext phi psi fun i ↦ by
    have hletters : ∀ k, phi ((nReindex h).toCore
        (npcOfCoreUnit (isProP_DN alpha h) eta r h (dnGen alpha h)) k) =
        psi ((nReindex h).toCore
          (npcOfCoreUnit (isProP_DN alpha h) eta r h (dnGen alpha h)) k) := by
      intro k
      exact heq (nIdx h k)
    have htwist := npcTwistUnit_hom_eq (isProP_DN alpha h) phi psi eta r h
      ((nReindex h).toCore
        (npcOfCoreUnit (isProP_DN alpha h) eta r h (dnGen alpha h))) hletters i
    have hcore := congrFun (npcToCoreUnit_ofCore (isProP_DN alpha h) eta r h
      (dnGen alpha h)) i
    rw [npcToCoreUnit] at hcore
    rw [hcore] at htwist
    exact htwist

/-- The procyclic-`N` dictionary at `eta = 1`, uniformly in the handle count. -/
noncomputable def npcReindexOne (r h : ℕ) :
    CoreReindex (2 + 2 * h) (Fin (coreRank h)) where
  toCore := fun t ↦ npcTwistOne r h ((nReindex h).toCore t)
  ofCore := fun c ↦ (nReindex h).ofCore (npcUntwistOne r h c)
  ofCore_tau := fun c ↦ (nReindex h).ofCore_tau (npcUntwistOne r h c)
  toCore_ofCore := fun c ↦ by
    rw [(nReindex h).toCore_ofCore (npcUntwistOne r h c), npcTwistOne_npcUntwistOne]
  ofCore_toCore := fun t ht ↦ by
    rw [npcUntwistOne_npcTwistOne, (nReindex h).ofCore_toCore t ht]
  toCore_nat := fun f t k ↦ by
    have hnat : (fun i ↦ f ((nReindex h).toCore t i)) = (nReindex h).toCore (t.map ⇑f) :=
      funext fun i ↦ (nReindex h).toCore_nat f t i
    calc f (npcTwistOne r h ((nReindex h).toCore t) k)
        = npcTwistOne r h (fun i ↦ f ((nReindex h).toCore t i)) k :=
          congrFun (map_npcTwistOne f r h ((nReindex h).toCore t)) k
      _ = npcTwistOne r h ((nReindex h).toCore (t.map ⇑f)) k := by rw [hnat]
  ofCore_nat := fun f c g ↦ by
    rw [(nReindex h).ofCore_nat f (npcUntwistOne r h c) g]
    exact congrArg (fun m ↦ (nReindex h).ofCore m g) (map_npcUntwistOne f r h c)

/-- The relation read through the `eta = 1` procyclic-`N` dictionary. -/
def npcCoreRelOne (alpha r h : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking (2 + 2 * h) G) : G :=
  nRelWord alpha (npcTwistOne r h (fun i ↦ t (nIdx h i)))

/-- The landed word-level pro-2 equality transported through `npcReindexOne`. -/
theorem npcProTwoWordOne (alpha r h : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (npcW alpha r h ⟨1, 1⟩)) = npcCoreRelOne alpha r h G t := by
  rw [eval_pro2_npcW]
  show _ = nRelWord alpha (npcTwistOne r h (fun i ↦ t (nIdx h i)))
  simp only [nRelWord, npcTwistOne_zero, npcTwistOne_one, npcTwistOne_two,
    npcTwistOne_three, npcTwistOne_handleIdxU, npcTwistOne_handleIdxV, nIdx_zero, nIdx_one,
    nIdx_two, nIdx_three, nIdx_handleIdxU, nIdx_handleIdxV, Marking.apply_sigma,
    zpowHat_etaDataOne]

/-- The relation transport in the shape consumed by `CorePresentation.ofPresentedBy`. -/
theorem eval_pro2_npcW_one_reindex (alpha r h : ℕ) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (npcW alpha r h ⟨1, 1⟩)) =
      (nNatWord alpha h).ev ((npcReindexOne r h).toCore t) :=
  npcProTwoWordOne alpha r h G t

/-- The procyclic-`N` core presentation at `eta = 1`, for every handle count. -/
noncomputable def npcCorePresentationOne (alpha r h : ℕ) :
    CorePresentation (2 + 2 * h) (npcW alpha r h ⟨1, 1⟩) (DN alpha h) :=
  CorePresentation.ofPresentedBy (isProP_DN alpha h) (presentedBy_DN alpha h)
    (dn_relation alpha h) (npcReindexOne r h)
    (fun t ↦ eval_pro2_npcW_one_reindex alpha r h t)

end NProcyclicCore

end GQ2.Dyadic.Instances
