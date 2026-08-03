/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.SelectedEta
import GQ2.Dyadic.Words.Npc

/-!
# The procyclic-`N` core dictionary at `eta = 1`

This file supplies the first missing structural layer of the procyclic-`N` branch.  It constructs
the alphabet/core dictionary, uniformly in the handle count, for the display `eta = 1`:

```text
(mu0, mu1, mu2, mu3, handles)
  = (x0, sigma, x1 * sigma^(2^r), x2, handles).
```

The construction factors through the compact-`N` dictionary and a triangular change of core
generators.  The general-unit display has the same triangular part, but recovering `sigma` from
`sigma^etaHat` additionally needs an inverse-unit theorem for profinite exponentiation; that API
does not yet exist.  The exact general dictionary and the missing interface are recorded in
`docs/dyadic/followup/npc-branch-plan.md`.

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

/-! ## Dictionary, relation transport, and core presentation -/

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
