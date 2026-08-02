/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo
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
