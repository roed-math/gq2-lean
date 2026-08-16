/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedSixCertificate

/-!
# The exact full-marked range surface for the `M6` ladder

`MpcMarkedSupply.lean` packages the four legal marked correction slots.  This module packages
their exact top-layer cost as a homomorphism, identifies full marked supply with membership of
the defect in its range, and states the corrected conditional induction endpoint.

The endpoint deliberately assumes the uniform successor
`MpcMkGood j → MpcMkGood (j + 1)`.  It does not assert the missing propagation theorem and
does not identify the marked cost range with a larger Fox or derivation kernel.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new axiom,
no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx GQ2.Roe.Labute GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcMkC6

noncomputable section

/-! ## 1. The exact marked cost map -/

/-- The four marked correction carriers, in head, `B`, pivot, `D` order. -/
abbrev MpcMkCostDomain (j : ℕ) :=
  mpcSxKill j × mpcSxKill j × mpcMkPivotKill j × mpcSxKill j

/-- The exact full marked cost, valued in the top layer of the rung. -/
def mpcMkCost (j : ℕ) (hj : 2 ≤ j) (t n : (DM 2 0 : Type)) :
    MpcMkCostDomain j →* zLayer (DM 2 0 : Type) (j + 1) where
  toFun u := ⟨levelMk (DM 2 0 : Type) (j + 2)
      (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2),
    mpcLad_incr_mem_zLayer t n (mpcSx_kill_le_lambda u.1.2)
      (mpcSx_kill_le_lambda u.2.1.2) u.2.2.1.2.2
      (mpcSx_kill_le_lambda u.2.2.2.2)⟩
  map_one' := by
    apply Subtype.ext
    simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one, mpcLad_incr_one, map_one]
  map_mul' u v := by
    apply Subtype.ext
    exact mpcLad_incr_hom t n
      (mpcMk_fullMove_ladMove hj ⟨u.1.2, u.2.1.2, u.2.2.1.2, u.2.2.2.2⟩)
      (mpcMk_fullMove_ladMove hj ⟨v.1.2, v.2.1.2, v.2.2.1.2, v.2.2.2.2⟩)

/-- The defect of a class-`(j+1)` solution, as an element of the next top layer. -/
def mpcMkDefectTop (j : ℕ)
    (p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type))
    (hp : p ∈ mpcWordSet (j + 1)) : zLayer (DM 2 0 : Type) (j + 1) :=
  ⟨levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p),
    ⟨mpcLadDefect p, hp.2.2.2.2, rfl⟩⟩

/-! ## 2. Supply is exact range membership -/

/-- Full marked supply is exactly membership of the top-layer defect in the marked cost
range. -/
theorem mpcMk_fullSupply_iff_mem_costRange {j : ℕ} (hj : 2 ≤ j)
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type)} (hp : p ∈ mpcWordSet (j + 1)) :
    MpcMkFullSupply j p ↔
      mpcMkDefectTop j p hp ∈
        MonoidHom.range (mpcMkCost j hj p.2.1 p.2.2.2) := by
  constructor
  · rintro ⟨us, ut, um, un, hm, hkill⟩
    let u : MpcMkCostDomain j :=
      (⟨us, hm.1⟩, ⟨ut, hm.2.1⟩, ⟨um, hm.2.2.1⟩, ⟨un, hm.2.2.2⟩)
    refine ⟨u, Subtype.ext ?_⟩
    have hone : levelMk (DM 2 0 : Type) (j + 2)
        (mpcLadDefect p * mpcBldIncr p.2.1 p.2.2.2 us ut um un) = 1 :=
      (mpcWord_mem_iff_levelMk (j + 2) _).mp hkill
    have hz : levelMk (DM 2 0 : Type) (j + 2)
        (mpcBldIncr p.2.1 p.2.2.2 us ut um un) ∈
          zLayer (DM 2 0 : Type) (j + 1) :=
      mpcLad_incr_mem_zLayer _ _ hm.1.2 hm.2.1.2 hm.2.2.1.2 hm.2.2.2.2
    change levelMk (DM 2 0 : Type) (j + 2)
        (mpcBldIncr p.2.1 p.2.2.2 us ut um un) =
      levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p)
    have hone' : levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) *
        levelMk (DM 2 0 : Type) (j + 2)
          (mpcBldIncr p.2.1 p.2.2.2 us ut um un) = 1 := by
      simpa only [map_mul] using hone
    symm
    calc
      levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) =
          (levelMk (DM 2 0 : Type) (j + 2)
            (mpcBldIncr p.2.1 p.2.2.2 us ut um un))⁻¹ :=
        eq_inv_of_mul_eq_one_left hone'
      _ = levelMk (DM 2 0 : Type) (j + 2)
          (mpcBldIncr p.2.1 p.2.2.2 us ut um un) := zLayer_inv_self hz
  · rintro ⟨u, hu⟩
    refine ⟨u.1, u.2.1, u.2.2.1, u.2.2.2,
      ⟨u.1.2, u.2.1.2, u.2.2.1.2, u.2.2.2.2⟩, ?_⟩
    rw [mpcWord_mem_iff_levelMk, map_mul]
    have heq : levelMk (DM 2 0 : Type) (j + 2)
        (mpcBldIncr p.2.1 p.2.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2) =
      levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) :=
      congrArg Subtype.val hu
    rw [heq, ← pow_two]
    exact zLayer_sq _ (mpcMkDefectTop j p hp).2

/-! ## 3. Good rungs and the corrected conditional endpoint -/

/-- A rung is good when some class-`(j+1)` solution has its defect in the exact full marked
cost range.  The depth witness makes the definition honest at every natural-number index. -/
def MpcMkGood (j : ℕ) : Prop :=
  ∃ hj : 2 ≤ j, ∃ p, ∃ hp : p ∈ mpcWordSet (j + 1),
    mpcMkDefectTop j p hp ∈
      MonoidHom.range (mpcMkCost j hj p.2.1 p.2.2.2)

/-- The range formulation is equivalent to existence of full marked supply. -/
theorem mpcMk_good_iff_exists_fullSupply {j : ℕ} (hj : 2 ≤ j) :
    MpcMkGood j ↔ ∃ p ∈ mpcWordSet (j + 1), MpcMkFullSupply j p := by
  constructor
  · rintro ⟨hj', p, hp, hr⟩
    exact ⟨p, hp, (mpcMk_fullSupply_iff_mem_costRange hj' hp).mpr hr⟩
  · rintro ⟨p, hp, hs⟩
    exact ⟨hj, p, hp, (mpcMk_fullSupply_iff_mem_costRange hj hp).mp hs⟩

/-- The already-proved class-five step is `MpcMkGood 3`. -/
theorem mpcMk_good_three : MpcMkGood 3 :=
  (mpcMk_good_iff_exists_fullSupply (by omega)).mpr mpcMk_exists_fullSupply_three

/-- An explicit full marked class-six certificate supplies the `j = 4` range base. -/
theorem mpcMk_good_four_of_fullSupply
    (h : MpcMkFullSupply 4 mpcFvW5) : MpcMkGood 4 :=
  (mpcMk_good_iff_exists_fullSupply (by omega)).mpr ⟨mpcFvW5, mpcFv_w5_mem, h⟩

/-- The explicit sparse certificate's sole Q6 equality supplies the `j = 4` range base. -/
theorem mpcMk_good_four_of_certificateKill
    (h : MpcMkC6CertificateKill) : MpcMkGood 4 :=
  mpcMk_good_four_of_fullSupply (mpcMkC6_fullSupply_of_certificateKill h)

/-- The exact class-six base and a uniform good-rung successor imply the pivot shift.  The
successor is deliberately a hypothesis: this module does not assert the missing propagation
theorem. -/
theorem mpcMk_shift_of_good_four
    (h4 : MpcMkGood 4)
    (hsucc : ∀ j, 4 ≤ j → MpcMkGood j → MpcMkGood (j + 1)) :
    MpcPivShift 2 := by
  apply mpcMk_shift_of_fullSupply
  intro j hj
  rcases lt_or_eq_of_le hj with hj' | rfl
  · have h4j : 4 ≤ j := by omega
    have hgood : MpcMkGood j := by
      have hall : ∀ k : ℕ, MpcMkGood (4 + k) := by
        intro k
        induction k with
        | zero => simpa using h4
        | succ k hk =>
            exact hsucc (4 + k) (by omega) hk
      have heq : 4 + (j - 4) = j := by omega
      rw [← heq]
      exact hall (j - 4)
    exact (mpcMk_good_iff_exists_fullSupply (by omega)).mp hgood
  · exact mpcMk_exists_fullSupply_three

/-! ## 4. Axiom pins -/

#print axioms MpcMkCostDomain
#print axioms mpcMkCost
#print axioms mpcMkDefectTop
#print axioms mpcMk_fullSupply_iff_mem_costRange
#print axioms MpcMkGood
#print axioms mpcMk_good_iff_exists_fullSupply
#print axioms mpcMk_good_three
#print axioms mpcMk_good_four_of_fullSupply
#print axioms mpcMk_good_four_of_certificateKill
#print axioms mpcMk_shift_of_good_four

end

end GQ2.Dyadic.Instances.MpcMk
