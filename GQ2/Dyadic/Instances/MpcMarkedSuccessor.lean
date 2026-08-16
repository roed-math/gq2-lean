/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedRange

/-!
# The exact marked successor interface for the M6 ladder

`MpcMarkedRange.lean` identifies full marked supply with membership of the current defect in
the exact four-slot cost range.  This module retains the corresponding range witness as an
explicit next point and proves that the successor cost map is unchanged by the visible base
shifts in the preceding move.

The resulting conditional successor does not assert the missing propagation theorem.  Its sole
new mathematical input is the honest one: the secondary defect of the recursively advanced
point must lie in the next, now-frozen, corank-five marked cost range.  No larger Fox or
derivation kernel is claimed to be the range.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new axiom,
no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

/-! ## 1. The explicit advanced point -/

/-- Apply a full marked cost-domain element to a correction quadruple. -/
def mpcMkAdvance (j : ℕ)
    (p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type))
    (u : MpcMkCostDomain j) :
    (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) :=
  (p.1 * u.1, p.2.1 * u.2.1, p.2.2.1 * u.2.2.1, p.2.2.2 * u.2.2.2)

/-- An exact marked cost witness produces the corresponding explicit point on the next rung. -/
theorem mpcMk_advance_mem {j : ℕ} (hj : 2 ≤ j)
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type)}
    (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j hj p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    mpcMkAdvance j p u ∈ mpcWordSet (j + 2) := by
  have hm : MpcMkFullMove j u.1 u.2.1 u.2.2.1 u.2.2.2 :=
    ⟨u.1.2, u.2.1.2, u.2.2.1.2, u.2.2.2.2⟩
  have hl := mpcMk_fullMove_ladMove hj hm
  apply mpcBld_step hp u.1 u.2.1 u.2.2.1 u.2.2.2
    hl.1.1 hl.1.2 hl.2.1.1 hl.2.1.2 hl.2.2.1.1 hl.2.2.1.2
    hl.2.2.2.1 hl.2.2.2.2
  rw [mpcWord_mem_iff_levelMk, map_mul]
  have heq : levelMk (DM 2 0 : Type) (j + 2)
      (mpcBldIncr p.2.1 p.2.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2) =
      levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) :=
    congrArg Subtype.val hu
  rw [heq]
  change levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) *
      levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) = 1
  rw [← pow_two]
  exact zLayer_sq _ (mpcMkDefectTop j p hp).2

/-! ## 2. The successor cost fiber -/

/-- At the successor layer, changing the two visible base slots by the preceding depth-`j`
move does not change the marked cost map. -/
theorem mpcMk_cost_succ_base_indep {j : ℕ} (hj : 2 ≤ j)
    (t n : (DM 2 0 : Type)) {ut un : (DM 2 0 : Type)}
    (hutj : ut ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hunj : un ∈ twoCentralSeries (DM 2 0 : Type) j) :
    mpcMkCost (j + 1) (by omega) (t * ut) (n * un) =
      mpcMkCost (j + 1) (by omega) t n := by
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  have hdrop : ∀ {a x e : levelQuot (DM 2 0 : Type) (j + 3)},
      a ∈ lambdaImage (DM 2 0 : Type) (j + 1) (j + 3) →
      e ∈ lambdaImage (DM 2 0 : Type) j (j + 3) →
      commP a (x * e) = commP a x := by
    intro a x e ha he
    have he2 : e ∈ lambdaImage (DM 2 0 : Type) 2 (j + 3) := by
      obtain ⟨ee, hee, rfl⟩ := he
      exact ⟨ee, twoCentralSeries_antitone (G := (DM 2 0 : Type)) hj hee, rfl⟩
    have hea : commP e a = 1 := mpcLad_vanish he2 ha
    have hae : commP a e = 1 := by rw [mpcSx_swap, hea, inv_one]
    rw [cfour_commP_mul_right,
      cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left ha x) e,
      hae]
    simp only [one_mul, mul_one]
  have hB : mpcWordLetB (t * ut) = mpcWordLetB t * ut := by
    rw [mpcWordLetB, mpcWordLetB, mul_assoc]
  have hD : mpcWordLetD (n * un) = mpcWordLetD n * un := by
    rw [mpcWordLetD, mpcWordLetD, mul_assoc]
  change levelMk (DM 2 0 : Type) (j + 3)
      (mpcBldIncr (t * ut) (n * un) u.1 u.2.1 u.2.2.1 u.2.2.2) =
    levelMk (DM 2 0 : Type) (j + 3)
      (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2)
  simp only [mpcBldIncr, hB, hD, map_mul, map_pow, mpcBld_map_commP]
  rw [hdrop ⟨u.1, u.1.2.2, rfl⟩ ⟨ut, hutj, rfl⟩,
    hdrop ⟨u.2.2.1, u.2.2.1.2.2, rfl⟩ ⟨un, hunj, rfl⟩]

/-! ## 3. The exact remaining successor input -/

/-- The uniform successor is reduced to the secondary defect of the explicit advanced point,
tested against the old point's now-frozen successor cost range.  This theorem does not assert
that range membership; it isolates it as the remaining mathematical input. -/
theorem mpcMk_good_succ_of_advance_range {j : ℕ} (hj : 2 ≤ j)
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type)}
    (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j hj p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp)
    (hnext : mpcMkDefectTop (j + 1) (mpcMkAdvance j p u)
        (mpcMk_advance_mem hj hp u hu) ∈
      MonoidHom.range (mpcMkCost (j + 1) (by omega) p.2.1 p.2.2.2)) :
    MpcMkGood (j + 1) := by
  let q := mpcMkAdvance j p u
  have hq : q ∈ mpcWordSet (j + 2) := mpcMk_advance_mem hj hp u hu
  refine ⟨by omega, q, hq, ?_⟩
  have hcost := mpcMk_cost_succ_base_indep hj p.2.1 p.2.2.2
    u.2.1.2.2 u.2.2.2.2.2
  change mpcMkDefectTop (j + 1) q hq ∈
    MonoidHom.range (mpcMkCost (j + 1) (by omega)
      (p.2.1 * u.2.1) (p.2.2.2 * u.2.2.2))
  rw [hcost]
  exact hnext

/-! ## 4. Axiom pins -/

#print axioms mpcMkAdvance
#print axioms mpcMk_advance_mem
#print axioms mpcMk_cost_succ_base_indep
#print axioms mpcMk_good_succ_of_advance_range

end

end GQ2.Dyadic.Instances.MpcMk
