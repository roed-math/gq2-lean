/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Certificates.M0

/-!
# Core and handle comparisons for the raw hyperbolic source

The compact core factors use only `sigma`, `tau`, and the three core letters. Consequently
their evaluation is unchanged when every unused handle base is replaced by `1`. This permits
the existing compact core formulas to be applied even when a promoted handle base acts
nontrivially.

The complementary handle lemma needs trivial action only on the right-hand handle letters.
When their dual offsets vanish, the dual jet of the whole handle product vanishes and its
central charge is the sum of the left-dual/right-primal evaluations. No condition on the
left-hand handle actions is imposed. Both results are uniform in the handle rank.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH
open Count Certificates Words

namespace Instances.EvenMHeadHandleHyperbolicRawHelpers

theorem evalZ_mFactors_congr {h : ℕ} {G : Type*} [Group G]
    (f g : Generator (2 + 2 * h) → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha : ℕ) (hs : f .sigma = g .sigma) (ht : f .tau = g .tau)
    (hc : ∀ i : Fin 3, f (coreLetter h i) = g (coreLetter h i)) :
    PWord.evalZ f E E₂ (PWord.prodList (Words.MCompact.mFactors alpha h)) =
      PWord.evalZ g E E₂ (PWord.prodList (Words.MCompact.mFactors alpha h)) := by
  simp only [Words.MCompact.mFactors, Words.MCompact.a0W, Words.MCompact.j2W,
    Words.MCompact.eRevW, Words.MCompact.deltaC, sigma2W, PWord.omega2Pow,
    PWord.evalZ_prodList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_inv, PWord.evalZ_conj,
    PWord.evalZ_comm, PWord.evalZ_profPow, hs, ht, hc]

/-- Preserve the compact core marking and replace every unused handle base by `1`. -/
def coreOnlyMark {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) : Marking (2 + 2 * h) C :=
  ⟨fun g ↦ match g with
    | .sigma => t.σ
    | .tau => t.τ
    | .wild i => if i.val < 3 then t.x i else 1⟩

@[simp] theorem coreOnlyMark_sigma {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) : (coreOnlyMark t).σ = t.σ := rfl

@[simp] theorem coreOnlyMark_tau {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) : (coreOnlyMark t).τ = t.τ := rfl

@[simp] theorem coreOnlyMark_coreLetter {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) (i : Fin 3) :
    coreOnlyMark t (coreLetter h i) = t (coreLetter h i) := by
  change (if i.val < 3 then t.x _ else 1) = _
  rw [if_pos i.isLt]
  rfl

theorem coreOnlyMark_wild_trivial {h : ℕ} {C A : Type*} [Group C]
    [AddCommGroup A] [DistribMulAction C A] (t : Marking (2 + 2 * h) C)
    (hcore : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a) :
    ∀ (i : Fin (2 + 2 * h + 1)) (a : A), (coreOnlyMark t).x i • a = a := by
  intro i a
  change (if i.val < 3 then t.x i else 1) • a = a
  split
  · rename_i hi
    exact hcore ⟨i.val, hi⟩ a
  · exact one_smul C a

theorem heisEvalZ_mFactors_coreOnly {h : ℕ} {C A : Type*} [Group C]
    [AddCommGroup A] [DistribMulAction C A] (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A) (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) :
    heisEvalZ ⇑(coreOnlyMark t) x y E E₂
        (PWord.prodList (Words.MCompact.mFactors alpha h)) =
      heisEvalZ ⇑t x y E E₂
        (PWord.prodList (Words.MCompact.mFactors alpha h)) := by
  apply evalZ_mFactors_congr
  · apply HeisLift.ext <;> rfl
  · apply HeisLift.ext <;> rfl
  · intro i
    apply HeisLift.ext <;> simp [heisGen]

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [DistribMulAction C A]

theorem list_prod_lz_of_l_zero (ps : List (HeisLift A C))
    (hl : ∀ p ∈ ps, p.l = 0) :
    ps.prod.l = 0 ∧ ps.prod.z = (ps.map HeisLift.z).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp := hl p (by simp)
      have ht := ih (fun r hr ↦ hl r (by simp [hr]))
      constructor
      · simp [HeisLift.mul_l, hp, ht.1]
      · simp [HeisLift.mul_z, hp, ht.2]

/-- Pure right dual coordinates expose the handle cross term even when left bases move. -/
theorem heisEvalZ_handlesW_of_right_trivial_dual_zero
    (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hV : ∀ (j : Fin h) (a : A), t (handleV j) • a = a)
    (hyV : ∀ j : Fin h, y (handleV j) = 0) :
    (heisEvalZ ⇑t x y E E₂ (handlesW h)).l = 0 ∧
      (heisEvalZ ⇑t x y E E₂ (handlesW h)).z =
        ∑ j : Fin h, y (handleU j) (x (handleV j)) := by
  let p : Fin h → HeisLift A C := fun j ↦
    heisEvalZ ⇑t x y E E₂ (.comm (.gen (handleU j)) (.gen (handleV j)))
  have hp (j : Fin h) : (p j).l = 0 ∧
      (p j).z = y (handleU j) (x (handleV j)) := by
    dsimp only [p]
    rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
      heisCommR_of_trivial_right _ _ (hV j)]
    constructor <;> simp [hyV]
  have hprod := list_prod_lz_of_l_zero ((List.finRange h).map p) (by
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact (hp j).1)
  have heval : heisEvalZ ⇑t x y E E₂ (handlesW h) =
      ((List.finRange h).map p).prod := by
    rw [handlesW, heisEvalZ_prodList, List.map_map]
    rfl
  rw [heval]
  refine ⟨hprod.1, hprod.2.trans ?_⟩
  rw [List.map_map]
  simp only [Function.comp_def]
  simp_rw [(hp _).2]
  exact (Fin.sum_univ_def _).symm

#print axioms evalZ_mFactors_congr
#print axioms coreOnlyMark
#print axioms coreOnlyMark_sigma
#print axioms coreOnlyMark_tau
#print axioms coreOnlyMark_coreLetter
#print axioms coreOnlyMark_wild_trivial
#print axioms heisEvalZ_mFactors_coreOnly
#print axioms list_prod_lz_of_l_zero
#print axioms heisEvalZ_handlesW_of_right_trivial_dual_zero

end Instances.EvenMHeadHandleHyperbolicRawHelpers
end
end GQ2.Dyadic
