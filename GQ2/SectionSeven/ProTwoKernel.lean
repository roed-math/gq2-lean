/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.SectionSeven.Basic
import GQ2.MaxProP


/-!
# Minimal nonscalar blocks vanish in every pro-two quotient

The elementary-decoration vanishing lemma only records maps to elementary abelian two-groups.
Here the same block is killed by every two-group target. Thus quotienting by the block, or by
its Frattini radical, retains the complete prescribed pro-two map. This is a structural input
for a fully marked refinement of exact-image recursion; it does not claim that the existing
aggregated frame-count theorem already supplies that refinement.

The proof uses the existing odd-order moving-element theorem and minimality of the block.
It requires no tame-head hypothesis, no chosen class, and no extra representation data.
-/

namespace GQ2.SectionSeven

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

/-- A minimal nonscalar wild block is invisible in every two-group quotient, not only in
the elementary abelian decorations used by the original exact-image recursion. -/
theorem MinimalBlock.le_ker_of_isPGroup (B : MinimalBlock L)
    {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) (f : Y →* Q) :
    B.K ≤ f.ker := by
  classical
  haveI := B.hK
  haveI := B.hS
  obtain ⟨y, hyodd, p, hpP, hpS⟩ :=
    GQ2.exists_odd_moving_general B.S B.P B.hS B.hP B.hSP
      (B.h2L.to_le B.hPL) B.chief B.nontrivial_action
  have hfy : f y = 1 := by
    obtain ⟨a, ha⟩ := hQ (f y)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_left.mpr hyodd).pow_left a)
      (orderOf_dvd_of_pow_eq_one ha) (orderOf_map_dvd f y)
  let X : Subgroup Y := f.ker ⊓ B.K
  have hXn : X.Normal := inferInstance
  have hXK : X ≤ B.K := inf_le_right
  have hgen : X ⊔ B.S = B.P := by
    rcases B.chief (X ⊔ B.S) (Subgroup.sup_normal X B.S) le_sup_right
        (sup_le (hXK.trans B.hKP) B.hSP.le) with hXS | hXP
    · exfalso
      have hXS' : X ≤ B.S := le_sup_left.trans hXS.le
      have hcomm : ∀ k ∈ B.K, y * k * y⁻¹ * k⁻¹ ∈ B.S := by
        intro k hk
        apply hXS'
        refine ⟨?_, B.K.mul_mem (B.hK.conj_mem k hk y) (B.K.inv_mem hk)⟩
        simp [map_mul, map_inv, hfy]
      have hp : p ∈ (B.K : Set Y) * (B.S : Set Y) := by
        rw [← Subgroup.mul_normal, B.gen]
        exact hpP
      obtain ⟨k, hk, s, hs, rfl⟩ := hp
      apply hpS
      have hexp : y * (k * s) * y⁻¹ * (k * s)⁻¹ =
          (y * k * y⁻¹ * k⁻¹) * (k * (y * s * y⁻¹ * s⁻¹) * k⁻¹) := by group
      rw [hexp]
      exact B.S.mul_mem (hcomm k hk)
        (B.hS.conj_mem _ (B.S.mul_mem (B.hS.conj_mem s hs y) (B.S.inv_mem hs)) k)
    · exact hXP
  rw [← B.minimal X hXn hXK hgen]
  exact inf_le_left

/-- Every subgroup removed from a minimal nonscalar block is likewise killed by every
two-group target. This applies to both `K` and the R-stage radical `Φ(K)`. -/
theorem MinimalBlock.subgroup_le_ker_of_isPGroup (B : MinimalBlock L)
    {N : Subgroup Y} (hN : N ≤ B.K)
    {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) (f : Y →* Q) :
    N ≤ f.ker := hN.trans (B.le_ker_of_isPGroup hQ f)

/-- The block lies in the full maximal pro-two kernel. No tame-head or class bound is
needed: the existing minimal-block hypotheses suffice. -/
theorem MinimalBlock.le_proPKernel [TopologicalSpace Y] (B : MinimalBlock L) :
    B.K ≤ proPKernel 2 Y := by
  rw [proPKernel]
  apply le_iInf
  intro U k hk
  exact (QuotientGroup.eq_one_iff k).mp
    (B.le_ker_of_isPGroup U.2 (QuotientGroup.mk' U.1.toSubgroup) hk)

/-- Quotienting by any normal subgroup of the block preserves every map into a two-group,
including its complete marking, rather than merely its elementary abelian reduction. -/
theorem MinimalBlock.existsUnique_factor_of_isPGroup (B : MinimalBlock L)
    {N : Subgroup Y} [N.Normal] (hN : N ≤ B.K)
    {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) (f : Y →* Q) :
    ∃! g : Y ⧸ N →* Q, g.comp (QuotientGroup.mk' N) = f := by
  refine ⟨QuotientGroup.lift N f (B.subgroup_le_ker_of_isPGroup hN hQ f), ?_, ?_⟩
  · ext y
    rfl
  · intro g hg
    ext y
    exact DFunLike.congr_fun hg y

#print axioms MinimalBlock.le_ker_of_isPGroup
#print axioms MinimalBlock.subgroup_le_ker_of_isPGroup
#print axioms MinimalBlock.le_proPKernel
#print axioms MinimalBlock.existsUnique_factor_of_isPGroup

end GQ2.SectionSeven

