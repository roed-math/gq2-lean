/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LWordDelta
import GQ2.Dyadic.Instances.LFlexibleH2Naturality

/-!
# Exactness of the coefficient sequence for a general word complex

This file completes the arbitrary-generator/arbitrary-relator word snake from `LWordDelta`.
For a finite discrete coefficient short exact sequence, the induced sequence

`WordH¹(A'') → WordH²(A') → WordH²(A) → WordH²(A'') → 0`

is exact.  These are elementary cokernel chases; no continuous cohomology, Tate duality,
Euler characteristic, or cohomological-dimension hypothesis is used.
-/

namespace GQ2.ContCoh.FiniteDiscreteCoeffSES

noncomputable section

open GQ2.FoxH GQ2.Dyadic
open GQ2.Dyadic.LSquare

variable {G ι ρ C A' A A'' : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group C]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DiscreteTopology A'] [Finite A'] [DistribMulAction G A'] [ContinuousSMul G A']
  [DistribMulAction C A']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction C A]
  [AddCommGroup A''] [TopologicalSpace A''] [IsTopologicalAddGroup A'']
  [DiscreteTopology A''] [Finite A''] [DistribMulAction G A''] [ContinuousSMul G A'']
  [DistribMulAction C A'']

variable (S : FiniteDiscreteCoeffSES (G := G) (A' := A') (A := A) (A'' := A''))
  (c : ι → C) (w : ρ → FreeGroup ι)
  (hfC : ∀ (u : C) (a : A'), S.f (u • a) = u • S.f a)
  (hgC : ∀ (u : C) (a : A), S.g (u • a) = u • S.g a)

/-- The induced coefficient inclusion on word `H²`. -/
noncomputable def wordH2MapF : WordH2 c w A' →+ WordH2 c w A :=
  moduleWordH2Map c w S.f hfC

/-- The induced coefficient quotient on word `H²`. -/
noncomputable def wordH2MapG : WordH2 c w A →+ WordH2 c w A'' :=
  moduleWordH2Map c w S.g hgC

/-- Consecutive word `H²` coefficient maps compose to zero. -/
theorem wordH2Map_comp_apply (x : WordH2 c w A') :
    S.wordH2MapG c w hgC (S.wordH2MapF c w hfC x) = 0 := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [wordH2MapF, wordH2MapG, moduleWordH2Map_mk, moduleWordH2Map_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change (fun k ↦ S.g (S.f (z k))) ∈ (heisD1 (A := A'') c w).range
  rw [show (fun k ↦ S.g (S.f (z k))) = 0 from funext fun k ↦ S.comp_zero (z k)]
  exact AddSubgroup.zero_mem _

/-- The right end of the word coefficient sequence is onto. -/
theorem wordH2MapG_surjective : Function.Surjective (S.wordH2MapG c w hgC) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
  let a : ρ → A := fun k ↦ S.liftCoeff (z k)
  refine ⟨QuotientAddGroup.mk a, ?_⟩
  rw [wordH2MapG, moduleWordH2Map_mk]
  congr 1
  funext k
  exact S.g_liftCoeff (z k)

/-- Exactness at `WordH²(A)`. -/
theorem wordH2_exact_middle (x : WordH2 c w A) :
    S.wordH2MapG c w hgC x = 0 ↔ x ∈ (S.wordH2MapF c w hfC).range := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  constructor
  · intro hx
    rw [wordH2MapG, moduleWordH2Map_mk,
      QuotientAddGroup.eq_zero_iff] at hx
    obtain ⟨a'', ha''⟩ := AddMonoidHom.mem_range.mp hx
    let a : ι → A := fun i ↦ S.liftCoeff (a'' i)
    have hga : stokesPi ι S.g a = a'' := by
      funext i
      exact S.g_liftCoeff (a'' i)
    have hnat := heisD1_map c w S.g hgC a
    have hzero : stokesPi ρ S.g (z - heisD1 (A := A) c w a) = 0 := by
      rw [map_sub, ← hnat, hga, ha'']
      change (fun k ↦ S.g (z k)) - (fun k ↦ S.g (z k)) = 0
      exact sub_self _
    have hker : ∀ k, S.g ((z - heisD1 (A := A) c w a) k) = 0 := by
      intro k
      exact congrFun hzero k
    let b : ρ → A' := fun k ↦ S.kernelLift ((z - heisD1 (A := A) c w a) k)
    have hfb : stokesPi ρ S.f b = z - heisD1 (A := A) c w a := by
      funext k
      exact S.f_kernelLift_of_mem_ker (hker k)
    refine ⟨QuotientAddGroup.mk b, ?_⟩
    rw [wordH2MapF, moduleWordH2Map_mk]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change stokesPi ρ S.f b - z ∈ (heisD1 (A := A) c w).range
    rw [hfb]
    have heq : (z - heisD1 (A := A) c w a) - z =
        -(heisD1 (A := A) c w a) := by abel
    rw [heq]
    exact (heisD1 (A := A) c w).range.neg_mem
      (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact S.wordH2Map_comp_apply c w hfC hgC y

/-- Exactness at `WordH²(A')`: the kernel of the coefficient inclusion is the image of the
word connecting map. -/
theorem wordH2_exact_left
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (x : WordH2 c w A') :
    S.wordH2MapF c w hfC x = 0 ↔
      x ∈ (S.wordDelta1 c w hfC hgC hr).range := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  constructor
  · intro hx
    rw [wordH2MapF, moduleWordH2Map_mk,
      QuotientAddGroup.eq_zero_iff] at hx
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx
    have hgz : heisD1 (A := A'') c w (stokesPi ι S.g a) = 0 := by
      rw [heisD1_map c w S.g hgC, ha]
      change stokesPi ρ S.g (stokesPi ρ S.f z) = 0
      funext k
      exact S.comp_zero (z k)
    let za : ↥(heisD1 (A := A'') c w).ker :=
      ⟨stokesPi ι S.g a, AddMonoidHom.mem_ker.mpr hgz⟩
    refine ⟨stokesH1Mk (heisD0 (A := A'') c) (heisD1 c w) za, ?_⟩
    rw [S.wordDelta1_stokesH1Mk c w hfC hgC hr]
    exact (S.wordSnakeZ_welldef c w hfC hgC za a z
      (fun _ ↦ rfl) (fun k ↦ congrFun ha.symm k)).symm
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨z, rfl⟩ := stokesH1Mk_surjective
      (heisD0 (A := A'') c) (heisD1 c w) y
    rw [S.wordDelta1_stokesH1Mk c w hfC hgC hr]
    apply AddMonoidHom.mem_ker.mpr
    rw [wordH2MapF, moduleWordH2Map_mk]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    apply AddMonoidHom.mem_range.mpr
    refine ⟨S.wordSnakeLift c w z, ?_⟩
    funext k
    exact (S.f_wordSnakeZ c w hgC z k).symm

end

end GQ2.ContCoh.FiniteDiscreteCoeffSES
