/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.CohomologyDevissage
import GQ2.Dyadic.Word.StokesDual

/-!
# The coefficient connecting map for a general word complex

This file builds the snake connecting map

`WordH1 c w A'' → WordH2 c w A'`

for the three-term complex defined by `heisD0` and `heisD1`, along a finite discrete
coefficient short exact sequence `0 → A' → A → A'' → 0`.  Unlike the older
`Fin 4` presentation-specific snake in `GQ2.Devissage.LESCore`, the construction is
uniform in the generator and relator types.  Its lift-independence theorem accepts any
cochain lift and any compatible degree-two representative; this is the interface used
to compare the word snake with the continuous one.
-/

namespace GQ2.ContCoh.FiniteDiscreteCoeffSES

noncomputable section

open GQ2.FoxH GQ2.Dyadic

section WordSnake

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

/-- The chosen coordinatewise lift of a word one-cocycle. -/
noncomputable def wordSnakeLift
    (z : ↥(heisD1 (A := A'') c w).ker) : ι → A :=
  fun i ↦ S.liftCoeff (z.1 i)

@[simp] theorem g_wordSnakeLift
    (z : ↥(heisD1 (A := A'') c w).ker) (i : ι) :
    S.g (S.wordSnakeLift c w z i) = z.1 i :=
  S.g_liftCoeff (z.1 i)

include hgC in
/-- The word boundary of the chosen lift lands coordinatewise in `ker g`. -/
theorem wordSnakeBoundary_g_zero
    (z : ↥(heisD1 (A := A'') c w).ker) (k : ρ) :
    S.g (heisD1 (A := A) c w (S.wordSnakeLift c w z) k) = 0 := by
  have hnat := heisD1_map c w S.g hgC (S.wordSnakeLift c w z)
  have hlift : stokesPi ι S.g (S.wordSnakeLift c w z) = z.1 := by
    funext i
    exact S.g_wordSnakeLift c w z i
  rw [hlift, AddMonoidHom.mem_ker.mp z.2] at hnat
  exact congrFun hnat.symm k

/-- The concrete `A'`-valued degree-two word representative extracted by the snake. -/
noncomputable def wordSnakeZ
    (z : ↥(heisD1 (A := A'') c w).ker) : ρ → A' :=
  fun k ↦ S.kernelLift (heisD1 (A := A) c w (S.wordSnakeLift c w z) k)

include hgC in
theorem f_wordSnakeZ
    (z : ↥(heisD1 (A := A'') c w).ker) (k : ρ) :
    S.f (S.wordSnakeZ c w z k) =
      heisD1 (A := A) c w (S.wordSnakeLift c w z) k :=
  S.f_kernelLift_of_mem_ker (S.wordSnakeBoundary_g_zero c w hgC z k)

/-- Pull the difference between an arbitrary lift and the chosen lift back through `f`. -/
noncomputable def wordSnakeLiftDiff
    (z : ↥(heisD1 (A := A'') c w).ker) (a : ι → A) : ι → A' :=
  fun i ↦ S.kernelLift (a i - S.wordSnakeLift c w z i)

theorem f_wordSnakeLiftDiff
    (z : ↥(heisD1 (A := A'') c w).ker) (a : ι → A)
    (hga : ∀ i, S.g (a i) = z.1 i) (i : ι) :
    S.f (S.wordSnakeLiftDiff c w z a i) =
      a i - S.wordSnakeLift c w z i := by
  apply S.f_kernelLift_of_mem_ker
  rw [map_sub, hga, S.g_wordSnakeLift, sub_self]

include hfC hgC in
/-- **Lift-independence of the word snake.**  Any coordinatewise lift of the same
word cocycle, and any degree-two cochain mapping to its word boundary, represents the
canonical connecting class. -/
theorem wordSnakeZ_welldef
    (z : ↥(heisD1 (A := A'') c w).ker) (a : ι → A) (b : ρ → A')
    (hga : ∀ i, S.g (a i) = z.1 i)
    (hfb : ∀ k, S.f (b k) = heisD1 (A := A) c w a k) :
    (QuotientAddGroup.mk b : WordH2 c w A') =
      QuotientAddGroup.mk (S.wordSnakeZ c w z) := by
  let d : ι → A' := S.wordSnakeLiftDiff c w z a
  have hfd : (fun i ↦ S.f (d i)) = a - S.wordSnakeLift c w z := by
    funext i
    exact S.f_wordSnakeLiftDiff c w z a hga i
  have hdiff : b - S.wordSnakeZ c w z = heisD1 (A := A') c w d := by
    funext k
    apply S.f_injective
    calc
      S.f ((b - S.wordSnakeZ c w z) k) =
          heisD1 (A := A) c w a k -
            heisD1 (A := A) c w (S.wordSnakeLift c w z) k := by
        rw [Pi.sub_apply, map_sub, hfb, S.f_wordSnakeZ c w hgC]
      _ = heisD1 (A := A) c w (a - S.wordSnakeLift c w z) k := by
        simpa only [Pi.sub_apply] using
          (congrFun (map_sub (heisD1 (A := A) c w) a (S.wordSnakeLift c w z)) k).symm
      _ = heisD1 (A := A) c w (stokesPi ι S.f d) k := by
        rw [show stokesPi ι S.f d = a - S.wordSnakeLift c w z from hfd]
      _ = S.f (heisD1 (A := A') c w d k) :=
        congrFun (heisD1_map c w S.f hfC d) k
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
  exact AddMonoidHom.mem_range.mpr ⟨d, hdiff.symm⟩

/-- The word connecting map on one-cocycles, before quotienting by word coboundaries. -/
noncomputable def wordDelta1Raw :
    ↥(heisD1 (A := A'') c w).ker →+ WordH2 c w A' where
  toFun z := QuotientAddGroup.mk (S.wordSnakeZ c w z)
  map_zero' :=
    ((S.wordSnakeZ_welldef c w hfC hgC 0 0 0
      (by intro i; simp) (by
        intro k
        simpa using (congrFun (map_zero (heisD1 (A := A) c w)) k).symm)).symm).trans
      (QuotientAddGroup.mk_zero _)
  map_add' x y := by
    refine ((S.wordSnakeZ_welldef c w hfC hgC (x + y)
      (S.wordSnakeLift c w x + S.wordSnakeLift c w y)
      (S.wordSnakeZ c w x + S.wordSnakeZ c w y) ?_ ?_).symm).trans
      (QuotientAddGroup.mk_add _ _ _)
    · intro i
      simp only [Pi.add_apply, map_add, S.g_wordSnakeLift]
      rfl
    · intro k
      rw [Pi.add_apply, map_add, S.f_wordSnakeZ c w hgC, S.f_wordSnakeZ c w hgC]
      exact (congrFun (map_add (heisD1 (A := A) c w)
        (S.wordSnakeLift c w x) (S.wordSnakeLift c w y)) k).symm

/-- The coefficient connecting map for the general word complex. -/
noncomputable def wordDelta1
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) :
    WordH1 c w A'' →+ WordH2 c w A' :=
  QuotientAddGroup.lift _ (S.wordDelta1Raw c w hfC hgC) <| by
    intro z hz
    rw [AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨a'', ha''⟩ := AddMonoidHom.mem_range.mp hz
    let a : A := S.liftCoeff a''
    have hga : ∀ i, S.g (heisD0 (A := A) c a i) = z.1 i := by
      intro i
      change S.g (c i • a - a) = z.1 i
      rw [map_sub, hgC, show S.g a = a'' from S.g_liftCoeff a'']
      exact congrFun ha'' i
    have hfb : ∀ k, S.f ((0 : ρ → A') k) =
        heisD1 (A := A) c w (heisD0 (A := A) c a) k := by
      intro k
      rw [Pi.zero_apply, map_zero]
      exact congrFun (heisD1_comp_heisD0 c w hr a).symm k
    exact ((S.wordSnakeZ_welldef c w hfC hgC z (heisD0 (A := A) c a) 0
      hga hfb).symm).trans (QuotientAddGroup.mk_zero _)

/-- Representative formula for the general word connecting map. -/
@[simp] theorem wordDelta1_stokesH1Mk
    (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (z : ↥(heisD1 (A := A'') c w).ker) :
    S.wordDelta1 c w hfC hgC hr
        (stokesH1Mk (heisD0 (A := A'') c) (heisD1 c w) z) =
      QuotientAddGroup.mk (S.wordSnakeZ c w z) :=
  rfl

end WordSnake

end

end GQ2.ContCoh.FiniteDiscreteCoeffSES
