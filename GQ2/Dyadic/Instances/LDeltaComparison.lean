/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LWordDelta
import GQ2.Dyadic.Instances.LFlexibleH2Naturality
import GQ2.Dyadic.Instances.LHeisenbergResolver

/-!
# Compatibility of the continuous and word coefficient connecting maps

For the improved L presentation, the continuous `H¹ → H²` coefficient snake and the
general word-complex snake commute with the canonical source comparison maps.  The
representative calculation uses the normalized continuous lift

`i ↦ snakeLift1 z (genL i) - snakeLift1 z 1`.

The witness-preserving flexible coboundary theorem identifies the obstruction of the
pushed continuous snake cocycle with the word boundary of this exact cochain.  Word
snake lift-independence then identifies its class with the canonical word snake.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

section DeltaSquare

variable {h q e : ℕ} {C A' A A'' : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DiscreteTopology A'] [Finite A']
  [DistribMulAction ((gamma h q : Type)) A'] [ContinuousSMul ((gamma h q : Type)) A']
  [DistribMulAction C A']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A] [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [AddCommGroup A''] [TopologicalSpace A''] [IsTopologicalAddGroup A'']
  [DiscreteTopology A''] [Finite A'']
  [DistribMulAction ((gamma h q : Type)) A''] [ContinuousSMul ((gamma h q : Type)) A'']
  [DistribMulAction C A'']

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

/-- **The L coefficient connecting square.**  The canonical continuous `H¹` comparison,
the flexible continuous-to-word `H²` map, and the two independently constructed
coefficient snakes commute. -/
theorem l_delta1_comparison
    (S : FiniteDiscreteCoeffSES (G := GammaL) (A' := A') (A := A) (A'' := A''))
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA' : ∀ (g : GammaL) (a : A'), g • a = rho g • a)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatA'' : ∀ (g : GammaL) (a : A''), g • a = rho g • a)
    (hA'₂ : ∀ a : A', a + a = 0)
    (hA''₂ : ∀ a : A'', a + a = 0)
    (hresA' : ResolvesAt WL wL (WordLift A' C))
    (hresA : ResolvesAt WL wL (WordLift A C))
    (hresA'' : ResolvesAt WL wL (WordLift A'' C))
    (hfC : ∀ (u : C) (a : A'), S.f (u • a) = u • S.f a)
    (hgC : ∀ (u : C) (a : A), S.g (u • a) = u • S.g a)
    (x : H1 GammaL A'') :
    S.wordDelta1 (fun i ↦ rho (genL i)) wL hfC hgC
        (fun k ↦ lower_rel (A := A) rho (fun _ ↦ rfl)
          (isAdmissibleMarkedPresentation_gammaR
            (2 * h + 1) q (Words.LSq.lSqW h)) hresA k)
        (lSourceH1Equiv rho hcompatA'' hA''₂ hresA'' x) =
      lModuleH2WordFlexible rho hcompatA' hA'₂ hresA'
        (S.delta1 x) := by
  obtain ⟨z, rfl⟩ := H1mk_surjective (G := GammaL) (M := A'') x
  rw [lSourceH1Equiv_mk, S.delta1_H1mk, S.wordDelta1_stokesH1Mk,
    lModuleH2WordFlexible_mk]
  let zw : ↥(heisD1 (A := A'') (fun i ↦ rho (genL i)) wL).ker :=
    lSourceZ1Map rho hcompatA'' hresA'' z
  let psi : GammaL → A := S.snakeLift1 z
  let a : Generator (2 * h + 1) → A :=
    fun i ↦ psi (genL i) - psi 1
  let b : Fin 2 → A' :=
    moduleObsFam WL genL rho hcompatA' (S.snakeZ z)
  have hga : ∀ i, S.g (a i) = zw.1 i := by
    intro i
    change S.g (S.snakeLift1 z (genL i) - S.snakeLift1 z 1) = z.1 (genL i)
    rw [map_sub, S.g_snakeLift1, S.g_snakeLift1, Z1_apply_one, sub_zero]
  let zf : Z2 GammaL A :=
    Z2comap (ContinuousMonoidHom.id GammaL) S.f S.continuous_f
      (fun g a' ↦ S.f_equivariant g a') (S.snakeZ z)
  have hzf : zf.1 = dOne GammaL A psi := by
    funext p
    exact S.f_snakeZ z p
  have hstrong : moduleObsFam WL genL rho hcompatA zf =
      heisD1 (A := A) (fun i ↦ rho (genL i)) wL a := by
    exact moduleObsFam_coboundary_eq_heisD1_flexible
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
      rho hcompatA hresA (lFlexibleResolverSystem rho hresA)
      (fun _ ↦ rfl) zf psi (S.snakeLift1_continuous z) hzf
  have hnat := moduleObsFun_mapCoeff WL genL rho hcompatA' hcompatA
    S.f S.f_equivariant (S.snakeZ z)
  have hfb : ∀ k, S.f (b k) =
      heisD1 (A := A) (fun i ↦ rho (genL i)) wL a k := by
    intro k
    exact (congrFun hnat k).symm.trans (congrFun hstrong k)
  exact (S.wordSnakeZ_welldef (fun i ↦ rho (genL i)) wL hfC hgC
    zw a b hga hfb).symm

end DeltaSquare

end

end GQ2.Dyadic.LSquare
