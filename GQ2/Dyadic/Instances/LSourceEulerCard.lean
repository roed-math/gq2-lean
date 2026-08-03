/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Spike
import GQ2.Dyadic.Instances.LFlexibleH2

/-!
# Euler-characteristic adapter for the L source H² comparisons

The L source package currently asks for three cardinal equalities

`#H²(GammaL, M) = #WordH²(M)`

at `M = A`, `ElemDual A`, and `ZMod 2`.  The first two are not independent once degree zero
and degree one have been compared.  The word complex has the same Euler characteristic as a
degree-`d` local Galois group whenever its presentation has deficiency `d`; cancellation then
forces equality in degree two.

This file proves that reduction without assuming word Stokes duality.  The word-side Euler
identity is only finite rank-nullity plus the chain relation `d¹ d⁰ = 0`.  On the source side
one may supply either the single coefficient-wise Euler equality or a `LocalEulerChar` bundle.
For the L row, the already-proved presentation-rank theorem identifies the deficiency with
`2h+1`.

The scalar equality is cheaper still: a `TateDualityG` bundle alone gives
`#H²(GammaL, ZMod 2) = 2`; no Euler characteristic is used there.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

/-! ## The Euler characteristic of a finite word complex -/

section WordEuler

variable {iota rel C A : Type*} [Fintype iota] [Fintype rel]
  [Group C] [AddCommGroup A] [DistribMulAction C A] [Finite A]

/-- The cardinal of word `H¹` times the cardinal of the word coboundaries is the cardinal of
the word cocycles.  The relator-death hypothesis is exactly what identifies the displayed
`addSubgroupOf` with the full range of `d⁰`. -/
theorem card_wordZ1_eq_card_WordH1_mul_range
    (c : iota → C) (w : rel → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) :
    Nat.card ↥(heisD1 (A := A) c w).ker =
      Nat.card (WordH1 c w A) * Nat.card (heisD0 (A := A) c).range := by
  have hle : (heisD0 (A := A) c).range ≤ (heisD1 (A := A) c w).ker := by
    rintro _ ⟨a, rfl⟩
    exact AddMonoidHom.mem_ker.mpr (heisD1_comp_heisD0 c w hr a)
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((heisD0 (A := A) c).range.addSubgroupOf (heisD1 (A := A) c w).ker)
  rwa [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv] at h

/-- First-isomorphism cardinality for the word differential `d⁰`. -/
theorem card_coeff_eq_card_heisD0_range_mul_ker (c : iota → C) :
    Nat.card A = Nat.card (heisD0 (A := A) c).range *
      Nat.card ↥(heisD0 (A := A) c).ker := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((heisD0 (A := A) c).ker)
  rw [show Nat.card (A ⧸ (heisD0 (A := A) c).ker) =
      Nat.card (heisD0 (A := A) c).range from
    Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange (heisD0 (A := A) c)).toEquiv] at h
  exact h

/-- **Euler characteristic of the degree-`d` word complex.**  If
`#generators = #relators + d + 1`, then

`#WordH¹ = #A^d * #WordH⁰ * #WordH²`.

No duality or source cohomology occurs in the proof. -/
theorem card_WordH1_eq_of_degree {d : ℕ}
    (c : iota → C) (w : rel → FreeGroup iota)
    (hdeg : Nat.card iota = Nat.card rel + (d + 1))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) :
    Nat.card (WordH1 c w A) =
      Nat.card A ^ d * Nat.card ↥(heisD0 (A := A) c).ker *
        Nat.card (WordH2 c w A) := by
  have hZ := card_wordZ1_mul_pow (A := A) c w
  have hH1 := card_wordZ1_eq_card_WordH1_mul_range (A := A) c w hr
  have hA := card_coeff_eq_card_heisD0_range_mul_ker (A := A) c
  have hpow : Nat.card A ^ Nat.card iota =
      Nat.card A ^ Nat.card rel * Nat.card A ^ (d + 1) := by
    rw [hdeg, pow_add]
  have hrelpos : 0 < Nat.card A ^ Nat.card rel := pow_pos Nat.card_pos _
  have hZ' : Nat.card ↥(heisD1 (A := A) c w).ker =
      Nat.card A ^ (d + 1) * Nat.card (WordH2 c w A) := by
    apply Nat.eq_of_mul_eq_mul_right hrelpos
    rw [hZ, hpow]
    ring
  have hrangepos : 0 < Nat.card (heisD0 (A := A) c).range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hrangepos
  rw [← hH1, hZ', pow_succ, hA]
  ring

end WordEuler

/-! ## Cancellation against source cohomology -/

section SourceEuler

variable {Gamma A : Type} {iota rel C : Type*}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [Group C] [Fintype iota] [Fintype rel]
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A]
  [DistribMulAction C A]

/-- Once `H⁰` and `H¹` are identified, matching source and word Euler equalities force the
degree-two cardinalities to agree.  This coefficient-wise equality is the smallest source
Euler assumption needed by the argument. -/
theorem card_H2_eq_WordH2_of_euler {d : ℕ}
    (c : iota → C) (w : rel → FreeGroup iota)
    (hdeg : Nat.card iota = Nat.card rel + (d + 1))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (h0 : H0 Gamma A ≃+ ↥(heisD0 (A := A) c).ker)
    (h1 : H1 Gamma A ≃+ WordH1 c w A)
    (hEuler : Nat.card (H1 Gamma A) =
      Nat.card (H0 Gamma A) * Nat.card (H2 Gamma A) * Nat.card A ^ d) :
    Nat.card (H2 Gamma A) = Nat.card (WordH2 c w A) := by
  have hword := card_WordH1_eq_of_degree (A := A) c w hdeg hr
  have h0card : Nat.card (H0 Gamma A) = Nat.card ↥(heisD0 (A := A) c).ker :=
    Nat.card_congr h0.toEquiv
  have h1card : Nat.card (H1 Gamma A) = Nat.card (WordH1 c w A) :=
    Nat.card_congr h1.toEquiv
  have hfactor : 0 < Nat.card (H0 Gamma A) * Nat.card A ^ d :=
    Nat.mul_pos Nat.card_pos (pow_pos Nat.card_pos _)
  apply Nat.eq_of_mul_eq_mul_left hfactor
  calc
    Nat.card (H0 Gamma A) * Nat.card A ^ d * Nat.card (H2 Gamma A)
        = Nat.card (H1 Gamma A) := by rw [hEuler]; ring
    _ = Nat.card (WordH1 c w A) := h1card
    _ = Nat.card A ^ d * Nat.card ↥(heisD0 (A := A) c).ker *
          Nat.card (WordH2 c w A) := hword
    _ = Nat.card (H0 Gamma A) * Nat.card A ^ d * Nat.card (WordH2 c w A) := by
      rw [← h0card]
      ring

/-- A local Euler-characteristic bundle supplies the coefficient-wise source equality in the
form needed above. -/
theorem card_H2_eq_WordH2_of_localEulerChar {d : ℕ}
    (c : iota → C) (w : rel → FreeGroup iota)
    (hdeg : Nat.card iota = Nat.card rel + (d + 1))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hA₂ : ∀ a : A, a + a = 0)
    (h0 : H0 Gamma A ≃+ ↥(heisD0 (A := A) c).ker)
    (h1 : H1 Gamma A ≃+ WordH1 c w A)
    (hE : LocalEulerChar Gamma d) :
    Nat.card (H2 Gamma A) = Nat.card (WordH2 c w A) := by
  apply card_H2_eq_WordH2_of_euler c w hdeg hr h0 h1
  have hEuler := (hE A).2.2.2
  rw [pow_mul', GQ2.LocalLiftingDuality.pow_padicValNat_card hA₂] at hEuler
  exact hEuler

end SourceEuler

/-! ## L specialization -/

section LAdapter

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

/-- At the L presentation, one coefficient-wise Euler equality replaces the corresponding
explicit `H²` cardinal equality.  The target-local resolver already present in
`ResolvedPushedHsimp` supplies the proved `H¹` comparison. -/
theorem l_card_H2_eq_WordH2_of_euler
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hEuler : Nat.card (H1 GammaL A) =
      Nat.card (H0 GammaL A) * Nat.card (H2 GammaL A) * Nat.card A ^ (2 * h + 1)) :
    Nat.card (H2 GammaL A) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL A) := by
  have hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1 := fun k ↦
    lower_rel (A := A) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) hres k
  exact card_H2_eq_WordH2_of_euler (fun i ↦ rho (genL i)) wL (degree h) hr
    (GQ2.Dyadic.Count.h0Equiv rho hcompat (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)))
    (h1Equiv_gammaR_range rho hcompat hres hA₂) hEuler

/-- `LocalEulerChar GammaL (2h+1)` supplies the L coefficient-wise Euler equality. -/
theorem l_card_H2_eq_WordH2_of_localEulerChar
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hE : LocalEulerChar GammaL (2 * h + 1)) :
    Nat.card (H2 GammaL A) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL A) := by
  apply l_card_H2_eq_WordH2_of_euler rho hcompat hA₂ hres
  have hEuler := (hE A).2.2.2
  rw [pow_mul', GQ2.LocalLiftingDuality.pow_padicValNat_card hA₂] at hEuler
  exact hEuler

end LAdapter

/-! ## The scalar equality and the three-cardinality bundle -/

section Scalar

variable {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [DistribMulAction Gamma (MuN 2)] [ContinuousSMul Gamma (MuN 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]

/-- The scalar cardinal equality needed by the L source comparison follows from local Tate
duality alone.  In particular it consumes no `LocalEulerChar` hypothesis. -/
theorem scalar_card_H2_eq_card_zmodTwo_of_tateDuality
    (D : TateDualityG Gamma 2)
    (htriv : ∀ (g : Gamma) (m : ZMod 2), g • m = m) :
    Nat.card (H2 Gamma (ZMod 2)) = Nat.card (ZMod 2) := by
  rw [card_H2_zmod2_eq_twoG D htriv, Nat.card_zmod]

end Scalar

section LCardinalityBundle

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)]
  [ContinuousSMul ((gamma h q : Type)) (ElemDual A)]
  [DistribMulAction ((gamma h q : Type)) (MuN 2)]
  [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
  [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

/-- The exact replacement for the three explicit cardinal equalities in
`sourceComparisonPackage_of_lFlexibleH2_card_eq`:

* one local Euler-characteristic bundle at the presentation deficiency gives the primal and
  dual module equalities, using the existing `H⁰`/`H¹` comparison maps;
* one Tate-duality bundle gives the scalar equality, independently of Euler characteristic.

This theorem does not provide either bundle for the abstract `GammaL`. -/
theorem l_sourceH2_cardinalities_of_euler_and_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hresDual : ResolvesAt WL wL (WordLift (ElemDual A) C))
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m) :
    (Nat.card (H2 GammaL A) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL A)) ∧
    (Nat.card (H2 GammaL (ElemDual A)) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL (ElemDual A))) ∧
    (Nat.card (H2 GammaL (ZMod 2)) = Nat.card (ZMod 2)) := by
  exact ⟨l_card_H2_eq_WordH2_of_localEulerChar rho hcompatA hA₂ hres hE,
    l_card_H2_eq_WordH2_of_localEulerChar rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual hE,
    scalar_card_H2_eq_card_zmodTwo_of_tateDuality D htriv⟩

end LCardinalityBundle

end

end GQ2.Dyadic.LSquare
