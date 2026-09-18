/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseModel
import GQ2.Dyadic.Instances.WordPhasePolarNormal
import GQ2.Dyadic.Instances.WordPhaseCompactMHandleData

/-!
# Additive source coordinates and literal polar congruence

The normal-form phase comparison originally retained only a bijection, which suffices for
Gauss reindexing. For an additive normal map, this file proves that its very same equivalence
is additive, not merely that some other additive coordinates exist. The quotient-to-H1 map
and the unique-normal-representative map are both upgraded to additive equivalences.

The compact normal map is additive at every rank. The ramified head swap is also an additive
equivalence. The final matrix theorem transports the complete finite polar coefficient matrix
to the source quotient, retaining the actual coefficient-space bilinear form. No new phase
identity, normal-form assumption, arithmetic axiom, or nondegeneracy premise is introduced:
the generic constructors take the same normal-form and phase inputs as the existing assembler.
-/

namespace GQ2.Dyadic.Instances.WordPhaseAdditiveNormal
noncomputable section
open GQ2 GQ2.Dyadic GQ2.FoxH GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhaseModel GQ2.Dyadic.Instances.WordPhase
open GQ2.QuadraticFp2 GQ2.Dyadic.Instances.WordPhasePolarNormal

section Normal
variable {K0 K1 K2 P : Type*} [AddCommGroup K0] [AddCommGroup K1]
  [AddCommGroup K2] [AddCommGroup P]
  (d0 : K0 →+ K1) (d1 : K1 →+ K2) (normal : P → K1)
  (hadd : ∀ p r, normal (p+r) = normal p + normal r)
  (hmem : ∀ p, d1 (normal p) = 0)
  (hnf : ∀ x, d1 x=0 → ∃! p, x-normal p ∈ Set.range d0)

include hadd
theorem stokesNormalClass_add (p r : P) :
    stokesNormalClass d0 d1 normal hmem (p+r) =
      stokesNormalClass d0 d1 normal hmem p + stokesNormalClass d0 d1 normal hmem r := by
  unfold stokesNormalClass
  change QuotientAddGroup.mk' (d0.range.addSubgroupOf d1.ker) ⟨normal (p+r), _⟩ =
    QuotientAddGroup.mk' (d0.range.addSubgroupOf d1.ker) ⟨normal p, _⟩ +
      QuotientAddGroup.mk' (d0.range.addSubgroupOf d1.ker) ⟨normal r, _⟩
  rw [← map_add]
  congr 1
  exact Subtype.ext (hadd p r)

def stokesNormalAddEquiv : StokesH1 d0 d1 ≃+ P :=
  (AddEquiv.ofBijective
    ({ toFun := stokesNormalClass d0 d1 normal hmem
       map_zero' := by
         have H := stokesNormalClass_add d0 d1 normal hadd hmem (0 : P) 0
         simpa using H
       map_add' := stokesNormalClass_add d0 d1 normal hadd hmem } : P →+ StokesH1 d0 d1)
    (stokesNormalClass_bijective d0 d1 normal hmem hnf)).symm

@[simp] theorem stokesNormalAddEquiv_toEquiv :
    (stokesNormalAddEquiv d0 d1 normal hadd hmem hnf).toEquiv =
      stokesNormalEquiv d0 d1 normal hmem hnf := rfl

theorem stokesNormalEquiv_add (x y : StokesH1 d0 d1) :
    stokesNormalEquiv d0 d1 normal hmem hnf (x+y) =
      stokesNormalEquiv d0 d1 normal hmem hnf x +
        stokesNormalEquiv d0 d1 normal hmem hnf y :=
  (stokesNormalAddEquiv d0 d1 normal hadd hmem hnf).map_add x y
end Normal

section Source
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction Gamma DD.Vmod]
  (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)

theorem h1OfVQuot_add (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    h1OfVQuot hcomp (x+y) = h1OfVQuot hcomp x + h1OfVQuot hcomp y := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    induction y using QuotientAddGroup.induction_on with
    | H b => rfl

def sourceQuotientH1AddEquiv : (VCocycle DD rho ⧸ vCobRange DD rho) ≃+ H1 Gamma DD.Vmod where
  toEquiv := sourceQuotientH1Equiv hcomp
  map_add' := h1OfVQuot_add hcomp

@[simp] theorem sourceQuotientH1AddEquiv_toEquiv :
    (sourceQuotientH1AddEquiv hcomp).toEquiv = sourceQuotientH1Equiv hcomp := rfl
end Source

theorem compactPhaseNormal_add {V : Type} [AddCommGroup V] (h : ℕ)
    (p r : CompactCoordinates V h) :
    wPmCompactPhaseNormal h (p+r) = wPmCompactPhaseNormal h p + wPmCompactPhaseNormal h r := by
  unfold wPmCompactPhaseNormal evenNormal
  rw [← map_add]
  congr 1
  apply Prod.ext
  · funext g
    cases g with
    | sigma => exact (add_zero (0 : V)).symm
    | tau => exact (add_zero (0 : V)).symm
    | wild i => fin_cases i <;> first | rfl | exact (add_zero (0 : V)).symm
  · funext jk
    rcases jk with ⟨j, k⟩
    fin_cases k <;> rfl

section Comparison
variable {n q : ℕ} {Rw : PWord (Generator n)} {w : Fin 2 → FreeGroup (Generator n)}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  (rho : ContinuousMonoidHom ((GammaR n q Rw : ProfiniteGrp) : Type) (Bg ⧸ D.M))
  [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction ((GammaR n q Rw : ProfiniteGrp) : Type) DD.Vmod]
  [ContinuousSMul ((GammaR n q Rw : ProfiniteGrp) : Type) DD.Vmod]
  (hcompat : ∀ (g : ((GammaR n q Rw : ProfiniteGrp) : Type)) (v : DD.Vmod),
    g • v = rho0 DD rho g • v)
  (hres : ResolvesAt (gammaFam n q Rw) w (WordLift DD.Vmod DD.C0))
  (hA2 : ∀ v : DD.Vmod, v+v=0)
  (hwildTwo : IsWildTwo (wildAlphabet n)
    (fun i ↦ Count.rho0Continuous DD rho (gammaGen n q Rw i)))
  {W : Type} [Fintype W] [AddCommGroup W]
  (normal : W → (Generator n → DD.Vmod))
  (hadd : ∀ p r, normal (p+r)=normal p+normal r)
  (hmem : ∀ p, heisD1 (A := DD.Vmod)
    (fun i ↦ Count.rho0Continuous DD rho (gammaGen n q Rw i)) w (normal p)=0)
  (hnf : ∀ x, heisD1 (A := DD.Vmod)
    (fun i ↦ Count.rho0Continuous DD rho (gammaGen n q Rw i)) w x=0 →
    ∃! p, x-normal p ∈ Set.range (heisD0 (A := DD.Vmod)
      (fun i ↦ Count.rho0Continuous DD rho (gammaGen n q Rw i))))
  [DistribMulAction ((GammaR n q Rw : ProfiniteGrp) : Type) (ZMod 2)]
  [ContinuousSMul ((GammaR n q Rw : ProfiniteGrp) : Type) (ZMod 2)]
  (htriv : ∀ (g : ((GammaR n q Rw : ProfiniteGrp) : Type)) (a : ZMod 2), g•a=a)
  (Q : W → ZMod 2)
  (hphase : ∀ (p : W) (c : VCocycle DD rho),
    (fun i ↦ c.c (gammaGen n q Rw i))=normal p → QZero DD rho c=Q p)

def sourceNormalAddEquiv : (VCocycle DD rho ⧸ vCobRange DD rho) ≃+ W :=
  (sourceQuotientH1AddEquiv hcompat).trans
    ((Count.h1Equiv_gammaR_range (Count.rho0Continuous DD rho) hcompat hres hA2).trans
      (stokesNormalAddEquiv _ _ normal hadd hmem hnf))

theorem sourceNormalAddEquiv_toEquiv :
    (sourceNormalAddEquiv rho hcompat hres hA2 normal hadd hmem hnf).toEquiv =
      (wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo normal hmem hnf
        htriv Q hphase).phaseEquiv := rfl

include hadd in
theorem phaseComparison_of_normalForm_add
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    (wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo normal hmem hnf
      htriv Q hphase).phaseEquiv (x+y) =
    (wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo normal hmem hnf
      htriv Q hphase).phaseEquiv x +
    (wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo normal hmem hnf
      htriv Q hphase).phaseEquiv y :=
  (sourceNormalAddEquiv rho hcompat hres hA2 normal hadd hmem hnf).map_add x y

include hwildTwo hphase in
theorem sourceNormalAddEquiv_phase (x : VCocycle DD rho ⧸ vCobRange DD rho) :
    QZeroBar DD rho htriv x =
      Q (sourceNormalAddEquiv rho hcompat hres hA2 normal hadd hmem hnf x) :=
  (wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo normal hmem hnf
    htriv Q hphase).phase_eq x

include hwildTwo hphase in
theorem sourceNormalAddEquiv_polar (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    polar (QZeroBar DD rho htriv) x y = polar Q
      (sourceNormalAddEquiv rho hcompat hres hA2 normal hadd hmem hnf x)
      (sourceNormalAddEquiv rho hcompat hres hA2 normal hadd hmem hnf y) := by
  simp only [polar, sourceNormalAddEquiv_phase rho hcompat hres hA2 hwildTwo
    normal hadd hmem hnf htriv Q hphase, map_add]
end Comparison

open Instances.WordPhaseCompactMHandleData

def ramifiedHandleSwapAddEquiv (V : Type) [AddCommGroup V] (h : ℕ) :
    CompactCoordinates V h ≃+ CompactCoordinates V h where
  toEquiv := wPcMRamifiedHandleSwap V h
  map_add' _ _ := rfl

@[simp] theorem ramifiedHandleSwapAddEquiv_toEquiv (V : Type) [AddCommGroup V] (h : ℕ) :
    (ramifiedHandleSwapAddEquiv V h).toEquiv = wPcMRamifiedHandleSwap V h := rfl

section Polar
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
  [DistribMulAction Gamma (ZMod 2)]
  {htriv : ∀ (g : Gamma) (a : ZMod 2), g•a=a}
  {W : Type} [Fintype W] [AddCommGroup W] {Q : W → ZMod 2}

def phaseComparisonAddEquiv (C : SourceWordPhaseComparison DD rho htriv W Q)
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y) :
    (VCocycle DD rho ⧸ vCobRange DD rho) ≃+ W where
  toEquiv := C.phaseEquiv
  map_add' := hadd

theorem phaseComparison_polar (C : SourceWordPhaseComparison DD rho htriv W Q)
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    polar (QZeroBar DD rho htriv) x y = polar Q (C.phaseEquiv x) (C.phaseEquiv y) := by
  simp only [polar, C.phase_eq, hadd]

theorem phaseComparison_polar_reducedMatrix {h : ℕ} [Fintype DD.Vmod]
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wPhCompactWallHandlePhase DD.qbar h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y)
    (hq : IsQuadraticFp2 DD.qbar)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    polar (QZeroBar DD rho htriv) x y =
      ∑ i, ∑ j, reducedCoefficientMatrix h i j *
        polar DD.qbar (blockCoordinates h (C.phaseEquiv x) i)
          (blockCoordinates h (C.phaseEquiv y) j) := by
  rw [phaseComparison_polar C hadd]
  exact polar_compactPhase_reducedMatrix DD.qbar hq h _ _
end Polar

#print axioms stokesNormalAddEquiv
#print axioms stokesNormalClass_add
#print axioms stokesNormalAddEquiv_toEquiv
#print axioms stokesNormalEquiv_add
#print axioms sourceQuotientH1AddEquiv
#print axioms h1OfVQuot_add
#print axioms sourceQuotientH1AddEquiv_toEquiv
#print axioms compactPhaseNormal_add
#print axioms sourceNormalAddEquiv
#print axioms sourceNormalAddEquiv_toEquiv
#print axioms sourceNormalAddEquiv_phase
#print axioms sourceNormalAddEquiv_polar
#print axioms phaseComparison_of_normalForm_add
#print axioms ramifiedHandleSwapAddEquiv
#print axioms ramifiedHandleSwapAddEquiv_toEquiv
#print axioms phaseComparisonAddEquiv
#print axioms phaseComparison_polar
#print axioms phaseComparison_polar_reducedMatrix
end
end GQ2.Dyadic.Instances.WordPhaseAdditiveNormal

