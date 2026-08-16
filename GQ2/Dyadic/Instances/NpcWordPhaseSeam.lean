/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcWordPhaseTrace
import GQ2.Dyadic.Instances.GammaLGraphHessian

/-!
# The scalar orientation and graph-Hessian seam for procyclic N

The scalar word trace for the uniform Npc resolver determines a canonical orientation of
continuous scalar `H²` whenever the flexible comparison is surjective.  The scalar Hilbert
count supplies that surjectivity, and the resulting orientation identifies `QZero` with the
sum of the two evaluated word Hessians.

The final identity keeps the graph-extension resolver as an exact premise.  This module does
not evaluate the Npc Hessian on the unramified full-offset graph marking; in particular it does
not replace the required relation `x₂ = Φ x₀` by the stronger and generally false `x₂ = 0`.
-/

namespace GQ2.Dyadic.Instances.NpcWordPhaseSeam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.NProcyclic
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.NpcWordPhaseTrace

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

section Orientation

variable {alpha r h q : ℕ} {d : EtaData} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
  [ContinuousSMul ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
  [DistribMulAction C (ZMod 2)]

local notation "Gamma" => ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
local notation "gen" => gammaGen (2 + 2 * h) q (npcW alpha r h d)
local notation "W" => gammaFam (2 + 2 * h) q (npcW alpha r h d)
local notation "w" => resolvedFamily alpha r h q d (4 * Monoid.exponent C)

def wPnpcScalarFlexibleResolverSystem
    (rho : ContinuousMonoidHom Gamma C) (hα : 1 ≤ alpha) (hq : Even q) :
    ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) (ZMod 2) :=
        DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := ZMod 2) W
        (fun i ↦ rho (gen i)) w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) := by
  intro V hV
  let Q := Gamma ⧸ V.toSubgroup
  letI : DistribMulAction Q (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
  let wV := resolvedFamily alpha r h q d (4 * Monoid.exponent Q)
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := Q) (A := ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hq d
  have hres : ResolvesAt W wV (WordLift (ZMod 2) Q) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) Q) (HeisLift (ZMod 2) Q) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  refine { word := wV, resolves := hres, range_eq := ?_ }
  apply congrArg AddMonoidHom.range
  apply DFunLike.ext _ _
  intro x
  have hleft := wPnpc_heisD1_resolvedFamily_apply
    (alpha := alpha) (r := r) (d := d)
    (t := Marking.mk (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) hα hq x
  have hright := wPnpc_heisD1_resolvedFamily_apply
    (alpha := alpha) (r := r) (d := d)
    (t := Marking.mk (fun i ↦ rho (gen i))) hα hq x
  exact hleft.trans hright.symm

noncomputable def wPnpcScalarH2WordFlexible
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q) :
    H2 Gamma (ZMod 2) →+ WordH2 (fun i ↦ rho (gen i)) w (ZMod 2) :=
  globalModuleH2WordFlexible
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d))
    rho hcompat (fun V ↦ hwildLevel_gammaR V) (by decide)
    (wPnpcScalarFlexibleResolverSystem rho hα hq)

theorem wPnpcScalarH2WordFlexible_injective
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q) :
    Function.Injective (wPnpcScalarH2WordFlexible rho hcompat hα hq) :=
  globalModuleH2WordFlexible_injective
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d))
    rho hcompat (fun V ↦ hwildLevel_gammaR V) (by decide)
    (wPnpcScalarFlexibleResolverSystem rho hα hq)

def wPnpcScalarH2TraceEquiv_of_surjective
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hsurj : Function.Surjective (wPnpcScalarH2WordFlexible rho hcompat hα hq)) :
    H2 Gamma (ZMod 2) ≃+ ZMod 2 :=
  (AddEquiv.ofBijective (wPnpcScalarH2WordFlexible rho hcompat hα hq)
    ⟨wPnpcScalarH2WordFlexible_injective rho hcompat hα hq, hsurj⟩).trans
      (wPnpcWordH2TraceEquiv (Marking.mk (fun i ↦ rho (gen i))) hα hq hr)

@[simp] theorem wPnpcScalarH2TraceEquiv_of_surjective_mk
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hsurj : Function.Surjective (wPnpcScalarH2WordFlexible rho hcompat hα hq))
    (f : Z2 Gamma (ZMod 2)) :
    wPnpcScalarH2TraceEquiv_of_surjective rho hcompat hα hq hr hsurj
        (H2mk Gamma (ZMod 2) f) =
      ∑ k, moduleObsFun W gen rho hcompat f k := rfl

omit [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)] [DistribMulAction Gamma (ZMod 2)]
  [ContinuousSMul Gamma (ZMod 2)] [DistribMulAction C (ZMod 2)] in
theorem wPnpcScalarH2WordFlexible_surjective
    (rho : ContinuousMonoidHom Gamma C)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo Gamma
      Nat.card (H2 Gamma (ZMod 2)) = 2)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    letI : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo Gamma
    letI : ContinuousSMul Gamma (ZMod 2) := scalarActionZmodTwo_continuousSMul Gamma
    Function.Surjective (wPnpcScalarH2WordFlexible rho (fun _ _ ↦ rfl) hα hq) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo Gamma
  letI : ContinuousSMul Gamma (ZMod 2) := scalarActionZmodTwo_continuousSMul Gamma
  let f := wPnpcScalarH2WordFlexible rho (fun _ _ ↦ rfl) hα hq
  have hinj : Function.Injective f :=
    wPnpcScalarH2WordFlexible_injective rho (fun _ _ ↦ rfl) hα hq
  letI : Finite (H2 Gamma (ZMod 2)) := Finite.of_injective f hinj
  letI : Fintype (H2 Gamma (ZMod 2)) := Fintype.ofFinite _
  letI : Fintype (WordH2 (fun i ↦ rho (gen i)) w (ZMod 2)) := Fintype.ofFinite _
  have hcard : Nat.card (H2 Gamma (ZMod 2)) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w (ZMod 2)) := by
    calc
      Nat.card (H2 Gamma (ZMod 2)) = 2 := hcardH2
      _ = Nat.card (ZMod 2) := (Nat.card_zmod 2).symm
      _ = Nat.card (WordH2 (fun i ↦ rho (gen i)) w (ZMod 2)) :=
        (Nat.card_congr
          (wPnpcWordH2TraceEquiv (Marking.mk (fun i ↦ rho (gen i))) hα hq hr).toEquiv).symm
  exact ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩).2

end Orientation

theorem wPnpc_QZero_eq_graphHessianTrace
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hresolved :
      letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
        inferInstanceAs (Finite (DD.Vmod × DD.C0))
      letI : Finite
          (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) :=
        inferInstance
      letI : TopologicalSpace
          (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⊥
      letI : DiscreteTopology
          (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⟨rfl⟩
      ∀ k, PWord.ResolvedAt
        (WordCoh.lift
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) E E₂
        (gammaFam (2 + 2 * h) q (npcW alpha r h d) k)) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c =
      hessRelZ
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat) E E₂
          (tameRelW (2 + 2 * h) q) +
        hessRelZ
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat) E E₂
          (npcW alpha r h d) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
    inferInstanceAs (Finite (DD.Vmod × DD.C0))
  letI : Finite
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) :=
    inferInstance
  letI : TopologicalSpace
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⊥
  letI : DiscreteTopology
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⟨rfl⟩
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let W : Fin 2 → PWord (Generator (2 + 2 * h)) :=
    gammaFam (2 + 2 * h) q (npcW alpha r h d)
  let w : Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
    resolvedFamily alpha r h q d (4 * Monoid.exponent L)
  let gen : Generator (2 + 2 * h) →
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) :=
    gammaGen (2 + 2 * h) q (npcW alpha r h d)
  let graph : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) L :=
    ⟨graphSemiProdHom c, continuous_graphSemiProdHom c⟩
  let kappa := GQ2.Dyadic.kappa0Cocycle DD.dat hdat
  let f : Z2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    ⟨graphPullback DD.dat (fun g ↦ rho0 DD rho g) c.c,
      graphPullback_mem_Z2_of_cocycle (fun _ _ ↦ rfl) c⟩
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := L) (A := ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hq d
  have hresolve : ResolvesAt W w (WordLift (ZMod 2) L) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) L) (HeisLift (ZMod 2) L) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift (fun i ↦ graph (gen i)) (w k) = 1 :=
    lower_rel (A := ZMod 2) graph (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d))
      hresolve
  have hsurj : Function.Surjective
      (wPnpcScalarH2WordFlexible graph (fun _ _ ↦ rfl) hα hq) :=
    wPnpcScalarH2WordFlexible_surjective graph hα hq hcardH2 hr
  let orient := wPnpcScalarH2TraceEquiv_of_surjective
    graph (fun _ _ ↦ rfl) hα hq hr hsurj
  have htrace : QZero DD rho c = ∑ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k := by
    rw [QZero]
    change iotaB f.1 = _
    rw [iotaB_eq_h2Equiv orient f]
    exact wPnpcScalarH2TraceEquiv_of_surjective_mk
      graph (fun _ _ ↦ rfl) hα hq hr hsurj f
  have hnorm : ∀ x y : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
      moduleNormalize f.1 (x, y) = kappa.κ (graph x) (graph y) := by
    intro x y
    have h11 : f.1 (1, 1) = 0 := by
      change DD.dat.f (c.c 1) (rho0 DD rho 1 • c.c 1) +
        DD.dat.m (rho0 DD rho 1) (c.c 1) = 0
      rw [c.c_one, smul_zero, hdat.f_zero_left, map_one, hdat.m_one, add_zero]
    rw [moduleNormalize, h11, smul_zero, sub_zero]
    exact graphPullback_eq_dyadicKappa0_graph hdat c x y
  have hcoord : ∀ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k =
      hessRelZ (fun i ↦ graph (gen i)) kappa E E₂ (W k) := by
    intro k
    exact moduleObsFun_eq_hessRelZ_of_normalized_pullback
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) W gen graph f kappa hnorm E E₂ k (hresolved k)
  rw [htrace, Fin.sum_univ_two, hcoord, hcoord]
  rfl

#print axioms wPnpcScalarFlexibleResolverSystem
#print axioms wPnpcScalarH2WordFlexible
#print axioms wPnpcScalarH2WordFlexible_injective
#print axioms wPnpcScalarH2TraceEquiv_of_surjective
#print axioms wPnpcScalarH2TraceEquiv_of_surjective_mk
#print axioms wPnpcScalarH2WordFlexible_surjective
#print axioms wPnpc_QZero_eq_graphHessianTrace

end
end GQ2.Dyadic.Instances.NpcWordPhaseSeam
