import GQ2.Dyadic.Instances.WordPhaseAdditiveNormal
import GQ2.Dyadic.Instances.NpcUnramifiedComparison
import GQ2.Dyadic.Instances.NpcRamifiedComparison

/-!
# Additivity of the actual full-offset procyclic-N normal coordinates

The completed Npc proof uses x2 determined by the cocycle equation, not the old
x2=0 slice. These normal maps are additive, so their source/word comparison can
be retained as an additive (hence F₂-linear) change of coordinates. No inverse-Lc
premise or restriction on the number of handles is introduced.
-/

namespace GQ2.Dyadic.Instances.NpcPhaseAdditiveNormal
noncomputable section
open GQ2 GQ2.Dyadic GQ2.FoxH GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open Count Certificates Words Words.Npc NProcyclic LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.WordPhaseAdditiveNormal
open Instances.NpcWordPhaseModel Instances.NpcUnramifiedComparison
open Instances.NpcRamifiedComparisonBase

theorem npcPhiNormal_add {A : Type*} [AddCommGroup A] (h : ℕ) (Phi : A ≃+ A)
    (p z : (A × A) × (Fin h → A × A)) :
    wPnpcPhaseNormal h Phi (p+z) = wPnpcPhaseNormal h Phi p + wPnpcPhaseNormal h Phi z := by
  unfold wPnpcPhaseNormal evenPhiNormal
  dsimp only
  rw [← (EvenCore.coreHandleAddEquiv h A).symm.map_add]
  congr 1
  apply Prod.ext
  · funext g
    cases g with
    | sigma => exact (add_zero (0 : A)).symm
    | tau => exact (add_zero (0 : A)).symm
    | wild i => fin_cases i <;> simp [wPnpcPhiCoordsEquiv, evenCoreOffsets, map_add]
  · funext jk
    rcases jk with ⟨j, k⟩
    fin_cases k <;> rfl

theorem npcTwistedNormal_add {A C : Type*} [AddCommGroup A] [Group C]
    [DistribMulAction C A] (h : ℕ) (g u : C) (Phi : A ≃+ A)
    (p z : (A × A) × (Fin h → A × A)) :
    wPnpcTwistedPhaseNormal h g u Phi (p+z) =
      wPnpcTwistedPhaseNormal h g u Phi p + wPnpcTwistedPhaseNormal h g u Phi z := by
  unfold wPnpcTwistedPhaseNormal evenTwistedNormal
  dsimp only
  rw [← (EvenCore.coreHandleAddEquiv h A).symm.map_add]
  congr 1
  apply Prod.ext
  · funext k
    cases k with
    | sigma => exact (add_zero (0 : A)).symm
    | tau => exact (add_zero (0 : A)).symm
    | wild i =>
      fin_cases i <;> simp [wPnpcRamifiedCoordsEquiv, evenCoreOffsets, map_add, smul_add,
        add_sub_add_comm]
  · funext jk
    rcases jk with ⟨j, k⟩
    fin_cases k <;> rfl

section Comparison
variable {alpha r h q N : ℕ} {d : EtaData}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    (Bg ⧸ D.M))
  [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
  [ContinuousSMul ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
  (hcompat : ∀ (g : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
    (v : DD.Vmod), g • v = rho0 DD rho g • v)
  (hres : ResolvesAt (gammaFam (2+2*h) q (npcW alpha r h d))
    (resolvedFamily alpha r h q d N) (WordLift DD.Vmod DD.C0))
  (hA2 : ∀ v : DD.Vmod, v+v=0)
  (hwildTwo : IsWildTwo (wildAlphabet (2+2*h)) (fun i => Count.rho0Continuous DD rho
    (gammaGen (2+2*h) q (npcW alpha r h d) i)))
  (g u : DD.C0) (Phi : DD.Vmod ≃+ DD.Vmod)
  (hwild : ∀ (i : Fin (2+2*h+1)) (v : DD.Vmod),
    rho0 DD rho (gammaGen (2+2*h) q (npcW alpha r h d) (.wild i)) • v=v)
  [DistribMulAction ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
  [ContinuousSMul ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
  (htriv : ∀ (g : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
    (a : ZMod 2), g • a=a)
  (d0 : DD.Vmod → ZMod 2)

/-- The very same unramified full-offset comparison is additive. -/
theorem npcStandardHeadComparison_add
    (hrow : IsPhiUnramRow (Marking.mk (fun i => Count.rho0Continuous DD rho
      (gammaGen (2+2*h) q (npcW alpha r h d) i))) (resolvedFamily alpha r h q d N)
      g u DD.Vmod)
    (hPhi : ∀ v, Phi v-u • Phi v=v-g • v)
    (huinj : ∀ v : DD.Vmod, v-u • v=0 → v=0)
    (htau : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2+2*h) q (npcW alpha r h d) .tau) • v=v)
    (hsigma : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2+2*h) q (npcW alpha r h d) .sigma) • v=v → v=0)
    (hphase : ∀ (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho), (fun i => c.c (gammaGen (2+2*h) q (npcW alpha r h d) i)) =
        wPnpcPhaseNormal h Phi p → QZero DD rho c = wPnpcWallHandlePhase d0 DD.qbar h p)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    let C := wPnpcPhaseComparison_of_standardHeadPhase rho hcompat hres hA2 hwildTwo
      g u hrow Phi hPhi huinj hwild htau hsigma htriv d0 hphase
    C.phaseEquiv (x+y) = C.phaseEquiv x + C.phaseEquiv y := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  exact phaseComparison_of_normalForm_add rho hcompat hres hA2 hwildTwo
    _ (npcPhiNormal_add h Phi) _ _ htriv _ hphase x y

include hcompat hres hA2 hwildTwo hwild in
/-- The ramified construction retains its additive witness instead of forgetting it in
`Nonempty`. Its assumptions are exactly the normal-form and full-phase inputs of the
existing ramified assembler; later actual-boundary producers discharge those inputs. -/
theorem exists_npcTwistedAdditiveComparison
    (hrow : IsTwoEntryRamifiedRow (Marking.mk (fun i => Count.rho0Continuous DD rho
      (gammaGen (2+2*h) q (npcW alpha r h d) i))) (resolvedFamily alpha r h q d N)
      q g u DD.Vmod)
    (htau : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2+2*h) q (npcW alpha r h d) .tau) • v=v → v=0)
    (hr : ∀ k, FreeGroup.lift (fun i => Count.rho0Continuous DD rho
      (gammaGen (2+2*h) q (npcW alpha r h d) i)) (resolvedFamily alpha r h q d N k)=1)
    (hphase : ∀ (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho), (fun i => c.c (gammaGen (2+2*h) q (npcW alpha r h d) i)) =
        wPnpcTwistedPhaseNormal h g u Phi p →
        QZero DD rho c = wPnpcWallHandlePhase d0 DD.qbar h p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    ∃ C : SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h),
      ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let normal := wPnpcTwistedPhaseNormal h g u Phi
  have hmem := wPnpcTwistedPhaseNormal_closed _ _ g u hrow Phi
  have hnf := wPnpcTwistedPhaseNormal_form _ _ g u hrow Phi hwild htau hr
  refine ⟨wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo normal
    hmem hnf htriv _ hphase, ?_⟩
  exact phaseComparison_of_normalForm_add rho hcompat hres hA2 hwildTwo
    normal (npcTwistedNormal_add h g u Phi) hmem hnf htriv _ hphase
end Comparison

end
end GQ2.Dyadic.Instances.NpcPhaseAdditiveNormal
