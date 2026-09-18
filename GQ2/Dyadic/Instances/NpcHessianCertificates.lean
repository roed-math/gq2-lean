import GQ2.Dyadic.Instances.NpcPhaseAdditiveHead
import GQ2.Dyadic.Instances.WordPhaseWallHandleCertificates
import GQ2.Dyadic.Instances.NpcUnramifiedDiagonal

/-!
# Original Hessian records for the actual full-offset Npc source phase

The diagonal and coefficient action remain pinned to the actual projected head and
lift-level resolver. These records certify the completed normal form, not the older
x2=0 slice. In particular no inverse-Lc premise is added. Dimensions and F₂ module
structures are derived by the generic wall-handle constructor.
-/

namespace GQ2.Dyadic.Instances.NpcHessianCertificates
noncomputable section
open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic Count Certificates Words Words.Npc NProcyclic NProcyclicUnram LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.NpcWordPhaseModel
open Instances.NpcUnramifiedComparison Instances.NpcUnramifiedFullOffsetHessian
open Instances.NpcUnramifiedDiagonal Instances.NpcRamifiedFullOffsetHessian
open Instances.NpcPhaseAdditiveHead Instances.WordPhaseWallHandleCertificates

noncomputable def npcUnramifiedHeadHessian
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod,
      pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) • v = v → v = 0)
    (hgfpf : ∀ v : DD.Vmod,
      ((rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
          npcResolver
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) d d.toZhat)⁻¹ :
        DD.C0) • v = v → v = 0)
    (hufpf : ∀ v : DD.Vmod,
      ((rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
          ((2 : ℤ) ^ r))⁻¹ : DD.C0) • v = v → v = 0) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    let s0 : DD.C0 := rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
    let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
    let u : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
    let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
      (unramPhi (A := DD.Vmod) g hufpf)
      (by simpa [g, u, s0, E, L] using
        (unramPhi_bijective (A := DD.Vmod) hgfpf hufpf))
    let s := pi s0
    let d0 : DD.Vmod → ZMod 2 := fun a ↦
      npcUnramifiedDiagonal base hbase s E alpha r d
        Phi.toAddMonoidHom (Phi.symm a)
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    SourceWallHessian DD rho (scalarActionZmodTwo_triv _) d0 h := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let s0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
  let u : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  have hgfpf' : ∀ v : DD.Vmod, g • v = v → v = 0 := by
    simpa [g, s0, E, N, L] using hgfpf
  have hufpf' : ∀ v : DD.Vmod, u • v = v → v = 0 := by
    simpa [u, s0] using hufpf
  let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
    (unramPhi (A := DD.Vmod) g hufpf') (unramPhi_bijective hgfpf' hufpf')
  let s := pi s0
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcUnramifiedDiagonal base hbase s E alpha r d
      Phi.toAddMonoidHom (Phi.symm a)
  letI : TopologicalSpace Cbar := ⊥
  letI : DiscreteTopology Cbar := ⟨rfl⟩
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  have hsd : Function.Surjective (sdSnd : L →* DD.C0) := by
    intro x
    exact ⟨((0, x) : L), rfl⟩
  have hord : orderOf s ∣ N := by
    exact (orderOf_map_dvd pi s0).trans
      ((Monoid.order_dvd_exponent s0).trans
        ((MonoidHom.exponent_dvd hsd).trans ⟨4, by ring⟩))
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hresolverEta : s ^ E d.toZhat = s ^ᶻ etaHatZ d.toPadic := by
    change s ^ npcResolver N d d.toZhat = s ^ᶻ etaHatZ d.toPadic
    rw [npcResolver_toZhat, zpow_natCast]
    exact (zpowHat_etaHatZ_zpow hN hord d.toPadic).symm
  have hPhiQuadratic : ∀ v : DD.Vmod,
      v + (s ^ E d.toZhat)⁻¹ • v =
        Phi.toAddMonoidHom v + (s ^ (2 ^ r : ℤ))⁻¹ • Phi.toAddMonoidHom v := by
    intro v
    have hs := unramPhi_spec (A := DD.Vmod) g hufpf' v
    change Phi v - u • Phi v = v - g • v at hs
    rw [sub_eq_add_neg, Certificates.neg_eq_self hA2,
      sub_eq_add_neg, Certificates.neg_eq_self hA2] at hs
    rw [hpi g, hpi u] at hs
    simpa [g, u, s, s0] using hs.symm
  have hd : IsQuadraticFp2 d0 :=
    isQuadratic_npcUnramifiedDiagonal_comp base hbase DD.hquad hA2
      s E d hresolverEta halpha Phi.toAddMonoidHom Phi.symm.toAddMonoidHom
      hPhiQuadratic
  let C := wPnpcComparison_unramifiedHead rho base hbase pi hpi hf hm hcompat
    hA2 hwildTwo halpha hqe hcardH2 htauHead hwildHead hsigmaFpf hgfpf hufpf
  exact sourceWallHessianOfComparison DD rho (scalarActionZmodTwo_triv _) d0 hd C
    (npcUnramifiedHeadComparison_add rho base hbase pi hpi hf hm hcompat hA2 hwildTwo
      halpha hqe hcardH2 htauHead hwildHead hsigmaFpf hgfpf hufpf)

theorem nonempty_npcRamifiedHeadHessian
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) • v = v → v = 0) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    let s := pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma))
    let u := pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau))
    let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
    let d0 : DD.Vmod → ZMod 2 := fun a ↦
      npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    Nonempty (SourceWallHessian DD rho (scalarActionZmodTwo_triv _) d0 h) := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  obtain ⟨hd, C, hadd⟩ := exists_npcRamifiedHeadAdditiveComparison rho base hbase pi hpi hf hm
    hphi hcompat hA2 hwildTwo halpha hqe hcardH2 hwildHead htauHeadOdd htauHeadFpf
  exact ⟨sourceWallHessianOfComparison DD rho (scalarActionZmodTwo_triv _) _ hd C hadd⟩


end
end GQ2.Dyadic.Instances.NpcHessianCertificates
