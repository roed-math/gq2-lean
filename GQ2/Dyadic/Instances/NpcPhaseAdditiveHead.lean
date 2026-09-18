import GQ2.Dyadic.Instances.NpcPhaseAdditiveNormal

/-!
# Additive coordinates at actual procyclic-N projected heads

These statements retain the precise full-offset phase at the actual faithful head and
the original lift-level resolver. The normal-form hypotheses of the generic additive
assembler are discharged here; no old x2=0 or inverse-Lc slice is substituted.
-/

namespace GQ2.Dyadic.Instances.NpcPhaseAdditiveHead
noncomputable section
open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic Count Certificates Words Words.Npc NProcyclic LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.NpcWordPhaseModel
open Instances.NpcUnramifiedComparison Instances.NpcRamifiedComparison
open Instances.NpcRamifiedComparisonBase Instances.NpcRamifiedDiagonal
open Instances.NpcPhaseAdditiveNormal
open NProcyclicUnram Instances.NpcUnramifiedFullOffsetHessian
open Certificates.MProcyclic Instances.NpcRamifiedFullOffsetHessian
theorem npcUnramifiedHeadComparison_add
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
          ((2 : ℤ) ^ r))⁻¹ : DD.C0) • v = v → v = 0)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    let C := wPnpcComparison_unramifiedHead rho base hbase pi hpi hf hm hcompat
      hA2 hwildTwo halpha hqe hcardH2 htauHead hwildHead hsigmaFpf hgfpf hufpf
    C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let s0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let t : Marking (2 + 2 * h) DD.C0 :=
    Marking.mk (fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
  let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
  let u : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  have hgfpf' : ∀ v : DD.Vmod, g • v = v → v = 0 := by
    simpa [g, s0, E, N, L] using hgfpf
  have hufpf' : ∀ v : DD.Vmod, u • v = v → v = 0 := by
    simpa [u, s0] using hufpf
  let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
    (unramPhi (A := DD.Vmod) g hufpf') (unramPhi_bijective hgfpf' hufpf')
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcUnramifiedDiagonal base hbase
      (pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)))
      E alpha r d Phi.toAddMonoidHom (Phi.symm a)
  have hbaseOrd : ∀ cc : DD.C0, orderOf cc ∣ Monoid.exponent L := by
    intro cc
    have hsd : Function.Surjective (sdSnd : L →* DD.C0) := by
      intro x
      exact ⟨((0, x) : L), rfl⟩
    exact (Monoid.order_dvd_exponent cc).trans (MonoidHom.exponent_dvd hsd)
  have horder : ∀ x : WordLift DD.Vmod DD.C0, orderOf x ∣ N := by
    intro x
    exact (WordLift.orderOf_dvd_two_mul hA2 hbaseOrd x).trans ⟨2, by ring⟩
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift DD.Vmod DD.C0) :=
    resolvesAt_npcFamOf hN horder alpha r h q d (fun _ ↦ 0)
  have hresolver : MProcyclic.ResolverLifts E (WordLift DD.Vmod DD.C0) := by
    intro x
    simpa only [E, npcResolver_omega2, zpow_natCast] using
      (powOmega2_pow_eq x (horder x) hN)
  have htauAct : ∀ v : DD.Vmod, t.τ • v = v := by
    intro v
    change rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) • v = v
    rw [hpi, htauHead, one_smul]
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), t.x i • v = v := by
    intro i v
    change rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) • v = v
    rw [hpi, hwildHead i, one_smul]
  have hsigmaActFpf : ∀ v : DD.Vmod, t.σ • v = v → v = 0 := by
    intro v hv
    apply hsigmaFpf v
    rw [← hpi]
    change rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) • v = v at hv
    exact hv
  have hrow : IsPhiUnramRow t (resolvedFamily alpha r h q d N) g u DD.Vmod :=
    isPhiUnramRow_npc t hA2 hqe (by omega) hwildAct htauAct d N hresolver
  have huinj : ∀ v : DD.Vmod, v - u • v = 0 → v = 0 := by
    intro v hv
    exact hufpf' v (sub_eq_zero.mp hv).symm
  exact npcStandardHeadComparison_add rho hcompat hres hA2 hwildTwo
    g u Phi hwildAct (scalarActionZmodTwo_triv _) d0 hrow
    (unramPhi_spec (A := DD.Vmod) g hufpf') huinj htauAct hsigmaActFpf
    (fun p c hc ↦
      wPnpc_QZero_eq_wallHandlePhase_of_projectedPhiMark rho base hbase pi hpi hf hm
        halpha hqe hcardH2 c htauHead hwildHead Phi p hc) x y
private theorem isTwoEntryRamifiedRow_npc_at
    {alpha r h q N : ℕ} {d : EtaData}
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA2 : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (htauFpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (halpha : 1 ≤ alpha)
    (hresolver : MProcyclic.ResolverLifts (npcResolver N d) (WordLift A C)) :
    IsTwoEntryRamifiedRow t (resolvedFamily alpha r h q d N) q
      ((t.σ ^ (npcResolver N d) d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) A := by
  intro x
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver N d) (fun _ ↦ (0 : ℤ))
          (tameRelW (2 + 2 * h) q))).a =
        t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hresolver,
      Certificates.foxD_tameRelW_of_tameRel t _ _ ht]
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver N d) (fun _ ↦ (0 : ℤ))
          (Words.Npc.npcW alpha r h d))).a =
        ((t.σ ^ (npcResolver N d) d.toZhat)⁻¹ • x (coreLetter h 0)
            - x (coreLetter h 0))
          - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hresolver,
      Certificates.Npc.foxD_npc_ram t _ _ hA2 hwild htauFpf hTodd halpha d]
theorem exists_npcRamifiedHeadAdditiveComparison
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
    IsQuadraticFp2 d0 ∧ ∃ C : SourceWordPhaseComparison DD rho
      (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h),
      ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let s0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let tau0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)
  let t : Marking (2 + 2 * h) DD.C0 :=
    Marking.mk (fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
  let s := pi s0
  let u := pi tau0
  let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
  let b : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
  have ht : t.TameRelAt q := by
    let theta := Count.rho0Continuous DD rho
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 + 2 * h) q (npcW alpha r h d)).rel theta (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2 + 2 * h) q) = 1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hbaseOrd : ∀ cc : DD.C0, orderOf cc ∣ Monoid.exponent L := by
    intro cc
    have hsd : Function.Surjective (sdSnd : L →* DD.C0) := by
      intro x
      exact ⟨((0, x) : L), rfl⟩
    exact (Monoid.order_dvd_exponent cc).trans (MonoidHom.exponent_dvd hsd)
  have horder : ∀ x : WordLift DD.Vmod DD.C0, orderOf x ∣ N := by
    intro x
    exact (WordLift.orderOf_dvd_two_mul hA2 hbaseOrd x).trans ⟨2, by ring⟩
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift DD.Vmod DD.C0) :=
    resolvesAt_npcFamOf hN horder alpha r h q d (fun _ ↦ 0)
  have hresolver : MProcyclic.ResolverLifts E (WordLift DD.Vmod DD.C0) := by
    intro x
    simpa only [E, npcResolver_omega2, zpow_natCast] using
      (powOmega2_pow_eq x (horder x) hN)
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), t.x i • v = v := by
    intro i v
    change rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) • v = v
    rw [hpi, hwildHead i, one_smul]
  have htauFpf : ∀ v : DD.Vmod, t.τ • v = v → v = 0 := by
    intro v hv
    apply htauHeadFpf v
    rw [← hpi]
    exact hv
  have hTodd : ∀ v : DD.Vmod, powOmega2 t.τ • v = v := by
    intro v
    change powOmega2 tau0 • v = v
    rw [hpi, powOmega2_map pi, powOmega2_eq_one_of_odd htauHeadOdd, one_smul]
  have hrow : IsTwoEntryRamifiedRow t (resolvedFamily alpha r h q d N) q g b DD.Vmod :=
    isTwoEntryRamifiedRow_npc_at t hA2 ht hwildAct htauFpf hTodd (by omega) hresolver
  have hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r h q d N k) = 1 := by
    let theta := Count.rho0Continuous DD rho
    intro k
    exact lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 + 2 * h) q (npcW alpha r h d)) hres k
  have hd : IsQuadraticFp2 (npcRamifiedDiagonal base hbase s u E alpha r d) :=
    isQuadratic_npcRamifiedDiagonal base hbase DD.hquad hA2 s u E halpha d
      htauHeadOdd htauHeadFpf
  have hd0 : IsQuadraticFp2 d0 :=
    isQuadraticFp2_comp (npcRamifiedDiagonal base hbase s u E alpha r d) hd
      (⇑Phi.symm) (fun a b ↦ map_add Phi.symm a b) (map_zero Phi.symm)
  refine ⟨hd0, ?_⟩
  exact exists_npcTwistedAdditiveComparison rho hcompat hres hA2 hwildTwo
    g b Phi hwildAct (scalarActionZmodTwo_triv _) d0 hrow htauFpf hr
    (fun p c hc ↦
      wPnpc_QZero_eq_ramifiedWallHandlePhase_of_projectedTwistedMark
        rho base hbase pi hpi hf hm hphi halpha hqe hcardH2 c hwildHead
        htauHeadOdd htauHeadFpf p hc)


end
end GQ2.Dyadic.Instances.NpcPhaseAdditiveHead
