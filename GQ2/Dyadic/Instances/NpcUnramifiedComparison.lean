/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian
import GQ2.Dyadic.Instances.NpcWordPhaseModel
import GQ2.Dyadic.Instances.WordPhaseModel

/-!
# Unramified procyclic-N source phase comparison

This file converts the full-offset unramified Npc Hessian into the standard twisted-head phase
model.  The coordinate change is `a = Phi c0`, so the only diagonal later exposed to the Gauss
layer is

`a ↦ npcUnramifiedDiagonal ... Phi.toAddMonoidHom (Phi.symm a)`.

The source comparison itself does not require this function to be quadratic.  Quadraticity is
the sole analytic input needed when packaging the unramified branch into `wPnpcPhaseModel`;
no separate polar/operator identity or Gauss premise survives.

This module does not close the ramified boundary branch.  There the correct first-order normal
cochain is `evenTwistedNormal` with generally nonzero `x2`, while the landed ramified Npc
Hessian theorem assumes `x2 = 0`.  Evaluating that twisted offset, including its truncated
`omega2` central charge, remains a separate second-order input.
-/

namespace GQ2.Dyadic.Instances.NpcUnramifiedComparison

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.NpcWordPhaseModel
open GQ2.Dyadic.Instances.NpcWordPhaseSeam
open GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [Finite A] [DistribMulAction C A]
def wPnpcPhiCoordsEquiv (h : ℕ) (A : Type*) [AddCommGroup A] (Phi : A ≃+ A) :
    (A × A × (Fin h × Fin 2 → A)) ≃ ((A × A) × (Fin h → A × A)) where
  toFun r := ((Phi r.1, r.2.1), fun j ↦ finTwoProdAddEquiv (fun k ↦ r.2.2 (j, k)))
  invFun p := (Phi.symm p.1.1, p.1.2,
    fun jk ↦ (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2)
  left_inv r := by
    apply Prod.ext
    · exact Phi.symm_apply_apply r.1
    · apply Prod.ext
      · rfl
      · funext jk
        rcases jk with ⟨j, k⟩
        fin_cases k <;> rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · exact Phi.apply_symm_apply p.1.1
      · rfl
    · funext j
      apply Prod.ext <;> rfl

/-- The Npc normal cochain after the cross-operator change of variables. -/
def wPnpcPhaseNormal (h : ℕ) {A : Type*} [AddCommGroup A]
    (Phi : A ≃+ A) (p : (A × A) × (Fin h → A × A)) :
    Generator (2 + 2 * h) → A :=
  let r := (wPnpcPhiCoordsEquiv h A Phi).symm p
  evenPhiNormal h Phi.toAddMonoidHom r.1 r.2.1 r.2.2

@[simp] theorem wPnpcPhaseNormal_sigma (h : ℕ) {A : Type*} [AddCommGroup A]
    (Phi : A ≃+ A) (p : (A × A) × (Fin h → A × A)) :
    wPnpcPhaseNormal h Phi p .sigma = 0 := by
  simp [wPnpcPhaseNormal]

@[simp] theorem wPnpcPhaseNormal_tau (h : ℕ) {A : Type*} [AddCommGroup A]
    (Phi : A ≃+ A) (p : (A × A) × (Fin h → A × A)) :
    wPnpcPhaseNormal h Phi p .tau = 0 := by
  simp [wPnpcPhaseNormal]

@[simp] theorem wPnpcPhaseNormal_coreLetter (h : ℕ)
    {A : Type*} [AddCommGroup A] (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) (i : Fin 3) :
    wPnpcPhaseNormal h Phi p (coreLetter h i) =
      ![Phi.symm p.1.1, p.1.2, p.1.1] i := by
  fin_cases i
  · rfl
  · rfl
  · exact Phi.apply_symm_apply p.1.1

@[simp] theorem wPnpcPhaseNormal_handleU {h : ℕ}
    {A : Type*} [AddCommGroup A] (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) (j : Fin h) :
    wPnpcPhaseNormal h Phi p (handleU j) = (p.2 j).1 := by
  show evenPhiNormal h Phi.toAddMonoidHom _ _ _ (handleU j) = _
  rw [evenPhiNormal_handleU]
  rfl

@[simp] theorem wPnpcPhaseNormal_handleV {h : ℕ}
    {A : Type*} [AddCommGroup A] (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) (j : Fin h) :
    wPnpcPhaseNormal h Phi p (handleV j) = (p.2 j).2 := by
  show evenPhiNormal h Phi.toAddMonoidHom _ _ _ (handleV j) = _
  rw [evenPhiNormal_handleV]
  rfl

theorem wPnpcPhaseNormal_coordsEquiv (h : ℕ)
    {A : Type*} [AddCommGroup A] (Phi : A ≃+ A)
    (r : A × A × (Fin h × Fin 2 → A)) :
    wPnpcPhaseNormal h Phi (wPnpcPhiCoordsEquiv h A Phi r) =
      evenPhiNormal h Phi.toAddMonoidHom r.1 r.2.1 r.2.2 := by
  simp [wPnpcPhaseNormal]

omit [Finite A] in
theorem wPnpcPhaseNormal_closed
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (g u : C) (hrow : IsPhiUnramRow t w g u A)
    (Phi : A ≃+ A)
    (hPhi : ∀ a, Phi a - u • Phi a = a - g • a)
    (p : (A × A) × (Fin h → A × A)) :
    heisD1 (A := A) t w (wPnpcPhaseNormal h Phi p) = 0 := by
  unfold wPnpcPhaseNormal
  exact heisD1_evenPhiNormal_eq_zero g u t w hrow Phi.toAddMonoidHom hPhi _ _ _

theorem wPnpcPhaseNormal_form
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (g u : C) (hrow : IsPhiUnramRow t w g u A)
    (Phi : A ≃+ A)
    (hPhi : ∀ a, Phi a - u • Phi a = a - g • a)
    (huinj : ∀ a : A, a - u • a = 0 → a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (htau : ∀ a : A, t.τ • a = a)
    (hsigma : ∀ a : A, t.σ • a = a → a = 0) :
    ∀ x, heisD1 (A := A) t w x = 0 →
      ∃! p : (A × A) × (Fin h → A × A),
        x - wPnpcPhaseNormal h Phi p ∈ Set.range (heisD0 t) := by
  intro x hx
  obtain ⟨r, hr, hu⟩ := evenPhiNormalForm_of_row g u t w hrow
    Phi.toAddMonoidHom hPhi huinj hwild htau hsigma x hx
  refine ⟨wPnpcPhiCoordsEquiv h A Phi r, ?_, ?_⟩
  · change x - wPnpcPhaseNormal h Phi (wPnpcPhiCoordsEquiv h A Phi r) ∈ _
    rw [wPnpcPhaseNormal_coordsEquiv]
    exact hr
  · intro p hp
    have hpr : (wPnpcPhiCoordsEquiv h A Phi).symm p = r := by
      refine hu _ ?_
      simpa [wPnpcPhaseNormal] using hp
    rw [← hpr, Equiv.apply_symm_apply]

noncomputable def wPnpcPhaseComparison_of_standardHeadPhase
    {alpha r h q N : ℕ} {d : EtaData}
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
    (hcompat : ∀
      (g : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift DD.Vmod DD.C0))
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (g u : DD.C0)
    (hrow : IsPhiUnramRow
      (Marking.mk (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
      (resolvedFamily alpha r h q d N) g u DD.Vmod)
    (Phi : DD.Vmod ≃+ DD.Vmod)
    (hPhi : ∀ v, Phi v - u • Phi v = v - g • v)
    (huinj : ∀ v : DD.Vmod, v - u • v = 0 → v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) • v = v)
    (htau : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) • v = v)
    (hsigma : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) • v = v → v = 0)
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (g : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (a : ZMod 2), g • a = a)
    (d0 : DD.Vmod → ZMod 2)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) =
          wPnpcPhaseNormal h Phi p →
      QZero DD rho c = wPnpcWallHandlePhase d0 DD.qbar h p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let t : Marking (2 + 2 * h) DD.C0 :=
    Marking.mk (fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPnpcPhaseNormal h Phi)
    (wPnpcPhaseNormal_closed t _ g u hrow Phi hPhi)
    (wPnpcPhaseNormal_form t _ g u hrow Phi hPhi huinj hwild htau hsigma)
    htriv (wPnpcWallHandlePhase d0 DD.qbar h) hphase

theorem wPnpc_QZero_eq_wallHandlePhase_of_projectedPhiMark
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (Phi : DD.Vmod ≃+ DD.Vmod)
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) =
      wPnpcPhaseNormal h Phi p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    QZero DD rho c = wPnpcWallHandlePhase
      (fun a ↦ npcUnramifiedDiagonal base hbase
        (pi (rho0 DD rho
          (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)))
        E alpha r d Phi.toAddMonoidHom (Phi.symm a)) DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let E2 : ℤ_[2] → ℤ := fun _ ↦ 0
  letI : TopologicalSpace Cbar := ⊥
  letI : DiscreteTopology Cbar := ⟨rfl⟩
  let K := WordCoh.CentExt (kappa0Cocycle DD.dat DD.hdat)
  letI : Finite K := inferInstance
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := ⟨rfl⟩
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hordK : ∀ y : K, orderOf y ∣ N := by
    intro y
    have hbasePow : y.base ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one y.base
    exact (nc3_orderOf_dvd_two_mul DD.dat DD.hdat hbasePow).trans ⟨2, by ring⟩
  have homega : ∀ y : K, y ^ᶻ omega2 = y ^ E omega2 := by
    intro y
    change y ^ᶻ omega2 = y ^ npcResolver N d omega2
    rw [npcResolver_omega2, PWord.zpowHat_omega2_zpow hN (hordK y), zpow_natCast]
  have heta : ∀ y : K, y ^ᶻ d.toZhat = y ^ E d.toZhat := by
    intro y
    change y ^ᶻ d.toZhat = y ^ npcResolver N d d.toZhat
    rw [npcResolver_toZhat, EtaData.toZhat,
      zpowHat_etaHatZ_zpow hN (hordK y), zpow_natCast]
  have hresolved : ∀ k, PWord.ResolvedAt
      (WordCoh.lift
        (fun i ↦ graphSemiProdHom c
          (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
        (kappa0Cocycle DD.dat DD.hdat)) E E2
      (gammaFam (2 + 2 * h) q (npcW alpha r h d) k) := by
    intro k
    fin_cases k
    · exact PWord.resolvedAt_of_isOmega2Only _ E E2 homega _
        (isOmega2Only_tameRelW (2 + 2 * h) q)
    · exact Count.resolvedAt_npcW _ homega heta alpha r
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcval : ∀ i, c.c (gammaGen (2 + 2 * h) q (npcW alpha r h d) i) =
      wPnpcPhaseNormal h Phi p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))) =
        Certificates.hessMark
          (pi (rho0 DD rho
            (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)))
          (1 : Cbar)
          (fun i ↦ wPnpcPhaseNormal h Phi p (.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPnpcPhaseNormal_sigma h Phi p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPnpcPhaseNormal_tau h Phi p)) htauHead
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  let raw := (wPnpcPhiCoordsEquiv h DD.Vmod Phi).symm p
  have hoffsets :
      (fun i ↦ wPnpcPhaseNormal h Phi p (.wild i)) =
        npcPhiOffsets h Phi.toAddMonoidHom raw.1 raw.2.1 raw.2.2 := by
    rfl
  have hraw := (wPnpcPhiCoordsEquiv h DD.Vmod Phi).apply_symm_apply p
  have hraw0 : raw.1 = Phi.symm p.1.1 := by
    apply Phi.injective
    have hh := congrArg (fun x ↦ x.1.1) hraw
    simp [raw, wPnpcPhiCoordsEquiv] at hh ⊢
  have hraw1 : raw.2.1 = p.1.2 := congrArg (fun x ↦ x.1.2) hraw
  have hrawU : ∀ j, raw.2.2 (j, 0) = (p.2 j).1 := by
    intro j
    exact congrArg (fun x ↦ (x.2 j).1) hraw
  have hrawV : ∀ j, raw.2.2 (j, 1) = (p.2 j).2 := by
    intro j
    exact congrArg (fun x ↦ (x.2 j).2) hraw
  rw [wPnpc_QZero_eq_graphHessianTrace rho DD.hdat (by omega) hqe hcardH2
      c E E2 hresolved,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) phi
      (tameRelW (2 + 2 * h) q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) phi
      (npcW alpha r h d),
    hmark, hoffsets,
    wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase _ _ _ E E2,
    zero_add,
    hessRelZ_npcW_evenPhiNormal base hbase _ E E2 (Vmod_exp2 DD)
      (npcResolver_omega2 N d) (omega2Exp_fourMulExponent_mod_four L)
      alpha r d Phi.toAddMonoidHom raw.1 raw.2.1 raw.2.2]
  rw [hraw0, hraw1]
  simp_rw [hrawU, hrawV]
  dsimp only [E, N, L, wPnpcWallHandlePhase, plusFormD]
  have hPhiInv : Phi.toAddMonoidHom (Phi.symm p.1.1) = p.1.1 :=
    Phi.apply_symm_apply p.1.1
  rw [hPhiInv]
  rw [polar_comm]

/-- The unramified Npc source comparison at a faithful projected head.  All resolver and
first-order normal-form data are constructed at the same semidirect-product exponent used by
the full-offset Hessian. -/
noncomputable def wPnpcComparison_unramifiedHead
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
    let N := 4 * Monoid.exponent L
    let E := npcResolver N d
    let s0 : DD.C0 := rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
    let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
    let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
      (unramPhi (A := DD.Vmod) g hufpf)
      (by simpa [g, s0, E, N, L] using
        (unramPhi_bijective (A := DD.Vmod) hgfpf hufpf))
    let d0 : DD.Vmod → ZMod 2 := fun a ↦
      npcUnramifiedDiagonal base hbase
        (pi (rho0 DD rho
          (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)))
        E alpha r d Phi.toAddMonoidHom (Phi.symm a)
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h) := by
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
  exact wPnpcPhaseComparison_of_standardHeadPhase rho hcompat hres hA2 hwildTwo
    g u hrow Phi (unramPhi_spec (A := DD.Vmod) g hufpf') huinj
    hwildAct htauAct hsigmaActFpf (scalarActionZmodTwo_triv _) d0
    (fun p c hc ↦
      wPnpc_QZero_eq_wallHandlePhase_of_projectedPhiMark rho base hbase pi hpi hf hm
        halpha hqe hcardH2 c htauHead hwildHead Phi p hc)

#print axioms wPnpcPhiCoordsEquiv
#print axioms wPnpcPhaseNormal
#print axioms wPnpcPhaseNormal_sigma
#print axioms wPnpcPhaseNormal_tau
#print axioms wPnpcPhaseNormal_coreLetter
#print axioms wPnpcPhaseNormal_handleU
#print axioms wPnpcPhaseNormal_handleV
#print axioms wPnpcPhaseNormal_coordsEquiv
#print axioms wPnpcPhaseNormal_closed
#print axioms wPnpcPhaseNormal_form
#print axioms wPnpcPhaseComparison_of_standardHeadPhase
#print axioms wPnpc_QZero_eq_wallHandlePhase_of_projectedPhiMark
#print axioms wPnpcComparison_unramifiedHead

end
end GQ2.Dyadic.Instances.NpcUnramifiedComparison
