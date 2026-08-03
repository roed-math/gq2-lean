/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLRamifiedGraphPhase
import GQ2.Dyadic.Instances.GammaLDeterminantBridge

/-!
# Closing the ramified determinant phase for the improved L presentation

The ramified graph normal form supplies the quotient-level source/word comparison without an
assumed pointwise phase identity.  This file combines it with the presentation-independent
Arf-zero input for the continuous source quadratic form.  The resulting word phase has the
positive ramified Gauss value required by the determinant bridge.

No Tate duality or local-field theorem is hidden here.  The remaining arithmetic input is
displayed explicitly as a quadratic form on continuous `H¹`, its comparison with `QZeroBar`,
and its Arf-zero theorem.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

local instance finiteSemiProdRamDet {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] [Finite V] [Finite C] :
    Finite (SectionSix.SemiProd C V) := inferInstanceAs (Finite (V × C))

/-- The concrete lower-action facts needed by the ramified graph normal form.  Wild letters
die in the descended action target; `tau` is fixed-point-free, while its two-primary part acts
trivially.  These are representation-theoretic facts, not phase-comparison hypotheses. -/
structure LRamifiedGraphData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M)) where
  wild_eq : ∀ i : Fin (2 * h + 1 + 1),
    rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1
  tau_fixedPointFree : ∀ v : DD.Vmod,
    rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0
  tau_oddPart_fixed : ∀ v : DD.Vmod,
    powOmega2 (rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v

/-- The presentation-independent arithmetic datum that remains in the ramified branch.  In a
local-field application `qSource` is `Q0loc`; the two propositions say that the descended
extension phase is that source form and that the source form has Arf invariant zero. -/
structure LRamifiedSourceArfData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (a : ZMod 2), g • a = a)
    (hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v) where
  qSource : H1 (gamma h q : Type) DD.Vmod → ZMod 2
  source_eq : ∀ x, QZeroBar DD rho htriv x = qSource (h1OfVQuot hcomp x)
  arf_zero : arf qSource = 0

set_option maxHeartbeats 2400000 in
/-- The complete ramified phase model at one finite descended representation.  The graph normal
form proves the source/word comparison.  Transport of the source Arf-zero theorem fixes the
Wall-head sign, and the finite lower action proves internally that the Wall operator preserves
the quadratic form and has two-power order. -/
theorem lSqRamifiedPhaseModel_of_graphData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hqe : Even q) (m : ℕ)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedGraphData (DD := DD) rho)
    (S : letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
        scalarActionZmodTwo ((gamma h q : Type))
      LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 1)).gaussRam m := by
  letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
  letI : Module (ZMod 2) DD.Vmod :=
    AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA2 v)
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4 * Monoid.exponent L
  let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
  let U : DD.Vmod ≃+ DD.Vmod :=
    smulAddEquiv (V := DD.Vmod) ((s ^ (omega2Exp N : ℤ))⁻¹)
  let e : H1 (gamma h q : Type) DD.Vmod ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) :=
    lSqRamifiedGraphSourceH1Equiv rho hcompat G.wild_eq
      G.tau_fixedPointFree G.tau_oddPart_fixed
  have hUq : ∀ v, DD.qbar (U v) = DD.qbar v := by
    intro v
    change DD.qbar (((s ^ (omega2Exp N : ℤ))⁻¹) • v) = DD.qbar v
    exact factorSet_q_invariant DD.dat DD.hdat hA2 _ v
  have hsExp : s ^ Monoid.exponent L = 1 := by
    let p : L := (0, s)
    have hp : p ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p
    calc
      s ^ Monoid.exponent L = sdSnd (p ^ Monoid.exponent L) :=
        (map_pow sdSnd p _).symm
      _ = 1 := by rw [hp]; exact map_one sdSnd
  have hsN : s ^ N = 1 := by
    rw [show N = Monoid.exponent L * 4 by simp [N, Nat.mul_comm], pow_mul, hsExp, one_pow]
  have hord : orderOf s ∣ N := orderOf_dvd_of_pow_eq_one hsN
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hresolved : s ^ omega2Exp N = powOmega2 s := powOmega2_pow_eq s hord hN
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := by
    refine ⟨(orderOf s).factorization 2, ?_⟩
    have hp : powOmega2 s ^ 2 ^ (orderOf s).factorization 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_powOmega2_dvd_two_pow s)
    have hinv : (s ^ omega2Exp N)⁻¹ ^ 2 ^ (orderOf s).factorization 2 = 1 := by
      rw [hresolved, inv_pow, hp, inv_one]
    funext v
    dsimp [U]
    show (((s ^ (omega2Exp N : ℤ))⁻¹ • ·)^[2 ^ (orderOf s).factorization 2]) v = v
    rw [zpow_natCast, smul_iterate_apply, hinv, one_smul]
  have hphase : LRamifiedPointwisePhaseIdentity
      (scalarActionZmodTwo_triv ((gamma h q : Type))) hcompat DD.qbar U h e := by
    exact lRamifiedPointwisePhaseIdentity_of_graphNormalForm rho DD.hdat hqe hcompat
      G.wild_eq G.tau_fixedPointFree G.tau_oddPart_fixed
  have pkg := lRamifiedPhasePackage_standardRam_of_sourceArf_zero
    (scalarActionZmodTwo_triv ((gamma h q : Type))) hcompat
    S.qSource S.source_eq S.arf_zero DD.qbar DD.hquad DD.hns hA2 m
    (by simpa only [Nat.card_eq_fintype_card] using hcard) U hUq hU2 h e hphase
  exact ⟨DD.Vmod × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    lSqWallHandlePhase DD.qbar U h, pkg.1, pkg.2.2⟩

/-! ## Boundary-lift packaging -/

set_option maxHeartbeats 2400000 in
/-- The ramified word phase in the exact boundary-lift signature consumed by the determinant
bridge.  Topology, the pulled-back coefficient action, its continuity, the quadratic module
structure, the graph comparison, and the Wall-operator order calculation are all constructed
internally.  The two callback inputs contain only concrete lower-action facts and the
presentation-independent source-Arf-zero datum, respectively. -/
theorem wordPhaseResidueK_ramified_of_graphData
    {h q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    {b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP)}
    (m : ℕ)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hgraph :
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      let DD := En.descData l hl
      ∀ rho : BoundaryLiftsK b F (SectionNine.blockFrame T Blk hE2).TC,
        LRamifiedGraphData (DD := DD)
          (rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
            (En.radData l hl) rfl rho))
    (hsource :
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      let DD := En.descData l hl
      letI : TopologicalSpace DD.Vmod := ⊥
      letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
      letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
        scalarActionZmodTwo ((gamma h q : Type))
      ∀ rho : BoundaryLiftsK b F (SectionNine.blockFrame T Blk hE2).TC,
        let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho
        letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
          DistribMulAction.compHom DD.Vmod (rho0 DD rhoM)
        let hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
            g • v = rho0 DD rhoM g • v := fun _ _ ↦ rfl
        LRamifiedSourceArfData rhoM (scalarActionZmodTwo_triv _) hcomp) :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    WordPhaseResidueK b F (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
      (scalarActionZmodTwo_triv _)
      ((standardNumerics (2 * h + 1)).gaussRam m) := by
  let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
  let DD := En.descData l hl
  intro rho
  let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
    (En.radData l hl) rfl rho
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  let theta := Count.rho0Continuous DD rhoM
  letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod theta.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × DD.Vmod ↦ p.1 • p.2) =
          (fun p : DD.C0 × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p : ((gamma h q : Type)) × DD.Vmod ↦ (theta p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  have hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rhoM g • v := fun _ _ ↦ rfl
  exact lSqRamifiedPhaseModel_of_graphData rhoM hcompat (Vmod_exp2 DD) hqe m hcard
    (hgraph rho) (hsource rho)

end

end GQ2.Dyadic.LSquare
