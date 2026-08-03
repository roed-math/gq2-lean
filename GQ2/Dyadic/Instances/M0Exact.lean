/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Count.Lifts
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.Count.RStage
import GQ2.Dyadic.Count.Variation
import GQ2.Dyadic.FieldBranchSelector
import GQ2.Dyadic.Instances.Cores

/-!
# Exact lifting for the compact-M presentation

This file constructs `ExactLiftingSemantics` for the improved compact-`M` word
`Words.MCompact.mCompactW α h`, uniformly in the handle count.  Existing M0 resolver,
endpoint, Stokes-upgrade, variation, and generic lift-count machinery supplies all but three
low-level inputs: per-simple Stokes duality, obstruction-zero hom-lift separation, and the
`R`-cocycle cardinality.

The nonzero variation witness is uniform in `α,h`: the compact-`M` core maps onto the fixed
order-two radical quotient by sending its `σ`-slot to the nontrivial class.  Consequently the
scalar `H²` count and the universal half-torsor identity are conclusions, not residuals.
-/

namespace GQ2.Dyadic.MCompact

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.CardH2GammaA DihedralGroup

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The intrinsic compact-M source and its word-level residue -/

/-- The compact-`M` candidate at arbitrary handle count. -/
noncomputable abbrev gamma (α h q : ℕ) : ProfiniteGrp :=
  GammaR (2 + 2 * h) q (mCompactW α h)

/-- The sole word-level analytic residue: perfect Stokes duality on each simple elementary
module at every honest odd resolver, whenever both resolved relators die. -/
def Hsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (t : Marking (2 + 2 * h) C) (e : ℕ), Odd e →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1 →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h) = 1 →
    ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (mCompactFam α h q e) V

/-- The improved compact-M presentation has deficiency `2h+2`. -/
theorem degree (h : ℕ) :
    Nat.card (Generator (2 + 2 * h)) = Nat.card (Fin 2) + ((2 * h + 2) + 1) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Generator.card_generator,
    Fintype.card_fin]
  omega

/-- Upgrade `Hsimp` to Stokes duality on every finite elementary module at a pushed-forward
candidate marking. -/
theorem stokesDuality {α h q : ℕ} (hsimp : Hsimp α h q) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) {e : ℕ} (he : Odd e)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q e) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
      (mCompactFam α h q e) A := by
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift (⇑t) (mCompactFam α h q e k) = 1 := fun k =>
    lower_rel (A := ZMod 2) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres k
  have hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 + 2 * h) q) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 0)
  have hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (mCompactW α h) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 1)
  exact mCompact_stokesDuality t hqe he hrt hrw
    (hsimp C t e he hrt hrw) A hA₂

/-- The variation lane's primary-module Stokes payload. -/
theorem stokesDuality_T {α h q : ℕ} (hsimp : Hsimp α h q) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) (Bg ⧸ D.M)) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
      (mCompactFam α h q (omega2Exp (heisLevel D))) (Additive ↥D.T) := by
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_mCompactFam
      (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_scal hqe).1
  exact stokesDuality hsimp hqe rho
    (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hres
    (Additive ↥D.T) (radT_add_self D)

/-! ## A handle-uniform nonzero variation witness -/

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-- The datum quotient has exponent two. -/
theorem datumQuot_sq (y : Base ⧸ datum.M) : y * y = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, show b * b = 1 from by revert b; decide,
    QuotientGroup.mk_one]

/-- Hence the finite datum quotient is pro-`2`. -/
theorem isProP_datumQuot : IsProP 2 (Base ⧸ datum.M) :=
  isProP_of_isPGroup fun y => ⟨1, by rw [pow_one, pow_two]; exact datumQuot_sq y⟩

/-- The uniform compact-`M` core map, sending the `σ`-slot to the nontrivial datum class. -/
noncomputable def datumCoreHom (α h : ℕ) (hα : 1 ≤ α) :
    ContinuousMonoidHom ((DM α h) : Type) (Base ⧸ datum.M) :=
  mLiftHom α h isProP_datumQuot (coreMark 1 1 (QuotientGroup.mk (r 1)) 1) (by
    rw [mRelWord_coreMark]
    simp only [mWord, commP, one_pow, inv_one, one_mul, mul_one]
    obtain ⟨k, hk⟩ := dvd_pow_self 2 (by omega : α ≠ 0)
    rw [hk, pow_mul,
      show (QuotientGroup.mk (r 1) : Base ⧸ datum.M) ^ 2 = 1 from by
        simpa [pow_two] using datumQuot_sq (QuotientGroup.mk (r 1) : Base ⧸ datum.M)]
    simp)

@[simp] theorem datumCoreHom_gen (α h : ℕ) (hα : 1 ≤ α) (i : Fin (coreRank h)) :
    datumCoreHom α h hα (dmGen α h i) =
      coreMark (h := h) 1 1 (QuotientGroup.mk (r 1)) 1 i :=
  mLiftHom_gen α h _ _ _ i

/-- The induced map from the intrinsic compact-`M` candidate. -/
noncomputable def datumRho (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((gamma α h q : Type)) (Base ⧸ datum.M) :=
  (datumCoreHom α h hα).comp
    (CorePresentation.coreHom (mCorePresentation α h hα) hq0 hqe)

/-- The datum map is onto, uniformly in `α` and the handle count. -/
theorem datumRho_surjective (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (datumRho α h q hα hq0 hqe) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hcases : (QuotientGroup.mk b : Base ⧸ datum.M) = 1
      ∨ (QuotientGroup.mk b : Base ⧸ datum.M) = QuotientGroup.mk (r 1) := quotient_cases b
  rcases hcases with h1 | hr
  · exact ⟨1, by rw [map_one, h1]⟩
  · obtain ⟨γ, hγ⟩ := CorePresentation.coreHom_surjective (mCorePresentation α h hα)
      (hq0 := hq0) (hqe := hqe) (dmC α h)
    refine ⟨γ, ?_⟩
    show datumCoreHom α h hα
      (CorePresentation.coreHom (mCorePresentation α h hα) hq0 hqe γ) = _
    rw [hγ, hr, show dmC α h = dmGen α h 2 from rfl, datumCoreHom_gen,
      coreMark_two]

/-- The scalar `H²` count required by the `R`-stage, derived from the uniform datum map and
the same M0 Stokes residue used by the lift count. -/
theorem cardH2 {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho α h q hα hq0 hqe with hrho
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((gamma α h q : Type)) (Additive ↥datum.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((gamma α h q : Type)) (ElemDual (Additive ↥datum.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma α h q : Type)) (ElemDual (Additive ↥datum.T)) := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × ElemDual (Additive ↥datum.T) => p.1 • p.2)
          = (fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)
            ∘ (fun p : ((gamma α h q : Type)) × ElemDual (Additive ↥datum.T) =>
                (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_mCompactFam
    (Q := WordLift (ZMod 2) (Base ⧸ datum.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := α) (h := h) (q := q) hqe
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel datum)))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel datum)))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := α) (h := h) (q := q) hqe).1
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel datum)))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := α) (h := h) (q := q) hqe).1
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel datum)))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := α) (h := h) (q := q) hqe).1
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective α h q hα hq0 hqe) (fun _ => rfl))
    hresS hresP hresD hresH (stokesDuality_T hsimp hqe rho)
    (stokesDuality hsimp hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective α h q hα hq0 hqe)

/-! ## The first two exact-lifting clauses -/

/-- The `liftsOver_card` clause at every recursion frame.  The generic degree-count theorem is
instantiated with the compact-M family; resolver, endpoint, admissibility, wildness, and the
elementary-module upgrade are discharged uniformly. -/
theorem liftsOver_card {α h q : ℕ} (hsimp : Hsimp α h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics (2 * h + 2)).mMult (Nat.card ↥RF.MB) := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk RF b F rho
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_mCompactFam
    (Q := WordLift (Additive ↥RF.MB) RF.YC)
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (α := α) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q
        (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
      (WordLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q
        (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
      (WordLift (ZMod 2) RF.YC) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (α := α) (h := h) (q := q) hqe).1
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl))
    (nCompact_degree h) hres
    (stokesDuality hsimp hqe rho.1.1
      (odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2)
      hresS (Additive ↥RF.MB) (mb_add_self RF)) hb.2

/-- The universal half-torsor clause.  `NoDescent` and surjectivity create the nonzero
variation class through the landed M0 resolvers; no half-torsor count is assumed. -/
theorem lem86 {α h q : ℕ} (hsimp : Hsimp α h q) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  letI := scalarActionZmodTwo (Bg ⧸ D.M)
  letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
  letI : DistribMulAction ((gamma α h q : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((gamma α h q : Type)) (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma α h q : Type)) (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × ElemDual (Additive ↥D.T) => p.1 • p.2)
          = (fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)
            ∘ (fun p : ((gamma α h q : Type)) × ElemDual (Additive ↥D.T) =>
                (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_mCompactFam
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := α) (h := h) (q := q) hqe
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := α) (h := h) (q := q) hqe).1
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := α) (h := h) (q := q) hqe).1
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (heisLevel D)))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := α) (h := h) (q := q) hqe).1
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (stokesDuality_T hsimp hqe rho)
    (stokesDuality hsimp hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
    (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-! ## The two irreducible R-stage residues -/

/-- Obstruction-zero lower lifts come from homomorphisms into the original marked target.

This is the exact low-level separation input consumed by `blockStageR136K`; it is not a
restatement of equation (136) or of `ExactLiftingSemantics`. -/
def StageSep (α h q : ℕ) : Prop :=
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : ((gamma α h q : Type))) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB),
    obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
        htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom ((gamma α h q : Type)) Y,
        ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ

/-- The `R`-cocycle torsor has the block frame's prescribed cardinality. -/
def StageZ (α h q : ℕ) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (f₀ : BoundaryLiftsK b F T),
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀.1.1) =
      (blockFrameImpl T Blk hE₂).zR

/-! ## Assembly -/

/-- **Exact lifting for the improved compact-M presentation, at every handle count.**

The only hypotheses not supplied by arithmetic side conditions or landed generic machinery are
the per-simple M0 Stokes input and the two low-level `R`-stage residues above. -/
theorem exactLifting {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q) (hsep : StageSep α h q) (hZ : StageZ α h q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2 hsimp hα hq0 hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2 hsimp hα hq0 hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

/-- Corrected exact lifting for the improved compact-M presentation.  Its existing resolver and
Stokes package proves obstruction-zero separation and the honest degree-indexed R-cocycle count,
so the false legacy `StageZ` and overstrong legacy `StageSep` premises disappear. -/
theorem exactLiftingRN {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q) {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    letI : CommGroup ↑Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↑Blk.frattiniK) :=
      RStageLocal.conjC Blk hRK
    letI := scalarActionZmodTwo (Y ⧸ Blk.K)
    have hb := resolvesAt_and_endpoint_mCompactFam
      (Q := WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K))
      heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
      orderOf_wordLift_dvd_heisExponent (α := α) (h := h) (q := q) hqe
    have hresR : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
        (mCompactFam α h q
          (omega2Exp (Monoid.exponent
            (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
        (WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
    have hres2 : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
        (mCompactFam α h q
          (omega2Exp (Monoid.exponent
            (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
        (WordLift (ZMod 2) (Y ⧸ Blk.K)) :=
      (resolvesAt_and_endpoint_mCompactFam heisLevel_ne_zero_and_even.1
        heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
        (α := α) (h := h) (q := q) hqe).1
    have he : Odd (omega2Exp (Monoid.exponent
        (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))) :=
      odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    have hpres :=
      isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)
    exact blockStageR136NK (standardNumerics (2 * h + 2)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2 hsimp hα hq0 hqe)
      (tfg_of_isAdmissibleMarkedPresentation hpres) b F
      (fun g hg => by
        let qKR : (blockFrameImpl T Blk hE₂).YB →* (Y ⧸ Blk.K) :=
          QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
            (by rw [Subgroup.comap_id]; exact SectionSeven.frattiniLike_le Blk.K)
        let rho : ContinuousMonoidHom ((gamma α h q : Type)) (Y ⧸ Blk.K) :=
          ⟨qKR.comp g.1.1.toMonoidHom,
            (continuous_of_discreteTopology (f := qKR)).comp g.1.1.continuous_toFun⟩
        have hrho_apply (gamma : (gamma α h q : Type)) :
            rho gamma = qKR (g.1.1 gamma) := rfl
        have hd : StokesDuality
            (fun i => qKR (g.1.1 (gammaGen (2 + 2 * h) q (mCompactW α h) i)))
            (mCompactFam α h q
              (omega2Exp (Monoid.exponent
                (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [hrho_apply] using
            (stokesDuality hsimp hqe rho he hres2 (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂
          (scalarActionZmodTwo_triv _) (cardH2 hsimp hα hq0 hqe) b F g hpres
          (isWildTwo_of_gammaGen g.1.1 g.1.2 (fun _ => rfl)) hres2 hresR hd hb.2 hg)
      (fun f₀ => by
        let theta : ContinuousMonoidHom ((gamma α h q : Type)) (Y ⧸ Blk.K) :=
          ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
            show Continuous fun gamma => QuotientGroup.mk' Blk.K (f₀.1.1 gamma)
            exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩
        have htheta_surj : Function.Surjective theta := by
          intro c
          obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
          obtain ⟨gamma, hgamma⟩ := f₀.1.2 y
          exact ⟨gamma, by
            change QuotientGroup.mk' Blk.K (f₀.1.1 gamma) = c
            rw [hgamma, hy]⟩
        have htheta_apply (gamma : (gamma α h q : Type)) :
            theta gamma = QuotientGroup.mk' Blk.K (f₀.1.1 gamma) := rfl
        have hd : StokesDuality
            (fun i => QuotientGroup.mk' Blk.K
              (f₀.1.1 (gammaGen (2 + 2 * h) q (mCompactW α h) i)))
            (mCompactFam α h q
              (omega2Exp (Monoid.exponent
                (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [htheta_apply] using
            (stokesDuality hsimp hqe theta he hres2 (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀.1.1 f₀.1.2 hpres
          hresR (isWildTwo_of_gammaGen theta htheta_surj (fun _ => rfl))
          (degree h) hd hb.2)

/-- Constructor-table regression: compact `M` uses the improved `mCompactW`. -/
theorem gamma_eq_improved (α h q : ℕ) :
    gamma α h q = GammaR (2 + 2 * h) q (mCompactW α h) := rfl

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Transport only the numerical degree of exact-lifting semantics, keeping its carrier fixed. -/
theorem exactLifting_standard_congr {Gam : ProfiniteGrp} {n m q : ℕ}
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} (hn : n = m) :
    ExactLiftingSemantics Gam n q P nuP (standardNumerics n) →
      ExactLiftingSemantics Gam m q P nuP (standardNumerics m) := by
  subst m
  exact id

/-- Transport only the numerical degree of corrected RN semantics. -/
theorem exactLiftingRN_standard_congr {Gam : ProfiniteGrp} {n m q : ℕ}
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} (hn : n = m) :
    ExactLiftingSemanticsRN Gam n q P nuP (standardNumerics n) →
      ExactLiftingSemanticsRN Gam m q P nuP (standardNumerics m) := by
  subst m
  exact id

/-- A selected compact-`M` row receives corrected degree-indexed exact lifting with no
`StageSep` or `StageZ` premise, and its semantic word remains the improved `mCompactW`. -/
theorem exactLiftingRN_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {α q : ℕ} (hbranch : S.branch = .M0 α)
    (hsimp : Hsimp α (handleCount FP (.M0 α)) q)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN
      (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
      (standardNumerics S.semantic.degree) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      change ExactLiftingSemanticsRN
        (GammaR (2 + 2 * handleCount FP (.M0 α)) q
        (mCompactW α (handleCount FP (.M0 α))))
        (2 + 2 * handleCount FP (.M0 α)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.M0 α)))
      have hα : 1 ≤ α := le_trans (by omega) valid
      have hn : 2 * handleCount FP (.M0 α) + 2 =
          2 + 2 * handleCount FP (.M0 α) := by omega
      exact exactLiftingRN_standard_congr hn
        (exactLiftingRN hsimp hα hq0 hqe nuP)

/-- On a field selection whose chosen row is compact `M`, certify the selector's semantic
presentation without changing back to the superseded draft word.  Branch validity supplies
the `1 ≤ α` needed only by the compact-M core map. -/
theorem exactLifting_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {α q : ℕ} (hbranch : S.branch = .M0 α)
    (hsimp : Hsimp α (handleCount FP (.M0 α)) q)
    (hq0 : q ≠ 0) (hqe : Even q)
    (hsep : StageSep α (handleCount FP (.M0 α)) q)
    (hZ : StageZ α (handleCount FP (.M0 α)) q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics
      (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
      (standardNumerics S.semantic.degree) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      change ExactLiftingSemantics
        (GammaR (2 + 2 * handleCount FP (.M0 α)) q
        (mCompactW α (handleCount FP (.M0 α))))
        (2 + 2 * handleCount FP (.M0 α)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.M0 α)))
      have hα : 1 ≤ α := le_trans (by omega) valid
      have hn : 2 * handleCount FP (.M0 α) + 2 =
          2 + 2 * handleCount FP (.M0 α) := by omega
      exact exactLifting_standard_congr hn
        (exactLifting hsimp hα hq0 hqe hsep hZ nuP)

end GQ2.Dyadic.MCompact
