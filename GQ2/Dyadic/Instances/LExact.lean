/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.N0Exact

/-!
# Exact lifting for the improved odd/L presentation

This file constructs `ExactLiftingSemantics` for the improved odd-degree word
`Words.LSq.lSqW h`.  This is a theorem about the presentation selected by the constructor table;
it is separate from the still-residual arithmetic theorem classifying an arbitrary field into the
`L` family.

The existing `lSqFam` resolver, endpoint, Stokes devissage, variation, and generic lift-count
machinery derive the lift count, half-torsor identity, and scalar `#H² = 2`.  The frozen
`ExactLiftingSemantics` constructor retains its two historical `R`-stage inputs; the corrected
`ExactLiftingSemanticsRN` constructor below derives both of them from the resolver and Stokes
data, so only per-simple Stokes duality remains explicit there.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA DihedralGroup

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## Presentation, resolver, and Stokes residue -/

/-- The improved odd-degree candidate at handle count `h`, of degree `2h+1`. -/
noncomputable abbrev gamma (h q : ℕ) : ProfiniteGrp :=
  GammaR (2 * h + 1) q (lSqW h)

/-- The only word-level analytic residue: perfect Stokes duality on each simple elementary
module at every honest odd resolver, whenever both resolved relators die. -/
def Hsimp (h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (t : Marking (2 * h + 1) C) (e : ℕ), Odd e →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 * h + 1) q) = 1 →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h) = 1 →
    ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (lSqFam h q e) V

/-- Upgrade `Hsimp` to every finite elementary module at a pushed-forward candidate marking. -/
theorem stokesDuality {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C) {e : ℕ} (he : Odd e)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q e) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g => rho (gammaGen (2 * h + 1) q (lSqW h) g))
      (lSqFam h q e) A := by
  set t : Marking (2 * h + 1) C :=
    ⟨fun g => rho (gammaGen (2 * h + 1) q (lSqW h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (lSqFam h q e k) = 1 := fun k =>
    lower_rel (A := ZMod 2) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hres k
  have hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 * h + 1) q) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 0)
  have hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 1)
  exact lSq_stokesDuality t hqe he hrt hrw (hsimp C t e he hrt hrw) A hA₂

/-- The primary-module Stokes payload needed by the variation argument. -/
theorem stokesDuality_T {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M)) :
    StokesDuality (fun g => rho (gammaGen (2 * h + 1) q (lSqW h) g))
      (lSqFam h q (omega2Exp (heisLevel D))) (Additive ↥D.T) := by
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_lSqFam
      (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_scal (h := h) (q := q) hqe).1
  exact stokesDuality hsimp hqe rho
    (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hres
    (Additive ↥D.T) (radT_add_self D)

/-! ## Degree and a uniform nonzero-variation quotient -/

/-- The two-relator odd presentation has deficiency `2h+1`. -/
theorem degree (h : ℕ) :
    Nat.card (Generator (2 * h + 1)) = Nat.card (Fin 2) + ((2 * h + 1) + 1) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Generator.card_generator,
    Fintype.card_fin]
  omega

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-- The standard variation quotient has exponent two. -/
theorem datumQuot_sq (y : Base ⧸ datum.M) : y * y = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, show b * b = 1 from by revert b; decide,
    QuotientGroup.mk_one]

/-- Send `sigma` to the nontrivial quotient class and every other letter to one. -/
noncomputable def datumMarking (h : ℕ) : Marking (2 * h + 1) (Base ⧸ datum.M) :=
  Marking.ofLetters (QuotientGroup.mk (DihedralGroup.r 1)) 1 (fun _ ↦ 1)

theorem datumMarking_relators (h q : ℕ) :
    ∀ k, PWord.eval ⇑(datumMarking h) (gammaFam (2 * h + 1) q (lSqW h) k) = 1 := by
  intro k
  fin_cases k
  · change PWord.eval ⇑(datumMarking h) (tameRelW (2 * h + 1) q) = 1
    simp [datumMarking, tameRelW]
  · change PWord.eval ⇑(datumMarking h) (lSqW h) = 1
    have hH : (datumMarking h).eval (LSq.handlesW h) = 1 := by
      rw [LSq.eval_handlesW]
      exact MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)
    rw [show PWord.eval ⇑(datumMarking h) (lSqW h) =
      (datumMarking h).eval (lSqW h) from rfl, eval_lSqW]
    rw [hH]
    simp [datumMarking, LSq.coreLetter, GQ2.zpowHat_omega2, GQ2.powOmega2]

/-- The all-trivial wild marking is a pro-`2` wild marking. -/
theorem datumMarking_isWildTwo (h : ℕ) :
    IsWildTwo (wildAlphabet (2 * h + 1)) (datumMarking h) := by
  show IsPGroup 2
    (Subgroup.normalClosure ((datumMarking h : Generator (2 * h + 1) → Base ⧸ datum.M) ''
      wildAlphabet (2 * h + 1)))
  have hbot : Subgroup.normalClosure
      ((datumMarking h : Generator (2 * h + 1) → Base ⧸ datum.M) ''
        wildAlphabet (2 * h + 1)) = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨i, hi, rfl⟩
    exact Subgroup.mem_bot.mpr (by rcases hi with ⟨j, rfl⟩; rfl)
  rw [hbot]
  exact IsPGroup.of_bot

/-- The uniform variation quotient map from the improved odd presentation. -/
noncomputable def datumRho (h q : ℕ) :
    ContinuousMonoidHom ((gamma h q : Type)) (Base ⧸ datum.M) :=
  Classical.choose ((isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)).extend
    (datumMarking h) (datumMarking_relators h q) (datumMarking_isWildTwo h))

@[simp] theorem datumRho_gammaGen (h q : ℕ) (i : Generator (2 * h + 1)) :
    datumRho h q (gammaGen (2 * h + 1) q (lSqW h) i) = datumMarking h i :=
  Classical.choose_spec ((isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)).extend
    (datumMarking h) (datumMarking_relators h q) (datumMarking_isWildTwo h)) i

/-- The variation quotient map is onto. -/
theorem datumRho_surjective (h q : ℕ) : Function.Surjective (datumRho h q) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hcases : (QuotientGroup.mk b : Base ⧸ datum.M) = 1 ∨
      (QuotientGroup.mk b : Base ⧸ datum.M) = QuotientGroup.mk (DihedralGroup.r 1) :=
    quotient_cases b
  rcases hcases with h1 | hr
  · exact ⟨1, by simpa using h1.symm⟩
  · refine ⟨gammaGen (2 * h + 1) q (lSqW h) .sigma, ?_⟩
    rw [datumRho_gammaGen]
    simpa [datumMarking] using hr.symm

/-! ## Scalar cohomology and the first two exact-lifting clauses -/

/-- The scalar `H²` count required by the `R`-stage, derived from the uniform variation
quotient and the same L-square Stokes residue used by the lift count. -/
theorem cardH2 {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    Nat.card (H2 ((gamma h q : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((gamma h q : Type))
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho h q with hrho
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (Additive ↥datum.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((gamma h q : Type)) (ElemDual (Additive ↥datum.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : Type)) (ElemDual (Additive ↥datum.T)) := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × ElemDual (Additive ↥datum.T) => p.1 • p.2)
          = (fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)
            ∘ (fun p : ((gamma h q : Type)) × ElemDual (Additive ↥datum.T) =>
                (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_lSqFam
    (Q := WordLift (ZMod 2) (Base ⧸ datum.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (h := h) (q := q) hqe
  have hresS : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel datum)))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel datum)))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (h := h) (q := q) hqe).1
  have hresD : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel datum)))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (h := h) (q := q) hqe).1
  have hresH : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel datum)))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (h := h) (q := q) hqe).1
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective h q) (fun _ => rfl))
    hresS hresP hresD hresH (stokesDuality_T hsimp hqe rho)
    (stokesDuality hsimp hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective h q)

/-- The lift count at every recursion frame. -/
theorem liftsOver_card {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics (2 * h + 1)).mMult (Nat.card ↥RF.MB) := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk RF b F rho
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_lSqFam
    (Q := WordLift (Additive ↥RF.MB) RF.YC)
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q
        (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
      (WordLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hresS : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q
        (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
      (WordLift (ZMod 2) RF.YC) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (h := h) (q := q) hqe).1
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl))
    (degree h) hres
    (stokesDuality hsimp hqe rho.1.1
      (odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2)
      hresS (Additive ↥RF.MB) (mb_add_self RF)) hb.2

/-- The universal half-torsor identity, derived from nonzero variation. -/
theorem lem86 {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  letI := scalarActionZmodTwo ((gamma h q : Type))
  letI := scalarActionZmodTwo (Bg ⧸ D.M)
  letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((gamma h q : Type)) (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : Type)) (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × ElemDual (Additive ↥D.T) => p.1 • p.2)
          = (fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)
            ∘ (fun p : ((gamma h q : Type)) × ElemDual (Additive ↥D.T) =>
                (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_lSqFam
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (h := h) (q := q) hqe
  have hresS : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel D)))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (h := h) (q := q) hqe).1
  have hresD : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel D)))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (h := h) (q := q) hqe).1
  have hresH : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (heisLevel D)))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (h := h) (q := q) hqe).1
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (stokesDuality_T hsimp hqe rho)
    (stokesDuality hsimp hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-! ## The two irreducible R-stage residues -/

/-- Obstruction-zero lower lifts come from homomorphisms into the original marked target. -/
def StageSep (h q : ℕ) : Prop :=
  letI := scalarActionZmodTwo ((gamma h q : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : ((gamma h q : Type))) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((gamma h q : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB),
    obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
        htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom ((gamma h q : Type)) Y,
        ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ

/-- The `R`-cocycle torsor has the block frame's prescribed cardinality. -/
def StageZ (h q : ℕ) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (f₀ : BoundaryLiftsK b F T),
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀.1.1) =
      (blockFrameImpl T Blk hE₂).zR

/-! ## Assembly and constructor-table regression -/

/-- Exact lifting for the improved odd/L presentation at every handle count. -/
theorem exactLifting {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q)
    (hsep : StageSep h q) (hZ : StageZ h q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) := by
  refine ⟨liftsOver_card hsimp hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2 hsimp hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2 hsimp hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

/-- Corrected exact lifting for the improved odd/L presentation.  Resolver and Stokes data
discharge both former `R`-stage residues, with the degree-indexed `zRN` coefficient. -/
theorem exactLiftingRN {h q : ℕ} (hsimp : Hsimp h q) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) := by
  refine ⟨liftsOver_card hsimp hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    letI : CommGroup ↑Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↑Blk.frattiniK) :=
      RStageLocal.conjC Blk hRK
    letI := scalarActionZmodTwo (Y ⧸ Blk.K)
    have hb := resolvesAt_and_endpoint_lSqFam
      (Q := WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K))
      heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
      orderOf_wordLift_dvd_heisExponent (h := h) (q := q) hqe
    have hresR : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
        (lSqFam h q
          (omega2Exp (Monoid.exponent
            (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
        (WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
    have hres2 : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
        (lSqFam h q
          (omega2Exp (Monoid.exponent
            (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
        (WordLift (ZMod 2) (Y ⧸ Blk.K)) :=
      (resolvesAt_and_endpoint_lSqFam heisLevel_ne_zero_and_even.1
        heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
        (h := h) (q := q) hqe).1
    have he : Odd (omega2Exp (Monoid.exponent
        (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))) :=
      odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    have hpres := isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)
    exact blockStageR136NK (standardNumerics (2 * h + 1)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2 hsimp hqe)
      (tfg_of_isAdmissibleMarkedPresentation hpres) b F
      (fun g hg => by
        let qKR : (blockFrameImpl T Blk hE₂).YB →* (Y ⧸ Blk.K) :=
          QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
            (by rw [Subgroup.comap_id]; exact SectionSeven.frattiniLike_le Blk.K)
        let rho : ContinuousMonoidHom ((gamma h q : Type)) (Y ⧸ Blk.K) :=
          ⟨qKR.comp g.1.1.toMonoidHom,
            (continuous_of_discreteTopology (f := qKR)).comp g.1.1.continuous_toFun⟩
        have hrho_apply (gamma : (gamma h q : Type)) :
            rho gamma = qKR (g.1.1 gamma) := rfl
        have hd : StokesDuality
            (fun i => qKR (g.1.1 (gammaGen (2 * h + 1) q (lSqW h) i)))
            (lSqFam h q
              (omega2Exp (Monoid.exponent
                (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [hrho_apply] using
            (stokesDuality hsimp hqe rho he hres2 (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂
          (scalarActionZmodTwo_triv _) (cardH2 hsimp hqe) b F g hpres
          (isWildTwo_of_gammaGen g.1.1 g.1.2 (fun _ => rfl)) hres2 hresR hd hb.2 hg)
      (fun f₀ => by
        let theta : ContinuousMonoidHom ((gamma h q : Type)) (Y ⧸ Blk.K) :=
          ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
            show Continuous fun gamma => QuotientGroup.mk' Blk.K (f₀.1.1 gamma)
            exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩
        have htheta_apply (gamma : (gamma h q : Type)) :
            theta gamma = QuotientGroup.mk' Blk.K (f₀.1.1 gamma) := rfl
        have htheta_surj : Function.Surjective theta := by
          intro c
          obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
          obtain ⟨gamma, hgamma⟩ := f₀.1.2 y
          exact ⟨gamma, by rw [htheta_apply, hgamma, hy]⟩
        have hd : StokesDuality
            (fun i => QuotientGroup.mk' Blk.K
              (f₀.1.1 (gammaGen (2 * h + 1) q (lSqW h) i)))
            (lSqFam h q
              (omega2Exp (Monoid.exponent
                (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [htheta_apply] using
            (stokesDuality hsimp hqe theta he hres2 (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀.1.1 f₀.1.2 hpres
          hresR (isWildTwo_of_gammaGen theta htheta_surj (fun _ => rfl))
          (degree h) hd hb.2)

/-- Regression theorem for the constructor table: the L-square exact-lifting carrier is
definitionally the `GammaR` presentation on the improved `lSqW`, not the initial draft word. -/
theorem gamma_eq_improved (h q : ℕ) : gamma h q = GammaR (2 * h + 1) q (lSqW h) := rfl

/-- At handle count zero, corrected degree-one semantics agrees with the frozen API.  This
regresses the new constructor against the historical theorem at the unique degree where their
R-stage coefficients coincide definitionally. -/
theorem exactLiftingRN_zero_regression {q : ℕ} (hsimp : Hsimp 0 q) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma 0 q) 1 q P nuP (standardNumerics 1) := by
  rw [← exactLiftingSemanticsRN_standard_one_iff]
  simpa using exactLiftingRN hsimp hqe nuP

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- A selected `.L` row literally uses the improved `lSqW` presentation.  This is presentation
regression only; the caller's `FieldBranchWitness.L` remains the separate classification input. -/
theorem gamma_eq_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hbranch : S.branch = .L) :
    GammaR S.semantic.degree q S.semantic.word = gamma (handleCount FP .L) q := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

/-- The selected `.L` presentation receives the presentation-level exact-lifting certificate.
This theorem does not assert that an arbitrary field belongs to the L family. -/
theorem exactLifting_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hbranch : S.branch = .L)
    (hsimp : Hsimp (handleCount FP .L) q) (hqe : Even q)
    (hsep : StageSep (handleCount FP .L) q) (hZ : StageZ (handleCount FP .L) q)
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
        (GammaR (2 * handleCount FP .L + 1) q (lSqW (handleCount FP .L)))
        (2 * handleCount FP .L + 1) q P nuP
        (standardNumerics (2 * handleCount FP .L + 1))
      exact exactLifting hsimp hqe hsep hZ nuP

/-- The selected improved L presentation receives corrected exact-lifting semantics directly;
the former `StageSep` and `StageZ` arguments are no longer present. -/
theorem exactLiftingRN_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {q : ℕ} (hbranch : S.branch = .L)
    (hsimp : Hsimp (handleCount FP .L) q) (hqe : Even q)
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
        (GammaR (2 * handleCount FP .L + 1) q (lSqW (handleCount FP .L)))
        (2 * handleCount FP .L + 1) q P nuP
        (standardNumerics (2 * handleCount FP .L + 1))
      exact exactLiftingRN hsimp hqe nuP

end

end GQ2.Dyadic.LSquare
