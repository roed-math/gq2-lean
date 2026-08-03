/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Count.Lifts
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.Count.Variation
import GQ2.Dyadic.FieldBranchSelector

/-!
# Exact lifting for the compact-N presentation

This file constructs `ExactLiftingSemantics` for the improved compact-`N` word
`Words.nCompactW α h`, uniformly in the handle count.  The three conjuncts are supplied as
follows.

| conjunct | construction | residual |
|---|---|---|
| `liftsOver_card` | `Count.nCompact_liftsOver_card` | per-simple N0 Stokes duality |
| `lem86` | `Count.lem86_of_variation` | the same Stokes input |
| `stageR136` | `blockStageR136K` + the uniform variation witness | hom-lift separation and `R`-cocycle count |

The variation witness is not frozen at the quadratic pilot.  A uniform map
`D_N(α,h) → 𝔽₂²/⟨s̄⟩`, and hence a surjection from the compact-`N` candidate, is
built below for every `α,h`.  Thus the half-torsor count and the `#H² = 2` input of the
`R`-stage require no separate branch hypothesis.
-/

namespace GQ2.Dyadic.NCompact

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA DihedralGroup

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The intrinsic compact-N source and its word-level residue -/

/-- The compact-`N` candidate at arbitrary handle count. -/
noncomputable abbrev gamma (α h q : ℕ) : ProfiniteGrp :=
  GammaR (2 + 2 * h) q (nCompactW α h)

/-- The sole word-level analytic residue for compact `N`: perfect Stokes duality on every
simple elementary module at every honest odd resolver.

The landed N0 certificate upgrades this input to arbitrary finite elementary modules.  It is
strictly smaller than any count or lifting conclusion and is shared by all three exact-lifting
conjuncts. -/
def Hsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (t : Marking (2 + 2 * h) C) (e : ℕ), Odd e →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1 →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW α h) = 1 →
    ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (nCompactFam α h q e) V

/-- The N0 certificate upgrades `Hsimp` to Stokes duality on every finite elementary module
at a marking pushed forward from the candidate group. -/
theorem stokesDuality {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) {e : ℕ} (he : Odd e)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q e) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
      (nCompactFam α h q e) A := by
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift (⇑t) (nCompactFam α h q e k) = 1 := fun k =>
    lower_rel (A := ZMod 2) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hres k
  have hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 + 2 * h) q) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 0)
  have hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (nCompactW α h) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 1)
  exact nCompact_stokesDuality t hα hqe he hrt hrw
    (hsimp C t e he hrt hrw) A hA₂

/-- The variation lane's primary-module Stokes payload, at its intrinsic Heisenberg level. -/
theorem stokesDuality_T {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) (Bg ⧸ D.M)) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
      (nCompactFam α h q (omega2Exp (heisLevel D))) (Additive ↥D.T) := by
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_nCompactFam
      (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_scal hα hqe).1
  exact stokesDuality hsimp hα hqe rho
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

/-- The uniform core map, sending the compact-`N` `σ`-slot to the nontrivial class and all
other core and handle slots to one. -/
noncomputable def datumCoreHom (α h : ℕ) :
    ContinuousMonoidHom ((DN α h) : Type) (Base ⧸ datum.M) :=
  nLiftHom α h isProP_datumQuot (coreMark 1 1 (QuotientGroup.mk (r 1)) 1) (by
    rw [nRelWord_coreMark]
    simp [nWord, commP])

@[simp] theorem datumCoreHom_gen (α h : ℕ) (i : Fin (coreRank h)) :
    datumCoreHom α h (dnGen α h i) =
      coreMark (h := h) 1 1 (QuotientGroup.mk (r 1)) 1 i :=
  nLiftHom_gen α h _ _ _ i

/-- The induced map from the intrinsic compact-`N` candidate. -/
noncomputable def datumRho (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((gamma α h q : Type)) (Base ⧸ datum.M) :=
  (datumCoreHom α h).comp (CorePresentation.coreHom (nCorePresentation α h) hq0 hqe)

/-- The datum map is onto, uniformly in `α` and in the handle count. -/
theorem datumRho_surjective (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (datumRho α h q hq0 hqe) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hcases : (QuotientGroup.mk b : Base ⧸ datum.M) = 1
      ∨ (QuotientGroup.mk b : Base ⧸ datum.M) = QuotientGroup.mk (r 1) := quotient_cases b
  rcases hcases with h1 | hr
  · exact ⟨1, by rw [map_one, h1]⟩
  · obtain ⟨γ, hγ⟩ := CorePresentation.coreHom_surjective (nCorePresentation α h)
      (hq0 := hq0) (hqe := hqe) (dnSigma α h)
    refine ⟨γ, ?_⟩
    show datumCoreHom α h (CorePresentation.coreHom (nCorePresentation α h) hq0 hqe γ) = _
    rw [hγ, hr, show dnSigma α h = dnGen α h 2 from rfl, datumCoreHom_gen,
      coreMark_two]

/-- The scalar `H²` count required by the `R`-stage, derived from the uniform datum map and
the same N0 Stokes residue used by the lift count. -/
theorem cardH2 {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho α h q hq0 hqe with hrho
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
  have hb := resolvesAt_and_endpoint_nCompactFam
    (Q := WordLift (ZMod 2) (Base ⧸ datum.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := α) (h := h) (q := q) hα hqe
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel datum)))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel datum)))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := α) (h := h) (q := q) hα hqe).1
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel datum)))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := α) (h := h) (q := q) hα hqe).1
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel datum)))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := α) (h := h) (q := q) hα hqe).1
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective α h q hq0 hqe) (fun _ => rfl))
    hresS hresP hresD hresH (stokesDuality_T hsimp hα hqe rho)
    (stokesDuality hsimp hα hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective α h q hq0 hqe)

/-! ## The first two exact-lifting clauses -/

/-- The `liftsOver_card` clause at every recursion frame.  Resolver, endpoint, admissibility,
wildness, and the elementary-module upgrade are all discharged uniformly. -/
theorem liftsOver_card {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
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
  have hb := resolvesAt_and_endpoint_nCompactFam
    (Q := WordLift (Additive ↥RF.MB) RF.YC)
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (α := α) (h := h) (q := q) hα hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q
        (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
      (WordLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q
        (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
      (WordLift (ZMod 2) RF.YC) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (α := α) (h := h) (q := q) hα hqe).1
  exact nCompact_liftsOver_card (hN := h) RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl)) hres
    (stokesDuality hsimp hα hqe rho.1.1
      (odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2)
      hresS (Additive ↥RF.MB) (mb_add_self RF)) hb.2

/-- The universal half-torsor clause.  `NoDescent` and surjectivity create the nonzero
variation class through the landed N0 resolvers; no half-torsor count is assumed. -/
theorem lem86 {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
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
  have hb := resolvesAt_and_endpoint_nCompactFam
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := α) (h := h) (q := q) hα hqe
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := α) (h := h) (q := q) hα hqe).1
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel D)))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := α) (h := h) (q := q) hα hqe).1
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (heisLevel D)))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := α) (h := h) (q := q) hα hqe).1
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (stokesDuality_T hsimp hα hqe rho)
    (stokesDuality hsimp hα hqe rho
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

/-- The `R`-cocycle torsor has the block frame's prescribed cardinality.

This is the second exact input consumed by `blockStageR136K`, separately named so future work
can discharge it without changing the compact-N exact-lifting constructor. -/
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

/-- **Exact lifting for the improved compact-N presentation, at every handle count.**

The only hypotheses not supplied by arithmetic side conditions or landed generic machinery are
the per-simple N0 Stokes input and the two low-level `R`-stage residues above. -/
theorem exactLifting {α h q : ℕ} (hsimp : Hsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q)
    (hsep : StageSep α h q) (hZ : StageZ α h q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2 hsimp hα hq0 hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2 hsimp hα hq0 hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Transport only the numerical degree of exact-lifting semantics, keeping its carrier fixed.
This isolates the harmless normalization `2*h+2 = 2+2*h` used by the semantic selector. -/
theorem exactLifting_standard_congr {Gam : ProfiniteGrp} {n m q : ℕ}
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} (hn : n = m) :
    ExactLiftingSemantics Gam n q P nuP (standardNumerics n) →
      ExactLiftingSemantics Gam m q P nuP (standardNumerics m) := by
  subst m
  exact id

/-- On a field selection whose chosen row is compact `N`, the semantic presentation receives
the handle-uniform exact-lifting certificate without changing back to the superseded draft word.
-/
theorem exactLifting_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {α q : ℕ} (hbranch : S.branch = .N0 α)
    (hsimp : Hsimp α (handleCount FP (.N0 α)) q) (hα : 1 ≤ α)
    (hq0 : q ≠ 0) (hqe : Even q)
    (hsep : StageSep α (handleCount FP (.N0 α)) q)
    (hZ : StageZ α (handleCount FP (.N0 α)) q)
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
        (GammaR (2 + 2 * handleCount FP (.N0 α)) q
        (nCompactW α (handleCount FP (.N0 α))))
        (2 + 2 * handleCount FP (.N0 α)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.N0 α)))
      have hn : 2 * handleCount FP (.N0 α) + 2 =
          2 + 2 * handleCount FP (.N0 α) := by omega
      exact exactLifting_standard_congr hn (exactLifting hsimp hα hq0 hqe hsep hZ nuP)

end GQ2.Dyadic.NCompact
