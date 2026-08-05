/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.N0Exact
import GQ2.Dyadic.Instances.M0Exact
import GQ2.Dyadic.Instances.N0M0UniformHeisenbergResolver

/-!
# The pushed and uniform word residues of the two compact even rows

`NCompact.Hsimp` and `MCompact.Hsimp` quantify over *all* finite markings whose two resolved
relators die, including non-wild markings which need not extend across `GammaR`.  As
`LExact.lean` records for the odd row, the continuous-cohomology comparison available for a
candidate cannot prove a residue in that shape.

This file installs the odd row's three-step weakening on both compact even rows:

* `PushedHsimp` ranges only over markings pushed forward from the candidate group and asks for
  bijectivity of the three induced word-cohomology maps;
* `ResolvedPushedHsimp` supplies the resolver at the two exact split targets whose continuous
  cohomology is to be compared, and concludes the same three bijections for a general
  elementary coefficient;
* `UniformPushedHsimp` fixes one displayed word per finite target, at the uniform level
  `4 * Monoid.exponent C`, so that a coefficient devissage may keep the word fixed.

Every count and lifting consumer of `Hsimp` is then re-derived from `UniformPushedHsimp`, with
the historical interfaces kept as compatibility wrappers.  Nothing here proves any of the three;
the action-image devissage files do that.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA DihedralGroup

namespace NCompact

noncomputable section

open GQ2.Dyadic.Words.MCompact

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-! ## The three weakened residues -/

/-- The source-facing compact-`N` residue.  It ranges only over markings pushed forward from the
candidate group, and asks for bijectivity of the three induced word-cohomology maps rather than
for the six clauses of `StokesDuality`. -/
def PushedHsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) (e : ℕ), Odd e →
    ∀ (hr : ∀ k, FreeGroup.lift
        (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
        (nCompactFam α h q e k) = 1)
      (hend : IsStokesEndpoint (nCompactFam α h q e))
      (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesCohomologyBijections
          (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
          (nCompactFam α h q e) V hr hend

/-- The target-local compact-`N` residue.  The resolver is supplied at the exact split targets
`WordLift A C` and `WordLift (ElemDual A) C` whose continuous cohomology is to be compared, and
the conclusion is already the three cohomology bijections for that same elementary module `A`.
Relator death is not an extra premise: `lower_rel` derives it from the candidate presentation and
the target-local resolver. -/
def ResolvedPushedHsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) (e : ℕ), Odd e →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
      [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
      [TopologicalSpace (WordLift (ElemDual A) C)]
      [DiscreteTopology (WordLift (ElemDual A) C)],
      (∀ a : A, a + a = 0) →
      ∀ (hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
          (nCompactFam α h q e) (WordLift A C))
        (_hresDual : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
          (nCompactFam α h q e) (WordLift (ElemDual A) C))
        (hend : IsStokesEndpoint (nCompactFam α h q e)),
        StokesCohomologyBijections
          (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
          (nCompactFam α h q e) A
          (fun k => lower_rel rho (fun _ => rfl)
            (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hres k)
          hend

/-- The coefficient-independent compact-`N` residue.  For a fixed finite target `C`, every
elementary coefficient module is tested against the same displayed word, at level
`4 * Monoid.exponent C`. -/
def UniformPushedHsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        StokesDuality
          (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
          (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) A

/-! ## The weakening chain -/

/-- The historical all-markings residue implies the pushed cohomological one.  The converse is
intentionally absent: relator-killing markings need not be wild, hence need not be pushed from
`GammaR`. -/
theorem pushedHsimp_of_hsimp {α h q : ℕ} (hsimp : Hsimp α h q) : PushedHsimp α h q := by
  intro C _ _ _ _ rho e he hr hend V _ _ _ hV₂ hsimple
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g)⟩ with ht
  have hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 + 2 * h) q) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 0)
  have hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (nCompactW α h) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 1)
  exact (stokesDuality_iff_cohomologyBijections ⇑t (nCompactFam α h q e) V hr hend).mp
    (hsimp C t e he hrt hrw V hV₂ hsimple)

/-- The pushed residue implies the target-local general-coefficient residue.  The only work is
the already-proved simple-module devissage; no new resolver is chosen. -/
theorem resolvedPushedHsimp_of_pushedHsimp {α h q : ℕ}
    (hsimp : PushedHsimp α h q) : ResolvedPushedHsimp α h q := by
  intro C _ _ _ _ rho e he A _ _ _ _ _ _ _ hA₂ hres _hresDual hend
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (nCompactFam α h q e k) = 1 := fun k =>
    lower_rel (A := A) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hres k
  have hd : StokesDuality ⇑t (nCompactFam α h q e) A :=
    stokesDuality_of_simple ⇑t (nCompactFam α h q e) hr hend
      (fun V _ _ _ hV₂ hsimple =>
        (stokesDuality_iff_cohomologyBijections ⇑t (nCompactFam α h q e) V hr hend).mpr
          (hsimp C rho e he hr hend V hV₂ hsimple)) A hA₂
  exact (stokesDuality_iff_cohomologyBijections ⇑t (nCompactFam α h q e) A hr hend).mp hd

/-- The historical all-markings residue also reaches the target-local residue. -/
theorem resolvedPushedHsimp_of_hsimp {α h q : ℕ}
    (hsimp : Hsimp α h q) : ResolvedPushedHsimp α h q :=
  resolvedPushedHsimp_of_pushedHsimp (pushedHsimp_of_hsimp hsimp)

/-- Upgrade the target-local residue to Stokes duality on exactly the supplied elementary
module.  The same primal and dual resolvers occur in the residue, so there is no
resolver-changing step. -/
theorem stokesDuality_of_resolvedPushed {α h q : ℕ} (hsimp : ResolvedPushedHsimp α h q)
    (hα : 1 ≤ α) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) {e : ℕ} (he : Odd e)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
    [TopologicalSpace (WordLift (ElemDual A) C)]
    [DiscreteTopology (WordLift (ElemDual A) C)]
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q e) (WordLift A C))
    (hresDual : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q e) (WordLift (ElemDual A) C)) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g))
      (nCompactFam α h q e) A := by
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (nCompactW α h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (nCompactFam α h q e k) = 1 := fun k =>
    lower_rel (A := A) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hres k
  have hend : IsStokesEndpoint (nCompactFam α h q e) :=
    nCompact_isStokesEndpoint hα hqe he
  exact (stokesDuality_iff_cohomologyBijections ⇑t (nCompactFam α h q e) A hr hend).mpr
    (hsimp C rho e he A hA₂ hres hresDual hend)

/-- Every target-local residue supplies the coefficient-independent uniform-word residue: the
common Heisenberg resolver is pulled back to the primal and dual split targets. -/
theorem uniformPushedHsimp_of_resolvedPushed {α h q : ℕ}
    (hsimp : ResolvedPushedHsimp α h q) (hα : 1 ≤ α) (hqe : Even q) :
    UniformPushedHsimp α h q := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace (WordLift A C) := ⊥
  letI : DiscreteTopology (WordLift A C) := ⟨rfl⟩
  letI : TopologicalSpace (WordLift (ElemDual A) C) := ⊥
  letI : DiscreteTopology (WordLift (ElemDual A) C) := ⟨rfl⟩
  have hb := resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := C) (A := A) hA₂ (α := α) (h := h) (q := q) hα hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) (WordLift A C) := by
    let incl : ContinuousMonoidHom (WordLift A C) (HeisLift A C) :=
      ⟨Count.heisPrim (A := A) (C := C), continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hresDual : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
      (WordLift (ElemDual A) C) := by
    let incl : ContinuousMonoidHom (WordLift (ElemDual A) C) (HeisLift A C) :=
      ⟨Count.heisDual (A := A) (C := C), continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisDual_injective
  exact stokesDuality_of_resolvedPushed hsimp hα hqe rho
    (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
      (fourMulExponent_ne_zero_and_even C).2)
    A hA₂ hres hresDual

/-! ## The count and lifting consumers, re-derived from the uniform residue -/

/-- The scalar `H²` count required by the `R`-stage, from the uniform datum map and the uniform
compact-`N` Stokes residue. -/
theorem cardH2_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
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
  have hb := resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := Base ⧸ datum.M) (A := Additive ↥datum.T) (radT_add_self datum)
    (α := α) (h := h) (q := q) hα hqe
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥datum.T) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisDual_injective
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective α h q hq0 hqe) (fun _ => rfl))
    hresS hresP hresD hresH
    (hsimp (Base ⧸ datum.M) rho (Additive ↥datum.T) (radT_add_self datum))
    (hsimp (Base ⧸ datum.M) rho (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective α h q hq0 hqe)

/-- The lift count at every recursion frame, from the uniform residue. -/
theorem liftsOver_card_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hqe : Even q)
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
  have hb := resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := RF.YC) (A := Additive ↥RF.MB) (mb_add_self RF)
    (α := α) (h := h) (q := q) hα hqe
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (HeisLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (WordLift (Additive ↥RF.MB) RF.YC) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥RF.MB) RF.YC)
        (HeisLift (Additive ↥RF.MB) RF.YC) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisPrim_injective
  exact nCompact_liftsOver_card (hN := h) RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl)) hres
    (hsimp RF.YC rho.1.1 (Additive ↥RF.MB) (mb_add_self RF)) hb.2

/-- The universal half-torsor identity, from the uniform residue. -/
theorem lem86_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hqe : Even q)
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
  have hb := resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := Bg ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D)
    (α := α) (h := h) (q := q) hα hqe
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (Bg ⧸ D.M)) (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisDual_injective
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (hsimp (Bg ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    (hsimp (Bg ⧸ D.M) rho (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-! ## Assembly -/

/-- Exact lifting for the compact-`N` presentation from the uniform residue. -/
theorem exactLifting_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (hsep : StageSep α h q) (hZ : StageZ α h q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card_of_uniformPushed hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86_of_uniformPushed hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2_of_uniformPushed hsimp hα hq0 hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2_of_uniformPushed hsimp hα hq0 hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

set_option maxHeartbeats 800000 in
/-- Corrected exact lifting for the compact-`N` presentation from the uniform residue.  The
resolver and Stokes data discharge both former `R`-stage residues. -/
theorem exactLiftingRN_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card_of_uniformPushed hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86_of_uniformPushed hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    letI : CommGroup ↑Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↑Blk.frattiniK) :=
      RStageLocal.conjC Blk hRK
    letI := scalarActionZmodTwo (Y ⧸ Blk.K)
    have hb := resolvesAt_and_endpoint_nCompactFam_uniformHeis
      (C := Y ⧸ Blk.K) (A := Additive ↑Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂) (α := α) (h := h) (q := q) hα hqe
    have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
        (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
        (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
    have hresR : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
        (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
        (WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) := by
      let incl : ContinuousMonoidHom
          (WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K))
          (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) :=
        ⟨Count.heisPrim, continuous_of_discreteTopology⟩
      exact hresH.pullback incl Count.heisPrim_injective
    have hres2 : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
        (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
        (WordLift (ZMod 2) (Y ⧸ Blk.K)) := by
      let incl : ContinuousMonoidHom
          (WordLift (ZMod 2) (Y ⧸ Blk.K))
          (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) :=
        ⟨Count.heisScal, continuous_of_discreteTopology⟩
      exact hresH.pullback incl Count.heisScal_injective
    have hpres := isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)
    exact blockStageR136NK (standardNumerics (2 * h + 2)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hq0 hqe)
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
            (fun i => qKR (g.1.1 (gammaGen (2 + 2 * h) q (nCompactW α h) i)))
            (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [hrho_apply] using
            (hsimp (Y ⧸ Blk.K) rho (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂
          (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hq0 hqe) b F g hpres
          (isWildTwo_of_gammaGen g.1.1 g.1.2 (fun _ => rfl)) hres2 hresR hd hb.2 hg)
      (fun f₀ => by
        let theta : ContinuousMonoidHom ((gamma α h q : Type)) (Y ⧸ Blk.K) :=
          ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
            show Continuous fun gamma => QuotientGroup.mk' Blk.K (f₀.1.1 gamma)
            exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩
        have htheta_apply (gamma : (gamma α h q : Type)) :
            theta gamma = QuotientGroup.mk' Blk.K (f₀.1.1 gamma) := rfl
        have htheta_surj : Function.Surjective theta := by
          intro c
          obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
          obtain ⟨gamma, hgamma⟩ := f₀.1.2 y
          exact ⟨gamma, by rw [htheta_apply, hgamma, hy]⟩
        have hd : StokesDuality
            (fun i => QuotientGroup.mk' Blk.K
              (f₀.1.1 (gammaGen (2 + 2 * h) q (nCompactW α h) i)))
            (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [htheta_apply] using
            (hsimp (Y ⧸ Blk.K) theta (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀.1.1 f₀.1.2 hpres
          hresR (isWildTwo_of_gammaGen theta htheta_surj (fun _ => rfl))
          (degree h) hd hb.2)

/-! ## Compatibility wrappers -/

/-- The target-local residue specializes to the uniform word. -/
theorem cardH2_of_resolvedPushed {α h q : ℕ} (hsimp : ResolvedPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2 :=
  cardH2_of_uniformPushed (uniformPushedHsimp_of_resolvedPushed hsimp hα hqe) hα hq0 hqe

/-- The pushed residue reaches the scalar count through devissage. -/
theorem cardH2_of_pushed {α h q : ℕ} (hsimp : PushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2 :=
  cardH2_of_resolvedPushed (resolvedPushedHsimp_of_pushedHsimp hsimp) hα hq0 hqe

/-- Corrected exact lifting from the target-local residue. -/
theorem exactLiftingRN_of_resolvedPushed {α h q : ℕ} (hsimp : ResolvedPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_uniformPushed (uniformPushedHsimp_of_resolvedPushed hsimp hα hqe)
    hα hq0 hqe nuP

/-- Corrected exact lifting from the pushed residue. -/
theorem exactLiftingRN_of_pushed {α h q : ℕ} (hsimp : PushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_resolvedPushed (resolvedPushedHsimp_of_pushedHsimp hsimp)
    hα hq0 hqe nuP

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The selected compact-`N` presentation receives corrected exact-lifting semantics from the
uniform residue. -/
theorem exactLiftingRN_of_fieldSelection_uniformPushed
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {α q : ℕ} (hbranch : S.branch = .N0 α)
    (hsimp : UniformPushedHsimp α (handleCount FP (.N0 α)) q) (hα : 1 ≤ α)
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
        (GammaR (2 + 2 * handleCount FP (.N0 α)) q
        (nCompactW α (handleCount FP (.N0 α))))
        (2 + 2 * handleCount FP (.N0 α)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.N0 α)))
      have hn : 2 * handleCount FP (.N0 α) + 2 =
          2 + 2 * handleCount FP (.N0 α) := by omega
      exact exactLiftingRN_standard_congr hn
        (exactLiftingRN_of_uniformPushed hsimp hα hq0 hqe nuP)

end

end NCompact

namespace MCompact

noncomputable section

open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Instances.MCompactCore

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-! ## The three weakened residues -/

/-- The source-facing compact-`M` residue.  It ranges only over markings pushed forward from the
candidate group, and asks for bijectivity of the three induced word-cohomology maps rather than
for the six clauses of `StokesDuality`. -/
def PushedHsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) (e : ℕ), Odd e →
    ∀ (hr : ∀ k, FreeGroup.lift
        (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
        (mCompactFam α h q e k) = 1)
      (hend : IsStokesEndpoint (mCompactFam α h q e))
      (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesCohomologyBijections
          (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
          (mCompactFam α h q e) V hr hend

/-- The target-local compact-`M` residue.  The resolver is supplied at the exact split targets
`WordLift A C` and `WordLift (ElemDual A) C` whose continuous cohomology is to be compared, and
the conclusion is already the three cohomology bijections for that same elementary module `A`. -/
def ResolvedPushedHsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) (e : ℕ), Odd e →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
      [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
      [TopologicalSpace (WordLift (ElemDual A) C)]
      [DiscreteTopology (WordLift (ElemDual A) C)],
      (∀ a : A, a + a = 0) →
      ∀ (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
          (mCompactFam α h q e) (WordLift A C))
        (_hresDual : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
          (mCompactFam α h q e) (WordLift (ElemDual A) C))
        (hend : IsStokesEndpoint (mCompactFam α h q e)),
        StokesCohomologyBijections
          (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
          (mCompactFam α h q e) A
          (fun k => lower_rel rho (fun _ => rfl)
            (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres k)
          hend

/-- The coefficient-independent compact-`M` residue.  For a fixed finite target `C`, every
elementary coefficient module is tested against the same displayed word, at level
`4 * Monoid.exponent C`. -/
def UniformPushedHsimp (α h q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        StokesDuality
          (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
          (mCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) A

/-! ## The weakening chain -/

/-- The historical all-markings residue implies the pushed cohomological one. -/
theorem pushedHsimp_of_hsimp {α h q : ℕ} (hsimp : Hsimp α h q) : PushedHsimp α h q := by
  intro C _ _ _ _ rho e he hr hend V _ _ _ hV₂ hsimple
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g)⟩ with ht
  have hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 + 2 * h) q) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 0)
  have hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (mCompactW α h) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 1)
  exact (stokesDuality_iff_cohomologyBijections ⇑t (mCompactFam α h q e) V hr hend).mp
    (hsimp C t e he hrt hrw V hV₂ hsimple)

/-- The pushed residue implies the target-local general-coefficient residue. -/
theorem resolvedPushedHsimp_of_pushedHsimp {α h q : ℕ}
    (hsimp : PushedHsimp α h q) : ResolvedPushedHsimp α h q := by
  intro C _ _ _ _ rho e he A _ _ _ _ _ _ _ hA₂ hres _hresDual hend
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (mCompactFam α h q e k) = 1 := fun k =>
    lower_rel (A := A) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres k
  have hd : StokesDuality ⇑t (mCompactFam α h q e) A :=
    stokesDuality_of_simple ⇑t (mCompactFam α h q e) hr hend
      (fun V _ _ _ hV₂ hsimple =>
        (stokesDuality_iff_cohomologyBijections ⇑t (mCompactFam α h q e) V hr hend).mpr
          (hsimp C rho e he hr hend V hV₂ hsimple)) A hA₂
  exact (stokesDuality_iff_cohomologyBijections ⇑t (mCompactFam α h q e) A hr hend).mp hd

/-- The historical all-markings residue also reaches the target-local residue. -/
theorem resolvedPushedHsimp_of_hsimp {α h q : ℕ}
    (hsimp : Hsimp α h q) : ResolvedPushedHsimp α h q :=
  resolvedPushedHsimp_of_pushedHsimp (pushedHsimp_of_hsimp hsimp)

/-- Upgrade the target-local residue to Stokes duality on exactly the supplied elementary
module. -/
theorem stokesDuality_of_resolvedPushed {α h q : ℕ} (hsimp : ResolvedPushedHsimp α h q)
    (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma α h q : Type)) C) {e : ℕ} (he : Odd e)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
    [TopologicalSpace (WordLift (ElemDual A) C)]
    [DiscreteTopology (WordLift (ElemDual A) C)]
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q e) (WordLift A C))
    (hresDual : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q e) (WordLift (ElemDual A) C)) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g))
      (mCompactFam α h q e) A := by
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (mCompactW α h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (mCompactFam α h q e k) = 1 := fun k =>
    lower_rel (A := A) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres k
  have hend : IsStokesEndpoint (mCompactFam α h q e) := mCompact_isStokesEndpoint hqe he
  exact (stokesDuality_iff_cohomologyBijections ⇑t (mCompactFam α h q e) A hr hend).mpr
    (hsimp C rho e he A hA₂ hres hresDual hend)

/-- Every target-local residue supplies the coefficient-independent uniform-word residue. -/
theorem uniformPushedHsimp_of_resolvedPushed {α h q : ℕ}
    (hsimp : ResolvedPushedHsimp α h q) (hqe : Even q) : UniformPushedHsimp α h q := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace (WordLift A C) := ⊥
  letI : DiscreteTopology (WordLift A C) := ⟨rfl⟩
  letI : TopologicalSpace (WordLift (ElemDual A) C) := ⊥
  letI : DiscreteTopology (WordLift (ElemDual A) C) := ⟨rfl⟩
  have hb := resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := C) (A := A) hA₂ (α := α) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) (WordLift A C) := by
    let incl : ContinuousMonoidHom (WordLift A C) (HeisLift A C) :=
      ⟨Count.heisPrim (A := A) (C := C), continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hresDual : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
      (WordLift (ElemDual A) C) := by
    let incl : ContinuousMonoidHom (WordLift (ElemDual A) C) (HeisLift A C) :=
      ⟨Count.heisDual (A := A) (C := C), continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisDual_injective
  exact stokesDuality_of_resolvedPushed hsimp hqe rho
    (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
      (fourMulExponent_ne_zero_and_even C).2)
    A hA₂ hres hresDual

/-! ## The count and lifting consumers, re-derived from the uniform residue -/

/-- The scalar `H²` count required by the `R`-stage, from the uniform datum map and the uniform
compact-`M` Stokes residue. -/
theorem cardH2_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
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
  have hb := resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := Base ⧸ datum.M) (A := Additive ↥datum.T) (radT_add_self datum)
    (α := α) (h := h) (q := q) hqe
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥datum.T) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisDual_injective
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective α h q hα hq0 hqe) (fun _ => rfl))
    hresS hresP hresD hresH
    (hsimp (Base ⧸ datum.M) rho (Additive ↥datum.T) (radT_add_self datum))
    (hsimp (Base ⧸ datum.M) rho (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective α h q hα hq0 hqe)

/-- The lift count at every recursion frame, from the uniform residue. -/
theorem liftsOver_card_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hqe : Even q)
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
  have hb := resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := RF.YC) (A := Additive ↥RF.MB) (mb_add_self RF)
    (α := α) (h := h) (q := q) hqe
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (HeisLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (WordLift (Additive ↥RF.MB) RF.YC) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥RF.MB) RF.YC)
        (HeisLift (Additive ↥RF.MB) RF.YC) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisPrim_injective
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl))
    (nCompact_degree h) hres
    (hsimp RF.YC rho.1.1 (Additive ↥RF.MB) (mb_add_self RF)) hb.2

/-- The universal half-torsor identity, from the uniform residue. -/
theorem lem86_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hqe : Even q)
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
  have hb := resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := Bg ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D)
    (α := α) (h := h) (q := q) hqe
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (Bg ⧸ D.M)) (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Bg ⧸ D.M))))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hresH.pullback incl Count.heisDual_injective
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (hsimp (Bg ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    (hsimp (Bg ⧸ D.M) rho (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-! ## Assembly -/

/-- Exact lifting for the compact-`M` presentation from the uniform residue. -/
theorem exactLifting_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (hsep : StageSep α h q) (hZ : StageZ α h q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card_of_uniformPushed hsimp hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86_of_uniformPushed hsimp hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2_of_uniformPushed hsimp hα hq0 hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2_of_uniformPushed hsimp hα hq0 hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

set_option maxHeartbeats 800000 in
/-- Corrected exact lifting for the compact-`M` presentation from the uniform residue. -/
theorem exactLiftingRN_of_uniformPushed {α h q : ℕ} (hsimp : UniformPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card_of_uniformPushed hsimp hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86_of_uniformPushed hsimp hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
    letI : CommGroup ↑Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↑Blk.frattiniK) :=
      RStageLocal.conjC Blk hRK
    letI := scalarActionZmodTwo (Y ⧸ Blk.K)
    have hb := resolvesAt_and_endpoint_mCompactFam_uniformHeis
      (C := Y ⧸ Blk.K) (A := Additive ↑Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂) (α := α) (h := h) (q := q) hqe
    have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
        (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
        (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
    have hresR : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
        (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
        (WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) := by
      let incl : ContinuousMonoidHom
          (WordLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K))
          (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) :=
        ⟨Count.heisPrim, continuous_of_discreteTopology⟩
      exact hresH.pullback incl Count.heisPrim_injective
    have hres2 : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
        (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
        (WordLift (ZMod 2) (Y ⧸ Blk.K)) := by
      let incl : ContinuousMonoidHom
          (WordLift (ZMod 2) (Y ⧸ Blk.K))
          (HeisLift (Additive ↑Blk.frattiniK) (Y ⧸ Blk.K)) :=
        ⟨Count.heisScal, continuous_of_discreteTopology⟩
      exact hresH.pullback incl Count.heisScal_injective
    have hpres := isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)
    exact blockStageR136NK (standardNumerics (2 * h + 2)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hq0 hqe)
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
            (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [hrho_apply] using
            (hsimp (Y ⧸ Blk.K) rho (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂
          (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hq0 hqe) b F g hpres
          (isWildTwo_of_gammaGen g.1.1 g.1.2 (fun _ => rfl)) hres2 hresR hd hb.2 hg)
      (fun f₀ => by
        let theta : ContinuousMonoidHom ((gamma α h q : Type)) (Y ⧸ Blk.K) :=
          ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
            show Continuous fun gamma => QuotientGroup.mk' Blk.K (f₀.1.1 gamma)
            exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩
        have htheta_apply (gamma : (gamma α h q : Type)) :
            theta gamma = QuotientGroup.mk' Blk.K (f₀.1.1 gamma) := rfl
        have htheta_surj : Function.Surjective theta := by
          intro c
          obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
          obtain ⟨gamma, hgamma⟩ := f₀.1.2 y
          exact ⟨gamma, by rw [htheta_apply, hgamma, hy]⟩
        have hd : StokesDuality
            (fun i => QuotientGroup.mk' Blk.K
              (f₀.1.1 (gammaGen (2 + 2 * h) q (mCompactW α h) i)))
            (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Y ⧸ Blk.K))))
            (Additive ↑Blk.frattiniK) := by
          simpa only [htheta_apply] using
            (hsimp (Y ⧸ Blk.K) theta (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀.1.1 f₀.1.2 hpres
          hresR (isWildTwo_of_gammaGen theta htheta_surj (fun _ => rfl))
          (degree h) hd hb.2)

/-! ## Compatibility wrappers -/

/-- The target-local residue specializes to the uniform word. -/
theorem cardH2_of_resolvedPushed {α h q : ℕ} (hsimp : ResolvedPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2 :=
  cardH2_of_uniformPushed (uniformPushedHsimp_of_resolvedPushed hsimp hqe) hα hq0 hqe

/-- The pushed residue reaches the scalar count through devissage. -/
theorem cardH2_of_pushed {α h q : ℕ} (hsimp : PushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    Nat.card (H2 ((gamma α h q : Type)) (ZMod 2)) = 2 :=
  cardH2_of_resolvedPushed (resolvedPushedHsimp_of_pushedHsimp hsimp) hα hq0 hqe

/-- Corrected exact lifting from the target-local residue. -/
theorem exactLiftingRN_of_resolvedPushed {α h q : ℕ} (hsimp : ResolvedPushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_uniformPushed (uniformPushedHsimp_of_resolvedPushed hsimp hqe)
    hα hq0 hqe nuP

/-- Corrected exact lifting from the pushed residue. -/
theorem exactLiftingRN_of_pushed {α h q : ℕ} (hsimp : PushedHsimp α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_resolvedPushed (resolvedPushedHsimp_of_pushedHsimp hsimp)
    hα hq0 hqe nuP

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The selected compact-`M` presentation receives corrected exact-lifting semantics from the
uniform residue. -/
theorem exactLiftingRN_of_fieldSelection_uniformPushed
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {α q : ℕ} (hbranch : S.branch = .M0 α)
    (hsimp : UniformPushedHsimp α (handleCount FP (.M0 α)) q) (hα : 1 ≤ α)
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
      have hn : 2 * handleCount FP (.M0 α) + 2 =
          2 + 2 * handleCount FP (.M0 α) := by omega
      exact exactLiftingRN_standard_congr hn
        (exactLiftingRN_of_uniformPushed hsimp hα hq0 hqe nuP)

end

end MCompact

end GQ2.Dyadic
