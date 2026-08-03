/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.NpcExact

/-!
# Exact lifting for the corrected procyclic-M presentation

The semantic branch carries an arbitrary unit and the literal corrected parameter
`p epsilon r`; the certificate side carries an `EtaDisplay`.  The only transport between them
is the landed equality for `Words.Mpc.mpcWUnit` and the corrected displayed `mpcW`.

The resolver genuinely depends on the display.  The `one` and `lit` constructors are
`omega2`-only and use the constant resolver; a genuine `hat num den` constructor uses the
two-valued `npcResolver`.  The display-dependent family below records that distinction once for
the lift count, variation, and half-torsor arguments.
-/

namespace GQ2.Dyadic.MProcyclicExact

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA DihedralGroup

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## Corrected semantic and displayed sources -/

/-- The corrected displayed procyclic-`M` candidate. -/
noncomputable abbrev displayedGamma (alpha r pp h q : ℕ) (d : EtaDisplay) : ProfiniteGrp :=
  GammaR (2 + 2 * h) q (mpcW alpha r pp d h)

/-- The arbitrary-unit candidate used by the semantic branch selector. -/
noncomputable abbrev gamma (alpha r pp h q : ℕ) (eta : ℤ_[2]ˣ) : ProfiniteGrp :=
  GammaR (2 + 2 * h) q (mpcWUnit alpha r pp eta h)

/-- The exact resolver family selected by the display shape. -/
noncomputable def resolvedFamily (alpha r pp h q : ℕ) (d : EtaDisplay) (N : ℕ) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  match d with
  | .one => mpcFam alpha r pp h q (omega2Exp N) .one
  | .lit k => mpcFam alpha r pp h q (omega2Exp N) (.lit k)
  | .hat num den =>
      mpcFamOf alpha r pp h q (.hat num den) (npcResolver N ⟨num, den⟩) (fun _ ↦ 0)

/-- The endpoint half of the display-dependent family does not depend on a target group. -/
theorem resolvedFamily_isStokesEndpoint {N alpha r pp h q : ℕ}
    (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0) (hα : 1 ≤ alpha) (hqe : Even q)
    (d : EtaDisplay) : IsStokesEndpoint (resolvedFamily alpha r pp h q d N) := by
  cases d with
  | one => exact mpc_isStokesEndpoint hα hqe (odd_omega2Exp hN hv)
  | lit k => exact mpc_isStokesEndpoint hα hqe (odd_omega2Exp hN hv)
  | hat num den =>
      exact mpcOf_isStokesEndpoint hα hqe
        (odd_npcResolver_omega2 hN hv ⟨num, den⟩) (.hat num den)

/-- The matched resolver/endpoint pair for every display.  In the `hat` branch this is
literally the two-valued resolver theorem, not a constant-resolver surrogate. -/
theorem resolvesAt_and_endpoint_resolvedFamily
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N alpha r pp h q : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hord : ∀ x : Q, orderOf x ∣ N) (hα : 1 ≤ alpha) (hqe : Even q)
    (d : EtaDisplay) :
    ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
        (resolvedFamily alpha r pp h q d N) Q
      ∧ IsStokesEndpoint (resolvedFamily alpha r pp h q d N) := by
  cases d with
  | one =>
      exact resolvesAt_and_endpoint_mpcFam hN hv hord hα hqe trivial
  | lit k =>
      exact resolvesAt_and_endpoint_mpcFam hN hv hord hα hqe trivial
  | hat num den =>
      exact resolvesAt_and_endpoint_mpcFamOf_hat hN hv hord hα hqe num den (fun _ ↦ 0)

/-- The sole word-level analytic residue, at the exact display-dependent resolver family. -/
def Hsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (t : Marking (2 + 2 * h) C) (N : ℕ),
    N ≠ 0 → N.factorization 2 ≠ 0 →
    (∀ k, FreeGroup.lift ⇑t (resolvedFamily alpha r pp h q d N k) = 1) →
    ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (resolvedFamily alpha r pp h q d N) V

/-- Upgrade the simple-module residue to every finite elementary module. -/
theorem stokesDuality {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g => rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A := by
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (resolvedFamily alpha r pp h q d N k) = 1 := fun k =>
    lower_rel (A := ZMod 2) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
      hres k
  exact stokesDuality_of_simple ⇑t (resolvedFamily alpha r pp h q d N) hr
    (resolvedFamily_isStokesEndpoint hN hv hα hqe d)
    (hsimp C t N hN hv hr) A hA₂

/-- The primary-module Stokes payload at the intrinsic Heisenberg level. -/
theorem stokesDuality_T {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g => rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) := by
  have hb := resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) orderOf_dvd_heisLevel_scal
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  exact stokesDuality hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hb.1
    (Additive ↥D.T) (radT_add_self D)

/-! ## A uniform nonzero-variation quotient -/

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

theorem datumQuot_sq (y : Base ⧸ datum.M) : y * y = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, show b * b = 1 from by revert b; decide,
    QuotientGroup.mk_one]

theorem isProP_datumQuot : IsProP 2 (Base ⧸ datum.M) :=
  isProP_of_isPGroup fun y ↦ ⟨1, by rw [pow_one, pow_two]; exact datumQuot_sq y⟩

/-- Send `sigma` to the nontrivial quotient class and every other letter to one. -/
noncomputable def datumMarking (h : ℕ) : Marking (2 + 2 * h) (Base ⧸ datum.M) :=
  Marking.ofLetters (QuotientGroup.mk (DihedralGroup.r 1)) 1 (fun _ ↦ 1)

/-- Both corrected relators die on the datum marking.  The branch condition `1 ≤ r` is used
exactly to make `sigma^(2^r)` trivial in the exponent-two quotient. -/
theorem datumMarking_relators (alpha r pp h q : ℕ) (d : EtaDisplay)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) :
    ∀ k, PWord.eval ⇑(datumMarking h)
      (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h) k) = 1 := by
  intro k
  fin_cases k
  · change PWord.eval ⇑(datumMarking h) (tameRelW (2 + 2 * h) q) = 1
    simp [datumMarking, tameRelW]
  · change PWord.eval ⇑(datumMarking h) (mpcW alpha r pp d h) = 1
    rw [show PWord.eval ⇑(datumMarking h) (mpcW alpha r pp d h) =
      (datumMarking h).eval (mpcW alpha r pp d h) from rfl]
    rw [← Marking.eval_pro2 (datumMarking h) (by rfl)
      (zpowHat_omega2_eq_self_of_isProP isProP_datumQuot) (mpcW alpha r pp d h)]
    rw [eval_pro2_mpcW hα]
    simp [datumMarking, coreLetter, handleU, handleV, s]
    obtain ⟨k, hk⟩ := dvd_pow_self 2 (by omega : r ≠ 0)
    rw [hk, pow_mul,
      show (QuotientGroup.mk (DihedralGroup.r 1) : Base ⧸ datum.M) ^ 2 = 1 from by
        simpa [pow_two] using
          datumQuot_sq (QuotientGroup.mk (DihedralGroup.r 1) : Base ⧸ datum.M)]
    simp [MarkedCore.mWord, MarkedCore.handleWord, GQ2.commP]

/-- The all-trivial wild marking is admissible. -/
theorem datumMarking_isWildTwo (h : ℕ) :
    IsWildTwo (wildAlphabet (2 + 2 * h)) (datumMarking h) := by
  show IsPGroup 2
    (Subgroup.normalClosure ((datumMarking h : Generator (2 + 2 * h) → Base ⧸ datum.M) ''
      wildAlphabet (2 + 2 * h)))
  have hbot : Subgroup.normalClosure
      ((datumMarking h : Generator (2 + 2 * h) → Base ⧸ datum.M) ''
        wildAlphabet (2 + 2 * h)) = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨i, hi, rfl⟩
    exact Subgroup.mem_bot.mpr (by rcases hi with ⟨j, rfl⟩; rfl)
  rw [hbot]
  exact IsPGroup.of_bot

/-- The uniform quotient map used to manufacture the nonzero variation class. -/
noncomputable def datumRho (alpha r pp h q : ℕ) (d : EtaDisplay)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) :
    ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Base ⧸ datum.M) :=
  Classical.choose ((isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
    (mpcW alpha r pp d h)).extend (datumMarking h)
      (datumMarking_relators alpha r pp h q d hα hr) (datumMarking_isWildTwo h))

@[simp] theorem datumRho_gammaGen (alpha r pp h q : ℕ) (d : EtaDisplay)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) (i : Generator (2 + 2 * h)) :
    datumRho alpha r pp h q d hα hr
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i) = datumMarking h i :=
  Classical.choose_spec ((isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
    (mpcW alpha r pp d h)).extend (datumMarking h)
      (datumMarking_relators alpha r pp h q d hα hr) (datumMarking_isWildTwo h)) i

/-- The variation quotient map is onto through its `sigma` value. -/
theorem datumRho_surjective (alpha r pp h q : ℕ) (d : EtaDisplay)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) :
    Function.Surjective (datumRho alpha r pp h q d hα hr) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hcases : (QuotientGroup.mk b : Base ⧸ datum.M) = 1 ∨
      (QuotientGroup.mk b : Base ⧸ datum.M) = QuotientGroup.mk (DihedralGroup.r 1) :=
    quotient_cases b
  rcases hcases with h1 | hs
  · exact ⟨1, by simpa using h1.symm⟩
  · refine ⟨gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) .sigma, ?_⟩
    rw [datumRho_gammaGen]
    simpa [datumMarking] using hs.symm

/-! ## Variation, scalar cohomology, and the first two lifting clauses -/

/-- The scalar `H²` count follows from the uniform quotient and the exact resolver family. -/
theorem cardH2 {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q) :
    letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d : Type))
    Nat.card (H2 ((displayedGamma alpha r pp h q d : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d : Type))
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho alpha r pp h q d hα hr with hrho
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r pp h q d : Type))
      (Additive ↥datum.T) := DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((displayedGamma alpha r pp h q d : Type))
      (ElemDual (Additive ↥datum.T)) := DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r pp h q d : Type))
      (ElemDual (Additive ↥datum.T)) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r pp h q d : Type)) ×
            ElemDual (Additive ↥datum.T) => p.1 • p.2)
          = (fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)
            ∘ (fun p : ((displayedGamma alpha r pp h q d : Type)) ×
                ElemDual (Additive ↥datum.T) => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
    (Q := WordLift (ZMod 2) (Base ⧸ datum.M)) orderOf_dvd_heisLevel_scal
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel datum))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel datum))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      hα hqe d).1
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel datum))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      hα hqe d).1
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel datum))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      hα hqe d).1
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective alpha r pp h q d hα hr)
      (fun _ => rfl))
    hresS hresP hresD hresH (stokesDuality_T hsimp hα hqe rho)
    (stokesDuality hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hresS
      (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective alpha r pp h q d hα hr)

/-- The lift count at every recursion frame, derived from the matched display resolver. -/
theorem liftsOver_card {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type))
        ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics (2 * h + 2)).mMult (Nat.card ↥RF.MB) := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk RF b F rho
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_resolvedFamily
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    (Q := WordLift (Additive ↥RF.MB) RF.YC) orderOf_wordLift_dvd_heisExponent
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC)))
      (WordLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC)))
      (WordLift (ZMod 2) RF.YC) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d).1
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl))
    (nCompact_degree h) hres
    (stokesDuality hsimp hα hqe rho.1.1 heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 hresS (Additive ↥RF.MB) (mb_add_self RF)) hb.2

/-- The universal half-torsor identity, with no branch-specific cardinality premise. -/
theorem lem86 {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d : Type))
  letI := scalarActionZmodTwo (Bg ⧸ D.M)
  letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r pp h q d : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((displayedGamma alpha r pp h q d : Type))
      (ElemDual (Additive ↥D.T)) := DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r pp h q d : Type))
      (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r pp h q d : Type)) ×
            ElemDual (Additive ↥D.T) => p.1 • p.2)
          = (fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)
            ∘ (fun p : ((displayedGamma alpha r pp h q d : Type)) ×
                ElemDual (Additive ↥D.T) => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) orderOf_dvd_heisLevel_scal
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel D))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := hb.1
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel D))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      hα hqe d).1
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel D))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      hα hqe d).1
  have hresH : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (heisLevel D))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      hα hqe d).1
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (stokesDuality_T hsimp hα hqe rho)
    (stokesDuality hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hresS
      (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-! ## The two irreducible R-stage residues -/

/-- Obstruction-zero lower lifts come from homomorphisms into the original marked target.
This is the exact separation input consumed by `blockStageR136K`. -/
def StageSep (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : ((displayedGamma alpha r pp h q d : Type))) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((displayedGamma alpha r pp h q d : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB),
    obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
        htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) Y,
        ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ

/-- The `R`-cocycle torsor has the block frame's prescribed cardinality. -/
def StageZ (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (f₀ : BoundaryLiftsK b F T),
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀.1.1) =
      (blockFrameImpl T Blk hE₂).zR

/-! ## Corrected degree-indexed R-stage -/

/-- Obstruction-zero separation for every displayed Mpc form.  The resolver is selected by
`resolvedFamily`: `.one`/`.lit` use the constant family, while `.hat` uses the two-valued Npc
resolver. -/
theorem homLift_of_obs_zeroRN {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    [DistribMulAction ((displayedGamma alpha r pp h q d : Type)) (ZMod 2)]
    [ContinuousSMul ((displayedGamma alpha r pp h q d : Type)) (ZMod 2)]
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ x ∈ Blk.frattiniK, ∀ k ∈ Blk.K, x * k = k * x)
    (hR₂ : ∀ x ∈ Blk.frattiniK, x * x = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : (displayedGamma alpha r pp h q d : Type)) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((displayedGamma alpha r pp h q d : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB)
    (hg : obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
      htriv hcard g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) Y,
      ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) := scalarActionZmodTwo (Y ⧸ Blk.K)
  have hb := resolvesAt_and_endpoint_resolvedFamily
    (Q := WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  have hresR : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (ZMod 2) (Y ⧸ Blk.K)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d).1
  have hRleK : Blk.frattiniK ≤ Blk.K := SectionSeven.frattiniLike_le Blk.K
  set qKR : (blockFrameImpl T Blk hE₂).YB →* (Y ⧸ Blk.K) :=
    QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
      (by rw [Subgroup.comap_id]; exact hRleK) with hqKR
  set θ : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Y ⧸ Blk.K) :=
    ⟨qKR.comp g.1.1.toMonoidHom,
      (continuous_of_discreteTopology (f := qKR)).comp g.1.1.continuous_toFun⟩ with hθ
  have hd : StokesDuality
      (fun i => θ (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (Additive ↥Blk.frattiniK) :=
    stokesDuality hsimp hα hqe θ heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 hresS (Additive ↥Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂)
  refine homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂ htriv hcard b F g
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    (isWildTwo_gammaGen_of_surjective g.1.1 g.1.2) hresS hresR ?_ hb.2 hg
  change StokesDuality
    (fun i => θ (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i))
    (resolvedFamily alpha r pp h q d
      (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
    (Additive ↥Blk.frattiniK)
  exact hd

/-- The corrected display-dependent Mpc R-cocycle coefficient. -/
theorem rCocycle_cardRN {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ x ∈ Blk.frattiniK, ∀ k ∈ Blk.K, x * k = k * x)
    (hR₂ : ∀ x ∈ Blk.frattiniK, x * x = 1)
    (f₀ : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) Y)
    (hf₀ : Function.Surjective f₀) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀) =
      zRN (blockFrameImpl T Blk hE₂) (standardNumerics (2 * h + 2)) := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) := scalarActionZmodTwo (Y ⧸ Blk.K)
  have hb := resolvesAt_and_endpoint_resolvedFamily
    (Q := WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  have hresR : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (ZMod 2) (Y ⧸ Blk.K)) :=
    (resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d).1
  set θ : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.toMonoidHom,
      (continuous_of_discreteTopology (f := QuotientGroup.mk' Blk.K)).comp
        f₀.continuous_toFun⟩ with hθ
  have hθsurj : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective Blk.K).comp hf₀
  have hd : StokesDuality
      (fun i => θ (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i))
      (resolvedFamily alpha r pp h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (Additive ↥Blk.frattiniK) :=
    stokesDuality hsimp hα hqe θ heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 hresS (Additive ↥Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂)
  exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀ hf₀
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    hresR (isWildTwo_gammaGen_of_surjective θ hθsurj) (nCompact_degree h) hd hb.2

/-- Corrected exact lifting for every displayed Mpc presentation.  The display-dependent
resolver discharges both R-stage residues, so no legacy `StageSep`/`StageZ` premise remains. -/
theorem exactLiftingDisplayedRN {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (displayedGamma alpha r pp h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d : Type))
    haveI := scalarActionZmodTwo_continuousSMul
      ((displayedGamma alpha r pp h q d : Type))
    exact blockStageR136NK (standardNumerics (2 * h + 2)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2 hsimp hα hr hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
          (mpcW alpha r pp d h))) b F
      (fun g hg => homLift_of_obs_zeroRN hsimp hα hqe T Blk hE₂ hRK hR₂ b F
        (scalarActionZmodTwo_triv _) (cardH2 hsimp hα hr hqe) g hg)
      (fun f₀ => rCocycle_cardRN hsimp hα hqe hE₂ hRK hR₂ f₀.1.1 f₀.1.2)

/-! ## Assembly and the arbitrary-unit compatibility bridge -/

/-- Exact lifting for a displayed corrected procyclic-`M` presentation.  The branch condition
`1 ≤ r` is used only by the uniform nonzero-variation quotient. -/
theorem exactLiftingDisplayed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    (hsep : StageSep alpha r pp h q d) (hZ : StageZ alpha r pp h q d)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (displayedGamma alpha r pp h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d : Type))
    haveI := scalarActionZmodTwo_continuousSMul
      ((displayedGamma alpha r pp h q d : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2 hsimp hα hr hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
          (mpcW alpha r pp d h))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2 hsimp hα hr hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

/-- Literal relator regression for the improved sign parameter `p epsilon r`. -/
theorem gammaRelators_sign_eq_display (alpha r h q : ℕ) (epsilon : Bool)
    {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta) :
    gammaRelators (2 + 2 * h) q (mpcWUnit alpha r (p epsilon r) eta h) =
      gammaRelators (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h) :=
  Words.Mpc.gammaRelators_mpcWUnit_eq_display alpha r (p epsilon r) h q d

/-- A compatible display identifies the arbitrary-unit candidate with the corrected displayed
candidate.  This is the only semantic-to-certificate transport used below. -/
theorem gamma_eq_display (alpha r pp h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    gamma alpha r pp h q eta = displayedGamma alpha r pp h q d.display := by
  rw [gamma, displayedGamma,
    Words.Mpc.GammaR_mpcWUnit_eq_display alpha r pp h q d]

/-- Sign-specialized semantic regression, keeping `p epsilon r` visible in the statement. -/
theorem gamma_sign_eq_display (alpha r h q : ℕ) (epsilon : Bool)
    {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta) :
    gamma alpha r (p epsilon r) h q eta =
      displayedGamma alpha r (p epsilon r) h q d.display :=
  gamma_eq_display alpha r (p epsilon r) h q d

/-- Exact lifting for the corrected arbitrary-unit procyclic-`M` presentation. -/
theorem exactLifting {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (hsimp : Hsimp alpha r (p epsilon r) h q d.display)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    (hsep : StageSep alpha r (p epsilon r) h q d.display)
    (hZ : StageZ alpha r (p epsilon r) h q d.display)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma alpha r (p epsilon r) h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  rw [gamma_sign_eq_display alpha r h q epsilon d]
  exact exactLiftingDisplayed hsimp hα hr hqe hsep hZ nuP

/-- Corrected exact lifting for the arbitrary-unit Mpc presentation with the improved literal
sign parameter `p epsilon r`. -/
theorem exactLiftingRN {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (hsimp : Hsimp alpha r (p epsilon r) h q d.display)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma alpha r (p epsilon r) h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  rw [gamma_sign_eq_display alpha r h q epsilon d]
  exact exactLiftingDisplayedRN hsimp hα hr hqe nuP

/-- Literal constructor regression: both the arbitrary unit and `p epsilon r` occur visibly in
the RN carrier. -/
theorem exactLiftingRN_literal {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (hsimp : Hsimp alpha r (p epsilon r) h q d.display)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN
      (GammaR (2 + 2 * h) q (mpcWUnit alpha r (p epsilon r) eta h))
      (2 * h + 2) q P nuP (standardNumerics (2 * h + 2)) :=
  exactLiftingRN d hsimp hα hr hqe nuP

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- A selected `.Mpc` row uses the corrected semantic constructor with the literal sign
parameter, and its stored display recovers the certificate word. -/
theorem gammaR_eq_display_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {epsilon : Bool}
    {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    GammaR S.semantic.degree q S.semantic.word =
      displayedGamma alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) q
        (hbranch ▸ S.display).display := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact gamma_sign_eq_display alpha r (handleCount FP (.Mpc alpha r epsilon eta)) q
        epsilon display

/-- The field selector hands a chosen `.Mpc` row directly to the exact-lifting constructor.
Branch validity supplies both `1 ≤ alpha` and the genuinely needed `1 ≤ r`. -/
theorem exactLifting_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {epsilon : Bool}
    {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (hsimp : Hsimp alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ S.display).display)
    (hqe : Even q)
    (hsep : StageSep alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ S.display).display)
    (hZ : StageZ alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ S.display).display)
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
        (GammaR (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q
          (mpcWUnit alpha r (p epsilon r) eta
            (handleCount FP (.Mpc alpha r epsilon eta))))
        (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)))
      have hn : 2 * handleCount FP (.Mpc alpha r epsilon eta) + 2 =
          2 + 2 * handleCount FP (.Mpc alpha r epsilon eta) := by omega
      exact NCompact.exactLifting_standard_congr hn
        (exactLifting display hsimp (le_trans (by omega) valid.1) valid.2 hqe hsep hZ nuP)

/-- The field selector hands a chosen `.Mpc` row to the corrected RN constructor, preserving
the literal `p epsilon r` and requiring no legacy R-stage premises. -/
theorem exactLiftingRN_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {epsilon : Bool}
    {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (hsimp : Hsimp alpha r (p epsilon r) (handleCount FP (.Mpc alpha r epsilon eta)) q
      (hbranch ▸ S.display).display)
    (hqe : Even q)
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
        (GammaR (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q
          (mpcWUnit alpha r (p epsilon r) eta
            (handleCount FP (.Mpc alpha r epsilon eta))))
        (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.Mpc alpha r epsilon eta)))
      have hn : 2 * handleCount FP (.Mpc alpha r epsilon eta) + 2 =
          2 + 2 * handleCount FP (.Mpc alpha r epsilon eta) := by omega
      exact NProcyclic.exactLiftingRN_standard_congr hn
        (exactLiftingRN display hsimp (le_trans (by omega) valid.1) valid.2 hqe nuP)

end

end GQ2.Dyadic.MProcyclicExact
