/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.N0Exact
import GQ2.Dyadic.Count.RStage
import GQ2.Dyadic.Instances.LUniformHeisenbergResolver

/-!
# Exact lifting for the corrected procyclic-N presentation

This file constructs `ExactLiftingSemantics` for the corrected procyclic-`N` word.  The
arithmetic selector stores an arbitrary unit `eta : Z_2^*`, while the word certificates use a
rational `EtaData` display.  The only bridge between those two faces is the literal equality
`Words.Npc.npcWUnit_eq_display`; no theorem below mentions the retired uncorrected word.

The resolver is necessarily the two-valued `Count.npcResolver`: the constant resolver does not
resolve both `omega2` and `etaHat` at general finite targets.  The lift count, nonzero variation,
`#H^2 = 2`, and the half-torsor identity are derived from the landed generic count APIs.  The
only remaining inputs are per-simple Stokes duality and the two low-level `R`-stage residues.
-/

namespace GQ2.Dyadic.NProcyclic

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA DihedralGroup

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The exact corrected word and its resolver family -/

/-- The displayed corrected procyclic-`N` candidate. -/
noncomputable abbrev displayedGamma (alpha r h q : ℕ) (d : EtaData) : ProfiniteGrp :=
  GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d)

/-- The arbitrary-unit semantic candidate selected by the arithmetic branch table. -/
noncomputable abbrev gamma (alpha r h q : ℕ) (eta : ℤ_[2]ˣ) : ProfiniteGrp :=
  GammaR (2 + 2 * h) q (Words.Npc.npcWUnit alpha r h eta)

/-- The single two-valued family used by all three exact-lifting clauses.  The `E₂` resolver
is fixed to zero because the Npc word contains no `z2pow` node. -/
noncomputable def resolvedFamily (alpha r h q : ℕ) (d : EtaData) (N : ℕ) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  npcFamOf alpha r h q d (npcResolver N d) (fun _ ↦ 0)

/-- The sole word-level analytic residue: perfect Stokes duality on every simple elementary
module, at the exact two-valued resolver family. -/
def Hsimp (alpha r h q : ℕ) (d : EtaData) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (t : Marking (2 + 2 * h) C) (N : ℕ),
    N ≠ 0 → N.factorization 2 ≠ 0 →
    (∀ k, FreeGroup.lift ⇑t (resolvedFamily alpha r h q d N k) = 1) →
    ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (resolvedFamily alpha r h q d N) V

/-- The generic devissage upgrades the simple-module residue to every finite elementary
module at a marking pushed forward from the displayed candidate. -/
theorem stokesDuality {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g => rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d N) A := by
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g => rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift ⇑t (resolvedFamily alpha r h q d N k) = 1 := fun k =>
    lower_rel (A := ZMod 2) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
        (Words.Npc.npcW alpha r h d)) hres k
  exact stokesDuality_of_simple ⇑t (resolvedFamily alpha r h q d N) hr
    (npcResolver_isStokesEndpoint hα hqe hN hv d (fun _ ↦ 0))
    (hsimp C t N hN hv hr) A hA₂

/-- The primary-module Stokes payload needed by the variation argument, at its intrinsic
Heisenberg level. -/
theorem stokesDuality_T {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g => rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d (heisLevel D)) (Additive ↥D.T) := by
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  exact stokesDuality hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hb.1
    (Additive ↥D.T) (radT_add_self D)

/-! ## A uniform nonzero-variation quotient -/

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-- The standard variation quotient has exponent two. -/
theorem datumQuot_sq (y : Base ⧸ datum.M) : y * y = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, show b * b = 1 from by revert b; decide,
    QuotientGroup.mk_one]

/-- An exponent-two group is commutative; this local instance lets the abelian Npc evaluation
lemma expose that the correction and eta-twist disappear on the variation quotient. -/
local instance datumQuotCommGroup : CommGroup (Base ⧸ datum.M) :=
  { (inferInstance : Group (Base ⧸ datum.M)) with
    mul_comm := fun a b ↦ by
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (datumQuot_sq a)
      have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (datumQuot_sq b)
      have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (datumQuot_sq (a * b))
      calc
        a * b = (a * b)⁻¹ := hab.symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [ha, hb] }

/-- The quotient is a finite pro-`2` group. -/
theorem isProP_datumQuot : IsProP 2 (Base ⧸ datum.M) :=
  isProP_of_isPGroup fun y ↦ ⟨1, by rw [pow_one, pow_two]; exact datumQuot_sq y⟩

/-- Send `sigma` to the nontrivial quotient class and every other letter to one. -/
noncomputable def datumMarking (h : ℕ) : Marking (2 + 2 * h) (Base ⧸ datum.M) :=
  Marking.ofLetters (QuotientGroup.mk (r 1)) 1 (fun _ ↦ 1)

theorem datumMarking_relators (alpha r h q : ℕ) (d : EtaData) :
    ∀ k, PWord.eval ⇑(datumMarking h)
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d) k) = 1 := by
  intro k
  fin_cases k
  · change PWord.eval ⇑(datumMarking h) (tameRelW (2 + 2 * h) q) = 1
    simp [datumMarking, tameRelW]
  · change PWord.eval ⇑(datumMarking h) (Words.Npc.npcW alpha r h d) = 1
    rw [show PWord.eval ⇑(datumMarking h) (Words.Npc.npcW alpha r h d) =
      (datumMarking h).eval (Words.Npc.npcW alpha r h d) from rfl,
      Words.Npc.eval_npcW_of_comm]
    simp [datumMarking, coreLetter, GQ2.zpowHat_omega2, GQ2.powOmega2]

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
noncomputable def datumRho (alpha r h q : ℕ) (d : EtaData) :
    ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Base ⧸ datum.M) :=
  Classical.choose ((isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
    (Words.Npc.npcW alpha r h d)).extend (datumMarking h)
      (datumMarking_relators alpha r h q d) (datumMarking_isWildTwo h))

@[simp] theorem datumRho_gammaGen (alpha r h q : ℕ) (d : EtaData)
    (i : Generator (2 + 2 * h)) :
    datumRho alpha r h q d
      (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i) = datumMarking h i :=
  Classical.choose_spec ((isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
    (Words.Npc.npcW alpha r h d)).extend (datumMarking h)
      (datumMarking_relators alpha r h q d) (datumMarking_isWildTwo h)) i

/-- The variation quotient map is onto: its `sigma` value is the nontrivial class. -/
theorem datumRho_surjective (alpha r h q : ℕ) (d : EtaData) :
    Function.Surjective (datumRho alpha r h q d) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hcases : (QuotientGroup.mk b : Base ⧸ datum.M) = 1 ∨
      (QuotientGroup.mk b : Base ⧸ datum.M) = QuotientGroup.mk (DihedralGroup.r 1) :=
    quotient_cases b
  rcases hcases with h1 | hr
  · exact ⟨1, by simpa using h1.symm⟩
  · refine ⟨gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) .sigma, ?_⟩
    rw [datumRho_gammaGen]
    simpa [datumMarking] using hr.symm

/-! ## Variation, scalar cohomology, and the first two lifting clauses -/

/-- The scalar `H²` count required by the `R`-stage.  It is a theorem, not a branch
hypothesis: the uniform quotient above supplies the nonzero variation class. -/
theorem cardH2 {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    Nat.card (H2 ((displayedGamma alpha r h q d : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho alpha r h q d with hrho
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) (Additive ↥datum.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥datum.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥datum.T)) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) ×
            ElemDual (Additive ↥datum.T) => p.1 • p.2)
          = (fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)
            ∘ (fun p : ((displayedGamma alpha r h q d : Type)) ×
                ElemDual (Additive ↥datum.T) => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (ZMod 2) (Base ⧸ datum.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel datum))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := hb.1
  have hresP : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel datum))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := alpha) (r := r) (h := h) (q := q)
      hα hqe d (fun _ ↦ 0)).1
  have hresD : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel datum))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := alpha) (r := r) (h := h) (q := q)
      hα hqe d (fun _ ↦ 0)).1
  have hresH : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel datum))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := alpha) (r := r) (h := h) (q := q)
      hα hqe d (fun _ ↦ 0)).1
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective alpha r h q d) (fun _ => rfl))
    hresS hresP hresD hresH (stokesDuality_T hsimp hα hqe rho)
    (stokesDuality hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hresS
      (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective alpha r h q d)

/-- The lift count at every recursion frame.  The only presentation-specific input is
`Hsimp`; the resolver, endpoint, admissibility, wildness, and deficiency are uniform. -/
theorem liftsOver_card {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
        ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics (2 * h + 2)).mMult (Nat.card ↥RF.MB) := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk RF b F rho
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (Additive ↥RF.MB) RF.YC)
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC)))
      (WordLift (Additive ↥RF.MB) RF.YC) := hb.1
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC)))
      (WordLift (ZMod 2) RF.YC) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (α := alpha) (r := r) (h := h) (q := q) hα hqe d (fun _ ↦ 0)).1
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl))
    (nCompact_degree h) hres
    (stokesDuality hsimp hα hqe rho.1.1 heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 hresS (Additive ↥RF.MB) (mb_add_self RF))
    hb.2

/-- The universal half-torsor identity.  `NoDescent` and surjectivity manufacture the
nonzero variation class through the same two-valued resolver used by the lift count. -/
theorem lem86 {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  letI := scalarActionZmodTwo (Bg ⧸ D.M)
  letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) ×
            ElemDual (Additive ↥D.T) => p.1 • p.2)
          = (fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)
            ∘ (fun p : ((displayedGamma alpha r h q d : Type)) ×
                ElemDual (Additive ↥D.T) => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel D))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := hb.1
  have hresP : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel D))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := alpha) (r := r) (h := h) (q := q)
      hα hqe d (fun _ ↦ 0)).1
  have hresD : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel D))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := alpha) (r := r) (h := h) (q := q)
      hα hqe d (fun _ ↦ 0)).1
  have hresH : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (heisLevel D))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := alpha) (r := r) (h := h) (q := q)
      hα hqe d (fun _ ↦ 0)).1
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (stokesDuality_T hsimp hα hqe rho)
    (stokesDuality hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hresS
      (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-! ## The two irreducible R-stage residues -/

/-- Obstruction-zero lower lifts come from homomorphisms into the original marked target.
This is the exact separation input consumed by `blockStageR136K`. -/
def StageSep (alpha r h q : ℕ) (d : EtaData) : Prop :=
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : ((displayedGamma alpha r h q d : Type))) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((displayedGamma alpha r h q d : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB),
    obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
        htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) Y,
        ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ

/-- The `R`-cocycle torsor has the block frame's prescribed cardinality. -/
def StageZ (alpha r h q : ℕ) (d : EtaData) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (f₀ : BoundaryLiftsK b F T),
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀.1.1) =
      (blockFrameImpl T Blk hE₂).zR

/-! ## Corrected degree-indexed R-stage -/

/-- Obstruction-zero separation for the displayed Npc presentation, derived from the same
two-valued resolver and `Hsimp` payload used by the other exact-lifting clauses.  This is the
sound replacement for the legacy `StageSep` premise: the block hypotheses `hRK` and `hR2`
remain explicit. -/
theorem homLift_of_obs_zeroRN {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    [DistribMulAction ((displayedGamma alpha r h q d : Type)) (ZMod 2)]
    [ContinuousSMul ((displayedGamma alpha r h q d : Type)) (ZMod 2)]
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ x ∈ Blk.frattiniK, ∀ k ∈ Blk.K, x * k = k * x)
    (hR₂ : ∀ x ∈ Blk.frattiniK, x * x = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : (displayedGamma alpha r h q d : Type)) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((displayedGamma alpha r h q d : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB)
    (hg : obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
      htriv hcard g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) Y,
      ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) := scalarActionZmodTwo (Y ⧸ Blk.K)
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  have hresR : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (ZMod 2) (Y ⧸ Blk.K)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (α := alpha) (r := r) (h := h) (q := q) hα hqe d (fun _ ↦ 0)).1
  have hRleK : Blk.frattiniK ≤ Blk.K := SectionSeven.frattiniLike_le Blk.K
  set qKR : (blockFrameImpl T Blk hE₂).YB →* (Y ⧸ Blk.K) :=
    QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
      (by rw [Subgroup.comap_id]; exact hRleK) with hqKR
  set θ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Y ⧸ Blk.K) :=
    ⟨qKR.comp g.1.1.toMonoidHom,
      (continuous_of_discreteTopology (f := qKR)).comp g.1.1.continuous_toFun⟩ with hθ
  have hd : StokesDuality
      (fun i => θ (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (Additive ↥Blk.frattiniK) :=
    stokesDuality hsimp hα hqe θ heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 hresS (Additive ↥Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂)
  refine homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂ htriv hcard b F g
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (isWildTwo_gammaGen_of_surjective g.1.1 g.1.2) hresS hresR ?_ hb.2 hg
  change StokesDuality (fun i => θ
      (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i))
    (resolvedFamily alpha r h q d
      (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
    (Additive ↥Blk.frattiniK)
  exact hd

/-- The corrected Npc R-cocycle coefficient, derived from its matched resolver and Stokes
payload.  This eliminates the false rank-one-calibrated `StageZ` premise above degree one. -/
theorem rCocycle_cardRN {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ x ∈ Blk.frattiniK, ∀ k ∈ Blk.K, x * k = k * x)
    (hR₂ : ∀ x ∈ Blk.frattiniK, x * x = 1)
    (f₀ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) Y)
    (hf₀ : Function.Surjective f₀) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀) =
      zRN (blockFrameImpl T Blk hE₂) (standardNumerics (2 * h + 2)) := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) := scalarActionZmodTwo (Y ⧸ Blk.K)
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  have hresR : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) := hb.1
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (WordLift (ZMod 2) (Y ⧸ Blk.K)) :=
    (resolvesAt_and_endpoint_npcFamOf heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
      (α := alpha) (r := r) (h := h) (q := q) hα hqe d (fun _ ↦ 0)).1
  set θ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.toMonoidHom,
      (continuous_of_discreteTopology (f := QuotientGroup.mk' Blk.K)).comp
        f₀.continuous_toFun⟩ with hθ
  have hθsurj : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective Blk.K).comp hf₀
  have hd : StokesDuality
      (fun i => θ (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i))
      (resolvedFamily alpha r h q d
        (Monoid.exponent (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))))
      (Additive ↥Blk.frattiniK) :=
    stokesDuality hsimp hα hqe θ heisLevel_ne_zero_and_even.1
      heisLevel_ne_zero_and_even.2 hresS (Additive ↥Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂)
  exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀ hf₀
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d)) hresR
    (isWildTwo_gammaGen_of_surjective θ hθsurj) (nCompact_degree h) hd hb.2

/-- Corrected exact lifting for a displayed Npc presentation.  All three clauses now follow
from `Hsimp` and arithmetic side conditions; no `StageSep` or `StageZ` premise remains. -/
theorem exactLiftingDisplayedRN {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (displayedGamma alpha r h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    haveI := scalarActionZmodTwo_continuousSMul
      ((displayedGamma alpha r h q d : Type))
    exact blockStageR136NK (standardNumerics (2 * h + 2)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2 hsimp hα hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
          (Words.Npc.npcW alpha r h d))) b F
      (fun g hg => homLift_of_obs_zeroRN hsimp hα hqe T Blk hE₂ hRK hR₂ b F
        (scalarActionZmodTwo_triv _) (cardH2 hsimp hα hqe) g hg)
      (fun f₀ => rCocycle_cardRN hsimp hα hqe hE₂ hRK hR₂ f₀.1.1 f₀.1.2)

/-! ## Assembly and the arbitrary-unit compatibility bridge -/

/-- Exact lifting for a displayed corrected procyclic-`N` presentation. -/
theorem exactLiftingDisplayed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    (hsep : StageSep alpha r h q d) (hZ : StageZ alpha r h q d)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (displayedGamma alpha r h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86 hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    haveI := scalarActionZmodTwo_continuousSMul
      ((displayedGamma alpha r h q d : Type))
    exact blockStageR136K T Blk hE₂ (scalarActionZmodTwo_triv _)
      (cardH2 hsimp hα hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
          (Words.Npc.npcW alpha r h d))) b F
      (fun g hg => hsep T Blk hE₂ b F (scalarActionZmodTwo_triv _)
        (cardH2 hsimp hα hqe) g hg)
      (fun f₀ => hZ T Blk hE₂ b F f₀)

/-- Regression theorem: a compatible rational display identifies the arbitrary-unit semantic
candidate with the displayed corrected candidate by literal equality of the underlying word. -/
theorem gamma_eq_display (alpha r h q : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) :
    gamma alpha r h q eta = displayedGamma alpha r h q d.data := by
  rw [gamma, displayedGamma, Words.Npc.npcWUnit_eq_display alpha r h d]

/-- Exact lifting for the corrected arbitrary-unit procyclic-`N` presentation.  The eta bridge
is used exactly once, through `npcWUnit_eq_display`; all certificate work stays on `npcW`. -/
theorem exactLifting {alpha r h q : ℕ} {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (hsimp : Hsimp alpha r h q d.data) (hα : 1 ≤ alpha) (hqe : Even q)
    (hsep : StageSep alpha r h q d.data) (hZ : StageZ alpha r h q d.data)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemantics (gamma alpha r h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  rw [gamma_eq_display alpha r h q d]
  exact exactLiftingDisplayed hsimp hα hqe hsep hZ nuP

/-- Corrected exact lifting for the arbitrary-unit Npc presentation.  The display equality is
the only transport; both legacy R-stage premises have been discharged in
`exactLiftingDisplayedRN`. -/
theorem exactLiftingRN {alpha r h q : ℕ} {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (hsimp : Hsimp alpha r h q d.data) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma alpha r h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  rw [gamma_eq_display alpha r h q d]
  exact exactLiftingDisplayedRN hsimp hα hqe nuP

/-- Literal constructor regression: the RN theorem is about the corrected arbitrary-unit word
`npcWUnit`, not the retired draft presentation. -/
theorem exactLiftingRN_literal {alpha r h q : ℕ} {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (hsimp : Hsimp alpha r h q d.data) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN
      (GammaR (2 + 2 * h) q (Words.Npc.npcWUnit alpha r h eta))
      (2 * h + 2) q P nuP (standardNumerics (2 * h + 2)) :=
  exactLiftingRN d hsimp hα hqe nuP

/-- Transport only the numerical degree in the corrected RN semantics. -/
theorem exactLiftingRN_standard_congr {Gam : ProfiniteGrp} {n m q : ℕ}
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} (hn : n = m) :
    ExactLiftingSemanticsRN Gam n q P nuP (standardNumerics n) →
      ExactLiftingSemanticsRN Gam m q P nuP (standardNumerics m) := by
  subst m
  exact id

/-! ## Field-selector handoff -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- A selected `.Npc` row uses the corrected semantic constructor and its stored display
literally recovers the frozen certificate word. -/
theorem gammaR_eq_display_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) :
    GammaR S.semantic.degree q S.semantic.word =
      displayedGamma alpha r (handleCount FP (.Npc alpha r eta)) q
        (hbranch ▸ S.display).data := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      exact gamma_eq_display alpha r (handleCount FP (.Npc alpha r eta)) q display

/-- The field selector hands a chosen `.Npc` row directly to the exact-lifting constructor.
Validity supplies `1 ≤ alpha`; no uncorrected presentation enters the transport. -/
theorem exactLifting_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (hsimp : Hsimp alpha r (handleCount FP (.Npc alpha r eta)) q
      (hbranch ▸ S.display).data)
    (hqe : Even q)
    (hsep : StageSep alpha r (handleCount FP (.Npc alpha r eta)) q
      (hbranch ▸ S.display).data)
    (hZ : StageZ alpha r (handleCount FP (.Npc alpha r eta)) q
      (hbranch ▸ S.display).data)
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
        (GammaR (2 + 2 * handleCount FP (.Npc alpha r eta)) q
          (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta))
        (2 + 2 * handleCount FP (.Npc alpha r eta)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.Npc alpha r eta)))
      have hn : 2 * handleCount FP (.Npc alpha r eta) + 2 =
          2 + 2 * handleCount FP (.Npc alpha r eta) := by omega
      exact NCompact.exactLifting_standard_congr hn
        (exactLifting display hsimp (le_trans (by omega) valid.1) hqe hsep hZ nuP)

/-- The field selector hands a chosen `.Npc` row to the corrected RN constructor with no
legacy R-stage premises. -/
theorem exactLiftingRN_of_fieldSelection
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (hsimp : Hsimp alpha r (handleCount FP (.Npc alpha r eta)) q
      (hbranch ▸ S.display).data)
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
        (GammaR (2 + 2 * handleCount FP (.Npc alpha r eta)) q
          (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta))
        (2 + 2 * handleCount FP (.Npc alpha r eta)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.Npc alpha r eta)))
      have hn : 2 * handleCount FP (.Npc alpha r eta) + 2 =
          2 + 2 * handleCount FP (.Npc alpha r eta) := by omega
      exact exactLiftingRN_standard_congr hn
        (exactLiftingRN display hsimp (le_trans (by omega) valid.1) hqe nuP)

/-! ## The uniform pushed residue, and consumers that do not assume `Hsimp`

`Hsimp` above ranges over *all* finite markings at which the two resolved relators die, including
non-wild markings which need not extend across `GammaR`; nothing proves it, and the file's own
`PushedHsimp` commentary downstream records that the converse weakening is unavailable.  What the
campaign has actually proved is the *uniform pushed* residue: markings pushed forward from the
candidate group, one displayed word per finite target at the level `4 * Monoid.exponent C`,
established branch-by-branch in `NpcUnramifiedScalar` (unramified, scalar sub-branch needing `η` a
`2`-adic unit) and `NpcRamifiedBranch` (ramified).

⚠ Layering note.  The row-uniform name used by the other rows is `UniformPushedHsimp`
(`LSquare.UniformPushedHsimp`, `NCompact.UniformPushedHsimp`, ...), and on this row that name has
to be introduced in `GQ2/Dyadic/Instances/NpcActionImageDevissage.lean`, which **imports this
file**.  The statement is therefore written once, here, as `UniformHsimp`, and that file's
`NProcyclic.UniformPushedHsimp` is now a re-export of it rather than a second copy: the two names
denote the same proposition, and a term of either type is accepted where the other is expected.
Nothing here weakens or replaces the `Hsimp` clauses above; every one of them is kept. -/

/-- The coefficient-independent residue at the uniform level `4 * Monoid.exponent C`, in the
shape produced by action-image devissage.  This is the single statement of the row's uniform
residue; `NProcyclic.UniformPushedHsimp` in `NpcActionImageDevissage.lean` re-exports it under the
name the other rows use, and cannot host it because that file imports this one. -/
def UniformHsimp (alpha r h q : ℕ) (d : EtaData) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        StokesDuality
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
          (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) A

/-- The row's matched `(resolver, endpoint)` pair at the uniform level.  Only the finite target
`C` enters the level, so a coefficient devissage may keep the displayed word fixed. -/
theorem resolvesAt_and_endpoint_uniformHeis {alpha r h q : ℕ}
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha) (hqe : Even q) (d : EtaData) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
        (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) (HeisLift A C)
      ∧ IsStokesEndpoint (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) :=
  resolvesAt_and_endpoint_npcFamOf (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
    (orderOf_heisLift_dvd_four_mul hA₂ (fun g : C ↦ Monoid.order_dvd_exponent g))
    hα hqe d (fun _ ↦ 0)

/-- The scalar `H²` count required by the `R`-stage, from the uniform residue.  Same statement as
`cardH2`; only the residue binder changes. -/
theorem cardH2_of_uniformPushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    Nat.card (H2 ((displayedGamma alpha r h q d : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho alpha r h q d with hrho
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) (Additive ↥datum.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥datum.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥datum.T)) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) ×
            ElemDual (Additive ↥datum.T) => p.1 • p.2)
          = (fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)
            ∘ (fun p : ((displayedGamma alpha r h q d : Type)) ×
                ElemDual (Additive ↥datum.T) => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_uniformHeis (C := Base ⧸ datum.M)
    (A := Additive ↥datum.T) (radT_add_self datum) (alpha := alpha) (r := r) (h := h) (q := q)
    hα hqe d
  have hresH : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Base ⧸ datum.M)))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) := hb.1
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Base ⧸ datum.M)))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨heisScal, continuous_of_discreteTopology⟩
    exact hresH.pullback incl heisScal_injective
  have hresP : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Base ⧸ datum.M)))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom (WordLift (Additive ↥datum.T) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl heisPrim_injective
  have hresD : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Base ⧸ datum.M)))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M))
        (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
      ⟨heisDual, continuous_of_discreteTopology⟩
    exact hresH.pullback incl heisDual_injective
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective alpha r h q d) (fun _ => rfl))
    hresS hresP hresD hresH
    (hsimp (Base ⧸ datum.M) rho (Additive ↥datum.T) (radT_add_self datum))
    (hsimp (Base ⧸ datum.M) rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective alpha r h q d)

/-- The lift count at every recursion frame, from the uniform residue.  Same statement as
`liftsOver_card`. -/
theorem liftsOver_card_of_uniformPushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
        ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics (2 * h + 2)).mMult (Nat.card ↥RF.MB) := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk RF b F rho
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_uniformHeis (C := RF.YC) (A := Additive ↥RF.MB)
    (mb_add_self RF) (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent RF.YC))
      (WordLift (Additive ↥RF.MB) RF.YC) := by
    let incl : ContinuousMonoidHom (WordLift (Additive ↥RF.MB) RF.YC)
        (HeisLift (Additive ↥RF.MB) RF.YC) := ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (fun _ => rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ => rfl))
    (nCompact_degree h) hres
    (hsimp RF.YC rho.1.1 (Additive ↥RF.MB) (mb_add_self RF))
    hb.2

/-- The universal half-torsor identity, from the uniform residue.  Same statement as `lem86`. -/
theorem lem86_of_uniformPushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  letI := scalarActionZmodTwo (Bg ⧸ D.M)
  letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type))
      (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) ×
            ElemDual (Additive ↥D.T) => p.1 • p.2)
          = (fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)
            ∘ (fun p : ((displayedGamma alpha r h q d : Type)) ×
                ElemDual (Additive ↥D.T) => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_uniformHeis (C := Bg ⧸ D.M) (A := Additive ↥D.T)
    (radT_add_self D) (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hresH : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Bg ⧸ D.M)))
      (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) := hb.1
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Bg ⧸ D.M)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) := ⟨heisScal, continuous_of_discreteTopology⟩
    exact hresH.pullback incl heisScal_injective
  have hresP : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Bg ⧸ D.M)))
      (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom (WordLift (Additive ↥D.T) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) := ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hresH.pullback incl heisPrim_injective
  have hresD : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Bg ⧸ D.M)))
      (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) := by
    let incl : ContinuousMonoidHom (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) := ⟨heisDual, continuous_of_discreteTopology⟩
    exact hresH.pullback incl heisDual_injective
  exact lem86_of_variation (tComplement_nonempty D).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (fun V => hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ => rfl)) hresS hresP hresD hresH
    (hsimp (Bg ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    (hsimp (Bg ⧸ D.M) rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 hedge hrho

/-- Obstruction-zero separation from the uniform residue.  Same statement as
`homLift_of_obs_zeroRN`. -/
theorem homLift_of_obs_zeroRN_of_uniformPushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    [DistribMulAction ((displayedGamma alpha r h q d : Type)) (ZMod 2)]
    [ContinuousSMul ((displayedGamma alpha r h q d : Type)) (ZMod 2)]
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ x ∈ Blk.frattiniK, ∀ k ∈ Blk.K, x * k = k * x)
    (hR₂ : ∀ x ∈ Blk.frattiniK, x * x = 1)
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (htriv : ∀ (γ : (displayedGamma alpha r h q d : Type)) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((displayedGamma alpha r h q d : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE₂).TB)
    (hg : obs (blockFrameImpl T Blk hE₂) (blockRObstructionData T Blk hE₂)
      htriv hcard g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) Y,
      ∀ γ, (blockFrameImpl T Blk hE₂).piB (φ γ) = g.1.1 γ := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) := scalarActionZmodTwo (Y ⧸ Blk.K)
  have hb := resolvesAt_and_endpoint_uniformHeis (C := Y ⧸ Blk.K)
    (A := Additive ↥Blk.frattiniK) (RStageLocal.frattiniK_add_self hRK hR₂)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hresR : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Y ⧸ Blk.K)))
      (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) := by
    let incl : ContinuousMonoidHom (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))
        (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  have hresS : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Y ⧸ Blk.K)))
      (WordLift (ZMod 2) (Y ⧸ Blk.K)) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) (Y ⧸ Blk.K))
        (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) :=
      ⟨heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisScal_injective
  have hRleK : Blk.frattiniK ≤ Blk.K := SectionSeven.frattiniLike_le Blk.K
  set qKR : (blockFrameImpl T Blk hE₂).YB →* (Y ⧸ Blk.K) :=
    QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
      (by rw [Subgroup.comap_id]; exact hRleK) with hqKR
  set θ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Y ⧸ Blk.K) :=
    ⟨qKR.comp g.1.1.toMonoidHom,
      (continuous_of_discreteTopology (f := qKR)).comp g.1.1.continuous_toFun⟩ with hθ
  have hd : StokesDuality
      (fun i => θ (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Y ⧸ Blk.K)))
      (Additive ↥Blk.frattiniK) :=
    hsimp (Y ⧸ Blk.K) θ (Additive ↥Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂)
  refine homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂ htriv hcard b F g
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d))
    (isWildTwo_gammaGen_of_surjective g.1.1 g.1.2) hresS hresR ?_ hb.2 hg
  change StokesDuality (fun i => θ
      (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i))
    (resolvedFamily alpha r h q d (4 * Monoid.exponent (Y ⧸ Blk.K)))
    (Additive ↥Blk.frattiniK)
  exact hd

/-- The `R`-cocycle coefficient from the uniform residue.  Same statement as
`rCocycle_cardRN`. -/
theorem rCocycle_cardRN_of_uniformPushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE₂ : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ x ∈ Blk.frattiniK, ∀ k ∈ Blk.K, x * k = k * x)
    (hR₂ : ∀ x ∈ Blk.frattiniK, x * x = 1)
    (f₀ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) Y)
    (hf₀ : Function.Surjective f₀) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE₂) f₀) =
      zRN (blockFrameImpl T Blk hE₂) (standardNumerics (2 * h + 2)) := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) := scalarActionZmodTwo (Y ⧸ Blk.K)
  have hb := resolvesAt_and_endpoint_uniformHeis (C := Y ⧸ Blk.K)
    (A := Additive ↥Blk.frattiniK) (RStageLocal.frattiniK_add_self hRK hR₂)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hresR : ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Y ⧸ Blk.K)))
      (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) := by
    let incl : ContinuousMonoidHom (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K))
        (HeisLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  set θ : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.toMonoidHom,
      (continuous_of_discreteTopology (f := QuotientGroup.mk' Blk.K)).comp
        f₀.continuous_toFun⟩ with hθ
  have hθsurj : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective Blk.K).comp hf₀
  have hd : StokesDuality
      (fun i => θ (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) i))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (Y ⧸ Blk.K)))
      (Additive ↥Blk.frattiniK) :=
    hsimp (Y ⧸ Blk.K) θ (Additive ↥Blk.frattiniK)
      (RStageLocal.frattiniK_add_self hRK hR₂)
  exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀ hf₀
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
      (Words.Npc.npcW alpha r h d)) hresR
    (isWildTwo_gammaGen_of_surjective θ hθsurj) (nCompact_degree h) hd hb.2

/-- Corrected exact lifting for a displayed Npc presentation from the uniform residue.  Same
statement as `exactLiftingDisplayedRN`. -/
theorem exactLiftingDisplayedRN_of_uniformPushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (displayedGamma alpha r h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  refine ⟨liftsOver_card_of_uniformPushed hsimp hα hqe, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact lem86_of_uniformPushed hsimp hα hqe D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    haveI := scalarActionZmodTwo_continuousSMul
      ((displayedGamma alpha r h q d : Type))
    exact blockStageR136NK (standardNumerics (2 * h + 2)) T Blk hE₂
      (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hqe)
      (tfg_of_isAdmissibleMarkedPresentation
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
          (Words.Npc.npcW alpha r h d))) b F
      (fun g hg => homLift_of_obs_zeroRN_of_uniformPushed hsimp hα hqe T Blk hE₂ hRK hR₂ b F
        (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hqe) g hg)
      (fun f₀ => rCocycle_cardRN_of_uniformPushed hsimp hα hqe hE₂ hRK hR₂ f₀.1.1 f₀.1.2)

/-- Corrected exact lifting for the arbitrary-unit Npc presentation from the uniform residue.
Same statement as `exactLiftingRN`. -/
theorem exactLiftingRN_of_uniformPushed {alpha r h q : ℕ} {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) (hsimp : UniformHsimp alpha r h q d.data) (hα : 1 ≤ alpha)
    (hqe : Even q) {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma alpha r h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) := by
  rw [gamma_eq_display alpha r h q d]
  exact exactLiftingDisplayedRN_of_uniformPushed hsimp hα hqe nuP

/-- The field selector hands a chosen `.Npc` row to the corrected RN constructor with the uniform
residue as its only presentation-specific input.  Same statement as
`exactLiftingRN_of_fieldSelection`. -/
theorem exactLiftingRN_of_fieldSelection_uniformPushed
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    (S : FieldBranchSelection K FP Q W) {alpha r q : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (hsimp : UniformHsimp alpha r (handleCount FP (.Npc alpha r eta)) q
      (hbranch ▸ S.display).data)
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
        (GammaR (2 + 2 * handleCount FP (.Npc alpha r eta)) q
          (Words.Npc.npcWUnit alpha r (handleCount FP (.Npc alpha r eta)) eta))
        (2 + 2 * handleCount FP (.Npc alpha r eta)) q P nuP
        (standardNumerics (2 + 2 * handleCount FP (.Npc alpha r eta)))
      have hn : 2 * handleCount FP (.Npc alpha r eta) + 2 =
          2 + 2 * handleCount FP (.Npc alpha r eta) := by omega
      exact exactLiftingRN_standard_congr hn
        (exactLiftingRN_of_uniformPushed display hsimp (le_trans (by omega) valid.1) hqe nuP)

end

end GQ2.Dyadic.NProcyclic
