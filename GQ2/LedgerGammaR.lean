/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.MixedBObsR
import GQ2.RadicalEdge.GammaA

/-!
# The `Γ_R` ledger identity: `obs_R(varCoc u) = mixedB_R`

The edge-specific half of the Γ_R half-torsor proof.  For a primal crossed cocycle
`w : Z¹(Γ_R, T)` (packaged as `u : TCocycle`) and the shifted-edge dual cocycle
`φf : Z¹(Γ_R, T^∨)`, the `WordCoh2R`
obstruction of the variation class `varCoc u` equals the Fox–Heisenberg mixed pairing:
`obs_R(varCoc u) = mixedB_R (markC_R ρ) (evalR w) (evalR φf)`.

The proof is the near-definitional edge unfold `varCoc u (a,b) = kappaHeis (H a) (H b)` (where
`H` is the graph hom of the pair `(w, φf)` into `WordLift (T × T^∨) C`) fed into the two generic
cores `MixedBObsR.obs_inflation_R` and `MixedBObsR.mixedB_eq_relZPairR`.
-/

namespace GQ2

namespace SectionEight

namespace LedgerGammaR

-- `MixedBObs` supplies the *word-independent* `kappaHeis`/`mBaseMarking`, reused verbatim;
-- `MixedBObsR` supplies their two Roe relator readings.  `RadicalEdgeGammaA`'s namespace is a
-- misnomer: `cactFun`/`edge`/`conj_mem_T` carry no `Γ` in their variable block.
open CentralObstruction ContCoh WordCohBridgeR FoxH WordCoh2R MixedBObs MixedBObsR
  RadicalEdgeGammaA

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  (D : RadicalCoverData Bg) (S : TComplement D)
  (ρ : ContinuousMonoidHom GR (Bg ⧸ D.M))
  [DistribMulAction GR (Additive ↥D.T)]
  (hcompat : ∀ (γ : GR) (a : Additive ↥D.T), γ • a = ρ γ • a)
  [ContinuousSMul GR (Additive ↥D.T)]
  [DistribMulAction GR (ElemDual (Additive ↥D.T))]
  (hcompatD : ∀ (γ : GR) (l : ElemDual (Additive ↥D.T)), γ • l = ρ γ • l)
  [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]

/-- The graph hom of the pair `(w, φf)` into `WordLift (T × T^∨) C`. -/
noncomputable def pairHomR (w : Z1 GR (Additive ↥D.T)) (φf : Z1 GR (ElemDual (Additive ↥D.T))) :
    ContinuousMonoidHom GR (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
  wordHomR ρ (fun γ a => Prod.ext (by rw [Prod.smul_fst, Prod.smul_fst]; exact hcompat γ a.1)
      (by rw [Prod.smul_snd, Prod.smul_snd]; exact hcompatD γ a.2))
    ⟨fun γ => (w.1 γ, φf.1 γ),
      mem_Z1_iff.mpr ⟨((mem_Z1_iff.mp w.2).1).prodMk ((mem_Z1_iff.mp φf.2).1), fun γ δ =>
        Prod.ext ((mem_Z1_iff.mp w.2).2 γ δ) ((mem_Z1_iff.mp φf.2).2 γ δ)⟩⟩

omit [ContinuousSMul GR (Additive ↥D.T)] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [ContinuousSMul GR (ZMod 2)] in
include hcompat hcompatD in
theorem obs_varCoc_eq_mixedB_R
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
    (w : Z1 GR (Additive ↥D.T)) (φf : Z1 GR (ElemDual (Additive ↥D.T)))
    (hφf : ∀ (γ : GR) (s : Additive ↥D.T),
      (φf.1 γ) s = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s)))
    (u : TCocycle D ρ) (hu : ∀ γ, u.u γ = ((Additive.toMul (w.1 γ) : ↥D.T) : Bg)) :
    obs_R htriv ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩
      = mixedB_R (markC_R ρ) (evalR w) (evalR φf) := by
  set H := pairHomR D ρ hcompat hcompatD w φf with hH
  -- the near-definitional edge unfold: `varCoc u (a,b) = kappaHeis (H a) (H b)`
  have hunfold : ∀ a b : GR, varCoc D ρ S u (a, b) = kappaHeis.κ (H a) (H b) := by
    intro a b
    show edgeQ D S (ρ a) ⟨u.u b, u.mem b⟩ = (H a).u.2 ((H a).g • (H b).u.1)
    show edgeQ D S (ρ a) ⟨u.u b, u.mem b⟩ = (φf.1 a) (ρ a • w.1 b)
    rw [hφf, ← hcompat, inv_smul_smul]
    exact congrArg (edgeQ D S (ρ a)) (Subtype.ext (hu b))
  -- assemble via the two generic cores
  rw [obs_inflation_R htriv H kappaHeis ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ hunfold]
  have hmark : gammaGenR.map H.toMonoidHom = mBaseMarking (markC_R ρ) (evalR w) (evalR φf) := by
    rw [markC_R_map]; rfl
  rw [hmark, ← mixedB_eq_relZPairR]

omit [ContinuousSMul GR (Additive ↥D.T)] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [ContinuousSMul GR (ZMod 2)] in
include hcompat hcompatD in
/-- **The nonzero variation class** (the Γ_R half-torsor proof `hvar`).  If the mixed pairing of
the primal cocycle
`w` against the shifted-edge dual `φf` is nonzero, the variation class `[varCoc u]` is a nonzero
element of `H²(Γ_R, 𝔽₂)`: a trivial class would be a coboundary, on which `obs_R` — hence `mixedB_R`
by the ledger — vanishes. -/
theorem varCoc_class_ne_zero_R
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
    (w : Z1 GR (Additive ↥D.T)) (φf : Z1 GR (ElemDual (Additive ↥D.T)))
    (hφf : ∀ (γ : GR) (s : Additive ↥D.T),
      (φf.1 γ) s = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s)))
    (u : TCocycle D ρ) (hu : ∀ γ, u.u γ = ((Additive.toMul (w.1 γ) : ↥D.T) : Bg))
    (hne : mixedB_R (markC_R ρ) (evalR w) (evalR φf) ≠ 0) :
    H2mk GR (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ ≠ 0 := by
  intro h0
  apply hne
  rw [← obs_varCoc_eq_mixedB_R D S ρ hcompat hcompatD htriv w φf hφf u hu]
  exact AddMonoidHom.mem_ker.mp
    (obs_B2_eq_zero_R htriv ((QuotientAddGroup.eq_zero_iff _).mp h0))

/-! ## The shifted-edge dual cocycle (reconstruction of c3's `φf`)

`φf γ = (s ↦ ε̄(ρ γ)(γ⁻¹ · s))` is the dual 1-cocycle carrying the edge; it is nonzero in `H¹`
exactly when the cover does not descend (`NoDescent`).  This is c3's internal construction,
re-exposed so the ledger identity can consume it. -/

omit [DiscreteTopology Bg] [ContinuousSMul GR (Additive ↥D.T)]
  [DistribMulAction GR (ElemDual (Additive ↥D.T))] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
/-- Additivity of the shifted-edge functional `s ↦ ε̄(ρ γ)(γ⁻¹ · s)` in its argument. -/
private theorem exists_phiF_R_edgeQ_add (γ : GR) (s s' : Additive ↥D.T) :
    edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • (s + s')))
      = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s))
        + edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s')) := by
  have hmulcast : Additive.toMul ((γ⁻¹ : GR) • (s + s'))
      = Additive.toMul ((γ⁻¹ : GR) • s) * Additive.toMul ((γ⁻¹ : GR) • s') := by
    rw [smul_add]; rfl
  rw [hmulcast]
  exact edge_add D S (Quotient.out (ρ γ)) _ _

omit [DiscreteTopology Bg] [ContinuousSMul GR (Additive ↥D.T)]
  [DistribMulAction GR (ElemDual (Additive ↥D.T))] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
/-- The underlying dual 1-cochain of the shifted-edge cocycle: `γ ↦ (s ↦ ε̄(ρ γ)(γ⁻¹ · s))`. -/
private noncomputable def phiFfun (γ : GR) : ElemDual (Additive ↥D.T) :=
  (AddMonoidHom.mk' (fun s => edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s)))
    (exists_phiF_R_edgeQ_add D S ρ γ) : Additive ↥D.T →+ ZMod 2)

omit [DiscreteTopology Bg] [ContinuousSMul GR (Additive ↥D.T)]
  [DistribMulAction GR (ElemDual (Additive ↥D.T))] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
private theorem phiFfun_apply (γ : GR) (s : Additive ↥D.T) :
    phiFfun D S ρ γ s = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s)) := rfl

omit [DiscreteTopology Bg] [ContinuousSMul GR (Additive ↥D.T)]
  [DistribMulAction GR (ElemDual (Additive ↥D.T))] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
include hcompat in
/-- Transport of the `GR`-action on `T` through `ρ` to the conjugation action `cactFun`. -/
private theorem exists_phiF_R_toMul_smul (γ : GR) (s : Additive ↥D.T) :
    Additive.toMul (γ • s) = cactFun D (ρ γ) (Additive.toMul s) := by
  rw [hcompat]; exact cActT_toMul D (ρ γ) s

omit [DiscreteTopology Bg] [ContinuousSMul GR (Additive ↥D.T)]
  [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
include hcompat hcompatD in
/-- Pointwise formula for the dual `GR`-action: `(γ • l) a = l (γ⁻¹ · a)`. -/
private theorem exists_phiF_R_smul_apply (γ : GR) (l : ElemDual (Additive ↥D.T))
    (a : Additive ↥D.T) : (γ • l) a = l (γ⁻¹ • a) := by
  rw [hcompatD, ElemDual.smul_apply, hcompat γ⁻¹ a, map_inv]

omit [DiscreteTopology Bg] [ContinuousSMul GR (Additive ↥D.T)]
  [DistribMulAction GR (ElemDual (Additive ↥D.T))] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
include hcompat in
/-- The crossed additive relation for the shifted-edge functional across a product `γ * δ`. -/
private theorem exists_phiF_R_edgeQ_mul (γ δ : GR) (s : Additive ↥D.T) :
    edgeQ D S (ρ (γ * δ)) (Additive.toMul ((γ * δ)⁻¹ • s))
      = edgeQ D S (ρ γ) (Additive.toMul (γ⁻¹ • s))
        + edgeQ D S (ρ δ) (Additive.toMul (δ⁻¹ • (γ⁻¹ : GR) • s)) := by
  have hactGA := exists_phiF_R_toMul_smul D ρ hcompat
  have hγ : (QuotientGroup.mk (Quotient.out (ρ γ)) : Bg ⧸ D.M) = ρ γ :=
    QuotientGroup.out_eq' _
  have hδ : (QuotientGroup.mk (Quotient.out (ρ δ)) : Bg ⧸ D.M) = ρ δ :=
    QuotientGroup.out_eq' _
  have hγδrep : (QuotientGroup.mk (Quotient.out (ρ γ) * Quotient.out (ρ δ)) : Bg ⧸ D.M)
      = ρ (γ * δ) := by rw [QuotientGroup.mk_mul, hγ, hδ, map_mul]
  rw [edgeQ_eq D S (ρ (γ * δ)) hγδrep, edge_mul]
  have h2 : edge D S (Quotient.out (ρ γ))
        ⟨Quotient.out (ρ δ) * (Additive.toMul ((γ * δ)⁻¹ • s)).1 * (Quotient.out (ρ δ))⁻¹,
          conj_mem_T D (Quotient.out (ρ δ)) (Additive.toMul ((γ * δ)⁻¹ • s))⟩
      = edgeQ D S (ρ γ) (Additive.toMul (γ⁻¹ • s)) := by
    rw [edgeQ_eq D S (ρ γ) hγ]
    congr 1
    apply Subtype.ext
    show Quotient.out (ρ δ) * (Additive.toMul ((γ * δ)⁻¹ • s)).1 * (Quotient.out (ρ δ))⁻¹
        = (Additive.toMul (γ⁻¹ • s)).1
    have hsplit : Additive.toMul ((γ * δ)⁻¹ • s)
        = cactFun D (ρ δ⁻¹) (Additive.toMul (γ⁻¹ • s)) := by
      rw [hactGA, show ((γ * δ)⁻¹ : GR) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ, map_mul,
        cactFun_mul, ← hactGA]
    rw [hsplit]
    have hδinv : (QuotientGroup.mk ((Quotient.out (ρ δ))⁻¹) : Bg ⧸ D.M) = ρ δ⁻¹ := by
      rw [QuotientGroup.mk_inv, hδ, map_inv]
    rw [cactFun_eq D (ρ δ⁻¹) hδinv]
    group
  have h1 : edge D S (Quotient.out (ρ δ)) (Additive.toMul ((γ * δ)⁻¹ • s))
      = edgeQ D S (ρ δ) (Additive.toMul (δ⁻¹ • (γ⁻¹ : GR) • s)) := by
    rw [edgeQ_eq D S (ρ δ) hδ]
    congr 1
    rw [mul_inv_rev, mul_smul]
  rw [h1, h2]

omit [ContinuousSMul GR (Additive ↥D.T)] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
include hcompat hcompatD in
/-- The shifted-edge cochain is a dual 1-cocycle: `φf ∈ Z¹(Γ_R, T^∨)`. -/
private theorem phiFfun_mem_Z1 :
    phiFfun D S ρ ∈ Z1 GR (ElemDual (Additive ↥D.T)) := by
  haveI := discreteTopology_quotient D
  have hactGA := exists_phiF_R_toMul_smul D ρ hcompat
  have hsmulD := exists_phiF_R_smul_apply D ρ hcompat hcompatD
  have hφapp := phiFfun_apply D S ρ
  have hcrossZ := exists_phiF_R_edgeQ_mul D S ρ hcompat
  rw [mem_Z1_iff]
  refine ⟨?_, ?_⟩
  · have hΦadd : ∀ (c : Bg ⧸ D.M) (s s' : Additive ↥D.T),
        edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul (s + s')).1
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul (s + s'))⟩
          = edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩
            + edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
      intro c s s'
      have hsplit : (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul (s + s')).1
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul (s + s'))⟩ : ↥D.T)
          = (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩ : ↥D.T)
            * ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
        apply Subtype.ext
        show Quotient.out (c⁻¹ : Bg ⧸ D.M)
            * ((Additive.toMul s).1 * (Additive.toMul s').1)
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹
          = (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
        group
      rw [hsplit]
      exact edge_add D S (Quotient.out c) _ _
    have hfac : phiFfun D S ρ = (fun c : Bg ⧸ D.M =>
        (AddMonoidHom.mk' (fun s : Additive ↥D.T =>
          edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩) (hΦadd c)
          : ElemDual (Additive ↥D.T))) ∘ (fun γ : GR => (ρ γ : Bg ⧸ D.M)) := by
      funext γ
      refine DFunLike.ext _ _ fun s => ?_
      rw [hφapp]
      show edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s))
        = edgeQ D S (ρ γ) ⟨Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
            * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩
      refine congrArg (edgeQ D S (ρ γ)) (Subtype.ext ?_)
      rw [hactGA]
      show Quotient.out (ρ γ⁻¹) * (Additive.toMul s).1 * (Quotient.out (ρ γ⁻¹))⁻¹
        = Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
          * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹
      rw [map_inv]
    rw [hfac]
    exact continuous_of_discreteTopology.comp ρ.continuous_toFun
  · intro γ δ
    refine DFunLike.ext _ _ fun s => ?_
    have hz := hcrossZ γ δ s
    show (phiFfun D S ρ (γ * δ)) s = (phiFfun D S ρ γ + γ • phiFfun D S ρ δ) s
    rw [ElemDual.add_apply, hsmulD]
    simpa only [hφapp] using hz

omit [ContinuousSMul GR (Additive ↥D.T)] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
include hcompat hcompatD in
/-- The shifted-edge cocycle class is nonzero in `H¹` when the cover fails to descend. -/
private theorem phiFfun_ne_zero (hρ : Function.Surjective ρ) (hedge : D.NoDescent) :
    H1mk GR (ElemDual (Additive ↥D.T))
        ⟨phiFfun D S ρ, phiFfun_mem_Z1 D S ρ hcompat hcompatD⟩ ≠ 0 := by
  have hsmulD := exists_phiF_R_smul_apply D ρ hcompat hcompatD
  have hactGA := exists_phiF_R_toMul_smul D ρ hcompat
  have hφapp := phiFfun_apply D S ρ
  intro h0
  have hmem : phiFfun D S ρ ∈ B1 GR (ElemDual (Additive ↥D.T)) := by
    have h1 := (QuotientAddGroup.eq_zero_iff _).mp h0
    rwa [AddSubgroup.mem_addSubgroupOf] at h1
  obtain ⟨lam, hlam⟩ := hmem
  set ℓ : ↥D.T → ZMod 2 :=
    fun t => (lam : ElemDual (Additive ↥D.T)) (Additive.ofMul t) with hℓdef
  have hℓadd : ∀ t t' : ↥D.T, ℓ (t * t') = ℓ t + ℓ t' := by
    intro t t'
    show (lam : ElemDual (Additive ↥D.T)) (Additive.ofMul (t * t')) = _
    rw [show Additive.ofMul (t * t')
        = Additive.ofMul t + Additive.ofMul t' from rfl, map_add]
  refine (not_noDescent_of_edge_trivial D S ℓ hℓadd ?_) hedge
  intro b t
  obtain ⟨γ, hγ⟩ := hρ (QuotientGroup.mk b)
  have hlamγ := congrFun hlam γ
  have hval := congrArg
    (fun ψ : ElemDual (Additive ↥D.T) => ψ ((γ : GR) • Additive.ofMul t)) hlamγ
  have hL : (dZero GR (ElemDual (Additive ↥D.T)) lam γ) ((γ : GR) • Additive.ofMul t)
      = lam (Additive.ofMul t) - lam ((γ : GR) • Additive.ofMul t) := by
    show ((γ • lam - lam : ElemDual (Additive ↥D.T))) ((γ : GR) • Additive.ofMul t) = _
    rw [ElemDual.sub_apply, hsmulD, inv_smul_smul]
  have hR : (phiFfun D S ρ γ) ((γ : GR) • Additive.ofMul t) = edge D S b t := by
    rw [hφapp, ← edgeQ_eq D S (ρ γ) hγ.symm t]
    refine congrArg (edgeQ D S (ρ γ)) ?_
    exact inv_smul_smul γ (Additive.ofMul t)
  rw [hL, hR] at hval
  have hbt : Additive.ofMul (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T)
      = (γ : GR) • Additive.ofMul t := by
    have hcast : (γ : GR) • Additive.ofMul t = Additive.ofMul (cactFun D (ρ γ) t) :=
      Additive.toMul.injective (by rw [hactGA]; rfl)
    rw [hcast]
    exact congrArg Additive.ofMul (Subtype.ext (cactFun_eq D (ρ γ) hγ.symm t).symm)
  show edge D S b t = ℓ (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T) + ℓ t
  rw [hℓdef]
  show edge D S b t
    = lam (Additive.ofMul (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T)) + lam (Additive.ofMul t)
  rw [hbt, ← hval]
  exact (by decide : ∀ a e : ZMod 2, a - e = e + a) _ _

omit [ContinuousSMul GR (Additive ↥D.T)] [ContinuousSMul GR (ElemDual (Additive ↥D.T))]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)] in
include hcompat hcompatD in
theorem exists_phiF_R (hρ : Function.Surjective ρ) (hedge : D.NoDescent) :
    ∃ φf : Z1 GR (ElemDual (Additive ↥D.T)),
      (∀ (γ : GR) (s : Additive ↥D.T),
        (φf.1 γ) s = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GR) • s)))
      ∧ H1mk GR (ElemDual (Additive ↥D.T)) φf ≠ 0 := by
  exact ⟨⟨phiFfun D S ρ, phiFfun_mem_Z1 D S ρ hcompat hcompatD⟩, fun _ _ => rfl,
    phiFfun_ne_zero D S ρ hcompat hcompatD hρ hedge⟩

end LedgerGammaR

end SectionEight

end GQ2
