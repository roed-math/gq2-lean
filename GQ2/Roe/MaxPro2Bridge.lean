/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Tame
public import GQ2.Roe.DRAbelianization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The maximal pro-2 quotient of `Γ_R` is `D_R`  (Roe note §3.1, Lemma 3.1 ⟦lem:pro2word⟧)

The `Γ_R`-half of the note's Lemma 3.1: the maximal pro-2 quotient of the Roe candidate group
`Γ_R = F₄ ⧸ N_R` (`GQ2/Roe/GammaR.lean`) collapses to the three-generator one-relator pro-2 group
`D_R` (`GQ2/Roe/DRPresentation.lean`), verbatim

```
\DR=
\angles{s,x,y\ \middle|\
r_2=(x^s)^{-1}x^{-3}y^2[y,y^s]=1}_{\mathrm{pro}\text{-}2},
```

matching the marked generators `σ ↦ s = drS`, `τ ↦ 1`, `x₀ ↦ x = drX`, `x₁ ↦ y = drY`.  This is
the Roe-candidate counterpart of `GQ2.SectionThree.maxAEquiv` (the `Γ_A`-side identification
`Γ_A(2) ≅ Π` of Prop 3.10, `GQ2/BoundaryConstruction.lean`), and it is proved by the same
architecture, one presentation over: forward via the maximal-pro-2 universal property fed by
`R`-admissibility at every finite 2-group level of `D_R`, backward via `D_R`'s own universal
property `drLiftHom` (ticket R7), mutual inverse by density.

## The word collapse (keystone)

The analytical heart is `wildValueR_eq_drWord_of_powOmega2_id`: **in a 2-group** (where `ω₂` acts
as the identity, `powOmega2_eq_self_of_orderOf_two_pow`), the finite Roe wild value `r_R` of a
marking `(σ, 1, x₀, x₁)` with `τ = 1` is *exactly* `drWord σ x₀ x₁` — the two `ω₂`-powers of `r_R`
(inside `aR = (x₀⁻³τ)^{ω₂}` and inside `σ₂ = σ^{ω₂}`) become the bare `(x₀³)⁻¹` and `σ`, so

  `r_R = (x₀^σ)⁻¹ · (x₀³)⁻¹ · x₁² · [x₁, x₁^σ] = drWord σ x₀ x₁`.

`τ` dies pro-2 (`maxProPMk_gammaTauR`) exactly as on the `Γ_A` side: the tame relation forces `τ`
to odd order (`Tame.tame_odd_order`), which in a 2-group is trivial.

## The two maps

* forward `PhiMaxR : Γ_R(2) → D_R` — the descent of the classifier `σ,τ,x₀,x₁ ↦ s,1,x,y` through
  the maximal-pro-2 quotient (`Π` is pro-2, and each finite 2-group level of `D_R` receives an
  `R`-admissible marking: `NR_le_ker` + the collapse + `dr_relation`);
* backward `PsiMaxR : D_R → Γ_R(2)` — `drLiftHom` at the images of `σ, x₀, x₁` in `Γ_R(2)`, whose
  relator obligation `drWord_maxR_eq_one` is the collapse + `quotientMk_wildRelatorR_eq_one` pushed
  into the pro-2 quotient (`τ` dead by `maxProPMk_gammaTauR`).

`dr_hom_ext` (R8) and `topGen_maxR` (from `freeProfinite_topGen` through the two quotient
surjections) give the mutual-inverse extensionality; `maxPro2Bridge` bundles the result.

## Consumers (R15/R32)

`maxPro2Bridge` and its generator-image lemmas `maxPro2Bridge_gammaSigmaR/…` are the pro-2 leg of
the boundary bundle: R15's `markedPro2_R` (`GQ2/Roe/MarkedPro2.lean`) composes this bridge with the
marked iso `G_{ℚ₂}(2) ≅ Γ_R(2)`, and the unramified-marking compatibility `ν_R = ν_{D_R} ∘ bridge`
is read off the generator images (`nuR_gammaSigma`/`nuDR_drS` and friends).  No axiom, no B-Lab
hypothesis: this half of Lemma 3.1 is unconditional (`#print axioms` = the standard three).
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

open SectionThree

/-! ## Profinite instances on the raw quotient `Γ_R = F₄ ⧸ N_R`

The bundled `GammaR` (`GQ2/Roe/GammaR.lean`) has instance-synthesis issues (R6 design note), so —
matching R6's `GQ2/Roe/Tame.lean` — everything below uses the raw quotient `F₄ ⧸ N_R`.  Its
`CompactSpace` and `IsTopologicalGroup` instances are unconditional, but `T2Space` and
`TotallyDisconnectedSpace` are guarded by `[IsClosed N_R]`; we discharge that once here (via
`NR_isClosed`) so that `maxProPQuotient 2 (F₄ ⧸ N_R)` elaborates without a local `haveI` at every
statement. -/

local instance instT2SpaceQuotNR : T2Space (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  inferInstance

local instance instTDSpaceQuotNR : TotallyDisconnectedSpace (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  inferInstance

/-! ## The word collapse at `τ = 1` in a 2-group (keystone) -/

/-- On a `2`-group `ω₂` acts as the identity: every element has `2`-power order
(`IsPGroup.iff_orderOf`), so `powOmega2 g = g` (`powOmega2_eq_self_of_orderOf_two_pow`).  The
elementwise face of "`ω₂ ≡ 1` on the 2-part", specialised to a group all of whose elements are
2-primary. -/
theorem powOmega2_id_of_isPGroup {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) (g : Q) :
    powOmega2 g = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) g
  exact powOmega2_eq_self_of_orderOf_two_pow hk

/-- **The word collapse** ⟦lem:pro2word⟧ (keystone).  In a group where `ω₂` acts as the identity
(automatic in a 2-group, `powOmega2_id_of_isPGroup`), the finite Roe wild value `r_R` of the marking
`(σ, 1, x₀, x₁)` with `τ = 1` equals the pro-2 relator word `drWord σ x₀ x₁`: the `ω₂`-power in
`aR = (x₀⁻³τ)^{ω₂}` collapses to `(x₀³)⁻¹` (with `τ = 1`) and the `ω₂`-power in `σ₂ = σ^{ω₂}`
collapses to `σ`, leaving

  `r_R = (x₀^σ)⁻¹ · (x₀³)⁻¹ · x₁² · [x₁, x₁^σ] = drWord σ x₀ x₁`.

The Roe-candidate counterpart of `GQ2.SectionThree.wildRelWord_eq`
(`GQ2/BoundaryConstruction.lean`). -/
theorem wildValueR_eq_drWord_of_powOmega2_id {G : Type*} [Group G] (σ x₀ x₁ : G)
    (ho : ∀ g : G, powOmega2 g = g) :
    (Marking.mk σ 1 x₀ x₁).wildValueR = drWord σ x₀ x₁ := by
  have haR : (Marking.mk σ 1 x₀ x₁).aR = (x₀ ^ 3)⁻¹ := by
    show powOmega2 ((x₀ ^ 3)⁻¹ * 1) = (x₀ ^ 3)⁻¹
    rw [mul_one]; exact ho _
  have hsig : (Marking.mk σ 1 x₀ x₁).sigma2 = σ := ho σ
  have hcR : (Marking.mk σ 1 x₀ x₁).cR = commP x₁ (conjP x₁ σ) := by
    rw [Marking.cR, Marking.y1R, hsig]
  rw [Marking.wildValueR, haR, hcR, drWord]

/-! ## Topological generation of `D_R` in discrete quotients -/

/-- In every discrete continuous quotient of `D_R`, the images of `s, x, y` generate — the
pushforward of `dr_topGen` (R8).  Roe counterpart of `GQ2.SectionThree.gen_piBd_quotient`. -/
theorem gen_DR_quotient {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] (f : (DR : Type) →* H) (hcont : Continuous f)
    (hsurj : Function.Surjective f) : Subgroup.closure {f drS, f drX, f drY} = ⊤ := by
  have h := topGen_map f hcont hsurj dr_topGen
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at h
  exact gen_of_topGen_discrete h

/-! ## The forward descent `Γ_R → D_R` -/

/-- The pro-2 classifier `F₄ ⟶ D_R`: `σ ↦ s = drS, τ ↦ 1, x₀ ↦ x = drX, x₁ ↦ y = drY`.  Roe
counterpart of `GQ2.SectionThree.piClassifier`. -/
noncomputable def drClassifier : FreeProfiniteGroup (Fin 4) ⟶ DR :=
  (FreeProfiniteGroup.homEquiv (Fin 4) DR).symm ![drS, 1, drX, drY]

@[simp] private lemma drClassifier_sigma : drClassifier.hom.toMonoidHom univMarking.σ = drS :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] private lemma drClassifier_tau : drClassifier.hom.toMonoidHom univMarking.τ = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] private lemma drClassifier_x0 : drClassifier.hom.toMonoidHom univMarking.x₀ = drX :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _
@[simp] private lemma drClassifier_x1 : drClassifier.hom.toMonoidHom univMarking.x₁ = drY :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- Through every finite 2-group level of `D_R`, the marking pushed from the pro-2 classifier is
`R`-admissible: `τ ↦ 1`, the Roe wild value collapses to `drWord`, which vanishes by `dr_relation`,
and generation / 2-core are automatic in the 2-group.  Roe counterpart of
`GQ2.SectionThree.isAdmissible_piClassifier_level`. -/
theorem isAdmissibleR_drClassifier_level (V : OpenNormalSubgroup (DR : Type)) :
    (univMarking.map ((QuotientGroup.mk' V.toSubgroup).comp
      drClassifier.hom.toMonoidHom)).AdmissibleR := by
  haveI : Finite ((DR : Type) ⧸ V.toSubgroup) := inferInstance
  have h2grp : IsPGroup 2 ((DR : Type) ⧸ V.toSubgroup) := isProP_DR V
  set q : (DR : Type) →* (DR : Type) ⧸ V.toSubgroup := QuotientGroup.mk' V.toSubgroup with hq
  set f : FreeProfiniteGroup (Fin 4) →* (DR : Type) ⧸ V.toSubgroup :=
    q.comp drClassifier.hom.toMonoidHom with hf
  have hσ : (univMarking.map f).σ = q drS := congrArg q drClassifier_sigma
  have hτ : (univMarking.map f).τ = 1 := (congrArg q drClassifier_tau).trans (map_one q)
  have hx0 : (univMarking.map f).x₀ = q drX := congrArg q drClassifier_x0
  have hx1 : (univMarking.map f).x₁ = q drY := congrArg q drClassifier_x1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Generates
    rw [Marking.Generates, hσ, hτ, hx0, hx1]
    have hgen : Subgroup.closure {q drS, q drX, q drY} = ⊤ :=
      gen_DR_quotient q continuous_quot_mk (QuotientGroup.mk'_surjective _)
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_mono fun z hz => ?_
    rcases hz with rfl | rfl | rfl <;> simp
  · -- TameRel (`τ = 1`)
    rw [Marking.TameRel, hσ, hτ]
    simp [conjP]
  · -- WildRelR via the collapse + `dr_relation`
    show (univMarking.map f).wildValueR = 1
    have ht : univMarking.map f = Marking.mk (q drS) 1 (q drX) (q drY) := by
      rw [show univMarking.map f = Marking.mk (univMarking.map f).σ (univMarking.map f).τ
          (univMarking.map f).x₀ (univMarking.map f).x₁ from rfl, hσ, hτ, hx0, hx1]
    rw [ht, wildValueR_eq_drWord_of_powOmega2_id _ _ _ (powOmega2_id_of_isPGroup h2grp),
      ← map_drWord, dr_relation, map_one]
  · -- Pro2Core: subgroups of the finite 2-group are 2-groups
    rw [Marking.Pro2Core, hx0, hx1]
    exact h2grp.to_subgroup _

/-- `N_R` is contained in the kernel of the pro-2 classifier (each finite level is `R`-admissible,
`isAdmissibleR_drClassifier_level`, so `NR_le_ker` applies).  Roe counterpart of
`GQ2.SectionThree.NA_le_ker_piClassifier`. -/
theorem NR_le_ker_drClassifier : NR ≤ drClassifier.hom.toMonoidHom.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine eq_one_of_forall_mem_openNormalSubgroup fun V => ?_
  haveI : Finite ((DR : Type) ⧸ V.toSubgroup) := inferInstance
  set f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) ((DR : Type) ⧸ V.toSubgroup) :=
    (quotientMk V.toSubgroup).comp drClassifier.hom with hf
  have hadm : (univMarking.map f.toMonoidHom).AdmissibleR := isAdmissibleR_drClassifier_level V
  exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp (NR_le_ker f hadm hx))

/-- The descent `φ_{D_R} : Γ_R → D_R` (`σ ↦ s, τ ↦ 1, x₀ ↦ x, x₁ ↦ y`).  Roe counterpart of
`GQ2.SectionThree.phiP`. -/
noncomputable def phiDR : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) (DR : Type) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  quotientLift NR drClassifier.hom NR_le_ker_drClassifier

@[simp] lemma phiDR_gammaSigmaR : phiDR gammaSigmaR = drS := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiDR (quotientMk NR univMarking.σ) = drS
  exact (quotientLift_quotientMk _ _ _ _).trans drClassifier_sigma

@[simp] lemma phiDR_gammaTauR : phiDR gammaTauR = 1 := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiDR (quotientMk NR univMarking.τ) = 1
  exact (quotientLift_quotientMk _ _ _ _).trans drClassifier_tau

@[simp] lemma phiDR_gammaX0R : phiDR gammaX0R = drX := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiDR (quotientMk NR univMarking.x₀) = drX
  exact (quotientLift_quotientMk _ _ _ _).trans drClassifier_x0

@[simp] lemma phiDR_gammaX1R : phiDR gammaX1R = drY := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiDR (quotientMk NR univMarking.x₁) = drY
  exact (quotientLift_quotientMk _ _ _ _).trans drClassifier_x1

/-- The forward map `Φ : Γ_R(2) → D_R`, the descent of `φ_{D_R}` through the maximal pro-2 quotient
(`D_R` is pro-2, so `φ_{D_R}` kills the pro-2 kernel).  Roe counterpart of
`GQ2.SectionThree.PhiMax`. -/
noncomputable def PhiMaxR :
    ContinuousMonoidHom (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) (DR : Type) :=
  quotientLift (proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) phiDR
    (proPKernel_le_ker isProP_DR phiDR)

@[simp] private lemma PhiMaxR_mk_gammaSigmaR :
    PhiMaxR (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR) = drS :=
  (quotientLift_quotientMk _ _ _ _).trans phiDR_gammaSigmaR

@[simp] private lemma PhiMaxR_mk_gammaTauR :
    PhiMaxR (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR) = 1 :=
  (quotientLift_quotientMk _ _ _ _).trans phiDR_gammaTauR

@[simp] private lemma PhiMaxR_mk_gammaX0R :
    PhiMaxR (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R) = drX :=
  (quotientLift_quotientMk _ _ _ _).trans phiDR_gammaX0R

@[simp] private lemma PhiMaxR_mk_gammaX1R :
    PhiMaxR (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R) = drY :=
  (quotientLift_quotientMk _ _ _ _).trans phiDR_gammaX1R

/-! ## `τ` dies in the maximal pro-2 quotient of `Γ_R` -/

/-- The marked tame relation holds in `Γ_R`: the tame relator dies in `N_R`
(`quotientMk_NR_tameRelator_eq_one`).  Roe counterpart of
`GQ2.SectionThree.gammaMarking_tameRel`. -/
theorem gammaMarkingR_tameRel : conjP gammaTauR gammaSigmaR = gammaTauR ^ 2 := by
  have h : quotientMk NR univMarking.tameRelator = 1 := quotientMk_NR_tameRelator_eq_one
  have e : quotientMk NR univMarking.tameRelator
      = conjP gammaTauR gammaSigmaR * (gammaTauR ^ 2)⁻¹ := by
    rw [Marking.tameRelator]
    simp only [map_mul, map_inv, map_pow]
    rfl
  exact mul_inv_eq_one.mp (e.symm.trans h)

/-- **`τ` dies in the maximal pro-2 quotient of `Γ_R`** (⟦lem:pro2word⟧; ⟦lem:tame⟧ restricted to
the pro-2 quotient): in every finite 2-group level the image of `τ` has both odd order (tame
relation, `Tame.tame_odd_order`) and 2-power order, hence is trivial.  Roe counterpart of
`GQ2.SectionThree.maxProPMk_gammaTau`. -/
theorem maxProPMk_gammaTauR :
    maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : gammaTauR ∈ proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) := by
    rw [proPKernel, Subgroup.mem_iInf]
    rintro ⟨U, hU⟩
    haveI : Finite ((FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ U.toSubgroup) := inferInstance
    set q : (FreeProfiniteGroup (Fin 4) ⧸ NR) →* (FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ U.toSubgroup :=
      QuotientGroup.mk' U.toSubgroup with hq
    have hrel : conjP (q gammaTauR) (q gammaSigmaR) = (q gammaTauR) ^ 2 := by
      have h := congrArg (⇑q) gammaMarkingR_tameRel
      rwa [Marking.map_conjP, map_pow] at h
    have hodd : Odd (orderOf (q gammaTauR)) :=
      Tame.tame_odd_order (orderOf_pos (q gammaSigmaR)).ne' hrel
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) (q gammaTauR)
    have h1 : orderOf (q gammaTauR) = 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hk
      · exfalso
        have h2dvd : 2 ∣ orderOf (q gammaTauR) := hk ▸ dvd_pow_self 2 hpos.ne'
        rw [Nat.odd_iff] at hodd; omega
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
  exact (quotientMk_eq_one_iff (proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR))).mpr hmem

/-! ## The backward relator kill and the backward descent `D_R → Γ_R(2)` -/

/-- **The pro-2 relator holds in `Γ_R(2)`** ⟦lem:pro2word⟧: `drWord` vanishes at the images of
`σ, x₀, x₁`.  In every finite 2-group level the Roe wild relation holds (`wildRelatorR` dies in
`Γ_R`, `quotientMk_wildRelatorR_eq_one`, transported by `map_wildRelatorR`) and `τ ↦ 1`
(`maxProPMk_gammaTauR`), so the collapse gives `drWord = 1`; separated by finite quotients, it
vanishes in the limit.  Roe counterpart of `GQ2.SectionThree.piRelatorWord_maxA_eq_one`; this is the
relator obligation of the backward `drLiftHom`. -/
theorem drWord_maxR_eq_one :
    drWord (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR)
        (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R)
        (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mkR := maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) with hmkR
  refine eq_one_of_forall_mem_openNormalSubgroup fun V => ?_
  haveI : Finite (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ V.toSubgroup) :=
    inferInstance
  set q : ContinuousMonoidHom (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR))
      (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ V.toSubgroup) :=
    quotientMk V.toSubgroup with hq
  set g : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4))
      (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ V.toSubgroup) :=
    q.comp (mkR.comp (quotientMk NR)) with hg
  have h2grp : IsPGroup 2 (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ V.toSubgroup) :=
    isProP_maxProPQuotient V
  -- `τ ↦ 1` at this level
  have hgτ : g univMarking.τ = 1 := by
    show q (mkR (quotientMk NR univMarking.τ)) = 1
    rw [show mkR (quotientMk NR univMarking.τ) = mkR gammaTauR from rfl, maxProPMk_gammaTauR,
      map_one]
  -- the Roe wild relator dies, so `wildValueR` of the pushed marking is `1`
  have h0w : quotientMk NR univMarking.wildRelatorR = (1 : FreeProfiniteGroup (Fin 4) ⧸ NR) :=
    quotientMk_wildRelatorR_eq_one
  have hkill : g.toMonoidHom univMarking.wildRelatorR = 1 := by
    show q (mkR (quotientMk NR univMarking.wildRelatorR)) = 1
    rw [h0w, map_one, map_one]
  have hwild : (univMarking.map g.toMonoidHom).wildValueR = 1 := by
    rw [← Marking.map_wildRelatorR g univMarking]; exact hkill
  -- the pushed marking is `(σ̄, 1, x̄₀, x̄₁)`
  have ht : univMarking.map g.toMonoidHom
      = Marking.mk (q (mkR gammaSigmaR)) 1 (q (mkR gammaX0R)) (q (mkR gammaX1R)) := by
    have cσ : g.toMonoidHom univMarking.σ = q (mkR gammaSigmaR) := by rw [hg]; rfl
    have cx0 : g.toMonoidHom univMarking.x₀ = q (mkR gammaX0R) := by rw [hg]; rfl
    have cx1 : g.toMonoidHom univMarking.x₁ = q (mkR gammaX1R) := by rw [hg]; rfl
    rw [show univMarking.map g.toMonoidHom = Marking.mk (g.toMonoidHom univMarking.σ)
        (g.toMonoidHom univMarking.τ) (g.toMonoidHom univMarking.x₀)
        (g.toMonoidHom univMarking.x₁) from rfl, Marking.mk.injEq]
    exact ⟨cσ, hgτ, cx0, cx1⟩
  rw [ht, wildValueR_eq_drWord_of_powOmega2_id _ _ _ (powOmega2_id_of_isPGroup h2grp)] at hwild
  -- push through the finite quotient and read off membership
  refine (quotientMk_eq_one_iff V.toSubgroup).mp ?_
  rw [map_drWord]
  exact hwild

/-- The backward map `Ψ : D_R → Γ_R(2)`, via `D_R`'s universal property `drLiftHom` (R7) at the
images of `σ, x₀, x₁` in the (pro-2) quotient `Γ_R(2)`; the relator obligation is
`drWord_maxR_eq_one`.  Roe counterpart of `GQ2.SectionThree.PsiMax`. -/
noncomputable def PsiMaxR :
    ContinuousMonoidHom (DR : Type) (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) :=
  drLiftHom isProP_maxProPQuotient
    ![maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR,
      maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R,
      maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R]
    drWord_maxR_eq_one

@[simp] private lemma PsiMaxR_drS :
    PsiMaxR drS = maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR :=
  drLiftHom_S _ _ _
@[simp] private lemma PsiMaxR_drX :
    PsiMaxR drX = maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R :=
  drLiftHom_X _ _ _
@[simp] private lemma PsiMaxR_drY :
    PsiMaxR drY = maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R :=
  drLiftHom_Y _ _ _

/-! ## Topological generation of `Γ_R(2)` and the two composites -/

/-- `Γ_R(2)` is topologically generated by the images of the four marked generators — the
pushforward of `freeProfinite_topGen` (R8) through the two quotient surjections `F₄ ↠ Γ_R ↠ Γ_R(2)`.
Roe counterpart of `GQ2.SectionThree.topGen_maxA`. -/
theorem topGen_maxR :
    (Subgroup.closure {maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR,
        maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR,
        maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R,
        maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R}).topologicalClosure = ⊤ := by
  have h := topGen_map
    (f := ((maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).comp (quotientMk NR)).toMonoidHom)
    ((maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).comp (quotientMk NR)).continuous_toFun
    ((quotientMk_surjective (proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR))).comp
      (quotientMk_surjective NR))
    (topGen_freeProfiniteGroup (Fin 4))
  have h1 : (⇑((maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).comp (quotientMk NR)).toMonoidHom)
      '' Set.range (FreeProfiniteGroup.of (X := Fin 4))
      = {maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR,
         maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR,
         maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R,
         maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R} := by
    rw [← Set.range_comp]
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rwa [h1] at h

/-- `Φ ∘ Ψ = id` on `D_R` (both fix `s, x, y`; `dr_hom_ext`). -/
theorem PhiMaxR_PsiMaxR (x : (DR : Type)) : PhiMaxR (PsiMaxR x) = x := by
  have h : PhiMaxR.comp PsiMaxR = ContinuousMonoidHom.id (DR : Type) :=
    dr_hom_ext _ _ (by simp) (by simp) (by simp)
  exact DFunLike.congr_fun h x

/-- `Ψ ∘ Φ = id` on `Γ_R(2)` (checked on the four marked generator images; `topGen_maxR`, `τ`
dead by `maxProPMk_gammaTauR`). -/
theorem PsiMaxR_PhiMaxR (x : maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) :
    PsiMaxR (PhiMaxR x) = x := by
  have h := monoidHom_eq_of_topGen
    (f := PsiMaxR.toMonoidHom.comp PhiMaxR.toMonoidHom) (g := MonoidHom.id _)
    (by rw [MonoidHom.coe_comp]; exact PsiMaxR.continuous_toFun.comp PhiMaxR.continuous_toFun)
    continuous_id topGen_maxR ?_
  · exact h x
  · rintro z (rfl | rfl | rfl | rfl) <;> simp [maxProPMk_gammaTauR]

/-! ## The marked isomorphism `Γ_R(2) ≅ D_R`  (⟦lem:pro2word⟧, `Γ_R` half of Lemma 3.1) -/

/-- **The maximal pro-2 quotient of `Γ_R` is `D_R`** ⟦lem:pro2word⟧ (the `Γ_R` half of the note's
Lemma 3.1): a continuous isomorphism `Γ_R(2) ≅ D_R` matching the marked generators
`σ ↦ s, τ ↦ 1, x₀ ↦ x, x₁ ↦ y`.  Roe counterpart of `GQ2.SectionThree.maxAEquiv`; the pro-2 leg of
the boundary bundle that R15's `markedPro2_R` and R32 consume. -/
noncomputable def maxPro2Bridge :
    ContinuousMulEquiv (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) (DR : Type) where
  toFun := PhiMaxR
  invFun := PsiMaxR
  left_inv := PsiMaxR_PhiMaxR
  right_inv := PhiMaxR_PsiMaxR
  map_mul' := map_mul PhiMaxR
  continuous_toFun := PhiMaxR.continuous_toFun
  continuous_invFun := PsiMaxR.continuous_toFun

/-! ## Generator-image lemmas (the marked compatibility hooks R15/R32 consume) -/

@[simp] theorem maxPro2Bridge_gammaSigmaR :
    maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR) = drS :=
  PhiMaxR_mk_gammaSigmaR

@[simp] theorem maxPro2Bridge_gammaTauR :
    maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR) = 1 :=
  PhiMaxR_mk_gammaTauR

@[simp] theorem maxPro2Bridge_gammaX0R :
    maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R) = drX :=
  PhiMaxR_mk_gammaX0R

@[simp] theorem maxPro2Bridge_gammaX1R :
    maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R) = drY :=
  PhiMaxR_mk_gammaX1R

@[simp] theorem maxPro2Bridge_symm_drS :
    maxPro2Bridge.symm drS = maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR :=
  PsiMaxR_drS

@[simp] theorem maxPro2Bridge_symm_drX :
    maxPro2Bridge.symm drX = maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R :=
  PsiMaxR_drX

@[simp] theorem maxPro2Bridge_symm_drY :
    maxPro2Bridge.symm drY = maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R :=
  PsiMaxR_drY

/-- **The bridge with its marked generator images** ⟦lem:pro2word⟧, in the existence shape of
`GQ2.SectionThree.prop_3_10_gammaA_proved` — the interface R15/R32 consume for the pro-2 leg. -/
theorem maxPro2Bridge_spec :
    ∃ e : ContinuousMulEquiv (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) (DR : Type),
      e (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR) = drS ∧
      e (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR) = 1 ∧
      e (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R) = drX ∧
      e (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R) = drY :=
  ⟨maxPro2Bridge, maxPro2Bridge_gammaSigmaR, maxPro2Bridge_gammaTauR, maxPro2Bridge_gammaX0R,
    maxPro2Bridge_gammaX1R⟩

/-! ## Stress lemmas (plan rule 9) -/

/-- **Stress test (marked generator images).** `maxPro2Bridge` realizes the marked pattern
`σ ↦ s, τ ↦ 1, x₀ ↦ x, x₁ ↦ y` on the four generator images. -/
theorem maxPro2Bridge_generators :
    maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaSigmaR) = drS ∧
      maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR) = 1 ∧
      maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX0R) = drX ∧
      maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaX1R) = drY :=
  ⟨maxPro2Bridge_gammaSigmaR, maxPro2Bridge_gammaTauR, maxPro2Bridge_gammaX0R,
    maxPro2Bridge_gammaX1R⟩

/-- **Stress test (`τ`-death, marked form).** The class of `τ` in `Γ_R(2)` is trivial, so the bridge
carries it to `1 ∈ D_R` — the pro-2 face of "`τ` dies" (⟦lem:pro2word⟧). -/
theorem maxPro2Bridge_gammaTauR_eq_one :
    maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR = 1 ∧
      maxPro2Bridge (1 : maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) = 1 :=
  ⟨maxProPMk_gammaTauR, map_one _⟩

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 3.1 = ⟦lem:pro2word⟧ (`maxPro2Bridge`, `maxPro2Bridge_spec`; the `Γ_R` half —
    `maxPro2(Γ_R) = D_R` — mirroring the `Γ_A`-side `GQ2.SectionThree.maxAEquiv` of Prop 3.10)
  * eq. (3.1) = ⟦lem:pro2word⟧ (`drWord`-relator, via `drWord_maxR_eq_one` / `dr_relation`)
  * Lemma 2.1 = ⟦lem:tame⟧ (`maxProPMk_gammaTauR`: `τ` dies pro-2)
-/
