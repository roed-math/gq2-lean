/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.AdmissibleLimit
public import GQ2.Prop32

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The tame quotient of `Γ_R` and the unramified character  (Roe note §2, Lemma 2.1 ⟦lem:tame⟧)

Formalizes the note's §2 for the Roe-candidate group `Γ_R` (`GQ2/Roe/GammaR.lean`).  With
`W_R = ⟪x₀, x₁⟫` the closed normal closure of the wild generators (`GQ2.wildCoreR`, R3), the note's
Lemma 2.1 ⟦lem:tame⟧ asserts, verbatim,

```
The quotient by W_R is the standard tame group  T_R = ⟨σ, τ | τ^σ = τ²⟩.
Moreover  ν_R(σ)=1,  ν_R(τ)=ν_R(x_0)=ν_R(x_1)=0
defines a continuous epimorphism  ν_R : Γ_R ↠ ℤ₂.
```

together with the `O₂`-corollary (note, after ⟦lem:tame⟧, verbatim `W_R=O_2(\GammaR)`).

The proof mirrors the `Γ_A` side (`GQ2/Prop32.lean`, `GQ2/SectionTenSources.lean`) with an `R`
suffix, so the P5 assembly (R32) consumes the results as drop-ins for the tame/pro-2 discharge:

* **Finite-level redundancy of the wild relation** (⟦lem:tame⟧, first half): in any finite group a
  marking with `t.TameRel` has `powOmega2 t.τ = 1` (`τ` of odd order, Lemma 3.1); and after killing
  `x₀, x₁` the Roe wild value collapses `t.wildValueR = powOmega2 t.τ`, so the Roe wild relation is
  automatic (`Marking.powOmega2_tau_eq_one_of_tameRel`, `Marking.wildValueR_of_trivial_wild`,
  `Marking.wildRelR_of_trivial_wild`).
* **The tame coordinate** `phiR : Γ_R →ₜ* T_tame` (`σ, τ ↦ σ, τ`, `x₀, x₁ ↦ 1`), descended from the
  shared classifier through `N_R` (using the redundancy above at every finite level of `T_tame`),
  with `phiR_surjective` and `ker phiR = W_R` (`ker_phiR`, via the marked iso `tameREquiv`, the
  `Γ_R` side of Prop. 3.2).  These have the exact statement shapes of `phiA_surjective` / `ker_phiA`.
* **`W_R = O₂(Γ_R)`** (`wildCoreR_isMax`): every closed normal pro-2 subgroup lies in `W_R`.  Since
  `W_R` is itself pro-2 (`GQ2.isProP_wildCoreR`, R3), `W_R` is the largest — the maximal-closed-normal-
  pro-2 shape of the `BoundaryMaps.wild_isMax` field, proved here **without axiom B10** (B10 concerns
  `G_ℚ₂`'s tame quotient) from `T_tame`'s intrinsic `eq_bot_of_normal_two_images` (whose engine is
  Lemma 3.1's `tame_normal_two_subgroup_central`).
* **The unramified character** `nuR : Γ_R →ₜ* Z₂` (`nuT ∘ phiR`; `σ ↦ 1`, `τ, x₀, x₁ ↦ 0`) with
  `nuR_surjective`, in the ν-shape the boundary bundle's `compatA`-field consumes
  (`nuT (phiR g)` on the tame side, `GQ2/BoundaryFrame.lean`).
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

open SectionThree

/-! ## Finite-level facts: the Roe wild relation is redundant after killing `x₀, x₁`

Note ⟦lem:tame⟧, first half.  In a finite quotient of `⟨σ, τ | τ^σ = τ²⟩` conjugation preserves the
order of `τ`, so `τ` and `τ²` have equal order, forcing `τ` of odd order and hence `τ^{ω₂} = 1`.  For
the killed-wild marking `(σ, τ, 1, 1)` the Roe wild value `r_R = (x₀^σ)⁻¹ · a · x₁² · c` collapses to
`a = (x₀⁻³τ)^{ω₂}|_{x₀=1} = τ^{ω₂}` (the conjugation and commutator factors die), so `r_R = 1`. -/

namespace Marking

variable {G : Type*} [Group G]

/-- **⟦lem:tame⟧ (odd-order collapse).**  In a *finite* group, a marking satisfying the tame
relation `τ^σ = τ²` has `τ` of odd order (Lemma 3.1, `GQ2.Tame.tame_odd_order`), hence its
`ω₂`-power is trivial.  The tame-frame input to the redundancy of the Roe wild relation. -/
theorem powOmega2_tau_eq_one_of_tameRel [Finite G] (t : Marking G) (h : t.TameRel) :
    powOmega2 t.τ = 1 :=
  powOmega2_eq_one_of_odd (Tame.tame_odd_order (orderOf_pos t.σ).ne' h)

/-- **⟦lem:tame⟧ (killed-wild collapse of `r_R`).**  When both wild generators are trivial, the Roe
wild value reduces to `powOmega2 t.τ`: the first factor `(x₀^σ)⁻¹ = 1`, the auxiliary commutator
`c = [x₁, y₁] = 1` and `x₁² = 1` all die, leaving `a = (x₀⁻³τ)^{ω₂} = τ^{ω₂}`.  Roe counterpart of
the `Γ_A`-side collapse `GQ2.Marking.wildRel_of_trivial_wild`, but stated as the exact value. -/
theorem wildValueR_of_trivial_wild (t : Marking G) (hx0 : t.x₀ = 1) (hx1 : t.x₁ = 1) :
    t.wildValueR = powOmega2 t.τ := by
  have ha : t.aR = powOmega2 t.τ := by
    simp only [aR, hx0, one_pow, inv_one, one_mul]
  have hc : t.cR = 1 := by
    simp only [cR, commP, hx1, inv_one, one_mul, mul_one, inv_mul_cancel]
  have hconj : (conjP t.x₀ t.σ)⁻¹ = 1 := by
    simp only [conjP, hx0, mul_one, inv_mul_cancel, inv_one]
  rw [wildValueR, hconj, ha, hc, hx1]
  simp

/-- **⟦lem:tame⟧ (wild relation redundant).**  If both wild generators are trivial and `τ` has
trivial `ω₂`-power (e.g. `τ` of odd order, `powOmega2_tau_eq_one_of_tameRel`), the Roe wild relation
`r_R = 1` holds automatically.  Roe counterpart of `GQ2.Marking.wildRel_of_trivial_wild`; the
finite-level input for `φ_R`'s classifier being `R`-admissible at every tame level. -/
theorem wildRelR_of_trivial_wild (t : Marking G) (hx0 : t.x₀ = 1) (hx1 : t.x₁ = 1)
    (hτ : powOmega2 t.τ = 1) : t.WildRelR := by
  show t.wildValueR = 1
  rw [wildValueR_of_trivial_wild t hx0 hx1, hτ]

end Marking

/-! ## The tame coordinate `φ_R : Γ_R ↠ T_tame`  (⟦lem:tame⟧, tame-quotient claim)

The classifier `F₄ → T_tame` (`σ, τ ↦ σ, τ`, `x₀, x₁ ↦ 1`) is the one shared with `Γ_A`
(`GQ2.SectionThree.tameClassifier`).  It kills `N_R`: through every finite level of `T_tame` the
pushed marking `(σ̄, τ̄, 1, 1)` is *`R`-admissible* — the three word-independent clauses come from the
`Γ_A` computation, and the Roe wild relation is redundant by the collapse above.  Descending gives
`φ_R`. -/

/- The bundled carrier `↥Γ_R` and the raw quotient `F₄ ⧸ N_R` are only *non-reducibly* defeq, so
instance synthesis for `wildCoreR.Normal` / `ker.Normal` (registered by R3 / `MonoidHom.normal_ker`
at the raw spelling) fails at the `↥Γ_R` spelling.  All constructions below therefore use the raw
`F₄ ⧸ N_R` spelling of `Γ_R` — the exact spelling of R3's `GQ2.wildCoreR` and `GQ2.isProP_wildCoreR`,
so the discharge package lines up with R3 without a re-spelling of `W_R`. -/

/-- The image of `σ` in `Γ_R = F₄ ⧸ N_R`. -/
noncomputable def gammaSigmaR : FreeProfiniteGroup (Fin 4) ⧸ NR := quotientMk NR univMarking.σ

/-- The image of `τ` in `Γ_R = F₄ ⧸ N_R`. -/
noncomputable def gammaTauR : FreeProfiniteGroup (Fin 4) ⧸ NR := quotientMk NR univMarking.τ

/-- The image of `x₀` in `Γ_R = F₄ ⧸ N_R`. -/
noncomputable def gammaX0R : FreeProfiniteGroup (Fin 4) ⧸ NR := quotientMk NR univMarking.x₀

/-- The image of `x₁` in `Γ_R = F₄ ⧸ N_R`. -/
noncomputable def gammaX1R : FreeProfiniteGroup (Fin 4) ⧸ NR := quotientMk NR univMarking.x₁

/-- Local copies of the (private) `Γ_A` classifier generator values, re-derived from the
presentation universal property. -/
@[simp] private lemma tameClassifier_σ' :
    tameClassifier.hom.toMonoidHom univMarking.σ = tameSigma :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] private lemma tameClassifier_τ' :
    tameClassifier.hom.toMonoidHom univMarking.τ = tameTau :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] private lemma tameClassifier_x0' :
    tameClassifier.hom.toMonoidHom univMarking.x₀ = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] private lemma tameClassifier_x1' :
    tameClassifier.hom.toMonoidHom univMarking.x₁ = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- Through every open normal level of `T_tame`, the marking pushed from the shared classifier is
**`R`-admissible**.  The generation, tame-relation and pro-2-core clauses are word-independent (taken
from the `Γ_A` computation `isAdmissible_tameClassifier_level`); the Roe wild relation is redundant
because the marking is `(σ̄, τ̄, 1, 1)` with `τ̄` of odd order (⟦lem:tame⟧). -/
theorem isAdmissibleR_tameClassifier_level (V : OpenNormalSubgroup Ttame) :
    (univMarking.map ((QuotientGroup.mk' V.toSubgroup).comp
      tameClassifier.hom.toMonoidHom)).AdmissibleR := by
  haveI : Finite (Ttame ⧸ V.toSubgroup) := inferInstance
  obtain ⟨hgen, htame, _, hcore⟩ := isAdmissible_tameClassifier_level V
  refine ⟨hgen, htame, ?_, hcore⟩
  refine Marking.wildRelR_of_trivial_wild _ ?_ ?_
    (Marking.powOmega2_tau_eq_one_of_tameRel _ htame)
  · simp only [Marking.map_x₀, MonoidHom.comp_apply, tameClassifier_x0', map_one]
  · simp only [Marking.map_x₁, MonoidHom.comp_apply, tameClassifier_x1', map_one]

/-- `N_R` is contained in the kernel of the shared classifier `F₄ → T_tame` (each finite level is an
`R`-admissible quotient, `isAdmissibleR_tameClassifier_level`, so `NR_le_ker` applies). -/
theorem NR_le_ker_tameClassifier :
    NR ≤ tameClassifier.hom.toMonoidHom.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine eq_one_of_forall_mem_openNormalSubgroup fun V => ?_
  haveI : Finite (Ttame ⧸ V.toSubgroup) := inferInstance
  set f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Ttame ⧸ V.toSubgroup) :=
    (quotientMk V.toSubgroup).comp tameClassifier.hom with hf
  have hadm : (univMarking.map f.toMonoidHom).AdmissibleR :=
    isAdmissibleR_tameClassifier_level V
  have hker := NR_le_ker f hadm hx
  rw [MonoidHom.mem_ker] at hker
  have h1 : QuotientGroup.mk' V.toSubgroup (tameClassifier.hom.toMonoidHom x) = 1 := hker
  exact (QuotientGroup.eq_one_iff _).mp h1

/-- **`φ_R : Γ_R → T_tame`**, the descent of the classifier (`σ, τ ↦ σ, τ`, `x₀, x₁ ↦ 1`).  Roe
counterpart of `GQ2.SectionThree.phiA`. -/
noncomputable def phiR : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) Ttame :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  quotientLift NR tameClassifier.hom NR_le_ker_tameClassifier

@[simp] lemma phiR_gammaSigma : phiR gammaSigmaR = tameSigma := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiR (quotientMk NR univMarking.σ) = tameSigma
  exact (quotientLift_quotientMk _ _ _ _).trans tameClassifier_σ'

@[simp] lemma phiR_gammaTau : phiR gammaTauR = tameTau := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiR (quotientMk NR univMarking.τ) = tameTau
  exact (quotientLift_quotientMk _ _ _ _).trans tameClassifier_τ'

@[simp] lemma phiR_gammaX0 : phiR gammaX0R = 1 := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiR (quotientMk NR univMarking.x₀) = 1
  exact (quotientLift_quotientMk _ _ _ _).trans tameClassifier_x0'

@[simp] lemma phiR_gammaX1 : phiR gammaX1R = 1 := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  show phiR (quotientMk NR univMarking.x₁) = 1
  exact (quotientLift_quotientMk _ _ _ _).trans tameClassifier_x1'

/-- `W_R ≤ ker φ_R` (the wild generators map to `1`, and the kernel is closed normal).  Roe
counterpart of `GQ2.SectionThree.wildPartB_le_ker_phiA`. -/
theorem wildCoreR_le_ker_phiR : wildCoreR ≤ phiR.toMonoidHom.ker := by
  have hker_closed : IsClosed (phiR.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 4) ⧸ NR)) := by
    rw [MonoidHom.coe_ker]
    exact IsClosed.preimage phiR.continuous_toFun isClosed_singleton
  refine Subgroup.topologicalClosure_minimal _ ?_ hker_closed
  refine Subgroup.normalClosure_le_normal ?_
  rintro z (rfl | rfl)
  · exact MonoidHom.mem_ker.mpr phiR_gammaX0
  · exact MonoidHom.mem_ker.mpr phiR_gammaX1

/-! ## The marked iso `Γ_R / W_R ≅ T_tame`  (Prop. 3.2, `Γ_R` side)

Exactly the `Γ_A` construction (`GQ2/Prop32.lean`): the presentation `T_tame = ⟨σ, τ | τ^σ = τ²⟩`
lets us build the section `χ_R : T_tame → Γ_R/W_R` (the tame relator dies in `Γ_R/W_R` because
`tameRelator ∈ N_R`, R3), and the two composites with the descent `ψ_R = φ_R / W_R` are the identity
by density of the marked generators. -/

/-- `Γ_R / W_R` as a profinite group (for the universal property of `T_tame`'s presentation). -/
noncomputable def TameR : ProfiniteGrp :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  haveI : IsClosed (wildCoreR : Set (FreeProfiniteGroup (Fin 4) ⧸ NR)) := wildCoreR_isClosed
  profiniteQuotient wildCoreR

/-- The base map `F₂ ⟶ Γ_R/W_R`: `σ ↦ σ̄, τ ↦ τ̄`. -/
noncomputable def chiBaseR : FreeProfiniteGroup (Fin 2) ⟶ TameR :=
  (FreeProfiniteGroup.homEquiv (Fin 2) TameR).symm
    ![quotientMk wildCoreR gammaSigmaR, quotientMk wildCoreR gammaTauR]

@[simp] private lemma chiBaseR_of_zero :
    chiBaseR.hom.toMonoidHom (FreeProfiniteGroup.of 0) = quotientMk wildCoreR gammaSigmaR :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] private lemma chiBaseR_of_one :
    chiBaseR.hom.toMonoidHom (FreeProfiniteGroup.of 1) = quotientMk wildCoreR gammaTauR :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- The base map kills the tame relator: its image is the `W_R`-class of the `Γ_R`-image of
`univMarking.tameRelator ∈ N_R` (R3's `tameRelator_mem_NR`). -/
theorem chiBaseR_tameWord : chiBaseR.hom.toMonoidHom tameWord = 1 := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  have h1 : chiBaseR.hom.toMonoidHom tameWord
      = quotientMk wildCoreR (quotientMk NR univMarking.tameRelator) := by
    rw [tameWord, Marking.tameRelator]
    simp only [map_mul, map_inv, map_pow, Marking.map_conjP, chiBaseR_of_zero, chiBaseR_of_one]
    rfl
  rw [h1, show quotientMk NR univMarking.tameRelator = 1 from
    (quotientMk_eq_one_iff _).mpr tameRelator_mem_NR]
  exact map_one _

/-- `χ_R : T_tame → Γ_R/W_R`, by the universal property of the presentation. -/
noncomputable def chiWR : ContinuousMonoidHom Ttame TameR :=
  presentationLift {tameWord} chiBaseR.hom fun r hr => by
    rcases hr with rfl
    exact chiBaseR_tameWord

@[simp] private lemma chiWR_tameSigma : chiWR tameSigma = quotientMk wildCoreR gammaSigmaR := by
  show chiWR (quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 0)) = _
  exact (presentationLift_mk _ _ _ _).trans chiBaseR_of_zero

@[simp] private lemma chiWR_tameTau : chiWR tameTau = quotientMk wildCoreR gammaTauR := by
  show chiWR (quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 1)) = _
  exact (presentationLift_mk _ _ _ _).trans chiBaseR_of_one

/-- `ψ_R : Γ_R/W_R → T_tame`, the descent of `φ_R`. -/
noncomputable def psiWR :
    ContinuousMonoidHom ((FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ wildCoreR) Ttame :=
  quotientLift wildCoreR phiR wildCoreR_le_ker_phiR

@[simp] private lemma psiWR_mk_gammaSigmaR :
    psiWR (quotientMk wildCoreR gammaSigmaR) = tameSigma :=
  (quotientLift_quotientMk _ _ _ _).trans phiR_gammaSigma

@[simp] private lemma psiWR_mk_gammaTauR :
    psiWR (quotientMk wildCoreR gammaTauR) = tameTau :=
  (quotientLift_quotientMk _ _ _ _).trans phiR_gammaTau

/-- `Γ_R/W_R` is topologically generated by the classes of the four marked generators. -/
theorem topGen_tameR :
    (Subgroup.closure (Set.range fun i : Fin 4 =>
        quotientMk wildCoreR (quotientMk NR (FreeProfiniteGroup.of i)))).topologicalClosure
      = ⊤ := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  have h := topGen_map
    (f := ((quotientMk wildCoreR).comp (quotientMk NR)).toMonoidHom)
    ((quotientMk wildCoreR).comp (quotientMk NR)).continuous_toFun
    ((quotientMk_surjective wildCoreR).comp (quotientMk_surjective NR))
    (topGen_freeProfiniteGroup (Fin 4))
  rwa [← Set.range_comp] at h

/-- `ψ_R ∘ χ_R = id` on `T_tame` (both send `σ ↦ σ, τ ↦ τ`; density). -/
theorem psiWR_chiWR (x : Ttame) : psiWR (chiWR x) = x := by
  have h := monoidHom_eq_of_topGen
    (f := psiWR.toMonoidHom.comp chiWR.toMonoidHom) (g := MonoidHom.id Ttame)
    (by rw [MonoidHom.coe_comp]
        exact Continuous.comp psiWR.continuous_toFun chiWR.continuous_toFun) continuous_id
    topGen_ttame ?_
  · exact h x
  · rintro z (rfl | rfl)
    · show psiWR (chiWR tameSigma) = tameSigma
      rw [chiWR_tameSigma, psiWR_mk_gammaSigmaR]
    · show psiWR (chiWR tameTau) = tameTau
      rw [chiWR_tameTau, psiWR_mk_gammaTauR]

/-- `χ_R ∘ ψ_R = id` on `Γ_R/W_R` (checked on the four marked generator classes; density). -/
theorem chiWR_psiWR (x : (FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ wildCoreR) :
    chiWR (psiWR x) = x := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  have h := monoidHom_eq_of_topGen
    (f := chiWR.toMonoidHom.comp psiWR.toMonoidHom) (g := MonoidHom.id _)
    (by rw [MonoidHom.coe_comp]
        exact Continuous.comp chiWR.continuous_toFun psiWR.continuous_toFun) continuous_id
    topGen_tameR ?_
  · exact h x
  · rintro z ⟨i, rfl⟩
    fin_cases i
    · show chiWR (psiWR (quotientMk wildCoreR gammaSigmaR)) = quotientMk wildCoreR gammaSigmaR
      rw [psiWR_mk_gammaSigmaR, chiWR_tameSigma]
    · show chiWR (psiWR (quotientMk wildCoreR gammaTauR)) = quotientMk wildCoreR gammaTauR
      rw [psiWR_mk_gammaTauR, chiWR_tameTau]
    · -- `x₀`-class is `1`
      have hx : quotientMk wildCoreR gammaX0R = 1 := by
        rw [quotientMk_eq_one_iff]
        exact Subgroup.le_topologicalClosure _
          (Subgroup.subset_normalClosure (Set.mem_insert _ _))
      show chiWR (psiWR (quotientMk wildCoreR gammaX0R)) = quotientMk wildCoreR gammaX0R
      rw [hx, map_one, map_one]
      rfl
    · -- `x₁`-class is `1`
      have hx : quotientMk wildCoreR gammaX1R = 1 := by
        rw [quotientMk_eq_one_iff]
        exact Subgroup.le_topologicalClosure _
          (Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl))
      show chiWR (psiWR (quotientMk wildCoreR gammaX1R)) = quotientMk wildCoreR gammaX1R
      rw [hx, map_one, map_one]
      rfl

/-- **Prop. 3.2, `Γ_R` side** (⟦lem:tame⟧, tame-quotient claim): the marked isomorphism
`Γ_R / W_R ≅ T_tame`, `σ̄ ↦ σ, τ̄ ↦ τ`.  Roe counterpart of `GQ2.SectionThree.tameAEquiv`. -/
noncomputable def tameREquiv :
    ContinuousMulEquiv ((FreeProfiniteGroup (Fin 4) ⧸ NR) ⧸ wildCoreR) Ttame where
  toFun := psiWR
  invFun := chiWR
  left_inv := chiWR_psiWR
  right_inv := psiWR_chiWR
  map_mul' := map_mul psiWR
  continuous_toFun := psiWR.continuous_toFun
  continuous_invFun := chiWR.continuous_toFun

/-! ## The discharge package for R32: surjectivity, kernel, and `W_R = O₂` -/

/-- **`htame` for `Γ_R`**: `φ_R` is onto (Prop 3.2, via `tameREquiv`).  Statement shape of
`GQ2.SectionThree.phiA_surjective`. -/
theorem phiR_surjective : Function.Surjective phiR := by
  intro t
  obtain ⟨x, hx⟩ := tameREquiv.surjective t
  obtain ⟨g, rfl⟩ := quotientMk_surjective wildCoreR x
  exact ⟨g, hx⟩

/-- **`ker φ_R = W_R`.**  `⊇` is `wildCoreR_le_ker_phiR`; `⊆` because the descent `ψ_R = φ_R / W_R`
is injective — it is the underlying map of the Prop-3.2 iso `tameREquiv`.  Statement shape of
`GQ2.SectionTen.ker_phiA`; consumed by R32 as the wild-inertia identification. -/
theorem ker_phiR : phiR.toMonoidHom.ker = wildCoreR := by
  refine le_antisymm (fun x hx => ?_) wildCoreR_le_ker_phiR
  have h1 : psiWR (quotientMk wildCoreR x) = 1 :=
    (quotientLift_quotientMk _ _ _ _).trans (MonoidHom.mem_ker.mp hx)
  have h2 : quotientMk wildCoreR x = 1 :=
    tameREquiv.injective (h1.trans (map_one psiWR).symm)
  exact (quotientMk_eq_one_iff _).mp h2

/-- **`W_R = O₂(Γ_R)`** (note, after ⟦lem:tame⟧, verbatim `W_R=O_2(\GammaR)`): every closed normal
pro-2 subgroup of `Γ_R` lies in `W_R`.  Since `W_R` is itself closed normal pro-2 (`wildCoreR_normal`,
`wildCoreR_isClosed`, `GQ2.isProP_wildCoreR`), it is the *largest* — i.e. `O₂(Γ_R)`.  Proved from
`T_tame`'s intrinsic triviality of normal pro-2 subgroups (`eq_bot_of_normal_two_images`, whose
engine is Lemma 3.1's `tame_normal_two_subgroup_central`) applied to the image under `φ_R`;
**independent of axiom B10**.  This is the `wild_isMax`-shape of `BoundaryMaps`. -/
theorem wildCoreR_isMax (N : Subgroup (FreeProfiniteGroup (Fin 4) ⧸ NR)) (hNn : N.Normal)
    (_hNc : IsClosed (N : Set (FreeProfiniteGroup (Fin 4) ⧸ NR))) (hNp : IsProP 2 N) :
    N ≤ wildCoreR := by
  set M : Subgroup Ttame := N.map phiR.toMonoidHom with hM
  haveI hMn : M.Normal := Subgroup.Normal.map hNn _ phiR_surjective
  have hMbot : M = ⊥ := by
    refine eq_bot_of_normal_two_images M ?_
    intro G _ _ _ _ f hf
    rw [hM, Subgroup.map_map]
    exact isPGroup_map_of_isProP hNp _ (hf.comp phiR.continuous_toFun)
  intro x hxN
  have h1 : phiR x ∈ M := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at h1
  have hxk : x ∈ phiR.toMonoidHom.ker := h1
  rwa [ker_phiR] at hxk

/-! ## The unramified character `ν_R : Γ_R ↠ Z₂`  (⟦lem:tame⟧, second half)

`ν_R = ν_t ∘ φ_R` factors the standard unramified character through the tame quotient — the
"geometric unramified character" of the note.  Its values `σ ↦ 1`, `τ, x₀, x₁ ↦ 0` are exactly the
tame-side ν-datum the boundary bundle's `compatA`-field (`nuT (tameA g)`, `GQ2/BoundaryFrame.lean`)
consumes; surjectivity is `ν_t` onto composed with `φ_R` onto. -/

/-- **`ν_R : Γ_R → Z₂`** (⟦lem:tame⟧): `ν_R(σ) = 1`, `ν_R(τ) = ν_R(x₀) = ν_R(x₁) = 0`, as
`ν_t ∘ φ_R`.  Roe counterpart of the tame-side `ν_t ∘ tameA` of `GQ2.BoundaryMaps`. -/
noncomputable def nuR : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) Ztwo :=
  nuT.comp phiR

@[simp] theorem nuR_gammaSigma : nuR gammaSigmaR = ztwoOne := by
  show nuT (phiR gammaSigmaR) = ztwoOne
  rw [phiR_gammaSigma, nuT_tameSigma]

@[simp] theorem nuR_gammaTau : nuR gammaTauR = 1 := by
  show nuT (phiR gammaTauR) = 1
  rw [phiR_gammaTau, nuT_tameTau]

@[simp] theorem nuR_gammaX0 : nuR gammaX0R = 1 := by
  show nuT (phiR gammaX0R) = 1
  rw [phiR_gammaX0, map_one]

@[simp] theorem nuR_gammaX1 : nuR gammaX1R = 1 := by
  show nuT (phiR gammaX1R) = 1
  rw [phiR_gammaX1, map_one]

/-- **`ν_R` is a continuous epimorphism onto `Z₂`** (⟦lem:tame⟧, second half): `ν_t` is onto
(`nuT_surjective`) and `φ_R` is onto (`phiR_surjective`). -/
theorem nuR_surjective : Function.Surjective nuR :=
  nuT_surjective.comp phiR_surjective

/-! ## Stress tests (plan rule 9)

Explicit generator evaluations pinning `φ_R` (tame generators to `σ, τ`, wild generators to `1`) and
`ν_R` (the unramified pattern `(1, 0, 0, 0)`). -/

/-- **Stress test.** `φ_R` on the four explicit generators: `σ, τ ↦ σ, τ`, `x₀, x₁ ↦ 1`. -/
theorem phiR_generators :
    phiR gammaSigmaR = tameSigma ∧ phiR gammaTauR = tameTau ∧
      phiR gammaX0R = 1 ∧ phiR gammaX1R = 1 :=
  ⟨phiR_gammaSigma, phiR_gammaTau, phiR_gammaX0, phiR_gammaX1⟩

/-- **Stress test.** `ν_R` realizes the unramified pattern `ν_R(σ) = 1`, `ν_R(τ) = ν_R(x₀) =
ν_R(x₁) = 0` (⟦lem:tame⟧). -/
theorem nuR_generators :
    nuR gammaSigmaR = ztwoOne ∧ nuR gammaTauR = 1 ∧ nuR gammaX0R = 1 ∧ nuR gammaX1R = 1 :=
  ⟨nuR_gammaSigma, nuR_gammaTau, nuR_gammaX0, nuR_gammaX1⟩

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 2.1 = ⟦lem:tame⟧
  * Definition 1.1 = ⟦def:GammaR⟧
-/
