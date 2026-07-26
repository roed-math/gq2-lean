/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SourceData
import GQ2.SectionTenSources
import GQ2.PresentationLiteral
import GQ2.Roe.Prop23
import GQ2.Roe.Supply
import GQ2.Roe.MarkedPro2
import GQ2.RStage.GammaR
import GQ2.MStageCountGammaR
import GQ2.HalfTorsorGammaR
import GQ2.Phase140.GammaR
import GQ2.GaussZ.GammaRD
import GQ2.Roe.Labute.Assembly

/-!
# The `Γ_R` assembly: `sourceR`, eq. (154), and the Replacement theorem  (R32)

The R-campaign capstone file: the Roe candidate `Γ_R` (note Definition 1.1 ⟦def:GammaR⟧) is
plugged into the two-source machine as a `GQ2.SourceData` instance, and the note's
⟦thm:main⟧ (Replacement theorem, `Γ_R ≅ G_{ℚ₂}`) is derived in the exact statement shape of
the `Γ_A` capstones:

* `sourceR (hBLab) : SourceData` — carrier `GammaR`; tame side `phiR`/`nuR` (R6); pro-2 side
  the **marked composite** `Γ_R ↠ Γ_R(2) ≅ D_R ≅ G_{ℚ₂}(2) ≅ Π` (below); the seven supply
  obligations bound to the landed `_gammaR` lemmas (R31a–g), each by the same lambda
  `BoundaryMaps.sourceA` uses for its `_gammaA` twin.
* `eq_154_R (hBLab) : #Sur_cont(Γ_R, G) = #Sur_cont(G_{ℚ₂}, G)` — eq. (154) with the
  candidate slot at `Γ_R`, via `thm_4_2_of_sources sourceR` frame by frame.
* `main_surjection_count_R (hBLab) : contSurjCount G = admissibleCountR G` — the
  surjection-count form at the **Roe** admissible-marking semantics (`prop_2_3_R`, R4).
* `main_presentation_literal_roe (hBLab) : Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)` —
  the note's ⟦thm:main⟧, by instantiating the `main_presentation` schematic at `Γ_R`.
* `main_presentation_literal_roe_unconditional : Nonempty (ContinuousMulEquiv GammaR
  AbsGalQ2)` — the same theorem with the B-Lab hypothesis **discharged** (L6): the campaign's
  terminal statement, hypothesis-free.

## The B-Lab hypothesis (owner decision 2026-07-25: no new axiom; DISCHARGED 2026-07-26)

Labute's classification instance (note Cor. 3.4 ⟦cor:abstractD0⟧) enters exactly once, as the
explicit binder `hBLab : BLabHypothesis` threaded from R15's `markedPro2_R`
(⟦prop:markedpro2⟧) — it is **not** an axiom.  The L-campaign has since **proved** the
instance (`GQ2.Roe.Labute.bLab`, `GQ2/Roe/Labute/Assembly.lean`, at the standard three axioms),
so every `hBLab` argument discharges by the one-liner `bLab`; the unconditional corollary at
the end of this file does exactly that.  The hypothesis-parametrized forms are kept as the
frozen statements the R-campaign gates audit.  Everything else in this file is unconditional.

## The pro-2 boundary coordinate (the construction this file adds)

`SourceData` asks for `pro2 : Γ_R → Π` (`Π = PiBd`, eq. (20)) with `ν`-compatibility, joint
surjectivity with the tame coordinate, and kernel `= proPKernel 2 Γ_R`.  Unlike `Γ_A` — whose
pro-2 quotient *is* `Π` with matching generators (Prop 3.10) — the pro-2 quotient of `Γ_R` is
the **differently presented** `D_R` (⟦lem:pro2word⟧, R15a `maxPro2Bridge`), and its
identification with `Π` is the abstract, `ν`-marked one of B-Lab.  We therefore compose

  `pro2R := eA ∘ e⁻¹ ∘ maxPro2Bridge ∘ maxProPMk`,

with `e : G_{ℚ₂}(2) ≅ D_R` from `markedPro2_R (hBLab)` and `eA : G_{ℚ₂}(2) ≅ Π` from
`prop_3_10_local_marked`.  Both come with `ℤ₂`-identifications `ι` pinned at the topological
generator (`ι(1) = ofAdd 1`), so the two `ν`-composites agree (`ztwoOne` topologically
generates `Ztwo`), which yields the `ν`-compatibility of `pro2R` with `φ_R` by density over
the four marked generators (`nuDR_maxPro2Bridge_comp`).  Joint surjectivity then follows from
the generic fibred-product kit (`SectionThree.fiberProductExists` + `hker_uniform`), exactly
as for `boundaryMapsWitness`.

**Design finding (generator pinning).**  The `SourceData` fields `pro2_sigma/x0/x1` pin
`pro2` to `piSigma/piX0/piX1` at the structure's own generators.  For `Γ_R` this is
*unsatisfiable at the honest generators* `gammaSigmaR/X0R/X1R`: their `pro2R`-images are the
`eA∘e⁻¹`-images of `drS/drX/drY`, and no continuous hom `D_R → Π` matches generators
literally (the tuple `(piSigma, piX0, piX1)` satisfies the `Π`-relator, not the Roe relator).
Since the eight pinning fields are consumed **nowhere** (they are interface documentation;
`thm_4_2_of_sources` and all its lanes touch only `b`/`tame`/`pro2`/`compat`/`surj`/
`ker_pro2`/the action layer/the obligations), `sourceR` takes `tau := gammaTauR` (honest —
`τ` dies pro-2) and *marked-pinned* choice elements `sigmaMarkR/x0MarkR/x1MarkR` obtained
from joint surjectivity for the other three.  The GaussZ obligations are unaffected: the R31g
twins pin the **tame** coordinate at the honest generators (`phiR_gammaSigma` etc.), which
`sourceR` supplies on the nose.

## Import discipline

Plain-import (non-`module`): this file sits atop the non-`module` §2/§8 stack
(`SourceData`, `SectionTenSources`, `PresentationLiteral`, `Roe/Prop23`, `Roe/Supply`,
`Roe/MarkedPro2`).  Importing the `module`-style suppliers (`Roe/Tame`, `Roe/MaxPro2Bridge`,
via `Roe/MarkedPro2`) is fine — the restriction is one-directional.  `sourceR` cannot live in
`GQ2/SourceData.lean`: `GQ2/MStageCountGammaR.lean` and `GQ2/GaussZ/GammaRD.lean` import
`GQ2.SourceData`, so this file is a new leaf importing both sides.

Axioms: **no new axiom, no `sorry`**.  The obligations are std-3 (R31a–g); the capstones
inherit the `Γ_A`-mirror census of eq. (154) through the shared `G_{ℚ₂}`-side machinery, plus
nothing — `BLabHypothesis` is a binder, not an axiom.

## Numerical anchor (R5, `GQ2/Roe/Sanity.lean` + `scripts/roe_sanity_counts.py`)

`main_surjection_count_R` + `main_surjection_count'` give
`admissibleCountR G = admissibleCount G` for every finite `G`
(`admissibleCountR_eq_admissibleCount` below).  R5 verified exactly this agreement
numerically, four ways (Lean word-level pins + two independent Python engines + the June
LMFDB-verified counts): `C₂ : 7`, `C₄ : 24`, `V₄ : 42`, `D₄ : 144`, `Q₈ : 144` — with the
archive convention `g^h = hgh⁻¹` reconciled to Lean's `g⁻¹xg` by the `σ ↦ σ⁻¹` bijection.
-/

namespace GQ2

open SectionThree SectionEight SectionTen ProfiniteGrp

/-! ## Instances for the raw carrier `Γ_R = F₄ ⧸ N_R`

As in `GQ2/Roe/MaxPro2Bridge.lean`: `T2Space`/`TotallyDisconnectedSpace` on the raw quotient
are guarded by `[IsClosed N_R]`, discharged once here via `NR_isClosed`. -/

local instance : T2Space (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  inferInstance

local instance : TotallyDisconnectedSpace (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  inferInstance

/-! ## `ℤ̂`/`Z₂` glue: `ztwoOne` topologically generates, so pinned `ι`s agree -/

/-- `ofInt` is the `ℤ`-power of `ofInt 1` — the multiplicative reading of `ℤ ⊆ ℤ̂` being
generated by `1`. -/
theorem Zhat.ofInt_zpow (n : ℤ) : Zhat.ofInt n = Zhat.ofInt 1 ^ n := by
  have hneg : Zhat.ofInt (-1) = (Zhat.ofInt 1)⁻¹ := by
    have h := Zhat.ofInt_add 1 (-1)
    rw [add_neg_cancel, Zhat.ofInt_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  induction n using Int.induction_on with
  | zero => rw [Zhat.ofInt_zero, zpow_zero]
  | succ k ih => rw [Zhat.ofInt_add, ih, zpow_add, zpow_one]
  | pred k ih =>
    have h : (-(k : ℤ) - 1) = (-(k : ℤ)) + (-1) := by ring
    rw [h, Zhat.ofInt_add, ih, hneg, zpow_add, zpow_neg_one]

/-- Two continuous `ℤ₂`-identifications `Ztwo ≅ Multiplicative ℤ₂` agreeing at `ztwoOne`
agree everywhere: `ztwoOne` is the image of the dense `1 ∈ ℤ ⊆ ℤ̂`. -/
private theorem ztwoEquiv_eq_of_ztwoOne
    {ι ι' : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2])}
    (h : ι ztwoOne = ι' ztwoOne) (z : Ztwo) : ι z = ι' z := by
  have hsurj : Function.Surjective (maxProPMk 2 Zhat) := quotientMk_surjective _
  have hfun : ∀ w : Zhat, ι'.symm (ι (maxProPMk 2 Zhat w)) = maxProPMk 2 Zhat w := by
    have h0 := Zhat.funext_ofInt (X := Ztwo)
      (f := fun w => ι'.symm (ι (maxProPMk 2 Zhat w))) (g := fun w => maxProPMk 2 Zhat w)
      (ι'.symm.continuous_toFun.comp
        (ι.continuous_toFun.comp (maxProPMk 2 Zhat).continuous_toFun))
      (maxProPMk 2 Zhat).continuous_toFun
      (fun n => by
        have e1 : maxProPMk 2 Zhat (Zhat.ofInt n) = ztwoOne ^ n :=
          (congrArg (maxProPMk 2 Zhat) (Zhat.ofInt_zpow n)).trans
            (map_zpow (maxProPMk 2 Zhat) (Zhat.ofInt 1) n)
        show ι'.symm (ι (maxProPMk 2 Zhat (Zhat.ofInt n))) = maxProPMk 2 Zhat (Zhat.ofInt n)
        rw [e1]
        calc ι'.symm (ι (ztwoOne ^ n)) = ι'.symm (ι ztwoOne ^ n) := by rw [map_zpow]
          _ = ι'.symm (ι' ztwoOne ^ n) := by rw [h]
          _ = ztwoOne ^ n := by rw [← map_zpow ι', ι'.symm_apply_apply])
    exact fun w => congrFun h0 w
  obtain ⟨w, rfl⟩ := hsurj z
  have hw := hfun w
  calc ι (maxProPMk 2 Zhat w) = ι' (ι'.symm (ι (maxProPMk 2 Zhat w))) :=
        (ι'.apply_symm_apply _).symm
    _ = ι' (maxProPMk 2 Zhat w) := congrArg (fun t => ι' t) hw

/-! ## Topological generation of `Γ_R` by the four marked generators -/

/-- `Γ_R` is topologically generated by its four marked generators — the `Γ_R` mirror of
`GQ2.SectionThree.topGen_gammaA` (glue lemma; the `Γ_A` original is stated at `N_A`). -/
theorem topGen_gammaR :
    (Subgroup.closure {gammaSigmaR, gammaTauR, gammaX0R, gammaX1R}).topologicalClosure
      = ⊤ := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  have h := topGen_map (f := (quotientMk NR).toMonoidHom) (quotientMk NR).continuous_toFun
    (quotientMk_surjective NR) (topGen_freeProfiniteGroup (Fin 4))
  have h1 : (⇑(quotientMk NR).toMonoidHom) '' Set.range (FreeProfiniteGroup.of (X := Fin 4))
      = {gammaSigmaR, gammaTauR, gammaX0R, gammaX1R} := by
    rw [← Set.range_comp]
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rwa [h1] at h

/-- **The `ν`-composite over the whole of `Γ_R`** (glue lemma; the pointwise closure of R15a's
generator quadruple `nuDR_maxPro2Bridge_*`): `ν_{D_R} ∘ maxPro2Bridge ∘ maxProPMk = ν_R`, by
density over the four marked generators. -/
theorem nuDR_maxPro2Bridge_comp (g : FreeProfiniteGroup (Fin 4) ⧸ NR) :
    nuDR (maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) g)) = nuR g := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  have h := monoidHom_eq_of_topGen
    (f := nuDR.toMonoidHom.comp ((maxPro2Bridge.toMulEquiv.toMonoidHom).comp
      (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).toMonoidHom))
    (g := nuR.toMonoidHom)
    (by
      rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
      exact nuDR.continuous_toFun.comp (maxPro2Bridge.continuous_toFun.comp
        (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).continuous_toFun))
    nuR.continuous_toFun topGen_gammaR ?_
  · exact h g
  · rintro z (rfl | rfl | rfl | rfl)
    · show nuDR (maxPro2Bridge (maxProPMk 2 _ gammaSigmaR)) = nuR gammaSigmaR
      rw [nuDR_maxPro2Bridge_sigma, nuR_gammaSigma]
    · show nuDR (maxPro2Bridge (maxProPMk 2 _ gammaTauR)) = nuR gammaTauR
      rw [nuDR_maxPro2Bridge_tau, nuR_gammaTau]
    · show nuDR (maxPro2Bridge (maxProPMk 2 _ gammaX0R)) = nuR gammaX0R
      rw [nuDR_maxPro2Bridge_x0, nuR_gammaX0]
    · show nuDR (maxPro2Bridge (maxProPMk 2 _ gammaX1R)) = nuR gammaX1R
      rw [nuDR_maxPro2Bridge_x1, nuR_gammaX1]

/-! ## The pro-2 boundary coordinate of `Γ_R` -/

section BoundaryLane

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The `Γ_R` pro-2 boundary coordinate exists** (⟦prop:markedpro2⟧ + Prop 3.10, local
half): a continuous `pro2R : Γ_R → Π` that is `ν`-compatible with `φ_R`, surjective, has
kernel exactly the pro-2 kernel, and kills `τ` — the composite
`eA ∘ e⁻¹ ∘ maxPro2Bridge ∘ maxProPMk` of the module docstring. -/
theorem exists_pro2R (hBLab : BLabHypothesis) :
    ∃ pro2R : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) PiBd,
      (∀ g, nuT (phiR g) = nuTwo (pro2R g)) ∧ Function.Surjective pro2R ∧
      pro2R.toMonoidHom.ker = proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) ∧
      pro2R gammaTauR = 1 := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  obtain ⟨ι, hι1, e, he⟩ := markedPro2_R localReciprocity hBLab
  obtain ⟨ι', hι'1, eA, heA⟩ := SectionThree.prop_3_10_local_marked localReciprocity
  -- the `ν`-glue on `G_{ℚ₂}(2)`: `ν_{D_R} ∘ e = ν₂ ∘ eA` (the two pinned `ι`s agree)
  have hglue : ∀ x : maxProPQuotient 2 AbsGalQ2, nuDR (e x) = nuTwo (eA x) := by
    have hsurj2 : Function.Surjective (maxProPMk 2 AbsGalQ2) := quotientMk_surjective _
    intro x
    obtain ⟨g, rfl⟩ := hsurj2 x
    have h1 : ι (nuDR (e (maxProPMk 2 AbsGalQ2 g)))
        = ι' (nuTwo (eA (maxProPMk 2 AbsGalQ2 g))) := (he g).symm.trans (heA g)
    have h2 : ι (nuTwo (eA (maxProPMk 2 AbsGalQ2 g)))
        = ι' (nuTwo (eA (maxProPMk 2 AbsGalQ2 g))) :=
      ztwoEquiv_eq_of_ztwoOne (hι1.trans hι'1.symm) _
    exact ι.injective (h1.trans h2.symm)
  have hmkR_surj :
      Function.Surjective (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) :=
    quotientMk_surjective _
  refine ⟨⟨(eA.toMulEquiv.toMonoidHom.comp ((e.symm.toMulEquiv.toMonoidHom).comp
      ((maxPro2Bridge.toMulEquiv.toMonoidHom).comp
        (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).toMonoidHom))),
    eA.continuous_toFun.comp (e.symm.continuous_toFun.comp
      (maxPro2Bridge.continuous_toFun.comp
        (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)).continuous_toFun))⟩,
    ?_, ?_, ?_, ?_⟩
  · -- `ν`-compatibility with the tame coordinate
    intro g
    show nuT (phiR g)
      = nuTwo (eA (e.symm (maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) g))))
    rw [← hglue, e.apply_symm_apply, nuDR_maxPro2Bridge_comp]
    rfl
  · -- surjectivity: every layer of the composite is onto
    intro p
    obtain ⟨x, hx⟩ := eA.surjective p
    obtain ⟨y, hy⟩ := e.symm.surjective x
    obtain ⟨z, hz⟩ := maxPro2Bridge.surjective y
    obtain ⟨g, hg⟩ := hmkR_surj z
    exact ⟨g, by
      show eA (e.symm (maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) g))) = p
      rw [hg, hz, hy, hx]⟩
  · -- kernel: the three isomorphism layers are injective, so the kernel is `maxProPMk`'s
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : eA (e.symm (maxPro2Bridge
          (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) x))) = 1 := hx
      have h2 : e.symm (maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) x))
          = 1 := eA.injective (h1.trans (map_one eA).symm)
      have h3 : maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) x) = 1 :=
        e.symm.injective (h2.trans (map_one e.symm).symm)
      have h4 : maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) x = 1 :=
        maxPro2Bridge.injective (h3.trans (map_one maxPro2Bridge).symm)
      exact (quotientMk_eq_one_iff (proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR))).mp h4
    · intro hx
      have h4 : maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) x = 1 :=
        (quotientMk_eq_one_iff (proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR))).mpr hx
      show eA (e.symm (maxPro2Bridge (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) x))) = 1
      rw [h4, map_one, map_one, map_one]
  · -- `τ` dies: it already dies in `Γ_R(2)`
    show eA (e.symm (maxPro2Bridge
      (maxProPMk 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) gammaTauR))) = 1
    rw [maxProPMk_gammaTauR, map_one, map_one, map_one]

variable (hBLab : BLabHypothesis)

/-- **The `Γ_R` pro-2 boundary coordinate** `pro2R : Γ_R → Π` (a choice from
`exists_pro2R`; B-Lab-conditional). -/
noncomputable def pro2R : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) PiBd :=
  (exists_pro2R hBLab).choose

/-- `ν`-compatibility: `ν_t ∘ φ_R = ν₂ ∘ pro2R` (the eq. (27) fibre condition for `Γ_R`). -/
theorem pro2R_compat : ∀ g, nuT (phiR g) = nuTwo (pro2R hBLab g) :=
  (exists_pro2R hBLab).choose_spec.1

theorem pro2R_surjective : Function.Surjective (pro2R hBLab) :=
  (exists_pro2R hBLab).choose_spec.2.1

/-- `ker pro2R = proPKernel 2 Γ_R` — the promoted `SourceData.ker_pro2` field, from the
max-pro-2 identification (the recon's "Γ_R from its max-pro-2 identification"). -/
theorem ker_pro2R :
    (pro2R hBLab).toMonoidHom.ker = proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  (exists_pro2R hBLab).choose_spec.2.2.1

theorem pro2R_gammaTauR : pro2R hBLab gammaTauR = 1 :=
  (exists_pro2R hBLab).choose_spec.2.2.2

/-- **Joint surjectivity of the `Γ_R` boundary pair** (eq. (27) for `Γ_R`): the generic
fibred-product kit at `(φ_R, pro2R)`, exactly as `boundaryMapsWitness.surjA`. -/
theorem bR_joint_surjective :
    Function.Surjective (fun g : FreeProfiniteGroup (Fin 4) ⧸ NR =>
      (⟨(phiR g, pro2R hBLab g), pro2R_compat hBLab g⟩ : ↥boundarySubgroup)) := by
  rintro ⟨⟨t, p⟩, hmem⟩
  obtain ⟨g, hg1, hg2⟩ := SectionThree.fiberProductExists nuT.toMonoidHom nuTwo.toMonoidHom
    phiR.toMonoidHom (pro2R hBLab).toMonoidHom phiR_surjective (pro2R_compat hBLab)
    (SectionThree.hker_uniform phiR (pro2R hBLab) phiR_surjective (pro2R_surjective hBLab)
      (ker_pro2R hBLab).ge (pro2R_compat hBLab)) t p hmem
  exact ⟨g, Subtype.ext (Prod.ext hg1 hg2)⟩

/-! ### The marked-pinned generators (the module-docstring design finding)

Boundary points to hit: the pinned pairs of the `SourceData` interface.  Membership in
`∂bd` is the `ν`-equation, discharged by the generator values of `ν_t` and `ν₂`. -/

/-- The pinned `σ`-boundary point `(σ_t, σ_Π) ∈ ∂bd`. -/
private noncomputable def sigmaBd : ↥boundarySubgroup :=
  ⟨(tameSigma, piSigma), by show nuT tameSigma = nuTwo piSigma
                            rw [nuT_tameSigma, nuTwo_piSigma]⟩

/-- The pinned `x₀`-boundary point `(1, x₀_Π) ∈ ∂bd`. -/
private noncomputable def x0Bd : ↥boundarySubgroup :=
  ⟨(1, piX0), by show nuT 1 = nuTwo piX0
                 rw [map_one, nuTwo_piX0]⟩

/-- The pinned `x₁`-boundary point `(1, x₁_Π) ∈ ∂bd`. -/
private noncomputable def x1Bd : ↥boundarySubgroup :=
  ⟨(1, piX1), by show nuT 1 = nuTwo piX1
                 rw [map_one, nuTwo_piX1]⟩

/-- The marked-pinned `σ`-generator of `sourceR`: an element of `Γ_R` over the boundary
point `(σ_t, σ_Π)` (joint surjectivity).  *Not* the honest `gammaSigmaR` — see the module
docstring's design finding. -/
noncomputable def sigmaMarkR : FreeProfiniteGroup (Fin 4) ⧸ NR :=
  (bR_joint_surjective hBLab sigmaBd).choose

theorem sigmaMarkR_spec :
    phiR (sigmaMarkR hBLab) = tameSigma ∧ pro2R hBLab (sigmaMarkR hBLab) = piSigma := by
  have h := (bR_joint_surjective hBLab sigmaBd).choose_spec
  exact ⟨congrArg (fun x : ↥boundarySubgroup => (x : Ttame × PiBd).1) h,
    congrArg (fun x : ↥boundarySubgroup => (x : Ttame × PiBd).2) h⟩

/-- The marked-pinned `x₀`-generator of `sourceR`. -/
noncomputable def x0MarkR : FreeProfiniteGroup (Fin 4) ⧸ NR :=
  (bR_joint_surjective hBLab x0Bd).choose

theorem x0MarkR_spec :
    phiR (x0MarkR hBLab) = 1 ∧ pro2R hBLab (x0MarkR hBLab) = piX0 := by
  have h := (bR_joint_surjective hBLab x0Bd).choose_spec
  exact ⟨congrArg (fun x : ↥boundarySubgroup => (x : Ttame × PiBd).1) h,
    congrArg (fun x : ↥boundarySubgroup => (x : Ttame × PiBd).2) h⟩

/-- The marked-pinned `x₁`-generator of `sourceR`. -/
noncomputable def x1MarkR : FreeProfiniteGroup (Fin 4) ⧸ NR :=
  (bR_joint_surjective hBLab x1Bd).choose

theorem x1MarkR_spec :
    phiR (x1MarkR hBLab) = 1 ∧ pro2R hBLab (x1MarkR hBLab) = piX1 := by
  have h := (bR_joint_surjective hBLab x1Bd).choose_spec
  exact ⟨congrArg (fun x : ↥boundarySubgroup => (x : Ttame × PiBd).1) h,
    congrArg (fun x : ↥boundarySubgroup => (x : Ttame × PiBd).2) h⟩

/-! ## The `Γ_R` source instance -/

/-- **The `Γ_R` instance of the source interface** (the R-campaign assembly): carrier
`GammaR`, tame side `φ_R`/`ν_R` (⟦lem:tame⟧, R6), pro-2 side `pro2R` (⟦lem:pro2word⟧ +
⟦prop:markedpro2⟧ + Prop 3.10 local, B-Lab-conditional), and the seven supply-obligation
families bound to the landed `_gammaR` lemmas of R31a–g — each by the same plain lambda
`BoundaryMaps.sourceA` uses for its `_gammaA` twin. -/
noncomputable def sourceR : SourceData where
  Γ := GammaR
  sigma := sigmaMarkR hBLab
  tau := gammaTauR
  x0 := x0MarkR hBLab
  x1 := x1MarkR hBLab
  tame := phiR
  pro2 := pro2R hBLab
  compat := pro2R_compat hBLab
  tame_sigma := (sigmaMarkR_spec hBLab).1
  tame_tau := phiR_gammaTau
  tame_x0 := (x0MarkR_spec hBLab).1
  tame_x1 := (x1MarkR_spec hBLab).1
  pro2_sigma := (sigmaMarkR_spec hBLab).2
  pro2_tau := pro2R_gammaTauR hBLab
  pro2_x0 := (x0MarkR_spec hBLab).2
  pro2_x1 := (x1MarkR_spec hBLab).2
  surj := bR_joint_surjective hBLab
  ker_pro2 := ker_pro2R hBLab
  smulZmod2 := RStageGammaR.instDistribMulActionGammaR
  contSMulZmod2 := inferInstance
  htriv := RStageGammaR.htriv_gammaR
  tfg := gammaR_topologicallyFinitelyGenerated
  hom8 := lemma_8_2_R
  cardH2 := SectionEight.LedgerGammaR.card_H2_gammaR
  liftsOver_card := fun RF b F ρ => RF.liftsOver_card_gammaR b F ρ
  lem86 := fun D hedge ρ hρ => SectionEight.LedgerGammaR.lemma_8_6_gammaR D hedge ρ hρ
  stageR136 := fun hE2 hRK hR2 b F => RStageGammaR.stageR136_gammaR_of_hcard hE2 hRK hR2
    SectionEight.LedgerGammaR.card_H2_gammaR b F
  tcocycle_card := fun b F En l h ρ => Phase140GammaR.tcocycle_card_gammaR b F En l h ρ
  hsep := fun b F En l h Dsc ρ c hc => Phase140GammaR.hsep_gammaR b F En l h Dsc ρ c hc
  hpartial := fun b F En l h Dsc ρ χ hχ =>
    Phase140GammaR.hpartial_gammaR b F En l h Dsc ρ χ hχ
  hZcard := fun b F En l h hsimple hVne hnt ρ =>
    Phase140GammaR.hZcard_gammaR b F En l h hsimple hVne hnt ρ
  gaussZ_unramified := fun T Blk => SectionNine.gaussZResidueD_gammaR_unramified T Blk
    (tame := phiR) (pro2 := pro2R hBLab) (compat := pro2R_compat hBLab)
    (htσ := phiR_gammaSigma) (htτ := phiR_gammaTau) (htx0 := phiR_gammaX0)
    (htx1 := phiR_gammaX1)
  gaussZ_ramified := fun T Blk => SectionNine.gaussZResidueD_gammaR_ramified T Blk
    (tame := phiR) (pro2 := pro2R hBLab) (compat := pro2R_compat hBLab)
    (htσ := phiR_gammaSigma) (htτ := phiR_gammaTau) (htx0 := phiR_gammaX0)
    (htx1 := phiR_gammaX1)

/-- The tame field of `sourceR` is `φ_R` on the nose (mirror of
`BoundaryMaps.sourceA_b`'s load-bearing `rfl`). -/
@[simp] theorem sourceR_tame : (sourceR hBLab).tame = phiR := rfl

/-- The carrier of `sourceR` is `Γ_R` on the nose. -/
theorem sourceR_Γ : (sourceR hBLab).Γ = GammaR := rfl

/-! ## The tame coordinate of `b_{Γ_R}` (the per-source Lemma 10.1 hypotheses) -/

/-- The tame coordinate of `b_{Γ_R}` is `φ_R` (mirror of `SectionTen.tameCoord_bA`). -/
theorem tameCoord_bR : SectionTen.tameCoord (sourceR hBLab).b = phiR := by
  ext g
  simp only [SectionTen.tameCoord_apply, SourceData.b_apply_coe, sourceR_tame]

/-- **`htame` for `Γ_R`**: `φ_R` is onto (Prop 3.2, `Γ_R` side; mirror of
`SectionTen.tameCoord_bA_surjective`). -/
theorem tameCoord_bR_surjective :
    Function.Surjective (SectionTen.tameCoord (sourceR hBLab).b) := by
  rw [tameCoord_bR]
  exact phiR_surjective

/-- **`hwild` for `Γ_R`**: the wild inertia `ker φ_R = W_R` is pro-2 (`ker_phiR` +
`isProP_wildCoreR`; mirror of `SectionTen.tameCoord_bA_ker_isProP`). -/
theorem tameCoord_bR_ker_isProP :
    IsProP 2 (SectionTen.tameCoord (sourceR hBLab).b).toMonoidHom.ker := by
  rw [tameCoord_bR]
  show IsProP 2 phiR.toMonoidHom.ker
  rw [ker_phiR]
  exact isProP_wildCoreR

end BoundaryLane

/-! ## Eq. (154) at `Γ_R` and the surjection-count capstones -/

section Capstones

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **Eq. (154) at `Γ_R`** (⟦thm:main⟧, counting layer): the Roe candidate and `G_{ℚ₂}` have
identical continuous-surjection counts onto every finite group.  `card_contSurj_eq` at
`(sourceR hBLab).b` / `boundaryMapsWitness.bF` rewrites each count as the sum of fixed-frame
exact-image counts; `thm_4_2_of_sources` equates them frame by frame — the "R32 path" pinned
by R30.  Stated `calc`-style because the `Γ_R` side enters through `(sourceR hBLab).b`
(definitionally, not syntactically, a `Γ_R`-boundary map). -/
theorem eq_154_R (hBLab : BLabHypothesis) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Finite G] :
    Nat.card (ContSurj GammaR G) = Nat.card (ContSurj AbsGalQ2 G) := by
  have hE2 : ∀ e : E₀, e ^ 2 = 1 := fun _ => Subsingleton.elim _ _
  calc Nat.card (ContSurj GammaR G)
      = ∑ᶠ α : TameFrames G,
          exactImageCount (sourceR hBLab).b (tameFrame α.1 α.2) (tameTarget G) :=
        card_contSurj_eq (sourceR hBLab).b G (tameCoord_bR_surjective hBLab)
          (tameCoord_bR_ker_isProP hBLab) gammaR_topologicallyFinitelyGenerated
    _ = ∑ᶠ α : TameFrames G,
          exactImageCount boundaryMapsWitness.bF (tameFrame α.1 α.2) (tameTarget G) :=
        finsum_congr fun α =>
          thm_4_2_of_sources (sourceR hBLab) boundaryMapsWitness (tameFrame α.1 α.2)
            localReciprocity tameUnitOrientation_witness (tameTarget G) hE2
    _ = Nat.card (ContSurj AbsGalQ2 G) :=
        (card_contSurj_eq boundaryMapsWitness.bF G
          (tameCoord_bF_surjective boundaryMapsWitness)
          (tameCoord_bF_ker_isProP boundaryMapsWitness)
          Foundations.absGalQ2_isTopologicallyFinitelyGenerated).symm

/-- **The `Γ_R` surjection-count capstone** (⟦thm:main⟧, counting layer, mirroring
`SectionTen.main_surjection_count'`): the number of continuous surjections `G_{ℚ₂} ↠ G`
equals the number of admissible **Roe**-marked generating quadruples of `G`
(eq. (154) at `Γ_R` + Prop 2.3 for the Roe words, `prop_2_3_R`). -/
theorem main_surjection_count_R (hBLab : BLabHypothesis) (G : Type) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] : contSurjCount G = admissibleCountR G :=
  (eq_154_R hBLab G).symm.trans (prop_2_3_R (G := G))

/-- **The two admissible-marking semantics agree** on every finite group (the numerical
content R5 verified four ways on `C₂ : 7`, `C₄ : 24`, `V₄ : 42`, `D₄ : 144`, `Q₈ : 144` —
Lean word-level pins, two independent Python engines, and the June LMFDB-verified counts;
`GQ2/Roe/Sanity.lean`, `scripts/roe_sanity_counts.py`). -/
theorem admissibleCountR_eq_admissibleCount (hBLab : BLabHypothesis) (G : Type) [Group G]
    [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    admissibleCountR G = admissibleCount G :=
  (main_surjection_count_R hBLab G).symm.trans (SectionTen.main_surjection_count' G)

end Capstones

/-! ## The Replacement theorem (note ⟦thm:main⟧)

The `AbsGalQ2` topology instances are file-local, exactly as in
`GQ2/PresentationLiteral.lean` (the `Γ_A` literal capstone's pattern), so the terminal
statement carries **no** instance binders — its hypothesis surface is exactly
`BLabHypothesis`. -/

noncomputable local instance absGalQ2_compactSpace_roe : CompactSpace AbsGalQ2 := by
  change CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

noncomputable local instance absGalQ2_totallyDisconnectedSpace_roe :
    TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

/-- **The Replacement theorem** (note ⟦thm:main⟧, verbatim `Γ_R ≅ G_{ℚ₂}`; the R-campaign
terminal theorem): granted the single Labute-classification instance `hBLab` (note
Cor. 3.4 ⟦cor:abstractD0⟧ — an explicit hypothesis, **not** an axiom; discharged by the
L-campaign), the Roe candidate `Γ_R` is continuously isomorphic to `G_{ℚ₂}`.

Instantiates the `main_presentation` schematic at `Γ_R`, mirroring
`GQ2.main_presentation_literal`: the candidate count hypothesis is
`eq_154_R` ∘ `main_surjection_count'` (the `Γ_R` count agrees with `admissibleCount` through
the `G_{ℚ₂}` bridge), the `G_{ℚ₂}` count is `main_surjection_count'`, and the finite-
generation witnesses are `gammaR_topologicallyFinitelyGenerated` (R31a) and B1. -/
theorem main_presentation_literal_roe (hBLab : BLabHypothesis) :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  main_presentation GammaR
    gammaR_topologicallyFinitelyGenerated
    Foundations.absGalQ2_isTopologicallyFinitelyGenerated
    (fun G => (eq_154_R hBLab G).trans (SectionTen.main_surjection_count' G))
    (fun G => SectionTen.main_surjection_count' G)

/-- **The Replacement theorem, unconditionally** (note ⟦thm:main⟧; the campaign's terminal
statement): the Roe candidate `Γ_R` (Definition 1.1 ⟦def:GammaR⟧) is continuously isomorphic
to `G_{ℚ₂}` — no hypotheses, no instance binders.

The single input of `main_presentation_literal_roe`, the Labute classification instance
`BLabHypothesis` (note Cor. 3.4 ⟦cor:abstractD0⟧, `D_R ≅ D₀` as marked Demushkin groups), was
**declined as an axiom** by the owner (2026-07-25) and **discharged as a theorem** by the
L-campaign (2026-07-26): `GQ2.Roe.Labute.bLab` (`GQ2/Roe/Labute/Assembly.lean`) proves it from
the λ-tower stage lemma, the levelwise sets and the profinite Hopfian endgame, at the standard
three axioms and with no `sorry` anywhere in its chain.

Consequently this theorem prints exactly the frozen literature census of the `Γ_A` capstones
(std-3 + the axioms of `GQ2/Foundations/Axioms.lean`) — the Roe route adds **nothing** to the
trust base, which `scripts/check_axioms.sh` (check 5) enforces. -/
theorem main_presentation_literal_roe_unconditional :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  main_presentation_literal_roe Roe.Labute.bLab

/-! ## Stress tests (plan rule 9) -/

/-- **Stress (hypothesis surface).**  The terminal theorem consumes exactly one hypothesis:
`BLabHypothesis`.  No axiom, no instance binder, nothing else. -/
example : BLabHypothesis → Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  main_presentation_literal_roe

/-- **Stress (statement fidelity).**  The `Γ_A` and `Γ_R` literal capstones have the same
statement shape — the note's ⟦thm:main⟧ is `main_presentation_literal` with the candidate
replaced by `Γ_R` (and the B-Lab binder added). -/
example (hBLab : BLabHypothesis) :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)
      ∧ Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  ⟨main_presentation_literal, main_presentation_literal_roe hBLab⟩

/-- **Stress (count shapes).**  The two surjection-count capstones, side by side: same
`G_{ℚ₂}` count, the two word semantics (`admissibleCount` vs `admissibleCountR`). -/
example (hBLab : BLabHypothesis) (G : Type) [Group G] [Finite G] [TopologicalSpace G]
    [DiscreteTopology G] :
    contSurjCount G = admissibleCount G ∧ contSurjCount G = admissibleCountR G :=
  ⟨SectionTen.main_surjection_count' G, main_surjection_count_R hBLab G⟩

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`;
hand-maintained)

  * Theorem 2.1 = ⟦thm:main⟧ (Replacement theorem: `main_presentation_literal_roe`,
    `main_presentation_literal_roe_unconditional`, `eq_154_R`, `main_surjection_count_R`)
  * Definition 1.1 = ⟦def:GammaR⟧ (`GammaR`, carrier of `sourceR`)
  * Lemma 2.1 = ⟦lem:tame⟧ (tame fields of `sourceR`)
  * Lemma 3.1 = ⟦lem:pro2word⟧ (`maxPro2Bridge` leg of `pro2R`)
  * Cor 3.4 = ⟦cor:abstractD0⟧ (`BLabHypothesis`, the binder — discharged by
    `GQ2.Roe.Labute.bLab`, `GQ2/Roe/Labute/Assembly.lean`)
  * Prop 3.6 = ⟦prop:markedpro2⟧ (`markedPro2_R` leg of `pro2R`)
-/
