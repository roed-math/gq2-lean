/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.CorrectionR

/-!
# The `Γ_R` cover-lift kernel (L4) and relator-free descent (L5)

The Roe-candidate twin of the `CoverLift`/`Descend` sections of `GQ2/RStage/GammaA.lean`
(`:726–954`) — the two lemmas the `Γ_R` separation arguments run on.  Both are stated **free of
any `(136)`-frame context** (no `H`/`E`/`T`/`Blk`/`RecursionFrame`), because they have two
independent consumers: the `(136)` R-stage (`GQ2/RStage/GammaR.lean`, ticket R31e) and the `(140)`
T-stage (ticket R31f), whose `Γ_A` originals instantiate the shared `Y` at the section variable
and at the frame field `RF.YB` respectively.

## L4 — `redValues_eq_of_coverLift_R`

If a boundary map `g_B : Γ_R → B₀` lifts through a central double cover `Q`, then any set-lift
marking `t_Y` of `g_B` has **equal** tame and Roe-wild relator values after reduction along
`red : Y → Q.cover`.  Both `t_Y.map red` and the lift's pushed marking cover `g_B`'s marking, so
they differ by corrections in the central 2-torsion kernel `⟨z⟩`; the correction ledger
(`tameValue_correction`, shared with `Γ_A`, and `wildValueR_correction`,
`GQ2/Roe/CorrectionR.lean`) evaluates *both* reduced relator values to the same `r̄₁` — this is
exactly why the two Roe rows had to shift by the *same* central involution.

Statement shape is binder-for-binder the `Γ_A` original `RStageGammaA.redValues_eq_of_coverLift`,
with `Marking.push → Marking.pushR`, `gammaGen → gammaGenR`, `GA → GR`, `wildValue → wildValueR`;
the instance context is even *weaker* (no `TopologicalSpace`/`DiscreteTopology` on `Y` or `B₀`).

## L5 — the relator-free descent, factored

The `Γ_A` original (`RStage/GammaA.lean:829`) is `private` **and** hard-wired to the block frame
(`blockFrameImpl T Blk hE2`, `Blk.frattiniK`), which is precisely why `GQ2/Phase140/GammaA/`
could not reuse it and re-proved a generalised variant (`mlift_of_relatorFree_marking`,
`Foundation.lean:461`).  To avoid repeating that split on the Roe side, the descent is factored
here into three public pieces:

* `exists_pushR_eq_of_relatorFree` — the **frame-free core**: a marking of `Y` that kills both
  `Γ_R` relators and has a pro-2 wild core *is* the pushforward of a continuous `φ : Γ_R → Y`.
  No `π`, no `B₀`, no surjectivity: the cleanest form of "`Γ_R` classifies relator-free markings".
* `isPGroup_wildCore_of_proj` — the `Pro2Core` transfer: an upstairs pro-2 certificate from a
  downstairs one plus 2-torsion of `ker π` (the `hcoreJ` chase of the `Γ_A` original, restated in
  `Y` so it can be reused independently).
* `lift_of_relatorFree_markingR` — the consumer-facing splice of the two, over an **abstract**
  `π : Y →* B₀`.  Strictly more general than the `Γ_A` original: `π` is arbitrary (not
  `blockFrameImpl.piB`), the kernel torsion is a hypothesis (not `hR2` + `ker_piB`), and the
  `Pro2Core` input is taken directly rather than through `Function.Surjective g_B` — so the
  non-surjective T-stage of R31f can supply it after its corestriction, instead of cloning.

## Reused verbatim from `GQ2/RStage/GammaA.lean`, never cloned

`corrMark`, `marking_ext`, `tameValue_correction` (the tame relator is **shared** with `Γ_A`).
The Roe-specific inputs are `RStageGammaR.push_tameRelR` / `push_wildRelR` /
`wildValueR_correction` (`GQ2/Roe/CorrectionR.lean`), `Marking.pushR` / `Marking.descendR` /
`Marking.pushR_descendR` (`GQ2/Roe/Prop23.lean`) and `gammaGenR` (`GQ2/WordCohBridgeR.lean`).

**Module-system note.**  Plain `import` (non-`module`), like its import `GQ2.Roe.CorrectionR` and
that file's own import `GQ2.RStage.GammaA`: `module`-style files cannot import plain ones.

Axioms: none introduced (std-3 only).
-/

namespace GQ2

open ContCoh SectionEight WordCohBridgeR RStageGammaA

namespace RStageGammaR

/-! ## L4 core: a cover lift forces equal reduced relator values -/

section CoverLiftR

variable {Y : Type} [Group Y] [Finite Y]
variable {B0 : Type} [Group B0] [Finite B0] [TopologicalSpace B0]

/-- **The per-cover L4 core for `Γ_R`**, abstractly over a bare central cover: if `g_B` lifts
through `Q` (via `gc`), then any set-lift marking `tY` of `g_B` has equal tame and **Roe**-wild
relator values after reduction along `red`.  Both `tY.map red` and the lift's pushed marking cover
`g_B`'s marking, so they differ by corrections in the central 2-torsion kernel
(`CentralCover.central`/`z_sq`); the correction calculus (`tameValue_correction`, shared with
`Γ_A`, and `wildValueR_correction`) evaluates both reduced relator values to the same `r̄₁`.

`Γ_R` twin of `RStageGammaA.redValues_eq_of_coverLift`, binder-for-binder.  Deliberately free of
frame context so that both the `(136)` R-stage (R31e) and the `(140)` T-stage (R31f) can
instantiate `Y` at their own carriers. -/
theorem redValues_eq_of_coverLift_R (Q : CentralCover B0) (piB : Y →* B0)
    (red : Y →* Q.cover) (hred_p : Q.p.comp red = piB)
    (gB : ContinuousMonoidHom GR B0)
    (gc : ContinuousMonoidHom GR Q.cover) (hgc : ∀ γ, Q.p (gc γ) = gB γ)
    (tY : Marking Y) (hproj : tY.map piB = Marking.pushR gB) :
    red tY.tameValue = red tY.wildValueR := by
  have hred_p' : ∀ y : Y, Q.p (red y) = piB y := fun y => DFunLike.congr_fun hred_p y
  -- the lift's marking; its relators die (both relator words lie in `N_R`)
  have htame1 : (Marking.pushR gc).tameValue = 1 :=
    (Marking.tameValue_eq_one_iff _).mpr (push_tameRelR gc)
  have hwild1 : (Marking.pushR gc).wildValueR = 1 :=
    (Marking.wildValueR_eq_one_iff _).mpr (push_wildRelR gc)
  -- both markings cover `g_B`'s marking: the field discrepancies live in `ker Q.p`
  have hpr : ∀ (a : Y) (w : Q.cover), Q.p (red a) = Q.p w → red a * w⁻¹ ∈ Q.p.ker := by
    intro a w h
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hσ' : Q.p (red tY.σ) = Q.p (Marking.pushR gc).σ := by
    rw [hred_p', show piB tY.σ = (Marking.pushR gB).σ from congrArg Marking.σ hproj]
    exact (hgc gammaGenR.σ).symm
  have hτ' : Q.p (red tY.τ) = Q.p (Marking.pushR gc).τ := by
    rw [hred_p', show piB tY.τ = (Marking.pushR gB).τ from congrArg Marking.τ hproj]
    exact (hgc gammaGenR.τ).symm
  have hx₀' : Q.p (red tY.x₀) = Q.p (Marking.pushR gc).x₀ := by
    rw [hred_p', show piB tY.x₀ = (Marking.pushR gB).x₀ from congrArg Marking.x₀ hproj]
    exact (hgc gammaGenR.x₀).symm
  have hx₁' : Q.p (red tY.x₁) = Q.p (Marking.pushR gc).x₁ := by
    rw [hred_p', show piB tY.x₁ = (Marking.pushR gB).x₁ from congrArg Marking.x₁ hproj]
    exact (hgc gammaGenR.x₁).symm
  have hmem0 : red tY.σ * ((Marking.pushR gc).σ)⁻¹ ∈ Q.p.ker := hpr tY.σ _ hσ'
  have hmem1 : red tY.τ * ((Marking.pushR gc).τ)⁻¹ ∈ Q.p.ker := hpr tY.τ _ hτ'
  have hmem2 : red tY.x₀ * ((Marking.pushR gc).x₀)⁻¹ ∈ Q.p.ker := hpr tY.x₀ _ hx₀'
  have hmem3 : red tY.x₁ * ((Marking.pushR gc).x₁)⁻¹ ∈ Q.p.ker := hpr tY.x₁ _ hx₁'
  -- kernel elements are central involutions (`⟨z⟩`, `z` central of square one)
  have hcen : ∀ w : Q.cover, w ∈ Q.p.ker → ∀ z : Q.cover, Commute w z := by
    intro w hw z
    rw [Q.ker_eq] at hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact Commute.zpow_left (Q.central z) n
  have hsq : ∀ w : Q.cover, w ∈ Q.p.ker → w ^ 2 = 1 := by
    intro w hw
    rw [pow_two]
    exact Q.sq_eq_one_of_mem_ker hw
  -- the reduced set-lift marking is the corrected lift marking
  have hcorr : tY.map red = corrMark (Marking.pushR gc)
      (red tY.σ * ((Marking.pushR gc).σ)⁻¹) (red tY.τ * ((Marking.pushR gc).τ)⁻¹)
      (red tY.x₀ * ((Marking.pushR gc).x₀)⁻¹) (red tY.x₁ * ((Marking.pushR gc).x₁)⁻¹) := by
    refine marking_ext ?_ ?_ ?_ ?_ <;> exact (inv_mul_cancel_right _ _).symm
  -- both reduced relator values are the τ-correction `r̄₁` (L1 at the central 2-torsion kernel)
  have hredT : red tY.tameValue = red tY.τ * ((Marking.pushR gc).τ)⁻¹ := by
    have h := Marking.map_tameValue red tY
    rw [hcorr] at h
    rw [← h,
      show corrMark (Marking.pushR gc) (red tY.σ * ((Marking.pushR gc).σ)⁻¹)
          (red tY.τ * ((Marking.pushR gc).τ)⁻¹) (red tY.x₀ * ((Marking.pushR gc).x₀)⁻¹)
          (red tY.x₁ * ((Marking.pushR gc).x₁)⁻¹)
        = Marking.mk (red tY.σ * ((Marking.pushR gc).σ)⁻¹ * (Marking.pushR gc).σ)
            (red tY.τ * ((Marking.pushR gc).τ)⁻¹ * (Marking.pushR gc).τ)
            (red tY.x₀ * ((Marking.pushR gc).x₀)⁻¹ * (Marking.pushR gc).x₀)
            (red tY.x₁ * ((Marking.pushR gc).x₁)⁻¹ * (Marking.pushR gc).x₁) from rfl,
      tameValue_correction _ _ _ _ _ _ (hcen _ hmem0) (hcen _ hmem1) (hsq _ hmem1),
      show (Marking.mk (Marking.pushR gc).σ (Marking.pushR gc).τ
            (red tY.x₀ * ((Marking.pushR gc).x₀)⁻¹ * (Marking.pushR gc).x₀)
            (red tY.x₁ * ((Marking.pushR gc).x₁)⁻¹ * (Marking.pushR gc).x₁)).tameValue
          = (Marking.pushR gc).tameValue from rfl,
      htame1, mul_one]
  have hredW : red tY.wildValueR = red tY.τ * ((Marking.pushR gc).τ)⁻¹ := by
    have h := Marking.map_wildValueR red tY
    rw [hcorr] at h
    rw [← h,
      wildValueR_correction (hcen _ hmem0) (hcen _ hmem1) (hcen _ hmem2) (hcen _ hmem3)
        (hsq _ hmem0) (hsq _ hmem1) (hsq _ hmem2) (hsq _ hmem3),
      hwild1, mul_one]
  rw [hredT, hredW]

end CoverLiftR

/-! ## L5 descent: a relator-free covering marking of `Y` descends from `Γ_R` -/

section DescendR

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {B0 : Type} [Group B0] [TopologicalSpace B0] [DiscreteTopology B0] [Finite B0]

/-- **L5 core, frame-free**: a marking of `Y` that kills both `Γ_R` relators and whose wild core
is pro-2 **is** the pushforward of a continuous `φ : Γ_R → Y`.  The marking generates a subgroup
`J ≤ Y` on which it is `R`-admissible (`Generates` by construction; `TameRel`/`WildRelR` by
subtype injectivity; `Pro2Core` by pulling the `Y`-certificate back along the injective
`J.subtype`), hence `Marking.descendR` applies and `Marking.pushR_descendR` returns the marking.

This is the honest content of the `Γ_A` original `lift_of_relatorFree_marking`, stripped of the
block frame — the `π`/`g_B` projection statement is the corollary
`lift_of_relatorFree_markingR` below. -/
theorem exists_pushR_eq_of_relatorFree (tHat : Marking Y) (htame : tHat.TameRel)
    (hwild : tHat.WildRelR)
    (hcore : IsPGroup 2 (Subgroup.normalClosure ({tHat.x₀, tHat.x₁} : Set Y))) :
    ∃ φ : ContinuousMonoidHom GR Y, Marking.pushR φ = tHat := by
  classical
  -- the generated subgroup and its marking
  set J : Subgroup Y := Subgroup.closure {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} with hJ
  have hmemσ : tHat.σ ∈ J := Subgroup.subset_closure (by simp)
  have hmemτ : tHat.τ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₀ : tHat.x₀ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₁ : tHat.x₁ ∈ J := Subgroup.subset_closure (by simp)
  set tJ : Marking ↥J :=
    ⟨⟨tHat.σ, hmemσ⟩, ⟨tHat.τ, hmemτ⟩, ⟨tHat.x₀, hmemx₀⟩, ⟨tHat.x₁, hmemx₁⟩⟩ with htJ
  have hmapJ : tJ.map J.subtype = tHat := marking_ext rfl rfl rfl rfl
  -- the relations, by subtype injectivity
  have htameJ : tJ.TameRel := by
    rw [← Marking.tameValue_eq_one_iff]
    have h := Marking.map_tameValue J.subtype tJ
    rw [hmapJ, (Marking.tameValue_eq_one_iff tHat).mpr htame] at h
    exact Subtype.val_injective h.symm
  have hwildJ : tJ.WildRelR := by
    rw [← Marking.wildValueR_eq_one_iff]
    have h := Marking.map_wildValueR J.subtype tJ
    rw [hmapJ, (Marking.wildValueR_eq_one_iff tHat).mpr hwild] at h
    exact Subtype.val_injective h.symm
  -- generation: the closure of the generators inside their own closure is everything
  have hgenJ : tJ.Generates := by
    show Subgroup.closure {tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} = ⊤
    have hpre : ({tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} : Set ↥J)
        = ((↑) : ↥J → Y) ⁻¹' {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} := by
      ext j
      simp [htJ, Subtype.ext_iff]
    rw [hpre]
    exact Subgroup.closure_closure_coe_preimage
  -- the 2-core: `J`-conjugates are `Y`-conjugates, so the `Y`-certificate pulls back
  have hcoreJ : tJ.Pro2Core := by
    show IsPGroup 2 (Subgroup.normalClosure {tJ.x₀, tJ.x₁})
    haveI : (Subgroup.normalClosure ({tHat.x₀, tHat.x₁} : Set Y)).Normal :=
      Subgroup.normalClosure_normal
    refine IsPGroup.to_le (IsPGroup.comap_of_injective hcore J.subtype Subtype.val_injective) ?_
    refine Subgroup.normalClosure_le_normal ?_
    rintro z (rfl | rfl)
    · exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
    · exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)
  have hadmJ : tJ.AdmissibleR := ⟨hgenJ, htameJ, hwildJ, hcoreJ⟩
  -- descend into `J`, then include into `Y`
  set φY : ContinuousMonoidHom ↥J Y := ⟨J.subtype, continuous_subtype_val⟩ with hφY
  refine ⟨φY.comp (Marking.descendR tJ hadmJ), ?_⟩
  show (Marking.pushR (Marking.descendR tJ hadmJ)).map J.subtype = tHat
  rw [Marking.pushR_descendR, hmapJ]

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] [DiscreteTopology B0] [Finite B0] in
/-- **The `Pro2Core` transfer.**  If `t_Y` covers `g_B`'s marking through `π` and the elements of
`ker π` are involutions, then a pro-2 wild core downstairs gives one upstairs: an element of the
normal closure of `{x₀, x₁}` in `Y` maps into the normal closure downstairs, so some `2^k`-th
power lands in `ker π`, and one more squaring kills it.

This is the `hcoreJ` chase of `RStageGammaA.lift_of_relatorFree_marking` (`:877–916`), restated
in `Y` and detached from `blockFrameImpl`/`Blk.frattiniK` so that both `Γ_R` stages can feed it
their own kernel-torsion certificate. -/
theorem isPGroup_wildCore_of_proj (π : Y →* B0) (hker2 : ∀ y ∈ π.ker, y * y = 1)
    (gB : ContinuousMonoidHom GR B0) (hcoreB : (Marking.pushR gB).Pro2Core)
    (tHat : Marking Y) (hproj : tHat.map π = Marking.pushR gB) :
    IsPGroup 2 (Subgroup.normalClosure ({tHat.x₀, tHat.x₁} : Set Y)) := by
  haveI hNB : (Subgroup.normalClosure
      {(Marking.pushR gB).x₀, (Marking.pushR gB).x₁}).Normal := Subgroup.normalClosure_normal
  have hcomap : ({tHat.x₀, tHat.x₁} : Set Y) ⊆
      ((Subgroup.normalClosure
        {(Marking.pushR gB).x₀, (Marking.pushR gB).x₁}).comap π : Set Y) := by
    rintro z (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap,
        show π tHat.x₀ = (Marking.pushR gB).x₀ from congrArg Marking.x₀ hproj]
      exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, Subgroup.mem_comap,
        show π tHat.x₁ = (Marking.pushR gB).x₁ from congrArg Marking.x₁ hproj]
      exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)
  have hle := Subgroup.normalClosure_le_normal hcomap
  intro n
  obtain ⟨k, hk⟩ := hcoreB ⟨π n.1, Subgroup.mem_comap.mp (hle n.2)⟩
  refine ⟨k + 1, ?_⟩
  have hk' : (π n.1) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine Subtype.val_injective ?_
  show (n.1 : Y) ^ 2 ^ (k + 1) = 1
  rw [pow_succ, pow_mul, pow_two]
  exact hker2 _ (MonoidHom.mem_ker.mpr (by rw [map_pow]; exact hk'))

/-- **L5, the descent** (consumer-facing form): a marking of `Y` that covers `g_B`'s marking
through an arbitrary `π : Y →* B₀` and kills both `Γ_R` relators descends to a continuous
`φ : Γ_R → Y` with `π ∘ φ = g_B`.  The projection identity holds because two `F₄`-classified homs
with equal pushed markings agree (`Marking.toHom_hom_univMarking_map`).

`Γ_R` twin of the `private` `RStageGammaA.lift_of_relatorFree_marking`, and strictly more general:
`π` is abstract, the kernel torsion is a hypothesis, and `Pro2Core` is taken directly instead of
via `Function.Surjective g_B` — which is exactly what the non-surjective `(140)` T-stage needs
(cf. `GQ2/Phase140/GammaA/Foundation.lean:461`, where the `Γ_A` side had to clone). -/
theorem lift_of_relatorFree_markingR (π : Y →* B0) (hker2 : ∀ y ∈ π.ker, y * y = 1)
    (gB : ContinuousMonoidHom GR B0) (hcoreB : (Marking.pushR gB).Pro2Core)
    (tHat : Marking Y) (hproj : tHat.map π = Marking.pushR gB)
    (htame : tHat.TameRel) (hwild : tHat.WildRelR) :
    ∃ φ : ContinuousMonoidHom GammaR Y, ∀ γ, π (φ γ) = gB γ := by
  classical
  obtain ⟨φ, hφ⟩ := exists_pushR_eq_of_relatorFree tHat htame hwild
    (isPGroup_wildCore_of_proj π hker2 gB hcoreB tHat hproj)
  refine ⟨φ, ?_⟩
  intro γ
  obtain ⟨w, rfl⟩ := quotientMk_surjective NR γ
  -- both sides are `F₄`-classified with the same pushed marking
  set πc : ContinuousMonoidHom Y B0 := ⟨π, continuous_of_discreteTopology⟩ with hπc
  set c₁ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) B0 :=
    (πc.comp φ).comp (quotientMk NR) with hc₁
  set c₂ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) B0 :=
    gB.comp (quotientMk NR) with hc₂
  have hpush : univMarking.map c₁.toMonoidHom = univMarking.map c₂.toMonoidHom := by
    show Marking.pushR (πc.comp φ) = Marking.pushR gB
    rw [show Marking.pushR (πc.comp φ) = (Marking.pushR φ).map π from rfl, hφ, hproj]
  have hc : c₁ = c₂ := by
    rw [← Marking.toHom_hom_univMarking_map c₁, ← Marking.toHom_hom_univMarking_map c₂, hpush]
  exact DFunLike.congr_fun hc w

end DescendR

end RStageGammaR

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.2) = ⟦eq:relators⟧ — the Roe wild relator whose central-involution correction ledger
    (`wildValueR_correction`) makes the two reduced relator values coincide in L4.
  * Definition 1.1 = ⟦def:GammaR⟧ — `N_R`/`AdmissibleR`, via `Marking.descendR` in L5.
-/
