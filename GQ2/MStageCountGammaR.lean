/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.MStageCountGammaA
import GQ2.Roe.CorrectionR
import GQ2.Roe.DualityAssembly
import GQ2.Roe.Prop23
import GQ2.SourceData

/-!
# The `Γ_R`-side `M`-stage multiplicity count (obligation ii.3)

The `Γ_R` twin of `GQ2/MStageCountGammaA.lean`: the `M`-stage lane of `thm_4_2` applies
`mStage_partition` with multiplicity `mult = |M_B|²`, and this file supplies the **`Γ_R`** count
`#LiftsOver_{Γ_R}(ρ) = |M_B|²` — the `SourceData.liftsOver_card` field at `Γ := Γ_R` (recon row
ii.3), whose `Γ_A` occupant is `RecursionFrame.liftsOver_card_gammaA`.

The port is line-for-line against the `Γ_A` original, with the Roe wild word substituted
throughout (`GA → GR`, `markC → markC_R`, `Marking.push → Marking.pushR`, `WildRel → WildRelR`,
`Marking.descend → Marking.descendR`, `Admissible → AdmissibleR`, `prop_5_15 → prop_5_15_R`,
`z1Equiv → z1EquivR`, `d1Fun/d1/H2w → d1FunR/d1R/H2wR`).  The two places where the Roe candidate
duality actually enters are exactly the two `prop_5_15_R` calls, both immediately after
`markC_admissible_R θ hθs`:

* **the `Z¹` count** (`liftsOver_card_gammaR_of_nonempty`, clause `.2.1`) — there is no local
  Euler characteristic for `Γ_R` either, so `z1EquivR` (`GQ2/WordCohBridgeR.lean`, R31b)
  identifies `Z¹_cont(Γ_R, M_B)` with the Roe word cocycles `Z¹_{word,R}(markC_R ρ)` and
  `prop_5_15_R` clause 2 counts those as `|M_B|² · #fixedPts_C(M_B^∨)`;
* **nonemptiness** (`liftsOver_nonempty_gammaR`, clause `.1`) — `#H²_{word,R} = #fixedPts = 1`
  puts the Roe relator pair `(v₁, v₂)` in `range (d¹_R (markC_R θ))`, so the set-lift marking's
  relator values are correctable (`RStageGammaA.corrected_tameValue` for the shared tame row,
  `RStageGammaR.corrected_wildValueR` for the Roe wild row, both transported by
  `RStageGammaR.d1FunR_base_change`) and the corrected marking descends through `Marking.descendR`
  (`descend_piBC_R`, the `π_{BC}` port of the Roe L5 descent).

`#fixedPts = 1` is the source-independent `lemma_7_1_dual` bridge: it lives in the shared `M_B`
module pack (`MB_mul_comm`/`MB_conj_eq`/`MB_add_self`/`mbCommGroup`/`mbSec`/`mbConjActC`/
`card_fixedPts_MB_dual`), which is `private` in both `GQ2/MStageCount.lean` and
`GQ2/MStageCountGammaA.lean` and is therefore carried here as a third `private` copy — source-free
in all three, and unchanged from the `Γ_A` text.

Axioms (target at close): `⊆ std-3 + B6 + B7` (as `liftsOver_card_gammaA`; B6/B7 enter through
`prop_5_15_R`'s duality assembly, exactly as they do through `prop_5_15`).

**Module-system note.**  Plain `import` (non-`module`), like its `Γ_A` original: it imports the
non-`module` files `GQ2.MStageCountGammaA` / `GQ2.Roe.CorrectionR` / `GQ2.Roe.Prop23` /
`GQ2.SourceData`.  Importing the `module` file `GQ2.Roe.DualityAssembly` from here is fine — the
restriction is one-directional.
-/

namespace GQ2

namespace SectionEight

open ContCoh SectionSeven WordCohBridgeR GQ2.FoxH RStageGammaA RStageGammaR

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **L5 descent through `π_{BC}`, Roe word** (the `Γ_R` twin of the private
`RecursionFrame.descend_piBC`): a marking of `B` covering `ρ`'s marking through `π_{BC}` and
killing the tame and the **Roe wild** relator descends to a continuous `φ : Γ_R → B` with
`π_{BC} ∘ φ = ρc`.  Same proof as the `Γ_A` version — the generated subgroup `J ≤ B` is
`R`-admissible (`Generates` by construction, `TameRel`/`WildRelR` by subtype injectivity,
`Pro2Core` by pushing to `ρc`'s `R`-admissible marking with the kernel `M_B` 2-torsion via
`MB_elem`) — with `Marking.descend`/`Admissible`/`N_A` replaced by
`Marking.descendR`/`AdmissibleR`/`N_R`. -/
private theorem RecursionFrame.descend_piBC_R (RF : RecursionFrame T Blk)
    (ρc : ContinuousMonoidHom GR RF.YC) (hsurj : Function.Surjective ρc)
    (tHat : Marking RF.YB) (hproj : tHat.map RF.piBC = Marking.pushR ρc)
    (htame : tHat.TameRel) (hwild : tHat.WildRelR) :
    ∃ φ : ContinuousMonoidHom GammaR RF.YB, ∀ γ, RF.piBC (φ γ) = ρc γ := by
  classical
  set J : Subgroup RF.YB := Subgroup.closure {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} with hJ
  have hmemσ : tHat.σ ∈ J := Subgroup.subset_closure (by simp)
  have hmemτ : tHat.τ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₀ : tHat.x₀ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₁ : tHat.x₁ ∈ J := Subgroup.subset_closure (by simp)
  set tJ : Marking ↥J :=
    ⟨⟨tHat.σ, hmemσ⟩, ⟨tHat.τ, hmemτ⟩, ⟨tHat.x₀, hmemx₀⟩, ⟨tHat.x₁, hmemx₁⟩⟩ with htJ
  have hmapJ : tJ.map J.subtype = tHat := marking_ext rfl rfl rfl rfl
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
  have hgenJ : tJ.Generates := by
    show Subgroup.closure {tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} = ⊤
    have hpre : ({tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} : Set ↥J)
        = ((↑) : ↥J → RF.YB) ⁻¹' {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} := by
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> simp [htJ]
      · rintro (h | h | h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
    rw [hpre]
    exact Subgroup.closure_closure_coe_preimage
  have hcoreJ : tJ.Pro2Core := by
    show IsPGroup 2 (Subgroup.normalClosure {tJ.x₀, tJ.x₁})
    have hadmB : (Marking.pushR ρc).AdmissibleR := Marking.pushR_admissible ρc hsurj
    set qJ : ↥J →* RF.YC := RF.piBC.comp J.subtype with hqJ
    haveI hNB : (Subgroup.normalClosure
        {(Marking.pushR ρc).x₀, (Marking.pushR ρc).x₁}).Normal := Subgroup.normalClosure_normal
    haveI hNBc : ((Subgroup.normalClosure
        {(Marking.pushR ρc).x₀, (Marking.pushR ρc).x₁}).comap qJ).Normal := hNB.comap qJ
    have hcomap : ({tJ.x₀, tJ.x₁} : Set ↥J) ⊆
        ((Subgroup.normalClosure
          {(Marking.pushR ρc).x₀, (Marking.pushR ρc).x₁}).comap qJ : Set ↥J) := by
      rintro z hz
      rcases hz with rfl | hz
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        have h1 : qJ tJ.x₀ = (Marking.pushR ρc).x₀ := congrArg Marking.x₀ hproj
        rw [h1]
        exact Subgroup.subset_normalClosure (by simp)
      · rcases hz with rfl
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        have h1 : qJ tJ.x₁ = (Marking.pushR ρc).x₁ := congrArg Marking.x₁ hproj
        rw [h1]
        exact Subgroup.subset_normalClosure (by simp)
    have hle := Subgroup.normalClosure_le_normal hcomap
    intro n
    obtain ⟨k, hk⟩ := hadmB.2.2.2 ⟨qJ n.1, Subgroup.mem_comap.mp (hle n.2)⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (qJ n.1) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hYval : ((n.1 : RF.YB)) ^ 2 ^ (k + 1) = 1 := by
      have hmemM : ((n.1 : RF.YB)) ^ 2 ^ k ∈ RF.MB := by
        rw [← RF.ker_piBC, MonoidHom.mem_ker, map_pow]
        exact hk'
      rw [pow_succ, pow_mul, pow_two]
      exact RF.MB_elem _ hmemM
    exact Subtype.val_injective (by
      simpa using Subtype.val_injective (by simpa using hYval :
        ((n.1 ^ 2 ^ (k + 1) : ↥J) : RF.YB) = ((1 : ↥J) : RF.YB)))
  have hadmJ : tJ.AdmissibleR := ⟨hgenJ, htameJ, hwildJ, hcoreJ⟩
  set φY : ContinuousMonoidHom ↥J RF.YB := ⟨J.subtype, continuous_subtype_val⟩ with hφY
  refine ⟨φY.comp (Marking.descendR tJ hadmJ), ?_⟩
  intro γ
  obtain ⟨w, rfl⟩ := quotientMk_surjective NR γ
  set c₁ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) RF.YC :=
    (⟨RF.piBC, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom RF.YB RF.YC).comp
      (φY.comp (Marking.classify tJ)) with hc₁
  set c₂ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) RF.YC :=
    ρc.comp (quotientMk NR) with hc₂
  have hclassify : univMarking.map (Marking.classify tJ).toMonoidHom = tJ :=
    univMarking_map_toHom (P := ProfiniteGrp.of ↥J) tJ
  have hpush : univMarking.map c₁.toMonoidHom = univMarking.map c₂.toMonoidHom := by
    refine marking_ext ?_ ?_ ?_ ?_
    · have h1 : (Marking.classify tJ) univMarking.σ = tJ.σ := congrArg Marking.σ hclassify
      show RF.piBC (φY ((Marking.classify tJ) univMarking.σ)) = ρc (quotientMk NR univMarking.σ)
      rw [h1]; exact congrArg Marking.σ hproj
    · have h1 : (Marking.classify tJ) univMarking.τ = tJ.τ := congrArg Marking.τ hclassify
      show RF.piBC (φY ((Marking.classify tJ) univMarking.τ)) = ρc (quotientMk NR univMarking.τ)
      rw [h1]; exact congrArg Marking.τ hproj
    · have h1 : (Marking.classify tJ) univMarking.x₀ = tJ.x₀ := congrArg Marking.x₀ hclassify
      show RF.piBC (φY ((Marking.classify tJ) univMarking.x₀)) = ρc (quotientMk NR univMarking.x₀)
      rw [h1]; exact congrArg Marking.x₀ hproj
    · have h1 : (Marking.classify tJ) univMarking.x₁ = tJ.x₁ := congrArg Marking.x₁ hclassify
      show RF.piBC (φY ((Marking.classify tJ) univMarking.x₁)) = ρc (quotientMk NR univMarking.x₁)
      rw [h1]; exact congrArg Marking.x₁ hproj
  have hc : c₁ = c₂ := by
    have h1 := Marking.toHom_hom_univMarking_map c₁
    have h2 := Marking.toHom_hom_univMarking_map c₂
    rw [← h1, ← h2, hpush]
  exact DFunLike.congr_fun hc w

/-! ### The shared `M_B` module pack (third `private` copy)

Verbatim from `GQ2/MStageCountGammaA.lean:164-361` (itself a copy of `GQ2/MStageCount.lean`'s):
`M_B ⊴ Y_B` is elementary abelian (2-torsion by `MB_elem`), carries the `Y_C`-conjugation action
through a set-section of `π_{BC}`, and has no nonzero `Y_C`-invariant `𝔽₂`-functional
(`lemma_7_1_dual`).  Every declaration here is **source-free** — no marking word appears — so the
Roe port changes nothing; the copy exists only because the originals are `private` to their
modules.  The twins install the pack by `letI`/`have` and diverge at their coboundary/torsor
tails. -/
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Elements of `M_B` commute: 2-torsion (`MB_elem`) makes every element self-inverse, so
`xy = (xy)⁻¹ = y⁻¹x⁻¹ = yx`. -/
private theorem RecursionFrame.MB_mul_comm (RF : RecursionFrame T Blk) :
    ∀ x ∈ RF.MB, ∀ y ∈ RF.MB, x * y = y * x := by
  intro x hx y hy
  rw [← inv_eq_of_mul_eq_one_right (RF.MB_elem _ (mul_mem hx hy)), mul_inv_rev,
    inv_eq_of_mul_eq_one_right (RF.MB_elem _ hy), inv_eq_of_mul_eq_one_right (RF.MB_elem _ hx)]

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Conjugation on `M_B` depends only on the `π_{BC}`-image of the conjugator: two preimages
differ by a kernel element, which is central in `M_B`. -/
private theorem RecursionFrame.MB_conj_eq (RF : RecursionFrame T Blk) {u v : RF.YB}
    (huv : RF.piBC u = RF.piBC v) (m : ↥RF.MB) : u * m.1 * u⁻¹ = v * m.1 * v⁻¹ := by
  have hm : u⁻¹ * v ∈ RF.MB := by
    rw [← RF.ker_piBC]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, huv, inv_mul_cancel])
  calc u * m.1 * u⁻¹
      = u * (m.1 * (u⁻¹ * v) * (u⁻¹ * v)⁻¹) * u⁻¹ := by group
    _ = u * ((u⁻¹ * v) * m.1 * (u⁻¹ * v)⁻¹) * u⁻¹ := by rw [← RF.MB_mul_comm _ hm _ m.2]
    _ = v * m.1 * v⁻¹ := by group

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `M_B` is 2-torsion additively: `a + a = 0` in `Additive ↥M_B`. -/
private theorem RecursionFrame.MB_add_self (RF : RecursionFrame T Blk)
    (a : Additive ↥RF.MB) : a + a = 0 :=
  Additive.toMul.injective (Subtype.ext (RF.MB_elem _ (Additive.toMul a).2))

/-- The commutative-group structure on `M_B` (2-torsion ⟹ abelian, `MB_mul_comm`). -/
@[reducible] private def RecursionFrame.mbCommGroup (RF : RecursionFrame T Blk) :
    CommGroup ↥RF.MB :=
  { (inferInstance : Group ↥RF.MB) with
    mul_comm := fun a b => Subtype.ext (RF.MB_mul_comm _ a.2 _ b.2) }

/-- A set-section of `π_{BC}` (choice-picked; `MB_conj_eq` makes the induced conjugation on
`M_B` independent of the choice). -/
private noncomputable def RecursionFrame.mbSec (RF : RecursionFrame T Blk) : RF.YC → RF.YB :=
  Function.surjInv RF.piBC_surj

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
private theorem RecursionFrame.mbSec_spec (RF : RecursionFrame T Blk) (c : RF.YC) :
    RF.piBC (RF.mbSec c) = c :=
  Function.surjInv_eq RF.piBC_surj c

/-- The `Y_C`-conjugation action on the additivized `M_B`, through the set-section `mbSec`
(well-defined by `MB_conj_eq`). -/
@[reducible] private noncomputable def RecursionFrame.mbConjActC (RF : RecursionFrame T Blk) :
    letI := RF.mbCommGroup
    DistribMulAction RF.YC (Additive ↥RF.MB) :=
  letI := RF.mbCommGroup
  { smul := fun c m => Additive.ofMul
      ⟨RF.mbSec c * (Additive.toMul m).1 * (RF.mbSec c)⁻¹,
        RF.MB_normal.conj_mem _ (Additive.toMul m).2 _⟩
    one_smul := fun m => by
      apply Additive.toMul.injective; apply Subtype.ext
      show RF.mbSec 1 * (Additive.toMul m).1 * (RF.mbSec 1)⁻¹ = (Additive.toMul m).1
      have h1 : RF.mbSec 1 ∈ RF.MB := by
        rw [← RF.ker_piBC]
        exact MonoidHom.mem_ker.mpr (RF.mbSec_spec 1)
      rw [RF.MB_mul_comm _ h1 _ (Additive.toMul m).2]; group
    mul_smul := fun c c' m => by
      apply Additive.toMul.injective; apply Subtype.ext
      show RF.mbSec (c * c') * (Additive.toMul m).1 * (RF.mbSec (c * c'))⁻¹
        = RF.mbSec c * (RF.mbSec c' * (Additive.toMul m).1 * (RF.mbSec c')⁻¹) * (RF.mbSec c)⁻¹
      rw [show RF.mbSec c * (RF.mbSec c' * (Additive.toMul m).1 * (RF.mbSec c')⁻¹)
            * (RF.mbSec c)⁻¹
          = (RF.mbSec c * RF.mbSec c') * (Additive.toMul m).1 * (RF.mbSec c * RF.mbSec c')⁻¹
          from by group]
      exact RF.MB_conj_eq (by rw [RF.mbSec_spec, map_mul, RF.mbSec_spec, RF.mbSec_spec])
        (Additive.toMul m)
    smul_zero := fun c => by
      apply Additive.toMul.injective; apply Subtype.ext
      show RF.mbSec c * (1 : RF.YB) * (RF.mbSec c)⁻¹ = 1
      group
    smul_add := fun c m m' => by
      apply Additive.toMul.injective; apply Subtype.ext
      show RF.mbSec c * ((Additive.toMul m).1 * (Additive.toMul m').1) * (RF.mbSec c)⁻¹
        = (RF.mbSec c * (Additive.toMul m).1 * (RF.mbSec c)⁻¹)
            * (RF.mbSec c * (Additive.toMul m').1 * (RF.mbSec c)⁻¹)
      group }

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`#(M_B^∨)^{Y_C} = 1`** — the source-independent `lemma_7_1_dual` bridge shared by both
twins: a nonzero `Y_C`-invariant functional `λ : M_B^∨` would push `ker λ` to an index-2
`Y`-normal subgroup between `Φ(K)` and `K`, which `lemma_7_1_dual` forbids. -/
private theorem RecursionFrame.card_fixedPts_MB_dual (RF : RecursionFrame T Blk) :
    letI := RF.mbCommGroup
    letI := RF.mbConjActC
    Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1 := by
  classical
  letI := RF.mbCommGroup
  letI := RF.mbConjActC
  show Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1
  have hzero : ∀ lam : ElemDual (Additive ↥RF.MB),
      (∀ g : RF.YC, g • lam = lam) → lam = 0 := by
    intro lam hlam
    by_contra hlamne
    have hinv : ∀ (c : RF.YC) (a : Additive ↥RF.MB), lam (c • a) = lam a := by
      intro c a
      have h2 : (c⁻¹ • lam) a = lam a := by rw [hlam c⁻¹]
      rwa [ElemDual.smul_apply, inv_inv] at h2
    have hmem : ∀ k : ↥Blk.K, RF.piB k.1 ∈ RF.MB := by
      intro k
      rw [RF.MB_eq]; exact Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩
    let s : ↥Blk.K →* ↥RF.MB :=
      (RF.piB.comp Blk.K.subtype).codRestrict RF.MB (fun k => hmem k)
    have hs : ∀ k : ↥Blk.K, (s k).1 = RF.piB k.1 := fun _ => rfl
    have hs_surj : Function.Surjective s := by
      intro m
      obtain ⟨k, hk, hkeq⟩ := (RF.MB_eq ▸ m.2 : m.1 ∈ Blk.K.map RF.piB)
      exact ⟨⟨k, hk⟩, Subtype.ext hkeq⟩
    let φ : ↥Blk.K →* Multiplicative (ZMod 2) :=
      { toFun := fun k => Multiplicative.ofAdd (lam (Additive.ofMul (s k)))
        map_one' := by simp
        map_mul' := fun a b => by simp [map_mul] }
    have hφ_apply : ∀ k, φ k = Multiplicative.ofAdd (lam (Additive.ofMul (s k))) := fun _ => rfl
    have hφne : φ ≠ 1 := by
      intro hφ1
      apply hlamne
      ext a
      show lam a = 0
      obtain ⟨k, hk⟩ := hs_surj (Additive.toMul a)
      have h0 : lam (Additive.ofMul (s k)) = 0 := by
        simpa [hφ_apply] using congrArg Multiplicative.toAdd (show φ k = 1 by rw [hφ1]; rfl)
      rw [hk] at h0
      exact h0
    have hφsurj : Function.Surjective φ := by
      intro y
      rcases eq_or_ne y 1 with rfl | hy
      · exact ⟨1, map_one φ⟩
      · obtain ⟨k, hk⟩ := not_forall.mp (fun hh => hφne (MonoidHom.ext hh))
        refine ⟨k, ?_⟩
        have hpin : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd 1 := by
          decide
        rw [hpin _ hk, hpin _ hy]
    set X : Subgroup Y := φ.ker.map Blk.K.subtype with hXdef
    have hXK : X ≤ Blk.K := by rw [hXdef]; exact Subgroup.map_subtype_le _
    have hRX : Blk.frattiniK ≤ X := by
      intro r hr
      have hrK : r ∈ Blk.K := frattiniLike_le Blk.K hr
      refine Subgroup.mem_map.mpr ⟨⟨r, hrK⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hφ_apply]
      have hs1 : s ⟨r, hrK⟩ = 1 := Subtype.ext (by
        rw [hs]
        show RF.piB r = 1
        exact (RF.ker_piB.symm ▸ hr : r ∈ RF.piB.ker))
      rw [hs1]; simp
    have hXnormal : X.Normal := by
      rw [hXdef]
      refine ⟨fun x hx y => ?_⟩
      obtain ⟨k, hkker, hkeq⟩ := Subgroup.mem_map.mp hx
      have hxK : x ∈ Blk.K := hkeq ▸ k.2
      have hyk : y * x * y⁻¹ ∈ Blk.K := Blk.hK.conj_mem x hxK y
      refine Subgroup.mem_map.mpr ⟨⟨y * x * y⁻¹, hyk⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker] at hkker ⊢
      rw [hφ_apply] at hkker ⊢
      have hconj : Additive.ofMul (s ⟨y * x * y⁻¹, hyk⟩)
          = (RF.piBC (RF.piB y)) • Additive.ofMul (s ⟨x, hxK⟩) := by
        have hact : (RF.piBC (RF.piB y)) • Additive.ofMul (s ⟨x, hxK⟩)
            = Additive.ofMul (⟨RF.mbSec (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1
                * (RF.mbSec (RF.piBC (RF.piB y)))⁻¹,
                RF.MB_normal.conj_mem _ (s ⟨x, hxK⟩).2 _⟩ : ↥RF.MB) := rfl
        rw [hact]
        congr 1
        apply Subtype.ext
        rw [hs]
        show RF.piB (y * x * y⁻¹)
          = RF.mbSec (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1
              * (RF.mbSec (RF.piBC (RF.piB y)))⁻¹
        rw [hs, map_mul, map_mul, map_inv]
        exact (RF.MB_conj_eq (RF.mbSec_spec (RF.piBC (RF.piB y)))
          ⟨RF.piB x, hmem ⟨x, hxK⟩⟩).symm
      rw [hconj, hinv]
      have hkx : s ⟨x, hxK⟩ = s k := congrArg s (Subtype.ext hkeq.symm)
      rw [hkx]; exact hkker
    have hidx : (X.subgroupOf Blk.K).index = 2 := by
      have hcm : X.subgroupOf Blk.K = φ.ker := by
        rw [hXdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective Blk.K.subtype_injective]
      show Nat.card (↥Blk.K ⧸ (X.subgroupOf Blk.K)) = 2
      rw [hcm, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
      simp
    exact absurd ⟨X, hXnormal, hRX, hXK, hidx⟩ (lemma_7_1_dual Blk)
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
    ⟨⟨0, smul_zero⟩⟩⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Nonemptiness of the `Γ_R` `B`-lift fibre** (the §9 induction, the M-stage residue): every
lower boundary lift `ρ : Γ_R ↠ C` lifts to a continuous homomorphism `Γ_R → B` through `π_{BC}`.

The `Γ_R` port of `RecursionFrame.liftsOver_nonempty_gammaA`: a set-lift marking of `ρ` has both
relator values in `M_B` (`push_tameRelR`/`push_wildRelR`, no surjectivity needed), and since
`(M_B^∨)^C = 0` (`lemma_7_1_dual`, via `card_fixedPts_MB_dual`) the Roe candidate duality
`prop_5_15_R` clause 1 gives `#H²_{word,R} = 1`, forcing the relator pair to be a `d¹_R`-image;
the corrected marking (shared tame row `corrected_tameValue`, Roe wild row `corrected_wildValueR`,
transported by `d1FunR_base_change`) then descends by `descend_piBC_R`. -/
theorem RecursionFrame.liftsOver_nonempty_gammaR
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaR ↥boundarySubgroup)
    (F : BoundaryFrame H E) (ρ : BoundaryLifts b F RF.TC) :
    Nonempty (RF.LiftsOver b F ρ) := by
  classical
  -- the shared `M_B` module pack (extracted above; also used by the card twin)
  haveI hMBn : RF.MB.Normal := RF.MB_normal
  set θ : ContinuousMonoidHom GR RF.YC :=
    ⟨ρ.1.1.toMonoidHom, ρ.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  letI : CommGroup ↥RF.MB := RF.mbCommGroup
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actC : DistribMulAction RF.YC (Additive ↥RF.MB) := RF.mbConjActC
  have hA₂ : ∀ a : Additive ↥RF.MB, a + a = 0 := RF.MB_add_self
  -- `#fixedPts = 1` (the `(M_B^∨)^{Y_C} = 0` group theory via `lemma_7_1_dual`)
  have hfix : Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1 :=
    RF.card_fixedPts_MB_dual
  -- the Roe candidate duality at `markC_R θ`, and the direct `Y_B`-conjugation action for `d1FunR`
  have adm := markC_admissible_R θ hθs
  have hsd := GQ2.FoxH.prop_5_15_R (markC_R θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2
  letI actYB : DistribMulAction RF.YB (Additive ↥RF.MB) :=
    { smul := fun g m => Additive.ofMul
        ⟨g * (Additive.toMul m).1 * g⁻¹, hMBn.conj_mem _ (Additive.toMul m).2 _⟩
      one_smul := fun m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show (1 : RF.YB) * (Additive.toMul m).1 * (1 : RF.YB)⁻¹ = (Additive.toMul m).1
        group
      mul_smul := fun g g' m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show (g * g') * (Additive.toMul m).1 * (g * g')⁻¹
          = g * (g' * (Additive.toMul m).1 * g'⁻¹) * g⁻¹
        group
      smul_zero := fun g => by
        apply Additive.toMul.injective; apply Subtype.ext
        show g * (1 : RF.YB) * g⁻¹ = 1
        group
      smul_add := fun g m m' => by
        apply Additive.toMul.injective; apply Subtype.ext
        show g * ((Additive.toMul m).1 * (Additive.toMul m').1) * g⁻¹
          = (g * (Additive.toMul m).1 * g⁻¹) * (g * (Additive.toMul m').1 * g⁻¹)
        group }
  have hcompat : ∀ (g : RF.YB) (a : Additive ↥RF.MB), g • a = RF.piBC g • a := by
    intro g a
    apply Additive.toMul.injective; apply Subtype.ext
    show g * (Additive.toMul a).1 * g⁻¹
      = RF.mbSec (RF.piBC g) * (Additive.toMul a).1 * (RF.mbSec (RF.piBC g))⁻¹
    exact RF.MB_conj_eq (by rw [RF.mbSec_spec]) (Additive.toMul a)
  -- §1: a set-lift marking of `ρ`'s marking through `π_{BC}`; relators land in `M_B`
  obtain ⟨yσ, hyσ⟩ := RF.piBC_surj ((Marking.pushR θ).σ)
  obtain ⟨yτ, hyτ⟩ := RF.piBC_surj ((Marking.pushR θ).τ)
  obtain ⟨yx₀, hyx₀⟩ := RF.piBC_surj ((Marking.pushR θ).x₀)
  obtain ⟨yx₁, hyx₁⟩ := RF.piBC_surj ((Marking.pushR θ).x₁)
  set tB : Marking RF.YB := ⟨yσ, yτ, yx₀, yx₁⟩ with htB
  have hproj : tB.map RF.piBC = Marking.pushR θ := marking_ext hyσ hyτ hyx₀ hyx₁
  have hv₁mem : tB.tameValue ∈ RF.MB := by
    have h := Marking.map_tameValue RF.piBC tB
    rw [hproj, (Marking.tameValue_eq_one_iff _).mpr (push_tameRelR θ)] at h
    rw [← RF.ker_piBC, MonoidHom.mem_ker]; exact h.symm
  have hv₂mem : tB.wildValueR ∈ RF.MB := by
    have h := Marking.map_wildValueR RF.piBC tB
    rw [hproj, (Marking.wildValueR_eq_one_iff _).mpr (push_wildRelR θ)] at h
    rw [← RF.ker_piBC, MonoidHom.mem_ker]; exact h.symm
  set v₁ : ↥RF.MB := ⟨tB.tameValue, hv₁mem⟩ with hv₁def
  set v₂ : ↥RF.MB := ⟨tB.wildValueR, hv₂mem⟩ with hv₂def
  -- §5': `H2wR = 0` (card `#fixedPts = 1`) ⟹ every relator pair is a `d¹_R`-coboundary
  have hH2w1 : Nat.card (H2wR (A := Additive ↥RF.MB) (markC_R θ)) = 1 := by rw [hsd.1, hfix]
  haveI : Subsingleton ((Additive ↥RF.MB × Additive ↥RF.MB)
      ⧸ (d1R (A := Additive ↥RF.MB) (markC_R θ)).range) :=
    (Nat.card_eq_one_iff_unique.mp hH2w1).1
  have hmem : ((Additive.ofMul v₁, Additive.ofMul v₂) :
      Additive ↥RF.MB × Additive ↥RF.MB) ∈ (d1R (A := Additive ↥RF.MB) (markC_R θ)).range := by
    rw [← QuotientAddGroup.eq_zero_iff]; exact Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hmem
  -- §6: the corrected marking kills both relators and still covers `ρ`
  set j : Additive ↥RF.MB → RF.YB := fun a => (Additive.toMul a).1 with hj
  have hjmul : ∀ a b : Additive ↥RF.MB, j (a + b) = j a * j b := fun _ _ => rfl
  have hjconj : ∀ (g : RF.YB) (a : Additive ↥RF.MB), j (g • a) = g * j a * g⁻¹ := fun _ _ => rfl
  have hbase : d1FunR (markC_R θ) x = d1FunR tB x := by
    rw [show markC_R θ = tB.map RF.piBC from hproj.symm]
    exact d1FunR_base_change RF.piBC hcompat tB x
  have hd1 : d1FunR tB x = (Additive.ofMul v₁, Additive.ofMul v₂) := by rw [← hbase]; exact hx
  set tHat : Marking RF.YB :=
    ⟨j (x 0) * tB.σ, j (x 1) * tB.τ, j (x 2) * tB.x₀, j (x 3) * tB.x₁⟩ with htHat
  have htameHat : tHat.TameRel := by
    rw [← Marking.tameValue_eq_one_iff,
      show tHat.tameValue = j ((d1FunR tB x).1) * tB.tameValue from
        RStageGammaA.corrected_tameValue j hjmul hjconj tB x, hd1]
    exact RF.MB_elem _ hv₁mem
  have hwildHat : tHat.WildRelR := by
    rw [← Marking.wildValueR_eq_one_iff,
      show tHat.wildValueR = j ((d1FunR tB x).2) * tB.wildValueR from
        corrected_wildValueR j hjmul hjconj tB x, hd1]
    exact RF.MB_elem _ hv₂mem
  have hprojHat : tHat.map RF.piBC = Marking.pushR θ := by
    have hker : ∀ a : Additive ↥RF.MB, RF.piBC (j a) = 1 := fun a => by
      rw [← MonoidHom.mem_ker, RF.ker_piBC]; exact (Additive.toMul a).2
    refine marking_ext ?_ ?_ ?_ ?_
    · show RF.piBC (j (x 0) * tB.σ) = (Marking.pushR θ).σ
      rw [map_mul, hker, one_mul]; exact hyσ
    · show RF.piBC (j (x 1) * tB.τ) = (Marking.pushR θ).τ
      rw [map_mul, hker, one_mul]; exact hyτ
    · show RF.piBC (j (x 2) * tB.x₀) = (Marking.pushR θ).x₀
      rw [map_mul, hker, one_mul]; exact hyx₀
    · show RF.piBC (j (x 3) * tB.x₁) = (Marking.pushR θ).x₁
      rw [map_mul, hker, one_mul]; exact hyx₁
  -- §7: descend to a `Γ_R`-lift of `ρ` through `π_{BC}`
  obtain ⟨φ, hφ⟩ := RF.descend_piBC_R θ hθs tHat hprojHat htameHat hwildHat
  exact ⟨⟨φ, fun γ => hφ γ⟩⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hmultR` for `Γ_R`**, assuming the fibre is nonempty: `#LiftsOver(ρ) = |M_B|²`.  The
`Z¹`-torsor bridge (`liftsOver_card_local`'s Step 2) is source-generic once a base lift exists;
the `Z¹` count is the Roe candidate-duality route (`z1EquivR` + `prop_5_15_R` clause 2), and
`hfix = 1` is the `lemma_7_1_dual` bridge, both mirroring the `Γ_A` twin. -/
theorem RecursionFrame.liftsOver_card_gammaR_of_nonempty
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaR ↥boundarySubgroup)
    (F : BoundaryFrame H E) (ρ : BoundaryLifts b F RF.TC)
    (hne : Nonempty (RF.LiftsOver b F ρ)) :
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2 := by
  classical
  -- the shared `M_B` module pack (extracted above), and the lower map (over `GR`)
  haveI hMBn : RF.MB.Normal := RF.MB_normal
  set θ : ContinuousMonoidHom GR RF.YC :=
    ⟨ρ.1.1.toMonoidHom, ρ.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  letI : CommGroup ↥RF.MB := RF.mbCommGroup
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actC : DistribMulAction RF.YC (Additive ↥RF.MB) := RF.mbConjActC
  letI actG : DistribMulAction GR (Additive ↥RF.MB) :=
    DistribMulAction.compHom (Additive ↥RF.MB) θ.toMonoidHom
  have hcomp : ∀ (γ : GR) (a : Additive ↥RF.MB), γ • a = θ γ • a := fun _ _ => rfl
  have hA₂ : ∀ a : Additive ↥RF.MB, a + a = 0 := RF.MB_add_self
  haveI : ContinuousSMul GR (Additive ↥RF.MB) := by
    refine ⟨?_⟩
    have hfac : (fun p : GR × Additive ↥RF.MB => p.1 • p.2)
        = (fun q : RF.YC × Additive ↥RF.MB => q.1 • q.2)
          ∘ (fun p : GR × Additive ↥RF.MB => (θ p.1, p.2)) := by funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  -- Step 3': the `Z¹` count via the Roe candidate duality (`z1EquivR` + `prop_5_15_R` clause 2)
  have adm := markC_admissible_R θ hθs
  have key : Nat.card (Z1 GR (Additive ↥RF.MB))
      = Nat.card (Additive ↥RF.MB) ^ 2
        * Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) := by
    rw [Nat.card_congr (z1EquivR θ hcomp hθs hA₂).toEquiv,
      (GQ2.FoxH.prop_5_15_R (markC_R θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]
  -- Step 4: `#fixedPts = 1` ⟵ `lemma_7_1_dual` (the `(M^∨)^C = 0` group theory, source-free)
  have hfix : Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1 :=
    RF.card_fixedPts_MB_dual
  -- Step 2: the `Z¹`-torsor bridge (source-generic once a base lift `f₀` exists)
  have htorsor : Nat.card (RF.LiftsOver b F ρ)
      = Nat.card (Z1 GR (Additive ↥RF.MB)) := by
    obtain ⟨f₀⟩ := hne
    have hsmul : ∀ (γ : GR) (a : Additive ↥RF.MB),
        γ • a = Additive.ofMul (⟨f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹,
              hMBn.conj_mem _ (Additive.toMul a).2 _⟩ : ↥RF.MB) := by
      intro γ a
      rw [hcomp]
      apply Additive.toMul.injective; apply Subtype.ext
      show RF.mbSec (θ γ) * (Additive.toMul a).1 * (RF.mbSec (θ γ))⁻¹
        = f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹
      exact RF.MB_conj_eq (by rw [RF.mbSec_spec]; exact (f₀.2 γ).symm) (Additive.toMul a)
    have hmemf : ∀ (f : RF.LiftsOver b F ρ) (γ : GR),
        f.1 γ * (f₀.1 γ)⁻¹ ∈ RF.MB := by
      intro f γ
      rw [← RF.ker_piBC]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, f.2 γ, f₀.2 γ, mul_inv_cancel])
    refine Nat.card_congr
      { toFun := fun f => ⟨fun γ => Additive.ofMul ⟨f.1 γ * (f₀.1 γ)⁻¹, hmemf f γ⟩, ?_⟩
        invFun := fun c => ⟨(⟨MonoidHom.mk'
            (fun γ : GR => (Additive.toMul (c.1 γ)).1 * f₀.1 γ) ?_, ?_⟩ :
              ContinuousMonoidHom GR RF.YB), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- forward lands in `Z¹`
      rw [mem_Z1_iff]
      refine ⟨((continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1 * p.2⁻¹)).comp
        (f.1.continuous_toFun.prodMk f₀.1.continuous_toFun)).subtype_mk (hmemf f), ?_⟩
      intro g s
      rw [hsmul g (Additive.ofMul ⟨f.1 s * (f₀.1 s)⁻¹, hmemf f s⟩)]
      apply Additive.toMul.injective; apply Subtype.ext
      show f.1 (g * s) * (f₀.1 (g * s))⁻¹
        = f.1 g * (f₀.1 g)⁻¹ * (f₀.1 g * (f.1 s * (f₀.1 s)⁻¹) * (f₀.1 g)⁻¹)
      rw [show f.1 (g * s) = f.1 g * f.1 s from map_mul f.1 g s,
        show f₀.1 (g * s) = f₀.1 g * f₀.1 s from map_mul f₀.1 g s]; group
    · -- inverse is a hom
      intro g h
      show (Additive.toMul (c.1 (g * h))).1 * f₀.1 (g * h)
        = (Additive.toMul (c.1 g)).1 * f₀.1 g * ((Additive.toMul (c.1 h)).1 * f₀.1 h)
      rw [(mem_Z1_iff.mp c.2).2 g h,
        show f₀.1 (g * h) = f₀.1 g * f₀.1 h from map_mul f₀.1 g h, hsmul g (c.1 h)]
      show (Additive.toMul (c.1 g)).1 * (f₀.1 g * (Additive.toMul (c.1 h)).1 * (f₀.1 g)⁻¹)
          * (f₀.1 g * f₀.1 h) = _
      group
    · -- inverse is continuous
      exact (continuous_of_discreteTopology
          (f := fun p : Additive ↥RF.MB × RF.YB => (Additive.toMul p.1).1 * p.2)).comp
        ((mem_Z1_iff.mp c.2).1.prodMk f₀.1.continuous_toFun)
    · -- inverse lands over `ρ`
      intro γ
      show RF.piBC ((Additive.toMul (c.1 γ)).1 * f₀.1 γ) = ρ.1.1 γ
      have hcker : RF.piBC ((Additive.toMul (c.1 γ)).1) = 1 := by
        have hmem : ((Additive.toMul (c.1 γ)).1 : RF.YB) ∈ RF.piBC.ker := by
          rw [RF.ker_piBC]
          exact (Additive.toMul (c.1 γ)).2
        exact MonoidHom.mem_ker.mp hmem
      rw [map_mul, hcker, one_mul, f₀.2 γ]
    · -- left inverse
      intro f
      apply Subtype.ext; apply ContinuousMonoidHom.ext; intro γ
      show f.1 γ * (f₀.1 γ)⁻¹ * f₀.1 γ = f.1 γ
      group
    · -- right inverse
      intro c
      apply Subtype.ext; funext γ
      show Additive.ofMul (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩
          : ↥RF.MB) = c.1 γ
      rw [show (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩ : ↥RF.MB)
          = Additive.toMul (c.1 γ) from Subtype.ext (by group)]
      rfl
  rw [htorsor, key, hfix, mul_one]
  rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hmultR` for `Γ_R`** (obligation ii.3, the `SourceData.liftsOver_card` field at `Γ := Γ_R`):
`#LiftsOver(ρ) = |M_B|²` over every lower boundary lift. -/
theorem RecursionFrame.liftsOver_card_gammaR
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaR ↥boundarySubgroup)
    (F : BoundaryFrame H E) (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2 :=
  RF.liftsOver_card_gammaR_of_nonempty b F ρ (RF.liftsOver_nonempty_gammaR b F ρ)

/-! ### `SourceData` field-type smoke test (R31 spelling discipline)

The `example` below is stated in the **verbatim field type** of `GQ2.SourceData.liftsOver_card`
(`GQ2/SourceData.lean:137-143`) specialised at `Γ := GammaR`, and is filled by exactly the
`fun RF b F ρ => …` partial application that `BoundaryMaps.sourceA` uses for the `Γ_A` occupant
(`GQ2/SourceData.lean:322`).  Any future drift between `liftsOver_card_gammaR` and the structure
field is caught here rather than in R32's `sourceR`. -/

/-- Smoke test for the `SourceData.liftsOver_card` field at `Γ := GammaR`. -/
example : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (ρ : BoundaryLifts b F RF.TC),
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2 :=
  fun RF b F ρ => RF.liftsOver_card_gammaR b F ρ

end SectionEight

end GQ2

/-! ### Paper-tag ledger (paper §8/§9 + Roe note `paper/roe-presentation-verification.tex`;
hand-maintained)

  * Proposition 5.15 = ⟦prop:duality⟧ — the Roe candidate deformation duality (`prop_5_15_R`),
    entering at the two marked spots (`#Z¹_R` count, `#H²_R = 1` nonemptiness).
  * Lemma 7.1 (dual form) — `card_fixedPts_MB_dual`, the source-free `(M_B^∨)^{Y_C} = 0` input.
-/
