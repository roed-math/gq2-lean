/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Word.WordCoh
import GQ2.Dyadic.Count.H3OneRelatorAsphericity

/-!
# Continuous mod-two cochains descend to one finite level

Every continuous map from three or four copies of a profinite group to a discrete space is
constant on the right cosets of one open normal subgroup in every coordinate.  The compactness
argument already exists for two variables in `GQ2.exists_openNormalSubgroup_factor_two`; the
proof here applies it to `(G × G) × (G × G)` and extracts a common subgroup of `G` along
the two coordinate axes.

The second half packages descent and inflation for continuous mod-two bar cochains.  Inflation
commutes with `d²` and `d³`, and a primitive found at any finite refinement inflates to a
continuous primitive upstairs.  This is the finite-level continuity input needed by a future
construction of `ContinuousModTwoBarFoxComparison`.
-/

namespace GQ2

noncomputable section

section UniformFactor

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

private def firstAxisHom : G →* G × G where
  toFun g := (g, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

private def secondAxisHom : G →* G × G where
  toFun g := (1, g)
  map_one' := rfl
  map_mul' _ _ := by simp

private theorem continuous_firstAxisHom : Continuous (firstAxisHom : G → G × G) := by
  exact continuous_id.prodMk continuous_const

private theorem continuous_secondAxisHom : Continuous (secondAxisHom : G → G × G) := by
  exact continuous_const.prodMk continuous_id

private def firstAxisComap (W : OpenNormalSubgroup (G × G)) : OpenNormalSubgroup G where
  toOpenSubgroup := W.toOpenSubgroup.comap firstAxisHom continuous_firstAxisHom
  isNormal' := W.isNormal'.comap firstAxisHom

private def secondAxisComap (W : OpenNormalSubgroup (G × G)) : OpenNormalSubgroup G where
  toOpenSubgroup := W.toOpenSubgroup.comap secondAxisHom continuous_secondAxisHom
  isNormal' := W.isNormal'.comap secondAxisHom

/-- The common coordinate-axis core of an open normal subgroup of `G × G`. -/
private def productCoordinateCore (W : OpenNormalSubgroup (G × G)) : OpenNormalSubgroup G :=
  firstAxisComap W ⊓ secondAxisComap W

private theorem pair_mem_of_mem_productCoordinateCore
    (W : OpenNormalSubgroup (G × G)) {u v : G}
    (hu : u ∈ productCoordinateCore W) (hv : v ∈ productCoordinateCore W) :
    (u, v) ∈ W := by
  have huCore : u ∈ firstAxisComap W :=
    SetLike.le_def.mp (inf_le_left : productCoordinateCore W ≤ firstAxisComap W) hu
  have hvCore : v ∈ secondAxisComap W :=
    SetLike.le_def.mp (inf_le_right : productCoordinateCore W ≤ secondAxisComap W) hv
  have hu' : (u, 1) ∈ W := huCore
  have hv' : (1, v) ∈ W := hvCore
  simpa using mul_mem hu' hv'

/-- Uniform local constancy in four variables, with one open normal subgroup in every slot. -/
theorem exists_openNormalSubgroup_factor_four
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : G × G × G × G → M) (hf : Continuous f) :
    ∃ V : OpenNormalSubgroup G,
      ∀ a b c d : G, ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V, ∀ z ∈ V,
        f (a * u, b * v, c * w, d * z) = f (a, b, c, d) := by
  let packed : (G × G) × (G × G) → M :=
    fun p ↦ f (p.1.1, p.1.2, p.2.1, p.2.2)
  have hpacked : Continuous packed := by
    exact hf.comp (by fun_prop)
  obtain ⟨W, hW⟩ :=
    GQ2.Dyadic.WordCoh.exists_openNormalSubgroup_factor_two packed hpacked
  refine ⟨productCoordinateCore W, fun a b c d u hu v hv w hw z hz ↦ ?_⟩
  exact hW (a, b) (c, d) (u, v)
    (pair_mem_of_mem_productCoordinateCore W hu hv) (w, z)
    (pair_mem_of_mem_productCoordinateCore W hw hz)

/-- Uniform local constancy in three variables, with one open normal subgroup in every slot. -/
theorem exists_openNormalSubgroup_factor_three
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : G × G × G → M) (hf : Continuous f) :
    ∃ V : OpenNormalSubgroup G,
      ∀ a b c : G, ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V,
        f (a * u, b * v, c * w) = f (a, b, c) := by
  let padded : G × G × G × G → M := fun p ↦ f (p.1, p.2.1, p.2.2.1)
  have hpadded : Continuous padded := hf.comp (by fun_prop)
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_four padded hpadded
  refine ⟨V, fun a b c u hu v hv w hw ↦ ?_⟩
  simpa [padded] using hV a b c 1 u hu v hv w hw 1 (one_mem V)

end UniformFactor

namespace ContCoh

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance : DistribMulAction G (ZMod 2) := trivialZModTwoAction G
local instance : ContinuousSMul G (ZMod 2) := continuousSMul_trivialZModTwoAction

/-! ## Descent and inflation -/

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Inflate a finite-level two-cochain along an open-normal quotient. -/
def modTwoInflateTwo (V : OpenNormalSubgroup G)
    (k : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) : G × G → ZMod 2 :=
  fun p ↦ k (QuotientGroup.mk' V.toSubgroup p.1, QuotientGroup.mk' V.toSubgroup p.2)

/-- Inflate a finite-level three-cochain along an open-normal quotient. -/
def modTwoInflateThree (V : OpenNormalSubgroup G)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    G × G × G → ZMod 2 :=
  fun p ↦ F (QuotientGroup.mk' V.toSubgroup p.1,
    QuotientGroup.mk' V.toSubgroup p.2.1, QuotientGroup.mk' V.toSubgroup p.2.2)

/-- Inflate a finite-level four-cochain along an open-normal quotient. -/
def modTwoInflateFour (V : OpenNormalSubgroup G)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) ×
      (G ⧸ V.toSubgroup) → ZMod 2) : G × G × G × G → ZMod 2 :=
  fun p ↦ F (QuotientGroup.mk' V.toSubgroup p.1,
    QuotientGroup.mk' V.toSubgroup p.2.1, QuotientGroup.mk' V.toSubgroup p.2.2.1,
    QuotientGroup.mk' V.toSubgroup p.2.2.2)

theorem continuous_modTwoInflateTwo (V : OpenNormalSubgroup G)
    (k : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    Continuous (modTwoInflateTwo V k) := by
  exact continuous_of_discreteTopology.comp
    ((QuotientGroup.continuous_mk.comp continuous_fst).prodMk
      (QuotientGroup.continuous_mk.comp continuous_snd))

theorem continuous_modTwoInflateThree (V : OpenNormalSubgroup G)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    Continuous (modTwoInflateThree V F) := by
  exact continuous_of_discreteTopology.comp
    ((QuotientGroup.continuous_mk.comp continuous_fst).prodMk
      ((QuotientGroup.continuous_mk.comp (continuous_fst.comp continuous_snd)).prodMk
        (QuotientGroup.continuous_mk.comp (continuous_snd.comp continuous_snd))))

theorem continuous_modTwoInflateFour (V : OpenNormalSubgroup G)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) ×
      (G ⧸ V.toSubgroup) → ZMod 2) :
    Continuous (modTwoInflateFour V F) := by
  exact continuous_of_discreteTopology.comp
    ((QuotientGroup.continuous_mk.comp continuous_fst).prodMk
      ((QuotientGroup.continuous_mk.comp (continuous_fst.comp continuous_snd)).prodMk
        ((QuotientGroup.continuous_mk.comp
          (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
          (QuotientGroup.continuous_mk.comp
            (continuous_snd.comp (continuous_snd.comp continuous_snd))))))

/-- A representative-section descent of a three-cochain.  Uniform coset constancy makes its
inflation equal to the original cochain; no algebraic choice enters downstream statements. -/
def modTwoDescendThree (V : OpenNormalSubgroup G) (F : G × G × G → ZMod 2) :
    (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2 :=
  fun p ↦ F (Quotient.out p.1, Quotient.out p.2.1, Quotient.out p.2.2)

/-- A representative-section descent of a four-cochain. -/
def modTwoDescendFour (V : OpenNormalSubgroup G) (F : G × G × G × G → ZMod 2) :
    (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) ×
      (G ⧸ V.toSubgroup) → ZMod 2 :=
  fun p ↦ F (Quotient.out p.1, Quotient.out p.2.1,
    Quotient.out p.2.2.1, Quotient.out p.2.2.2)

private theorem out_inv_mul_mem (V : OpenNormalSubgroup G) (x : G) :
    (Quotient.out (QuotientGroup.mk' V.toSubgroup x))⁻¹ * x ∈ V := by
  apply QuotientGroup.leftRel_apply.mp
  exact Quotient.exact (Quotient.out_eq _)

theorem inflate_descendThree_eq (V : OpenNormalSubgroup G) (F : G × G × G → ZMod 2)
    (hV : ∀ a b c : G, ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V,
      F (a * u, b * v, c * w) = F (a, b, c)) :
    modTwoInflateThree V (modTwoDescendThree V F) = F := by
  funext p
  let a := Quotient.out (QuotientGroup.mk' V.toSubgroup p.1)
  let b := Quotient.out (QuotientGroup.mk' V.toSubgroup p.2.1)
  let c := Quotient.out (QuotientGroup.mk' V.toSubgroup p.2.2)
  have h := hV a b c (a⁻¹ * p.1) (out_inv_mul_mem V p.1)
    (b⁻¹ * p.2.1) (out_inv_mul_mem V p.2.1)
    (c⁻¹ * p.2.2) (out_inv_mul_mem V p.2.2)
  simpa [modTwoInflateThree, modTwoDescendThree, a, b, c] using h.symm

theorem inflate_descendFour_eq (V : OpenNormalSubgroup G)
    (F : G × G × G × G → ZMod 2)
    (hV : ∀ a b c d : G, ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V, ∀ z ∈ V,
      F (a * u, b * v, c * w, d * z) = F (a, b, c, d)) :
    modTwoInflateFour V (modTwoDescendFour V F) = F := by
  funext p
  let a := Quotient.out (QuotientGroup.mk' V.toSubgroup p.1)
  let b := Quotient.out (QuotientGroup.mk' V.toSubgroup p.2.1)
  let c := Quotient.out (QuotientGroup.mk' V.toSubgroup p.2.2.1)
  let d := Quotient.out (QuotientGroup.mk' V.toSubgroup p.2.2.2)
  have h := hV a b c d (a⁻¹ * p.1) (out_inv_mul_mem V p.1)
    (b⁻¹ * p.2.1) (out_inv_mul_mem V p.2.1)
    (c⁻¹ * p.2.2.1) (out_inv_mul_mem V p.2.2.1)
    (d⁻¹ * p.2.2.2) (out_inv_mul_mem V p.2.2.2)
  simpa [modTwoInflateFour, modTwoDescendFour, a, b, c, d] using h.symm

/-- Every continuous mod-two three-cochain is inflated from one finite quotient. -/
theorem exists_modTwoCochainThree_factor (F : G × G × G → ZMod 2) (hF : Continuous F) :
    ∃ (V : OpenNormalSubgroup G)
      (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2),
      modTwoInflateThree V c = F := by
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_three F hF
  exact ⟨V, modTwoDescendThree V F, inflate_descendThree_eq V F hV⟩

/-- Every continuous mod-two four-cochain is inflated from one finite quotient. -/
theorem exists_modTwoCochainFour_factor (F : G × G × G × G → ZMod 2)
    (hF : Continuous F) :
    ∃ (V : OpenNormalSubgroup G)
      (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) ×
        (G ⧸ V.toSubgroup) → ZMod 2), modTwoInflateFour V c = F := by
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_four F hF
  exact ⟨V, modTwoDescendFour V F, inflate_descendFour_eq V F hV⟩

/-! ## Differential compatibility and finite-level primitives -/

theorem dTwo_modTwoInflateTwo (V : OpenNormalSubgroup G)
    (k : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    letI := trivialZModTwoAction (G ⧸ V.toSubgroup)
    dTwo G (ZMod 2) (modTwoInflateTwo V k) =
      modTwoInflateThree V (dTwo (G ⧸ V.toSubgroup) (ZMod 2) k) := by
  letI := trivialZModTwoAction (G ⧸ V.toSubgroup)
  funext t
  have hsmulG (g : G) (x : ZMod 2) : g • x = x := rfl
  have hsmulQ (g : G ⧸ V.toSubgroup) (x : ZMod 2) : g • x = x := rfl
  simp [dTwo, modTwoInflateTwo, modTwoInflateThree, hsmulG, hsmulQ]

theorem dThree_modTwoInflateThree (V : OpenNormalSubgroup G)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    letI := trivialZModTwoAction (G ⧸ V.toSubgroup)
    dThree (G := G) (A := ZMod 2) (modTwoInflateThree V F) =
      modTwoInflateFour V (dThree (G := G ⧸ V.toSubgroup) (A := ZMod 2) F) := by
  letI := trivialZModTwoAction (G ⧸ V.toSubgroup)
  funext t
  have hsmulG (g : G) (x : ZMod 2) : g • x = x := rfl
  have hsmulQ (g : G ⧸ V.toSubgroup) (x : ZMod 2) : g • x = x := rfl
  simp [dThree, modTwoInflateThree, modTwoInflateFour, hsmulG, hsmulQ]

/-- A continuous degree-three cocycle descends to an actual cocycle on one finite quotient.
The proof uses surjectivity of the quotient projection together with compatibility of `d³`
and inflation. -/
theorem exists_modTwoThreeCocycle_factor
    (F : G × G × G → ZMod 2) (hFcontinuous : Continuous F)
    (hFcocycle : dThree (G := G) (A := ZMod 2) F = 0) :
    ∃ (V : OpenNormalSubgroup G)
      (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2),
      modTwoInflateThree V c = F ∧
        (letI := trivialZModTwoAction (G ⧸ V.toSubgroup)
         dThree (G := G ⧸ V.toSubgroup) (A := ZMod 2) c = 0) := by
  obtain ⟨V, c, hfactor⟩ := exists_modTwoCochainThree_factor F hFcontinuous
  refine ⟨V, c, hfactor, ?_⟩
  letI := trivialZModTwoAction (G ⧸ V.toSubgroup)
  funext t
  rcases t with ⟨t₁, t₂, t₃, t₄⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup t₁
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup t₂
  obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup t₃
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup t₄
  have hcycleInflated :
      dThree (G := G) (A := ZMod 2) (modTwoInflateThree V c) = 0 := by
    rw [hfactor]
    exact hFcocycle
  have hcompat := congrFun (dThree_modTwoInflateThree V c) (a, b, c', d)
  have hzero := congrFun hcycleInflated (a, b, c', d)
  rw [hzero] at hcompat
  simpa [modTwoInflateFour] using hcompat.symm

/-- The canonical projection from a finer open-normal quotient to a coarser one. -/
def openNormalQuotientProj {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup) : (G ⧸ W.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map W.toSubgroup V.toSubgroup (MonoidHom.id _)
    (by rw [Subgroup.comap_id]; exact hWV)

@[simp] theorem openNormalQuotientProj_mk {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup) (g : G) :
    openNormalQuotientProj hWV (QuotientGroup.mk' W.toSubgroup g) =
      QuotientGroup.mk' V.toSubgroup g := by
  rw [openNormalQuotientProj, QuotientGroup.map_mk']
  rfl

/-- Pull a three-cochain to a finer finite quotient. -/
def modTwoRefineThree {V W : OpenNormalSubgroup G} (hWV : W.toSubgroup ≤ V.toSubgroup)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    (G ⧸ W.toSubgroup) × (G ⧸ W.toSubgroup) × (G ⧸ W.toSubgroup) → ZMod 2 :=
  fun p ↦ F (openNormalQuotientProj hWV p.1,
    openNormalQuotientProj hWV p.2.1, openNormalQuotientProj hWV p.2.2)

theorem inflate_refineThree {V W : OpenNormalSubgroup G}
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (F : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2) :
    modTwoInflateThree W (modTwoRefineThree hWV F) = modTwoInflateThree V F := by
  funext p
  change F (openNormalQuotientProj hWV (QuotientGroup.mk' W.toSubgroup p.1),
    openNormalQuotientProj hWV (QuotientGroup.mk' W.toSubgroup p.2.1),
    openNormalQuotientProj hWV (QuotientGroup.mk' W.toSubgroup p.2.2)) =
      F (QuotientGroup.mk' V.toSubgroup p.1, QuotientGroup.mk' V.toSubgroup p.2.1,
        QuotientGroup.mk' V.toSubgroup p.2.2)
  rw [openNormalQuotientProj_mk, openNormalQuotientProj_mk, openNormalQuotientProj_mk]

/-- A finite-level `d²` primitive at any refinement inflates to a continuous primitive of the
original continuous three-cochain. -/
theorem continuous_primitive_of_finite_refinement
    (F : G × G × G → ZMod 2)
    (V W : OpenNormalSubgroup G) (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) → ZMod 2)
    (hF : modTwoInflateThree V c = F)
    (k : (G ⧸ W.toSubgroup) × (G ⧸ W.toSubgroup) → ZMod 2)
    (hk : letI := trivialZModTwoAction (G ⧸ W.toSubgroup)
      dTwo (G ⧸ W.toSubgroup) (ZMod 2) k = modTwoRefineThree hWV c) :
    ∃ K : G × G → ZMod 2, Continuous K ∧ dTwo G (ZMod 2) K = F := by
  let K := modTwoInflateTwo W k
  refine ⟨K, continuous_modTwoInflateTwo W k, ?_⟩
  rw [dTwo_modTwoInflateTwo W k, hk, inflate_refineThree hWV c, hF]

end ContCoh

end

end GQ2
