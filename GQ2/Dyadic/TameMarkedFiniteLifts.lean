/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.ThmFourTwoRN

/-!
# Finite quotient lifts retaining the tame marking

Do not sum away the boundary frame.  For a quotient of the second source,
its wild image is a normal two-group, so quotienting by that image supplies
a particular finite tame frame.  Equality of the counts at that frame gives
a quotient of the first source with the same tame marking.  The conclusion
is expressed by simultaneous representatives, suitable for relative
profinite reconstruction.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
  (S : SourceDataRN n q P hP nuP SN)
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- The actual wild image, not necessarily the full two-core of the target. -/
def finiteWildImage (f : ContSurj S.Γ Y) : Subgroup Y :=
  S.tame.toMonoidHom.ker.map f.1.toMonoidHom

instance finiteWildImage_normal (f : ContSurj S.Γ Y) : (finiteWildImage S f).Normal :=
  (MonoidHom.normal_ker S.tame.toMonoidHom).map f.1.toMonoidHom f.2

omit [Finite Y] in
theorem finiteWildImage_isPGroup (f : ContSurj S.Γ Y)
    (hwild : IsProP 2 S.tame.toMonoidHom.ker) : IsPGroup 2 (finiteWildImage S f) :=
  SectionThree.isPGroup_map_of_isProP hwild f.1.toMonoidHom f.1.continuous_toFun

/-- Descent of a finite quotient to its actual tame head. -/
def finiteTameHeadHom (f : ContSurj S.Γ Y) (htame : Function.Surjective S.tame) :
    Tq q →* Y ⧸ finiteWildImage S f :=
  S.tame.toMonoidHom.liftOfSurjective htame
    ⟨(QuotientGroup.mk' (finiteWildImage S f)).comp f.1.toMonoidHom, fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
        QuotientGroup.ker_mk']
      exact Subgroup.mem_map_of_mem f.1.toMonoidHom hx⟩

omit [DiscreteTopology Y] [Finite Y] in
theorem finiteTameHeadHom_tame (f : ContSurj S.Γ Y)
    (htame : Function.Surjective S.tame) (x : S.Γ) :
    finiteTameHeadHom S f htame (S.tame x) =
      QuotientGroup.mk' (finiteWildImage S f) (f.1 x) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- The continuous finite tame head determined by the particular source quotient. -/
def finiteTameHead (f : ContSurj S.Γ Y) (htame : Function.Surjective S.tame) :
    ContinuousMonoidHom (Tq q) (Y ⧸ finiteWildImage S f) :=
  have hquot : Topology.IsQuotientMap S.tame :=
    S.tame.continuous_toFun.isClosedMap.isQuotientMap S.tame.continuous_toFun htame
  { toMonoidHom := finiteTameHeadHom S f htame
    continuous_toFun := hquot.continuous_iff.mpr <|
      (QuotientGroup.continuous_mk.comp f.1.continuous_toFun).congr fun x =>
        (finiteTameHeadHom_tame S f htame x).symm }

omit [DiscreteTopology Y] [Finite Y] in
theorem finiteTameHead_surjective (f : ContSurj S.Γ Y)
    (htame : Function.Surjective S.tame) : Function.Surjective (finiteTameHead S f htame) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (finiteWildImage S f) y
  obtain ⟨x, rfl⟩ := f.2 z
  exact ⟨S.tame x, finiteTameHeadHom_tame S f htame x⟩

/-- The marked target uses the actual wild image and trivial scalar decoration. -/
def finiteWildMarkedTarget (f : ContSurj S.Γ Y)
    (hwild : IsProP 2 S.tame.toMonoidHom.ker) :
    MarkedTarget (Y ⧸ finiteWildImage S f) SectionTen.E₀ Y where
  LY := finiteWildImage S f
  normal := inferInstance
  isPGroup_two := finiteWildImage_isPGroup S f hwild
  piY := QuotientGroup.mk' (finiteWildImage S f)
  piY_surjective := QuotientGroup.mk'_surjective _
  ker_piY := QuotientGroup.ker_mk' _
  thetaY := 1

variable {S}

omit [DiscreteTopology Y] [Finite Y] in
/-- Equality at the actual tame head means that every source point has a simultaneous
representative for its finite image and its exact tame coordinate. -/
theorem exists_simultaneous_representative_of_finiteTameHead
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (f₂ : ContSurj S₂.Γ Y) (htame₂ : Function.Surjective S₂.tame)
    (f₁ : ContSurj S₁.Γ Y)
    (hframe : ∀ x : S₁.Γ,
      QuotientGroup.mk' (finiteWildImage S₂ f₂) (f₁.1 x) =
        finiteTameHead S₂ f₂ htame₂ (S₁.tame x)) :
    ∀ x : S₁.Γ, ∃ y : S₂.Γ, f₂.1 y = f₁.1 x ∧ S₂.tame y = S₁.tame x := by
  intro x
  obtain ⟨y₀, hy₀⟩ := htame₂ (S₁.tame x)
  have hquot : QuotientGroup.mk' (finiteWildImage S₂ f₂) (f₂.1 y₀) =
      QuotientGroup.mk' (finiteWildImage S₂ f₂) (f₁.1 x) := by
    rw [← finiteTameHeadHom_tame S₂ f₂ htame₂ y₀, hy₀]
    exact (hframe x).symm
  have hmem : (f₂.1 y₀)⁻¹ * f₁.1 x ∈ finiteWildImage S₂ f₂ :=
    QuotientGroup.eq.mp hquot
  obtain ⟨w, hw, hfw⟩ := hmem
  change f₂.1 w = (f₂.1 y₀)⁻¹ * f₁.1 x at hfw
  have htw : S₂.tame w = 1 := MonoidHom.mem_ker.mp hw
  refine ⟨y₀ * w, ?_, ?_⟩
  · rw [map_mul, hfw, mul_inv_cancel_left]
  · rw [map_mul, htw, mul_one, hy₀]

/-- Every finite quotient of the second corrected source admits a surjection from the
first whose pointwise finite/tame images have simultaneous representatives in the second.
This retains the frame information erased by ordinary surjection-count reconstruction. -/
theorem exists_tameCompatible_finiteSurj_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₂ : Function.Surjective S₂.tame)
    (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker)
    (f₂ : ContSurj S₂.Γ Y) :
    ∃ f₁ : ContSurj S₁.Γ Y,
      ∀ x : S₁.Γ, ∃ y : S₂.Γ, f₂.1 y = f₁.1 x ∧ S₂.tame y = S₁.tame x := by
  let F : BoundaryFrameK q P (Y ⧸ finiteWildImage S₂ f₂) SectionTen.E₀ :=
    tameFrameK (finiteTameHead S₂ f₂ htame₂)
      (finiteTameHead_surjective S₂ f₂ htame₂)
  let T := finiteWildMarkedTarget S₂ f₂ hwild₂
  have hne₂ : Nonempty (BoundaryLiftsK S₂.b F T) := by
    refine ⟨⟨f₂, fun x => Prod.ext ?_ (Subsingleton.elim _ _)⟩⟩
    exact (finiteTameHeadHom_tame S₂ f₂ htame₂ x).symm
  haveI : Finite (BoundaryLiftsK S₂.b F T) :=
    finite_boundaryLiftsK S₂.b F T S₂.tfg
  have hpos₂ : 0 < exactImageCountK S₂.b F T := Nat.card_pos_iff.mpr ⟨hne₂, inferInstance⟩
  have hc := thm_4_2_of_sourcesRN S₁ S₂ F hq0 hqe hnuP T
    (fun _ => Subsingleton.elim _ _)
  rw [← hc] at hpos₂
  obtain ⟨f₁, hf₁⟩ := (Nat.card_pos_iff.mp hpos₂).1
  refine ⟨f₁, exists_simultaneous_representative_of_finiteTameHead S₁ S₂ f₂ htame₂ f₁ ?_⟩
  intro x
  exact congrArg Prod.fst (hf₁ x)

#print axioms finiteWildImage_isPGroup
#print axioms finiteTameHead
#print axioms exists_simultaneous_representative_of_finiteTameHead
#print axioms exists_tameCompatible_finiteSurj_of_sourcesRN

end
end GQ2.Dyadic
