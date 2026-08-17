/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedCoreShift

/-!
# Exact relative representatives in the two-central tower

The W205 four-core correction problem asks that every correction row both lie at a prescribed
two-central depth and vanish exactly after forgetting the handle.  This file turns those two
group-level conditions into one finite-level subgroup.

For a continuous epimorphism `f : P -> Q`, the image of

`lambda_j(P) intersect ker(f)`

in `P / lambda_n(P)` is exactly the intersection of the image of `lambda_j(P)` with the kernel
of the induced map on level-`n` quotients, provided `j <= n`.  The reverse inclusion is the
substantive direction: lift the target error through `lambda_n(P)` and remove it without
changing the level-`n` class.

Specializing to `dmForgetHandles 2 1` gives the finite relative layer used by all four W205
core rows.  The extra continuous-character condition on the `C` row is deliberately not
collapsed into this layer: it is an additional constraint on the representative, and the
current APIs do not show that it is determined by a finite level class.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedRelativeLift

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Roe.Labute

/-! ## A generic exact relative lift -/

/-- A continuous homomorphism induces a continuous homomorphism on every two-central level. -/
noncomputable def relativeLevelMap
    {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (n : ℕ) :
    ContinuousMonoidHom (levelQuot P n) (levelQuot Q n) := by
  let q : ContinuousMonoidHom P (levelQuot Q n) :=
    ⟨(levelMk Q n).comp f.toMonoidHom,
      (continuous_levelMk Q n).comp f.continuous_toFun⟩
  exact quotientLift (twoCentralSeries P n) q fun x hx ↦ by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr
      (map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun n ⟨x, hx, rfl⟩)

@[simp] theorem relativeLevelMap_levelMk
    {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (n : ℕ) (x : P) :
    relativeLevelMap f n (levelMk P n x) = levelMk Q n (f x) :=
  rfl

/-- An epimorphism remains onto on every two-central quotient. -/
theorem relativeLevelMap_surjective
    {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (relativeLevelMap f n) := by
  intro y
  obtain ⟨q, rfl⟩ := levelMk_surjective Q n y
  obtain ⟨p, rfl⟩ := hf q
  exact ⟨levelMk P n p, rfl⟩

/-- A relative class has a representative which vanishes under `f` exactly, not merely
modulo `lambda_n(Q)`. -/
theorem exists_exact_relativeRepresentative
    {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Surjective f)
    {j n : ℕ} (hjn : j ≤ n) {x : levelQuot P n}
    (hx : x ∈ lambdaImage P j n) (hker : relativeLevelMap f n x = 1) :
    ∃ e : P,
      e ∈ twoCentralSeries P j ∧
      f e = 1 ∧
      levelMk P n e = x := by
  obtain ⟨e, he, rfl⟩ := hx
  have hfe : f e ∈ twoCentralSeries Q n := by
    have hfeq : levelMk Q n (f e) = 1 := by
      simpa only [relativeLevelMap_levelMk] using hker
    exact (QuotientGroup.eq_one_iff _).mp hfeq
  have hfe' : f e ∈ (twoCentralSeries P n).map f.toMonoidHom := by
    rw [map_twoCentralSeries_eq f.toMonoidHom f.continuous_toFun hf n]
    exact hfe
  obtain ⟨t, ht, hte⟩ := hfe'
  refine ⟨t⁻¹ * e, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (twoCentralSeries_antitone P hjn ht)) he
  · rw [map_mul, map_inv]
    change f t = f e at hte
    simp [hte]
  · have htone : levelMk P n t = 1 := (QuotientGroup.eq_one_iff _).mpr ht
    rw [map_mul, map_inv, htone, inv_one, one_mul]

/-- Finite-level relative classes are exactly images of exact relative elements. -/
theorem exactRelativeImage_eq_inf_ker
    {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Surjective f)
    {j n : ℕ} (hjn : j ≤ n) :
    (twoCentralSeries P j ⊓ f.toMonoidHom.ker).map (levelMk P n) =
      lambdaImage P j n ⊓ (relativeLevelMap f n).toMonoidHom.ker := by
  ext x
  constructor
  · rintro ⟨e, ⟨he, hef⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, ?_⟩
    change relativeLevelMap f n (levelMk P n e) = 1
    have hefone : f e = 1 := MonoidHom.mem_ker.mp hef
    rw [relativeLevelMap_levelMk, hefone, map_one]
  · rintro ⟨hx, hker⟩
    obtain ⟨e, he, hef, hex⟩ :=
      exists_exact_relativeRepresentative f hf hjn hx (MonoidHom.mem_ker.mp hker)
    exact ⟨e, ⟨he, MonoidHom.mem_ker.mpr hef⟩, hex⟩

/-! ## The one-handle relative layer -/

/-- The induced finite-level map which forgets the single handle. -/
noncomputable def oneHandleForgetLevelMap (n : ℕ) :
    ContinuousMonoidHom (levelQuot (DM 2 1) n) (levelQuot (DM 2 0) n) :=
  relativeLevelMap (dmForgetHandles 2 1) n

@[simp] theorem oneHandleForgetLevelMap_levelMk (n : ℕ) (x : DM 2 1) :
    oneHandleForgetLevelMap n (levelMk (DM 2 1) n x) =
      levelMk (DM 2 0) n (dmForgetHandles 2 1 x) :=
  rfl

/-- The finite subgroup of depth-`j` classes which vanish after forgetting the handle. -/
def oneHandleRelativeLambdaImage (j n : ℕ) :
    Subgroup (levelQuot (DM 2 1) n) :=
  lambdaImage (DM 2 1) j n ⊓ (oneHandleForgetLevelMap n).toMonoidHom.ker

/-- The relative layer is precisely the image of the exact handle-forgetting kernel. -/
theorem oneHandleRelativeLambdaImage_eq_exactImage
    {j n : ℕ} (hjn : j ≤ n) :
    oneHandleRelativeLambdaImage j n =
      (twoCentralSeries (DM 2 1) j ⊓
        (dmForgetHandles 2 1).toMonoidHom.ker).map (levelMk (DM 2 1) n) := by
  symm
  simpa [oneHandleRelativeLambdaImage, oneHandleForgetLevelMap] using
    (exactRelativeImage_eq_inf_ker (dmForgetHandles 2 1)
      (dmForgetHandles_surjective 2 1) hjn)

/-- Membership in the finite relative layer has an exact depth-`j`, handle-kernel
representative. -/
theorem mem_oneHandleRelativeLambdaImage_iff_exists_exact
    {j n : ℕ} (hjn : j ≤ n) (x : levelQuot (DM 2 1) n) :
    x ∈ oneHandleRelativeLambdaImage j n ↔
      ∃ e : DM 2 1,
        e ∈ twoCentralSeries (DM 2 1) j ∧
        dmForgetHandles 2 1 e = 1 ∧
        levelMk (DM 2 1) n e = x := by
  rw [oneHandleRelativeLambdaImage_eq_exactImage hjn]
  constructor
  · rintro ⟨e, ⟨he, hef⟩, hex⟩
    exact ⟨e, he, MonoidHom.mem_ker.mp hef, hex⟩
  · rintro ⟨e, he, hef, hex⟩
    exact ⟨e, ⟨he, MonoidHom.mem_ker.mpr hef⟩, hex⟩

#print axioms relativeLevelMap
#print axioms relativeLevelMap_levelMk
#print axioms relativeLevelMap_surjective
#print axioms exists_exact_relativeRepresentative
#print axioms exactRelativeImage_eq_inf_ker
#print axioms oneHandleForgetLevelMap
#print axioms oneHandleForgetLevelMap_levelMk
#print axioms oneHandleRelativeLambdaImage
#print axioms oneHandleRelativeLambdaImage_eq_exactImage
#print axioms mem_oneHandleRelativeLambdaImage_iff_exists_exact

end
end GQ2.Dyadic.Instances.MpcBalancedRelativeLift
