import GQ2.ShapiroDeepness
import GQ2.QuadraticAdjoin

/-!
# P-15f2c2b: the involution spine — discharging the c2a package

`ShapiroDeepness.hvanish_involution_of_deepClass` (the landed assembly) is parameterized by an
abstract "Kummer presentation package" `hc2a` and by `hunram`.  This file **discharges `hc2a`**
from the concrete `QuadraticAdjoin.exists_kummer_presentation` (P-15f2c2a), leaving a version
`hvanish_involution_of_deepClass'` that no longer carries the abstract package — only the tower
`(k ≤ L, hindex)` and the unramifiedness `hunram` (the latter supplied by P-15f2c2c4's
`UnramifiedBridge.hunram_involution` at the call site / f2d).

The one real brick is the **fixing-index-2 → degree-2 bridge**
`finrank_extendScalars_eq_two`: `[G_k : G_L] = 2 ⟹ [L : k] = 2`.  Route (base-`↥k` framing):
transport the index along `IntermediateField.fixingSubgroupEquiv k`, then run
`InfiniteGalois.normalAutEquivQuotient` (`Gal(ℚ̄₂/k) ⧸ G_L ≃ Gal(L/k)`, using index-2 ⟹ normal)
composed with `IsGalois.card_aut_eq_finrank`.  Everything else is the deep-unit norm bridge
(`LocalKummer.norm_sub_one_lt_of_isDeepUnit`) and `A ∈ L` from `IsDeepUnit`'s fixedness
(`InfiniteGalois.fixedField_fixingSubgroup`).
-/

namespace GQ2

namespace ShapiroDeepness

open IntermediateField ContCoh SectionSix LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The fixing-index-2 → degree-2 bridge -/

/-- `extendScalars hkL` (i.e. `L` viewed over `↥k`) is `ℚ_[2]`-finite when `L` is: the identity on
the shared carrier is a `ℚ_[2]`-linear equivalence `↥L ≃ₗ ↥(extendScalars hkL)`. -/
theorem finiteDimensional_extendScalars (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] L] (hkL : k ≤ L) :
    FiniteDimensional ℚ_[2] ↥(extendScalars hkL) := by
  let e : ↥L ≃ₗ[ℚ_[2]] ↥(extendScalars hkL) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        apply Subtype.ext
        simp only [IntermediateField.coe_smul, RingHom.id_apply, SetLike.val_smul] }
  exact Module.Finite.equiv e

/-- **Index transport**: the fixing subgroup of `extendScalars hkL` inside `Gal(ℚ̄₂/↥k)` is the
image of `L.fixingSubgroup.subgroupOf k.fixingSubgroup` under `fixingSubgroupEquiv k`, so the two
have equal index. -/
theorem index_extendScalars_fixingSubgroup (k L : IntermediateField ℚ_[2] ℚ̄₂) (hkL : k ≤ L) :
    ((extendScalars hkL).fixingSubgroup).index
      = (L.fixingSubgroup.subgroupOf k.fixingSubgroup).index := by
  have hmap : (L.fixingSubgroup.subgroupOf k.fixingSubgroup).map
      (fixingSubgroupEquiv k).toMonoidHom = (extendScalars hkL).fixingSubgroup := by
    ext φ
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
      IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      exact h y ((IntermediateField.mem_extendScalars hkL).mp hy)
    · intro h y hy
      exact h y ((IntermediateField.mem_extendScalars hkL).mpr hy)
  rw [← hmap, Subgroup.index_map_of_bijective (fixingSubgroupEquiv k).bijective]

/-- **The bridge** (P-15f2c2b core): a fixing-index-2 subextension has relative degree 2. -/
theorem finrank_extendScalars_eq_two (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] L] (hkL : k ≤ L)
    (hindex : (L.fixingSubgroup.subgroupOf k.fixingSubgroup).index = 2) :
    Module.finrank ↥k ↥(extendScalars hkL) = 2 := by
  have hHindex : ((extendScalars hkL).fixingSubgroup).index = 2 := by
    rw [index_extendScalars_fixingSubgroup k L hkL]; exact hindex
  haveI hHnorm : ((extendScalars hkL).fixingSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two hHindex
  haveI : IsGalois ↥k ↥(extendScalars hkL) :=
    (InfiniteGalois.normal_iff_isGalois (extendScalars hkL)).mp hHnorm
  haveI hfd2 : FiniteDimensional ℚ_[2] ↥(extendScalars hkL) :=
    finiteDimensional_extendScalars k L hkL
  haveI : FiniteDimensional ↥k ↥(extendScalars hkL) :=
    Module.Finite.right ℚ_[2] ↥k ↥(extendScalars hkL)
  let H : ClosedSubgroup (ℚ̄₂ ≃ₐ[↥k] ℚ̄₂) :=
    ⟨(extendScalars hkL).fixingSubgroup, fixingSubgroup_isClosed _⟩
  haveI : H.toSubgroup.Normal := hHnorm
  have hff : IntermediateField.fixedField H.toSubgroup = extendScalars hkL :=
    InfiniteGalois.fixedField_fixingSubgroup _
  rw [← IsGalois.card_aut_eq_finrank ↥k ↥(extendScalars hkL)]
  calc Nat.card (↥(extendScalars hkL) ≃ₐ[↥k] ↥(extendScalars hkL))
      = Nat.card (↥(IntermediateField.fixedField H.toSubgroup)
          ≃ₐ[↥k] ↥(IntermediateField.fixedField H.toSubgroup)) := by rw [← hff]
    _ = Nat.card ((ℚ̄₂ ≃ₐ[↥k] ℚ̄₂) ⧸ H.toSubgroup) :=
          (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient H).toEquiv).symm
    _ = ((extendScalars hkL).fixingSubgroup).index := rfl
    _ = 2 := hHindex

/-! ## Discharging the c2a package -/

/-- **`hc2a` discharged** (P-15f2c2b): the abstract Kummer presentation package of
`hvanish_involution_of_deepClass`, proved from `QuadraticAdjoin.exists_kummer_presentation`. -/
theorem kummer_presentation_of_index_two (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L] (hkL : k ≤ L)
    (hindex : (L.fixingSubgroup.subgroupOf k.fixingSubgroup).index = 2)
    (A : ℚ̄₂) (hdeep : IsDeepUnit L.fixingSubgroup A) :
    ∃ (d : (↥k)ˣ) (δ : ℚ̄₂) (u : (↥k)ˣ) (v : ↥k),
      δ ^ 2 = ((d : ↥k) : ℚ̄₂) ∧ δ ∈ L ∧
      (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
        = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup) ∧
      A = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ := by
  have hdeg : Module.finrank ↥k ↥(extendScalars hkL) = 2 :=
    finrank_extendScalars_eq_two k L hkL hindex
  have hAL : A ∈ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    exact (IntermediateField.mem_fixedField_iff _ A).mpr hdeep.2.1
  have hA1 : ‖A - 1‖ < ‖(2 : ℚ̄₂)‖ := norm_sub_one_lt_of_isDeepUnit hdeep
  exact QuadraticAdjoin.exists_kummer_presentation hkL hdeg hAL hA1

/-! ## The c2b vanish lemma (hc2a discharged) -/

/-- **Involution `hvanish`, self-contained** (P-15f2c2b): the involution inner cochain vanishes
for the square root of a deep block coordinate, with the c2a package **discharged** — only the
tower `(hkL, hindex)` and the unramifiedness `hunram` remain (the latter from P-15f2c2c4). -/
theorem hvanish_involution_of_deepClass' (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] L] [FiniteDimensional ℚ_[2] k] (hkL : k ≤ L)
    (hindex : ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)).index = 2)
    (hunram : ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L →
      ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖)
    (s : k.fixingSubgroup) (hs : s ∉ (L.fixingSubgroup).subgroupOf (k.fixingSubgroup))
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((L.fixingSubgroup).subgroupOf (k.fixingSubgroup) :
        Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (ξ : H1 L.fixingSubgroup (ZMod 2)) (hξ : ξ ∈ deepClasses L.fixingSubgroup) :
    ∃ β : ℚ̄₂,
      H2ofFun k.fixingSubgroup
        (evensNormFun ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)) s
          (fun w ↦ Kummer.kummerCocycleFun β
            ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))) = 0 :=
  hvanish_involution_of_deepClass k L hkL hindex hunram
    (kummer_presentation_of_index_two k L hkL hindex) s hs htriv hUo ξ hξ

end ShapiroDeepness

end GQ2
