import GQ2.EvensKahn

/-!
# B12-2 — the Krull bridge: open index-2 subgroup ⇒ quadratic subextension

This file supplies the **B12-2 deliverable** of the `kummerClassK_surjective` axiom-discharge
initiative (archived board `docs/orchestration/b12-tickets.md`, plan `b12-proof-plan.md`,
§4-I2): given an **open
subgroup of index 2** `H ≤ G_k := ↥(k.fixingSubgroup)`, it produces the quadratic subextension
`k ≤ L` whose fixing group cuts out exactly `H`, with `[L : k] = 2`
(`exists_quadratic_of_open_index_two`).

**Route** (all joints pinned in B12-0.3): `H' := H.map k.fixingSubgroup.subtype` is open in the
ambient `Gal(ℚ̄₂/ℚ₂)` (`k` finite ⇒ `k.fixingSubgroup` open; push the image forward by
`IsOpen.isOpenMap_subtype_val`), hence closed; `L := fixedField H'` (staying in the ambient group —
never transporting to `Gal(ℚ̄₂/↥k)`); Krull's `InfiniteGalois.fixingSubgroup_fixedField` gives
`L.fixingSubgroup = H'`, through which `H'`-openness feeds `InfiniteGalois.isOpen_iff_finite` to
yield `FiniteDimensional ℚ_[2] L`; the `subgroupOf`-form descends by
`comap_map_eq_self_of_injective`; and the degree is the ported `finrank_extendScalars_eq_two`.

**Placement.**  It imports only `GQ2.EvensKahn` (+ Mathlib), so it stays strictly upstream of
`Foundations/Axioms.lean` — the zero-churn requirement for the eventual census flip (B12-4).  The
three `extendScalars` degree lemmas it needs (`finiteDimensional_extendScalars`,
`index_extendScalars_fixingSubgroup`, `finrank_extendScalars_eq_two`) live downstream in
`GQ2.ShapiroDeepness` (`InvolutionVanish.lean`), so they are re-proved here as **`private`** copies,
verbatim-modulo-namespace (pure Mathlib field theory; the `private` marker guarantees no clash with
any parallel port).

*File-split note (B12-2 ∥ B12-1 coordination).*  The board routes B12-1/B12-2/B12-3 through one
shared file `GQ2/KummerSurjectivity.lean`.  Two agents independently *creating* that same new file
produces a whole-file merge conflict, whereas separate files merge cleanly; so the B12-2 lane is
developed here in its own leaf and exported for B12-3 to import.  It can be folded back into
`KummerSurjectivity.lean` in the later consolidation pass the plan already contemplates (§3).  The
public name lives in namespace `GQ2.KummerSurjectivity` so B12-3 references it unqualified.
-/

namespace GQ2

namespace KummerSurjectivity

open IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Ported `extendScalars` degree lemmas

Private, verbatim-modulo-namespace copies of `GQ2.ShapiroDeepness.{finiteDimensional_extendScalars,
index_extendScalars_fixingSubgroup, finrank_extendScalars_eq_two}` (`InvolutionVanish.lean`), which
sit downstream of `Foundations/Axioms.lean`.  Their proofs are pure Mathlib field theory. -/

/-- `extendScalars hkL` (i.e. `L` viewed over `↥k`) is `ℚ_[2]`-finite when `L` is: the identity on
the shared carrier is a `ℚ_[2]`-linear equivalence `↥L ≃ₗ ↥(extendScalars hkL)`. -/
private theorem finiteDimensional_extendScalars (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] L] (hkL : k ≤ L) :
    FiniteDimensional ℚ_[2] ↥(extendScalars hkL) := by
  let e : ↥L ≃ₗ[ℚ_[2]] ↥(extendScalars hkL) :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ by
        apply Subtype.ext
        simp only [IntermediateField.coe_smul, RingHom.id_apply, SetLike.val_smul] }
  exact Module.Finite.equiv e

/-- **Index transport**: the fixing subgroup of `extendScalars hkL` inside `Gal(ℚ̄₂/↥k)` is the
image of `L.fixingSubgroup.subgroupOf k.fixingSubgroup` under `fixingSubgroupEquiv k`, so the two
have equal index. -/
private theorem index_extendScalars_fixingSubgroup (k L : IntermediateField ℚ_[2] ℚ̄₂)
    (hkL : k ≤ L) :
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

/-- **The fixing-index-2 → degree-2 bridge**: a fixing-index-2 subextension has relative degree 2. -/
private theorem finrank_extendScalars_eq_two (k L : IntermediateField ℚ_[2] ℚ̄₂)
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

/-! ## The Krull bridge -/

/-- **B12-2 (§4-I2): an open subgroup of index 2 in `G_k` cuts out a quadratic subextension.**

Given `k` finite over `ℚ₂` and an **open** subgroup `H ≤ G_k = ↥(k.fixingSubgroup)` of **index 2**,
there is an intermediate field `k ≤ L`, finite over `ℚ₂`, with `L.fixingSubgroup.subgroupOf
k.fixingSubgroup = H` and `[L : k] = 2`.  This is the Krull–Galois half of the
`kummerClassK_surjective` discharge: it turns the kernel of a nonzero `H¹(G_k, 𝔽₂)`-cocycle into the
quadratic extension whose Kummer class realises that cocycle. -/
theorem exists_quadratic_of_open_index_two
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (H : Subgroup ↥(k.fixingSubgroup)) (hHopen : IsOpen (↑H : Set ↥(k.fixingSubgroup)))
    (hHindex : H.index = 2) :
    ∃ (L : IntermediateField ℚ_[2] ℚ̄₂) (hkL : k ≤ L), FiniteDimensional ℚ_[2] L ∧
      (L.fixingSubgroup).subgroupOf k.fixingSubgroup = H ∧
      Module.finrank ↥k ↥(extendScalars hkL) = 2 := by
  -- Push `H` forward into the ambient Galois group; it lands inside `k.fixingSubgroup`.
  set H' := H.map k.fixingSubgroup.subtype with hH'
  have hH'leK : H' ≤ k.fixingSubgroup := Subgroup.map_subtype_le H
  -- `H'` is open (image of an open set under the open map `Subtype.val` of the open `k.fixingSubgroup`).
  have hKopen : IsOpen (↑(k.fixingSubgroup) : Set (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)) := fixingSubgroup_isOpen k
  have hH'open : IsOpen (↑H' : Set (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)) := by
    rw [hH', Subgroup.coe_map, Subgroup.coe_subtype]
    exact hKopen.isOpenMap_subtype_val _ hHopen
  have hH'closed : IsClosed (↑H' : Set (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)) :=
    Subgroup.isClosed_of_isOpen H' hH'open
  -- The fixed field of `H'`, taken directly inside the ambient group.
  set L := IntermediateField.fixedField H' with hLdef
  have hLfix : L.fixingSubgroup = H' :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H', hH'closed⟩
  -- `k ≤ L`: every element of `H'` lies in `k.fixingSubgroup`, hence fixes `k` pointwise.
  have hkL : k ≤ L := by
    intro x hx
    rw [hLdef, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (IntermediateField.mem_fixingSubgroup_iff k f).mp (hH'leK hf) x hx
  -- `L` is `ℚ₂`-finite: `H'`-openness travels through Krull into `isOpen_iff_finite`.
  have hLfin : FiniteDimensional ℚ_[2] L := by
    rw [← InfiniteGalois.isOpen_iff_finite L, hLfix]
    exact hH'open
  -- Descend the Krull identity to the `subgroupOf` form via injectivity of `subtype`.
  have hsub : (L.fixingSubgroup).subgroupOf k.fixingSubgroup = H := by
    rw [hLfix, hH']
    exact Subgroup.comap_map_eq_self_of_injective (k.fixingSubgroup.subtype_injective) H
  haveI := hLfin
  refine ⟨L, hkL, hLfin, hsub, ?_⟩
  apply finrank_extendScalars_eq_two k L hkL
  rw [hsub]; exact hHindex

end KummerSurjectivity

end GQ2
