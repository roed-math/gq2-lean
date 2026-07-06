import GQ2.BlockFrameImpl
import GQ2.RStageObstructionBuild

/-!
# P-16d6a (banked WIP): the concrete R-stage obstruction datum for `blockFrame`

Builds `RObstructionData (blockFrameImpl T Blk hE2)` — the (136) `stageR136` datum — against the
concrete §7-block frame (P-17c ✓, `blockFrameImpl`).  Not yet spliced.

Concrete covers (`blockFrameImpl`): `YB = Y/R`, `piB = mk' R`, `scalarCover l h` = the cover
`Y/l ↠ Y/R` (`cover = Y/l.1`, `p = map l.1 R id`, `z = mk' l.1 r₀`).  So `coverMap l h = mk' l.1`
and `coverMap_lifts` is `map ∘ mk' = mk'`.
-/

namespace GQ2

open SectionEight SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- The R-stage compat covers of the concrete block frame: `coverMap l h = mk' l.1`. -/
noncomputable def blockRCoverData (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    RCoverData (blockFrameImpl T Blk hE2) where
  coverMap := fun l _h => by
    haveI : (l.1).Normal := l.2.1
    exact QuotientGroup.mk' l.1
  coverMap_lifts := fun l _h => by
    haveI : (l.1).Normal := l.2.1
    ext y
    rfl

/-! ## a-DRmod: `D_Rmod` as the Y-invariant `𝔽₂`-characters of `R` -/

open scoped Classical

variable {L : Subgroup Y}

/-- **Y-invariant `𝔽₂`-characters of `R = Blk.R = Φ(K)`** (`(R^∨)^C`): additive homs
`R → 𝔽₂` fixed by `Y`-conjugation.  Their kernels are exactly the index-≤2 `Y`-normal
subgroups of `R`, i.e. `D_R`; this submodule is the `𝔽₂`-realization `D_Rmod`. -/
def RCharSub (Blk : SectionSeven.MinimalBlock L) :
    Submodule (ZMod 2) (Additive ↥Blk.R →+ ZMod 2) where
  carrier := {χ | ∀ (y : Y) (r : ↥Blk.R),
    χ (Additive.ofMul ⟨y * (r : Y) * y⁻¹,
        (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 y⟩)
      = χ (Additive.ofMul r)}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {χ ψ} hχ hψ y r => by
    simp only [AddMonoidHom.add_apply, hχ y r, hψ y r]
  smul_mem' := fun c {χ} hχ y r => by
    simp only [AddMonoidHom.smul_apply, hχ y r]

/-- `D_Rmod` is finite. -/
instance (Blk : SectionSeven.MinimalBlock L) : Finite ↥(RCharSub Blk) := by
  haveI : Finite (Additive ↥Blk.R → ZMod 2) := inferInstance
  haveI : Finite (Additive ↥Blk.R →+ ZMod 2) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Additive ↥Blk.R →+ ZMod 2))
  infer_instance

/-- The kernel of a character `χ`, as a subgroup of `↥Blk.R`. -/
def RCharKerSub (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) : Subgroup ↥Blk.R where
  carrier := {r | χ.1 (Additive.ofMul r) = 0}
  one_mem' := by
    show χ.1 (Additive.ofMul 1) = 0
    rw [show Additive.ofMul (1 : ↥Blk.R) = 0 from rfl, map_zero]
  mul_mem' := fun {a b} ha hb => by
    show χ.1 (Additive.ofMul (a * b)) = 0
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
      map_add, ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    show χ.1 (Additive.ofMul a⁻¹) = 0
    rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a from rfl, map_neg, ha, neg_zero]

/-- `χ` as a `MonoidHom ↥R →* Multiplicative 𝔽₂` (for the kernel/index calculus). -/
def RCharMulHom (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    ↥Blk.R →* Multiplicative (ZMod 2) where
  toFun r := Multiplicative.ofAdd (χ.1 (Additive.ofMul r))
  map_one' := by
    show Multiplicative.ofAdd (χ.1 (Additive.ofMul (1 : ↥Blk.R))) = 1
    rw [show Additive.ofMul (1 : ↥Blk.R) = 0 from rfl, map_zero]; rfl
  map_mul' := fun a b => by
    show Multiplicative.ofAdd (χ.1 (Additive.ofMul (a * b))) = _ * _
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add]; rfl

theorem RCharKerSub_eq_ker (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    RCharKerSub Blk χ = (RCharMulHom Blk χ).ker := by
  ext r
  rw [MonoidHom.mem_ker]
  show χ.1 (Additive.ofMul r) = 0 ↔ Multiplicative.ofAdd (χ.1 (Additive.ofMul r)) = 1
  rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq]

/-- The kernel of `χ`, pushed to a subgroup of `Y`. -/
def RCharKer (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) : Subgroup Y :=
  (RCharKerSub Blk χ).map Blk.R.subtype

theorem RCharKer_le (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    RCharKer Blk χ ≤ Blk.R := by
  rw [RCharKer]; exact Subgroup.map_subtype_le _

theorem RCharKer_normal (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (RCharKer Blk χ).Normal := by
  constructor
  intro n hn g
  rw [RCharKer, Subgroup.mem_map] at hn ⊢
  obtain ⟨r, hr, rfl⟩ := hn
  refine ⟨⟨g * (r : Y) * g⁻¹,
      (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 g⟩, ?_, rfl⟩
  show χ.1 (Additive.ofMul ⟨g * (r : Y) * g⁻¹, _⟩) = 0
  rw [χ.2 g r]
  exact hr

theorem RCharKer_relIndex_le (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (RCharKer Blk χ).relIndex Blk.R ≤ 2 := by
  have h1 : (RCharKer Blk χ).relIndex Blk.R = (RCharKerSub Blk χ).index := by
    rw [Subgroup.relIndex, RCharKer, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective Blk.R.subtype_injective]
  rw [h1, RCharKerSub_eq_ker, Subgroup.index_ker]
  calc Nat.card (RCharMulHom Blk χ).range
      ≤ Nat.card (Multiplicative (ZMod 2)) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl

end GQ2
