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

end GQ2
