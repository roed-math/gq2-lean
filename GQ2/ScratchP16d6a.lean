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

end GQ2
