import GQ2.RStageObstruction
import GQ2.CentralObstruction

/-!
# §8 R-stage obstruction module — Option-A construction  (P-16d2)

Builds the obstruction datum `obs`/`hmB`/`hobs`/`hfib` consumed by
`GQ2.SectionEight.stageR136_ofObstruction` (`GQ2/RStageObstruction.lean`), from the **Option-A
compatibility structure** `RCoverData` (user-approved 2026-07-05): the datum, absent from the bare
`RecursionFrame` + `Enrichment`, that each scalar cover `p_λ = (scalarCover l).p` really is a
quotient of the single radical extension `Y ↠ B = Y/R` — a hom family
`coverMap_λ : Y →* (scalarCover l).cover` with `p_λ ∘ coverMap_λ = π_B`.

Kept self-contained here (own file, no edit to the co-owned `Enrichment`); a later refactor may
fold `RCoverData` into `Enrichment` as a field.  See `docs/p16d2-plan.md` for the full route.

Build status (see the per-lemma notes): the compatibility structure and the "lifts to `Y` ⟹ lifts
through every `p_λ`" direction are std-3; the obstruction-linearity, the hard separation, and the
`z_R` torsor count are the remaining cores (each needs the twisted-cocycle layer for the
`R`-extension — tracked).
-/

namespace GQ2

namespace SectionEight

open SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

/-- **Option-A compatibility datum (P-16d2)**: the missing link between the frame's abstract scalar
covers and the single radical extension `Y ↠ B`.  For each nonzero scalar character `λ`, a
homomorphism `coverMap λ : Y →* (scalarCover λ).cover` realizing `scalarCover λ` as a quotient of
`Y` over `B`: `p_λ ∘ coverMap λ = π_B`.  (This is the frame-level content of "`p_λ` is the pushout
`Y/ker λ ↠ Y/R`", which the `RecursionFrame`/`Enrichment` document but do not carry.) -/
structure RCoverData {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) where
  /-- `coverMap λ : Y →* B_λ`, the realization of the scalar cover as a quotient of `Y`. -/
  coverMap : (l : RF.DR) → (h : l ≠ RF.zeroDR) → Y →* (RF.scalarCover l h).cover
  /-- `p_λ ∘ coverMap λ = π_B`: the cover projects `coverMap λ` back to the `B`-stage map. -/
  coverMap_lifts : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (RF.scalarCover l h).p.comp (coverMap l h) = RF.piB

namespace RCoverData

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  {RF : RecursionFrame T Blk}

/-- `coverMap λ` bundled as a `ContinuousMonoidHom` (free: `Y` is discrete). -/
noncomputable def coverMapC (D : RCoverData RF) (l : RF.DR) (h : l ≠ RF.zeroDR) :
    ContinuousMonoidHom Y (RF.scalarCover l h).cover :=
  ⟨D.coverMap l h, continuous_of_discreteTopology⟩

/-- **Easy `hobs` direction**: if a `B`-stage boundary lift `f` lifts all the way to `Y` (is
`RF.liftB` of some `Y`-lift `F`), then it lifts through **every** scalar cover `p_λ` — compose the
`Y`-lift with `coverMap λ`.  (The converse — "lifts through every `p_λ` ⟹ lifts to `Y`" — is the
hard separation, using `R`-elementary-abelianness and the Frattini structure.) -/
theorem lifts_scalarCover_of_liftB (D : RCoverData RF)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (fY : BoundaryLifts b F T) :
    ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
      ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = (RF.liftB b F fY).1.1 γ := by
  refine ⟨(D.coverMapC l h).comp fY.1.1, fun γ => ?_⟩
  show (RF.scalarCover l h).p (D.coverMap l h (fY.1.1 γ)) = RF.piB (fY.1.1 γ)
  rw [← MonoidHom.comp_apply, D.coverMap_lifts l h]

end RCoverData

end SectionEight

end GQ2
