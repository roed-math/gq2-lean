/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.TameBoundary

/-!
# The boundary-abstracted frame layer (dyadic campaign, ticket SD-R1)

Clone of the frame/lift/count layer of `GQ2/BoundaryFrame.lean:261-358`, re-typed at the
general `K`-boundary `boundarySubgroupQ q nuP` (F3, `GQ2/Dyadic/TameBoundary.lean:159`)
in place of the concrete `ℚ₂` boundary `boundarySubgroup` (`GQ2/BoundaryFrame.lean:248`).

## Parameterization delta versus the `ℚ₂` model

| model (`GQ2/BoundaryFrame.lean`) | clone | change |
|---|---|---|
| `Ttame` (:124) | `Tq q` (`TameQuotientK.lean:257`) | F3's general tame group, SD1 memo §2.1 |
| `PiBd` (:142) | `(P : ProfiniteGrp)` with `nuP` | abstract marked pro-2 slot, SD1 memo §2.2 (Q4) |
| `boundarySubgroup` (:248) | `boundarySubgroupQ q nuP` | the general fibre product |
| `BoundaryFrame` (:267) | `BoundaryFrameK q P` | `alpha` at `Tq q`, `psiBar` at `P` |
| `MarkedTarget` (:288) | **reused verbatim** | target-side, boundary-free (memo §3.2) |

`IsProP 2 ↥P` is *not* a parameter of this layer: the frame and the counts never inspect the
pro-2 structure of the slot (it enters only at the `SourceDataN` record and at instantiation
time — memo §2.2).  `nuP` enters only through the type of `b`.

**The `n = 1` bridge is definitional** (memo §0/§2.1, probe P1): `boundarySubgroupQ 2 nuTwo =
boundarySubgroup := rfl`, so at `q = 2`, `P := PiBd`, `nuP := nuTwo` every declaration below is
stated at *literally* the `ℚ₂` boundary — no transport, no cast.  `frameMapK_eq_frameMap`
and `exactImageCountK_eq_exactImageCount` below record this as `rfl`-lemmas for SD2/SD3 and the
`n = 1` regression.

Naming scheme (memo §4, for SD2/SD3 pinning): every clone is its model's name with a `K`
suffix.  Namespace `GQ2.Dyadic`.

Plain-import (memo §5): this leaf and the whole `GQ2/Dyadic/Recursion/` subtree import the
plain-import §8/§9 stack, so none of it may be `module`-style.

Axioms: **none beyond std-3.**  Print check performed for every declaration in this file:
each prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print
(`GQ2.finite_boundaryLifts`, `GQ2.exactImageCount`) — hence a subset, as SD-R acceptance
requires.
-/

open scoped Pointwise

namespace GQ2.Dyadic

/-! ## The frame  (eq. (28) at the `K`-boundary) -/

/-- **The `K`-boundary frame** — clone of `GQ2.BoundaryFrame` (`GQ2/BoundaryFrame.lean:267`)
with `alpha` re-typed from `Ttame` to F3's `Tq q` and `psiBar` from `PiBd` to the abstract
marked pro-2 slot `P`.  A finite tame quotient `α : T_q ↠ H`, an elementary abelian 2-group
`E`, and a homomorphism `ψ̄ : P → E`. -/
structure BoundaryFrameK (q : ℕ) (P : ProfiniteGrp) (H E : Type) [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    [Finite E] where
  /-- The finite tame quotient map `α : T_q ↠ H`. -/
  alpha : ContinuousMonoidHom (Tq q) H
  alpha_surjective : Function.Surjective alpha
  /-- `E` has exponent 2 ("elementary abelian"). -/
  exponent_two : ∀ e : E, e ^ 2 = 1
  /-- The scalar datum `ψ̄ : P → E`. -/
  psiBar : ContinuousMonoidHom P E

/-- The comparison map `β : ∂ → H × E`, `β(t, p) = (α t, ψ̄ p)` — clone of
`GQ2.BoundaryFrame.frameMap` (`GQ2/BoundaryFrame.lean:278`) at `boundarySubgroupQ q nuP`. -/
noncomputable def BoundaryFrameK.frameMap {q : ℕ} {P : ProfiniteGrp} {H E : Type} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] {nuP : ContinuousMonoidHom P Ztwo}
    (F : BoundaryFrameK q P H E) (x : ↥(boundarySubgroupQ q nuP)) : H × E :=
  (F.alpha x.val.1, F.psiBar x.val.2)

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {H E Y : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-! ## The exact-image counts  (eq. (29) at the `K`-boundary)

`MarkedTarget` and `MarkedTarget.stratum` (`GQ2/BoundaryFrame.lean:288,307`) are **not**
cloned: they are target-side and mention no boundary object, so they are consumed by import
(memo §3.2, "`MarkedTarget` is reused verbatim"). -/

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- The **boundary equation** of eq. (29) at the `K`-boundary: `q_Y ∘ f = β ∘ b_Γ`, pointwise
on `Γ`.  Clone of `GQ2.IsBoundaryLift` (`GQ2/BoundaryFrame.lean:328`). -/
def IsBoundaryLiftK [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) (f : ContinuousMonoidHom Γ Y) : Prop :=
  ∀ γ : Γ, (T.piY (f γ), T.thetaY (f γ)) = F.frameMap (b γ)

/-- The set counted by eq. (29) at the `K`-boundary.  Clone of `GQ2.BoundaryLifts`
(`GQ2/BoundaryFrame.lean:335`). -/
def BoundaryLiftsK [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) : Type :=
  {f : ContSurj Γ Y // IsBoundaryLiftK b F T f.1}

/-- **`e^β_Γ(𝒴)`** at the `K`-boundary (eq. (29)).  Clone of `GQ2.exactImageCount`
(`GQ2/BoundaryFrame.lean:343`). -/
noncomputable def exactImageCountK [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) : ℕ :=
  Nat.card (BoundaryLiftsK b F T)

/-- The count is genuinely finite when `Γ` is topologically finitely generated.  Clone of
`GQ2.finite_boundaryLifts` (`GQ2/BoundaryFrame.lean:350`) — verbatim proof. -/
theorem finite_boundaryLiftsK [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Finite (BoundaryLiftsK b F T) := by
  haveI : Finite (ContinuousMonoidHom Γ Y) := finite_continuousMonoidHom hfg Y
  haveI : Finite (ContSurj Γ Y) := Subtype.finite
  exact Subtype.finite

/-! ## The `n = 1` refl-bridge  (memo §0, probe P1)

At `q = 2`, `P := PiBd`, `nuP := nuTwo` the general boundary **is** the `ℚ₂` boundary
definitionally, so the clone's counts are the model's counts on the nose.  These lemmas are
the acceptance hooks SD2/SD3 pin against; each is `rfl`. -/

/-- F3's refl-bridge at the subgroup level (probe P1): the general boundary at `q = 2` with the
`ℚ₂` slot **is** `GQ2.boundarySubgroup`. -/
theorem boundarySubgroupQ_two : boundarySubgroupQ 2 nuTwo = boundarySubgroup := rfl

/-- The `n = 1` frame: a `K`-frame at `q = 2`, `P := PiBd` **is** a `ℚ₂` boundary frame. -/
@[simps] def BoundaryFrameK.toBoundaryFrame (F : BoundaryFrameK 2 PiBd H E) :
    BoundaryFrame H E where
  alpha := F.alpha
  alpha_surjective := F.alpha_surjective
  exponent_two := F.exponent_two
  psiBar := F.psiBar

/-- The frame maps agree at `n = 1` — `rfl`. -/
theorem frameMapK_eq_frameMap (F : BoundaryFrameK 2 PiBd H E)
    (x : ↥(boundarySubgroupQ 2 nuTwo)) :
    F.frameMap x = F.toBoundaryFrame.frameMap x := rfl

/-- The boundary equations agree at `n = 1` — `rfl`. -/
theorem isBoundaryLiftK_eq [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) (F : BoundaryFrameK 2 PiBd H E)
    (T : MarkedTarget H E Y) (f : ContinuousMonoidHom Γ Y) :
    IsBoundaryLiftK b F T f = IsBoundaryLift b F.toBoundaryFrame T f := rfl

/-- The counted sets agree at `n = 1` — `rfl`. -/
theorem boundaryLiftsK_eq [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) (F : BoundaryFrameK 2 PiBd H E)
    (T : MarkedTarget H E Y) :
    BoundaryLiftsK b F T = BoundaryLifts b F.toBoundaryFrame T := rfl

/-- **The `n = 1` count regression**: the clone's exact-image count is the model's — `rfl`.
This is the hook `thm_4_2_via_N` (memo §3.4) needs to typecheck at the old boundary. -/
theorem exactImageCountK_eq [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) (F : BoundaryFrameK 2 PiBd H E)
    (T : MarkedTarget H E Y) :
    exactImageCountK b F T = exactImageCount b F.toBoundaryFrame T := rfl

end GQ2.Dyadic
