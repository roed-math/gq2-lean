/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.RadicalEdge.Bridge
import GQ2.AffineTLift

/-!
# `l`-independence of the `T`-cocycle count

The (140) witness `μ` of `prop_8_9` is fixed once, at a reference scalar `l₀`
(`docs/orchestration/p16d6-concrete-spec.md` §1: `μ := Nat.card (TCocycle (En.radData l₀ h₀) …)`), but the
`phase140_of_nonsingular` field needs `hμ (l h) : ∀ ρ, Nat.card (TCocycle (En.radData l h) …) = μ`
at the **current** scalar `l`.  Combined with the `ρ`-independence of the Prop. 8.9 assembly
(`tcocycle_mu_indep`), that requires the count to be **independent of `l`** as well.

This is nearly definitional: the enrichment datum `En.radData l h` varies with `l` only in its
cover `C := RF.scalarCover l h` and its square form `q := En.q l h`, but

* `TCocycle D ρ` reads `D` **only through `D.T`** (`u γ ∈ D.T`; the crossed condition is about `ρ`
  and conjugation, not the cover), and `(En.radData l h).T = RF.TBsub` for every `l`;
* the lower map `RF.rhoPrime b F (En.radData l h) rfl ρ = (piBCiso …).symm ∘ ρ` depends on the datum
  only through `D.M = RF.MB` (via `piBCiso`), again constant in `l`.

So the two count objects coincide.  Pure std-3, no source input — the genuinely `l`-dependent piece
of the witness is `G0 = gaussSum (En.qbar l h)` (part of the Prop. 8.9 assembly; see `docs/orchestration/p16d6c-handoff.md`).
-/

namespace GQ2

namespace SectionEight

open CentralObstruction AffineTLift

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace Y]
  [DiscreteTopology Y] in
/-- **`l`-independence of the `T`-cocycle count** (the Prop. 8.9 assembly, c3): for a fixed boundary lift `ρ`, the
crossed count `#Z¹_{Γ,ρ}(T)` computed against the enrichment datum `En.radData l h` does not depend
on the scalar `l` — the datum's `M`/`T` layers (and hence `TCocycle` and `rhoPrime`) are the same
for every `l`.  Feeds the (140) `hμ` field: pin `μ` at a reference `l₀`, transport to the current
`l` here, then apply the Prop. 8.9 assembly's `ρ`-independence. -/
theorem tcocycle_card_l_indep (En : RF.Enrichment)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (l' : RF.DR) (h' : l' ≠ RF.zeroDR)
    (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (TCocycle (En.radData l' h') (RF.rhoPrime b F (En.radData l' h') rfl ρ)) := by
  -- both `M`/`T` layers are `RF.MB`/`RF.TBsub`, and `rhoPrime` factors through `piBCiso`, which
  -- depends on the datum only via the (proof-irrelevant) `D.M = RF.MB` witness — so the underlying
  -- function, membership, and crossed conditions all transport on the nose (defeq).
  exact Nat.card_congr
    ⟨fun u => ⟨u.u, u.mem, u.cont, u.crossed⟩, fun v => ⟨v.u, v.mem, v.cont, v.crossed⟩,
      fun u => rfl, fun v => rfl⟩

end SectionEight

end GQ2
