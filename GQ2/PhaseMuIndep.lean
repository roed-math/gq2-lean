import GQ2.RadicalEdgeBridge
import GQ2.AffineTLift

/-!
# P-16d6b: μ-independence of the `T`-cocycle count  (Route A — coboundary twist)

The (140) engine (`zBC_eq_mu_mul_reductionCount`, `phase140_of_nonsingular`) consumes a constant
`μ` with `hμ : ∀ ρ, Nat.card (TCocycle D (rhoPrime ρ)) = μ` — the crossed count `#Z¹_{Γ,ρ}(T)` is
**independent of the exact-image map `ρ`** (paper 5.15/5.16 content).

**Route (corrected).**  The two ρ-twisted conjugation actions on `T` are *genuinely different*
`Γ`-module structures — only `M` (not `L_B ⊇ M`) centralizes `T`, so `w ∈ L_B/M` acts on `T` by a
non-identity unipotent map and there is **no elementary twist bijection** (the naive Route A).
The counts nonetheless coincide, by the **local Euler characteristic**: `prop_5_16_bundle` clause 2
gives `#Z¹_{Γ,ρ}(T) = |T|² · |fixedPts(ρ(Γ), T^∨)|`, and every boundary lift `ρ` is
**surjective** onto `YC` (`BoundaryLifts` wraps `ContSurj`), so `ρ(Γ) = C` and
`fixedPts(ρ(Γ), T^∨) = fixedPts(C, T^∨)` is one and the same value for all `ρ`.  Hence
`μ = |T|² · |(T^∨)^C|`, manifestly ρ-independent.

This file (own leaf, off the co-owned `RecursionSplice.lean`) banks:
* `boundaryLift_diff_mem_LY` — the shared-boundary fact (`ρ'/ρ ∈ L_C`); **proved**.
* `tcocycle_mu_indep` — the `∃μ` packaging, reducing to the pairwise core; **proved**.
* `tcocycle_card_indep` — the count-equality core (**Route B**, via `prop_5_16_bundle`);
  **in progress** (needs the `TCocycle D ρ ≃ Z1 Γ T` bridge + surjectivity).

Packaging + boundary fact are `Ax ∅`; the core's audit will be `⊆ {B6, B7, B9}` (Euler char).
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
variable (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)

/-- **Shared-boundary fact**: two boundary lifts of the same `C`-target agree after `π_Y`, so their
ratio lands in `ker π_Y = L_C = RF.TC.LY`.  (The cochain whose twist relates the two ρ-actions.) -/
theorem boundaryLift_diff_mem_LY (ρ ρ' : BoundaryLifts b F RF.TC) (γ : Γ) :
    ρ'.1.1 γ * (ρ.1.1 γ)⁻¹ ∈ RF.TC.LY := by
  have hρ := (ρ.2 γ)
  have hρ' := (ρ'.2 γ)
  -- both first components equal `(F.frameMap (b γ)).1`, so the `π_Y`-images agree
  have hpi : RF.TC.piY (ρ'.1.1 γ) = RF.TC.piY (ρ.1.1 γ) := by
    have h1 : RF.TC.piY (ρ.1.1 γ) = (F.frameMap (b γ)).1 := congrArg Prod.fst hρ
    have h2 : RF.TC.piY (ρ'.1.1 γ) = (F.frameMap (b γ)).1 := congrArg Prod.fst hρ'
    rw [h1, h2]
  rw [← RF.TC.ker_piY, MonoidHom.mem_ker, map_mul, map_inv, hpi, mul_inv_cancel]

/-- **P-16d6b core (Route B)**: `#Z¹_{Γ,ρ}(T)` is the same for any two boundary lifts of the
`C`-target.  The actions differ (no twist bijection); the equality is the Euler-characteristic
count, ρ-independent because boundary lifts are surjective.

**Plan (in progress):**
1. **Bridge** `TCocycle D ρ ≃ Z1 Γ T`: turn the crossed-cocycle structure (`u : Γ → Bg`,
   `u γ ∈ T`, ρ-conjugation) into the additive `GQ2.Z1 Γ T` for `T` as an `𝔽₂[Γ]`-module with the
   ρ-twisted `DistribMulAction` (`γ • t := c · t · c⁻¹`, `mk c = ρ γ`; well-defined by `M_cent_T`,
   `𝔽₂`-linear by `D.helem`/`D.hcomm`).
2. **Count** via `prop_5_16_bundle` clause 2: `#Z1 = |T|² · |fixedPts(ρ(Γ), T^∨)|` — supplying its
   two-action hypotheses at the T-layer (`hcomp` from the bridge, `hA₂` = `D.helem`, `hpair` from
   the polar form).
3. **ρ-independence**: `ρ.1.1 : Γ ↠ YC` surjective (`BoundaryLifts` ⊆ `ContSurj`), so
   `ρ(Γ) = C` and `fixedPts(ρ(Γ), T^∨) = fixedPts(C, T^∨)`, identical for `ρ` and `ρ'`.  Then both
   counts equal `|T|² · |(T^∨)^C|`.

(`boundaryLift_diff_mem_LY` is banked but not on the critical path for Route B; kept as a true
lemma.) -/
theorem tcocycle_card_indep (ρ ρ' : BoundaryLifts b F RF.TC) :
    Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ))
      = Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ')) := by
  sorry

/-- **P-16d6b deliverable**: the `T`-cocycle count is `ρ`-independent — the constant `μ` and the
`hμ` hypothesis consumed by `zBC_eq_mu_mul_reductionCount` / `phase140_of_nonsingular`. -/
theorem tcocycle_mu_indep :
    ∃ μ : ℕ, ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ := by
  by_cases h : Nonempty (BoundaryLifts b F RF.TC)
  · obtain ⟨ρ₀⟩ := h
    exact ⟨Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ₀)),
      fun ρ => tcocycle_card_indep RF b F D hD ρ ρ₀⟩
  · exact ⟨0, fun ρ => absurd ⟨ρ⟩ h⟩

end SectionEight

end GQ2
