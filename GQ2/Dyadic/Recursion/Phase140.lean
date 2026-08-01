/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Splice
import GQ2.Phase140.LIndep

/-!
# The paper-faithful (140) reducer at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **`b`-typed layer** of `GQ2/Phase140/Obstruction.lean` (468 ln) and
`GQ2/Phase140/LIndep.lean` (65 ln), re-typed at the general `K`-boundary, with the `#H¹` factor
parameterized (memo §4.1(c)).

## Finding: the entire `H²`-machinery half of the model is boundary-free (~130 of 533 ln spine)

`GQ2/Phase140/Obstruction.lean` splits at line 327.  Everything **above** — the `Iota` section
(`iotaB`, `iotaB_eq_zero_iff`, `iotaB_of_mem_B2`, `H2mk_eq_zero_iff`, `iotaB_add`), the `Pull`
section (`pullCoc`, `pullCoc_mem_Z2`), `CoverLift` (`CentralCover.p_z_eq_one`, `ker_dichotomy`,
`z_pow_comm`, `z_pow_val_inj`) and `LiftIff` (`centralCover_lift_iff`,
`sign_iotaB_pullCoc_eq_lift_sign`) — mentions no boundary datum: 11 of the model's 14
declarations, and all of the cohomological content.  They are consumed here by import.

The `b`-typed spine is the `PhaseSign` section (`:327-367`) and `phase140_of_phaseObstruction`
(`:386-459`).  From `LIndep`, `tcocycle_card_l_indep` (`:51`) *is* `b`-typed (it quantifies over
`BoundaryLifts b F RF.TC` through `rhoPrime`) and is cloned; its two-line `Nat.card_congr` proof
is boundary-independent.

## Parameterization delta versus the `ℚ₂` model: the `cardV` / `vH` split

Memo §4.1(c).  The model's `phase140_of_phaseObstruction` **already** carries the factor as an
opaque `(cardV : ℕ)`, pinned by `hWV : cardV = Nat.card ↥RF.MB / Nat.card ↥RF.TBsub` (`:398`),
and that pin is used only to pretty-print the conclusion (`hVcast`, `:454-458`).  The clone:

* keeps `cardV` — the **outer** `#B¹` normalization, degree-independent (memo §1.3);
* adds `vH` — the **inner** `#H¹` factor, the record field `SN.h1Mult |V|`;
* **drops `hWV` entirely** — with `vH` displayed directly there is nothing left to pin, so the
  clone has one hypothesis *fewer* than its model and `hVcast` disappears from the proof.

`hMobst`'s right-hand side becomes `cardV * (vH + G0 * Σ)` and the conclusion's display becomes
`vH * exactImageCountK …`, matching `RecursionInputsK.phase140` / `ClosedRecursionK.eq140`
(`Recursion.lean:462`, `:189`) on the nose.  The `2` and `2 · #D_T` of (140) and the `2·nPhase −
e(C)` sign bookkeeping do **not** move (memo §4.1 non-movers); `sum_phaseSignK` is verbatim.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-! ## The signed liftability through a phase cover -/

section PhaseSign

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)

open scoped Classical in
/-- The **signed liftability** of a lower exact-image map through a phase cover at the
`K`-boundary.  Clone of `GQ2.SectionEight.phaseSign` (`GQ2/Phase140/Obstruction.lean:340`) —
verbatim. -/
noncomputable def phaseSignK (Cζ : CentralCover RF.YC) (ρ : BoundaryLiftsK b F RF.TC) : ℤ :=
  if ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = ρ.1.1 γ then 1 else -1

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(141)** at the `K`-boundary: the signed liftability sum over the lower exact-image maps is
`2·n_{Γ,0}(ζ) − e_Γ(C)`.  Clone of `GQ2.SectionEight.sum_phaseSign`
(`GQ2/Phase140/Obstruction.lean:346`) — verbatim; the `2` here is the ±-class bookkeeping and is
degree-independent (memo §4.1 non-movers). -/
theorem sum_phaseSignK [Fintype (BoundaryLiftsK b F RF.TC)] (Cζ : CentralCover RF.YC) :
    ∑ᶠ ρ : BoundaryLiftsK b F RF.TC, phaseSignK RF b F Cζ ρ
      = 2 * (nPhaseK RF b F Cζ : ℤ) - (exactImageCountK b F RF.TC : ℤ) := by
  classical
  rw [finsum_eq_sum_of_fintype]
  have hterm : ∀ ρ : BoundaryLiftsK b F RF.TC, phaseSignK RF b F Cζ ρ
      = 2 * (if (∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = ρ.1.1 γ)
          then (1 : ℤ) else 0) - 1 := by
    intro ρ
    unfold phaseSignK
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ρ _ => hterm ρ, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  · congr 1
    rw [Finset.sum_boole, show nPhaseK RF b F Cζ = Nat.card {f : BoundaryLiftsK b F RF.TC //
        ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = f.1.1 γ} from rfl,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  · rw [show exactImageCountK b F RF.TC = Nat.card (BoundaryLiftsK b F RF.TC) from rfl,
      Nat.card_eq_fintype_card]

end PhaseSign

/-! ## `l`-independence of the `T`-cocycle count -/

section LIndep

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)

open AffineTLift CentralObstruction in
omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- **`l`-independence of the `T`-cocycle count** at the `K`-boundary.  Clone of
`GQ2.SectionEight.tcocycle_card_l_indep` (`GQ2/Phase140/LIndep.lean:51`) — verbatim: both `M`/`T`
layers are the literal frame fields `RF.MB`/`RF.TBsub`, and `rhoPrimeK` factors through
`piBCiso`, which depends on the datum only through the proof-irrelevant `D.M = RF.MB` witness, so
underlying function, membership and crossed conditions all transport definitionally.

Feeds the (140) `hμ` field: pin `μ` at a reference `l₀`, transport to the current `l` here. -/
theorem tcocycle_cardK_l_indep (En : RF.Enrichment)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (l' : RF.DR) (h' : l' ≠ RF.zeroDR)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      = Nat.card (TCocycle (En.radData l' h') (rhoPrimeK RF b F (En.radData l' h') rfl ρ)) :=
  Nat.card_congr
    ⟨fun u => ⟨u.u, u.mem, u.cont, u.crossed⟩, fun v => ⟨v.u, v.mem, v.cont, v.crossed⟩,
      fun _ => rfl, fun _ => rfl⟩

end LIndep

/-! ## The (140) reducer -/

open AffineTLift CentralObstruction in
/-- **The (140) display from per-`ρ` phase-obstruction data** at the `K`-boundary, with the
`#H¹` factor parameterized.  Clone of `GQ2.SectionEight.phase140_of_phaseObstruction`
(`GQ2/Phase140/Obstruction.lean:386`).

Consumes the identity the paper's Prop 8.9 proof produces per lower map,

  `2·|D_T| · #(central red_T image)(ρ) = cardV · (vH + G0 · Σ_ζ (±1)_{ζ,ρ})`,

and combines it with the `T`-torsor factoring (`zBCK_eq_mu_mul_reductionCount`) and the (141)
count (`sum_phaseSignK`).  Per the header, the model's `hWV` pin is **dropped**: `vH` is displayed
directly, so the clone takes one hypothesis fewer and the model's `hVcast` step disappears.  Every
other step is verbatim.

The conclusion is `RecursionInputsK.phase140` (`Recursion.lean:462`) at `μ := cardV * μ₀`. -/
theorem phase140_of_phaseObstructionK {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (μ₀ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (hC : D.C = RF.scalarCover l h)
    (Dsc : Descent D) (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    [Fintype (BoundaryLiftsK b F RF.TC)]
    (cardV vH : ℕ)
    (hμ : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (TCocycle D (rhoPrimeK RF b F D hD ρ)) = μ₀)
    (hMobst : ∀ ρ : BoundaryLiftsK b F RF.TC,
      2 * (Nat.card DT : ℤ) * (Nat.card ↥(Set.range
          (fun f : {f : MLifts D (rhoPrimeK RF b F D hD ρ) // f.Central} =>
            redT (rhoPrimeK RF b F D hD ρ) f.1)) : ℤ)
        = (cardV : ℤ) * ((vH : ℤ)
            + G0 * ∑ᶠ ζ : DT, phaseSignK RF b F (phase ζ) ρ)) :
    2 * (Nat.card DT : ℤ) * zBCK RF b F l h
      = (cardV * μ₀ : ℕ)
          * ((vH : ℕ) * exactImageCountK b F RF.TC
            + G0 * ∑ᶠ ζ : DT, (2 * (nPhaseK RF b F (phase ζ) : ℤ)
                - (exactImageCountK b F RF.TC : ℤ))) := by
  classical
  -- the `T`-torsor factoring
  have hfib := zBCK_eq_mu_mul_reductionCount RF b F l h D hD hC Dsc htriv hfg μ₀ hμ
  set img : BoundaryLiftsK b F RF.TC → ℕ := fun ρ => Nat.card ↥(Set.range
    (fun f : {f : MLifts D (rhoPrimeK RF b F D hD ρ) // f.Central} =>
      redT (rhoPrimeK RF b F D hD ρ) f.1)) with himg
  have hz : (zBCK RF b F l h : ℤ) = (μ₀ : ℤ) * ∑ ρ, (img ρ : ℤ) := by
    rw [hfib, finsum_eq_sum_of_fintype]
    push_cast
    ring
  have hexact : (exactImageCountK b F RF.TC : ℤ)
      = (Fintype.card (BoundaryLiftsK b F RF.TC) : ℤ) := by
    rw [show exactImageCountK b F RF.TC = Nat.card (BoundaryLiftsK b F RF.TC) from rfl,
      Nat.card_eq_fintype_card]
  -- the (141) evaluation of the swapped inner sum
  have hswap : (∑ ζ : DT, ∑ ρ, phaseSignK RF b F (phase ζ) ρ)
      = ∑ᶠ ζ : DT, (2 * (nPhaseK RF b F (phase ζ) : ℤ)
          - (exactImageCountK b F RF.TC : ℤ)) := by
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [← sum_phaseSignK RF b F (phase ζ), finsum_eq_sum_of_fintype]
  -- sum the per-ρ identity and swap the double sum
  have hsum : 2 * (Nat.card DT : ℤ) * ∑ ρ, (img ρ : ℤ)
      = (cardV : ℤ) * ((exactImageCountK b F RF.TC : ℤ) * vH
          + G0 * ∑ᶠ ζ : DT, (2 * (nPhaseK RF b F (phase ζ) : ℤ)
              - (exactImageCountK b F RF.TC : ℤ))) := by
    calc 2 * (Nat.card DT : ℤ) * ∑ ρ, (img ρ : ℤ)
        = ∑ ρ, 2 * (Nat.card DT : ℤ) * (img ρ : ℤ) := by rw [Finset.mul_sum]
      _ = ∑ ρ, (cardV : ℤ) * ((vH : ℤ)
            + G0 * ∑ᶠ ζ : DT, phaseSignK RF b F (phase ζ) ρ) :=
          Finset.sum_congr rfl fun ρ _ => hMobst ρ
      _ = (cardV : ℤ) * (∑ ρ, ((vH : ℤ)
            + G0 * ∑ ζ : DT, phaseSignK RF b F (phase ζ) ρ)) := by
          rw [← Finset.mul_sum]
          exact congrArg _ (Finset.sum_congr rfl fun ρ _ => by rw [finsum_eq_sum_of_fintype])
      _ = (cardV : ℤ) * ((exactImageCountK b F RF.TC : ℤ) * vH
            + G0 * ∑ ζ : DT, ∑ ρ, phaseSignK RF b F (phase ζ) ρ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
            Finset.sum_comm, hexact, nsmul_eq_mul]
      _ = (cardV : ℤ) * ((exactImageCountK b F RF.TC : ℤ) * vH
            + G0 * ∑ᶠ ζ : DT, (2 * (nPhaseK RF b F (phase ζ) : ℤ)
                - (exactImageCountK b F RF.TC : ℤ))) := by rw [hswap]
  -- assemble (no `hVcast`: `vH` is displayed directly, so there is no pin to discharge)
  rw [hz, show 2 * (Nat.card DT : ℤ) * ((μ₀ : ℤ) * ∑ ρ, (img ρ : ℤ))
      = (μ₀ : ℤ) * (2 * (Nat.card DT : ℤ) * ∑ ρ, (img ρ : ℤ)) from by ring, hsum,
    show ((cardV * μ₀ : ℕ) : ℤ) = (cardV : ℤ) * (μ₀ : ℤ) from by push_cast; ring]
  ring

end GQ2.Dyadic
