import GQ2.RStageLocal
import GQ2.WordCohBridge
import GQ2.HalfTorsorGammaA
import GQ2.FinitelyGenerated

/-!
# P-16d6e5 (residue package, candidate source): the (136) R-stage for `Γ = Γ_A`

Mirror of `GQ2/RStageLocal.lean` at the candidate source `Γ_A`, per `docs/p16d6e5-plan.md`.
The local file counts `Z¹(G_ℚ₂, R)` with `prop_5_16`'s `card_Z1_eq` (B6/B7); here the same
counts come from the **candidate duality** `prop_5_15` (`IsSelfDual`) through the word-complex
bridge `z1Equiv : Z1 GA A ≃+ Z1w (markC ρ)` (`WordCohBridge`) — **no B-axioms on the word side**.

Deliverables (route of record: `docs/p16d6e5-plan.md`):
* `htriv_gammaA` — the trivial `Γ_A`-action on `𝔽₂` (registered here as the canonical trivial
  `DistribMulAction GammaA (ZMod 2)`; `γ • m = m` is then `rfl`);
* `hZcount_gammaA` — `#RCocycle = z_R` via `z1Equiv` + `prop_5_15` clause 2 + `blockRChar_card`;
* `hsep_hom_gammaA` — the `(R^∨)^C`-separation via the marking-level lifting argument (L1–L5 of
  the plan; the trace-span package is `prop_5_8_right`-based, NO `H²(Γ_A,R)`);
* `stageR136_gammaA_of_hcard` — the (136) identity, threading `hcard_A` (P-16d6e6's
  `card_H2_gammaA_eq_two`) so e5 is decoupled from e6.

**Standing plumbing note (the `GA`/`GammaA` bridge).**  `GammaA := profiniteQuotient NA` is
**defeq** to `GA := FreeProfiniteGroup (Fin 4) ⧸ NA`, but their *instances* do not cross-resolve
(distinct head symbols): `GammaA` carries `TotallyDisconnectedSpace` (a `ProfiniteGrp`) while
`GA` does not auto-synthesise it, and a `DistribMulAction GammaA (ZMod 2)` is not found when a
`DistribMulAction GA (ZMod 2)` is requested.  The theorems are stated over `Γ := GammaA` (so the
`blockStageR136`/`RecursionInputs` instances resolve and the conclusion matches the P-16d6e7
`RecursionInputs RF B.bA F …` bundle); the word-machinery calls (over `GA`) are bridged inside
each proof by `inferInstanceAs`/`show`-transports across the defeq (`gammaA_eq_GA` below).  This
is the main mechanical cost of the candidate side and is isolated to the proof interiors.
-/

namespace GQ2

namespace RStageGammaA

open ContCoh SectionEight SectionSeven WordCohBridge GQ2.FoxH

/-- `Γ_A`'s underlying type is the raw quotient `GA` against which the marking machinery
(`z1Equiv`, `markC`, `prop_5_15`) is stated. -/
theorem gammaA_eq_GA : (GammaA : Type) = GA := rfl

/-! ## The canonical trivial `Γ_A`-action on `𝔽₂` -/

/-- The trivial `Γ_A`-action on `𝔽₂` (`Aut(𝔽₂) = 1`, so every action is this one). -/
instance instDistribMulActionGammaA : DistribMulAction GammaA (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul GammaA (ZMod 2) := ⟨continuous_snd⟩

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **The `Γ_A`-action on `𝔽₂` is trivial** (P-16d6e5 residue): definitional, from the
registered trivial action. -/
theorem htriv_gammaA (γ : GammaA) (m : ZMod 2) : γ • m = m := rfl

/-! ## `hZcount`: the `z_R` torsor count at the candidate source

The candidate mirror of `RStageLocal.hZcount_local`: `RCocycle ≃ Z¹(Γ_A, R_{f₀})` (identical
conjugation-action setup, reusing `RStageLocal`'s `ConjAction` section), then the count via
`z1Equiv` + `prop_5_15` clause 2 (`#Z1w = #R²·#fixedPts C (R^∨)`) instead of the local
`card_Z1_eq`, and the same `fixedPts ≃ RCharSub` bridge + `blockRChar_card`. -/
theorem hZcount_gammaA
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
    (f₀ : BoundaryLifts b F T) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
      = (blockFrameImpl T Blk hE2).zR := by
  sorry

/-! ## `hsep_hom`: the `(R^∨)^C` separation at the candidate source (L1–L5, the main work) -/

/-- **The `(R^∨)^C`-separation at `Γ_A`** (P-16d6e5 residue): if the obstruction functional of a
boundary lift `g` vanishes, `g` lifts to a continuous homomorphism into `Y`.  Route
(`docs/p16d6e5-plan.md` §2): `obs g = 0` gives, per invariant character, a concrete lift through
the scalar cover (`obs_zero_iff_lifts`); the relator-value corrections of a set-lift are `d1Fun`
rows (L1); the trace-span package (L3, `prop_5_8_right`) forces full word-solvability; the
corrected marking descends by `markC_admissible` + `NA_le_ker` + `quotientLift` (L5).  `hcard_A`
is threaded (proof-irrelevant Prop; supplied by P-16d6e6's `card_H2_gammaA_eq_two`). -/
theorem hsep_hom_gammaA
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
    (g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_gammaA
        hcard_A g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom GammaA Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ := by
  sorry

/-! ## `stageR136`: the (136) identity, assembled -/

/-- **(136) for the block frame at the candidate source** (P-16d6e5, threading `hcard_A`):
`htriv`/`hZcount`/`hsep_hom` are the residues discharged here; `hcard_A` (P-16d6e6) and the
`lemma_7_2` structural facts `hRK`/`hR2` thread hypothesis-side.  `hfg` is
`gammaA_topologicallyFinitelyGenerated` (P-03 ✓ — dischargeable here, unlike the local B1
reservation).  The conclusion is the `stageR136` field of the candidate `RecursionInputs`
bundle (P-16d6e7 assembly), verbatim. -/
theorem stageR136_gammaA_of_hcard
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  blockStageR136 T Blk hE2 htriv_gammaA hcard_A gammaA_topologicallyFinitelyGenerated b F
    (fun g hg => hsep_hom_gammaA hE2 hRK hR2 hcard_A b F g hg)
    (fun f₀ => hZcount_gammaA hE2 hRK hR2 b F f₀)

end RStageGammaA

end GQ2
