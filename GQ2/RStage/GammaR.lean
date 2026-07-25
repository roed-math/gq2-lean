/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.RStage.GammaA
import GQ2.Roe.GammaR

/-!
# The ambient trivial `Γ_R`-action on `𝔽₂`

The **instance prerequisite** of the `Γ_R` source-data supply (ticket R31, discovered by the R30
`SourceData` recon): the `(136)`/`(140)`/Gauss-`Z` layers are all stated at an ambient
`DistribMulAction Γ (ZMod 2)`, and `GQ2.SourceData` carries that action as the three fields
`smulZmod2` / `contSMulZmod2` / `htriv`.  On the `Γ_A` side these are the *global* instances
registered in `GQ2/RStage/GammaA.lean:53-69`; this file registers their `Γ_R` mirrors so that
R32's `sourceR` can fill the three fields with `inferInstance`, `inferInstance`,
`RStageGammaR.htriv_gammaR` — exactly as `BoundaryMaps.sourceA` does
(`GQ2/SourceData.lean:316-318`).

Since `Aut(𝔽₂) = 1`, *every* action of any group on `ZMod 2` is the trivial one, so the content
here is nil: the instance is defined by `smul _ m := m` and `htriv_gammaR` is `rfl`.  What matters
is that the action is **registered globally at the `ProfiniteGrp`-bundled carrier `GammaR`**, the
carrier spelling the `SourceData` fields use (`↥Γ` at `Γ := GammaR`) — a `DistribMulAction`
registered at the raw quotient `F₄ ⧸ N_R` would *not* cross-resolve, exactly the `GammaA`/`GA`
instance-diamond documented in the `GQ2/RStage/GammaA.lean` standing plumbing note.

**Module-system note.**  Plain `import` (non-`module`), like its siblings `GQ2/Roe/Supply.lean`
and `GQ2/Roe/Prop23.lean`: it imports the non-`module` `GQ2.RStage.GammaA`, and `module`-style
files cannot import plain ones.  Importing the `module` file `GQ2.Roe.GammaR` from here is fine —
the restriction is one-directional.

Axioms: none introduced (`htriv_gammaR` is `rfl`; the instances are definitional).
-/

namespace GQ2

namespace RStageGammaR

/-- `Γ_R`'s underlying type is the raw quotient `F₄ ⧸ N_R` against which the Roe marking
machinery (`markC_R`, `Z1wR`, `prop_5_15_R`) is stated — the `Γ_R` mirror of
`RStageGammaA.gammaA_eq_GA`, and the bridge every `Γ_R` word-machinery call transports across. -/
theorem gammaR_eq_quotient : (GammaR : Type) = (FreeProfiniteGroup (Fin 4) ⧸ NR) := rfl

/-! ## The canonical trivial `Γ_R`-action on `𝔽₂` -/

/-- The trivial `Γ_R`-action on `𝔽₂` (`Aut(𝔽₂) = 1`, so every action is this one).  Mirror of
`RStageGammaA.instDistribMulActionGammaA`. -/
instance instDistribMulActionGammaR : DistribMulAction GammaR (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul GammaR (ZMod 2) := ⟨continuous_snd⟩

/-- **The `Γ_R`-action on `𝔽₂` is trivial** — the `htriv` field of `Γ_R`'s `SourceData`
(`GQ2/SourceData.lean:123`), mirror of `RStageGammaA.htriv_gammaA`.  Definitional, from the
registered trivial action. -/
theorem htriv_gammaR (γ : GammaR) (m : ZMod 2) : γ • m = m := rfl

/-! ### Sanity lemmas -/

/-- **Sanity 1.**  The registered action is the trivial one on the nose: scalar multiplication is
the second projection, so it is constant in the group argument. -/
theorem smul_eq_of_gammaR (γ δ : GammaR) (m : ZMod 2) : γ • m = δ • m := rfl

/-- **Sanity 2.**  The `Γ_R` action agrees with the `Γ_A` one under any map of underlying
elements — both are the unique (trivial) action, so the two sources present `𝔽₂` identically to
the `(136)`/`(140)` layers. -/
theorem htriv_gammaR_and_gammaA (γ : GammaR) (α : GammaA) (m : ZMod 2) :
    γ • m = m ∧ α • m = m :=
  ⟨htriv_gammaR γ m, RStageGammaA.htriv_gammaA α m⟩

/-- **Sanity 3.**  The action is by additive-group automorphisms and fixes everything, so the
fixed-point set is all of `𝔽₂` — the degenerate input the `(140)` layer's `fixedPts` factors
reduce through. -/
theorem gammaR_smul_add (γ : GammaR) (m n : ZMod 2) : γ • (m + n) = γ • m + γ • n := by
  rw [htriv_gammaR, htriv_gammaR, htriv_gammaR]

/-! ### `SourceData` field-type smoke tests (R31 spelling discipline)

Each `example` below is stated in the **verbatim field type** of `GQ2.SourceData`
(`GQ2/SourceData.lean:119-123`) specialised at `Γ := GammaR`, so that any future drift between
these declarations and the structure is caught here rather than in R32's `sourceR`.  (The fields
are mutually dependent — `contSMulZmod2`/`htriv` are stated under `letI := smulZmod2` — so the
`letI` is discharged here by the *registered global* instances, which is precisely the
`inferInstance` route `BoundaryMaps.sourceA` takes.) -/

/-- Smoke test for the `SourceData.smulZmod2` field at `Γ := GammaR`. -/
example : DistribMulAction (GammaR : Type) (ZMod 2) := inferInstance

/-- Smoke test for the `SourceData.contSMulZmod2` field at `Γ := GammaR`. -/
example : ContinuousSMul (GammaR : Type) (ZMod 2) := inferInstance

/-- Smoke test for the `SourceData.htriv` field at `Γ := GammaR`. -/
example : ∀ (γ : (GammaR : Type)) (m : ZMod 2), γ • m = m := htriv_gammaR

end RStageGammaR

end GQ2
