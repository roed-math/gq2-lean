import GQ2.KeystoneDelta
import GQ2.WordCoh2

/-!
# P-16d6e4aA (A-2) — the `ι_{Γ_A}`-computation rule

The F-brick of the (83)-for-`Γ_A` seam (`docs/p16d6e4aA-gammaA-gauss-design.md` §2):
the coboundary indicator `ι_Γ` (`SectionEight.iotaB`, the `Q⁰`-valuation) is computed, over
the raw candidate carrier `GA = F₄ ⧸ N_A`, by the **word-relator obstruction** of the P-16c4
degree-2 presentation-comparison:

* `iotaB_eq_obs` — `ι_{Γ_A} φ = obs φ` for every continuous 2-cocycle `φ`: both are
  `𝔽₂`-valued with the *same* vanishing locus (`iotaB_eq_zero_iff` vs the c4 keystone
  `WordCoh2.obs_ker_eq_B2`), hence equal.
* `iotaB_eq_levelFactor_obs` — the evaluation form: `ι_{Γ_A} φ` is the (tame + wild) relator
  obstruction `F.obs = relZPair(…).1 + relZPair(…).2` of **any** finite-admissible-level
  factorization `F` of the `(1,1)`-normalization of `φ` (`obsFun_eq` well-definedness).
* `QZero_eq_obs` / `QZero_eq_levelFactor_obs` — the same, specialized to the base
  determinant form: `Q⁰_{Γ_A,ρ'}(c)` is the relator obstruction of any level factorization
  of the (normalized) graph pullback `graphPullback DD.dat ρ'₀ c.c` — **the A-3 interface**:
  brick A-3 constructs an explicit `LevelFactor` for the graph pullback in the e6 generator
  coordinates and reads the two relator values off the factor-set expansion.

Everything is glue over landed technology (`iotaB` = the `B²`-indicator,
`PhaseObstruction.lean:51`; `obs`/`obs_ker_eq_B2`/`obsFun_eq`, `WordCoh2.lean` §CardBound;
`graphPullback_mem_Z2_of_cocycle`, `KeystoneDelta.lean:1516`, generic-`Γ`) — std-3, no
axioms, no sorries.
-/

namespace GQ2

namespace IotaGammaA

open SectionEight SectionEight.AffineTLift WordCohBridge WordCoh2 ContCoh

variable [DistribMulAction GA (ZMod 2)] [ContinuousSMul GA (ZMod 2)]
variable (htriv : ∀ (x : GA) (m : ZMod 2), x • m = m)
include htriv

omit [ContinuousSMul GA (ZMod 2)] in
/-- **The `ι_{Γ_A}`-computation rule** (A-2 core): the coboundary indicator agrees with the
P-16c4 word-relator obstruction on every continuous 2-cocycle — both are `𝔽₂`-valued with
kernel exactly `B²(Γ_A, 𝔽₂)`. -/
theorem iotaB_eq_obs (φ : Z2 GA (ZMod 2)) :
    iotaB (φ : GA × GA → ZMod 2) = WordCoh2.obs htriv φ := by
  have h2 : WordCoh2.obs htriv φ = 0 ↔ (φ : GA × GA → ZMod 2) ∈ B2 GA (ZMod 2) := by
    rw [← AddMonoidHom.mem_ker, obs_ker_eq_B2 htriv, AddSubgroup.mem_addSubgroupOf]
  exact (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _
    (iotaB_eq_zero_iff.trans h2.symm)

omit [ContinuousSMul GA (ZMod 2)] in
/-- **The evaluation form** (the A-3 interface, cocycle-level): `ι_{Γ_A} φ` is the
(tame + wild) relator obstruction of *any* finite-admissible-level factorization of the
`(1,1)`-normalization of `φ`. -/
theorem iotaB_eq_levelFactor_obs (φ : Z2 GA (ZMod 2))
    (F : LevelFactor (normalizeCochain (φ : GA × GA → ZMod 2))) :
    iotaB (φ : GA × GA → ZMod 2) = F.obs :=
  (iotaB_eq_obs htriv φ).trans (obsFun_eq htriv φ F)

section QZero

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {ρM : ContinuousMonoidHom GA (Bg ⧸ D.M)}

omit [ContinuousSMul GA (ZMod 2)] in
/-- **`Q⁰` over `Γ_A` is the word-relator obstruction** (A-2 → A-3 handoff, packaged form):
the base determinant form evaluates through `obs` at the graph pullback. -/
theorem QZero_eq_obs (c : VCocycle DD ρM) :
    QZero DD ρM c
      = WordCoh2.obs htriv ⟨graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c,
          graphPullback_mem_Z2_of_cocycle htriv c⟩ :=
  iotaB_eq_obs htriv ⟨graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c,
    graphPullback_mem_Z2_of_cocycle htriv c⟩

omit [ContinuousSMul GA (ZMod 2)] in
/-- **The A-3 consumable**: `Q⁰_{Γ_A,ρ'}(c)` is the (tame + wild) relator obstruction of any
finite-admissible-level factorization of the normalized graph pullback.  A-3 supplies an
explicit `LevelFactor` in the e6 generator coordinates and expands `F.obs` along the two
relator words. -/
theorem QZero_eq_levelFactor_obs (c : VCocycle DD ρM)
    (F : LevelFactor (normalizeCochain
      (graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c))) :
    QZero DD ρM c = F.obs :=
  (QZero_eq_obs htriv c).trans
    (obsFun_eq htriv ⟨graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c,
      graphPullback_mem_Z2_of_cocycle htriv c⟩ F)

end QZero

end IotaGammaA

end GQ2
