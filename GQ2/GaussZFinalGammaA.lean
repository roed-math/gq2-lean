import GQ2.GaussZCoordGammaA
import GQ2.GaussZRelatorGammaA

/-!
# P-16d6e4aA (A-4): the `Γ_A` Gauss residue — assembly shell + the pinned-value seams

The final brick of the (83)-for-`Γ_A` lane: `gaussZResidue_gammaA_{unramified,ramified}`
discharge the `prop_8_9` ledger hypothesis `hGaussZA` at the pinned values `∓2^m`, mirroring
`GaussZFinal.gaussZResidue_local_*` with the `Γ_A` toolkit:

* the reduction `gaussZ_reduction` (generic) at `Γ := GammaA`, with `Z¹`-finiteness from
  `GaussZCoordGammaA.finite_vcocycle_gammaA` and the `V^{C₀} = 0` freeness from
  `hfix_of_simple_nt` (`hnt`-only — no `hfaith` on the source side);
* the **pinned-value seams** `sum_sign_QZeroBar_gammaA_{unramified,ramified}`:
  `∑ sign(Q̄⁰) = ∓2^m` over `Z¹⧸B¹` — **the A-4 core, currently SORRIED (skeleton-first)**.
  Route (`docs/p16d6e4aA-a4-prep.md`, the paper's Prop 6.5/6.9): reindex the quotient by the
  `x₀`-supported section (`FoxHeisenberg.x0Supported`, the paper's gauge; bijective onto
  `H¹_w` by the `d¹`-closed forms + `card_H1w_gammaA`); evaluate `Q̄⁰` on the section through
  A-3's `QZero_eq_relZPair_kappa0` by the κ⁰-ledger (the quadratic mirror of the banked
  mixed ledgers `heisMarking_wildValue_z`/`_ramified` — Prop 6.5's table: `h₀ ↦ q(c)` via
  `classTwoIdentity`, `[d₀,z₀] ↦ B(c, U⁻¹c)` ram / `0` split); identify with `q̄` (unram,
  `T = 1` ⟹ `U = 1` collapse) / `qDouble q̄ U` (ram) and count via `prop_6_9_unramified` /
  `lemma_6_8` clause 4 + `gaussSum_eq_of_arf_eq`.

Axioms: the shell is std-3; the seams are expected std-3 (word-side; the pins are proved).
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridge FoxH RStageGammaA

section Assembly

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (B : BoundaryMaps) (F : BoundaryFrame H E) (En : RF.Enrichment)

/-- **The unramified pinned value over `Γ_A`** (the A-4 seam, paper Prop 6.9/(91) minus case):
with the tame package acting trivially on `V` (`T = 1`), the descended base determinant form
sums to `−2^m` over `Z¹⧸B¹`.  SORRIED (skeleton-first; the κ⁰-ledger increments fill it). -/
theorem sum_sign_QZeroBar_gammaA_unramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLifts B.bA F RF.TC)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective ⇑c)
    (hfacρ : ∀ g : GammaA, ρ.1.1 g = c (B.tameA g))
    (hunram : ∀ v : En.Vmod, c tameTau • v = v) :
    ∑ᶠ x : VCocycle (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        ⧸ vCobRange (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ),
      sign (QZeroBar (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        htriv_gammaA x)
      = -(2 ^ m : ℤ) := by
  sorry

/-- **The ramified pinned value over `Γ_A`** (the A-4 seam, paper Prop 6.9/(91) plus case):
with the tame package moving `V` (`V^T = 0` regime), the sum is `+2^m`.  SORRIED
(skeleton-first). -/
theorem sum_sign_QZeroBar_gammaA_ramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLifts B.bA F RF.TC)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective ⇑c)
    (hfacρ : ∀ g : GammaA, ρ.1.1 g = c (B.tameA g))
    (hram : ∃ v : En.Vmod, c tameTau • v ≠ v) :
    ∑ᶠ x : VCocycle (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        ⧸ vCobRange (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ),
      sign (QZeroBar (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        htriv_gammaA x)
      = (2 ^ m : ℤ) := by
  sorry

/-- **`hGaussZA`, unramified case** (P-16d6e4aA A-4): with a per-lift tame package whose
inertia acts trivially on `V`, `GaussZResidue B.bA F En l h (−2^m)` — the `prop_8_9` ledger
hypothesis at the pinned unramified value, over the candidate source.  The
`gaussZResidue_local_unramified` twin: `gaussZ_reduction` at `Γ := GammaA` + the pinned seam;
`hfaith` is NOT taken (the `V^{C₀} = 0` freeness runs on `hfix_of_simple_nt`). -/
theorem gaussZResidue_gammaA_unramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hpack : ∀ ρ : BoundaryLifts B.bA F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
      Function.Surjective ⇑c ∧ (∀ g : GammaA, ρ.1.1 g = c (B.tameA g)) ∧
        ∀ v : En.Vmod, c tameTau • v = v) :
    GaussZResidue B.bA F En l h (-(2 ^ m : ℤ)) := by
  intro ρ
  classical
  obtain ⟨c, hc, hfacρ, hunram⟩ := hpack ρ
  set ρM := RF.rhoPrime B.bA F (En.radData l h) rfl ρ with hρMdef
  haveI hfinZ : Finite (VCocycle (En.descData l h) ρM) :=
    finite_vcocycle_gammaA B.bA F En l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective (fun γ : GammaA => rho0 (En.descData l h) ρM γ) := by
    intro y
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime B.bA F En l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (En.descData l h).Vmod,
      (∀ γ : GammaA, rho0 (En.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  calc ∑ᶠ cc : VCocycle (En.descData l h) ρM, sign (QZero (En.descData l h) ρM cc)
      = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ x, sign (QZeroBar (En.descData l h) ρM htriv_gammaA x) :=
        gaussZ_reduction htriv_gammaA hfix
    _ = (Nat.card En.Vmod : ℤ) * (-(2 ^ m : ℤ)) := by
        rw [sum_sign_QZeroBar_gammaA_unramified B F En hsimple hVne hnt m hm hcard l h
          ρ c hc hfacρ hunram]

/-- **`hGaussZA`, ramified case** (P-16d6e4aA A-4): with a per-lift tame package whose
inertia moves `V`, `GaussZResidue B.bA F En l h (+2^m)`. -/
theorem gaussZResidue_gammaA_ramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hpack : ∀ ρ : BoundaryLifts B.bA F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
      Function.Surjective ⇑c ∧ (∀ g : GammaA, ρ.1.1 g = c (B.tameA g)) ∧
        ∃ v : En.Vmod, c tameTau • v ≠ v) :
    GaussZResidue B.bA F En l h (2 ^ m : ℤ) := by
  intro ρ
  classical
  obtain ⟨c, hc, hfacρ, hram⟩ := hpack ρ
  set ρM := RF.rhoPrime B.bA F (En.radData l h) rfl ρ with hρMdef
  haveI hfinZ : Finite (VCocycle (En.descData l h) ρM) :=
    finite_vcocycle_gammaA B.bA F En l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective (fun γ : GammaA => rho0 (En.descData l h) ρM γ) := by
    intro y
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime B.bA F En l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (En.descData l h).Vmod,
      (∀ γ : GammaA, rho0 (En.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  calc ∑ᶠ cc : VCocycle (En.descData l h) ρM, sign (QZero (En.descData l h) ρM cc)
      = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ x, sign (QZeroBar (En.descData l h) ρM htriv_gammaA x) :=
        gaussZ_reduction htriv_gammaA hfix
    _ = (Nat.card En.Vmod : ℤ) * (2 ^ m : ℤ) := by
        rw [sum_sign_QZeroBar_gammaA_ramified B F En hsimple hVne hnt m hm hcard l h
          ρ c hc hfacρ hram]

end Assembly

end AffineTLift

end SectionEight

end GQ2
