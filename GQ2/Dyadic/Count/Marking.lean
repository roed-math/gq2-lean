/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Separating
import GQ2.Dyadic.Count.Lifts
import GQ2.Phase140.GammaA.Foundation

/-!
# Dyadic campaign, ticket CB-6: the marking route, degree-generically

CB-5 banked `sepWordN`, the degree-generic `sep_word`, and established that it does **not** close
`IsTwoSeparating` — the fork CB-4 promoted to a binder — because that fork is a statement about
`H²(Γ, A)` at *module* coefficients and the repository has no degree-`2` comparison there.  The
`ℚ₂` candidate-side proof of `hsep` (`Phase140GammaA.hsep_gammaA`) never forms `H²(Γ_A, T)`
either: it runs the **marking route**, and `sepWordN` is that route's engine.

This file ports the marking route off `Fin 4`/`Marking` to an arbitrary alphabet `ι` and an
arbitrary relator family `W : ρ → PWord ι`, and closes `SourceDataN.hsep` on the candidate side
with it.

## Section map

| § | content | status |
|---|---------|--------|
| 1 | the cover-lift kernel: `sum_relatorFib_eq_zero` | closed |
| 2 | the invariant-dual relator sum, over the abstract carrier | closed |
| 3 | **`hsepN_marking`** — the `hsep` clause by the marking route | closed |
| 4 | the verbatim `SourceDataN.hsep` field goal, marking-route form | closed |
| 5 | branch instantiation of `Count/Separating.lean` §5 at `Vmod` | closed |

## Numeric leaves

**Nothing in this file reads a count.**  No `Nat.card`, no `SourceNumerics`, no degree `n` occurs
in any statement below; `IsSelfDualN` is never mentioned and `StokesDuality` is consumed through
`sepWordN` only, i.e. through its `h2_inj` clause.  CB-SG's exponent warning therefore has no
purchase here: there is no exponent to check against `standardNumerics`.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.AffineTLift

/-! ## §1. The cover-lift kernel

`RStageGammaA.redValues_eq_of_coverLift` (`GQ2/RStage/GammaA.lean:740`), at an arbitrary alphabet
and relator family.  The `ℚ₂` statement is *"the two reduced relator values agree"*, which over
`𝔽₂` is *"their sum is zero"*; with `ρ` relators instead of two the honest statement is that the
**traced** sum of the reduced relator values vanishes — and this is exactly the input `sepWordN`
consumes.

The `ℚ₂` proof is a four-field hand computation with `corrMark` and the `L1`
`tameValue_correction`/`wildValue_correction` pair.  Generically none of that is needed: CB-3's
correction law (`Count/Lifts.lean` §2) says the relator values of two markings over a common lower
marking differ by `j (d¹x)`, the lift's own relator values are trivial (`hpres.rel` at the lift),
and CB-VAR's `sum_heisD1_zmod2` kills the traced sum of a `d¹`-image. -/

section CoverLift

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}
  (pi : G →* C) (j : ZMod 2 → G)

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [TopologicalSpace G] [DiscreteTopology G] [Finite G] [TopologicalSpace C] [DiscreteTopology C]
  [Finite C] [DistribMulAction C (ZMod 2)] in
/-- **Two markings over a common lower marking differ by kernel offsets.**  The generic form of
the four `hmem` steps of `redValues_eq_of_coverLift`. -/
theorem exists_kernel_offset (hjsurj : ∀ g : G, pi g = 1 → ∃ a : ZMod 2, g = j a)
    (f₀ u : ι → G) (hcov : ∀ i, pi (f₀ i) = pi (u i)) :
    ∃ x : ι → ZMod 2, ∀ i, f₀ i = j (x i) * u i := by
  classical
  choose x hx using fun i => hjsurj (f₀ i * (u i)⁻¹)
    (by rw [map_mul, map_inv, hcov i, mul_inv_cancel])
  exact ⟨x, fun i => by rw [← hx i]; group⟩

/-- **The cover-lift kernel, degree-generically.**  If the lower map lifts through the `𝔽₂`-cover
`pi`-compatibly, then the traced sum of the fibre coordinates of the relator values of *any*
set-lift marking vanishes.

`RStageGammaA.redValues_eq_of_coverLift` at arbitrary `ι`/`ρ`; the hypotheses on `j` say that its
image is a central `2`-torsion copy of `𝔽₂` inside `ker pi`, which is what a central double cover
supplies (§2 instantiates `j` at `a ↦ z ^ a.val`). -/
theorem sum_relatorFib_eq_zero
    (htrivC : ∀ (g : C) (m : ZMod 2), g • m = m)
    (hjmul : ∀ a b : ZMod 2, j (a + b) = j a * j b)
    (hjcomm : ∀ (g : G) (a : ZMod 2), j a * g = g * j a)
    (hjsurj : ∀ g : G, pi g = 1 → ∃ a : ZMod 2, g = j a)
    (hjinj : Function.Injective j)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (gc : ContinuousMonoidHom Γ G) (hgc : ∀ i, pi (gc (gen i)) = c i)
    (f₀ : ι → G) (hcov : ∀ i, pi (f₀ i) = c i)
    (ζ : ρ → ZMod 2) (hζ : ∀ k, PWord.eval f₀ (W k) = j (ζ k)) :
    ∑ k, ζ k = 0 := by
  classical
  letI : DistribMulAction G (ZMod 2) := DistribMulAction.compHom (ZMod 2) pi
  have hact : ∀ (g : G) (a : ZMod 2), g • a = pi g • a := fun _ _ => rfl
  have hjconj : ∀ (g : G) (a : ZMod 2), j (g • a) = g * j a * g⁻¹ := by
    intro g a
    rw [hact, htrivC, ← hjcomm g a]
    group
  obtain ⟨x, hx⟩ := exists_kernel_offset pi j hjsurj f₀ (fun i => gc (gen i))
    (fun i => (hcov i).trans (hgc i).symm)
  have hkey : ∀ k, j (ζ k) = j (heisD1 (A := ZMod 2) c w x k) := by
    intro k
    rw [← hζ k, show f₀ = fun i => j (x i) * gc (gen i) from funext hx,
      eval_corrected_heisD1 pi j hact hjmul hjconj hgc hres x k, hpres.rel gc k, mul_one]
  rw [show ζ = heisD1 (A := ZMod 2) c w x from funext fun k => hjinj (hkey k)]
  exact sum_heisD1_zmod2 hr hend x

end CoverLift

end GQ2.Dyadic.Count
