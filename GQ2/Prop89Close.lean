import GQ2.KeystoneDelta
import GQ2.RStageLocal
import GQ2.Half139Local
import GQ2.HalfTorsorGammaA
import GQ2.FinitelyGenerated
import GQ2.PhaseLIndep
import GQ2.PhaseMuIndep
import GQ2.PhaseGaussLIndep
import GQ2.GaussZReduction
import GQ2.Phase140Assembly
import GQ2.RStageGammaA

/-!
# The P-16 capstone: `prop_8_9` at the concrete block frame  (P-16d6e)

**Proposition 8.9 (closed exact-image recursion)**, relocated here from `SectionEight.lean`
(which cannot name `blockFrameImpl` — it sits above `BlockFrameImpl.lean` in the import
order; `thm_4_2`-relocation pattern).  Two reviewed statement actions relative to the
original draft (`docs/p16d6e-assembly-plan.md` §1, the authoritative record):

* **Per-`λ` phase family** — the paper's (134) classes `Δ_{χ,κ}` carry the scalar-pushout
  class `κ = κ_λ` of the `λ`-cover, so the family is
  `phase : (l : DR) → l ≠ zeroDR → DT → CentralCover YC` (the shared-family draft form was
  a transcription deviation; it would force an unproven `zBC`-l-independence).
* **Concrete block frame + hypothesis ledger** — the statement is at
  `RF := blockFrameImpl T Blk hE2` (the only intended consumer: SectionNine's inductive
  branch at `blockFrame`/`blockEnrichment`, P-17c/P-17h; general-`RF` (136) is not provable
  — no axioms tie a bare frame's `DR`/`zR`/`mB` to obstruction theory).  Hypothesis-side
  (dischargers recorded in the plan doc §1): `hE2` (P-17a standing), `hfgF` (**B1**, first
  consumption reserved to P-17i), `hheadA`/`hheadF` (§9 boundary data), `hsimple`/`hfaith`/
  `hVne` (the block's chief-factor structure, P-17h), `hG0indep` (c3-G0's
  `gaussSum_qbar_l_indep_*` at the block's tame package, P-17h).
* Conclusion strengthened with `0 < Nat.card DT` (P-17i; free — `0 ∈ (T^∨)^C`).
-/

namespace GQ2

namespace SectionEight

open SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **Proposition 8.9 (closed exact-image recursion)**: for the concrete block frame of a
boundary-framed target with a §7 simple-head block, there are **shared** data
`(μ, G⁰, D_T)` and a **per-`λ`** phase family such that the boxed system (136)–(142) holds
for **both sources**.  Every count on the right sides concerns a target with strictly
smaller marked 2-kernel, so the system is a closed deterministic recursion (paper, end of
§8).  [P-16 statement — relocated & amended at P-16d6e, see the module docstring; proof =
the P-16d6e assembly, axioms ≤ {B6, B7, B9} per App. D.] -/
theorem prop_8_9 (B : BoundaryMaps) {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (En : (blockFrameImpl T Blk hE2).Enrichment) (F : BoundaryFrame H E)
    [CompactSpace GammaA] [TotallyDisconnectedSpace GammaA] [IsTopologicalGroup GammaA]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
    (hfgF : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hheadA : Function.Surjective (fun γ : GammaA => (F.frameMap (B.bA γ)).1))
    (hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1))
    [Nontrivial (blockFrameImpl T Blk hE2).YC]
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hfaith : ∀ g : (blockFrameImpl T Blk hE2).YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (G0 : ℤ)
    (hGaussZA : ∀ (l : (blockFrameImpl T Blk hE2).DR)
      (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR), GaussZResidue B.bA F En l h G0)
    (hGaussZF : ∀ (l : (blockFrameImpl T Blk hE2).DR)
      (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR), GaussZResidue B.bF F En l h G0) :
    ∃ (μ : ℕ) (G0' : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : (l : (blockFrameImpl T Blk hE2).DR) →
        l ≠ (blockFrameImpl T Blk hE2).zeroDR → DT →
          CentralCover (blockFrameImpl T Blk hE2).YC),
      0 < Nat.card DT ∧
        ClosedRecursion (blockFrameImpl T Blk hE2) B.bA F μ G0' DT phase ∧
          ClosedRecursion (blockFrameImpl T Blk hE2) B.bF F μ G0' DT phase := by
  sorry

end SectionEight

end GQ2
