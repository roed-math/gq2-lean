/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.CanonicalRecords
import GQ2.Dyadic.Instances.AskCounting

/-!
# The analytic clauses at a tied row's candidate carrier  (dyadic campaign, lane W84-CLAUSES)

W83-RECORDS reduced each of the four tied quadratic rows to "the four analytic clauses at the
row's candidate carrier `Γ_R = GammaR n q_K word`, plus two `ASK` blocks at `G_K`".  This module
takes the cheapest row, `M0 2 0` at `ℚ₂(√5)`, and asks what those six things actually cost.

Nothing here is asserted that is not proved; every reduction names the residue it stops at.
-/

namespace GQ2.Dyadic.Instances.RowClauses

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances

/-! ## §1 The frozen (136) coefficient, at an arbitrary carrier

`Instances.AskCounting` measured the gap between the frozen and corrected R-stage coefficients
and drew the equivalence `ExactLiftingSemantics ↔ askCStageVanishing` **at `G_K` only**, because
its corrected input was `correctedRStageSemantics_galK`.  Nothing in that argument is arithmetic:
the two coefficients `zR = #R² · #D_R` and `zRN = #R^{n+1} · #D_R` are frame invariants, and both
of `askC_zRN_eq_zR_of_card_one` and `askC_zRN_ne_zR` are already carrier-free.

So the same equivalence holds at **any** carrier that has the corrected bundle, with the
corrected bundle as an explicit hypothesis in place of the `G_K` theorem.  That is what §1
proves.  `askCStageVanishing` is already stated at a free `Γ : ProfiniteGrp`, so no new `Prop`
is introduced here. -/

section Coefficient

variable {Γ : ProfiniteGrp} {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-- **The frozen bundle from the corrected one plus the vanishing, at any carrier.**  The
carrier-free form of `askC_exactLiftingSemantics_galK`: that proof used `G_K` only through
`correctedRStageSemantics_galK`, whose conclusion is the third conjunct of
`ExactLiftingSemanticsRN`, and the first two conjuncts of the two bundles are literally the
same. -/
theorem rowCl_exactLifting_of_stageVanishing
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n))
    (hvan : askCStageVanishing Γ q P nuP) :
    ExactLiftingSemantics Γ n q P nuP (standardNumerics n) := by
  refine ⟨hRN.1, hRN.2.1, ?_⟩
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F
  have hcorr := hRN.2.2 hE2 hRK hR2 b F
  rcases lt_or_ge 1 (Nat.card ↥Blk.frattiniK) with hR | hR
  · rw [hvan hE2 hRK hR2 b F hR, mul_zero] at hcorr ⊢
    exact hcorr
  · have h1 : Nat.card ↥Blk.frattiniK = 1 := le_antisymm hR Nat.card_pos
    rw [← askC_zRN_eq_zR_of_card_one (n := n) (blockFrameImpl T Blk hE2) h1]
    exact hcorr

/-- **The vanishing from the frozen bundle, at any carrier, at `2 ≤ n`.**  The carrier-free form
of `askC_stageVanishing_of_exactLifting`.  Both bundles evaluate the same left-hand side
`#D_R · e_Γ(B)`, so their right-hand sides agree; at `2 ≤ n` with `1 < #R` the coefficients are
distinct naturals and `ℤ` is a domain. -/
theorem rowCl_stageVanishing_of_exactLifting (hn : 2 ≤ n)
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n))
    (hfroz : ExactLiftingSemantics Γ n q P nuP (standardNumerics n)) :
    askCStageVanishing Γ q P nuP := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F hR
  have hfr := hfroz.2.2 hE2 hRK hR2 b F
  have hcorr := hRN.2.2 hE2 hRK hR2 b F
  have hcoeff : ((blockFrameImpl T Blk hE2).zR : ℤ)
      - (zRN (blockFrameImpl T Blk hE2) (standardNumerics n) : ℤ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun hc => askC_zRN_ne_zR (blockFrameImpl T Blk hE2) hn hR
      (Nat.cast_injective (R := ℤ) hc.symm)
  have hzero : (((blockFrameImpl T Blk hE2).zR : ℤ)
      - (zRN (blockFrameImpl T Blk hE2) (standardNumerics n) : ℤ))
      * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) = 0 := by
    rw [sub_mul, ← hfr, ← hcorr, sub_self]
  rcases mul_eq_zero.mp hzero with hc | hs
  · exact absurd hc hcoeff
  · exact hs

/-- **The equivalence at any carrier with the corrected bundle, at `2 ≤ n`.**  Wave 81's
`askC_exactLifting_iff_stageVanishing` with `G_K` replaced by an arbitrary `Γ` and its corrected
theorem replaced by a hypothesis. -/
theorem rowCl_exactLifting_iff_stageVanishing (hn : 2 ≤ n)
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n)) :
    ExactLiftingSemantics Γ n q P nuP (standardNumerics n)
      ↔ askCStageVanishing Γ q P nuP :=
  ⟨rowCl_stageVanishing_of_exactLifting hn hRN, rowCl_exactLifting_of_stageVanishing hRN⟩

end Coefficient

end GQ2.Dyadic.Instances.RowClauses
