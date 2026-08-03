/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.ProPAbelianization
import GQ2.Dyadic.MarkedRecipBundle

/-!
# Completed pro-2 reciprocity for a dyadic field

This file extracts the completion-theoretic content that is honestly available from
`MarkedRecip`: the dense reciprocity map induces a continuous **surjection**

`(Kˣ)^(2) →ₜ* (G_K(2))^ab`.

The source is `proPCompletion 2 ((↥K)ˣ)`, defined as the maximal pro-2 quotient of the
profinite completion.  No injectivity statement is made: density of reciprocity alone cannot
identify its completed kernel.  That arithmetic kernel calculation, followed by the torsion
calculation, remains the missing input to `demushkinQ = 2`.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The `MarkedRecip` reciprocity map, bundled with its continuity proof. -/
def MarkedRecip.continuousRecip (B : MarkedRecip R K) :
    ContinuousMonoidHom ((↥K)ˣ) (GalKab K) :=
  ⟨B.recip, B.continuous_recip⟩

/-- The purely group-theoretic identification `(G_K^ab)(2) ≃ (G_K(2))^ab`.

The inferred source type carries the deliberately local quotient instances from
`GQ2.ProPAbelianization`; keeping those instances out of the global instance graph avoids the
topological-quotient conflicts documented in `SectionThree.lean`. -/
def maxProTwoGalKabEquivTopAbMaxProTwoGalK :=
  maxProPTopAbEquiv (p := 2) (GalK K)

/-- Completed pro-2 local reciprocity, from the pro-2 completion of `Kˣ` to the topological
abelianization of `G_K(2)`. -/
def proTwoReciprocityToTopAb (B : MarkedRecip R K) :
    ContinuousMonoidHom (proPCompletion 2 ((↥K)ˣ))
      (topAbelianization (maxProPQuotient 2 (GalK K))) :=
  proPCompletionToTopAbMaxProP (p := 2) (GalK K) B.continuousRecip

@[simp] theorem proTwoReciprocityToTopAb_mk (B : MarkedRecip R K) (x : (↥K)ˣ) :
    proTwoReciprocityToTopAb B (proPCompletionMk 2 ((↥K)ˣ) x) =
      topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip x) :=
  proPCompletionToTopAbMaxProP_mk (p := 2) (GalK K) B.continuousRecip x

/-- **Completed pro-2 reciprocity is surjective.**  This is the strongest completion-level
conclusion supplied by the present `MarkedRecip` interface: compactness makes the range of the
extended map closed, while the original reciprocity image is dense. -/
theorem proTwoReciprocityToTopAb_surjective (B : MarkedRecip R K) :
    Function.Surjective (proTwoReciprocityToTopAb B) :=
  proPCompletionToTopAbMaxProP_surjective_of_denseRange (p := 2) (GalK K)
    B.continuousRecip B.denseRange_recip

end

end GQ2.Dyadic
