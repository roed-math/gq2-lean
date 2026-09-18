/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformAnalyticCore
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcMobileSpliceSupply

/-!
# Complete analytic cores for the new even-M sources

Both changed source families now supply the full boundary-independent corrected analytic
record. Their complete normalized pro-2 cores were constructed separately. What is not
claimed here is the boundary-dependent affine determinant or any field identification.
-/

namespace GQ2.Dyadic.Instances.TameSpliceAnalyticSources
noncomputable section
open GQ2 GQ2.Dyadic Count MarkedCore
open SourceBoundaryReplacementRN EvenMHeadHandlePairSpliceSupply
open MpcMobileNuSource MpcMobileSpliceSupply

/-- The unit-handle pair splice has a complete analytic core at every positive handle rank.
The unit-handle equation is needed only to identify its normalized marked pro-2 core. -/
def headHandlePairSplice_analyticCore
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    SourceAnalyticCoreRN (2 + 2 * h) q (DM alpha h) (isProP_DM alpha h) nuP
      (standardNumerics (2 + 2 * h)) :=
  (uniformStokesSupply_headHandlePairSplice halpha hα hq0 hqe j nuP).analyticCore
    (headHandlePairSpliceW_specializes halpha hq0 hqe j nuP) _ _ nuP

@[simp] theorem headHandlePairSplice_analyticCore_Gamma
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    (headHandlePairSplice_analyticCore halpha hα hq0 hqe j nuP).Γ =
      GammaR (2 + 2 * h) q (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP) := rfl

/-- The actual-unit Mpc splice has a complete analytic core, including at handle rank zero.
The exact D-coordinate equation belongs to the normalized core theorem, not this analysis. -/
def mpcMobileSplice_analyticCore
    {alpha h q : ℕ} (r p : ℕ) (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) (eta : ℤ_[2]ˣ)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    SourceAnalyticCoreRN (2 + 2 * h) q (DM alpha h) (isProP_DM alpha h) nuP
      (standardNumerics (2 + 2 * h)) :=
  (mpcMobileTameSplice_uniformStokesSupply (r := r) (p := p)
    hq0 hqe eta halpha hα nuP).analyticCore
    (tameSpecializes_tameSplice (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
      (Count.tameSpecializes_mCompact hq0 hqe alpha h)) _ _ nuP

@[simp] theorem mpcMobileSplice_analyticCore_Gamma
    {alpha h q : ℕ} (r p : ℕ) (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) (eta : ℤ_[2]ˣ)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    (mpcMobileSplice_analyticCore r p halpha hα hq0 hqe eta nuP).Γ =
      GammaR (2 + 2 * h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (Words.MCompact.mCompactW alpha h)) := rfl

#print axioms headHandlePairSplice_analyticCore
#print axioms mpcMobileSplice_analyticCore

end
end GQ2.Dyadic.Instances.TameSpliceAnalyticSources
