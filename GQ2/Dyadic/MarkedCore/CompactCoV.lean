/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.Certificate
public import GQ2.Dyadic.MarkedCore.CoVDischarge

@[expose] public section

/-!
# MC-CoV — the compact-`M` change of variables, MC5-facing reductions (errata item 3)

**Ticket MC-CoV** of the dyadic campaign (lane MC), upper half after the MC-CoV-split.  The
derivation lives one level down in `MarkedCore/CoVDischarge.lean`, below the certificate layer;
this file is the part that has to sit *above* `Certificate.lean`, because it names that file's
`M`-side entry points.

## What the discharge says (proved in `CoVDischarge.lean`)

The compact row's `Ā`-value is forced by the abelianized relation `2Ā + 2^αC̄₀ = 0`, not by an
`r`-exponent (`nu_dmA_eq`); a rank-four marking is exactly its triple `(ν'(B̄), ν'(C̄₀), ν'(D̄))`
(`mNu_frame`); the pivot datum `IsUnit (ν'(C̄₀))` is a `St_M`-invariant, so no change of
variables can create it (`isUnit_nu_stab_iff`) — but at rank four it is **equivalent** to the
intrinsic, `f`-free clause `MChiKerUnimodular`, "`ν'` is unimodular somewhere on `ker χ_M`"
(`isUnit_nu_dmC_iff_chiKer`), which is literally the packet's own branch condition `r = 0`
selecting the compact row.  So on the compact branch the datum is a **theorem**.

## This file

Each theorem below is the `Certificate.lean` (resp. `M.lean`) statement with
`hpivot : IsUnit (ν'(C̄₀))` replaced by `MChiKerUnimodular`.  The replacement is an *equivalence*
at rank four, so no strength is lost, and it costs a frame `B : MDecomposition α`, which MC3
already consumes as a hypothesis throughout.  This trio **is** the compact-`M` consumer API.

⚠ The parent statements deliberately keep `hpivot` and stay uniform in `h`; the discharge is
rank-four (`h = 0`, `α ≥ 2`) only, so it cannot be folded into them — at `h = 1` the citation
is a type error and at `α = 1` the discharge is false.  The finding is recorded in
`Certificate.lean`'s module docstring.  Splitting the file made the discharge *citable* from
below (MC5-swap's build cycle is gone); it did not make the parents' datum removable.
-/

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

open Multiplicative

/-! ## §1 The MC5-facing reductions, with the binder replaced -/
section MC5

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **MC5's `nMarkedMatching`, with the compact-`N` pair datum replaced by the intrinsic
χ-kernel criterion.**  No scaling hypothesis occurs: the exact `SL₂(ℤ₂)` action normalizes the
primitive pair. -/
theorem nMarkedMatching_of_chiKer {α : ℕ} (hα : 2 ≤ α) (B : NDecomposition α)
    (nu' : ContinuousMonoidHom (DN α 0 : Type) (Multiplicative ℤ_[2]))
    (hker : NChiKerUnimodular α 0 nu') :
    ∃ u : ContinuousMulEquiv (DN α 0 : Type) (DN α 0 : Type),
      (∀ x, chiN α 0 (u x) = chiN α 0 x) ∧ ∀ x, nu' (u x) = nuN α 0 x :=
  nMarkedMatching α 0 nu' (nPairUnimodular_of_chiKer hα B nu' hker)

/-- **Compact rank-four `N` certificate production from the intrinsic χ-kernel arithmetic
fact.**  This is the preferred compact consumer API: neither `NScalingHypothesis` nor a
generator-named pair condition appears. -/
theorem marked_matching_certificate_N_of_chiKer {α : ℕ} (hα : 2 ≤ α)
    (B : NDecomposition α) (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DN α 0 : Type) G)
    (horient : ∀ x, chiG (f x) = chiN α 0 x)
    (hcont : Continuous fun x : (DN α 0 : Type) => nuG (f x))
    (hker : ∃ x : (DN α 0 : Type), chiN α 0 x = 1 ∧ IsUnit (toAdd (nuG (f x)))) :
    Nonempty (MarkedCoreCertificateN α 0 chiG nuG) := by
  set nu' : ContinuousMonoidHom (DN α 0 : Type) (Multiplicative ℤ_[2]) :=
    { toFun := fun x => nuG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hcont } with hnu'
  exact marked_matching_certificate_N α 0 chiG nuG f horient hcont
    (nPairUnimodular_of_chiKer hα B nu' hker)

/-- **MC5's `mMarkedMatching`, with the compact-`M` datum discharged.** -/
theorem mMarkedMatching_of_chiKer {α : ℕ} (hα : 2 ≤ α) (hα1 : 1 ≤ α) (B : MDecomposition α)
    (hMix : MMixHypothesis α 0 hα1)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (hker : MChiKerUnimodular α 0 nu') :
    ∃ u : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type),
      (∀ x, chiM α 0 (u x) = chiM α 0 x) ∧ ∀ x, nu' (u x) = nuM α 0 hα1 x :=
  mMarkedMatching hα1 hMix nu' (isUnit_nu_dmC_of_chiKer hα B nu' hker)

/-- **MC-M (correction form), with the compact-`M` datum discharged.** -/
theorem prop_MC_M_correction_of_chiKer {α : ℕ} (hα : 2 ≤ α) (hα1 : 1 ≤ α)
    (B : MDecomposition α) (hMix : MMixHypothesis α 0 hα1)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (hker : MChiKerUnimodular α 0 nu') :
    ∃ Ψ : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type),
      (∀ x, chiM α 0 (Ψ x) = chiM α 0 x)
        ∧ ∀ i, nu' (Ψ (dmGen α 0 i)) = nuM α 0 hα1 (dmGen α 0 i) :=
  prop_MC_M_correction hα1 hMix nu' (isUnit_nu_dmC_of_chiKer hα B nu' hker)

/-- **Certificate production, `M`-side, with the compact-`M` datum discharged.**  The pivot row
of `marked_matching_certificate_M` is now the compact-row condition on the transported marking,
which is what the packet's `(C, I, λ, γ)` data supplies directly. -/
theorem marked_matching_certificate_M_of_chiKer {α : ℕ} (hα : 2 ≤ α) (hα1 : 1 ≤ α)
    (B : MDecomposition α) (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DM α 0 : Type) G)
    (horient : ∀ x, chiG (f x) = chiM α 0 x)
    (hcont : Continuous fun x : (DM α 0 : Type) => nuG (f x))
    (hMix : MMixHypothesis α 0 hα1)
    (hker : ∃ x : (DM α 0 : Type), chiM α 0 x = 1 ∧ IsUnit (toAdd (nuG (f x)))) :
    Nonempty (MarkedCoreCertificateM α 0 hα1 chiG nuG) := by
  set nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]) :=
    { toFun := fun x => nuG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hcont } with hnu'
  exact marked_matching_certificate_M α 0 hα1 chiG nuG f horient hcont hMix
    (isUnit_nu_dmC_of_chiKer hα B nu' hker)

end MC5

end MarkedCore

end Dyadic

end GQ2
