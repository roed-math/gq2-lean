/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.CoreMix
public import GQ2.Dyadic.MarkedCore.N

@[expose] public section

/-!
# The widened clearing monoid `A⁺(P,h)`, and the `N`-side core-mixing discharge

**Ticket HM6f** of the dyadic campaign (lane MC), implementing
`docs/dyadic/handlemix-core-spike.md` §6.2's second row.  HM6 (`CoreMix.lean`) proved that the
rank-four **core↔core** mixing automorphisms exist — MC1 §3.4's families `N5`, `N6` on `D_N` and
MC1 §2.4's family `M5` on `D_M`, at every 2-adic parameter, with no new axiom.  This file is the
one step between those automorphisms and the binders that consume them.

## Why the landed predicate cannot be reused, and why widening in place is wrong

HM4's `DmRealizes`/`DnRealizes` (`HandleMixClear.lean:854,861`) bundle two clauses: "acts as `F`
on the ν-frame" **and** "lies in `Submonoid.closure (d?ClearAuts α h)`".  The second clause names
the **handle** generating set `A(P,h)`, which was the right packaging for HM4/HM5 — whose whole
point was that the ν-clearing correction never leaves `A(P,h)` — and is too narrow for the core
stratum, where the realizing automorphism is by construction a *new* generator.

MC4 then made the failure sharp.  `dnClearAuts_fixes_core` (`N.lean:1199`) proves that **no**
generator of `A(P,h)` touches a marked slot of index `< 3`, so every element of `A(P,h)` fixes
`x₀`, `x₁` and `σ` on the nose; and `nCoreMixHypothesis_not_of_mix` (`N.lean:1234`) turns that
into a refutation: for every `p ≠ 0`,

`¬ NCoreMixHypothesis α h S3`  whenever  `frameEnd (nFrameMixX1 p) ∈ S3` .

So HM4's schematic S3 binder is **unsatisfiable**, not merely unproved, for any genuinely mixing
stratum.  Two consequences fix this file's shape.

1. The repair is a **wider generating set**, `A⁺(P,h)`, not a different proof.
2. The widening must be **additive**.  Editing `dmClearAuts`/`dnClearAuts` in place would keep
   `dnClearAuts_fixes_core`'s *statement* while making it **false** — HM6's `dnCoreMixPEquiv`
   moves slot `1` — and MC4's refutation, HM5's `chiN_of_mem_dnClearAuts` and HM4's
   `exists_dnClear_nu` all read that set.  Everything below is therefore new: new sets, new
   predicates, and transport lemmas carrying the landed results across.  `HandleMixClear.lean`
   is untouched.

## What `A⁺(P,h)` is

`A(P,h)` plus the core families that HM6 proved exist:

| core | added generators |
|---|---|
| `D_M` | `dmCoreMixEquiv α h k` (M5), every `k : ℤ_[2]` |
| `D_N` | `dnCoreMixPEquiv α h k` (N5), `dnCoreMixQEquiv α h k` (N6), `dnTauCEquiv α h k` (N3) |

The `N`-side list carries one extra family, MC1 §3.4's **exact** transvection `N3`
(`σ ↦ x₂^k·σ`, MC4's `dnTauCEquiv`, axiom-free): the raw `N6` twist shears the `σ̄`-row along
with the `x̄₁`-row, and `N3` is what cancels the shear to leave MC1's *pure* family (memo §3.2).
Its `M`-side analogue does not exist and is not wanted — `τ_d` moves the letter carrying
`c^{2^α}` (memo §2.3, §3.2).

## Contents

* **§1** `dmClearAutsWide`/`dnClearAutsWide`, the subset and membership lemmas;
* **§2** `DmRealizesWide`/`DnRealizesWide`, the transport `DmRealizes.wide`, and the monoid laws;
* **§3** the generator rows over `A⁺(P,h)` — four handle rows transported, three core rows new;
* **§4** `D?RealizesAllWide`, the widened hypothesis names, and the transported HM4/HM5 payoffs
  (`exists_d?Clear_nu_wide`, `chi?_of_mem_d?ClearAutsWide`), plus the residual rigidity
  `dnClearAutsWide_fixes_x0`;
* **§5** **the payoff**: MC1's pure `N5`/`N6`, the widened S3 binder as a THEOREM, and MC4's
  `NMixPairHypothesis`/`NMixHypothesis` discharged;
* **§6** what stays binder-shaped on the `M` side.
-/

open Multiplicative

namespace GQ2

namespace Dyadic

namespace MarkedCore

open scoped GQ2

/-! ## §1 The widened generating sets -/

section WideGens

variable (α h : ℕ)

/-- **`A⁺(P,h)` on `D_M`**: HM4's `dmClearAuts` together with MC1 §2.4's family `M5` at every
2-adic parameter (HM6's `dmCoreMixEquiv`).  Additive by construction — `dmClearAuts` is a
subset, never rewritten. -/
noncomputable def dmClearAutsWide (α h : ℕ) : Set (Function.End (DM α h : Type)) :=
  dmClearAuts α h ∪ Set.range fun k : ℤ_[2] => autEnd (dmCoreMixEquiv α h k)

/-- **`A⁺(P,h)` on `D_N`**: HM4's `dnClearAuts`, MC1 §3.4's core-mixing families `N5` and `N6`
(HM6's `dnCoreMixPEquiv`, `dnCoreMixQEquiv`), and MC1 §3.4's exact transvection `N3` (MC4's
`dnTauCEquiv`), which §5 needs to cancel `N6`'s `σ̄`-shear. -/
noncomputable def dnClearAutsWide (α h : ℕ) : Set (Function.End (DN α h : Type)) :=
  dnClearAuts α h ∪ (Set.range fun k : ℤ_[2] => autEnd (dnCoreMixPEquiv α h k))
    ∪ (Set.range fun k : ℤ_[2] => autEnd (dnCoreMixQEquiv α h k))
    ∪ Set.range fun k : ℤ_[2] => autEnd (dnTauCEquiv α h k)

theorem dmClearAuts_subset_wide : dmClearAuts α h ⊆ dmClearAutsWide α h := Set.subset_union_left

theorem dnClearAuts_subset_wide : dnClearAuts α h ⊆ dnClearAutsWide α h :=
  Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_left)

theorem dmClearAuts_closure_le_wide :
    Submonoid.closure (dmClearAuts α h) ≤ Submonoid.closure (dmClearAutsWide α h) :=
  Submonoid.closure_mono (dmClearAuts_subset_wide α h)

theorem dnClearAuts_closure_le_wide :
    Submonoid.closure (dnClearAuts α h) ≤ Submonoid.closure (dnClearAutsWide α h) :=
  Submonoid.closure_mono (dnClearAuts_subset_wide α h)

theorem dmCoreMixEquiv_mem_wide (k : ℤ_[2]) :
    autEnd (dmCoreMixEquiv α h k) ∈ dmClearAutsWide α h := Set.mem_union_right _ ⟨k, rfl⟩

theorem dnCoreMixPEquiv_mem_wide (k : ℤ_[2]) :
    autEnd (dnCoreMixPEquiv α h k) ∈ dnClearAutsWide α h :=
  Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨k, rfl⟩))

theorem dnCoreMixQEquiv_mem_wide (k : ℤ_[2]) :
    autEnd (dnCoreMixQEquiv α h k) ∈ dnClearAutsWide α h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨k, rfl⟩)

theorem dnTauCEquiv_mem_wide (k : ℤ_[2]) :
    autEnd (dnTauCEquiv α h k) ∈ dnClearAutsWide α h := Set.mem_union_right _ ⟨k, rfl⟩

end WideGens

/-! ## §2 The widened realization predicates

Literally HM4's `DmRealizes`/`DnRealizes` with `d?ClearAuts` replaced by `d?ClearAutsWide`.  The
ν-frame clause is unchanged, which is what makes `DmRealizes.wide` a one-liner and what lets
every landed row cross over. -/

section WideRealizes

variable (α h : ℕ)

/-- **`Ψ` realizes the frame move `F` inside `A⁺(P,h)` on `D_M`** — HM4's `DmRealizes` over the
widened generating set. -/
def DmRealizesWide (α h : ℕ) (Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type))
    (F : Function.End (Fin (coreRank h) → ℤ_[2])) : Prop :=
  autEnd Ψ ∈ Submonoid.closure (dmClearAutsWide α h)
    ∧ ∀ f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Ψ (dmGen α h i)) = F (nuFrame f (dmGen α h))

/-- The `N`-mirror of `DmRealizesWide`. -/
def DnRealizesWide (α h : ℕ) (Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type))
    (F : Function.End (Fin (coreRank h) → ℤ_[2])) : Prop :=
  autEnd Ψ ∈ Submonoid.closure (dnClearAutsWide α h)
    ∧ ∀ f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Ψ (dnGen α h i)) = F (nuFrame f (dnGen α h))

/-- **The transport lemma**: everything HM4 realized inside `A(P,h)` is realized inside
`A⁺(P,h)`.  This is why the widening costs nothing — every landed row, and every consequence
drawn from one, crosses over by `Submonoid.closure_mono`. -/
theorem DmRealizes.wide {Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type)}
    {F : Function.End (Fin (coreRank h) → ℤ_[2])} (hΨ : DmRealizes α h Ψ F) :
    DmRealizesWide α h Ψ F :=
  ⟨dmClearAuts_closure_le_wide α h hΨ.1, hΨ.2⟩

/-- The `N`-mirror of `DmRealizes.wide`. -/
theorem DnRealizes.wide {Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type)}
    {F : Function.End (Fin (coreRank h) → ℤ_[2])} (hΨ : DnRealizes α h Ψ F) :
    DnRealizesWide α h Ψ F :=
  ⟨dnClearAuts_closure_le_wide α h hΨ.1, hΨ.2⟩

theorem dmRealizesWide_refl : DmRealizesWide α h (ContinuousMulEquiv.refl _) 1 :=
  ⟨by rw [autEnd_refl]; exact one_mem _, fun _ => rfl⟩

theorem dnRealizesWide_refl : DnRealizesWide α h (ContinuousMulEquiv.refl _) 1 :=
  ⟨by rw [autEnd_refl]; exact one_mem _, fun _ => rfl⟩

/-- Realized moves compose: `Ψ₁.trans Ψ₂` realizes `F₁ * F₂` (substitutions compose
innermost-first — HM3's recorded convention, and `exists_dmRealizes`'s `mul` case verbatim). -/
theorem DmRealizesWide.trans {Ψ₁ Ψ₂ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type)}
    {F₁ F₂ : Function.End (Fin (coreRank h) → ℤ_[2])} (h₁ : DmRealizesWide α h Ψ₁ F₁)
    (h₂ : DmRealizesWide α h Ψ₂ F₂) : DmRealizesWide α h (Ψ₁.trans Ψ₂) (F₁ * F₂) := by
  refine ⟨by rw [autEnd_trans]; exact mul_mem h₂.1 h₁.1, fun f => ?_⟩
  have hstep : nuFrame f (fun i => (Ψ₁.trans Ψ₂) (dmGen α h i))
      = nuFrame (f.comp (autHom Ψ₂)) (fun i => Ψ₁ (dmGen α h i)) := rfl
  have hbase : nuFrame (f.comp (autHom Ψ₂)) (dmGen α h)
      = nuFrame f (fun i => Ψ₂ (dmGen α h i)) := rfl
  rw [hstep, h₁.2, hbase, h₂.2]
  rfl

/-- The `N`-mirror of `DmRealizesWide.trans`. -/
theorem DnRealizesWide.trans {Ψ₁ Ψ₂ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type)}
    {F₁ F₂ : Function.End (Fin (coreRank h) → ℤ_[2])} (h₁ : DnRealizesWide α h Ψ₁ F₁)
    (h₂ : DnRealizesWide α h Ψ₂ F₂) : DnRealizesWide α h (Ψ₁.trans Ψ₂) (F₁ * F₂) := by
  refine ⟨by rw [autEnd_trans]; exact mul_mem h₂.1 h₁.1, fun f => ?_⟩
  have hstep : nuFrame f (fun i => (Ψ₁.trans Ψ₂) (dnGen α h i))
      = nuFrame (f.comp (autHom Ψ₂)) (fun i => Ψ₁ (dnGen α h i)) := rfl
  have hbase : nuFrame (f.comp (autHom Ψ₂)) (dnGen α h)
      = nuFrame f (fun i => Ψ₂ (dnGen α h i)) := rfl
  rw [hstep, h₁.2, hbase, h₂.2]
  rfl

end WideRealizes

/-! ## §3 The generator rows over `A⁺(P,h)`

Four handle rows per core, transported from HM4 by `.wide`, and the three core rows, whose frame
side is HM6e (`nuFrame_d?CoreMix*Equiv`) and whose membership side is §1. -/

section WideRows

variable (α h : ℕ)

theorem dmRealizesWide_tauU (j : Fin h) (k : ℤ_[2]) :
    DmRealizesWide α h (dmTauUEquiv α h j k) (frameEnd (frameTauU j k)) :=
  (dmRealizes_tauU α h j k).wide α h

theorem dmRealizesWide_tauV (j : Fin h) (k : ℤ_[2]) :
    DmRealizesWide α h (dmTauVEquiv α h j k) (frameEnd (frameTauV j k)) :=
  (dmRealizes_tauV α h j k).wide α h

theorem dmRealizesWide_tauD (k : ℤ_[2]) :
    DmRealizesWide α h (dmTauDEquiv α h k) (frameEnd (frameTauD k)) :=
  (dmRealizes_tauD α h k).wide α h

theorem dmRealizesWide_mix (j : Fin h) :
    DmRealizesWide α h (dmMixEquiv α h j) (frameEnd (frameMixAdd j)) :=
  (dmRealizes_mix α h j).wide α h

theorem dnRealizesWide_tauU (j : Fin h) (k : ℤ_[2]) :
    DnRealizesWide α h (dnTauUEquiv α h j k) (frameEnd (frameTauU j k)) :=
  (dnRealizes_tauU α h j k).wide α h

theorem dnRealizesWide_tauV (j : Fin h) (k : ℤ_[2]) :
    DnRealizesWide α h (dnTauVEquiv α h j k) (frameEnd (frameTauV j k)) :=
  (dnRealizes_tauV α h j k).wide α h

theorem dnRealizesWide_tauD (k : ℤ_[2]) :
    DnRealizesWide α h (dnTauDEquiv α h k) (frameEnd (frameTauD k)) :=
  (dnRealizes_tauD α h k).wide α h

theorem dnRealizesWide_mix (j : Fin h) :
    DnRealizesWide α h (dnMixEquiv α h j) (frameEnd (frameMixAdd j)) :=
  (dnRealizes_mix α h j).wide α h

/-- **The `M5` row** — the statement HM4's binder could not hold: MC1 §2.4's core-mixing family,
realized by an automorphism *of the widened monoid*. -/
theorem dmRealizesWide_coreMix (k : ℤ_[2]) :
    DmRealizesWide α h (dmCoreMixEquiv α h k) (frameEnd (hm6FrameBD k)) :=
  ⟨Submonoid.subset_closure (dmCoreMixEquiv_mem_wide α h k), nuFrame_dmCoreMixEquiv α h k⟩

/-- **The `N5` row.** -/
theorem dnRealizesWide_coreMixP (k : ℤ_[2]) :
    DnRealizesWide α h (dnCoreMixPEquiv α h k) (frameEnd (hm6FrameBD k)) :=
  ⟨Submonoid.subset_closure (dnCoreMixPEquiv_mem_wide α h k), nuFrame_dnCoreMixPEquiv α h k⟩

/-- **The `N6` row.** -/
theorem dnRealizesWide_coreMixQ (k : ℤ_[2]) :
    DnRealizesWide α h (dnCoreMixQEquiv α h k) (frameEnd (hm6FrameBC k)) :=
  ⟨Submonoid.subset_closure (dnCoreMixQEquiv_mem_wide α h k), nuFrame_dnCoreMixQEquiv α h k⟩

/-- **The `N3` row** — MC4's exact transvection `σ ↦ x₂^k·σ`, entered into `A⁺(P,h)` because §5's
pure `N6` needs it (memo §3.2).  Its frame side is MC4's `nuFrame_nTauCMark`. -/
theorem dnRealizesWide_tauC (k : ℤ_[2]) :
    DnRealizesWide α h (dnTauCEquiv α h k) (frameEnd (nCoreMat (planeElemU k))) := by
  refine ⟨Submonoid.subset_closure (dnTauCEquiv_mem_wide α h k), fun f => ?_⟩
  rw [show (fun i => dnTauCEquiv α h k (dnGen α h i))
      = nTauCMark (isProP_DN α h) k (dnGen α h) from funext (dnTauCEquiv_gen α h k)]
  exact nuFrame_nTauCMark (isProP_DN α h) f (dnGen α h) k

end WideRows

/-! ## §4 The widened strata, and what the landed payoffs become -/

section WideStrata

variable (α h : ℕ)

/-- HM4's `DmRealizesAll` over `A⁺(P,h)`. -/
def DmRealizesAllWide (α h : ℕ) (S : Set (Function.End (Fin (coreRank h) → ℤ_[2]))) : Prop :=
  ∀ F ∈ S, ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type), DmRealizesWide α h Ψ F

/-- The `N`-mirror of `DmRealizesAllWide`. -/
def DnRealizesAllWide (α h : ℕ) (S : Set (Function.End (Fin (coreRank h) → ℤ_[2]))) : Prop :=
  ∀ F ∈ S, ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type), DnRealizesWide α h Ψ F

theorem DmRealizesAll.wide {S : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (hS : DmRealizesAll α h S) : DmRealizesAllWide α h S :=
  fun F hF => (hS F hF).imp fun _ hΨ => hΨ.wide α h

theorem DnRealizesAll.wide {S : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (hS : DnRealizesAll α h S) : DnRealizesAllWide α h S :=
  fun F hF => (hS F hF).imp fun _ hΨ => hΨ.wide α h

/-- **HM4's S3 binder, over `A⁺(P,h)`** — the repaired form of `MCoreMixHypothesis`.  A `def`,
**never an axiom**, exactly like the binder it replaces. -/
def MCoreMixHypothesisWide (α h : ℕ) (S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))) :
    Prop := DmRealizesAllWide α h S3

/-- **The `N`-mirror — and, unlike `NCoreMixHypothesis`, satisfiable**: §5 proves it for the
whole `N5`/`N6` stratum.  `nCoreMixHypothesis_not_of_mix` refutes the narrow form for the very
same stratum set, so the pair `nCoreMixHypothesisWide_mixX1` / `nCoreMixHypothesis_not_of_mix`
is the exact statement of what the widening buys. -/
def NCoreMixHypothesisWide (α h : ℕ) (S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))) :
    Prop := DnRealizesAllWide α h S3

/-- **The handle stratum stays a theorem over `A⁺(P,h)`** — HM4's `mLiftSplit_handle`,
transported. -/
theorem mLiftSplit_handle_wide :
    DmRealizesAllWide α h (Submonoid.closure (frameClearGens h) : Set _) :=
  (mLiftSplit_handle α h).wide α h

/-- The `N`-mirror of `mLiftSplit_handle_wide`. -/
theorem nLiftSplit_handle_wide :
    DnRealizesAllWide α h (Submonoid.closure (frameClearGens h) : Set _) :=
  (nLiftSplit_handle α h).wide α h

/-! ### HM4's ν-clearing payoff, over the widened monoid -/

/-- **HM4's restated obligation survives the widening** (`exists_dmClear_nu`, with `A⁺(P,h)` in
place of `A(P,h)`): the correction that clears the handle plane is still available, and is still
a *composite of explicit generators* — now of a larger explicit list. -/
theorem exists_dmClear_nu_wide (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dmClearAutsWide α h)
        ∧ (∀ j : Fin h, nu' (Ψ (dmGen α h (handleIdxU j))) = 1)
        ∧ (∀ j : Fin h, nu' (Ψ (dmGen α h (handleIdxV j))) = 1)
        ∧ nu' (Ψ (dmC α h)) = nu' (dmC α h) := by
  obtain ⟨Ψ, hmem, hU, hV, h2⟩ := exists_dmClear_nu α h nu' hc
  exact ⟨Ψ, dmClearAuts_closure_le_wide α h hmem, hU, hV, h2⟩

/-- The `N`-mirror of `exists_dmClear_nu_wide`. -/
theorem exists_dnClear_nu_wide (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dnSigma α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      autEnd Ψ ∈ Submonoid.closure (dnClearAutsWide α h)
        ∧ (∀ j : Fin h, nu' (Ψ (dnGen α h (handleIdxU j))) = 1)
        ∧ (∀ j : Fin h, nu' (Ψ (dnGen α h (handleIdxV j))) = 1)
        ∧ nu' (Ψ (dnSigma α h)) = nu' (dnSigma α h) := by
  obtain ⟨Ψ, hmem, hU, hV, h2⟩ := exists_dnClear_nu α h nu' hc
  exact ⟨Ψ, dnClearAuts_closure_le_wide α h hmem, hU, hV, h2⟩

end WideStrata

/-! ### The χ-side survives the widening (HM5's headline)

HM5's `chi?_of_mem_d?ClearAuts` says every element of `A(P,h)` preserves the canonical
orientation.  The three new families do too, for one reason: both twisting curves are
χ-trivial — `χ(γ) = χ(a)·χ(c)` and `χ(δ) = χ(a)·χ(d)⁻¹` by `map_hm6Mix*_comm`, and on both cores
the relevant values are `1` (memo §3.3's character check). -/

section WideChar

variable (α h : ℕ)

/-- `χ_M` kills the `M5` twisting curve: `χ_M(A) = χ_M(C₀) = 1`. -/
theorem chiM_hm6CurveM :
    chiM α h (hm6CurveM α (dmGen α h 0) (dmGen α h 1) (dmGen α h 2) (dmGen α h 3)) = 1 := by
  rw [hm6CurveM, map_hm6MixBD_comm]
  rw [show dmGen α h 0 = dmA α h from rfl, show dmGen α h 2 = dmC α h from rfl, chiM_dmA,
    chiM_dmC, one_mul]

/-- `χ_N` kills the `N5` twisting curve: `χ_N(x₀) = χ_N(σ) = 1`. -/
theorem chiN_hm6CurveNp :
    chiN α h (hm6CurveNp (dnGen α h 0) (dnGen α h 1) (dnGen α h 2) (dnGen α h 3)) = 1 := by
  rw [hm6CurveNp, map_hm6MixBD_comm]
  rw [show dnGen α h 0 = dnX0 α h from rfl, show dnGen α h 2 = dnSigma α h from rfl, chiN_dnX0,
    chiN_dnSigma, one_mul]

/-- `χ_N` kills the `N6` twisting curve: `χ_N(x₀) = χ_N(x₂) = 1`. -/
theorem chiN_hm6CurveNq :
    chiN α h (hm6CurveNq (dnGen α h 0) (dnGen α h 1) (dnGen α h 2) (dnGen α h 3)) = 1 := by
  rw [hm6CurveNq, map_hm6MixBC_comm]
  rw [show dnGen α h 0 = dnX0 α h from rfl, show dnGen α h 3 = dnX2 α h from rfl, chiN_dnX0,
    chiN_dnX2, inv_one, one_mul]

/-- **`M5` preserves the canonical orientation of the `M_α` core** (memo §3.3:
`χ(φ(B)) = χ(B)χ(C₀) = −1` and `χ(φ(D)) = χ(D)χ(A) = u`). -/
theorem chiM_dmCoreMixEquiv (k : ℤ_[2]) (x : (DM α h : Type)) :
    chiM α h (dmCoreMixEquiv α h k x) = chiM α h x := by
  refine dm_char_fixed (chiM α h) _ (fun i => ?_) x
  have hcurve : chiM α h (zpowZtwo (isProP_DM α h)
      (hm6CurveM α (dmGen α h 0) (dmGen α h 1) (dmGen α h 2) (dmGen α h 3)) k) = 1 := by
    rw [map_zpowZtwo (isProP_DM α h) isProP_two_unitsPadicInt (chiM α h), chiM_hm6CurveM α h,
      zpowZtwo_one_base]
  rw [dmCoreMixEquiv_gen, hm6MarkM]
  by_cases h1 : i = 1
  · subst h1; rw [hm6UpdateBD_one, map_mul, hcurve, mul_one]
  by_cases h3 : i = 3
  · subst h3; rw [hm6UpdateBD_three, map_mul, map_conjP_comm, hcurve, mul_one]
  rw [hm6UpdateBD_of_ne _ _ _ h1 h3]

/-- **`N5` preserves the canonical orientation of the `N_α` core.** -/
theorem chiN_dnCoreMixPEquiv (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnCoreMixPEquiv α h k x) = chiN α h x := by
  refine dn_char_fixed (chiN α h) _ (fun i => ?_) x
  have hcurve : chiN α h (zpowZtwo (isProP_DN α h)
      (hm6CurveNp (dnGen α h 0) (dnGen α h 1) (dnGen α h 2) (dnGen α h 3)) k) = 1 := by
    rw [map_zpowZtwo (isProP_DN α h) isProP_two_unitsPadicInt (chiN α h), chiN_hm6CurveNp α h,
      zpowZtwo_one_base]
  rw [dnCoreMixPEquiv_gen, hm6MarkNp]
  by_cases h1 : i = 1
  · subst h1; rw [hm6UpdateBD_one, map_mul, hcurve, mul_one]
  by_cases h3 : i = 3
  · subst h3; rw [hm6UpdateBD_three, map_mul, map_conjP_comm, hcurve, mul_one]
  rw [hm6UpdateBD_of_ne _ _ _ h1 h3]

/-- **`N6` preserves the canonical orientation of the `N_α` core.** -/
theorem chiN_dnCoreMixQEquiv (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnCoreMixQEquiv α h k x) = chiN α h x := by
  refine dn_char_fixed (chiN α h) _ (fun i => ?_) x
  have hcurve : chiN α h (zpowZtwo (isProP_DN α h)
      (hm6CurveNq (dnGen α h 0) (dnGen α h 1) (dnGen α h 2) (dnGen α h 3)) k) = 1 := by
    rw [map_zpowZtwo (isProP_DN α h) isProP_two_unitsPadicInt (chiN α h), chiN_hm6CurveNq α h,
      zpowZtwo_one_base]
  rw [dnCoreMixQEquiv_gen, hm6MarkNq]
  by_cases h1 : i = 1
  · subst h1; rw [hm6UpdateBC_one, map_mul, hcurve, mul_one]
  by_cases h2 : i = 2
  · subst h2; rw [hm6UpdateBC_two, map_mul, hcurve, mul_one]
  rw [hm6UpdateBC_of_ne _ _ _ h1 h2]

/-- **The whole widened monoid is invisible to `χ_M`** — HM5's `dmClearAuts_closure_le` with the
`M5` generator added. -/
theorem dmClearAutsWide_closure_le_chiM :
    Submonoid.closure (dmClearAutsWide α h) ≤ endStabilizer (chiM α h) := by
  refine closure_le_endStabilizer _ ?_
  intro E hE
  rcases hE with hE | ⟨k, rfl⟩
  · exact dmClearAuts_closure_le α h isProP_two_unitsPadicInt (chiM α h)
      (isClearBlind_chiM α h) (Submonoid.subset_closure hE)
  · exact chiM_dmCoreMixEquiv α h k

/-- The `N`-mirror of `dmClearAutsWide_closure_le_chiM`. -/
theorem dnClearAutsWide_closure_le_chiN :
    Submonoid.closure (dnClearAutsWide α h) ≤ endStabilizer (chiN α h) := by
  refine closure_le_endStabilizer _ ?_
  intro E hE
  rcases hE with ((hE | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨k, rfl⟩
  · exact dnClearAuts_closure_le α h isProP_two_unitsPadicInt (chiN α h)
      (isClearBlind_chiN α h) (Submonoid.subset_closure hE)
  · exact chiN_dnCoreMixPEquiv α h k
  · exact chiN_dnCoreMixQEquiv α h k
  · exact chiN_dnTauCEquiv α h k

/-- **`χ_M ∘ Ψ = χ_M` for every `Ψ ∈ A⁺(P,h)`** — HM5's headline over the widened monoid. -/
theorem chiM_of_mem_dmClearAutsWide {F : Function.End (DM α h : Type)}
    (hF : F ∈ Submonoid.closure (dmClearAutsWide α h)) (x : (DM α h : Type)) :
    chiM α h (F x) = chiM α h x := dmClearAutsWide_closure_le_chiM α h hF x

/-- **`χ_N ∘ Ψ = χ_N` for every `Ψ ∈ A⁺(P,h)`.** -/
theorem chiN_of_mem_dnClearAutsWide {F : Function.End (DN α h : Type)}
    (hF : F ∈ Submonoid.closure (dnClearAutsWide α h)) (x : (DN α h : Type)) :
    chiN α h (F x) = chiN α h x := dnClearAutsWide_closure_le_chiN α h hF x

/-! ### The residual rigidity

MC4's `dnClearAuts_fixes_core` pins three slots; after the widening exactly **one** survives, and
it is the one every family leaves alone.  So `A⁺(P,h)` is wider by exactly what the core stratum
needs and not by more: a frame move touching the `x̄₀`-row would still be unrealizable. -/

/-- **Every automorphism in `A⁺(P,h)` still fixes `x₀`.**  The two handle transvections move a
handle letter, `τ_c` and `N3` move `x₂` resp. `σ`, `Φ_j` moves a handle letter and `x₂`, and the
two core-mixing families move `x₁` together with `x₂` resp. `σ` — nothing reaches slot `0`. -/
theorem dnClearAutsWide_fixes_x0 {F : Function.End (DN α h : Type)}
    (hF : F ∈ Submonoid.closure (dnClearAutsWide α h)) : F (dnX0 α h) = dnX0 α h := by
  have hne1 : (0 : Fin (coreRank h)) ≠ 1 := nCoreZero_ne_one
  have hne2 : (0 : Fin (coreRank h)) ≠ 2 := nCoreZero_ne_two
  have hne3 : (0 : Fin (coreRank h)) ≠ 3 := coreVal_lt_three_ne (by rw [coreVal_zero]; omega)
  have hzero : dnX0 α h = dnGen α h 0 := rfl
  rw [hzero]
  induction hF using Submonoid.closure_induction with
  | mem G hG =>
    rcases hG with ((hG | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · exact dnClearAuts_fixes_core α h (by rw [coreVal_zero]; omega) (Submonoid.subset_closure hG)
    · show dnCoreMixPEquiv α h k (dnGen α h 0) = dnGen α h 0
      rw [dnCoreMixPEquiv_gen, hm6MarkNp, hm6UpdateBD_of_ne _ _ _ hne1 hne3]
    · show dnCoreMixQEquiv α h k (dnGen α h 0) = dnGen α h 0
      rw [dnCoreMixQEquiv_gen, hm6MarkNq, hm6UpdateBC_of_ne _ _ _ hne1 hne2]
    · show dnTauCEquiv α h k (dnGen α h 0) = dnGen α h 0
      exact dnTauCEquiv_of_ne α h k hne2
  | one => rfl
  | mul a b _ _ ha hb =>
    show a (b (dnGen α h 0)) = dnGen α h 0
    rw [show b (dnGen α h 0) = dnGen α h 0 from hb]
    exact ha

end WideChar

/-! ## §5 The payoff: MC1's pure `N5`/`N6`, and the `N`-side S3 discharge

The raw twists of HM6 carry S1 shears along; memo §3.2 isolates MC1's pure families by composing
with the elementary Nielsen lifts.  On the ν-frame both corrections are *landed exact
automorphisms* — `dnTauDEquiv` (HM4's `τ_c`) for `N5` and `dnTauCEquiv` (MC4's `N3`) for `N6` —
so the whole isolation is a two-step composite inside `A⁺(P,h)`:

```
pure N5(p) = N5(p) ∘ τ_c(−p)          frame: x̄₁ ↦ x̄₁ + p·σ̄     (σ̄, x̄₂ fixed)
pure N6(q) = N6(−q) ∘ N3(−q)          frame: x̄₁ ↦ x̄₁ + q·x̄₂    (σ̄, x̄₂ fixed)
```

Both collapses use one arithmetic fact about `D_N` and nothing else: **every `ℤ₂`-character of
`D_N` kills `x₀`** (MC4's `nChar_dnX0`), so the `x̄₀`-components the raw twists produce are
invisible.  That is memo §3.2's "the coupled `t`-shifts come out automatically". -/

section PureFamilies

variable (α h : ℕ)

/-- The `x̄₀`-row of the ν-frame of the marked generators vanishes, for **every** character
(MC4's `nChar_dnX0`).  The single input to the two collapses below. -/
theorem nuFrame_dnGen_zero (f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (dnGen α h) 0 = 0 := by
  rw [nuFrame_apply, show dnGen α h 0 = dnX0 α h from rfl, nChar_dnX0, toAdd_one]

end PureFamilies

section PureFrame

variable {h : ℕ}

private theorem cwOne_ne_three : (1 : Fin (coreRank h)) ≠ 3 :=
  coreVal_lt_three_ne (by rw [coreVal_one]; omega)

private theorem cwZero_ne_three : (0 : Fin (coreRank h)) ≠ 3 :=
  coreVal_lt_three_ne (by rw [coreVal_zero]; omega)

/-- **The `N5` collapse, at the frame level**: `hm6FrameBD p ∘ frameTauD (−p)` is MC4's pure
mixing move `nFrameMixX1 p` on any frame whose `x̄₀`-row vanishes.  The `τ_c(−p)` factor cancels
the `σ̄`-shear the raw twist puts on the `x̄₂`-row; the leftover `p·x̄₀` is the invisible one. -/
theorem hm6FrameBD_frameTauD (p : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2]) (h0 : m 0 = 0) :
    hm6FrameBD p (frameTauD (-p) m) = nFrameMixX1 p m := by
  funext i
  by_cases h1 : i = 1
  · subst h1
    rw [hm6FrameBD_one, frameTauD_of_ne _ _ cwOne_ne_three, frameTauD_of_ne _ _ cwZero_ne_three,
      frameTauD_of_ne _ _ coreTwo_ne_three, nFrameMixX1, Function.update_self, h0, zero_add,
      smul_eq_mul]
  by_cases h3 : i = 3
  · subst h3
    rw [hm6FrameBD_three, frameTauD_three, frameTauD_of_ne _ _ cwZero_ne_three,
      frameTauD_of_ne _ _ coreTwo_ne_three, nFrameMixX1,
      Function.update_of_ne (Ne.symm cwOne_ne_three), h0, zero_add, neg_smul]
    abel
  rw [hm6FrameBD_of_ne _ _ h1 h3, frameTauD_of_ne _ _ h3, nFrameMixX1, Function.update_of_ne h1]

/-- **The `N6` collapse, at the frame level**: `hm6FrameBC (−q) ∘ nCoreMat (planeElemU (−q))` is
`nFrameMix 0 q` on any frame whose `x̄₀`-row vanishes.  The `N3(−q)` factor cancels the `x̄₂`-shear
the raw twist puts on the `σ̄`-row. -/
theorem hm6FrameBC_nCoreMat (q : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2]) (h0 : m 0 = 0) :
    hm6FrameBC (-q) (nCoreMat (planeElemU (-q)) m) = nFrameMix 0 q m := by
  have h13 : (1 : Fin (coreRank h)) ≠ 3 := cwOne_ne_three
  have h03 : (0 : Fin (coreRank h)) ≠ 3 := cwZero_ne_three
  set m' := nCoreMat (planeElemU (-q)) m with hm'
  have e0 : m' 0 = 0 := by rw [hm', nCoreMat_of_ne _ _ nCoreZero_ne_two h03, h0]
  have e1 : m' 1 = m 1 := nCoreMat_of_ne _ _ nCoreOne_ne_two h13
  have e2 : m' 2 = m 2 - q * m 3 := by
    rw [hm', nCoreMat_two, planeElemU]
    norm_num [sub_eq_add_neg]
  have e3 : m' 3 = m 3 := by
    rw [hm', nCoreMat_three, planeElemU]
    norm_num
  funext i
  by_cases h1 : i = 1
  · subst h1
    rw [hm6FrameBC_one, e0, e1, e3, nFrameMix, Function.update_self, smul_eq_mul]
    ring
  by_cases h2 : i = 2
  · subst h2
    rw [hm6FrameBC_two, e0, e2, e3, nFrameMix,
      Function.update_of_ne (Ne.symm nCoreOne_ne_two), smul_eq_mul]
    ring
  by_cases h3 : i = 3
  · subst h3
    rw [hm6FrameBC_three, e3, nFrameMix, Function.update_of_ne (Ne.symm h13)]
  rw [hm6FrameBC_of_ne _ _ h1 h2, hm', nCoreMat_of_ne _ _ h2 h3, nFrameMix,
    Function.update_of_ne h1]

/-- The two pure moves commute into MC4's `nFrameMix p q`. -/
theorem nFrameMixX1_nFrameMix (p q : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2]) :
    nFrameMixX1 p (nFrameMix 0 q m) = nFrameMix p q m := by
  funext i
  by_cases h1 : i = 1
  · subst h1
    rw [nFrameMixX1, Function.update_self, nFrameMix, Function.update_self, nFrameMix,
      Function.update_self, Function.update_of_ne (Ne.symm nCoreOne_ne_two)]
    ring
  rw [nFrameMixX1, Function.update_of_ne h1, nFrameMix, Function.update_of_ne h1, nFrameMix,
    Function.update_of_ne h1]

end PureFrame

section PureLift

variable (α h : ℕ)

/-- **MC1 §3.4's pure family `N5`** at 2-adic parameter `p`: HM6's raw twist followed by HM4's
exact transvection `τ_c(−p)`. -/
noncomputable def dnPureMixP (α h : ℕ) (p : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  (dnCoreMixPEquiv α h p).trans (dnTauDEquiv α h (-p))

/-- **MC1 §3.4's pure family `N6`** at 2-adic parameter `q`: HM6's raw twist at `−q` followed by
MC4's exact transvection `N3(−q)`. -/
noncomputable def dnPureMixQ (α h : ℕ) (q : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  (dnCoreMixQEquiv α h (-q)).trans (dnTauCEquiv α h (-q))

/-- **The pure `N5` row**: `x̄₁ ↦ x̄₁ + p·σ̄`, realized inside `A⁺(P,h)`.  Set beside
`nCoreMixHypothesis_not_of_mix`, which refutes the same row over `A(P,h)`, this is exactly what
the widening buys. -/
theorem dnRealizesWide_frameMixX1 (p : ℤ_[2]) :
    DnRealizesWide α h (dnPureMixP α h p) (frameEnd (nFrameMixX1 p)) := by
  rw [dnPureMixP]
  obtain ⟨hmem, hfr⟩ := (dnRealizesWide_coreMixP α h p).trans α h (dnRealizesWide_tauD α h (-p))
  refine ⟨hmem, fun f => ?_⟩
  rw [hfr f, frameEnd_mul_apply, frameEnd_apply]
  exact hm6FrameBD_frameTauD p _ (nuFrame_dnGen_zero α h f)

/-- **The pure `N6` row**: `x̄₁ ↦ x̄₁ + q·x̄₂`, realized inside `A⁺(P,h)`. -/
theorem dnRealizesWide_frameMixQ (q : ℤ_[2]) :
    DnRealizesWide α h (dnPureMixQ α h q) (frameEnd (nFrameMix 0 q)) := by
  rw [dnPureMixQ]
  obtain ⟨hmem, hfr⟩ :=
    (dnRealizesWide_coreMixQ α h (-q)).trans α h (dnRealizesWide_tauC α h (-q))
  refine ⟨hmem, fun f => ?_⟩
  rw [hfr f, frameEnd_mul_apply, frameEnd_apply]
  exact hm6FrameBC_nCoreMat q _ (nuFrame_dnGen_zero α h f)

/-- **The whole S3 pair, realized inside `A⁺(P,h)`**: `x̄₁ ↦ x̄₁ + p·σ̄ + q·x̄₂`, MC4's
`nFrameMix p q`. -/
theorem dnRealizesWide_frameMix (p q : ℤ_[2]) :
    DnRealizesWide α h ((dnPureMixP α h p).trans (dnPureMixQ α h q))
      (frameEnd (nFrameMix p q)) := by
  obtain ⟨hmem, hfr⟩ :=
    (dnRealizesWide_frameMixX1 α h p).trans α h (dnRealizesWide_frameMixQ α h q)
  refine ⟨hmem, fun f => ?_⟩
  rw [hfr f, frameEnd_mul_apply, frameEnd_apply, nFrameMixX1_nFrameMix]

/-- **The `N`-side S3 stratum is a THEOREM over `A⁺(P,h)`** — MC1 §8 Decision 2 moves from
"(B) binder now" to "(A) proved" for `N`, at spike cost.  Compare
`nCoreMixHypothesis_not_of_mix`: over the *narrow* `A(P,h)` the identical stratum set makes the
binder **false**.  No new axiom, no B8, no compactness of `Aut(D_N)`; census unchanged. -/
theorem nCoreMixHypothesisWide_mixX1 :
    NCoreMixHypothesisWide α h (Set.range fun p : ℤ_[2] => frameEnd (nFrameMixX1 p)) := by
  rintro F ⟨p, rfl⟩
  exact ⟨_, dnRealizesWide_frameMixX1 α h p⟩

/-- The same for the full `N5`/`N6` pair stratum. -/
theorem nCoreMixHypothesisWide_mixPair :
    NCoreMixHypothesisWide α h
      (Set.range fun pq : ℤ_[2] × ℤ_[2] => frameEnd (nFrameMix pq.1 pq.2)) := by
  rintro F ⟨⟨p, q⟩, rfl⟩
  exact ⟨_, dnRealizesWide_frameMix α h p q⟩

/-! ### MC4's own binder, discharged

`NMixPairHypothesis` (`N.lean:1695`) is MC4's sound restatement of the S3 stratum: at the marked
generators, through the ν-frame, with a χ-preservation clause and **without** the `A(P,h)`
membership clause that `nCoreMixHypothesis_not_of_mix` refutes.  Everything it asks for is now
available — the ν-frame side from `dnRealizesWide_frameMix`, the χ side from
`chiN_of_mem_dnClearAutsWide` applied to that same automorphism's membership certificate.  So the
binder becomes a theorem, and with it MC4's `nStabParam_lift` and `nMarkedCorrection` lose their
S3 hypothesis; only the S2 unit-scaling binder (which runs through the *existing* axiom B8)
remains on the `N` lane. -/

/-- **MC4's S3 binder for the pair `N5`/`N6` is a THEOREM** (memo §5.1's discharge, wired). -/
theorem nMixPairHypothesis_coreMix : NMixPairHypothesis α h := by
  intro p q
  obtain ⟨hmem, hfr⟩ := dnRealizesWide_frameMix α h p q
  exact ⟨_, chiN_of_mem_dnClearAutsWide α h hmem, hfr⟩

/-- **MC4's `NMixHypothesis` is a THEOREM** — the `q = 0` slice. -/
theorem nMixHypothesis_coreMix : NMixHypothesis α h :=
  nMixHypothesis_of_pair α h (nMixPairHypothesis_coreMix α h)

/-- **MC4's parametrized lift, with the S3 binder discharged**: every admissible stabilizer
parameter tuple is realized by a χ-preserving continuous automorphism of `D_N`, conditionally on
the S2 unit-scaling binder **alone**.  This is `nStabParam_lift` with one of its two hypotheses
removed. -/
theorem nStabParam_lift_of_scaling (hScal : NPlaneScalingHypothesis α h) {P : NStabParam}
    (hP : P.Admissible) :
    ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (Ψ x) = chiN α h x)
        ∧ ∀ f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]),
          nuFrame f (fun i => Ψ (dnGen α h i)) = P.nuAction (nuFrame f (dnGen α h)) :=
  nStabParam_lift α h hScal (nMixPairHypothesis_coreMix α h) hP

end PureLift

/-! ### Stress pin: narrow FALSE, wide TRUE, on the same stratum

MC4 pins its refutation at `(α, h) = (2, 1)`; the two `example`s below pin the refutation and its
repair *side by side*, at the same parameters and against the **same** set of frame moves.  This
is the whole content of the widening in two lines, and it is checked by the kernel. -/

section StressPin

/-- MC4: the schematic S3 binder over `A(P,h)` is **false** for the mixing stratum. -/
example : ¬ NCoreMixHypothesis 2 1 (Set.range fun p : ℤ_[2] => frameEnd (nFrameMixX1 p)) :=
  nCoreMixHypothesis_not_of_mix 2 1 one_ne_zero ⟨1, rfl⟩

/-- HM6f: over `A⁺(P,h)` the same stratum is **realized**. -/
example : NCoreMixHypothesisWide 2 1 (Set.range fun p : ℤ_[2] => frameEnd (nFrameMixX1 p)) :=
  nCoreMixHypothesisWide_mixX1 2 1

/-- And MC4's own binder is discharged there. -/
example : NMixPairHypothesis 2 1 := nMixPairHypothesis_coreMix 2 1

end StressPin

/-! ## §6 What stays binder-shaped

Two residues, both on the `M` side, and neither of them repairable by widening.

* **The `M5` isolation.**  `dmRealizesWide_coreMix` realizes the *raw* twist
  `hm6FrameBD k`, and `(dmCoreMixEquiv α h k).trans (dmTauDEquiv α h (-k))` clears its `C̄₀`-shear
  exactly as on the `N` side.  What is left over is `D̄ ↦ D̄ + k·Ā`, and unlike `x̄₀` on `D_N` the
  row `Ā` is *not* killed by every character of `D_M` — the abelianized relation is
  `2Ā + 2^α·C̄₀ = 0`, not `Ā = 0`.  Isolating MC1's pure `M5` therefore needs one more shear,
  `τ_a(−k) : B ↦ A^{−k}·B`, which is an **exact** family (memo §3.2) but lives on the `M` side
  in MC3's `M.lean`; this file does not import it.  Nothing mathematical is missing — the
  composite is one `.trans` away once the two files meet.
* **The `⟨M4, M6, M7⟩` residual** (memo §4.2, §4.3).  These are *structurally obstructed*, not
  merely unbuilt: they are not symplectic, hence not reachable by any relator-preserving word
  automorphism, so no widening of the generating set — this one or any other — can produce them.
  `MCoreMixHypothesisWide α h ⟨M4, M6, M7⟩` therefore stays a binder, with MC1 §8 Decision 2(A)'s
  levelwise/graded-Lie price unchanged and its "unknown risk" label intact.  Memo §5.2(1) records
  that MC5's ν-correction does not consume it, and §5.2(2) that restating `hLift` in the consumed
  form would remove it from the consumers entirely — a scoping decision, not a mathematical one.

The `N` lane has no S3 residue at all after §5. -/

end MarkedCore

end Dyadic

end GQ2
