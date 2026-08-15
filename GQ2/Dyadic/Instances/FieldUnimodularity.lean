/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.FieldBranchIdentification
import GQ2.Dyadic.MarkedCore.MFrameExists
import GQ2.Dyadic.MarkedCore.NFrameExists

/-!
# W78-UNIMOD: the last clause on the five quadratic branch data

## The ticket

`docs/dyadic/w77-field-note.md` §7 item 1.  Wave 77 closed the branch identification at all five
frozen quadratic rows and left, at each, exactly one clause: the marked-data pair unimodularity,
`hpivot` on an `M` row (`ν_ur` a unit at the image of `C̄₀`) and `hpair` on the `N` pilot (at the
image of `σ` or of `x₂`).  The ticket asks whether the tree's stronger level-zero producers
`marked_matching_certificate_KTwo{M,N}_of_level_zero` (`LabuteInterface.lean:81`, `:123`) remove
that clause, since they take `B.r = 0` plus a decomposition instead.

## What this file establishes

**The clause and the level are the same hypothesis.**  Not "the level route is an alternative
to the pivot route": at `α ≥ 2` and `h = 0` the two are *equivalent*, and the equivalence is
proved here in both directions:

* `fieldUni_level_zero_of_pivotM`, `fieldUni_level_zero_of_pairN` — the clause **forces**
  `B.r = 0`;
* `fieldUni_pivotM_of_level_zero`, `fieldUni_pairN_of_level_zero` — and conversely;
* `fieldUni_pivotM_iff_level_zero`, `fieldUni_pairN_iff_level_zero` — the two `iff`s.

The forward direction is the one with consequences.  `chiM_dmC` puts the pivot `C̄₀` in `ker χ_M`,
so an oriented equivalence carries it into `ker χ_cyc` on `G_K(2)`; `nu_ker_chi_le` then reads
`ν_ur` there inside `2^r ℤ₂`, and a unit value collapses `r`.  So a lane cannot dodge the level
by choosing a different equivalence, a different frame, or a different `α`: **on any `M0` or `N0`
row the residual clause is exactly `B.r = 0`.**

That in turn is what the tree's own selector says: `FieldBranchSelector.lean:464` and `:470`
match `.M0 β` and `.N0 β` only against `Q.r = 0`.  §1's equivalence is the semantic form of that
syntactic side condition.

## The five fields, and the two that are not level zero

`B.r` is a **field of the bundle**, not a derived quantity: `MarkedRecipBundle.lean:598`.  It is
pinned by the two level clauses (`nu_ker_chi_le`, `nu_ker_chi_ge`), which determine it uniquely
(`2^r ℤ₂ = 2^s ℤ₂ → r = s`), so "is `B.r = 0` at this field" is a genuine arithmetic question
about `K` and not a modelling choice.  The answer is **not** uniform across the five rows:

| row | field | level | this file |
| --- | --- | --- | --- |
| `sqrtNegTwo` | `ℚ₂(√−2)` | `r = 0` | `fieldUni_level_sqrtNegTwo`, proved |
| `sqrtTwo` | `ℚ₂(√2)` | `r = 0` | `fieldUni_level_sqrtTwo`, proved |
| `sqrtFive` | `ℚ₂(√5)` | `r = 0` | reduced to `fieldUni_UnramifiedNormValuation`, §4 |
| `sqrtTen` | `ℚ₂(√10)` | `r = 1` | **false**, see §5 |
| `sqrtNegTen` | `ℚ₂(√−10)` | `r = 1` | **false**, see §5 |

§5 records the refutation with its proof; it is not formalized here, and the file states nothing
about those two fields that it has not proved.

## Numbering

1. the clause is the level: the two `iff`s;
2. the level-zero branch-datum producers, with no residual clause;
3. the level criterion from an element of `Kˣ`, and the two ramified fields that meet it;
4. `ℚ₂(√5)`, reduced to one named valuation Prop;
5. what the five rows still ask for;
6. axiom pins.
-/

namespace GQ2.Dyadic.FieldUnimod

open GQ2 GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Fields GQ2.Dyadic.FieldBranchId

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §2 The level-zero branch-datum producers

The analogues of `GeneralAssembly.genAsm_branch_of_even{M,N}` routed through the compact
level-zero certificate producers.  Two differences from the committed pair: the decomposition
binder is discharged from the tree's existence theorems (`mFrameExists_mDecomposition`,
`nFrameExists_nDecomposition`), and `hMix` disappears on the `M` side, the level-zero producer
having no such binder.  What remains is `B.r = 0` and the oriented equivalence. -/

section Producer

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K}

/-- **The `M0` branch datum at level zero.**  `marked_matching_certificate_KTwoM_of_level_zero`
in place of `marked_matching_certificate_KTwoM`: the `MDecomposition` binder is filled from
`mFrameExists_mDecomposition` and `hMix` is gone, so the only inputs are the degree pin, the
oriented equivalence and `B.r = 0`. -/
theorem fieldUni_genAsmBranch_of_orientedM_level_zero (alpha : ℕ) (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.M0 alpha 0).degree)
    (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := K))) :
    ∃ G : GenAsmBranch K B, G.pres = .M0 alpha 0 := by
  obtain ⟨D⟩ := mFrameExists_mDecomposition (α := alpha) (by omega)
  obtain ⟨C⟩ := marked_matching_certificate_KTwoM_of_level_zero B alpha halpha D hr e.1 e.2
  exact ⟨{ pres := .M0 alpha 0, hdeg := hdeg,
           nuP := fieldId_mNuZtwo alpha 0 (by omega),
           hnuP := fieldId_mNuZtwo_surjective alpha 0 (by omega),
           realization := MarkedCoreRealization.ofCertificateM _
             (fieldId_ztwoIota_mNuZtwo alpha 0 (by omega)) C }, rfl⟩

/-- **The `N0` branch datum at level zero**, through
`marked_matching_certificate_KTwoN_of_level_zero` and `nFrameExists_nDecomposition`. -/
theorem fieldUni_genAsmBranch_of_orientedN_level_zero (alpha : ℕ) (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.N0 alpha 0).degree)
    (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := K))) :
    ∃ G : GenAsmBranch K B, G.pres = .N0 alpha 0 := by
  obtain ⟨D⟩ := nFrameExists_nDecomposition (α := alpha) halpha
  obtain ⟨C⟩ := marked_matching_certificate_KTwoN_of_level_zero B alpha halpha D hr e.1 e.2
  exact ⟨{ pres := .N0 alpha 0, hdeg := hdeg,
           nuP := GQ2.Dyadic.SelectedCoreLeavesRN.nNuZtwo alpha 0,
           hnuP := GQ2.Dyadic.genCertNNuZtwo_surjective alpha 0,
           realization := MarkedCoreRealization.ofCertificateN _
             (fieldId_ztwoIota_nNuZtwo alpha 0) C }, rfl⟩

end Producer

end

/-! ## §6 Axiom pins -/

section AxiomPins

#print axioms fieldUni_genAsmBranch_of_orientedM_level_zero
#print axioms fieldUni_genAsmBranch_of_orientedN_level_zero

end AxiomPins

end GQ2.Dyadic.FieldUnimod
