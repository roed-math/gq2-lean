/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.TraceForm
public import GQ2.StiefelWhitney

@[expose] public section

/-!
# Deriving the Evens–Kahn formula (B9) from the relative Stiefel–Whitney identity (B9-A, N4/N5)

This file supplies the engine behind the B9-A flip (plan `docs/orchestration/b9a-proof-plan.md`,
nodes N4/N5): since 2026-07-24, `GQ2/Foundations/Axioms.lean` proves the same-name theorem
`evensKahn_dyadic` — byte-identical to the pre-flip axiom — as
`evensKahn_dyadic_of_rsw relativeStiefelWhitney_dyadic …
(hilbertSymbol_normCriterion_finiteDyadic k htriv)`.

One declaration:

* `evensKahn_dyadic_of_rsw` — the reusable engine.  It takes the relative Stiefel–Whitney
  statement as an explicit hypothesis `hrsw` (this file stays upstream of the axiom file, so it
  cannot name the B9 axiom) together with the B11a norm criterion `hnorm`, and proves the
  pre-flip B9 conclusion.

## The `hnorm` hypothesis (owner-approved firewall, Q2)

The engine carries `hnorm`, the dyadic Hilbert-symbol norm criterion — the exact conclusion of
axiom **B11a**, `hilbertSymbol_normCriterion_finiteDyadic k htriv`.  It is forced: the degree-2
component evaluates `swTwo` on the diagonal transfer forms via `swTwo_diag`, whose Delzant
well-definedness (`swTwo_well_defined`, plan node N2) consumes the criterion.  B11a lives
downstream in `GQ2/Foundations/Axioms.lean`, so it cannot be imported here; the firewall carries
it as a hypothesis (`GQ2/StiefelWhitney.lean`'s `swTwo_diag`/`swTwo_congr` already do), and this
file inherits it one level up.  The owner approved this design (Q2,
`docs/orchestration/b9a-tickets.md`).  The degree-1 component needs no such input.  At the flip
the hypothesis is discharged from B11a, so the flipped `evensKahn_dyadic` is byte-identical (no
`hnorm`) with `#print axioms` = {`relativeStiefelWhitney_dyadic`,
`hilbertSymbol_normCriterion_finiteDyadic`, + std-3} (plan node N2).

## No unit-arithmetic bridge is needed

T1 pinned the diagonalization weights of `traceFormOne_isDiagonalization` (`⟨2, 2d⟩`) and
`traceFormTwisted_isDiagonalization` (`⟨2u, 2dn/u⟩ = ⟨twoUnit k*u, twoUnit k*d*n*u⁻¹⟩`) to the exact
B9 normal form, so `swOne_diag`/`swTwo_diag` land on the B9 `kummerClassK` arguments syntactically;
the two components close by `rw` with no `(↥k)ˣ` associativity/commutativity bridging.

## Imports and `sorry` status

Imports are strictly upstream of `GQ2/Foundations/Axioms.lean` (`GQ2.TraceForm`,
`GQ2.StiefelWhitney` and their closure supply the B9 vocabulary
`kummerClassK`/`corH1`/`evensNormH2`/`twoUnit` from `GQ2.EvensKahn`).  This file has **no** `sorry`
and **no** `axiom`.  `evensKahn_dyadic_of_rsw` depends only on the sorried Lemma 6.16
diagonalizations and Delzant well-definedness (`GQ2/TraceForm.lean`, `GQ2/StiefelWhitney.lean`;
tickets T2/T3); `evensKahn_dyadic_derived` additionally uses the sorried draft
`relativeStiefelWhitney_dyadic`.  Those sorries are reported by `lake` against *their* files, never
this one.

## Citations

Kahn, Invent. Math. 78 (1984), Théorème 2; Evens, Trans. AMS 108 (1963), Thm 1; Kozlowski, Proc.
AMS 91 (1984), Thm 1.1; Serre, *Local Fields* [7], Ch. XIV §2 (B11a).  Paper: §6, eq. (111),
Lemmas 6.13/6.16.  Plan: `docs/orchestration/b9a-proof-plan.md` nodes N4/N5.
-/

namespace GQ2

-- Same relaxation as the sibling files `GQ2/StiefelWhitney.lean` and `GQ2/TraceForm.lean`: the
-- quadratic-form / trace-form instance chains resolve through the `IntermediateField` instance
-- space, and the final `rw`/`exact` on the trace-form identities carry a heavy `isDefEq`.
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **B9 from the relative Stiefel–Whitney identity `hrsw`, given the B11a norm criterion `hnorm`.**
The reusable engine of this file.  From the abstract identity `hrsw` (the exact statement of
`relativeStiefelWhitney_dyadic`, taken as a hypothesis so the file stays upstream of the axiom file)
and the norm criterion `hnorm`, it proves the byte-identical B9 conclusion at `a = u + vδ`.

Proof (plan node N5): the transfer unit `a = u + vδ ∈ k(δ)ˣ` is built as a nonzero element of the
field `quadExt k δ` (its image is `β² ≠ 0`); `finrank_quadExt_eq_two` gives `[k(δ):k] = 2`; `hrsw`
gives the two Stiefel–Whitney components; the Lemma 6.16 diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩` and
`Tr⟨1⟩ ≃ ⟨2, 2d⟩`, via `swOne_diag`/`swTwo_diag`, rewrite them into the B9 Kummer-class form.

`GQ2/Foundations/Axioms.lean` instantiates this at the B9 axiom
`relativeStiefelWhitney_dyadic` and `hnorm := hilbertSymbol_normCriterion_finiteDyadic k htriv`,
recovering the byte-identical B9 statement as the same-name theorem. -/
theorem evensKahn_dyadic_of_rsw
    (hrsw : ∀ (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
        (d : (↥k)ˣ) (δ β : AlgebraicClosure ℚ_[2])
        (_hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
        (_hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
        (a : (↥(quadExt k δ))ˣ)
        (_hβ : β ^ 2 = ((a : ↥(quadExt k δ)) : AlgebraicClosure ℚ_[2]))
        (_hβ0 : β ≠ 0)
        (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
            k.fixingSubgroup).index = 2)
        (s : k.fixingSubgroup)
        (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
        (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
        (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
            k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
        (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
            k.fixingSubgroup) → ZMod 2)
        (_hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
            ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
        (hα : ∀ g h, α (g * h) = α g + α h)
        (hαc : Continuous α),
        (swOne k (traceFormTwisted k δ ↑a)
          = swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc)
        ∧ (swTwo k htriv (traceFormTwisted k δ ↑a)
          = swTwo k htriv (traceFormOne k δ)
            + swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc
            + evensNormH2 htriv hUo hidx hs α hα hαc))
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (u n d : (↥k)ˣ) (v : ↥k)
    (hn : (n : ↥k) = (u : ↥k) ^ 2 - (d : ↥k) * v ^ 2)
    (δ β : AlgebraicClosure ℚ_[2])
    (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
    (hβ : β ^ 2 = ((u : ↥k) : AlgebraicClosure ℚ_[2]) + (v : AlgebraicClosure ℚ_[2]) * δ)
    (hβ0 : β ≠ 0)
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (s : k.fixingSubgroup)
    (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup) → ZMod 2)
    (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
        ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hα : ∀ g h, α (g * h) = α g + α h)
    (hαc : Continuous α)
    (hnorm : ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0
        ↔ ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2) :
    (kummerClassK k (twoUnit k * u) + kummerClassK k (twoUnit k * d * n * u⁻¹)
      = kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d)
        + corH1 htriv hUo hidx hs α hα hαc)
    ∧ (kummerClassK k (twoUnit k * u) ⌣[htriv] kummerClassK k (twoUnit k * d * n * u⁻¹)
      = kummerClassK k (twoUnit k) ⌣[htriv] kummerClassK k (twoUnit k * d)
        + (kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d)) ⌣[htriv]
            corH1 htriv hUo hidx hs α hα hαc
        + evensNormH2 htriv hUo hidx hs α hα hαc) := by
  -- Step 1: the transfer element `a₀ = u + v·δ` as an element of `L = quadExt k δ`, and its image.
  have hδmem : δ ∈ quadExt k δ := by
    unfold quadExt; exact IntermediateField.subset_adjoin _ _ rfl
  have humem : ((u : ↥k) : ℚ̄₂) ∈ quadExt k δ := by
    simpa using IntermediateField.algebraMap_mem (quadExt k δ) (u : ↥k)
  have hvmem : (v : ℚ̄₂) ∈ quadExt k δ := by
    simpa using IntermediateField.algebraMap_mem (quadExt k δ) v
  have hmem : ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ ∈ quadExt k δ :=
    add_mem humem (mul_mem hvmem hδmem)
  set a₀ : ↥(quadExt k δ) := ⟨((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ, hmem⟩
  have ha₀coe : ((a₀ : ↥(quadExt k δ)) : ℚ̄₂) = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ := rfl
  -- `a₀ ≠ 0` because its image is `β² ≠ 0`, so `a₀` is a unit of the field `quadExt k δ`.
  have ha₀ne : a₀ ≠ 0 := by
    intro h
    refine pow_ne_zero 2 hβ0 ?_
    have hz : ((a₀ : ↥(quadExt k δ)) : ℚ̄₂) = 0 := by rw [h]; simp
    rw [ha₀coe] at hz
    rw [hβ]; exact hz
  set aU : (↥(quadExt k δ))ˣ := Units.mk0 a₀ ha₀ne
  have haUcoe : ((aU : ↥(quadExt k δ)) : ℚ̄₂) = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ := ha₀coe
  -- Step 2: `[k(δ):k] = 2` from the B9 subgroup encoding, and the twisted `hβ` for `aU`.
  have hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2 := finrank_quadExt_eq_two k d hδ hidx hUo
  have hβ' : β ^ 2 = ((aU : ↥(quadExt k δ)) : ℚ̄₂) := by rw [haUcoe]; exact hβ
  -- Step 3: apply the relative Stiefel–Whitney identity `hrsw` at the transfer unit `aU`.
  obtain ⟨eq1, eq2⟩ := hrsw k d δ β hδ hdeg aU hβ' hβ0 hidx s hs htriv hUo α hαdef hα hαc
  -- Step 4: Lemma 6.16 diagonalizations (weights already in B9 normal form) and their SW values.
  have hdiagOne : IsDiagonalization k (traceFormOne k δ) (twoUnit k) (twoUnit k * d) :=
    traceFormOne_isDiagonalization k d hδ hdeg
  have hdiagTw : IsDiagonalization k (traceFormTwisted k δ (aU : ↥(quadExt k δ)))
      (twoUnit k * u) (twoUnit k * d * n * u⁻¹) :=
    traceFormTwisted_isDiagonalization k u n d v hn hδ hdeg (aU : ↥(quadExt k δ)) haUcoe
  have hsw1One : swOne k (traceFormOne k δ)
      = kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d) :=
    swOne_diag k hdiagOne
  have hsw1Tw : swOne k (traceFormTwisted k δ (aU : ↥(quadExt k δ)))
      = kummerClassK k (twoUnit k * u) + kummerClassK k (twoUnit k * d * n * u⁻¹) :=
    swOne_diag k hdiagTw
  have hsw2One : swTwo k htriv (traceFormOne k δ)
      = kummerClassK k (twoUnit k) ⌣[htriv] kummerClassK k (twoUnit k * d) :=
    swTwo_diag k htriv hnorm hdiagOne
  have hsw2Tw : swTwo k htriv (traceFormTwisted k δ (aU : ↥(quadExt k δ)))
      = kummerClassK k (twoUnit k * u) ⌣[htriv] kummerClassK k (twoUnit k * d * n * u⁻¹) :=
    swTwo_diag k htriv hnorm hdiagTw
  -- Step 5: rewrite both identity components into the B9 Kummer-class form (no bridge needed).
  refine ⟨?_, ?_⟩
  · rw [hsw1Tw, hsw1One] at eq1; exact eq1
  · rw [hsw2Tw, hsw2One, hsw1One] at eq2; exact eq2

end GQ2
