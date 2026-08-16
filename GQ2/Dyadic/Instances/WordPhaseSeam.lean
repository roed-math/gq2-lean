/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.WordPhaseModel

/-!
# W88-SEAM: the scalar word trace at the compact family

Ticket source: `docs/dyadic/w87-normal-note.md` §6 item 1.  W87 reduced the compact rows'
determinant clause to a single analytic statement, `wPmCompactHeadPhase`, and then reduced
*that* to the **trace seam**: the compact twin of `LSquare.QZero_eq_lUniform_graphHessianTrace`,
which says the source scalar obstruction is the sum of the evaluated word Hessians of the two
relators.  The odd proof of the seam runs through a scalar orientation `H² Γ 𝔽₂ ≃+ 𝔽₂`, and
the only word-specific ingredient of that orientation is the **word trace** `WordH² ≃+ 𝔽₂`,
which existed for the `L` family alone (`LSquare.lWordH2TraceEquiv`).

This file supplies the word trace at both compact words.

## §1 The word-generic trace equivalence

`LSquare.wordH2Trace_injective_of_pairColumn` is already word-generic: for any two-relator
family, the descended trace is injective as soon as the scalar differential hits the column
`(1,1)`.  Surjectivity is generic too.  `wPsWordH2TraceEquiv` is therefore the `L`-free
statement: a two-relator word whose scalar `d¹` contains `(1,1)` has scalar word `H²` of order
two, with the coordinate sum as the isomorphism.  `LSquare.lWordH2TraceEquiv` is the `L`
instance of it; that declaration is untouched.

## §2 The compact pair column

Every action of any group on `𝔽₂` is trivial (`GQ2.ResidueLift.htriv_zmod2`), so the
completely-split hypotheses of `heisD1_{n,m}CompactFam_tauRow_of_split`
(`Instances/N0M0ScalarStokes.lean`) are free at scalar coefficients: those theorems say both
rows of the resolved compact family read off the `tau` coordinate, so the `tau` basis vector
is carried to `(1,1)` on the nose.  This is the compact counterpart of
`LSquare.lSq_heisD1_tauColumn`, and it holds for both compact words.

## §3 The compact word traces

`wPsNCompactWordH2TraceEquiv` and `wPsMCompactWordH2TraceEquiv`: the objects W87 §6 item 1
asked for.  Both are stated at the uniform exponent `omega2Exp (4 * Monoid.exponent C)`, which
is the exponent every downstream consumer uses (`Count.resolvesAt_{n,m}CompactFam_uniformHeis`,
`wPmCompactPhaseComparison_of_headPhase`).
-/

namespace GQ2.Dyadic.Instances.WordPhaseSeam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.LSquare

/-! ## §1 The word-generic trace equivalence -/

section Generic

variable {iota : Type*} [Fintype iota] [DecidableEq iota] {C : Type*} [Group C]
  [DistribMulAction C (ZMod 2)]

/-- **The scalar word trace of any two-relator word that hits the column `(1,1)`.**  The
`L`-free form of `LSquare.lWordH2TraceEquiv`: injectivity is
`LSquare.wordH2Trace_injective_of_pairColumn`, already word-generic, and surjectivity is the
representative `(z, 0)`. -/
def wPsWordH2TraceEquiv (c : iota → C) (w : Fin 2 → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (hpair : ∃ x, heisD1 (A := ZMod 2) c w x = ![1, 1]) :
    WordH2 c w (ZMod 2) ≃+ ZMod 2 :=
  AddEquiv.ofBijective (wordH2Trace c w hr hend)
    ⟨wordH2Trace_injective_of_pairColumn c w hr hend hpair,
      fun z ↦ ⟨QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range (![z, 0]), by
        change z + 0 = z
        exact add_zero z⟩⟩

@[simp] theorem wPsWordH2TraceEquiv_mk (c : iota → C) (w : Fin 2 → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (hpair : ∃ x, heisD1 (A := ZMod 2) c w x = ![1, 1]) (v : Fin 2 → ZMod 2) :
    wPsWordH2TraceEquiv c w hr hend hpair
      (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range v) = ∑ k, v k := rfl

end Generic

/-! ## §2 The compact pair column -/

section PairColumn

variable {α h q : ℕ} {C : Type*} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]

/-- The scalar basis vector supported on the tame generator `tau`, at the compact alphabet.
The compact twin of `LSquare.lScalarTauBasis`. -/
def wPsCompactTauBasis (h : ℕ) : Generator (2 + 2 * h) → ZMod 2 :=
  fun i ↦ if i = Generator.tau then 1 else 0

@[simp] theorem wPsCompactTauBasis_tau (h : ℕ) :
    wPsCompactTauBasis h Generator.tau = 1 := by
  simp [wPsCompactTauBasis]

/-- **The `tau` column of the uniform compact-`N` scalar differential is `(1,1)`.**  The compact
twin of `LSquare.lSq_heisD1_tauColumn`.  The completely-split hypotheses of
`heisD1_nCompactFam_tauRow_of_split` cost nothing at scalar coefficients: every action on `𝔽₂`
is trivial. -/
theorem wPs_heisD1_nCompactFam_tauColumn (t : Marking (2 + 2 * h) C)
    (hq : Even q) (hα : 1 ≤ α) :
    heisD1 (A := ZMod 2) ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (wPsCompactTauBasis h) = ![1, 1] := by
  rw [heisD1_nCompactFam_tauRow_of_split (A := ZMod 2) t (by decide)
    (fun _ a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a)
    (fun a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a) hq hα]
  simp

/-- **The `tau` column of the uniform compact-`M` scalar differential is `(1,1)`.** -/
theorem wPs_heisD1_mCompactFam_tauColumn (t : Marking (2 + 2 * h) C) (hq : Even q) :
    heisD1 (A := ZMod 2) ⇑t
        (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (wPsCompactTauBasis h) = ![1, 1] := by
  rw [heisD1_mCompactFam_tauRow_of_split (A := ZMod 2) t (by decide)
    (fun _ a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a)
    (fun a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a) hq]
  simp

end PairColumn

/-! ## §3 The compact word traces -/

section CompactTrace

variable {α h q : ℕ} {C : Type*} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]

/-- **The scalar word trace at the uniform compact-`N` family.**  The object W87 §6 item 1
asked for: the `NCompact` twin of `LSquare.lWordH2TraceEquiv`. -/
def wPsNCompactWordH2TraceEquiv (t : Marking (2 + 2 * h) C) (hq : Even q) (hα : 1 ≤ α)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)) k) = 1) :
    WordH2 ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) (ZMod 2) ≃+ ZMod 2 :=
  wPsWordH2TraceEquiv ⇑t _ hr
    (nCompact_isStokesEndpoint hα hq
      (odd_omega2Exp (Count.fourMulExponent_ne_zero_and_even C).1
        (Count.fourMulExponent_ne_zero_and_even C).2))
    ⟨wPsCompactTauBasis h, wPs_heisD1_nCompactFam_tauColumn t hq hα⟩

/-- **The scalar word trace at the uniform compact-`M` family.** -/
def wPsMCompactWordH2TraceEquiv (t : Marking (2 + 2 * h) C) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)) k) = 1) :
    WordH2 ⇑t (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
      (ZMod 2) ≃+ ZMod 2 :=
  wPsWordH2TraceEquiv ⇑t _ hr
    (MCompact.mCompact_isStokesEndpoint hq
      (odd_omega2Exp (Count.fourMulExponent_ne_zero_and_even C).1
        (Count.fourMulExponent_ne_zero_and_even C).2))
    ⟨wPsCompactTauBasis h, wPs_heisD1_mCompactFam_tauColumn t hq⟩

end CompactTrace

/-! ## Axiom audit

Every declaration in this file is pinned below.  The honest split: **all of them are std-3**
(`propext`, `Classical.choice`, `Quot.sound`) and none carries a campaign axiom.  In
particular the two compact word traces are axiom-neutral, exactly like their `L` original
`LSquare.lWordH2TraceEquiv`.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no recursion options, no
`set_option` of any kind.

**Trap check.**  No declaration here takes a `TateDualityG`, a `LocalEulerChar` or a
`RamifiedCertificate`.  The Tate-duality route to the same cardinality
(`LSquare.lScalarH2_card_eq_wordH2_of_tateDuality`) is deliberately *not* used: the word
trace is built from the explicit `tau` column, so it is duality-free on both sides. -/

section AxiomPins

#print axioms wPsWordH2TraceEquiv
#print axioms wPsWordH2TraceEquiv_mk
#print axioms wPsCompactTauBasis
#print axioms wPsCompactTauBasis_tau
#print axioms wPs_heisD1_nCompactFam_tauColumn
#print axioms wPs_heisD1_mCompactFam_tauColumn
#print axioms wPsNCompactWordH2TraceEquiv
#print axioms wPsMCompactWordH2TraceEquiv

end AxiomPins

end

end GQ2.Dyadic.Instances.WordPhaseSeam
