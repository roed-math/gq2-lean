/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Separation
import GQ2.Dyadic.Count.Variation

/-!
# Dyadic campaign, ticket CB-5: the word-side suppliers of CB-4's separation forks

CB-4 (`Count/Separation.lean`) stated both separation forks **cup-free**, so that one binder each
serves the arithmetic and the candidate side, and then supplied the arithmetic side
(`isRightSeparating_of_tateDualityG`, `isTwoSeparating_of_tateDualityG`).  This file supplies the
word side.

## What is here

| § | content | status |
|---|---|---|
| 1 | `sepWordN` — the degree-generic `sep_word` | **closed**, no side conditions |
| 2 | the graph hom of a primal/dual pair of cocycles, module-generic | closed |
| 3 | the pair cochain **is** the inflated Heisenberg cocycle | closed |
| 4 | `wordPairing_eq_zero_of_pair_B2` — vanishing of the traced word pairing | closed |
| 5 | **`isRightSeparating_of_selfDualN`** — the `hpartial` fork, candidate side | **closed** |

Section 5 is the ticket's deliverable (b): the degree-generic clone of `ℚ₂`'s
`Phase140GammaA.b1_of_pair_cochain_B2`, which is `Fin 4`-pinned end to end.

## ⚠ The `hsep` fork is *not* closed by §1, and this is a statement about the fork

The ticket scoped (a) as "`IsTwoSeparating` from `IsSelfDualN.cardH2`", by way of the generic
`sep_word`.  §1 delivers the generic `sep_word` — cheaply, and in fact **more cheaply than the
`ℚ₂` ancestor**, since it needs neither the count nor the `2`-torsion hypothesis.  What it does
*not* deliver is `IsTwoSeparating Γ A`, and the obstruction is structural rather than a missing
lemma:

* `IsTwoSeparating Γ A` (`Count/Separation.lean` §5) is a statement about **`H²(Γ, A)`** — a
  continuous `2`-cocycle of the *source group* at **module** coefficients.
* `sepWordN` is a statement about `WordH²(A) = (ρ → A) ⧸ im d¹` — the **word** complex.
* The bridge between them would be a degree-`2` comparison at module coefficients,
  `H²(Γ, A) ↪ WordH²(A)`.  CB-1's comparison (`z1Equiv`/`h1Equiv`) stops at degree `1`; CB-H2's
  degree-`2` rung (`h2Word`) is **scalar-only by construction** — `CentExt` is a central
  extension by `𝔽₂`, `splitU` needs the trivial action, and `obs` lands in `𝔽₂` on the nose
  because the target has two elements.  No such module-coefficient rung exists in the repository.

The `ℚ₂` candidate-side proof of `hsep` (`Phase140/GammaA/Hsep.lean`, `hsep_gammaA`) never forms
`H²(Γ_A, T)` either: it runs the **marking route** — set-lift the marking, read the relator values
in `T`, apply `sep_word` to *those*, correct the marking, descend.  So `sepWordN` is genuinely the
engine that route needs, and the piece still owed is the rest of that route in degree-generic form
(the `exists_relatorFree_marking` / `mlift_of_relatorFree_marking` layer), **or** the
module-coefficient degree-`2` rung.  Either is a ticket, not a lemma.  See §1's docstring for the
precise statement of what `sepWordN` gives and the two ways to consume it.

By contrast the `hpartial` fork needs only degree `1` at module coefficients (for `ξ` and for its
primal partners) and degree `2` at the **scalars** (for the pair cochain, which is `𝔽₂`-valued),
and both of those exist — which is why §5 closes.

## What §5 costs, and what made it affordable

CB-4 flagged the missing pieces for (b) as a degree-generic `obs_inflation` and a degree-generic
`mixedB_eq_relZPair`.  **CB-VAR built both while this ticket was queued**, for the opposite
direction of the same ledger identity:

* `pObsFam_inflation` (`Count/Variation.lean` §4) *is* the degree-generic `MixedBObs.obs_inflation`;
* `pRelZ_kappaHeisN` (§3) *is* the alphabet-generic, `PWord`-valued `mixedB_eq_relZPair`, and it
  needs no `Fin 4` and no `heisEta1` replacement — the `Fin 4`-shaped statement is replaced by one
  `PWord.map_eval` along the structural isomorphism `CentExt kappaHeisN ≅ H(A) ⋊ C`;
* `sum_heisD1_zmod2` (§5a) is the detection functional, and it is what turns "the obstruction lies
  in `im d¹`" into a scalar equation.

So §4 is a **re-use** of CB-VAR's ledger in the contrapositive direction rather than a new
development, and the ticket's predicted `heisEta1`-for-`mixedB_eq_relZPair` substitution never had
to be made: `heisEta1` enters only at the very end, through `IsSelfDualN.pairing`'s own statement.

## Numeric leaves

**Nothing in this file reads a count.**  Neither `sepWordN` nor `isRightSeparating_of_selfDualN`
mentions `Nat.card`, `SourceNumerics`, or a degree `n`; `IsSelfDualN` is consumed through clause
**3** (`pairing`) only, never through `cardZ1`, and §1 consumes `StokesDuality`'s `h2_inj` clause
directly.  CB-SG's exponent warning therefore does not apply to anything here — there is no
exponent to check.

## Import discipline

Plain-import.  `Count.Separation` (CB-4, plain) carries the two forks; `Count.Variation` (CB-VAR,
plain) carries the ledger, and through `Count.HTwo`/`Count.Compare` the rung, the comparison and
`IsSelfDualN`.  No new module enters the `Count` closure.

Axioms: no new axioms, no `sorry`.  All headline declarations print exactly the standard three.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction

/-! ## §1. The degree-generic `sep_word`

`RStageGammaA.sep_word` (`GQ2/RStage/GammaA.lean:334`) and its Roe twin `sep_word_R`, over an
arbitrary alphabet and relator family: a degree-`2` word cochain killed by every **invariant**
`𝔽₂`-functional is a word coboundary.

Two things are worth recording about the generic proof, because both differ from the `ℚ₂` one:

* **It is a direct implication, not a contradiction.**  `ℚ₂` argues: if `[v] ≠ 0` pick a functional
  `Ψ` on `H²w` with `Ψ[v] ≠ 0`, then use `wTrace_surjective` — a *counting* surjectivity, off
  `IsSelfDual`'s clause 1 — to write `Ψ` as a trace.  Here the hypothesis is turned into an
  extension problem instead: `η²(v)` kills `ker d⁰`, so it descends to `A^∨ ⧸ ker d⁰`, which
  injects into `ι → A^∨`, and `elemDual_extend` (`𝔽₂` is self-injective on finite elementary
  groups) extends it.  That produces exactly the witness `StokesQuasiIso.h2_inj` asks for.
* **Consequently no count and no `2`-torsion hypothesis are used.**  `ℚ₂`'s `sep_word` takes
  `hsd : IsSelfDual t A` and `hA₂ : ∀ a : A, a + a = 0`; this takes `StokesDuality c w A` and
  nothing else.  The `2`-torsion needed by the extension is `2`-torsion of `ι → A^∨`, which is
  automatic (`wordDual_two_torsion`), not a hypothesis on `A`.  In particular the clause of the
  duality package consumed is `h2_inj`, the clause `IsSelfDualN.cardH2` is *derived from*
  (`stokesQuasiIso_card_H2`), so the ticket's "from `IsSelfDualN.cardH2`" is honoured one step
  upstream and with no cardinality in sight. -/

section SepWord

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] {C : Type*} [Group C]
  {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]

/-- **The degree-generic `sep_word`.**  If the traced sum `∑ₖ vₖ` of a degree-`2` word cochain is
killed by every `d⁰`-invariant `𝔽₂`-functional on `A`, then `v` is a word coboundary.

`RStageGammaA.sep_word` at an arbitrary alphabet `ι`, an arbitrary relator family `w : ρ → F(ι)`
and an arbitrary finite coefficient module — and with **fewer hypotheses than the `ℚ₂` ancestor**:
no `IsSelfDual` count clause, no `2`-torsion of `A`, no generation, no tame/wild relator
conditions.  The whole input is `StokesDuality`'s `h2_inj`.

The proof is the composition the ticket names: the hypothesis is precisely that `η²(v)` factors
through `d⁰ : A^∨ → (ι → A^∨)`, `elemDual_extend` produces the factorization, and `h2_inj` converts
it into a `d¹`-preimage. -/
theorem sepWordN {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A) (v : ρ → A)
    (hv : ∀ lam : ElemDual A, heisD0 (A := ElemDual A) c lam = 0 → lam (∑ k, v k) = 0) :
    v ∈ (heisD1 (A := A) c w).range := by
  classical
  set d₀ : ElemDual A →+ (ι → ElemDual A) := heisD0 (A := ElemDual A) c with hd₀
  set E : ElemDual A →+ ZMod 2 := (heisEta2 v : ElemDual (ElemDual A)) with hEdef
  have hE : ∀ q ∈ d₀.ker, E q = 0 := fun q hq => hv q (AddMonoidHom.mem_ker.mp hq)
  obtain ⟨lam, hlam⟩ := elemDual_extend (A := ι → ElemDual A) (wordDual_two_torsion (A := A))
    (QuotientAddGroup.kerLift d₀) (QuotientAddGroup.kerLift_injective d₀)
    (QuotientAddGroup.lift d₀.ker E hE : ElemDual (ElemDual A ⧸ d₀.ker))
  refine hd.h2_inj v ⟨lam, ElemDual.ext fun q => ?_⟩
  show lam (d₀ q) = E q
  exact hlam (QuotientAddGroup.mk q)

end SepWord

end GQ2.Dyadic.Count
