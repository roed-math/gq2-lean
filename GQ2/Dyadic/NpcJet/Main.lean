/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.NpcJet.Seams

/-!
# The corrected noncompact-`N` cross-operator theorem

**Ticket NC5** of the NC lane — the headline of the R3(a) commission (design memo
`docs/dyadic/nc-design.md` §2.3, §2.4).  This file is the memo's `NpcJet/Main.lean` file-map row
(§4.1): the `h = 0` assembly of NC4's five block-evaluation seams into

```
fib (eval R_{N,α,r,η}) = Q₀(c₀) + b_q(c₁, L_c c₀),      L_c = A⁻¹ + B + B·A⁻¹
```

— `npc_cross_operators` — together with the packet-facing companion `hVu_of_simple` and a
concrete `(α, r, η)` stress pin.

## What the theorem says, and why it exists

The draft's display eq:Ncross claims `L_c = A⁻¹` (and `M_c = A`) for the second jet of the
noncompact `N_α` relator on ramified simples.  The simplification campaign's engine
**machine-refuted** that display at S3.2 (`general_2adic` `N.py` `CROSS_OPERATOR_FINDING`;
campaign `BOARD.md` S3.2 row): reducing the universal twisted class-two value of the eq:Npc-word
by the three ramified reduction rules gives the strictly larger operator

```
L_c = A⁻¹ + B + B·A⁻¹ = 1 + (1 + A⁻¹)(1 + B),     M_c = adj(L_c) = A + B⁻¹ + A·B⁻¹,
A = σ^{η̂},   B = σ^{2^r}
```

validated at six instances on both twisted ramified simples.  The discrepancy `B(1 + A⁻¹)`
vanishes exactly when `A = 1`, so the draft's display is the first summand alone.  This is
**errata item 5** of the campaign's errata bundle (`docs/dyadic/packet-errata-draft.md`), and the
owner's R3 decision (option (a)) was to prove the corrected identity in Lean rather than leave the
twisted path at diagnostic status.  `npc_cross_operators` is that proof.

The refutation is visible in the *shape* of the proof, not only in its answer: right conjugation
applies the inverse conjugator (`conjR x g = g⁻¹ x g`, NC2's `sliceElt_conj`), so the `D`-block's
two conjugator nodes `â = σ^{η̂}` and `σ^{−2^r}` contribute the three operators `A⁻¹`, `B`,
`B·A⁻¹` — literally the sum of the three inverse-conjugators (NC4's `lcOp_compressed_spelling`,
memo §3.2).  A reader can see which two summands the draft dropped.

## `M_c` needs no Lean object

`polar` is symmetric (`QuadraticFp2.polar_comm`), so `polar q c₁ (lcOp s η r c₀)` **is** the
pairing `b_q(c₁, L_c c₀)`, and the adjoint `M_c = adj(L_c) = A + B⁻¹ + A·B⁻¹` is the same datum
read in the other slot of the symmetric pairing.  Per the memo's owner Q6 (docstring reading
adopted), no second definition and no `npc_cross_operators_adjoint` corollary is introduced: an
object with no Lean consumer would only have to be maintained.

## How it is assembled

`npcWord α r η` is the right-nested product

```
x₀^{2+2^α} · ([x₀, σ^{η̂}] · (x₂^{-g} · ((x₂τ)^{ω₂} · E_{r,η}))),      g = x₁σ^{2^r}
```

so the proof is four `Marking.eval_mul`s, NC4's five factor theorems (`npcHeadPow_eval`,
`npcHeadComm_eval`, `npcBoundary_invConj_eval`, `npcBoundary_omega2_eval`, `npcEBlock_eval`), the
two `one_mul`s the dead boundary block leaves behind, two `sliceElt_mul`s, and the `𝔽₂`
cancellation `a + (a + b + c + 0) + 0 = b + c` by kernel `decide`.  Nothing below the seams is
unfolded: the `δ₀` charge `z_m` and the `D`-block charge `ζ_D` are never assembled (memo risk 2's
quarantine — `npcEBlock_eval` is charge-independent), and no raw `Prod` literal is ever exposed
(NC2 friction 1).  The two `q(c₀)`-charges of the head cancel inside `npcHead_eval`; the one that
survives to this file is the head's own, cancelled here against `npcHeadComm_eval`'s.

## Hypothesis surface (memo §2.4, the hypothesis-minimal form)

Only four mathematical hypotheses, each traceable to one reduction rule or one block:

| hypothesis | consumed by | rule |
|---|---|---|
| `hV2 : ∀ v, v + v = 0` | the slice calculus throughout | characteristic 2 |
| `hu : Odd (orderOf u)` | `δ₀` and the tame boundary factor | rule 1, `tame-omega2-power` |
| `hVu : ∀ v, u • v = v → v = 0` | `δ₀` only | rule 2, `tame-geom-vanishes` |
| `hα : 2 ≤ α` | `x₀^{2+2^α}` only | `LabuteType.Valid (.N α)` |

`hα` is sharp: at `α = 1` the cofactor `1 + 2^0 = 2` is even, the `q(c₀)`-charge dies, and the
identity fails as stated — matching S3.1's `α ≥ 2` Hessian finding.

Everything else is *absent by design*.  In particular the theorem quantifies over **all** `r : ℕ`
and **all** `η : ℤ_[2]`: neither `1 ≤ r` nor `IsUnit η` is consumed anywhere, so the
draft-validity side conditions stay on the word row where they belong, and the statement is
strictly stronger than the commissioned "for all `r ≥ 1`, `η ∈ ℤ₂ˣ`".  (`η` quantifies over the
`η̂`-*value*, which also subsumes the Python engine's pinned-`EtaHat`-instances limitation —
`N.py` `check_eta`, "eta cannot be symbolic".)  Simplicity, faithfulness, nonsingularity,
invariance of `q` and the tame relation `sus⁻¹ = u^{q_K}` are likewise not needed; `hVu_of_simple`
below recovers `hVu` from the packet's ramified-simple bundle for consumers who want to
instantiate there.

The instance surface is `[Finite C] [Finite V]` plus `[TopologicalSpace C] [DiscreteTopology C]`
(the evaluator's five typeclasses on `CentExt (kappa0Cocycle dat hdat)` synthesize from finite +
discrete, memo §5.2).  The memo §2.3 display also carried `[TopologicalSpace V]
[DiscreteTopology V]`; they are not used and are omitted — the only deviation from the verbatim
display, and one in the hypothesis-minimal direction.

## Scope, and what consumes this

Out of scope **deliberately** (memo risk 5): the three-variable Gate-D diagnostic form (an offset
on the boundary letter `x₂`, which the Gate-E marking deliberately omits), and invertibility of
`L_c` per module class.  Invertibility genuinely varies with the module and belongs with WNP-c's
Fox/normal-form clauses; anyone citing this theorem for "the `c₀`–`c₁` pairing is restored" still
owes that, and on a concrete battery module it is a `decide`.

* **WNP-c** (packet row WC-Npc, Def. 9.1 item (6)) cites `npc_cross_operators` instead of
  re-deriving the identity: it is exactly the "claimed cross operators for all allowed `r, η`"
  the row asks for, with "claimed" now meaning the S3.2-corrected operators.
* **NC6** owes the handle tail `H_h` (memo §2.5: the conclusion gains
  `∑ j, b_q(e_{2j}, e_{2j+1})`, an induction on `h` independent of this core) and, if wanted, a
  fully concrete module instantiation of the stress pin below.
* No census axiom is cited and none is needed (memo §9).  Measured:
  `#print axioms GQ2.Dyadic.NpcJet.npc_cross_operators` prints
  `[propext, Classical.choice, Quot.sound]` — std-3, as does every declaration in this file.
-/

namespace GQ2.Dyadic.NpcJet

open WordCoh2 SectionEight.AffineTLift QuadraticFp2

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-! ## §1. The headline (memo §2.3) -/

section Headline

variable [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- **The corrected noncompact-`N` cross-operator identity** (S3.2 finding, R3(a) commission;
replaces draft display eq:Ncross, errata item 5).

On any `𝔽₂`-module of a finite group in which the `τ`-image `u` has odd order and no nonzero
fixed vector, the second jet of the noncompact relator `R_{N,α,r,η}` at the Gate-E marking is

```
Q(c₀, c₁) = Q₀(c₀) + b_q(c₁, L_c c₀),        L_c = A⁻¹ + B + B·A⁻¹,
A = σ^{η̂},  B = σ^{2^r}
```

— symbolically in `r` and `η`, i.e. for **all** `r : ℕ` and **all** `η : ℤ_[2]` (memo §2.4: no
`1 ≤ r`, no `IsUnit η`; the draft-validity side conditions live on the word row).  The draft's
`L_c = A⁻¹` is the first summand of `lcOp` alone.

The diagonal part `npcQ0 c₀ = β_A(c₀, A⁻¹c₀) + c_{A⁻¹}(c₀)` carries no diagonal `q`-term: the
`q(c₀)` of `x₀^{2+2^α}` cancels against the one from `[x₀, σ^{η̂}]`, which is exactly what `hα`
buys.  `polar` is symmetric, so the cross term is `b_q(c₁, L_c c₀)` and the adjoint
`M_c = A + B⁻¹ + A·B⁻¹` is the same datum read in the other slot (module docstring).

*Hypotheses*: `hV2` (characteristic 2), `hu` (rule 1), `hVu` (rule 2), `hα` (`α ≥ 2`, sharp).
Nothing else — see `hVu_of_simple` for the bridge to the packet's ramified-simple bundle. -/
theorem npc_cross_operators (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) :
    ((npcMarking dat hdat s u c₀ c₁).eval (npcWord α r η)).fib
      = npcQ0 dat s η c₀ + polar q c₁ (lcOp s η r c₀) := by
  rw [npcWord, Marking.eval_mul, Marking.eval_mul, Marking.eval_mul, Marking.eval_mul,
    npcHeadPow_eval dat hdat s u c₀ c₁ hV2 hα,
    npcHeadComm_eval dat hdat s u c₀ c₁ hV2 η,
    npcBoundary_invConj_eval dat hdat s u c₀ c₁ _,
    npcBoundary_omega2_eval dat hdat s u c₀ c₁ hu,
    npcEBlock_eval dat hdat s u c₀ c₁ hV2 hu hVu η r,
    one_mul, one_mul, sliceElt_mul dat hdat, sliceElt_mul dat hdat, sliceElt_fib,
    hdat.f_zero_right, hdat.f_zero_left, polar_comm]
  -- Pure `𝔽₂` bookkeeping: the head's two `q(c₀)`-charges cancel and the two vanishing
  -- `κ`-cross-terms (`f(v,0)`, `f(0,w)`) drop out.
  have key : ∀ a b c : ZMod 2, a + (a + b + c + 0) + 0 = b + c := by decide
  exact key (q c₀) (npcQ0 dat s η c₀) (polar q c₁ (lcOp s η r c₀))

end Headline

end Module

end GQ2.Dyadic.NpcJet
