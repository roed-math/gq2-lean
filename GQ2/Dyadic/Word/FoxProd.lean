/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.Dyadic.Word.Fox

@[expose] public section

/-!
# Dyadic campaign, ticket W41-MPC: the Fox product rule across a list append

`Words/Alphabet.lean` §1 carries `eval_prodList_append`, the statement that `PWord.eval` splits
over an append of factor lists.  Every branch word whose top-level display is a concatenation of
blocks — `mCompactW`, `lSqW`, `mpcW` — needs it the moment a lane wants the block decomposition
rather than the flat factor list.

At the **Fox** layer the same split is not multiplicativity but the product rule
`D(uv) = D(u) + ū·D(v)`, so the append law carries a prefix weight:

```
D(prodList (l₁ ++ l₂)) = D(prodList l₁) + (prodList l₁)‾ · D(prodList l₂).
```

`Word/Fox.lean` already has the two degenerate cases — the two-factor rule `foxD_mul`, and
`foxD_prodList_of_trivial`, which flattens a *single* list under the hypothesis that every factor
acts trivially — but neither reaches a block decomposition of a word like

```
mpcW α r p η h = prodList (linFactors ++ hatFactors ++ plusFactors ++ handleTailW h)
```

whose blocks do **not** all act trivially (the linear copy's prefix weight is the `S₂`-power
Prop. 9.2's balance controls).  This file supplies the missing law.

## Genericity

Following `Words/Alphabet.lean` §1's discipline: nothing here mentions a fixed alphabet, a fixed
rank `n`, or a fixed group.  The raw form `foxD_prodList_append'` needs only
`[Group C] [AddCommGroup A] [DistribMulAction C A]`, exactly the binder block `foxD` itself is
declared over — no finiteness, because it is the `WordLift` multiplication law and nothing else.
The textbook form `foxD_prodList_append` adds `[Finite A] [Finite C]`, and only because
`foxEval_g` (the base of the Fox evaluation is the evaluation of the base) does: `ω₂` computes
`2`-primary parts in finite groups.  The two-list corollary
`foxD_prodList_append_of_trivial_left` and the value twin `evalFin_prodList_append` are stated at
the same generality as their inputs.

`evalFin_prodList_append` is the `evalFin` twin of `Words.eval_prodList_append`, and is needed
alongside the Fox law because the prefix weight in the product rule is an `evalFin` value: a lane
computing a three-block word rewrites the weight of `l₁ ++ l₂` into the product of the two
blocks' weights.

## Implementation notes

`module`-style, one `public import` of `GQ2.Dyadic.Word.Fox`, which is itself `module`-style.
The natural long-run home of these four declarations is `Word/Fox.lean` §"The trivially-acting
subgroup", immediately after `evalFin_prodList` and `foxD_prodList_of_trivial`; they are in a
leaf of their own here only so that ticket W41-MPC does not invalidate every certificate file
downstream of `Fox.lean`.  A hoist is a pure move — no statement changes.
-/

namespace GQ2.Dyadic

open GQ2.FoxH

section ProdAppend

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **`evalFin` splits over an append of factor lists** — the `evalFin` twin of
`GQ2.Dyadic.Words.eval_prodList_append`, and the lemma that computes the prefix weight appearing
in `foxD_prodList_append`. -/
theorem evalFin_prodList_append (μ : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (l₁ l₂ : List (PWord X)) :
    PWord.evalFin μ E E₂ (PWord.prodList (l₁ ++ l₂))
      = PWord.evalFin μ E E₂ (PWord.prodList l₁) * PWord.evalFin μ E E₂ (PWord.prodList l₂) := by
  rw [evalFin_prodList, List.map_append, List.prod_append, evalFin_prodList, evalFin_prodList]

variable (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The Fox product rule across an append**, raw form (the prefix weight still spelled inside
the lift group, so no finiteness):

```
D(prodList (l₁ ++ l₂)) = D(prodList l₁) + (prodList l₁)‾ · D(prodList l₂).
```

The induction is on `l₁` and uses nothing but `foxD_mul'`, i.e. the multiplication law of
`WordLift`. -/
theorem foxD_prodList_append' : ∀ l₁ l₂ : List (PWord X),
    foxD t a E E₂ (PWord.prodList (l₁ ++ l₂))
      = foxD t a E E₂ (PWord.prodList l₁)
        + (foxEval t a E E₂ (PWord.prodList l₁)).g • foxD t a E E₂ (PWord.prodList l₂)
  | [], l₂ => by
      rw [List.nil_append, PWord.prodList_nil, foxD_one, foxEval_one, WordLift.one_g, one_smul,
        zero_add]
  | w :: ws, l₂ => by
      rw [List.cons_append, PWord.prodList_cons, PWord.prodList_cons, foxD_mul', foxD_mul',
        foxD_prodList_append' ws l₂, foxEval_mul, WordLift.mul_g, smul_add, mul_smul, add_assoc]

/-- **The Fox product rule across an append**, textbook form: the prefix weight is the branch
word's own finite evaluation `PWord.evalFin`. -/
theorem foxD_prodList_append [Finite A] [Finite C] (l₁ l₂ : List (PWord X)) :
    foxD t a E E₂ (PWord.prodList (l₁ ++ l₂))
      = foxD t a E E₂ (PWord.prodList l₁)
        + PWord.evalFin t E E₂ (PWord.prodList l₁) • foxD t a E E₂ (PWord.prodList l₂) := by
  rw [foxD_prodList_append', foxEval_g]

/-- The append rule with a trivially-acting prefix block: the weight disappears and the two
blocks' rows simply add.  This is the block-level analogue of `foxD_prodList_of_trivial`, which
is the factor-level statement. -/
theorem foxD_prodList_append_of_trivial_left [Finite A] [Finite C] (l₁ l₂ : List (PWord X))
    (h₁ : PWord.evalFin t E E₂ (PWord.prodList l₁) ∈ trivAct C A) :
    foxD t a E E₂ (PWord.prodList (l₁ ++ l₂))
      = foxD t a E E₂ (PWord.prodList l₁) + foxD t a E E₂ (PWord.prodList l₂) := by
  rw [foxD_prodList_append, mem_trivAct.mp h₁]

end ProdAppend

end GQ2.Dyadic

/-! ## Axiom footprint -/

section AxiomAudit

#print axioms GQ2.Dyadic.evalFin_prodList_append
#print axioms GQ2.Dyadic.foxD_prodList_append'
#print axioms GQ2.Dyadic.foxD_prodList_append
#print axioms GQ2.Dyadic.foxD_prodList_append_of_trivial_left

end AxiomAudit
