/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores

/-!
# Dyadic campaign, ticket WAH: the shared branch-word alphabet toolkit

The five wave-2 branch-word files — `Words/{N0,M0,Npc,L,Mpc}.lean` — each opened by naming its
own letters, and by wave's end each carried a variant of the same small toolkit.  WN0-a (the
pilot) flagged the duplication at 2×; by WMP-a it was at 5×, and on 2026-08-01 it broke the root
build: WL-a had declared its copy in the bare `GQ2.Dyadic.Words` namespace and collided with
`N0.lean`'s twenty names the moment `GQ2.lean` imported both.  The emergency fix re-namespaced
`L.lean` to `Words.LSq`; **this file removes the cause**, by giving the genuinely shared
declarations one home in `GQ2.Dyadic.Words` — the parent namespace, so that
`Words.{MCompact,Npc,LSq,Mpc}` reach them without an `open`.

Nothing here is new mathematics and nothing here changed statement when it moved.

## What lives here, and what does not

Two tiers, and the boundary between them is the alphabet:

1. **Alphabet-generic** (`§1`): `isOmega2Only_prodList`, `pro2_prodList`,
   `eval_prodList_append`, `invConj_mul_self`.  These never mention `Generator n` at a fixed `n`
   (or mention it at a *variable* `n`), so all five lanes share them, `LSq` included.
2. **The `Generator (2 + 2h)` alphabet** (`§2`–`§4`): `coreLetter`, `handleU`, `handleV`,
   `wildGen`, `genOfName`, `denoteCtx`, `handlesW`, `handleTailW`, their kill-wild/`pro2`
   companions, and the `ZMod 8` refutation kit.  Four lanes share these — `N0`, `MCompact`,
   `Npc`, `Mpc`.

**`LSq` is on a different alphabet and keeps its own copies.**  At degree `n = 2h + 1` the word
has two core letters, not three; the alphabet is `Generator (2 * h + 1)`, not
`Generator (2 + 2 * h)`; the handle pairs start at `x₂`, not `x₃`; `wildGen`'s bound is
`2h + 2`, not `2h + 3`; and `genOfName`'s table stops at `x₁`.  Those are six different
*statements*, not six different proofs of one statement, so `Words.LSq` declares its own seven
and this file does not try to unify them.  A rank-polymorphic restatement would change every
call site in `Certificates/{L,LFox}.lean`, which is a different ticket from this one.

## ⚠ The three handle shapes

Three conventions for "where do the handles attach" are on record, one per emitting row, and
each wave-2 lane rediscovered the distinction the hard way.  They are recorded here so the next
lane reads them instead:

| shape | rows | the `h = 0` tree | the Lean device |
|---|---|---|---|
| **count-`0` node** | `N0` (WN0-a), `Npc` (WNP-a) | carries `HyperbolicHandles 3 0` — a real child with count zero | the word always has `handlesW h` as a factor; `handlesW 0 = .one` (`handlesW_zero`) |
| **no node at `h = 0`** | `MCompact` (WM0-a), `Mpc` (WMP-a) | carries **no** `HyperbolicHandles` child at all | `handleTailW`, a `List` that is `[]` at `h = 0`; the word is `prodList (core ++ handleTailW h)` |
| **no node at `n = 1`** | `LSq` (WL-a) | carries no child at degree `n = 1`, i.e. at `h = 0` | `LSq.handleTail`, the same list device but at `HyperbolicHandles 2` and indexed by the degree `n = 2h + 1` |

The second and third are the *same* device on different alphabets; the first is a different
device.  What this means in practice: a lane on the count-`0` shape may write `handlesW h`
directly into its factor list and simp with `handlesW_zero`, while a lane on either
no-node shape must go through the list, because its certificate hash is of a tree with one
fewer child and `denote` will not produce a spurious `.one`.  Getting this wrong is not caught
by the type checker — it is caught by the gate-A hash pin, which is the good news.

The `RawWord`-level tails (`rawHandleTail`) are **not** hoisted: they are certificate-tree data
rather than alphabet, `LSq`'s is at `HyperbolicHandles 2`, and `MCompact`'s and `Mpc`'s differ in
their `.int` spelling (`.int ((h + 1 : ℕ) : ℤ)` against `.int (h + 1)`) — propositionally equal,
syntactically not, and the hash pins are `rfl`.  See the WAH report.

## Implementation notes

This file is **not** `module`-style, for the reason `N0.lean` records: it imports
`GQ2.Dyadic.TameBoundary`, which is not `module`-style, and a `module` file may not import a
non-`module` one.  It is imported by all five `Words/*.lean` files and so reaches `GQ2.lean`
transitively; no import registration of its own is needed.
-/

namespace GQ2.Dyadic.Words

open Export (RawWord)

/-! ## §1. Alphabet-generic combinators

Four lemmas that mention no fixed alphabet.  Each was copied into between two and four of the
five lanes; each is stated here at the most general form any lane used, which for three of them
is strictly more general than every copy it replaces (see the WAH report's upgrade column).
-/

/-- `PWord.prodList` of `ω₂`-only words is `ω₂`-only: the induction that every lane needs before
it can evaluate a `Multiply` node with `PWord.evalNat`. -/
theorem isOmega2Only_prodList {Gen : Type*} :
    ∀ {l : List (PWord Gen)}, (∀ w ∈ l, w.IsOmega2Only) → (PWord.prodList l).IsOmega2Only
  | [], _ => trivial
  | w :: _ws, hw =>
      ⟨hw w (List.mem_cons_self ..),
       isOmega2Only_prodList fun u hu => hw u (List.mem_cons_of_mem _ hu)⟩

/-- `pro2` commutes with `PWord.prodList`, at **every** rank.

Stated at a variable `n` rather than at either lane's alphabet: the proof only ever uses
`pro2_mul`, so the `Generator (2 + 2h)` copies (four lanes) and the `Generator (2h + 1)` copy
(`LSq`) were the same theorem twice. -/
theorem pro2_prodList {n : ℕ} :
    ∀ l : List (PWord (Generator n)),
      pro2 (PWord.prodList l) = PWord.prodList (l.map pro2)
  | [] => rfl
  | w :: ws => by
      rw [PWord.prodList_cons, pro2_mul, pro2_prodList ws, List.map_cons, PWord.prodList_cons]

/-- Evaluation splits over an append of factor lists — what a lane needs the moment its word is
`prodList (core ++ handleTail h)` rather than a single flat list.

The profinite instances are **not** decoration and `G : Type` is **not** an oversight:
`PWord.eval` itself is declared at `{G : Type}` with all four (`Word/Eval.lean`), because a
`^ᶻ`-power needs them, so this is the most general form available and both copies had it. -/
theorem eval_prodList_append {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] {Gen : Type*} (μ : Gen → G)
    (l₁ l₂ : List (PWord Gen)) :
    PWord.eval μ (PWord.prodList (l₁ ++ l₂)) =
      PWord.eval μ (PWord.prodList l₁) * PWord.eval μ (PWord.prodList l₂) := by
  rw [PWord.eval_prodList, List.map_append, List.prod_append, PWord.eval_prodList,
    PWord.eval_prodList]

/-- `x^{-g} · x = [g, x]` — the one group-theoretic move behind every lane's gate-C comparison,
where the `x^{-σ}` factor of the word pairs with the `x` left behind by a collapsed `ω₂`. -/
theorem invConj_mul_self {G : Type*} [Group G] (x g : G) : (conjR x g)⁻¹ * x = commP g x := by
  simp only [conjR, commP, mul_inv_rev, inv_inv]
  group

end GQ2.Dyadic.Words
