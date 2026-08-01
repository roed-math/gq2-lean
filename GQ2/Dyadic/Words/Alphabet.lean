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

/-! ## §2. The `Generator (2 + 2h)` alphabet

Four of the five lanes — `N0` (WN0-a, the pilot), `MCompact` (WM0-a), `Npc` (WNP-a) and `Mpc`
(WMP-a) — spell the same alphabet: the core wild letters `x₀, x₁, x₂`, the letters `σ` and `τ`,
and `h` handle pairs `x₃, …, x_{2h+2}`.  So the alphabet is `Generator (2 + 2h)`, whose wild
letters are `Fin (2h + 3)`; MC2's core has rank `coreRank h = 4 + 2h`, the same letters plus
`σ`, which is not wild.  All four lanes declared these six verbatim.

⚠ `genOfName` is the **certificate's name table**, and it is shared only because all four
emitters happened to name their letters the same way.  A lane whose certificate uses different
names must declare its own table and its own `denoteCtx` — as `Words.LSq` does — rather than
silently inheriting this one.  The failure mode is benign but confusing: the `denote` bridges
are `rfl`, so a wrong table shows up as a bridge that will not close, never as a wrong theorem.

The table is a literal `match` and not a decimal parser on purpose: `String.toNat?` is
well-founded recursion and does **not** reduce in the kernel, so a parsing `gen` field would put
every lane's `denote` bridge out of reach of `rfl`.  Handle letters never come through here —
they come through `wildGen` — which is why the table stops at `x₂`.
-/

/-- The core wild letters `x₀, x₁, x₂`, present at every handle count. -/
def coreLetter (h : ℕ) (i : Fin 3) : Generator (2 + 2 * h) :=
  .wild ⟨(i : ℕ), by have := i.isLt; omega⟩

/-- The first letter `x_{3+2j}` of the `j`-th handle pair. -/
def handleU {h : ℕ} (j : Fin h) : Generator (2 + 2 * h) :=
  .wild ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The second letter `x_{4+2j}` of the `j`-th handle pair. -/
def handleV {h : ℕ} (j : Fin h) : Generator (2 + 2 * h) :=
  .wild ⟨4 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The wild letter `x_i`, or `none` when `i` is past the alphabet.  This is the `handleGen`
field of the denotation context: `Export.handleFactors` indexes handle letters by a plain `ℕ`,
so the range check has to live here. -/
def wildGen (h : ℕ) (i : ℕ) : Option (Generator (2 + 2 * h)) :=
  if hi : i < 2 * h + 3 then some (.wild ⟨i, by omega⟩) else none

/-- The generator names the compact-`N`, compact-`M`, noncompact-`N` and procyclic-`M`
certificates use — one literal table, because all four emitters agree.  See the ⚠ above. -/
def genOfName (h : ℕ) (s : String) : Option (Generator (2 + 2 * h)) :=
  match s with
  | "sigma" => some .sigma
  | "tau" => some .tau
  | "x0" => wildGen h 0
  | "x1" => wildGen h 1
  | "x2" => wildGen h 2
  | _ => none

/-- The denotation context of the `Generator (2 + 2h)` rows: the certificates' names, the handle
letters, and **no** symbolic parameters — every frozen exponent in all four rows is a literal
`Int` (S5.G), so `param` is nowhere consulted and returning `none` is honest rather than
lossy. -/
def denoteCtx (h : ℕ) : Export.DenoteCtx (Generator (2 + 2 * h)) where
  gen := genOfName h
  handleGen := wildGen h
  param := fun _ => none

/-! ## §3. The handle block

`handlesW` is the expanded hyperbolic block; `handleTailW` is the *list* device the two no-node
lanes need (see the three handle shapes in the module docstring).  Both orders are
`List.finRange h`, which is simultaneously what `Export.handleFactors` expands the
`HyperbolicHandles` node to and how MC2's `handleWord` orders its factors — so every bridge
below is structural rather than a reindexing argument.
-/

/-- `H_h = ∏_{j<h} [x_{3+2j}, x_{4+2j}]`, the block the certificates write as
`HyperbolicHandles 3 h`. -/
def handlesW (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

@[simp] theorem handlesW_zero : handlesW 0 = .one := rfl

/-- The handle **tail** of the factor list: empty at `h = 0`, a one-element list otherwise —
the shape the `MCompact` and `Mpc` certificate trees need, which carry no `HyperbolicHandles`
child at all at `h = 0`. -/
noncomputable def handleTailW : (h : ℕ) → List (PWord (Generator (2 + 2 * h)))
  | 0 => []
  | h + 1 => [handlesW (h + 1)]

@[simp] theorem isOmega2Only_handlesW (h : ℕ) : (handlesW h).IsOmega2Only := by
  unfold handlesW
  refine isOmega2Only_prodList ?_
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact ⟨trivial, trivial⟩

@[simp] theorem pro2_handlesW (h : ℕ) : pro2 (handlesW h) = handlesW h := by
  rw [handlesW, pro2_prodList, List.map_map]
  rfl

/-! ## §4. The boundary companions

The kill-wild values of the letters and the evaluation of the handle block.  `Marking.eval`
forces `{G : Type}` with the four profinite instances (it is `PWord.eval`); `killWildLetters`
does not, and the `Mpc` lane had generalized its copy of the trio to `{G : Type*}`.

⚠ **That generalization is not taken here, deliberately.**  The trio is `@[simp]`, and at
`Type*` it fires on module-lift goals in `Certificates/M0Fox.lean` where the `Type`-restricted
form did not — four proofs there change behaviour (two `simp`s that then make no progress, one
that closes its goal early).  A hoist that repairs consumer proofs is not a hoist, so this file
carries the form three of the four copies had; `Mpc` uses the trio only at `Type` groups and is
unaffected.
-/

section KillWild

variable {G : Type} [Group G] {h : ℕ}

@[simp] theorem killWildLetters_coreLetter (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    Marking.killWildLetters t (coreLetter h i) = 1 := rfl

@[simp] theorem killWildLetters_handleU (t : Marking (2 + 2 * h) G) (j : Fin h) :
    Marking.killWildLetters t (handleU j) = 1 := rfl

@[simp] theorem killWildLetters_handleV (t : Marking (2 + 2 * h) G) (j : Fin h) :
    Marking.killWildLetters t (handleV j) = 1 := rfl

end KillWild

/-- Evaluating the handle block is MC2's `handleWord` on the handle letters — the same
`List.finRange h` order on both sides, so this is a rewrite and not a reindexing. -/
theorem eval_handlesW {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] {h : ℕ} (t : Marking (2 + 2 * h) G) :
    t.eval (handlesW h) =
      MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  rw [Marking.eval_def, handlesW, PWord.eval_prodList, List.map_map]
  rfl

/-! ## §5. The leading exponent `p_α = 2 + 2^α`

Two facts about the compact/noncompact-`N` leading exponent, shared verbatim by `N0` and `Npc`
and cited (not re-derived) by `Certificates/{N0,N0Fox,Npc,NpcFox}.lean`.  Pure `ℕ` arithmetic;
they sit here because they are the only part of those two rows' vocabulary that four certificate
files need and no lane owns.
-/

/-- The freeze's **spelling discipline** for the leading exponent: `2 + 2^α` is opaque, while
`2(1 + 2^{α−1})` displays the Hessian content — `1 + 2^{α−1}` is odd exactly when `α ≥ 2`, and
that oddness is what produces the `q(c₀)` term of the plus form.  The *words* keep the
certificates' `2 + 2^α`. -/
theorem two_add_two_pow (α : ℕ) (hα : 1 ≤ α) : 2 + 2 ^ α = 2 * (1 + 2 ^ (α - 1)) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 1 := ⟨α - 1, by omega⟩
  simp [pow_succ]
  ring

/-- `1 + 2^{α−1}` is odd for `α ≥ 2` — the Hessian side condition behind `BranchData.Valid`. -/
theorem odd_one_add_two_pow {α : ℕ} (hα : 2 ≤ α) : Odd (1 + 2 ^ (α - 1)) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  have h : (2 : ℕ) ^ (β + 2 - 1) = 2 * 2 ^ β := by
    rw [show β + 2 - 1 = β + 1 by omega, pow_succ]; ring
  exact ⟨2 ^ β, by rw [h]; ring⟩

/-! ## §6. The `ZMod 8` refutation and stress kit

Every lane refutes F3's unrelativized `KillsWild` at the same witness — `τ` a generator of
`Multiplicative (ZMod 8)`, everything else trivial — and every lane pins its numerical stress
values at the same `h = 0` marking.  Both markings and the order bound were written out five
times each; the order bound was written out **ten** times, because each file declared it twice,
once per section, under two different names.

⚠ Two accessibility notes.  (i) The order bound was `private` in all ten copies; `private` is
file-scoped, so hoisting necessarily makes it public — that is a visibility change, not a
statement change, and nothing outside `Words/` refers to it.  (ii) `zmod8_orderOf_dvd` is kept
as an alias of `orderOf_dvd_eight` rather than renamed away, so that every call site in the five
lanes stays untouched.  New code should use `orderOf_dvd_eight`.

The `local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥` and its
`DiscreteTopology` companion are **not** hoisted: they stay `local` in the lanes that state
`eval` facts, because `Marking` itself carries no typeclass arguments and nothing here needs
them.  Making them global instances would give `Multiplicative (ZMod 8)` a topology repo-wide,
which is a much larger claim than this file should make.
-/

/-- Every element of `Multiplicative (ZMod 8)` has order dividing `8` — the side condition of
`PWord.zpowHat_omega2_zpow` and of `PWord.eval_eq_evalNat_of_dvd` at every lane's witness. -/
theorem orderOf_dvd_eight (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- The `Refutation`-section spelling of `orderOf_dvd_eight`, kept so that the five lanes'
refutation proofs need no edit.  Prefer `orderOf_dvd_eight`. -/
theorem zmod8_orderOf_dvd (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_eight x

/-- The refuting marking: `τ` a generator of `ZMod 8` (so `τ^{ω₂} = τ ≠ 1`), everything else
trivial.  The wild letters are irrelevant — `killWildLetters` overwrites them. -/
def refuteMarking (h : ℕ) : Marking (2 + 2 * h) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters 1 (Multiplicative.ofAdd 1) (fun _ => 1)

/-- A concrete marking of the `Generator (2 + 2h)` alphabet at `h = 0`, written additively:
`(σ, τ, x₀, x₁, x₂) = (5, 1, 1, 1, 1)` in `Multiplicative (ZMod 8)`. -/
def zmod8Marking : Marking (2 + 2 * 0) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 1)
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]

end GQ2.Dyadic.Words
