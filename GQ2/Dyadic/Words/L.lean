/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.Word.Fox
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.SqCore.Certificate
import GQ2.Roe.GammaR
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Dyadic campaign, ticket WL-a: the odd-degree branch word `L_sq`

**Row 1 of the R5 selection freeze** (`general_2adic/artifacts/reports/selection-freeze.md`), the
type-`L` relator at odd degree `n = 2h + 1`:

```
R^{sq}_{L,n} = (x₀^σ)⁻¹ (x₀⁻³τ)^{ω₂} x₁² [x₁, x₁^{σ₂}] · ∏_{j=1}^{(n−1)/2} [x_{2j}, x_{2j+1}]
```

with `L = 11 + n`, complexity vector `(11+n, 3, 1, 1, 3)`.  This is the **primary** type-`L` word
of the R2 decision — *not* the collector `R_{L,K}`, which is retained only as the safety-net
regression row (see the note at the end of this docstring).

## The two things this file exists to say

1. **The tree is the certificate's tree.**  `rawLsq h` is the `Export.RawWord` interchange form,
   restated in the emitted spelling of `general_2adic/generated/lean/L_sq_n{1,3,5,7}_v001.lean`,
   with all four gate-A digests pinned.  `lSqW h` is the semantic `PWord`, and
   `denote_rawLsq_*` proves it is *the denotation of the hashed tree*.

2. **At `n = 1` the word is Roe's `Γ_R` relator** (freeze row 1, SQ1).  `eval_lSqW_zero` proves
   `(Marking.ofQ2 s).eval (lSqW 0) = s.wildRelatorR` — the very word `GQ2/Roe/GammaR.lean:77`
   defines `Γ_R` by.  This is the lane's key regression and the hook AS4 wraps.

| instance | degree | handles | certificate | digest |
|---|---|---|---|---|
| `rawLsq 0` | `n = 1` | `h = 0` | `L-sq-n1-v001` | `d129037ce9617752…` |
| `rawLsq 1` | `n = 3` | `h = 1` | `L-sq-n3-v001` | `f82d892d162aaa73…` |
| `rawLsq 2` | `n = 5` | `h = 2` | `L-sq-n5-v001` | `50c5564eb7c77840…` |
| `rawLsq 3` | `n = 7` | `h = 3` | `L-sq-n7-v001` | `29c723fdfb2930f8…` |

## Authoring rules followed (WW5/S5.G template, WN0-a's distilled list)

1. **The certificate's spelling, never a normalized one.**  `.integerPower … (.int (-3))` and
   not `.inverse (.integerPower … (.int 3))`; `ω₂` through `omega2Power`; the three
   `.auxiliary` wrappers (`a`, `c`, `y1`, `sigma2`) kept, because they are hashed.
2. **The handle block is absent at `h = 0`.**  Unlike the compact-`N` row — which emits
   `HyperbolicHandles 3 0` — the `L_sq` emitter drops the node entirely at `n = 1`: the frozen
   `L-sq-n1-v001` tree has **four** children, `L-sq-n{3,5,7}` have five.  `rawLsq` therefore
   splits (`rawHandleTail`), and so does `lSqW`, or the `denote` bridge at `h = 0` is false.
   This is a real asymmetry between the two rows and not a transcription slip.
3. **Every `Multiply` is `PWord.prodList`**, including the two-letter `(x₀⁻³τ)` inside the
   `ω₂`-power: `prodList` is right-nested *onto `PWord.one`*, so writing that subword as a binary
   `PWord.mul` breaks `denote_rawLsq_zero` and nothing else.
4. **Reuse WW5's kernel pin by `rfl`.**  `rawLsq_zero : rawLsq 0 = Export.frozenLsqN1` inherits
   `Export.canonicalJson_frozenLsqN1`, so the `n = 1` tree → bytes tier is checked in the kernel
   without a second string literal to drift.
5. **`<decl>_astHash` + `#eval Export.assertAstHash`**, one pair per instance.  `native_decide`
   appears nowhere: the census must stay at eleven.
6. **Generator names by a literal `match` table** (`String.toNat?` is well-founded recursion and
   does not reduce in the kernel); handle letters come through `handleGen` instead, which is why
   the table stops at `x₁`.
7. **Boundaries stated as VALUES**, not as `= 1`.

## The `n = 1` cross-identification, and what is *not* free

`lSqW 0` and WW1's `gammaRWildWord` (`GQ2/Dyadic/Word/Fox.lean:1046`) are **different trees**,
and deliberately so: the certificate emits `x₀^{-3}` and an `n`-ary `Multiply`, whereas the `ℚ₂`
ledger of `GQ2/Roe/Words.lean` spells `(x₀³)⁻¹` and associates its product to the left.  Both
denote the same group element, and the whole gap is

* one `zpow` realignment, `x ^ (-3 : ℤ) = (x ^ (3 : ℕ))⁻¹` and `x ^ (2 : ℤ) = x ^ (2 : ℕ)`
  (`zpow_neg`/`zpow_natCast` — WL-recon's "one `norm_cast` on `IntegerPower`"), and
* associativity plus the trailing `PWord.one`s that `prodList` introduces.

Everything else — `conjR`/`conjP`, `commR`/`commP`, `omega2Pow`/`^ᶻ omega2`, `sigma2W`/`sigma2Hat`
— is `rfl`.  `eval_lSqW_zero` is the profinite headline; `evalFin_lSqW_zero` routes the same
identification through WW1's `evalFin_gammaRWildWord` to the finite ledger `wildValueR`.

## Gate C and the rank-3 core

`pro2` sends `τ ↦ 1` and collapses every `ω₂`, so `σ₂ ↦ σ` and the word becomes

```
(x₀^σ)⁻¹ x₀⁻³ x₁² [x₁, x₁^σ] · H_h  =  SqCore.sqRelWord,
```

the **rank-3 square-commutator core ⊕ handles** of the SqCore lane, whose core word is
definitionally `GQ2.drWord` (`SqCore.sqWord_eq_drWord`).  `eval_pro2_lSqW_eq_sqRelWord` is exact
at every `h`; `eval_pro2_lSqW_dsq` then says the pro-`2` specialization *is* the defining relator
of `D_sq(h)` (`SqCore.dsq_relation`), and `dsqMarking_map_sqEquivDRMarked` transports the `h = 0`
case onto Roe's `D_R` through **SQ4's `sqEquivDRMarked`** (SQ4 (vi): SQ2's `dsqEquivDR` is the
same map but its `cast` presentation blows the heartbeat budget at `isDefEq`, and carries no
generator-value lemmas).

⚠ Nothing in this file consumes the rank-3 *discharge*: `SqCore.marked_square_core_rank3` and its
two certificate consumers (`marked_square_core_rank3_certificate`,
`marked_square_core_rank3_certificate_nu_ur`) are the only B3c+B8 declarations in the SqCore lane,
and they are cited here in prose only.  Every headline below prints std-3 or smaller.

## `q_K > 2`

The `n = 1` base is structurally blind to a `q_K`-versus-`2` slip (WL-recon Q5): `ℚ₂` has
`q_K = 2`, and no `2`-group can tell `σ₂` from `σ` at all, because `ω₂` is the identity on a group
of `2`-power exponent.  The `QFour` section below lands the missing discriminator — an explicit
`q_K = 4` tame pair at which the frozen word dies and the `σ₂ → σ` mutant does not — in the shape
of F3's `√5` regression (`hom_count_distinguishes_tq_two_four`, `GQ2/Dyadic/TameBoundary.lean`).

## The collector, as a safety net only

The freeze retains the collector `R_{L,K} = h₀ u₁⁻¹ x₁^σ c₀ ∏[x_{2j},x_{2j+1}]` (draft
`eq:Lword`) as the type-`L` **safety-net regression row** — proved and Lean-checked at `n = 1`,
where it is `Marking.wildRelator` / WW1's `gammaAWildWord` — and as the shared-core reference for
the `L_tw` fallback.  Per the re-pointed WL spec it is **not** built here and WL-b/c are not
written against it: no tree, no hash, no boundary theorem for it appears below.  Should a later
regression genuinely need its display, it must be added marked regression-only.

## Implementation notes

**Not** `module`-style, and forced twice over: `GQ2.Dyadic.TameBoundary` (F3) and
`GQ2.Dyadic.SqCore.Certificate` are both plain files, and a `module` file may not import a
non-`module` one.  This matches the lane convention WN0-a ratified for `Words/` and
`Certificates/`.
-/

/- ORCHESTRATOR INTEGRATION FIX 2026-08-01: this file originally declared its shared-alphabet
toolkit in the bare `GQ2.Dyadic.Words` namespace, colliding with 20 identical names from
`Words/N0.lean` the moment `GQ2.lean` imported both (the root build broke; the WL-a audit's
build step was pipe-masked and the break surfaced via WL-b). Re-namespaced to
`GQ2.Dyadic.Words.LSq`, matching the `Words.MCompact`/`Words.Npc` pattern. The real de-dup is
the queued WAH alphabet hoist. -/
namespace GQ2.Dyadic.Words.LSq

open Export (RawWord)
open MarkedCore (handleWord)

/-! ## The odd-degree alphabet

At degree `n = 2h + 1` the word uses `x₀, x₁` and `σ, τ`, and the `h` handle pairs use
`x₂, …, x_{2h+1}`.  So the alphabet is `Generator (2h + 1)`, whose wild letters are `Fin (2h + 2)`
— exactly `x₀, …, x_n`.  The SqCore core has rank `sqRank h = 3 + 2h`: the same wild letters plus
`σ`, which is not wild.
-/

variable {h : ℕ}

/-- The core wild letters `x₀, x₁`, present at every handle count. -/
def coreLetter (h : ℕ) (i : Fin 2) : Generator (2 * h + 1) :=
  .wild ⟨(i : ℕ), by have := i.isLt; omega⟩

/-- The first letter `x_{2+2j}` of the `j`-th handle pair (`j` counted from `0`; the freeze
displays `[x_{2j}, x_{2j+1}]` with `j` from `1`). -/
def handleU {h : ℕ} (j : Fin h) : Generator (2 * h + 1) :=
  .wild ⟨2 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The second letter `x_{3+2j}` of the `j`-th handle pair. -/
def handleV {h : ℕ} (j : Fin h) : Generator (2 * h + 1) :=
  .wild ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The wild letter `x_i`, or `none` past the alphabet.  This is the `handleGen` field of the
denotation context: `Export.handleFactors` indexes handle letters by a plain `ℕ`, so the range
check lives here. -/
def wildGen (h : ℕ) (i : ℕ) : Option (Generator (2 * h + 1)) :=
  if hi : i < 2 * h + 2 then some (.wild ⟨i, by omega⟩) else none

/-- The generator names the `L_sq` certificate uses.

A literal table rather than a decimal parser: `String.toNat?` is well-founded recursion and does
**not** reduce in the kernel, so a parsing `gen` field would put the `denote` bridges below out of
reach of `rfl`.  Handle letters never come through here — they come through `wildGen` — which is
why the table stops at `x₁`. -/
def genOfName (h : ℕ) (s : String) : Option (Generator (2 * h + 1)) :=
  match s with
  | "sigma" => some .sigma
  | "tau" => some .tau
  | "x0" => wildGen h 0
  | "x1" => wildGen h 1
  | _ => none

/-- The denotation context of the `L_sq` row: the certificate's names, the handle letters, and
**no** symbolic parameters — every exponent in this row is a literal `Int` (`-3`, `2`), so `param`
is nowhere consulted and returning `none` is honest rather than lossy. -/
def denoteCtx (h : ℕ) : Export.DenoteCtx (Generator (2 * h + 1)) where
  gen := genOfName h
  handleGen := wildGen h
  param := fun _ => none

/-! ## The word -/

/-- `H_h = ∏_{j<h} [x_{2+2j}, x_{3+2j}]`, the block the certificate writes as
`HyperbolicHandles 2 h`.

Spelled as a `PWord.prodList` over `List.finRange h`, which is simultaneously what
`Export.handleFactors` expands the node to and how MC2's `handleWord` orders its factors — so both
bridges below are structural rather than a reindexing argument. -/
def handlesW (h : ℕ) : PWord (Generator (2 * h + 1)) :=
  PWord.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

@[simp] theorem handlesW_zero : handlesW 0 = .one := rfl

/-- The four core factors of `R^{sq}_{L,n}`, in the certificate's order:
`(x₀^σ)⁻¹`, `(x₀⁻³τ)^{ω₂}`, `x₁²`, `[x₁, x₁^{σ₂}]`.

Independent of `h` except through the alphabet — the degree enters only through the handle
tail. -/
noncomputable def lSqCore (h : ℕ) : List (PWord (Generator (2 * h + 1))) :=
  [.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma)),
   PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]),
   .zpow (.gen (coreLetter h 1)) 2,
   .comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) sigma2W)]

/-- The handle tail as a *list*: **empty** at `h = 0`, a single block otherwise.  The emptiness is
the certificate's, not a simplification — `L-sq-n1-v001` carries no `HyperbolicHandles` node (see
authoring rule 2). -/
def handleTail : (h : ℕ) → List (PWord (Generator (2 * h + 1)))
  | 0 => []
  | k + 1 => [handlesW (k + 1)]

/-- **The frozen odd-degree branch word** (selection freeze row 1; `R_sq(L,n)`, `n = 2h + 1`)

```
R^{sq}_{L,n} = (x₀^σ)⁻¹ (x₀⁻³τ)^{ω₂} x₁² [x₁, x₁^{σ₂}] · ∏_{j=1}^{h} [x_{2j}, x_{2j+1}]
```

The conjugator of the commutator block is **`σ₂ = σ^{ω₂}`**, not `σ`: it is what makes the block
survive into the pro-`2` core as `[x₁, x₁^σ]` while remaining invisible to every `2`-group at the
tame level, and it is the letter the `q_K = 4` pin below discriminates. -/
noncomputable def lSqW (h : ℕ) : PWord (Generator (2 * h + 1)) :=
  PWord.prodList (lSqCore h ++ handleTail h)

/-- The alphabet and the core rank line up: at degree `n = 2h + 1` the word has `n + 1` wild
letters and one `σ`, and SqCore's rank is `sqRank h = 3 + 2h = n + 2` — the freeze's "rank-3 core
⊕ handles" count.  (The freeze's word *length* `L = 11 + n` is a complexity number, not a Lean
statement, and lives in the docstring.) -/
theorem sqRank_eq_degree_add_two (h : ℕ) : SqCore.sqRank h = 2 * h + 1 + 2 := by
  simp only [SqCore.sqRank]; omega

/-! ## The certificate tree and the WW5 hash pins -/

/-- The four core children of the `L_sq` certificate tree, in the spelling emitted by
`general_2adic/generated/lean/L_sq_n{1,3,5,7}_v001.lean`.

`integerPower` with a literal `Int` (including the negative `-3`, which is *not* rewritten as an
`Inverse`); `ω₂` through `omega2Power`; the four `.auxiliary` wrappers `a`, `c`, `y1`, `sigma2`
retained, because `Auxiliary` nodes are part of the hashed bytes. -/
def rawLsqCore : List RawWord :=
  [.inverse (.conjugate (.generator "x0") (.generator "sigma")),
   .auxiliary "a"
     (.omega2Power (.multiply [.integerPower (.generator "x0") (.int (-3)), .generator "tau"])),
   .integerPower (.generator "x1") (.int 2),
   .auxiliary "c"
     (.commutator (.generator "x1")
       (.auxiliary "y1"
         (.conjugate (.generator "x1")
           (.auxiliary "sigma2" (.omega2Power (.generator "sigma"))))))]

/-- The certificate's handle tail: **no node at all** at `h = 0`, `HyperbolicHandles 2 h`
otherwise.  The hash is always of the *unexpanded* block. -/
def rawHandleTail : (h : ℕ) → List RawWord
  | 0 => []
  | k + 1 => [.hyperbolicHandles 2 (.int ((k + 1 : ℕ) : ℤ))]

/-- **The `L_sq` certificate tree** at `h` handles (degree `n = 2h + 1`). -/
def rawLsq (h : ℕ) : RawWord := .multiply (rawLsqCore ++ rawHandleTail h)

/-- The tree is well-formed in WW5's sense at every instance: nonempty names, no `etahat` entries
to be odd, no shadow parameters to be sorted.  `assertAstHash` refuses a tree that is not, so this
is the precondition of every pin below. -/
theorem wf_rawLsq (h : ℕ) : (rawLsq h).wf = true := by
  cases h with
  | zero => rfl
  | succ k => rfl

/-- **Cross-check against WW5's own kernel pin.**  `Export.frozenLsqN1` is the `n = 1` tree as WW5
typed it, and `Export.canonicalJson_frozenLsqN1` pins its canonical bytes in the kernel.  This
`rfl` inherits that pin for `rawLsq 0`, so the tree → bytes tier is checked in-kernel here too
without a second string literal to drift. -/
theorem rawLsq_zero : rawLsq 0 = Export.frozenLsqN1 := by rfl

/-- The canonical bytes of the `n = 1` instance, inherited from WW5's kernel pin. -/
theorem canonicalJson_rawLsq_zero :
    Export.canonicalJson (rawLsq 0) =
      "{\"children\":[{\"op\":\"Inverse\",\"word\":{\"conjugator\":{\"name\":\"sigma\",\"op\
      \":\"Generator\"},\"op\":\"Conjugate\",\"word\":{\"name\":\"x0\",\"op\":\"Generator\"\
      }}},{\"definition\":{\"op\":\"Omega2Power\",\"word\":{\"children\":[{\"exponent\":{\"\
      type\":\"Int\",\"value\":-3},\"op\":\"IntegerPower\",\"word\":{\"name\":\"x0\",\"op\"\
      :\"Generator\"}},{\"name\":\"tau\",\"op\":\"Generator\"}],\"op\":\"Multiply\"}},\"nam\
      e\":\"a\",\"op\":\"Auxiliary\"},{\"exponent\":{\"type\":\"Int\",\"value\":2},\"op\":\
      \"IntegerPower\",\"word\":{\"name\":\"x1\",\"op\":\"Generator\"}},{\"definition\":{\"\
      left\":{\"name\":\"x1\",\"op\":\"Generator\"},\"op\":\"Commutator\",\"right\":{\"defi\
      nition\":{\"conjugator\":{\"definition\":{\"op\":\"Omega2Power\",\"word\":{\"name\":\
      \"sigma\",\"op\":\"Generator\"}},\"name\":\"sigma2\",\"op\":\"Auxiliary\"},\"op\":\"C\
      onjugate\",\"word\":{\"name\":\"x1\",\"op\":\"Generator\"}},\"name\":\"y1\",\"op\":\"\
      Auxiliary\"}},\"name\":\"c\",\"op\":\"Auxiliary\"}],\"op\":\"Multiply\"}" := by
  rw [rawLsq_zero]
  exact Export.canonicalJson_frozenLsqN1

/-! ### The gate-A constants

One `<decl>_astHash` constant and one `#eval Export.assertAstHash` guard per frozen instance —
the WW5 convention (`pretty_lean.py`'s `HASH_SUFFIX`).  The `#eval` recomputes the digest from the
tree, so a constant cannot drift away from the word it labels, and the digests are the ones stored
in the simplification campaign's certificates, so a green elaboration is a cross-repo agreement
rather than a self-consistency check.  The `n = 1` digest is also the one
`Export.frozenRowHashes` records for row `L`. -/

/-- Gate-A hash of `rawLsq 0`, certificate `L-sq-n1-v001` — the `ℚ₂`/`Γ_R` instance, and the
digest the selection freeze quotes for row 1. -/
def rawLsq_n1_astHash : String :=
  "d129037ce96177524c5798cbe0c13d7844ab513d136360d1270dbd89e81051cb"

/-- Gate-A hash of `rawLsq 1`, certificate `L-sq-n3-v001` — the one-handle instance, which is
what makes the `h`-generality of this file testable rather than decorative. -/
def rawLsq_n3_astHash : String :=
  "f82d892d162aaa73dc0296fdd8e130365211a4592f8552b3e1052d95445fa97f"

/-- Gate-A hash of `rawLsq 2`, certificate `L-sq-n5-v001`. -/
def rawLsq_n5_astHash : String :=
  "50c5564eb7c77840cf523d98de398ca9bdfb202259ffe03f3be6ccdf058351dd"

/-- Gate-A hash of `rawLsq 3`, certificate `L-sq-n7-v001`. -/
def rawLsq_n7_astHash : String :=
  "29c723fdfb2930f8cae0fb80d25958c530f960a19f2aabd1977c4fbb68fc1268"

#eval Export.assertAstHash "WL L-sq-n1-v001" (rawLsq 0) rawLsq_n1_astHash

#eval Export.assertAstHash "WL L-sq-n3-v001" (rawLsq 1) rawLsq_n3_astHash

#eval Export.assertAstHash "WL L-sq-n5-v001" (rawLsq 2) rawLsq_n5_astHash

#eval Export.assertAstHash "WL L-sq-n7-v001" (rawLsq 3) rawLsq_n7_astHash

/-- The `n = 1` digest agrees with `Export.frozenRowHashes`, WW5's own record of the frozen
selection rows — so this file cannot invent a digest for its row. -/
theorem astHash_mem_frozenRowHashes :
    ("L (L-sq-n1-v001)", rawLsq_n1_astHash) ∈ Export.frozenRowHashes := by
  simp [Export.frozenRowHashes, rawLsq_n1_astHash]

/-! ### The `denote` bridge

What makes the hash pins bite on the *semantic* word.  `Export.denote` expands the handle block,
inlines the four auxiliaries and resolves the names; these four `rfl`s say that doing so to the
hashed tree produces exactly `lSqW`, so the `PWord` the rest of this file reasons about is the
certificate's word and not a hand-typed lookalike.

One per pinned instance, because `denote` expands `hyperbolicHandles` only at a concrete length
(wave-2 authoring rule (2)); the `h`-generic statement is not available, and inventing one would
mean re-encoding the block, which WW5 forbids. -/

theorem denote_rawLsq_zero : Export.denote (denoteCtx 0) (rawLsq 0) = some (lSqW 0) := by rfl

theorem denote_rawLsq_one : Export.denote (denoteCtx 1) (rawLsq 1) = some (lSqW 1) := by rfl

theorem denote_rawLsq_two : Export.denote (denoteCtx 2) (rawLsq 2) = some (lSqW 2) := by rfl

theorem denote_rawLsq_three : Export.denote (denoteCtx 3) (rawLsq 3) = some (lSqW 3) := by rfl

/-! ## The `ω₂`-only fragment

The `L_sq` word uses no `ℤ₂`-power and no profinite exponent other than `ω₂` (twice: on the
`a`-letter and inside `σ₂`), so the whole `ℕ`-exponent calculus of packet Lem. 2.2 applies to it
with a single global exponent.  This is what lets the numerical pins below evaluate the *genuine*
`ω₂`, and what WL-b will need to transport the word into `FreeGroup`, where `ω₂` cannot be applied
at all. -/

theorem isOmega2Only_prodList {Gen : Type*} :
    ∀ {l : List (PWord Gen)}, (∀ w ∈ l, w.IsOmega2Only) → (PWord.prodList l).IsOmega2Only
  | [], _ => trivial
  | w :: _ws, hw =>
      ⟨hw w (List.mem_cons_self ..),
       isOmega2Only_prodList fun u hu => hw u (List.mem_cons_of_mem _ hu)⟩

@[simp] theorem isOmega2Only_handlesW (h : ℕ) : (handlesW h).IsOmega2Only := by
  unfold handlesW
  refine isOmega2Only_prodList ?_
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact ⟨trivial, trivial⟩

@[simp] theorem isOmega2Only_lSq (h : ℕ) : (lSqW h).IsOmega2Only := by
  refine isOmega2Only_prodList ?_
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · simp only [lSqCore, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp [PWord.prodList]
  · cases h with
    | zero => simp only [handleTail, List.not_mem_nil] at hw
    | succ k =>
        simp only [handleTail, List.mem_cons, List.not_mem_nil, or_false] at hw
        rw [hw]; exact isOmega2Only_handlesW (k + 1)

/-! ## The master evaluation

Everything downstream — both boundaries, the `Γ_R` identification and every numerical pin — is a
substitution into this one identity.  The right-hand side is the freeze's display, read with the
campaign conventions `x^g = g⁻¹xg`, `[x,y] = x⁻¹y⁻¹xy`, `σ₂ = σ^{ω₂}`, and left-associated. -/

section Eval

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- `prodList` of a concatenation evaluates factorwise. -/
theorem eval_prodList_append {Gen : Type*} (μ : Gen → G) (l₁ l₂ : List (PWord Gen)) :
    PWord.eval μ (PWord.prodList (l₁ ++ l₂))
      = PWord.eval μ (PWord.prodList l₁) * PWord.eval μ (PWord.prodList l₂) := by
  rw [PWord.eval_prodList, PWord.eval_prodList, PWord.eval_prodList, List.map_append,
    List.prod_append]

/-- Evaluating the handle block is MC2's `handleWord` on the handle letters — the same
`List.finRange h` order on both sides, so this is a rewrite and not a reindexing. -/
theorem eval_handlesW (t : Marking (2 * h + 1) G) :
    t.eval (handlesW h) = handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  rw [Marking.eval_def, handlesW, PWord.eval_prodList, List.map_map]
  rfl

/-- The handle *tail* evaluates to the handle block at every `h`, empty list and all. -/
theorem eval_handleTail (t : Marking (2 * h + 1) G) :
    PWord.eval ⇑t (PWord.prodList (handleTail h)) = t.eval (handlesW h) := by
  cases h with
  | zero => rfl
  | succ k =>
      rw [handleTail, PWord.prodList_cons, PWord.prodList_nil, PWord.eval_mul, PWord.eval_one,
        mul_one]
      rfl

/-- **The frozen `L_sq` word, evaluated.**  At every marking and every handle count,

```
R^{sq}_{L,n} ↦ (x₀^σ)⁻¹ · (x₀^{-3} τ)^{ω₂} · x₁² · [x₁, x₁^{σ^{ω₂}}] · H_h.
```

The `ℤ`-exponents `-3` and `2` are the certificate's; realigning them with the `ℕ`-exponents of
the `ℚ₂` ledger and of `SqCore.sqWord` is the one `norm_cast`-flavoured step of this file, and it
happens downstream, never here. -/
theorem eval_lSqW (t : Marking (2 * h + 1) G) :
    t.eval (lSqW h) =
      (conjR (t (coreLetter h 0)) t.σ)⁻¹ * (t (coreLetter h 0) ^ (-3 : ℤ) * t.τ) ^ᶻ omega2 *
        t (coreLetter h 1) ^ (2 : ℤ) *
        commR (t (coreLetter h 1)) (conjR (t (coreLetter h 1)) (t.σ ^ᶻ omega2)) *
        t.eval (handlesW h) := by
  rw [Marking.eval_def, lSqW, eval_prodList_append, eval_handleTail, lSqCore]
  simp only [PWord.eval_prodList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_omega2PowHat, PWord.eval_zpow,
    PWord.eval_comm, mul_one, Marking.apply_sigma, Marking.apply_tau, sigma2W, mul_assoc]

end Eval

/-! ### The exponent realignment

The one `norm_cast`-flavoured move of the file, isolated (WL-recon: "the sole bridge is one
`norm_cast` on `IntegerPower`").  The certificate carries genuine `ℤ`-powers `-3` and `2`; the
`ℚ₂` ledger of `GQ2/Roe/Words.lean` and `SqCore.sqWord` carry `ℕ`-powers `(x³)⁻¹` and `y²`, and
WW1's reflected tree carries the `ℤ`-power `(x^(3:ℤ))⁻¹`.  `group` bridges none of these on its
own: it will not match `3` against `↑3` across the `zpow`/`npow` boundary. -/

/-- `x^{-3} = (x³)⁻¹` with an `ℕ`-exponent on the right — the `ledger`/`sqWord` form. -/
theorem zpow_neg_three {H : Type*} [Group H] (x : H) : x ^ (-3 : ℤ) = (x ^ (3 : ℕ))⁻¹ := by
  rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]

/-- `x^{-3} = (x³)⁻¹` with the exponent kept in `ℤ` — the form WW1's reflected tree uses. -/
theorem zpow_neg_three_int {H : Type*} [Group H] (x : H) : x ^ (-3 : ℤ) = (x ^ (3 : ℤ))⁻¹ :=
  zpow_neg x 3

/-- The twin on the square. -/
theorem zpow_two {H : Type*} [Group H] (x : H) : x ^ (2 : ℤ) = x ^ (2 : ℕ) := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]

/-! ## Gate B: the tame boundary

Packet Prop. 9.2's proof shape.  Killing the wild letters annihilates the conjugate `(x₀^σ)⁻¹`,
the square `x₁²`, the commutator block and every handle; what survives is the `ω₂`-tail of the
`a`-letter, `a = (x₀⁻³τ)^{ω₂} ↦ τ^{ω₂}`.  That tail then dies by **Gate B rule T1** — `ω₂` kills
pro-odd elements — and *only* by T1: it is not a syntactic cancellation.

Stating the *value* rather than "`= 1`" is deliberate; it is what makes the T1 step visible, and
what shows that the death of this word at the tame boundary is a fact about `τ`, not about the
word's shape. -/

section Tame

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The tame boundary value of the `L_sq` word** — exactly `τ^{ω₂}`, at every degree. -/
theorem eval_killWildLetters_lSq (h : ℕ) (t : Marking (2 * h + 1) G) :
    (Marking.killWildLetters t).eval (lSqW h) = t.τ ^ᶻ omega2 := by
  have hH : (Marking.killWildLetters t).eval (handlesW h) = 1 := by
    rw [eval_handlesW]
    exact MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)
  rw [eval_lSqW, hH]
  simp only [show ∀ i, (Marking.killWildLetters t) (coreLetter h i) = 1 from fun _ => rfl,
    Marking.killWildLetters_τ, Marking.killWildLetters_σ,
    one_zpow, one_mul, mul_one, one_conjR, inv_one, commR_self]

/-- The same statement through F2's **substitution operator**: the syntactic kill-wild rewrite
`killWild` evaluated at `t` (`Marking.eval_killWild`). -/
theorem eval_killWild_lSq (h : ℕ) (t : Marking (2 * h + 1) G) :
    t.eval (killWild (lSqW h)) = t.τ ^ᶻ omega2 := by
  rw [Marking.eval_killWild, eval_killWildLetters_lSq]

/-- **Gate-B admissibility, relativized to a tame `τ`** — packet Prop. 9.2.

The `L_sq` word dies at the tame boundary of every marking whose `τ`-letter is killed by `ω₂`.
Inside `Γ_R` that hypothesis is *supplied*, by packet Lem. 3.1: the tame relation `τ^σ = τ^{q_K}`
with `q_K` even forces `τ` to be pro-odd (`GQ2.Dyadic.odd_order`), and `ω₂` kills pro-odd
elements.  This — never the bare `KillsWild` — is the route branch lanes use (WN0-a's ruling). -/
theorem killsWild_of_tau {h : ℕ}
    (hτ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      [TotallyDisconnectedSpace G] (t : Marking (2 * h + 1) G), t.τ ^ᶻ omega2 = 1) :
    KillsWild (lSqW h) := by
  intro G _ _ _ _ _ t
  rw [eval_killWildLetters_lSq]
  exact hτ G t

/-- **Gate B rule T1, at a finite marking**: if the `τ`-letter has odd order, the tame boundary
value is trivial.  This is the form the finite-target harnesses (F5) test. -/
theorem eval_killWildLetters_lSq_eq_one_of_odd {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] (h : ℕ) (t : Marking (2 * h + 1) P)
    (hτ : Odd (orderOf t.τ)) : (Marking.killWildLetters t).eval (lSqW h) = 1 := by
  rw [eval_killWildLetters_lSq]
  simpa using PWord.eval_omega2Pow_eq_one_of_odd (⇑t) (.gen .tau) hτ

end Tame

/-! ### ⚠ F3's `KillsWild` is *not* satisfiable by this word either

WN0-a's finding, reproduced verbatim on the `L_sq` row, which is what makes it lane-wide rather
than a compact-`N` accident.

`GQ2.Dyadic.KillsWild R` quantifies over **every** profinite group and **every** marking, with no
relation imposed on the `τ`-letter.  By `eval_killWildLetters_lSq` the tame boundary value of
`L_sq` is `τ^{ω₂}`, so `KillsWild` would force `τ^{ω₂} = 1` universally — false already in
`Multiplicative (ZMod 8)`.

This is not a defect in the *word*: the packet's hypothesis is about the tame quotient, where `τ`
is pro-odd by Lem. 3.1, and there the word is admissible (`killsWild_of_tau`,
`eval_killWildLetters_lSq_eq_one_of_odd`).  It is a mismatch between F3's `∀`-form and the
packet's hypothesis, and every branch word carrying a `(x_iτ)^{ω₂}`-shaped letter hits it.
Recorded, not acted on (micro-row **F3b**): `TameBoundary.lean` is not this ticket's file. -/

section Refutation

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

private theorem zmod8_orderOf_dvd (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- The refuting marking: `τ` a generator of `ZMod 8` (so `τ^{ω₂} = τ ≠ 1`), everything else
trivial.  The wild letters are irrelevant — `killWildLetters` overwrites them. -/
def refuteMarking (h : ℕ) : Marking (2 * h + 1) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters 1 (Multiplicative.ofAdd 1) (fun _ => 1)

/-- **The frozen `L_sq` word is not Gate-B admissible in F3's unrelativized sense.** -/
theorem not_killsWild (h : ℕ) : ¬ KillsWild (lSqW h) := by
  intro hR
  have hval := hR (Multiplicative (ZMod 8)) (refuteMarking h)
  rw [eval_killWildLetters_lSq,
    PWord.zpowHat_omega2_zpow (by norm_num) (zmod8_orderOf_dvd _), omega2Exp_eight,
    show (refuteMarking h).τ = Multiplicative.ofAdd (1 : ZMod 8) from rfl, Nat.cast_one,
    zpow_one] at hval
  exact absurd hval (by decide)

end Refutation

/-! ## Gate C: the marked pro-`2` boundary — the rank-3 square-commutator core

`pro2` sends `τ ↦ 1` and collapses every `ω₂`-power, so `σ₂ ↦ σ` and the `a`-letter loses its
tame factor:

```
(x₀^σ)⁻¹ (x₀⁻³τ)^{ω₂} x₁² [x₁, x₁^{σ₂}] · H_h  ↦  (x₀^σ)⁻¹ x₀⁻³ x₁² [x₁, x₁^σ] · H_h,
```

which is `SqCore.sqWord σ x₀ x₁ · H_h` = `SqCore.sqRelWord`, the rank-3 core ⊕ handles.  The core
is definitionally `GQ2.drWord` (`SqCore.sqWord_eq_drWord`), which at `h = 0` is why the pro-`2`
specialization of the `n = 1` word is Roe's pro-`2` relator.

The only non-associativity move is the exponent realignment `x₀^{-3} = (x₀^3)⁻¹` — the certificate
carries a genuine `ℤ`-power, the core word an `ℕ`-power. -/

section Pro2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

theorem pro2_prodList :
    ∀ l : List (PWord (Generator (2 * h + 1))),
      pro2 (PWord.prodList l) = PWord.prodList (l.map pro2)
  | [] => rfl
  | w :: ws => by
      rw [PWord.prodList_cons, pro2_mul, pro2_prodList ws, List.map_cons, PWord.prodList_cons]

@[simp] theorem pro2_handlesW (h : ℕ) : pro2 (handlesW h) = handlesW h := by
  rw [handlesW, pro2_prodList, List.map_map]
  rfl

/-- **Gate C, syntactically**: `τ` is gone, both `ω₂`-powers are collapsed (`σ₂ ↦ σ`), nothing else
moves.  The `a`-letter becomes `x₀^{-3} · (1 · 1)`, whose trailing `1`s are the collapsed `τ` and
`prodList`'s unit. -/
theorem pro2_lSqCore (h : ℕ) :
    (lSqCore h).map pro2 =
      [.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma)),
       PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .one],
       .zpow (.gen (coreLetter h 1)) 2,
       .comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) (.gen .sigma))] := by
  simp only [lSqCore, List.map_cons, List.map_nil, pro2_inv, pro2_conj, pro2_gen_wild,
    pro2_gen_sigma, pro2_omega2Pow, pro2_prodList, pro2_zpow, pro2_gen_tau, pro2_comm,
    pro2_sigma2W, coreLetter]

/-- **The pro-`2` boundary value of the `L_sq` word is the rank-3 square-commutator core ⊕
handles.**  At *every* marking and every `h`: no hypothesis is needed, because `pro2` has already
removed `τ` and both `ω₂`s, so the identity is one of plain group words. -/
theorem eval_pro2_lSqW (h : ℕ) (t : Marking (2 * h + 1) G) :
    t.eval (pro2 (lSqW h)) =
      SqCore.sqWord t.σ (t (coreLetter h 0)) (t (coreLetter h 1)) *
        handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  have hH : PWord.eval ⇑t (PWord.prodList ((handleTail h).map pro2))
      = handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
    cases h with
    | zero => rw [handleTail]; rfl
    | succ k =>
        rw [handleTail, List.map_cons, List.map_nil, PWord.prodList_cons, PWord.prodList_nil,
          PWord.eval_mul, PWord.eval_one, mul_one, pro2_handlesW,
          show PWord.eval ⇑t (handlesW (k + 1)) = t.eval (handlesW (k + 1)) from rfl,
          eval_handlesW]
  rw [Marking.eval_def, lSqW, pro2_prodList, List.map_append, eval_prodList_append, hH,
    pro2_lSqCore]
  simp only [PWord.eval_prodList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_zpow, PWord.eval_comm,
    PWord.eval_one, mul_one, Marking.apply_sigma]
  rw [zpow_neg_three, zpow_two, SqCore.sqWord]
  simp only [conjR, commR, GQ2.conjP, GQ2.commP, mul_assoc]

/-- At `h = 0` the handle tail is empty and the pro-`2` value is the bare rank-3 core word — the
statement the ticket asks for, and the one SqCore's rank-3 theory consumes. -/
theorem eval_pro2_lSqW_zero (t : Marking 1 G) :
    t.eval (pro2 (lSqW 0)) = SqCore.sqWord t.σ (t.x 0) (t.x 1) := by
  rw [eval_pro2_lSqW (h := 0) (t := t),
    show handleWord (fun j : Fin 0 => t (handleU j)) (fun j : Fin 0 => t (handleV j)) = 1 from rfl,
    mul_one]
  rfl

end Pro2

/-! ### The letter correspondence

`σ ↦ 0`, `x_i ↦ i + 1` — simultaneously SqCore's core ordering (`σ, x₀, x₁` at `0, 1, 2`) and its
handle ordering (`x_{2+2j}, x_{3+2j}` at `sqHandleIdxU/V j = 3 + 2j, 4 + 2j`).  A marking carries
no algebraic structure, so this whole block is instance-free. -/

section SqIndex

variable {G : Type*}

/-- The core index of a wild letter: `σ` sits at `0` and `x_i` at `i + 1`. -/
def sqIdxMark (t : Marking (2 * h + 1) G) : Fin (SqCore.sqRank h) → G := fun i =>
  if (i : ℕ) = 0 then t.σ
  else t.x ⟨(i : ℕ) - 1, by have := i.isLt; simp only [SqCore.sqRank] at this; omega⟩

@[simp] theorem sqIdxMark_zero (t : Marking (2 * h + 1) G) : sqIdxMark t 0 = t.σ := by
  simp only [sqIdxMark, SqCore.sqVal_zero]
  norm_num

@[simp] theorem sqIdxMark_one (t : Marking (2 * h + 1) G) :
    sqIdxMark t 1 = t (coreLetter h 0) := by
  rw [sqIdxMark, if_neg (by rw [SqCore.sqVal_one]; omega)]
  exact congrArg t (congrArg Generator.wild
    (Fin.ext (by simp only [SqCore.sqVal_one]; rfl)))

@[simp] theorem sqIdxMark_two (t : Marking (2 * h + 1) G) :
    sqIdxMark t 2 = t (coreLetter h 1) := by
  rw [sqIdxMark, if_neg (by rw [SqCore.sqVal_two]; omega)]
  exact congrArg t (congrArg Generator.wild
    (Fin.ext (by simp only [SqCore.sqVal_two]; rfl)))

@[simp] theorem sqIdxMark_handleU (t : Marking (2 * h + 1) G) (j : Fin h) :
    sqIdxMark t (SqCore.sqHandleIdxU j) = t (handleU j) := by
  rw [sqIdxMark, if_neg (by rw [SqCore.sqHandleIdxU_val]; omega)]
  exact congrArg t (congrArg Generator.wild
    (Fin.ext (by simp only [SqCore.sqHandleIdxU_val]; omega)))

@[simp] theorem sqIdxMark_handleV (t : Marking (2 * h + 1) G) (j : Fin h) :
    sqIdxMark t (SqCore.sqHandleIdxV j) = t (handleV j) := by
  rw [sqIdxMark, if_neg (by rw [SqCore.sqHandleIdxV_val]; omega)]
  exact congrArg t (congrArg Generator.wild
    (Fin.ext (by simp only [SqCore.sqHandleIdxV_val]; omega)))

end SqIndex

section Pro2Core

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The headline of Gate C**: the pro-`2` specialization of the frozen `L_sq` word *is*
`SqCore.sqRelWord`, the rank-3 square-commutator relator shape at rank `sqRank h = 3 + 2h`, read
through the letter correspondence `σ ↦ 0`, `x_i ↦ i + 1`. -/
theorem eval_pro2_lSqW_eq_sqRelWord (h : ℕ) (t : Marking (2 * h + 1) G) :
    t.eval (pro2 (lSqW h)) = SqCore.sqRelWord (sqIdxMark t) := by
  rw [eval_pro2_lSqW, SqCore.sqRelWord, sqIdxMark_zero, sqIdxMark_one, sqIdxMark_two]
  simp only [sqIdxMark_handleU, sqIdxMark_handleV]

end Pro2Core

/-! ### The pro-`2` specialization is a relator of `D_sq`

`SqCore.dsq_relation` says `sqRelWord` dies at the marked generators of `D_sq(h)`; through
`eval_pro2_lSqW_eq_sqRelWord` that is the statement that the *word this file pins* presents the
rank-3 core.  At `h = 0` it lands on Roe's `D_R` through SQ4's marked equivalence. -/

section Presented

/-- The `L_sq`-alphabet marking of `D_sq(h)`: `σ` and the wild letters at their SqCore generators,
`τ ↦ 1` (there is no tame letter in a pro-`2` core). -/
noncomputable def dsqMarking (h : ℕ) : Marking (2 * h + 1) (SqCore.DSq h : Type) :=
  Marking.ofLetters (SqCore.dsqSigma h) 1
    (fun i => SqCore.sqGen h ⟨(i : ℕ) + 1, by have := i.isLt; simp only [SqCore.sqRank]; omega⟩)

theorem sqIdxMark_dsqMarking (h : ℕ) : sqIdxMark (dsqMarking h) = SqCore.sqGen h := by
  funext i
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
  · rw [sqIdxMark, if_pos h0]
    exact congrArg (SqCore.sqGen h) (Fin.ext h0.symm)
  · rw [sqIdxMark, if_neg (by omega)]
    show SqCore.sqGen h _ = SqCore.sqGen h i
    exact congrArg (SqCore.sqGen h) (Fin.ext (by simp; omega))

/-- **The frozen `L_sq` word's pro-`2` specialization is the defining relator of the rank-3
square-commutator core `D_sq(h)`**, at every odd degree `n = 2h + 1`. -/
theorem eval_pro2_lSqW_dsq (h : ℕ) : (dsqMarking h).eval (pro2 (lSqW h)) = 1 := by
  rw [eval_pro2_lSqW_eq_sqRelWord, sqIdxMark_dsqMarking]
  exact SqCore.dsq_relation h

/-- The `L_sq`-alphabet marking of Roe's pro-`2` group `D_R` (note eq. (3.1)). -/
noncomputable def drMarking : Marking 1 (DR : Type) :=
  Marking.ofLetters drS 1 ![drX, drY]

/-- **SQ4's marked identification, on this file's markings**: `D_sq(0) ≅ D_R` carries the `L_sq`
marking of the core onto the Roe marking, letter for letter.

Stated against `SqCore.sqEquivDRMarked` and not SQ2's `dsqEquivDR`: the two are *the same map*,
but only this one has generator-value theorems, and the `cast` presentation of `dsqEquivDR` blows
the heartbeat budget at `isDefEq` (SQ4 outcome (vi)). -/
theorem dsqMarking_map_sqEquivDRMarked :
    (dsqMarking 0).map ⇑SqCore.sqEquivDRMarked = drMarking := by
  ext g
  cases g with
  | sigma => exact SqCore.sqToDR_sigma
  | tau => exact SqCore.sqEquivDRMarked.map_one
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => exact SqCore.sqToDR_x0
      | 1, _ => exact SqCore.sqToDR_x1

/-- **The `n = 1` pro-`2` specialization is Roe's relator `r₂`.**  `pro2 (lSqW 0)` evaluates at the
Roe marking of `D_R` to `drWord drS drX drY = 1` (`GQ2.dr_relation`) — the pro-`2` half of "at
`n = 1` the `L_sq` word is `Γ_R`". -/
theorem eval_pro2_lSqW_zero_dr : drMarking.eval (pro2 (lSqW 0)) = 1 := by
  rw [eval_pro2_lSqW_zero, show drMarking.σ = drS from rfl, show drMarking.x 0 = drX from rfl,
    show drMarking.x 1 = drY from rfl, SqCore.sqWord_eq_drWord]
  exact dr_relation

end Presented

/-! ## `n = 1`: the word **is** Roe's `Γ_R` relator

The lane's key regression (freeze row 1, SQ1).  `GQ2/Roe/GammaR.lean:77` defines

```
r_R = (x₀^σ)⁻¹ · a · x₁² · c,   a = ((x₀³)⁻¹τ)^{ω₂},  c = [x₁, x₁^{σ₂}],  σ₂ = σ^{ω₂}
```

and `Γ_R = F₄ ⧸ N_R` is the marked quotient killing exactly that word.  The `L_sq` certificate at
`n = 1` denotes it — after the two `zpow` realignments and associativity, and nothing else. -/

section GammaR

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The `n = 1` cross-identification** (freeze row 1; SQ1): the frozen `L_sq` word denotes the
Roe wild relator `Marking.wildRelatorR`, the word `Γ_R` is defined by.

The only content beyond `rfl` is `zpow_neg_three` (the certificate's `x₀^{-3}` against the
ledger's `(x₀³)⁻¹`), `zpow_two`, and the reassociation `prodList` forces. -/
theorem eval_lSqW_zero (s : _root_.GQ2.Marking G) :
    (Marking.ofQ2 s).eval (lSqW 0) = s.wildRelatorR := by
  rw [eval_lSqW (h := 0) (t := Marking.ofQ2 s),
    show (Marking.ofQ2 s).eval (handlesW 0) = 1 from rfl, mul_one,
    zpow_neg_three, zpow_two,
    show (Marking.ofQ2 s) (coreLetter 0 0) = s.x₀ from rfl,
    show (Marking.ofQ2 s) (coreLetter 0 1) = s.x₁ from rfl,
    show (Marking.ofQ2 s).σ = s.σ from rfl, show (Marking.ofQ2 s).τ = s.τ from rfl]
  simp only [_root_.GQ2.Marking.wildRelatorR, _root_.GQ2.Marking.aRHat,
    _root_.GQ2.Marking.cRHat, _root_.GQ2.Marking.y1RHat, _root_.GQ2.Marking.sigma2Hat,
    conjR, commR, _root_.GQ2.conjP, _root_.GQ2.commP]

/-- **Relator for relator**: the `L_sq` word at `n = 1` dies in a finite quotient exactly when the
pushed marking satisfies the Roe wild relation `WildRelR` — so `Γ_R`'s `R`-admissibility may be
read off this word.  This is the hook AS4 wraps. -/
theorem eval_lSqW_zero_eq_one_iff {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P]
    [Finite P] (f : ContinuousMonoidHom G P) (s : _root_.GQ2.Marking G) :
    f.toMonoidHom ((Marking.ofQ2 s).eval (lSqW 0)) = 1
      ↔ (s.map f.toMonoidHom).WildRelR := by
  rw [eval_lSqW_zero]
  exact _root_.GQ2.Marking.map_wildRelatorR_eq_one_iff f s

/-- **The WW1 route**: the same identification through the `evalFin` evaluator, landing on the
`Γ_R` tree `gammaRWildWord` that WW1 built from the `GQ2/Roe/Words.lean` ledger.  The two trees are
*not* equal — WW1 mirrors the ledger's `(x₀³)⁻¹` and left association, this file mirrors the
certificate's `x₀^{-3}` and `n`-ary `Multiply` — so this is the statement that the certificate's
spelling and the ledger's spelling are one word. -/
theorem evalFin_lSqW_zero {P : Type} [Group P] (s : _root_.GQ2.Marking P) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (⇑(Marking.ofQ2 s)) E E₂ (lSqW 0)
      = PWord.evalFin (⇑(Marking.ofQ2 s)) E E₂ gammaRWildWord := by
  rw [gammaRWildWord, aRWordQ2, cRWordQ2, y1RWordQ2, lSqW]
  simp only [handleTail, List.append_nil, lSqCore, PWord.prodList_cons, PWord.prodList_nil,
    sigma2W, PWord.evalFin_mul, PWord.evalFin_inv, PWord.evalFin_conj,
    PWord.evalFin_comm, PWord.evalFin_zpow, PWord.evalFin_omega2Pow, PWord.evalFin_gen,
    PWord.evalFin_one, mul_one, mul_assoc,
    show coreLetter 0 0 = (Generator.wild 0 : Generator 1) from rfl,
    show coreLetter 0 1 = (Generator.wild 1 : Generator 1) from rfl]
  rw [zpow_neg_three_int]

/-- Chained with WW1's `evalFin_gammaRWildWord`: the `L_sq` word at `n = 1` computes the finite
`ℚ₂` ledger value `wildValueR` of `GQ2/Roe/Words.lean`. -/
theorem evalFin_lSqW_zero_eq_wildValueR {P : Type} [Group P] (s : _root_.GQ2.Marking P)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (⇑(Marking.ofQ2 s)) E E₂ (lSqW 0) = s.wildValueR := by
  rw [evalFin_lSqW_zero, evalFin_gammaRWildWord]

end GammaR

/-! ## The mandated `q_K > 2` pin

WL-recon Q5.  The `n = 1` base is `ℚ₂`, where `q_K = 2`, and it is structurally blind to a
`q_K`-versus-`2` slip; worse, **no `2`-group can see the `σ₂`-versus-`σ` choice at all**, because
`ω₂` acts as the identity on a group of `2`-power exponent, so `σ₂ = σ` there identically.  A
discriminating pin therefore needs a target with a nontrivial odd part *and* an honest `q_K = 4`
tame pair — `q_K = 4` being the residue cardinality of `ℚ₂(√5)`, the only `q ≠ 2` entry in the
campaign's quadratic table (F3's `hom_count_distinguishes_tq_two_four`).

The target is `D₅ × D₃` (order 60, exponent 30):

* `τ = (r 1, 1)` has order `5`, and `σ = (sr 0, r 1)` inverts it: `τ^σ = τ⁴`, while `τ^σ ≠ τ²` —
  a genuine `q_K = 4` pair, and **not** a `q_K = 2` one;
* `σ` has order `6`, so `σ₂ = σ^{ω₂} = σ³ = (sr 0, 1) ≠ σ`: the `ω₂` in `σ₂` is doing work;
* at `x₀ = 1`, `x₁ = (1, sr 0)` the frozen word **dies**, because `x₁^{σ₂} = x₁`;
* the `σ₂ → σ` mutant does **not** die — `[x₁, x₁^σ] = (1, r 1) ≠ 1`.

So a lane that silently replaced `σ₂` by `σ` would break admissibility at a `q_K = 4` target while
remaining invisible at every `ℚ₂` and every `2`-group pin in this file. -/

section QFour

/-- The `q_K = 4` test target `D₅ × D₃`: order `60`, exponent `30`, odd part `15`. -/
abbrev QFour : Type := DihedralGroup 5 × DihedralGroup 3

local instance : TopologicalSpace QFour := ⊥
local instance : DiscreteTopology QFour := ⟨rfl⟩

/-- `ω₂` is represented by `15` on a group of exponent `30`: `15 ≡ 1 (mod 2)` and
`15 ≡ 0 (mod 15)`. -/
theorem omega2Exp_thirty : omega2Exp 30 = 15 := by
  have h15 : (15 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have hfac : (30 : ℕ).factorization 2 = 1 := by
    rw [show (30 : ℕ) = 2 * 15 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization Nat.prime_two, h15]
  norm_num [omega2Exp, hfac]

/-- Every element of `D₅ × D₃` is killed by `30`: `D₅` has exponent `10`, `D₃` exponent `6`.
Split componentwise rather than by a single `decide` over the `60` elements, which exhausts the
kernel's recursion budget. -/
private theorem qFour_pow_thirty (x : QFour) : x ^ 30 = 1 := by
  obtain ⟨a, b⟩ := x
  have ha : a ^ 10 = 1 := by revert a; decide
  have hb : b ^ 6 = 1 := by revert b; decide
  have ha30 : a ^ 30 = 1 := by rw [show (30 : ℕ) = 10 * 3 by norm_num, pow_mul, ha, one_pow]
  have hb30 : b ^ 30 = 1 := by rw [show (30 : ℕ) = 6 * 5 by norm_num, pow_mul, hb, one_pow]
  show ((a ^ 30, b ^ 30) : QFour) = 1
  rw [ha30, hb30]
  rfl

private theorem qFour_orderOf_dvd (x : QFour) : orderOf x ∣ 30 :=
  orderOf_dvd_of_pow_eq_one (qFour_pow_thirty x)

/-- The `q_K = 4` marking: `σ = (sr 0, r 1)`, `τ = (r 1, 1)`, `x₀ = 1`, `x₁ = (1, sr 0)`. -/
def qFourMarking : Marking (2 * 0 + 1) QFour :=
  Marking.ofLetters (DihedralGroup.sr 0, DihedralGroup.r 1) (DihedralGroup.r 1, 1)
    ![1, (1, DihedralGroup.sr 0)]

/-- **The target is a `q_K = 4` tame pair.**  `τ^σ = τ⁴`. -/
theorem qFour_tameRel : conjR qFourMarking.τ qFourMarking.σ = qFourMarking.τ ^ (4 : ℕ) := by
  decide

/-- **…and not a `q_K = 2` one.**  `τ^σ ≠ τ²`, so this pin genuinely separates `q_K = 4` from the
`ℚ₂` base — F3's `hom_count_distinguishes_tq_two_four` in the shape the word can feel. -/
theorem qFour_not_tameRel_two :
    conjR qFourMarking.τ qFourMarking.σ ≠ qFourMarking.τ ^ (2 : ℕ) := by
  decide

/-- The tame letter is killed by `5` (it is the rotation `r 1` of `D₅`). -/
theorem qFour_tau_pow_five : qFourMarking.τ ^ 5 = 1 := by decide

/-- …so it is pro-odd, and `killsWild_of_tau`'s hypothesis holds here: `τ^{ω₂}` is trivial and the
word's tame boundary vanishes.  Tame inertia being pro-odd is exactly packet Lem. 3.1's content,
and it is what a `q_K = 4` branch supplies just as the `q_K = 2` one does. -/
theorem qFour_tau_odd : Odd (orderOf qFourMarking.τ) := by
  have h5 : orderOf qFourMarking.τ ∣ 5 := orderOf_dvd_of_pow_eq_one qFour_tau_pow_five
  refine Nat.odd_iff.mpr ?_
  by_contra hc
  exact absurd ((Nat.dvd_of_mod_eq_zero (by omega : orderOf qFourMarking.τ % 2 = 0)).trans h5)
    (by norm_num)

/-- **`σ₂` is the `2`-part of `σ`**: `σ = (sr 0, r 1)` has order `6`, and `ω₂` projects it onto
`(sr 0, 1)`.  Pinned as a value so the claim is checked rather than asserted. -/
theorem qFour_sigma2 :
    qFourMarking.σ ^ᶻ omega2 = ((DihedralGroup.sr 0, 1) : QFour) := by
  rw [PWord.zpowHat_omega2_zpow (by norm_num) (qFour_orderOf_dvd _), omega2Exp_thirty]
  decide

/-- **`σ₂ ≠ σ`** — the fact no `2`-group can witness, since `ω₂` is the identity on a group of
`2`-power exponent. -/
theorem qFour_sigma2_ne_sigma : qFourMarking.σ ^ᶻ omega2 ≠ qFourMarking.σ := by
  rw [qFour_sigma2]; decide

/-- **The frozen word dies at the `q_K = 4` marking.** -/
theorem eval_qFour_lSq : qFourMarking.eval (lSqW 0) = 1 := by
  rw [Marking.eval_def, PWord.eval_eq_evalNat_of_dvd (by norm_num) qFour_orderOf_dvd,
    omega2Exp_thirty]
  · decide
  · exact isOmega2Only_lSq 0

/-- The `σ₂ → σ` **mutant** of the frozen word: the `L_sq` core with the commutator block
conjugated by the bare `σ`.  Not a certificate word — it carries no hash and is used only to
witness that the `σ₂`-slot is load-bearing. -/
noncomputable def lSqSigmaSlipW (h : ℕ) : PWord (Generator (2 * h + 1)) :=
  PWord.prodList
    ([.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma)),
      PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]),
      .zpow (.gen (coreLetter h 1)) 2,
      .comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) (.gen .sigma))]
      ++ handleTail h)

@[simp] theorem isOmega2Only_lSqSigmaSlip (h : ℕ) : (lSqSigmaSlipW h).IsOmega2Only := by
  refine isOmega2Only_prodList ?_
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp [PWord.prodList]
  · cases h with
    | zero => simp only [handleTail, List.not_mem_nil] at hw
    | succ k =>
        simp only [handleTail, List.mem_cons, List.not_mem_nil, or_false] at hw
        rw [hw]; exact isOmega2Only_handlesW (k + 1)

/-- **…and the mutant does not.**  Its value is the `D₃`-rotation `[x₁, x₁^σ] = (1, r 1)`, so a
slip from `σ₂` to `σ` is detected at this `q_K = 4` target — and, by `qFour_sigma2_ne_sigma`, only
at a target whose `σ` has a nontrivial odd part. -/
theorem eval_qFour_lSqSigmaSlip :
    qFourMarking.eval (lSqSigmaSlipW 0) = ((1, DihedralGroup.r 1) : QFour) := by
  rw [Marking.eval_def, PWord.eval_eq_evalNat_of_dvd (by norm_num) qFour_orderOf_dvd,
    omega2Exp_thirty]
  · decide
  · exact isOmega2Only_lSqSigmaSlip 0

/-- The mutant is not a relator here. -/
theorem eval_qFour_lSqSigmaSlip_ne_one : qFourMarking.eval (lSqSigmaSlipW 0) ≠ 1 := by
  rw [eval_qFour_lSqSigmaSlip]; decide

/-- The pin, in one line: at a `q_K = 4` marking the frozen word and its `σ₂ → σ` mutant have
*different* values. -/
theorem lSq_ne_lSqSigmaSlip_at_qFour :
    qFourMarking.eval (lSqW 0) ≠ qFourMarking.eval (lSqSigmaSlipW 0) := by
  rw [eval_qFour_lSq]
  exact fun hc => eval_qFour_lSqSigmaSlip_ne_one hc.symm

end QFour

/-! ## Numerical stress pins

Nothing below is cited by a proof; these are regression pins in the sense of plan §3 A1.

**The python twins are F5's rows** (`scripts/dyadic_sanity_counts.py`).  Those counts are cited,
never proved here: reproducing them in Lean needs an epimorphism enumeration, which is F5's job
and not a `decide`. -/

section StressZMod8

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

private theorem orderOf_dvd_eight (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- A concrete marking of the `L_sq` alphabet at `h = 0`, written additively:
`(σ, τ, x₀, x₁) = (5, 1, 1, 1)` in `Multiplicative (ZMod 8)`. -/
def zmod8Marking : Marking (2 * 0 + 1) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 1)
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]

/-- **Stress (genuine `ω₂`)**: the *profinite* denotation of the `n = 1` word — real `x ^ᶻ ω₂`
powers, not a hand-chosen integer exponent — is `ofAdd 7`.

Additively, and abelian so both commutators drop: `(x₀^σ)⁻¹ = −1`, `(x₀^{-3}τ)^{ω₂} = (−3+1)·1 =
−2`, `x₁² = 2`, `[x₁,x₁^{σ₂}] = 0`, total `−1 − 2 + 2 = −1 = 7`.  Pins three things at once: the
`−3` exponent (a `+3` would give `5`), the *inverse* on the first factor (dropping it would give
`1`), and the `ω₂` sitting on the whole `(x₀^{-3}τ)` subword rather than on `τ` alone. -/
theorem eval_zmod8_lSq :
    zmod8Marking.eval (lSqW 0) = Multiplicative.ofAdd (7 : ZMod 8) := by
  rw [Marking.eval_def, PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight,
    omega2Exp_eight]
  · decide
  · exact isOmega2Only_lSq 0

/-- **Stress (`ω₂` is not vacuous)**: the same evaluation with the profinite exponent forced to
`3` — an odd non-`ω₂` representative — gives `−1 − 6 + 2 = −5 = 3`, a different value.  So the
`ω₂`-slots genuinely carry information at this marking. -/
theorem evalNat_zmod8_lSq_three :
    PWord.evalNat ⇑zmod8Marking 3 (lSqW 0) = Multiplicative.ofAdd (3 : ZMod 8) := by
  decide

/-- **Stress (the tame boundary is not vacuous either)**: at this marking the `τ`-letter has even
order, so the Gate-B value `τ^{ω₂}` is *not* trivial — which is `not_killsWild` again, read
numerically.  Inside `Γ_R`, where `τ` is pro-odd, this value is `1`. -/
theorem eval_killWildLetters_zmod8 :
    (Marking.killWildLetters zmod8Marking).eval (lSqW 0)
      = Multiplicative.ofAdd (1 : ZMod 8) := by
  rw [eval_killWildLetters_lSq,
    PWord.zpowHat_omega2_zpow (by norm_num) (orderOf_dvd_eight _), omega2Exp_eight]
  decide

end StressZMod8

/-- **Stress (nonabelian: the rank-3 core is not a vacuous relator)**: the square-commutator core
word is nontrivial at an explicit marking of `S₃`, so the conjugations do real work.

In `S₃` every element satisfies `y² = 1`, so the square drops out; what survives is
`(x^s)⁻¹ · (x³)⁻¹ = (1 2)·(0 2)`, a `3`-cycle.  An explicit witness rather than `∃ … by decide`:
the search over `S₃³` exhausts the kernel's recursion budget, and a witness costs nothing. -/
theorem sqWord_ne_one_perm :
    SqCore.sqWord (Equiv.swap 0 1) (Equiv.swap 0 2) (Equiv.swap 0 1)
      ≠ (1 : Equiv.Perm (Fin 3)) := by decide

/-- **Stress (the commutator block is not vacuous)**: `[x₁, x₁^σ] ≠ 1` at an `S₃` marking where
`σ` does not centralize `x₁` — the block that the `q_K = 4` pin above watches. -/
theorem commutator_block_ne_one_perm :
    GQ2.commP (Equiv.swap 1 2) (GQ2.conjP (Equiv.swap 1 2) (Equiv.swap 0 1))
      ≠ (1 : Equiv.Perm (Fin 3)) := by decide

end GQ2.Dyadic.Words.LSq
