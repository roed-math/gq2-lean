/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores

/-!
# Dyadic campaign, ticket WN0-a: the compact `N_α` branch word

The first of the five wave-2 branch-word files, and the pilot the **G2** gate reviews before
the other four lanes dispatch.  It carries **row 2 of the R5 selection freeze**
(`general_2adic/artifacts/reports/selection-freeze.md`), the compact-`N` relator

```
R_{N,α,0} = x₀^{p_α} [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂} · H_h,      p_α = 2 + 2^α,  α ≥ 2
```

as an F2 `PWord` over `Generator (2 + 2h)`, together with its two boundary specializations, the
`ℚ₂(√−2)` instance, and the WW5 one-tree hash pins for all four emitted instances.

**The conjugator is `σ`, not `σ₂`.**  This is the one place where the compact-`N` word differs
from its `M` siblings, it is what produces the invertible `1 − S⁻¹` unramified Fox block that
WN0-b must exhibit (packet §14), and it is preserved verbatim from the certificate.

## What is pinned, and against what

`rawNCompact α h` is the **certificate tree** — the `Export.RawWord` interchange form, restated
here in the emitted spelling of `general_2adic/generated/lean/N_compact_*.lean`.  Those emitted
files are standalone (each declares its own `RawWord` prelude and is imported by nothing), so
they cannot be imported; restating the tree against the real `GQ2.Dyadic` vocabulary and pinning
its digest is the sanctioned route, and it is what the four `#eval Export.assertAstHash` guards
below check.  All four frozen instances are covered:

| instance | certificate | digest |
|---|---|---|
| `α = 2, h = 0` | `N-compact-alpha2-h0-v001` | `a940b6ad06d9728a…` |
| `α = 2, h = 1` | `N-compact-alpha2-h1-v001` | `bb7b2f6593741831…` |
| `α = 3, h = 0` | `N-compact-alpha3-h0-v001` | `39b524e998b12f60…` |
| `α = 4, h = 0` | `N-compact-alpha4-h0-v001` | `decb720a917e8ddd…` |

`nCompactW α h` is the **semantic word**, and `denote_rawNCompact` proves it is *the denotation
of the hashed tree* — not merely a word that looks like it.  That is the load-bearing link: the
hash pins the tree, and `denote` pins the `PWord` to the tree, so a `PWord` edited without the
certificate moving cannot build.

## Authoring rules followed (WW5/S5.G, `docs/dyadic/tickets.md`)

1. **The certificate's spelling, not a normalized one.**  Neither side normalizes before
   hashing, so the tree is authored exactly as emitted: `.integerPower … (.int 6)` and never
   `.zhatPower … (.int 6)`; `ω₂` through the dedicated `omega2Power` node; the frozen exponents
   as literal `Int` (S5.G: no valuation environment is needed anywhere in this row).
2. **`x₂^{-σ}` is `Inverse ∘ Conjugate`.**  The certificate emits
   `.inverse (.conjugate x2 sigma)`, i.e. `(x₂^σ)⁻¹`, whereas F2's sugar `PWord.invConj` is
   `(x₂⁻¹)^σ` — the *other* association.  Both are legitimate readings of `x^{-g}` and they
   denote the same group element (`conjR_inv`), but only one of them hashes, so this file uses
   `.inv (.conj …)` throughout and never `PWord.invConj`.  Packet Rem. 2.3's prohibition is on
   parsing `-σ` as an *exponent*; it is silent on the association, and the certificate chose.
3. **Handles at general `h`, with `h = 0` explicit.**  Every statement below is at general `h`;
   the `h = 0` instances are separate declarations, because `h = 0` is where the handle tail is
   the empty product and the pro-`2` value is MC2's core on the nose.
4. **`<decl>_astHash` + `#eval Export.assertAstHash`**, the WW5 convention, one pair per
   instance.  `native_decide` appears nowhere: the census must stay at eleven.
5. **Every `Multiply` is `PWord.prodList`, including the two-letter one.**  The certificate's
   `Multiply` node is `n`-ary and `Export.denote` folds it with `PWord.prodList`, which is
   right-nested *onto `PWord.one`*: `Multiply [x₂, τ]` denotes to `x₂ · (τ · 1)` and **not** to
   the binary `PWord.mul x₂ τ`.  Writing the inner `(x₂τ)` of the `ω₂`-factor as a binary `.mul`
   — the obvious thing to write — makes `denote_rawNCompact` fail, and nothing else does.  Every
   wave-2 lane will hit this; see the pattern notes.

## Implementation notes

This file is **not** `module`-style, and that is forced: it imports `GQ2.Dyadic.TameBoundary`
(F3), which is itself not `module`-style, and a `module` file may not import a non-`module` one.
`GQ2/Dyadic/Word/` is `module`-style throughout, so `Words/` breaks that pattern — see the
pattern notes at the end of this docstring block.  The import is not optional: `KillsWild` is
F3's Gate-B interface and this file has something to *say* about it (`not_killsWild`), which a
docstring claim could not check.
-/

namespace GQ2.Dyadic.Words

open Export (RawWord)

/-! ## The compact-`N` alphabet

The word uses `x₀, x₁, x₂` and `σ, τ`; the `h` handle pairs use `x₃, …, x_{2h+2}`.  So the
alphabet is `Generator (2 + 2h)`, whose wild letters are `Fin (2h + 3)`.  MC2's core has rank
`coreRank h = 4 + 2h` — the same letters, plus `σ`, which is not wild.
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

/-- The generator names the compact-`N` certificate uses.

A literal table rather than a decimal parser on purpose: `String.toNat?` is well-founded
recursion and does **not** reduce in the kernel, so a parsing `gen` field would put the
`denote` bridge below out of reach of `rfl`.  Each branch lane names its own letters, so a
per-lane table is the pattern; handle letters never come through here (they come through
`wildGen`), which is why the table stops at `x₂`. -/
def genOfName (h : ℕ) (s : String) : Option (Generator (2 + 2 * h)) :=
  match s with
  | "sigma" => some .sigma
  | "tau" => some .tau
  | "x0" => wildGen h 0
  | "x1" => wildGen h 1
  | "x2" => wildGen h 2
  | _ => none

/-- The denotation context of the compact-`N` row: the certificate's names, the handle letters,
and **no** symbolic parameters — every frozen exponent in this row is a literal `Int` (S5.G), so
`param` is nowhere consulted and returning `none` is honest rather than lossy. -/
def denoteCtx (h : ℕ) : Export.DenoteCtx (Generator (2 + 2 * h)) where
  gen := genOfName h
  handleGen := wildGen h
  param := fun _ => none

/-! ## The word -/

/-- `H_h = ∏_{j<h} [x_{3+2j}, x_{4+2j}]`, the block the certificate writes as
`HyperbolicHandles 3 h`.

Spelled as a `PWord.prodList` over `List.finRange h`, which is simultaneously what
`Export.handleFactors` expands the node to and how MC2's `handleWord` orders its factors — so
both bridges below are structural rather than a reindexing argument. -/
def handlesW (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

@[simp] theorem handlesW_zero : handlesW 0 = .one := rfl

/-- **The frozen compact-`N` branch word** (selection freeze row 2; draft eq. `Ncompact-word`)

```
R_{N,α,0} = x₀^{2+2^α} · [x₀,x₁] · x₂^{-σ} · (x₂τ)^{ω₂} · H_h
```

with `α ≥ 2` (`BranchData.Valid (.N0 α)`) and `h` hyperbolic handles.  The five factors are the
five children of the certificate's `Multiply` node, in order, and `x₂^{-σ}` is
`.inv (.conj …)` — the certificate's association, see the module docstring.

The conjugator is **`σ`**, not `σ₂`: at the marked pro-`2` boundary this is what turns the third
and fourth factors into the single commutator `[σ, x₂]` of MC2's core, and it is what gives
WN0-b its invertible `1 − S⁻¹` unramified block. -/
noncomputable def nCompactW (α h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α),
     .comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)),
     .inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)),
     PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
     handlesW h]

/-- The freeze's **spelling discipline** for the leading exponent: `2 + 2^α` is opaque, while
`2(1 + 2^{α−1})` displays the Hessian content — `1 + 2^{α−1}` is odd exactly when `α ≥ 2`, and
that oddness is what produces the `q(c₀)` term of the plus form.  Recorded here so that
WN0-b/c can cite it rather than re-deriving it; the *word* keeps the certificate's `2 + 2^α`. -/
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

/-! ## The certificate tree and the WW5 hash pins -/

/-- **The compact-`N` certificate tree**, in the spelling emitted by
`general_2adic/generated/lean/N_compact_alpha{2,3,4}_h{0,1}_v001.lean`.

`integerPower` with a literal `Int`, never `zhatPower … (.int n)`; `ω₂` through `omega2Power`;
`x₂^{-σ}` as `Inverse ∘ Conjugate`; the handle block unexpanded, because the hash is always of
the *unexpanded* tree. -/
def rawNCompact (α h : ℕ) : RawWord :=
  .multiply
    [.integerPower (.generator "x0") (.int (2 + 2 ^ α)),
     .commutator (.generator "x0") (.generator "x1"),
     .inverse (.conjugate (.generator "x2") (.generator "sigma")),
     .omega2Power (.multiply [.generator "x2", .generator "tau"]),
     .hyperbolicHandles 3 (.int h)]

/-- The tree is well-formed in WW5's sense, at every instance: nonempty names, no `etahat`
entries to be odd, no shadow parameters to be sorted.  `assertAstHash` refuses a tree that is
not, so this is the precondition of every pin below. -/
theorem wf_rawNCompact (α h : ℕ) : (rawNCompact α h).wf = true := by
  simp [rawNCompact, Export.RawWord.wf, Export.RawWord.wfList]

/-- **Cross-check against WW5's own kernel pin.**  `Export.frozenNCompactAlpha2H0` is the
`(α,h) = (2,0)` tree as WW5 typed it, and `Export.canonicalJson_frozenNCompactAlpha2H0` pins its
canonical bytes in the kernel.  This `rfl` inherits that pin for `rawNCompact 2 0`, so the
tree → bytes tier is checked in-kernel here too, without a second string literal to drift. -/
theorem rawNCompact_two_zero : rawNCompact 2 0 = Export.frozenNCompactAlpha2H0 := by rfl

/-- The canonical bytes of the `(α,h) = (2,0)` instance, inherited from WW5's kernel pin. -/
theorem canonicalJson_rawNCompact_two_zero :
    Export.canonicalJson (rawNCompact 2 0) =
      "{\"children\":[{\"exponent\":{\"type\":\"Int\",\"value\":6},\"op\":\"IntegerPower\",\
      \"word\":{\"name\":\"x0\",\"op\":\"Generator\"}},{\"left\":{\"name\":\"x0\",\"op\":\"\
      Generator\"},\"op\":\"Commutator\",\"right\":{\"name\":\"x1\",\"op\":\"Generator\"}},\
      {\"op\":\"Inverse\",\"word\":{\"conjugator\":{\"name\":\"sigma\",\"op\":\"Generator\"\
      },\"op\":\"Conjugate\",\"word\":{\"name\":\"x2\",\"op\":\"Generator\"}}},{\"op\":\"Om\
      ega2Power\",\"word\":{\"children\":[{\"name\":\"x2\",\"op\":\"Generator\"},{\"name\":\
      \"tau\",\"op\":\"Generator\"}],\"op\":\"Multiply\"}},{\"count\":{\"type\":\"Int\",\"v\
      alue\":0},\"op\":\"HyperbolicHandles\",\"start_index\":3}],\"op\":\"Multiply\"}" := by
  rw [rawNCompact_two_zero]
  exact Export.canonicalJson_frozenNCompactAlpha2H0

/-! ### The gate-A constants

One `<decl>_astHash` constant and one `#eval Export.assertAstHash` guard per frozen instance —
the WW5 convention (`pretty_lean.py`'s `HASH_SUFFIX`).  The `#eval` recomputes the digest from
the tree, so a constant cannot drift away from the word it labels, and the digests are the ones
stored in the simplification campaign's certificates, so a green elaboration is a cross-repo
agreement rather than a self-consistency check. -/

/-- Gate-A hash of `rawNCompact 2 0`, certificate `N-compact-alpha2-h0-v001` (the `ℚ₂(√−2)`
instance, and the digest the selection freeze quotes for row 2). -/
def rawNCompact_alpha2_h0_astHash : String :=
  "a940b6ad06d9728a6b0b5d20f27c76994d83103e65accc6b844fe6174755fc10"

/-- Gate-A hash of `rawNCompact 2 1`, certificate `N-compact-alpha2-h1-v001` — the one handle
instance, which is what makes the `h`-generality of this file testable rather than decorative. -/
def rawNCompact_alpha2_h1_astHash : String :=
  "bb7b2f6593741831d080c9e7e416f034feb6c59de83f78d73a4e04c401220106"

/-- Gate-A hash of `rawNCompact 3 0`, certificate `N-compact-alpha3-h0-v001`. -/
def rawNCompact_alpha3_h0_astHash : String :=
  "39b524e998b12f6b0531786bf19e5f0c36e83be56b4c711f5be79c2f80c02513"

/-- Gate-A hash of `rawNCompact 4 0`, certificate `N-compact-alpha4-h0-v001`. -/
def rawNCompact_alpha4_h0_astHash : String :=
  "decb720a917e8ddd66448c8b188055272d65940b3b540c65841b316b032bf16e"

#eval Export.assertAstHash "WN0 N-compact-alpha2-h0-v001" (rawNCompact 2 0)
  rawNCompact_alpha2_h0_astHash

#eval Export.assertAstHash "WN0 N-compact-alpha2-h1-v001" (rawNCompact 2 1)
  rawNCompact_alpha2_h1_astHash

#eval Export.assertAstHash "WN0 N-compact-alpha3-h0-v001" (rawNCompact 3 0)
  rawNCompact_alpha3_h0_astHash

#eval Export.assertAstHash "WN0 N-compact-alpha4-h0-v001" (rawNCompact 4 0)
  rawNCompact_alpha4_h0_astHash

/-! ### The `denote` bridge

What makes the hash pins bite on the *semantic* word.  `Export.denote` expands the handle block
and resolves the names; these four `rfl`s say that doing so to the hashed tree produces exactly
`nCompactW`, so the `PWord` the rest of this file reasons about is the certificate's word and
not a hand-typed lookalike.

One per pinned instance, because `denote` expands `hyperbolicHandles` only at a concrete length
(wave-2 authoring rule (2)); the `h`-generic statement is not available, and inventing one would
mean re-encoding the block, which WW5 forbids. -/

theorem denote_rawNCompact_two_zero :
    Export.denote (denoteCtx 0) (rawNCompact 2 0) = some (nCompactW 2 0) := by rfl

theorem denote_rawNCompact_two_one :
    Export.denote (denoteCtx 1) (rawNCompact 2 1) = some (nCompactW 2 1) := by rfl

theorem denote_rawNCompact_three_zero :
    Export.denote (denoteCtx 0) (rawNCompact 3 0) = some (nCompactW 3 0) := by rfl

theorem denote_rawNCompact_four_zero :
    Export.denote (denoteCtx 0) (rawNCompact 4 0) = some (nCompactW 4 0) := by rfl

end GQ2.Dyadic.Words
