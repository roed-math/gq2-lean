/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores

/-!
# Dyadic campaign, ticket WM0-a: the compact `M_α` branch word

**Row 4 of the R5 selection freeze** (`general_2adic/artifacts/reports/selection-freeze.md`),
the compact-`M` relator

```
A₀ = x₀⁻¹σ₂⁻ᵐ,   J₂ = x₂^{-σ}(x₂τ)^{ω₂},   E_m^rev = 𝓔(σ₂^m, σ₂^m; δ₀, δ₁),   m = 2^{α−1}
R_{M,0} = A₀² [A₀, x₁] σ₂^{2m} · J₂ · E_m^rev · H_h,                          α ≥ 2
```

as an F2 `PWord` over `Generator (2 + 2h)`, with its two boundary specializations, the `ℚ₂(√2)`
and `ℚ₂(√5)` instances, and the WW5 one-tree hash pins for all **five** emitted instances.

This is the second wave-2 branch-word file; `GQ2/Dyadic/Words/N0.lean` (WN0-a) is the template
and its ten authoring rules are followed here.  Three things are genuinely new, and the other
three lanes should read them before writing their own file — they are collected under
*Deviations from the WN0-a template* below.

## What is pinned, and against what

`rawMCompact α h` is the **certificate tree** — the `Export.RawWord` interchange form, restated
in the emitted spelling of `general_2adic/generated/lean/M_compact_*.lean`.  Those emitted files
are standalone (each declares its own `RawWord` prelude and is imported by nothing), so they
cannot be imported; restating the tree against the real `GQ2.Dyadic` vocabulary and pinning its
digest is the sanctioned route, and it is what the five `#eval Export.assertAstHash` guards
below check.  All five frozen instances are covered:

| instance | `candidate_id` | `m` | digest |
|---|---|---|---|
| `α = 2, h = 0, q_K = 2` | `M-compact-alpha2-h0-q2-v001` | 2 | `7c9005f50f9e1d5d…` |
| `α = 2, h = 0, q_K = 4` | `M-compact-alpha2-h0-q4-v001` | 2 | `7c9005f50f9e1d5d…` |
| `α = 2, h = 1, q_K = 2` | `M-compact-alpha2-h1-q2-v001` | 2 | `245eba4f5ae719e1…` |
| `α = 3, h = 0, q_K = 2` | `M-compact-alpha3-h0-q2-v001` | 4 | `0209b708538277e0…` |
| `α = 4, h = 0, q_K = 2` | `M-compact-alpha4-h0-q2-v001` | 8 | `c9edd3f4842ffe2c…` |

⚠ **Five instances, four trees.**  The first two rows carry the *same* digest because they are
the same tree: `q_K` is an arithmetic parameter of the field (it sits in the tame relation
`τ^σ = τ^{q_K}`), not a letter of the word, so it cannot move a word hash.  The manifest records
this explicitly in its `shared_word_hashes` block.  **A word hash is therefore not a key** — the
key is the `candidate_id`, and this file declares one `_astHash` constant and one `#eval` guard
per *candidate*, with `astHash_q2_eq_q4` stating the coincidence as a theorem rather than
leaving two constants silently equal.  That `q_K` is nonetheless *observable* is visible in the
F5 counts cited at the bottom of this file: the same tree at `q_K = 2` and `q_K = 4` has
different epimorphism-count vectors.

`mCompactW α h` is the **semantic word**, and `denote_rawMCompact_*` proves it is the denotation
of the hashed tree — not merely a word that looks like it.

## Deviations from the WN0-a template

1. **The handle node is absent at `h = 0`.**  The compact-`N` certificate emits
   `HyperbolicHandles 3 0` even when there are no handles; the compact-`M` certificate emits
   **no handle child at all** at `h = 0` (five children, not six) and appends
   `HyperbolicHandles 3 h` only for `h ≥ 1`.  Both are checked against the frozen digests, so
   this is the certificates' spelling and not a choice: `rawHandleTail`/`handleTailW` reproduce
   it, and the word is `prodList (mFactors α h ++ handleTailW h)`.  The consequence for
   consumers is that the `h = 0` word has **no trailing `PWord.one` for the handle block** —
   the opposite of the compact-`N` gotcha, and worth knowing before writing a `rfl`.
2. **The declarations are in the nested namespace `GQ2.Dyadic.Words.MCompact`.**  WN0-a put its
   alphabet helpers (`coreLetter`, `handleU`, `handleV`, `wildGen`, `genOfName`, `denoteCtx`,
   `handlesW`) at the top of `GQ2.Dyadic.Words`, and the compact-`M` alphabet is *the same
   alphabet*, so re-declaring them there would make `GQ2.lean` unimportable the moment both
   files are registered.  Nesting is the minimal fix inside this ticket's one owned file.  The
   real fix is a hoist: the seven alphabet declarations are branch-independent and belong in a
   shared `Words/Alphabet.lean` — **recorded as a cleanup/WWH candidate**, not done here.
3. **`α ≥ 1` is a genuine hypothesis of the pro-`2` comparison.**  The compact-`N` boundary
   theorems hold at every `α`; here the third factor is `σ₂^{2m}` with `m = 2^{α−1}`, and
   `2m = 2^α` is *false* at `α = 0`.  `eval_pro2_mCompact` therefore carries `1 ≤ α`
   (`BranchData.Valid` supplies `2 ≤ α`).

## Authoring rules followed (WW5/S5.G, WN0-a)

1. **The certificate's spelling, not a normalized one.**  Neither side normalizes before
   hashing: `.integerPower … (.int k)` and never `.zhatPower`; `ω₂` through `omega2Power`; the
   `auxiliary` wrappers (`A0`, `sigma2`, `J2`, `Erev`, `d0`, `d1`, `u0`, `u1`) kept, because
   they are hashed (`Auxiliary` is an `op` in the canonical JSON) even though `denote` inlines
   them.
2. **`x₂^{-σ}` is `Inverse ∘ Conjugate`**, the certificate's association, never `PWord.invConj`
   (which is `(x₂⁻¹)^σ` — the same group element, a different tree).  Identical to compact `N`;
   the conjugator is `σ`, not `σ₂`, in the `J₂` block too, and F5's row C4 measures that this
   is the choice the finite targets can see.
3. **Every `Multiply` is `PWord.prodList`**, including the two-letter ones (`A₀`, `J₂`, the
   `δ`-letters): `prodList` is right-nested *onto `PWord.one`*, so `δ₀` denotes to
   `(x₀τ)^{ω₂} · (x₀⁻¹ · 1)` and not to a binary `.mul`.  This is why `deltaC` below is not
   `GQ2.Dyadic.deltaW` — see `eval_deltaC_eq_deltaW` for the bridge that says they are
   nevertheless the same group element.
4. **`<decl>_astHash` + `#eval Export.assertAstHash`**, one pair per *candidate*.
   `native_decide` appears nowhere: the census must stay at eleven.
5. **Generator names by literal `match`**, never a decimal parser (`String.toNat?` is
   well-founded recursion and does not reduce in the kernel), and no `toString`/`s!` in a
   hashed tree for the same reason: `rawDelta0`/`rawDelta1` are written out.
6. **`denote` bridges per instance**, never `h`-generic: `denote` expands
   `hyperbolicHandles` only at a concrete length.
7. **Explicit witnesses** over `∃ … by decide`, and F5 counts in docstrings only.

## Implementation notes

This file is **not** `module`-style, and that is forced: it imports `GQ2.Dyadic.TameBoundary`
(F3), which is itself not `module`-style, and a `module` file may not import a non-`module` one.
The `Words/` + `Certificates/` layers being non-`module` is the lane convention ratified at
WN0-a.
-/

namespace GQ2.Dyadic.Words.MCompact

open Export (RawWord)

/-! ## The compact-`M` alphabet

The word uses `x₀, x₁, x₂` and `σ, τ`; the `h` handle pairs use `x₃, …, x_{2h+2}`.  So the
alphabet is `Generator (2 + 2h)` — the same alphabet as the compact-`N` row, and these seven
declarations are verbatim WN0-a's (see deviation 2 above: they want hoisting, not copying). -/

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

/-- The generator names the compact-`M` certificate uses: a literal table, because
`String.toNat?` does not reduce in the kernel and the `denote` bridges below are `rfl`. -/
def genOfName (h : ℕ) (s : String) : Option (Generator (2 + 2 * h)) :=
  match s with
  | "sigma" => some .sigma
  | "tau" => some .tau
  | "x0" => wildGen h 0
  | "x1" => wildGen h 1
  | "x2" => wildGen h 2
  | _ => none

/-- The denotation context of the compact-`M` row: the certificate's names, the handle letters,
and **no** symbolic parameters — every frozen exponent in this row is a literal `Int` (S5.G:
`α` and `m` are baked into each emitted instance), so `param` is nowhere consulted. -/
def denoteCtx (h : ℕ) : Export.DenoteCtx (Generator (2 + 2 * h)) where
  gen := genOfName h
  handleGen := wildGen h
  param := fun _ => none

/-! ## The exponent `m = 2^{α−1}` -/

/-- The compact-`M` exponent **`m = 2^{α−1}`** (freeze row 4; the certificates carry it as the
parameter `m`, with `two_m = 2m`).  The word uses `σ₂^{−m}` inside `A₀`, `σ₂^{2m}` as its third
factor, and `σ₂^{m}`, `σ₂^{2m}` as the two conjugators of the `𝓔`-block. -/
def mOf (α : ℕ) : ℕ := 2 ^ (α - 1)

@[simp] theorem mOf_two : mOf 2 = 2 := rfl
@[simp] theorem mOf_three : mOf 3 = 4 := rfl
@[simp] theorem mOf_four : mOf 4 = 8 := rfl

/-- **`2m = 2^α`** — the identity that turns the word's third factor `σ₂^{2m}` into the
`c^{2^α}` slot of MC2's `M`-core.  It needs `α ≥ 1`: at `α = 0`, `m = 2^{0−1} = 2^0 = 1` by
truncated subtraction and `2m = 2 ≠ 1`.  This is the one place where the compact-`M` row is
less uniform in `α` than the compact-`N` row. -/
theorem two_mul_mOf {α : ℕ} (hα : 1 ≤ α) : 2 * mOf α = 2 ^ α := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 1 := ⟨α - 1, by omega⟩
  simp [mOf, pow_succ]
  ring

/-- `m = 2^{α−1}` is **even** exactly on the valid rows `α ≥ 2` — the compact-`M` analogue of
the compact-`N` oddness of `1 + 2^{α−1}`, and the arithmetic behind `BranchData.Valid (.M0 α)`.
Recorded for WM0-b/c to cite rather than re-derive. -/
theorem even_mOf {α : ℕ} (hα : 2 ≤ α) : Even (mOf α) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  exact ⟨2 ^ β, by simp [mOf, pow_succ]; ring⟩

/-! ## The word

Five blocks, in the certificate's order: `A₀²`, `[A₀,x₁]`, `σ₂^{2m}`, `J₂`, `E_m^rev`, then the
handle tail.  Each block is its own definition, both because the certificate wraps each in an
`auxiliary` node and because WM0-b's Fox rows are computed block by block. -/

/-- `H_h = ∏_{j<h} [x_{3+2j}, x_{4+2j}]`, the block the certificate writes as
`HyperbolicHandles 3 h`, spelled over `List.finRange h` — simultaneously what
`Export.handleFactors` expands the node to and how MC2's `handleWord` orders its factors. -/
def handlesW (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

@[simp] theorem handlesW_zero : handlesW 0 = .one := rfl

/-- The handle **tail** of the factor list: empty at `h = 0`, a one-element list otherwise.
This mirrors the certificate exactly (deviation 1): the compact-`M` tree has no
`HyperbolicHandles` child at all when `h = 0`. -/
noncomputable def handleTailW : (h : ℕ) → List (PWord (Generator (2 + 2 * h)))
  | 0 => []
  | h + 1 => [handlesW (h + 1)]

/-- The **`δ`-letter `δ_i = (x_iτ)^{ω₂} x_i⁻¹`** in the certificate's spelling: two nested
`Multiply` nodes, hence two `prodList`s with their trailing `PWord.one`s.  `GQ2.Dyadic.deltaW`
is the same letter written with binary `.mul`; `eval_deltaC_eq_deltaW` bridges them. -/
noncomputable def deltaC (h : ℕ) (i : Fin 3) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]),
    .inv (.gen (coreLetter h i))]

/-- **`A₀ = x₀⁻¹ σ₂^{−m}`**, the compact-`M` Labute letter `A` (certificate `auxiliary "A0"`).
It is the letter that carries the whole difference from the compact-`N` row: `N` has the bare
`x₀` there, `M` has `x₀` twisted by a negative power of `σ₂`. -/
noncomputable def a0W (α h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [.inv (.gen (coreLetter h 0)), .zpow sigma2W (-(mOf α : ℤ))]

/-- **`J₂ = x₂^{-σ}(x₂τ)^{ω₂}`** (certificate `auxiliary "J2"`), the unramified block — the same
two factors that stand third and fourth in the compact-`N` word, here bracketed together by the
certificate's `auxiliary` node.  The conjugator is `σ`. -/
noncomputable def j2W (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)),
    PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])]

/-- **The reversed `𝓔`-correction block**
`E_m^rev = δ₁^{σ₂^{2m}} δ₁^{σ₂^{m}} δ₀^{σ₂^{m}} δ₀` (certificate `auxiliary "Erev"`).

This is the expanded form of S1.9's `𝓔(σ₂^m, σ₂^m; δ₀, δ₁)`; `eval_eRevW_eq_eBlock` proves the
identification at every marking, so the group-level `eBlock` API applies to it.  The **order**
of the four factors is the R4 decision; see the mutant note at the end of this file. -/
noncomputable def eRevW (α h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.conj (deltaC h 1) (.zpow sigma2W (2 * (mOf α : ℤ))),
     .conj (deltaC h 1) (.zpow sigma2W (mOf α : ℤ)),
     .conj (deltaC h 0) (.zpow sigma2W (mOf α : ℤ)),
     deltaC h 0]

/-- The five non-handle factors of the compact-`M` word, in the certificate's order. -/
noncomputable def mFactors (α h : ℕ) : List (PWord (Generator (2 + 2 * h))) :=
  [.zpow (a0W α h) 2,
   .comm (a0W α h) (.gen (coreLetter h 1)),
   .zpow sigma2W (2 * (mOf α : ℤ)),
   j2W h,
   eRevW α h]

/-- **The frozen compact-`M` branch word** (selection freeze row 4; draft eq. `Mcompact-word`)

```
R_{M,0} = A₀² [A₀, x₁] σ₂^{2m} · J₂ · E_m^rev · H_h,
A₀ = x₀⁻¹σ₂⁻ᵐ,  J₂ = x₂^{-σ}(x₂τ)^{ω₂},  E_m^rev = 𝓔(σ₂^m, σ₂^m; δ₀, δ₁),  m = 2^{α−1}
```

with `α ≥ 2` (`BranchData.Valid (.M0 α)`) and `h` hyperbolic handles.  The handle block is a
factor only when `h ≥ 1` — the certificate's shape, see deviation 1 in the module docstring. -/
noncomputable def mCompactW (α h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList (mFactors α h ++ handleTailW h)

/-! ## The certificate tree and the WW5 hash pins -/

/-- `σ₂ = σ^{ω₂}` as the certificate spells it: an `auxiliary` wrapper on an `Omega2Power`.
The wrapper is hashed, so it cannot be dropped. -/
def rawSigma2 : RawWord := .auxiliary "sigma2" (.omega2Power (.generator "sigma"))

/-- `σ₂^k`, the certificate's `IntegerPower` on `rawSigma2`. -/
def rawSigma2Pow (k : ℤ) : RawWord := .integerPower rawSigma2 (.int k)

/-- `δ₀ = (x₀τ)^{ω₂}x₀⁻¹`, with the certificate's `d0`/`u0` auxiliary wrappers. -/
def rawDelta0 : RawWord :=
  .auxiliary "d0"
    (.multiply
      [.auxiliary "u0" (.omega2Power (.multiply [.generator "x0", .generator "tau"])),
       .inverse (.generator "x0")])

/-- `δ₁ = (x₁τ)^{ω₂}x₁⁻¹`, with the certificate's `d1`/`u1` auxiliary wrappers. -/
def rawDelta1 : RawWord :=
  .auxiliary "d1"
    (.multiply
      [.auxiliary "u1" (.omega2Power (.multiply [.generator "x1", .generator "tau"])),
       .inverse (.generator "x1")])

/-- `A₀ = x₀⁻¹σ₂^{−m}`, certificate `auxiliary "A0"`. -/
def rawA0 (α : ℕ) : RawWord :=
  .auxiliary "A0" (.multiply [.inverse (.generator "x0"), rawSigma2Pow (-(mOf α : ℤ))])

/-- `J₂ = x₂^{-σ}(x₂τ)^{ω₂}`, certificate `auxiliary "J2"`. -/
def rawJ2 : RawWord :=
  .auxiliary "J2"
    (.multiply
      [.inverse (.conjugate (.generator "x2") (.generator "sigma")),
       .omega2Power (.multiply [.generator "x2", .generator "tau"])])

/-- `E_m^rev`, certificate `auxiliary "Erev"`: the four-factor expansion, in the R4 order. -/
def rawErev (α : ℕ) : RawWord :=
  .auxiliary "Erev"
    (.multiply
      [.conjugate rawDelta1 (rawSigma2Pow (2 * (mOf α : ℤ))),
       .conjugate rawDelta1 (rawSigma2Pow (mOf α : ℤ)),
       .conjugate rawDelta0 (rawSigma2Pow (mOf α : ℤ)),
       rawDelta0])

/-- The handle tail of the certificate tree: **absent** at `h = 0` (deviation 1). -/
def rawHandleTail : ℕ → List RawWord
  | 0 => []
  | h + 1 => [.hyperbolicHandles 3 (.int ((h + 1 : ℕ) : ℤ))]

/-- **The compact-`M` certificate tree**, in the spelling emitted by
`general_2adic/generated/lean/M_compact_alpha{2,3,4}_h{0,1}_q{2,4}_v001.lean`. -/
def rawMCompact (α h : ℕ) : RawWord :=
  .multiply
    ([.integerPower (rawA0 α) (.int 2),
      .commutator (rawA0 α) (.generator "x1"),
      rawSigma2Pow (2 * (mOf α : ℤ)),
      rawJ2,
      rawErev α] ++ rawHandleTail h)

/-- The tree is well-formed in WW5's sense at every instance: nonempty names, no `etahat`
entries to be odd, no shadow parameters to be sorted.  `assertAstHash` refuses a tree that is
not, so this is the precondition of every pin below. -/
theorem wf_rawMCompact (α h : ℕ) : (rawMCompact α h).wf = true := by
  cases h <;>
    simp [rawMCompact, rawHandleTail, rawA0, rawJ2, rawErev, rawDelta0, rawDelta1, rawSigma2,
      rawSigma2Pow, Export.RawWord.wf, Export.RawWord.wfList]

/-! ### The gate-A constants

One `<decl>_astHash` constant and one `#eval Export.assertAstHash` guard per frozen
**candidate** — five of each, over four distinct trees.  The `#eval` recomputes the digest from
the tree, so a constant cannot drift away from the word it labels, and the digests are the ones
stored in the simplification campaign's certificates, so a green elaboration is a cross-repo
agreement rather than a self-consistency check. -/

/-- Gate-A hash of `rawMCompact 2 0`, certificate `M-compact-alpha2-h0-q2-v001` — the digest the
selection freeze quotes for row 4, and the one `Export.frozenRowHashes` already records. -/
def rawMCompact_alpha2_h0_q2_astHash : String :=
  "7c9005f50f9e1d5ddfa8880a3a3168d1a47661efdaae81339ab968055bbf036a"

/-- Gate-A hash of `rawMCompact 2 0` **as the `ℚ₂(√5)` candidate**
`M-compact-alpha2-h0-q4-v001` (`q_K = 4`).  Same tree, therefore the same digest; kept as its
own constant because the certificate key is the `candidate_id`. -/
def rawMCompact_alpha2_h0_q4_astHash : String :=
  "7c9005f50f9e1d5ddfa8880a3a3168d1a47661efdaae81339ab968055bbf036a"

/-- Gate-A hash of `rawMCompact 2 1`, certificate `M-compact-alpha2-h1-q2-v001` — the one-handle
instance, which is what makes the `h`-generality of this file testable rather than decorative
(and the only instance whose tree carries a `HyperbolicHandles` node at all). -/
def rawMCompact_alpha2_h1_astHash : String :=
  "245eba4f5ae719e13a2f345210af2a127b6ec1b8f6ce05fccb267f427259c87b"

/-- Gate-A hash of `rawMCompact 3 0`, certificate `M-compact-alpha3-h0-q2-v001` — the `ℚ₂(√2)`
instance (`m = 4`). -/
def rawMCompact_alpha3_h0_astHash : String :=
  "0209b708538277e0d59995e5f4abf94563098ab60d8790ebbb513f09f3e1361f"

/-- Gate-A hash of `rawMCompact 4 0`, certificate `M-compact-alpha4-h0-q2-v001`. -/
def rawMCompact_alpha4_h0_astHash : String :=
  "c9edd3f4842ffe2c372c9d2653be4ae964ad85a6a6dc806e5878e8a22848323f"

/-- **`q_K` is not a letter of the word.**  The `ℚ₂(√5)` candidate (`q_K = 4`) and the
`q_K = 2` engine instance at `α = 2, h = 0` are the *same tree*, so their gate-A digests are
equal — the manifest's `shared_word_hashes` finding, stated here rather than left implicit in
two identical string literals.  A word hash is consequently **not** a key for the frozen
family; the `candidate_id` is. -/
theorem astHash_q2_eq_q4 :
    rawMCompact_alpha2_h0_q2_astHash = rawMCompact_alpha2_h0_q4_astHash := rfl

/-- The `α = 2, h = 0` digest is the one WW5 already recorded for row `M0` in
`Export.frozenRowHashes`, so this file reproduces the freeze's number rather than inventing
one. -/
theorem astHash_mem_frozenRowHashes :
    ("M0 (M-compact-alpha2-h0-q2-v001)", rawMCompact_alpha2_h0_q2_astHash) ∈
      Export.frozenRowHashes := by
  simp [Export.frozenRowHashes, rawMCompact_alpha2_h0_q2_astHash]

#eval Export.assertAstHash "WM0 M-compact-alpha2-h0-q2-v001" (rawMCompact 2 0)
  rawMCompact_alpha2_h0_q2_astHash

#eval Export.assertAstHash "WM0 M-compact-alpha2-h0-q4-v001 (√5; same tree as q2)"
  (rawMCompact 2 0) rawMCompact_alpha2_h0_q4_astHash

#eval Export.assertAstHash "WM0 M-compact-alpha2-h1-q2-v001" (rawMCompact 2 1)
  rawMCompact_alpha2_h1_astHash

#eval Export.assertAstHash "WM0 M-compact-alpha3-h0-q2-v001 (√2)" (rawMCompact 3 0)
  rawMCompact_alpha3_h0_astHash

#eval Export.assertAstHash "WM0 M-compact-alpha4-h0-q2-v001" (rawMCompact 4 0)
  rawMCompact_alpha4_h0_astHash

/-! ### The `denote` bridge

What makes the hash pins bite on the *semantic* word.  `Export.denote` expands the handle block,
inlines the `auxiliary` wrappers and resolves the names; these `rfl`s say that doing so to the
hashed tree produces exactly `mCompactW`, so the `PWord` the rest of this file reasons about is
the certificate's word and not a hand-typed lookalike.

One per distinct tree (four, for five candidates), because `denote` expands
`hyperbolicHandles` only at a concrete length (wave-2 authoring rule (2)). -/

theorem denote_rawMCompact_two_zero :
    Export.denote (denoteCtx 0) (rawMCompact 2 0) = some (mCompactW 2 0) := by rfl

theorem denote_rawMCompact_two_one :
    Export.denote (denoteCtx 1) (rawMCompact 2 1) = some (mCompactW 2 1) := by rfl

theorem denote_rawMCompact_three_zero :
    Export.denote (denoteCtx 0) (rawMCompact 3 0) = some (mCompactW 3 0) := by rfl

theorem denote_rawMCompact_four_zero :
    Export.denote (denoteCtx 0) (rawMCompact 4 0) = some (mCompactW 4 0) := by rfl

end GQ2.Dyadic.Words.MCompact
