/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.Words.Alphabet

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

**Audited axiom state** (scratch `#print axioms` pass over every non-`private` declaration,
2026-07-31): 103 declarations, 101 auditable by name, and **all are std-3 or smaller** — 12
depend on no axiom at all (the raw trees and the gate-A constants), 8 on `[propext]`, 12 on
`[propext, Quot.sound]`, the remaining 69 on the full `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`, no `Lean.ofReduceBool` (i.e. no `native_decide`), and **no `B`-axiom of the dyadic
census** anywhere: the census stays at eleven.  Every `decide` here is a kernel `decide` on a
finite `ZMod 8` or `Equiv.Perm (Fin 3)` computation.
-/

namespace GQ2.Dyadic.Words.MCompact

open Export (RawWord)

/-! ## The alphabet — compact-`M`

The word uses `x₀, x₁, x₂` and `σ, τ`; the `h` handle pairs use `x₃, …, x_{2h+2}`, so the
alphabet is `Generator (2 + 2h)`, whose wild letters are `Fin (2h + 3)`.

`coreLetter`, `handleU`, `handleV`, `wildGen`, `genOfName`, `denoteCtx`, `handlesW` and the
handle/kill-wild companions live once, in `GQ2.Dyadic.Words` (`Words/Alphabet.lean`), and are
reached from this sub-namespace without an `open`.  This row is on the **no-node-at-`h = 0`** handle
shape: the emitted tree carries no `HyperbolicHandles` child at `h = 0`, so the word goes
through the list device `handleTailW`, also hoisted.
-/

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

/-! ## The `ω₂`-only fragment

The compact-`M` word uses no `ℤ₂`-power and no profinite exponent other than `ω₂` — the
`σ₂`-powers are `ℤ`-powers *of* `σ^{ω₂}`, not new profinite exponents — so the whole
`ℕ`-exponent calculus of packet Lem. 2.2 applies with a single global exponent.  This is what
lets the numerical pins below evaluate the *genuine* `ω₂`. -/

@[simp] theorem isOmega2Only_deltaC (h : ℕ) (i : Fin 3) : (deltaC h i).IsOmega2Only := by
  simp [deltaC]

@[simp] theorem isOmega2Only_a0W (α h : ℕ) : (a0W α h).IsOmega2Only := by simp [a0W]

@[simp] theorem isOmega2Only_j2W (h : ℕ) : (j2W h).IsOmega2Only := by simp [j2W]

@[simp] theorem isOmega2Only_eRevW (α h : ℕ) : (eRevW α h).IsOmega2Only := by simp [eRevW]

@[simp] theorem isOmega2Only_mCompact (α h : ℕ) : (mCompactW α h).IsOmega2Only := by
  cases h <;> simp [mCompactW, mFactors, handleTailW, a0W, j2W, eRevW, deltaC]

/-! ## Evaluation scaffolding

The word is `prodList (five factors ++ handle tail)`, so every evaluation below splits once and
then computes.  `eval_mCompact_factors` is the split; it is stated at general `h` and it is
where the `h = 0` handle-node absence stops mattering — `handleTailW 0 = []` and
`handlesW 0 = .one` both evaluate to `1`. -/

section Eval

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α h : ℕ}

/-- The handle *tail* evaluates to the handle *block*, uniformly in `h`: the empty tail of the
`h = 0` certificate and the singleton tail of the `h ≥ 1` certificates both land on
`handlesW h`. -/
theorem eval_handleTailW (t : Marking (2 + 2 * h) G) :
    PWord.eval ⇑t (PWord.prodList (handleTailW h)) = t.eval (handlesW h) := by
  cases h with
  | zero => rfl
  | succ k => rw [handleTailW]; simp [Marking.eval_def]

/-- **The split**: the compact-`M` word is its five certificate factors times its handle block,
at every marking and every `h`. -/
theorem eval_mCompact_factors (t : Marking (2 + 2 * h) G) :
    t.eval (mCompactW α h) =
      t.eval (PWord.prodList (mFactors α h)) * t.eval (handlesW h) := by
  rw [Marking.eval_def, mCompactW, eval_prodList_append, eval_handleTailW]
  rfl

@[simp] theorem eval_sigma2W (t : Marking (2 + 2 * h) G) :
    t.eval (sigma2W : PWord (Generator (2 + 2 * h))) = t.σ ^ᶻ omega2 := rfl

/-- The value of a certificate `δ`-letter: `δ_i = (x_iτ)^{ω₂}x_i⁻¹`. -/
theorem eval_deltaC (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    t.eval (deltaC h i) = (t (coreLetter h i) * t.τ) ^ᶻ omega2 * (t (coreLetter h i))⁻¹ := by
  rw [Marking.eval_def, deltaC, PWord.eval_prodList]
  simp

/-- **The certificate's `δ`-letter is F2's `δ`-letter.**  They are different *trees* — the
certificate's is two nested `Multiply` nodes, hence two `prodList`s with trailing `PWord.one`s,
while `GQ2.Dyadic.deltaW` uses binary `.mul` — and only the certificate's spelling hashes.  They
are nevertheless the same group element at every marking, which is what lets WM0-b/c use the
existing `deltaW` API on this word. -/
theorem eval_deltaC_eq_deltaW (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    t.eval (deltaC h i) =
      t.eval (deltaW (n := 2 + 2 * h) ⟨(i : ℕ), by have := i.isLt; omega⟩) := by
  rw [eval_deltaC, Marking.eval_def, deltaW]
  simp [coreLetter]

/-- **The correction block *is* S1.9's `𝓔`-block.**

`E_m^rev = δ₁^{σ₂^{2m}} δ₁^{σ₂^{m}} δ₀^{σ₂^{m}} δ₀` is the expansion of
`𝓔(σ₂^m, σ₂^m; δ₀, δ₁)` — `eBlock_eq` with `g = h = σ₂^m`, where the leading conjugator
`σ₂^{2m}` is `σ₂^m · σ₂^m`.  Proved at every marking, so the group-level `eBlock`/`map_eBlock`
API of `GQ2/Dyadic/Word/Blocks.lean` applies to this word's correction block verbatim; this is
the identity the ticket's "the `𝓔`-block group identity your word's correction block satisfies"
names, and it is what makes the block a *constant-size* object for WM0-b/c. -/
theorem eval_eRevW_eq_eBlock (t : Marking (2 + 2 * h) G) :
    t.eval (eRevW α h) =
      eBlock (t.eval sigma2W ^ (mOf α : ℤ)) (t.eval sigma2W ^ (mOf α : ℤ))
        (t.eval (deltaC h 0)) (t.eval (deltaC h 1)) := by
  rw [eBlock_eq, Marking.eval_def, eRevW, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_conj,
    PWord.eval_zpow, mul_one, ← Marking.eval_def, eval_sigma2W]
  rw [show (2 * (mOf α : ℤ)) = (mOf α : ℤ) + (mOf α : ℤ) by ring, zpow_add]
  simp only [mul_assoc]

end Eval

/-! ## Gate B: the tame boundary

Packet Prop. 9.2's proof shape, in the compact-`M` spelling.  Killing the wild letters leaves

```
A₀ ↦ σ₂^{−m},   [A₀,x₁] ↦ 1,   J₂ ↦ τ^{ω₂},   δ₀, δ₁ ↦ τ^{ω₂},   H_h ↦ 1
```

so the first and third factors are `σ₂^{−2m}·σ₂^{2m} = 1` — **the balanced `σ₂`-powers cancel**,
which is the whole point of the `σ₂^{2m}` factor being there — and what survives is the
`δ`-letter story: one `τ^{ω₂}` from `J₂` and the `𝓔`-block on two copies of `τ^{ω₂}`.  Stating
the **value** rather than "` = 1`" is deliberate (WN0-a's rule): the death of this word at the
tame boundary is a fact about `τ`, supplied by Gate B rule T1, and not a syntactic
cancellation. -/

section Tame

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α h : ℕ}

/-- Every `δ`-letter dies down to `τ^{ω₂}` at the tame boundary. -/
theorem eval_killWildLetters_deltaC (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    (Marking.killWildLetters t).eval (deltaC h i) = t.τ ^ᶻ omega2 := by
  rw [eval_deltaC]
  simp

/-- **The tame boundary value of the compact-`M` word**: `τ^{ω₂} · 𝓔(σ₂^m, σ₂^m; τ^{ω₂}, τ^{ω₂})`.

The `A₀²` and `σ₂^{2m}` factors have cancelled (`σ₂^{−2m}·σ₂^{2m} = 1`), the commutator and the
handles have died with the wild letters, and everything left is built from `τ^{ω₂}`. -/
theorem eval_killWildLetters_mCompact (α h : ℕ) (t : Marking (2 + 2 * h) G) :
    (Marking.killWildLetters t).eval (mCompactW α h) =
      t.τ ^ᶻ omega2 *
        eBlock ((t.σ ^ᶻ omega2) ^ (mOf α : ℤ)) ((t.σ ^ᶻ omega2) ^ (mOf α : ℤ))
          (t.τ ^ᶻ omega2) (t.τ ^ᶻ omega2) := by
  have hH : (Marking.killWildLetters t).eval (handlesW h) = 1 := by
    rw [eval_handlesW]
    exact MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)
  have hE := eval_eRevW_eq_eBlock (α := α) (Marking.killWildLetters t)
  rw [eval_killWildLetters_deltaC, eval_killWildLetters_deltaC] at hE
  rw [eval_mCompact_factors, hH, mul_one, Marking.eval_def, mFactors, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_zpow,
    PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_prodList,
    PWord.eval_omega2PowHat, ← Marking.eval_def, eval_sigma2W, hE, a0W, j2W,
    killWildLetters_coreLetter, Marking.apply_tau, Marking.killWildLetters_σ,
    Marking.killWildLetters_τ, one_conjR, commR_one_right, inv_one, one_mul, mul_one]
  -- the balanced `σ₂`-powers: `σ₂^{−2m} · σ₂^{2m} = 1`
  rw [← zpow_mul, ← mul_assoc, ← zpow_add,
    show (-(mOf α : ℤ) * 2 + 2 * (mOf α : ℤ)) = 0 by ring, zpow_zero, one_mul]

/-- The same statement through F2's **substitution operator**: the syntactic kill-wild rewrite
`killWild` evaluated at `t` (`Marking.eval_killWild`). -/
theorem eval_killWild_mCompact (α h : ℕ) (t : Marking (2 + 2 * h) G) :
    t.eval (killWild (mCompactW α h)) =
      t.τ ^ᶻ omega2 *
        eBlock ((t.σ ^ᶻ omega2) ^ (mOf α : ℤ)) ((t.σ ^ᶻ omega2) ^ (mOf α : ℤ))
          (t.τ ^ᶻ omega2) (t.τ ^ᶻ omega2) := by
  rw [Marking.eval_killWild, eval_killWildLetters_mCompact]

/-- The tame boundary value is trivial as soon as `τ^{ω₂} = 1`: the `𝓔`-block on two trivial
`δ`-letters is trivial, whatever its conjugators are. -/
theorem eval_killWildLetters_mCompact_of_tau (α h : ℕ) (t : Marking (2 + 2 * h) G)
    (hτ : t.τ ^ᶻ omega2 = 1) :
    (Marking.killWildLetters t).eval (mCompactW α h) = 1 := by
  rw [eval_killWildLetters_mCompact, hτ]
  simp [eBlock]

/-- **Gate B rule T1, at a finite marking**: if the `τ`-letter has odd order, the tame boundary
value is trivial.  This is the form the finite-target harnesses (F5) test. -/
theorem eval_killWildLetters_mCompact_eq_one_of_odd {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] (α h : ℕ) (t : Marking (2 + 2 * h) P)
    (hτ : Odd (orderOf t.τ)) : (Marking.killWildLetters t).eval (mCompactW α h) = 1 :=
  eval_killWildLetters_mCompact_of_tau α h t
    (by simpa using PWord.eval_omega2Pow_eq_one_of_odd (⇑t) (.gen .tau) hτ)

end Tame

/-- **Gate-B admissibility, relativized to a tame `τ`** — packet Prop. 9.2.

The compact-`M` word dies at the tame boundary of every marking whose `τ`-letter is killed by
`ω₂`.  Inside `Γ_R` that hypothesis is *supplied*, by packet Lem. 3.1: the tame relation
`τ^σ = τ^{q}` with `q` even forces `τ` to be pro-odd (`GQ2.Dyadic.odd_order`), and `ω₂` kills
pro-odd elements.

⚠ The **bare** `KillsWild` is the wrong interface here, exactly as WN0-a found for compact `N`
— see `not_killsWild` below.  Branch lanes use this form or `killsWild_of_odd`, never the bare
one. -/
theorem killsWild_of_tau {α h : ℕ}
    (hτ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G),
      t.τ ^ᶻ omega2 = 1) :
    KillsWild (mCompactW α h) := by
  intro G _ _ _ _ _ t
  exact eval_killWildLetters_mCompact_of_tau α h t (hτ G t)

/-! ### ⚠ F3's `KillsWild` is *not* satisfiable by this word either

WN0-a's ruling, confirmed on the second wave-2 word and for the same reason.
`GQ2.Dyadic.KillsWild R` quantifies over **every** profinite group and **every** marking with no
relation imposed on the `τ`-letter, and the tame boundary value of any `δ`-letter word is built
from `τ^{ω₂}`; here it is `τ^{ω₂} · 𝓔(…; τ^{ω₂}, τ^{ω₂})`, which at `σ = 1` is just
`(τ^{ω₂})^4` — false in `Multiplicative (ZMod 8)` at `τ = ofAdd 1`, where `τ^{ω₂} = τ`
(`omega2Exp 8 = 1`) and `4 ≠ 0`.

This is not a defect in the *word*: the packet's hypothesis is about the tame quotient, where
`τ` is pro-odd by Lem. 3.1, and there the word is admissible (`killsWild_of_tau`,
`eval_killWildLetters_mCompact_eq_one_of_odd`).  Recorded rather than acted on:
`TameBoundary.lean` is not this ticket's file, and micro-row F3b already owns the amendment. -/

section Refutation

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

/-- **The frozen compact-`M` word is not Gate-B admissible in F3's unrelativized sense.** -/
theorem not_killsWild (α h : ℕ) : ¬ KillsWild (mCompactW α h) := by
  intro hR
  have hval := hR (Multiplicative (ZMod 8)) (refuteMarking h)
  rw [eval_killWildLetters_mCompact,
    PWord.zpowHat_omega2_zpow (by norm_num) (zmod8_orderOf_dvd _),
    PWord.zpowHat_omega2_zpow (by norm_num) (zmod8_orderOf_dvd _), omega2Exp_eight,
    show (refuteMarking h).τ = Multiplicative.ofAdd (1 : ZMod 8) from rfl,
    show (refuteMarking h).σ = (1 : Multiplicative (ZMod 8)) from rfl] at hval
  rw [eBlock] at hval
  simp only [conjR, one_zpow, Nat.cast_one, zpow_one, inv_one, one_mul, mul_one] at hval
  exact absurd hval (by decide)

end Refutation

/-! ## Gate C: the marked pro-`2` boundary

The headline of the ticket.  `pro2` sends `τ ↦ 1` and collapses every `ω₂`-power (so
`σ₂ ↦ σ`), which does three things at once:

* `A₀ = x₀⁻¹σ₂^{−m} ↦ x₀⁻¹σ^{−m}` — the compact-`M` Labute letter `A`;
* `J₂ = x₂^{-σ}(x₂τ)^{ω₂} ↦ (x₂^σ)⁻¹x₂ = [σ, x₂]` — the same one certified move as compact `N`,
  and the same payoff for choosing `σ` rather than `σ₂` as the conjugator;
* every `δ`-letter `↦ x_i x_i⁻¹ = 1`, so the whole correction block `E_m^rev` disappears.

What is left is `A₀²[A₀,x₁]σ^{2m}[σ,x₂]·H_h` with `2m = 2^α`, which is **MC2's `mWord` on the
Labute letters `(A₀, x₁, σ, x₂)`** times MC2's `handleWord` — the certificate's own
`gate_C_core_displayed` string, verbatim. -/

section Pro2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α h : ℕ}

@[simp] theorem pro2_handleTailW (h : ℕ) : (handleTailW h).map pro2 = handleTailW h := by
  cases h <;> simp [handleTailW]

/-- The core letters are wild, so `pro2` fixes them.  Stated against `coreLetter` rather than
against `Generator.wild` so that it fires without unfolding the alphabet — unfolding
`coreLetter` inside a `simp` set desynchronises the goal from `invConj_mul_self`'s argument. -/
@[simp] theorem pro2_gen_coreLetter (h : ℕ) (i : Fin 3) :
    pro2 (.gen (coreLetter h i)) = (.gen (coreLetter h i) : PWord (Generator (2 + 2 * h))) := rfl

/-- **Gate C, syntactically**: the five certificate factors are rewritten one by one and the
handle tail is untouched. -/
theorem pro2_mCompact (α h : ℕ) :
    pro2 (mCompactW α h) =
      PWord.prodList ((mFactors α h).map pro2 ++ handleTailW h) := by
  rw [mCompactW, pro2_prodList, List.map_append, pro2_handleTailW]

/-- Every `δ`-letter dies at the pro-`2` boundary: `δ_i ↦ x_i·x_i⁻¹ = 1`. -/
@[simp] theorem eval_pro2_deltaC (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    t.eval (pro2 (deltaC h i)) = 1 := by
  rw [deltaC, pro2_prodList, Marking.eval_def, PWord.eval_prodList]
  simp

/-- …hence so does the whole correction block. -/
@[simp] theorem eval_pro2_eRevW (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (eRevW α h)) = 1 := by
  have h0 := eval_pro2_deltaC (h := h) t 0
  have h1 := eval_pro2_deltaC (h := h) t 1
  rw [eRevW, pro2_prodList, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pro2_conj,
    PWord.eval_conj, ← Marking.eval_def, h0, h1, one_conjR, mul_one]

/-- **The pro-`2` boundary value of the compact-`M` word is MC2's compact-`M` core.**

`pro2 R_{M,0}` evaluates, at *every* marking, to `mWord α A₀ x₁ σ x₂ · handleWord` with
`A₀ = x₀⁻¹σ^{−m}`.  No hypothesis on the marking is needed — `pro2` has already removed `τ` and
every `ω₂` — but `1 ≤ α` is needed on the *exponent*: the word's third factor is the `ℤ`-power
`σ^{2m}` and MC2's core word's third factor is the `ℕ`-power `σ^{2^α}`, and `2m = 2^α` fails at
`α = 0` (`two_mul_mOf`).  `BranchData.Valid (.M0 α)` supplies `2 ≤ α`. -/
theorem eval_pro2_mCompact (hα : 1 ≤ α) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mCompactW α h)) =
      MarkedCore.mWord α ((t (coreLetter h 0))⁻¹ * t.σ ^ (-(mOf α : ℤ)))
          (t (coreLetter h 1)) t.σ (t (coreLetter h 2)) *
        MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  have hH : PWord.eval ⇑t (PWord.prodList (handleTailW h))
      = MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
    rw [eval_handleTailW, eval_handlesW]
  have hE := eval_pro2_eRevW (α := α) (h := h) t
  have hsq : ∀ x : G, x ^ (2 : ℤ) = x ^ (2 : ℕ) := fun x => by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have hexp : t.σ ^ (2 * (mOf α : ℤ)) = t.σ ^ (2 ^ α : ℕ) := by
    rw [show (2 * (mOf α : ℤ)) = ((2 * mOf α : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      two_mul_mOf hα]
  rw [pro2_mCompact, Marking.eval_def, eval_prodList_append, hH, PWord.eval_prodList, mFactors]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pro2_zpow, pro2_comm,
    pro2_prodList, pro2_inv, pro2_conj, pro2_gen_sigma, pro2_gen_tau,
    pro2_omega2Pow, pro2_sigma2W, pro2_gen_coreLetter, PWord.eval_zpow, PWord.eval_comm,
    PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_one, PWord.eval_prodList,
    ← Marking.eval_def, hE, a0W, j2W, Marking.apply_sigma, mul_one]
  -- Realign the two `ℤ`-powers with MC2's `ℕ`-powers, then normalise both bracketings.
  rw [hsq, hexp, MarkedCore.mWord, ← invConj_mul_self (t (coreLetter h 2)) t.σ]
  simp only [commR, commP, conjR, mul_assoc]

/-- At `h = 0` the handle tail is empty and the pro-`2` value is MC2's core word on the nose —
the statement the ticket asks for, and the one MC2's rank-four theory consumes. -/
theorem eval_pro2_mCompact_zero (hα : 1 ≤ α) (t : Marking 2 G) :
    t.eval (pro2 (mCompactW α 0)) =
      MarkedCore.mWord α ((t.x 0)⁻¹ * t.σ ^ (-(mOf α : ℤ))) (t.x 1) t.σ (t.x 2) := by
  rw [eval_pro2_mCompact (α := α) (h := 0) hα t,
    show MarkedCore.handleWord (fun j : Fin 0 => t (handleU j)) (fun j : Fin 0 => t (handleV j))
      = 1 from rfl, mul_one]
  rfl

/-- The same value read as MC2's **full relator shape** `mRelWord` at the standard marking
(`coreMark`: the four Labute letters, `1` on every handle letter). -/
theorem eval_pro2_mCompact_eq_mRelWord (hα : 1 ≤ α) (t : Marking 2 G) :
    t.eval (pro2 (mCompactW α 0)) =
      MarkedCore.mRelWord (h := 0) α
        (MarkedCore.coreMark ((t.x 0)⁻¹ * t.σ ^ (-(mOf α : ℤ))) (t.x 1) t.σ (t.x 2)) := by
  rw [eval_pro2_mCompact_zero hα, MarkedCore.mRelWord_coreMark]

end Pro2

/-! ## The two field instances

`ℚ₂(√2)` is `(α, q_K) = (3, 2)`, so `m = 2^{α−1} = 4` and `2m = 8`; `ℚ₂(√5)` is
`(α, q_K) = (2, 4)`, so `m = 2` and `2m = 4`.  Both are `h = 0` and both are branch rows
`BranchData.M0 α`.  The two words below are the frozen certificates
`M-compact-alpha3-h0-q2-v001` and `M-compact-alpha2-h0-q4-v001` spelled out with their
exponents evaluated — the shape AS3 takes end-to-end. -/

/-- **The `ℚ₂(√2)` relation** (`α = 3`, `m = 4`, certificate `M-compact-alpha3-h0-q2-v001`):

```
R_{M,0} = (x₀⁻¹σ₂⁻⁴)² [x₀⁻¹σ₂⁻⁴, x₁] σ₂⁸ · x₂^{-σ}(x₂τ)^{ω₂} · δ₁^{σ₂⁸}δ₁^{σ₂⁴}δ₀^{σ₂⁴}δ₀
```

Note the **absence** of a trailing `PWord.one`: at `h = 0` the compact-`M` certificate has no
handle child (module docstring, deviation 1), so this is a five-element `prodList`. -/
theorem mCompactW_three_zero :
    mCompactW 3 0 = PWord.prodList
      [.zpow (PWord.prodList [.inv (.gen (coreLetter 0 0)), .zpow sigma2W (-4)]) 2,
       .comm (PWord.prodList [.inv (.gen (coreLetter 0 0)), .zpow sigma2W (-4)])
         (.gen (coreLetter 0 1)),
       .zpow sigma2W 8,
       PWord.prodList [.inv (.conj (.gen (coreLetter 0 2)) (.gen .sigma)),
         PWord.omega2Pow (PWord.prodList [.gen (coreLetter 0 2), .gen .tau])],
       PWord.prodList
         [.conj (deltaC 0 1) (.zpow sigma2W 8),
          .conj (deltaC 0 1) (.zpow sigma2W 4),
          .conj (deltaC 0 0) (.zpow sigma2W 4),
          deltaC 0 0]] := rfl

/-- **The `ℚ₂(√5)` relation** (`α = 2`, `m = 2`, certificate `M-compact-alpha2-h0-q4-v001`).

The tree is the `q_K = 2` engine instance's tree — `q_K` is not a letter — so this same
statement pins both `α = 2, h = 0` candidates. -/
theorem mCompactW_two_zero :
    mCompactW 2 0 = PWord.prodList
      [.zpow (PWord.prodList [.inv (.gen (coreLetter 0 0)), .zpow sigma2W (-2)]) 2,
       .comm (PWord.prodList [.inv (.gen (coreLetter 0 0)), .zpow sigma2W (-2)])
         (.gen (coreLetter 0 1)),
       .zpow sigma2W 4,
       PWord.prodList [.inv (.conj (.gen (coreLetter 0 2)) (.gen .sigma)),
         PWord.omega2Pow (PWord.prodList [.gen (coreLetter 0 2), .gen .tau])],
       PWord.prodList
         [.conj (deltaC 0 1) (.zpow sigma2W 4),
          .conj (deltaC 0 1) (.zpow sigma2W 2),
          .conj (deltaC 0 0) (.zpow sigma2W 2),
          deltaC 0 0]] := rfl

/-- The `ℚ₂(√2)` branch row is a valid compact-`M` row (F1/F4: `2 ≤ α`), at level `r = 0`. -/
theorem branchData_sqrtTwo :
    (BranchData.M0 3).Valid ∧ (BranchData.M0 3).level = 0 :=
  ⟨BranchData.valid_M0_iff.mpr (by norm_num), rfl⟩

/-- The `ℚ₂(√5)` branch row is a valid compact-`M` row, at level `r = 0`.  `q_K = 4` does not
appear: it is not branch data. -/
theorem branchData_sqrtFive :
    (BranchData.M0 2).Valid ∧ (BranchData.M0 2).level = 0 :=
  ⟨BranchData.valid_M0_iff.mpr (by norm_num), rfl⟩

/-! ## Numerical stress pins

Nothing below is cited by a proof; these are regression pins in the sense of plan §3 A1.

**The python twins are F5's rows** (`scripts/dyadic_sanity_counts.py`).  F5 measures the two
field instances of this row by their epimorphism-count vectors over `(S₃, D₈, A₄)`:

| F5 row | `(α, m, q_K)` | `(S₃, D₈, A₄)` |
|---|---|---|
| `d=2  M(alpha=3, r=0)` | `(3, 4, 2)` | `(6, 1568, 120)` |
| `d=5  M(alpha=2, r=0)` | `(2, 2, 4)` | `(0, 1568, 480)` |

and its mutant row **C4** re-runs the *same code* on `d = 2` with the conjugator of `J₂` flipped
to `σ₂`, obtaining `(6, 1568, 504)` — so `A₄` is what sees the `σ`-versus-`σ₂` choice, `120`
against `120`… `504`, exactly as on the compact-`N` row.  Two further readings of the table:
the two rows differ because `q_K` differs (the same word tree, a different tame relation — the
arithmetic visibility of `q_K` that the shared word hash cannot express), and **no `2`-group can
witness any of this**, because on a group of `2`-power exponent `ω₂` acts as the identity and
`σ₂ = σ` identically.

Those counts are **cited, never proved here**: reproducing them needs an epimorphism
enumeration over a group with nontrivial odd part, which is F5's job and not a `decide`. -/

section StressZMod8

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

/-- **Stress (genuine `ω₂`)**: the *profinite* denotation of the `ℚ₂(√5)` word — real `x ^ᶻ ω₂`
powers, not a hand-chosen integer exponent — is `ofAdd 3`.

Additively, and abelian so the commutator drops and conjugation is trivial:
`A₀² = 2(−x₀ − 2σ) = −2 − 20`, `σ₂^{2m} = 4σ = 20`, `J₂ = −x₂ + (x₂+τ) = 1`, and the four
`δ`-letters of `E_m^rev` contribute `4τ = 4`, for `−2 + 5 = 3`.  Pins three things at once: the
exponent `2` on `A₀`, the *four* `δ`-letters of the correction block (dropping one would give
`2`), and the `ω₂` sitting on the whole `(x_iτ)` subword rather than on `x_i` alone. -/
theorem eval_zmod8_mCompact :
    zmod8Marking.eval (mCompactW 2 0) = Multiplicative.ofAdd (3 : ZMod 8) := by
  rw [Marking.eval_def, PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight,
    omega2Exp_eight]
  · decide
  · exact isOmega2Only_mCompact 2 0

/-- **Stress (the `σ₂`-powers really are balanced)**: `α` is invisible at an abelian marking.

`A₀²` contributes `−2m·σ₂` and the third factor contributes `+2m·σ₂`, so every trace of `m` —
hence of `α` — cancels once the group is commutative.  This is the *point* of the `σ₂^{2m}`
factor, read numerically, and it is also why the `ZMod 8` pins above cannot be used to
distinguish the instances: that job belongs to `A₄` in F5's table. -/
theorem eval_zmod8_mCompact_alpha_indep :
    zmod8Marking.eval (mCompactW 2 0) = zmod8Marking.eval (mCompactW 3 0) := by
  rw [Marking.eval_def, Marking.eval_def,
    PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight _ (isOmega2Only_mCompact 2 0),
    PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight _ (isOmega2Only_mCompact 3 0),
    omega2Exp_eight]
  decide

/-- **Stress (`ω₂` is not vacuous)**: the same evaluation with the profinite exponent forced to
`3` — an odd non-`ω₂` representative — gives `ofAdd 7`, a different value.  So the `ω₂`-slot
genuinely carries information at this marking. -/
theorem evalNat_zmod8_mCompact_three :
    PWord.evalNat ⇑zmod8Marking 3 (mCompactW 2 0) = Multiplicative.ofAdd (7 : ZMod 8) := by
  decide

/-- **Stress (the tame boundary is not vacuous either)**: at this marking the `τ`-letter has
even order, so the Gate-B value `τ^{ω₂}·𝓔(…; τ^{ω₂}, τ^{ω₂})` is `5τ = 5`, not trivial — which
is `not_killsWild` again, read numerically.  Inside `Γ_R`, where `τ` is pro-odd, this value
is `1`. -/
theorem eval_killWildLetters_zmod8 :
    (Marking.killWildLetters zmod8Marking).eval (mCompactW 2 0)
      = Multiplicative.ofAdd (5 : ZMod 8) := by
  rw [Marking.eval_def,
    PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight _ (isOmega2Only_mCompact 2 0),
    omega2Exp_eight]
  decide

end StressZMod8

/-- **Stress (nonabelian: the core is not a vacuous relator)**: MC2's compact-`M` core word is
nontrivial at an explicit marking of `S₃`, so the two commutators do real work.

In `S₃` a transposition `a` has `a² = 1` and `c^{2^α} = c⁴ = 1`, so both power factors of
`mWord` drop out and everything that survives comes from `[a,b]·[c,d]`.  At two distinct
transpositions each commutator is the *same* `3`-cycle `g`, so the core word is `g² ≠ 1`.

An explicit witness rather than `∃ … by decide`: the search over `S₃⁴` exhausts the kernel's
recursion budget, and a witness costs nothing.  F5's `d = 2` row for this group reports the
epimorphism count `6`; that number is *not* what is proved here (see the section note). -/
theorem mWord_ne_one_perm :
    MarkedCore.mWord 2 (Equiv.swap 0 1) (Equiv.swap 0 2) (Equiv.swap 0 1) (Equiv.swap 0 2)
      ≠ (1 : Equiv.Perm (Fin 3)) := by decide

/-! ## ⚠ The forward-order mutant, and what this ticket does *not* claim

The R4 decision is that the correction block is the **reversed** `𝓔`-block
`E_m^rev = δ₁^{σ₂^{2m}}δ₁^{σ₂^{m}}δ₀^{σ₂^{m}}δ₀`; the draft's forward order `E_m^fwd` is the
same four factors read backwards (F5 builds it literally as `factors.reverse()`).  What this
file proves about that choice is exactly this:

* **Gate C cannot see it.**  Every `δ`-letter dies at the pro-`2` boundary, so *both* blocks
  specialize to `1` and both words specialize to the same MC2 core
  (`eval_pro2_mFwdW_eq_mCompact`).
* **Gate B cannot see it either.**  Under the packet's tame hypothesis `τ^{ω₂} = 1` both blocks
  are trivial and both words are admissible under the identical hypothesis
  (`eval_killWildLetters_mFwdW_of_tau`).  Without that hypothesis the two tame *values* are
  the same four conjugates of `τ^{ω₂}` in opposite orders — which is a difference no boundary
  gate is asked about.

And what this file must **not** claim, per the dated 2026-07-31 correction to the WM0 spec:

* **There is no finite-target rejection of the forward order, and this ticket does not promise
  one.**  F5's row C2 measures the two orders *pointwise* on every marking of `S₃`, `D₈` and
  `A₄` at both displayed instances and finds them **identical** (`diffs 0/0/0`, pinned
  `NOT-SEPARATED` so that it fails loudly if a target ever separates).  That blindness is
  structural, by the freeze's own coverage criterion: a separating orbit needs `𝔽₂`-dimension
  `≥ 2^α`, and these wild layers have dimension `≤ 2` against `2^α = 8` (√2) and `4` (√5).
* **The order is invisible at first Fox order too** (S4.1).  It is a *second*-order phenomenon.
* **The rejection of record is S4.1 §9.4's difference formula** in `(q, b_q, P, W)` — the
  draft's stated reason (a rank drop) and its stated witness (the fifth-root orbit) are both
  wrong, errata item 6; the seventeenth-root orbit is what covers both displayed instances.
  The Lean-side rejection is **WM0-c's second-order certificate**, not this file. -/

section Mutant

/-- The compact-`M` word with an arbitrary correction block in the fifth slot: the word depends
on the block only here, which is what makes the two mutant statements below one-liners. -/
noncomputable def mWordWith (α h : ℕ) (E : PWord (Generator (2 + 2 * h))) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    ([.zpow (a0W α h) 2,
      .comm (a0W α h) (.gen (coreLetter h 1)),
      .zpow sigma2W (2 * (mOf α : ℤ)),
      j2W h,
      E] ++ handleTailW h)

@[simp] theorem mWordWith_eRevW (α h : ℕ) : mWordWith α h (eRevW α h) = mCompactW α h := rfl

/-- **The forward-order `𝓔`-block**, the draft's rejected order: `E_m^rev` read backwards.  This
is F5's row-C2 mutant, built the same way (one flag, never a second transcription). -/
noncomputable def eFwdW (α h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [deltaC h 0,
     .conj (deltaC h 0) (.zpow sigma2W (mOf α : ℤ)),
     .conj (deltaC h 1) (.zpow sigma2W (mOf α : ℤ)),
     .conj (deltaC h 1) (.zpow sigma2W (2 * (mOf α : ℤ)))]

/-- The forward-order **word**: the frozen word with `E_m^rev` replaced by `E_m^fwd`. -/
noncomputable def mFwdW (α h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  mWordWith α h (eFwdW α h)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α h : ℕ}

/-- The word depends on its correction block only through that block's value. -/
theorem eval_mWordWith_congr (t : Marking (2 + 2 * h) G)
    {E E' : PWord (Generator (2 + 2 * h))} (hE : t.eval E = t.eval E') :
    t.eval (mWordWith α h E) = t.eval (mWordWith α h E') := by
  have hE' : PWord.eval ⇑t E = PWord.eval ⇑t E' := hE
  rw [mWordWith, mWordWith, Marking.eval_def, Marking.eval_def, eval_prodList_append,
    eval_prodList_append]
  simp only [PWord.eval_prodList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hE']

/-- `pro2` acts on the correction block slot and leaves the shape alone. -/
theorem pro2_mWordWith (α h : ℕ) (E : PWord (Generator (2 + 2 * h))) :
    pro2 (mWordWith α h E) =
      PWord.prodList
        ([pro2 (.zpow (a0W α h) 2),
          pro2 (.comm (a0W α h) (.gen (coreLetter h 1))),
          pro2 (.zpow sigma2W (2 * (mOf α : ℤ))),
          pro2 (j2W h),
          pro2 E] ++ handleTailW h) := by
  rw [mWordWith, pro2_prodList, List.map_append, pro2_handleTailW]
  rfl

/-- The same congruence after the pro-`2` rewrite. -/
theorem eval_pro2_mWordWith_congr (t : Marking (2 + 2 * h) G)
    {E E' : PWord (Generator (2 + 2 * h))} (hE : t.eval (pro2 E) = t.eval (pro2 E')) :
    t.eval (pro2 (mWordWith α h E)) = t.eval (pro2 (mWordWith α h E')) := by
  have hE' : PWord.eval ⇑t (pro2 E) = PWord.eval ⇑t (pro2 E') := hE
  rw [pro2_mWordWith, pro2_mWordWith, Marking.eval_def, Marking.eval_def, eval_prodList_append,
    eval_prodList_append]
  simp only [PWord.eval_prodList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hE']

@[simp] theorem eval_pro2_eFwdW (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (eFwdW α h)) = 1 := by
  have h0 := eval_pro2_deltaC (h := h) t 0
  have h1 := eval_pro2_deltaC (h := h) t 1
  rw [eFwdW, pro2_prodList, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pro2_conj,
    PWord.eval_conj, ← Marking.eval_def, h0, h1, one_conjR, mul_one]

/-- **Gate C is blind to the block order**: both words have the same pro-`2` specialization at
every marking, because both correction blocks die there. -/
theorem eval_pro2_mFwdW_eq_mCompact (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mFwdW α h)) = t.eval (pro2 (mCompactW α h)) := by
  rw [mFwdW, ← mWordWith_eRevW α h]
  exact eval_pro2_mWordWith_congr t (by rw [eval_pro2_eFwdW, eval_pro2_eRevW])

theorem eval_killWildLetters_eFwdW_of_tau (t : Marking (2 + 2 * h) G)
    (hτ : t.τ ^ᶻ omega2 = 1) : (Marking.killWildLetters t).eval (eFwdW α h) = 1 := by
  rw [eFwdW, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_conj,
    ← Marking.eval_def, eval_killWildLetters_deltaC, hτ, one_conjR, mul_one]

theorem eval_killWildLetters_eRevW_of_tau (t : Marking (2 + 2 * h) G)
    (hτ : t.τ ^ᶻ omega2 = 1) : (Marking.killWildLetters t).eval (eRevW α h) = 1 := by
  rw [eval_eRevW_eq_eBlock, eval_killWildLetters_deltaC, eval_killWildLetters_deltaC, hτ]
  simp [eBlock]

/-- **Gate B is blind to the block order**: the forward-order word dies at the tame boundary
under exactly the hypothesis that kills the frozen one (`eval_killWildLetters_mCompact_of_tau`),
so no admissibility statement at this layer can separate them. -/
theorem eval_killWildLetters_mFwdW_of_tau (t : Marking (2 + 2 * h) G)
    (hτ : t.τ ^ᶻ omega2 = 1) : (Marking.killWildLetters t).eval (mFwdW α h) = 1 := by
  rw [mFwdW,
    eval_mWordWith_congr (α := α) (Marking.killWildLetters t)
      (E' := eRevW α h)
      ((eval_killWildLetters_eFwdW_of_tau t hτ).trans
        (eval_killWildLetters_eRevW_of_tau t hτ).symm),
    mWordWith_eRevW]
  exact eval_killWildLetters_mCompact_of_tau α h t hτ

end

end Mutant

end GQ2.Dyadic.Words.MCompact
