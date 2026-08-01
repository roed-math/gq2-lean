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

/-! ## The `ω₂`-only fragment

The compact-`N` word uses no `ℤ₂`-power and no profinite exponent other than `ω₂`, so the whole
`ℕ`-exponent calculus of packet Lem. 2.2 applies to it with a single global exponent.  This is
what lets the numerical pins below evaluate the *genuine* `ω₂`, and what WN0-b will need to
transport the word into `FreeGroup`, where `ω₂` cannot be applied at all. -/

@[simp] theorem isOmega2Only_handlesW (h : ℕ) : (handlesW h).IsOmega2Only := by
  unfold handlesW
  refine isOmega2Only_prodList ?_
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact ⟨trivial, trivial⟩

@[simp] theorem isOmega2Only_nCompact (α h : ℕ) : (nCompactW α h).IsOmega2Only := by
  unfold nCompactW
  refine isOmega2Only_prodList ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨rfl, trivial, trivial, trivial⟩
  · exact isOmega2Only_handlesW h

/-! ## Gate B: the tame boundary

Packet Prop. 9.2's proof shape.  Killing the wild letters annihilates the leading power, the
commutator, the `x₂^{-σ}` factor and every handle; what survives is the `ω₂`-tail of the
`δ₂`-letter, `δ₂ = (x₂τ)^{ω₂}x₂⁻¹ ↦ τ^{ω₂}`.  That tail then dies by **Gate B rule T1** — `ω₂`
kills pro-odd elements — and *only* by T1: it is not a syntactic cancellation. -/

section Tame

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α h : ℕ}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp] theorem killWildLetters_coreLetter (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    Marking.killWildLetters t (coreLetter h i) = 1 := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp] theorem killWildLetters_handleU (t : Marking (2 + 2 * h) G) (j : Fin h) :
    Marking.killWildLetters t (handleU j) = 1 := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp] theorem killWildLetters_handleV (t : Marking (2 + 2 * h) G) (j : Fin h) :
    Marking.killWildLetters t (handleV j) = 1 := rfl

/-- Evaluating the handle block is MC2's `handleWord` on the handle letters — the same
`List.finRange h` order on both sides, so this is a rewrite and not a reindexing. -/
theorem eval_handlesW (t : Marking (2 + 2 * h) G) :
    t.eval (handlesW h) =
      MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  rw [Marking.eval_def, handlesW, PWord.eval_prodList, List.map_map]
  rfl

/-- **The tame boundary value of the compact-`N` word.**

Killing the wild letters leaves exactly `τ^{ω₂}`: every other factor is a word in the killed
letters alone.  Stating the *value* rather than "` = 1`" is deliberate — it is what makes the
T1 step below visible, and what shows that the death of this word at the tame boundary is a
fact about `τ`, not about the word's shape. -/
theorem eval_killWildLetters_nCompact (α h : ℕ) (t : Marking (2 + 2 * h) G) :
    (Marking.killWildLetters t).eval (nCompactW α h) = t.τ ^ᶻ omega2 := by
  have hH : PWord.eval ⇑(Marking.killWildLetters t) (handlesW h) = 1 := by
    rw [show PWord.eval ⇑(Marking.killWildLetters t) (handlesW h)
          = (Marking.killWildLetters t).eval (handlesW h) from rfl, eval_handlesW]
    exact MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)
  rw [Marking.eval_def, nCompactW, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_zpow,
    PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen,
    PWord.eval_omega2PowHat, PWord.eval_prodList, killWildLetters_coreLetter,
    one_zpow, commR_self, one_conjR, inv_one, one_mul, mul_one, hH]
  rfl

/-- The same statement through F2's **substitution operator**: the syntactic kill-wild rewrite
`killWild` evaluated at `t` (`Marking.eval_killWild`). -/
theorem eval_killWild_nCompact (α h : ℕ) (t : Marking (2 + 2 * h) G) :
    t.eval (killWild (nCompactW α h)) = t.τ ^ᶻ omega2 := by
  rw [Marking.eval_killWild, eval_killWildLetters_nCompact]

/-- **Gate-B admissibility, relativized to a tame `τ`** — packet Prop. 9.2.

The compact-`N` word dies at the tame boundary of every marking whose `τ`-letter is killed by
`ω₂`.  Inside `Γ_R` that hypothesis is *supplied*, by packet Lem. 3.1: the tame relation
`τ^σ = τ^{q}` with `q` even forces `τ` to be pro-odd (`GQ2.Dyadic.odd_order`), and `ω₂` kills
pro-odd elements. -/
theorem killsWild_of_tau (hτ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G),
      t.τ ^ᶻ omega2 = 1) :
    KillsWild (nCompactW α h) := by
  intro G _ _ _ _ _ t
  rw [eval_killWildLetters_nCompact]
  exact hτ G t

/-- **Gate B rule T1, at a finite marking**: if the `τ`-letter has odd order, the tame boundary
value is trivial.  This is the form the finite-target harnesses (F5) test. -/
theorem eval_killWildLetters_nCompact_eq_one_of_odd {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] (α h : ℕ) (t : Marking (2 + 2 * h) P)
    (hτ : Odd (orderOf t.τ)) : (Marking.killWildLetters t).eval (nCompactW α h) = 1 := by
  rw [eval_killWildLetters_nCompact]
  simpa using PWord.eval_omega2Pow_eq_one_of_odd (⇑t) (.gen .tau) hτ

end Tame

/-! ### ⚠ F3's `KillsWild` is *not* satisfiable by this word

A finding of the pilot lane, and the one statement in this file that the other four branch lanes
should read before writing theirs.

`GQ2.Dyadic.KillsWild R` quantifies over **every** profinite group and **every** marking, with no
relation imposed on the `τ`-letter.  By `eval_killWildLetters_nCompact` the tame boundary value
of the compact-`N` word is `τ^{ω₂}`, so `KillsWild` would force `τ^{ω₂} = 1` universally — false
already in `Multiplicative (ZMod 8)`.

This is not a defect in the *word*: the packet's hypothesis is about the tame quotient, where
`τ` is pro-odd by Lem. 3.1, and there the word is admissible (`killsWild_of_tau`,
`eval_killWildLetters_nCompact_eq_one_of_odd`).  It is a mismatch between F3's `∀`-form and the
packet's hypothesis, and every branch word with a `δ`-letter will hit it, because a `δ`-letter's
whole point is to carry `(x_iτ)^{ω₂}`.  **Recommended F3 amendment**: give `KillsWild` a
`τ`-pro-odd side condition, or quantify only over markings factoring through `Γ_R`.  Recorded
rather than acted on: `TameBoundary.lean` is not this ticket's file. -/

section Refutation

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

private theorem zmod8_orderOf_dvd (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- The refuting marking: `τ` a generator of `ZMod 8` (so `τ^{ω₂} = τ ≠ 1`), everything else
trivial.  The wild letters are irrelevant — `killWildLetters` overwrites them. -/
def refuteMarking (h : ℕ) : Marking (2 + 2 * h) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters 1 (Multiplicative.ofAdd 1) (fun _ => 1)

/-- **The frozen compact-`N` word is not Gate-B admissible in F3's unrelativized sense.** -/
theorem not_killsWild (α h : ℕ) : ¬ KillsWild (nCompactW α h) := by
  intro hR
  have hval := hR (Multiplicative (ZMod 8)) (refuteMarking h)
  rw [eval_killWildLetters_nCompact,
    PWord.zpowHat_omega2_zpow (by norm_num) (zmod8_orderOf_dvd _), omega2Exp_eight,
    show (refuteMarking h).τ = Multiplicative.ofAdd (1 : ZMod 8) from rfl, Nat.cast_one,
    zpow_one] at hval
  exact absurd hval (by decide)

end Refutation

/-! ## Gate C: the marked pro-`2` boundary

The headline of the ticket.  `pro2` sends `τ ↦ 1` and collapses every `ω₂`-power, so the third
and fourth factors become `(x₂^σ)⁻¹ · x₂`, and *that is the commutator* `[σ, x₂]`:

```
(x₂^σ)⁻¹ · x₂ = (σ⁻¹x₂σ)⁻¹ · x₂ = σ⁻¹x₂⁻¹σ · x₂ = [σ, x₂].
```

So the pro-`2` specialization is `x₀^{2+2^α}[x₀,x₁][σ,x₂] · H_h` = MC2's `nWord α x₀ x₁ σ x₂`
times MC2's `handleWord`.  This is where the `σ`-versus-`σ₂` choice pays: with `σ₂` the third
factor would not pair with the fourth. -/

section Pro2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α h : ℕ}

@[simp] theorem pro2_handlesW (h : ℕ) : pro2 (handlesW h) = handlesW h := by
  rw [handlesW, pro2_prodList, List.map_map]
  rfl

/-- **Gate C, syntactically**: the `τ`-letter is gone and the `ω₂`-power is collapsed; nothing
else moves.  The fourth factor is `x₂ · 1`, whose trailing `1` is the collapsed `τ`. -/
theorem pro2_nCompact (α h : ℕ) :
    pro2 (nCompactW α h) = PWord.prodList
      [.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α),
       .comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)),
       .inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)),
       PWord.prodList [.gen (coreLetter h 2), .one],
       handlesW h] := by
  rw [nCompactW, pro2_prodList]
  simp only [List.map_cons, List.map_nil, pro2_omega2Pow, pro2_handlesW, pro2_prodList,
    pro2_zpow, pro2_comm, pro2_inv, pro2_conj, pro2_gen_wild, pro2_gen_sigma, pro2_gen_tau,
    coreLetter]

/-- **The pro-`2` boundary value of the compact-`N` word is MC2's compact-`N` core.**

`pro2 R_{N,α,0}` evaluates, at *every* marking, to `nWord α x₀ x₁ σ x₂ · handleWord`.  No
hypothesis on the marking is needed: `pro2` has already removed `τ` and every `ω₂`, so the
identity is one of plain group words. -/
theorem eval_pro2_nCompact (α h : ℕ) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (nCompactW α h)) =
      MarkedCore.nWord α (t (coreLetter h 0)) (t (coreLetter h 1)) t.σ (t (coreLetter h 2)) *
        MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  have hH : PWord.eval ⇑t (handlesW h)
      = MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := eval_handlesW t
  rw [pro2_nCompact, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_zpow,
    PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_one,
    PWord.eval_prodList, mul_one, hH]
  -- The word's leading exponent is a genuine `ℤ`-power (`PWord.zpow`), MC2's core word's is an
  -- `ℕ`-power; align them before the group normalisation, or `group` cannot match `2 ^ α`
  -- against `↑(2 ^ α)`.
  rw [show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    MarkedCore.nWord, ← invConj_mul_self (t (coreLetter h 2)) t.σ]
  -- Both sides are now the same sequence of atoms; only the bracketing differs (`prodList` is
  -- right-nested, `nWord` left-nested).
  simp only [commR, commP, conjR, mul_assoc, Marking.apply_sigma]

/-- At `h = 0` the handle tail is the empty product and the pro-`2` value is MC2's core word on
the nose — the statement the ticket asks for, and the one MC2's rank-four theory consumes. -/
theorem eval_pro2_nCompact_zero (α : ℕ) (t : Marking 2 G) :
    t.eval (pro2 (nCompactW α 0)) = MarkedCore.nWord α (t.x 0) (t.x 1) t.σ (t.x 2) := by
  rw [eval_pro2_nCompact (α := α) (h := 0) (t := t),
    show MarkedCore.handleWord (fun j : Fin 0 => t (handleU j)) (fun j : Fin 0 => t (handleV j))
      = 1 from rfl, mul_one]
  rfl

/-- The same value read as MC2's **full relator shape** `nRelWord` at the standard marking
(`coreMark`: the four Labute letters, `1` on every handle letter). -/
theorem eval_pro2_nCompact_eq_nRelWord (α : ℕ) (t : Marking 2 G) :
    t.eval (pro2 (nCompactW α 0)) =
      MarkedCore.nRelWord (h := 0) α (MarkedCore.coreMark (t.x 0) (t.x 1) t.σ (t.x 2)) := by
  rw [eval_pro2_nCompact_zero, MarkedCore.nRelWord_coreMark]

end Pro2

/-! ## The `ℚ₂(√−2)` instance

`α = 2`, `h = 0`, `q_K = 2` — the branch row `BranchData.N0 2`, certificate
`N-compact-alpha2-h0-v001`, and the instance whose digest the selection freeze quotes for
row 2.  This is the word AS2 will take end-to-end. -/

/-- **The √−2 relation**, spelled out: `R_{N,2,0} = x₀⁶ [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂}`.

The leading exponent is `2 + 2² = 6`.  The trailing `PWord.one` is the empty handle block
`H_0` — it is a genuine factor of the tree (the certificate carries `HyperbolicHandles 3 0`,
which denotes to the empty product), not an artefact, and it is why this is stated as a
five-element `prodList`. -/
theorem nCompactW_two_zero :
    nCompactW 2 0 = PWord.prodList
      [.zpow (.gen (coreLetter 0 0)) 6,
       .comm (.gen (coreLetter 0 0)) (.gen (coreLetter 0 1)),
       .inv (.conj (.gen (coreLetter 0 2)) (.gen .sigma)),
       PWord.omega2Pow (PWord.prodList [.gen (coreLetter 0 2), .gen .tau]),
       .one] := rfl

/-- The `ℚ₂(√−2)` branch row is a valid compact-`N` row (F1/F4: `2 ≤ α`), at level `r = 0`. -/
theorem branchData_sqrtNegTwo :
    (BranchData.N0 2).Valid ∧ (BranchData.N0 2).level = 0 :=
  ⟨BranchData.valid_N0_iff.mpr (by norm_num), rfl⟩

/-! ## Numerical stress pins

Nothing below is cited by a proof; these are regression pins in the sense of plan §3 A1.

**The python twins are F5's rows** (`scripts/dyadic_sanity_counts.py`).  F5 measures the frozen
row `d=-2  N(alpha=2, r=0)` by its epimorphism-count vector over `(S₃, D₈, A₄)`, obtaining
`(6, 1568, 120)`, and its row **C4** re-runs the *same code* with the conjugator flipped to `σ₂`,
obtaining `(6, 1568, 504)`.  So `A₄` is what sees the σ-versus-σ₂ choice — `120` against `504` —
while `S₃` and `D₈` are blind to it.

Those counts are **cited, never proved here**: reproducing them in Lean needs genuine `ω₂` on a
group with a nontrivial odd part (`A₄`), i.e. an epimorphism enumeration, which is F5's job and
not a `decide`.  Note in particular that no *`2`-group* can witness the difference — on a group
of `2`-power exponent `ω₂` acts as the identity, so `σ₂ = σ` there identically. -/

section StressZMod8

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

private theorem orderOf_dvd_eight (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- A concrete marking of the compact-`N` alphabet at `h = 0`, written additively:
`(σ, τ, x₀, x₁, x₂) = (5, 1, 1, 1, 1)` in `Multiplicative (ZMod 8)`. -/
def zmod8Marking : Marking (2 + 2 * 0) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 1)
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]

/-- **Stress (genuine `ω₂`)**: the *profinite* denotation of the √−2 word — real `x ^ᶻ ω₂`
powers, not a hand-chosen integer exponent — is `ofAdd 7`.

Additively, and abelian so the commutator drops: `x₀⁶ = 6`, `[x₀,x₁] = 0`, `x₂^{-σ} = −1`,
`(x₂τ)^{ω₂} = 1·(1+1) = 2`, total `6 − 1 + 2 = 7`.  Pins three things at once: the leading
exponent `2 + 2² = 6`, the *inverse* on the `x₂^{-σ}` factor (dropping it would give `9 = 1`),
and the `ω₂` sitting on the whole `(x₂τ)` subword rather than on `x₂` alone (that would give
`6`). -/
theorem eval_zmod8_nCompact :
    zmod8Marking.eval (nCompactW 2 0) = Multiplicative.ofAdd (7 : ZMod 8) := by
  rw [Marking.eval_def, PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight,
    omega2Exp_eight]
  · decide
  · exact isOmega2Only_nCompact 2 0

/-- **Stress (`ω₂` is not vacuous)**: the same evaluation with the profinite exponent forced to
`3` — an odd non-`ω₂` representative — gives `6 − 1 + 3·2 = 11 = 3`, a different value.  So the
`ω₂`-slot genuinely carries information at this marking, and `eval_zmod8_nCompact` is not an
accident of the exponent happening to be `1`. -/
theorem evalNat_zmod8_nCompact_three :
    PWord.evalNat ⇑zmod8Marking 3 (nCompactW 2 0) = Multiplicative.ofAdd (3 : ZMod 8) := by
  decide

/-- **Stress (the tame boundary is not vacuous either)**: at this marking the `τ`-letter has
even order, so the Gate-B value `τ^{ω₂}` is *not* trivial — which is `not_killsWild` again,
read numerically.  Inside `Γ_R`, where `τ` is pro-odd, this value is `1`. -/
theorem eval_killWildLetters_zmod8 :
    (Marking.killWildLetters zmod8Marking).eval (nCompactW 2 0)
      = Multiplicative.ofAdd (1 : ZMod 8) := by
  rw [eval_killWildLetters_nCompact,
    PWord.zpowHat_omega2_zpow (by norm_num) (orderOf_dvd_eight _), omega2Exp_eight]
  decide

end StressZMod8

/-- **Stress (nonabelian: the core is not a vacuous relator)**: MC2's compact-`N` core word is
nontrivial at an explicit marking of `S₃`, so the two commutators do real work.

In `S₃` every element satisfies `a⁶ = 1`, so the leading power `a^{2+2²}` drops out entirely and
everything that survives comes from `[a,b]·[c,d]`.  At two distinct transpositions each
commutator is the *same* `3`-cycle `g`, so the core word is `g² ≠ 1`.

An explicit witness rather than `∃ … by decide`: the search over `S₃⁴` exhausts the kernel's
recursion budget, and a witness costs nothing.  F5's row for this group reports the
epimorphism count `6`; that number is *not* what is proved here (see the section note). -/
theorem nWord_ne_one_perm :
    MarkedCore.nWord 2 (Equiv.swap 0 1) (Equiv.swap 0 2) (Equiv.swap 0 1) (Equiv.swap 0 2)
      ≠ (1 : Equiv.Perm (Fin 3)) := by decide

end GQ2.Dyadic.Words
