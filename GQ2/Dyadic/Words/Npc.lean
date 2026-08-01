/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.NpcJet.Defs

/-!
# Dyadic campaign, ticket WNP-a: the corrected noncompact (procyclic-`N`) branch word

The second of the five wave-2 branch-word files, written against the WN0-a template.  It carries
**row 3 of the R5 selection freeze** (`general_2adic/artifacts/reports/selection-freeze.md`), the
noncompact-`N` relator at level `r ≥ 1`

```
R_{N,α,r,η} = x₀^{p_α} [x₀, A] · x₂^{-g} (x₂τ)^{ω₂} · E_{r,η} · H_h,   p_α = 2 + 2^α,  α ≥ 2
A = σ^{η̂},   B = σ^{2^r},   g = x₁ σ^{2^r},
D_{r,η} = δ₀^A (δ₀ δ₀^A)^{B⁻¹},     E_{r,η} = [D_{r,η}, x₁],    δ₀ = (x₀τ)^{ω₂} x₀⁻¹
```

as an F2 `PWord` over `Generator (2 + 2h)`, together with its two boundary specializations, the
`(α,r,η) = (2,1,1)` instance, and the WW5 one-tree hash pins for all **seven** emitted instances.

## This is the corrected word

Draft display `eq:Ncross` is **refuted as displayed** (S3.2, machine-verified; errata item 5).
The true cross operators are `L_c = A⁻¹ + B + B·A⁻¹` and `M_c = adj(L_c)`, not the draft's
`L_c = A⁻¹`, and the correction is carried by the block `E_{r,η}` — which is *why* this word has
a fifth factor that the compact-`N` word (`GQ2/Dyadic/Words/N0.lean`) does not.  The Lean design
of record for that correction is the **NC lane**, `GQ2/Dyadic/NpcJet/`, and §4 below discharges
this ticket's *pre-agreement* obligation against it.

`D_{r,η}` is written in the **compressed** spelling `δ₀^A (δ₀ δ₀^A)^{B⁻¹}`.  That is the frozen
form (selection-freeze row 3; §8.3's compression *is* the frozen spelling), and it is forced:
the expanded reading `δ₀^{σ^{η̂}} δ₀^{σ^{−2^r}} δ₀^{σ^{η̂−2^r}}` needs the sum exponent
`η̂ − 2^r`, which **has no AST node**.  The compressed form writes the same element as a single
conjugation of `δ₀ δ₀^A` by `B⁻¹`.

## What is pinned, and against what

`rawNpc α r h e` is the **certificate tree** — the `Export.RawWord` interchange form, restated
here in the emitted spelling of `general_2adic/generated/lean/N_noncompact_*.lean`.  Those emitted
files are standalone (each declares its own `RawWord` prelude and is imported by nothing), so they
cannot be imported; restating the tree against the real `GQ2.Dyadic` vocabulary and pinning its
digest is the sanctioned route, and it is what the seven `#eval Export.assertAstHash` guards below
check.  Keying is by `candidate_id`, never by `word_hash` (S5.G: q2/q4 twins share hashes in the
`M` families; the `N_noncompact` digests below happen to be distinct, but the convention is the
convention).  All seven frozen instances are covered:

| `(α, r, η, h)` | certificate | digest |
|---|---|---|
| `(2, 1, 1, 0)` | `N-noncompact-alpha2-r1-eta1_1-h0-v001` | `08b7742caf3a34f8…` |
| `(2, 1, 1, 1)` | `N-noncompact-alpha2-r1-eta1_1-h1-v001` | `89c418c4a7e57b0d…` |
| `(2, 1, −1, 0)` | `N-noncompact-alpha2-r1-etam1_1-h0-v001` | `a6cccf74bfafde11…` |
| `(2, 1, −1/5, 0)` | `N-noncompact-alpha2-r1-etam1_5-h0-v001` | `552fd470fd82b3e6…` |
| `(2, 2, 1, 0)` | `N-noncompact-alpha2-r2-eta1_1-h0-v001` | `b282255367bb55ed…` |
| `(3, 1, 1, 0)` | `N-noncompact-alpha3-r1-eta1_1-h0-v001` | `3549d6ef8cf6781d…` |
| `(3, 1, −1/9, 0)` | `N-noncompact-alpha3-r1-etam1_9-h0-v001` | `9022e09e6ac47398…` |

`npcW α r h e` is the **semantic word**, and the seven `denote_rawNpc_*` theorems prove it is *the
denotation of the hashed tree* — not merely a word that looks like it.

## Authoring rules followed (WW5/S5.G, WN0-a's distilled template)

1. **The certificate's spelling, not a normalized one.**  `.integerPower … (.int n)` and never
   `.zhatPower … (.int n)`; `ω₂` through `omega2Power`; `η̂` through the dedicated `etahat` spec
   (S5.G: `.etahat` is the *only* `RawSpec` used by any frozen word, and every exponent is a
   literal `Int`, so `denoteCtx.param` is never consulted).
2. **`x₂^{-g}` is `Inverse ∘ Conjugate`**, and `B⁻¹` is `Inverse ∘ IntegerPower`.  Both are the
   certificate's associations, and neither is F2's sugar; see §4, divergences (D2) and (D3).
3. **Every `Multiply` is `PWord.prodList`**, including the two-element ones — `prodList` is
   right-nested *onto `PWord.one`*, and writing a binary `.mul` instead is the one edit that
   makes the `denote` bridges fail and nothing else.
4. **Handles at general `h`, with `h = 0` and `h = 1` both pinned.**
5. **`<decl>_astHash` + `#eval Export.assertAstHash`**, one pair per instance.  `native_decide`
   appears nowhere: the census must stay at eleven.
6. **Generator names by a literal `match` table** — `String.toNat?` is well-founded recursion and
   does not reduce in the kernel, which would put the `denote` bridges out of reach of `rfl`.

## ⚠ The `η̂`-power breaks `IsOmega2Only`

Unlike the compact-`N` word, this word is **not** in the `ω₂`-only fragment: `A = σ^{η̂}` is a
profinite power with `γ ≠ ω₂`.  So WN0-a's route to numerical stress pins — `PWord.eval_eq_evalNat_of_dvd`,
which needs `IsOmega2Only` — is **unavailable here**, and §8 uses the two honest resolvers instead
(`zpowHat_etaHatZ_of_odd` for `η̂`, `zpowHat_omega2_zpow` for `ω₂`).  This is recorded as a fact
(`not_isOmega2Only_npcW`), not as a docstring claim, and it is the first thing WMP-a should expect
too: every branch word with an `η̂`-conjugator inherits it.

## Implementation notes

This file is **not** `module`-style, forced exactly as `N0.lean` is: it imports
`GQ2.Dyadic.TameBoundary` (F3), which is not `module`-style, and a `module` file may not import a
non-`module` one.  The `GQ2.Dyadic.NpcJet.Defs` import is likewise plain and legal.

Everything lives in the nested namespace `GQ2.Dyadic.Words.Npc`, one segment deeper than N0's
declarations, which sit directly in `GQ2.Dyadic.Words`.  The nesting is deliberate: the alphabet
toolkit (`coreLetter`, `handleU`, `handleV`, `wildGen`, `genOfName`, `denoteCtx`, `handlesW`) is
**identical** to N0's, so sharing the namespace would clash and importing N0 would couple two
independently-owned lane files.  ⚠ That toolkit is now duplicated twice and will be duplicated
five times — a `Words/Alphabet.lean` hoist is the obvious cleanup, exactly parallel to WN0-c's
`~350`-line certificate-toolkit finding that produced the WWH ticket.  Recorded, not acted on.
-/

namespace GQ2.Dyadic.Words

namespace Npc

open Export (RawWord)

/-! ## §0. The noncompact-`N` alphabet

The word uses `x₀, x₁, x₂` and `σ, τ`; the `h` handle pairs use `x₃, …, x_{2h+2}`.  So the
alphabet is `Generator (2 + 2h)`, whose wild letters are `Fin (2h + 3)` — the same shape as the
compact row, since `E_{r,η}` introduces no new letters (`δ₀` is built from `x₀` and `τ`).
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

/-- The wild letter `x_i`, or `none` when `i` is past the alphabet — the `handleGen` field of the
denotation context, whose index is a plain `ℕ`. -/
def wildGen (h : ℕ) (i : ℕ) : Option (Generator (2 + 2 * h)) :=
  if hi : i < 2 * h + 3 then some (.wild ⟨i, by omega⟩) else none

/-- The generator names the noncompact-`N` certificate uses.  A literal table, not a decimal
parser: `String.toNat?` does not reduce in the kernel.  Handle letters come through `wildGen`,
which is why the table stops at `x₂`. -/
def genOfName (h : ℕ) (s : String) : Option (Generator (2 + 2 * h)) :=
  match s with
  | "sigma" => some .sigma
  | "tau" => some .tau
  | "x0" => wildGen h 0
  | "x1" => wildGen h 1
  | "x2" => wildGen h 2
  | _ => none

/-- The denotation context of the noncompact-`N` row: the certificate's names, the handle letters,
and **no** symbolic parameters.  Every frozen exponent in this row is a literal `Int` and the only
profinite specs are `omega2` and `etahat` (S5.G), so `param` is nowhere consulted and returning
`none` is honest rather than lossy. -/
def denoteCtx (h : ℕ) : Export.DenoteCtx (Generator (2 + 2 * h)) where
  gen := genOfName h
  handleGen := wildGen h
  param := fun _ => none

/-! ## §1. The word

Built bottom-up in the certificate's order: `δ₀`, the two conjugators `A` and `B`, the compressed
`D`-block, the correction `E`, the handle block, and the relator. -/

/-- `H_h = ∏_{j<h} [x_{3+2j}, x_{4+2j}]`, the block the certificate writes as
`HyperbolicHandles 3 h`, as a `prodList` over `List.finRange h` — simultaneously what
`Export.handleFactors` expands the node to and how MC2's `handleWord` orders its factors. -/
def handlesW (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

@[simp] theorem handlesW_zero : handlesW 0 = .one := rfl

/-- **The `δ`-letter `δ₀ = (x₀τ)^{ω₂} x₀⁻¹`** in the certificate's spelling.

The tree carries it as `Auxiliary "d0"` wrapping an `Auxiliary "u0"` — display and complexity
bookkeeping which `Export.denote` inlines — so what it denotes to is this two-element `prodList`.
Semantically this is F2's `deltaW 0`; syntactically it is not, because F2 uses binary `.mul`.  See
§4, divergence (D1). -/
noncomputable def deltaZeroW (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 0), .gen .tau]),
     .inv (.gen (coreLetter h 0))]

/-- **The conjugator `A = σ^{η̂}`**, the profinite `η̂`-power of `σ`.

`η` is carried as the syntactic `EtaData` pair `⟨num, den⟩` of the certificate's `etahat` spec,
and `EtaData.toZhat ⟨num, den⟩` is *by definition* `etaHatZ (num · den⁻¹)` — which is why the NC
lane's `PWord.etaPow` shape and this one agree on the nose (§4, non-divergence (D5)). -/
noncomputable def aW (h : ℕ) (e : EtaData) : PWord (Generator (2 + 2 * h)) :=
  .profPow (.gen .sigma) e.toZhat

/-- **The conjugator `B = σ^{2^r}`**, a genuine `ℤ`-power.  `r ≥ 1` is the noncompact condition;
nothing below needs it, and `r = 0` would give back a compact-shaped conjugator. -/
def bW (h r : ℕ) : PWord (Generator (2 + 2 * h)) :=
  .zpow (.gen .sigma) (2 ^ r)

/-- **The compressed `D`-block** `D_{r,η} = δ₀^A (δ₀ δ₀^A)^{B⁻¹}` (selection-freeze row 3).

The second conjugator is `.inv (bW h r)` — the certificate's `Inverse ∘ IntegerPower`, i.e.
`(σ^{2^r})⁻¹` and **not** `σ^{−2^r}`.  Both denote the same group element (`zpow_neg`), only one
of them hashes; see §4, divergence (D3). -/
noncomputable def dBlockW (h r : ℕ) (e : EtaData) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.conj (deltaZeroW h) (aW h e),
     .conj (PWord.prodList [deltaZeroW h, .conj (deltaZeroW h) (aW h e)]) (.inv (bW h r))]

/-- **The correction block** `E_{r,η} = [D_{r,η}, x₁]`.

This is the entire content of the S3.2 correction.  `E_{r,η}` is invisible at the tame boundary
(§5), invisible at the marked pro-`2` boundary (§6) and invisible at first Fox order, and it is
what makes the second-order cross operator `L_c = A⁻¹ + B + B·A⁻¹` rather than the draft's
`A⁻¹`: the three conjugators `A`, `1`, `B⁻¹` of the expanded `D`-block contribute the three
summands (NC lane, memo §3.2). -/
noncomputable def eBlockW (h r : ℕ) (e : EtaData) : PWord (Generator (2 + 2 * h)) :=
  .comm (dBlockW h r e) (.gen (coreLetter h 1))

/-- **The frozen corrected noncompact-`N` branch word** (selection freeze row 3; draft
eq. `Npc-word`, as corrected by S3.2)

```
R_{N,α,r,η} = x₀^{2+2^α} · [x₀, A] · x₂^{-g} · (x₂τ)^{ω₂} · E_{r,η} · H_h
```

with `α ≥ 2`, `r ≥ 1`, `η ∈ ℤ₂ˣ`, `A = σ^{η̂}`, `g = x₁σ^{2^r}`, and `h` hyperbolic handles.  The
**six** factors are the six children of the certificate's `Multiply` node, in order; the compact
row has five, and the extra one is `E_{r,η}`.

Two conjugator choices distinguish this word from the compact row and both are load-bearing:
the commutator's right argument is `A = σ^{η̂}` rather than `x₁`, and the boundary conjugator is
`g = x₁σ^{2^r}` rather than `σ`.  Together they are what turns the pro-`2` value into MC2's `N`
core *at twisted Labute letters* (§6). -/
noncomputable def npcW (α r h : ℕ) (e : EtaData) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α),
     .comm (.gen (coreLetter h 0)) (aW h e),
     .inv (.conj (.gen (coreLetter h 2)) (PWord.prodList [.gen (coreLetter h 1), bW h r])),
     PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
     eBlockW h r e,
     handlesW h]

/-- The freeze's **spelling discipline** for the leading exponent, shared with the compact row:
`2 + 2^α` is opaque, while `2(1 + 2^{α−1})` displays the Hessian content — `1 + 2^{α−1}` is odd
exactly when `α ≥ 2`, and that oddness is what produces the `Q₀(c₀)` term of the plus form
`Q(c₀,c₁) = Q₀(c₀) + b_q(c₁, L_c c₀)`.  The *word* keeps the certificate's `2 + 2^α`. -/
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

/-! ## §2. The certificate tree and the WW5 hash pins -/

/-- The certificate's `δ₀`, with both `Auxiliary` wrappers as emitted.  `denote` inlines them, but
the hash is of the tree *with* them, so they must be here. -/
def rawDeltaZero : RawWord :=
  .auxiliary "d0"
    (.multiply
      [.auxiliary "u0" (.omega2Power (.multiply [.generator "x0", .generator "tau"])),
       .inverse (.generator "x0")])

/-- The certificate's `A = σ^{η̂}`: a `ZhatPower` node carrying the `etahat` spec. -/
def rawA (num den : ℤ) : RawWord := .zhatPower (.generator "sigma") (.etahat num den)

/-- The certificate's compressed `D`-block `δ₀^A (δ₀ δ₀^A)^{B⁻¹}`. -/
def rawD (r : ℕ) (num den : ℤ) : RawWord :=
  .multiply
    [.conjugate rawDeltaZero (rawA num den),
     .conjugate (.multiply [rawDeltaZero, .conjugate rawDeltaZero (rawA num den)])
       (.inverse (.integerPower (.generator "sigma") (.int (2 ^ r))))]

/-- **The noncompact-`N` certificate tree**, in the spelling emitted by
`general_2adic/generated/lean/N_noncompact_alpha{2,3}_r{1,2}_eta*_h{0,1}_v001.lean`. -/
def rawNpc (α r h : ℕ) (num den : ℤ) : RawWord :=
  .multiply
    [.integerPower (.generator "x0") (.int (2 + 2 ^ α)),
     .commutator (.generator "x0") (rawA num den),
     .inverse
       (.conjugate (.generator "x2")
         (.multiply [.generator "x1", .integerPower (.generator "sigma") (.int (2 ^ r))])),
     .omega2Power (.multiply [.generator "x2", .generator "tau"]),
     .commutator (rawD r num den) (.generator "x1"),
     .hyperbolicHandles 3 (.int h)]

/-- **Well-formedness is conditional here**, unlike the compact row: `RawSpec.wf` demands that
every `etahat` entry be odd, and this tree carries three of them.  So the precondition of the
seven `assertAstHash` guards below is exactly the oddness of `η`'s numerator and denominator —
which is not a formality but the statement that `η = num·den⁻¹` really is a `2`-adic **unit**. -/
theorem wf_rawNpc (α r h : ℕ) {num den : ℤ} (hn : num % 2 ≠ 0) (hd : den % 2 ≠ 0) :
    (rawNpc α r h num den).wf = true := by
  simp [rawNpc, rawA, rawD, rawDeltaZero, Export.RawWord.wf, Export.RawWord.wfList,
    Export.RawSpec.wf, hn, hd]

/-- The four frozen `η`-pairs are `S1.M`-canonical (positive denominator, gcd-reduced), so the
`RawSpec.canon` pass that precedes hashing is the identity on them and the digests below are
digests of the trees exactly as written. -/
theorem etaData_canonical :
    (EtaData.mk 1 1).IsCanonical ∧ (EtaData.mk (-1) 1).IsCanonical ∧
      (EtaData.mk (-1) 5).IsCanonical ∧ (EtaData.mk (-1) 9).IsCanonical := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact ⟨by norm_num, by decide⟩

/-! ### The gate-A constants

One `<decl>_astHash` constant and one `#eval Export.assertAstHash` guard per frozen instance —
the WW5 convention (`pretty_lean.py`'s `HASH_SUFFIX`).  The `#eval` recomputes the digest from the
tree, so a constant cannot drift away from the word it labels, and the digests are the ones stored
in the simplification campaign's certificates, so a green elaboration is a cross-repo agreement
rather than a self-consistency check.

The seven instances span the parameter directions independently: `η ≠ 1` (two sign rows and two
genuinely fractional rows), `r = 2` (so the `2^r` slot is exercised, not just read), `α = 3` (so
`p_α` is exercised), and `h = 1` (so the handle block is not vacuous). -/

/-- Gate-A hash of `rawNpc 2 1 0 1 1`, certificate `N-noncompact-alpha2-r1-eta1_1-h0-v001` — the
**frozen-Npc harness pin**, `(α,r,η) = (2,1,1)`, whose `F5` epimorphism-count vector over
`(S₃, D₈, A₄)` is `6/1568/120`. -/
def rawNpc_a2_r1_eta1_1_h0_astHash : String :=
  "08b7742caf3a34f8152833b1849acd5e1e7df17be50dd68d9c511d966f4fd205"

/-- Gate-A hash of `rawNpc 2 1 1 1 1`, certificate `N-noncompact-alpha2-r1-eta1_1-h1-v001` — the
one-handle instance, which is what makes the `h`-generality of this file testable. -/
def rawNpc_a2_r1_eta1_1_h1_astHash : String :=
  "89c418c4a7e57b0daedee1aa33f09017566351336cc14ac431999890f0dde565"

/-- Gate-A hash of `rawNpc 2 1 0 (-1) 1`, certificate `N-noncompact-alpha2-r1-etam1_1-h0-v001`
— the `η = −1` row. -/
def rawNpc_a2_r1_etam1_1_h0_astHash : String :=
  "a6cccf74bfafde112021ca16b89730104c272a8c3ccb2d353b1f04284cd31c54"

/-- Gate-A hash of `rawNpc 2 1 0 (-1) 5`, certificate `N-noncompact-alpha2-r1-etam1_5-h0-v001`
— the `η = −1/5` row, where the `etahat` denominator is a nontrivial `2`-adic unit. -/
def rawNpc_a2_r1_etam1_5_h0_astHash : String :=
  "552fd470fd82b3e632c704897d6f77298f09aae5e5031d77bdab41a0093d8dcc"

/-- Gate-A hash of `rawNpc 2 2 0 1 1`, certificate `N-noncompact-alpha2-r2-eta1_1-h0-v001` — the
`r = 2` row, where `B = σ⁴`. -/
def rawNpc_a2_r2_eta1_1_h0_astHash : String :=
  "b282255367bb55eddbd02cc99729a0cb4e686c1fd8945e1618237106d79ea004"

/-- Gate-A hash of `rawNpc 3 1 0 1 1`, certificate `N-noncompact-alpha3-r1-eta1_1-h0-v001` — the
`α = 3` row, where `p_α = 10`. -/
def rawNpc_a3_r1_eta1_1_h0_astHash : String :=
  "3549d6ef8cf6781d52a54047e5f69504e4ed0b8fbd85bc50db8069346807836d"

/-- Gate-A hash of `rawNpc 3 1 0 (-1) 9`, certificate `N-noncompact-alpha3-r1-etam1_9-h0-v001`
— the `η = −1/9` row at `α = 3`. -/
def rawNpc_a3_r1_etam1_9_h0_astHash : String :=
  "9022e09e6ac4739858958d44d773d869b4eb2bbab37cc0a917435caf7cb987f9"

#eval Export.assertAstHash "WNP N-noncompact-alpha2-r1-eta1_1-h0-v001" (rawNpc 2 1 0 1 1)
  rawNpc_a2_r1_eta1_1_h0_astHash

#eval Export.assertAstHash "WNP N-noncompact-alpha2-r1-eta1_1-h1-v001" (rawNpc 2 1 1 1 1)
  rawNpc_a2_r1_eta1_1_h1_astHash

#eval Export.assertAstHash "WNP N-noncompact-alpha2-r1-etam1_1-h0-v001" (rawNpc 2 1 0 (-1) 1)
  rawNpc_a2_r1_etam1_1_h0_astHash

#eval Export.assertAstHash "WNP N-noncompact-alpha2-r1-etam1_5-h0-v001" (rawNpc 2 1 0 (-1) 5)
  rawNpc_a2_r1_etam1_5_h0_astHash

#eval Export.assertAstHash "WNP N-noncompact-alpha2-r2-eta1_1-h0-v001" (rawNpc 2 2 0 1 1)
  rawNpc_a2_r2_eta1_1_h0_astHash

#eval Export.assertAstHash "WNP N-noncompact-alpha3-r1-eta1_1-h0-v001" (rawNpc 3 1 0 1 1)
  rawNpc_a3_r1_eta1_1_h0_astHash

#eval Export.assertAstHash "WNP N-noncompact-alpha3-r1-etam1_9-h0-v001" (rawNpc 3 1 0 (-1) 9)
  rawNpc_a3_r1_etam1_9_h0_astHash

/-! ### The `denote` bridge

What makes the hash pins bite on the *semantic* word.  `Export.denote` expands the handle block,
inlines the two `Auxiliary` wrappers of `δ₀`, and resolves the names and specs; these seven `rfl`s
say that doing so to the hashed tree produces exactly `npcW`.

One per pinned instance, because `denote` expands `hyperbolicHandles` only at a concrete length
(wave-2 authoring rule (2)); the `h`-generic statement is not available, and inventing one would
mean re-encoding the block, which WW5 forbids. -/

theorem denote_rawNpc_a2_r1_eta1_1_h0 :
    Export.denote (denoteCtx 0) (rawNpc 2 1 0 1 1) = some (npcW 2 1 0 ⟨1, 1⟩) := by rfl

theorem denote_rawNpc_a2_r1_eta1_1_h1 :
    Export.denote (denoteCtx 1) (rawNpc 2 1 1 1 1) = some (npcW 2 1 1 ⟨1, 1⟩) := by rfl

theorem denote_rawNpc_a2_r1_etam1_1_h0 :
    Export.denote (denoteCtx 0) (rawNpc 2 1 0 (-1) 1) = some (npcW 2 1 0 ⟨-1, 1⟩) := by rfl

theorem denote_rawNpc_a2_r1_etam1_5_h0 :
    Export.denote (denoteCtx 0) (rawNpc 2 1 0 (-1) 5) = some (npcW 2 1 0 ⟨-1, 5⟩) := by rfl

theorem denote_rawNpc_a2_r2_eta1_1_h0 :
    Export.denote (denoteCtx 0) (rawNpc 2 2 0 1 1) = some (npcW 2 2 0 ⟨1, 1⟩) := by rfl

theorem denote_rawNpc_a3_r1_eta1_1_h0 :
    Export.denote (denoteCtx 0) (rawNpc 3 1 0 1 1) = some (npcW 3 1 0 ⟨1, 1⟩) := by rfl

theorem denote_rawNpc_a3_r1_etam1_9_h0 :
    Export.denote (denoteCtx 0) (rawNpc 3 1 0 (-1) 9) = some (npcW 3 1 0 ⟨-1, 9⟩) := by rfl

end Npc

end GQ2.Dyadic.Words
