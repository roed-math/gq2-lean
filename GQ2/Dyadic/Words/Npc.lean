/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.NpcJet.Defs
import GQ2.Dyadic.Words.Alphabet

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

## Audited axiom state

All **84** declarations were checked with `#print axioms`, and every one of them depends on a
**subset of the standard three** `[propext, Classical.choice, Quot.sound]` — 55 on all three, 12
on `[propext, Quot.sound]`, 4 on `[propext]`, and 9 on nothing at all.  In particular the twelve
headlines

`wf_rawNpc`, `denote_rawNpc_a2_r1_eta1_1_h0` (and its six siblings),
`eval_npcW_eq_eval_npcWord`, `eval_killWildLetters_npcW`, `not_killsWild`,
`etaHatZ_ne_omega2`, `not_isOmega2Only_npcW`, `eval_pro2_npcW`, `eval_npcW_of_comm`,
`eval_zmod8_npcW`, `dBlockG_ne_one_perm`, `eBlockG_ne_one_perm`

each print exactly `[propext, Classical.choice, Quot.sound]`.  No campaign axiom is reachable from
this file, and **no `Lean.ofReduceBool`**: every decision procedure used here is kernel `decide`,
never `native_decide`, so the census stays at eleven.
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

/-! ## §4. Pre-agreement with the NC lane's `npcWord`

The ticket's cross-lane obligation: this file's word must **pre-agree** with
`GQ2.Dyadic.NpcJet.npcWord`, the word the corrected-cross-operator lane (`NpcJet/`) proves
`npc_cross_operators` about.  The two are built from the same mathematics and are *not* the same
`PWord`, and the honest report of that is the point of this section.

### The four divergences, and the one non-divergence

**(D5) — not a divergence.**  `η` routing agrees *definitionally*.  The certificate carries the
syntactic pair `⟨num, den⟩`, whose `Zhat` value is `EtaData.toZhat ⟨num,den⟩`; the NC lane writes
`PWord.etaPow _ η = .profPow _ (etaHatZ η)`.  Since `EtaData.toZhat e` **is** `etaHatZ e.toPadic`
by definition, taking `η := e.toPadic` makes the two conjugators the same term
(`aW_eq_etaPow`, `rfl`).  No `η̂`-bridge lemma is owed to anybody.

**(D1) `prodList` vs binary `.mul`.**  The certificate's `Multiply` is `n`-ary and `Export.denote`
folds it with `PWord.prodList`, which is right-nested *onto `PWord.one`*, so a two-element
`Multiply` denotes to `u · (v · 1)` and not to `.mul u v` (`prodList_pair`).  The NC lane writes
binary `.mul` throughout.  This hits `δ₀`, the `(x₂τ)` subword, the `D`-block, and the
conjugator `g`.

**(D2) `x₂^{-g}` association.**  The certificate emits `Inverse ∘ Conjugate`, i.e. `(x₂^g)⁻¹`;
the NC lane uses F2's sugar `PWord.invConj = Conjugate ∘ Inverse`, i.e. `(x₂⁻¹)^g`.  Different
constructors (`invConj_ne_inv_conj`), same group element (`conjR_inv`).  This is WN0-a's rule (iii)
recurring verbatim, and it is a genuine *ratified* choice: the certificate chose, so the hashed
word has the `Inverse` outermost.

**(D3) `B⁻¹` spelling.**  The certificate emits `Inverse ∘ IntegerPower`, `(σ^{2^r})⁻¹`; the NC
lane writes the negative power `σ^{−2^r}`.  Different constructors (`zpow_neg_ne_inv_zpow`), same
group element (`zpow_neg`).

**(D4) the handle slot.**  The certificate tree always carries a sixth `HyperbolicHandles` child;
`npcWord` is the `h = 0` core only, and NC6 appends handles separately as `npcWordH` over
`Generator (m+2)`.  At `h = 0` the sixth factor denotes to `1`, so the arities coincide.

### The outcome

A **literal** cross-identification is therefore *not* available — the two words differ as syntax
trees at (D1)–(D4), and no rewriting of this file can change that without breaking the hash.  What
*is* available, and is what the downstream lanes actually need, is the **value-level** identity
below: at `h = 0` the hash-pinned word and `NpcJet.npcWord` evaluate to the same group element at
every marking of every profinite group.  That is exactly the transport that lets WNP-b/c cite
`npc_cross_operators` about the *certificate's* word rather than about a lookalike.

⚠ **The `h`-general form is not stated**, and the obstruction is arity spelling, not mathematics:
this file's alphabet is `Generator (2 + 2h)` (WN0-a's ratified convention, matching `Export`'s and
MC2's handle indexing) while `npcWordH` lives over `Generator (m + 2)` at `m = 2h`, and
`2 + 2*h` is not definitionally `2*h + 2` for a variable `h`.  On top of that `npcHandles` is
*left*-nested with free index functions where `handlesW` is a `prodList` over `List.finRange h`.
WNP-b/c should route the handled statement through NC6's `npc_cross_operators_handles_std`
(which already fixes `n = 2 + 2h` and the letters `x_{3+2j}, x_{4+2j}`) together with the handle
value-bridge `eval_handlesW` below, not through a cast on `npcWordH`. -/

/-- **(D5)** The `η̂`-conjugator of the certificate *is* the NC lane's `etaPow`, on the nose. -/
theorem aW_eq_etaPow (h : ℕ) (e : EtaData) :
    aW h e = (PWord.gen (Generator.sigma (n := 2 + 2 * h))).etaPow e.toPadic := rfl

/-- **(D1)** A two-element `Multiply` denotes to a product *onto `PWord.one`*.  Stated so the
divergence is a checked fact rather than a docstring claim. -/
theorem prodList_pair {Gen : Type*} (u v : PWord Gen) :
    PWord.prodList [u, v] = .mul u (.mul v .one) := rfl

/-- **(D2)** The certificate's association and F2's sugar are different constructors. -/
theorem invConj_ne_inv_conj {n : ℕ} (u g : PWord (Generator n)) :
    PWord.invConj u g ≠ .inv (.conj u g) := by
  simp [PWord.invConj]

/-- **(D3)** The negative power and the inverted power are different constructors. -/
theorem zpow_neg_ne_inv_zpow {n : ℕ} (u : PWord (Generator n)) (k : ℤ) :
    (PWord.zpow u (-k)) ≠ .inv (.zpow u k) := by
  simp

section PreAgreement

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The pre-agreement identity.**  At `h = 0`, the hash-pinned certificate word and the NC
lane's `npcWord` are the same group element at every marking of every profinite group, with
`η := e.toPadic`.

This is the bridge WNP-b/c consume: it transports `NpcJet.npc_cross_operators` — the corrected
`L_c = A⁻¹ + B + B·A⁻¹` identity — onto the word whose digest this file pins.  The proof is
exactly the four divergences being value-preserving: `mul_one` for (D1), `conjR_inv` for (D2),
`zpow_neg` for (D3), and `handlesW_zero` for (D4). -/
theorem eval_npcW_eq_eval_npcWord (α r : ℕ) (e : EtaData) (t : Marking 2 G) :
    t.eval (npcW α r 0 e) = t.eval (NpcJet.npcWord α r e.toPadic) := by
  rw [Marking.eval_def, Marking.eval_def, npcW, NpcJet.npcWord, NpcJet.npcEBlock,
    NpcJet.npcDBlock, eBlockW, dBlockW, deltaZeroW, deltaW, aW, bW]
  simp only [PWord.eval_prodList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.eval_mul, PWord.eval_zpow, PWord.eval_comm, PWord.eval_inv, PWord.eval_conj,
    PWord.eval_gen, PWord.eval_profPow, PWord.eval_invConj, PWord.omega2Pow, PWord.etaPow,
    handlesW_zero, PWord.eval_one, mul_one, conjR_inv, zpow_neg, coreLetter]
  rfl

end PreAgreement

/-! ## §5. Gate B: the tame boundary

Packet Prop. 9.2's proof shape.  Killing the wild letters annihilates the leading power, the
`[x₀,A]` commutator, the `x₂^{-g}` factor, **the whole correction block**, and every handle; what
survives is the `ω₂`-tail of the `δ₂`-letter, `δ₂ = (x₂τ)^{ω₂}x₂⁻¹ ↦ τ^{ω₂}`.  That tail then
dies by **Gate B rule T1** — `ω₂` kills pro-odd elements — and *only* by T1.

⚠ Note *why* `E_{r,η}` dies, because it is not the reason one first guesses.  `D_{r,η}` does
**not** die: `δ₀ = (x₀τ)^{ω₂}x₀⁻¹ ↦ τ^{ω₂}`, so the killed `D`-block is a nonempty product of
conjugates of `τ^{ω₂}`.  What kills `E_{r,η} = [D_{r,η}, x₁]` is the *other* argument — `x₁ ↦ 1`
and `[·, 1] = 1`.  So the tame invisibility of the correction is a fact about the commutator
bracket, not about the `δ`-letters, and the proof below never unfolds `dBlockW` at all. -/

section Tame

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α r h : ℕ}

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
`List.finRange h` order on both sides, so this is a rewrite and not a reindexing.  Also the
handle-side half of what WNP-b/c need to reach NC6's `npc_cross_operators_handles_std` (§4). -/
theorem eval_handlesW (t : Marking (2 + 2 * h) G) :
    t.eval (handlesW h) =
      MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  rw [Marking.eval_def, handlesW, PWord.eval_prodList, List.map_map]
  rfl

/-- **The tame boundary value of the corrected noncompact-`N` word.**

Killing the wild letters leaves exactly `τ^{ω₂}` — the same value as the compact row, and in
particular the correction block contributes nothing.  Stating the *value* rather than "` = 1`" is
deliberate: it is what makes the T1 step visible, and what shows that the death of this word at
the tame boundary is a fact about `τ`, not about the word's shape. -/
theorem eval_killWildLetters_npcW (α r h : ℕ) (e : EtaData) (t : Marking (2 + 2 * h) G) :
    (Marking.killWildLetters t).eval (npcW α r h e) = t.τ ^ᶻ omega2 := by
  have hH : PWord.eval ⇑(Marking.killWildLetters t) (handlesW h) = 1 := by
    rw [show PWord.eval ⇑(Marking.killWildLetters t) (handlesW h)
          = (Marking.killWildLetters t).eval (handlesW h) from rfl, eval_handlesW]
    exact MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)
  rw [Marking.eval_def, npcW, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_zpow,
    PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_prodList,
    PWord.eval_omega2PowHat, eBlockW, killWildLetters_coreLetter, one_zpow, commR_one_left,
    commR_one_right, one_conjR, inv_one, one_mul, mul_one, hH]
  rfl

/-- The same statement through F2's **substitution operator**: the syntactic kill-wild rewrite
`killWild` evaluated at `t` (`Marking.eval_killWild`). -/
theorem eval_killWild_npcW (α r h : ℕ) (e : EtaData) (t : Marking (2 + 2 * h) G) :
    t.eval (killWild (npcW α r h e)) = t.τ ^ᶻ omega2 := by
  rw [Marking.eval_killWild, eval_killWildLetters_npcW]

/-- **Gate-B admissibility, relativized to a tame `τ`** — packet Prop. 9.2.

The corrected noncompact-`N` word dies at the tame boundary of every marking whose `τ`-letter is
killed by `ω₂`.  Inside `Γ_R` that hypothesis is *supplied*, by packet Lem. 3.1: the tame relation
`τ^σ = τ^{q}` with `q` even forces `τ` to be pro-odd (`GQ2.Dyadic.odd_order`), and `ω₂` kills
pro-odd elements.  Per WN0-a's binding `KillsWild` ruling, this — and never the bare `KillsWild`
— is the admissibility route for a branch word carrying a `δ`-letter. -/
theorem killsWild_of_tau {α r h : ℕ} (e : EtaData)
    (hτ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G),
      t.τ ^ᶻ omega2 = 1) :
    KillsWild (npcW α r h e) := by
  intro G _ _ _ _ _ t
  rw [eval_killWildLetters_npcW]
  exact hτ G t

/-- **Gate B rule T1, at a finite marking**: if the `τ`-letter has odd order, the tame boundary
value is trivial.  This is the form the finite-target harnesses (F5) test. -/
theorem eval_killWildLetters_npcW_eq_one_of_odd {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] (α r h : ℕ) (e : EtaData) (t : Marking (2 + 2 * h) P)
    (hτ : Odd (orderOf t.τ)) : (Marking.killWildLetters t).eval (npcW α r h e) = 1 := by
  rw [eval_killWildLetters_npcW]
  simpa using PWord.eval_omega2Pow_eq_one_of_odd (⇑t) (.gen .tau) hτ

end Tame

/-! ### ⚠ F3's `KillsWild` is *not* satisfiable by this word either

WN0-a's finding, inherited verbatim.  `GQ2.Dyadic.KillsWild R` quantifies over **every** profinite
group and **every** marking with no relation imposed on `τ`; by `eval_killWildLetters_npcW` the
tame boundary value here is again `τ^{ω₂}`, so `KillsWild` would force `τ^{ω₂} = 1` universally —
false already in `Multiplicative (ZMod 8)`.  The admissibility routes are `killsWild_of_tau` and
`eval_killWildLetters_npcW_eq_one_of_odd`.  Recorded here as a *second* lane confirming the F3b
micro-ticket's premise: every wave-2 branch word with a `δ`-letter hits this. -/

section Refutation

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

private theorem zmod8_orderOf_dvd (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- The refuting marking: `τ` a generator of `ZMod 8` (so `τ^{ω₂} = τ ≠ 1`), everything else
trivial.  The wild letters are irrelevant — `killWildLetters` overwrites them. -/
def refuteMarking (h : ℕ) : Marking (2 + 2 * h) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters 1 (Multiplicative.ofAdd 1) (fun _ => 1)

/-- **The frozen corrected noncompact-`N` word is not Gate-B admissible in F3's unrelativized
sense.** -/
theorem not_killsWild (α r h : ℕ) (e : EtaData) : ¬ KillsWild (npcW α r h e) := by
  intro hR
  have hval := hR (Multiplicative (ZMod 8)) (refuteMarking h)
  rw [eval_killWildLetters_npcW,
    PWord.zpowHat_omega2_zpow (by norm_num) (zmod8_orderOf_dvd _), omega2Exp_eight,
    show (refuteMarking h).τ = Multiplicative.ofAdd (1 : ZMod 8) from rfl, Nat.cast_one,
    zpow_one] at hval
  exact absurd hval (by decide)

end Refutation

/-! ## §6. Gate C: the marked pro-`2` boundary

`pro2` sends `τ ↦ 1` and collapses every `ω₂`-power, but — per the pinned `η̂`-contract of
`specialization.py`, transcribed in `GQ2/Dyadic/Word/Syntax.lean` — it **keeps** the `η̂`-power,
because in the maximal pro-`2` quotient `η̂` becomes the genuine `ℤ₂`-power `η`.  So the surviving
word is

```
x₀^{2+2^α} · [x₀, σ^{η̂}] · (x₂^g)⁻¹ · x₂ · 1 · H_h,      g = x₁σ^{2^r},
```

and `(x₂^g)⁻¹ · x₂ = [g, x₂]` exactly as in the compact row — with the boundary conjugator `g`
in place of `σ`.  Hence the pro-`2` value is **MC2's `N`-core at twisted Labute letters**

```
nWord α  x₀  σ^{η̂}  (x₁σ^{2^r})  x₂   ·   handleWord,
```

the certified-move comparison this ticket owes: same core *shape* as the compact row, with `x₁`
replaced by the `η̂`-conjugator and `σ` replaced by `g`.  That substitution is the whole
difference between the compact and procyclic `N` rows at pro-`2` order.

⚠ **`E_{r,η}` is invisible here, and that is the design.**  `δ₀ = (x₀τ)^{ω₂}x₀⁻¹` becomes
`x₀·x₀⁻¹ = 1` (Gate C kills the `δ`-letters), so `D_{r,η} ↦ 1` and `E_{r,η} = [D_{r,η},x₁] ↦ 1`.
The correction is *second-order* content: it must not perturb the pro-`2` core, or the branch row
would no longer match MC2's rank-four theory.  Contrast §5, where `E_{r,η}` also dies but for the
opposite reason — there `D_{r,η}` survives and the *commutator's other argument* vanishes. -/

section EtaHatNeOmega2

local instance : TopologicalSpace (Multiplicative (ZMod 3)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 3)) := ⟨rfl⟩

private theorem zmod3_orderOf_odd (x : Multiplicative (ZMod 3)) : Odd (orderOf x) := by
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (by revert x; decide)
  rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd) with h | h <;> rw [h] <;> decide

/-- **`η̂` is never `ω₂`** — the side condition Gate C's `η̂`-contract needs, and the reason the
`pro2` rewrite keeps the `A`-conjugator instead of collapsing it.

Proved by playing the two Gate-B rules against each other on a group of order `3`: rule **T2**
(`zpowHat_etaHatZ_of_odd`) says `η̂` *fixes* pro-odd elements, rule **T1**
(`zpowHat_padicOmega2_eq_one_of_odd`) says `ω₂` *kills* them, and a generator of `ZMod 3` is not
trivial.  So the two exponents are separated by their action on the odd part, which is exactly the
mathematical content of "`η̂` has odd components `1`" versus "`ω₂` has odd components `0`". -/
theorem etaHatZ_ne_omega2 (η : ℤ_[2]) : etaHatZ η ≠ omega2 := by
  intro hEq
  have hodd : Odd (orderOf (Multiplicative.ofAdd (1 : ZMod 3))) := zmod3_orderOf_odd _
  have h1 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ᶻ etaHatZ η = Multiplicative.ofAdd (1 : ZMod 3) :=
    zpowHat_etaHatZ_of_odd hodd
  have h2 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ᶻ omega2 = 1 := by
    rw [← zpowHat_padicOmega2_one]
    exact zpowHat_padicOmega2_eq_one_of_odd hodd
  rw [hEq, h2] at h1
  exact absurd h1 (by decide)

end EtaHatNeOmega2

/-- The `η̂`-datum of any `EtaData` is not `ω₂` — the form the `pro2` rewrites below use. -/
theorem toZhat_ne_omega2 (e : EtaData) : e.toZhat ≠ omega2 := etaHatZ_ne_omega2 e.toPadic

/-- ⚠ **The corrected noncompact word is not in the `ω₂`-only fragment.**

`A = σ^{η̂}` is a profinite power with `γ ≠ ω₂`, so `PWord.IsOmega2Only` fails — and with it the
`ℕ`-exponent route of packet Lem. 2.2 (`PWord.eval_eq_evalNat_of_dvd`) that WN0-a used for its
numerical pins.  §8 therefore evaluates through the two honest resolvers instead.  Every branch
word carrying an `η̂`-conjugator inherits this; WMP-a should expect it. -/
theorem not_isOmega2Only_npcW (α r h : ℕ) (e : EtaData) : ¬ (npcW α r h e).IsOmega2Only :=
  fun hw => toZhat_ne_omega2 e hw.2.1.2.1

section Pro2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {α r h : ℕ}

@[simp] theorem pro2_handlesW (h : ℕ) : pro2 (handlesW h) = handlesW h := by
  rw [handlesW, pro2_prodList, List.map_map]
  rfl

/-- Gate C **keeps** the `η̂`-conjugator, by the pinned `η̂`-contract. -/
@[simp] theorem pro2_aW (h : ℕ) (e : EtaData) : pro2 (aW h e) = aW h e := by
  rw [aW, pro2_profPow_of_ne _ (toZhat_ne_omega2 e)]
  rfl

/-- Gate C keeps the `ℤ`-power conjugator `B = σ^{2^r}` untouched. -/
@[simp] theorem pro2_bW (h r : ℕ) : pro2 (bW h r) = bW h r := by
  rw [bW, pro2_zpow, pro2_gen_sigma]

/-- Gate C kills the `δ`-letter: `δ₀ ↦ x₀ x₀⁻¹`, whose value is `1`. -/
theorem eval_pro2_deltaZeroW (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (deltaZeroW h)) = 1 := by
  rw [deltaZeroW, pro2_prodList, Marking.eval_def]
  simp [PWord.omega2Pow]

/-- Hence the whole `D`-block dies at Gate C — a product of conjugates of `1`. -/
theorem eval_pro2_dBlockW (t : Marking (2 + 2 * h) G) (r : ℕ) (e : EtaData) :
    t.eval (pro2 (dBlockW h r e)) = 1 := by
  have hδ : PWord.eval ⇑t (pro2 (deltaZeroW h)) = 1 := eval_pro2_deltaZeroW t
  rw [dBlockW, pro2_prodList, Marking.eval_def]
  simp [hδ]

/-- **And so the correction block is invisible at the marked pro-`2` boundary.**  This is the
design constraint that makes the corrected word a legal replacement for the draft's: whatever
`E_{r,η}` does at second order, it must not move the pro-`2` core. -/
theorem eval_pro2_eBlockW (t : Marking (2 + 2 * h) G) (r : ℕ) (e : EtaData) :
    t.eval (pro2 (eBlockW h r e)) = 1 := by
  rw [eBlockW, pro2_comm, Marking.eval_def, PWord.eval_comm,
    show PWord.eval ⇑t (pro2 (dBlockW h r e)) = 1 from eval_pro2_dBlockW t r e, commR_one_left]

/-- **Gate C, syntactically**: the `τ`-letter is gone and the `ω₂`-power is collapsed; the
`η̂`-power and the `ℤ`-power conjugator are kept, and nothing else moves.  The fourth factor is
`x₂ · 1`, whose trailing `1` is the collapsed `τ`; the fifth is the correction block, left folded
because what matters about it is its *value* (`eval_pro2_eBlockW`), not its pro-`2` syntax. -/
theorem pro2_npcW (α r h : ℕ) (e : EtaData) :
    pro2 (npcW α r h e) = PWord.prodList
      [.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α),
       .comm (.gen (coreLetter h 0)) (aW h e),
       .inv (.conj (.gen (coreLetter h 2)) (PWord.prodList [.gen (coreLetter h 1), bW h r])),
       PWord.prodList [.gen (coreLetter h 2), .one],
       pro2 (eBlockW h r e),
       handlesW h] := by
  rw [npcW, pro2_prodList]
  simp only [List.map_cons, List.map_nil, pro2_omega2Pow, pro2_handlesW, pro2_prodList,
    pro2_zpow, pro2_comm, pro2_inv, pro2_conj, pro2_gen_wild, pro2_gen_tau, pro2_aW, pro2_bW,
    coreLetter]

/-- **The pro-`2` boundary value of the corrected noncompact-`N` word is MC2's `N`-core at the
twisted Labute letters `(x₀, σ^{η̂}, x₁σ^{2^r}, x₂)`.**

No hypothesis on the marking is needed: `pro2` has already removed `τ` and every `ω₂`, so the
identity is one of plain group words — except that the second Labute letter is a genuine profinite
power `σ^{η̂}`, which Gate C deliberately does not collapse. -/
theorem eval_pro2_npcW (α r h : ℕ) (e : EtaData) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (npcW α r h e)) =
      MarkedCore.nWord α (t (coreLetter h 0)) (t.σ ^ᶻ e.toZhat)
          (t (coreLetter h 1) * t.σ ^ (2 ^ r : ℤ)) (t (coreLetter h 2)) *
        MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  have hH : PWord.eval ⇑t (handlesW h)
      = MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := eval_handlesW t
  have hE : PWord.eval ⇑t (pro2 (eBlockW h r e)) = 1 := eval_pro2_eBlockW t r e
  rw [pro2_npcW, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_zpow,
    PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_one,
    PWord.eval_prodList, PWord.eval_profPow, aW, bW, Marking.apply_sigma, mul_one, one_mul,
    hE, hH]
  -- The word's leading exponent is a genuine `ℤ`-power, MC2's core word's is an `ℕ`-power;
  -- align them before the group normalisation.
  rw [show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    MarkedCore.nWord, ← invConj_mul_self (t (coreLetter h 2))
      (t (coreLetter h 1) * t.σ ^ (2 ^ r : ℤ))]
  simp only [commR, commP, conjR, mul_assoc]

/-- At `h = 0` the handle tail is the empty product and the pro-`2` value is MC2's core word on
the nose. -/
theorem eval_pro2_npcW_zero (α r : ℕ) (e : EtaData) (t : Marking 2 G) :
    t.eval (pro2 (npcW α r 0 e)) =
      MarkedCore.nWord α (t.x 0) (t.σ ^ᶻ e.toZhat) (t.x 1 * t.σ ^ (2 ^ r : ℤ)) (t.x 2) := by
  rw [eval_pro2_npcW (α := α) (r := r) (h := 0) (e := e) (t := t),
    show MarkedCore.handleWord (fun j : Fin 0 => t (handleU j)) (fun j : Fin 0 => t (handleV j))
      = 1 from rfl, mul_one]
  rfl

/-- The same value read as MC2's **full relator shape** `nRelWord` at the standard marking. -/
theorem eval_pro2_npcW_eq_nRelWord (α r : ℕ) (e : EtaData) (t : Marking 2 G) :
    t.eval (pro2 (npcW α r 0 e)) =
      MarkedCore.nRelWord (h := 0) α
        (MarkedCore.coreMark (t.x 0) (t.σ ^ᶻ e.toZhat) (t.x 1 * t.σ ^ (2 ^ r : ℤ)) (t.x 2)) := by
  rw [eval_pro2_npcW_zero, MarkedCore.nRelWord_coreMark]

end Pro2

/-! ## §7. The instance pins

Three of the seven rows are singled out because they exercise independent directions of the
parameter space; the rest are covered by the hash pins and `denote` bridges of §2. -/

/-- **The frozen-`Npc` harness instance** `(α, r, η) = (2, 1, 1)`, `h = 0`: a valid procyclic
branch row at level `r = 1`.

This is the row `F5`'s finite-target harness measures.  Its epimorphism-count vector over
`(S₃, D₈, A₄)` is **`6 / 1568 / 120`** (`scripts/dyadic_sanity_counts.py`, banked 2026-07-31).
That triple is **cited, never proved here**: reproducing it in Lean means an epimorphism
enumeration, not a `decide`, and it is F5's job.  Note the `S₃` and `D₈` entries coincide with the
compact row's — the sanity counts do *not* separate the compact and procyclic families, which is
precisely why the separating gate is the `S₃`-**module** test and not a count (see below). -/
theorem branchData_npc_pin :
    (BranchData.Npc 2 1 1).Valid ∧ (BranchData.Npc 2 1 1).level = 1 :=
  ⟨BranchData.valid_Npc_iff.mpr ⟨by norm_num, by norm_num⟩, rfl⟩

/-- The `η = −1` row is a valid branch row too — `BranchData.Valid` constrains only `α` and `r`,
so every `η ∈ ℤ₂ˣ` is admissible and the certificates must (and do) cover `η ≠ 1`. -/
theorem branchData_npc_etam1 :
    (BranchData.Npc 2 1 (-1)).Valid ∧ (BranchData.Npc 2 1 (-1)).level = 1 :=
  ⟨BranchData.valid_Npc_iff.mpr ⟨by norm_num, by norm_num⟩, rfl⟩

/-- The `r = 2` row, where `B = σ⁴`: level `2`, still valid. -/
theorem branchData_npc_r2 :
    (BranchData.Npc 2 2 1).Valid ∧ (BranchData.Npc 2 2 1).level = 2 :=
  ⟨BranchData.valid_Npc_iff.mpr ⟨by norm_num, by norm_num⟩, rfl⟩

/-- **The `(2,1,1)` word**, spelled out: `R_{N,2,1,1} = x₀⁶ [x₀,σ^{η̂}] · x₂^{-g} (x₂τ)^{ω₂} ·
[D_{1,1}, x₁]` with `g = x₁σ²` and `B = σ²`.  The leading exponent is `2 + 2² = 6` and the
trailing `PWord.one` is the empty handle block `H_0`. -/
theorem npcW_pin_unfold :
    npcW 2 1 0 ⟨1, 1⟩ = PWord.prodList
      [.zpow (.gen (coreLetter 0 0)) 6,
       .comm (.gen (coreLetter 0 0)) (aW 0 ⟨1, 1⟩),
       .inv (.conj (.gen (coreLetter 0 2))
         (PWord.prodList [.gen (coreLetter 0 1), .zpow (.gen .sigma) 2])),
       PWord.omega2Pow (PWord.prodList [.gen (coreLetter 0 2), .gen .tau]),
       eBlockW 0 1 ⟨1, 1⟩,
       .one] := rfl

/-! ## §8. Sanity: what is and is not visible

Nothing below is cited by a proof; these are regression pins in the sense of plan §3 A1.

### ⚠ The `S₃`-module early rejection is a *rejection* test only — docstring here

The lane's separating gate is the two-dimensional `S₃`-module radical detection for the
**uncorrected** word (the mutant row): a candidate whose mixed Hessian has a `2`-dimensional
radical on the relevant module is rejected early.  It belongs to **WNP-b/c**, which replay
`E_{r,η}` symbolically and can therefore see the second-order content this file's word only
carries.  The discipline that governs it, quoted from the campaign's harness rules:

> a **REJECT is sound, a PASS is never evidence.**

That is: the module test can only ever *refute* a candidate.  A candidate that survives it has
learned nothing — no PASS from this or any finite-target harness may be reported as support for
the corrected word.  The support for the correction is S3.2's machine verification plus the NC
lane's `npc_cross_operators`, and nothing else.

### The counts

F5 measures the frozen `(α,r,η) = (2,1,1)` row at `6 / 1568 / 120` over `(S₃, D₈, A₄)` — cited in
§7, proved nowhere here.  No `2`-group can see the `σ`-versus-`σ₂` distinction (on a group of
`2`-power exponent `ω₂` acts as the identity), and by the abelian result below no abelian group of
any order can see the `η̂`-twist or the correction block. -/

section AbelianInvisibility

variable {A : Type} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- **On any abelian target the `η̂`-twist, the correction block and the handles are all
invisible**: the word collapses to `x₀^{2+2^α} · x₂⁻¹ · (x₂τ)^{ω₂}`, in which neither `η` nor `r`
nor `h` appears.

This is the Lean form of "the counts are blind": an abelian finite-target harness cannot
distinguish the corrected word from the uncorrected one, cannot see `η`, and cannot see the level
`r`.  Any sanity row with teeth must be nonabelian — which is what makes `A₄` the interesting
column of F5's triple and the `S₃`-*module* test, not the `S₃` *count*, the separating gate. -/
theorem eval_npcW_of_comm (α r h : ℕ) (e : EtaData) (t : Marking (2 + 2 * h) A) :
    t.eval (npcW α r h e) =
      t (coreLetter h 0) ^ ((2 : ℤ) + 2 ^ α) * (t (coreLetter h 2))⁻¹ *
        (t (coreLetter h 2) * t.τ) ^ᶻ omega2 := by
  have hH : PWord.eval ⇑t (handlesW h) = 1 := by
    rw [show PWord.eval ⇑t (handlesW h) = t.eval (handlesW h) from rfl, eval_handlesW]
    rw [MarkedCore.handleWord]
    refine List.prod_eq_one ?_
    intro y hy
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    simp [commP, mul_comm]
  rw [npcW, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_zpow,
    PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen, PWord.eval_prodList,
    PWord.eval_omega2PowHat, eBlockW, commR, conjR, hH, mul_one, Marking.apply_tau]
  simp only [mul_comm, mul_left_comm, mul_inv_cancel, one_mul, mul_inv_cancel_left]

end AbelianInvisibility

section StressZMod8

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

private theorem orderOf_dvd_eight (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 :=
  orderOf_dvd_of_pow_eq_one (by revert x; decide)

/-- A concrete marking of the noncompact-`N` alphabet at `h = 0`, written additively:
`(σ, τ, x₀, x₁, x₂) = (5, 1, 1, 1, 1)` in `Multiplicative (ZMod 8)` — the *same* marking WN0-a
uses, so the two rows' values are directly comparable. -/
def zmod8Marking : Marking (2 + 2 * 0) (Multiplicative (ZMod 8)) :=
  Marking.ofLetters (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 1)
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]

/-- **Stress (genuine `ω₂`, and the compact/procyclic rows agree here)**: the profinite denotation
of the `(2,1,1)` word at the `ZMod 8` marking is `ofAdd 7` — *the same value WN0-a computes for
the compact row*, since the two differ only in the twisted conjugators and the correction block,
all of which are abelian-invisible.

Additively: `x₀⁶ = 6`, `x₂⁻¹ = −1`, `(x₂τ)^{ω₂} = 1·(1+1) = 2`, total `6 − 1 + 2 = 7`.  Pins the
leading exponent `2 + 2² = 6`, the *inverse* on the `x₂^{-g}` factor, and the `ω₂` sitting on the
whole `(x₂τ)` subword rather than on `x₂` alone. -/
theorem eval_zmod8_npcW :
    zmod8Marking.eval (npcW 2 1 0 ⟨1, 1⟩) = Multiplicative.ofAdd (7 : ZMod 8) := by
  rw [eval_npcW_of_comm, PWord.zpowHat_omega2_zpow (by norm_num) (orderOf_dvd_eight _),
    omega2Exp_eight, Nat.cast_one, zpow_one]
  decide

/-- **Stress (the whole `η`-and-`r` family is constant at this marking)**: changing `η` to `−1/5`
and `r` to `2` does not move the value, because the marking is abelian.  A pin on the *negative*
result of `eval_npcW_of_comm` — if a future edit made `η` or `r` visible abelian, this breaks. -/
theorem eval_zmod8_npcW_etam1_5_r2 :
    zmod8Marking.eval (npcW 2 2 0 ⟨-1, 5⟩) = zmod8Marking.eval (npcW 2 1 0 ⟨1, 1⟩) := by
  rw [eval_npcW_of_comm, eval_npcW_of_comm]

/-- **Stress (the tame boundary is not vacuous)**: at this marking the `τ`-letter has even order,
so the Gate-B value `τ^{ω₂}` is *not* trivial — `not_killsWild` read numerically. -/
theorem eval_killWildLetters_zmod8 :
    (Marking.killWildLetters zmod8Marking).eval (npcW 2 1 0 ⟨1, 1⟩)
      = Multiplicative.ofAdd (1 : ZMod 8) := by
  rw [eval_killWildLetters_npcW,
    PWord.zpowHat_omega2_zpow (by norm_num) (orderOf_dvd_eight _), omega2Exp_eight]
  decide

end StressZMod8

/-! ### The `D`-block is not vacuous

The `ZMod 8` pins above are abelian, so by `eval_npcW_of_comm` they say nothing about the
correction.  These two are the nonabelian counterweight, at the group level: the compressed
`D`-block and the correction block are genuinely nontrivial words.

Group-level rather than marking-level on purpose — that keeps them free of any profinite content,
so they are plain `decide`s, and it is the form WNP-b will replay symbolically over WW2's
certificate grammar with its own `η̂`-operator alphabet. -/

/-- **The compressed `D`-block at the group level**: `D = d^A (d · d^A)^{B⁻¹}` with `d` standing
for `δ₀`.  `eval_dBlockW` says this is what `dBlockW` evaluates to. -/
def dBlockG {G : Type*} [Group G] (d A B : G) : G := conjR d A * conjR (d * conjR d A) B⁻¹

section DBlockEval

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {h r : ℕ}

/-- The word-level `D`-block evaluates to the group-level one, at `d = δ₀`, `A = σ^{η̂}`,
`B = σ^{2^r}`.  The `mul_one`s absorbed here are the (D1) `prodList` tails. -/
theorem eval_dBlockW (e : EtaData) (t : Marking (2 + 2 * h) G) :
    t.eval (dBlockW h r e) =
      dBlockG (t.eval (deltaZeroW h)) (t.σ ^ᶻ e.toZhat) (t.σ ^ (2 ^ r : ℤ)) := by
  rw [dBlockW, dBlockG, Marking.eval_def, PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, PWord.eval_conj,
    PWord.eval_prodList, PWord.eval_inv, PWord.eval_gen, PWord.eval_profPow, aW, bW,
    PWord.eval_zpow, Marking.apply_sigma, mul_one]
  rfl

/-- The correction block evaluates to the commutator of the group-level `D`-block with `x₁`. -/
theorem eval_eBlockW (e : EtaData) (t : Marking (2 + 2 * h) G) :
    t.eval (eBlockW h r e) =
      commR (dBlockG (t.eval (deltaZeroW h)) (t.σ ^ᶻ e.toZhat) (t.σ ^ (2 ^ r : ℤ)))
        (t (coreLetter h 1)) := by
  rw [eBlockW, Marking.eval_def, PWord.eval_comm,
    show PWord.eval ⇑t (dBlockW h r e) = t.eval (dBlockW h r e) from rfl, eval_dBlockW]
  rfl

end DBlockEval

/-- **The compressed `D`-block is nontrivial**, at an explicit triple in `S₃`.

An explicit witness rather than `∃ … by decide`: the search over `S₃³` exhausts the kernel's
recursion budget, and a witness costs nothing.  With `B = 1` the block reduces to `d^A · d · d^A`,
which at `d = (0 1)`, `A = (0 2)` is `(1 2)(0 1)(1 2) = (0 2) ≠ 1`. -/
theorem dBlockG_ne_one_perm :
    dBlockG (Equiv.swap 0 1) (Equiv.swap 0 2) (1 : Equiv.Perm (Fin 3)) ≠ 1 := by decide

/-- **The correction block is nontrivial**: the `D`-block above does not commute with `x₁ = (0 1)`.
So `E_{r,η}` is not a decorative factor — it dies at both boundaries (§5, §6) while being a
nontrivial word, which is exactly the profile a second-order correction must have. -/
theorem eBlockG_ne_one_perm :
    commR (dBlockG (Equiv.swap 0 1) (Equiv.swap 0 2) (1 : Equiv.Perm (Fin 3)))
        (Equiv.swap 0 1) ≠ 1 := by decide

/-- **Stress (nonabelian: the pro-`2` core is not a vacuous relator)**: MC2's `N` core word is
nontrivial at an explicit marking of `S₃`, so the two commutators of §6's core do real work. -/
theorem nWord_ne_one_perm :
    MarkedCore.nWord 2 (Equiv.swap 0 1) (Equiv.swap 0 2) (Equiv.swap 0 1) (Equiv.swap 0 2)
      ≠ (1 : Equiv.Perm (Fin 3)) := by decide

end Npc

end GQ2.Dyadic.Words
