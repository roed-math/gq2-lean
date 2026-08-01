/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.Words.Npc

/-!
# Dyadic campaign, ticket WMP-a: the procyclic `M_α` branch word

The opening ticket of the hardest branch lane.  It carries **row 5 of the R5 selection freeze**
(`general_2adic/artifacts/reports/selection-freeze.md`), the procyclic-`M` relator

```
R_{M,pc} = R_lin^pc · R̂^pc · D₀²[D₀,D₁] · H_h,        R̂^pc = Sh_M(R_lin^pc)
R_lin^pc = A²[A,B] · C₀^{2^α}[C₀,D] · E₀₁^pc · E₂^pc
```

with the frozen letters (`s = 2^r`, `p = ε·2^{r−1}`, `m = 2^{α−1}`, `U = σ₂^s`, `V = σ₂^p`)

```
C₀ = x₂σ₂^s,   A = x₀⁻¹C₀⁻ᵐ,   B = x₁σ₂^p,   D = σ^{η̂},
E₀₁^pc = 𝓔(σ₂^{p+sm}, σ₂^{sm}; δ₀, δ₁),
E₂^pc  = δ₂^U · 𝒩_{U,m}(z)^{U^m},   z = δ₂δ₂^V,
```

as an F2 `PWord` over `Generator (2 + 2h)`, together with its two boundary specializations,
the packet-Prop. 9.2 power-balance pair for the hat copy, and the WW5 one-tree hash pins for
**all six** frozen instances.  `ℚ₂(√−10)` is the procyclic row `(r,ε,η) = (1,1,1)` (packet
Cor. 8.2; the sign row does not exist, packet Prop. 8.1) — **merge gate 9 lives on that pin**.

Freeze row-5 facts a reader of this file needs (they are *transmitted*, not re-derived):
**L = 67, flat in `α`** (the draft spellings ran 69/79/99/139); max product arity 2 for every
`α`, so the phase-4 exit criterion (no expanded `O(m)` product in the Lean-facing API) is met —
the orbit-norm block rides S1.9's constant-size identity `orbitNorm_eq`
(`𝒩_{U,m}(z) = (z^UU⁻¹)^mU^m`, `GQ2/Dyadic/Word/Blocks.lean`), which is already a committed
theorem and is what keeps the `E₂^pc` display bounded.

## The two copies, and what is deliberately *not* here

The hat copy `R̂^pc` is `Sh_M(R_lin^pc)` for **one frozen substitution** (S4.2,
`artifacts/reports/shadow-theorem-memo.md`):

```
x₀ ↦ δ₀,  x₁ ↦ δ₁,  x₂ ↦ 1,  δ₂ ↦ 1,  τ ↦ 1,  σ ↦ σ,   δ-letters atomic.
```

In the **emitted certificates the hat copy is materialized as explicit `Auxiliary` nodes**
(`Ahat`/`Bhat`/`C0hat`; `Ĉ₀ = σ₂^s`, the `x₂` of `C₀` killed) — no frozen tree carries a
`.shadow` node, no symbolic exponent survives, and `Ê₂ = 1` is dropped from the display
(S5.G measurement; the 2026-07-31 WMP note as nuanced by S5.G).  This file therefore states
the trees **as emitted** and needs no `Sh_M` operator.  The Lean-side `Sh_M` substitution
(`PWord → PWord`, spec = the table above) is **owed at WMP-b/c**, where the hat copy is proved
to be the substitution's image (the S4.2 certificate-shrink route); its four properties
(P1 tame-triviality with the *same* witness; P2 pro-2 value `σ^{bal}`, trivial iff the σ-balance
vanishes; P3 zero first Fox jet via the transport theorem — the **naive chain rule is refuted**,
profinite powers change representative; P4 second jet = raw determinant jet, a module condition;
P5 the char-2 cancellation) are the WMP-b/c interface.  `Ê₀₁ = E₀₁` verbatim: `E₀₁^pc` is a word
in `δ₀, δ₁, σ₂` alone, and `Sh_M` fixes those letters.

## Lean-facing findings the WMP lane must respect (freeze row 5; binding on WMP-b/c)

* **`E₂^pc` is first-order essential; `E₀₁^pc` is first-order redundant** — the hat copy
  reproduces `E₀₁^pc`'s entire first-order contribution operator-for-operator, so `E₀₁^pc`'s
  justification is **second-order only** (the exact gate-F refutation on the fifth-root module).
  Gate D cannot justify `E₀₁^pc`, and `E₀₁^pc` and the shadow substitution are **not
  independently choosable**.  Paper-relevant; it changes what WMP-c proves.
* WMP-b needs the **σ-column coincidence lemma** — the two copies' σ-entries are the *same*
  operator, so the product's σ-column vanishes without either factor vanishing — **not** the
  geometric-sum identity `(1+S^a)[b] = (1+S^b)[a]` (that identity closes the same column by a
  different route and is not the statement to formalize).  The WW3 `heisJetZero` family is the
  "copies cancel" consumable the σ-column lemma must be stated against.
* Draft Rem. 5.4 (WMP-b/c targets): on ramified simples `R̂^pc` has **zero first Fox
  derivative** and **exactly reproduces the raw extraspecial determinant including every
  `T`-dependent central term**; the copies cancel in characteristic 2; what remains of
  `D₀²[D₀,D₁]` is `Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)` — a *word identity*, not finite-order
  interpolation.
* **The `WC-Mpc` affine-phase data exists in no ticket** (recorded in every procyclic
  certificate's `known_proof_status`): it is WW4/WMP-c work, and WW4's six-item gap list is the
  WMP-c dispatch's spine.  The shadow contributes no affine shift when P3 holds (it contributes
  no primal or dual offset), but that corollary is *unwritten*; WW4's "no affine shift"
  corollary against `heisJetZero` is the stated form.
* **S4.5 riders** (swap `E₂^pc·E₀₁^pc` is DECIDED EQUAL, proof-grade; the freeze stands
  unamended): (i) `E₂^pc`'s second-order content is **empty** on the gate-E marking, so any
  block-order statement WMP-c makes is a **gate-D statement**, not a Hessian one; (ii) the
  equality rests on the **`x₂`-has-no-primal-letter convention** — if the Lean marking ever
  gives the boundary generator a primal coordinate, block order becomes load-bearing again
  (`s45-swap-decision.md` §3.2 difference formula).
* `η` is immovable in this grammar: only the Tietze display `D := σ^{η̂}` is available (`σ` is
  a marked letter).  The three displays that occur in the frozen instances are `σ` (η = 1), a
  literal power `σ^k`, and the genuine `σ^{η̂}` node — `EtaDisplay` below.

## Negative-test material (docstring-only; WMP-c/F5 territory)

* The old `D₀²[D₀,D₁]`-only correction is **FALSE** at `V = 𝔽₆₄`, `|ζ| = 9`, `S = x^32`,
  `q = Tr_{𝔽₈/𝔽₂}(x⁹)` — a 2-dimensional *mixed-Hessian* radical.  The frozen word passes this
  order-nine module: the procyclic shadow clears the obstruction the draft's field-specific word
  needed the relative norm for (shadow memo §5, "positive surprise").
* The `√−10` field-specific relative-norm word (draft §7.4) is **RETIRED to regression-only**
  status (R4 riding decision): the shadow route is the *only* one reaching `Q₊` (radical 0;
  plus-only and relative-norm both leave radical 2 — errata item 7).  Its regression row is
  **F5's row B1** (`scripts/dyadic_sanity_counts.py`, `rel_minus10_relative_norm`); its hat map
  (`x₂ ↦ W`, `Nm_τ`) is *not* an `Sh_M` value and is recorded unfrozen (`MINUS_TEN_VARIANT`).
* Draft §7.3's `ℚ₂(√10)` word `R₁₀` (marking `ν(a,b,c,d) = (−4,0,2,1)`,
  `R₁₀ = A²[A,x₁]C₀⁴[C₀,σ]E₁₀`) is F5's row **B2**: it agrees with the frozen `ε = 0` row
  pointwise on every marking of every harness target, and the frozen spelling is what F5's
  A-rows test — counts `(S₃, D₈, A₄) = (6, 1568, 120)` for both `√10` and `√−10`, **cited,
  never proved here** (no 2-group can see the σ-vs-σ₂ distinction, and `A₄` needs a genuine
  epimorphism enumeration).

## What is pinned, and against what

`rawMpc α r p η̂ h` below is the certificate tree in the emitted spelling of
`general_2adic/generated/lean/M_procyclic_*.lean` (six standalone files, importable by nothing);
the six instantiations are hash-pinned against `general_2adic/generated/MANIFEST.json`, **keyed
by `candidate_id`, never by `word_hash`** (compact-row q2/q4 twins share a `word_hash`; the
manifest's own contract says so).

| instance | `(α,r,ε,η,h)` | candidate | digest |
|---|---|---|---|
| `ℚ₂(√−10)` | `(2,1,1,1,0)` | `M-procyclic-alpha2-r1-eps1-eta1-h0-q2-v001` | `55b24a4b…` |
| `ℚ₂(√10)` | `(2,1,0,1,0)` | `M-procyclic-alpha2-r1-eps0-eta1-h0-q2-v001` | `1eb3dd01…` |
| one handle | `(2,1,1,1,1)` | `M-procyclic-alpha2-r1-eps1-eta1-h1-q2-v001` | `94927545…` |
| `η̂` displayed | `(2,1,1,−1/3,0)` | `M-procyclic-alpha2-r1-eps1-etahat-h0-q2-v001` | `144906bb…` |
| `r = 2` | `(2,2,1,5,0)` | `M-procyclic-alpha2-r2-eps1-eta5-h0-q2-v001` | `c9dc9031…` |
| `α = 3` | `(3,1,1,3,0)` | `M-procyclic-alpha3-r1-eps1-eta3-h0-q2-v001` | `2a117b37…` |

`mpcW α r p η̂ h` is the **semantic word** and the six `denote_rawMpc_*` bridges prove it is
*the denotation of the hashed tree* — the load-bearing link, per instance and never generic
(wave-2 rule 2: `OrbitNorm` denotes at a concrete length only, `m = 2` at `α = 2` and `m = 4`
at `α = 3`; the hash is of the *unexpanded* tree either way).

## Authoring rules followed (WW5/S5.G/WN0-a, `docs/dyadic/tickets.md`)

1. **The certificate's spelling, not a normalized one.**  `integerPower` with literal `Int`s,
   `ω₂` through `omega2Power`, `η̂` through `zhatPower … (.etahat num den)`; the emitted display
   drops trivial exponents — `σ₂¹` is the bare `sigma2` auxiliary, `p = 0` collapses `B` to the
   bare generator `x1` and `z = δ₂δ₂^{σ₂⁰}` to `δ₂²` (an `integerPower`), `η = 1` displays `D`
   as the bare `sigma` — and the literal `match` tables below reproduce exactly those spellings.
2. **The `Auxiliary` nodes hash as displayed** — `A`/`B`/`C0`/`D`/`E01`/`E2`/`sigma2`/`u_i`/
   `d_i` and the hat copy's `Ahat`/`Bhat`/`C0hat` — and are **never inlined before hashing**
   (`denote` inlines them *after*; the digest is of the displayed tree).  `sigma2` is one shared
   displayed definition; the hatted names are genuinely new definitions (shadow memo §1).
3. **The handle tail is display-accurate**: the emitted `h = 0` procyclic trees carry **no**
   `HyperbolicHandles` node at all (measured; unlike the compact-`N` row, whose `h = 0` tree
   carries `HyperbolicHandles 3 0`), and the `h = 1` tree appends `HyperbolicHandles 3 1` as a
   fourteenth factor.  `rawHandleTail` matches on `h` accordingly.
4. **Every `Multiply` is `PWord.prodList`** (trailing `.one`s included), generator names by
   literal `match` table, handles by `Fin h`/`List.finRange`, `denote` bridges per instance,
   `<decl>_astHash` + `#eval Export.assertAstHash` per instance, tame boundaries stated as
   **values**, explicit witnesses over `∃ … by decide`, F5 counts in docstrings only, and the
   `KillsWild` ruling: the admissibility routes are the `τ`-relativized ones below, never the
   bare form (`not_killsWild` refutes it, as it must for every δ-letter word).

## Implementation notes

Non-`module` (forced: `GQ2.Dyadic.TameBoundary` is non-`module`; the `Words/` lane convention
was ratified at WN0-a).  Everything lives in the namespace `GQ2.Dyadic.Words.Mpc`, so nothing
clashes with the pilot's `GQ2.Dyadic.Words.*` alphabet declarations when both are imported.
The `Zhat` commutation helpers (`zhat_mul_comm`, `Commute` of two `^ᶻ`-powers of one base) are
generic and sit here only until a WW hoist claims them; they are what discharges
`[C₀, σ^{η̂}] = [Ĉ₀, σ^{η̂}] = 1` at both boundaries with the `η̂` display quantified, which the
shadow memo lists as "trivial mathematically and merely absent from the operator normalizer".
-/

namespace GQ2.Dyadic.Words.Mpc

open Export (RawWord)

/-! ## `ℤ̂`-commutation helpers

`Zhat` is the profinite completion of the *abelian* group `ℤ`, so its multiplication is
commutative and any two `^ᶻ`-powers of a common base commute.  Neither fact is in
`GQ2/Zhat.lean` yet; they are proved here by density (`Zhat.funext_ofInt`), and they are the
whole of what the `[C₀,D]`-type commutators need at the boundaries.  WW-hoist candidates. -/

section ZhatCommute

private theorem ofInt_mul_comm (n : ℤ) (ξ : Zhat) : Zhat.ofInt n * ξ = ξ * Zhat.ofInt n := by
  have h := Zhat.funext_ofInt (f := fun ζ => Zhat.ofInt n * ζ) (g := fun ζ => ζ * Zhat.ofInt n)
    (continuous_const_mul _) (continuous_mul_const _)
    (fun m => by rw [← Zhat.ofInt_add, ← Zhat.ofInt_add, Int.add_comm])
  exact congrFun h ξ

/-- `ℤ̂` is commutative (it is the profinite completion of an abelian group).  By double
density from `Zhat.ofInt_add`. -/
theorem zhat_mul_comm (γ ξ : Zhat) : γ * ξ = ξ * γ := by
  have h := Zhat.funext_ofInt (f := fun ζ => ζ * ξ) (g := fun ζ => ξ * ζ)
    (continuous_mul_const _) (continuous_const_mul _)
    (fun n => ofInt_mul_comm n ξ)
  exact congrFun h γ

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- Two `ℤ̂`-powers of a common base commute — the semantic content of
"`[σ₂^s, σ^{η̂}] = 1` is trivial mathematically" (shadow memo §4). -/
theorem commute_zpowHat (x : G) (γ ξ : Zhat) : Commute (x ^ᶻ γ) (x ^ᶻ ξ) := by
  show _ * _ = _ * _
  rw [← zpowHat_mul, ← zpowHat_mul, zhat_mul_comm]

/-- A `ℕ`-power of a `ℤ̂`-power is the `ℤ̂`-power of the (multiplicatively written) `ℕ`-power
of the exponent. -/
theorem zpowHat_npow (x : G) (γ : Zhat) : ∀ k : ℕ, (x ^ᶻ γ) ^ k = x ^ᶻ (γ ^ k)
  | 0 => by rw [pow_zero, pow_zero, zpowHat_one]
  | k + 1 => by rw [pow_succ, pow_succ, zpowHat_mul, zpowHat_npow x γ k]

/-- An ordinary `ℕ`-power of `x` commutes with any `ℤ̂`-power of `x`. -/
theorem commute_pow_zpowHat (x : G) (k : ℕ) (γ : Zhat) : Commute (x ^ k) (x ^ᶻ γ) := by
  have h : x ^ k = x ^ᶻ Zhat.ofInt (k : ℤ) := by rw [zpowHat_ofInt, zpow_natCast]
  rw [h]
  exact commute_zpowHat x _ γ

/-- A `ℕ`-power of a `ℤ̂`-power of `x` commutes with any `ℤ̂`-power of `x` — the exact shape of
the boundary commutators `[σ₂^s, D]`, `[σ₂^{sm}-parts, D]`. -/
theorem commute_zpowHat_pow (x : G) (γ : Zhat) (k : ℕ) (ξ : Zhat) :
    Commute ((x ^ᶻ γ) ^ k) (x ^ᶻ ξ) := by
  rw [zpowHat_npow]
  exact commute_zpowHat x _ ξ

end ZhatCommute

/-! ## The `η̂` display

Row 5: "η is immovable in this grammar: only the Tietze display `D := σ^{η̂}` is available."
The six frozen certificates use three displays for that letter, and the display is
*certificate data* (it is hashed), so it is carried as a small syntactic datum rather than
recomputed from `η`:

* `η = 1` — the bare generator `sigma` (`√−10`, `√10`, the `h = 1` instance);
* a literal odd power `σ^k` (`k = 5` at `r = 2`, `k = 3` at `α = 3`) — legitimate by S1.2's
  representative independence, and the spelling the engines close the σ-column with;
* the genuine `zhatPower … (.etahat num den)` node (`η = −1/3` on the `etahat` instance) —
  the one display that keeps the `η̂`-quantified statement honest.

`zhat` is the `ℤ̂`-exponent each display denotes; `eval_toPWord` below says the three displays
evaluate to `σ ^ᶻ zhat` uniformly, which is what makes every boundary theorem in this file
display-independent. -/

/-- The displayed spelling of the procyclic letter `D = σ^{η̂}`, as emitted (S5.G). -/
inductive EtaDisplay where
  /-- `η = 1`: the letter displays as the bare generator `σ`. -/
  | one : EtaDisplay
  /-- A literal integer power `σ^k` (the emitted display for a small odd `η ≡ k`). -/
  | lit (k : ℤ) : EtaDisplay
  /-- The genuine `η̂` node `σ^{η̂}`, `η = num/den` (odd numerator and denominator). -/
  | hat (num den : ℤ) : EtaDisplay

namespace EtaDisplay

/-- The `ℤ̂`-exponent a display denotes. -/
noncomputable def zhat : EtaDisplay → Zhat
  | .one => Zhat.ofInt 1
  | .lit k => Zhat.ofInt k
  | .hat num den => Export.RawSpec.toZhat (.etahat num den)

/-- The display's well-formedness, mirroring `RawSpec.wf`: `etahat` entries must be odd
(Python raises otherwise, so an even entry has no certificate counterpart). -/
def wfB : EtaDisplay → Bool
  | .hat num den => num % 2 != 0 && den % 2 != 0
  | _ => true

/-- The displayed subtree of the certificate: the letter `D` is an `Auxiliary` wrapper around
the display in every instance. -/
def toRaw : EtaDisplay → RawWord
  | .one => .auxiliary "D" (.generator "sigma")
  | .lit k => .auxiliary "D" (.integerPower (.generator "sigma") (.int k))
  | .hat num den => .auxiliary "D" (.zhatPower (.generator "sigma") (.etahat num den))

/-- The denoted `PWord` (the `Auxiliary` wrapper is inlined by `denote`). -/
noncomputable def toPWord {n : ℕ} : EtaDisplay → PWord (Generator n)
  | .one => .gen .sigma
  | .lit k => .zpow (.gen .sigma) k
  | .hat num den => .profPow (.gen .sigma) (Export.RawSpec.toZhat (.etahat num den))

/-- A display is `ω₂`-only iff it is not the genuine `η̂` node. -/
def IsOmega2Only : EtaDisplay → Prop
  | .hat _ _ => False
  | _ => True

end EtaDisplay

/-! ## The procyclic-`M` alphabet

Identical to the compact-`N` alphabet (`x₀, x₁, x₂, σ, τ` plus `h` handle pairs) but declared
afresh: the WN0-a template rule is that each branch lane names its own letters, and the two
lanes' declarations live in different namespaces so both can be imported together. -/

/-- The core wild letters `x₀, x₁, x₂`. -/
def coreLetter (h : ℕ) (i : Fin 3) : Generator (2 + 2 * h) :=
  .wild ⟨(i : ℕ), by have := i.isLt; omega⟩

/-- The first letter `x_{3+2j}` of the `j`-th handle pair. -/
def handleU {h : ℕ} (j : Fin h) : Generator (2 + 2 * h) :=
  .wild ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The second letter `x_{4+2j}` of the `j`-th handle pair. -/
def handleV {h : ℕ} (j : Fin h) : Generator (2 + 2 * h) :=
  .wild ⟨4 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The wild letter `x_i`, or `none` past the alphabet (the `handleGen` field of the
denotation context). -/
def wildGen (h : ℕ) (i : ℕ) : Option (Generator (2 + 2 * h)) :=
  if hi : i < 2 * h + 3 then some (.wild ⟨i, by omega⟩) else none

/-- The generator names the procyclic-`M` certificates use — a literal table, never a decimal
parser (`String.toNat?` does not reduce in the kernel, WN0-a rule). -/
def genOfName (h : ℕ) (s : String) : Option (Generator (2 + 2 * h)) :=
  match s with
  | "sigma" => some .sigma
  | "tau" => some .tau
  | "x0" => wildGen h 0
  | "x1" => wildGen h 1
  | "x2" => wildGen h 2
  | _ => none

/-- The denotation context of the procyclic-`M` row.  `param` is `none` everywhere: **no
symbolic exponent survives in any frozen tree** (S5.G) — every exponent is a literal `Int`. -/
def denoteCtx (h : ℕ) : Export.DenoteCtx (Generator (2 + 2 * h)) where
  gen := genOfName h
  handleGen := wildGen h
  param := fun _ => none

/-! ## The semantic word

Spelled `prodList`-for-`Multiply` throughout, because these are *denotations* of the certificate
trees, not free re-spellings.  The display irregularities the emitter produces at trivial
exponents are reproduced by literal `match` tables:

* `sig2PowW k` — `σ₂^k` displays as the bare `σ₂` at `k = 1`;
* `bW p` — `B = x₁σ₂^p` collapses to the bare `x₁` at `p = 0` (the `√10` row, F1 discovery:
  both `ε` values occur, `ε = 0` is `ℚ₂(√10)` and `ε = 1` is the packet's `√−10`);
* `zW p` — `z = δ₂δ₂^{σ₂^p}` displays as `δ₂²` (an integer power) at `p = 0`;
* `bHatW p` — `B̂ = δ₁σ₂^p` collapses to the bare `δ₁` at `p = 0`. -/

section Word

variable (h : ℕ)

/-- `u_i = (x_iτ)^{ω₂}` on a core letter, in the certificate's `prodList` spelling. -/
noncomputable def uW (i : Fin 3) : PWord (Generator (2 + 2 * h)) :=
  PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])

/-- The δ-letter `δ_i = u_i x_i⁻¹` on a core letter, `prodList`-spelled. -/
noncomputable def dW (i : Fin 3) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [uW h i, .inv (.gen (coreLetter h i))]

/-- `σ₂^k` as displayed: bare `σ₂` at `k = 1`, an integer power otherwise (`k ≥ 2` in every
use; the `k = 0` arm is never reachable from a frozen tree). -/
noncomputable def sig2PowW : ℕ → PWord (Generator (2 + 2 * h))
  | 1 => sigma2W
  | k => .zpow sigma2W (k : ℤ)

/-- `C₀ = x₂σ₂^s` (`s = 2^r ≥ 2`, so the power display is uniform). -/
noncomputable def c0W (s : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [.gen (coreLetter h 2), .zpow sigma2W (s : ℤ)]

/-- `A = x₀⁻¹C₀⁻ᵐ`. -/
noncomputable def aW (s m : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [.inv (.gen (coreLetter h 0)), .zpow (c0W h s) (-(m : ℤ))]

/-- `B = x₁σ₂^p`, collapsing to the bare `x₁` at `p = 0`. -/
noncomputable def bW : ℕ → PWord (Generator (2 + 2 * h))
  | 0 => .gen (coreLetter h 1)
  | p => PWord.prodList [.gen (coreLetter h 1), sig2PowW h p]

/-- `E₀₁^pc = 𝓔(σ₂^a, σ₂^b; δ₀, δ₁) = (δ₁^{σ₂^b}δ₁δ₀)^{σ₂^a}·δ₀` with `a = p + sm`,
`b = sm` — the asymmetric procyclic conjugator pair (the compact row's `E_m^rev` is the
symmetric `𝓔(σ₂^m, σ₂^m; ·)`; the `p`-shift on the outer conjugator is the `ε`-visible part
of this block). -/
noncomputable def e01W (a b : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.conj (PWord.prodList [.conj (dW h 1) (.zpow sigma2W (b : ℤ)), dW h 1, dW h 0])
      (.zpow sigma2W (a : ℤ)),
     dW h 0]

/-- The orbit-norm base `z = δ₂δ₂^{σ₂^p}`, displaying as `δ₂²` at `p = 0`. -/
noncomputable def zW : ℕ → PWord (Generator (2 + 2 * h))
  | 0 => .zpow (dW h 2) 2
  | p => PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h p)]

/-- `E₂^pc = δ₂^U · 𝒩_{U,m}(z)^{U^m}` with `U = σ₂^s`: the orbit-norm node, whose denotation
is the *expanded* product `Export.orbitNormFactors` (hash unaffected — it is of the unexpanded
tree), and whose Lean-facing form rides S1.9's `orbitNorm_eq`.  The outer conjugator `U^m` is
displayed as the single literal power `σ₂^{sm}`. -/
noncomputable def e2W (s m p : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.conj (dW h 2) (.zpow sigma2W (s : ℤ)),
     .conj (PWord.prodList (Export.orbitNormFactors (zW h p) (.zpow sigma2W (s : ℤ)) m))
       (.zpow sigma2W ((s * m : ℕ) : ℤ))]

/-- `Ĉ₀ = σ₂^s`: the hat copy of `C₀` — `Sh_M` kills the `x₂` and the display is the bare
power. -/
noncomputable def c0HatW (s : ℕ) : PWord (Generator (2 + 2 * h)) :=
  .zpow sigma2W (s : ℤ)

/-- `Â = δ₀⁻¹Ĉ₀⁻ᵐ`: the hat copy of `A` (`x₀ ↦ δ₀`, δ-letters atomic). -/
noncomputable def aHatW (s m : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [.inv (dW h 0), .zpow (c0HatW h s) (-(m : ℤ))]

/-- `B̂ = δ₁σ₂^p`: the hat copy of `B`, collapsing to the bare `δ₁` at `p = 0`. -/
noncomputable def bHatW : ℕ → PWord (Generator (2 + 2 * h))
  | 0 => dW h 1
  | p => PWord.prodList [dW h 1, sig2PowW h p]

/-- `H_h = ∏_{j<h} [x_{3+2j}, x_{4+2j}]`, ordered by `List.finRange` (matches both the
`Export.handleFactors` expansion and MC2's `handleWord`). -/
noncomputable def handlesW : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList ((List.finRange h).map fun j => .comm (.gen (handleU j)) (.gen (handleV j)))

end Word

/-- The handle tail of the factor list: **empty at `h = 0`** — the emitted `h = 0` procyclic
trees carry no handles node at all (measured; the compact-`N` emitter differs) — and the single
expanded handle block at `h ≥ 1`. -/
noncomputable def handleTailW : (h : ℕ) → List (PWord (Generator (2 + 2 * h)))
  | 0 => []
  | h + 1 => [handlesW (h + 1)]

/-- The linear-copy factors `R_lin^pc = A²[A,B]·C₀^{2^α}[C₀,D]·E₀₁^pc·E₂^pc`.

Exponent vocabulary is F1's: `s r = 2^r`, `m α = 2^{α−1}`, and the `p`-argument is
`GQ2.Dyadic.p ε r = ε·2^{r−1}` at the instances. -/
noncomputable def linFactors (α r p : ℕ) (η : EtaDisplay) (h : ℕ) :
    List (PWord (Generator (2 + 2 * h))) :=
  [.zpow (aW h (s r) (m α)) 2,
   .comm (aW h (s r) (m α)) (bW h p),
   .zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ),
   .comm (c0W h (s r)) η.toPWord,
   e01W h (p + s r * m α) (s r * m α),
   e2W h (s r) (m α) p]

/-- The hat-copy factors `R̂^pc = Â²[Â,B̂]·Ĉ₀^{2^α}[Ĉ₀,D]·Ê₀₁^pc`, exactly as emitted:
`Ê₀₁ = E₀₁` verbatim (its letters are `Sh_M`-fixed) and `Ê₂ = 1` is dropped from the display
(`Sh_M` sends `δ₂ ↦ 1`, and every `E₂^pc` letter is a `δ₂`). -/
noncomputable def hatFactors (α r p : ℕ) (η : EtaDisplay) (h : ℕ) :
    List (PWord (Generator (2 + 2 * h))) :=
  [.zpow (aHatW h (s r) (m α)) 2,
   .comm (aHatW h (s r) (m α)) (bHatW h p),
   .zpow (c0HatW h (s r)) ((2 ^ α : ℕ) : ℤ),
   .comm (c0HatW h (s r)) η.toPWord,
   e01W h (p + s r * m α) (s r * m α)]

/-- **The frozen procyclic-`M` branch word** (selection freeze row 5; draft eq. `Mpc-word`)

```
R_{M,pc} = R_lin^pc · R̂^pc · D₀²[D₀,D₁] · H_h
```

as the denotation of the emitted certificate tree: thirteen factors (fourteen with a handle
block), every `Multiply` a `prodList`, the two `E₀₁^pc` copies verbatim-identical subtrees, and
the plus block `D₀²[D₀,D₁]` on the δ-letters (its value at second order is
`Q₊(c₀,c₁) = q(c₀)+b_q(c₀,c₁)`, the word identity WMP-c consumes). -/
noncomputable def mpcW (α r p : ℕ) (η : EtaDisplay) (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    (linFactors α r p η h ++ hatFactors α r p η h ++
      [.zpow (dW h 0) 2, .comm (dW h 0) (dW h 1)] ++ handleTailW h)

/-! ## The certificate trees

The emitted spelling of `general_2adic/generated/lean/M_procyclic_*.lean`, shared-subtree for
shared-subtree.  `sigma2` is one displayed definition (charged once, §9.3 rule 3); the hat
copy's `Ahat`/`Bhat`/`C0hat` are genuinely new `Auxiliary` definitions; `E01` occurs twice as
the *same* subtree. -/

/-- The shared auxiliary `σ₂ = σ^{ω₂}`. -/
def rawSigma2 : RawWord := .auxiliary "sigma2" (.omega2Power (.generator "sigma"))

/-- `σ₂^k` as displayed (bare at `k = 1`). -/
def rawSig2Pow : ℕ → RawWord
  | 1 => rawSigma2
  | k => .integerPower rawSigma2 (.int k)

/-- The auxiliary `δ₀ = u₀x₀⁻¹`, `u₀ = (x₀τ)^{ω₂}`. -/
def rawD0 : RawWord :=
  .auxiliary "d0"
    (.multiply
      [.auxiliary "u0" (.omega2Power (.multiply [.generator "x0", .generator "tau"])),
       .inverse (.generator "x0")])

/-- The auxiliary `δ₁`. -/
def rawD1 : RawWord :=
  .auxiliary "d1"
    (.multiply
      [.auxiliary "u1" (.omega2Power (.multiply [.generator "x1", .generator "tau"])),
       .inverse (.generator "x1")])

/-- The auxiliary `δ₂`. -/
def rawD2 : RawWord :=
  .auxiliary "d2"
    (.multiply
      [.auxiliary "u2" (.omega2Power (.multiply [.generator "x2", .generator "tau"])),
       .inverse (.generator "x2")])

/-- The auxiliary `C₀ = x₂σ₂^s`. -/
def rawC0 (s : ℕ) : RawWord :=
  .auxiliary "C0" (.multiply [.generator "x2", .integerPower rawSigma2 (.int s)])

/-- The auxiliary `A = x₀⁻¹C₀⁻ᵐ`. -/
def rawA (s m : ℕ) : RawWord :=
  .auxiliary "A"
    (.multiply [.inverse (.generator "x0"), .integerPower (rawC0 s) (.int (-(m : ℤ)))])

/-- The auxiliary `B = x₁σ₂^p` (bare `x1` at `p = 0` — the `√10` display). -/
def rawB : ℕ → RawWord
  | 0 => .auxiliary "B" (.generator "x1")
  | p => .auxiliary "B" (.multiply [.generator "x1", rawSig2Pow p])

/-- The auxiliary `E01 = 𝓔(σ₂^a, σ₂^b; δ₀, δ₁)`, `a = p + sm`, `b = sm`. -/
def rawE01 (a b : ℕ) : RawWord :=
  .auxiliary "E01"
    (.multiply
      [.conjugate
         (.multiply [.conjugate rawD1 (.integerPower rawSigma2 (.int b)), rawD1, rawD0])
         (.integerPower rawSigma2 (.int a)),
       rawD0])

/-- The orbit-norm base `z = δ₂δ₂^{σ₂^p}` (`δ₂²` as an integer power at `p = 0`). -/
def rawZ : ℕ → RawWord
  | 0 => .integerPower rawD2 (.int 2)
  | p => .multiply [rawD2, .conjugate rawD2 (rawSig2Pow p)]

/-- The auxiliary `E2 = δ₂^{σ₂^s}·𝒩_{σ₂^s,m}(z)^{σ₂^{sm}}` — the `OrbitNorm` node, hashed
unexpanded. -/
def rawE2 (s m p : ℕ) : RawWord :=
  .auxiliary "E2"
    (.multiply
      [.conjugate rawD2 (.integerPower rawSigma2 (.int s)),
       .conjugate
         (.orbitNorm (.integerPower rawSigma2 (.int s)) (.int m) (rawZ p))
         (.integerPower rawSigma2 (.int (s * m)))])

/-- The hat auxiliary `Ĉ₀ = σ₂^s`. -/
def rawC0hat (s : ℕ) : RawWord :=
  .auxiliary "C0hat" (.integerPower rawSigma2 (.int s))

/-- The hat auxiliary `Â = δ₀⁻¹Ĉ₀⁻ᵐ`. -/
def rawAhat (s m : ℕ) : RawWord :=
  .auxiliary "Ahat"
    (.multiply [.inverse rawD0, .integerPower (rawC0hat s) (.int (-(m : ℤ)))])

/-- The hat auxiliary `B̂ = δ₁σ₂^p` (bare `δ₁` at `p = 0`). -/
def rawBhat : ℕ → RawWord
  | 0 => .auxiliary "Bhat" rawD1
  | p => .auxiliary "Bhat" (.multiply [rawD1, rawSig2Pow p])

/-- The handle tail: **no node at `h = 0`** (the emitted procyclic display; the compact-`N`
emitter carries an explicit count-0 node instead), one `HyperbolicHandles` node at `h ≥ 1`. -/
def rawHandleTail : ℕ → List RawWord
  | 0 => []
  | h + 1 => [.hyperbolicHandles 3 (.int (h + 1))]

/-- **The emitted certificate tree** of `R_{M,pc}` at parameters `(α, r, p, η̂-display, h)`.
The six frozen instantiations are hash-pinned below; the tree is data and `denote` is its only
bridge to the semantics. -/
def rawMpc (α r p : ℕ) (η : EtaDisplay) (h : ℕ) : RawWord :=
  .multiply
    ([.integerPower (rawA (s r) (m α)) (.int 2),
      .commutator (rawA (s r) (m α)) (rawB p),
      .integerPower (rawC0 (s r)) (.int (2 ^ α)),
      .commutator (rawC0 (s r)) η.toRaw,
      rawE01 (p + s r * m α) (s r * m α),
      rawE2 (s r) (m α) p,
      .integerPower (rawAhat (s r) (m α)) (.int 2),
      .commutator (rawAhat (s r) (m α)) (rawBhat p),
      .integerPower (rawC0hat (s r)) (.int (2 ^ α)),
      .commutator (rawC0hat (s r)) η.toRaw,
      rawE01 (p + s r * m α) (s r * m α),
      .integerPower rawD0 (.int 2),
      .commutator rawD0 rawD1] ++ rawHandleTail h)

/-- Well-formedness in WW5's sense, for every parameter tuple whose `η̂` display is
well-formed (odd `etahat` entries; the other displays carry no side condition).
`assertAstHash` refuses an ill-formed tree, so this is the precondition of every pin below. -/
theorem wf_rawMpc (α r : ℕ) (p : ℕ) (η : EtaDisplay) (h : ℕ) (hη : η.wfB = true) :
    (rawMpc α r p η h).wf = true := by
  rcases p with - | - | p <;> rcases h with - | h <;>
    rcases η with - | k | ⟨num, den⟩ <;>
    simp_all [rawMpc, rawA, rawB, rawC0, rawE01, rawE2, rawZ, rawAhat, rawBhat, rawC0hat,
      rawD0, rawD1, rawD2, rawSigma2, rawSig2Pow, rawHandleTail, EtaDisplay.toRaw,
      EtaDisplay.wfB, Export.RawWord.wf, Export.RawWord.wfList, Export.RawSpec.wf]

/-! ## The gate-A constants and the six hash pins

One `<decl>_astHash` constant and one `#eval Export.assertAstHash` guard per frozen instance
(the WW5 convention).  The `#eval` recomputes the digest from the tree at elaboration time, so
the constants cannot drift, and the digests are the certificates' `word_hash` values from
`general_2adic/generated/MANIFEST.json` — a green elaboration is cross-repo agreement.  The
manifest keys by `candidate_id`, never by `word_hash`. -/

/-- **The `ℚ₂(√−10)` tree**: `(α,r,ε,η,h) = (2,1,1,1,0)`, i.e. `(α,r,p) = (2,1,1)` with the
bare-`σ` display.  Packet Cor. 8.2 puts `ℚ₂(√−10)` on the procyclic row with
`(r,ε,η) = (1,1,1)`; **the sign row does not exist** (packet Prop. 8.1), and this pin is
**merge gate 9** of the formalization board. -/
def rawMpcSqrtNeg10 : RawWord := rawMpc 2 1 1 .one 0

/-- The `ℚ₂(√10)` tree: `ε = 0`, i.e. `p = 0` — `B` is the bare `x₁`, `z = δ₂²` (F1 discovery:
both `ε` values occur on this row; draft §7.3's field-specific `R₁₀` is F5's regression row B2,
not this tree). -/
def rawMpcSqrt10 : RawWord := rawMpc 2 1 0 .one 0

/-- The one-handle tree: the `√−10` parameters with `H_1` appended as a fourteenth factor. -/
def rawMpcOneHandle : RawWord := rawMpc 2 1 1 .one 1

/-- The `η̂`-displayed tree: `η = −1/3` through the genuine `zhatPower … (.etahat (-1) 3)`
node — the instance that keeps this file's statements honest at quantified `η̂`. -/
def rawMpcEtaHat : RawWord := rawMpc 2 1 1 (.hat (-1) 3) 0

/-- The `r = 2` tree: `s = 4`, `p = 2`, `η = 5` displayed as the literal power `σ⁵`. -/
def rawMpcLevelTwo : RawWord := rawMpc 2 2 2 (.lit 5) 0

/-- The `α = 3` tree: `m = 4` (the orbit-norm length grows; L does not), `η = 3` displayed as
`σ³`. -/
def rawMpcAlphaThree : RawWord := rawMpc 3 1 1 (.lit 3) 0

/-- Gate-A hash of `rawMpcSqrtNeg10`, certificate
`M-procyclic-alpha2-r1-eps1-eta1-h0-q2-v001` — the digest the selection freeze quotes for
row 5, and the one WW5's `frozenRowHashes` registry already carries. -/
def rawMpcSqrtNeg10_astHash : String :=
  "55b24a4b141274bc30d09468096f4fa021184c5dc22c17823e423457928a26cf"

/-- Gate-A hash of `rawMpcSqrt10`, certificate `M-procyclic-alpha2-r1-eps0-eta1-h0-q2-v001`. -/
def rawMpcSqrt10_astHash : String :=
  "1eb3dd0112182d42371d9c56a12c4e718004ca37c1e80383132170c928433362"

/-- Gate-A hash of `rawMpcOneHandle`, certificate
`M-procyclic-alpha2-r1-eps1-eta1-h1-q2-v001`. -/
def rawMpcOneHandle_astHash : String :=
  "94927545d3c6703f7a2c5a962bd655b68754306cdba8346d4a8c350629a417f8"

/-- Gate-A hash of `rawMpcEtaHat`, certificate
`M-procyclic-alpha2-r1-eps1-etahat-h0-q2-v001`. -/
def rawMpcEtaHat_astHash : String :=
  "144906bb32da92b3d956cb910d28ef7929dd81fb6ce931ae51d9029cf54b511f"

/-- Gate-A hash of `rawMpcLevelTwo`, certificate
`M-procyclic-alpha2-r2-eps1-eta5-h0-q2-v001`. -/
def rawMpcLevelTwo_astHash : String :=
  "c9dc9031f4c92657d33eb1898406402d41584d6b4f375266f103ba87eb784b65"

/-- Gate-A hash of `rawMpcAlphaThree`, certificate
`M-procyclic-alpha3-r1-eps1-eta3-h0-q2-v001`. -/
def rawMpcAlphaThree_astHash : String :=
  "2a117b37ae3001988c46f710ad4613246d4653902dd78abbb308141a744b0bb4"

/-- **The merge-gate-9 registry pin**: the `√−10` digest this file declares is byte-identical
to the one WW5's `Export.frozenRowHashes` recorded for the Mpc row — a wave-2 words file must
reproduce its row's digest there, not invent one. -/
theorem frozenRowHashes_mpc :
    Export.frozenRowHashes[3]!.2 = rawMpcSqrtNeg10_astHash := rfl

#eval Export.assertAstHash "WMP M-procyclic-alpha2-r1-eps1-eta1-h0-q2-v001 (sqrt(-10), gate 9)"
  rawMpcSqrtNeg10 rawMpcSqrtNeg10_astHash

#eval Export.assertAstHash "WMP M-procyclic-alpha2-r1-eps0-eta1-h0-q2-v001 (sqrt(10))"
  rawMpcSqrt10 rawMpcSqrt10_astHash

#eval Export.assertAstHash "WMP M-procyclic-alpha2-r1-eps1-eta1-h1-q2-v001 (h = 1)"
  rawMpcOneHandle rawMpcOneHandle_astHash

#eval Export.assertAstHash "WMP M-procyclic-alpha2-r1-eps1-etahat-h0-q2-v001 (etahat display)"
  rawMpcEtaHat rawMpcEtaHat_astHash

#eval Export.assertAstHash "WMP M-procyclic-alpha2-r2-eps1-eta5-h0-q2-v001 (r = 2)"
  rawMpcLevelTwo rawMpcLevelTwo_astHash

#eval Export.assertAstHash "WMP M-procyclic-alpha3-r1-eps1-eta3-h0-q2-v001 (alpha = 3)"
  rawMpcAlphaThree rawMpcAlphaThree_astHash

/-! ### The `denote` bridges

What makes the hash pins bite on the semantic word: `Export.denote` inlines the `Auxiliary`
wrappers, expands the `OrbitNorm` and `HyperbolicHandles` blocks, and resolves the names, and
these six `rfl`s say that doing so to the hashed trees produces exactly `mpcW` at the matching
parameters.  One per pinned instance and **never generic** (wave-2 rule 2: `OrbitNorm` denotes
at a concrete length only — `m = 2` on the four `α = 2` instances, `m = 4` at `α = 3`; the
handle block likewise at `h = 0` and `h = 1`).  The hash never moves under any of this: it is
taken of the unexpanded tree. -/

set_option maxRecDepth 4000

theorem denote_rawMpc_sqrtNeg10 :
    Export.denote (denoteCtx 0) rawMpcSqrtNeg10 = some (mpcW 2 1 1 .one 0) := by rfl

theorem denote_rawMpc_sqrt10 :
    Export.denote (denoteCtx 0) rawMpcSqrt10 = some (mpcW 2 1 0 .one 0) := by rfl

theorem denote_rawMpc_oneHandle :
    Export.denote (denoteCtx 1) rawMpcOneHandle = some (mpcW 2 1 1 .one 1) := by rfl

theorem denote_rawMpc_etaHat :
    Export.denote (denoteCtx 0) rawMpcEtaHat = some (mpcW 2 1 1 (.hat (-1) 3) 0) := by rfl

theorem denote_rawMpc_levelTwo :
    Export.denote (denoteCtx 0) rawMpcLevelTwo = some (mpcW 2 2 2 (.lit 5) 0) := by rfl

theorem denote_rawMpc_alphaThree :
    Export.denote (denoteCtx 0) rawMpcAlphaThree = some (mpcW 3 1 1 (.lit 3) 0) := by rfl

end GQ2.Dyadic.Words.Mpc
