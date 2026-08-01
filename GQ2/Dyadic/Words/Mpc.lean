/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Word.Export
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.Words.Alphabet

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
was ratified at WN0-a).  **Audited axiom state**: 160 declarations, every one std-3-or-less
(`propext`/`Classical.choice`/`Quot.sound` or fewer; scratch audit over the full declaration
list), no `native_decide` anywhere — kernel `decide` only — so the census is untouched.  Everything lives in the namespace `GQ2.Dyadic.Words.Mpc`, so nothing
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

/-! ## The alphabet — procyclic-`M`

The word uses `x₀, x₁, x₂` and `σ, τ`; the `h` handle pairs use `x₃, …, x_{2h+2}`, so the
alphabet is `Generator (2 + 2h)`, whose wild letters are `Fin (2h + 3)`.

`coreLetter`, `handleU`, `handleV`, `wildGen`, `genOfName`, `denoteCtx`, `handlesW` and the
handle/kill-wild companions live once, in `GQ2.Dyadic.Words` (`Words/Alphabet.lean`), and are
reached from this sub-namespace without an `open`.  This row is on the **no-node-at-`h = 0`** handle
shape — the measured procyclic display, which the compact-`N` emitter does not share — so the
word goes through the list device `handleTailW`, also hoisted.
-/

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
  | 0 => .zpow (dW h 2) ((2 : ℕ) : ℤ)
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

end Word

/-- The linear-copy factors `R_lin^pc = A²[A,B]·C₀^{2^α}[C₀,D]·E₀₁^pc·E₂^pc`.

Exponent vocabulary is F1's: `s r = 2^r`, `m α = 2^{α−1}`, and the `p`-argument is
`GQ2.Dyadic.p ε r = ε·2^{r−1}` at the instances. -/
noncomputable def linFactors (α r p : ℕ) (η : EtaDisplay) (h : ℕ) :
    List (PWord (Generator (2 + 2 * h))) :=
  [.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ),
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
  [.zpow (aHatW h (s r) (m α)) ((2 : ℕ) : ℤ),
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
      [.zpow (dW h 0) ((2 : ℕ) : ℤ), .comm (dW h 0) (dW h 1)] ++ handleTailW h)

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

set_option maxRecDepth 4000

/-! ### Layer pins for the two novel constructors

WW5's two-tier discipline pins tree → bytes in the kernel and bytes → digest by `#eval`.  The
kernel tier cannot be inherited here the way WN0-a inherited it (`Export` carries no frozen
Mpc tree to `rfl`-equate against — this row's trees arrive with this ticket), and a whole-tree
byte pin would be an 11-kB string literal (the `√−10` canonical serialization is 10 849
bytes), so the six `#eval` digest gates above carry the tree → digest check end-to-end, and
the kernel tier is supplied for exactly the two constructors WW5's own literal rows never
exercised: the `OrbitNorm` node and the `ZhatPower … (.etahat …)` node.  A serialization
regression in either fails here, in the kernel, on a minimal input. -/

/-- The `OrbitNorm` node serializes with sorted keys `length/op/step/word` — pinned in the
kernel; no WW5 literal row contains one. -/
example : Export.canonicalJson (.orbitNorm (.generator "u") (.int 2) (.generator "z"))
    = "{\"length\":{\"type\":\"Int\",\"value\":2},\"op\":\"OrbitNorm\",\"step\":\
      {\"name\":\"u\",\"op\":\"Generator\"},\"word\":{\"name\":\"z\",\"op\":\"\
      Generator\"}}" := rfl

/-- The `ZhatPower`/`etahat` node serializes with sorted keys, the spec with
`den/num/type` — pinned in the kernel at the frozen `η = −1/3` display; no WW5 literal row
contains one. -/
example : Export.canonicalJson (.zhatPower (.generator "sigma") (.etahat (-1) 3))
    = "{\"exponent_spec\":{\"den\":3,\"num\":-1,\"type\":\"EtaHat\"},\"op\":\"Zha\
      tPower\",\"word\":{\"name\":\"sigma\",\"op\":\"Generator\"}}" := rfl

/-! ### The `denote` bridges

What makes the hash pins bite on the semantic word: `Export.denote` inlines the `Auxiliary`
wrappers, expands the `OrbitNorm` and `HyperbolicHandles` blocks, and resolves the names, and
these six `rfl`s say that doing so to the hashed trees produces exactly `mpcW` at the matching
parameters.  One per pinned instance and **never generic** (wave-2 rule 2: `OrbitNorm` denotes
at a concrete length only — `m = 2` on the four `α = 2` instances, `m = 4` at `α = 3`; the
handle block likewise at `h = 0` and `h = 1`).  The hash never moves under any of this: it is
taken of the unexpanded tree. -/

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

/-! ## The displayed factorization `R_{M,pc} = R_lin^pc · R̂^pc · D₀²[D₀,D₁] · H_h`

The named copies, as `prodList`s of their factor lists, and the value-level factorization of
the whole word.  `mpcHatW` is the word packet Prop. 9.2 is about; WMP-b's Fox certificate reads
`mpcLinW` (the linear copy) and proves the hat copy's row vanishes. -/

/-- The linear copy `R_lin^pc`. -/
noncomputable def mpcLinW (α r p : ℕ) (η : EtaDisplay) (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList (linFactors α r p η h)

/-- The hat copy `R̂^pc = Sh_M(R_lin^pc)`, as emitted (explicit `Auxiliary` spelling). -/
noncomputable def mpcHatW (α r p : ℕ) (η : EtaDisplay) (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList (hatFactors α r p η h)

/-- The plus block `D₀²[D₀,D₁]` — shadow-stable (`Sh_M` fixes it), and the sole survivor of
the char-2 cancellation: its second-order value is `Q₊(c₀,c₁) = q(c₀)+b_q(c₀,c₁)`. -/
noncomputable def plusW (h : ℕ) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList [.zpow (dW h 0) ((2 : ℕ) : ℤ), .comm (dW h 0) (dW h 1)]

section Factored

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {n h : ℕ}

/-- Evaluation of a `prodList` at a marking, as a `List.prod`. -/
theorem eval_prodListM (t : Marking n G) :
    ∀ ws : List (PWord (Generator n)),
      t.eval (PWord.prodList ws) = (ws.map (t.eval ·)).prod
  | [] => rfl
  | w :: ws => by
      rw [PWord.prodList_cons, Marking.eval_mul, eval_prodListM t ws, List.map_cons,
        List.prod_cons]

/-! `Marking.eval` unfolding lemmas for the constructors F2 leaves without marking-level
`@[simp]` forms — all `rfl`; local conveniences (WWH hoist candidates), used so that every
letter-value lemma in this file lives at one level and simp never has to cross
`Marking.eval_def`. -/

@[simp] theorem meval_conj (t : Marking n G) (u g : PWord (Generator n)) :
    t.eval (.conj u g) = conjR (t.eval u) (t.eval g) := rfl

@[simp] theorem meval_comm (t : Marking n G) (u v : PWord (Generator n)) :
    t.eval (.comm u v) = commR (t.eval u) (t.eval v) := rfl

@[simp] theorem meval_zpow (t : Marking n G) (u : PWord (Generator n)) (k : ℤ) :
    t.eval (.zpow u k) = t.eval u ^ k := rfl

@[simp] theorem meval_profPow (t : Marking n G) (u : PWord (Generator n)) (γ : Zhat) :
    t.eval (.profPow u γ) = t.eval u ^ᶻ γ := rfl

@[simp] theorem meval_omega2Pow (t : Marking n G) (u : PWord (Generator n)) :
    t.eval (PWord.omega2Pow u) = t.eval u ^ᶻ omega2 := rfl

/-- **The displayed factorization, at the value level**: the word evaluates to
`R_lin^pc · R̂^pc · D₀²[D₀,D₁] · H_h` at every marking.  (`prodList` does not split
syntactically over `++`, so this is a statement about values, which is all the boundary
theory needs.) -/
theorem eval_mpcW_factored (α r p : ℕ) (η : EtaDisplay) (t : Marking (2 + 2 * h) G) :
    t.eval (mpcW α r p η h)
      = t.eval (mpcLinW α r p η h) * t.eval (mpcHatW α r p η h) * t.eval (plusW h) *
          t.eval (handlesW h) := by
  have htail : ((handleTailW h).map (t.eval ·)).prod = t.eval (handlesW h) := by
    match h with
    | 0 => simp [handleTailW, handlesW]
    | h + 1 => simp [handleTailW]
  rw [mpcW, mpcLinW, mpcHatW, plusW, eval_prodListM, eval_prodListM, eval_prodListM,
    eval_prodListM, List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append, htail]

end Factored

/-! ## Gate B: the tame boundary

Packet Prop. 9.2's proof shape.  Killing the wild letters sends every δ-letter to
`w := τ^{ω₂}` and every `C₀`-type letter to a power of `S₂ := σ^{ω₂}`; the commutators whose
two sides are both powers of one base die unconditionally (`[A,B]`, `[C₀,D]`, `[Ĉ₀,D]`,
`[D₀,D₁]` — the `D`-cases through the `ℤ̂`-commutation helpers, at every `η̂` display), and what
survives is an explicit word in `w` and `S₂` whose σ-skeleton carries the **Prop. 9.2 power
balance** `−2m·2^r + 2^α·2^r = 0` and whose `w`-part dies exactly under Gate-B rule **T1**
(`τ^{ω₂} = 1` — supplied inside `Γ_R` by packet Lem. 3.1, `τ` pro-odd).  Stating the *values*
is the template rule; the vanishing statements are separate. -/

/-! ### The Prop. 9.2 power balance

`s = 2^r`, `m = 2^{α−1}`: the hat copy's σ-skeleton exponent is `−2m·s + 2^α·s`, and it
vanishes for every `α ≥ 1`.  Stated in the packet's ℤ-display and in the ℕ-form the group
computations consume. -/

/-- The ℕ-form of the balance: `s·2^α = 2·(s·m)` — the exponent identity that kills both
copies' σ-skeletons at both boundaries. -/
theorem s_mul_two_pow {α : ℕ} (hα : 1 ≤ α) (r : ℕ) : s r * 2 ^ α = 2 * (s r * m α) := by
  rw [← two_mul_m hα]
  ring

/-- **Packet Prop. 9.2, the displayed balance**: the hat copy's total σ₂-power is
`−2m·2^r + 2^α·2^r = 0`. -/
theorem prop_9_2_balance {α : ℕ} (hα : 1 ≤ α) (r : ℕ) :
    -(2 * (m α : ℤ)) * 2 ^ r + 2 ^ α * 2 ^ r = 0 := by
  have hz : 2 * (m α : ℤ) = 2 ^ α := by exact_mod_cast two_mul_m hα
  rw [← hz]
  ring

section Tame

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {h : ℕ}

/-- The three displays of `D = σ^{η̂}` evaluate uniformly to `σ ^ᶻ η̂` — what makes every
boundary statement in this file display-independent. -/
theorem eval_etaDisplay (t : Marking (2 + 2 * h) G) (η : EtaDisplay) :
    t.eval η.toPWord = t.σ ^ᶻ η.zhat := by
  cases η with
  | one => simp [EtaDisplay.toPWord, EtaDisplay.zhat]
  | lit k => simp [EtaDisplay.toPWord, EtaDisplay.zhat]
  | hat num den => rfl

/-- Killing the wild letters does not touch the `D`-letter: its value is still `σ ^ᶻ η̂`. -/
theorem eval_killWild_etaDisplay (t : Marking (2 + 2 * h) G) (η : EtaDisplay) :
    (Marking.killWildLetters t).eval η.toPWord = t.σ ^ᶻ η.zhat := by
  rw [eval_etaDisplay]
  rfl

/-- `σ₂^k` (as displayed) evaluates to `(σ^{ω₂})^k` at every marking and every `k` — the
`k = 1` display collapse is invisible at the value level. -/
theorem eval_sig2PowW (t : Marking (2 + 2 * h) G) (k : ℕ) :
    t.eval (sig2PowW h k) = (t.σ ^ᶻ omega2) ^ k := by
  match k with
  | 0 => simp [sig2PowW]
  | 1 => simp [sig2PowW]
  | k + 2 => simp only [sig2PowW, meval_zpow, Marking.eval_sigma2W, zpow_natCast]

@[simp] theorem eval_killWild_uW (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    (Marking.killWildLetters t).eval (uW h i) = t.τ ^ᶻ omega2 := by
  simp [uW]

/-- **Every δ-letter dies to `w = τ^{ω₂}` at the tame boundary** — the reason Gate B is a fact
about `τ`, and the `x₂`-free reason `δ₂` and the whole `E₂^pc` block have tame content at
all. -/
@[simp] theorem eval_killWild_dW (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    (Marking.killWildLetters t).eval (dW h i) = t.τ ^ᶻ omega2 := by
  simp [dW]

theorem eval_killWild_c0W (t : Marking (2 + 2 * h) G) (s' : ℕ) :
    (Marking.killWildLetters t).eval (c0W h s') = (t.σ ^ᶻ omega2) ^ s' := by
  simp [c0W, zpow_natCast]

theorem eval_killWild_aW (t : Marking (2 + 2 * h) G) (s' m' : ℕ) :
    (Marking.killWildLetters t).eval (aW h s' m')
      = ((t.σ ^ᶻ omega2) ^ (s' * m'))⁻¹ := by
  simp only [aW, PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul, Marking.eval_inv,
    Marking.eval_gen, Marking.eval_one, meval_zpow, killWildLetters_coreLetter, inv_one,
    one_mul, mul_one, eval_killWild_c0W]
  rw [zpow_neg, zpow_natCast, ← pow_mul]

theorem eval_killWild_bW (t : Marking (2 + 2 * h) G) (p : ℕ) :
    (Marking.killWildLetters t).eval (bW h p) = (t.σ ^ᶻ omega2) ^ p := by
  match p with
  | 0 => simp [bW]
  | p + 1 =>
      rw [show bW h (p + 1)
          = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (p + 1)] from rfl]
      simp [eval_sig2PowW]

/-- The tame value of `E₀₁^pc` is S1.9's four-factor block `𝓔(S₂^a, S₂^b; w, w)` at the
collapsed letters `δ₀ = δ₁ = w`. -/
theorem eval_killWild_e01W (t : Marking (2 + 2 * h) G) (a b : ℕ) :
    (Marking.killWildLetters t).eval (e01W h a b)
      = eBlock ((t.σ ^ᶻ omega2) ^ a) ((t.σ ^ᶻ omega2) ^ b) (t.τ ^ᶻ omega2) (t.τ ^ᶻ omega2) := by
  simp only [e01W, PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul, Marking.eval_one,
    meval_conj, meval_zpow, eval_killWild_dW, Marking.eval_sigma2W, Marking.killWildLetters_σ,
    zpow_natCast, mul_one]
  rw [eBlock]
  simp [mul_assoc]

/-- The tame value of the orbit-norm expansion is S1.9's `orbitNorm` block — the group-level
compression `orbitNorm_eq` then applies to it. -/
theorem eval_orbitNormFactors {n : ℕ} (t : Marking n G)
    (z u : PWord (Generator n)) (k : ℕ) :
    t.eval (PWord.prodList (Export.orbitNormFactors z u k))
      = orbitNorm (t.eval u) (t.eval z) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hsplit : Export.orbitNormFactors z u (k + 1)
          = Export.orbitNormFactors z u k ++ [.conj z (.zpow u ((k : ℤ) + 1))] := by
        simp [Export.orbitNormFactors, List.range_succ]
      rw [hsplit, eval_prodListM, List.map_append, List.prod_append, ← eval_prodListM t, ih,
        orbitNorm_succ]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        meval_conj, meval_zpow]
      rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

theorem eval_killWild_zW (t : Marking (2 + 2 * h) G) (p : ℕ) :
    (Marking.killWildLetters t).eval (zW h p)
      = t.τ ^ᶻ omega2 * conjR (t.τ ^ᶻ omega2) ((t.σ ^ᶻ omega2) ^ p) := by
  match p with
  | 0 =>
      simp only [zW, meval_zpow, eval_killWild_dW, pow_zero, conjR_one, zpow_natCast, pow_two]
  | p + 1 =>
      rw [show zW h (p + 1)
          = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (p + 1))] from rfl]
      simp [eval_sig2PowW]

/-- The tame value of `E₂^pc`: the `δ₂`-prefix collapses to `w^{S₂^s}` and the orbit-norm
block to `𝒩_{S₂^s, m}(w·w^{S₂^p})^{S₂^{sm}}` — all of it a word in `w` and `S₂`, dead under T1
and only under T1. -/
theorem eval_killWild_e2W (t : Marking (2 + 2 * h) G) (s' m' p : ℕ) :
    (Marking.killWildLetters t).eval (e2W h s' m' p)
      = conjR (t.τ ^ᶻ omega2) ((t.σ ^ᶻ omega2) ^ s')
        * conjR
            (orbitNorm ((t.σ ^ᶻ omega2) ^ s')
              (t.τ ^ᶻ omega2 * conjR (t.τ ^ᶻ omega2) ((t.σ ^ᶻ omega2) ^ p)) m')
            ((t.σ ^ᶻ omega2) ^ (s' * m')) := by
  simp only [e2W, PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul, Marking.eval_one,
    meval_conj, meval_zpow, eval_killWild_dW, eval_orbitNormFactors, eval_killWild_zW,
    Marking.eval_sigma2W, Marking.killWildLetters_σ, zpow_natCast, mul_one]

theorem eval_killWild_c0HatW (t : Marking (2 + 2 * h) G) (s' : ℕ) :
    (Marking.killWildLetters t).eval (c0HatW h s') = (t.σ ^ᶻ omega2) ^ s' := by
  simp [c0HatW, zpow_natCast]

theorem eval_killWild_aHatW (t : Marking (2 + 2 * h) G) (s' m' : ℕ) :
    (Marking.killWildLetters t).eval (aHatW h s' m')
      = (t.τ ^ᶻ omega2)⁻¹ * ((t.σ ^ᶻ omega2) ^ (s' * m'))⁻¹ := by
  simp only [aHatW, PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul,
    Marking.eval_inv, Marking.eval_one, meval_zpow, eval_killWild_dW, eval_killWild_c0HatW,
    mul_one]
  rw [zpow_neg, zpow_natCast, ← pow_mul]

theorem eval_killWild_bHatW (t : Marking (2 + 2 * h) G) (p : ℕ) :
    (Marking.killWildLetters t).eval (bHatW h p)
      = t.τ ^ᶻ omega2 * (t.σ ^ᶻ omega2) ^ p := by
  match p with
  | 0 => simp [bHatW]
  | p + 1 =>
      rw [show bHatW h (p + 1)
          = PWord.prodList [dW h 1, sig2PowW h (p + 1)] from rfl]
      simp [eval_sig2PowW]

theorem eval_killWild_handlesW (t : Marking (2 + 2 * h) G) :
    (Marking.killWildLetters t).eval (handlesW h) = 1 := by
  rw [eval_handlesW]
  exact MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)

/-! ### The hat copy at the tame boundary: the Prop. 9.2 value-then-vanishing pair -/

/-- **The tame boundary value of the hat copy** (the value half of packet Prop. 9.2).

Unconditional simplifications only: `[Ĉ₀, D]` dies because both sides are `ℤ̂`-powers of `σ`
(at every `η̂` display — `commute_zpowHat_pow`), and nothing else is touched.  What remains is
the σ-skeleton `(S₂^{sm})⁻²·S₂^{s·2^α}` — the displayed `−2m·2^r + 2^α·2^r` — interleaved with
the `w`-carrying factors. -/
theorem eval_killWildLetters_mpcHatW (α r p : ℕ) (η : EtaDisplay) (t : Marking (2 + 2 * h) G) :
    (Marking.killWildLetters t).eval (mpcHatW α r p η h)
      = ((t.τ ^ᶻ omega2)⁻¹ * ((t.σ ^ᶻ omega2) ^ (s r * m α))⁻¹) ^ 2
        * commR ((t.τ ^ᶻ omega2)⁻¹ * ((t.σ ^ᶻ omega2) ^ (s r * m α))⁻¹)
            (t.τ ^ᶻ omega2 * (t.σ ^ᶻ omega2) ^ p)
        * (t.σ ^ᶻ omega2) ^ (s r * 2 ^ α)
        * eBlock ((t.σ ^ᶻ omega2) ^ (p + s r * m α)) ((t.σ ^ᶻ omega2) ^ (s r * m α))
            (t.τ ^ᶻ omega2) (t.τ ^ᶻ omega2) := by
  rw [mpcHatW, hatFactors, eval_prodListM]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, meval_zpow,
    meval_comm, eval_killWild_aHatW, eval_killWild_bHatW, eval_killWild_c0HatW,
    eval_killWild_e01W, eval_killWild_etaDisplay]
  rw [commR_eq_one_iff.mpr (commute_zpowHat_pow t.σ omega2 (s r) η.zhat), one_mul]
  simp only [zpow_natCast]
  rw [← pow_mul]
  simp only [pow_two, mul_assoc]

/-- **The vanishing half of packet Prop. 9.2**: under Gate-B rule T1 (`τ^{ω₂} = 1` — inside
`Γ_R` this is packet Lem. 3.1, `τ` pro-odd) the hat copy's tame value is `1`, *by* the power
balance `−2m·2^r + 2^α·2^r = 0` and by nothing else: the `w`-factors die pointwise, and the
surviving σ-skeleton is `(S₂^{sm})⁻²·S₂^{s·2^α} = S₂^{2sm−2sm}`. -/
theorem eval_killWildLetters_mpcHatW_eq_one {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking (2 + 2 * h) G) (hw : t.τ ^ᶻ omega2 = 1) :
    (Marking.killWildLetters t).eval (mpcHatW α r p η h) = 1 := by
  rw [eval_killWildLetters_mpcHatW, hw]
  simp only [inv_one, one_mul, mul_one, eBlock, one_conjR]
  rw [commR_eq_one_iff.mpr
      (((Commute.refl (t.σ ^ᶻ omega2)).pow_pow (s r * m α) p).inv_left), mul_one,
    s_mul_two_pow hα r, mul_comm 2 (s r * m α), pow_mul]
  group

/-! ### The full word at the tame boundary -/

/-- **The tame boundary value of the frozen procyclic-`M` word** (the template's value-form
statement).

Killing the wild letters leaves an explicit word in `w = τ^{ω₂}`, `S₂ = σ^{ω₂}`: the two
copies' σ-skeletons (each balanced by Prop. 9.2), the two `𝓔`-blocks at `δ₀ = δ₁ = w`, the
`E₂^pc` value through S1.9's `orbitNorm`, the hat `[Â,B̂]`-commutator (a genuine `w`-term), and
the plus block's `w²`.  The four same-base commutators are already dead — `[C₀,D]` and
`[Ĉ₀,D]` at *every* `η̂` display via the `ℤ̂`-commutation — and no `T1`-type hypothesis has
been spent. -/
theorem eval_killWildLetters_mpcW (α r p : ℕ) (η : EtaDisplay) (t : Marking (2 + 2 * h) G) :
    (Marking.killWildLetters t).eval (mpcW α r p η h)
      = (((t.σ ^ᶻ omega2) ^ (s r * m α))⁻¹) ^ 2 * (t.σ ^ᶻ omega2) ^ (s r * 2 ^ α)
        * eBlock ((t.σ ^ᶻ omega2) ^ (p + s r * m α)) ((t.σ ^ᶻ omega2) ^ (s r * m α))
            (t.τ ^ᶻ omega2) (t.τ ^ᶻ omega2)
        * (conjR (t.τ ^ᶻ omega2) ((t.σ ^ᶻ omega2) ^ (s r))
            * conjR
                (orbitNorm ((t.σ ^ᶻ omega2) ^ (s r))
                  (t.τ ^ᶻ omega2 * conjR (t.τ ^ᶻ omega2) ((t.σ ^ᶻ omega2) ^ p)) (m α))
                ((t.σ ^ᶻ omega2) ^ (s r * m α)))
        * (((t.τ ^ᶻ omega2)⁻¹ * ((t.σ ^ᶻ omega2) ^ (s r * m α))⁻¹) ^ 2
            * commR ((t.τ ^ᶻ omega2)⁻¹ * ((t.σ ^ᶻ omega2) ^ (s r * m α))⁻¹)
                (t.τ ^ᶻ omega2 * (t.σ ^ᶻ omega2) ^ p)
            * (t.σ ^ᶻ omega2) ^ (s r * 2 ^ α)
            * eBlock ((t.σ ^ᶻ omega2) ^ (p + s r * m α)) ((t.σ ^ᶻ omega2) ^ (s r * m α))
                (t.τ ^ᶻ omega2) (t.τ ^ᶻ omega2))
        * (t.τ ^ᶻ omega2) ^ 2 := by
  rw [eval_mpcW_factored, eval_killWildLetters_mpcHatW, eval_killWild_handlesW, mul_one]
  -- the linear copy
  rw [mpcLinW, linFactors, eval_prodListM]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, meval_zpow,
    meval_comm, eval_killWild_aW, eval_killWild_bW, eval_killWild_c0W, eval_killWild_e01W,
    eval_killWild_e2W, eval_killWild_etaDisplay]
  -- `[A,B] = 1` (powers of `S₂`) and `[C₀,D] = 1` (`ℤ̂`-powers of `σ`).
  rw [commR_eq_one_iff.mpr
      (((Commute.refl (t.σ ^ᶻ omega2)).pow_pow (s r * m α) p).inv_left),
    commR_eq_one_iff.mpr (commute_zpowHat_pow t.σ omega2 (s r) η.zhat)]
  -- the plus block
  rw [plusW, eval_prodListM]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, meval_zpow,
    meval_comm, eval_killWild_dW, commR_self]
  -- realign the two ℤ-squares and the `C₀`-power, then normalize brackets.
  simp only [zpow_natCast]
  rw [← pow_mul]
  simp only [one_mul, pow_two, mul_assoc]

/-- **Gate-B collapse of the full word under rule T1**: with `τ^{ω₂} = 1` every `w`-factor
dies, both σ-skeletons cancel by the Prop. 9.2 balance, and the whole tame value is `1`.
This is the content behind the admissibility routes below; nothing about the word's *shape*
is used beyond the balance. -/
theorem eval_killWildLetters_mpcW_eq_one {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking (2 + 2 * h) G) (hw : t.τ ^ᶻ omega2 = 1) :
    (Marking.killWildLetters t).eval (mpcW α r p η h) = 1 := by
  rw [eval_killWildLetters_mpcW, hw]
  simp only [inv_one, one_mul, mul_one, eBlock, one_conjR, one_pow]
  rw [commR_eq_one_iff.mpr
      (((Commute.refl (t.σ ^ᶻ omega2)).pow_pow (s r * m α) p).inv_left),
    orbitNorm_eq]
  simp only [one_conjR, one_mul, inv_pow, inv_mul_cancel, mul_one]
  rw [s_mul_two_pow hα r, mul_comm 2 (s r * m α), pow_mul]
  group

end Tame

/-! ## The `ω₂`-only fragment

Five of the six frozen instances are `ω₂`-only — their `D`-letter displays are the bare `σ` or
a literal power — so the `ℕ`-exponent route of packet Lem. 2.2 is available for their numeric
pins.  **The `η̂`-displayed instance is not** (`.hat` is a genuine profinite power with
`γ ≠ ω₂`): every branch word carrying an `η̂`-node inherits WNP-a's finding, and its honest
evaluations go through the resolvers instead. -/

section Omega2Only

variable {h : ℕ}

theorem isOmega2Only_uW (i : Fin 3) : (uW h i).IsOmega2Only := by
  simp [uW]

theorem isOmega2Only_dW (i : Fin 3) : (dW h i).IsOmega2Only := by
  simp [dW, isOmega2Only_uW]

theorem isOmega2Only_sig2PowW (k : ℕ) : (sig2PowW h k).IsOmega2Only := by
  match k with
  | 0 => simp [sig2PowW]
  | 1 => simp [sig2PowW]
  | k + 2 => simp [sig2PowW]

theorem isOmega2Only_c0W (s' : ℕ) : (c0W h s').IsOmega2Only := by
  simp [c0W]

theorem isOmega2Only_aW (s' m' : ℕ) : (aW h s' m').IsOmega2Only := by
  simp [aW, isOmega2Only_c0W]

theorem isOmega2Only_bW (p : ℕ) : (bW h p).IsOmega2Only := by
  match p with
  | 0 => simp [bW]
  | p + 1 =>
      rw [show bW h (p + 1)
          = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (p + 1)] from rfl]
      simp [isOmega2Only_sig2PowW]

theorem isOmega2Only_e01W (a b : ℕ) : (e01W h a b).IsOmega2Only := by
  simp [e01W, isOmega2Only_dW]

theorem isOmega2Only_zW (p : ℕ) : (zW h p).IsOmega2Only := by
  match p with
  | 0 => simp [zW, isOmega2Only_dW]
  | p + 1 =>
      rw [show zW h (p + 1)
          = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (p + 1))] from rfl]
      simp [isOmega2Only_dW, isOmega2Only_sig2PowW]

theorem isOmega2Only_orbitNormFactors {z u : PWord (Generator (2 + 2 * h))}
    (hz : z.IsOmega2Only) (hu : u.IsOmega2Only) (k : ℕ) :
    (PWord.prodList (Export.orbitNormFactors z u k)).IsOmega2Only := by
  refine isOmega2Only_prodList fun w hw => ?_
  rw [Export.orbitNormFactors] at hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact ⟨hz, hu⟩

theorem isOmega2Only_e2W (s' m' p : ℕ) : (e2W h s' m' p).IsOmega2Only := by
  refine isOmega2Only_prodList fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨isOmega2Only_dW 2, by simp⟩
  · exact ⟨isOmega2Only_orbitNormFactors (isOmega2Only_zW p) (by simp) m', by simp⟩

theorem isOmega2Only_c0HatW (s' : ℕ) : (c0HatW h s').IsOmega2Only := by
  simp [c0HatW]

theorem isOmega2Only_aHatW (s' m' : ℕ) : (aHatW h s' m').IsOmega2Only := by
  simp [aHatW, isOmega2Only_dW, isOmega2Only_c0HatW]

theorem isOmega2Only_bHatW (p : ℕ) : (bHatW h p).IsOmega2Only := by
  match p with
  | 0 => simp [bHatW, isOmega2Only_dW]
  | p + 1 =>
      rw [show bHatW h (p + 1) = PWord.prodList [dW h 1, sig2PowW h (p + 1)] from rfl]
      simp [isOmega2Only_dW, isOmega2Only_sig2PowW]

theorem isOmega2Only_prodList_handleTail :
    (PWord.prodList (handleTailW h)).IsOmega2Only := by
  match h with
  | 0 => trivial
  | h + 1 => exact ⟨isOmega2Only_handlesW _, trivial⟩

/-- The handle tail contains at most the handle block: its sole member (when `h ≥ 1`) is
`handlesW h`. -/
theorem eq_handlesW_of_mem_handleTail :
    ∀ {h : ℕ} {w : PWord (Generator (2 + 2 * h))}, w ∈ handleTailW h → w = handlesW h
  | 0, w, hw => absurd hw (by simp [handleTailW])
  | h + 1, w, hw => by simpa [handleTailW] using hw

theorem isOmega2Only_etaDisplay {η : EtaDisplay} (hη : η.IsOmega2Only) :
    (η.toPWord (n := 2 + 2 * h)).IsOmega2Only := by
  cases η with
  | one => trivial
  | lit k => trivial
  | hat num den => exact hη.elim

/-- **Five of the six frozen instances are `ω₂`-only**: whenever the `D`-display is not the
genuine `η̂` node, the whole word is in the `ω₂`-only fragment and packet Lem. 2.2's
`ℕ`-exponent route applies with a single global exponent. -/
theorem isOmega2Only_mpcW (α r p : ℕ) {η : EtaDisplay} (hη : η.IsOmega2Only) (h : ℕ) :
    (mpcW α r p η h).IsOmega2Only := by
  refine isOmega2Only_prodList fun w hw => ?_
  simp only [linFactors, hatFactors, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with (((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)) |
    (rfl | rfl)) | htail
  · exact isOmega2Only_aW (s r) (m α)
  · exact ⟨isOmega2Only_aW (s r) (m α), isOmega2Only_bW p⟩
  · exact isOmega2Only_c0W (s r)
  · exact ⟨isOmega2Only_c0W (s r), isOmega2Only_etaDisplay hη⟩
  · exact isOmega2Only_e01W (p + s r * m α) (s r * m α)
  · exact isOmega2Only_e2W (s r) (m α) p
  · exact isOmega2Only_aHatW (s r) (m α)
  · exact ⟨isOmega2Only_aHatW (s r) (m α), isOmega2Only_bHatW p⟩
  · exact isOmega2Only_c0HatW (s r)
  · exact ⟨isOmega2Only_c0HatW (s r), isOmega2Only_etaDisplay hη⟩
  · exact isOmega2Only_e01W (p + s r * m α) (s r * m α)
  · exact isOmega2Only_dW 0
  · exact ⟨isOmega2Only_dW 0, isOmega2Only_dW 1⟩
  · obtain rfl := eq_handlesW_of_mem_handleTail htail
    exact isOmega2Only_handlesW _

/-- ⚠ **The `η̂`-displayed instance is *not* `ω₂`-only** (WNP-a's finding, inherited): the
`D`-letter is a profinite power with `γ = η̂ ≠ ω₂`, so `PWord.eval_eq_evalNat_of_dvd` is
unavailable on that row and its honest evaluations go through the resolvers. -/
theorem not_isOmega2Only_mpcW_hat (α r p : ℕ) (num den : ℤ) (h : ℕ) :
    ¬ (mpcW α r p (.hat num den) h).IsOmega2Only :=
  fun hw => Npc.toZhat_ne_omega2 ⟨num, den⟩ hw.2.2.2.1.2.1

end Omega2Only

/-! ### Gate-B admissibility: the relativized routes, and the refutation of the bare form

The WN0-a ruling binds: F3's bare `KillsWild` quantifies over every marking with no `τ`
condition, and the tame value of any δ-letter word is a `τ^{ω₂}`-word — so the bare form is
**unsatisfiable** for this word too (`not_killsWild` below), and the admissibility routes are
the `τ`-relativized ones.  Inside `Γ_R` the hypothesis is supplied by packet Lem. 3.1: the
tame relation forces `τ` pro-odd, and `ω₂` kills pro-odd elements. -/

section Admissibility

variable {h : ℕ}

/-- **Gate-B admissibility, relativized to a tame `τ`** — packet Prop. 9.2 as an
admissibility statement: the word dies at the tame boundary of every marking whose `τ`-letter
is killed by `ω₂`. -/
theorem killsWild_of_tau {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (hτ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G), t.τ ^ᶻ omega2 = 1) :
    KillsWild (mpcW α r p η h) := by
  intro G _ _ _ _ _ t
  exact eval_killWildLetters_mpcW_eq_one hα r p η t (hτ G t)

/-- **Gate B rule T1, at a finite marking**: if the `τ`-letter has odd order, the tame
boundary value is trivial — the form the finite-target harnesses (F5) test. -/
theorem eval_killWildLetters_mpcW_eq_one_of_odd {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking (2 + 2 * h) P) (hτ : Odd (orderOf t.τ)) :
    (Marking.killWildLetters t).eval (mpcW α r p η h) = 1 :=
  eval_killWildLetters_mpcW_eq_one hα r p η t
    (by simpa using PWord.eval_omega2Pow_eq_one_of_odd (⇑t) (.gen .tau) hτ)

end Admissibility

section Refutation

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

/-- **The frozen procyclic-`M` word is not Gate-B admissible in F3's unrelativized sense**
(demonstrated at the `√−10` row; the same `w`-count refutes every parameter row).  This is
the KillsWild ruling biting exactly as it must for a δ-letter word: the tame value is a
`τ^{ω₂}`-word, and nothing kills it on a group of even exponent. -/
theorem not_killsWild : ¬ KillsWild (mpcW 2 1 1 .one 0) := by
  intro hR
  have hval := hR (Multiplicative (ZMod 8)) (refuteMarking 0)
  rw [show Marking.killWildLetters (refuteMarking 0) = refuteMarking 0 from
      by ext g; cases g <;> rfl] at hval
  rw [Marking.eval_def,
    PWord.eval_eq_evalNat_of_dvd (by norm_num) zmod8_orderOf_dvd _
      (isOmega2Only_mpcW 2 1 1 (show EtaDisplay.IsOmega2Only .one from trivial) 0),
    omega2Exp_eight] at hval
  exact absurd hval (by decide)

end Refutation

/-! ## Gate C: the marked pro-`2` boundary

The headline of the ticket: `pro2` sends `τ ↦ 1` and collapses every `ω₂`-power, so **every
δ-letter dies** — `δᵢ ↦ (xᵢ·1)·xᵢ⁻¹`, one certified move each — and with them **both
correction blocks** (`E₀₁^pc`, `E₂^pc`: every letter is a δ) **and the hat copy's
δ-content**.  What survives of the hat copy is its σ-skeleton `σ^{−2sm}·σ^{s·2^α}`, killed by
the *same* Prop. 9.2 balance that killed it at Gate B; the plus block dies with its δ's; and
the linear copy becomes **exactly eq. `Mpc-core`**, `mWord α A B C₀ D` on the pro-2 letter
values

```
A = x₀⁻¹C₀⁻ᵐ,  B = x₁σ^p,  C₀ = x₂σ^s,  D = σ^{η̂}
```

(with `σ₂ ↦ σ`, and `σ^{η̂}` the honest `ℤ̂`-power — the `η̂`-contract keeps the letter, by
`Npc.toZhat_ne_omega2`), times MC2's `handleWord`.  No hypothesis on the marking is needed
beyond `1 ≤ α` for the balance. -/

section Pro2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {h : ℕ}

/-- The pro-2 value of the three `η̂` displays is uniformly the honest `σ ^ᶻ η̂` — the `.hat`
case is where Gate C's `η̂`-contract keeps the profinite power (`η̂ ≠ ω₂`, WNP-a's
`toZhat_ne_omega2`, reused; the orchestrator's D5 note: `EtaData.toZhat` *is*
`etaHatZ ∘ toPadic` definitionally, so no bridge is owed). -/
theorem eval_pro2_etaDisplay (t : Marking (2 + 2 * h) G) (η : EtaDisplay) :
    t.eval (pro2 η.toPWord) = t.σ ^ᶻ η.zhat := by
  cases η with
  | one => simp [EtaDisplay.toPWord, EtaDisplay.zhat]
  | lit k => simp [EtaDisplay.toPWord, EtaDisplay.zhat]
  | hat num den =>
      rw [show (EtaDisplay.hat num den).toPWord (n := 2 + 2 * h)
          = .profPow (.gen .sigma) (Export.RawSpec.toZhat (.etahat num den)) from rfl,
        pro2_profPow_of_ne _
          (show Export.RawSpec.toZhat (.etahat num den) ≠ omega2 from
            Npc.toZhat_ne_omega2 ⟨num, den⟩)]
      rfl

/-- **Every δ-letter dies at the pro-2 boundary**: `δᵢ ↦ (xᵢ·1)·xᵢ⁻¹ = 1` — the certified
move behind "the hat copy and both correction blocks die at pro-2". -/
theorem eval_pro2_dW (t : Marking (2 + 2 * h) G) (i : Fin 3) :
    t.eval (pro2 (dW h i)) = 1 := by
  simp [dW, uW]

theorem eval_pro2_sig2PowW (t : Marking (2 + 2 * h) G) (k : ℕ) :
    t.eval (pro2 (sig2PowW h k)) = t.σ ^ k := by
  match k with
  | 0 => simp [sig2PowW]
  | 1 => simp [sig2PowW]
  | k + 2 => simp only [sig2PowW, pro2_zpow, pro2_sigma2W, meval_zpow, Marking.eval_gen,
      Marking.apply_sigma, zpow_natCast]

theorem eval_pro2_c0W (t : Marking (2 + 2 * h) G) (s' : ℕ) :
    t.eval (pro2 (c0W h s')) = t (coreLetter h 2) * t.σ ^ s' := by
  simp [c0W, zpow_natCast, coreLetter]

theorem eval_pro2_aW (t : Marking (2 + 2 * h) G) (s' m' : ℕ) :
    t.eval (pro2 (aW h s' m'))
      = (t (coreLetter h 0))⁻¹ * ((t (coreLetter h 2) * t.σ ^ s') ^ m')⁻¹ := by
  rw [aW, pro2_prodList]
  simp only [List.map_cons, List.map_nil, pro2_inv, pro2_zpow, coreLetter, pro2_gen_wild,
    PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul, Marking.eval_inv,
    Marking.eval_gen, Marking.eval_one, meval_zpow, mul_one]
  rw [show Marking.eval t (pro2 (c0W h s')) = t (coreLetter h 2) * t.σ ^ s' from
      eval_pro2_c0W t s', zpow_neg, zpow_natCast]
  rfl

theorem eval_pro2_bW (t : Marking (2 + 2 * h) G) (p : ℕ) :
    t.eval (pro2 (bW h p)) = t (coreLetter h 1) * t.σ ^ p := by
  match p with
  | 0 => simp [bW, coreLetter]
  | p + 1 =>
      rw [show bW h (p + 1)
          = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (p + 1)] from rfl,
        pro2_prodList]
      simp only [List.map_cons, List.map_nil, coreLetter, pro2_gen_wild,
        PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul, Marking.eval_gen,
        Marking.eval_one, mul_one, eval_pro2_sig2PowW]

/-- `E₀₁^pc` dies whole at the pro-2 boundary: both δ-letters die and conjugates of `1`
are `1`. -/
theorem eval_pro2_e01W (t : Marking (2 + 2 * h) G) (a b : ℕ) :
    t.eval (pro2 (e01W h a b)) = 1 := by
  simp [e01W, eval_pro2_dW]

theorem eval_pro2_zW (t : Marking (2 + 2 * h) G) (p : ℕ) :
    t.eval (pro2 (zW h p)) = 1 := by
  match p with
  | 0 => simp [zW, eval_pro2_dW]
  | p + 1 =>
      rw [show zW h (p + 1)
          = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (p + 1))] from rfl,
        pro2_prodList]
      simp [eval_pro2_dW]

theorem pro2_orbitNormFactors (z u : PWord (Generator (2 + 2 * h))) (k : ℕ) :
    (Export.orbitNormFactors z u k).map pro2
      = Export.orbitNormFactors (pro2 z) (pro2 u) k := by
  simp [Export.orbitNormFactors, List.map_map]

/-- `E₂^pc` dies whole at the pro-2 boundary: `δ₂` dies, so the orbit-norm base dies, so the
orbit norm dies (`orbitNorm_eq` at base `1`). -/
theorem eval_pro2_e2W (t : Marking (2 + 2 * h) G) (s' m' p : ℕ) :
    t.eval (pro2 (e2W h s' m' p)) = 1 := by
  rw [e2W, pro2_prodList]
  simp only [List.map_cons, List.map_nil, pro2_conj, pro2_zpow, pro2_sigma2W,
    PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul, Marking.eval_one, meval_conj,
    meval_zpow, mul_one, eval_pro2_dW, one_conjR, one_mul, pro2_prodList,
    pro2_orbitNormFactors, eval_orbitNormFactors, eval_pro2_zW]
  rw [orbitNorm_eq]
  simp

theorem eval_pro2_c0HatW (t : Marking (2 + 2 * h) G) (s' : ℕ) :
    t.eval (pro2 (c0HatW h s')) = t.σ ^ s' := by
  simp [c0HatW, zpow_natCast]

theorem eval_pro2_aHatW (t : Marking (2 + 2 * h) G) (s' m' : ℕ) :
    t.eval (pro2 (aHatW h s' m')) = (t.σ ^ (s' * m'))⁻¹ := by
  rw [aHatW, pro2_prodList]
  simp only [List.map_cons, List.map_nil, pro2_inv, pro2_zpow, PWord.prodList_cons,
    PWord.prodList_nil, Marking.eval_mul, Marking.eval_inv, Marking.eval_one, meval_zpow,
    mul_one, eval_pro2_dW, inv_one, one_mul]
  rw [show Marking.eval t (pro2 (c0HatW h s')) = t.σ ^ s' from eval_pro2_c0HatW t s',
    zpow_neg, zpow_natCast, ← pow_mul]

theorem eval_pro2_bHatW (t : Marking (2 + 2 * h) G) (p : ℕ) :
    t.eval (pro2 (bHatW h p)) = t.σ ^ p := by
  match p with
  | 0 => simp [bHatW, eval_pro2_dW]
  | p + 1 =>
      rw [show bHatW h (p + 1) = PWord.prodList [dW h 1, sig2PowW h (p + 1)] from rfl,
        pro2_prodList]
      simp [eval_pro2_dW, eval_pro2_sig2PowW]

/-- **The hat copy dies at the pro-2 boundary** — its δ-letters vanish and its σ-skeleton is
killed by the *same* Prop. 9.2 balance as at Gate B.  The `[Ĉ₀,D]`-commutator dies at every
`η̂` display through the `ℤ̂`-commutation. -/
theorem eval_pro2_mpcHatW {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcHatW α r p η h)) = 1 := by
  rw [mpcHatW, hatFactors, pro2_prodList, eval_prodListM]
  simp only [List.map_cons, List.map_nil, pro2_zpow, pro2_comm, List.prod_cons, List.prod_nil,
    meval_zpow, meval_comm, mul_one, eval_pro2_aHatW, eval_pro2_bHatW, eval_pro2_c0HatW,
    eval_pro2_e01W, eval_pro2_etaDisplay]
  rw [commR_eq_one_iff.mpr (((Commute.refl t.σ).pow_pow (s r * m α) p).inv_left),
    commR_eq_one_iff.mpr (commute_pow_zpowHat t.σ (s r) η.zhat)]
  simp only [zpow_natCast, one_mul]
  rw [← pow_mul, s_mul_two_pow hα r, mul_comm 2 (s r * m α), pow_mul]
  group

/-- The plus block dies at the pro-2 boundary with its δ-letters. -/
theorem eval_pro2_plusW (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (plusW h)) = 1 := by
  rw [plusW, pro2_prodList, eval_prodListM]
  simp [eval_pro2_dW]

/-- **Gate C: the pro-2 boundary value of the frozen procyclic-`M` word is eq. `Mpc-core`.**

`pro2 R_{M,pc}` evaluates, at every marking, to `mWord α A B C₀ D · handleWord` on the pro-2
letter values `A = x₀⁻¹C₀⁻ᵐ`, `B = x₁σ^p`, `C₀ = x₂σ^s`, `D = σ^{η̂}`.  The hat copy and both
correction blocks are gone — their δ/δ₂-letters vanish, and the hat σ-skeleton dies by the
Prop. 9.2 balance (`1 ≤ α` is exactly that hypothesis).  This is the statement MC-M's rank-4
theory consumes, and the σ-versus-σ₂ collapse (`σ₂ ↦ σ`) is what makes the letters land on
the marked core's. -/
theorem eval_pro2_mpcW {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcW α r p η h))
      = MarkedCore.mWord α
          ((t (coreLetter h 0))⁻¹ * ((t (coreLetter h 2) * t.σ ^ s r) ^ m α)⁻¹)
          (t (coreLetter h 1) * t.σ ^ p)
          (t (coreLetter h 2) * t.σ ^ s r)
          (t.σ ^ᶻ η.zhat)
        * MarkedCore.handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) := by
  have hfact : t.eval (pro2 (mpcW α r p η h))
      = t.eval (pro2 (mpcLinW α r p η h)) * t.eval (pro2 (mpcHatW α r p η h)) *
          t.eval (pro2 (plusW h)) * t.eval (pro2 (handlesW h)) := by
    have htail : (((handleTailW h).map pro2).map (t.eval ·)).prod
        = t.eval (pro2 (handlesW h)) := by
      match h with
      | 0 => simp [handleTailW, handlesW]
      | h + 1 => simp [handleTailW]
    rw [mpcW, mpcLinW, mpcHatW, plusW, pro2_prodList, pro2_prodList, pro2_prodList,
      pro2_prodList, eval_prodListM, eval_prodListM, eval_prodListM, eval_prodListM,
      List.map_append, List.map_append, List.map_append, List.map_append, List.map_append,
      List.map_append, List.prod_append, List.prod_append, List.prod_append, htail]
  rw [hfact, eval_pro2_mpcHatW hα, eval_pro2_plusW, pro2_handlesW, eval_handlesW, mul_one,
    mul_one]
  -- the linear copy is the core word
  rw [mpcLinW, linFactors, pro2_prodList, eval_prodListM]
  simp only [List.map_cons, List.map_nil, pro2_zpow, pro2_comm, List.prod_cons, List.prod_nil,
    meval_zpow, meval_comm, mul_one, eval_pro2_aW, eval_pro2_bW, eval_pro2_c0W,
    eval_pro2_e01W, eval_pro2_e2W, eval_pro2_etaDisplay]
  simp only [zpow_natCast]
  rw [MarkedCore.mWord]
  simp only [commR, GQ2.commP, mul_assoc]

/-- At `h = 0` the handle factor is empty and the pro-2 value is eq. `Mpc-core` on the nose,
in the `t.x`-spelling. -/
theorem eval_pro2_mpcW_zero {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking 2 G) :
    t.eval (pro2 (mpcW α r p η 0))
      = MarkedCore.mWord α
          ((t.x 0)⁻¹ * ((t.x 2 * t.σ ^ s r) ^ m α)⁻¹)
          (t.x 1 * t.σ ^ p)
          (t.x 2 * t.σ ^ s r)
          (t.σ ^ᶻ η.zhat) := by
  rw [eval_pro2_mpcW hα (h := 0),
    show MarkedCore.handleWord (fun j : Fin 0 => t (handleU j))
        (fun j : Fin 0 => t (handleV j)) = 1 from rfl, mul_one]
  rfl

/-- The same value read as MC-M's **full relator shape** `mRelWord` at the standard marking
(`coreMark` on the four Labute letters `A, B, C₀, D`). -/
theorem eval_pro2_mpcW_eq_mRelWord {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : EtaDisplay)
    (t : Marking 2 G) :
    t.eval (pro2 (mpcW α r p η 0))
      = MarkedCore.mRelWord (h := 0) α
          (MarkedCore.coreMark
            ((t.x 0)⁻¹ * ((t.x 2 * t.σ ^ s r) ^ m α)⁻¹)
            (t.x 1 * t.σ ^ p)
            (t.x 2 * t.σ ^ s r)
            (t.σ ^ᶻ η.zhat)) := by
  rw [eval_pro2_mpcW_zero hα, MarkedCore.mRelWord_coreMark]

end Pro2

/-! ## The six frozen instances

The branch rows, in F1's vocabulary.  The word arguments `(α, r, p, η-display, h)` and the
`BranchData` fields are related by `p = B.pVal = GQ2.Dyadic.p ε r` and `s = B.sVal = 2^r`;
the pins below tie each instance's word parameters to those fields so the display data
cannot drift from the branch datum. -/

section Instances

/-- **`ℚ₂(√−10)` is procyclic** `(r, ε, η) = (1, 1, 1)` — packet Cor. 8.2.  The sign row does
not exist (packet Prop. 8.1: under ramified `i`, an even `η` is impossible), which is why
this instance is **merge gate 9**: the field the draft treated by a field-specific sign-row
word is carried by the frozen procyclic row. -/
theorem branchData_sqrtNeg10 :
    (BranchData.Mpc 2 1 true 1).Valid ∧ (BranchData.Mpc 2 1 true 1).level = 1 ∧
      (BranchData.Mpc 2 1 true 1).sVal = 2 ∧ (BranchData.Mpc 2 1 true 1).pVal = 1 :=
  ⟨⟨by norm_num, by norm_num⟩, rfl, rfl, rfl⟩

/-- `ℚ₂(√10)` is the `ε = 0` row (draft §7.3 has `B = x₁`, i.e. `p = 0` — the F1 discovery
that both `ε` values occur).  Draft §7.3's field-specific word `R₁₀` (marking
`ν(a,b,c,d) = (−4,0,2,1)`) is F5's regression row B2, pointwise-equal to this row on every
harness target but NOT the frozen spelling. -/
theorem branchData_sqrt10 :
    (BranchData.Mpc 2 1 false 1).Valid ∧ (BranchData.Mpc 2 1 false 1).pVal = 0 :=
  ⟨⟨by norm_num, by norm_num⟩, rfl⟩

/-- The `r = 2` row: `s = 4`, `p = 2` (for any Frobenius unit `η` — the word's `η`-display
is separate certificate data, `σ⁵` on the frozen instance). -/
theorem branchData_levelTwo (η : ℤ_[2]ˣ) :
    (BranchData.Mpc 2 2 true η).Valid ∧ (BranchData.Mpc 2 2 true η).sVal = 4 ∧
      (BranchData.Mpc 2 2 true η).pVal = 2 :=
  ⟨⟨by norm_num, by norm_num⟩, rfl, rfl⟩

/-- The `α = 3` row: the orbit-norm length is `m 3 = 4` while the word length is flat
(L = 67 at every `α` — the phase-4 exit criterion). -/
theorem branchData_alphaThree (η : ℤ_[2]ˣ) :
    (BranchData.Mpc 3 1 true η).Valid ∧ m 3 = 4 :=
  ⟨⟨by norm_num, by norm_num⟩, rfl⟩

/-- The word-parameter dictionary at the six instances, in F1's vocabulary: `s r`, `m α` and
`GQ2.Dyadic.p ε r` evaluate to exactly the literals the emitted trees display. -/
example : s 1 = 2 ∧ s 2 = 4 ∧ m 2 = 2 ∧ m 3 = 4 ∧ GQ2.Dyadic.p true 1 = 1 ∧
    GQ2.Dyadic.p true 2 = 2 ∧ GQ2.Dyadic.p false 1 = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> simp [GQ2.Dyadic.p, epsVal]

/-- The `η̂`-display pair `(−1, 3)` is already S1.M-canonical, so WW5's constructor-level
canonicalization is a no-op on the frozen tree and the hash is of the displayed pair. -/
example : Export.RawSpec.canon (.etahat (-1) 3) = .etahat (-1) 3 := rfl

/-- The `√−10` letters, spelled out at the instance (`s = 2`, `m = 2`, `p = 1`):
`C₀ = x₂σ₂²`, `A = x₀⁻¹C₀⁻²`, `B = x₁σ₂`, and the hat letters `Ĉ₀ = σ₂²`, `Â = δ₀⁻¹Ĉ₀⁻²`,
`B̂ = δ₁σ₂`. -/
example :
    c0W 0 2 = PWord.prodList [.gen (coreLetter 0 2), .zpow sigma2W 2] ∧
    aW 0 2 2 = PWord.prodList [.inv (.gen (coreLetter 0 0)), .zpow (c0W 0 2) (-2)] ∧
    bW 0 1 = PWord.prodList [.gen (coreLetter 0 1), sigma2W] ∧
    c0HatW 0 2 = PWord.zpow sigma2W 2 ∧
    aHatW 0 2 2 = PWord.prodList [.inv (dW 0 0), .zpow (c0HatW 0 2) (-2)] ∧
    bHatW 0 1 = PWord.prodList [dW 0 1, sigma2W] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section InstanceBoundaries

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The `√−10` pro-2 boundary, end-to-end**: the frozen word's Gate-C value at the gate-9
instance is eq. `Mpc-core` at the instance letters `A = x₀⁻¹(x₂σ²)⁻²`, `B = x₁σ`,
`C₀ = x₂σ²`, `D = σ` (`η = 1`). -/
theorem eval_pro2_sqrtNeg10 (t : Marking 2 G) :
    t.eval (pro2 (mpcW 2 1 1 .one 0))
      = MarkedCore.mWord 2 ((t.x 0)⁻¹ * ((t.x 2 * t.σ ^ 2) ^ 2)⁻¹) (t.x 1 * t.σ)
          (t.x 2 * t.σ ^ 2) t.σ := by
  rw [eval_pro2_mpcW_zero (by norm_num) 1 1 .one t]
  norm_num [s, EtaDisplay.zhat]

/-- **The `√10` pro-2 boundary**: at `ε = 0` the `B`-letter collapses to the bare `x₁` — the
`p = 0` display is invisible at the value level but the letter is genuinely different. -/
theorem eval_pro2_sqrt10 (t : Marking 2 G) :
    t.eval (pro2 (mpcW 2 1 0 .one 0))
      = MarkedCore.mWord 2 ((t.x 0)⁻¹ * ((t.x 2 * t.σ ^ 2) ^ 2)⁻¹) (t.x 1)
          (t.x 2 * t.σ ^ 2) t.σ := by
  rw [eval_pro2_mpcW_zero (by norm_num) 1 0 .one t]
  norm_num [s, EtaDisplay.zhat]

end InstanceBoundaries

end Instances

/-! ## Numerical stress pins

Nothing below is cited by a proof; these are regression pins in the sense of plan §3 A1.

**The python twins are F5's rows** (`scripts/dyadic_sanity_counts.py`): its A-rows measure
the frozen `√10`/`√−10` spellings by epimorphism-count vectors over `(S₃, D₈, A₄)`, both
`(6, 1568, 120)`; row B1 keeps the retired `√−10` relative-norm word as the regression
alternative, row B2 pins the draft-§7.3 `√10` word pointwise-equal to the frozen row.  Those
counts are **cited, never proved here** (they need genuine epimorphism enumeration on groups
with odd part).  Per WNP-a's abelian-invisibility finding, no abelian pin can see `η` or the
correction blocks — the pins below test the exponent skeleton, the `ω₂`-placement, and the
balance instead, and the nonabelian core content is the S₃ witness. -/

section StressZMod8

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

/-- **Stress (genuine `ω₂`)**: the *profinite* denotation of the `√−10` word — real
`x ^ᶻ ω₂` powers — is `ofAdd 3`.

Additively (`σ₂ = 5`, `δᵢ = 1`, `C₀ = 3`, `A = 1`, `Ĉ₀ = 2`, `Â = 3`):
`2 + 0 + 4 + 0 + 4 + 5` (linear copy) `+ 6 + 0 + 0 + 0 + 4` (hat copy) `+ 2 + 0` (plus
block) `= 27 ≡ 3`.  This pins the exponent skeleton (`C₀⁴`, `A²`, `m = 2`), the `ω₂`-placement
on the `(xᵢτ)`-subwords, and the two `E`-block arities at once. -/
theorem eval_zmod8_sqrtNeg10 :
    zmod8Marking.eval (mpcW 2 1 1 .one 0) = Multiplicative.ofAdd (3 : ZMod 8) := by
  rw [Marking.eval_def,
    PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight _
      (isOmega2Only_mpcW 2 1 1 (show EtaDisplay.IsOmega2Only .one from trivial) 0),
    omega2Exp_eight]
  decide

/-- **Stress (`ω₂` is not vacuous)**: forcing the profinite exponent to `3` — an odd non-`ω₂`
representative — gives `ofAdd 7 ≠ ofAdd 3`, so the `ω₂`-slots genuinely carry information at
this marking. -/
theorem evalNat_zmod8_sqrtNeg10_three :
    PWord.evalNat ⇑zmod8Marking 3 (mpcW 2 1 1 .one 0) = Multiplicative.ofAdd (7 : ZMod 8) := by
  decide

/-- **Stress (the tame boundary is not vacuous, and the balance is visible)**: at this marking
the `τ`-letter has even order, so the Gate-B value is *not* trivial — `not_killsWild` read
numerically — while the σ-skeleton part has already cancelled: the value `ofAdd 5` is exactly
the `w`-count `13·w = 13 ≡ 5` (`w = τ^{ω₂} = 1` additively), the σ-contribution being `0` by
the Prop. 9.2 balance even though `σ₂ = 5 ≠ 0` here. -/
theorem eval_killWildLetters_zmod8_sqrtNeg10 :
    (Marking.killWildLetters zmod8Marking).eval (mpcW 2 1 1 .one 0)
      = Multiplicative.ofAdd (5 : ZMod 8) := by
  rw [Marking.eval_def,
    PWord.eval_eq_evalNat_of_dvd (by norm_num) orderOf_dvd_eight _
      (isOmega2Only_mpcW 2 1 1 (show EtaDisplay.IsOmega2Only .one from trivial) 0),
    omega2Exp_eight]
  decide

end StressZMod8

/-- **Stress (nonabelian: the core is not a vacuous relator)**: eq. `Mpc-core` is nontrivial
at an explicit marking of `S₃`, so the two commutators do real work.  In `S₃` both `a²` and
`c⁴` drop out (`a² = c⁴ = 1` for transpositions) and each commutator of the two distinct
transpositions is the same `3`-cycle `g`, so the core value is `g² ≠ 1`.

An explicit witness rather than `∃ … by decide` (kernel recursion budget); the abelian pins
above cannot see this content (WNP-a's invisibility finding), which is exactly why this
witness is the one that matters for the core.  F5's A-rows report the epimorphism count
`120` on `A₄` for this row; that number is cited, never proved here. -/
theorem mWord_ne_one_perm :
    MarkedCore.mWord 2 (Equiv.swap 0 1) (Equiv.swap 0 2) (Equiv.swap 0 1) (Equiv.swap 0 2)
      ≠ (1 : Equiv.Perm (Fin 3)) := by decide

end GQ2.Dyadic.Words.Mpc
