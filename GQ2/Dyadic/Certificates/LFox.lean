/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Word.FoxCert

/-!
# Dyadic campaign, ticket WL-b: the Fox certificate of the odd-degree branch word `L_sq`

The certificate layer of the type-`L` lane, sitting on WL-a's word (`GQ2/Dyadic/Words/L.lean`),
WW1's Fox evaluator (`GQ2/Dyadic/Word/Fox.lean`) and WW2's certificate grammar
(`GQ2/Dyadic/Word/FoxCert.lean`).  It carries packet Def. 9.1 items (3)–(4) for **row 1** of the
R5 selection freeze,

```
R^{sq}_{L,n} = (x₀^σ)⁻¹ (x₀⁻³τ)^{ω₂} x₁² [x₁, x₁^{σ₂}] · ∏_{j=1}^{h} [x_{2j}, x_{2j+1}],
```

`n = 2h + 1`, as the evaluated Fox row `d¹ : (Generator (2h+1) → V) →+ V` in the packet's column
order `σ, τ, x₀, x₁, x₂, …`.

## The row

The universal first-order row, in the notation `S = σ`, `P` = the `ω₂`-norm projector (WW2's
opaque atom `TameSym.proj`):

| relator | `σ` | `τ` | `x₀` | `x₁` | handles |
|---|---|---|---|---|---|
| wild `R^{sq}_{L,n}` | `0` | `P` | `S⁻¹ + P` | `0` | `0` |

(`lSqWildRow`), with the three module classes obtained by *assigning* `P`, never computing it:

| class | `P` | row |
|---|---|---|
| unramified (`T = 1`, `S` free) | `1` | `(0, 1, 1 + S⁻¹, 0, 0…)` |
| split/scalar (`T = 1`, `S = 1`) | `1` | `(0, 1, 0, 0, 0…)` |
| ramified (`V^T = 0`) | `0` | `(0, 0, S⁻¹, 0, 0…)` |

⚠ **This is the same universal row as the compact-`N` one** (`nCompactWildRow`,
`(0, P, 0, 0, S⁻¹ + P)`), sitting on a *different column*: there the invertible block rides the
conjugated letter `x₂^{-σ}`, here it rides `(x₀^σ)⁻¹`.  The two rows are one piece of formal
data up to the column relabelling, which is the first-order shadow of the packet's remark that
both branch families are built from the same conjugated-letter atom.

## Where each entry comes from (packet §9.2's proof shape, mechanised)

* `D((x₀^σ)⁻¹) = −S⁻¹·a(x₀)` — the `σ`-contributions of `σ⁻¹x₀σ` cancel in pairs and the
  conjugator survives as `S⁻¹` (`foxD_invConjX0`).  **This is the `S⁻¹` of the `x₀`-column**, and
  it exists only because the conjugator is there.
* `D((x₀^{-3}τ)^{ω₂}) = P·(a(x₀) + a(τ))` — the lift-level `ω₂` rule.  The cube contributes
  `a(x₀)` and **not** `3·a(x₀)`: the geometric sum over a trivially-acting base has *odd* length,
  hence augmentation `1` (`WordLift.sum_pow_smul_of_trivial_odd`, `fox.py` §2's second corollary).
  This is the one place the `L_sq` row differs in mechanism from the compact-`N` row, whose
  leading power `p_α = 2 + 2^α` is *even* and therefore contributes `0`.  `P` is never computed:
  the two class collapses are WW1's engine lemmas `WordLift.powOmega2_u_of_trivial` (`P = 1`)
  and `WordLift.powOmega2_u_of_oddFixedPointFree` (`P = 0`).
* `D(x₁²) = 2·a(x₁) = 0` — the square is even, so the `x₁`-column loses its first summand
  (`foxD_x1Sq`).
* `D([x₁, x₁^{σ₂}]) = 0` and `D(H_h) = 0` — commutators of trivially-acting letters
  (`foxD_comm_of_trivial`), with **no hypothesis on `σ₂`** (it enters only as a conjugator).
  Together these kill the `x₁`-column outright and all `2h` handle columns.

So the whole square-commutator block `x₁²[x₁,x₁^{σ₂}]` — the part of the word that carries the
rank-3 core's name — is **invisible at first order**: `foxDHom_lSq_coreLetter_one_column`.

## The `n = 1` base: transport, not re-derivation

Per the frozen selection (`selection-freeze.md` row 1, SQ1) the `n = 1` word *is* Roe's `Γ_R`
relator, and WW1/WW2 already certified that row (`foxD_gammaRWildWord_split`,
`gammaRWildRowCert`, `gammaRWildRowPivotCert`, `gammaRWildRowRamifiedCert`).  This file therefore
**transports** rather than re-derives: `foxDHom_lSqW_zero` proves the two Fox *carriers* are
equal — WL-a's `evalFin_lSqW_zero` applied at the **lifted** marking, which is legitimate because
`foxLift_ofQ2` says the lifted `n = 1` marking is again an `ofQ2` marking (of `FoxH.liftMarking`)
— after which every WW2 certificate for `gammaRWildWord` is a certificate for `lSqW 0` with its
`target`, its `colOps` and its `verifies` proof **reused verbatim**
(`lSqWildRowCertQ2Unram`, `lSqWildRowCertQ2Pivot`, `lSqWildRowCertQ2Ram`).

The two trees are genuinely different (the certificate spells `x₀^{-3}` and an `n`-ary
`Multiply`, the ledger `(x₀³)⁻¹` and left association) and the gap is WL-a's two `zpow`
realignments plus associativity; none of that is redone here, it rides inside
`evalFin_lSqW_zero`.

## Handle stability (the board's "`n = 1` base + handle stability")

Stated as theorems, not prose, in three complementary shapes:

1. **Evaluated, matrix form** — `foxDHom_lSq_eq_base_comp_unram` (and `…_ram`):
   `foxDHom t (lSqW h) = (foxDHom (coreMarking t) (lSqW 0)).comp (coreRestrict h)`,
   an equality of `AddMonoidHom`s, where `coreRestrict h` is restriction of an offset vector
   along the core embedding `coreEmbed h : Generator 1 ↪ Generator (2h+1)`.  Since `coreRestrict`
   forgets exactly the `2h` handle coordinates, this **is** "the degree-`n` certificate = the
   `n = 1` certificate ⊕ `2h` zero columns".
2. **Formal-data form** — `lSqWildRow_row_coreEmbed`: the degree-`n` formal row restricted to the
   core letters is the `n = 1` formal row, relabelled along `coreSym h`; and
   `lSqWildRow_handleU_eq_zero`/`_handleV_eq_zero`: every handle entry is `.zero`.
3. **Column form** — `foxDHom_lSq_handleU_column`/`_handleV_column`: each of the `2h` handle
   columns of the evaluated row is zero, at every `h` and in both classes.

## The `q_K` pin — the honest content

WL-a's mandated `q_K > 2` discriminator is a `q_K = 4` target at which the frozen word dies and
its `σ₂ → σ` mutant does not (`Words.lSq_ne_lSqSigmaSlip_at_qFour`).  **The Fox row cannot see
that**, and the pin at this layer is exactly that fact, proved rather than observed:
`foxD_lSqSigmaSlip_eq_lSq` says the mutant and the frozen word have **the same Fox row at every
marking of the class**, because their only differing factor is a commutator of trivially-acting
letters.  Correspondingly no row theorem below carries a `q` or a tame relation
`τ^σ = τ^{q_K}` — `foxD_lSq_unram_of_tameRel` records that the hypothesis is discardable at every
`q`.  The `q_K`-sensitivity of the lane lives at the *word* level and in the tame row, never in
the wild row.

## What is deliberately **not** here

* **The two-relator Jacobian.**  The tame relator `τ^σ(τ^q)⁻¹`, its row and its normal forms are
  word-independent, and already exist — in `GQ2/Dyadic/Certificates/N0Fox.lean` (`tameRelW`,
  `normCoeff`, `tameUnramRow`, `tameRow`, `foxD_tameRelW_of_tameRel`, `foxD_tameRelW_unram`).
  That file cannot be imported here (see the namespace note below), and duplicating it would be
  four sections of copy.  **Dedup ticket recorded**: those declarations belong in
  `GQ2/Dyadic/Word/FoxCert.lean`, one layer down, next to the grammar they use — they mention no
  branch word.  Once hoisted, the `L_sq` Jacobian certificate is the compact-`N` one with the
  column moved: the same single row operation `row_wild += S · row_tame` produces the same
  diagonal `(τ ↦ S⁻¹ ; x₀ ↦ 1 − S⁻¹)`.
* **The `1 − S⁻¹` invertibility criterion.**  Proved once and for all as
  `Certificates.isUnit_oneSubSInvEnd_iff` (invertible on `V` iff `V^S = 0`); the block on this
  row is literally the same operator, so there is no reason to re-derive it.

## Axiom state (recorded per WL-b instructions; `#print axioms` run in a scratch file, not
committed)

**Audited 2026-07-31, all 91 named declarations of this file**: every one depends on a subset of
the standard axioms `[propext, Classical.choice, Quot.sound]` — 51 print exactly std-3, 32 print
`[propext, Quot.sound]`, 2 print `[propext]` and 6 depend on no axioms at all.  Zero `sorryAx`,
zero `native_decide`, and **zero `B3c`/`B8` leaks**: WL-a imports `SqCore.Certificate` but never
applies the rank-3 discharge, and nothing here touches it either.  The census stays at eleven.

In particular the headlines `foxD_lSq_unram`, `foxD_lSq_ram`, `foxD_lSq_split`,
`foxD_lSqSigmaSlip_eq_lSq` (with its two class corollaries), `foxDHom_lSq_handleU_column`,
`foxDHom_lSq_handleV_column`, `foxDHom_lSq_coreLetter_one_column`,
`foxDHom_lSq_eq_base_comp_unram`, `foxDHom_lSq_eq_base_comp_ram`,
`lSqWildRow_toHom_comp_coreRestrict`, `lSqWildRowCertUnram`, `lSqWildRowCertRam`,
`lSqWildRowCertSplit`, `lSqWildRowPivotCert`, `foxDHom_lSqW_zero`, `lSqWildRowCertQ2Unram`,
`lSqWildRowCertQ2Pivot`, `lSqWildRowCertQ2Ram` and `foxD_lSq_unram_zero_eq_hand` all print exactly
std-3; `lSqWildRow_row_coreEmbed` prints strictly less (`[propext, Quot.sound]`).

## Implementation notes

**Not `module`-style, and forced**: `GQ2.Dyadic.Words.L` is a plain file (it imports F3's
`TameBoundary` and `SqCore.Certificate`), and a `module` file may not import a non-`module` one —
the WN0-a ruling that `Words/` and `Certificates/` are plain-import layers.  The other import,
`GQ2.Dyadic.Word.FoxCert`, is `module`-style, which is fine in this direction.

⚠ **Namespace**: this file lives in `GQ2.Dyadic.Certificates.LSq`, a *sub*-namespace, rather than
in the bare `GQ2.Dyadic.Certificates` that `N0Fox.lean` uses.  The reason is concrete: `Words/L.lean`
and `Words/N0.lean` both declare `coreLetter`, `handleU`, `handleV`, `handlesW`, `handleTail`, …
directly in `GQ2.Dyadic.Words`, so importing both **fails** — and `GQ2.lean` imports both.
(`Words/M0.lean` and `Words/Npc.lean` avoided this with the sub-namespaces `Words.MCompact` and
`Words.Npc`.)  Until `Words/L.lean` is re-namespaced, this file cannot import `N0Fox.lean` either,
and it keeps its own names out of the way so that the same collision cannot recur one layer up.
The `open GQ2.Dyadic.Words` below is the single line that a re-namespacing of `Words/L.lean`
would have to touch here.

The mathlib-shaped micro-lemmas `even_nsmul_eq_zero` and `neg_eq_self` are restated locally, as
`N0Fox.lean` also keeps them local.
-/

namespace GQ2.Dyadic.Certificates.LSq

-- ORCHESTRATOR 2026-08-01: `Words/L.lean` re-namespaced to `Words.LSq` (integration fix);
-- this is the anticipated one-line touch.
open GQ2.FoxH GQ2.Dyadic.Words.LSq

/-! ## Micro-lemmas over an elementary coefficient module -/

/-- An even multiple of a `2`-torsion element vanishes. -/
theorem even_nsmul_eq_zero {V : Type*} [AddCommGroup V] (hV₂ : ∀ v : V, v + v = 0) {k : ℕ}
    (hk : Even k) (v : V) : k • v = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul]
  exact hV₂ _

/-- Over a `2`-torsion module every element is its own negative. -/
theorem neg_eq_self {V : Type*} [AddCommGroup V] (hV₂ : ∀ v : V, v + v = 0) (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_left (hV₂ v)

/-! ## The odd-degree alphabet at a simple tame module

The standing setting: a finite coefficient module `V` over a finite marked group `C`, with the
marking `t` of the `L_sq` alphabet `Generator (2h + 1)`.  "Simple tame module" enters only through
the hypotheses `hwild` (the wild inertia acts trivially — every `x_i`, handles included) and the
class condition on `τ`; the `σ`-action `S` is never restricted, and **`σ₂` is never constrained at
all**. -/

section Rows

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 * h + 1) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite V] in
/-- The core letters `x₀`, `x₁` act trivially, from the uniform wild hypothesis. -/
theorem trivAct_coreLetter (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (i : Fin 2) : t (coreLetter h i) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
/-- The handle letters act trivially. -/
theorem trivAct_handleU (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleU j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
@[inherit_doc trivAct_handleU]
theorem trivAct_handleV (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleV j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

/-! ### The five factors, one at a time -/

/-- **Factor 1 — the source of the invertible block.**  `D((x₀^σ)⁻¹) = −S⁻¹·a(x₀)`.

Both `σ`-contributions of `σ⁻¹x₀σ` cancel (the conjugation rule's `+ x̄₀·a(σ) − a(σ)` at a
trivially-acting `x₀`), the conjugator survives as the operator `S⁻¹`, and the outer inverse
contributes the sign.  Deleting the `^σ` would leave `−a(x₀)`, and the unramified `x₀`-column
would be `1 − 1 = 0`; **the block exists because the conjugator is `σ`**. -/
theorem foxD_invConjX0 (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma)))
      = -(t.σ⁻¹ • a (coreLetter h 0)) := by
  have hx0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  have hconj : PWord.evalFin ⇑t E E₂ (.conj (.gen (coreLetter h 0)) (.gen .sigma))
      ∈ trivAct C V := by
    rw [PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_conjR (trivAct_coreLetter t hwild 0) _
  rw [foxD_inv, mem_trivAct.mp (inv_mem hconj), foxD_conj, PWord.evalFin_gen, PWord.evalFin_gen,
    foxD_gen, foxD_gen, hx0]
  simp

/-- **The cube, at odd length.**  `D(x₀^{-3}) = a(x₀)` over a char-`2` module: the geometric sum
`1 + X₀ + X₀²` at a trivially-acting `X₀` has *odd* length, hence augmentation `1`
(`WordLift.sum_pow_smul_of_trivial_odd`), and the negative exponent contributes a sign that a
char-`2` module absorbs.

This is where the `L_sq` row parts company with the compact-`N` row: there the leading power
`p_α = 2 + 2^α` is even and contributes `0`; here the leading power is odd and contributes the
whole `x₀`-offset. -/
theorem foxD_x0NegCube (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (.zpow (.gen (coreLetter h 0)) (-3)) = a (coreLetter h 0) := by
  have hx0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, foxD_zpow_neg', foxD_zpow_natCast]
  simp only [foxEval_gen, PWord.evalFin_gen, foxD_gen]
  rw [WordLift.sum_pow_smul_of_trivial_odd hV₂ hx0 _ ⟨1, by norm_num⟩,
    mem_trivAct.mp (inv_mem (pow_mem (trivAct_coreLetter t hwild 0) 3)),
    neg_eq_self hV₂]

/-- The `a`-letter's inner word `x₀^{-3} · τ` — as a `PWord.prodList`, the certificate's spelling
(WL-a authoring rule 3: the trailing `PWord.one` is part of the tree). -/
theorem foxD_aInner (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau])
      = a (coreLetter h 0) + a .tau := by
  have hx0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_mul,
    PWord.evalFin_zpow, PWord.evalFin_gen, foxD_gen, foxD_one, smul_zero, add_zero,
    foxD_x0NegCube t E E₂ hV₂ hwild,
    mem_trivAct.mp (zpow_mem (trivAct_coreLetter t hwild 0) (-3))]

omit [Finite C] [Finite V] in
/-- The evaluation of the `a`-letter's inner word `x₀^{-3}τ` acts as `τ` does. -/
theorem evalFin_aInner_smul (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (v : V) :
    PWord.evalFin ⇑t E E₂ (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]) • v
      = t.τ • v := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_zpow, PWord.evalFin_gen, PWord.evalFin_gen,
    PWord.evalFin_one, mul_one, mul_smul,
    mem_trivAct.mp (zpow_mem (trivAct_coreLetter t hwild 0) (-3))]
  rfl

omit [Finite C] [Finite V] in
/-- The base of the `a`-letter, in closed form.  No hypothesis: this is the shape of the tree. -/
theorem evalFin_aInner :
    PWord.evalFin ⇑t E E₂ (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau])
      = t (coreLetter h 0) ^ (-3 : ℤ) * t.τ := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_zpow, PWord.evalFin_gen, PWord.evalFin_gen,
    PWord.evalFin_one, mul_one]
  rfl

/-- **Factor 2, split/unramified (`P = 1`)** — `D((x₀^{-3}τ)^{ω₂}) = a(x₀) + a(τ)`.

The `ω₂`-collapse is WW1's engine lemma `WordLift.powOmega2_u_of_trivial`; `powOmega2` is not
unfolded. -/
theorem foxD_aBlock_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂
        (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
      = a (coreLetter h 0) + a .tau := by
  rw [foxD_def, foxEval_omega2Pow,
    WordLift.powOmega2_u_of_trivial hV₂ _
      (fun v => by rw [foxEval_g]; exact (evalFin_aInner_smul t E E₂ hwild v).trans (hτ v))]
  exact foxD_aInner t E E₂ hV₂ hwild a

/-- **Factor 2, ramified (`P = 0`)** — `D((x₀^{-3}τ)^{ω₂}) = 0`.

The engine lemma is `WordLift.powOmega2_u_of_oddFixedPointFree`: the base `x₀^{-3}τ` acts as the
fixed-point-free `T`, and its `2`-primary part acts trivially, so the norm sum vanishes. -/
theorem foxD_aBlock_ram (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂
        (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
      = 0 := by
  rw [foxD_def, foxEval_omega2Pow]
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => hτfpf v ?_) (fun v => ?_)
  · rw [foxEval_g] at hv
    exact (evalFin_aInner_smul t E E₂ hwild v).symm.trans hv
  · rw [foxEval_g, evalFin_aInner t E E₂]
    exact WordLift.powOmega2_smul_of_trivial_mul _ _
      (mem_trivAct.mp (zpow_mem (trivAct_coreLetter t hwild 0) (-3))) hTodd v

/-- **Factor 3** — `D(x₁²) = 0`: the square is even, so over a char-`2` module the geometric sum
at a trivially-acting `X₁` is the scalar `2`, hence `0`. -/
theorem foxD_x1Sq (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (.zpow (.gen (coreLetter h 1)) 2) = 0 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, foxD_zpow_natCast]
  simp only [PWord.evalFin_gen, foxD_gen]
  rw [WordLift.sum_pow_smul_of_trivial (mem_trivAct.mp (trivAct_coreLetter t hwild 1))]
  exact even_nsmul_eq_zero hV₂ ⟨1, by norm_num⟩ _

/-- **Factor 4** — `D([x₁, x₁^{σ₂}]) = 0`.

The commutator of two trivially-acting words, so **no hypothesis on `σ₂`** is used: `σ₂` occurs
in `R^{sq}_{L,n}` only as a conjugator, and `trivAct_conjR` is normality of the kernel of the
permutation representation.  This is the first-order reason the `q_K`-discriminating `σ₂`-slot is
invisible to the Fox row (`foxD_lSqSigmaSlip_eq_lSq`). -/
theorem foxD_cBlock (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂
        (.comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) sigma2W)) = 0 := by
  refine foxD_comm_of_trivial _ _ _ _ ?_ ?_
  · rw [PWord.evalFin_gen]
    exact trivAct_coreLetter t hwild 1
  · rw [PWord.evalFin_conj, PWord.evalFin_gen]
    exact trivAct_conjR (trivAct_coreLetter t hwild 1) _

/-- **Factor 5** — `D(H_h) = 0`: the handle block is a product of commutators of trivially-acting
letters, so its Fox row is zero at every handle count. -/
theorem foxD_handlesW (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) : foxD ⇑t a E E₂ (handlesW h) = 0 := by
  have hmem : ∀ w ∈ (List.finRange h).map fun j =>
      (PWord.comm (.gen (handleU j)) (.gen (handleV j)) : PWord (Generator (2 * h + 1))),
      PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_commR (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)
  rw [handlesW, foxD_prodList_of_trivial _ _ _ _ _ hmem]
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact foxD_comm_of_trivial _ _ _ _ (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)

/-- The handle *tail* contributes nothing, at every `h` — empty list at `h = 0`, a single
vanishing block otherwise.  (WL-a's asymmetry: the frozen `n = 1` tree carries **no**
`HyperbolicHandles` node at all, so `handleTail 0 = []` is the certificate's, not a
simplification.) -/
theorem foxD_handleTail_eq_zero (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 * h + 1) → V) :
    ((handleTail h).map (foxD ⇑t a E E₂)).sum = 0 := by
  cases h with
  | zero => rfl
  | succ k =>
      rw [handleTail, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact foxD_handlesW t E E₂ hwild a

omit [Finite C] [Finite V] in
/-- Every factor of the `L_sq` word evaluates trivially, at both `τ`-classes (the class enters
only through `ha`, the `a`-letter's own evaluation). -/
theorem trivAct_lSq_factors (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (ha : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
        ∈ trivAct C V) :
    ∀ w ∈ lSqCore h ++ handleTail h, PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · simp only [lSqCore, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
      exact inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 0) _)
    · exact ha
    · rw [PWord.evalFin_zpow, PWord.evalFin_gen]
      exact zpow_mem (trivAct_coreLetter t hwild 1) _
    · rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_conj, PWord.evalFin_gen]
      exact trivAct_commR (trivAct_coreLetter t hwild 1)
        (trivAct_conjR (trivAct_coreLetter t hwild 1) _)
  · cases h with
    | zero => simp only [handleTail, List.not_mem_nil] at hw
    | succ k =>
        simp only [handleTail, List.mem_cons, List.not_mem_nil, or_false] at hw
        rw [hw, handlesW]
        refine trivAct_evalFin_prodList ?_
        intro u hu
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hu
        rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
        exact trivAct_commR (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)

omit [Finite C] [Finite V] in
/-- The `a`-letter evaluates trivially on a split/unramified module. -/
theorem trivAct_aBlock_unram (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hτ : ∀ v : V, t.τ • v = v) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
        ∈ trivAct C V := by
  rw [PWord.evalFin_omega2Pow]
  refine trivAct_powOmega2 (mem_trivAct.mpr fun v => ?_)
  exact (evalFin_aInner_smul t E E₂ hwild v).trans (hτ v)

omit [Finite V] in
/-- The `a`-letter evaluates trivially on a ramified module too — there its `ω₂`-part is trivial
for a different reason (`WordLift.powOmega2_smul_of_trivial_mul`). -/
theorem trivAct_aBlock_ram (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
        ∈ trivAct C V := by
  rw [PWord.evalFin_omega2Pow]
  refine mem_trivAct.mpr fun v => ?_
  rw [evalFin_aInner t E E₂]
  exact WordLift.powOmega2_smul_of_trivial_mul _ _
    (mem_trivAct.mp (zpow_mem (trivAct_coreLetter t hwild 0) (-3))) hTodd v

/-! ### The wild rows -/

/-- **The `L_sq` wild row on an unramified simple module** (packet Def. 9.1(3); freeze row 1): at
a marking whose wild letters and whose `τ` act trivially,

```
D(R^{sq}_{L,n}) = a(τ) + (1 + S⁻¹)·a(x₀).
```

Only two of the `2h + 4` columns are nonzero — and they are the *same two* as in the `n = 1`
published `Γ_R` row `x₁ + (1 + S⁻¹)x₂` (`foxD_gammaRWildWord_split_apply`), whatever the degree.
No hypothesis whatever on `S`, and none on `σ₂`. -/
theorem foxD_lSq_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqW h)
      = a .tau + a (coreLetter h 0) + t.σ⁻¹ • a (coreLetter h 0) := by
  have ha := trivAct_aBlock_unram t E E₂ hwild hτ
  rw [lSqW, foxD_prodList_of_trivial _ _ _ _ _ (trivAct_lSq_factors t E E₂ hwild ha),
    List.map_append, List.sum_append, foxD_handleTail_eq_zero t E E₂ hwild, add_zero]
  simp only [lSqCore, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_invConjX0 t E E₂ hwild, foxD_aBlock_unram t E E₂ hV₂ hwild hτ,
    foxD_x1Sq t E E₂ hV₂ hwild, foxD_cBlock t E E₂ hwild, neg_eq_self hV₂]
  abel

/-- **The `L_sq` wild row on a ramified simple module** (`P = 0`): only the `(x₀^σ)⁻¹`
contribution survives,

```
D(R^{sq}_{L,n}) = S⁻¹·a(x₀),
```

a single **unit** entry — the ramified twin, matching WW1's `foxD_gammaRWildWord_ramified_apply`
at `n = 1`. -/
theorem foxD_lSq_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqW h) = t.σ⁻¹ • a (coreLetter h 0) := by
  have ha := trivAct_aBlock_ram t E E₂ hwild hTodd
  rw [lSqW, foxD_prodList_of_trivial _ _ _ _ _ (trivAct_lSq_factors t E E₂ hwild ha),
    List.map_append, List.sum_append, foxD_handleTail_eq_zero t E E₂ hwild, add_zero]
  simp only [lSqCore, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_invConjX0 t E E₂ hwild, foxD_aBlock_ram t E E₂ hwild hτfpf hTodd,
    foxD_x1Sq t E E₂ hV₂ hwild, foxD_cBlock t E E₂ hwild, neg_eq_self hV₂]
  abel

/-- **The `L_sq` wild row on a split (scalar) module**: with `S` acting trivially too, the
`1 + S⁻¹` block *vanishes* and the row degenerates to the `τ`-pivot `a(τ)`.

This is the honest content of "the scalar module separates nothing": the wild relator carries no
information about `x₀` on a module where the whole tame quotient acts trivially. -/
theorem foxD_lSq_split (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqW h) = a .tau := by
  have hσinv : ∀ v : V, t.σ⁻¹ • v = v := fun v => inv_smul_eq_iff.mpr (hσ v).symm
  rw [foxD_lSq_unram t E E₂ hV₂ hwild hτ, hσinv, add_assoc, hV₂, add_zero]

/-! ### The `q_K` pin: the wild row cannot see `σ₂`, hence cannot see `q_K`

WL-a's mandated `q_K > 2` discriminator is the `D₅ × D₃` target at which the frozen word dies and
its `σ₂ → σ` mutant does not (`Words.lSq_ne_lSqSigmaSlip_at_qFour`).  At the Fox layer that
separation **disappears**, and saying so is the honest pin. -/

/-- **The `q_K` pin.**  The `σ₂ → σ` mutant `Words.lSqSigmaSlipW` — which WL-a proved is separated
from the frozen word at a genuine `q_K = 4` tame pair — has **the same Fox row** as the frozen
word, at every marking of the class and every degree.

Both words differ only in their fourth factor, a commutator of trivially-acting letters, and both
such rows vanish.  So the first jet is blind to the `σ₂`-slot, and *a fortiori* to `q_K`: the
lane's `q_K`-sensitivity lives at the word level and in the tame row, never in the wild row. -/
theorem foxD_lSqSigmaSlip_eq_lSq (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (ha : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
        ∈ trivAct C V) (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqSigmaSlipW h) = foxD ⇑t a E E₂ (lSqW h) := by
  have hslip : ∀ w ∈ [(PWord.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma)) :
        PWord (Generator (2 * h + 1))),
      PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]),
      .zpow (.gen (coreLetter h 1)) 2,
      .comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) (.gen .sigma))]
        ++ handleTail h, PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · rw [PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
        exact inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 0) _)
      · exact ha
      · rw [PWord.evalFin_zpow, PWord.evalFin_gen]
        exact zpow_mem (trivAct_coreLetter t hwild 1) _
      · rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_conj, PWord.evalFin_gen,
          PWord.evalFin_gen]
        exact trivAct_commR (trivAct_coreLetter t hwild 1)
          (trivAct_conjR (trivAct_coreLetter t hwild 1) _)
    · cases h with
      | zero => simp only [handleTail, List.not_mem_nil] at hw
      | succ k =>
          simp only [handleTail, List.mem_cons, List.not_mem_nil, or_false] at hw
          rw [hw, handlesW]
          refine trivAct_evalFin_prodList ?_
          intro u hu
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hu
          rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
          exact trivAct_commR (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)
  rw [lSqSigmaSlipW, foxD_prodList_of_trivial _ _ _ _ _ hslip, lSqW,
    foxD_prodList_of_trivial _ _ _ _ _ (trivAct_lSq_factors t E E₂ hwild ha), lSqCore]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [foxD_comm_of_trivial (u := PWord.gen (coreLetter h 1))
      (v := .conj (.gen (coreLetter h 1)) (.gen .sigma)) _ _ _ _
      (by rw [PWord.evalFin_gen]; exact trivAct_coreLetter t hwild 1)
      (by
        rw [PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
        exact trivAct_conjR (trivAct_coreLetter t hwild 1) _),
    foxD_cBlock t E E₂ hwild]

/-- **The `q_K` pin, unramified class** — the general statement with its side condition
discharged, so it is directly consumable. -/
theorem foxD_lSqSigmaSlip_eq_lSq_unram
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqSigmaSlipW h) = foxD ⇑t a E E₂ (lSqW h) :=
  foxD_lSqSigmaSlip_eq_lSq t E E₂ hwild (trivAct_aBlock_unram t E E₂ hwild hτ) a

/-- **The `q_K` pin, ramified class.** -/
theorem foxD_lSqSigmaSlip_eq_lSq_ram
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqSigmaSlipW h) = foxD ⇑t a E E₂ (lSqW h) :=
  foxD_lSqSigmaSlip_eq_lSq t E E₂ hwild (trivAct_aBlock_ram t E E₂ hwild hTodd) a

/-- **`q_K`-insensitivity, hypothesis form**: the certified row is the same expression at every
`q`, so a tame relation `τ^σ = τ^q` among the hypotheses is *discardable*.  Contrast the tame row,
where `q` is the whole content. -/
theorem foxD_lSq_unram_of_tameRel {q : ℕ} (_hrel : conjR t.τ t.σ = t.τ ^ q)
    (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 * h + 1) → V) :
    foxD ⇑t a E E₂ (lSqW h)
      = a .tau + a (coreLetter h 0) + t.σ⁻¹ • a (coreLetter h 0) :=
  foxD_lSq_unram t E E₂ hV₂ hwild hτ a

end Rows

/-! ## The zero columns, and the `2h` handle columns in particular

A *column* of the evaluated row is its value on a single-slot offset vector `Pi.single g v`.  The
wild row has exactly two nonzero columns at every handle count, so the `2h` handle columns — the
whole `h`-dependence of the first jet — vanish identically, and so does the `x₁`-column. -/

section Columns

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 * h + 1) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

theorem handleU_ne_coreLetter (j : Fin h) (i : Fin 2) : handleU j ≠ coreLetter h i := by
  simp only [handleU, coreLetter, ne_eq, Generator.wild.injEq, Fin.mk.injEq]
  have := i.isLt
  omega

theorem handleV_ne_coreLetter (j : Fin h) (i : Fin 2) : handleV j ≠ coreLetter h i := by
  simp only [handleV, coreLetter, ne_eq, Generator.wild.injEq, Fin.mk.injEq]
  have := i.isLt
  omega

theorem handleU_ne_tau (j : Fin h) :
    handleU j ≠ (Generator.tau : Generator (2 * h + 1)) := by simp [handleU]

theorem handleV_ne_tau (j : Fin h) :
    handleV j ≠ (Generator.tau : Generator (2 * h + 1)) := by simp [handleV]

theorem coreLetter_one_ne_tau :
    coreLetter h 1 ≠ (Generator.tau : Generator (2 * h + 1)) := by simp [coreLetter]

theorem coreLetter_one_ne_zero : coreLetter h 1 ≠ coreLetter h 0 := by
  simp only [coreLetter, ne_eq, Generator.wild.injEq, Fin.mk.injEq]
  decide

/-- **Every column of the wild row other than `τ` and `x₀` is zero** (unramified class): the `σ`,
`x₁` columns and — the point — all `2h` handle columns.

This is the Lean form of the Sage-side fact that the handle block has zero first jet: hyperbolic
stabilization contributes nothing at first order, uniformly in `h`. -/
theorem foxDHom_lSq_unram_column_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    {g : Generator (2 * h + 1)} (hgτ : g ≠ .tau) (hgx : g ≠ coreLetter h 0) (v : V) :
    foxDHom ⇑t E E₂ (lSqW h) (Pi.single g v) = 0 := by
  rw [foxDHom_apply, foxD_lSq_unram t E E₂ hV₂ hwild hτ,
    Pi.single_eq_of_ne (Ne.symm hgτ), Pi.single_eq_of_ne (Ne.symm hgx)]
  simp

/-- The `2h` handle columns of the wild row are zero — the `u`-half. -/
theorem foxDHom_lSq_handleU_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (lSqW h) (Pi.single (handleU j) v) = 0 :=
  foxDHom_lSq_unram_column_eq_zero t E E₂ hV₂ hwild hτ (handleU_ne_tau j)
    (handleU_ne_coreLetter (h := h) j 0) v

/-- The `2h` handle columns of the wild row are zero — the `v`-half. -/
theorem foxDHom_lSq_handleV_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (lSqW h) (Pi.single (handleV j) v) = 0 :=
  foxDHom_lSq_unram_column_eq_zero t E E₂ hV₂ hwild hτ (handleV_ne_tau j)
    (handleV_ne_coreLetter (h := h) j 0) v

/-- **The whole square-commutator block is invisible at first order**: the `x₁`-column of the wild
row is zero.  The block `x₁²[x₁,x₁^{σ₂}]` is what gives the word its name and its rank-3 core, and
it contributes exactly nothing to the first jet — the square because `2` is even, the commutator
because both its letters act trivially. -/
theorem foxDHom_lSq_coreLetter_one_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (v : V) : foxDHom ⇑t E E₂ (lSqW h) (Pi.single (coreLetter h 1) v) = 0 :=
  foxDHom_lSq_unram_column_eq_zero t E E₂ hV₂ hwild hτ coreLetter_one_ne_tau
    coreLetter_one_ne_zero v

/-- The same, ramified class: there the row has a *single* nonzero column, so every column but
`x₀` — handles included — dies. -/
theorem foxDHom_lSq_ram_column_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    {g : Generator (2 * h + 1)} (hgx : g ≠ coreLetter h 0) (v : V) :
    foxDHom ⇑t E E₂ (lSqW h) (Pi.single g v) = 0 := by
  rw [foxDHom_apply, foxD_lSq_ram t E E₂ hV₂ hwild hτfpf hTodd,
    Pi.single_eq_of_ne (Ne.symm hgx)]
  simp

end Columns

/-! ## The core embedding and the handle-stability theorem

`coreEmbed h : Generator 1 → Generator (2h + 1)` is the degree-`1` alphabet sitting inside the
degree-`n` one: `σ ↦ σ`, `τ ↦ τ`, `x_i ↦ x_i` for `i < 2`.  Restriction along it forgets exactly
the `2h` handle coordinates, so "the certificate at degree `n` = the `n = 1` certificate ⊕ `2h`
zero columns" is the statement that the degree-`n` row **factors** through that restriction. -/

section CoreEmbed

/-- The `n = 1` alphabet inside the degree-`n` one. -/
def coreEmbed (h : ℕ) : Generator 1 → Generator (2 * h + 1)
  | .sigma => .sigma
  | .tau => .tau
  | .wild i => coreLetter h i

@[simp] theorem coreEmbed_sigma (h : ℕ) : coreEmbed h .sigma = .sigma := rfl
@[simp] theorem coreEmbed_tau (h : ℕ) : coreEmbed h .tau = .tau := rfl
@[simp] theorem coreEmbed_wild (h : ℕ) (i : Fin 2) : coreEmbed h (.wild i) = coreLetter h i := rfl

/-- At `h = 0` the embedding is the identity: the degree-`1` alphabet is its own core. -/
theorem coreEmbed_zero : coreEmbed 0 = id := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => exact congrArg Generator.wild (Fin.ext rfl)

theorem coreEmbed_injective (h : ℕ) : Function.Injective (coreEmbed h) := by
  intro g₁ g₂ hg
  cases g₁ <;> cases g₂ <;>
    simp_all [coreEmbed, coreLetter, Generator.wild.injEq, Fin.ext_iff]

/-- No handle letter is in the image of the core embedding — the `u`-half. -/
theorem coreEmbed_ne_handleU {h : ℕ} (g : Generator 1) (j : Fin h) :
    coreEmbed h g ≠ handleU j := by
  cases g with
  | sigma => simp [coreEmbed, handleU]
  | tau => simp [coreEmbed, handleU]
  | wild i => exact fun hc => handleU_ne_coreLetter j i hc.symm

/-- No handle letter is in the image of the core embedding — the `v`-half. -/
theorem coreEmbed_ne_handleV {h : ℕ} (g : Generator 1) (j : Fin h) :
    coreEmbed h g ≠ handleV j := by
  cases g with
  | sigma => simp [coreEmbed, handleV]
  | tau => simp [coreEmbed, handleV]
  | wild i => exact fun hc => handleV_ne_coreLetter j i hc.symm

variable {h : ℕ} {C : Type*}

/-- The degree-`n` marking restricted to the core letters — a genuine `n = 1` marking. -/
def coreMarking (t : Marking (2 * h + 1) C) : Marking 1 C := ⟨fun g => t (coreEmbed h g)⟩

@[simp] theorem coreMarking_apply (t : Marking (2 * h + 1) C) (g : Generator 1) :
    coreMarking t g = t (coreEmbed h g) := rfl

@[simp] theorem coreMarking_σ (t : Marking (2 * h + 1) C) : (coreMarking t).σ = t.σ := rfl
@[simp] theorem coreMarking_τ (t : Marking (2 * h + 1) C) : (coreMarking t).τ = t.τ := rfl

@[simp] theorem coreMarking_x (t : Marking (2 * h + 1) C) (i : Fin 2) :
    (coreMarking t).x i = t (coreLetter h i) := rfl

/-- Restriction of an offset vector along the core embedding — the map that forgets exactly the
`2h` handle coordinates. -/
def coreRestrict (h : ℕ) (V : Type*) [AddCommGroup V] :
    ((Generator (2 * h + 1) → V) →+ (Generator 1 → V)) :=
  AddMonoidHom.mk' (fun a => a ∘ coreEmbed h) fun _ _ => rfl

@[simp] theorem coreRestrict_apply {V : Type*} [AddCommGroup V]
    (a : Generator (2 * h + 1) → V) (g : Generator 1) :
    coreRestrict h V a g = a (coreEmbed h g) := rfl

end CoreEmbed

section Stability

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 * h + 1) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite V] in
/-- The core marking inherits the wild-triviality hypothesis. -/
theorem coreMarking_hwild (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (i : Fin (1 + 1)) (v : V) : (coreMarking t).x i • v = v := by
  rw [coreMarking_x]
  exact hwild _ v

/-- **THE HANDLE-STABILITY THEOREM, unramified class** (board WL-b: "`n = 1` base + handle
stability").

The evaluated Fox row of `R^{sq}_{L,n}` at degree `n = 2h + 1` **factors** through restriction to
the `n = 1` core alphabet:

```
foxDHom t (lSqW h) = (foxDHom (coreMarking t) (lSqW 0)) ∘ coreRestrict h.
```

Since `coreRestrict h` forgets exactly the `2h` handle coordinates, this is precisely *"the
certificate at degree `n` is the `n = 1` certificate ⊕ `2h` zero columns"* — as an equation of
`AddMonoidHom`s rather than a remark.  Note it is an equation between the row at `h` handles and
the row at **zero** handles, so nothing about the handle block is used beyond its vanishing. -/
theorem foxDHom_lSq_eq_base_comp_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v) :
    foxDHom ⇑t E E₂ (lSqW h)
      = (foxDHom ⇑(coreMarking t) E E₂ (lSqW 0)).comp (coreRestrict h V) := by
  refine AddMonoidHom.ext fun a => ?_
  rw [AddMonoidHom.comp_apply, foxDHom_apply, foxDHom_apply,
    foxD_lSq_unram t E E₂ hV₂ hwild hτ,
    foxD_lSq_unram (h := 0) (coreMarking t) E E₂ hV₂ (coreMarking_hwild t hwild) hτ]
  rfl

/-- **THE HANDLE-STABILITY THEOREM, ramified class.**  Same factorization, `P ↦ 0`. -/
theorem foxDHom_lSq_eq_base_comp_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    foxDHom ⇑t E E₂ (lSqW h)
      = (foxDHom ⇑(coreMarking t) E E₂ (lSqW 0)).comp (coreRestrict h V) := by
  refine AddMonoidHom.ext fun a => ?_
  rw [AddMonoidHom.comp_apply, foxDHom_apply, foxDHom_apply,
    foxD_lSq_ram t E E₂ hV₂ hwild hτfpf hTodd,
    foxD_lSq_ram (h := 0) (coreMarking t) E E₂ hV₂ (coreMarking_hwild t hwild) hτfpf hTodd]
  rfl

/-- **Handle stability, offset-splitting form**: an offset vector supported on the handle letters
is annihilated outright.  Together with `foxDHom_lSq_eq_base_comp_unram` this is the "⊕ `2h` zero
columns" clause read on each column separately. -/
theorem foxDHom_lSq_handle_supported_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 * h + 1) → V) (hsupp : ∀ g : Generator 1, a (coreEmbed h g) = 0) :
    foxDHom ⇑t E E₂ (lSqW h) a = 0 := by
  rw [foxDHom_lSq_eq_base_comp_unram t E E₂ hV₂ hwild hτ, AddMonoidHom.comp_apply,
    foxDHom_apply, foxD_lSq_unram (h := 0) (coreMarking t) E E₂ hV₂
      (coreMarking_hwild t hwild) hτ]
  rw [show coreRestrict h V a (.tau : Generator 1) = a (coreEmbed h .tau) from rfl,
    show coreRestrict h V a (coreLetter 0 0) = a (coreEmbed h (coreLetter 0 0)) from rfl,
    hsupp .tau, hsupp (coreLetter 0 0)]
  simp

end Stability

/-! ## The formal row and its degree-independence

The certificate data — a pure `FoxCoeff` expression per column, the same at every module of a
class.  This is the Lean twin of the frozen certificate's `fox_certificate.rows`. -/

/-- The **universal `L_sq` wild row** `(0, P, S⁻¹ + P, 0, 0…)` — one piece of formal data,
certified below at *both* interpretations (`P ↦ 1` split/unramified, `P ↦ 0` ramified).

Up to the column relabelling `x₂ ↦ x₀` this is literally `Certificates.nCompactWildRow`: both
branch families produce the same universal first-order row. -/
def lSqWildRow (h : ℕ) : FoxRowNormalForm (Generator (2 * h + 1)) (TameSym (2 * h + 1)) :=
  ⟨fun g => match g with
    | .sigma => .zero
    | .tau => .atom .proj
    | .wild i => if (i : ℕ) = 0 then .add (.atom (.gen .sigma (-1))) (.atom .proj) else .zero⟩

/-- The `x₀`-slot of the `L_sq` alphabet. -/
def x0Idx (h : ℕ) : Fin (2 * h + 1 + 1) := ⟨0, by omega⟩

theorem coreLetter_zero (h : ℕ) : coreLetter h 0 = Generator.wild (x0Idx h) := rfl

theorem tau_ne_coreLetter_zero (h : ℕ) :
    (Generator.tau : Generator (2 * h + 1)) ≠ coreLetter h 0 := by
  rw [coreLetter_zero]; simp

theorem sigma_ne_coreLetter_zero (h : ℕ) :
    (Generator.sigma : Generator (2 * h + 1)) ≠ coreLetter h 0 := by
  rw [coreLetter_zero]; simp

section FormalRow

variable {h : ℕ}

@[simp] theorem lSqWildRow_sigma : (lSqWildRow h).row .sigma = .zero := rfl

@[simp] theorem lSqWildRow_tau : (lSqWildRow h).row .tau = .atom .proj := rfl

@[simp] theorem lSqWildRow_x0 :
    (lSqWildRow h).row (.wild (x0Idx h)) = .add (.atom (.gen .sigma (-1))) (.atom .proj) := rfl

/-- **Every wild slot but `x₀` is zero** — the `x₁`-slot and all `2h` handle slots at once. -/
theorem lSqWildRow_wild_ne {j : Fin (2 * h + 1 + 1)} (hj : (j : ℕ) ≠ 0) :
    (lSqWildRow h).row (.wild j) = .zero := if_neg hj

/-- **Handle stability, formal-data form (`u`-half)**: the `2h` handle entries of the formal row
are `.zero`, at every `h`. -/
theorem lSqWildRow_handleU_eq_zero (j : Fin h) : (lSqWildRow h).row (handleU j) = .zero :=
  lSqWildRow_wild_ne (by simp)

/-- **Handle stability, formal-data form (`v`-half)**. -/
theorem lSqWildRow_handleV_eq_zero (j : Fin h) : (lSqWildRow h).row (handleV j) = .zero :=
  lSqWildRow_wild_ne (by simp)

/-- The `x₁` entry of the formal row is zero: the square-commutator block leaves no first-order
trace. -/
theorem lSqWildRow_coreLetter_one_eq_zero : (lSqWildRow h).row (coreLetter h 1) = .zero :=
  lSqWildRow_wild_ne (by simp)

end FormalRow

/-! ### Relabelling the coefficient alphabet

To say "the degree-`n` formal row *is* the `n = 1` formal row" one needs the two rows' coefficient
alphabets identified, since `TameSym (2h+1) ≠ TameSym 1`.  `coreSym h` is the relabelling induced
by `coreEmbed h`, `mapSym` its functorial lift, and `eval_mapSym` the compatibility that makes
the identification denotationally sound. -/

/-- Functorial relabelling of a formal coefficient along a map of atom alphabets.

**Hoist candidate**: this and `eval_mapSym` are branch-independent and belong in
`GQ2/Dyadic/Word/FoxCert.lean` as `FoxCoeff.map`/`FoxCoeff.eval_map`, next to `FoxCoeff.eval`.
They are named `mapSym`/`eval_mapSym` here precisely so that such a hoist cannot collide with
them. -/
def mapSym {S S' : Type*} (f : S → S') : FoxCoeff S → FoxCoeff S'
  | .zero => .zero
  | .one => .one
  | .atom s => .atom (f s)
  | .add p q => .add (mapSym f p) (mapSym f q)
  | .comp p q => .comp (mapSym f p) (mapSym f q)
  | .neg p => .neg (mapSym f p)

/-- Relabelling is denotationally transparent: evaluating the relabelled coefficient is
evaluating the original under the precomposed interpretation. -/
theorem eval_mapSym {S S' : Type*} {A : Type*} [AddCommGroup A] (f : S → S')
    (ρ : S' → AddMonoid.End A) : ∀ p : FoxCoeff S,
    (mapSym f p).eval ρ = p.eval (ρ ∘ f)
  | .zero => rfl
  | .one => rfl
  | .atom _ => rfl
  | .add p q => by rw [mapSym, FoxCoeff.eval_add, FoxCoeff.eval_add, eval_mapSym f ρ p,
      eval_mapSym f ρ q]
  | .comp p q => by rw [mapSym, FoxCoeff.eval_comp, FoxCoeff.eval_comp, eval_mapSym f ρ p,
      eval_mapSym f ρ q]
  | .neg p => by rw [mapSym, FoxCoeff.eval_neg, FoxCoeff.eval_neg, eval_mapSym f ρ p]

/-- The atom relabelling induced by the core embedding: marked-letter atoms move along
`coreEmbed h`, the `σ₂`-atoms and the opaque projector are untouched. -/
def coreSym (h : ℕ) : TameSym 1 → TameSym (2 * h + 1)
  | .gen g k => .gen (coreEmbed h g) k
  | .sigma2 k => .sigma2 k
  | .proj => .proj

/-- **The interpretation is natural for the relabelling**: reading a degree-`1` atom through
`coreSym h` at the degree-`n` marking `t` is reading it directly at the core marking of `t`.  All
three constructors are definitional. -/
theorem toEnd_comp_coreSym {h : ℕ} {C : Type*} [Group C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] (t : Marking (2 * h + 1) C) (π : AddMonoid.End V) :
    TameSym.toEnd t π ∘ coreSym h = TameSym.toEnd (coreMarking t) π := by
  funext s
  cases s with
  | gen g k => rfl
  | sigma2 k => rfl
  | proj => rfl

/-- **HANDLE STABILITY, FORMAL-DATA FORM**: the degree-`n` formal row, read on the core letters,
*is* the `n = 1` formal row — relabelled along `coreSym h` and nothing more.  With
`lSqWildRow_handleU_eq_zero`/`_handleV_eq_zero` (all handle entries `.zero`) this is the formal
twin of `foxDHom_lSq_eq_base_comp_unram`: **the degree-`n` certificate data = the `n = 1`
certificate data ⊕ `2h` zero columns.** -/
theorem lSqWildRow_row_coreEmbed (h : ℕ) (g : Generator 1) :
    (lSqWildRow h).row (coreEmbed h g) = mapSym (coreSym h) ((lSqWildRow 0).row g) := by
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl

/-- The formal-row handle stability, evaluated: the two `toHom`s agree after restriction. -/
theorem lSqWildRow_toHom_comp_coreRestrict {h : ℕ} {C : Type*} [Group C] {V : Type*}
    [AddCommGroup V] [DistribMulAction C V] (t : Marking (2 * h + 1) C) (π : AddMonoid.End V)
    (a : Generator (2 * h + 1) → V) :
    (lSqWildRow h).toHom (TameSym.toEnd t π) a
      = (lSqWildRow 0).toHom (TameSym.toEnd (coreMarking t) π) (coreRestrict h V a) := by
  rw [FoxRowNormalForm.toHom_apply, FoxRowNormalForm.toHom_apply,
    sum_generator_pair _ (x0Idx h) rfl fun j hj => by
      rw [lSqWildRow_wild_ne (h := h) fun hjv => hj (Fin.ext hjv)]
      rfl,
    sum_generator_pair _ (x0Idx 0) rfl fun j hj => by
      rw [lSqWildRow_wild_ne (h := 0) fun hjv => hj (Fin.ext hjv)]
      rfl]
  rw [lSqWildRow_tau, lSqWildRow_tau, lSqWildRow_x0, lSqWildRow_x0]
  simp only [FoxCoeff.eval_add_apply, FoxCoeff.eval_atom_apply, TameSym.toEnd_proj,
    TameSym.toEnd_gen_apply, Marking.apply_sigma, coreMarking_σ]
  rfl

/-! ## The published-row certificates

WW2's `FoxRowCertificate` shape at degree `n`: one formal row `lSqWildRow` certified at both
interpretations (empty ops), plus the one-op normal form and the scalar degeneration.  This is the
Lean form of the Sage certificate's "one universal row + per-branch specializations". -/

section RowDenote

variable {h : ℕ} {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  (t : Marking (2 * h + 1) C) (π : AddMonoid.End V)

/-- **The universal wild row's denotation**: `P·a(τ) + (S⁻¹ + P)·a(x₀)`. -/
theorem lSqWildRow_toHom_apply (a : Generator (2 * h + 1) → V) :
    (lSqWildRow h).toHom (TameSym.toEnd t π) a
      = π (a .tau) + (t.σ⁻¹ • a (coreLetter h 0) + π (a (coreLetter h 0))) := by
  rw [FoxRowNormalForm.toHom_apply,
    sum_generator_pair _ (x0Idx h) rfl fun j hj => by
      rw [lSqWildRow_wild_ne (h := h) fun hjv => hj (Fin.ext hjv)]
      rfl]
  rw [lSqWildRow_tau, lSqWildRow_x0, FoxCoeff.eval_add_apply, FoxCoeff.eval_atom_apply,
    FoxCoeff.eval_atom_apply, FoxCoeff.eval_atom_apply, TameSym.toEnd_proj,
    TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_neg, zpow_one, ← coreLetter_zero]

end RowDenote

/-- The formal coefficient `1 + S⁻¹` of the published row — WW2's `oneAddSInv` at the degree-`n`
alphabet. -/
def oneAddSInvL (h : ℕ) : FoxCoeff (TameSym (2 * h + 1)) :=
  .add .one (.atom (.gen .sigma (-1)))

/-- **The one column operation of the pivot normal form**: `c_{x₀} ↦ c_{x₀} + c_τ ∘ (−(1 + S⁻¹))`,
the elementary transvection clearing the `x₀`-column against the `τ`-pivot.  This is WW2's
`gammaRPivotOps` at the degree-`n` alphabet — the same op, the same column. -/
def lSqPivotOps (h : ℕ) : List (FoxColOp (Generator (2 * h + 1)) (TameSym (2 * h + 1))) :=
  [.transvect .tau (coreLetter h 0) (.neg (oneAddSInvL h))]

section Certificates

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 * h + 1) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The published `L_sq` wild row at every unramified simple tame module**: empty ops, target
the universal row `(0, P, S⁻¹ + P, 0, 0…)` read with `P ↦ 1`. -/
noncomputable def lSqWildRowCertUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v) :
    FoxRowCertificate (TameSym.splitEnd (A := V) t) (foxDHom ⇑t E E₂ (lSqW h)) where
  colOps := []
  target := lSqWildRow h
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_lSq_unram t E E₂ hV₂ hwild hτ,
      TameSym.splitEnd, lSqWildRow_toHom_apply]
    show a .tau + a (coreLetter h 0) + t.σ⁻¹ • a (coreLetter h 0)
        = a .tau + (t.σ⁻¹ • a (coreLetter h 0) + a (coreLetter h 0))
    abel

/-- **The published `L_sq` wild row at every ramified simple tame module**: the *same* formal row
read with `P ↦ 0`, i.e. `(0, 0, S⁻¹, 0, 0…)` — a single unit entry. -/
noncomputable def lSqWildRowCertRam (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    FoxRowCertificate (TameSym.ramifiedEnd (A := V) t) (foxDHom ⇑t E E₂ (lSqW h)) where
  colOps := []
  target := lSqWildRow h
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_lSq_ram t E E₂ hV₂ hwild hτfpf hTodd,
      TameSym.ramifiedEnd, lSqWildRow_toHom_apply]
    show t.σ⁻¹ • a (coreLetter h 0)
        = (0 : V) + (t.σ⁻¹ • a (coreLetter h 0) + (0 : V))
    rw [zero_add, add_zero]

/-- **The split (scalar) module certificate**: with `S = 1` the `1 + S⁻¹` block vanishes and the
row *is already* the standard `τ`-pivot — zero operations, target `FoxRowNormalForm.single τ`. -/
noncomputable def lSqWildRowCertSplit (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) :
    FoxRowCertificate (TameSym.splitEnd (A := V) t) (foxDHom ⇑t E E₂ (lSqW h)) where
  colOps := []
  target := .single .tau
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_lSq_split t E E₂ hV₂ hwild hτ hσ,
      FoxRowNormalForm.single_toHom_apply]

/-- **The one-op normal form** — the ticket's certification headline at degree `n`.

A single column transvection (`lSqPivotOps`; WW2's `gammaRPivotOps` at this alphabet) clears the
`x₀`-column against the `τ`-pivot and carries the evaluated row to the standard pivot row
`(0, 1, 0, 0, 0…)`.  Invertibility is the slot-distinctness `τ ≠ x₀`; replay is the `rfl`-level
`foxRowApplyOps` step plus the row identity, and the ops algebra closes by `abel` with no
characteristic assumption beyond the one already in the row. -/
noncomputable def lSqWildRowPivotCert (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v) :
    FoxRowCertificate (TameSym.splitEnd (A := V) t) (foxDHom ⇑t E E₂ (lSqW h)) where
  colOps := lSqPivotOps h
  target := .single .tau
  colOps_invertible := by
    intro c hc
    rw [lSqPivotOps, List.mem_singleton] at hc
    subst hc
    exact tau_ne_coreLetter_zero h
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_apply, foxDHom_apply, lSqPivotOps, FoxColOp.listHom_cons,
      FoxColOp.listHom_nil, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      foxD_lSq_unram t E E₂ hV₂ hwild hτ, FoxRowNormalForm.single_toHom_apply]
    simp only [FoxColOp.toHom_transvect_apply, reduceIte, oneAddSInvL, FoxCoeff.eval_neg_apply,
      FoxCoeff.eval_add_apply, FoxCoeff.eval_one_apply, FoxCoeff.eval_atom_apply,
      TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_neg, zpow_one,
      if_neg (Ne.symm (tau_ne_coreLetter_zero h))]
    abel_nf

end Certificates

/-! ## The `n = 1` base: transport onto WW2's `Γ_R` certificates

Per the frozen selection (`selection-freeze.md` row 1, SQ1) the `n = 1` word *is* Roe's `Γ_R`
relator, and WW1/WW2 already certified that row.  Nothing below re-derives it: the single content
is that the two Fox **carriers** coincide, after which WW2's certificate data and proofs are
reused verbatim. -/

section BaseTransport

/-- **WL-a's `n = 1` identification, universe-generalized.**

⚠ `Words.evalFin_lSqW_zero` is stated at `{P : Type}` — universe `0` — while the lift group
`WordLift V C` of the Fox evaluator lives in `Type (max u v)`, so the transport below cannot cite
it directly.  Nothing in the statement is `Type`-specific, so this is WL-a's lemma with `Type`
relaxed to `Type*`, carrying **WL-a's proof verbatim**; it is a universe fix, not a second
derivation, and `evalFin_lSqW_zero'_eq` pins that the two agree where both apply.

**Dedup ticket**: relax `{P : Type}` to `{P : Type*}` in `GQ2/Dyadic/Words/L.lean`
(`evalFin_lSqW_zero`, and check its neighbours `evalFin_lSqW_zero_eq_wildValueR` and
`eval_lSqW_zero_eq_one_iff`), after which this twin deletes and its consumers cite WL-a. -/
theorem evalFin_lSqW_zero' {P : Type*} [Group P] (s : _root_.GQ2.Marking P) (E : Zhat → ℤ)
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

/-- Sanity pin: at universe `0`, where both apply, the twin above **is** WL-a's lemma. -/
theorem evalFin_lSqW_zero'_eq {P : Type} [Group P] (s : _root_.GQ2.Marking P) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    evalFin_lSqW_zero' s E E₂ = Words.LSq.evalFin_lSqW_zero s E E₂ := rfl

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V]

omit [Finite C] [Finite V] in
/-- **The `n = 1` transport, evaluator level.**  WL-a's `evalFin_lSqW_zero` applied at the
*lifted* marking — legitimate because `foxLift_ofQ2` says the lifted `n = 1` marking is again an
`ofQ2` marking (of the ℚ₂ development's `FoxH.liftMarking`), so the `ℚ₂`-shaped identification
applies verbatim in the lift group `V ⋊ C`.

The two trees are genuinely different (`x₀^{-3}` and an `n`-ary `Multiply` against the ledger's
`(x₀³)⁻¹` and left association); the whole gap is WL-a's two `zpow` realignments plus
associativity, and it stays inside `evalFin_lSqW_zero`. -/
theorem foxEval_lSqW_zero (t : _root_.GQ2.Marking C) (x : Fin 4 → V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    foxEval (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ (lSqW 0)
      = foxEval (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaRWildWord := by
  rw [foxEval_def, foxEval_def, foxLift_ofQ2, evalFin_lSqW_zero']

omit [Finite C] [Finite V] in
/-- The `n = 1` transport, derivative level, at `q2Offsets`-shaped offsets. -/
theorem foxD_lSqW_zero (t : _root_.GQ2.Marking C) (x : Fin 4 → V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    foxD (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ (lSqW 0)
      = foxD (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaRWildWord :=
  congrArg WordLift.u (foxEval_lSqW_zero t x E E₂)

omit [Finite C] [Finite V] in
/-- The `n = 1` transport at arbitrary offsets. -/
theorem foxD_lSqW_zero_apply (t : _root_.GQ2.Marking C) (a : Generator 1 → V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    foxD (⇑(Marking.ofQ2 t)) a E E₂ (lSqW 0)
      = foxD (⇑(Marking.ofQ2 t)) a E E₂ gammaRWildWord := by
  have hx := foxD_lSqW_zero t (q2OffsetsInv a) E E₂
  rwa [q2Offsets_q2OffsetsInv] at hx

/-- **THE `n = 1` BASE, certificate carrier level**: the Fox row of the frozen `L_sq` word at
`n = 1` and the Fox row of WW1's `Γ_R` tree are **the same `AddMonoidHom`**.

This is what makes the base case a *transport* and not a re-derivation: every WW2 certificate for
`gammaRWildWord` becomes a certificate for `lSqW 0` by rewriting along this equation, with its
`target`, its `colOps` and its `verifies` proof reused unchanged. -/
theorem foxDHom_lSqW_zero (t : _root_.GQ2.Marking C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    foxDHom (⇑(Marking.ofQ2 t)) E E₂ (lSqW 0)
      = foxDHom (A := V) (⇑(Marking.ofQ2 t)) E E₂ gammaRWildWord :=
  AddMonoidHom.ext fun a => foxD_lSqW_zero_apply t a E E₂

/-- **Instance pin, `n = 1` / `q_K = 2` (the `ℚ₂` base): the published-row certificate**, obtained
from WW2's `gammaRWildRowCert` with `target = gammaRSplitRow` — the frozen row `(0, 1, 1 + S⁻¹, 0)`
in the packet's column order `σ, τ, x₀, x₁` — **reused verbatim**. -/
noncomputable def lSqWildRowCertQ2Unram (t : _root_.GQ2.Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    FoxRowCertificate (TameSym.splitEnd (A := V) (Marking.ofQ2 t))
      (foxDHom (⇑(Marking.ofQ2 t)) E E₂ (lSqW 0)) where
  colOps := []
  target := gammaRSplitRow
  colOps_invertible := by simp
  verifies := by
    rw [foxDHom_lSqW_zero]
    exact (gammaRWildRowCert t hV₂ hx0 hx1 htau E E₂).verifies

/-- **Instance pin, `n = 1` / `q_K = 2`: the pivot certificate**, from WW2's
`gammaRWildRowPivotCert` — one column transvection to the standard `τ`-pivot row. -/
noncomputable def lSqWildRowCertQ2Pivot (t : _root_.GQ2.Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    FoxRowCertificate (TameSym.splitEnd (A := V) (Marking.ofQ2 t))
      (foxDHom (⇑(Marking.ofQ2 t)) E E₂ (lSqW 0)) where
  colOps := gammaRPivotOps
  target := .single .tau
  colOps_invertible := (gammaRWildRowPivotCert (V := V) t hV₂ hx0 hx1 htau E E₂).colOps_invertible
  verifies := by
    rw [foxDHom_lSqW_zero]
    exact (gammaRWildRowPivotCert t hV₂ hx0 hx1 htau E E₂).verifies

/-- **Instance pin, `n = 1` / `q_K = 2`: the ramified twin**, from WW2's
`gammaRWildRowRamifiedCert` — target `(0, 0, S⁻¹, 0)` under `P ↦ 0`. -/
noncomputable def lSqWildRowCertQ2Ram (t : _root_.GQ2.Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    FoxRowCertificate (TameSym.ramifiedEnd (A := V) (Marking.ofQ2 t))
      (foxDHom (⇑(Marking.ofQ2 t)) E E₂ (lSqW 0)) where
  colOps := []
  target := gammaRRamifiedRow
  colOps_invertible := by simp
  verifies := by
    rw [foxDHom_lSqW_zero]
    exact (gammaRWildRowRamifiedCert t hV₂ hx0 hx1 htau hTodd E E₂).verifies

/-- **The two `n = 1` routes agree.**  The degree-generic row of this file, specialized to `h = 0`
at an `ofQ2` marking, is WW1's hand row for `Γ_R` — so the transported certificates above and the
`h = 0` instances of the degree-`n` certificates certify the *same* row.  This is the ticket's
regression: the generic derivation and the ℚ₂ hand derivation meet. -/
theorem foxD_lSq_unram_zero_eq_hand (t : _root_.GQ2.Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (a : Generator 1 → V) :
    foxD (⇑(Marking.ofQ2 t)) a E E₂ (lSqW 0)
      = a .tau + a (.wild 0) + t.σ⁻¹ • a (.wild 0) := by
  rw [foxD_lSqW_zero_apply t a E E₂]
  exact foxD_gammaRWildWord_split_apply t hV₂ hx0 hx1 htau E E₂ a

end BaseTransport

end GQ2.Dyadic.Certificates.LSq
