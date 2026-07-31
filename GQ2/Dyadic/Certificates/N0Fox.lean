/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Words.N0
import GQ2.Dyadic.Word.FoxCert

/-!
# Dyadic campaign, ticket WN0-b: the Fox certificate of the compact `N_α` branch word

The certificate layer of the pilot lane, sitting on WN0-a's word (`GQ2/Dyadic/Words/N0.lean`),
WW1's Fox evaluator (`GQ2/Dyadic/Word/Fox.lean`) and WW2's certificate grammar
(`GQ2/Dyadic/Word/FoxCert.lean`).  It carries packet Def. 9.1 items (3)–(4) for row 2 of the
R5 selection freeze,

```
R_{N,α,0} = x₀^{2+2^α} [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂} · H_h,      p_α = 2 + 2^α,
```

together with the tame relator `τ^σ (τ^q)⁻¹` of `T_q`, as the **evaluated two-relator Jacobian**
`d¹_{R,ρ} : (Generator (2+2h) → V) →+ V × V` in the packet's column order `σ, τ, x₀, x₁, x₂, …`.

## The rows

The universal first-order rows, in the notation `S = σ`, `T = τ`, `P` = the `ω₂`-norm projector
(WW2's opaque atom `TameSym.proj`):

| relator | `σ` | `τ` | `x₀` | `x₁` | `x₂` | handles |
|---|---|---|---|---|---|---|
| tame `τ^σ(τ^q)⁻¹` | `S⁻¹(T−1)` | `S⁻¹ − (1+T+⋯+T^{q−1})` | `0` | `0` | `0` | `0` |
| wild `R_{N,α,0}` | `0` | `P` | `0` | `0` | `S⁻¹ + P` | `0` |

and the three module classes, obtained by *assigning* `P` (never computing it — the binding
`ω₂`-discipline of WW2):

| class | `P` | tame row | wild row |
|---|---|---|---|
| unramified (`T = 1`, `S` free) | `1` | `(0, S⁻¹, 0, 0, 0)` | `(0, 1, 0, 0, 1 − S⁻¹)` |
| split/scalar (`T = 1`, `S = 1`) | `1` | `(0, 1, 0, 0, 0)` | `(0, 1, 0, 0, 0)` |
| ramified (`V^T = 0`) | `0` | `(S⁻¹(T−1), S⁻¹−1−T, 0, 0, 0)` | `(0, 0, 0, 0, −S⁻¹)` |

**The `1 − S⁻¹` block is the point** (packet §14, board WN0-b): it is produced by the conjugated
letter `x₂^{-σ}` — and by nothing else — and `isUnit_oneSubSInvEnd_iff` proves it is invertible
on `V` **exactly when `V^S = 0`**, hence on every nontrivial simple unramified module and on no
scalar module.  That dichotomy is why the wild relator splits `x₂` off outright in the
unramified branch while the split/scalar module sees only the `τ`-column.

## The certificates (the freeze's "one-op normal forms both branches")

Both branch normal forms are reached by a **single** elementary operation, and each carries its
own invertibility witness — the Lean twins of the two operations recorded in the frozen
certificates `N-compact-alpha{2,3,4}-h{0,1}-v001`:

* **unramified**: one *row* operation, `FoxRowOp.addSnd S` (Sage `AddRow(wild += S·tame)`),
  clearing the wild row's `τ`-entry against the tame pivot and leaving the **diagonal**
  `(τ ↦ S⁻¹ ; x₂ ↦ 1 − S⁻¹)` — `nCompactJacobianCertUnram`;
* **ramified**: one *column* operation, `FoxColOp.scale x₂ S S⁻¹` (Sage `ScaleCol(x₂ *= S)`),
  turning the single unit entry `−S⁻¹` into `1` — `nCompactJacobianCertRam`.  Here the carried
  formal inverse is the whole content: `S` is invertible outright, no simplicity needed.

Alongside them the **published-row certificates** (empty ops) pin the rows themselves at each
class, in WW2's `FoxRowCertificate` shape, and `nCompactWildRow` is *one* piece of formal data
— the universal row with the opaque `P` — certified at *both* interpretations
(`TameSym.splitEnd`, `TameSym.ramifiedEnd`).  That is the Lean form of the Sage certificate's
"one row + per-branch specializations" structure.

## Where each entry comes from (packet §9.2's proof shape, mechanised)

* `D(x₀^{p_α}) = p_α · a(x₀) = 0` — **`p_α` is even**, and that is the whole of the leading
  power's first-order content (`foxD_leadingPow`).  This is where `α ≥ 1` enters, and *only*
  `α ≥ 1`: the branch condition `α ≥ 2` is a **Hessian** (second-order) condition, invisible to
  this file.  The parity is read off WN0-a's spelling-discipline lemma `two_add_two_pow`
  (`2 + 2^α = 2(1 + 2^{α−1})`) — the exact device the Sage side needs for symbolic `α`, where
  the displayed spelling `2 + 2^α` leaves an opaque atom whose parity is undecided.
* `D([x₀,x₁]) = 0`, and `D(H_h) = 0` — commutators of trivially-acting letters
  (`foxD_comm_of_trivial`).  The `2h` handle columns are therefore identically zero
  (`foxDHom_nCompact_handle_column`), at every `h`, which is "hyperbolic stabilization at first
  order".
* `D((x₂^σ)⁻¹) = −S⁻¹ · a(x₂)` — the `σ`-contributions of `σ⁻¹x₂σ` cancel in pairs and the
  conjugator survives as `S⁻¹` (`foxD_invConjX2`).  **This is the `−S⁻¹` of the `x₂`-column.**
* `D((x₂τ)^{ω₂}) = P · (a(x₂) + a(τ))` — the lift-level `ω₂` rule.  `P` is never computed: the
  two class collapses are WW1's engine lemmas `WordLift.powOmega2_u_of_trivial` (`P = 1`) and
  `WordLift.powOmega2_u_of_oddFixedPointFree` (`P = 0`), and `powOmega2` is **never unfolded**
  in an offset computation anywhere below.

## Implementation notes

**Not `module`-style, and forced**: `GQ2.Dyadic.Words.N0` is not `module`-style (it imports F3's
`TameBoundary`), and a `module` file may not import a non-`module` one — the WN0-a ruling that
`Words/` and `Certificates/` are plain-import layers.  The other import,
`GQ2.Dyadic.Word.FoxCert`, is `module`-style, which is fine in this direction.

Three small generic lemmas about `foxD` live here rather than in `Fox.lean`
(`foxD_prodList_of_trivial`, `foxD_comm_of_trivial`, and the `trivAct` subgroup): they are
needed by every wave-2 branch lane, and a hoist into `GQ2/Dyadic/Word/Fox.lean` is a mechanical
follow-up for the orchestrator — see the dedup notes on each.
-/

namespace GQ2.Dyadic.Certificates

open GQ2.FoxH GQ2.Dyadic.Words

/-! ## The trivially-acting subgroup

Every hypothesis of a "simple tame module" class says that some marked letter acts trivially on
the coefficient module, and every step of a row computation needs that property to *propagate*
through the word constructors.  Packaging "acts trivially" as membership in the kernel of the
permutation representation makes the propagation free: products, inverses, powers and
conjugates are subgroup operations.

**Dedup note.** This subgroup and the two `foxD` lemmas below are lane-generic; a hoist into
`GQ2/Dyadic/Word/Fox.lean` is mechanical.  They are stated here because WN0 is the pilot and
`Fox.lean` is closed. -/

section TrivAct

variable (C : Type*) [Group C] (V : Type*) [AddCommGroup V] [DistribMulAction C V]

/-- **The elements of `C` acting trivially on `V`**: the kernel of the permutation
representation, so a genuine subgroup (and normal). -/
def trivAct : Subgroup C := MonoidHom.ker (MulAction.toPermHom C V)

variable {C V}

theorem mem_trivAct {g : C} : g ∈ trivAct C V ↔ ∀ v : V, g • v = v := by
  constructor
  · intro hg v
    have h := MonoidHom.mem_ker.mp hg
    simpa using congrArg (fun e : Equiv.Perm V => e v) h
  · intro hg
    exact MonoidHom.mem_ker.mpr (Equiv.ext fun v => by simpa using hg v)

/-- A conjugate of a trivially-acting element acts trivially, **for any conjugator** — the
normality of the kernel, in the `conjR` spelling the word syntax uses. -/
theorem trivAct_conjR {x : C} (hx : x ∈ trivAct C V) (g : C) : conjR x g ∈ trivAct C V := by
  rw [mem_trivAct] at hx ⊢
  intro v
  rw [conjR, mul_smul, mul_smul, hx, inv_smul_smul]

/-- A commutator of two trivially-acting elements acts trivially. -/
theorem trivAct_commR {x y : C} (hx : x ∈ trivAct C V) (hy : y ∈ trivAct C V) :
    commR x y ∈ trivAct C V := by
  rw [commR]
  exact mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) hy

/-- The `2`-primary part of a trivially-acting element acts trivially: `powOmega2` is a natural
number power (`GQ2.powOmega2`), so this is `Subgroup.pow_mem`.

This is the *base-group* twin of the engine lemma `WordLift.powOmega2_g_smul_of_trivial`, whose
proof is the same one line.  It touches only the `.g`-coordinate: **no offset (`.u`) computation
in this file unfolds `powOmega2`** — those all route through WW1's engine lemmas, per the
binding `ω₂`-discipline. -/
theorem trivAct_powOmega2 {x : C} (hx : x ∈ trivAct C V) : powOmega2 x ∈ trivAct C V := by
  rw [powOmega2]
  exact pow_mem hx _

end TrivAct

/-! ## Generic Fox lemmas: products and commutators over trivially-acting letters -/

section FoxHelpers

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- `evalFin` of an `n`-ary product is the product of the `evalFin`s — the `evalFin` twin of
`PWord.eval_prodList`. -/
theorem evalFin_prodList (μ : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    ∀ l : List (PWord X),
      PWord.evalFin μ E E₂ (PWord.prodList l) = (l.map (PWord.evalFin μ E E₂)).prod
  | [] => rfl
  | w :: ws => by
      rw [PWord.prodList_cons, PWord.evalFin_mul, evalFin_prodList μ E E₂ ws, List.map_cons,
        List.prod_cons]

/-- An `n`-ary product of trivially-evaluating words evaluates trivially. -/
theorem trivAct_evalFin_prodList {μ : X → C} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    {l : List (PWord X)} (hl : ∀ w ∈ l, PWord.evalFin μ E E₂ w ∈ trivAct C A) :
    PWord.evalFin μ E E₂ (PWord.prodList l) ∈ trivAct C A := by
  rw [evalFin_prodList]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact hl w hw

variable [Finite A] [Finite C] (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The Fox derivative of an `n`-ary product of trivially-evaluating factors is the plain sum
of the factors' derivatives**: each prefix acts trivially, so every `ū·` in the Fox product rule
`D(uv) = D(u) + ū·D(v)` disappears.  The workhorse of every branch-word row computation. -/
theorem foxD_prodList_of_trivial : ∀ (l : List (PWord X)),
    (∀ w ∈ l, PWord.evalFin t E E₂ w ∈ trivAct C A) →
      foxD t a E E₂ (PWord.prodList l) = (l.map (foxD t a E E₂)).sum
  | [], _ => rfl
  | w :: ws, hl => by
      rw [PWord.prodList_cons, foxD_mul,
        foxD_prodList_of_trivial ws fun u hu => hl u (List.mem_cons_of_mem _ hu),
        mem_trivAct.mp (hl w List.mem_cons_self), List.map_cons, List.sum_cons]

/-- **The Fox derivative of a commutator of two trivially-evaluating words vanishes.**

`D([u,v]) = ū⁻¹(v̄⁻¹−1)D(u) + ū⁻¹v̄⁻¹(ū−1)D(v)`, and both operator factors die when the two
bases act trivially — *whatever* the offsets are.  This is the general form of "handle letters
appear only in commutators, whose Fox rows cancel": no freshness of the letters is used, only
the triviality of their action. -/
theorem foxD_comm_of_trivial {u v : PWord X} (hu : PWord.evalFin t E E₂ u ∈ trivAct C A)
    (hv : PWord.evalFin t E E₂ v ∈ trivAct C A) : foxD t a E E₂ (.comm u v) = 0 := by
  rw [foxD_def, foxEval_comm]
  exact WordLift.commP_u_of_trivial _ _
    (fun w => by rw [foxEval_g]; exact mem_trivAct.mp hu w)
    (fun w => by rw [foxEval_g]; exact mem_trivAct.mp hv w)

end FoxHelpers

/-- An even multiple of a `2`-torsion element vanishes. -/
theorem even_nsmul_eq_zero {V : Type*} [AddCommGroup V] (hV₂ : ∀ v : V, v + v = 0) {k : ℕ}
    (hk : Even k) (v : V) : k • v = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul]
  exact hV₂ _

/-- `p_α = 2 + 2^α` is even for `α ≥ 1` — read off WN0-a's spelling-discipline lemma
`Words.two_add_two_pow` (`2 + 2^α = 2(1 + 2^{α−1})`), which is exactly the device the Sage side
needs to decide the parity for *symbolic* `α`. -/
theorem even_two_add_two_pow {α : ℕ} (hα : 1 ≤ α) : Even (2 + 2 ^ α) :=
  ⟨1 + 2 ^ (α - 1), by rw [Words.two_add_two_pow α hα]; ring⟩

/-! ## The compact-`N` alphabet at a simple tame module

The standing setting: a finite coefficient module `V` over a finite marked group `C`, with the
marking `t` of the compact-`N` alphabet `Generator (2 + 2h)`.  "Simple tame module" enters only
through the hypotheses `hwild` (the wild inertia acts trivially — every `x_i`, handles included)
and the class condition on `τ`; the `σ`-action `S` is never restricted. -/

section Rows

variable {h α q : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite V] in
/-- The `x₀`, `x₁`, `x₂` letters act trivially, from the uniform wild hypothesis. -/
theorem trivAct_coreLetter (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (i : Fin 3) : t (coreLetter h i) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
/-- The handle letters act trivially. -/
theorem trivAct_handleU (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleU j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
@[inherit_doc trivAct_handleU]
theorem trivAct_handleV (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleV j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

/-! ### The five factors, one at a time -/

/-- **Factor 1** — `D(x₀^{p_α}) = 0`.  The leading power's whole first-order content is the
parity of `p_α = 2 + 2^α`, which is even as soon as `α ≥ 1`; over a char-`2` module the
geometric sum `1 + X₀ + ⋯` at a trivially-acting `X₀` is the scalar `p_α`, hence `0`.

The branch condition is `α ≥ 2` (`BranchData.Valid`), but that extra strength is a **Hessian**
condition (`1 + 2^{α−1}` odd, `Words.odd_one_add_two_pow`) and is invisible here. -/
theorem foxD_leadingPow (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hα : 1 ≤ α)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α)) = 0 := by
  rw [show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring,
    foxD_zpow_natCast, WordLift.sum_pow_smul_of_trivial (fun v => ?_)]
  · exact even_nsmul_eq_zero hV₂ (even_two_add_two_pow hα) _
  · exact mem_trivAct.mp (trivAct_coreLetter t hwild 0) v

/-- **Factor 2** — `D([x₀,x₁]) = 0`. -/
theorem foxD_leadingComm (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1))) = 0 :=
  foxD_comm_of_trivial _ _ _ _ (trivAct_coreLetter t hwild 0) (trivAct_coreLetter t hwild 1)

/-- **Factor 3 — the source of the `1 − S⁻¹` block.**  `D((x₂^σ)⁻¹) = −S⁻¹·a(x₂)`.

Both `σ`-contributions of `σ⁻¹x₂σ` cancel (the conjugation rule's `+ x̄₂·a(σ) − a(σ)` at a
trivially-acting `x₂`), the conjugator survives as the operator `S⁻¹`, and the outer inverse
contributes the sign.  Deleting the `^σ` would leave `−a(x₂)` and the unramified `x₂`-column
would be `1 − 1 = 0`; **the invertible block exists because the conjugator is `σ`**. -/
theorem foxD_invConjX2 (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)))
      = -(t.σ⁻¹ • a (coreLetter h 2)) := by
  have hx2 := mem_trivAct.mp (trivAct_coreLetter t hwild 2)
  have hconj : PWord.evalFin ⇑t E E₂ (.conj (.gen (coreLetter h 2)) (.gen .sigma))
      ∈ trivAct C V := by
    rw [PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_conjR (trivAct_coreLetter t hwild 2) _
  rw [foxD_inv, mem_trivAct.mp (inv_mem hconj), foxD_conj, PWord.evalFin_gen, PWord.evalFin_gen,
    foxD_gen, foxD_gen, hx2]
  simp

/-- The `δ₂`-block's inner word `x₂ · τ` — as a `PWord.prodList`, the certificate's spelling
(WN0-a authoring rule 5: the trailing `PWord.one` is part of the tree). -/
theorem foxD_deltaInner (a : Generator (2 + 2 * h) → V)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) :
    foxD ⇑t a E E₂ (PWord.prodList [.gen (coreLetter h 2), .gen .tau])
      = a (coreLetter h 2) + a .tau := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_mul,
    PWord.evalFin_gen, PWord.evalFin_gen, foxD_gen, foxD_gen, foxD_one, smul_zero, add_zero,
    mem_trivAct.mp (trivAct_coreLetter t hwild 2)]

omit [Finite C] [Finite V] in
/-- The evaluation of the `δ₂`-block's inner word `x₂τ` acts as `τ` does. -/
theorem evalFin_deltaInner_smul (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (v : V) :
    PWord.evalFin ⇑t E E₂ (PWord.prodList [.gen (coreLetter h 2), .gen .tau]) • v = t.τ • v := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one, mul_smul,
    mem_trivAct.mp (trivAct_coreLetter t hwild 2)]
  rfl

/-- **Factor 4, split/unramified (`P = 1`)** — `D((x₂τ)^{ω₂}) = a(x₂) + a(τ)`.

The `ω₂`-collapse is WW1's engine lemma `WordLift.powOmega2_u_of_trivial`; `powOmega2` is not
unfolded. -/
theorem foxD_deltaBlock_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
      = a (coreLetter h 2) + a .tau := by
  rw [foxD_def, foxEval_omega2Pow,
    WordLift.powOmega2_u_of_trivial hV₂ _
      (fun v => by rw [foxEval_g]; exact (evalFin_deltaInner_smul t E E₂ hwild v).trans (hτ v))]
  exact foxD_deltaInner t E E₂ a hwild

/-- **Factor 4, ramified (`P = 0`)** — `D((x₂τ)^{ω₂}) = 0`.

The engine lemma is `WordLift.powOmega2_u_of_oddFixedPointFree`: the base `x₂τ` acts as the
fixed-point-free `T`, and its `2`-primary part acts trivially, so the norm sum vanishes. -/
theorem foxD_deltaBlock_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
      = 0 := by
  have hbase : PWord.evalFin ⇑t E E₂ (PWord.prodList [.gen (coreLetter h 2), .gen .tau])
      = t (coreLetter h 2) * t.τ := by
    rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
      PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one]
    rfl
  rw [foxD_def, foxEval_omega2Pow]
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => hτfpf v ?_) (fun v => ?_)
  · rw [foxEval_g] at hv
    exact ((evalFin_deltaInner_smul t E E₂ hwild v).symm.trans hv)
  · rw [foxEval_g, hbase]
    exact WordLift.powOmega2_smul_of_trivial_mul _ _
      (mem_trivAct.mp (trivAct_coreLetter t hwild 2)) hTodd v

/-- **Factor 5** — `D(H_h) = 0`: the handle block is a product of commutators of trivially-acting
letters, so its Fox row is zero at every handle count. -/
theorem foxD_handlesW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) : foxD ⇑t a E E₂ (handlesW h) = 0 := by
  have hmem : ∀ w ∈ (List.finRange h).map fun j =>
      (PWord.comm (.gen (handleU j)) (.gen (handleV j)) : PWord (Generator (2 + 2 * h))),
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

omit [Finite C] [Finite V] in
/-- Every factor of the compact-`N` word evaluates trivially, at both `τ`-classes (the class
enters only through `hδ`, the `δ₂`-block's own evaluation). -/
theorem trivAct_nCompact_factors (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) ∈ trivAct C V) :
    ∀ w ∈ [(PWord.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α) : PWord (Generator (2 + 2 * h))),
        .comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)),
        .inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)),
        PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
        handlesW h],
      PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · rw [PWord.evalFin_zpow, PWord.evalFin_gen]
    exact zpow_mem (trivAct_coreLetter t hwild 0) _
  · rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_commR (trivAct_coreLetter t hwild 0) (trivAct_coreLetter t hwild 1)
  · rw [PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
    exact inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) _)
  · exact hδ
  · rw [handlesW]
    refine trivAct_evalFin_prodList ?_
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_commR (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)

/-! ### The wild rows -/

/-- **The compact-`N` wild row on an unramified simple module** (packet Def. 9.1(3); freeze
row 2): at a marking whose wild letters and whose `τ` act trivially,

```
D(R_{N,α,0}) = a(τ) + (1 − S⁻¹)·a(x₂).
```

Only two of the `2h + 5` columns are nonzero, and the `x₂`-column is the invertible block
`1 − S⁻¹` of `isUnit_oneSubSInvEnd_iff`.  No hypothesis whatever on `S`. -/
theorem foxD_nCompact_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hα : 1 ≤ α) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (nCompactW α h)
      = a .tau + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  have hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) ∈ trivAct C V := by
    rw [PWord.evalFin_omega2Pow]
    refine trivAct_powOmega2 (mem_trivAct.mpr fun v => ?_)
    exact (evalFin_deltaInner_smul t E E₂ hwild v).trans (hτ v)
  rw [nCompactW, foxD_prodList_of_trivial _ _ _ _ _ (trivAct_nCompact_factors t E E₂ hwild hδ)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_leadingPow t E E₂ hV₂ hwild hα, foxD_leadingComm t E E₂ hwild,
    foxD_invConjX2 t E E₂ hwild, foxD_deltaBlock_unram t E E₂ hV₂ hwild hτ,
    foxD_handlesW t E E₂ hwild]
  abel

/-- **The compact-`N` wild row on a ramified simple module** (`P = 0`): only the `x₂^{-σ}`
contribution survives,

```
D(R_{N,α,0}) = −S⁻¹·a(x₂),
```

a single **unit** entry — the ramified twin of the `Γ_R` row pair, and the branch whose one-op
normal form is a column scaling. -/
theorem foxD_nCompact_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (hα : 1 ≤ α)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (nCompactW α h) = -(t.σ⁻¹ • a (coreLetter h 2)) := by
  have hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) ∈ trivAct C V := by
    rw [PWord.evalFin_omega2Pow]
    refine mem_trivAct.mpr fun v => ?_
    have hbase : PWord.evalFin ⇑t E E₂ (PWord.prodList [.gen (coreLetter h 2), .gen .tau])
        = t (coreLetter h 2) * t.τ := by
      rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
        PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one]
      rfl
    rw [hbase]
    exact WordLift.powOmega2_smul_of_trivial_mul _ _
      (mem_trivAct.mp (trivAct_coreLetter t hwild 2)) hTodd v
  rw [nCompactW, foxD_prodList_of_trivial _ _ _ _ _ (trivAct_nCompact_factors t E E₂ hwild hδ)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_leadingPow t E E₂ hV₂ hwild hα, foxD_leadingComm t E E₂ hwild,
    foxD_invConjX2 t E E₂ hwild, foxD_deltaBlock_ram t E E₂ hwild hτfpf hTodd,
    foxD_handlesW t E E₂ hwild]
  abel

/-- **The compact-`N` wild row on a split (scalar) module**: with `S` acting trivially too, the
`1 − S⁻¹` block *vanishes* and the row degenerates to the `τ`-pivot `a(τ)`.

This is the honest content of "the scalar module separates nothing": the wild relator carries no
information about `x₂` on a module where the whole tame quotient acts trivially. -/
theorem foxD_nCompact_split (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) (hα : 1 ≤ α) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (nCompactW α h) = a .tau := by
  have hσinv : ∀ v : V, t.σ⁻¹ • v = v := fun v => inv_smul_eq_iff.mpr (hσ v).symm
  rw [foxD_nCompact_unram t E E₂ hV₂ hwild hτ hα, hσinv]
  abel

end Rows

end GQ2.Dyadic.Certificates
