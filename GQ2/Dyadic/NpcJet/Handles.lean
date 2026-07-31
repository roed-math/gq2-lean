/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.NpcJet.Main

/-!
# The handle tail of the corrected noncompact-`N` jet, and a concrete carrier for it

**Ticket NC6** of the NC lane (R3(a) commission) — the lane's last file.  Binding design memo:
`docs/dyadic/nc-design.md` **§2.5** (the handle tail) and its NC6 row (§4.1/§4.2), plus the
"what NC6 still owes" list in `NpcJet/Main.lean`'s docstring.  Two deliverables:

1. **The handle tail `H_h`** (memo §2.5).  The genus-`h` noncompact relator is the `h = 0` core
   times the hyperbolic-handle block `H_h = ∏_{j<h} [x_{a j}, x_{b j}]`, and its jet is the
   headline's value plus `∑_{j<h} b_q(e_{a j}, e_{b j})` — the `plus_form_noncompact` tail
   (`N.py:3429`).  This is an induction on `h` that is **independent of the core**: NC5's
   `npc_cross_operators` is cited, never re-proved.
2. **A fully concrete-carrier instantiation.**  NC5's stress pin `npc_cross_operators_pin` fixes
   `(α, r, η) = (2, 1, 1)` but quantifies over an arbitrary module.  §3 below exhibits an explicit
   one — the cyclic group of order `3` acting freely on `𝔽₂²` by the companion matrix of
   `x² + x + 1`, with the anisotropic form `q(x,y) = x + xy + y` — verifies every hypothesis by
   kernel `decide`, and instantiates both the headline and the handled headline at it, with both
   sides **computed to numerals**.

## §1. The genus-`h` word (memo §2.5)

The memo's shape is "`Generator n` with `n = 2 + 2h`, handle letters `x_{3+2j}, x_{4+2j}`".  Since
`npcWord` is fixed at `Generator 2` (NC2's file is closed), the genus-`h` word is built by
*substitution* along the generator embedding `npcLift m : Generator 2 → PWord (Generator (m + 2))`
(`σ ↦ σ`, `τ ↦ τ`, `x_i ↦ x_i`), which needs no side condition: the ambient arity is written
`m + 2`, so the three core letters always fit.

```
npcWordH m α r η a b h = subst (npcLift m) (npcWord α r η) · npcHandles a b h
npcHandles a b h       = ∏_{j<h} [x_{a j}, x_{b j}]                (`handlesProd`-shaped)
```

The handle letters are addressed by **arbitrary** index functions `a b : ℕ → Fin (m + 3)` rather
than by the hard-wired `3 + 2j`, `4 + 2j`: the induction does not care, and the memo's literal
indexing is then one corollary (`npc_cross_operators_handles_std`, at `m = 2h`) rather than a
constraint on the statement.  `npcHandles_eval_eq_handlesProd` records that the block really is
the `handlesProd` of `GQ2/Dyadic/Word/Blocks.lean` read at the marking (with the index shift: the
`PWord` block counts handles from `0`, `handlesProd` from `1`).

The genus-`h` Gate-E marking `npcMarkingH m s u e` carries **one** offset function `e : ℕ → V`
indexed by the *letter* index, so `e 0 = c₀`, `e 1 = c₁`, `e 2 = 0` (the boundary letter is still
deliberately offset-free — memo §2.4, hypothesis `he2`), and `e (3 + 2j)`, `e (4 + 2j)` are the
memo's handle offsets.  This is why the tail below reads `∑ j, b_q(e_{a j}, e_{b j})` with no
second offset family.

## §2. The handled headline

```
fib (eval_{t_h} R_{N,α,r,η,h})
  = Q₀(c₀) + b_q(c₁, L_c c₀) + ∑_{j<h} b_q(e_{a j}, e_{b j}),     L_c = A⁻¹ + B + B·A⁻¹
```

— `npc_cross_operators_handles`, in exactly NC5's hypothesis-minimal shape: the same four
mathematical hypotheses `hV2`, `hu`, `hVu`, `hα` and nothing else (`1 ≤ r`, `IsUnit η`,
simplicity, faithfulness, nonsingularity and invariance of `q` are absent here too), plus the one
bookkeeping hypothesis `he2 : e 2 = 0` that says the marking is the Gate-E one.  The proof is four
rewrites:

* `npcWordH_core_eval` — substitution along `npcLift` is evaluation at the restricted marking
  (`PWord.eval_subst`), so the core factor is *literally* NC5's left-hand side;
* `npcHandles_eval` — the induction, whose step is NC2's `sliceElt_comm` (both handle letters are
  in the Heisenberg slice) followed by `sliceElt_mul`;
* `fib_mul_central` — the handle block's value `((0,1), T)` is central *and* `κ⁰`-inert, so it
  adds `T` to the fibre with no cross term;
* `npc_cross_operators` — NC5's headline, cited.

Note what the induction shows about charges: `npcHandles_eval` lets the handle letters carry
**arbitrary** fibre charges `z` and the answer does not mention them.  That is `sliceElt_comm`'s
charge-cancellation again (memo §3.3, risk 2), now at the handles rather than at the `E`-block.

`npc_cross_operators_handles_zero` checks that `h = 0` degenerates to the headline, and
`npc_cross_operators_handles_std` puts the memo's literal indexing (`n = 2 + 2h`, handle letters
`x_{3+2j}`, `x_{4+2j}`) on the tail.

## §3. The concrete carrier

`PinC = ℤ/3` (written multiplicatively) acting on `PinV = 𝔽₂²` by `g·(x,y) = (y, x+y)`, with

```
q(x,y) = x + xy + y,      f((x,y),(x',y')) = xx' + xy' + yy',      m = 0.
```

`g` has order `3` and **no nonzero fixed vector** (its characteristic polynomial `x² + x + 1` is
irreducible over `𝔽₂`), `q` is the anisotropic form with `f(v,v) = q(v)`, and `f` is `g`-invariant
— which is exactly what lets `m = 0` satisfy eq. (59).  Discharged **by kernel `decide`**: all
eight `IsEquivariantFactorSet` fields, `hV2`, `hVu` (fixed-point-freeness), and `x ^ 3 = 1`.
Discharged **by construction**: the `DistribMulAction` (four `decide`d axioms), the topology
(`⊥` + `DiscreteTopology`), `Finite`, and `hu` (`orderOf g ∣ 3` and `3` is prime, so the order is
`1` or `3` — both odd).

Because `|PinC|` is odd, `zpowHat_etaHatZ_of_odd` makes the profinite conjugator concrete:
`A = g ^ᶻ η̂ = g` for **every** `η : ℤ_[2]`, so at `r = 1`

```
L_c v = g⁻¹v + g²v + (g²g⁻¹)v = g²v + g²v + gv = g·v         (characteristic 2),
Q₀(c₀) = f(c₀, g⁻¹c₀).
```

Both sides are then numerals: at `c₀ = c₁ = (1,0)` the jet is `1` (`npc_cross_operators_pin_value`)
— so the identity is **not vacuous at a concrete carrier** — and adding one handle with offsets
`(1,0)`, `(0,1)` flips it to `0` (`npc_cross_operators_pin_handles_value`), which is the handle
tail being observed rather than assumed.

## The NC lane, closed

* **NC1** — `docs/dyadic/nc-design.md`: the design memo and feasibility spike.  The S3.2
  refutation of draft display eq:Ncross, the corrected `L_c = A⁻¹ + B + B·A⁻¹`, the frozen
  statement (§2), the block-by-block route (§3).
* **NC2** — `NpcJet/Defs.lean`: the word `npcWord`, the Gate-E marking, `lcOp`/`npcQ0`, and the
  Heisenberg-slice calculus (`sliceElt_mul/inv/sq/conj/comm`, the `y^k` power law).
* **NC3** — `NpcJet/Omega.lean`: the two reduction rules — `ω₂` on pro-odd elements (rule 1) and
  the vanishing orbit norm on `V^u = 0` (rule 2) — plus the `η̂`-power vocabulary.
* **NC4** — `NpcJet/Seams.lean`: the per-block evaluation theorems `δ₀`/`D`/`E`/boundary/head,
  where the three inverse conjugators of the corrected `L_c` become visible.
* **NC5** — `NpcJet/Main.lean`: the `h = 0` headline `npc_cross_operators`, the packet bridge
  `hVu_of_simple`, the discrepancy display (errata item 5) and the `(α, r, η)` pin.
* **NC6** — this file: the handle tail `H_h`, the `handlesProd` reading, and the concrete carrier
  with computed values.

## What WNP-c still owes (memo risk 5)

`npc_cross_operators` and its handled form say the jet **is** `Q₀ + b_q(c₁, L_c c₀) + tail`.  They
do **not** say the `c₀`–`c₁` pairing is nondegenerate: that needs `L_c = 1 + (1 + A⁻¹)(1 + B)` to
be **invertible on the module at hand**, which genuinely varies with the module (on the carrier of
§3 it is `L_c = g`, invertible; on a module with `A = B = 1` it is the identity; in general it can
degenerate) and belongs with WNP-c's Fox/normal-form clauses, not with the jet identity.  On a
concrete battery module it is a `decide`.  Also still out of scope by design: the three-variable
Gate-D diagnostic form (an offset on the boundary letter `x₂`).

## Axioms

Measured on the built module, **every** declaration in this file prints
`[propext, Classical.choice, Quot.sound]` — std-3 — including the `decide`-discharged ones
(`pinHdat`, `pinV2`, `pinVu`, `pinPow3`, the `DistribMulAction` instance), whose `Decidable`
instances reach mathlib's classical layer even though the reductions themselves are kernel
evaluations.  `decide` is used only in the kernel sense: there is no `native_decide` anywhere.  No
census axiom is cited and none is needed (memo §9); census stays at 11.
-/

namespace GQ2.Dyadic.NpcJet

open WordCoh2 SectionEight.AffineTLift QuadraticFp2

/-! ## §1. The genus-`h` word (memo §2.5) -/

/-- **The generator embedding** `Generator 2 ↪ Generator (m + 2)`: `σ ↦ σ`, `τ ↦ τ` and the three
core wild letters `x₀, x₁, x₂` to themselves.  Writing the ambient arity as `m + 2` makes the
bound `i < m + 3` automatic, so no `2 ≤ n` side condition travels with the genus-`h` word. -/
def npcLift (m : ℕ) : Generator 2 → PWord (Generator (m + 2))
  | .sigma => .gen .sigma
  | .tau => .gen .tau
  | .wild i => .gen (.wild ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩)

@[simp] theorem npcLift_sigma (m : ℕ) : npcLift m .sigma = .gen .sigma := rfl

@[simp] theorem npcLift_tau (m : ℕ) : npcLift m .tau = .gen .tau := rfl

/-- **The hyperbolic-handle block** `H_h = ∏_{j<h} [x_{a j}, x_{b j}]` (memo §2.5; campaign §7.1,
`GQ2/Dyadic/Word/Blocks.lean`'s `handlesProd` at the word level).  The handle letters are addressed
by arbitrary index functions: the memo's `x_{3+2j}, x_{4+2j}` is the instance
`npc_cross_operators_handles_std`, not a constraint on the block. -/
def npcHandles {m : ℕ} (a b : ℕ → Fin (m + 3)) : ℕ → PWord (Generator (m + 2))
  | 0 => .one
  | h + 1 => .mul (npcHandles a b h) (.comm (.gen (.wild (a h))) (.gen (.wild (b h))))

@[simp] theorem npcHandles_zero {m : ℕ} (a b : ℕ → Fin (m + 3)) :
    npcHandles a b 0 = .one := rfl

theorem npcHandles_succ {m : ℕ} (a b : ℕ → Fin (m + 3)) (h : ℕ) :
    npcHandles a b (h + 1)
      = .mul (npcHandles a b h) (.comm (.gen (.wild (a h))) (.gen (.wild (b h)))) := rfl

/-- **The genus-`h` noncompact relator** `R_{N,α,r,η,h}` (memo §2.5): the `h = 0` core of NC2,
transported along `npcLift`, times the handle block.  At `h = 0` the second factor is `1`, so this
is the core itself up to the (jet-invisible) renaming of letters. -/
noncomputable def npcWordH (m α r : ℕ) (η : ℤ_[2]) (a b : ℕ → Fin (m + 3)) (h : ℕ) :
    PWord (Generator (m + 2)) :=
  .mul (PWord.subst (npcLift m) (npcWord α r η)) (npcHandles a b h)

section MarkingLevel

variable {m : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The handle block is `handlesProd`-shaped** (memo §2.5), read at any marking of any profinite
group: the word-level block of this file evaluates to the group-level block of
`GQ2/Dyadic/Word/Blocks.lean`.  The index shift is the two files' conventions — the `PWord` block
counts its handles from `0`, `handlesProd` from `1`. -/
theorem npcHandles_eval_eq_handlesProd (t : Marking (m + 2) G) (a b : ℕ → Fin (m + 3)) (h : ℕ) :
    t.eval (npcHandles a b h)
      = handlesProd (fun j ↦ t.x (a (j - 1))) (fun j ↦ t.x (b (j - 1))) h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      rw [npcHandles_succ, Marking.eval_mul, ih, handlesProd_succ, Marking.eval_comm,
        Marking.eval_gen, Marking.eval_gen, Marking.apply_wild, Marking.apply_wild,
        Nat.add_sub_cancel]

end MarkingLevel

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The genus-`h` Gate-E marking** (memo §2.5): `σ ↦ s`, `τ ↦ u` on the `C`-line and *every*
wild letter trivial-lower with offset `e i` — one offset function indexed by the letter index, so
`e 0 = c₀`, `e 1 = c₁`, `e 2 = 0` (the boundary letter, memo §2.4) and `e 3, e 4, …` are the handle
offsets.  The `e 2 = 0` normalization is carried as the hypothesis `he2` where it is used, not
built into the definition, so that the marking stays a plain `ofLetters`. -/
def npcMarkingH (m : ℕ) (s u : C) (e : ℕ → V) :
    Marking (m + 2) (CentExt (kappa0Cocycle dat hdat)) :=
  Marking.ofLetters (cLine dat hdat s) (cLine dat hdat u) (fun i ↦ sliceElt dat hdat (e i.val) 0)

@[simp] theorem npcMarkingH_x (m : ℕ) (s u : C) (e : ℕ → V) (i : Fin (m + 3)) :
    (npcMarkingH dat hdat m s u e).x i = sliceElt dat hdat (e i.val) 0 := rfl

/-! ## §2. The handle tail (memo §2.5) -/

/-- **A central slice element adds its charge to the fibre.**  `((0,1), T)` has `V`-part `0`, so
the `κ⁰`-correction `f(v, c·0) + m_c(0)` vanishes on the right and the product's fibre is the plain
sum.  This is what lets the handle block's value be appended to the core's without a cross term. -/
theorem fib_mul_central (x : CentExt (kappa0Cocycle dat hdat)) (T : ZMod 2) :
    CentExt.fib (c := kappa0Cocycle dat hdat) (x * sliceElt dat hdat 0 T) = x.fib + T := by
  rw [CentExt.mul_fib, sliceElt_fib, sliceElt_base]
  show x.fib + T + (dat.f (x.base).v ((x.base).cc • (0 : V)) + dat.m (x.base).cc 0) = x.fib + T
  rw [smul_zero, hdat.f_zero_right, IsEquivariantFactorSet.m_zero dat hdat, add_zero, add_zero]

section Finite

variable [Finite C] [Finite V]

/-- **The handle tail** (memo §2.5): at a marking whose wild letters all lie in the Heisenberg
slice, the handle block evaluates to the central element carrying `∑_{j<h} b_q(e_{a j}, e_{b j})`.

An induction on `h` whose step is NC2's `sliceElt_comm` — which cancels both arguments' fibres.
That is why the charges `z` are quantified over and do not appear in the answer: the handle
letters may carry arbitrary charges (memo §3.3's charge-independence, now at the handles). -/
theorem npcHandles_eval (hV2 : ∀ v : V, v + v = 0) {m : ℕ}
    (t : Marking (m + 2) (CentExt (kappa0Cocycle dat hdat))) (a b : ℕ → Fin (m + 3))
    (e : ℕ → V) (z : ℕ → ZMod 2)
    (hx : ∀ i : Fin (m + 3), t.x i = sliceElt dat hdat (e i.val) (z i.val)) (h : ℕ) :
    t.eval (npcHandles a b h)
      = sliceElt dat hdat 0 (∑ j ∈ Finset.range h, polar q (e (a j).val) (e (b j).val)) := by
  induction h with
  | zero => simp [npcHandles]
  | succ h ih =>
      rw [npcHandles_succ, Marking.eval_mul, ih, Marking.eval_comm, Marking.eval_gen,
        Marking.eval_gen, Marking.apply_wild, Marking.apply_wild, hx, hx,
        sliceElt_comm dat hdat hV2, sliceElt_mul dat hdat, hdat.f_zero_left, add_zero, add_zero,
        Finset.sum_range_succ]

/-- **Substitution along the lift is restriction of the marking** (`PWord.eval_subst`): if `t`
agrees with the Gate-E marking on the five core letters, then the transported core word has the
core's value, verbatim.  This is what lets NC5's headline be *cited* rather than re-proved. -/
theorem npcWordH_core_eval {m : ℕ} (t : Marking (m + 2) (CentExt (kappa0Cocycle dat hdat)))
    (s u : C) (c₀ c₁ : V)
    (hcore : ∀ g : Generator 2, t.eval (npcLift m g) = npcMarking dat hdat s u c₀ c₁ g)
    (w : PWord (Generator 2)) :
    t.eval (PWord.subst (npcLift m) w) = (npcMarking dat hdat s u c₀ c₁).eval w := by
  rw [Marking.eval_def, PWord.eval_subst, Marking.eval_def]
  exact congrArg (fun μ ↦ PWord.eval μ w) (funext hcore)

/-- The genus-`h` marking restricts to the Gate-E marking of NC2 along `npcLift`, with `c₀ = e 0`
and `c₁ = e 1`.  The boundary letter is where `he2 : e 2 = 0` is consumed — without it the marking
would be computing the three-variable Gate-D diagnostic form (memo §2.4). -/
theorem npcMarkingH_core (m : ℕ) (s u : C) (e : ℕ → V) (he2 : e 2 = 0) :
    ∀ g : Generator 2, (npcMarkingH dat hdat m s u e).eval (npcLift m g)
      = npcMarking dat hdat s u (e 0) (e 1) g := by
  intro g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      fin_cases i
      · rfl
      · rfl
      · show sliceElt dat hdat (e 2) 0 = sliceElt dat hdat 0 0
        rw [he2]

section Headline

variable [TopologicalSpace C] [DiscreteTopology C]

/-- **The corrected noncompact-`N` cross-operator identity with handles** (memo §2.5, the
`plus_form_noncompact` tail): at genus `h` the second jet of `R_{N,α,r,η,h}` at the Gate-E marking
is

```
Q(c₀, c₁, e) = Q₀(c₀) + b_q(c₁, L_c c₀) + ∑_{j<h} b_q(e_{a j}, e_{b j}),
L_c = A⁻¹ + B + B·A⁻¹,   A = σ^{η̂},  B = σ^{2^r}.
```

The hypothesis surface is NC5's, unchanged — `hV2` (characteristic 2), `hu` (rule 1), `hVu`
(rule 2), `hα` (`α ≥ 2`, sharp) — plus the Gate-E normalization `he2 : e 2 = 0`; still no `1 ≤ r`,
no `IsUnit η`, no simplicity, faithfulness, nonsingularity or invariance of `q`.  The core is
`npc_cross_operators`, cited: nothing below NC5's seams is re-entered. -/
theorem npc_cross_operators_handles (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2])
    {m : ℕ} (e : ℕ → V) (he2 : e 2 = 0) (a b : ℕ → Fin (m + 3)) (h : ℕ) :
    ((npcMarkingH dat hdat m s u e).eval (npcWordH m α r η a b h)).fib
      = npcQ0 dat s η (e 0) + polar q (e 1) (lcOp s η r (e 0))
        + ∑ j ∈ Finset.range h, polar q (e (a j).val) (e (b j).val) := by
  rw [npcWordH, Marking.eval_mul,
    npcWordH_core_eval dat hdat _ s u (e 0) (e 1) (npcMarkingH_core dat hdat m s u e he2),
    npcHandles_eval dat hdat hV2 _ a b e (fun _ ↦ 0) (fun _ ↦ rfl), fib_mul_central dat hdat,
    npc_cross_operators dat hdat hV2 s u hu hVu α hα r η (e 0) (e 1)]

/-- **The handle tail degenerates to the headline at `h = 0`** — the consistency check that the
genus-`h` statement really extends NC5's, and not something else. -/
theorem npc_cross_operators_handles_zero (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2])
    {m : ℕ} (e : ℕ → V) (he2 : e 2 = 0) (a b : ℕ → Fin (m + 3)) :
    ((npcMarkingH dat hdat m s u e).eval (npcWordH m α r η a b 0)).fib
      = npcQ0 dat s η (e 0) + polar q (e 1) (lcOp s η r (e 0)) := by
  rw [npc_cross_operators_handles dat hdat hV2 s u hu hVu α hα r η e he2 a b 0,
    Finset.sum_range_zero, add_zero]

/-- **The memo's literal indexing** (memo §2.5): `n = 2 + 2h` with handle letters `x_{3+2j}` and
`x_{4+2j}`, so the tail is `∑_{j<h} b_q(e_{3+2j}, e_{4+2j})`.  The index functions are total (they
reduce mod `2h + 3`), and on the summation range `j < h` the reduction is the identity. -/
theorem npc_cross_operators_handles_std (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (h : ℕ) (e : ℕ → V) (he2 : e 2 = 0) :
    ((npcMarkingH dat hdat (2 * h) s u e).eval
        (npcWordH (2 * h) α r η (fun j ↦ ⟨(3 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩)
          (fun j ↦ ⟨(4 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩) h)).fib
      = npcQ0 dat s η (e 0) + polar q (e 1) (lcOp s η r (e 0))
        + ∑ j ∈ Finset.range h, polar q (e (3 + 2 * j)) (e (4 + 2 * j)) := by
  rw [npc_cross_operators_handles dat hdat hV2 s u hu hVu α hα r η e he2]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  show polar q (e ((3 + 2 * j) % (2 * h + 3))) (e ((4 + 2 * j) % (2 * h + 3))) = _
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end Headline

end Finite

end Module

/-! ## §3. A concrete carrier

Everything below is one explicit example, built so that every hypothesis of the headline is
discharged by kernel `decide` or by a two-line construction.  The point is non-vacuity: the
identity is not merely true of some hypothetical module class. -/

/-- **The concrete group**: the cyclic group of order `3`, written multiplicatively.  A `def`
rather than an abbreviation, so the discrete topology below does not leak onto
`Multiplicative (ZMod 3)` anywhere else. -/
def PinC : Type := Multiplicative (ZMod 3)

instance : Group PinC := inferInstanceAs (Group (Multiplicative (ZMod 3)))
instance : Fintype PinC := inferInstanceAs (Fintype (Multiplicative (ZMod 3)))
instance : DecidableEq PinC := inferInstanceAs (DecidableEq (Multiplicative (ZMod 3)))
instance : TopologicalSpace PinC := ⊥
instance : DiscreteTopology PinC := ⟨rfl⟩

/-- **The concrete module**: `𝔽₂²`. -/
def PinV : Type := ZMod 2 × ZMod 2

instance : AddCommGroup PinV := inferInstanceAs (AddCommGroup (ZMod 2 × ZMod 2))
instance : Fintype PinV := inferInstanceAs (Fintype (ZMod 2 × ZMod 2))
instance : DecidableEq PinV := inferInstanceAs (DecidableEq (ZMod 2 × ZMod 2))

/-- The order-`3` rotation of `𝔽₂²` — the companion matrix of `x² + x + 1`, which is irreducible
over `𝔽₂`, so the rotation has no nonzero fixed vector. -/
def pinRot (v : PinV) : PinV := (v.2, v.1 + v.2)

/-- The `ℤ/3`-action on `𝔽₂²` by powers of `pinRot`. -/
def pinAct (c : ZMod 3) (v : PinV) : PinV :=
  match c.val with
  | 0 => v
  | 1 => pinRot v
  | _ => pinRot (pinRot v)

instance : SMul PinC PinV := ⟨fun c v ↦ pinAct (Multiplicative.toAdd c) v⟩

instance : DistribMulAction PinC PinV where
  one_smul v := by revert v; decide
  mul_smul c d v := by revert c d v; decide
  smul_zero c := by revert c; decide
  smul_add c v w := by revert c v w; decide

/-- The generator of `PinC`. -/
def pinG : PinC := Multiplicative.ofAdd (1 : ZMod 3)

/-- The **anisotropic** quadratic form `q(x,y) = x + xy + y` on `𝔽₂²`: it vanishes only at `0`, and
it is `pinG`-invariant. -/
def pinQ (v : PinV) : ZMod 2 := v.1 + v.1 * v.2 + v.2

/-- A factor set for `pinQ`: the (non-symmetric) bilinear `f((x,y),(x',y')) = xx' + xy' + yy'`,
whose diagonal is `pinQ` and whose symmetrization is the polar form.  It is `pinG`-invariant, which
is exactly what lets the equivariant-lift corrections be taken to be `m = 0`. -/
def pinF (v w : PinV) : ZMod 2 := v.1 * w.1 + v.1 * w.2 + v.2 * w.2

/-- The concrete factor-set datum: `f = pinF`, `m = 0`. -/
def pinDat : FactorSet PinC PinV where
  f := pinF
  m := fun _ _ ↦ 0

/-- All eight equivariant-factor-set identities, by kernel `decide` (`4³ = 64` cases for the
cocycle identity, `3 · 4² = 48` for eq. (59)). -/
theorem pinHdat : IsEquivariantFactorSet pinQ pinDat where
  f_cocycle := by decide
  f_diag := by decide
  f_polar := by decide
  f_zero_left := by decide
  f_zero_right := by decide
  m_quad := by decide
  m_mul := by decide
  m_one := by decide

/-- Characteristic `2`. -/
theorem pinV2 : ∀ v : PinV, v + v = 0 := by decide

/-- **Fixed-point freeness** — the headline's `hVu`, i.e. rule 2's `V^u = 0`, at `u = pinG`. -/
theorem pinVu : ∀ v : PinV, pinG • v = v → v = 0 := by decide

theorem pinPow3 (x : PinC) : x ^ 3 = 1 := by revert x; decide

/-- **Rule 1's hypothesis**: every element of `PinC` has odd order, since its order divides the
prime `3`. -/
theorem pinOddOrder (x : PinC) : Odd (orderOf x) := by
  have h : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (pinPow3 x)
  rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1 <;> rw [h1] <;> decide

/-- **The profinite conjugator is concrete here**: `PinC` is pro-odd, so `η̂` acts as the identity
(`zpowHat_etaHatZ_of_odd`, Gate B's rule T2) and `A = g ^ᶻ η̂ = g` for *every* `η : ℤ_[2]`. -/
theorem pinA (η : ℤ_[2]) : pinG ^ᶻ etaHatZ η = pinG :=
  zpowHat_etaHatZ_of_odd (pinOddOrder pinG)

/-- **The corrected cross operator at the concrete carrier**, `r = 1`: `A = B⁻¹ = g` gives
`L_c v = g⁻¹v + g²v + gv = g·v` in characteristic `2`.  (The draft's `L_c = A⁻¹ = g²` is a
*different* operator — the discrepancy `B(1 + A⁻¹)` is `g² + g ≠ 0` here.) -/
theorem pin_lcOp (η : ℤ_[2]) (v : PinV) : lcOp pinG η 1 v = pinG • v := by
  rw [lcOp, pinA]
  revert v
  decide

/-- **The diagonal part at the concrete carrier**: `Q₀(c₀) = f(c₀, g⁻¹c₀)`, the correction `m`
being `0`. -/
theorem pin_npcQ0 (η : ℤ_[2]) (v : PinV) : npcQ0 pinDat pinG η v = pinF v (pinG⁻¹ • v) := by
  rw [npcQ0, pinA]
  exact add_zero _

/-- **The headline at a fully concrete carrier**: `npc_cross_operators` with the module, the group,
the form, the factor set, `s`, `u` and every hypothesis pinned.  Nothing is quantified here except
the word parameters `(α, r, η)` and the two offsets. -/
theorem npc_cross_operators_pin_module (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : PinV) :
    ((npcMarking pinDat pinHdat pinG pinG c₀ c₁).eval (npcWord α r η)).fib
      = npcQ0 pinDat pinG η c₀ + polar pinQ c₁ (lcOp pinG η r c₀) :=
  npc_cross_operators pinDat pinHdat pinV2 pinG pinG (pinOddOrder pinG) pinVu α hα r η c₀ c₁

/-- **Both sides are numerals**: at `(α, r, η) = (2, 1, 1)` and `c₀ = c₁ = (1,0)` the jet of the
noncompact relator is `1`.  The identity is therefore **not vacuous** — there is a module, a group
and a marking at which its two sides are computed and nonzero. -/
theorem npc_cross_operators_pin_value :
    ((npcMarking pinDat pinHdat pinG pinG ((1, 0) : PinV) ((1, 0) : PinV)).eval
      (npcWord 2 1 1)).fib = 1 := by
  rw [npc_cross_operators_pin_module 2 le_rfl 1 1, pin_lcOp, pin_npcQ0]
  decide

/-- The genus-`1` offsets used by the handled pin: `c₀ = c₁ = (1,0)`, boundary `0`, and one handle
with offsets `(1,0)`, `(0,1)`. -/
def pinE : ℕ → PinV
  | 0 => (1, 0)
  | 1 => (1, 0)
  | 2 => 0
  | 3 => (1, 0)
  | _ => (0, 1)

/-- **The handled headline at the concrete carrier**, `h = 1`, in the memo's indexing. -/
theorem npc_cross_operators_pin_handles (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) :
    ((npcMarkingH pinDat pinHdat (2 * 1) pinG pinG pinE).eval
        (npcWordH (2 * 1) α r η (fun j ↦ ⟨(3 + 2 * j) % (2 * 1 + 3), Nat.mod_lt _ (by omega)⟩)
          (fun j ↦ ⟨(4 + 2 * j) % (2 * 1 + 3), Nat.mod_lt _ (by omega)⟩) 1)).fib
      = npcQ0 pinDat pinG η (pinE 0) + polar pinQ (pinE 1) (lcOp pinG η r (pinE 0))
        + ∑ j ∈ Finset.range 1, polar pinQ (pinE (3 + 2 * j)) (pinE (4 + 2 * j)) :=
  npc_cross_operators_handles_std pinDat pinHdat pinV2 pinG pinG (pinOddOrder pinG) pinVu α hα r η
    1 pinE rfl

/-- **The handle tail is observed, not assumed**: the same carrier, the same `(α, r, η) = (2,1,1)`
and the same `c₀ = c₁ = (1,0)` as `npc_cross_operators_pin_value`, but with one handle carrying
offsets `(1,0)`, `(0,1)` — and the jet is `0` instead of `1`.  The tail
`b_q((1,0), (0,1)) = 1` is what flipped it. -/
theorem npc_cross_operators_pin_handles_value (η : ℤ_[2]) :
    ((npcMarkingH pinDat pinHdat (2 * 1) pinG pinG pinE).eval
        (npcWordH (2 * 1) 2 1 η (fun j ↦ ⟨(3 + 2 * j) % (2 * 1 + 3), Nat.mod_lt _ (by omega)⟩)
          (fun j ↦ ⟨(4 + 2 * j) % (2 * 1 + 3), Nat.mod_lt _ (by omega)⟩) 1)).fib = 0 := by
  rw [npc_cross_operators_pin_handles 2 le_rfl 1, pin_lcOp, pin_npcQ0, Finset.sum_range_one]
  decide

end GQ2.Dyadic.NpcJet
