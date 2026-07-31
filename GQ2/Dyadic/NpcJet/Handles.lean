/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.NpcJet.Main

/-!
# The handle tail of the corrected noncompact-`N` jet

**Ticket NC6** of the NC lane (R3(a) commission) — the lane's last file.  Binding design memo:
`docs/dyadic/nc-design.md` **§2.5** (the handle tail) and its NC6 row (§4.1/§4.2), plus the
"what NC6 still owes" list in `NpcJet/Main.lean`'s docstring.  The first of NC6's two deliverables:

1. **The handle tail `H_h`** (memo §2.5).  The genus-`h` noncompact relator is the `h = 0` core
   times the hyperbolic-handle block `H_h = ∏_{j<h} [x_{a j}, x_{b j}]`, and its jet is the
   headline's value plus `∑_{j<h} b_q(e_{a j}, e_{b j})` — the `plus_form_noncompact` tail
   (`N.py:3429`).  This is an induction on `h` that is **independent of the core**: NC5's
   `npc_cross_operators` is cited, never re-proved.

(Deliverable 2, the concrete carrier, lands in the next commit on this file.)

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

## The NC lane, closed

| ticket | file | contents |
|---|---|---|
| NC1 | `docs/dyadic/nc-design.md` | the design memo + feasibility spike: the S3.2 refutation of draft eq:Ncross, the corrected `L_c = A⁻¹ + B + B·A⁻¹`, the frozen statement (§2), the block-by-block route (§3) |
| NC2 | `NpcJet/Defs.lean` | the word `npcWord`, the Gate-E marking, `lcOp`/`npcQ0`, and the Heisenberg-slice calculus (`sliceElt_mul/inv/sq/conj/comm`, the `y^k` power law) |
| NC3 | `NpcJet/Omega.lean` | the two reduction rules: `ω₂` on pro-odd elements (rule 1) and the vanishing orbit norm on `V^u = 0` (rule 2), plus the `η̂`-power vocabulary |
| NC4 | `NpcJet/Seams.lean` | the per-block evaluation theorems `δ₀`/`D`/`E`/boundary/head — where the three inverse conjugators of the corrected `L_c` become visible |
| NC5 | `NpcJet/Main.lean` | the `h = 0` headline `npc_cross_operators`, the packet bridge `hVu_of_simple`, the discrepancy display (errata item 5) and the `(α, r, η)` pin |
| NC6 | this file | the handle tail `H_h` and the `handlesProd` reading (the concrete carrier follows) |

## What WNP-c still owes (memo risk 5)

`npc_cross_operators` and its handled form say the jet **is** `Q₀ + b_q(c₁, L_c c₀) + tail`.  They
do **not** say the `c₀`–`c₁` pairing is nondegenerate: that needs `L_c = 1 + (1 + A⁻¹)(1 + B)` to
be **invertible on the module at hand**, which genuinely varies with the module (on a module
with `A = B = 1` it is the identity; in general it can degenerate) and belongs with WNP-c's Fox/normal-form clauses, not with the jet identity.  On a
concrete battery module it is a `decide`.  Also still out of scope by design: the three-variable
Gate-D diagnostic form (an offset on the boundary letter `x₂`).

## Axioms

Measured on the built module, **every** declaration in this file prints
`[propext, Classical.choice, Quot.sound]` — std-3.  No census axiom is cited and none is needed
(memo §9); census stays at 11.
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

end GQ2.Dyadic.NpcJet
