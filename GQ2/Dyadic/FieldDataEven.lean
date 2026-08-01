/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.FieldData

/-!
# Dyadic campaign, ticket FD2: the even-degree cup-form normal form

The `n` even half of packet Def. 9.1 item (5).  FD1 (`GQ2/Dyadic/FieldData.lean`) proved
`diag_eq_one_iff_odd`: for a nondegenerate `𝔽₂` cup–Bockstein form the anisotropy `b e e = 1` of
the Labute vector holds **iff** `dim W` is odd.  At `W = H¹(G_K,𝔽₂)` of dimension `n + 2` that is
`n` odd, which is the type-`L` row.  Every `M`/`N` row has `n = 2 + 2h`, lands on the other side
of the iff with `b e e = 0`, and WL-c's `⟨1⟩ ⊥ ker d` splitting simply does not apply.  This file
is the even-degree analogue.

## The head

With `b e e = 0` the vector `e` is isotropic, so no `⟨1⟩` can be split off along it.  The fix is
one line of linear algebra: pick **any** `f` with `b f f = 1` — one exists as soon as `e ≠ 0`,
since `b e w = b w w` and nondegeneracy — and take the plane `⟨f, e⟩`.  Its Gram is forced:

```
b f f = 1,   b f e = b e f = b f f = 1,   b e e = 0        i.e.   [[1,1],[1,0]]
```

the `b f e = 1` entry being the Labute identity itself, not a choice.  So the head needs no basis
search and no Witt-style argument: it is *the same plane* for every admissible `f`.  On the
complement `(f,e)^⊥` the form is **alternating for free** — `b u u = b e u = 0` there is the
second defining clause of the complement — hence symplectic, and WL-c's `exists_symplectic_equiv`
finishes exactly as in the odd case.

`headGram` is `[[1,1],[1,0]]`, and that is deliberate: it is on the nose the head of MC2's
relator side for both even rows (`mRelWord_centLift_fib`, `nRelWord_centLift_fib` in
`GQ2/Dyadic/MarkedCore/Cores.lean` — `κ(m₀,m₀) + (κ(m₀,m₁) + κ(m₁,m₀))` followed by the
`(m₂,m₃)` plane and the `h` handles, i.e. `[[1,1],[1,0]] ⊥ H^{⊥(h+1)}` at rank `n + 2`).  The
two sides of item (5) therefore meet on the same normal form for `M`/`N` as they already do for
`L`.  `headGram_eq_diag` records the isometry with `⟨1⟩ ⊥ ⟨1⟩` for readers who expect the
diagonal shape; the `[[1,1],[1,0]]` presentation is the one exported.

## The dichotomy, and which branch the campaign is in

`e ≠ 0` is a genuine hypothesis, not a formality: at `e = 0` the form is alternating outright and
the normal form is `H^{⊥m}` with **no** head (`exists_cupForm_normalForm_alternating`).  Both
branches are delivered.  At `W = H¹(G_K,𝔽₂)` the Labute vector is `κ_K = [−1]`, so

* `κ_K = 0 ⟺ −1 ∈ (K^×)²  ⟺  i ∈ K` (`kappaK_eq_zero_iff`, from the Kummer kernel), and
* the campaign's **standing hypothesis is that `K(i)/K` is ramified** (packet Prop. 8.1
  `prop:sign-excluded`; `GQ2/Dyadic/Parameters.lean:550`), which forces `i ∉ K`.

So every `M`/`N` row is in the `κ_K ≠ 0` branch and gets the rank-2 head.  The alternating
branch is kept because the splitting theorem is stated for a general `W` and because nothing in
`GQ2/Dyadic/` currently *derives* `κ_K ≠ 0` from the ramified-`i` binder — supplying that
implication is the assembler's step, and `kappaK_eq_zero_iff` is the interface for it.

⚠ Do not read `κ_K ≠ 0` off the row parameter `q_K`.  `FieldParameters.qK` is the **residue**
cardinality `2^f` (`GQ2/Dyadic/Parameters.lean:85`); it is unrelated to `μ_{2^∞}(K)`.  `ℚ₂(√5)`
has `q_K = 4` in that sense and still has `i ∉ K`.  This is the same conflation FD1's erratum
flagged in `Certificates/L.lean`.

## Statement shapes for AS1

The capstone `exists_cupFormK_normalForm_even K h (hn : Module.finrank ℚ_[2] K = 2*h+2)
(hκ : kappaK K ≠ 0)` is the twin of FD1's `exists_cupFormK_normalForm`, with the hyperbolic
count **pinned by the same counting argument**: `#H¹ = 2^(n+2) = 2^(2h+4)` against
`4 · 4^m = 2^(2m+2)` gives `m = h + 1`, so the form is `[[1,1],[1,0]] ⊥ H^{⊥(h+1)}` at rank
`n + 2` — matching MC2's relator count `h + 1` (the `(m₂,m₃)` plane plus `h` handles).  In the
alternating branch the same count gives `H^{⊥(h+2)}`.  `exists_cupFormK_normalForm_of_even` is
the branch-free disjunction for assemblers that do not want to case on `κ_K`.

## Implementation notes

A leaf: nothing imports this file, and `GQ2/Dyadic/FieldData.lean` is untouched.  Not
`module`-style (it imports the plain-import `FieldData`).  No new instances.  No
`native_decide`; every `decide` is a kernel `decide` over `𝔽₂ × 𝔽₂` or `𝔽₂ × 𝔽₂ × 𝔽₂` (at most
64 cases) — the `headGram` pins of §1.1 and the six `headDiagEquiv` field obligations.

## Axiom state

Audited by `#print axioms` on all 29 named declarations, run in a scratch file, not committed.
**No new axioms**: every declaration prints a subset of std-3 ∪ {B6, B7, B11a} — exactly the set
FD1 used, and no more — so the census stays at eleven.  Zero `sorryAx`, zero `native_decide`,
zero `Lean.ofReduceBool`.  The split is 25 / 4:

* exactly `[propext, Classical.choice, Quot.sound]` — **all** of §§1–3, i.e. the entire general
  linear-algebra layer (`headGram` and its five pins, `headDiagEquiv`, `headGram_eq_diag`,
  `exists_diag_eq_one`, `headPerp`, `headProj_mem`, `isSymplectic_headPerp`, `headSplitEquiv`,
  `headSplit_gram`, **`exists_cupForm_normalForm_even`**, `exists_headGram_normalForm`,
  `isSymplecticFp2_of_labute_eq_zero`, `exists_cupForm_normalForm_alternating`) together with
  `kappaK_eq_zero_iff` — the Kummer kernel `exists_sq_of_kummerClassK_eq_zero` and its converse
  are theorems, not axioms;
* std-3 + **B6** `tateDualityAt` + **B7** `absGalQ2_localEulerCharacteristic` + **B11a**
  `hilbertSymbol_normCriterion_finiteDyadic` — the four `H¹` declarations of §4 that consume
  FD1's facts: `cupFormK_kappa_self_zero`, **`exists_cupFormK_normalForm_even`**,
  `exists_cupFormK_normalForm_even_alternating`, `exists_cupFormK_normalForm_of_even`.

No B3c/B5-K/B8/B9/B10-K enters through any import chain.  Note in particular that the *splitting
theorem itself* is axiom-free beyond std-3, exactly as WL-c's odd-case twin is: **the even case
needs no arithmetic input the odd case did not have** — only the opposite value of the same `𝔽₂`
equation on `e`, plus `e ≠ 0`.
-/

namespace GQ2.Dyadic.FieldDataEven

open ContCoh GQ2 Certificates.LSqStokes FieldData

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The rank-2 non-alternating head

Over `𝔽₂` a nondegenerate symmetric bilinear form of rank two is either the hyperbolic plane
`[[0,1],[1,0]]` (alternating) or the unique non-alternating class, presented here as
`[[1,1],[1,0]]`.  That is the presentation MC2's even rows land on, so it is the one exported;
`headGram_eq_diag` gives the isometry with the diagonal presentation `⟨1⟩ ⊥ ⟨1⟩`. -/

section Head

/-- **The rank-2 non-alternating Gram** `[[1,1],[1,0]]` on `𝔽₂ × 𝔽₂`: coordinate `0` is the
anisotropic vector `f` (`b f f = 1`) and coordinate `1` is the isotropic Labute vector `e`
(`b e e = 0`), with `b f e = 1` forced by the Labute identity.

This is the head of MC2's even-row relator Gram on the nose: `mRelWord_centLift_fib` and
`nRelWord_centLift_fib` both open with `κ(m₀,m₀) + (κ(m₀,m₁) + κ(m₁,m₀))`. -/
def headGram (p r : ZMod 2 × ZMod 2) : ZMod 2 := p.1 * r.1 + (p.1 * r.2 + p.2 * r.1)

@[simp] theorem headGram_mk (a c a' c' : ZMod 2) :
    headGram (a, c) (a', c') = a * a' + (a * c' + c * a') := rfl

theorem headGram_comm (p r : ZMod 2 × ZMod 2) : headGram p r = headGram r p := by
  simp only [headGram]; ring

/-- The head is **not** alternating: its diagonal is the first coordinate, the linear functional
whose representing vector is the second basis vector. -/
theorem headGram_self (p : ZMod 2 × ZMod 2) : headGram p p = p.1 := by
  revert p; decide

/-- The diagonal of the head is represented by `(0,1)` — the head's own Labute vector, isotropic
as it must be. -/
theorem headGram_labute (p : ZMod 2 × ZMod 2) : headGram (0, 1) p = headGram p p := by
  revert p; decide

/-! ### §1.1 The head, pinned

Four kernel `decide`s that identify `headGram` as an *object* rather than as a formula: it is a
cup–Bockstein form, it is nondegenerate, it is **not** alternating (hence not a hyperbolic
plane), and its Gram is `[[1,1],[1,0]]` — the upper-left block of MC2's published `G_M = G_N`. -/

/-- **The head's Gram matrix**, pinned against MC2's `G_M`/`G_N` (`docs/dyadic/mc-design.md`:
`[[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]`, whose upper-left `2×2` block this is). -/
theorem headGram_matrix :
    headGram (1, 0) (1, 0) = 1 ∧ headGram (1, 0) (0, 1) = 1
      ∧ headGram (0, 1) (1, 0) = 1 ∧ headGram (0, 1) (0, 1) = 0 := by decide

/-- The head is a cup–Bockstein form. -/
theorem isCupFormFp2_headGram : IsCupFormFp2 headGram where
  symm := by decide
  add_left := by decide

/-- The head is nondegenerate. -/
theorem nondegFp2_headGram : NondegFp2 headGram := by
  show ∀ v : ZMod 2 × ZMod 2, (∀ w, headGram v w = 0) → v = 0
  decide

/-- **The head is not alternating**, hence not a hyperbolic plane.  This is why the even case is
a genuine dichotomy: `[[1,1],[1,0]] ⊥ H^{⊥(h+1)}` and `H^{⊥(h+2)}` have the same rank `n + 2`
and are *not* isometric, so no single normal form covers even degree the way `⟨1⟩ ⊥ H^{⊥m}`
covers odd degree. -/
theorem headGram_not_alternating : ¬ ∀ p : ZMod 2 × ZMod 2, headGram p p = 0 := by decide

/-- The change of basis `(a, c) ↦ (a + c, c)`, i.e. `(f, e) ↦ (f, e + f)`, an involution over
`𝔽₂`. -/
def headDiagEquiv : (ZMod 2 × ZMod 2) ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 where
  toFun p := (p.1 + p.2, p.2)
  map_add' p q := by revert p q; decide
  map_smul' c p := by revert c p; decide
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by revert p; decide
  right_inv p := by revert p; decide

@[simp] theorem headDiagEquiv_apply (p : ZMod 2 × ZMod 2) :
    headDiagEquiv p = (p.1 + p.2, p.2) := rfl

/-- **The head is `⟨1⟩ ⊥ ⟨1⟩`**, in the basis `(f, e + f)`: both vectors are anisotropic and
they are orthogonal (`b f (e+f) = b f e + b f f = 1 + 1 = 0`).  Recorded for readers who expect
the diagonal presentation; the `[[1,1],[1,0]]` one is what the relator side uses. -/
theorem headGram_eq_diag (p r : ZMod 2 × ZMod 2) :
    headGram p r = (headDiagEquiv p).1 * (headDiagEquiv r).1
      + (headDiagEquiv p).2 * (headDiagEquiv r).2 := by
  simp only [headDiagEquiv_apply]
  revert p r; decide

end Head

/-! ## §2 The head-plane splitting

The even-degree analogue of WL-c's `cupSplitEquiv`/`exists_cupForm_normalForm`.  The plane split
off is `⟨f, e⟩` rather than `⟨e⟩`, and the complement is alternating because membership in it
*is* the equation `b e u = 0`, which by the Labute identity is `b u u = 0`.  Everything else is
WL-c's, unchanged: `exists_symplectic_equiv` handles the residue. -/

section Splitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {b : W → W → ZMod 2} {e f : W}

omit [Module (ZMod 2) W] in
/-- **An anisotropic vector exists as soon as the Labute vector is nonzero.**  If the diagonal
`d w = b w w` were identically zero then `b e w = 0` for every `w`, so `e = 0` by nondegeneracy.
This is the only place `e ≠ 0` is used, and it is what the head needs. -/
theorem exists_diag_eq_one (hnd : NondegFp2 b) (he : ∀ w, b e w = b w w) (hne : e ≠ 0) :
    ∃ f : W, b f f = 1 := by
  by_contra hcon
  push Not at hcon
  refine hne (hnd e fun w => ?_)
  rw [he w]
  rcases ZMod.eq_zero_or_eq_one (b w w) with h | h
  · exact h
  · exact absurd h (hcon w)

/-- The orthogonal complement of the head plane `⟨f, e⟩`, as a submodule. -/
def headPerp (b : W → W → ZMod 2) (hb : IsCupFormFp2 b) (f e : W) : Submodule (ZMod 2) W where
  carrier := {u | b f u = 0 ∧ b e u = 0}
  add_mem' := fun hx hy =>
    ⟨by rw [hb.add_right, hx.1, hy.1, add_zero], by rw [hb.add_right, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨hb.zero_right f, hb.zero_right e⟩
  smul_mem' := fun c _ hx =>
    ⟨by rw [hb.smul_right, hx.1, mul_zero], by rw [hb.smul_right, hx.2, mul_zero]⟩

@[simp] theorem mem_headPerp {hb : IsCupFormFp2 b} {u : W} :
    u ∈ headPerp b hb f e ↔ b f u = 0 ∧ b e u = 0 := Iff.rfl

omit [AddCommGroup W] [Module (ZMod 2) W] in
/-- The Labute identity fixes the off-diagonal entry of the head: `b e f = b f f = 1`. -/
theorem head_offDiag (he : ∀ w, b e w = b w w) (hf : b f f = 1) : b e f = 1 := by
  rw [he f]; exact hf

/-- The projection onto the head complement, `u ↦ u + (b e u)·f + (b f u + b e u)·e`. -/
theorem headProj_mem (hb : IsCupFormFp2 b) (he : ∀ w, b e w = b w w) (he0 : b e e = 0)
    (hf : b f f = 1) (u : W) :
    u + (b e u) • f + (b f u + b e u) • e ∈ headPerp b hb f e := by
  have hef : b e f = 1 := head_offDiag he hf
  have hfe : b f e = 1 := by rw [hb.symm]; exact hef
  constructor
  · rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hf, hfe, mul_one, mul_one]
    exact CharTwo.add_self_eq_zero _
  · rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hef, he0, mul_one, mul_zero,
      add_zero]
    exact CharTwo.add_self_eq_zero _

/-- **The head complement is symplectic.**  Alternating is immediate — membership is the pair of
equations `b f u = 0`, `b e u = 0`, and the second one *is* `b u u = 0` by the Labute identity —
and nondegeneracy is the usual projection argument.  Contrast the odd case, where alternating on
`ker d` holds by construction and nondegeneracy needs `b e e = 1`. -/
theorem isSymplectic_headPerp (hb : IsCupFormFp2 b) (hnd : NondegFp2 b)
    (he : ∀ w, b e w = b w w) (he0 : b e e = 0) (hf : b f f = 1) :
    IsSymplecticFp2 (fun x y : headPerp b hb f e => b (x : W) (y : W)) where
  add_left u v w := hb.add_left _ _ _
  add_right u v w := hb.add_right _ _ _
  alt u := by rw [← he]; exact u.2.2
  nondeg := by
    intro u hu
    have huf : b (u : W) f = 0 := by rw [hb.symm]; exact u.2.1
    have hue : b (u : W) e = 0 := by rw [hb.symm]; exact u.2.2
    have hu0 : (u : W) = 0 := by
      refine hnd _ fun y => ?_
      have hy : (y + (b e y) • f + (b f y + b e y) • e : W) ∈ headPerp b hb f e :=
        headProj_mem hb he he0 hf y
      have hval : b (u : W) (y + (b e y) • f + (b f y + b e y) • e) = 0 := hu ⟨_, hy⟩
      rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, huf, hue, mul_zero,
        mul_zero, add_zero, add_zero] at hval
      exact hval
    exact Subtype.ext hu0

/-- **The head splitting** `W ≃ₗ (𝔽₂ × 𝔽₂) × (f,e)^⊥`, the even-degree twin of WL-c's
`cupSplitEquiv`.  The two head coordinates of `u` are `b e u` (its `f`-component) and
`b f u + b e u` (its `e`-component). -/
noncomputable def headSplitEquiv (hb : IsCupFormFp2 b) (he : ∀ w, b e w = b w w)
    (he0 : b e e = 0) (hf : b f f = 1) :
    W ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × headPerp b hb f e where
  toFun u := ((b e u, b f u + b e u),
    ⟨u + (b e u) • f + (b f u + b e u) • e, headProj_mem hb he he0 hf u⟩)
  map_add' u u' := by
    refine Prod.ext (Prod.ext (hb.add_right _ _ _) ?_) (Subtype.ext ?_)
    · show b f (u + u') + b e (u + u') = (b f u + b e u) + (b f u' + b e u')
      rw [hb.add_right, hb.add_right]; ring
    · show u + u' + (b e (u + u')) • f + (b f (u + u') + b e (u + u')) • e
        = (u + (b e u) • f + (b f u + b e u) • e) + (u' + (b e u') • f + (b f u' + b e u') • e)
      rw [hb.add_right, hb.add_right, add_smul, show b f u + b f u' + (b e u + b e u')
        = (b f u + b e u) + (b f u' + b e u') from by ring, add_smul]
      abel
  map_smul' c u := by
    refine Prod.ext (Prod.ext (hb.smul_right _ _ _) ?_) (Subtype.ext ?_)
    · show b f (c • u) + b e (c • u) = c * (b f u + b e u)
      rw [hb.smul_right, hb.smul_right, mul_add]
    · show c • u + (b e (c • u)) • f + (b f (c • u) + b e (c • u)) • e
        = c • (u + (b e u) • f + (b f u + b e u) • e)
      rw [hb.smul_right, hb.smul_right, ← mul_add, smul_add, smul_add, mul_smul, mul_smul]
  invFun p := p.1.1 • f + p.1.2 • e + (p.2 : W)
  left_inv u := by
    have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
    show (b e u) • f + (b f u + b e u) • e + (u + (b e u) • f + (b f u + b e u) • e) = u
    calc (b e u) • f + (b f u + b e u) • e + (u + (b e u) • f + (b f u + b e u) • e)
        = u + ((b e u) • f + (b e u) • f)
            + ((b f u + b e u) • e + (b f u + b e u) • e) := by abel
      _ = u := by rw [h2, h2, add_zero, add_zero]
  right_inv p := by
    have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
    have hef : b e f = 1 := head_offDiag he hf
    have hfe : b f e = 1 := by rw [hb.symm]; exact hef
    have hbe : b e (p.1.1 • f + p.1.2 • e + (p.2 : W)) = p.1.1 := by
      rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hef, he0, p.2.2.2,
        mul_one, mul_zero, add_zero, add_zero]
    have hbf : b f (p.1.1 • f + p.1.2 • e + (p.2 : W)) = p.1.1 + p.1.2 := by
      rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hf, hfe, p.2.2.1,
        mul_one, mul_one, add_zero]
    refine Prod.ext (Prod.ext hbe ?_) (Subtype.ext ?_)
    · show b f (p.1.1 • f + p.1.2 • e + (p.2 : W))
          + b e (p.1.1 • f + p.1.2 • e + (p.2 : W)) = p.1.2
      rw [hbe, hbf]
      calc p.1.1 + p.1.2 + p.1.1 = p.1.2 + (p.1.1 + p.1.1) := by ring
        _ = p.1.2 := by rw [CharTwo.add_self_eq_zero, add_zero]
    · show p.1.1 • f + p.1.2 • e + (p.2 : W)
          + (b e (p.1.1 • f + p.1.2 • e + (p.2 : W))) • f
          + (b f (p.1.1 • f + p.1.2 • e + (p.2 : W))
              + b e (p.1.1 • f + p.1.2 • e + (p.2 : W))) • e = (p.2 : W)
      rw [hbe, hbf, show p.1.1 + p.1.2 + p.1.1 = p.1.2 from by
        rw [show p.1.1 + p.1.2 + p.1.1 = p.1.2 + (p.1.1 + p.1.1) from by ring,
          CharTwo.add_self_eq_zero, add_zero]]
      calc p.1.1 • f + p.1.2 • e + (p.2 : W) + p.1.1 • f + p.1.2 • e
          = (p.2 : W) + (p.1.1 • f + p.1.1 • f) + (p.1.2 • e + p.1.2 • e) := by abel
        _ = (p.2 : W) := by rw [h2, h2, add_zero, add_zero]

/-- **The `[[1,1],[1,0]] ⊥ (rest)` Gram identity** along the head splitting. -/
theorem headSplit_gram (hb : IsCupFormFp2 b) (he : ∀ w, b e w = b w w) (he0 : b e e = 0)
    (hf : b f f = 1) (p r : ZMod 2 × ZMod 2) (k k' : headPerp b hb f e) :
    b (p.1 • f + p.2 • e + (k : W)) (r.1 • f + r.2 • e + (k' : W))
      = headGram p r + b (k : W) (k' : W) := by
  have hef : b e f = 1 := head_offDiag he hf
  have hfe : b f e = 1 := by rw [hb.symm]; exact hef
  have hkf : b (k : W) f = 0 := by rw [hb.symm]; exact k.2.1
  have hke : b (k : W) e = 0 := by rw [hb.symm]; exact k.2.2
  have hyf : b f (r.1 • f + r.2 • e + (k' : W)) = r.1 + r.2 := by
    rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hf, hfe, k'.2.1,
      mul_one, mul_one, add_zero]
  have hye : b e (r.1 • f + r.2 • e + (k' : W)) = r.1 := by
    rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hef, he0, k'.2.2,
      mul_one, mul_zero, add_zero, add_zero]
  have hyk : b (k : W) (r.1 • f + r.2 • e + (k' : W)) = b (k : W) (k' : W) := by
    rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hkf, hke,
      mul_zero, mul_zero, add_zero, zero_add]
  rw [hb.add_left, hb.add_left, hb.smul_left, hb.smul_left, hyf, hye, hyk]
  simp only [headGram]
  ring

/-- **The even-degree normal form.**  A nondegenerate `𝔽₂` cup–Bockstein form whose Labute vector
`e` is *isotropic* but *nonzero* is isometric to `[[1,1],[1,0]] ⊥ H^{⊥m}`.

This is the `b e e = 0` twin of WL-c's `exists_cupForm_normalForm`, and it consumes exactly the
same inputs: `IsCupFormFp2`, `NondegFp2`, the Labute identity, and one `𝔽₂` equation on `e` —
with `= 0` where the odd case has `= 1`, plus `e ≠ 0` (vacuous in the odd case, where
`b e e = 1` already forces it).  **No arithmetic input beyond FD1's is used.** -/
theorem exists_cupForm_normalForm_even [Finite W] (hb : IsCupFormFp2 b) (hnd : NondegFp2 b)
    (he : ∀ w, b e w = b w w) (he0 : b e e = 0) (hne : e ≠ 0) :
    ∃ (m : ℕ) (φ : W ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × (Fin m → ZMod 2 × ZMod 2)),
      ∀ x y, b x y = headGram (φ x).1 (φ y).1 + hypGram (φ x).2 (φ y).2 := by
  obtain ⟨f, hf⟩ := exists_diag_eq_one hnd he hne
  obtain ⟨m, ψ, hψ⟩ :=
    exists_symplectic_equiv (fun x y : headPerp b hb f e => b (x : W) (y : W))
      (isSymplectic_headPerp hb hnd he he0 hf)
  set φ₀ := headSplitEquiv hb he he0 hf with hφ₀
  refine ⟨m, φ₀.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)).prodCongr ψ), fun x y => ?_⟩
  have hx : (φ₀ x).1.1 • f + (φ₀ x).1.2 • e + ((φ₀ x).2 : W) = x := φ₀.left_inv x
  have hy : (φ₀ y).1.1 • f + (φ₀ y).1.2 • e + ((φ₀ y).2 : W) = y := φ₀.left_inv y
  show b x y = headGram (φ₀ x).1 (φ₀ y).1 + hypGram (ψ (φ₀ x).2) (ψ (φ₀ y).2)
  rw [← hψ]
  calc b x y = b ((φ₀ x).1.1 • f + (φ₀ x).1.2 • e + ((φ₀ x).2 : W))
        ((φ₀ y).1.1 • f + (φ₀ y).1.2 • e + ((φ₀ y).2 : W)) := by rw [hx, hy]
    _ = headGram (φ₀ x).1 (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) :=
        headSplit_gram hb he he0 hf _ _ _ _

/-- **Non-vacuity.**  The head is its own smallest instance: `headGram` on `𝔽₂ × 𝔽₂` satisfies
every hypothesis of `exists_cupForm_normalForm_even`, with Labute vector `(0,1)` — nonzero and
isotropic.  So the even branch is inhabited, and (by counting, `#W = 4 = 4 · 4⁰`) its normal form
is the bare head with no hyperbolic part.  A decidable end-to-end check that the hypothesis
shapes compose; the `H¹` capstones of §4 are the same application over a field. -/
theorem exists_headGram_normalForm :
    ∃ (m : ℕ) (φ : (ZMod 2 × ZMod 2) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × (Fin m → ZMod 2 × ZMod 2)),
      ∀ x y, headGram x y = headGram (φ x).1 (φ y).1 + hypGram (φ x).2 (φ y).2 :=
  exists_cupForm_normalForm_even isCupFormFp2_headGram nondegFp2_headGram headGram_labute
    (by decide) (by decide)

/-! ### §2.1 The degenerate branch: a vanishing Labute vector

If `e = 0` the diagonal vanishes identically, the form is alternating outright, and the normal
form is purely hyperbolic — no head at all.  Three lines, but it is a *different* normal form, so
the even case is a genuine dichotomy and not a single statement. -/

omit [Module (ZMod 2) W] in
/-- With `e = 0` the cup form is itself symplectic. -/
theorem isSymplecticFp2_of_labute_eq_zero (hb : IsCupFormFp2 b) (hnd : NondegFp2 b)
    (he : ∀ w, b e w = b w w) (he0 : e = 0) : IsSymplecticFp2 b where
  add_left := hb.add_left
  add_right := hb.add_right
  alt v := by rw [← he v, he0]; exact hb.zero_left v
  nondeg := hnd

/-- **The alternating branch of the even case**: at `e = 0` the form is `H^{⊥m}`. -/
theorem exists_cupForm_normalForm_alternating [Finite W] (hb : IsCupFormFp2 b)
    (hnd : NondegFp2 b) (he : ∀ w, b e w = b w w) (he0 : e = 0) :
    ∃ (m : ℕ) (φ : W ≃ₗ[ZMod 2] (Fin m → ZMod 2 × ZMod 2)),
      ∀ x y, b x y = hypGram (φ x) (φ y) :=
  exists_symplectic_equiv b (isSymplecticFp2_of_labute_eq_zero hb hnd he he0)

end Splitting

/-! ## §3 The even `e`-datum at `K` -/

section EDatum

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- **The even-degree `e`-datum**: `b_K(κ,κ) = 0` when `n = [K:ℚ₂]` is even.  This is the other
side of FD1's `cupFormK_kappa_self_iff`, and like it, it is a parity corollary of facts (i) and
(ii) — not a fresh arithmetic input. -/
theorem cupFormK_kappa_self_zero (hev : Even (Module.finrank ℚ_[2] K)) :
    cupFormK K (kappaK K) (kappaK K) = 0 := by
  rcases ZMod.eq_zero_or_eq_one (cupFormK K (kappaK K) (kappaK K)) with h | h
  · exact h
  · exact absurd ((cupFormK_kappa_self_iff K).mp h) (Nat.not_odd_iff_even.mpr hev)

omit [FiniteDimensional ℚ_[2] ↥K] in
/-- **The Labute vector vanishes exactly when `−1` is a square**, i.e. exactly when `i ∈ K`.
Both halves are theorems in the repo already (`exists_sq_of_kummerClassK_eq_zero` and
`kummerClassK_eq_zero_of_sq`); this packages them at `a = −1`.

This is the interface for the campaign's standing ramified-`i` hypothesis: `K(i)/K` ramified
forces `i ∉ K`, hence `κ_K ≠ 0`, hence the rank-2 head branch below. -/
theorem kappaK_eq_zero_iff : kappaK K = 0 ↔ ∃ w : ↥K, w ^ 2 = -1 := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := exists_sq_of_kummerClassK_eq_zero K (-1) h
    exact ⟨w, by rw [hw]; exact Units.coe_neg_one⟩
  · rintro ⟨w, hw⟩
    exact kummerClassK_eq_zero_of_sq K (-1) w (by rw [hw]; exact Units.coe_neg_one.symm)

end EDatum

/-! ## §4 `hHilb` at the field, even degree

FD1's facts (i) `card_H1_zmodTwo` and (ii) `nondegFp2_cupFormK` are degree-general and are used
here unchanged; §3's `cupFormK_kappa_self_zero` replaces its fact (iii).  The composition is
FD1's, with the counting pin re-run against `4 · 4^m` instead of `2 · 4^m`. -/

section NormalForm

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- **`hHilb` at the field `K`, even degree.**  For `K/ℚ₂` of even degree `n = 2h + 2` with
`i ∉ K` (equivalently `κ_K ≠ 0`), the mod-2 cup form of `H¹(G_K, 𝔽₂)` is isometric to
`[[1,1],[1,0]] ⊥ H^{⊥(h+1)}` at rank `n + 2` — which is exactly MC2's even-row relator Gram
(`mRelWord_centLift_fib` / `nRelWord_centLift_fib`: a `[[1,1],[1,0]]` head on `(m₀,m₁)`, the
hyperbolic `(m₂,m₃)` plane, and `h` handle planes).

Axioms: the standard three, plus **B6** (`tateDualityAt`, through nondegeneracy and `#H² = 2`),
**B7** (`absGalQ2_localEulerCharacteristic`, through the dimension) and **B11a**
(`hilbertSymbol_normCriterion_finiteDyadic`, through the Labute identity) — the same three FD1
used, and no more. -/
theorem exists_cupFormK_normalForm_even (h : ℕ) (hn : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hκ : kappaK K ≠ 0) :
    ∃ φ : H1 ↥(K.fixingSubgroup) (ZMod 2)
        ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × (Fin (h + 1) → ZMod 2 × ZMod 2),
      ∀ x y, cupFormK K x y = headGram (φ x).1 (φ y).1 + hypGram (φ x).2 (φ y).2 := by
  haveI := finite_H1_zmodTwo K
  obtain ⟨m, φ, hφ⟩ :=
    exists_cupForm_normalForm_even (isCupFormFp2_cupFormK K) (nondegFp2_cupFormK K)
      (cupFormK_kappa K) (cupFormK_kappa_self_zero K ⟨h + 1, by omega⟩) hκ
  -- pin `m = h + 1` by counting: `4·4^m = #H¹ = 2^(n+2) = 2^(2h+4)`
  have hm : m = h + 1 := by
    have h1 : Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 4 * 4 ^ m := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
      simp
    have h2 : Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 2 ^ (2 + 2 * m) := by
      rw [h1, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
    have h3 : (2 : ℕ) ^ (2 + 2 * m) = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
      rw [← h2, card_H1_zmodTwo K]
    have h4 := Nat.pow_right_injective (le_refl 2) h3
    omega
  subst hm
  exact ⟨φ, hφ⟩

/-- **`hHilb` at the field `K`, even degree, alternating branch.**  If `i ∈ K` (equivalently
`κ_K = 0`) the cup form is alternating and the normal form is `H^{⊥(h+2)}` with no head.  Outside
the campaign's ramified-`i` standing hypothesis, but the splitting theorem is general and the
count is free. -/
theorem exists_cupFormK_normalForm_even_alternating (h : ℕ)
    (hn : Module.finrank ℚ_[2] K = 2 * h + 2) (hκ : kappaK K = 0) :
    ∃ φ : H1 ↥(K.fixingSubgroup) (ZMod 2) ≃ₗ[ZMod 2] (Fin (h + 2) → ZMod 2 × ZMod 2),
      ∀ x y, cupFormK K x y = hypGram (φ x) (φ y) := by
  haveI := finite_H1_zmodTwo K
  obtain ⟨m, φ, hφ⟩ :=
    exists_cupForm_normalForm_alternating (isCupFormFp2_cupFormK K) (nondegFp2_cupFormK K)
      (cupFormK_kappa K) hκ
  have hm : m = h + 2 := by
    have h1 : Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 4 ^ m := by
      rw [Nat.card_congr φ.toEquiv]
      simp
    have h2 : Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 2 ^ (2 * m) := by
      rw [h1, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have h3 : (2 : ℕ) ^ (2 * m) = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
      rw [← h2, card_H1_zmodTwo K]
    have h4 := Nat.pow_right_injective (le_refl 2) h3
    omega
  subst hm
  exact ⟨φ, hφ⟩

/-- **The branch-free even statement.**  At even degree `n = 2h + 2` the cup form of
`H¹(G_K,𝔽₂)` is either `[[1,1],[1,0]] ⊥ H^{⊥(h+1)}` (the ramified-`i` case, `i ∉ K`, which is
every `M`/`N` row) or `H^{⊥(h+2)}` (`i ∈ K`).  Unlike the odd case there is no single normal
form: the two are not isometric, the first being non-alternating. -/
theorem exists_cupFormK_normalForm_of_even (h : ℕ)
    (hn : Module.finrank ℚ_[2] K = 2 * h + 2) :
    (∃ φ : H1 ↥(K.fixingSubgroup) (ZMod 2)
        ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × (Fin (h + 1) → ZMod 2 × ZMod 2),
      ∀ x y, cupFormK K x y = headGram (φ x).1 (φ y).1 + hypGram (φ x).2 (φ y).2)
    ∨ (∃ φ : H1 ↥(K.fixingSubgroup) (ZMod 2) ≃ₗ[ZMod 2] (Fin (h + 2) → ZMod 2 × ZMod 2),
      ∀ x y, cupFormK K x y = hypGram (φ x) (φ y)) := by
  by_cases hκ : kappaK K = 0
  · exact Or.inr (exists_cupFormK_normalForm_even_alternating K h hn hκ)
  · exact Or.inl (exists_cupFormK_normalForm_even K h hn hκ)

end NormalForm

end GQ2.Dyadic.FieldDataEven
