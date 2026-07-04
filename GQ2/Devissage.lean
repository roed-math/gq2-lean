import GQ2.FoxHeisenberg

/-!
# §5.11 dévissage: two-out-of-three for `IsSelfDual` along a module SES  (ticket P-13e)

`lemma_5_11` (`GQ2/FoxHeisenberg.lean`) is the two-out-of-three property of the `IsSelfDual`
package along a short exact sequence `0 → A' → A → A'' → 0` of finite elementary `𝔽₂[C]`-modules.
The proof device is the **long exact cohomology sequence** of the word complex
`C(A) : A --d⁰--> A⁴ --d¹--> A²` (displays (30)/(49)/(50)): the degreewise functors `A ↦ A`,
`A ↦ Fin 4 → A`, `A ↦ A × A` are **exact** (identity / finite products), and `d⁰`, `d¹` are
**natural** in the coefficient module (this file's `d0_natural`/`d1_natural`), so the module SES
induces a short exact sequence of complexes, whence a nine-term LES

  `0 → H⁰(A') → H⁰(A) → H⁰(A'') → H¹(A') → H¹(A) → H¹(A'') → H²(A') → H²(A) → H²(A'') → 0`.

A key simplification: **rank-nullity on `d¹`** gives `dim Z¹w = 2·dim A + dim H²w` for *every* `A`
(`Z1w = ker d¹`, `H2w = coker d¹`), so the two card clauses of `IsSelfDual` are **equivalent** —
the card part reduces to the single clause `#H²w(A) = #fixedPts(ElemDual A)`.

This file builds that infrastructure bottom-up.  `Ax = ∅`; heavy work lives here, `lemma_5_11`
gets a one-line splice in `FoxHeisenberg.lean`.
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## Naturality of the word complex under coefficient maps

The maps `d⁰`, `d¹` commute with a `C`-equivariant additive map `φ : A →+ B` (applied degreewise),
so `φ` induces a chain map `C(A) → C(B)`.  These are the arrows of the SES of complexes. -/

section Naturality

variable {A B : Type*} [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B]

/-- **`d⁰` is natural**: `d⁰_B(φ v) = φ ∘ d⁰_A(v)` for a `C`-equivariant `φ`. -/
theorem d0_natural (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (v : A) :
    d0 t (φ v) = fun i => φ (d0 t v i) := by
  funext i
  fin_cases i <;> simp [d0, hφ]

/-- **`d¹` is natural**: `d¹_B(φ ∘ x) = (φ, φ) ∘ d¹_A(x)` for a `C`-equivariant `φ` — the finite
Fox rule pushed through the coefficient map (`WordLift.map φ` + `Marking.map_{tame,wild}Value`). -/
theorem d1_natural [Finite A] [Finite B] [Finite C] (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (x : Fin 4 → A) :
    d1Fun t (fun i => φ (x i)) = (φ (d1Fun t x).1, φ (d1Fun t x).2) := by
  set Φ := WordLift.map (C := C) φ hφ with hΦ
  have hL : (liftMarking t x).map Φ = liftMarking t (fun i => φ (x i)) := rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (fun i => φ (x i))).tameValue.u = φ ((liftMarking t x).tameValue.u)
    rw [← hL, Marking.map_tameValue, WordLift.map_u]
  · show (liftMarking t (fun i => φ (x i))).wildValue.u = φ ((liftMarking t x).wildValue.u)
    rw [← hL, Marking.map_wildValue, WordLift.map_u]

end Naturality

end GQ2.FoxH
