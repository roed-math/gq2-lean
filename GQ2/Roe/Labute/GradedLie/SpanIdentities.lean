/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.SpanFoundation

/-!
# GL-A: transport identities for the span induction

Design record: `docs/orchestration/span-gradedlie-plan.md` §2.3, §3 (GL-A).
**Statements frozen (GL0); fills ticket GL-A.**  Private helpers are the worker's to
add; small private lemmas from `StageLemma.lean` may be restated binder-for-binder
(house precedent) but this file must NOT import `StageLemma`.

The core is the **transport identity** `d̄(w)² = d̄(w²)` (both shapes) for
modifications one level deeper (`w i ∈ λ_{k-2}`-image), valid for `k ≥ 4`; the single
place the threshold enters is `(commP u g)² = commP (u²) g`, whose correction
`⁅⁅u,g⁆,u⁆ ∈ [λ_{k-1}, λ_{k-2}] ⊆ λ_{2k-3}` dies in `Q_{k+1}` exactly when `k ≥ 4`
(machine-validated at k = 4, 5, 6 — memo §5).

Everything is stated for generic pro-2 `G` (the instance pack of the tower API);
the consumers instantiate at `freeProTwo`.
-/

namespace GQ2.Roe.Labute

section TransportCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Squaring is multiplicative on `λ_{k-1}`-image elements of `Q_{k+1}`: the
commutator correction lands in `[λ_{k-1}, λ_{k-1}] ⊆ λ_{2k-2}`, trivial for `k ≥ 3`.
Fill: GL-A. -/
theorem sq_mul_of_mem_lambdaImage_pred (k : ℕ) (hk : 3 ≤ k)
    {u v : levelQuot G (k + 1)} (hu : u ∈ lambdaImage G (k - 1) (k + 1))
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (u * v) ^ 2 = u ^ 2 * v ^ 2 := by
  sorry

/-- **The commP-square transport** (the `k ≥ 4` gate of the whole step): for
`u ∈ λ_{k-2}`-image and arbitrary `g`, `(commP u g)² = commP (u²) g` in `Q_{k+1}` —
the correction `⁅⁅u,g⁆,u⁆ ∈ λ_{2k-3}` dies exactly when `2k-3 ≥ k+1`.  Fill: GL-A. -/
theorem commP_sq_of_mem_lambdaImage (k : ℕ) (hk : 4 ≤ k)
    {u : levelQuot G (k + 1)} (g : levelQuot G (k + 1))
    (hu : u ∈ lambdaImage G (k - 2) (k + 1)) :
    commP u g ^ 2 = commP (u ^ 2) g := by
  sorry

/-- **The transport identity, `r₀` shape** (memo §2.3): π of a depth-`(k-1)` defect
word is the depth-`k` defect word at the squared modification.  Slots arbitrary.
Fill: GL-A. -/
theorem dbarWordR0_sq (k : ℕ) (hk : 4 ≤ k) (a s y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 2) (k + 1)) :
    dbarWordR0 a s y w ^ 2 = dbarWordR0 a s y (fun i => w i ^ 2) := by
  sorry

/-- The transport identity, `r₂` shape.  Fill: GL-A. -/
theorem dbarWordR2_sq (k : ℕ) (hk : 4 ≤ k) (s x y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 2) (k + 1)) :
    dbarWordR2 s x y w ^ 2 = dbarWordR2 s x y (fun i => w i ^ 2) := by
  sorry

/-- λ-images lift along `levelProj`: the levelMk-image of the same witness works.
Fill: GL-A (no compactness needed). -/
theorem exists_levelProj_preimage_lambdaImage (j k : ℕ)
    {q : levelQuot G k} (hq : q ∈ lambdaImage G j k) :
    ∃ q' ∈ lambdaImage G j (k + 1), levelProj G k q' = q := by
  sorry

/-- A central-involution factor is invisible to squares: for `ζ ∈ Zₖ`,
`(q·ζ)² = q²`.  Fill: GL-A (from `zLayer_commute`/`zLayer_sq`). -/
theorem sq_mul_zLayer (k : ℕ) {q ζ : levelQuot G (k + 1)} (hζ : ζ ∈ zLayer G k) :
    (q * ζ) ^ 2 = q ^ 2 := by
  sorry

/-- Bracket atoms are multiplicative in the ambient slot (values are central):
`commP v (z₁z₂) = commP v z₁ · commP v z₂` for `v ∈ λ_{k-1}`-image.  Fill: GL-A. -/
theorem commP_mul_right_of_mem (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (z₁ z₂ : levelQuot G (k + 1)) :
    commP v (z₁ * z₂) = commP v z₁ * commP v z₂ := by
  sorry

/-- Bracket atoms invert in the ambient slot.  Fill: GL-A. -/
theorem commP_inv_right_of_mem (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (z : levelQuot G (k + 1)) :
    commP v z⁻¹ = (commP v z)⁻¹ := by
  sorry

end TransportCalculus

/-! ### Single-slot d̄ evaluations and free-quotient generation -/

section SingleSlot

variable {G : Type*} [Group G]

/-- Twisted slot alone, `r₀`: `d̄(v,1,1) = v²·[v,a]`.  Fill: GL-A (simp warm-up). -/
theorem dbarWordR0_single₀ (a s y v : G) :
    dbarWordR0 a s y ![v, 1, 1] = v ^ 2 * commP v a := by
  sorry

/-- First bracket slot alone, `r₀`: `d̄(1,v,1) = [v,y]`.  Fill: GL-A. -/
theorem dbarWordR0_single₁ (a s y v : G) :
    dbarWordR0 a s y ![1, v, 1] = commP v y := by
  sorry

/-- Second bracket slot alone, `r₀`: `d̄(1,1,v) = [v,s]`.  Fill: GL-A. -/
theorem dbarWordR0_single₂ (a s y v : G) :
    dbarWordR0 a s y ![1, 1, v] = commP v s := by
  sorry

/-- Twisted slot alone, `r₂`: `d̄(1,1,v) = v²·[v,y]`.  Fill: GL-A. -/
theorem dbarWordR2_single₂ (s x y v : G) :
    dbarWordR2 s x y ![1, 1, v] = v ^ 2 * commP v y := by
  sorry

/-- First bracket slot alone, `r₂`: `d̄(v,1,1) = [v,x]`.  Fill: GL-A. -/
theorem dbarWordR2_single₀ (s x y v : G) :
    dbarWordR2 s x y ![v, 1, 1] = commP v x := by
  sorry

/-- Second bracket slot alone, `r₂`: `d̄(1,v,1) = [v,s]`.  Fill: GL-A. -/
theorem dbarWordR2_single₁ (s x y v : G) :
    dbarWordR2 s x y ![1, v, 1] = commP v s := by
  sorry

end SingleSlot

/-- **The free level quotients are generated by the marked classes** (plain subgroup
closure — the quotient is finite discrete): push `topGen_freeProTwo` through `levelMk`
via `map_topologicalClosure_eq_of_discrete` + `MonoidHom.map_closure`.  Fill: GL-A. -/
theorem closure_levelMk_freeGen (m : ℕ) :
    Subgroup.closure
      (Set.range fun i => levelMk (freeProTwo : Type) m (freeGen i)) = ⊤ := by
  sorry

end GQ2.Roe.Labute
