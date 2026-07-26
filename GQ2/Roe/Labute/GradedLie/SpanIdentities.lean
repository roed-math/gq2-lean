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

/-! ### Pure group identities (restated from `StageLemma.lean`)

`StageLemma.lean` sits *above* this file in the import graph (it imports
`GradedLie.SpanAssembly`), so its private calculus is restated here binder-for-binder
rather than imported — the house precedent recorded in the design memo §3. -/

/-- The fundamental move rule (pure group identity, no hypotheses).  Restated from
`StageLemma.lean`. -/
private theorem mul_swap_commP {H : Type*} [Group H] (v a : H) :
    v * a = a * v * commP v a := by simp only [commP]; group

/-- Left expansion of `commP` (pure group identity).  Restated from `StageLemma.lean`. -/
private theorem commP_mul_left {H : Type*} [Group H] (x u g : H) :
    commP (x * u) g = u⁻¹ * commP x g * u * commP u g := by simp only [commP]; group

/-- Right expansion of `commP` (pure group identity).  Restated from `StageLemma.lean`. -/
private theorem commP_mul_right {H : Type*} [Group H] (x g v : H) :
    commP x (g * v) = commP x v * (v⁻¹ * commP x g * v) := by simp only [commP]; group

/-- A vanishing `commP` is exactly a trivial conjugation.  Restated from
`StageLemma.lean`. -/
private theorem conj_eq_self_of_commP_eq_one {H : Type*} [Group H] {x u : H}
    (h : commP x u = 1) : u⁻¹ * x * u = x := by
  simp only [commP] at h
  calc u⁻¹ * x * u = x * (x⁻¹ * u⁻¹ * x * u) := by group
    _ = x := by rw [h, mul_one]

/-- A trivial first slot kills `commP`. -/
private theorem commP_one_left {H : Type*} [Group H] (g : H) : commP (1 : H) g = 1 := by
  simp only [commP]; group

section TransportCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Layer calculus (restated from `StageLemma.lean`, plus two `λⱼ`-graded variants) -/

/-- `λₘ` dies in `Qₘ` (the top layer image is trivial).  Restated from
`StageLemma.lean`. -/
private theorem lambdaImage_self (m : ℕ) : lambdaImage G m m = ⊥ := by
  rw [lambdaImage, Subgroup.map_eq_bot_iff, levelMk, QuotientGroup.ker_mk']

/-- `λ₁ = ⊤` survives to every level quotient.  Restated from `StageLemma.lean`. -/
private theorem lambdaImage_one_eq_top (m : ℕ) : lambdaImage G 1 m = ⊤ := by
  rw [lambdaImage, twoCentralSeries_one]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G m)

/-- The layer images are antitone in the depth index.  Restated from
`StageLemma.lean`. -/
private theorem lambdaImage_le_of_le {j j' m : ℕ} (h : j ≤ j') :
    lambdaImage G j' m ≤ lambdaImage G j m :=
  Subgroup.map_mono (twoCentralSeries_antitone G h)

open scoped commutatorElement in
/-- The λ-grading lemma, transported to the level quotients and to the repo commutator
convention: `commP λₐ λᵦ ⊆ λ_{a+b}` in `Qₘ`.  Restated from `StageLemma.lean`. -/
private theorem commP_mem_lambdaImage_add {a b m : ℕ} {v g : levelQuot G m}
    (hv : v ∈ lambdaImage G a m) (hg : g ∈ lambdaImage G b m) :
    commP v g ∈ lambdaImage G (a + b) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨commP x y, ?_, by simp only [commP, map_mul, map_inv]⟩
  have h : commP x y = ⁅x⁻¹, y⁻¹⁆ := by simp only [commP, commutatorElement_def, inv_inv]
  rw [h]
  exact commutator_mem_twoCentralSeries_add G ((twoCentralSeries G a).inv_mem hx)
    ((twoCentralSeries G b).inv_mem hy)

/-- Squaring pushes a layer image one level deeper (`λⱼ² ⊆ λ_{j+1}`). -/
private theorem sq_mem_lambdaImage_succ {j m : ℕ} {v : levelQuot G m}
    (hv : v ∈ lambdaImage G j m) : v ^ 2 ∈ lambdaImage G (j + 1) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨x ^ 2, sq_mem_twoCentralSeries_succ G hx, by rw [map_pow]⟩

/-- Bracketing with an arbitrary ambient element pushes a layer image one level deeper
(`λ₁ = ⊤` fed into `commP_mem_lambdaImage_add`). -/
private theorem commP_mem_lambdaImage_succ {j m : ℕ} {v : levelQuot G m}
    (hv : v ∈ lambdaImage G j m) (g : levelQuot G m) :
    commP v g ∈ lambdaImage G (j + 1) m :=
  commP_mem_lambdaImage_add hv (by rw [lambdaImage_one_eq_top]; trivial)

/-- Every `commP` of a `λ_{k-1}`-modification is central.  Restated from
`StageLemma.lean`. -/
private theorem commP_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (g : levelQuot G (k + 1)) :
    commP v g ∈ zLayer G k := by
  have h := commP_mem_lambdaImage_succ hv g
  rwa [show k - 1 + 1 = k by omega] at h

/-- Two `λ_{k-1}`-modifications commute: `[λ_{k-1}, λ_{k-1}] ⊆ λ_{2k-2} ⊆ λ_{k+1} = 1`
(this is exactly where `k ≥ 3` enters).  Restated from `StageLemma.lean`. -/
private theorem commP_lambdaImage_eq_one (k : ℕ) (hk : 3 ≤ k) {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP u v = 1 := by
  have h := lambdaImage_le_of_le (G := G) (m := k + 1)
    (show k + 1 ≤ k - 1 + (k - 1) by omega) (commP_mem_lambdaImage_add hu hv)
  rw [lambdaImage_self] at h
  simpa using h

/-- Restated from `StageLemma.lean`. -/
private theorem mul_comm_lambdaImage (k : ℕ) (hk : 3 ≤ k) {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    u * v = v * u := by
  rw [mul_swap_commP u v, commP_lambdaImage_eq_one k hk hu hv, mul_one]

/-! ### The frozen GL-A interface -/

/-- Squaring is multiplicative on `λ_{k-1}`-image elements of `Q_{k+1}`: the
commutator correction lands in `[λ_{k-1}, λ_{k-1}] ⊆ λ_{2k-2}`, trivial for `k ≥ 3`.
Fill: GL-A. -/
theorem sq_mul_of_mem_lambdaImage_pred (k : ℕ) (hk : 3 ≤ k)
    {u v : levelQuot G (k + 1)} (hu : u ∈ lambdaImage G (k - 1) (k + 1))
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (u * v) ^ 2 = u ^ 2 * v ^ 2 := by
  have h : v * u = u * v := mul_comm_lambdaImage k hk hv hu
  calc (u * v) ^ 2 = u * (v * u) * v := by rw [pow_two]; group
    _ = u * (u * v) * v := by rw [h]
    _ = u ^ 2 * v ^ 2 := by rw [pow_two u, pow_two v]; group

/-- **The commP-square transport** (the `k ≥ 4` gate of the whole step): for
`u ∈ λ_{k-2}`-image and arbitrary `g`, `(commP u g)² = commP (u²) g` in `Q_{k+1}` —
the correction `⁅⁅u,g⁆,u⁆ ∈ λ_{2k-3}` dies exactly when `2k-3 ≥ k+1`.  Fill: GL-A. -/
theorem commP_sq_of_mem_lambdaImage (k : ℕ) (hk : 4 ≤ k)
    {u : levelQuot G (k + 1)} (g : levelQuot G (k + 1))
    (hu : u ∈ lambdaImage G (k - 2) (k + 1)) :
    commP u g ^ 2 = commP (u ^ 2) g := by
  -- `commP u g ∈ λ_{k-1}`, so `⁅commP u g, u⁆ ∈ λ_{(k-1)+(k-2)} = λ_{2k-3} = 1`.
  have hug : commP u g ∈ lambdaImage G (k - 2 + 1) (k + 1) :=
    commP_mem_lambdaImage_succ hu g
  have hkill : commP (commP u g) u = 1 := by
    have h := lambdaImage_le_of_le (G := G) (m := k + 1)
      (show k + 1 ≤ k - 2 + 1 + (k - 2) by omega) (commP_mem_lambdaImage_add hug hu)
    rw [lambdaImage_self] at h
    simpa using h
  have hconj : u⁻¹ * commP u g * u = commP u g := conj_eq_self_of_commP_eq_one hkill
  rw [pow_two u, commP_mul_left, hconj, ← pow_two]

/-- Squares distribute over a four-fold product of `λ_{k-1}`-image elements (the shape of
the two `d̄`-words). -/
private theorem sq_mul₄ (k : ℕ) (hk : 3 ≤ k) {f₁ f₂ f₃ f₄ : levelQuot G (k + 1)}
    (h₁ : f₁ ∈ lambdaImage G (k - 1) (k + 1)) (h₂ : f₂ ∈ lambdaImage G (k - 1) (k + 1))
    (h₃ : f₃ ∈ lambdaImage G (k - 1) (k + 1)) (h₄ : f₄ ∈ lambdaImage G (k - 1) (k + 1)) :
    (f₁ * f₂ * f₃ * f₄) ^ 2 = f₁ ^ 2 * f₂ ^ 2 * f₃ ^ 2 * f₄ ^ 2 := by
  rw [sq_mul_of_mem_lambdaImage_pred k hk
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) h₃) h₄,
    sq_mul_of_mem_lambdaImage_pred k hk (Subgroup.mul_mem _ h₁ h₂) h₃,
    sq_mul_of_mem_lambdaImage_pred k hk h₁ h₂]

/-- The four factors of a `d̄`-word at a `λ_{k-2}`-modification all live in `λ_{k-1}`. -/
private theorem sq_mem_lambdaImage_pred (k : ℕ) (hk : 4 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 2) (k + 1)) : v ^ 2 ∈ lambdaImage G (k - 1) (k + 1) := by
  have h := sq_mem_lambdaImage_succ hv
  rwa [show k - 2 + 1 = k - 1 by omega] at h

/-- Companion of `sq_mem_lambdaImage_pred` for the bracket factors. -/
private theorem commP_mem_lambdaImage_pred (k : ℕ) (hk : 4 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 2) (k + 1)) (g : levelQuot G (k + 1)) :
    commP v g ∈ lambdaImage G (k - 1) (k + 1) := by
  have h := commP_mem_lambdaImage_succ hv g
  rwa [show k - 2 + 1 = k - 1 by omega] at h

/-- **The transport identity, `r₀` shape** (memo §2.3): π of a depth-`(k-1)` defect
word is the depth-`k` defect word at the squared modification.  Slots arbitrary.
Fill: GL-A. -/
theorem dbarWordR0_sq (k : ℕ) (hk : 4 ≤ k) (a s y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 2) (k + 1)) :
    dbarWordR0 a s y w ^ 2 = dbarWordR0 a s y (fun i => w i ^ 2) := by
  simp only [dbarWordR0]
  rw [sq_mul₄ k (by omega) (sq_mem_lambdaImage_pred k hk (hw 0))
      (commP_mem_lambdaImage_pred k hk (hw 0) a)
      (commP_mem_lambdaImage_pred k hk (hw 1) y)
      (commP_mem_lambdaImage_pred k hk (hw 2) s),
    commP_sq_of_mem_lambdaImage k hk a (hw 0),
    commP_sq_of_mem_lambdaImage k hk y (hw 1),
    commP_sq_of_mem_lambdaImage k hk s (hw 2)]

/-- The transport identity, `r₂` shape.  Fill: GL-A. -/
theorem dbarWordR2_sq (k : ℕ) (hk : 4 ≤ k) (s x y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 2) (k + 1)) :
    dbarWordR2 s x y w ^ 2 = dbarWordR2 s x y (fun i => w i ^ 2) := by
  simp only [dbarWordR2]
  rw [sq_mul₄ k (by omega) (sq_mem_lambdaImage_pred k hk (hw 2))
      (commP_mem_lambdaImage_pred k hk (hw 2) y)
      (commP_mem_lambdaImage_pred k hk (hw 0) x)
      (commP_mem_lambdaImage_pred k hk (hw 1) s),
    commP_sq_of_mem_lambdaImage k hk y (hw 2),
    commP_sq_of_mem_lambdaImage k hk x (hw 0),
    commP_sq_of_mem_lambdaImage k hk s (hw 1)]

/-- λ-images lift along `levelProj`: the levelMk-image of the same witness works.
Fill: GL-A (no compactness needed). -/
theorem exists_levelProj_preimage_lambdaImage (j k : ℕ)
    {q : levelQuot G k} (hq : q ∈ lambdaImage G j k) :
    ∃ q' ∈ lambdaImage G j (k + 1), levelProj G k q' = q := by
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨levelMk G (k + 1) g, ⟨g, hg, rfl⟩, rfl⟩

/-- A central-involution factor is invisible to squares: for `ζ ∈ Zₖ`,
`(q·ζ)² = q²`.  Fill: GL-A (from `zLayer_commute`/`zLayer_sq`). -/
theorem sq_mul_zLayer (k : ℕ) {q ζ : levelQuot G (k + 1)} (hζ : ζ ∈ zLayer G k) :
    (q * ζ) ^ 2 = q ^ 2 := by
  rw [(zLayer_commute hζ q).symm.mul_pow, zLayer_sq G hζ, mul_one]

/-- Bracket atoms are multiplicative in the ambient slot (values are central):
`commP v (z₁z₂) = commP v z₁ · commP v z₂` for `v ∈ λ_{k-1}`-image.  Fill: GL-A. -/
theorem commP_mul_right_of_mem (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (z₁ z₂ : levelQuot G (k + 1)) :
    commP v (z₁ * z₂) = commP v z₁ * commP v z₂ := by
  have hc₁ : commP v z₁ ∈ zLayer G k := commP_mem_zLayer k hk hv z₁
  have hc₂ : commP v z₂ ∈ zLayer G k := commP_mem_zLayer k hk hv z₂
  have hconj : z₂⁻¹ * commP v z₁ * z₂ = commP v z₁ := by
    calc z₂⁻¹ * commP v z₁ * z₂ = z₂⁻¹ * (commP v z₁ * z₂) := by group
      _ = z₂⁻¹ * (z₂ * commP v z₁) := by rw [(zLayer_commute hc₁ z₂).eq]
      _ = commP v z₁ := by group
  rw [commP_mul_right, hconj]
  exact (zLayer_commute hc₂ (commP v z₁)).eq

/-- Bracket atoms invert in the ambient slot.  Fill: GL-A. -/
theorem commP_inv_right_of_mem (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (z : levelQuot G (k + 1)) :
    commP v z⁻¹ = (commP v z)⁻¹ := by
  have h := commP_mul_right_of_mem k hk hv z z⁻¹
  rw [mul_inv_cancel, show commP v (1 : levelQuot G (k + 1)) = 1 by
    simp only [commP]; group] at h
  calc commP v z⁻¹ = (commP v z)⁻¹ * (commP v z * commP v z⁻¹) := by group
    _ = (commP v z)⁻¹ := by rw [← h, mul_one]

end TransportCalculus

/-! ### Single-slot d̄ evaluations and free-quotient generation -/

section SingleSlot

variable {G : Type*} [Group G]

/-- Twisted slot alone, `r₀`: `d̄(v,1,1) = v²·[v,a]`.  Fill: GL-A (simp warm-up). -/
theorem dbarWordR0_single₀ (a s y v : G) :
    dbarWordR0 a s y ![v, 1, 1] = v ^ 2 * commP v a := by
  simp [dbarWordR0, Matrix.cons_val_two, commP_one_left]

/-- First bracket slot alone, `r₀`: `d̄(1,v,1) = [v,y]`.  Fill: GL-A. -/
theorem dbarWordR0_single₁ (a s y v : G) :
    dbarWordR0 a s y ![1, v, 1] = commP v y := by
  simp [dbarWordR0, Matrix.cons_val_two, commP_one_left]

/-- Second bracket slot alone, `r₀`: `d̄(1,1,v) = [v,s]`.  Fill: GL-A. -/
theorem dbarWordR0_single₂ (a s y v : G) :
    dbarWordR0 a s y ![1, 1, v] = commP v s := by
  simp [dbarWordR0, Matrix.cons_val_two, commP_one_left]

/-- Twisted slot alone, `r₂`: `d̄(1,1,v) = v²·[v,y]`.  Fill: GL-A. -/
theorem dbarWordR2_single₂ (s x y v : G) :
    dbarWordR2 s x y ![1, 1, v] = v ^ 2 * commP v y := by
  simp [dbarWordR2, Matrix.cons_val_two, commP_one_left]

/-- First bracket slot alone, `r₂`: `d̄(v,1,1) = [v,x]`.  Fill: GL-A. -/
theorem dbarWordR2_single₀ (s x y v : G) :
    dbarWordR2 s x y ![v, 1, 1] = commP v x := by
  simp [dbarWordR2, Matrix.cons_val_two, commP_one_left]

/-- Second bracket slot alone, `r₂`: `d̄(1,v,1) = [v,s]`.  Fill: GL-A. -/
theorem dbarWordR2_single₁ (s x y v : G) :
    dbarWordR2 s x y ![1, v, 1] = commP v s := by
  simp [dbarWordR2, Matrix.cons_val_two, commP_one_left]

end SingleSlot

/-- **The free level quotients are generated by the marked classes** (plain subgroup
closure — the quotient is finite discrete): push `topGen_freeProTwo` through `levelMk`
via `map_topologicalClosure_eq_of_discrete` + `MonoidHom.map_closure`.  Fill: GL-A. -/
theorem closure_levelMk_freeGen (m : ℕ) :
    Subgroup.closure
      (Set.range fun i => levelMk (freeProTwo : Type) m (freeGen i)) = ⊤ := by
  haveI : DiscreteTopology (levelQuot (freeProTwo : Type) m) :=
    discreteTopology_levelQuot (freeProTwo : Type) freeTopGenFinset isProP_maxProPQuotient m
  have himg : (Subgroup.closure (Set.range freeGen)).map (levelMk (freeProTwo : Type) m) =
      Subgroup.closure (Set.range fun i => levelMk (freeProTwo : Type) m (freeGen i)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← himg, ← map_topologicalClosure_eq_of_discrete (freeProTwo : Type) _ _
      (continuous_levelMk (freeProTwo : Type) m), topGen_freeProTwo]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective (freeProTwo : Type) m)

end GQ2.Roe.Labute
