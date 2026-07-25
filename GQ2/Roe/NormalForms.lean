/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.WildRow
public import GQ2.FoxHeisenberg.HessianRow

@[expose] public section

/-!
# Lemma 4.2: simple normal forms for the Roe word complex  (⟦lem:normalforms⟧)

The `Γ_R` counterpart of the `Γ_A` normal-form layer (`GQ2.FoxHeisenberg.HessianRow`'s
`section NormalForms`), for the note's Lemma 4.2 ⟦lem:normalforms⟧: on a **nontrivial simple**
coefficient module `V`, every degree-one class of the Roe word complex has a unique
representative

  `(a, b, c, d) = (0, 0, 0, d)`.

The tame relator is **shared** with `Γ_A`, but the two wild columns are interchanged
(`liftMarking_wildValueR_u_eq_swap`, `GQ2.Roe.WildRow`): the `Γ_A` normal form is `x₀`-supported
(the `c`-coordinate, slot `x 2`), whereas the `Γ_R` normal form is **`x₁`-supported** (the
`d`-coordinate, slot `x 3` — `x1Supported`).  Concretely the split `Z¹_R` shape is
`x 1 = 0 ∧ x 2 = 0` (vs `Γ_A`'s `x 1 = 0 ∧ x 3 = 0`), so after the coboundary kills `x 0` the
surviving free coordinate is `x 3 = d`.

Two cases (the note's proof of ⟦lem:normalforms⟧, quoted):

* **`T = 1` (`P = 1`), split.**  "The tame and wild rows of ⟦eq:jacobian⟧ first give `b = 0`,
  `(1 + S⁻¹)c = 0`.  Since `V` is nontrivial simple, `S − 1` is invertible; hence `c = 0`, and the
  unique coboundary with `(S − 1)v = a` kills `a`."  → `lemma_5_13_split_R` (the `Z¹_R`/`B¹_R`
  shapes) via the shared tame row `d1Fun_tame_split` (`L_t = S⁻¹·x₁`, forcing `x 1 = 0`) and the
  Roe wild row `liftMarking_wildValueR_u` (`L_w = x₁ + (1 + S⁻¹)·x₂`, forcing `x 2 = 0` by
  `V^S = 0`).  **No `σ₂`-tameness `hU`** enters (one fewer hypothesis than `Γ_A`'s
  `lemma_5_13_split`) — `σ₂` is only a conjugator in `r_R`.
* **`V^T = 0` (`P = 0`), ramified.**  "The wild row gives `c = 0`.  Subtracting the coboundary of
  `(T − 1)⁻¹b` kills `b`, after which the tame row forces `a = 0`."  → `lemma_5_13_ramified_R`
  (the unique `x₁`-supported representative) via `liftMarking_wildValueR_u_ramified`
  (`L_w = S⁻¹·x₂`, forcing `x 2 = 0`) and the shared tame row, exactly as `Γ_A`'s
  `lemma_5_13_ramified` with `x 2 ↔ x 3`.

Organisation mirrors `HessianRow.lean`'s `section NormalForms` 1:1 with an `R` suffix
(`b1wR_split_shape`, `lemma_5_13_split_R`, `lemma_5_13_ramified_R`).  Downstream:

* the **degree-one pairing** (⟦prop:hessian⟧, the `x₁`-supported Hessian `(d,λ) ↦ λ(d)` resp.
  `λ((1 + U + U⁻¹)d)`) is ticket **R24** (`GQ2/Roe/Hessian.lean`), not here;
* the **cohomological consequences** of ⟦lem:normalforms⟧ — "`H⁰_R = H²_R = 0`,
  `dim H¹_R = dim V`", Jacobian surjectivity, and the self-duality assembly
  `selfDual_of_simple_R` — are ticket **R26** (`GQ2/Roe/DualityAssembly.lean`), which consumes
  `b1wR_split_shape`, `lemma_5_13_ramified_R` and `x1Supported` from here, mirroring how
  `GQ2/DualityAssembly.lean` consumes `b1w_split_shape`, `lemma_5_13_ramified` and `x0Supported`.
-/

namespace GQ2

namespace FoxH

section NormalFormsR

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-- The degree-one tuple supported on the `x₁`-slot (`x 3`) — the note's `(0,0,0,d)` normal form
(⟦lem:normalforms⟧), the `Γ_R` analogue of `x0Supported` after the wild-column swap. -/
def x1Supported (d : V) : Fin 4 → V := ![0, 0, 0, d]

omit [Finite C] [Finite V] in
/-- **The `B¹_R` coboundary shape when the wild generators act trivially** — literally `Γ_A`'s
`b1w_split_shape` (`B¹_R = B¹` since `d⁰` does not see the relator, `B1wR_eq_B1w`).  Under `T = 1`
and `x₀, x₁` acting trivially, every coboundary `d⁰v` is supported on the `σ`-slot:
`B¹_R = {((S−1)v, 0, 0, 0)}`. -/
theorem b1wR_split_shape (t : Marking C) (htau : ∀ v : V, t.τ • v = v)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (y : Fin 4 → V) :
    y ∈ B1wR (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0] := by
  rw [B1wR_eq_B1w]
  exact b1w_split_shape t htau hx0 hx1 y

/-- **Lemma 4.2, split case, cocycle shape** (⟦lem:normalforms⟧, `T = 1`): if `τ` acts trivially on
a nontrivial simple module, `Z¹_R = {(a, 0, 0, d)}` and `B¹_R = {((S−1)v, 0, 0, 0)}`.  The `Γ_R`
twin of `lemma_5_13_split` — but with the two wild columns interchanged, so the killed wild slot is
`x 2` (`Γ_A`: `x 3`) and the surviving normal-form slot is `x 3 = d` (`Γ_A`: `x 2 = c`).

Hypotheses match `lemma_5_13_split` **minus `hU`**: the Roe wild row `liftMarking_wildValueR_u`
carries no `σ₂`-tameness dependency (`σ₂` is only a conjugator in `r_R`), so `hU : ∀ v, σ₂ • v = v`
is not needed here.  `hcore` supplies the trivial wild action (`wild_acts_trivially`); `hVS` is
`V^S = 0` (`1 + S⁻¹` invertible), excluding the trivial module `𝔽₂`.

Proof: the `B¹_R` half is `b1wR_split_shape`; the `Z¹_R` half combines the shared tame row
`d1Fun_tame_split` (`= S⁻¹·x₁`, forcing `x 1 = 0`) with the Roe wild row
`liftMarking_wildValueR_u` (`= x₁ + (1 + S⁻¹)·x₂`), giving `x 1 = 0` from `S⁻¹` injective and
`x 2 = 0` from `hVS`. -/
theorem lemma_5_13_split_R (t : Marking C) (ht : t.TameRel) (_ : t.WildRelR)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) (hcore : t.Pro2Core)
    (htau : ∀ v : V, t.τ • v = v) (hVS : ∀ v : V, t.σ • v = v → v = 0) :
    (∀ x : Fin 4 → V, x ∈ Z1wR (A := V) t ↔ x 1 = 0 ∧ x 2 = 0) ∧
    (∀ y : Fin 4 → V, y ∈ B1wR (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0]) := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  refine ⟨fun x => ?_, fun y => b1wR_split_shape t htau hx0 hx1 y⟩
  rw [mem_Z1wR_iff t x, Prod.ext_iff]
  rw [d1FunR_fst t x, d1Fun_tame_split t ht htau hV₂ x, d1FunR_snd t x,
    liftMarking_wildValueR_u t x hV₂ hx0 hx1 htau]
  simp only [Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hx1z : x 1 = 0 := by rwa [inv_smul_eq_iff, smul_zero] at h1
    rw [hx1z, zero_add] at h2
    have h3 : t.σ⁻¹ • x 2 = x 2 :=
      (add_eq_zero_iff_neg_eq.mp h2).symm.trans (neg_eq_of_add_eq_zero_left (hV₂ (x 2)))
    exact ⟨hx1z, hVS _ (inv_smul_eq_iff.mp h3).symm⟩
  · rintro ⟨h1, h3⟩
    simp [h1, h3]

/-- **Lemma 4.2, ramified case, unique normal form** (⟦lem:normalforms⟧, `V^T = 0`): every
degree-one class has a unique representative supported on `x₁` — the note's `(0,0,0,d)`.  The `Γ_R`
twin of `lemma_5_13_ramified` with the wild column swapped: the wild row forces `x 2 = 0` (`Γ_A`:
`x 3 = 0`) and the surviving witness is `x 3 = d` (`Γ_A`: `x 2 = c`).

Hypotheses as in `lemma_5_13_ramified`: `hx0`/`hx1` (trivial wild action, taken directly so the
lemma applies to the contragredient dual `A∨` — the R26 assembly consumes it on both `A` and `A∨`);
`htau` is `V^T = 0` (`1 + T` invertible); `hTodd` is the ramified `σ₂`-analogue "`τ` acts with odd
order" (tame inertia is prime-to-2), which kills the `ω₂`-norm in `liftMarking_wildValueR_u_ramified`.

Proof exactly as `lemma_5_13_ramified`: the Roe wild row `liftMarking_wildValueR_u_ramified`
(`= S⁻¹·x₂`) forces `x 2 = 0`; `v = (T − 1)⁻¹·x₁` and subtracting `d⁰v` kills the `x₁`-slot; the
reduced cocycle's shared tame row forces `x 0 = (S − 1)v`; hence `x − x1Supported(x 3) = d⁰v`, and
`d = x 3` is the unique witness. -/
theorem lemma_5_13_ramified_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    ∀ x ∈ Z1wR (A := V) t, ∃! d : V, x - x1Supported d ∈ B1wR (A := V) t := by
  -- `T − 1` is injective (`V^T = 0`) hence surjective on the finite space `V`.
  have hTsurj : Function.Surjective (fun w : V => t.τ • w - w) :=
    surjective_smul_sub_of_fixedPointFree htau
  intro x hx
  rw [mem_Z1wR_iff t x] at hx
  -- Wild row `S⁻¹·x₂ = 0` forces `x₂ = 0`.
  have hx2 : x 2 = 0 := by
    have hwild : (liftMarking t x).wildValueR.u = 0 := congrArg Prod.snd hx
    rw [liftMarking_wildValueR_u_ramified t x hV₂ hx0 hx1 htau hTodd] at hwild
    rw [← smul_inv_smul t.σ (x 2), hwild, smul_zero]
  -- `v = (T − 1)⁻¹ x₁`; subtracting `d⁰v` kills the `x₁`-slot.
  obtain ⟨v, hv⟩ := hTsurj (x 1)
  have hv2 : t.τ • v - v = x 1 := hv
  have hc0 : (x - d0 t v) 0 = x 0 - (t.σ • v - v) := by
    simp only [Pi.sub_apply, d0, AddMonoidHom.mk'_apply, Matrix.cons_val_zero]
  have hc1 : (x - d0 t v) 1 = 0 := by
    simp only [Pi.sub_apply, d0, AddMonoidHom.mk'_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hv2, sub_self]
  have hxcob : d1FunR t (x - d0 t v) = 0 := by
    have hsub := (d1R t).map_sub x (d0 t v)
    simp only [d1R_apply] at hsub
    rw [hx, d1FunR_comp_d0 t ht hw v, sub_zero] at hsub
    exact hsub
  -- The reduced cocycle's tame row `σ⁻¹(T − 1)x'₀ = 0` forces `x'₀ = 0`, i.e. `x₀ = (S − 1)v`.
  have hx'0 : x 0 - (t.σ • v - v) = 0 := by
    have ht' : (d1FunR t (x - d0 t v)).1 = 0 := congrArg Prod.fst hxcob
    rw [d1FunR_fst t (x - d0 t v), d1Fun_tame t ht (x - d0 t v), hc0, hc1] at ht'
    simp only [smul_zero, add_zero, sub_zero] at ht'
    rw [sub_eq_zero] at ht'
    exact htau _ (by simpa only [smul_inv_smul] using congrArg (t.σ • ·) ht')
  have hx0v : x 0 = t.σ • v - v := sub_eq_zero.mp hx'0
  -- Hence `x − x1Supported(x₃) = d⁰v`, and `d = x₃` is the unique witness.
  have hcob : x - x1Supported (x 3) = d0 t v := by
    funext i
    fin_cases i <;> simp [Pi.sub_apply, x1Supported, d0, hx0, hx1, hx2, hx0v, ← hv2]
  refine ⟨x 3, ?_, fun d hd => ?_⟩
  · simp only [B1wR, AddMonoidHom.mem_range]; exact ⟨v, hcob.symm⟩
  · simp only [B1wR, AddMonoidHom.mem_range] at hd
    obtain ⟨w, hw'⟩ := hd
    have h := congrFun hw' 3
    have hdw : (0 : V) = x 3 - d := by simpa [d0, x1Supported, hx1, Pi.sub_apply] using h
    exact (sub_eq_zero.mp hdw.symm).symm

/-- **Stress test (trivial-module cross-check).**  On `V = 𝔽₂` with trivial `C`-action the
`x₁`-supported normal form `(0,0,0,d)` is always a Roe cocycle: `d¹_R` collapses to the diagonal
`x ↦ (x₁, x₁)` (R21's `d1FunR_of_trivial`, ⟦lem:trivial⟧), which the `x₁`-supported tuple (whose
`x 1`-slot is `0`) kills.  The trivial module is the excluded case of `lemma_5_13_split_R`
(`1 + S⁻¹ = 0` there); this checks the `x1Supported` normal-form vocabulary composes with R21's
evaluated differential. -/
theorem x1Supported_mem_Z1wR_of_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : V), c • a = a) (hV₂ : ∀ v : V, v + v = 0) (d : V) :
    x1Supported d ∈ Z1wR (A := V) t := by
  rw [mem_Z1wR_iff t (x1Supported d), d1FunR_of_trivial t ht hw htriv hV₂]
  simp [x1Supported]

end NormalFormsR

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 4.2 (Simple normal forms) = ⟦lem:normalforms⟧ — the cochain-level normal forms:
    `b1wR_split_shape` (the `B¹_R` shape), `lemma_5_13_split_R` (split `Z¹_R`/`B¹_R` shapes,
    `x 1 = 0 ∧ x 2 = 0`) and `lemma_5_13_ramified_R` (the unique `x₁`-supported representative
    `(0,0,0,d)`).  The `x₁`-supported tuple `x1Supported` (slot `x 3`) is the `Γ_R` normal form.
  * The cohomological reading of ⟦lem:normalforms⟧ ("`H⁰_R = H²_R = 0`, `dim H¹_R = dim V`",
    Jacobian surjectivity) is ticket **R26**'s card bookkeeping (`GQ2/Roe/DualityAssembly.lean`),
    consuming `b1wR_split_shape`/`lemma_5_13_ramified_R`/`x1Supported` from here.
  * The degree-one pairing ⟦prop:hessian⟧ (the `x₁`-supported Hessian) is ticket **R24**
    (`GQ2/Roe/Hessian.lean`).
-/
