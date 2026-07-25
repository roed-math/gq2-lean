/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.TrivialSelfDual

@[expose] public section

/-!
# Heisenberg naturality for the `r_R` pairing (Lemma 5.6), and the traced-row re-export

The dévissage χ-layer needs two traced ingredients over the Roe complex:

* the **traced Stokes rows** `prop_5_8_left_R`/`prop_5_8_right_R` (⟦lem:stokes⟧) — the chain
  identities `B^R(d⁰a, y) = ⟨a, L^{A^∨}(y)⟩` making the `χ`-maps well-defined.  These are ticket
  **R25**'s (`GQ2/Roe/TrivialSelfDual.lean`), landed with `trivialSelfDual_R`; this file re-exports
  them (`public import`), never re-proving them;
* **Lemma 5.6** (⟦lem-heisnatural⟧), the coefficient-naturality square of the traced pairing
  `B^R_{A'}(f∗x, y') = B^R_A(x, f^∨ y')`, needed by the `χ¹`/δ-square rungs.  R20 tagged `lemma_5_6`
  pure-`(A)`; its wild half (`Marking.map_wildValue`) is in fact word-coupled, but the port is
  **verbatim** — the only change is the final `simp` swapping `mixedB`/`Marking.map_wildValue` for
  `mixedB_R`/`Marking.map_wildValueR`.  R25 does not need it (the trivial module has no coefficient
  maps), so R26a provides it here (mechanical clone, `docs/orchestration/roe-r20-recon.md`).
-/

namespace GQ2

namespace FoxH

open scoped Pointwise

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **Lemma 5.6 (strict coefficient naturality)** for the Roe pairing (R-clone of `lemma_5_6`,
`GQ2/FoxHeisenberg/Traced.lean`): `B^R_{A'}(f∗x, y') = B^R_A(x, f^∨ y')`.  Verbatim port — only the
final `simp` swaps `mixedB`/`Marking.map_wildValue` for `mixedB_R`/`Marking.map_wildValueR`. -/
theorem lemma_5_6_R {A' : Type*} [AddCommGroup A'] [DistribMulAction C A'] [Finite A] [Finite A']
    [Finite C] (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a) (t : Marking C)
    (x : Fin 4 → A) (y' : Fin 4 → ElemDual A') :
    mixedB_R t (fun i => f (x i)) y'
      = mixedB_R t x (fun i => ((y' i : A' →+ ZMod 2).comp f : ElemDual A)) := by
  -- The dual (contragredient) `f^∨ : A'^∨ →+ A^∨`, `λ ↦ λ ∘ f`, bundled so results stay `ElemDual`.
  let fStar : ElemDual A' →+ ElemDual A :=
    { toFun := fun lam => lam.comp f
      map_zero' := AddMonoidHom.zero_comp f
      map_add' := fun a b => AddMonoidHom.add_comp a b f }
  have fStar_apply : ∀ (lam : ElemDual A') (a : A), fStar lam a = lam (f a) := fun _ _ => rfl
  -- Dual `f`-equivariance: `f^∨ (g • λ) = g • f^∨ λ`.
  have hcomp : ∀ (g : C) (lam : ElemDual A'), fStar (g • lam) = g • fStar lam := by
    intro g lam; ext a; simp only [fStar_apply, ElemDual.smul_apply, hf]
  -- The mixed subgroup of `H(A') ⋊ C × H(A) ⋊ C`.
  let S : Subgroup (HeisLift A' C × HeisLift A C) :=
    { carrier := {pq | pq.1.a = f pq.2.a ∧ pq.2.l = fStar pq.1.l ∧ pq.1.z = pq.2.z ∧
        pq.1.g = pq.2.g}
      one_mem' := ⟨by simp, by simp, rfl, rfl⟩
      mul_mem' := fun {P Q} hP hQ =>
        ⟨by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_a, map_add, hf, hP.1, hQ.1,
            hP.2.2.2],
          by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_l, map_add, hcomp,
            hP.2.1, hQ.2.1, hP.2.2.2],
          by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_z, hP.2.2.1,
            hQ.2.2.1, hP.2.1, hP.2.2.2, hQ.1, fStar_apply, hf],
          by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_g, hP.2.2.2, hQ.2.2.2]⟩
      inv_mem' := fun {P} hP =>
        ⟨by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_a, map_neg, hf, hP.1, hP.2.2.2],
          by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_l, map_neg, hcomp,
            hP.2.1, hP.2.2.2],
          by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_z, hP.2.2.1, hP.2.1, hP.1,
            fStar_apply],
          by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_g, hP.2.2.2]⟩ }
  -- The two projections and the mixed marking.
  let π₁ : ↥S →* HeisLift A' C := (MonoidHom.fst (HeisLift A' C) (HeisLift A C)).comp S.subtype
  let π₂ : ↥S →* HeisLift A C := (MonoidHom.snd (HeisLift A' C) (HeisLift A C)).comp S.subtype
  let M : Marking ↥S :=
    ⟨⟨(⟨f (x 0), y' 0, 0, t.σ⟩, ⟨x 0, (y' 0).comp f, 0, t.σ⟩), ⟨rfl, rfl, rfl, rfl⟩⟩,
      ⟨(⟨f (x 1), y' 1, 0, t.τ⟩, ⟨x 1, (y' 1).comp f, 0, t.τ⟩), ⟨rfl, rfl, rfl, rfl⟩⟩,
      ⟨(⟨f (x 2), y' 2, 0, t.x₀⟩, ⟨x 2, (y' 2).comp f, 0, t.x₀⟩), ⟨rfl, rfl, rfl, rfl⟩⟩,
      ⟨(⟨f (x 3), y' 3, 0, t.x₁⟩, ⟨x 3, (y' 3).comp f, 0, t.x₁⟩), ⟨rfl, rfl, rfl, rfl⟩⟩⟩
  have hπ₁ : M.map π₁ = heisMarking t (fun i => f (x i)) y' := rfl
  have hπ₂ : M.map π₂ = heisMarking t x (fun i => ((y' i).comp f : ElemDual A)) := rfl
  -- On `S`, the two projections have equal `z`-coordinate (the defining `z`-equation).
  have key : ∀ w : ↥S, (π₁ w).z = (π₂ w).z := fun w => w.2.2.2.1
  simp only [mixedB_R, ← hπ₁, ← hπ₂, Marking.map_tameValue, Marking.map_wildValueR,
    key M.tameValue, key M.wildValueR]

end FoxH

end GQ2
