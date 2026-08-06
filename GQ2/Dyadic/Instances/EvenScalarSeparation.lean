/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.N0M0ScalarStokes

/-!
# The scalar even assembly, parametrised by separation alone

`N0M0ScalarStokes.evenScalarStokesDuality` asks for the traced pairing on scalar normal
coordinates *in a fixed shape* — the compact rows'

```
ν₀(d₀ + d₁) + ν₁(d₀) + b_σ(d₂) + ν₂(a_σ) + Σ handles,
```

and then separates it.  The procyclic-`N` row's scalar Gram matrix is **not** that one (its
`(x₀, x_σ)` and `(x_σ, x₂)` planes carry the conjugator exponents `n_η` and `2^r`), so this file
records the same assembly with the pairing clause replaced by the property it is only ever used
for: left nondegeneracy on scalar normal coordinates.

Nothing else changes.  Both end clauses are the biduality map `A → A^{∨∨}` in disguise, exactly
as in the compact case, and the middle clause is the normal-form count
`stokesH1Map_bijective_of_normalForm`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]

set_option maxHeartbeats 3200000 in
/-- **Stokes duality of the even word complex at a completely trivial action**, from the
`tau`-row, the scalar normal form and *left nondegeneracy* of the traced pairing on scalar
normal coordinates.  `evenScalarStokesDuality` is the special case in which that nondegeneracy
is read off the compact rows' Gram matrix. -/
theorem evenScalarStokesDuality_of_separation
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hd0A : ∀ a : A, heisD0 (A := A) ⇑t a = 0)
    (hd0D : ∀ lam : ElemDual A, heisD0 (A := ElemDual A) ⇑t lam = 0)
    (hd1A : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x = ![x .tau, x .tau])
    (hd1D : ∀ y : Generator (2 + 2 * h) → ElemDual A, heisD1 ⇑t w y = ![y .tau, y .tau])
    (hsep : ∀ p : ScalarParam h A, p ≠ 0 →
      ∃ rr : ScalarParam h (ElemDual A),
        heisEta1 ⇑t w (evenScalarNormalP h p) (evenScalarNormalP h rr) ≠ 0) :
    StokesDuality ⇑t w A := by
  classical
  apply (stokesDuality_iff_cohomologyBijections (⇑t) w A hr hend).mpr
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro a b hab
      apply Subtype.ext
      have hval : (heisEta0 (A := A) a.val : ElemDual (Fin 2 → ElemDual A))
          = heisEta0 b.val := congrArg Subtype.val hab
      have hsub : (heisEta0 : A →+ ElemDual (Fin 2 → ElemDual A)) (a.val - b.val) = 0 := by
        rw [map_sub, hval, sub_self]
      exact sub_eq_zero.mp ((injective_iff_map_eq_zero _).mp
        (heisEta0_injective_elem (A := A) hA₂) _ hsub)
    · intro y
      have hker : ∀ u : ElemDual A,
          (y.val : ElemDual (Fin 2 → ElemDual A)) (![u, u]) = 0 := by
        intro u
        have hy := DFunLike.congr_fun (AddMonoidHom.mem_ker.mp y.2)
          (Pi.single (Generator.tau : Generator (2 + 2 * h)) u)
        rw [dualMap_apply, hd1D] at hy
        simpa using hy
      let φ : ElemDual A →+ (Fin 2 → ElemDual A) :=
        AddMonoidHom.mk' (fun u ↦ ![u, 0]) (by
          intro u v
          funext k
          fin_cases k <;> simp)
      obtain ⟨a, ha⟩ := (elemDualEval_bijective hA₂).2
        ((y.val : ElemDual (Fin 2 → ElemDual A)).comp φ)
      have hL : ∀ u : ElemDual A,
          (y.val : ElemDual (Fin 2 → ElemDual A)) (![u, 0]) = u a := by
        intro u
        exact (DFunLike.congr_fun ha u).symm
      have hR : ∀ u : ElemDual A,
          (y.val : ElemDual (Fin 2 → ElemDual A)) (![0, u]) = u a := by
        intro u
        have hsum : (![u, u] : Fin 2 → ElemDual A) = ![u, 0] + ![0, u] := by
          funext k
          fin_cases k <;> simp
        have h1 := hker u
        rw [hsum, map_add, hL u] at h1
        exact (eq_neg_of_add_eq_zero_right h1).trans (CharTwo.neg_eq _)
      refine ⟨⟨a, AddMonoidHom.mem_ker.mpr (hd0A a)⟩, ?_⟩
      apply Subtype.ext
      apply ElemDual.ext
      intro ξ
      have hsplit : ξ = ![ξ 0, 0] + ![0, ξ 1] := by
        funext k
        fin_cases k <;> simp
      show heisEta0 a ξ = (y.val : ElemDual (Fin 2 → ElemDual A)) ξ
      rw [heisEta0_apply, Fin.sum_univ_two]
      conv_rhs => rw [hsplit]
      rw [map_add, hL (ξ 0), hR (ξ 1)]
  · exact stokesH1Map_bijective_of_normalForm t w hr hend
      (evenScalarNormalP h) (evenScalarNormalP h) (evenScalarNormalP_zero h)
      (heisD1_evenScalarNormal_eq_zero_of_tauRow t w hd1A)
      (heisD1_evenScalarNormal_eq_zero_of_tauRow (A := ElemDual A) t w hd1D)
      (evenScalarNormalForm_of_tauRow t w hd0A hd1A)
      (evenScalarNormalForm_of_tauRow (A := ElemDual A) t w hd0D hd1D)
      hsep (card_scalarParam h hA₂)
  · constructor
    · rw [injective_iff_map_eq_zero]
      intro V hV
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective V
      rw [stokesH2Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
        AddMonoidHom.mem_range] at hV
      obtain ⟨lam, hlam⟩ := hV
      have hzero : (heisEta2 : (Fin 2 → A) →+ ElemDual (ElemDual A)) v = 0 := by
        rw [← hlam]
        apply ElemDual.ext
        intro mu
        rw [dualMap_apply, hd0D, map_zero]
        rfl
      have hvsum : v 0 + v 1 = 0 := by
        by_contra hne
        obtain ⟨mu, hmu⟩ := elemDual_separates hA₂ hne
        apply hmu
        have := DFunLike.congr_fun hzero mu
        rw [heisEta2_apply, Fin.sum_univ_two] at this
        simpa using this
      have hv : v = ![v 0, v 0] := by
        funext k
        fin_cases k
        · simp
        · have hneg : v 1 = -(v 0) := eq_neg_of_add_eq_zero_right hvsum
          have h20 : -(v 0) = v 0 := neg_eq_of_add_eq_zero_left (hA₂ (v 0))
          simp [hneg, h20]
      refine (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr
        ⟨Pi.single (Generator.tau : Generator (2 + 2 * h)) (v 0), ?_⟩)
      rw [hd1A]
      simpa using hv.symm
    · intro W
      obtain ⟨lam, rfl⟩ := QuotientAddGroup.mk_surjective W
      obtain ⟨a, ha⟩ := (elemDualEval_bijective hA₂).2 lam
      refine ⟨QuotientAddGroup.mk (![a, 0] : Fin 2 → A), ?_⟩
      rw [stokesH2Map, QuotientAddGroup.map_mk]
      congr 1
      apply ElemDual.ext
      intro mu
      rw [heisEta2_apply, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
      exact DFunLike.congr_fun ha mu

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.evenScalarStokesDuality_of_separation

end AxiomAudit
