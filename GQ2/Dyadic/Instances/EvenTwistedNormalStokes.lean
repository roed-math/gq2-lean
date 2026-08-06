/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.N0M0UnramifiedStokes

/-!
# Stokes duality from an arbitrary normal parametrisation of the even middle

`evenNormalStokesDuality` (in `N0M0UnramifiedStokes`) assembles Stokes duality on the even
alphabet from five inputs, with the middle cohomology parametrised by the *fixed* map
`evenNormal`, whose `x₂`-slot is zero.  Both compact even rows land on that map because their
ramified wild row is the single pivot `−S⁻¹·a(x₂)`, which forces `x₂ = 0` on a cocycle.

Neither procyclic row does.  The corrected procyclic-`N` ramified wild row is the **two**-entry
row

`D(R_{N,α,r,η}) = (A⁻¹ − 1)·a(x₀) − B⁻¹·a(x₂)`,  `A = S^{E(η̂)}`, `B = S^{2^r}`

(`Certificates.NProcyclic.foxD_npc_ram`), so on a cocycle `x₂` is not zero but the *twist*
`B(A⁻¹ − 1)·x₀` of the free coordinate `x₀`; the procyclic-`M` dictionary is triangular in the
same way.  The middle is still freely parametrised by `A × A × (Fin h × Fin 2 → A)`, just by a
different injection.

This file therefore restates the assembly with the parametrisation as a parameter.  Nothing in
the proof used any property of `evenNormal` beyond `evenNormal … 0 0 0 = 0`, so the generalised
statement carries exactly one extra hypothesis, `hnf0`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words

variable {h : ℕ}

set_option maxHeartbeats 3200000 in
/-- **Stokes duality from an arbitrary even normal parametrisation.**  An acyclic-ends complex
on the even alphabet whose middle cohomology is freely parametrised by
`A × A × (Fin h × Fin 2 → A)` through *any* zero-preserving injection, with a left-separating
traced pairing, satisfies Stokes duality.

`evenNormalStokesDuality` is the case `nfA p = evenNormal h p.1 p.2.1 p.2.2`. -/
theorem evenNormalStokesDuality_of_normalMap
    {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (nfA : A × A × (Fin h × Fin 2 → A) → (Generator (2 + 2 * h) → A))
    (nfD : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A) →
      (Generator (2 + 2 * h) → ElemDual A))
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hnf0 : nfA 0 = 0)
    (hd₀A : Function.Injective (heisD0 (A := A) ⇑t))
    (hd₀D : Function.Injective (heisD0 (A := ElemDual A) ⇑t))
    (hd₁A : Function.Surjective (heisD1 (A := A) ⇑t w))
    (hd₁D : Function.Surjective (heisD1 (A := ElemDual A) ⇑t w))
    (hmemA : ∀ p : A × A × (Fin h × Fin 2 → A), heisD1 ⇑t w (nfA p) = 0)
    (hmemD : ∀ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisD1 ⇑t w (nfD r) = 0)
    (hnfA : ∀ x, heisD1 (A := A) ⇑t w x = 0 →
      ∃! p : A × A × (Fin h × Fin 2 → A), x - nfA p ∈ Set.range (heisD0 ⇑t))
    (hnfD : ∀ y, heisD1 (A := ElemDual A) ⇑t w y = 0 →
      ∃! r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        y - nfD r ∈ Set.range (heisD0 ⇑t))
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (nfA p) (nfD r) ≠ 0) :
    StokesDuality ⇑t w A := by
  classical
  have hs₀ := stokes_square₀ (A := A) (⇑t) w hr hend
  have hs₁ := stokes_square₁ (A := A) (⇑t) w hr hend
  apply (stokesDuality_iff_cohomologyBijections (⇑t) w A hr hend).mpr
  refine ⟨?_, ?_, ?_⟩
  · have htargetInj : Function.Injective
        (dualMap (heisD1 (A := ElemDual A) (⇑t) w)) :=
      dualMap_injective _ hd₁D
    constructor
    · intro a b _
      apply Subtype.ext
      have ha0 : a.val = 0 := hd₀A (by rw [AddMonoidHom.mem_ker.mp a.2, map_zero])
      have hb0 : b.val = 0 := hd₀A (by rw [AddMonoidHom.mem_ker.mp b.2, map_zero])
      rw [ha0, hb0]
    · intro y
      have hy0 : y.val = 0 := htargetInj (by rw [AddMonoidHom.mem_ker.mp y.2, map_zero])
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [hy0]
  · have h1inj : Function.Injective (stokesH1Map hs₀ hs₁) := by
      rw [injective_iff_map_eq_zero]
      intro H hH
      obtain ⟨x, rfl⟩ := stokesH1Mk_surjective
        (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w) H
      obtain ⟨p, hp, -⟩ := hnfA x.val (AddMonoidHom.mem_ker.mp x.2)
      by_cases hp0 : p = 0
      · rw [hp0, hnf0, sub_zero] at hp
        exact (stokesH1Mk_eq_zero_iff
          (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w) x).mpr hp
      · obtain ⟨r, hpair⟩ := hsep p hp0
        let y := nfD r
        have hy : heisD1 (A := ElemDual A) (⇑t) w y = 0 := hmemD r
        rw [stokesH1Mk, stokesH1Map, QuotientAddGroup.map_mk,
          QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hH
        obtain ⟨xi, hxi⟩ := AddMonoidHom.mem_range.mp hH
        have hvan : heisEta1 (⇑t) w x.val y = 0 := by
          have heq := DFunLike.congr_fun hxi y
          rw [dualMap_apply, hy, map_zero] at heq
          exact heq.symm
        obtain ⟨v, hv⟩ := hp
        have hxrepr : x.val = nfA p + heisD0 (⇑t) v := by
          rw [hv]; abel
        have hsame : heisEta1 (⇑t) w x.val y = heisEta1 (⇑t) w (nfA p) y := by
          rw [hxrepr, map_add]
          change heisEta1 (⇑t) w (nfA p) y + heisEta1 (⇑t) w (heisD0 (⇑t) v) y =
              heisEta1 (⇑t) w (nfA p) y
          rw [heisEta1_comp_d0 (⇑t) w hr hend v y, hy, map_zero]
          simp
        exact (hpair (hsame ▸ hvan)).elim
    have hcardA : Nat.card (StokesH1 (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w)) =
        Nat.card (A × A × (Fin h × Fin 2 → A)) :=
      card_stokesH1_of_normalForm _ _ nfA hmemA hnfA
    have hcardD : Nat.card
        (StokesH1 (heisD0 (A := ElemDual A) (⇑t))
          (heisD1 (A := ElemDual A) (⇑t) w)) =
        Nat.card (ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A)) :=
      card_stokesH1_of_normalForm _ _ nfD hmemD hnfD
    have hcoordCard : Nat.card (A × A × (Fin h × Fin 2 → A)) =
        Nat.card (ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A)) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
        Nat.card_fun, Nat.card_fun, card_elemDual hA₂]
    have htargetCard : Nat.card
        (StokesH1 (dualMap (heisD1 (A := ElemDual A) (⇑t) w))
          (dualMap (heisD0 (A := ElemDual A) (⇑t)))) =
        Nat.card (StokesH1 (heisD0 (A := ElemDual A) (⇑t))
          (heisD1 (A := ElemDual A) (⇑t) w)) := by
      rw [Nat.card_eq_of_bijective _ (wordH1_target_uc (A := A) (⇑t) w hr),
        card_elemDual (stokesH1_two_torsion _ _ wordDual_two_torsion)]
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨h1inj, hcardA.trans (hcoordCard.trans (hcardD.symm.trans htargetCard.symm))⟩
  · have htargetSurj : Function.Surjective
        (dualMap (heisD0 (A := ElemDual A) (⇑t))) :=
      dualMap_surjective wordDual_two_torsion _ hd₀D
    have hsourceZero : ∀ z : StokesH2 (heisD1 (A := A) (⇑t) w), z = 0 := by
      intro z
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr (hd₁A a))
    have htargetZero : ∀ z : StokesH2
        (dualMap (heisD0 (A := ElemDual A) (⇑t))), z = 0 := by
      intro z
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        (AddMonoidHom.mem_range.mpr (htargetSurj a))
    constructor
    · intro a b _
      rw [hsourceZero a, hsourceZero b]
    · intro y
      refine ⟨0, ?_⟩
      rw [map_zero, htargetZero y]

/-- The `evenNormal` parametrisation is the case the two compact rows use: it is zero-preserving,
so `evenNormalStokesDuality` is an instance of the general form. -/
theorem evenNormalStokesDuality_of_normalMap_evenNormal
    {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hd₀A : Function.Injective (heisD0 (A := A) ⇑t))
    (hd₀D : Function.Injective (heisD0 (A := ElemDual A) ⇑t))
    (hd₁A : Function.Surjective (heisD1 (A := A) ⇑t w))
    (hd₁D : Function.Surjective (heisD1 (A := ElemDual A) ⇑t w))
    (hmemA : ∀ p : A × A × (Fin h × Fin 2 → A),
      heisD1 ⇑t w (evenNormal h p.1 p.2.1 p.2.2) = 0)
    (hmemD : ∀ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisD1 ⇑t w (evenNormal h r.1 r.2.1 r.2.2) = 0)
    (hnfA : ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenNormal h p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t))
    (hnfD : ∀ y, heisD1 (A := ElemDual A) ⇑t w y = 0 →
      ∃! r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        y - evenNormal h r.1 r.2.1 r.2.2 ∈ Set.range (heisD0 ⇑t))
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (evenNormal h p.1 p.2.1 p.2.2)
          (evenNormal h r.1 r.2.1 r.2.2) ≠ 0) :
    StokesDuality ⇑t w A :=
  evenNormalStokesDuality_of_normalMap t w
    (fun p ↦ evenNormal h p.1 p.2.1 p.2.2) (fun r ↦ evenNormal h r.1 r.2.1 r.2.2)
    hA₂ hr hend (by simp [evenNormal_zero (A := A) h])
    hd₀A hd₀D hd₁A hd₁D hmemA hmemD hnfA hnfD hsep

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.evenNormalStokesDuality_of_normalMap
#print axioms GQ2.Dyadic.evenNormalStokesDuality_of_normalMap_evenNormal

end AxiomAudit
