import GQ2.FrattiniNongen
import GQ2.RadicalEdgeData
import GQ2.OrbitData

/-!
# §8 frame-enrichment, block layer  (P-16d1)

The **constructibility half** of the P-16d1 frame-enrichment layer: at the `B = Y/R` stage
of the §8 recursion the scalar covers `p_λ` carry square-form data on `M_B = π_B(K)` with
polar radical containing `T_B = π_B((K∩S)·R)` — a per-`λ` Lemma 8.6 datum
(`RadicalCoverData`).  The abstract per-`λ` fields live on the recursion frame
(`GQ2.SectionEight.RecursionFrame.Enrichment`, in `SectionEight.lean`); this file proves the
**block-level** facts the concrete frame construction will discharge them with:

* `blockT_map_le_blockM_map` — `T_B ≤ M_B` (`(K∩S)·R ≤ K`, via `lemma_7_1_head`);
* `mForm_of_qbar` — from the Prop 7.4 package `(λ, q̄, hspec)` (a `Y`-invariant additive
  `λ` on `R` with descended square values `λ(k²) = q̄(k mod S)`), the `M_B`-level form
  `q_M(π_B k) := λ(k²)` is **well defined** and has the (b)/(c) radical clauses of
  `RadicalCoverData`.  The whole derivation rides on `R ≤ K ∩ S` (`lemma_7_1_head`): the
  `π_B`-fibres over `M_B` lie inside single `S`-cosets of `K`, so every value reads off
  `q̄` through `hspec`.  (The cover clause `hq` is definitional for the concrete pushout
  cover `Y/ker λ ↠ Y/R` and is not part of this lemma.)

All std-3; no axioms.
-/

namespace GQ2

namespace SectionEight

open SectionSeven

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

/-- Under any projection of the block, the `T`-layer image lands in the `M`-layer image:
`(K ∩ S) ⊔ R ≤ K` because `R = Φ(K) ≤ K ∩ S` (`lemma_7_1_head`). -/
theorem blockT_map_le_blockM_map (B : MinimalBlock L) {YB : Type} [Group YB]
    (piB : Y →* YB) :
    ((B.K ⊓ B.S) ⊔ B.R).map piB ≤ B.K.map piB :=
  Subgroup.map_mono (sup_le inf_le_left ((lemma_7_1_head B).trans inf_le_left))

/-- **The `M_B`-level square form from the Prop 7.4 descent** (P-16d1): given the 7.4
package for a `Y`-invariant additive `λ` on `R` — the descended `q̄` on `V = P/S` with
`λ(k²) = q̄(k mod S)` — the assignment `q_M(π_B k) := λ(k²)` is well defined on
`M_B = π_B(K)` and satisfies the value, polar-radical, and `T`-vanishing clauses of the
per-`λ` `RadicalCoverData`.  Route: `ker π_B = R ≤ S` (`lemma_7_1_head`), so `π_B`-fibres
lie in single `S`-cosets and every clause reduces to an `S`-coset computation in `q̄`. -/
theorem mForm_of_qbar (B : MinimalBlock L) {YB : Type} [Group YB]
    (piB : Y →* YB) (hker : piB.ker = B.R)
    (lam : ↥B.R → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.R, lam (r * r') = lam r + lam r')
    (hsq : ∀ k ∈ B.K, k * k ∈ B.R)
    (qbar : (↥B.P ⧸ (B.S.subgroupOf B.P)) → ZMod 2)
    (hspec : ∀ (k : Y) (hk : k ∈ B.K),
      lam ⟨k * k, hsq k hk⟩ = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩)) :
    ∃ qM : ↥(B.K.map piB) → ZMod 2,
      (∀ (k : Y) (hk : k ∈ B.K),
        qM ⟨piB k, Subgroup.mem_map_of_mem piB hk⟩ = lam ⟨k * k, hsq k hk⟩) ∧
      (∀ (t : YB) (ht : t ∈ ((B.K ⊓ B.S) ⊔ B.R).map piB) (m : YB)
        (hm : m ∈ B.K.map piB),
        polarMul qM (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩)
          ⟨t, blockT_map_le_blockM_map B piB ht⟩ ⟨m, hm⟩ = 0) ∧
      (∀ (t : YB) (ht : t ∈ ((B.K ⊓ B.S) ⊔ B.R).map piB),
        qM ⟨t, blockT_map_le_blockM_map B piB ht⟩ = 0) := by
  classical
  haveI := B.hS
  have hRS : B.R ≤ B.S := (lemma_7_1_head B).trans inf_le_right
  -- choose a `K`-preimage of every element of `M_B`
  choose kk hkK hkk using fun m : ↥(B.K.map piB) => Subgroup.mem_map.mp m.2
  -- transport: ANY `K`-preimage computes the same `q̄`-value (fibres sit in `S`-cosets)
  have hclass : ∀ (m : ↥(B.K.map piB)) (k : Y) (hk : k ∈ B.K), piB k = (m : YB) →
      qbar (QuotientGroup.mk ⟨kk m, B.hKP (hkK m)⟩)
        = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩) := by
    intro m k hk hkm
    have hr : k⁻¹ * kk m ∈ B.R := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hkk m, hkm]
      exact inv_mul_cancel _
    have hS' : (kk m)⁻¹ * k ∈ B.S := by
      have h1 : ((k⁻¹ * kk m)⁻¹ : Y) ∈ B.S := B.S.inv_mem (hRS hr)
      rwa [mul_inv_rev, inv_inv] at h1
    have hSclass : (QuotientGroup.mk (⟨kk m, B.hKP (hkK m)⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = QuotientGroup.mk ⟨k, B.hKP hk⟩ := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr hS'
    rw [hSclass]
  -- the identity coset has `q̄`-value zero (`λ` is additive)
  have hq1 : qbar (1 : ↥B.P ⧸ B.S.subgroupOf B.P) = 0 := by
    have h := hspec 1 (one_mem _)
    rw [show (⟨1, B.hKP (one_mem _)⟩ : ↥B.P) = 1 from rfl, QuotientGroup.mk_one] at h
    rw [← h, show (⟨1 * 1, hsq 1 (one_mem _)⟩ : ↥B.R) = 1 from Subtype.ext (one_mul 1)]
    have h2 := hlam_hom 1 1
    rw [one_mul] at h2
    exact (add_left_cancel (a := lam (1 : ↥B.R)) (by rw [add_zero]; exact h2)).symm
  refine ⟨fun m => qbar (QuotientGroup.mk ⟨kk m, B.hKP (hkK m)⟩), ?_, ?_, ?_⟩
  · -- value clause
    intro k hk
    show qbar (QuotientGroup.mk ⟨kk ⟨piB k, Subgroup.mem_map_of_mem piB hk⟩,
      B.hKP (hkK _)⟩) = lam ⟨k * k, hsq k hk⟩
    rw [hclass ⟨piB k, Subgroup.mem_map_of_mem piB hk⟩ k hk rfl]
    exact (hspec k hk).symm
  · -- polar-radical clause
    intro t ht m hm
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
    have hxKS : x ∈ B.K ⊓ B.S := by
      rwa [sup_eq_left.mpr (lemma_7_1_head B)] at hx
    have hxK : x ∈ B.K := (Subgroup.mem_inf.mp hxKS).1
    have hxS : x ∈ B.S := (Subgroup.mem_inf.mp hxKS).2
    show qbar (QuotientGroup.mk
        ⟨kk ⟨piB x * piB k, mul_mem (blockT_map_le_blockM_map B piB ht) hm⟩,
          B.hKP (hkK _)⟩)
      + qbar (QuotientGroup.mk ⟨kk ⟨piB x, blockT_map_le_blockM_map B piB ht⟩,
          B.hKP (hkK _)⟩)
      + qbar (QuotientGroup.mk ⟨kk ⟨piB k, hm⟩, B.hKP (hkK _)⟩) = 0
    rw [hclass ⟨piB x * piB k, mul_mem (blockT_map_le_blockM_map B piB ht) hm⟩
        (x * k) (mul_mem hxK hk) (map_mul piB x k),
      hclass ⟨piB x, blockT_map_le_blockM_map B piB ht⟩ x hxK rfl,
      hclass ⟨piB k, hm⟩ k hk rfl]
    -- `x·k` and `k` share an `S`-coset; the `x`-coset is the identity coset
    have hxk : (QuotientGroup.mk (⟨x * k, B.hKP (mul_mem hxK hk)⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = QuotientGroup.mk ⟨k, B.hKP hk⟩ := by
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have h1 : k⁻¹ * x⁻¹ * k⁻¹⁻¹ ∈ B.S := B.hS.conj_mem x⁻¹ (B.S.inv_mem hxS) k⁻¹
      have h2 : ((x * k)⁻¹ * k : Y) = k⁻¹ * x⁻¹ * k⁻¹⁻¹ := by group
      show ((x * k)⁻¹ * k : Y) ∈ B.S
      rw [h2]
      exact h1
    have hx1 : (QuotientGroup.mk (⟨x, B.hKP hxK⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxS)
    rw [hxk, hx1, hq1, add_zero]
    exact CharTwo.add_self_eq_zero _
  · -- `T`-vanishing clause
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hxKS : x ∈ B.K ⊓ B.S := by
      rwa [sup_eq_left.mpr (lemma_7_1_head B)] at hx
    have hxK : x ∈ B.K := (Subgroup.mem_inf.mp hxKS).1
    have hxS : x ∈ B.S := (Subgroup.mem_inf.mp hxKS).2
    show qbar (QuotientGroup.mk ⟨kk ⟨piB x, blockT_map_le_blockM_map B piB ht⟩,
      B.hKP (hkK _)⟩) = 0
    rw [hclass ⟨piB x, blockT_map_le_blockM_map B piB ht⟩ x hxK rfl]
    rw [show (QuotientGroup.mk (⟨x, B.hKP hxK⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxS)]
    exact hq1

end SectionEight

end GQ2
