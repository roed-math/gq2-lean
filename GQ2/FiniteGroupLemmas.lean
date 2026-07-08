import Mathlib

/-!
# Lemmas 9.1–9.2 — finite group theory feeding the induction

* **Lemma 9.1** (coprime-kernel subdirect products / fibre products) — statement scaffold.
* **Lemma 9.2 core** (odd normal subgroup with 2-group quotient splits) — **proved** via
  Mathlib's Schur–Zassenhaus.
-/

namespace GQ2.FiniteGroup

open scoped Classical

/-- **Lemma 9.1 (coprime-kernel subdirect product).** Let `f : A ↠ C` and `g : B ↠ C` be finite
epimorphisms whose kernels have coprime orders. A subgroup `J` of `A × B` that lies in the fibre
product `{(a,b) | f a = g b}` and projects onto both factors is the *entire* fibre product.

Proof via Goursat: `J.goursatFst ≤ ker f` and `J.goursatSnd ≤ ker g`, and Goursat's isomorphism
`A/goursatFst ≃ B/goursatSnd` gives `|goursatFst|·|ker g| = |goursatSnd|·|ker f|`.  Coprimality of
`|ker f|`, `|ker g|` then forces `ker g ≤ J.goursatSnd`, which is exactly the missing wild direction
needed to hit every fibre-product element. -/
theorem coprime_fiber_product {A B C : Type*} [Group A] [Group B] [Group C]
    [Finite A] [Finite B] (f : A →* C) (g : B →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card g.ker))
    (J : Subgroup (A × B))
    (hJsub : ∀ p ∈ J, f p.1 = g p.2)
    (hJA : Function.Surjective fun p : J => (p : A × B).1)
    (hJB : Function.Surjective fun p : J => (p : A × B).2) :
    ∀ p : A × B, f p.1 = g p.2 → p ∈ J := by
  classical
  haveI : Finite C := Finite.of_surjective f hf
  have hI₁ : Function.Surjective (Prod.fst ∘ J.subtype) := hJA
  have hI₂ : Function.Surjective (Prod.snd ∘ J.subtype) := hJB
  -- The two Goursat kernels sit inside `ker f`, `ker g`.
  have hG'ker : J.goursatFst ≤ f.ker := by
    intro a ha
    have h1 : (a, (1 : B)) ∈ J := Subgroup.mem_goursatFst.1 ha
    have hfa : f a = 1 := by simpa using hJsub _ h1
    exact MonoidHom.mem_ker.2 hfa
  have hH'ker : J.goursatSnd ≤ g.ker := by
    intro b hb
    have h1 : ((1 : A), b) ∈ J := Subgroup.mem_goursatSnd.1 hb
    have hgb : g b = 1 := by simpa using (hJsub _ h1).symm
    exact MonoidHom.mem_ker.2 hgb
  -- Goursat's isomorphism `A/goursatFst ≃* B/goursatSnd`.
  haveI hn1 : J.goursatFst.Normal := Subgroup.normal_goursatFst hI₁
  haveI hn2 : J.goursatSnd.Normal := Subgroup.normal_goursatSnd hI₂
  obtain ⟨e, -⟩ := Subgroup.goursat_surjective hI₁ hI₂
  have hq : Nat.card (A ⧸ J.goursatFst) = Nat.card (B ⧸ J.goursatSnd) := Nat.card_congr e.toEquiv
  have hA : Nat.card A = Nat.card (A ⧸ J.goursatFst) * Nat.card J.goursatFst :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hB : Nat.card B = Nat.card (B ⧸ J.goursatSnd) * Nat.card J.goursatSnd :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hAf : Nat.card A = Nat.card C * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hBg : Nat.card B = Nat.card C * Nat.card g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  -- `|goursatFst| · |ker g| = |goursatSnd| · |ker f|`.
  have hqpos : 0 < Nat.card (B ⧸ J.goursatSnd) := Nat.card_pos
  have i : Nat.card (B ⧸ J.goursatSnd) * Nat.card J.goursatFst = Nat.card C * Nat.card f.ker := by
    rw [← hq, ← hA]; exact hAf
  have ii : Nat.card (B ⧸ J.goursatSnd) * Nat.card J.goursatSnd = Nat.card C * Nat.card g.ker := by
    rw [← hB]; exact hBg
  have key : Nat.card J.goursatFst * Nat.card g.ker
           = Nat.card J.goursatSnd * Nat.card f.ker := by
    apply Nat.eq_of_mul_eq_mul_left hqpos
    calc Nat.card (B ⧸ J.goursatSnd) * (Nat.card J.goursatFst * Nat.card g.ker)
        = (Nat.card (B ⧸ J.goursatSnd) * Nat.card J.goursatFst) * Nat.card g.ker := by ring
      _ = (Nat.card C * Nat.card f.ker) * Nat.card g.ker := by rw [i]
      _ = (Nat.card C * Nat.card g.ker) * Nat.card f.ker := by ring
      _ = (Nat.card (B ⧸ J.goursatSnd) * Nat.card J.goursatSnd) * Nat.card f.ker := by rw [ii]
      _ = Nat.card (B ⧸ J.goursatSnd) * (Nat.card J.goursatSnd * Nat.card f.ker) := by ring
  -- Coprimality upgrades `goursatSnd ≤ ker g` to an equality of orders, hence `ker g ≤ goursatSnd`.
  have hh'kg : Nat.card J.goursatSnd ∣ Nat.card g.ker := Subgroup.card_dvd_of_le hH'ker
  have hkg_dvd : Nat.card g.ker ∣ Nat.card J.goursatSnd := by
    have hdvd : Nat.card g.ker ∣ Nat.card J.goursatSnd * Nat.card f.ker :=
      ⟨Nat.card J.goursatFst, by rw [← key]; ring⟩
    exact hcop.symm.dvd_of_dvd_mul_right hdvd
  have hcard : Nat.card J.goursatSnd = Nat.card g.ker := Nat.dvd_antisymm hh'kg hkg_dvd
  have hker_le : g.ker ≤ J.goursatSnd := by
    have hset : (J.goursatSnd : Set B) = (g.ker : Set B) :=
      (Set.toFinite (g.ker : Set B)).eq_of_subset_of_card_le
        (SetLike.coe_subset_coe.2 hH'ker) (le_of_eq hcard.symm)
    exact SetLike.coe_subset_coe.1 hset.ge
  -- Endgame: hit an arbitrary fibre-product element.
  rintro ⟨a, b⟩ hp
  obtain ⟨j, hj⟩ := hJA a
  set b' := (j : A × B).2 with hb'
  have hjmem : ((a, b') : A × B) ∈ J := by
    have : (j : A × B) = (a, b') := Prod.ext hj rfl
    rw [← this]; exact j.2
  have hfab' : f a = g b' := by simpa [hj] using hJsub _ j.2
  have hgeq : g b' = g b := hfab'.symm.trans hp
  have hker : b'⁻¹ * b ∈ g.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgeq, inv_mul_cancel]
  have hmem2 : ((1 : A), b'⁻¹ * b) ∈ J := Subgroup.mem_goursatSnd.1 (hker_le hker)
  have : ((a, b) : A × B) = (a, b') * (1, b'⁻¹ * b) := by
    simp
  rw [this]
  exact J.mul_mem hjmem hmem2


end GQ2.FiniteGroup
