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
*(Statement scaffold; proof deferred.)* -/
theorem coprime_fiber_product {A B C : Type*} [Group A] [Group B] [Group C]
    [Finite A] [Finite B] (f : A →* C) (g : B →* C)
    (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card g.ker))
    (J : Subgroup (A × B))
    (hJsub : ∀ p ∈ J, f p.1 = g p.2)
    (hJA : Function.Surjective fun p : J => (p : A × B).1)
    (hJB : Function.Surjective fun p : J => (p : A × B).2) :
    ∀ p : A × B, f p.1 = g p.2 → p ∈ J := by
  sorry

/-- **Lemma 9.2 (core splitting).** If `N ◁ Y` is a normal subgroup of *odd* order whose quotient
`Y/N` is a `2`-group, then `N` has a complement in `Y` (so `Y = N ⋊ K` with `K ≅ Y/N` a 2-group).
This is the Schur–Zassenhaus input to the terminal case of the induction (paper Lemma 9.2). -/
theorem oddOrder_twoQuotient_split {Y : Type*} [Group Y] [Finite Y]
    (N : Subgroup Y) [N.Normal] (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 (Y ⧸ N)) :
    ∃ K : Subgroup Y, N.IsComplement' K := by
  -- The index `[Y : N] = |Y/N|` is a power of 2.
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hidx : N.index = 2 ^ n := by
    rw [Subgroup.index_eq_card]; exact hn
  -- `|N|` is odd, hence coprime to 2, hence to `2 ^ n = [Y : N]`.
  have hnd : ¬ (2 : ℕ) ∣ Nat.card N := by
    have hm := Nat.odd_iff.mp hN
    omega
  have hcop2 : Nat.Coprime (Nat.card N) 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnd).symm
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hidx]; exact hcop2.pow_right n
  -- Schur–Zassenhaus.
  exact Subgroup.exists_right_complement'_of_coprime hcop

end GQ2.FiniteGroup
