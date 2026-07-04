import GQ2.GaussCount

/-!
# Gauss signs: assembly layer for Lemma 6.8 / Proposition 6.9  (ticket P-15b)

Proof-side bricks for the Gauss-sign pair (§6.2), stated **below** `GQ2/SectionSix.lean` in the
import order (this file must not import `SectionSix`, which will consume it — the P-15c cycle
lesson).  Everything here is abstract over the acting group / the isometry; the `SectionSix`
splices instantiate `U := powOmega2 (c tameSigma)` and `G := Hf`.

* `arf_qDouble_eq_zero` — **the final clause of Lemma 6.8 from (87) + (88)**: if `arf q = s`
  and the rank exponent `k` of `1 + U` has `k ≡ s (mod 2)`, then `arf (q_U) = 0`.  This
  consumes the now-proved Wall sign (`gaussSum_qDouble`, P-15a).
* `zeroCount_qDouble_of_arf_zero` — **the ramified count of Proposition 6.9 from
  `arf (q_U) = 0`**: the doubling of a nonsingular form by a 2-power isometry is nonsingular
  (`qDouble_nonsingular`), so the engine's `zeroCount_of_arf_zero` evaluates `#(q_U)⁻¹(0)`.
* `central_two_pow_smul_eq_one` — a central element of 2-power order acting on a nontrivial
  faithful simple exponent-2 module is trivial (its fixed space is a nonzero submodule by
  `exists_fixed_ne_zero`).  This is the source of the oddness of tame images in both branches
  of 6.8/6.9 (the paper's "cyclic 2-group acting in characteristic 2 has nonzero fixed
  vectors" step).

No `sorry` in this file.
-/

namespace GQ2

namespace GaussSigns

open QuadraticFp2

variable {V : Type*} [AddCommGroup V] [Finite V]

/-- **Lemma 6.8, final clause, from (87) and (88)**: for a nonsingular `q` and a 2-power-order
isometry `U` with `arf q = s` and rank exponent `k ≡ s (mod 2)` for `N = 1 + U`, the doubling
has `arf (q_U) = 0`.  (Wall's relation `arf (q_U) = arf q + k`, now fully proved, plus
`s + s = 0`.) -/
theorem arf_qDouble_eq_zero (q : V → ZMod 2) (U : V ≃+ V) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (hUq : ∀ v, q (U v) = q v)
    (hU2 : ∃ n, (⇑U)^[2 ^ n] = id) (N : V →+ V) (hN : ∀ x, N x = x + U x)
    {k : ℕ} (hk : Nat.card ↥N.range = 2 ^ k) {s : ZMod 2} (h87 : arf q = s)
    (h88 : (k : ZMod 2) = s) : arf (qDouble q ⇑U) = 0 := by
  letI : Fintype V := Fintype.ofFinite V
  have harf := arf_qDouble_of_gaussSum_sign q U (gaussSum_ne_zero q hq hns)
    (gaussSum_qDouble q U hq h2 hns hUq hU2 N hN hk)
  rw [harf, h87, h88]
  exact CharTwo.add_self_eq_zero s

/-- **The ramified count of Proposition 6.9 from `arf (q_U) = 0`**: the doubling is
nonsingular, and a nonsingular form of trivial Arf invariant on `2^(2m)` points has
`2^(2m−1) + 2^(m−1)` zeros. -/
theorem zeroCount_qDouble_of_arf_zero (q : V → ZMod 2) (U : V ≃+ V) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (hUq : ∀ v, q (U v) = q v)
    (hU2 : ∃ n, (⇑U)^[2 ^ n] = id) (harf : arf (qDouble q ⇑U) = 0)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q ⇑U) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  letI : Fintype V := Fintype.ofFinite V
  have hqU : IsQuadraticFp2 (qDouble q ⇑U) := by
    constructor
    · rw [qDouble, hq.map_zero, map_zero, polar_self q hq h2, add_zero]
    · intro u v w
      rw [polar_qDouble_eq q U hq hUq, polar_qDouble_eq q U hq hUq,
        polar_qDouble_eq q U hq hUq, hq.polar_add_left]
    · intro u v w
      rw [polar_qDouble_eq q U hq hUq, polar_qDouble_eq q U hq hUq,
        polar_qDouble_eq q U hq hUq, ← hq.polar_add_right]
      congr 1
      rw [map_add, map_add]
      abel
  exact zeroCount_of_arf_zero (qDouble q ⇑U) hqU
    (qDouble_nonsingular q U hq h2 hns hUq hU2) hm
    (by rw [← Nat.card_eq_fintype_card]; exact hcard) harf

/-- **The Arf pinch** (unramified 6.9, arithmetic half): if both the nonzero zeros and the
nonzeros of a nonsingular `q` on `2^(2m)` points come in packets of size `n` (as they do for
the free action of an invariance group of odd order `n`), then `arf q = 0` would force
`n ∣ 2^m − 1`; so if that is excluded, `arf q = 1`.  (The two candidate zero counts
`2^(2m−1) ± 2^(m−1)` differ from the divisibility constraints by exactly `2^m ∓ 1`.) -/
theorem arf_eq_one_of_dvd (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {m n : ℕ} (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (hdvd0 : n ∣ zeroCount q - 1) (hdvd1 : n ∣ 2 ^ (2 * m) - zeroCount q)
    (hnot : ¬ n ∣ 2 ^ m - 1) : arf q = 1 := by
  letI : Fintype V := Fintype.ofFinite V
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz (arf q) with h0 | h1
  · exfalso
    have hzc := zeroCount_of_arf_zero q hq hns hm
      (by rw [← Nat.card_eq_fintype_card]; exact hcard) h0
    rw [hzc] at hdvd0 hdvd1
    have h2m : (2 : ℕ) ^ (2 * m) = 2 ^ (2 * m - 1) + 2 ^ (2 * m - 1) := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have hmm' : (2 : ℕ) ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have hsub := Nat.dvd_sub hdvd0 hdvd1
    have hle : (2 : ℕ) ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hone : (1 : ℕ) ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    have harith : (2 ^ (2 * m - 1) + 2 ^ (m - 1) - 1)
        - (2 ^ (2 * m) - (2 ^ (2 * m - 1) + 2 ^ (m - 1))) = 2 ^ m - 1 := by
      omega
    rw [harith] at hsub
    exact hnot hsub
  · exact h1

variable {G : Type*} [Group G] [DistribMulAction G V]

omit [Finite V] in
/-- A **central element of 2-power order acts trivially** on a nontrivial faithful simple
exponent-2 module: its fixed space is nonzero (`exists_fixed_ne_zero`) and a submodule (by
centrality), hence everything by simplicity, hence the element is `1` by faithfulness. -/
theorem central_two_pow_smul_eq_one (h2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : G), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (u : G) (hcentral : ∀ g : G, u * g = g * u) (hu : ∃ j : ℕ, u ^ 2 ^ j = 1) :
    u = 1 := by
  obtain ⟨j, hj⟩ := hu
  obtain ⟨v₀, hv₀⟩ := hV
  -- the action of `u` as an additive equivalence of 2-power order
  have hUiter : (⇑(DistribMulAction.toAddEquiv V u))^[2 ^ j] = id := by
    funext v
    show (u • ·)^[2 ^ j] v = v
    rw [smul_iterate, hj]
    exact one_smul G v
  obtain ⟨a, ha0, hMa⟩ :=
    exists_fixed_ne_zero h2 j (DistribMulAction.toAddEquiv V u) hUiter v₀ hv₀
  -- the fixed space of `u`
  let W : AddSubgroup V :=
    { carrier := {v : V | u • v = v}
      add_mem' := fun hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, hx, hy]
      zero_mem' := smul_zero u
      neg_mem' := fun hx => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, hx] }
  have hstab : ∀ (g : G), ∀ w ∈ W, g • w ∈ W := by
    intro g w hw
    show u • (g • w) = g • w
    rw [← mul_smul, hcentral g, mul_smul]
    exact congrArg (g • ·) hw
  rcases hsimple W hstab with hbot | htop
  · exact absurd ((AddSubgroup.mem_bot).mp (hbot ▸ (hMa : u • a = a) : a ∈ (⊥ : AddSubgroup V)))
      ha0
  · exact hfaith u fun v => (htop ▸ AddSubgroup.mem_top v : v ∈ W)

end GaussSigns

end GQ2
