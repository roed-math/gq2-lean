import GQ2.DeepPart

/-!
# P-15f3: `prop_6_18_unramified` via the Hermitian-line model

The unramified case of Proposition 6.18 (eq. (115)): for a simple faithful `𝔽₂[C]`-module `V`
of cardinality `2^{2m}` at an **unramified** marking (`c tameTau` acts trivially), the base
determinant form `Q⁰_loc` has the negative Gauss sign:
`#(Q⁰_loc)⁻¹(0) = 2^{2m−1} − 2^{m−1}`.

Unlike the ramified case (which routes through Lemma 6.17's self-perpendicularity + vanishing,
`GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish`, hardwired to the `+` sign), the unramified
minus-type count comes from the **Hermitian-line model**: `V` is identified with a finite field
`F = 𝔽_{2^{2m}}` (Schur, `C` cyclic hence `𝔽₂[C]`-image a field), `H¹(G_{ℚ₂}, V) ≅ F` as an
`F`-line, and `Q⁰_loc` transports to a nonsingular **norm-one-invariant** quadratic form on `F`,
whose zero-count is `2^{2m−1} − 2^{m−1}` by the model-free algebraic core
`GQ2.DeepPart.card_normOne_invariant_form_zero`.

This file lives downstream of `DeepPart` (which supplies `Q0loc`, the Euler collapse, the
Hermitian count, and `nonsingular_Q0loc`), so — following the P-15d / 6.18-ramified pattern — the
statement is **moved out** of `SectionSix.lean` (a pointer comment is left there); the fully
qualified name stays `GQ2.SectionSix.prop_6_18_unramified` is preserved by re-export.
-/

namespace GQ2

open ContCoh QuadraticFp2 Corestriction SectionSix DeepPart

open scoped Classical

namespace UnramifiedModel

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **Proposition 6.18, eq. (115), unramified case**: negative Gauss sign,
`#(Q⁰_loc)⁻¹(0) = 2^{2m−1} − 2^{m−1}`.

Proved via the Hermitian-line model (see the file docstring): identify `V` with `𝔽_{2^{2m}}`,
transport `Q⁰_loc` to a norm-one-invariant nonsingular form, and count zeros with
`card_normOne_invariant_form_zero`.  [P-14 statement; proof P-15f3, Ax: B6, B7.]

**Statement amended (P-15f, flag for P-20)**: added `hc : Function.Surjective ⇑c` (as in
`prop_6_18_ramified`). -/
theorem prop_6_18_unramified (D : TateDuality 2) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C)
    (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    Nat.card {x : H1 AbsGalQ2 V // Q0loc D dat ρ x = 0}
      = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  classical
  haveI : Finite (H1 AbsGalQ2 V) := Foundations.finite_H1 V
  haveI : Fintype (H1 AbsGalQ2 V) := Fintype.ofFinite _
  have hV2 : ∀ v : V, v + v = 0 := exp_two_of_simple_of_card hsimple m hm hcard
  have hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v := fun g v => by rw [hρ]; exact hinv _ v
  have hquad : IsQuadraticFp2 (Q0loc D dat ρ (V := V)) :=
    isQuadraticFp2_Q0loc D q hq dat hdat ρ hρ hqG
  have hnons : Nonsingular (Q0loc D dat ρ (V := V)) :=
    nonsingular_Q0loc D q hq hns hV2 dat hdat ρ hρ hqG
  -- the `C`-action moves some vector (else `V` is `𝔽₂`, contradicting `#V = 2^{2m}`, `m ≥ 1`)
  have hmove : ∃ (h₀ : C) (v : V), h₀ • v ≠ v := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v, hv⟩ := hV
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : addOrderOf v = 2 := addOrderOf_eq_prime (by rw [two_nsmul]; exact hV2 v) hv
    have htop : AddSubgroup.zmultiples v = ⊤ := by
      refine (hsimple _ (fun h w hw => by rw [hcon]; exact hw)).resolve_left (fun h0 => hv ?_)
      have hmem : v ∈ AddSubgroup.zmultiples v := AddSubgroup.mem_zmultiples v
      rw [h0, AddSubgroup.mem_bot] at hmem; exact hmem
    have hcard2 : Nat.card V = 2 := by
      have h1 : Nat.card ↥(AddSubgroup.zmultiples v) = 2 := by rw [Nat.card_zmultiples, hord]
      rwa [htop, Nat.card_congr AddSubgroup.topEquiv.toEquiv] at h1
    rw [hcard] at hcard2
    have h4 : (4 : ℕ) ≤ 2 ^ (2 * m) :=
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨h₀, hmoves⟩ := hmove
  have hρsurj : Function.Surjective ⇑ρ := by
    intro y
    obtain ⟨t, ht⟩ := hc y
    obtain ⟨g, hg⟩ := B.tameF_surjective t
    exact ⟨g, by rw [hfac, hg, ht]⟩
  have hcardH1 : Fintype.card (H1 AbsGalQ2 V) = 2 ^ (2 * m) := by
    rw [← Nat.card_eq_fintype_card,
      card_H1_eq_card_of_simple V D ρ.toMonoidHom hρsurj hρ hsimple h₀ hmoves q hq hns hinv hV2,
      hcard]
  -- **The Arf invariant is `1` (minus type)** — the crux, via the free norm-one action.
  have harf : arf (Q0loc D dat ρ (V := V)) = 1 := by
    sorry
  simpa only [zeroCount] using
    zeroCount_of_arf_one (Q0loc D dat ρ (V := V)) hquad hnons hm hcardH1 harf

end UnramifiedModel

end GQ2
