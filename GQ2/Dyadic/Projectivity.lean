/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.RegularSummand.Involution

@[expose] public section

/-!
# Ramified-simple projectivity at a general residue degree (dyadic campaign, AX5)

Lemma 6.11 of the `ℚ₂` development — *a faithful ramified simple tame `𝔽₂[C]`-module is an
equivariant split summand of a regular module* — at the general tame relation
`sg⁻¹ t sg = t^{q_K}` with `q_K = 2^f`, `f ≥ 1`, rather than only at `q = 2`.

**No axiom is spent here.**  The `ℚ₂` chain
(`GQ2/RegularSummand/{Trace,Freeness,Involution,Lifting}.lean`) touches the relation exponent
in exactly one place: the two facts it derives from the tame relation,

* `(Subgroup.zpowers t).Normal` — the inertia `⟨t⟩` is normal in the image, and
* `Odd (orderOf t)` — the inertia has odd order,

are all that the thousand lines of proof body below `GQ2.lemma_6_11_of_tame_pair` ever use.
Those declarations now take the two facts as hypotheses (the `…_of_odd_normal` forms), so this
file only has to supply them at general `q` and apply the core.  The externally-consumed
`q = 2` statements (`GQ2.lemma_6_11_of_tame_pair`, `GQ2.two_torsion_of_centralizer_eq_one`,
`GQ2.lemma_6_11`) are preserved verbatim as wrappers: nothing on the `ℚ₂` path moved.

`tame_odd_order_pow` and `tame_zpowers_normal_pow` are the **finite-image** halves of the
packet's Lemmas 3.1 and 3.2 (the `q = 2` cases are `GQ2.Tame.tame_odd_order` and
`GQ2.Tame.zpowers_normal_of_tame`).  The profinite `T_q` statements belong to the F-lane and
should be built on these rather than reproved.

## Attribution

Lemma 6.11 is the paper's own assembly rather than a single literature theorem: relative
projectivity and the trace criterion are Higman, *Modules with a group of operators*,
Duke Math. J. **21** (1954) 369–376, and the isotypic bookkeeping is Clifford,
*Representations induced in an invariant subgroup*, Ann. of Math. (2) **38** (1937) 533–550
(both citations inherited from `GQ2.RegularSummand`, unverified at page level here).  Mathlib
has neither Higman's criterion nor Clifford theory, and its Maschke averaging
(`LinearMap.equivariantProjection`) needs `|C|` invertible — false in characteristic `2`; the
odd-index relative trace `GQ2.regular_summand_of_subgroup_summand` is the characteristic-`2`
substitute and divides by nothing.
-/

namespace GQ2.Dyadic

variable {G : Type*} [Group G]

/-- Iterated conjugation at a general exponent: `(sⁿ)⁻¹ t sⁿ = t^(qⁿ)`.  The `q = 2` case is
`GQ2.Tame.conj_pow_iterate`. -/
theorem conj_pow_iterate_pow {s t : G} {q : ℕ} (h : s⁻¹ * t * s = t ^ q) :
    ∀ n : ℕ, (s ^ n)⁻¹ * t * s ^ n = t ^ (q ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have step : (s ^ (k + 1))⁻¹ * t * s ^ (k + 1)
        = (s ^ k)⁻¹ * (s⁻¹ * t * s) * s ^ k := by group
    rw [step, h]
    have conj_q : (s ^ k)⁻¹ * t ^ q * s ^ k = ((s ^ k)⁻¹ * t * s ^ k) ^ q := by
      have hc := conj_pow (a := (s ^ k)⁻¹) (b := t) (i := q)
      simpa using hc.symm
    rw [conj_q, ih, ← pow_mul, ← pow_succ]

/-- **Packet Lem. 3.1 at general `q` (finite image).**  If `s` has finite order and
`s⁻¹ t s = t^q` with `q` even and nonzero (in particular `q = q_K = 2^f`, `f ≥ 1`), then `t` has
odd order: conjugating by `s^{orderOf s} = 1` gives `t^(q^k) = t`, so `orderOf t ∣ q^k - 1`,
which is odd. -/
theorem tame_odd_order_pow {s t : G} {q : ℕ} (hs : orderOf s ≠ 0) (hq0 : q ≠ 0) (hq : Even q)
    (h : s⁻¹ * t * s = t ^ q) : Odd (orderOf t) := by
  set k := orderOf s with hk
  have hconj := conj_pow_iterate_pow h k
  rw [pow_orderOf_eq_one] at hconj
  simp only [inv_one, one_mul, mul_one] at hconj
  have hpos : 1 ≤ q ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq0)
  have hone : t ^ (q ^ k - 1) = 1 := by
    rw [← mul_left_inj t, one_mul, ← pow_succ, Nat.sub_add_cancel hpos, ← hconj]
  have hdvd : orderOf t ∣ q ^ k - 1 := orderOf_dvd_of_pow_eq_one hone
  rcases Nat.even_or_odd (orderOf t) with he | ho
  · exfalso
    have hd1 : (2 : ℕ) ∣ q ^ k - 1 := he.two_dvd.trans hdvd
    have h2q : (2 : ℕ) ∣ q ^ k := (Even.two_dvd hq).trans (dvd_pow_self q hs)
    omega
  · exact ho

/-- `⟨t^q⟩ = ⟨t⟩` when `q` is prime to `orderOf t`. -/
theorem zpowers_pow_eq_of_coprime {t : G} {q : ℕ} (hcop : Nat.Coprime q (orderOf t)) :
    Subgroup.zpowers (t ^ q) = Subgroup.zpowers t := by
  refine le_antisymm (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) q))
    (Subgroup.zpowers_le.2 ?_)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]; exact hm⟩

/-- **Packet Lem. 3.2 at general `q` (finite image).**  `⟨t⟩ ◁ ⟨s,t⟩` whenever `s⁻¹ t s = t^q`.
No hypothesis on `q` is needed: conjugation is an automorphism, so `t ↦ t^q` preserves the order
of `t`, which already forces `gcd(q, orderOf t) = 1` and hence `⟨t^q⟩ = ⟨t⟩`. -/
theorem tame_zpowers_normal_pow {s t : G} [Finite G] {q : ℕ}
    (hgen : Subgroup.closure {s, t} = ⊤) (h : s⁻¹ * t * s = t ^ q) :
    (Subgroup.zpowers t).Normal := by
  have hcop : Nat.Coprime q (orderOf t) := by
    have hsc : SemiconjBy s⁻¹ t (t ^ q) := by
      show s⁻¹ * t = t ^ q * s⁻¹
      rw [← h]; group
    have hconj : orderOf t = orderOf (t ^ q) := hsc.orderOf_eq
    rw [orderOf_pow t] at hconj
    have hpos : 0 < orderOf t := orderOf_pos t
    have hgpos : 0 < Nat.gcd (orderOf t) q :=
      Nat.pos_of_ne_zero fun h0 => by rw [Nat.gcd_eq_zero_iff] at h0; omega
    have : Nat.gcd (orderOf t) q = 1 := by
      by_contra hne
      have h1 : 1 < Nat.gcd (orderOf t) q := by omega
      have hlt := Nat.div_lt_self hpos h1
      omega
    exact Nat.coprime_comm.mp this
  have hmaps : (Subgroup.zpowers t).map (MulAut.conj s⁻¹).toMonoidHom = Subgroup.zpowers t := by
    have hc : (MulAut.conj s⁻¹).toMonoidHom t = t ^ q := by
      show s⁻¹ * t * s⁻¹⁻¹ = t ^ q
      rw [inv_inv]; exact h
    rw [MonoidHom.map_zpowers, hc]; exact zpowers_pow_eq_of_coprime hcop
  have hs_norm : s ∈ Subgroup.normalizer (Subgroup.zpowers t) := by
    have hinv := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmaps
    simpa using Subgroup.inv_mem _ hinv
  have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers t) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers t)
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  exacts [SetLike.mem_coe.2 hs_norm, SetLike.mem_coe.2 ht_norm]

/-- **Lemma 6.11 at general `q_K = 2^f`** (the AX5 deliverable): a faithful ramified simple
2-torsion module over a finite group generated by a tame pair `(sg, t)` at
`sg⁻¹ t sg = t^(2^f)`, `f ≥ 1`, is an equivariant split summand of a regular module.  The
regular module is `Fin N → C → ZMod 2` with the left-translation action spelled inline, `ι` the
equivariant embedding and `r` the equivariant retraction; this split-summand shape is what the
two consumers of projectivity (`GQ2.equivariant_lift_of_regular_summand` for
`Hom_C(V^∨, −)`-exactness, and `GQ2.Shapiro.familiesExtend_of_package` for the surjective half
of inflation–restriction) actually use.

The two leaves above supply the odd-normal input, and the whole `q = 2` chain — cyclic Sylow
2-subgroup, vanishing inertia fixed space, the `O₂`-linchpin, the `𝔽₂`-rational trace element,
the counting criterion for freeness over the Sylow subgroup, and the odd-index relative
trace — runs verbatim as `GQ2.lemma_6_11_of_odd_normal`. -/
theorem lemma_6_11_of_tame_pair_pow {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} {f : ℕ} (hf : 1 ≤ f)
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ (2 ^ f))
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v := by
  have heven : Even (2 ^ f) := by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨2 ^ f', by rw [pow_succ]; ring⟩
  exact lemma_6_11_of_odd_normal hgen (tame_zpowers_normal_pow hgen hrel)
    (tame_odd_order_pow (orderOf_pos sg).ne' (pow_ne_zero _ two_ne_zero) heven hrel)
    hV2 hfaith hsimple hram

end GQ2.Dyadic
