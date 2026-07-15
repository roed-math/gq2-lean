/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.RegularSummand.Freeness

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The involution kernel for Lemma 6.11

The fixed-point bound for the involution in a cyclic Sylow `2`-subgroup and the resulting ramified tame-pair freeness package.
See `GQ2.RegularSummand` for the paper-facing overview and references.
-/

namespace GQ2

/-! ## The weight-orbit kernel: the involution counting bound

`involution_fixedPoints_sq_le` was the last `sorry` of the `lemma_6_11` chain (the paper's
pp. 29–30 weight-orbit content).  It is proved here by an **explicit `𝔽₂`-rational trace
element** — a recorded deviation from the paper's `𝔽̄₂` weight-orbit argument: no base
change, no idempotent decomposition, no semilinear algebra.

Set `t := c τ`, of odd order `m` with `⟨t⟩ ⊴ C`, and let `ω = g₀^{2^{s-1}}` be the
involution of the cyclic Sylow-2 subgroup (`s ≥ 1`; the trivial-Sylow case is handled by
the consumer).  Conjugation gives `ω t ω⁻¹ = t^q` with `q² ≡ 1 (mod m)`.

* **`ω` centralizes `⟨t⟩` (`q ≡ 1`) — impossible** (`two_torsion_of_centralizer_eq_one`,
  the `O₂`-linchpin of Remark 6.12): the centralizer `D := C_C(⟨t⟩)` is abelian (`⟨t⟩` is
  central in it and `D/⟨t⟩` embeds in the cyclic `C/⟨t⟩`), hence its 2-torsion `S` is a
  normal 2-subgroup of `C` containing `ω`; a 2-group acting on the even-cardinality module
  `V` has a second fixed point beyond `0` (orbit counting), the `S`-fixed subgroup is
  `C`-stable by normality, so simplicity forces `S` to act trivially — against faithfulness
  and `ω ≠ 1`.

* **Otherwise, an explicit trace element.**  `g := gcd(q−1, m)` is a *unitary* divisor:
  `gcd(q−1, m/g) = 1` (`coprime_sub_one_div_gcd`, from `m ∣ (q−1)(q+1)` and `m` odd).  So on
  `u := t^g`, of order `r := m/g`, multiplication by `q` is a **fixed-point-free involution
  of `(ZMod r) ∖ {0}`**.  Every nontrivial power of `t` has zero fixed space
  (`fixedPoints_zpowers_tame_eq_zero`: its fixed subgroup is `C`-stable since `⟨t⟩ ⊴ C`, and
  faithfulness kills `⊤`), so the geometric sum `∑_{j<r} u^j • v` vanishes
  (`sum_range_orderOf_smul_eq_zero`).  For `ω`-fixed `v`, summing over the `val`-smaller
  half `Λ` of each pair `{k, qk}` gives `w := ∑_{k∈Λ} u^{k.val} • v` with
  `w + ω•w = ∑_{k≠0} u^{k.val} • v = v` — an explicit additive-Hilbert-90 trace.  Hence
  `ker(1+ω) ⊆ range(1+ω)`, and `#V^ω ^ 2 ≤ #ker·#range = #V` by first-isomorphism
  counting. -/

section InvolutionKernel

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V]

/-- **Every nontrivial element of the inertia `⟨t⟩` has zero fixed space** on a faithful
simple module — the "all isotypic factors are faithful" content of the weight-orbit plan, in
operator form.  The fixed space of `n = t^k` is `C`-stable (a conjugate `h⁻¹ n h = (h⁻¹th)^k`
is again a power of `n` since `h⁻¹th ∈ ⟨t⟩` by normality); simplicity leaves `⊥` or `⊤`, and
`⊤` makes `n` act trivially, so `n = 1` by faithfulness. -/
theorem fixedPoints_zpowers_tame_eq_zero {sg t : C}
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    {n : C} (hn : n ∈ Subgroup.zpowers t) (hn1 : n ≠ 1) :
    ∀ v : V, n • v = v → v = 0 := by
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  set W : AddSubgroup V :=
    { carrier := {v | n • v = v}
      zero_mem' := smul_zero n
      add_mem' := fun ha hb => by
        show n • (_ + _) = _
        rw [smul_add, ha, hb]
      neg_mem' := fun ha => by
        show n • (-_) = -_
        rw [smul_neg, ha] } with hWdef
  have hstable : ∀ (h : C), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    have hconjt : h⁻¹ * t * h ∈ Subgroup.zpowers t := by
      have h1 := hnorm.conj_mem t (Subgroup.mem_zpowers t) h⁻¹
      rwa [inv_inv] at h1
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hconjt
    have hpow : h⁻¹ * n * h = n ^ a := by
      have e1 : (h⁻¹ * t * h) ^ k = h⁻¹ * t ^ k * h := by
        have e0 := conj_zpow (i := k) (a := h⁻¹) (b := t)
        rwa [inv_inv] at e0
      rw [← hk, ← e1, ← ha, ← zpow_mul, mul_comm, zpow_mul]
    have hfix : (h⁻¹ * n * h) • w = w := by
      rw [hpow]
      exact zpow_mem (show n ∈ MulAction.stabilizer C w from hw) a
    show n • (h • w) = h • w
    calc n • (h • w) = (n * h) • w := (mul_smul n h w).symm
      _ = (h * (h⁻¹ * n * h)) • w := by group
      _ = h • ((h⁻¹ * n * h) • w) := mul_smul _ _ _
      _ = h • w := by rw [hfix]
  rcases hsimple W hstable with hbot | htop
  · intro v hv
    have hvW : v ∈ W := hv
    rwa [hbot, AddSubgroup.mem_bot] at hvW
  · exact absurd (hfaith n fun v => (htop ▸ AddSubgroup.mem_top v : v ∈ W)) hn1

omit [Finite C] in
/-- The **geometric sum** of a fixed-point-free finite-order action vanishes: the sum
`∑_{j < orderOf u} u^j • v` is `u`-invariant, so it lies in the zero fixed space. -/
theorem sum_range_orderOf_smul_eq_zero {u : C}
    (hfree : ∀ v : V, u • v = v → v = 0) (v : V) :
    ∑ j ∈ Finset.range (orderOf u), u ^ j • v = 0 := by
  refine hfree _ ?_
  rw [Finset.smul_sum]
  have hstep : ∀ j : ℕ, u • (u ^ j • v) = u ^ (j + 1) • v := fun j => by
    rw [← mul_smul, ← pow_succ']
  rw [Finset.sum_congr rfl fun j _ => hstep j]
  have h1 := Finset.sum_range_succ' (fun j => u ^ j • v) (orderOf u)
  have h2 := Finset.sum_range_succ (fun j => u ^ j • v) (orderOf u)
  have h3 : (∑ j ∈ Finset.range (orderOf u), u ^ (j + 1) • v) + u ^ 0 • v
      = (∑ j ∈ Finset.range (orderOf u), u ^ j • v) + u ^ orderOf u • v := h1.symm.trans h2
  rw [pow_zero, one_smul, pow_orderOf_eq_one, one_smul] at h3
  exact add_right_cancel h3

/-- Arithmetic core of the trace construction: for `m` odd with `m ∣ (q−1)(q+1)`, the gcd
`g := gcd(q−1, m)` is a *unitary* divisor — `gcd(q−1, m/g) = 1`.  (For any prime `p ∣ q−1`
dividing `m`, oddness forces `p ∤ q+1`, so the full `p`-part of `m` divides `q−1` and hence
`g`; nothing survives into `m/g`.) -/
private theorem coprime_sub_one_div_gcd {q m : ℕ} (hm : 0 < m) (hmodd : Odd m)
    (hq1 : 1 ≤ q) (hdvd : m ∣ (q - 1) * (q + 1)) :
    Nat.Coprime (q - 1) (m / Nat.gcd (q - 1) m) := by
  set g := Nat.gcd (q - 1) m with hg
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hr0 : 0 < m / g := Nat.div_pos (Nat.le_of_dvd hm hgm) hg0
  by_contra hcop
  obtain ⟨p, hp, hpq1, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpm : p ∣ m := hpr.trans (Nat.div_dvd_of_dvd hgm)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hpm)
  have hpq1' : ¬ p ∣ q + 1 := by
    intro hpq1p
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub hpq1p hpq1
      have : q + 1 - (q - 1) = 2 := by omega
      rwa [this] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hpe : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
  have hpeq : p ^ m.factorization p ∣ q - 1 := by
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ (hpe.trans hdvd)
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq1')
  have hpeg : p ^ m.factorization p ∣ g := Nat.dvd_gcd hpeq hpe
  have hge : m.factorization p ≤ g.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hg0.ne').mp hpeg
  have hfe : (m / g).factorization p = m.factorization p - g.factorization p := by
    rw [Nat.factorization_div hgm, Finsupp.tsub_apply]
  have h1r : 1 ≤ (m / g).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hr0.ne').mp hpr
  omega

/-- **The `O₂`-linchpin (Remark 6.12)**: on a nonzero faithful simple 2-torsion module, an
element of order dividing 2 commuting with the inertia generator `t` is trivial.  The
centralizer `D := C_C(⟨t⟩)` is abelian (`⟨t⟩ ≤ Z(D)` and `D/⟨t⟩` embeds in the cyclic
`C/⟨t⟩`, so `commutative_of_cyclic_center_quotient` applies); its 2-torsion `S` is therefore
a subgroup, normal in `C`, and `IsPGroup 2`.  A 2-group acting on a module of even
cardinality with one fixed point has another
(`IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`), so the `S`-fixed subgroup
is nonzero and `C`-stable, hence `⊤` by simplicity: `S` acts trivially and faithfulness
collapses it. -/
theorem two_torsion_of_centralizer_eq_one [Finite V] {sg t : C}
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV0 : ∃ v₀ : V, v₀ ≠ (0 : V))
    {x : C} (hx2 : x ^ 2 = 1) (hxt : x * t = t * x) : x = 1 := by
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  haveI hqcyc : IsCyclic (C ⧸ Subgroup.zpowers t) := quotient_zpowers_isCyclic_of_tame hgen
  set D : Subgroup C := Subgroup.centralizer (Subgroup.zpowers t : Set C) with hD
  have hDn : D.Normal := by rw [hD]; infer_instance
  have hxD : x ∈ D := by
    rw [hD]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    exact ((Commute.zpow_right hxt k).symm).eq
  -- `D` is abelian: `⟨t⟩ ≤ Z(D)` and `D/⟨t⟩` embeds in the cyclic quotient
  have hDcomm : IsMulCommutative ↥D := by
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      ((QuotientGroup.mk' (Subgroup.zpowers t)).comp D.subtype) ?_
    intro d hd
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hd
    have hdt : (d : C) ∈ Subgroup.zpowers t := (QuotientGroup.eq_one_iff _).mp hd
    refine Subgroup.mem_center_iff.mpr fun a => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp a.2 (d : C) hdt).symm
  have hDab : ∀ a b : ↥D, a * b = b * a := fun a b => hDcomm.is_comm.comm a b
  -- the 2-torsion of `D`: a normal 2-subgroup of `C` containing `x`
  set S : Subgroup C :=
    { carrier := {y : C | y ∈ D ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}
      one_mem' := ⟨D.one_mem, 0, one_pow _⟩
      mul_mem' := by
        rintro a b ⟨haD, ka, hka⟩ ⟨hbD, kb, hkb⟩
        refine ⟨D.mul_mem haD hbD, ka + kb, ?_⟩
        have hcomm : Commute a b := congrArg Subtype.val (hDab ⟨a, haD⟩ ⟨b, hbD⟩)
        have ha' : a ^ 2 ^ (ka + kb) = 1 := by rw [pow_add, pow_mul, hka, one_pow]
        have hb' : b ^ 2 ^ (ka + kb) = 1 := by
          rw [pow_add, mul_comm (2 ^ ka), pow_mul, hkb, one_pow]
        rw [hcomm.mul_pow, ha', hb', one_mul]
      inv_mem' := by
        rintro a ⟨haD, ka, hka⟩
        exact ⟨D.inv_mem haD, ka, by rw [inv_pow, hka, inv_one]⟩ } with hS
  have hSn : S.Normal := by
    constructor
    rintro y ⟨hyD, k, hk⟩ g
    refine ⟨hDn.conj_mem y hyD g, k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have hSp : IsPGroup 2 ↥S := by
    intro y
    obtain ⟨-, k, hk⟩ := y.2
    exact ⟨k, Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hk)⟩
  -- orbit counting: a second `S`-fixed point beyond `0`
  have h2V : (2 : ℕ) ∣ Nat.card V := by
    letI : Module (ZMod 2) V := AddCommGroup.zmodModule fun v => (two_nsmul v).trans (hV2 v)
    haveI : Fintype V := Fintype.ofFinite V
    haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
    obtain ⟨v₀, hv₀⟩ := hV0
    haveI : Nontrivial V := ⟨v₀, 0, hv₀⟩
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  have hfix0 : (0 : V) ∈ MulAction.fixedPoints ↥S V := fun y => smul_zero y
  obtain ⟨w, hwfix, hw0⟩ :=
    hSp.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2V hfix0
  -- the `S`-fixed subgroup is `C`-stable and nonzero, hence `⊤`
  set W : AddSubgroup V :=
    { carrier := {v : V | ∀ y ∈ S, y • v = v}
      zero_mem' := fun y _ => smul_zero y
      add_mem' := fun ha hb y hy => by rw [smul_add, ha y hy, hb y hy]
      neg_mem' := fun ha y hy => by rw [smul_neg, ha y hy] } with hW
  have hstable : ∀ (h : C), ∀ w' ∈ W, h • w' ∈ W := by
    intro h w' hw' y hy
    have hyc : h⁻¹ * y * h ∈ S := by
      have h1 := hSn.conj_mem y hy h⁻¹
      rwa [inv_inv] at h1
    calc y • (h • w') = (y * h) • w' := (mul_smul y h w').symm
      _ = (h * (h⁻¹ * y * h)) • w' := by group
      _ = h • ((h⁻¹ * y * h) • w') := mul_smul _ _ _
      _ = h • w' := by rw [hw' _ hyc]
  have hwW : w ∈ W := fun y hy => hwfix ⟨y, hy⟩
  have hWtop : W = ⊤ := by
    rcases hsimple W hstable with hbot | htop
    · exfalso
      rw [hbot, AddSubgroup.mem_bot] at hwW
      exact hw0 hwW.symm
    · exact htop
  have hxS : x ∈ S := ⟨hxD, 1, by rw [pow_one]; exact hx2⟩
  refine hfaith x fun v => ?_
  have hvW : v ∈ W := hWtop ▸ AddSubgroup.mem_top v
  exact hvW x hxS

end InvolutionKernel

/-- **First-isomorphism counting for a self-retracting endomorphism.**  If every element of
`ker A` lies in `range A` for an endomorphism `A` of a finite abelian group `V`, then
`#(ker A) ^ 2 ≤ #V`, since `#V = #(range A) · #(ker A)` and `#(ker A) ≤ #(range A)`. -/
private lemma card_ker_sq_le_of_ker_le_range {V : Type} [AddCommGroup V] [Finite V]
    (A : V →+ V) (hle : A.ker ≤ A.range) : Nat.card ↥A.ker ^ 2 ≤ Nat.card V := by
  have hcardle : Nat.card ↥A.ker ≤ Nat.card ↥A.range := AddSubgroup.card_le_of_le hle
  have hiso : Nat.card (V ⧸ A.ker) = Nat.card ↥A.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange A).toEquiv
  have hprod : Nat.card V = Nat.card ↥A.range * Nat.card ↥A.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup A.ker, hiso]
  calc Nat.card ↥A.ker ^ 2 = Nat.card ↥A.ker * Nat.card ↥A.ker := by rw [pow_two]
    _ ≤ Nat.card ↥A.range * Nat.card ↥A.ker := Nat.mul_le_mul_right _ hcardle
    _ = Nat.card V := hprod.symm

/-- **The multiply-by-`q` pairing of `(ZMod r) ∖ {0}`.**  When `q` is a unitary involution in
`ZMod r` (`q² = 1`) with `q − 1` coprime to `r`, the map `k ↦ q·k` is a fixed-point-free
involution of `(ZMod r) ∖ {0}`; the two `val`-comparison halves `Λ₁, Λ₂` partition
`(ZMod r) ∖ {0}` and are swapped by `k ↦ q·k`.  (The unitary hypothesis `hcast` and the
coprimality `hcop` are what make the involution fixed-point-free.) -/
private lemma exists_transversal_pairing {r : ℕ} [NeZero r] (q : ℕ)
    (hcop : Nat.Coprime (q - 1) r) (hcast : (q : ZMod r) * (q : ZMod r) = 1) (hq1 : 1 ≤ q) :
    ∃ Λ₁ Λ₂ : Finset (ZMod r), Disjoint Λ₁ Λ₂ ∧
      Λ₁ ∪ Λ₂ = Finset.univ.erase (0 : ZMod r) ∧
      (∀ k ∈ Λ₁, (q : ZMod r) * k ∈ Λ₂) ∧ (∀ k ∈ Λ₂, (q : ZMod r) * k ∈ Λ₁) ∧
      ∀ k : ZMod r, (q : ZMod r) * ((q : ZMod r) * k) = k := by
  have hinv2 : ∀ k : ZMod r, (q : ZMod r) * ((q : ZMod r) * k) = k := fun k => by
    rw [← mul_assoc, hcast, one_mul]
  have hval_inj : ∀ a b : ZMod r, ZMod.val a = ZMod.val b → a = b := by
    intro a b h
    have ha := ZMod.natCast_rightInverse (n := r) a
    have hb := ZMod.natCast_rightInverse (n := r) b
    rw [← ha, ← hb, h]
  have hqfix : ∀ k : ZMod r, k ≠ 0 → (q : ZMod r) * k ≠ k := by
    intro k hk0 hfix
    have h1 : ((q - 1 : ℕ) : ZMod r) * k = 0 := by
      rw [Nat.cast_sub hq1, Nat.cast_one, sub_mul, one_mul, hfix, sub_self]
    have hunit : IsUnit ((q - 1 : ℕ) : ZMod r) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
    exact hk0 ((IsUnit.mul_right_eq_zero hunit).mp h1)
  have hq0' : ∀ k : ZMod r, k ≠ 0 → (q : ZMod r) * k ≠ 0 := fun k hk0 h0 =>
    hk0 (by rw [← hinv2 k, h0, mul_zero])
  refine ⟨Finset.univ.filter (fun k => k ≠ 0 ∧ ZMod.val k < ZMod.val ((q : ZMod r) * k)),
    Finset.univ.filter (fun k => k ≠ 0 ∧ ZMod.val ((q : ZMod r) * k) < ZMod.val k),
    ?_, ?_, ?_, ?_, hinv2⟩
  · rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega
  · ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (⟨hk0, -⟩ | ⟨hk0, -⟩) <;> exact hk0
    · intro hk0
      have hne : ZMod.val ((q : ZMod r) * k) ≠ ZMod.val k := fun h =>
        hqfix k hk0 (hval_inj _ _ h)
      rcases Nat.lt_or_ge (ZMod.val k) (ZMod.val ((q : ZMod r) * k)) with h | h
      · exact Or.inl ⟨hk0, h⟩
      · exact Or.inr ⟨hk0, by omega⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨Finset.mem_univ _, hq0' k hk.2.1, ?_⟩
    rw [hinv2 k]; exact hk.2.2
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨Finset.mem_univ _, hq0' k hk.2.1, ?_⟩
    rw [hinv2 k]; exact hk.2.2

/-- **The `𝔽₂`-rational trace element** (heart of the involution bound).  For a 2-torsion
action of a group with a unitary involution `ω` conjugating `u` (of order `r`) by `u ↦ u^q`,
and a pairing of `(ZMod r) ∖ {0}` into halves `Λ₁, Λ₂` swapped by `k ↦ q·k`, every `ω`-fixed
`v` equals `w + ω•w` for the trace `w = ∑_{k ∈ Λ₁} u^{k.val} • v`: the geometric-sum vanishing
`∑_{k<r} u^k•v = 0` collapses the full orbit sum to `v`, and `ω` swaps the two half-sums. -/
private lemma exists_trace_element {C : Type} [Group C] {V : Type} [AddCommGroup V]
    [DistribMulAction C V] (hV2 : ∀ v : V, v + v = 0) {ω u : C} {r : ℕ} [NeZero r]
    (huord : orderOf u = r) (husum : ∀ v : V, ∑ k ∈ Finset.range r, u ^ k • v = 0)
    {q : ℕ} (hconju : ∀ a : ℕ, ω * u ^ a * ω⁻¹ = u ^ (q * a))
    {Λ₁ Λ₂ : Finset (ZMod r)} (hdisj : Disjoint Λ₁ Λ₂)
    (hunion : Λ₁ ∪ Λ₂ = Finset.univ.erase (0 : ZMod r))
    (hmapsto : ∀ k ∈ Λ₁, (q : ZMod r) * k ∈ Λ₂)
    (hmapsto' : ∀ k ∈ Λ₂, (q : ZMod r) * k ∈ Λ₁)
    (hinv2 : ∀ k : ZMod r, (q : ZMod r) * ((q : ZMod r) * k) = k)
    {v : V} (hv : ω • v = v) : ∃ w : V, v = w + ω • w := by
  refine ⟨∑ k ∈ Λ₁, u ^ (ZMod.val k) • v, ?_⟩
  have hstep : ∀ k : ZMod r,
      ω • (u ^ (ZMod.val k) • v) = u ^ (ZMod.val ((q : ZMod r) * k)) • v := by
    intro k
    have h1 : ω * u ^ (ZMod.val k) = u ^ (q * ZMod.val k) * ω := by
      calc ω * u ^ (ZMod.val k) = (ω * u ^ (ZMod.val k) * ω⁻¹) * ω := by group
        _ = u ^ (q * ZMod.val k) * ω := by rw [hconju (ZMod.val k)]
    have h2 : u ^ (q * ZMod.val k) = u ^ (ZMod.val ((q : ZMod r) * k)) := by
      have hval : ZMod.val ((q : ZMod r) * k) = q * ZMod.val k % r := by
        rw [ZMod.val_mul, ZMod.val_natCast]
        exact (Nat.mod_modEq q r).mul_right (ZMod.val k)
      have hpm : u ^ (q * ZMod.val k % r) = u ^ (q * ZMod.val k) := by
        have h := pow_mod_orderOf u (q * ZMod.val k)
        rwa [huord] at h
      rw [hval]
      exact hpm.symm
    calc ω • (u ^ (ZMod.val k) • v) = (ω * u ^ (ZMod.val k)) • v := (mul_smul _ _ _).symm
      _ = (u ^ (q * ZMod.val k) * ω) • v := by rw [h1]
      _ = u ^ (q * ZMod.val k) • (ω • v) := mul_smul _ _ _
      _ = u ^ (q * ZMod.val k) • v := by rw [hv]
      _ = u ^ (ZMod.val ((q : ZMod r) * k)) • v := by rw [h2]
  have hωsum : ω • (∑ k ∈ Λ₁, u ^ (ZMod.val k) • v) = ∑ k ∈ Λ₂, u ^ (ZMod.val k) • v := by
    calc ω • (∑ k ∈ Λ₁, u ^ (ZMod.val k) • v)
        = ∑ k ∈ Λ₁, ω • (u ^ (ZMod.val k) • v) := Finset.smul_sum
      _ = ∑ k ∈ Λ₁, u ^ (ZMod.val ((q : ZMod r) * k)) • v :=
          Finset.sum_congr rfl fun k _ => hstep k
      _ = ∑ k ∈ Λ₂, u ^ (ZMod.val k) • v :=
          Finset.sum_nbij' (fun k => (q : ZMod r) * k) (fun k => (q : ZMod r) * k)
            hmapsto hmapsto' (fun k _ => hinv2 k) (fun k _ => hinv2 k) (fun k _ => rfl)
  have h2 : ∑ k : ZMod r, u ^ (ZMod.val k) • v = ∑ j ∈ Finset.range r, u ^ j • v :=
    Finset.sum_nbij' (fun k => ZMod.val k) (fun j => (j : ZMod r))
      (fun k _ => Finset.mem_range.mpr (ZMod.val_lt k))
      (fun j _ => Finset.mem_univ _)
      (fun k _ => ZMod.natCast_rightInverse k)
      (fun j hj => ZMod.val_cast_of_lt (Finset.mem_range.mp hj))
      (fun k _ => rfl)
  have hfull : ∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v = v := by
    have h1 : (∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v)
        + u ^ (ZMod.val (0 : ZMod r)) • v = ∑ k : ZMod r, u ^ (ZMod.val k) • v :=
      Finset.sum_erase_add _ _ (Finset.mem_univ 0)
    rw [h2, husum v, ZMod.val_zero, pow_zero, one_smul] at h1
    calc ∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v
        = ((∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v) + v) + v := by
          rw [add_assoc, hV2, add_zero]
      _ = 0 + v := by rw [h1]
      _ = v := zero_add v
  have hsplit : (∑ k ∈ Λ₁, u ^ (ZMod.val k) • v) + (∑ k ∈ Λ₂, u ^ (ZMod.val k) • v)
      = ∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v := by
    rw [← Finset.sum_union hdisj, hunion]
  rw [hωsum, hsplit, hfull]

/-- **The involution counting bound** (the key finite-group input to Lemma 6.11): the involution
`ω = g₀^{2^{s-1}}` of the cyclic Sylow-2 subgroup acts freely enough on the ramified simple
faithful module, `#V^ω ^ 2 ≤ #V`.  This is the `p = 2` elementary-abelian case of the
paper's pp. 29–30 weight-orbit argument.

The hypothesis `hs1 : 1 ≤ s` is necessary.  The
bound is *false* for a trivial Sylow-2 subgroup (`s = 0` gives `ω = 1`, e.g. the Frobenius
group `C₇ ⋊ C₃` of order 21 acting on `𝔽₈` is ramified simple faithful with `#V^ω = #V`);
the sole consumer `card_fixedPoints_pow_le_of_ramified` needs no leaf there (`#V^P ^ 1 ≤ #V`
is subtype counting).

Proof: `t := c τ` has odd order `m` and `⟨t⟩ ⊴ C`; conjugation gives `ω t ω⁻¹ = t^q`,
`q² ≡ 1 (mod m)`.  If `t^q = t`, then `ω` lies in the 2-torsion of the abelian centralizer
`C_C(⟨t⟩)` — a normal 2-subgroup acting trivially by simplicity, against faithfulness
(`two_torsion_of_centralizer_eq_one`), impossible since `ω ≠ 1`.  Otherwise the trace element
`w := ∑_{k ∈ Λ} (t^g)^{k.val} • v` over a transversal `Λ` of the fixed-point-free involution
`k ↦ qk` of `(ZMod (m/g)) ∖ {0}` (`g := gcd(q−1, m)`, unitary by
`coprime_sub_one_div_gcd`) satisfies `w + ω•w = v` for every `ω`-fixed `v` (geometric-sum
vanishing `sum_range_orderOf_smul_eq_zero` + `fixedPoints_zpowers_tame_eq_zero`), so
`ker(1+ω) ⊆ range(1+ω)` and first-isomorphism counting gives the bound. -/
theorem involution_fixedPoints_sq_le_of_tame_pair {C : Type} [Group C]
    [Finite C] {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C)
    (g₀ : ↥(P : Subgroup C)) (hg : ∀ x : ↥(P : Subgroup C), x ∈ Subgroup.zpowers g₀)
    (s : ℕ) (hs1 : 1 ≤ s) (hs : Nat.card ↥(P : Subgroup C) = 2 ^ s) :
    Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2 ≤ Nat.card V := by
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  have hmodd : Odd (orderOf t) := Tame.tame_odd_order (orderOf_pos sg).ne' hrel
  set m : ℕ := orderOf t with hm
  have hm0 : 0 < m := orderOf_pos t
  -- ramification gives `t ≠ 1` and a nonzero vector
  obtain ⟨vr, hvr⟩ := hram
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, one_smul] at hvr
    exact hvr rfl
  have hV0 : ∃ v₀ : V, v₀ ≠ (0 : V) := by
    refine ⟨vr, fun h => hvr ?_⟩
    rw [h, smul_zero]
  -- the involution ω = g₀^{2^{s-1}}
  set ω : C := ((g₀ ^ (2 ^ s / 2) : ↥(P : Subgroup C)) : C) with hωdef
  have hsmul_def : ∀ v : V, (g₀ ^ (2 ^ s / 2)) • v = ω • v := fun v => rfl
  have hg₀ord : orderOf ((g₀ : C)) = 2 ^ s := by
    have h1 : orderOf g₀ = 2 ^ s := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hs]
    rw [← h1]
    exact orderOf_injective (P : Subgroup C).subtype Subtype.val_injective g₀
  have hs2 : 2 ^ s / 2 = 2 ^ (s - 1) := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have hωcoe : ω = (g₀ : C) ^ (2 ^ s / 2) := by
    rw [hωdef, SubmonoidClass.coe_pow]
  have hωord : orderOf ω = 2 := by
    rw [hωcoe, hs2, orderOf_pow, hg₀ord]
    have hgcd : Nat.gcd (2 ^ s) (2 ^ (s - 1)) = 2 ^ (s - 1) :=
      Nat.gcd_eq_right (pow_dvd_pow 2 (by omega))
    rw [hgcd]
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ s')]
  have hω2 : ω * ω = 1 := by
    have h := pow_orderOf_eq_one ω
    rwa [hωord, pow_two] at h
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωord
    omega
  -- conjugation by ω sends t to t^q, q² ≡ 1 (mod m)
  have hconjmem : ω * t * ω⁻¹ ∈ Subgroup.zpowers t :=
    hnorm.conj_mem t (Subgroup.mem_zpowers t) ω
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hconjmem
  set q : ℕ := (j % (m : ℤ)).toNat with hq
  have hjm0 : 0 ≤ j % (m : ℤ) := Int.emod_nonneg j (by exact_mod_cast hm0.ne')
  have hjm1 : j % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos j (by exact_mod_cast hm0)
  have hqcast : (q : ℤ) = j % (m : ℤ) := Int.toNat_of_nonneg hjm0
  have hqm : q < m := by omega
  have htq : t ^ q = ω * t * ω⁻¹ := by
    have hm1 : t ^ (m : ℤ) = 1 := by
      rw [zpow_natCast, hm, pow_orderOf_eq_one]
    have h2 : t ^ j = t ^ (j % (m : ℤ)) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv j (m : ℤ)]
      rw [zpow_add, zpow_mul, hm1, one_zpow, mul_one]
    calc t ^ q = t ^ (q : ℤ) := (zpow_natCast t q).symm
      _ = t ^ (j % (m : ℤ)) := by rw [hqcast]
      _ = t ^ j := h2.symm
      _ = ω * t * ω⁻¹ := hj
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at htq
    refine ht1 ?_
    calc t = ω⁻¹ * (ω * t * ω⁻¹) * ω := by group
      _ = ω⁻¹ * 1 * ω := by rw [← htq]
      _ = 1 := by group
  have htqq : t ^ (q * q) = t := by
    calc t ^ (q * q) = (t ^ q) ^ q := by rw [pow_mul]
      _ = (ω * t * ω⁻¹) ^ q := by rw [htq]
      _ = ω * t ^ q * ω⁻¹ := conj_pow
      _ = ω * (ω * t * ω⁻¹) * ω⁻¹ := by rw [htq]
      _ = (ω * ω) * t * (ω * ω)⁻¹ := by group
      _ = t := by rw [hω2, one_mul, inv_one, mul_one]
  have hqq : (q - 1) * (q + 1) = q * q - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [hk]
    have h2 : (k + 1) * (k + 1) = k * (k + 1 + 1) + 1 := by ring
    rw [Nat.add_sub_cancel, h2, Nat.add_sub_cancel]
  have hdvd : m ∣ (q - 1) * (q + 1) := by
    have hqq0 : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    have ht1' : t ^ (q * q - 1) = 1 := by
      have h4 : t ^ (q * q - 1) * t = 1 * t := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hqq0, htqq]
      exact mul_right_cancel h4
    have h5 : t ^ ((q - 1) * (q + 1)) = 1 := by rw [hqq]; exact ht1'
    have h6 := orderOf_dvd_iff_pow_eq_one.mpr h5
    rwa [← hm] at h6
  -- dichotomy: ω centralizes t (impossible), or the trace element exists
  by_cases hcen : ω * t = t * ω
  · exact absurd
      (two_torsion_of_centralizer_eq_one hgen hrel hV2 hfaith hsimple hV0
        (by rw [pow_two]; exact hω2) hcen) hω1
  -- the ramified branch: q ≥ 2 and the unitary-gcd setup
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq1 : q = 1 := by omega
    rw [hq1, pow_one] at htq
    refine hcen ?_
    calc ω * t = (ω * t * ω⁻¹) * ω := by group
      _ = t * ω := by rw [← htq]
  set g : ℕ := Nat.gcd (q - 1) m with hgdef
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm0
  have hglt : g < m := by
    have h1 : g ∣ q - 1 := Nat.gcd_dvd_left _ _
    have h2 : g ≤ q - 1 := Nat.le_of_dvd (by omega) h1
    omega
  set r : ℕ := m / g with hrdef
  have hgr : g * r = m := by rw [hrdef]; exact Nat.mul_div_cancel' hgm
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · exact h
  haveI : NeZero r := ⟨by omega⟩
  have hcop' : Nat.Coprime (q - 1) r := by
    rw [hrdef, hgdef]
    exact coprime_sub_one_div_gcd hm0 hmodd (by omega) hdvd
  set u : C := t ^ g with hudef
  have humem : u ∈ Subgroup.zpowers t :=
    Subgroup.mem_zpowers_iff.mpr ⟨(g : ℤ), by rw [zpow_natCast, ← hudef]⟩
  have huord : orderOf u = r := by
    rw [hudef, orderOf_pow, ← hm, Nat.gcd_eq_right hgm, hrdef]
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huord
    omega
  have hufree : ∀ v : V, u • v = v → v = 0 :=
    fixedPoints_zpowers_tame_eq_zero hgen hrel hfaith hsimple humem hu1
  have husum : ∀ v : V, ∑ k ∈ Finset.range r, u ^ k • v = 0 := by
    intro v
    have h := sum_range_orderOf_smul_eq_zero hufree v
    rwa [huord] at h
  have hconju : ∀ a : ℕ, ω * u ^ a * ω⁻¹ = u ^ (q * a) := by
    intro a
    calc ω * u ^ a * ω⁻¹ = ω * t ^ (g * a) * ω⁻¹ := by rw [hudef, ← pow_mul]
      _ = (ω * t * ω⁻¹) ^ (g * a) := by rw [conj_pow]
      _ = (t ^ q) ^ (g * a) := by rw [htq]
      _ = t ^ (q * (g * a)) := by rw [← pow_mul]
      _ = t ^ (g * (q * a)) := by rw [mul_left_comm]
      _ = (t ^ g) ^ (q * a) := by rw [pow_mul]
      _ = u ^ (q * a) := by rw [← hudef]
  -- mult-by-q is a fixed-point-free involution of (ZMod r) ∖ {0}
  have hrdvd : r ∣ q * q - 1 := by
    have hrm : r ∣ m := ⟨g, by rw [← hgr]; ring⟩
    rw [← hqq]
    exact hrm.trans hdvd
  have hcast : ((q : ZMod r) * (q : ZMod r)) = 1 := by
    have hqq0 : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    have h0 : ((q * q - 1 : ℕ) : ZMod r) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod r) r _).mpr hrdvd
    calc ((q : ZMod r) * (q : ZMod r)) = ((q * q : ℕ) : ZMod r) := by push_cast; ring
      _ = (((q * q - 1) + 1 : ℕ) : ZMod r) := by rw [Nat.sub_add_cancel hqq0]
      _ = ((q * q - 1 : ℕ) : ZMod r) + 1 := by push_cast; ring
      _ = 1 := by rw [h0, zero_add]
  -- the transversal pairing k ↔ q·k of `(ZMod r) ∖ {0}` (fixed-point-free involution)
  obtain ⟨Λ₁, Λ₂, hdisj, hunion, hmapsto, hmapsto', hinv2⟩ :=
    exists_transversal_pairing q hcop' hcast (by omega)
  -- the trace element: every ω-fixed vector is in the range of 1 + ω
  have htrace : ∀ v : V, ω • v = v → ∃ w : V, v = w + ω • w := fun v hv =>
    exists_trace_element hV2 huord husum hconju hdisj hunion hmapsto hmapsto' hinv2 hv
  -- counting: ker(1 + ω) ⊆ range(1 + ω) forces #ker² ≤ #V
  set A : V →+ V :=
    { toFun := fun w => w + ω • w
      map_zero' := by rw [smul_zero, add_zero]
      map_add' := fun a b => by rw [smul_add]; abel } with hA
  have hAfix : ∀ v : V, A v = 0 → ω • v = v := by
    intro v h
    have h1 : v + ω • v = 0 := h
    exact add_left_cancel (h1.trans (hV2 v).symm)
  have hfixiff : ∀ v : V, ((g₀ ^ (2 ^ s / 2)) • v = v) ↔ v ∈ A.ker := by
    intro v
    rw [AddMonoidHom.mem_ker, hsmul_def v]
    constructor
    · intro h
      show v + ω • v = 0
      rw [h]
      exact hV2 v
    · intro h
      exact hAfix v h
  have hkerle : A.ker ≤ A.range := by
    intro v hv
    rw [AddMonoidHom.mem_ker] at hv
    obtain ⟨w, hw⟩ := htrace v (hAfix v hv)
    exact AddMonoidHom.mem_range.mpr ⟨w, hw.symm⟩
  have hcard1 : Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} = Nat.card ↥A.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixiff)
  calc Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2
      = Nat.card ↥A.ker ^ 2 := by rw [hcard1]
    _ ≤ Nat.card V := card_ker_sq_le_of_ker_le_range A hkerle

/-- **The Sylow-2 fixed-space bound on a ramified simple faithful module.**  The full bound
`#V^P ^ |P| ≤ #V` follows (via `card_fixedPoints_pow_le_of_half`, the elementary-abelian
reduction) from the **involution counting bound** `#V^ω ^ 2 ≤ #V` for the involution
`ω = g₀^{2^{s-1}}` in the cyclic Sylow-2 subgroup (`involution_fixedPoints_sq_le` above,
which needs `1 ≤ s`); a trivial Sylow-2 subgroup gives the bound by subtype counting.

Faithfulness is genuinely needed (Remark 6.12: `C₃ ⋊ C₄` acting through `S₃` on `𝔽₄` is
ramified simple but its central `C₂` fixes everything, so `#V^ω = #V > #V^{1/2}`). -/
theorem card_fixedPoints_pow_le_of_ramified_of_tame_pair {C : Type} [Group C]
    [Finite C] {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C) :
    Nat.card {v : V // ∀ p : ↥(P : Subgroup C), p • v = v} ^ Nat.card ↥(P : Subgroup C)
      ≤ Nat.card V := by
  have hcyc : IsCyclic ↥(P : Subgroup C) :=
    isCyclic_of_isPGroup_two_of_tame hgen hrel (P : Subgroup C) P.isPGroup'
  obtain ⟨g₀, hg⟩ := hcyc.exists_generator
  obtain ⟨s, hs⟩ := P.isPGroup'.exists_card_eq
  -- trivial Sylow-2 subgroup: the bound is plain subtype counting
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · subst hs0
    rw [hs, pow_zero, pow_one]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  -- Elementary-abelian reduction: it suffices that the involution `g₀^{2^{s-1}}` acts freely.
  refine card_fixedPoints_pow_le_of_half hV2 g₀ hg s hs ?_
  exact involution_fixedPoints_sq_le_of_tame_pair hgen hrel hV2 hfaith hsimple hram P g₀ hg
    s hs1 hs

/-- **`𝔽₂[P]`-freeness of the restriction to the Sylow 2-subgroup** (Lemma 6.11, steps 1–2):
a ramified simple faithful module is equivariantly additively isomorphic to a regular module
`𝔽₂[P]^r`.  **Proved** from the counting criterion `free_of_card_fixedPoints_pow_le` at the
cyclic Sylow 2-subgroup (`isCyclic_of_isPGroup_two_of_tame`, with the tame relation
transported from `tame_relation` along `c`) and the counting bound
`card_fixedPoints_pow_le_of_ramified` above.  This argument uses only the standard axioms. -/
theorem sylow_free_of_ramified_of_tame_pair {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C) :
    ∃ (r : ℕ) (φ : V ≃+ (Fin r → ↥(P : Subgroup C) → ZMod 2)),
      ∀ (p : ↥(P : Subgroup C)) (v : V) (n : Fin r) (x : ↥(P : Subgroup C)),
        φ ((p : C) • v) n x = φ v n (p⁻¹ * x) := by
  have hcyc : IsCyclic ↥(P : Subgroup C) :=
    isCyclic_of_isPGroup_two_of_tame hgen hrel (P : Subgroup C) P.isPGroup'
  have hcount :=
    card_fixedPoints_pow_le_of_ramified_of_tame_pair hgen hrel hV2 hfaith hsimple hram P
  obtain ⟨r, φ, hφ⟩ := free_of_card_fixedPoints_pow_le hV2 hcyc P.isPGroup' hcount
  exact ⟨r, φ, hφ⟩

/-- **The weight-orbit kernel in split-pair form** (what `lemma_6_11` consumes): the equivariant
`𝔽₂[P]`-freeness `sylow_free_of_ramified` yields an equivariant split pair — take `j := φ`,
`q := φ⁻¹`.  Retraction equivariance is `φ`'s equivariance transported across the iso
(`φ⁻¹`-inject, then `φ`'s equivariance at `φ⁻¹ F`), and `q ∘ j = id` is `φ⁻¹ ∘ φ = id`. -/
theorem sylow_split_pair_of_ramified_of_tame_pair {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C) :
    ∃ (r : ℕ) (j : V →+ (Fin r → ↥(P : Subgroup C) → ZMod 2))
      (q : (Fin r → ↥(P : Subgroup C) → ZMod 2) →+ V),
      (∀ (p : ↥(P : Subgroup C)) (v : V) (n : Fin r) (x : ↥(P : Subgroup C)),
        j ((p : C) • v) n x = j v n (p⁻¹ * x)) ∧
      (∀ (p : ↥(P : Subgroup C)) (F : Fin r → ↥(P : Subgroup C) → ZMod 2),
        q (fun n x => F n (p⁻¹ * x)) = (p : C) • q F) ∧
      ∀ v : V, q (j v) = v := by
  obtain ⟨r, φ, hφ⟩ := sylow_free_of_ramified_of_tame_pair hgen hrel hV2 hfaith hsimple hram P
  refine ⟨r, φ.toAddMonoidHom, φ.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · exact hφ
  · intro p F
    show φ.symm (fun n x => F n (p⁻¹ * x)) = (p : C) • φ.symm F
    refine φ.injective ?_
    rw [AddEquiv.apply_symm_apply]
    funext n x
    have hpx := hφ p (φ.symm F) n x
    rw [AddEquiv.apply_symm_apply] at hpx
    exact hpx.symm
  · intro v
    exact φ.symm_apply_apply v

/-- **Lemma 6.11, abstract tame-pair form**: the split-summand package from a generating pair
`(sg, t)` with the tame
relation, rather than a `Ttame`-marking.  This is the form the κ⁰ assembly consumes
(`ActsThroughTame` supplies exactly such a pair); the `Ttame` form below is a wrapper. -/
theorem lemma_6_11_of_tame_pair {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  haveI : (P : Subgroup C).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hodd : Odd (P : Subgroup C).index :=
    Nat.not_even_iff_odd.mp fun he => Sylow.not_dvd_index P he.two_dvd
  obtain ⟨r, j, q, hj, hq, hqj⟩ :=
    sylow_split_pair_of_ramified_of_tame_pair hgen hrel hV2 hfaith hsimple hram P
  exact regular_summand_of_subgroup_summand hV2 (P : Subgroup C) hodd j q hj hq hqj

/-- **Lemma 6.11 (paper node, §6.3)**: a ramified simple faithful 2-torsion module over the
tame image is an equivariant split summand of a regular module.  The regular module `𝔽₂[C]^N`
is `Fin N → C → ZMod 2` with the left-translation action written inline; `ι` is the
equivariant embedding, `r` the equivariant retraction.

The proof composes the odd-index relative trace
`regular_summand_of_subgroup_summand` at a Sylow 2-subgroup (`Sylow.not_dvd_index` gives the
odd index) composed with the weight-orbit kernel `sylow_split_pair_of_ramified` above.

From this the deep-count multiplicativity (`Hom(V^∨, −)`-exactness) follows —
`equivariant_lift_of_regular_summand` below — which is the sole remaining input to
`lemma_6_17_dim`'s lower bound `#X₊ ≥ 2^m`.  Applied at `V := V^∨` (also ramified simple
faithful) by the consumer. -/
theorem lemma_6_11 {C : Type} [Group C] [TopologicalSpace C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v := by
  have hrel : (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 := by
    simpa only [conjP, map_mul, map_inv, map_pow] using congrArg (⇑c) tame_relation
  exact lemma_6_11_of_tame_pair hgen hrel hV2 hfaith hsimple hram

end GQ2
