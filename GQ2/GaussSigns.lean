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

/-! ### The cyclic-operator crux (P-15b (U2))

For the unramified branch we need the arithmetic input `#Hf ∤ 2^m − 1` (equivalently, the
generator is not contained in the proper subfield `𝔽_{2^m}`).  The heart of it, stated for a
single `𝔽₂`-linear operator, is: an **irreducible** operator on a `2m`-dimensional `𝔽₂`-space
cannot satisfy `T^(2^m − 1) = 1`.  Proof: `minpoly T` is irreducible (no proper invariant
subspace) of degree `2m` (the cyclic bridge `finrank = natDegree`), yet `T^(2^m−1) = 1` forces
`minpoly T ∣ X^{2^m} − X`, so its degree divides `m` — impossible for `m ≥ 1`. -/

section CyclicOperator

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The minimal polynomial of an irreducible operator is irreducible. -/
theorem minpoly_irreducible_of_noInvariant (T : Module.End (ZMod 2) V)
    (hV : Nontrivial V)
    (hirr : ∀ W : Submodule (ZMod 2) V, W ≠ ⊥ → W ≠ ⊤ → ∃ v ∈ W, T v ∉ W) :
    Irreducible (minpoly (ZMod 2) T) := by
  have hint : IsIntegral (ZMod 2) T := Algebra.IsIntegral.isIntegral T
  have hne : minpoly (ZMod 2) T ≠ 0 := minpoly.ne_zero hint
  have hdeg_pos : 0 < (minpoly (ZMod 2) T).natDegree := minpoly.natDegree_pos hint
  -- `aeval T p` commutes with `T`, so its kernel is `T`-invariant
  have hinv_ker : ∀ p : (ZMod 2)[X], ∀ w ∈ LinearMap.ker (aeval T p),
      T w ∈ LinearMap.ker (aeval T p) := by
    intro p w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hc : Commute (aeval T p) T := by
      have h := (Commute.all p (X : (ZMod 2)[X])).map (aeval T)
      rwa [aeval_X] at h
    calc aeval T p (T w) = (aeval T p * T) w := rfl
      _ = (T * aeval T p) w := by rw [hc.eq]
      _ = T (aeval T p w) := rfl
      _ = T 0 := by rw [hw]
      _ = 0 := map_zero T
  -- lower-degree polynomials do not annihilate `T`
  have haeval_ne : ∀ p : (ZMod 2)[X], p ≠ 0 →
      p.natDegree < (minpoly (ZMod 2) T).natDegree → aeval T p ≠ 0 := by
    intro p hp0 hdeg h0
    have hdvd : minpoly (ZMod 2) T ∣ p := minpoly.dvd _ _ h0
    have := Polynomial.natDegree_le_of_dvd hdvd hp0
    omega
  -- non-units in `𝔽₂[X]` have positive degree
  have hnu_deg : ∀ p : (ZMod 2)[X], p ≠ 0 → ¬ IsUnit p → 0 < p.natDegree := by
    intro p hp0 hpu
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exact absurd (Polynomial.isUnit_iff.mpr
        ⟨p.coeff 0, isUnit_iff_ne_zero.mpr (by
          intro hc0
          apply hp0
          rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc0, map_zero]),
        (Polynomial.eq_C_of_natDegree_eq_zero h).symm⟩) hpu
    · exact h
  refine ⟨?_, ?_⟩
  · intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · intro a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hna, hnb⟩ := hcon
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hne hab
    have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hne hab
    have hdega := hnu_deg a ha0 hna
    have hdegb := hnu_deg b hb0 hnb
    have hdegsum : (minpoly (ZMod 2) T).natDegree = a.natDegree + b.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha0 hb0]
    -- `W = ker (aeval T a)` is a proper nonzero `T`-invariant subspace
    set W := LinearMap.ker (aeval T a) with hWdef
    have hWtop : W ≠ ⊤ := by
      rw [hWdef, Ne, LinearMap.ker_eq_top]
      exact haeval_ne a ha0 (by omega)
    have hWbot : W ≠ ⊥ := by
      rw [hWdef, Ne, LinearMap.ker_eq_bot]
      intro hinj
      have hbne : aeval T b ≠ 0 := haeval_ne b hb0 (by omega)
      obtain ⟨v, hv⟩ : ∃ v, aeval T b v ≠ 0 := by
        by_contra hc
        simp only [not_exists, not_not] at hc
        exact hbne (LinearMap.ext hc)
      apply hv
      apply hinj
      have hz : aeval T a (aeval T b v) = 0 := by
        have : (aeval T a) (aeval T b v) = aeval T (a * b) v := by rw [map_mul]; rfl
        rw [this, ← hab, minpoly.aeval, LinearMap.zero_apply]
      rw [hz, map_zero]
    obtain ⟨v, hvW, hvnot⟩ := hirr W hWbot hWtop
    exact hvnot (hinv_ker a v hvW)

omit [FiniteDimensional (ZMod 2) V] in
/-- For an irreducible operator, `finrank = natDegree (minpoly)` (the cyclic bridge): the map
`p ↦ aeval T p v` for a nonzero `v` is a surjection `𝔽₂[X] ↠ V` with kernel `(minpoly T)`. -/
theorem finrank_eq_natDegree_minpoly (T : Module.End (ZMod 2) V)
    (hV : Nontrivial V)
    (hirr : ∀ W : Submodule (ZMod 2) V, W ≠ ⊥ → W ≠ ⊤ → ∃ v ∈ W, T v ∉ W) :
    Module.finrank (ZMod 2) V = (minpoly (ZMod 2) T).natDegree := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- the cyclic map `φ p = aeval T p v`
  let φ : (ZMod 2)[X] →ₗ[ZMod 2] V :=
    { toFun := fun p => aeval T p v
      map_add' := fun p q => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c p => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hφ : ∀ p, φ p = aeval T p v := fun _ => rfl
  -- `T (φ p) = φ (X * p)`
  have hφT : ∀ p, T (φ p) = φ (X * p) := by
    intro p
    rw [hφ, hφ, map_mul, aeval_X]
    exact (Module.End.mul_apply T (aeval T p) v).symm
  -- `φ` is surjective: its range is `T`-invariant and nonzero, hence `⊤`
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hR
    have hbot : LinearMap.range φ ≠ ⊥ := by
      intro hbot
      have h1 : φ 1 ∈ LinearMap.range φ := LinearMap.mem_range_self φ 1
      rw [hbot, Submodule.mem_bot] at h1
      rw [hφ, map_one] at h1
      exact hv (by simpa using h1)
    obtain ⟨w, hwR, hwT⟩ := hirr (LinearMap.range φ) hbot hR
    obtain ⟨p, rfl⟩ := hwR
    exact hwT ⟨X * p, (hφT p).symm⟩
  -- `ker φ = span {minpoly}`
  have hker : LinearMap.ker φ = (Ideal.span {minpoly (ZMod 2) T}).restrictScalars (ZMod 2) := by
    apply le_antisymm
    · intro p hp
      rw [LinearMap.mem_ker, hφ] at hp
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      apply minpoly.dvd
      ext w
      obtain ⟨q, rfl⟩ := hsurj w
      rw [LinearMap.zero_apply, hφ]
      have : aeval T p (aeval T q v) = aeval T q (aeval T p v) := by
        rw [show aeval T p (aeval T q v) = aeval T (p * q) v by rw [map_mul]; rfl,
          show aeval T q (aeval T p v) = aeval T (q * p) v by rw [map_mul]; rfl, mul_comm]
      rw [this, hp, map_zero]
    · intro p hp
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hp
      obtain ⟨c, rfl⟩ := hp
      rw [LinearMap.mem_ker, hφ, map_mul]
      show (aeval T (minpoly (ZMod 2) T) * aeval T c) v = 0
      rw [minpoly.aeval, zero_mul, LinearMap.zero_apply]
  -- transport finrank through the isomorphism `V ≃ (ZMod 2)[X] ⧸ ker φ`
  rw [← (φ.quotKerEquivOfSurjective hsurj).finrank_eq, hker,
    (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (Ideal.span {minpoly (ZMod 2) T})).finrank_eq,
    finrank_quotient_span_eq_natDegree]

/-- **The cyclic-operator crux of P-15b (U2)**: an irreducible `𝔽₂`-operator on a
`2m`-dimensional space (`m ≥ 1`) cannot satisfy `T^(2^m − 1) = 1`. -/
theorem irreducible_operator_pow_ne_one (m : ℕ) (hm : 1 ≤ m)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) (T : Module.End (ZMod 2) V)
    (hirr : ∀ W : Submodule (ZMod 2) V, W ≠ ⊥ → W ≠ ⊤ → ∃ v ∈ W, T v ∉ W) :
    T ^ (2 ^ m - 1) ≠ 1 := by
  have hVnt : Nontrivial V := nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hdim]; omega)
  intro hT
  have hirred : Irreducible (minpoly (ZMod 2) T) :=
    minpoly_irreducible_of_noInvariant T hVnt hirr
  -- `minpoly T ∣ X^(2^m-1) - 1`
  have hdvd1 : minpoly (ZMod 2) T ∣ X ^ (2 ^ m - 1) - 1 := by
    apply minpoly.dvd
    rw [map_sub, map_one, map_pow, aeval_X, hT, sub_self]
  -- `X^(2^m-1) - 1 ∣ X^(2^m) - X = X^((Nat.card (ZMod 2))^m) - X`
  have hdvd2 : (X ^ (2 ^ m - 1) - 1 : (ZMod 2)[X]) ∣ X ^ (Nat.card (ZMod 2)) ^ m - X := by
    rw [Nat.card_zmod 2]
    have key : (X ^ (2 ^ m - 1) - 1 : (ZMod 2)[X]) * X = X ^ (2 ^ m) - X := by
      rw [sub_mul, one_mul, ← pow_succ]
      congr 2
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    exact ⟨X, key.symm⟩
  have hdvd : minpoly (ZMod 2) T ∣ X ^ (Nat.card (ZMod 2)) ^ m - X := hdvd1.trans hdvd2
  -- factor-degree bound: `natDegree (minpoly) ∣ m`
  have hdeg_dvd : (minpoly (ZMod 2) T).natDegree ∣ m :=
    hirred.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  -- but `natDegree (minpoly) = 2m`
  have hdeg : (minpoly (ZMod 2) T).natDegree = 2 * m := by
    rw [← finrank_eq_natDegree_minpoly T hVnt hirr, hdim]
  rw [hdeg] at hdeg_dvd
  have := Nat.le_of_dvd (by omega) hdeg_dvd
  omega

end CyclicOperator

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

/-! ### Free-action orbit divisibility

The arithmetic pinch is fed by a group `U` acting on `V`, freely on `V ∖ 0`, preserving `q` —
this is the norm-one group of the endomorphism field in the paper's unramified proof.  A free
action of a finite group has all orbits of size `#U`, so `#U` divides the cardinality of any
`U`-stable subset. -/

/-- A **free action of a finite group divides the cardinality** of the set acted on: every
orbit is equivalent to the group. -/
theorem card_dvd_of_freeAction {U : Type*} [Group U] [Finite U] {S : Type*} [Finite S]
    [MulAction U S] (hfree : ∀ (u : U) (s : S), u • s = s → u = 1) :
    Nat.card U ∣ Nat.card S := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (MulAction.orbitRel.Quotient U S) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits U S), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have hstab : MulAction.stabilizer U (Quotient.out ω : S) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    exact hfree u _ (MulAction.mem_stabilizer_iff.mp hu)
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer U (Quotient.out ω : S)), hstab,
    Nat.card_congr (QuotientGroup.quotientBot.toEquiv)]

omit [AddCommGroup V] in
/-- A `U`-stable subtype inherits the free-action divisibility. -/
theorem card_dvd_card_subtype_of_free {U : Type*} [Group U] [Finite U] [MulAction U V]
    (P : V → Prop) (hP : ∀ (u : U) (v : V), P v → P (u • v))
    (hfree : ∀ (u : U) (v : V), P v → u • v = v → u = 1) :
    Nat.card U ∣ Nat.card {v : V // P v} := by
  letI : MulAction U {v : V // P v} :=
    { smul := fun u v => ⟨u • v.1, hP u v.1 v.2⟩
      one_smul := fun v => Subtype.ext (one_smul U v.1)
      mul_smul := fun a b v => Subtype.ext (mul_smul a b v.1) }
  refine card_dvd_of_freeAction fun u v huv => ?_
  exact hfree u v.1 v.2 (Subtype.ext_iff.mp huv)

/-- **Proposition 6.9, unramified case, from a free action** (the arithmetic core, independent
of building the endomorphism field): if a finite group `U` acts on `V` (`#V = 2^(2m)`) fixing
`0`, preserving a nonsingular `q`, freely on `V ∖ 0`, and with order not dividing `2^m − 1`,
then `#q⁻¹(0) = 2^(2m−1) − 2^(m−1)`.

The free orbits (all of size `#U`) divide both the nonzero-zero count and the nonzero count, so
`#U ∣ zeroCount − 1` and `#U ∣ #V − zeroCount`; if `arf q` were `0` these force `#U ∣ 2^m − 1`,
excluded by hypothesis, so `arf q = 1`.  In the paper `U` is the norm-one group of order
`2^m + 1` (so `#U ∤ 2^m − 1` since `0 < 2^m − 1 < 2^m + 1`), but the cyclic invariance group
`Hf` itself already works — see `prop_6_9_unramified_of_abelian`. -/
theorem prop_6_9_unramified_of_free (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    {U : Type*} [Group U] [Finite U] [MulAction U V] (hUdvd : ¬ Nat.card U ∣ 2 ^ m - 1)
    (hU0 : ∀ u : U, u • (0 : V) = 0) (hUq : ∀ (u : U) (v : V), q (u • v) = q v)
    (hfree : ∀ (u : U) (v : V), v ≠ 0 → u • v = v → u = 1) :
    zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  letI : Fintype V := Fintype.ofFinite V
  have hufix : ∀ (u : U) (v : V), v ≠ 0 → u • v ≠ 0 := by
    intro u v hv hcon
    exact hv (smul_left_cancel u (hcon.trans (hU0 u).symm))
  -- `#U` divides the count of nonzero zeros and of nonzeros
  have hdvdZ : Nat.card U ∣ Nat.card {v : V // q v = 0 ∧ v ≠ 0} :=
    card_dvd_card_subtype_of_free (fun v => q v = 0 ∧ v ≠ 0)
      (fun u v hv => ⟨(hUq u v).trans hv.1, hufix u v hv.2⟩)
      (fun u v hv h => hfree u v hv.2 h)
  have hdvdN : Nat.card U ∣ Nat.card {v : V // q v ≠ 0} :=
    card_dvd_card_subtype_of_free (fun v => q v ≠ 0)
      (fun u v hv => by rw [hUq u v]; exact hv)
      (fun u v hv h => hfree u v (fun hv0 => hv (by rw [hv0, hq.map_zero])) h)
  -- translate to `zeroCount`
  have hzeros : zeroCount q = Nat.card {v : V // q v = 0 ∧ v ≠ 0} + 1 := by
    have hset : {v : V | q v = 0} = insert 0 {v : V | q v = 0 ∧ v ≠ 0} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · intro h
        by_cases hv : v = 0
        · exact Or.inl hv
        · exact Or.inr ⟨h, hv⟩
      · rintro (rfl | ⟨h, _⟩)
        · exact hq.map_zero
        · exact h
    rw [zeroCount, show {v : V // q v = 0} = ↥{v : V | q v = 0} from rfl,
      Nat.card_coe_set_eq, hset,
      Set.ncard_insert_of_notMem (by simp) (Set.toFinite _),
      ← Nat.card_coe_set_eq]
    rfl
  have hnonzeros : Nat.card {v : V // q v ≠ 0} = 2 ^ (2 * m) - zeroCount q := by
    have hcompl : {v : V | q v ≠ 0} = {v : V | q v = 0}ᶜ := by
      ext v; simp [Set.mem_compl_iff]
    rw [show {v : V // q v ≠ 0} = ↥{v : V | q v ≠ 0} from rfl, Nat.card_coe_set_eq, hcompl,
      Set.ncard_compl, ← Nat.card_coe_set_eq,
      show ↥{v : V | q v = 0} = {v : V // q v = 0} from rfl, ← zeroCount, hcard]
  -- feed the pinch
  refine zeroCount_of_arf_one q hq hns hm
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    (arf_eq_one_of_dvd q hq hns hm hcard (n := Nat.card U) ?_ ?_ hUdvd)
  · rw [hzeros, Nat.add_sub_cancel]; exact hdvdZ
  · rw [← hnonzeros]; exact hdvdN

/-- **Proposition 6.9, unramified case, from abelian invariance** — the unramified branch reduced
to two concrete facts.  If a finite **abelian** group `Hf` acts on `V` (`#V = 2^(2m)`)
faithfully, simply, preserving a nonsingular `q`, with `#Hf ∤ 2^m − 1`, then
`#q⁻¹(0) = 2^(2m−1) − 2^(m−1)`.

The action is automatically free on `V ∖ 0`: for `g ≠ 1`, the fixed space `{v | g • v = v}` is
`Hf`-stable (by commutativity), so `⊥` or `⊤` by simplicity, and `⊤` would make `g` act trivially
(contradicting faithfulness).  This is exactly the unramified geometry — `Hf` is the cyclic
Frobenius image — modulo the arithmetic input `#Hf ∤ 2^m − 1` (equivalently: the generator is not
contained in the proper subfield `𝔽_{2^m}`, i.e. `V` is genuinely `2m`-dimensional and simple). -/
theorem prop_6_9_unramified_of_abelian (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    {Hf : Type*} [Group Hf] [Finite Hf] [DistribMulAction Hf V]
    (habelian : ∀ g h : Hf, g * h = h * g)
    (hfaith : ∀ g : Hf, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : Hf), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdvd : ¬ Nat.card Hf ∣ 2 ^ m - 1)
    (hinv : ∀ (g : Hf) (v : V), q (g • v) = q v) :
    zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  refine prop_6_9_unramified_of_free q hq hns m hm hcard (U := Hf) hdvd
    (fun g => smul_zero g) hinv ?_
  intro g v hv hgv
  by_contra hg
  -- the fixed space of `g`, an `Hf`-stable subgroup
  let W : AddSubgroup V :=
    { carrier := {w : V | g • w = w}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, hx, hy]
      zero_mem' := smul_zero g
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, hx] }
  have hstab : ∀ (h : Hf), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    show g • (h • w) = h • w
    rw [← mul_smul, habelian g h, mul_smul]
    exact congrArg (h • ·) hw
  rcases hsimple W hstab with hbot | htop
  · exact hv ((AddSubgroup.mem_bot).mp (hbot ▸ (hgv : g • v = v) : v ∈ (⊥ : AddSubgroup V)))
  · exact hg (hfaith g fun w => (htop ▸ AddSubgroup.mem_top w : w ∈ W))

/-- **Proposition 6.9, unramified case, from a cyclic generator** — the complete unramified
reduction.  If `Hf` is generated by a single `g` (the Frobenius) acting on the exponent-2 space
`V` (`#V = 2^(2m)`) faithfully, simply, preserving a nonsingular `q`, then
`#q⁻¹(0) = 2^(2m−1) − 2^(m−1)`.

Both hypotheses of `prop_6_9_unramified_of_abelian` are discharged here: abelianness is immediate
from cyclicity, and the arithmetic input `#Hf ∤ 2^m − 1` comes from the operator crux
`irreducible_operator_pow_ne_one` applied to `T = (g • ·)` (were `#Hf ∣ 2^m − 1` we would have
`T^(2^m−1) = 1` for the irreducible `T` on the `2m`-dimensional `V`, which it forbids). -/
theorem prop_6_9_unramified_of_cyclic (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (h2 : ∀ v : V, v + v = 0)
    {Hf : Type*} [Group Hf] [Finite Hf] [DistribMulAction Hf V]
    (g : Hf) (hgen : ∀ x : Hf, x ∈ Subgroup.zpowers g)
    (hfaith : ∀ h : Hf, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : Hf), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hinv : ∀ (h : Hf) (v : V), q (h • v) = q v) :
    zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  classical
  -- every element is a natural power of `g` (finite order)
  have hfin : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf g, orderOf_pos g, pow_orderOf_eq_one g⟩
  have hnatpow : ∀ h : Hf, ∃ k : ℕ, g ^ k = h := fun h =>
    (Submonoid.mem_powers_iff h g).mp (hfin.mem_powers_iff_mem_zpowers.mpr (hgen h))
  -- abelianness from cyclicity
  have habelian : ∀ a b : Hf, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := hnatpow a
    obtain ⟨j, rfl⟩ := hnatpow b
    rw [← pow_add, ← pow_add, Nat.add_comm]
  -- the arithmetic input `#Hf ∤ 2^m − 1`
  have hdvd : ¬ Nat.card Hf ∣ 2 ^ m - 1 := by
    intro hd
    letI : Module (ZMod 2) V := AddCommGroup.zmodModule (n := 2) (fun v => by
      rw [two_nsmul]; exact h2 v)
    haveI : Module.Finite (ZMod 2) V :=
      (Module.finite_iff_finite (R := ZMod 2)).mpr inferInstance
    -- `T = g • ·` as a `𝔽₂`-linear endomorphism
    let T : Module.End (ZMod 2) V :=
      { toFun := fun v => g • v
        map_add' := fun x y => smul_add g x y
        map_smul' := fun c v => map_nsmul (DistribSMul.toAddMonoidHom V g) c.val v }
    have hTapp : ∀ v, T v = g • v := fun _ => rfl
    -- `finrank = 2m`
    have hdim : Module.finrank (ZMod 2) V = 2 * m := by
      letI : Fintype V := Fintype.ofFinite V
      have hc := hcard
      have h1 : Fintype.card V = 2 ^ Module.finrank (ZMod 2) V := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      rw [Nat.card_eq_fintype_card, h1] at hc
      exact Nat.pow_right_injective (le_refl 2) hc
    -- irreducibility of `T`: a `T`-invariant subspace is `Hf`-stable (all powers of `g`)
    have hirr : ∀ W : Submodule (ZMod 2) V, W ≠ ⊥ → W ≠ ⊤ → ∃ v ∈ W, T v ∉ W := by
      intro W hWb hWt
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hpow : ∀ (k : ℕ) (w : V), w ∈ W → g ^ k • w ∈ W := by
        intro k
        induction k with
        | zero => intro w hw; simpa using hw
        | succ k ih =>
          intro w hw
          rw [pow_succ, mul_smul]
          exact ih (g • w) (hcon w hw)
      have hHf : ∀ (h : Hf), ∀ w ∈ W.toAddSubgroup, h • w ∈ W.toAddSubgroup := by
        intro h w hw
        obtain ⟨k, rfl⟩ := hnatpow h
        exact hpow k w hw
      rcases hsimple W.toAddSubgroup hHf with hb | ht
      · exact hWb (Submodule.toAddSubgroup_injective (hb.trans Submodule.bot_toAddSubgroup.symm))
      · exact hWt (Submodule.toAddSubgroup_injective
          (ht.trans Submodule.top_toAddSubgroup.symm))
    -- `T^(2^m-1) = 1` from `g^(2^m-1) = 1`
    have hgpow : g ^ (2 ^ m - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hd)
    have hTpow : ∀ (n : ℕ) (v : V), (T ^ n) v = g ^ n • v := by
      intro n
      induction n with
      | zero => intro v; simp
      | succ n ih => intro v; rw [pow_succ, Module.End.mul_apply, hTapp, ih, pow_succ, mul_smul]
    have hT1 : T ^ (2 ^ m - 1) = 1 := by
      ext v
      rw [hTpow, hgpow, one_smul, Module.End.one_apply]
    exact irreducible_operator_pow_ne_one m hm hdim T hirr hT1
  exact prop_6_9_unramified_of_abelian q hq hns m hm hcard habelian hfaith hsimple hdvd hinv

/-! ### The ramified Arf-parity engine (Lemma 6.8 (87), Hermitian-model-free)

For the ramified branch, `arf q = s (mod 2)` is forced by the same free-action machinery run
with a **dual** pinch: a norm-one group of order `2^{m'} + 1` (`m' = f/2`) acting diagonally on
`V ≅ W^{⊕s}` gives orbit-divisibilities, and `2^{m'}+1` divides `2^{m'·s} − 1` iff `s` is even
and `2^{m'·s} + 1` iff `s` is odd — pinning `arf q` to the parity of `s` with no Hermitian
diagonalization. -/

/-- `2^{m'·s} ≡ (−1)^s` modulo `2^{m'}+1`. -/
theorem two_pow_mod (m' s : ℕ) :
    ((2 : ZMod (2 ^ m' + 1)) ^ (m' * s)) = (-1) ^ s := by
  have hbase : (2 : ZMod (2 ^ m' + 1)) ^ m' = -1 := by
    have h : ((2 ^ m' : ℕ) : ZMod (2 ^ m' + 1)) = ((2 ^ m' + 1 : ℕ) : ZMod (2 ^ m' + 1)) - 1 := by
      push_cast; ring
    rw [ZMod.natCast_self] at h
    push_cast at h
    rw [h]; ring
  rw [pow_mul, hbase]

/-- If `s` is odd then `2^{m'}+1 ∤ 2^{m'·s} − 1` (for `m' ≥ 1`). -/
theorem not_dvd_sub_one_of_odd {m' s : ℕ} (hm' : 1 ≤ m') (hs : Odd s) :
    ¬ (2 ^ m' + 1) ∣ 2 ^ (m' * s) - 1 := by
  intro hdvd
  have hle : 1 ≤ 2 ^ (m' * s) := Nat.one_le_two_pow
  have hmod : (2 : ZMod (2 ^ m' + 1)) ^ (m' * s) = 1 := by
    have : ((2 ^ (m' * s) - 1 : ℕ) : ZMod (2 ^ m' + 1)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have h2 : ((2 ^ (m' * s) : ℕ) : ZMod (2 ^ m' + 1)) - 1 = 0 := by
      rw [← this]; push_cast [hle]; ring
    push_cast at h2
    linear_combination h2
  rw [two_pow_mod, hs.neg_one_pow] at hmod
  have hchar : (2 : ZMod (2 ^ m' + 1)) = 0 := by linear_combination -hmod
  rw [show (2 : ZMod (2 ^ m' + 1)) = ((2 : ℕ) : ZMod (2 ^ m' + 1)) by push_cast; ring] at hchar
  have : (2 ^ m' + 1) ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hchar
  have h3 : 2 ^ m' + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) this
  have : 2 ≤ 2 ^ m' := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) hm'
  omega

/-- If `s` is even then `2^{m'}+1 ∤ 2^{m'·s} + 1` (for `m' ≥ 1`). -/
theorem not_dvd_add_one_of_even {m' s : ℕ} (hm' : 1 ≤ m') (hs : Even s) :
    ¬ (2 ^ m' + 1) ∣ 2 ^ (m' * s) + 1 := by
  intro hdvd
  have hmod : (2 : ZMod (2 ^ m' + 1)) ^ (m' * s) + 1 = 0 := by
    have : ((2 ^ (m' * s) + 1 : ℕ) : ZMod (2 ^ m' + 1)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    linear_combination this
  rw [two_pow_mod, hs.neg_one_pow] at hmod
  have hchar : (2 : ZMod (2 ^ m' + 1)) = 0 := by linear_combination hmod
  rw [show (2 : ZMod (2 ^ m' + 1)) = ((2 : ℕ) : ZMod (2 ^ m' + 1)) by push_cast; ring] at hchar
  have : (2 ^ m' + 1) ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hchar
  have h3 : 2 ^ m' + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) this
  have : 2 ≤ 2 ^ m' := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) hm'
  omega

/-- **The dual Arf pinch**: free-action packets of size `n` with `n ∤ 2^m + 1` force `arf q = 0`
(mirror of `arf_eq_one_of_dvd`; the `arf = 1` branch would give `n ∣ 2^m + 1`). -/
theorem arf_eq_zero_of_dvd (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {m n : ℕ} (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (hdvd0 : n ∣ zeroCount q - 1) (hdvd1 : n ∣ 2 ^ (2 * m) - zeroCount q)
    (hnot : ¬ n ∣ 2 ^ m + 1) : arf q = 0 := by
  letI : Fintype V := Fintype.ofFinite V
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz (arf q) with h0 | h1
  · exact h0
  · exfalso
    have hzc := zeroCount_of_arf_one q hq hns hm
      (by rw [← Nat.card_eq_fintype_card]; exact hcard) h1
    rw [hzc] at hdvd0 hdvd1
    have h2m : (2 : ℕ) ^ (2 * m) = 2 ^ (2 * m - 1) + 2 ^ (2 * m - 1) := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    have hmm : (2 : ℕ) ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    have hlt : (2 : ℕ) ^ (m - 1) < 2 ^ (2 * m - 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hsub := Nat.dvd_sub hdvd1 hdvd0
    have harith : ∀ A B C D : ℕ, A = B + B → C = D + D → D < B →
        (A - (B - D)) - ((B - D) - 1) = C + 1 := by intro A B C D h1 h2 h3; omega
    rw [harith _ _ _ _ h2m hmm hlt] at hsub
    exact hnot hsub

/-- **Free-action zero-count divisibilities**: a finite group acting on `V` (`#V = 2^(2m)`)
fixing `0`, preserving `q`, and freely on `V ∖ 0`, divides both `zeroCount q − 1` (nonzero zeros)
and `2^(2m) − zeroCount q` (nonzeros).  (Factored from `prop_6_9_unramified_of_free`.) -/
theorem free_zeroCount_dvds (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    {m : ℕ} (hcard : Nat.card V = 2 ^ (2 * m))
    {U : Type*} [Group U] [Finite U] [MulAction U V]
    (hU0 : ∀ u : U, u • (0 : V) = 0) (hUq : ∀ (u : U) (v : V), q (u • v) = q v)
    (hfree : ∀ (u : U) (v : V), v ≠ 0 → u • v = v → u = 1) :
    Nat.card U ∣ zeroCount q - 1 ∧ Nat.card U ∣ 2 ^ (2 * m) - zeroCount q := by
  letI : Fintype V := Fintype.ofFinite V
  have hufix : ∀ (u : U) (v : V), v ≠ 0 → u • v ≠ 0 := fun u v hv hcon =>
    hv (smul_left_cancel u (hcon.trans (hU0 u).symm))
  have hdvdZ : Nat.card U ∣ Nat.card {v : V // q v = 0 ∧ v ≠ 0} :=
    card_dvd_card_subtype_of_free (fun v => q v = 0 ∧ v ≠ 0)
      (fun u v hv => ⟨(hUq u v).trans hv.1, hufix u v hv.2⟩)
      (fun u v hv h => hfree u v hv.2 h)
  have hdvdN : Nat.card U ∣ Nat.card {v : V // q v ≠ 0} :=
    card_dvd_card_subtype_of_free (fun v => q v ≠ 0)
      (fun u v hv => by rw [hUq u v]; exact hv)
      (fun u v hv h => hfree u v (fun hv0 => hv (by rw [hv0, hq.map_zero])) h)
  have hzeros : zeroCount q = Nat.card {v : V // q v = 0 ∧ v ≠ 0} + 1 := by
    have hset : {v : V | q v = 0} = insert 0 {v : V | q v = 0 ∧ v ≠ 0} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · intro h
        by_cases hv : v = 0
        · exact Or.inl hv
        · exact Or.inr ⟨h, hv⟩
      · rintro (rfl | ⟨h, _⟩)
        · exact hq.map_zero
        · exact h
    rw [zeroCount, show {v : V // q v = 0} = ↥{v : V | q v = 0} from rfl,
      Nat.card_coe_set_eq, hset,
      Set.ncard_insert_of_notMem (by simp) (Set.toFinite _), ← Nat.card_coe_set_eq]
    rfl
  have hnonzeros : Nat.card {v : V // q v ≠ 0} = 2 ^ (2 * m) - zeroCount q := by
    have hcompl : {v : V | q v ≠ 0} = {v : V | q v = 0}ᶜ := by
      ext v; simp [Set.mem_compl_iff]
    rw [show {v : V // q v ≠ 0} = ↥{v : V | q v ≠ 0} from rfl, Nat.card_coe_set_eq, hcompl,
      Set.ncard_compl, ← Nat.card_coe_set_eq,
      show ↥{v : V | q v = 0} = {v : V // q v = 0} from rfl, ← zeroCount, hcard]
  refine ⟨?_, ?_⟩
  · rw [hzeros, Nat.add_sub_cancel]; exact hdvdZ
  · rw [← hnonzeros]; exact hdvdN

/-- **The norm-one Arf-parity engine** (Lemma 6.8 (87), Hermitian-model-free): if a finite group
`U` of order `2^{m'} + 1` acts on `V` (`#V = 2^{2·m'·s}`, `m' ≥ 1`, `s ≥ 1`) fixing `0`,
preserving a nonsingular `q`, and freely on `V ∖ 0`, then `arf q = s (mod 2)`.

In the ramified application `U` is the norm-one group of the endomorphism field `D = End_I(W)`
acting diagonally on `V ≅ W^{⊕s}`; the parity of `s` decides which of the two Arf pinches fires. -/
theorem arf_eq_of_free_norm_one (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (m' s : ℕ) (hm' : 1 ≤ m') (hs1 : 1 ≤ s) (hcard : Nat.card V = 2 ^ (2 * (m' * s)))
    {U : Type*} [Group U] [Finite U] [MulAction U V] (hUcard : Nat.card U = 2 ^ m' + 1)
    (hU0 : ∀ u : U, u • (0 : V) = 0) (hUq : ∀ (u : U) (v : V), q (u • v) = q v)
    (hfree : ∀ (u : U) (v : V), v ≠ 0 → u • v = v → u = 1) :
    arf q = (s : ZMod 2) := by
  obtain ⟨hdvd0, hdvd1⟩ := free_zeroCount_dvds q hq hcard hU0 hUq hfree
  rw [hUcard] at hdvd0 hdvd1
  have hms1 : 1 ≤ m' * s := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rcases Nat.even_or_odd s with hs | hs
  · have hval : (s : ZMod 2) = 0 := by
      obtain ⟨j, rfl⟩ := hs
      rw [Nat.cast_add, CharTwo.add_self_eq_zero]
    rw [hval]
    exact arf_eq_zero_of_dvd q hq hns (m := m' * s) hms1 hcard hdvd0 hdvd1
      (not_dvd_add_one_of_even hm' hs)
  · have hval : (s : ZMod 2) = 1 := by
      obtain ⟨j, rfl⟩ := hs
      rw [show 2 * j + 1 = j + j + 1 by ring, Nat.cast_add, Nat.cast_add, Nat.cast_one,
        CharTwo.add_self_eq_zero, zero_add]
    rw [hval]
    exact arf_eq_one_of_dvd q hq hns (m := m' * s) hms1 hcard hdvd0 hdvd1
      (not_dvd_sub_one_of_odd hm' hs)

/-! ### The general Arf-parity engine (any group generating past the middle subfield)

Generalizing `arf_eq_of_free_norm_one`: the acting group need not have order exactly `2^{m'}+1`.
It suffices that `#U ∣ 2^{2m'} − 1`, `#U ∤ 2^{m'} − 1`, and `#U > 2` — i.e. `#U` "generates past
the subfield `𝔽_{2^{m'}}`".  This lets the invariance group `⟨T⟩` (tame inertia) itself serve as
`U` in the ramified proof, so the endomorphism-field **involution and norm-one subgroup are not
needed**: `T` acts irreducibly on `W` (dim `2m' = f`), so `ord(T) ∤ 2^{m'} − 1`
(`irreducible_operator_pow_ne_one`) and `ord(T) ∣ 2^{2m'} − 1` (`T` a unit of the field `𝔽₂[T]`). -/

/-- With `g := (2 : ZMod n)^{m'}` satisfying `g² = 1` and `g ≠ 1`, an odd `s` gives
`n ∤ 2^{m'·s} − 1`. -/
theorem gen_not_dvd_sub_one_of_odd {n m' s : ℕ} (hsq : (2 : ZMod n) ^ (2 * m') = 1)
    (hg1 : (2 : ZMod n) ^ m' ≠ 1) (hs : Odd s) : ¬ n ∣ 2 ^ (m' * s) - 1 := by
  intro hdvd
  apply hg1
  have hcast : (2 : ZMod n) ^ (m' * s) = 1 := by
    have h0 : ((2 ^ (m' * s) - 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow] at h0
    push_cast at h0
    linear_combination h0
  have hsq2 : ((2 : ZMod n) ^ m') ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact hsq
  rw [pow_mul] at hcast
  obtain ⟨k, rfl⟩ := hs
  rw [pow_succ, pow_mul, hsq2, one_pow, one_mul] at hcast
  exact hcast

/-- With `(2 : ZMod n)^{2m'} = 1` and `n > 2`, an even `s` gives `n ∤ 2^{m'·s} + 1`. -/
theorem gen_not_dvd_add_one_of_even {n m' s : ℕ} (hn : 2 < n)
    (hsq : (2 : ZMod n) ^ (2 * m') = 1) (hs : Even s) : ¬ n ∣ 2 ^ (m' * s) + 1 := by
  intro hdvd
  have hcast : (2 : ZMod n) ^ (m' * s) + 1 = 0 := by
    have h0 : ((2 ^ (m' * s) + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    linear_combination h0
  have hsq2 : ((2 : ZMod n) ^ m') ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact hsq
  rw [pow_mul] at hcast
  obtain ⟨k, rfl⟩ := hs
  rw [show k + k = 2 * k by ring, pow_mul, hsq2, one_pow] at hcast
  have hn2 : (n : ℕ) ∣ 2 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; linear_combination hcast
  have := Nat.le_of_dvd (by norm_num) hn2
  omega

/-- **The general Arf-parity engine**: a finite group `U` acting on `V` (`#V = 2^{2·m'·s}`,
`m' ≥ 1`, `s ≥ 1`) fixing `0`, preserving nonsingular `q`, freely on `V ∖ 0`, with
`#U ∣ 2^{2m'} − 1`, `#U ∤ 2^{m'} − 1`, `#U > 2`, forces `arf q = s (mod 2)`. -/
theorem arf_eq_of_free (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (m' s : ℕ) (hm' : 1 ≤ m') (hs1 : 1 ≤ s) (hcard : Nat.card V = 2 ^ (2 * (m' * s)))
    {U : Type*} [Group U] [Finite U] [MulAction U V]
    (hUsq : Nat.card U ∣ 2 ^ (2 * m') - 1) (hUnot : ¬ Nat.card U ∣ 2 ^ m' - 1)
    (hU2 : 2 < Nat.card U) (hU0 : ∀ u : U, u • (0 : V) = 0)
    (hUq : ∀ (u : U) (v : V), q (u • v) = q v)
    (hfree : ∀ (u : U) (v : V), v ≠ 0 → u • v = v → u = 1) :
    arf q = (s : ZMod 2) := by
  obtain ⟨hdvd0, hdvd1⟩ := free_zeroCount_dvds q hq hcard hU0 hUq hfree
  have hms1 : 1 ≤ m' * s := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hsq : (2 : ZMod (Nat.card U)) ^ (2 * m') = 1 := by
    have h0 : ((2 ^ (2 * m') - 1 : ℕ) : ZMod (Nat.card U)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hUsq
    rw [Nat.cast_sub Nat.one_le_two_pow] at h0
    push_cast at h0
    linear_combination h0
  have hg1 : (2 : ZMod (Nat.card U)) ^ m' ≠ 1 := by
    intro h
    apply hUnot
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    linear_combination h
  rcases Nat.even_or_odd s with hs | hs
  · have hval : (s : ZMod 2) = 0 := by
      obtain ⟨j, rfl⟩ := hs
      rw [Nat.cast_add, CharTwo.add_self_eq_zero]
    rw [hval]
    exact arf_eq_zero_of_dvd q hq hns (m := m' * s) hms1 hcard hdvd0 hdvd1
      (gen_not_dvd_add_one_of_even hU2 hsq hs)
  · have hval : (s : ZMod 2) = 1 := by
      obtain ⟨j, rfl⟩ := hs
      rw [show 2 * j + 1 = j + j + 1 by ring, Nat.cast_add, Nat.cast_add, Nat.cast_one,
        CharTwo.add_self_eq_zero, zero_add]
    rw [hval]
    exact arf_eq_one_of_dvd q hq hns (m := m' * s) hms1 hcard hdvd0 hdvd1
      (gen_not_dvd_sub_one_of_odd hsq hg1 hs)

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

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.8 = ⟦lem-ramifiedhermitian⟧
  * Proposition 6.9 = ⟦prop-candidatezero⟧
-/
