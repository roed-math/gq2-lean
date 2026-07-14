import GQ2.QuadraticFp2

/-!
# The nonsingular `𝔽₂` zero-count engine and Wall doubling  (ticket P-15a)

For a **nonsingular** quadratic map `q : V → 𝔽₂` on a finite elementary abelian `2`-group `V`,
this file computes the number of zeros `#q⁻¹(0)` (the base determinant Gauss sums of Props
6.9/6.18) and proves **Lemma 6.6** (Wall doubling).

## The Gauss sum

The engine is the integer **Gauss sum** `g(q) = ∑_{v} (−1)^{q(v)}`.  Its square is `#V`:

  `g(q)² = ∑_{x,y} (−1)^{q(x)+q(y)} = ∑_{u} (−1)^{q(u)} ∑_{x} (−1)^{B(x,u)} = (−1)^{q(0)}·#V = #V`,

the inner character sum `∑_x (−1)^{B(x,u)}` vanishing for `u ≠ 0` (nonsingularity: `B(·,u) ≠ 0`)
and equal to `#V` at `u = 0`.  So `g(q) = ±2^m` when `#V = 2^{2m}`, whence
`#q⁻¹(0) = (#V + g)/2 = 2^{2m−1} ± 2^{m−1}`, with the sign read by the democratic `arf`.  This
route needs **no** hyperbolic-splitting induction — the character-sum identity does all the work.

No axioms (`Ax = ∅`); everything is elementary `𝔽₂` combinatorics.
-/

open scoped BigOperators

namespace GQ2

namespace QuadraticFp2

/-! ## The sign character `𝔽₂ → ℤ` -/

/-- The nontrivial character `𝔽₂ → ℤˣ ⊂ ℤ`, `0 ↦ 1`, `1 ↦ −1`. -/
def sign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := rfl

theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by revert a b; decide

theorem sign_one_add (a : ZMod 2) : sign (1 + a) = - sign a := by revert a; decide


variable {V : Type*} [AddCommGroup V]

/-! ## The Gauss sum -/

/-- The integer **Gauss sum** `g(q) = ∑_v (−1)^{q(v)} = #q⁻¹(0) − #q⁻¹(1)`. -/
noncomputable def gaussSum (q : V → ZMod 2) [Fintype V] : ℤ := ∑ v, sign (q v)

/-- `B(·, u)` as an additive character `V →+ 𝔽₂` (additive by `polar_add_left`). -/
def polarHom (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (u : V) : V →+ ZMod 2 :=
  AddMonoidHom.mk' (fun v => polar q v u) (fun a b => hq.polar_add_left a b u)

@[simp] theorem polarHom_apply (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (u v : V) :
    polarHom q hq u v = polar q v u := rfl

/-- **Character-sum vanishing**: for a nonzero additive character `φ : V →+ 𝔽₂` on a finite group,
`∑_v (−1)^{φ(v)} = 0`.  (Shift by any `u₀` with `φ(u₀) = 1` negates the sum.) -/
theorem charSum_eq_zero [Fintype V] (φ : V →+ ZMod 2) (hφ : ∃ u₀, φ u₀ = 1) :
    ∑ v, sign (φ v) = 0 := by
  obtain ⟨u₀, hu₀⟩ := hφ
  have hreindex : ∑ v, sign (φ (v + u₀)) = ∑ v, sign (φ v) :=
    Equiv.sum_comp (Equiv.addRight u₀) (fun v => sign (φ v))
  have hval : ∀ v, sign (φ (v + u₀)) = - sign (φ v) := by
    intro v
    rw [map_add, hu₀, add_comm, sign_one_add]
  rw [Finset.sum_congr rfl (fun v _ => hval v), Finset.sum_neg_distrib] at hreindex
  linarith

/-- **Twisted-sum vanishing** (Wall step, level 0): if a function `f : V → 𝔽₂` shifts by `1` under
some translation `r₀` (`f(x + r₀) = f(x) + 1`), then `∑_x (−1)^{f(x)} = 0`.  This is the
"character is nonzero on the radical ⇒ the Gauss sum vanishes" building block for Lemma 6.6's
sign relation. -/
theorem sum_sign_shift_eq_zero [Fintype V] (f : V → ZMod 2) (r₀ : V)
    (h : ∀ x, f (x + r₀) = f x + 1) : ∑ x, sign (f x) = 0 := by
  have hreindex : ∑ x, sign (f (x + r₀)) = ∑ x, sign (f x) :=
    Equiv.sum_comp (Equiv.addRight r₀) (fun x => sign (f x))
  have hval : ∀ x, sign (f (x + r₀)) = - sign (f x) := by
    intro x; rw [h, add_comm, sign_one_add]
  rw [Finset.sum_congr rfl (fun x _ => hval x), Finset.sum_neg_distrib] at hreindex
  linarith

/-- Any nonzero element of `𝔽₂` is `1`. -/
private theorem zmod2_ne_zero_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

/-- **The Gauss sum squares to `#V`** for a nonsingular form: the character-sum identity
`g(q)² = ∑_u (−1)^{q(u)} ∑_x (−1)^{B(x,u)} = (−1)^{q(0)}·#V`. -/
theorem gaussSum_sq [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) :
    gaussSum q ^ 2 = Fintype.card V := by
  classical
  -- inner character sum `∑_x (−1)^{B(x,u)}`
  have hinner : ∀ u : V,
      (∑ x, sign (polar q x u)) = if u = 0 then (Fintype.card V : ℤ) else 0 := by
    intro u
    split_ifs with hu
    · subst hu
      have hz : ∀ x : V, polar q x 0 = 0 := by
        intro x
        unfold polar
        rw [add_zero, hq.map_zero, add_zero]
        exact CharTwo.add_self_eq_zero _
      simp only [hz, sign_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · refine charSum_eq_zero (polarHom q hq u) ?_
      obtain ⟨w, hw⟩ := hns u hu
      exact ⟨w, by rw [polarHom_apply, polar_comm]; exact zmod2_ne_zero_eq_one _ hw⟩
  -- per-`x` reindex `y ↦ x + u`
  have hx : ∀ x : V, (∑ y, sign (q x) * sign (q y)) = ∑ u, sign (q u) * sign (polar q x u) := by
    intro x
    have step1 : ∀ y : V, sign (q x) * sign (q y) = sign (q x + q y) :=
      fun y => (sign_add _ _).symm
    rw [Finset.sum_congr rfl (fun y _ => step1 y),
      ← Equiv.sum_comp (Equiv.addLeft x) (fun y => sign (q x + q y))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    show sign (q x + q (x + u)) = sign (q u) * sign (polar q x u)
    have key : q x + q (x + u) = polar q x u + q u := by
      unfold polar
      rw [add_assoc (q (x + u) + q x), CharTwo.add_self_eq_zero, add_zero]
      exact add_comm _ _
    rw [key, sign_add, mul_comm]
  calc gaussSum q ^ 2
      = ∑ x, ∑ y, sign (q x) * sign (q y) := by
        rw [gaussSum, sq, Finset.sum_mul_sum]
    _ = ∑ x, ∑ u, sign (q u) * sign (polar q x u) := Finset.sum_congr rfl (fun x _ => hx x)
    _ = ∑ u, sign (q u) * ∑ x, sign (polar q x u) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun u _ => by rw [Finset.mul_sum])
    _ = ∑ u, sign (q u) * (if u = 0 then (Fintype.card V : ℤ) else 0) :=
        Finset.sum_congr rfl (fun u _ => by rw [hinner u])
    _ = Fintype.card V := by
        rw [Finset.sum_eq_single (0 : V) (fun u _ hu => by rw [if_neg hu, mul_zero])
          (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, hq.map_zero, sign_zero, one_mul]

/-! ## From the Gauss sum to the zero count -/
omit [AddCommGroup V] in
/-- **Bridge**: `g(q) = 2·#q⁻¹(0) − #V` (the Gauss sum counts zeros minus ones). -/
theorem gaussSum_eq [Fintype V] (q : V → ZMod 2) :
    gaussSum q = 2 * (zeroCount q : ℤ) - Fintype.card V := by
  classical
  have hz : (zeroCount q : ℤ) = ∑ v, (if q v = 0 then (1 : ℤ) else 0) := by
    rw [zeroCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
  have hsign : ∀ v : V, sign (q v) = 2 * (if q v = 0 then (1 : ℤ) else 0) - 1 := by
    intro v; unfold sign; split_ifs <;> ring
  rw [gaussSum, Finset.sum_congr rfl (fun v _ => hsign v), Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, ← hz, nsmul_eq_mul, mul_one]

omit [AddCommGroup V] in
/-- The democratic `arf` is `0` exactly when the Gauss sum is positive (zeros a strict majority). -/
theorem arf_eq_zero_iff_gaussSum_pos [Fintype V] (q : V → ZMod 2) :
    arf q = 0 ↔ 0 < gaussSum q := by
  rw [arf, gaussSum_eq, Nat.card_eq_fintype_card]
  split_ifs with hc <;> simp <;> omega

/-- For a nonsingular form with `#V = 2^{2m}`, the Gauss sum is `±2^m`. -/
theorem gaussSum_eq_pow [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) {m : ℕ} (hcard : Fintype.card V = 2 ^ (2 * m)) :
    gaussSum q = 2 ^ m ∨ gaussSum q = -2 ^ m := by
  have hsq : gaussSum q ^ 2 = (2 ^ m) ^ 2 := by
    rw [gaussSum_sq q hq hns, hcard]; push_cast; ring
  have hfac : (gaussSum q - 2 ^ m) * (gaussSum q + 2 ^ m) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

/-- **Zero count, `arf = 0` (positive Gauss sign)**: `#q⁻¹(0) = 2^{2m−1} + 2^{m−1}`. -/
theorem zeroCount_of_arf_zero [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card V = 2 ^ (2 * m))
    (harf : arf q = 0) : zeroCount q = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  have hpos := (arf_eq_zero_iff_gaussSum_pos q).mp harf
  have hg : gaussSum q = 2 ^ m := by
    rcases gaussSum_eq_pow q hq hns hcard with h | h
    · exact h
    · exfalso
      have hp : (0 : ℤ) < 2 ^ m := by positivity
      rw [h] at hpos; linarith
  have hbridge := gaussSum_eq q
  rw [hg, hcard] at hbridge
  push_cast at hbridge
  have h2m : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by rw [← pow_succ']; congr 1; omega
  have hm1 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hzc : (zeroCount q : ℤ) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
    rw [h2m, hm1] at hbridge; linarith
  exact_mod_cast hzc

/-- **Zero count, `arf = 1` (negative Gauss sign)**: `#q⁻¹(0) = 2^{2m−1} − 2^{m−1}`. -/
theorem zeroCount_of_arf_one [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card V = 2 ^ (2 * m))
    (harf : arf q = 1) : zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  have hnpos : ¬ 0 < gaussSum q := by
    intro hpos
    rw [(arf_eq_zero_iff_gaussSum_pos q).mpr hpos] at harf
    exact zero_ne_one harf
  have hg : gaussSum q = -2 ^ m := by
    rcases gaussSum_eq_pow q hq hns hcard with h | h
    · exfalso; apply hnpos; rw [h]; positivity
    · exact h
  have hbridge := gaussSum_eq q
  rw [hg, hcard] at hbridge
  push_cast at hbridge
  have h2m : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by rw [← pow_succ']; congr 1; omega
  have hm1 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hle : 2 ^ (m - 1) ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzc : (zeroCount q : ℤ) = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
    rw [h2m, hm1] at hbridge; linarith
  have hcast : ((2 ^ (2 * m - 1) - 2 ^ (m - 1) : ℕ) : ℤ) = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
    push_cast [Nat.cast_sub hle]; ring
  rw [← hcast] at hzc
  exact_mod_cast hzc

/-! ## Lemma 6.6 (Wall doubling) — structural reformulations

The doubling has the clean shape `q_U = q + q∘(1+U)`: since `U` is an isometry,
`B(x, Ux) = q(x + Ux)` (`q(Ux) = q(x)` cancels the cross terms).  This makes the polar form of
`q_U` transparently `B_U(x,y) = B(x,y) + B((1+U)x, (1+U)y)`. -/

/-- `q_U(x) = q(x) + q((1+U)x)`. -/
theorem qDouble_eq_add (q : V → ZMod 2) (U : V ≃+ V) (hUq : ∀ v, q (U v) = q v) (x : V) :
    qDouble q ⇑U x = q x + q (x + U x) := by
  unfold qDouble polar
  rw [hUq, add_assoc (q (x + U x)) (q x) (q x), CharTwo.add_self_eq_zero, add_zero]

/-- The polar form of the doubling: `B_U(x,y) = B(x,y) + B((1+U)x, (1+U)y)`. -/
theorem polar_qDouble (q : V → ZMod 2) (U : V ≃+ V) (hUq : ∀ v, q (U v) = q v) (x y : V) :
    polar (qDouble q ⇑U) x y = polar q x y + polar q (x + U x) (y + U y) := by
  unfold polar
  rw [qDouble_eq_add q U hUq (x + y), qDouble_eq_add q U hUq x, qDouble_eq_add q U hUq y, map_add,
    show (x + y) + (U x + U y) = (x + U x) + (y + U y) from by abel]
  ring

/-- A finite elementary abelian `2`-group has `2`-power cardinality. -/
theorem exists_card_eq_two_pow {W : Type*} [AddCommGroup W] [Finite W]
    (h2 : ∀ w : W, w + w = 0) : ∃ k, Nat.card W = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 (Multiplicative W) := fun g => ⟨1, by
    show g ^ 2 = 1
    rw [pow_two, ← ofAdd_toAdd g, ← ofAdd_add, h2, ofAdd_zero]⟩
  exact (IsPGroup.iff_card (p := 2) (G := Multiplicative W)).mp hpg

/-- The range of `1 + U` has `2`-power cardinality (it is a subgroup of the elem. ab. 2-group `V`). -/
theorem exists_card_range_eq_two_pow {V : Type*} [AddCommGroup V] [Finite V]
    (h2 : ∀ v : V, v + v = 0) (f : V →+ V) : ∃ k, Nat.card f.range = 2 ^ k :=
  exists_card_eq_two_pow (fun w => Subtype.ext (h2 (w : V)))

/-! ## Lemma 6.6 — nonsingularity of the doubling

`B_U(x,y) = B(x, (1+U+U⁻¹)y)`, so `q_U` is nonsingular iff `1+U+U⁻¹` (equivalently `1+U+U²`) is
injective — true for a `2`-power-order `U`: `U³y = y ⟹ Uy = y` (the fixed point has period
dividing `gcd(3, 2ⁿ) = 1`), and on `fix U` the operator `1+U+U²` acts as `3 = 1 ≠ 0`. -/

section Nonsingular

variable {V : Type*} [AddCommGroup V] (q : V → ZMod 2) (U : V ≃+ V)

/-- Isometry: `B(Ux, Uy) = B(x, y)`. -/
theorem polar_isometry_both (hUq : ∀ v, q (U v) = q v) (x y : V) :
    polar q (U x) (U y) = polar q x y := by
  unfold polar
  rw [← map_add, hUq, hUq, hUq]

/-- Isometry adjoint: `B(Ux, y) = B(x, U⁻¹y)`. -/
theorem polar_isometry_left (hUq : ∀ v, q (U v) = q v) (x y : V) :
    polar q (U x) y = polar q x (U.symm y) := by
  unfold polar
  have hqsymm : q (U.symm y) = q y := by
    conv_rhs => rw [← AddEquiv.apply_symm_apply U y]
    rw [hUq]
  have hcross : q (U x + y) = q (x + U.symm y) := by
    rw [show U x + y = U (x + U.symm y) by rw [map_add, AddEquiv.apply_symm_apply], hUq]
  rw [hcross, hUq, hqsymm]

/-- `B_U(x,y) = B(x, (1 + U + U⁻¹)y)`. -/
theorem polar_qDouble_eq (hq : IsQuadraticFp2 q) (hUq : ∀ v, q (U v) = q v) (x y : V) :
    polar (qDouble q ⇑U) x y = polar q x (y + U y + U.symm y) := by
  rw [polar_qDouble q U hUq, hq.polar_add_left, hq.polar_add_right, hq.polar_add_right,
    polar_isometry_both q U hUq, polar_isometry_left q U hUq, hq.polar_add_right,
    hq.polar_add_right]
  linear_combination CharTwo.add_self_eq_zero (polar q x y)

/-- **`(1 + U + U²)` is injective** for a `2`-power-order isometry `U` on an exponent-`2` group:
`(1+U+U²)y = 0 ⟹ Uy = y` (period divides `gcd(3, 2ⁿ) = 1`), whence `y = 3y = 0`. -/
theorem onePlusUUsq_injective (h2 : ∀ v : V, v + v = 0)
    (hU2 : ∃ n, (⇑U)^[2 ^ n] = id) (y : V) (hy : y + U y + U (U y) = 0) : y = 0 := by
  obtain ⟨n, hn⟩ := hU2
  have hUhy : U y + U (U y) + U (U (U y)) = 0 := by
    have := congrArg (⇑U) hy
    rwa [map_add, map_add, map_zero] at this
  have hU3 : (⇑U)^[3] y = y := by
    show U (U (U y)) = y
    have hsum : y + U (U (U y)) = 0 := by
      have hkey : (y + U y + U (U y)) + (U y + U (U y) + U (U (U y))) - (y + U (U (U y)))
          = (U y + U y) + (U (U y) + U (U y)) := by abel
      rw [h2, h2, add_zero] at hkey
      have : (y + U y + U (U y)) + (U y + U (U y) + U (U (U y))) = y + U (U (U y)) :=
        sub_eq_zero.mp hkey
      rw [hy, hUhy, add_zero] at this
      exact this.symm
    rw [eq_neg_of_add_eq_zero_right hsum, neg_eq_of_add_eq_zero_left (h2 y)]
  have hp3 : Function.IsPeriodicPt (⇑U) 3 y := hU3
  have hp2n : Function.IsPeriodicPt (⇑U) (2 ^ n) y := by
    show (⇑U)^[2 ^ n] y = y
    rw [hn]; rfl
  have hgcd : Function.IsPeriodicPt (⇑U) 1 y := by
    have h := hp3.gcd hp2n
    rwa [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right n (by decide)] at h
  have hUy : U y = y := by
    have := hgcd
    rwa [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_one] at this
  rw [hUy, hUy] at hy
  rw [h2 y, zero_add] at hy
  exact hy

/-- **Lemma 6.6, nonsingularity**: for a nonsingular `q` and a `2`-power-order isometry `U`, the
doubling `q_U` is nonsingular (`1 + U + U⁻¹` is bijective on the finite `V`). -/
theorem qDouble_nonsingular [Finite V] (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hns : Nonsingular q) (hUq : ∀ v, q (U v) = q v) (hU2 : ∃ n, (⇑U)^[2 ^ n] = id) :
    Nonsingular (qDouble q ⇑U) := by
  -- the map `g y = y + U y + U⁻¹ y` is injective, hence surjective
  set g : V →+ V := (AddMonoidHom.id V) + U.toAddMonoidHom + U.symm.toAddMonoidHom with hg
  have hg_apply : ∀ y, g y = y + U y + U.symm y := fun y => rfl
  have hg_inj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hgy
    rw [hg_apply] at hgy
    -- y + U y + U⁻¹ y = 0 ⟹ U y + U² y + y = 0 (apply U) ⟹ (1+U+U²)(y) = 0 ⟹ y = 0
    refine onePlusUUsq_injective U h2 hU2 y ?_
    have hUgy := congrArg (⇑U) hgy
    rw [map_add, map_add, map_zero, AddEquiv.apply_symm_apply] at hUgy
    rw [← hUgy]; abel
  have hg_surj : Function.Surjective g := Finite.injective_iff_surjective.mp hg_inj
  intro x hx
  obtain ⟨z, hz⟩ := hns x hx
  obtain ⟨y, hy⟩ := hg_surj z
  refine ⟨y, ?_⟩
  rw [polar_qDouble_eq q U hq hUq, ← hg_apply, hy]
  exact hz

/-- Two `𝔽₂` elements with equivalent vanishing are equal. -/
private theorem zmod2_eq_of_iff : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide

/-- If `a` vanishes exactly when `b` does not, then `a = b + 1` in `𝔽₂`. -/
private theorem zmod2_add_one_of_iff : ∀ a b : ZMod 2, (a = 0 ↔ b ≠ 0) → a = b + 1 := by decide

/-- The Gauss sum of a nonsingular form is nonzero (its square is `#V ≥ 1`). -/
theorem gaussSum_ne_zero [Fintype V] (hq : IsQuadraticFp2 q) (hns : Nonsingular q) :
    gaussSum q ≠ 0 := by
  intro h
  have hsq := gaussSum_sq q hq hns
  rw [h, zero_pow (by norm_num)] at hsq
  haveI : Nonempty V := ⟨0⟩
  exact absurd hsq.symm (by exact_mod_cast Fintype.card_pos.ne')

/-- **Arf-additivity from the Gauss-sum sign** (the reduction of Lemma 6.6's Arf clause): given the
Wall sign relation `g(q_U) = (−1)ᵏ g(q)`, the democratic Arf invariants satisfy
`arf(q_U) = arf(q) + k`.  (Both Gauss sums are nonzero, so the sign of `(−1)ᵏ` flips `arf` by
`k mod 2`.) -/
theorem arf_qDouble_of_gaussSum_sign [Fintype V] {k : ℕ} (hgne : gaussSum q ≠ 0)
    (hsign : gaussSum (qDouble q ⇑U) = (-1) ^ k * gaussSum q) :
    arf (qDouble q ⇑U) = arf q + (k : ZMod 2) := by
  have hq0 := arf_eq_zero_iff_gaussSum_pos q
  have hqU0 := arf_eq_zero_iff_gaussSum_pos (qDouble q ⇑U)
  rcases Nat.even_or_odd k with hk | hk
  · have hcz : (k : ZMod 2) = 0 := by
      obtain ⟨j, rfl⟩ := hk
      rw [Nat.cast_add, CharTwo.add_self_eq_zero]
    rw [hk.neg_one_pow, one_mul] at hsign
    rw [hcz, add_zero]
    exact zmod2_eq_of_iff _ _ (by rw [hqU0, hq0, hsign])
  · have hco : (k : ZMod 2) = 1 := by
      obtain ⟨j, rfl⟩ := hk
      rw [show 2 * j + 1 = j + j + 1 by ring, Nat.cast_add, Nat.cast_add, Nat.cast_one,
        CharTwo.add_self_eq_zero, zero_add]
    rw [hk.neg_one_pow] at hsign
    rw [hco]
    refine zmod2_add_one_of_iff _ _ ?_
    rw [hqU0, hsign, ne_eq, hq0]
    constructor
    · intro h hc; rw [neg_one_mul] at h; linarith
    · intro h; rw [neg_one_mul]
      rcases lt_or_gt_of_ne hgne with hlt | hgt
      · linarith
      · exact absurd hgt h

end Nonsingular

/-! ## Wall's sign relation — the abstract Wall count

Lemma 6.6's remaining piece is Wall's sign `g(q_U) = (−1)^k g(q)`, `2^k = #im(1+U)`.  Following
the paper's proof, everything reduces to the **Wall count**: the Wall form `ω(Nx, u) = B(x, u)`
on `R = im N` (`N = 1 + U`) satisfies

  `∑_{t,u ∈ R} (−1)^{ω(t,t) + ω(u,u) + ω(t,u)} = (−2)^{dim R}`.

We prove the count abstractly, for a biadditive `ω` on a finite elementary abelian 2-group `W`
that is right-nondegenerate and admits a **2-power-order monodromy** `M` (`ω t u = ω u (M t)`;
in the application `M = U⁻¹|_R`).  The monodromy hypothesis is essential: the count is *false*
for a general nondegenerate `ω` (`ω = [[1,1],[0,1]]` on `𝔽₂²` has count `−8 ≠ (−2)²`).  It
enters by producing a nonzero `M`-fixed vector `a` — whose row and column functionals agree —
along which the induction splits: if `ω a a = 1`, splitting off `⟨a⟩` factors the count by `−2`;
if `ω a a = 0`, a shift-pairing kills all terms outside `ker (ω a)²` and `⟨a⟩` acts freely on
what remains, giving a factor `4 = (−2)²`. -/

section WallCount

private theorem zmod2_self_add_val_smul_one : ∀ z : ZMod 2, z + z.val • (1 : ZMod 2) = 0 := by
  decide

private theorem zmod2_val_smul : ∀ x z : ZMod 2, x.val • z = x * z := by decide

/-- `(z + z') • w = z • w + z' • w` for `ZMod 2`-coefficients acting through `val`-nsmul on an
exponent-2 group (the `val`s differ by `0` or `2`, and `2 • w = 0`). -/
private theorem zmod2_val_add_smul {W : Type*} [AddCommGroup W] (h2 : ∀ w : W, w + w = 0)
    (z z' : ZMod 2) (w : W) : (z + z').val • w = z.val • w + z'.val • w := by
  have hval : (z + z').val = z.val + z'.val ∨ (z + z').val + 2 = z.val + z'.val := by
    revert z z'; decide
  rcases hval with h | h
  · rw [h, add_nsmul]
  · rw [← add_nsmul, ← h, add_nsmul, two_nsmul, h2, add_zero]

/-- A `2`-power-order automorphism of an exponent-2 group with a nonzero element has a
**nonzero fixed vector**: a fixed vector `a` of `M²` yields the `M`-fixed `a + Ma`, which
vanishes only if `a` itself is already `M`-fixed. -/
theorem exists_fixed_ne_zero {W : Type*} [AddCommGroup W] (h2 : ∀ w : W, w + w = 0) :
    ∀ (n : ℕ) (M : W ≃+ W), (⇑M)^[2 ^ n] = id → ∀ w₀ : W, w₀ ≠ 0 → ∃ a : W, a ≠ 0 ∧ M a = a
  | 0, M, hM, w₀, hw₀ => ⟨w₀, hw₀, by simpa using congrFun hM w₀⟩
  | (n + 1), M, hM, w₀, hw₀ => by
    have hMM : (⇑(M.trans M))^[2 ^ n] = id := by
      have h1 : ⇑(M.trans M) = (⇑M)^[2] := by
        funext w
        simp [Function.iterate_succ]
      rw [h1, ← Function.iterate_mul, show 2 * 2 ^ n = 2 ^ (n + 1) by ring]
      exact hM
    obtain ⟨a, ha0, haM⟩ := exists_fixed_ne_zero h2 n (M.trans M) hMM w₀ hw₀
    have haMM : M (M a) = a := haM
    by_cases hb : a + M a = 0
    · refine ⟨a, ha0, ?_⟩
      have h := congrArg (a + ·) hb
      simpa [← add_assoc, h2 a] using h
    · refine ⟨a + M a, hb, ?_⟩
      rw [map_add, haMM, add_comm]

/-- Reindexing an integer sum along a sign-reversing shift: if `f (x + r₀) = − f x` pointwise
then `∑ f = 0`. -/
theorem sum_neg_shift_eq_zero {W : Type*} [AddCommGroup W] [Fintype W] (f : W → ℤ) (r₀ : W)
    (h : ∀ x, f (x + r₀) = - f x) : ∑ x, f x = 0 := by
  have h1 : ∑ x, f (x + r₀) = ∑ x, f x := Equiv.sum_comp (Equiv.addRight r₀) f
  have h2 : ∑ x, f (x + r₀) = - ∑ x, f x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => h x
  linarith

/-- Splitting a finite exponent-2 group along a vector `b` with `φ b = 1`:
`ZMod 2 × ker φ ≃ W`, `(x, h) ↦ x·b + h`. -/
private def splitEquiv {W : Type*} [AddCommGroup W] (h2 : ∀ w : W, w + w = 0)
    (φ : W →+ ZMod 2) (b : W) (hb : φ b = 1) : ZMod 2 × ↥φ.ker ≃ W where
  toFun p := p.1.val • b + ↑p.2
  invFun w := (φ w, ⟨w + (φ w).val • b, by
    rw [AddMonoidHom.mem_ker, map_add, map_nsmul, hb]
    exact zmod2_self_add_val_smul_one _⟩)
  left_inv := by
    rintro ⟨x, h, hh⟩
    have hφ : φ (x.val • b + h) = x := by
      rw [map_add, map_nsmul, hb, AddMonoidHom.mem_ker.mp hh, add_zero, zmod2_val_smul, mul_one]
    refine Prod.ext hφ (Subtype.ext ?_)
    show (x.val • b + h) + (φ (x.val • b + h)).val • b = h
    rw [hφ, add_comm (x.val • b) h, add_assoc, ← smul_add, h2 b, smul_zero, add_zero]
  right_inv := by
    intro w
    show (φ w).val • b + (w + (φ w).val • b) = w
    rw [add_comm w ((φ w).val • b), ← add_assoc, ← smul_add, h2 b, smul_zero, zero_add]

private theorem splitEquiv_apply {W : Type*} [AddCommGroup W] (h2 : ∀ w : W, w + w = 0)
    (φ : W →+ ZMod 2) (b : W) (hb : φ b = 1) (x : ZMod 2) (h : ↥φ.ker) :
    splitEquiv h2 φ b hb (x, h) = x.val • b + ↑h := rfl

private theorem card_of_splitEquiv {W : Type*} [AddCommGroup W] [Finite W]
    (h2 : ∀ w : W, w + w = 0) (φ : W →+ ZMod 2) (b : W) (hb : φ b = 1) :
    Nat.card W = 2 * Nat.card ↥φ.ker := by
  rw [← Nat.card_congr (splitEquiv h2 φ b hb), Nat.card_prod, Nat.card_zmod]

private theorem zmod2_mul_self : ∀ x : ZMod 2, x * x = x := by decide

private theorem zmod2_sign_add_one : ∀ z : ZMod 2, sign (z + 1) = - sign z := by decide

/-- The bilinear expansion of `ω` along a two-part decomposition in each slot. -/
private theorem omega_expand {W : Type*} [AddCommGroup W] (ω : W →+ W →+ ZMod 2)
    (x y : ZMod 2) (b b' v u : W) :
    ω (x.val • b + v) (y.val • b' + u)
      = x * y * ω b b' + x * ω b u + y * ω v b' + ω v u := by
  simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    zmod2_val_smul]
  ring

universe u

/-- **Isotropic descent (×4)**: on a finite exponent-2 group `H` with a functional `ψ` and a
vector `b` (`ψ b = 1`) that is `ωH`-orthogonal to itself and to all of `C = ker ψ`, the Wall
count of `ωH` on `H` is `4 ·` the Wall count of the restriction `ωC` to `C`.  (The `⟨b⟩`- and
`ψ`-coordinates are invisible to the summand, so the count is `#(ZMod 2)² = 4` copies of the
count on `C`.) -/
private theorem wall_count_descent {H : Type u} [AddCommGroup H] [Fintype H]
    (h2H : ∀ h : H, h + h = 0) (ωH : H →+ H →+ ZMod 2) (ψ : H →+ ZMod 2) [Fintype ↥ψ.ker]
    (b : H) (hψb : ψ b = 1) (hbb : ωH b b = 0)
    (hbc : ∀ c : ↥ψ.ker, ωH b ↑c = 0) (hcb : ∀ c : ↥ψ.ker, ωH ↑c b = 0)
    (ωC : ↥ψ.ker →+ ↥ψ.ker →+ ZMod 2) (hωC : ∀ c c' : ↥ψ.ker, ωC c c' = ωH ↑c ↑c')
    {k'' : ℕ} (hIH : (∑ c : ↥ψ.ker, ∑ c₂ : ↥ψ.ker, sign (ωC c c + ωC c₂ c₂ + ωC c c₂))
      = (-2 : ℤ) ^ k'') :
    (∑ h : H, ∑ h₂ : H, sign (ωH h h + ωH h₂ h₂ + ωH h h₂)) = (4 : ℤ) * (-2) ^ k'' := by
  set eH : ZMod 2 × ↥ψ.ker ≃ H := splitEquiv h2H ψ b hψb with heHdef
  have heH2 : ∀ (y : ZMod 2) (c : ↥ψ.ker), eH (y, c) = y.val • b + ↑c := fun _ _ => rfl
  have hEH : ∀ (y y₂ : ZMod 2) (c c₂ : ↥ψ.ker),
      (ωH (eH (y, c)) (eH (y, c)) + ωH (eH (y₂, c₂)) (eH (y₂, c₂))
        + ωH (eH (y, c)) (eH (y₂, c₂)))
      = ωC c c + ωC c₂ c₂ + ωC c c₂ := by
    intro y y₂ c c₂
    simp only [heH2, omega_expand, hbb, hbc, hcb, hωC, mul_zero, add_zero, zero_add]
  calc (∑ h : H, ∑ h₂ : H, sign (ωH h h + ωH h₂ h₂ + ωH h h₂))
      = ∑ q : (ZMod 2 × ↥ψ.ker) × (ZMod 2 × ↥ψ.ker),
          sign (ωH (eH q.1) (eH q.1) + ωH (eH q.2) (eH q.2) + ωH (eH q.1) (eH q.2)) := by
        rw [← Fintype.sum_prod_type']
        exact (Equiv.sum_comp (eH.prodCongr eH) fun p : H × H =>
          sign (ωH p.1 p.1 + ωH p.2 p.2 + ωH p.1 p.2)).symm
    _ = ∑ r : (ZMod 2 × ZMod 2) × (↥ψ.ker × ↥ψ.ker),
          sign (ωC r.2.1 r.2.1 + ωC r.2.2 r.2.2 + ωC r.2.1 r.2.2) := by
        rw [← Equiv.sum_comp (Equiv.prodProdProdComm (ZMod 2) ↥ψ.ker (ZMod 2) ↥ψ.ker).symm]
        refine Finset.sum_congr rfl fun r _ => ?_
        obtain ⟨⟨y, y₂⟩, c, c₂⟩ := r
        exact congrArg sign (hEH y y₂ c c₂)
    _ = ∑ _pyy : ZMod 2 × ZMod 2, ∑ pcc : ↥ψ.ker × ↥ψ.ker,
          sign (ωC pcc.1 pcc.1 + ωC pcc.2 pcc.2 + ωC pcc.1 pcc.2) := by
        rw [Fintype.sum_prod_type]
    _ = (4 : ℤ) * (-2) ^ k'' := by
        rw [Finset.sum_const, show (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4
          from by decide, nsmul_eq_mul]
        rw [show (∑ pcc : ↥ψ.ker × ↥ψ.ker,
              sign (ωC pcc.1 pcc.1 + ωC pcc.2 pcc.2 + ωC pcc.1 pcc.2))
            = (-2 : ℤ) ^ k'' from by rw [Fintype.sum_prod_type]; exact hIH]
        norm_num

/-- Assembly of the isotropic case: reindexing the count on `W ≃ ZMod 2 × ker (ω a)` along `t₀`,
the `t₀`-odd blocks cancel (`hsh2`, `hsh1`), the surviving diagonal block is the kernel-level
count (`hE00`), which descends to `4 · (-2)^k''` (`hDH`), giving `(-2)^(k''+2)`. -/
private theorem wall_count_isotropic_assemble {W : Type u} [AddCommGroup W] [Fintype W]
    (ω : W →+ W →+ ZMod 2) (a : W) (hAmem : a ∈ (ω a).ker) [Fintype ↥(ω a).ker]
    (ωH : ↥(ω a).ker →+ ↥(ω a).ker →+ ZMod 2) (eT : ZMod 2 × ↥(ω a).ker ≃ W) {k'' : ℕ}
    (hsh2 : ∀ (x y : ZMod 2) (h h₂ : ↥(ω a).ker),
      (ω (eT (x, h)) (eT (x, h)) + ω (eT (y, h₂ + ⟨a, hAmem⟩)) (eT (y, h₂ + ⟨a, hAmem⟩))
        + ω (eT (x, h)) (eT (y, h₂ + ⟨a, hAmem⟩)))
      = (ω (eT (x, h)) (eT (x, h)) + ω (eT (y, h₂)) (eT (y, h₂))
        + ω (eT (x, h)) (eT (y, h₂))) + x)
    (hsh1 : ∀ (x y : ZMod 2) (h h₂ : ↥(ω a).ker),
      (ω (eT (x, h + ⟨a, hAmem⟩)) (eT (x, h + ⟨a, hAmem⟩)) + ω (eT (y, h₂)) (eT (y, h₂))
        + ω (eT (x, h + ⟨a, hAmem⟩)) (eT (y, h₂)))
      = (ω (eT (x, h)) (eT (x, h)) + ω (eT (y, h₂)) (eT (y, h₂))
        + ω (eT (x, h)) (eT (y, h₂))) + y)
    (hE00 : ∀ h h₂ : ↥(ω a).ker,
      (ω (eT (0, h)) (eT (0, h)) + ω (eT (0, h₂)) (eT (0, h₂))
        + ω (eT (0, h)) (eT (0, h₂)))
      = ωH h h + ωH h₂ h₂ + ωH h h₂)
    (hDH : (∑ h : ↥(ω a).ker, ∑ h₂ : ↥(ω a).ker,
        sign (ωH h h + ωH h₂ h₂ + ωH h h₂)) = (4 : ℤ) * (-2) ^ k'') :
    (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ (k'' + 2) := by
  calc (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u))
      = ∑ q : (ZMod 2 × ↥(ω a).ker) × (ZMod 2 × ↥(ω a).ker),
          sign (ω (eT q.1) (eT q.1) + ω (eT q.2) (eT q.2) + ω (eT q.1) (eT q.2)) := by
        rw [← Fintype.sum_prod_type']
        exact (Equiv.sum_comp (eT.prodCongr eT) fun p : W × W =>
          sign (ω p.1 p.1 + ω p.2 p.2 + ω p.1 p.2)).symm
    _ = ∑ x : ZMod 2, ∑ h : ↥(ω a).ker, ∑ p2 : ZMod 2 × ↥(ω a).ker,
          sign (ω (eT (x, h)) (eT (x, h)) + ω (eT p2) (eT p2) + ω (eT (x, h)) (eT p2)) := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = (-2 : ℤ) ^ (k'' + 2) := by
        rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
          Finset.sum_insert (by decide), Finset.sum_singleton]
        -- the `x = 1` half vanishes: shift the inner kernel index by `a`
        rw [show (∑ h : ↥(ω a).ker, ∑ p2 : ZMod 2 × ↥(ω a).ker,
              sign (ω (eT (1, h)) (eT (1, h)) + ω (eT p2) (eT p2)
                + ω (eT (1, h)) (eT p2))) = 0 from
          Finset.sum_eq_zero fun h _ => by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_eq_zero fun y _ => ?_
            exact sum_sign_shift_eq_zero _ ⟨a, hAmem⟩ fun h₂ => hsh2 1 y h h₂]
        rw [add_zero]
        -- in the `x = 0` half, split the second `t₀`-coordinate
        rw [show (∑ h : ↥(ω a).ker, ∑ p2 : ZMod 2 × ↥(ω a).ker,
              sign (ω (eT (0, h)) (eT (0, h)) + ω (eT p2) (eT p2)
                + ω (eT (0, h)) (eT p2)))
            = ∑ h : ↥(ω a).ker,
                ((∑ h₂ : ↥(ω a).ker,
                  sign (ω (eT (0, h)) (eT (0, h)) + ω (eT (0, h₂)) (eT (0, h₂))
                    + ω (eT (0, h)) (eT (0, h₂))))
                + (∑ h₂ : ↥(ω a).ker,
                  sign (ω (eT (0, h)) (eT (0, h)) + ω (eT (1, h₂)) (eT (1, h₂))
                    + ω (eT (0, h)) (eT (1, h₂))))) from
          Finset.sum_congr rfl fun h _ => by
            rw [Fintype.sum_prod_type,
              show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
              Finset.sum_insert (by decide), Finset.sum_singleton]]
        rw [Finset.sum_add_distrib]
        -- the `y = 1` half vanishes: shift the outer kernel index by `a`
        rw [show (∑ h : ↥(ω a).ker, ∑ h₂ : ↥(ω a).ker,
              sign (ω (eT (0, h)) (eT (0, h)) + ω (eT (1, h₂)) (eT (1, h₂))
                + ω (eT (0, h)) (eT (1, h₂)))) = 0 from
          sum_neg_shift_eq_zero _ ⟨a, hAmem⟩ fun h => by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun h₂ _ => by
              rw [hsh1 0 1 h h₂, zmod2_sign_add_one]]
        rw [add_zero]
        -- the surviving block is the kernel count; descend and finish
        rw [show (∑ h : ↥(ω a).ker, ∑ h₂ : ↥(ω a).ker,
              sign (ω (eT (0, h)) (eT (0, h)) + ω (eT (0, h₂)) (eT (0, h₂))
                + ω (eT (0, h)) (eT (0, h₂))))
            = ∑ h : ↥(ω a).ker, ∑ h₂ : ↥(ω a).ker,
                sign (ωH h h + ωH h₂ h₂ + ωH h h₂) from
          Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h₂ _ =>
            congrArg sign (hE00 h h₂)]
        rw [hDH]
        ring

/-- The **corrected monodromy** on `C = ker ψH`: from the monodromy `MH` on `H = ker (ω a)`
fixing `⟨a, ·⟩`, the map `c ↦ MH c + ψH(MH c) • a` is an automorphism of `C` that is again a
`2`-power-order monodromy for the restricted form `ωC` (`ωC t u = ωC u (MC t)`). -/
private theorem wall_count_corrected_monodromy {W : Type u} [AddCommGroup W]
    (ω : W →+ W →+ ZMod 2) (M : W ≃+ W) (hM : ∀ t u : W, ω t u = ω u (M t))
    (a : W) (hAmem : a ∈ (ω a).ker) (hMa : M a = a) [Fintype ↥(ω a).ker]
    (h2H : ∀ h : ↥(ω a).ker, h + h = 0)
    (MH : ↥(ω a).ker ≃+ ↥(ω a).ker) (hMHapp : ∀ h : ↥(ω a).ker, ↑(MH h) = M ↑h)
    {m : ℕ} (hMH2m : (⇑MH)^[2 ^ m] = id)
    (ψH : ↥(ω a).ker →+ ZMod 2) (hψA : ψH ⟨a, hAmem⟩ = 1)
    (ωC : ↥ψH.ker →+ ↥ψH.ker →+ ZMod 2) (hωC : ∀ t u : ↥ψH.ker, ωC t u = ω ↑↑t ↑↑u)
    (hcmem'' : ∀ c : ↥ψH.ker, ω ↑↑c a = 0) :
    ∃ MC : ↥ψH.ker ≃+ ↥ψH.ker,
      (∀ t u : ↥ψH.ker, ωC t u = ωC u (MC t)) ∧ ∃ m' : ℕ, (⇑MC)^[2 ^ m'] = id := by
  have hMAfix : MH ⟨a, hAmem⟩ = ⟨a, hAmem⟩ := Subtype.ext (by rw [hMHapp]; exact hMa)
  have hMCmem : ∀ c : ↥ψH.ker,
      MH ↑c + (ψH (MH ↑c)).val • ⟨a, hAmem⟩ ∈ ψH.ker := by
    intro c
    rw [AddMonoidHom.mem_ker, map_add, map_nsmul, hψA]
    exact zmod2_self_add_val_smul_one _
  let MC0 : ↥ψH.ker →+ ↥ψH.ker :=
    AddMonoidHom.mk' (fun c => ⟨MH ↑c + (ψH (MH ↑c)).val • ⟨a, hAmem⟩, hMCmem c⟩) (by
      intro c c'
      refine Subtype.ext ?_
      show MH ↑(c + c') + (ψH (MH ↑(c + c'))).val • _ = _
      rw [AddSubgroup.coe_add, map_add, map_add, zmod2_val_add_smul h2H]
      show _ = (MH ↑c + (ψH (MH ↑c)).val • ⟨a, hAmem⟩)
        + (MH ↑c' + (ψH (MH ↑c')).val • ⟨a, hAmem⟩)
      abel)
  have hMCapp : ∀ c : ↥ψH.ker, (↑(MC0 c) : ↥(ω a).ker)
      = MH ↑c + (ψH (MH ↑c)).val • ⟨a, hAmem⟩ := fun _ => rfl
  have hMC0inj : Function.Injective MC0 := by
    intro c c' hcc
    have hval : MH ↑c + (ψH (MH ↑c)).val • (⟨a, hAmem⟩ : ↥(ω a).ker)
        = MH ↑c' + (ψH (MH ↑c')).val • ⟨a, hAmem⟩ := congrArg Subtype.val hcc
    have hd : MH (↑c + ↑c') = (ψH (MH ↑c) + ψH (MH ↑c')).val • ⟨a, hAmem⟩ := by
      have h0 : (MH ↑c + (ψH (MH ↑c)).val • (⟨a, hAmem⟩ : ↥(ω a).ker))
          + (MH ↑c' + (ψH (MH ↑c')).val • ⟨a, hAmem⟩)
          = MH (↑c + ↑c') + (ψH (MH ↑c) + ψH (MH ↑c')).val • ⟨a, hAmem⟩ := by
        rw [map_add, zmod2_val_add_smul h2H]
        abel
      rw [hval, h2H] at h0
      have h1 := congrArg
        (· + (ψH (MH ↑c) + ψH (MH ↑c')).val • (⟨a, hAmem⟩ : ↥(ω a).ker)) h0.symm
      simpa [add_assoc, h2H] using h1
    rcases ZMod.eq_zero_or_eq_one (ψH (MH ↑c) + ψH (MH ↑c')) with hε | hε
    · rw [hε, ZMod.val_zero, zero_nsmul] at hd
      have h0 : (↑c : ↥(ω a).ker) + ↑c' = 0 := by
        apply MH.injective
        rw [hd, map_zero]
      have h1 := congrArg (· + (↑c' : ↥(ω a).ker)) h0
      refine Subtype.ext ?_
      simpa [add_assoc, h2H] using h1
    · rw [hε, ZMod.val_one, one_nsmul] at hd
      have h0 : (↑c : ↥(ω a).ker) + ↑c' = ⟨a, hAmem⟩ := by
        apply MH.injective
        rw [hd, hMAfix]
      have h1 : ψH (↑c + ↑c') = 1 := by rw [h0]; exact hψA
      rw [map_add, AddMonoidHom.mem_ker.mp c.2, AddMonoidHom.mem_ker.mp c'.2,
        add_zero] at h1
      exact absurd h1 (by decide)
  let MC : ↥ψH.ker ≃+ ↥ψH.ker :=
    AddEquiv.ofBijective MC0 ⟨hMC0inj, Finite.injective_iff_surjective.mp hMC0inj⟩
  have hMCapp' : ∀ c : ↥ψH.ker, (↑(MC c) : ↥(ω a).ker)
      = MH ↑c + (ψH (MH ↑c)).val • ⟨a, hAmem⟩ := fun _ => rfl
  -- monodromy identity on `C`
  have hMCrest : ∀ t u : ↥ψH.ker, ωC t u = ωC u (MC t) := by
    intro t u
    rw [hωC, hωC]
    have hcoe : ((↑↑(MC t) : ↥(ω a).ker) : W) = M ↑↑t + (ψH (MH ↑t)).val • a := by
      rw [hMCapp']
      push_cast
      rw [hMHapp]
    rw [hcoe, map_add, map_nsmul, zmod2_val_smul, hcmem'' u, mul_zero, add_zero]
    exact hM ↑↑t ↑↑u
  -- 2-power order on `C`
  have hMC2 : ∃ m' : ℕ, (⇑MC)^[2 ^ m'] = id := by
    refine ⟨m, ?_⟩
    have hiter : ∀ (i : ℕ) (c : ↥ψH.ker),
        (↑((⇑MC)^[i] c) : ↥(ω a).ker)
          = (⇑MH)^[i] ↑c + (ψH ((⇑MH)^[i] ↑c)).val • ⟨a, hAmem⟩ := by
      intro i
      induction i with
      | zero =>
        intro c
        show (↑c : ↥(ω a).ker) = ↑c + (ψH ↑c).val • ⟨a, hAmem⟩
        rw [AddMonoidHom.mem_ker.mp c.2, ZMod.val_zero, zero_nsmul, add_zero]
      | succ i ihi =>
        intro c
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        rw [hMCapp' ((⇑MC)^[i] c), ihi c]
        rw [map_add, map_nsmul, hMAfix]
        rw [show ψH (MH ((⇑MH)^[i] ↑c) + (ψH ((⇑MH)^[i] ↑c)).val • ⟨a, hAmem⟩)
              = ψH (MH ((⇑MH)^[i] ↑c)) + ψH ((⇑MH)^[i] ↑c) from by
            rw [map_add, map_nsmul, hψA, zmod2_val_smul, mul_one]]
        rw [zmod2_val_add_smul h2H]
        rw [show ∀ X Y Z : ↥(ω a).ker, (X + Y) + (Z + Y) = (X + Z) + (Y + Y) from
          fun X Y Z => by abel, h2H, add_zero]
    funext c
    refine Subtype.ext ?_
    rw [hiter, hMH2m]
    show (↑c : ↥(ω a).ker) + (ψH ↑c).val • ⟨a, hAmem⟩ = ↑c
    rw [AddMonoidHom.mem_ker.mp c.2, ZMod.val_zero, zero_nsmul, add_zero]
  exact ⟨MC, hMCrest, hMC2⟩

/-- If a monodromy `MH` on a subobject `K ↪ W` (embedding `f`, injective) is intertwined with a
monodromy `M` on `W` (`f (MH h) = M (f h)`) and `M` has `2`-power order `2 ^ m`, then so does
`MH`.  (Iterating the intertwining relation and cancelling the injection.) -/
private theorem wall_count_ker_monodromy_pow {W : Type u} [AddCommGroup W] (M : W ≃+ W)
    {K : Type u} [AddCommGroup K] (MH : K ≃+ K) (f : K → W) (hf : Function.Injective f)
    (hMHapp : ∀ h : K, f (MH h) = M (f h)) {m : ℕ} (hm : (⇑M)^[2 ^ m] = id) :
    (⇑MH)^[2 ^ m] = id := by
  have hiter : ∀ (i : ℕ) (h : K), f ((⇑MH)^[i] h) = (⇑M)^[i] (f h) := by
    intro i
    induction i with
    | zero => intro h; rfl
    | succ i ihi =>
      intro h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hMHapp, ihi]
  funext h
  refine hf ?_
  simp only [hiter, hm, id_eq]

/-- Isotropic shift, inner index: with `W ≃ ZMod 2 × ker (ω a)` split along `t₀` (`he2`) and
`a ∈ ker (ω a)`, shifting the *inner* kernel index by `a` changes the Wall exponent by exactly
the *outer* `t₀`-coordinate `x`.  (Every `⟨a⟩`-cross term is a `t₀`-coordinate multiple.) -/
private theorem wall_count_isotropic_shift_inner {W : Type u} [AddCommGroup W]
    (ω : W →+ W →+ ZMod 2) (a t₀ : W) (hAmem : a ∈ (ω a).ker)
    (eT : ZMod 2 × ↥(ω a).ker ≃ W)
    (he2 : ∀ (x : ZMod 2) (h : ↥(ω a).ker), eT (x, h) = x.val • t₀ + ↑h)
    (haa : ω a a = 0) (ht₀1 : ω t₀ a = 1) (hat₀ : ω a t₀ = 1)
    (hmem : ∀ h : ↥(ω a).ker, ω a ↑h = 0) (hmem' : ∀ h : ↥(ω a).ker, ω ↑h a = 0) :
    ∀ (x y : ZMod 2) (h h₂ : ↥(ω a).ker),
      (ω (eT (x, h)) (eT (x, h)) + ω (eT (y, h₂ + ⟨a, hAmem⟩)) (eT (y, h₂ + ⟨a, hAmem⟩))
        + ω (eT (x, h)) (eT (y, h₂ + ⟨a, hAmem⟩)))
      = (ω (eT (x, h)) (eT (x, h)) + ω (eT (y, h₂)) (eT (y, h₂))
        + ω (eT (x, h)) (eT (y, h₂))) + x := by
  intro x y h h₂
  simp only [he2, AddSubgroup.coe_add, omega_expand]
  simp only [map_add, AddMonoidHom.add_apply, hmem, hmem', haa, ht₀1, hat₀, add_zero]
  linear_combination (CharTwo.add_self_eq_zero y : y + y = 0)

/-- Isotropic shift, outer index: shifting the *outer* kernel index by `a` changes the Wall
exponent by exactly the *inner* `t₀`-coordinate `y` (mirror of `wall_count_isotropic_shift_inner`).
-/
private theorem wall_count_isotropic_shift_outer {W : Type u} [AddCommGroup W]
    (ω : W →+ W →+ ZMod 2) (a t₀ : W) (hAmem : a ∈ (ω a).ker)
    (eT : ZMod 2 × ↥(ω a).ker ≃ W)
    (he2 : ∀ (x : ZMod 2) (h : ↥(ω a).ker), eT (x, h) = x.val • t₀ + ↑h)
    (haa : ω a a = 0) (ht₀1 : ω t₀ a = 1) (hat₀ : ω a t₀ = 1)
    (hmem : ∀ h : ↥(ω a).ker, ω a ↑h = 0) (hmem' : ∀ h : ↥(ω a).ker, ω ↑h a = 0) :
    ∀ (x y : ZMod 2) (h h₂ : ↥(ω a).ker),
      (ω (eT (x, h + ⟨a, hAmem⟩)) (eT (x, h + ⟨a, hAmem⟩)) + ω (eT (y, h₂)) (eT (y, h₂))
        + ω (eT (x, h + ⟨a, hAmem⟩)) (eT (y, h₂)))
      = (ω (eT (x, h)) (eT (x, h)) + ω (eT (y, h₂)) (eT (y, h₂))
        + ω (eT (x, h)) (eT (y, h₂))) + y := by
  intro x y h h₂
  simp only [he2, AddSubgroup.coe_add, omega_expand]
  simp only [map_add, AddMonoidHom.add_apply, hmem, hmem', haa, ht₀1, hat₀, add_zero]
  linear_combination (CharTwo.add_self_eq_zero x : x + x = 0)

/-- Isotropic diagonal block: on the `x = y = 0` block of the `t₀`-split, the Wall summand of `ω`
is the kernel-level summand of the restricted form `ωH` (the `t₀`-coordinates being zero). -/
private theorem wall_count_isotropic_diag_block {W : Type u} [AddCommGroup W]
    (ω : W →+ W →+ ZMod 2) (a t₀ : W)
    (ωH : ↥(ω a).ker →+ ↥(ω a).ker →+ ZMod 2)
    (hωH : ∀ t u : ↥(ω a).ker, ωH t u = ω ↑t ↑u)
    (eT : ZMod 2 × ↥(ω a).ker ≃ W)
    (he2 : ∀ (x : ZMod 2) (h : ↥(ω a).ker), eT (x, h) = x.val • t₀ + ↑h) :
    ∀ h h₂ : ↥(ω a).ker,
      (ω (eT (0, h)) (eT (0, h)) + ω (eT (0, h₂)) (eT (0, h₂))
        + ω (eT (0, h)) (eT (0, h₂)))
      = ωH h h + ωH h₂ h₂ + ωH h h₂ := by
  intro h h₂
  simp only [he2, ZMod.val_zero, zero_nsmul, zero_add]
  rw [hωH, hωH, hωH]

/-- Inductive step of `wall_count_aux`, **isotropic case** `ω a a = 0`.  Choosing `t₀` with
`ω t₀ a = 1` and splitting `W` along `t₀`, shifting the inner index by `a` changes the
exponent by exactly the outer `t₀`-coordinate, so every block with a `t₀`-component cancels;
on the surviving `ker (ω a)²` block the `⟨a⟩`-coordinates are invisible, giving `4 ·` the count
on `C = ker ψ` (`ψ = ω t₀` restricted, monodromy `M` corrected by an `a`-component). -/
private theorem wall_count_aux_isotropic {n : ℕ}
    (ih : ∀ (W : Type u) [AddCommGroup W] [Fintype W],
      (∀ w : W, w + w = 0) → ∀ (ω : W →+ W →+ ZMod 2) (M : W ≃+ W),
        (∀ t u : W, ω t u = ω u (M t)) → (∃ m : ℕ, (⇑M)^[2 ^ m] = id) →
        (∀ u : W, (∀ t : W, ω t u = 0) → u = 0) →
        ∀ k : ℕ, Nat.card W = 2 ^ k → Fintype.card W ≤ n →
        (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ k)
    (W : Type u) [AddCommGroup W] [Fintype W]
    (h2 : ∀ w : W, w + w = 0) (ω : W →+ W →+ ZMod 2) (M : W ≃+ W)
    (hM : ∀ t u : W, ω t u = ω u (M t)) (hM2 : ∃ m : ℕ, (⇑M)^[2 ^ m] = id)
    (hnd : ∀ u : W, (∀ t : W, ω t u = 0) → u = 0)
    (k : ℕ) (hk : Nat.card W = 2 ^ k) (hn : Fintype.card W ≤ n + 1)
    (a : W) (ha0 : a ≠ 0) (hMa : M a = a) (haa : ω a a = 0) :
    (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ k := by
  obtain ⟨m, hm⟩ := hM2
  -- the row and column functionals of the `M`-fixed vector agree
  have hacol : ∀ u : W, ω a u = ω u a := fun u => by rw [hM a u, hMa]
  -- `M` preserves `ker (ω a)`
  have hMker : ∀ u : W, ω a u = 0 → ω a (M u) = 0 := by
    intro u hu
    rw [← hM u a, ← hacol u]
    exact hu
  -- shared restricted structure on `H = ker (ω a)`
  haveI : Fintype ↥(ω a).ker := Fintype.ofFinite _
  have h2H : ∀ h : ↥(ω a).ker, h + h = 0 := fun h => Subtype.ext (h2 (h : W))
  have hmem : ∀ h : ↥(ω a).ker, ω a ↑h = 0 := fun h => h.2
  have hmem' : ∀ h : ↥(ω a).ker, ω ↑h a = 0 := fun h => by rw [← hacol]; exact hmem h
  -- the doubly-restricted form
  let ωH : ↥(ω a).ker →+ ↥(ω a).ker →+ ZMod 2 :=
    AddMonoidHom.mk' (fun t => (ω ↑t).comp (ω a).ker.subtype) (by
      intro t t'
      ext u
      simp [map_add])
  have hωH : ∀ t u : ↥(ω a).ker, ωH t u = ω ↑t ↑u := fun _ _ => rfl
  -- restricted monodromy on `ker (ω a)` (shared by both cases)
  have hMHmem : ∀ h : ↥(ω a).ker, M ↑h ∈ (ω a).ker := fun h =>
    AddMonoidHom.mem_ker.mpr (hMker ↑h (hmem h))
  let MH0 : ↥(ω a).ker →+ ↥(ω a).ker :=
    AddMonoidHom.mk' (fun h => ⟨M ↑h, hMHmem h⟩) (by
      intro t t'
      ext
      simp)
  have hMH0inj : Function.Injective MH0 := by
    intro t t' htt
    exact Subtype.ext (M.injective (congrArg Subtype.val htt))
  let MH : ↥(ω a).ker ≃+ ↥(ω a).ker :=
    AddEquiv.ofBijective MH0 ⟨hMH0inj, Finite.injective_iff_surjective.mp hMH0inj⟩
  have hMHapp : ∀ h : ↥(ω a).ker, ↑(MH h) = M ↑h := fun _ => rfl
  have hMH2m : (⇑MH)^[2 ^ m] = id :=
    wall_count_ker_monodromy_pow M MH _ Subtype.coe_injective hMHapp hm
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : W, ω t₀ a ≠ 0 := by
    by_contra hcon
    exact ha0 (hnd a fun t => not_not.mp (not_exists.mp hcon t))
  have ht₀1 : ω t₀ a = 1 := zmod2_ne_zero_eq_one _ ht₀
  have hat₀ : ω a t₀ = 1 := by rw [hacol t₀]; exact ht₀1
  have hAmem : a ∈ (ω a).ker := AddMonoidHom.mem_ker.mpr haa
  -- the inner functional `ψ` and its kernel `C`
  set ψH : ↥(ω a).ker →+ ZMod 2 := (ω t₀).comp (ω a).ker.subtype with hψdef
  have hψA : ψH ⟨a, hAmem⟩ = 1 := ht₀1
  haveI : Fintype ↥ψH.ker := Fintype.ofFinite _
  have h2C : ∀ c : ↥ψH.ker, c + c = 0 := fun c => Subtype.ext (h2H (c : ↥(ω a).ker))
  have hcmem : ∀ c : ↥ψH.ker, ω t₀ ↑↑c = 0 := fun c => AddMonoidHom.mem_ker.mp c.2
  have hcmem' : ∀ c : ↥ψH.ker, ω a ↑↑c = 0 := fun c => hmem ↑c
  have hcmem'' : ∀ c : ↥ψH.ker, ω ↑↑c a = 0 := fun c => hmem' ↑c
  -- the doubly-restricted form
  let ωC : ↥ψH.ker →+ ↥ψH.ker →+ ZMod 2 :=
    AddMonoidHom.mk' (fun t => (ωH ↑t).comp ψH.ker.subtype) (by
      intro t t'
      ext u
      simp [map_add])
  have hωC : ∀ t u : ↥ψH.ker, ωC t u = ω ↑↑t ↑↑u := fun _ _ => rfl
  -- the corrected monodromy `c ↦ MH c + ψ (MH c) • a` on `C`
  obtain ⟨MC, hMCrest, hMC2⟩ := wall_count_corrected_monodromy ω M hM a hAmem hMa
    h2H MH hMHapp hMH2m ψH hψA ωC hωC hcmem''
  -- nondegeneracy on `C`
  have hndC : ∀ u : ↥ψH.ker, (∀ t : ↥ψH.ker, ωC t u = 0) → u = 0 := by
    intro u hu
    refine Subtype.ext (Subtype.ext (hnd ↑↑u fun s => ?_))
    obtain ⟨⟨x, h⟩, rfl⟩ := (splitEquiv h2 (ω a) t₀ hat₀).surjective s
    obtain ⟨⟨y, c⟩, rfl⟩ := (splitEquiv h2H ψH ⟨a, hAmem⟩ hψA).surjective h
    rw [splitEquiv_apply, splitEquiv_apply]
    rw [map_add, AddMonoidHom.add_apply, map_nsmul, AddMonoidHom.nsmul_apply,
      zmod2_val_smul, hcmem u, mul_zero, zero_add]
    rw [show ((↑(y.val • (⟨a, hAmem⟩ : ↥(ω a).ker) + ↑c) : ↥(ω a).ker) : W)
          = y.val • a + ↑↑c from by push_cast; rfl]
    rw [map_add, AddMonoidHom.add_apply, map_nsmul, AddMonoidHom.nsmul_apply,
      zmod2_val_smul, hcmem' u, mul_zero, zero_add]
    exact hu c
  -- cardinalities
  have hc1 : Nat.card W = 2 * Nat.card ↥(ω a).ker :=
    card_of_splitEquiv h2 (ω a) t₀ hat₀
  have hc2 : Nat.card ↥(ω a).ker = 2 * Nat.card ↥ψH.ker :=
    card_of_splitEquiv h2H ψH ⟨a, hAmem⟩ hψA
  haveI : Nonempty ↥ψH.ker := ⟨0⟩
  have hCpos := Nat.card_pos (α := ↥ψH.ker)
  obtain ⟨k'', rfl⟩ : ∃ k'', k = k'' + 2 := by
    rcases k with _ | _ | k''
    · rw [pow_zero] at hk; omega
    · rw [pow_one] at hk; omega
    · exact ⟨k'', rfl⟩
  have hkC : Nat.card ↥ψH.ker = 2 ^ k'' := by
    have h4 : 4 * Nat.card ↥ψH.ker = 4 * 2 ^ k'' := by
      have : (2 : ℕ) ^ (k'' + 2) = 4 * 2 ^ k'' := by ring
      omega
    omega
  have hnC : Fintype.card ↥ψH.ker ≤ n := by
    have e1 : Nat.card W = Fintype.card W := Nat.card_eq_fintype_card
    have e2 : Nat.card ↥ψH.ker = Fintype.card ↥ψH.ker := Nat.card_eq_fintype_card
    omega
  have hIH := ih ↥ψH.ker h2C ωC MC hMCrest hMC2 hndC k'' hkC hnC
  -- ### the sum computation
  set eT : ZMod 2 × ↥(ω a).ker ≃ W := splitEquiv h2 (ω a) t₀ hat₀ with heTdef
  have he2 : ∀ (x : ZMod 2) (h : ↥(ω a).ker), eT (x, h) = x.val • t₀ + ↑h :=
    fun _ _ => rfl
  -- shifting the inner index by `a` changes the exponent by the outer `t₀`-coordinate
  have hsh2 := wall_count_isotropic_shift_inner ω a t₀ hAmem eT he2 haa ht₀1 hat₀ hmem hmem'
  -- shifting the outer kernel index changes the exponent by the inner `t₀`-coordinate
  have hsh1 := wall_count_isotropic_shift_outer ω a t₀ hAmem eT he2 haa ht₀1 hat₀ hmem hmem'
  -- the `(0,0)`-block is the kernel-level count
  have hE00 := wall_count_isotropic_diag_block ω a t₀ ωH hωH eT he2
  -- kernel-level count is `⟨a⟩`-blind: it descends to `C` with multiplicity 4
  have hDH : (∑ h : ↥(ω a).ker, ∑ h₂ : ↥(ω a).ker,
        sign (ωH h h + ωH h₂ h₂ + ωH h h₂)) = (4 : ℤ) * (-2) ^ k'' :=
    wall_count_descent h2H ωH ψH ⟨a, hAmem⟩ hψA haa hcmem' hcmem'' ωC hωC hIH
  -- assemble: reindex, split the two `t₀`-coordinates, kill the odd blocks
  exact wall_count_isotropic_assemble ω a hAmem ωH eT hsh2 hsh1 hE00 hDH

/-- Inductive step of `wall_count_aux`, **anisotropic case** `ω a a = 1`.  Splitting
`W ≃ ZMod 2 × ker (ω a)` along `a`, the count factors as
`(∑_{x,y} (−1)^{x+y+xy}) · (kernel count) = (−2) · (−2)^{k−1}`. -/
private theorem wall_count_aux_anisotropic {n : ℕ}
    (ih : ∀ (W : Type u) [AddCommGroup W] [Fintype W],
      (∀ w : W, w + w = 0) → ∀ (ω : W →+ W →+ ZMod 2) (M : W ≃+ W),
        (∀ t u : W, ω t u = ω u (M t)) → (∃ m : ℕ, (⇑M)^[2 ^ m] = id) →
        (∀ u : W, (∀ t : W, ω t u = 0) → u = 0) →
        ∀ k : ℕ, Nat.card W = 2 ^ k → Fintype.card W ≤ n →
        (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ k)
    (W : Type u) [AddCommGroup W] [Fintype W]
    (h2 : ∀ w : W, w + w = 0) (ω : W →+ W →+ ZMod 2) (M : W ≃+ W)
    (hM : ∀ t u : W, ω t u = ω u (M t)) (hM2 : ∃ m : ℕ, (⇑M)^[2 ^ m] = id)
    (hnd : ∀ u : W, (∀ t : W, ω t u = 0) → u = 0)
    (k : ℕ) (hk : Nat.card W = 2 ^ k) (hn : Fintype.card W ≤ n + 1)
    (a : W) (_ha0 : a ≠ 0) (hMa : M a = a) (haa : ω a a = 1) :
    (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ k := by
  obtain ⟨m, hm⟩ := hM2
  -- the row and column functionals of the `M`-fixed vector agree
  have hacol : ∀ u : W, ω a u = ω u a := fun u => by rw [hM a u, hMa]
  -- `M` preserves `ker (ω a)`
  have hMker : ∀ u : W, ω a u = 0 → ω a (M u) = 0 := by
    intro u hu
    rw [← hM u a, ← hacol u]
    exact hu
  -- shared restricted structure on `H = ker (ω a)`
  haveI : Fintype ↥(ω a).ker := Fintype.ofFinite _
  have h2H : ∀ h : ↥(ω a).ker, h + h = 0 := fun h => Subtype.ext (h2 (h : W))
  have hmem : ∀ h : ↥(ω a).ker, ω a ↑h = 0 := fun h => h.2
  have hmem' : ∀ h : ↥(ω a).ker, ω ↑h a = 0 := fun h => by rw [← hacol]; exact hmem h
  -- the doubly-restricted form
  let ωH : ↥(ω a).ker →+ ↥(ω a).ker →+ ZMod 2 :=
    AddMonoidHom.mk' (fun t => (ω ↑t).comp (ω a).ker.subtype) (by
      intro t t'
      ext u
      simp [map_add])
  have hωH : ∀ t u : ↥(ω a).ker, ωH t u = ω ↑t ↑u := fun _ _ => rfl
  -- restricted monodromy on `ker (ω a)` (shared by both cases)
  have hMHmem : ∀ h : ↥(ω a).ker, M ↑h ∈ (ω a).ker := fun h =>
    AddMonoidHom.mem_ker.mpr (hMker ↑h (hmem h))
  let MH0 : ↥(ω a).ker →+ ↥(ω a).ker :=
    AddMonoidHom.mk' (fun h => ⟨M ↑h, hMHmem h⟩) (by
      intro t t'
      ext
      simp)
  have hMH0inj : Function.Injective MH0 := by
    intro t t' htt
    exact Subtype.ext (M.injective (congrArg Subtype.val htt))
  let MH : ↥(ω a).ker ≃+ ↥(ω a).ker :=
    AddEquiv.ofBijective MH0 ⟨hMH0inj, Finite.injective_iff_surjective.mp hMH0inj⟩
  have hMHapp : ∀ h : ↥(ω a).ker, ↑(MH h) = M ↑h := fun _ => rfl
  have hMrest : ∀ t u : ↥(ω a).ker, ωH t u = ωH u (MH t) := by
    intro t u
    rw [hωH, hωH, hMHapp]
    exact hM ↑t ↑u
  have hMH2m : (⇑MH)^[2 ^ m] = id := by
    have hiter : ∀ (i : ℕ) (h : ↥(ω a).ker), ↑((⇑MH)^[i] h) = (⇑M)^[i] (h : W) := by
      intro i
      induction i with
      | zero => intro h; rfl
      | succ i ihi =>
        intro h
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hMHapp, ihi]
    funext h
    refine Subtype.ext ?_
    rw [hiter, hm]
    rfl
  have hMH2 : ∃ m' : ℕ, (⇑MH)^[2 ^ m'] = id := ⟨m, hMH2m⟩
  -- nondegeneracy restricts
  have hndH : ∀ u : ↥(ω a).ker, (∀ t : ↥(ω a).ker, ωH t u = 0) → u = 0 := by
    intro u hu
    refine Subtype.ext (hnd ↑u fun t => ?_)
    obtain ⟨⟨x, h⟩, rfl⟩ := (splitEquiv h2 (ω a) a haa).surjective t
    rw [splitEquiv_apply]
    rw [map_add, AddMonoidHom.add_apply, map_nsmul, AddMonoidHom.nsmul_apply,
      zmod2_val_smul, hmem u, mul_zero, zero_add]
    exact hu h
  -- cardinalities
  have hcard2 : Nat.card W = 2 * Nat.card ↥(ω a).ker := card_of_splitEquiv h2 (ω a) a haa
  haveI : Nonempty ↥(ω a).ker := ⟨0⟩
  have hHpos := Nat.card_pos (α := ↥(ω a).ker)
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hkH : Nat.card ↥(ω a).ker = 2 ^ k' := by
    have h : 2 * Nat.card ↥(ω a).ker = 2 * 2 ^ k' := by
      rw [← hcard2, hk, pow_succ']
    omega
  have hnH : Fintype.card ↥(ω a).ker ≤ n := by
    have h1 : Nat.card W = Fintype.card W := Nat.card_eq_fintype_card
    have h2' : Nat.card ↥(ω a).ker = Fintype.card ↥(ω a).ker := Nat.card_eq_fintype_card
    omega
  have hIH := ih ↥(ω a).ker h2H ωH MH hMrest hMH2 hndH k' hkH hnH
  -- the split-coordinate expansion of the summand
  have he_apply : ∀ (x : ZMod 2) (h : ↥(ω a).ker),
      splitEquiv h2 (ω a) a haa (x, h) = x.val • a + ↑h := fun _ _ => rfl
  have hEsplit : ∀ (x y : ZMod 2) (h h₂ : ↥(ω a).ker),
      ω (splitEquiv h2 (ω a) a haa (x, h)) (splitEquiv h2 (ω a) a haa (x, h))
        + ω (splitEquiv h2 (ω a) a haa (y, h₂)) (splitEquiv h2 (ω a) a haa (y, h₂))
        + ω (splitEquiv h2 (ω a) a haa (x, h)) (splitEquiv h2 (ω a) a haa (y, h₂))
        = (x + y + x * y) + (ωH h h + ωH h₂ h₂ + ωH h h₂) := by
    intro x y h h₂
    rw [he_apply, he_apply, omega_expand, omega_expand, omega_expand,
      haa, hωH, hωH, hωH, hmem h, hmem h₂, hmem' h, hmem' h₂]
    simp only [mul_one, mul_zero, add_zero, zmod2_mul_self]
    ring
  -- reindex and factor
  calc (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u))
      = ∑ q : (ZMod 2 × ↥(ω a).ker) × (ZMod 2 × ↥(ω a).ker),
          sign (ω (splitEquiv h2 (ω a) a haa q.1) (splitEquiv h2 (ω a) a haa q.1)
            + ω (splitEquiv h2 (ω a) a haa q.2) (splitEquiv h2 (ω a) a haa q.2)
            + ω (splitEquiv h2 (ω a) a haa q.1) (splitEquiv h2 (ω a) a haa q.2)) := by
        rw [← Fintype.sum_prod_type']
        exact (Equiv.sum_comp
          ((splitEquiv h2 (ω a) a haa).prodCongr (splitEquiv h2 (ω a) a haa))
          fun p : W × W => sign (ω p.1 p.1 + ω p.2 p.2 + ω p.1 p.2)).symm
    _ = ∑ r : (ZMod 2 × ZMod 2) × (↥(ω a).ker × ↥(ω a).ker),
          sign ((r.1.1 + r.1.2 + r.1.1 * r.1.2)
            + (ωH r.2.1 r.2.1 + ωH r.2.2 r.2.2 + ωH r.2.1 r.2.2)) := by
        rw [← Equiv.sum_comp
          (Equiv.prodProdProdComm (ZMod 2) ↥(ω a).ker (ZMod 2) ↥(ω a).ker).symm]
        refine Finset.sum_congr rfl fun r _ => ?_
        obtain ⟨⟨x, y⟩, h, h₂⟩ := r
        exact congrArg sign (hEsplit x y h h₂)
    _ = (∑ pxy : ZMod 2 × ZMod 2, sign (pxy.1 + pxy.2 + pxy.1 * pxy.2))
          * (∑ phh : ↥(ω a).ker × ↥(ω a).ker,
              sign (ωH phh.1 phh.1 + ωH phh.2 phh.2 + ωH phh.1 phh.2)) := by
        rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun pxy _ => ?_
        refine Finset.sum_congr rfl fun phh _ => ?_
        rw [sign_add]
    _ = (-2 : ℤ) ^ (k' + 1) := by
        rw [show (∑ pxy : ZMod 2 × ZMod 2, sign (pxy.1 + pxy.2 + pxy.1 * pxy.2))
              = -2 from by decide]
        rw [show (∑ phh : ↥(ω a).ker × ↥(ω a).ker,
              sign (ωH phh.1 phh.1 + ωH phh.2 phh.2 + ωH phh.1 phh.2))
            = (-2 : ℤ) ^ k' from by rw [Fintype.sum_prod_type]; exact hIH]
        ring

/-- **The abstract Wall count**, by strong induction on the cardinality: for a biadditive
`ω` on a finite exponent-2 group `W`, right-nondegenerate and with a `2`-power-order monodromy
`M` (`ω t u = ω u (M t)`), the count `∑_{t,u} (−1)^{ω(t,t)+ω(u,u)+ω(t,u)}` equals `(−2)^k`,
`#W = 2^k`. -/
private theorem wall_count_aux :
    ∀ (n : ℕ) (W : Type u) [AddCommGroup W] [Fintype W],
      ∀ (_h2 : ∀ w : W, w + w = 0) (ω : W →+ W →+ ZMod 2) (M : W ≃+ W),
        (∀ t u : W, ω t u = ω u (M t)) → (∃ m : ℕ, (⇑M)^[2 ^ m] = id) →
        (∀ u : W, (∀ t : W, ω t u = 0) → u = 0) →
        ∀ k : ℕ, Nat.card W = 2 ^ k → Fintype.card W ≤ n →
        (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ k := by
  intro n
  induction n with
  | zero =>
    intro W _ _ h2 ω M hM hM2 hnd k hk hn
    haveI : Nonempty W := ⟨0⟩
    exact absurd hn (by have := Fintype.card_pos (α := W); omega)
  | succ n ih =>
    intro W _ _ h2 ω M hM hM2 hnd k hk hn
    by_cases hW : ∀ w : W, w = 0
    · -- trivial group: `k = 0` and the double sum is the single term at `(0,0)`
      have huniv : (Finset.univ : Finset W) = {0} := by
        ext w; simp [hW w]
      have hk0 : k = 0 := by
        have h1 : Nat.card W = 1 := by
          rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv, Finset.card_singleton]
        rw [h1] at hk
        rcases Nat.pow_eq_one.mp hk.symm with h | h
        · norm_num at h
        · exact h
      subst hk0
      rw [huniv, Finset.sum_singleton, Finset.sum_singleton]
      simp [sign]
    · obtain ⟨w₀, hw₀⟩ := not_forall.mp hW
      obtain ⟨m, hm⟩ := id hM2
      obtain ⟨a, ha0, hMa⟩ := exists_fixed_ne_zero h2 m M hm w₀ hw₀
      rcases ZMod.eq_zero_or_eq_one (ω a a) with haa | haa
      · exact wall_count_aux_isotropic ih W h2 ω M hM hM2 hnd k hk hn a ha0 hMa haa
      · exact wall_count_aux_anisotropic ih W h2 ω M hM hM2 hnd k hk hn a ha0 hMa haa

/-- **The abstract Wall count**: for a biadditive `ω` on a finite exponent-2 group `W`,
right-nondegenerate and admitting a `2`-power-order monodromy `M` (`ω t u = ω u (M t)`),

  `∑_{t,u} (−1)^{ω(t,t) + ω(u,u) + ω(t,u)} = (−2)^k`,  where `#W = 2^k`.

In the application to Lemma 6.6 (Wall's sign relation), `W = im (1 + U)`, `ω` is the Wall form
`ω(Nx, u) = B(x, u)`, and the monodromy is `U⁻¹` (which is where the `2`-power-order hypothesis
on `U` enters). -/
theorem wall_count {W : Type u} [AddCommGroup W] [Fintype W]
    (h2 : ∀ w : W, w + w = 0) (ω : W →+ W →+ ZMod 2) (M : W ≃+ W)
    (hM : ∀ t u : W, ω t u = ω u (M t)) (hM2 : ∃ m : ℕ, (⇑M)^[2 ^ m] = id)
    (hnd : ∀ u : W, (∀ t : W, ω t u = 0) → u = 0)
    {k : ℕ} (hk : Nat.card W = 2 ^ k) :
    (∑ t : W, ∑ u : W, sign (ω t t + ω u u + ω t u)) = (-2 : ℤ) ^ k :=
  wall_count_aux (Fintype.card W) W h2 ω M hM hM2 hnd k hk le_rfl

end WallCount

/-! ## Duality and the kernel-perp identification

For the fiber computation we need `K^⊥ = im N` (`K = ker N`, `N = 1 + U`): the vectors pairing
trivially with every `U`-fixed vector are exactly the image of `N`.  The inclusion `⊇` is a
direct computation; `⊆` is a counting argument through the duality `#Hom(A, 𝔽₂) = #A` for
finite elementary abelian 2-groups. -/

section Duality

/-- Duality for finite elementary abelian 2-groups: `#Hom(A, 𝔽₂) = #A`. -/
theorem card_addHom_zmod2 (A : Type*) [AddCommGroup A] [Finite A]
    (h2 : ∀ x : A, x + x = 0) : Nat.card (A →+ ZMod 2) = Nat.card A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) A := AddCommGroup.zmodModule (n := 2) (by
    intro x
    rw [two_nsmul, h2])
  letI : Fintype A := Fintype.ofFinite A
  haveI : Finite (A →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun f => (f : A → ZMod 2)) DFunLike.coe_injective
  letI : Fintype (A →ₗ[ZMod 2] ZMod 2) := Fintype.ofFinite _
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2 (M := A) (M₁ := ZMod 2)).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hdual : Fintype.card (A →ₗ[ZMod 2] ZMod 2)
      = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) A) :=
    Module.card_eq_pow_finrank
  have hA : Fintype.card A = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) A :=
    Module.card_eq_pow_finrank
  rw [hdual, hA, Subspace.dual_finrank_eq]

/-- Rank–nullity by counting: `#im f · #ker f = #V`. -/
private theorem card_range_mul_card_ker {V : Type*} [AddCommGroup V] [Finite V]
    {T : Type*} [AddCommGroup T] (f : V →+ T) :
    Nat.card ↥f.range * Nat.card ↥f.ker = Nat.card V := by
  haveI : Finite ↥f.range := by
    refine Finite.of_surjective (fun v : V => (⟨f v, ⟨v, rfl⟩⟩ : ↥f.range)) ?_
    rintro ⟨_, ⟨v, rfl⟩⟩
    exact ⟨v, rfl⟩
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker).symm

variable {V : Type*} [AddCommGroup V] (q : V → ZMod 2) (U : V ≃+ V)

/-- Fixed vectors of `U` pair trivially with the image of `N = 1 + U`. -/
theorem polar_ker_range (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hUq : ∀ v, q (U v) = q v) (N : V →+ V) (hN : ∀ x, N x = x + U x)
    (s : V) (hs : N s = 0) (x : V) : polar q s (N x) = 0 := by
  have hUs : U s = s := by
    have h := hN s
    rw [hs] at h
    have h' := congrArg (s + ·) h.symm
    simpa [← add_assoc, h2 s] using h'
  rw [hN x, hq.polar_add_right]
  have hcross : polar q s (U x) = polar q s x := by
    conv_lhs => rw [← hUs]
    rw [polar_isometry_both q U hUq]
  rw [hcross]
  exact CharTwo.add_self_eq_zero _

/-- **`K^⊥ = im N`**: `u` pairs trivially with every `U`-fixed vector iff `u ∈ im (1 + U)`.
The forward inclusion is the duality counting (the pairing `V → Hom(ker N, 𝔽₂)` has kernel of
the size of `im N`); the reverse is `polar_ker_range`. -/
theorem perp_ker_iff_mem_range [Finite V] (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hns : Nonsingular q) (hUq : ∀ v, q (U v) = q v) (N : V →+ V) (hN : ∀ x, N x = x + U x)
    (u : V) : (∀ s : ↥N.ker, polar q ↑s u = 0) ↔ u ∈ N.range := by
  classical
  let θ : V →+ (↥N.ker →+ ZMod 2) := AddMonoidHom.mk'
    (fun v => (polarHom q hq v).comp N.ker.subtype) (by
      intro v v'
      ext s
      exact hq.polar_add_right _ _ _)
  have hθ : ∀ (v : V) (s : ↥N.ker), θ v s = polar q ↑s v := fun _ _ => rfl
  constructor
  · -- counting direction
    intro hu
    have hle : N.range ≤ θ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [AddMonoidHom.mem_ker]
      ext s
      rw [AddMonoidHom.zero_apply, hθ]
      exact polar_ker_range q U hq h2 hUq N hN ↑s (AddMonoidHom.mem_ker.mp s.2) x
    haveI : Finite (↥N.ker →+ ZMod 2) :=
      Finite.of_injective (fun f => (f : ↥N.ker → ZMod 2)) DFunLike.coe_injective
    haveI : Finite (↥θ.range →+ ZMod 2) :=
      Finite.of_injective (fun f => (f : ↥θ.range → ZMod 2)) DFunLike.coe_injective
    -- the range of `θ` is exponent 2
    have h2hom : ∀ f : ↥θ.range, f + f = 0 := by
      intro f
      refine Subtype.ext ?_
      ext s
      exact CharTwo.add_self_eq_zero _
    -- evaluation of the kernel against the range of `θ` is injective by nonsingularity
    let ev : ↥N.ker →+ (↥θ.range →+ ZMod 2) := AddMonoidHom.mk'
      (fun s => AddMonoidHom.mk' (fun f => (↑f : ↥N.ker →+ ZMod 2) s) (fun _ _ => rfl))
      (by
        intro s s'
        ext f
        exact map_add (↑f : ↥N.ker →+ ZMod 2) s s')
    have hev_inj : Function.Injective ev := by
      rw [injective_iff_map_eq_zero]
      intro s hsev
      have hall : ∀ v : V, polar q ↑s v = 0 := fun v =>
        congrArg (fun g => g ⟨θ v, ⟨v, rfl⟩⟩) hsev
      refine Subtype.ext ?_
      by_contra hs0
      obtain ⟨w, hw⟩ := hns ↑s hs0
      exact hw (hall w)
    -- cardinality bookkeeping
    haveI : Nonempty ↥θ.range := ⟨0⟩
    haveI : Nonempty ↥N.range := ⟨0⟩
    have c1 : Nat.card ↥N.ker ≤ Nat.card ↥θ.range :=
      (Nat.card_le_card_of_injective ev hev_inj).trans
        (card_addHom_zmod2 ↥θ.range h2hom).le
    have c2 := card_range_mul_card_ker θ
    have c3 := card_range_mul_card_ker N
    have hθkle : Nat.card ↥θ.ker ≤ Nat.card ↥N.range := by
      have h3 : Nat.card ↥θ.range * Nat.card ↥θ.ker
          ≤ Nat.card ↥θ.range * Nat.card ↥N.range := by
        rw [c2, ← c3, mul_comm (Nat.card ↥N.range)]
        exact Nat.mul_le_mul_right _ c1
      exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos
    -- conclude set equality and membership
    have heq : (θ.ker : Set V) = (N.range : Set V) := by
      refine (Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)).symm
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hθkle
    have hu' : u ∈ θ.ker := by
      rw [AddMonoidHom.mem_ker]
      ext s
      rw [AddMonoidHom.zero_apply, hθ]
      exact hu s
    have : u ∈ (N.range : Set V) := heq ▸ hu'
    exact this
  · rintro ⟨x, rfl⟩ s
    exact polar_ker_range q U hq h2 hUq N hN ↑s (AddMonoidHom.mem_ker.mp s.2) x

end Duality

/-! ## Wall's sign relation

Assembling the pieces: grouping the twisted double Gauss sum over the fibers of `N = 1 + U`
turns it into `#ker N ·` (the Wall count of the Wall form `ω(Nx, u) = B(x, u)` on `im N`),
whose monodromy is `U⁻¹`.  With `#im N = 2^k` this gives

  `g(q_U) · g(q) = #K · (−2)^k = (−1)^k · #V = (−1)^k · g(q)²`,

and cancelling `g(q) ≠ 0` yields **`g(q_U) = (−1)^k g(q)`** — the sign relation of Lemma 6.6. -/

section WallSign

variable {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2) (U : V ≃+ V)

omit [Finite V] in
/-- **Independence of `polar q x (N y)` on the fibre of `N`.** If `N x = N x'` then `x` and `x'`
pair identically against everything in `im N`; this is what lets the Wall form `ω` be defined on
`R = im N` via any chosen representative. -/
private theorem polar_indep_of_range (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hUq : ∀ v, q (U v) = q v) (N : V →+ V) (hN : ∀ x, N x = x + U x)
    {x x' : V} (hxx : N x = N x') (y : V) : polar q x (N y) = polar q x' (N y) := by
  have hz : N (x + x') = 0 := by
    rw [map_add, hxx]
    exact h2 _
  have h0 : polar q (x + x') (N y) = 0 := polar_ker_range q U hq h2 hUq N hN _ hz y
  rw [hq.polar_add_left] at h0
  have h1 := congrArg (· + polar q x' (N y)) h0
  simpa [add_assoc, CharTwo.add_self_eq_zero] using h1

omit [Finite V] in
/-- **The diagonal of the Wall form is `q`.** For the Wall form `ω t u = polar q (xrep t) u` on
`R = im N`, the value `ω t t` recovers `q ↑t`. -/
private theorem wallForm_diag (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hUq : ∀ v, q (U v) = q v) (N : V →+ V) (hN : ∀ x, N x = x + U x)
    (xrep : ↥N.range → V) (hxrep : ∀ t, N (xrep t) = ↑t)
    (ω : ↥N.range →+ ↥N.range →+ ZMod 2)
    (hω : ∀ t u : ↥N.range, ω t u = polar q (xrep t) ↑u) (t : ↥N.range) : ω t t = q ↑t := by
  rw [hω]
  conv_lhs => rw [← hxrep t]
  rw [hN, hq.polar_add_right, polar_self q hq h2, zero_add]
  rw [show (↑t : V) = xrep t + U (xrep t) from by rw [← hN, hxrep]]
  unfold polar
  rw [hUq]
  linear_combination CharTwo.add_self_eq_zero (q (xrep t))

omit [Finite V] in
/-- **The monodromy `MR = U⁻¹` on `R` is `2`-power-order.** From `U^[2^n] = id` we get
`MR^[2^n] = id`, using that `↑(MR t) = U.symm ↑t`. -/
private theorem monodromy_iterate_id (hU2 : ∃ n, (⇑U)^[2 ^ n] = id) (N : V →+ V)
    (MR : ↥N.range ≃+ ↥N.range) (hMRapp : ∀ t : ↥N.range, (↑(MR t) : V) = U.symm ↑t) :
    ∃ n' : ℕ, (⇑MR)^[2 ^ n'] = id := by
  obtain ⟨n, hn⟩ := hU2
  refine ⟨n, ?_⟩
  have hLI : Function.LeftInverse ⇑U.symm ⇑U := U.symm_apply_apply
  have hsymm : (⇑U.symm)^[2 ^ n] = id := by
    funext v
    have h := (hLI.iterate (2 ^ n)) v
    rw [hn] at h
    simpa using h
  have hiter : ∀ (i : ℕ) (t : ↥N.range), ↑((⇑MR)^[i] t) = (⇑U.symm)^[i] (t : V) := by
    intro i
    induction i with
    | zero => intro t; rfl
    | succ i ihi =>
      intro t
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hMRapp, ihi]
  funext t
  refine Subtype.ext ?_
  rw [hiter, hsymm]
  rfl

omit [Finite V] in
/-- **Wall's monodromy relation** `ω t u = ω u (MR t)`, where `MR = U⁻¹` on `R = im N`. This is the
`U`-equivariance of the polar form transported to the Wall form. -/
private theorem wallForm_monodromy_rel (hq : IsQuadraticFp2 q) (hUq : ∀ v, q (U v) = q v)
    (N : V →+ V) (hN : ∀ x, N x = x + U x) (xrep : ↥N.range → V)
    (hxrep : ∀ t, N (xrep t) = ↑t) (ω : ↥N.range →+ ↥N.range →+ ZMod 2)
    (hω : ∀ t u : ↥N.range, ω t u = polar q (xrep t) ↑u) (MR : ↥N.range ≃+ ↥N.range)
    (hMRapp : ∀ t : ↥N.range, (↑(MR t) : V) = U.symm ↑t) (t u : ↥N.range) :
    ω t u = ω u (MR t) := by
  rw [hω, hω, hMRapp]
  conv_lhs => rw [← hxrep u]
  rw [hN, hq.polar_add_right]
  rw [show polar q (xrep t) (U (xrep u)) = polar q (U.symm (xrep t)) (xrep u) from by
    conv_lhs => rw [show xrep t = U (U.symm (xrep t)) from (U.apply_symm_apply _).symm]
    exact polar_isometry_both q U hUq _ _]
  rw [← hq.polar_add_left, polar_comm]
  congr 1
  rw [show (↑t : V) = N (xrep t) from (hxrep t).symm, hN, map_add,
    AddEquiv.symm_apply_apply]
  exact add_comm _ _

omit [Finite V] in
/-- **Nondegeneracy of the Wall form.** If `ω t u = 0` for every `t`, then `u = 0`; this comes from
nonsingularity of `q` together with `polar_indep_of_range`. -/
private theorem wallForm_nondegenerate (hns : Nonsingular q) (N : V →+ V)
    (xrep : ↥N.range → V) (hxrep : ∀ t, N (xrep t) = ↑t)
    (hindep : ∀ (x x' : V), N x = N x' → ∀ y : V, polar q x (N y) = polar q x' (N y))
    (ω : ↥N.range →+ ↥N.range →+ ZMod 2)
    (hω : ∀ t u : ↥N.range, ω t u = polar q (xrep t) ↑u) (u : ↥N.range)
    (hu : ∀ t : ↥N.range, ω t u = 0) : u = 0 := by
  refine Subtype.ext ?_
  by_contra hu0
  obtain ⟨w, hw⟩ := hns ↑u hu0
  have hall : ∀ x : V, polar q x ↑u = 0 := by
    intro x
    have ht := hu ⟨N x, ⟨x, rfl⟩⟩
    rw [hω] at ht
    obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp u.2
    rw [← hy] at ht ⊢
    rw [hindep x (xrep ⟨N x, ⟨x, rfl⟩⟩) (by rw [hxrep]) y]
    exact ht
  exact hw ((polar_comm q ↑u w).trans (hall w))

/-- **The kernel character sum.** Summing `sign (polar q ↑s u)` over `s ∈ ker N` gives `#ker N` when
`u ∈ im N` (the perp of `ker N`) and `0` otherwise. -/
private theorem kernelCharSum [Fintype V] [DecidableEq V] (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (hUq : ∀ v, q (U v) = q v) (N : V →+ V)
    (hN : ∀ x, N x = x + U x) [Fintype ↥N.ker] (u : V) : (∑ s : ↥N.ker, sign (polar q ↑s u))
      = if u ∈ N.range then (Nat.card ↥N.ker : ℤ) else 0 := by
  by_cases hu : u ∈ N.range
  · rw [if_pos hu]
    have hz : ∀ s : ↥N.ker, polar q ↑s u = 0 :=
      fun s => (perp_ker_iff_mem_range q U hq h2 hns hUq N hN u).mpr hu s
    rw [show (∑ s : ↥N.ker, sign (polar q ↑s u)) = ∑ _s : ↥N.ker, 1 from
      Finset.sum_congr rfl fun s _ => by rw [hz s]; decide]
    rw [Finset.sum_const, Nat.card_eq_fintype_card, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg hu]
    have hex : ∃ s₀ : ↥N.ker, polar q ↑s₀ u ≠ 0 := by
      by_contra hcon
      exact hu ((perp_ker_iff_mem_range q U hq h2 hns hUq N hN u).mp
        fun s => not_not.mp (not_exists.mp hcon s))
    obtain ⟨s₀, hs₀⟩ := hex
    exact charSum_eq_zero ((polarHom q hq u).comp N.ker.subtype)
      ⟨s₀, zmod2_ne_zero_eq_one _ hs₀⟩

omit [Finite V] in
/-- **The twisted double sum.** The product `g(q_U) · g(q)` is the double sum of
`sign (q (N x) + q u + polar q x u)` over `x, u ∈ V`. -/
private theorem twistedDoubleSum [Fintype V] (hUq : ∀ v, q (U v) = q v) (N : V →+ V)
    (hN : ∀ x, N x = x + U x) : gaussSum (qDouble q ⇑U) * gaussSum q
      = ∑ x : V, ∑ u : V, sign (q (N x) + q u + polar q x u) := by
  unfold gaussSum
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft x) (fun y => sign (qDouble q ⇑U x) * sign (q y))]
  simp only [Equiv.coe_addLeft]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← sign_add]
  congr 1
  rw [qDouble_eq_add q U hUq, hN]
  unfold polar
  linear_combination -CharTwo.add_self_eq_zero (q u)

/-- **Wall's sign relation** (the last piece of Lemma 6.6, eq. (86)): for a nonsingular `q`
and a `2`-power-order isometry `U`, with `N = 1 + U` and `#im N = 2^k`,

  `g(q_U) = (−1)^k · g(q)`. -/
theorem gaussSum_qDouble [Fintype V] (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hns : Nonsingular q) (hUq : ∀ v, q (U v) = q v) (hU2 : ∃ n, (⇑U)^[2 ^ n] = id)
    (N : V →+ V) (hN : ∀ x, N x = x + U x) {k : ℕ} (hk : Nat.card ↥N.range = 2 ^ k) :
    gaussSum (qDouble q ⇑U) = (-1 : ℤ) ^ k * gaussSum q := by
  classical
  letI : Fintype ↥N.range := Fintype.ofFinite _
  letI : Fintype ↥N.ker := Fintype.ofFinite _
  haveI : Nonempty ↥N.ker := ⟨0⟩
  have h2R : ∀ t : ↥N.range, t + t = 0 := fun t => Subtype.ext (h2 (t : V))
  -- ### the Wall form `ω(Nx, u) = B(x, u)` on `R = im N`
  choose xrep hxrep using fun t : ↥N.range => AddMonoidHom.mem_range.mp t.2
  have hindep : ∀ (x x' : V), N x = N x' → ∀ y : V, polar q x (N y) = polar q x' (N y) :=
    fun x x' hxx y => polar_indep_of_range q U hq h2 hUq N hN hxx y
  let ω : ↥N.range →+ ↥N.range →+ ZMod 2 := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun u => polar q (xrep t) ↑u) (by
      intro u u'
      rw [AddSubgroup.coe_add, hq.polar_add_right]))
    (by
      intro t t'
      ext u
      show polar q (xrep (t + t')) ↑u = polar q (xrep t) ↑u + polar q (xrep t') ↑u
      obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp u.2
      rw [← hy, hindep (xrep (t + t')) (xrep t + xrep t')
        (by rw [hxrep, map_add, hxrep, hxrep, AddSubgroup.coe_add]) y, hq.polar_add_left])
  have hω : ∀ t u : ↥N.range, ω t u = polar q (xrep t) ↑u := fun _ _ => rfl
  -- the diagonal of the Wall form is `q`
  have hdiag : ∀ t : ↥N.range, ω t t = q ↑t :=
    fun t => wallForm_diag q U hq h2 hUq N hN xrep hxrep ω hω t
  -- ### the monodromy `U⁻¹` on `R`
  have hUrange : ∀ t : ↥N.range, U.symm ↑t ∈ N.range := by
    intro t
    obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp t.2
    refine ⟨U.symm y, ?_⟩
    rw [hN, AddEquiv.apply_symm_apply, ← hy, hN, map_add, AddEquiv.symm_apply_apply]
  let MR0 : ↥N.range →+ ↥N.range :=
    AddMonoidHom.mk' (fun t => ⟨U.symm ↑t, hUrange t⟩) (by
      intro t t'
      ext
      simp)
  have hMR0inj : Function.Injective MR0 := by
    intro t t' htt
    exact Subtype.ext (U.symm.injective (congrArg Subtype.val htt))
  let MR : ↥N.range ≃+ ↥N.range :=
    AddEquiv.ofBijective MR0 ⟨hMR0inj, Finite.injective_iff_surjective.mp hMR0inj⟩
  have hMRapp : ∀ t : ↥N.range, (↑(MR t) : V) = U.symm ↑t := fun _ => rfl
  have hMrel : ∀ t u : ↥N.range, ω t u = ω u (MR t) :=
    fun t u => wallForm_monodromy_rel q U hq hUq N hN xrep hxrep ω hω MR hMRapp t u
  have hMR2 : ∃ n' : ℕ, (⇑MR)^[2 ^ n'] = id := monodromy_iterate_id U hU2 N MR hMRapp
  -- ### nondegeneracy of the Wall form
  have hndR : ∀ u : ↥N.range, (∀ t : ↥N.range, ω t u = 0) → u = 0 :=
    fun u hu => wallForm_nondegenerate q hns N xrep hxrep hindep ω hω u hu
  -- ### the Wall count
  have hcount := wall_count h2R ω MR hMrel hMR2 hndR hk
  -- ### the fiber decomposition of the double Gauss sum
  let Ncor : V → ↥N.range := fun x => ⟨N x, ⟨x, rfl⟩⟩
  have hfibmem : ∀ (t : ↥N.range) (s : ↥N.ker), Ncor (xrep t + ↑s) = t := by
    intro t s
    refine Subtype.ext ?_
    show N (xrep t + ↑s) = ↑t
    rw [map_add, hxrep, AddMonoidHom.mem_ker.mp s.2, add_zero]
  have hfibmem' : ∀ (t : ↥N.range) (x : {x : V // Ncor x = t}), (↑x : V) + xrep t ∈ N.ker := by
    intro t x
    rw [AddMonoidHom.mem_ker, map_add, hxrep]
    rw [show N ↑x = ↑t from congrArg Subtype.val x.2]
    exact h2 _
  let fibEquiv : ∀ t : ↥N.range, ↥N.ker ≃ {x : V // Ncor x = t} := fun t =>
    { toFun := fun s => ⟨xrep t + ↑s, hfibmem t s⟩
      invFun := fun x => ⟨↑x + xrep t, hfibmem' t x⟩
      left_inv := by
        intro s
        refine Subtype.ext ?_
        show (xrep t + ↑s) + xrep t = ↑s
        rw [add_comm (xrep t) (↑s : V), add_assoc, h2, add_zero]
      right_inv := by
        intro x
        refine Subtype.ext ?_
        show xrep t + ((↑x : V) + xrep t) = ↑x
        rw [add_comm (↑x : V) (xrep t), ← add_assoc, h2, zero_add] }
  -- the kernel character sum: `#K` on the perp of the kernel (= the range), `0` off it
  have hχ : ∀ u : V, (∑ s : ↥N.ker, sign (polar q ↑s u))
      = if u ∈ N.range then (Nat.card ↥N.ker : ℤ) else 0 :=
    fun u => kernelCharSum q U hq h2 hns hUq N hN u
  -- the twisted double sum
  have hF1 : gaussSum (qDouble q ⇑U) * gaussSum q
      = ∑ x : V, ∑ u : V, sign (q (N x) + q u + polar q x u) :=
    twistedDoubleSum q U hUq N hN
  -- grouping over the fibers of `N`
  have hfiber : gaussSum (qDouble q ⇑U) * gaussSum q
      = (Nat.card ↥N.ker : ℤ)
        * ∑ t : ↥N.range, ∑ u : ↥N.range, sign (ω t t + ω u u + ω t u) := by
    rw [hF1, Finset.sum_comm]
    have hstep : ∀ u : V, (∑ x : V, sign (q (N x) + q u + polar q x u))
        = (∑ s : ↥N.ker, sign (polar q ↑s u))
          * ∑ t : ↥N.range, sign (q ↑t + q u + polar q (xrep t) u) := by
      intro u
      rw [← Fintype.sum_fiberwise Ncor (fun x => sign (q (N x) + q u + polar q x u))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Equiv.sum_comp (fibEquiv t) (fun x : {x : V // Ncor x = t} =>
        sign (q (N ↑x) + q u + polar q ↑x u)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      show sign (q (N (xrep t + ↑s)) + q u + polar q (xrep t + ↑s) u) = _
      rw [← sign_add]
      congr 1
      rw [show N (xrep t + ↑s) = ↑t from by
        rw [map_add, hxrep, AddMonoidHom.mem_ker.mp s.2, add_zero], hq.polar_add_left]
      ring
    rw [show (∑ u : V, ∑ x : V, sign (q (N x) + q u + polar q x u))
        = ∑ u : V, (∑ s : ↥N.ker, sign (polar q ↑s u))
          * ∑ t : ↥N.range, sign (q ↑t + q u + polar q (xrep t) u) from
      Finset.sum_congr rfl fun u _ => hstep u]
    rw [show (∑ u : V, (∑ s : ↥N.ker, sign (polar q ↑s u))
          * ∑ t : ↥N.range, sign (q ↑t + q u + polar q (xrep t) u))
        = ∑ u : V, (if u ∈ N.range then ((Nat.card ↥N.ker : ℤ)
            * ∑ t : ↥N.range, sign (q ↑t + q u + polar q (xrep t) u)) else 0) from
      Finset.sum_congr rfl fun u _ => by
        rw [hχ u]
        split_ifs with h
        · rfl
        · rw [zero_mul]]
    rw [← Finset.sum_filter, Finset.sum_subtype (p := (· ∈ N.range))
      (Finset.univ.filter (· ∈ N.range)) (fun x => by simp)]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
    rw [← hdiag t, ← hdiag u, ← hω t u]
  -- ### combine: `#K · (−2)^k = (−1)^k · #V = (−1)^k · g(q)²`, then cancel `g(q)`
  have hcards : (Nat.card ↥N.ker : ℤ) * 2 ^ k = (Fintype.card V : ℤ) := by
    have h := card_range_mul_card_ker N
    rw [hk, Nat.card_eq_fintype_card (α := V)] at h
    have h' : Nat.card ↥N.ker * 2 ^ k = Fintype.card V := by rw [mul_comm]; exact h
    exact_mod_cast h'
  have hsq := gaussSum_sq q hq hns
  have hne := gaussSum_ne_zero q hq hns
  have hmain : gaussSum (qDouble q ⇑U) * gaussSum q
      = ((-1 : ℤ) ^ k * gaussSum q) * gaussSum q := by
    rw [hfiber, hcount, show ((-2 : ℤ)) ^ k = (-1) ^ k * 2 ^ k from by
      rw [← neg_one_mul, mul_pow]]
    rw [show ((-1 : ℤ) ^ k * gaussSum q) * gaussSum q = (-1) ^ k * gaussSum q ^ 2 from by ring]
    rw [hsq]
    rw [show (Nat.card ↥N.ker : ℤ) * ((-1) ^ k * 2 ^ k)
        = (-1) ^ k * ((Nat.card ↥N.ker : ℤ) * 2 ^ k) from by ring, hcards]
  exact mul_right_cancel₀ hne hmain

end WallSign

end QuadraticFp2

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (86) = ⟦eq-relativeArf⟧
  * Lemma 6.6 = ⟦lem-wall⟧
-/
