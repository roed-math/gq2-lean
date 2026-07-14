import GQ2.DeepPart.Q0locLayer

/-!
# The Hermitian-line count  (paper Prop 6.18, unramified computation)

The final computation of the paper's Prop 6.18 (unramified case): on `D = 𝔽_{2^{2m}}` the
Hermitian trace form `x ↦ Tr(c·x^{2^m+1})` (`c` outside the fixed field `D₀ = 𝔽_{2^m}`,
so the `D₀`-level form `Tr_{D₀/𝔽₂}(a·N(x))` in absolute-trace clothing) has exactly
`1 + (2^m+1)(2^{m−1}−1) = 2^{2m−1} − 2^{m−1}` zeros — the minus-type count.  Everything is
finite-field counting: norm fibres are `ker`-cosets of size `2^m+1` (cyclic `gcd` count), and
the nonzero trace-kernel of the fixed field contributes `2^{m−1}−1`.

This file is part of the `GQ2.DeepPart` split (P-15f); see `GQ2/DeepPart.lean` for the overview.
-/

open scoped Classical

namespace GQ2.DeepPart

open GQ2 GQ2.ContCoh GQ2.Foundations

section HermitianCount

open GQ2.QuadraticFp2

variable {D : Type*} [Field D] [Fintype D]

/-- A field of order `2^{2m}` (`m ≥ 1`) has characteristic 2. -/
theorem ringChar_eq_two_of_card {m : ℕ} (_ : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) : ringChar D = 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card D (ringChar D)
  have h1 : ringChar D ∣ Fintype.card D := hn.symm ▸ dvd_pow_self _ n.2.ne'
  rw [hcard] at h1
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

/-- The absolute trace of `D = 𝔽_{2^{2m}}`, written as the Frobenius-power sum. -/
theorem algebraMap_trace_eq {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (z : D) :
    algebraMap (ZMod (ringChar D)) D (Algebra.trace (ZMod (ringChar D)) D z)
      = ∑ i ∈ Finset.range (2 * m), z ^ 2 ^ i := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : Fact (Nat.Prime (ringChar D)) := ⟨by rw [hchar]; exact Nat.prime_two⟩
  have hcK : Nat.card (ZMod (ringChar D)) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card, hchar]
  have hrank : Module.finrank (ZMod (ringChar D)) D = 2 * m := by
    have hc2 : Fintype.card (ZMod (ringChar D)) = 2 := by rw [ZMod.card, hchar]
    have hpow := Module.card_eq_pow_finrank (K := ZMod (ringChar D)) (V := D)
    rw [hc2, hcard] at hpow
    exact (Nat.pow_right_injective le_rfl hpow.symm)
  have hsum := FiniteField.algebraMap_trace_eq_sum_pow (ZMod (ringChar D)) D z
  rw [hrank, hcK] at hsum
  exact hsum

/-- Detecting trace-vanishing through the Frobenius-power sum. -/
theorem trace_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (z : D) :
    Algebra.trace (ZMod (ringChar D)) D z = 0
      ↔ ∑ i ∈ Finset.range (2 * m), z ^ 2 ^ i = 0 := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : Fact (Nat.Prime (ringChar D)) := ⟨by rw [hchar]; exact Nat.prime_two⟩
  rw [← (algebraMap (ZMod (ringChar D)) D).injective.eq_iff' (map_zero _),
    algebraMap_trace_eq hm hcard]

/-- **Frobenius-invariance of the trace**: `Tr(z²) = Tr(z)` (shift the Frobenius sum). -/
theorem trace_pow_two {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (z : D) :
    Algebra.trace (ZMod (ringChar D)) D (z ^ 2) = Algebra.trace (ZMod (ringChar D)) D z := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : Fact (Nat.Prime (ringChar D)) := ⟨by rw [hchar]; exact Nat.prime_two⟩
  apply (algebraMap (ZMod (ringChar D)) D).injective
  rw [algebraMap_trace_eq hm hcard, algebraMap_trace_eq hm hcard]
  have hpt : ∀ i, (z ^ 2) ^ 2 ^ i = z ^ 2 ^ (i + 1) := fun i => by rw [← pow_mul, ← pow_succ']
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  have h1 := Finset.sum_range_succ' (fun i => z ^ 2 ^ i) (2 * m)
  have h2 := Finset.sum_range_succ (fun i => z ^ 2 ^ i) (2 * m)
  have hf0 : z ^ 2 ^ 0 = z := by rw [pow_zero, pow_one]
  have hfn : z ^ 2 ^ (2 * m) = z := by
    rw [← hcard]
    exact FiniteField.pow_card z
  have hkey := h1.symm.trans h2
  rw [hf0, hfn] at hkey
  exact add_right_cancel hkey

/-- Iterated Frobenius-invariance: `Tr(z^{2^k}) = Tr(z)`. -/
theorem trace_pow_pow {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (k : ℕ) (z : D) :
    Algebra.trace (ZMod (ringChar D)) D (z ^ 2 ^ k) = Algebra.trace (ZMod (ringChar D)) D z := by
  induction k with
  | zero => rw [pow_zero, pow_one]
  | succ n ih =>
    have hz : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [hz, trace_pow_two hm hcard, ih]

/-- **The trace vanishes on the fixed field**: `Tr(y) = 0` whenever `y^{2^m} = y` (the
Frobenius-sum doubles up in characteristic 2). -/
theorem trace_eq_zero_of_frobenius_fixed {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) [Algebra (ZMod (ringChar D)) D]
    {y : D} (hy : y ^ 2 ^ m = y) :
    Algebra.trace (ZMod (ringChar D)) D y = 0 := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  rw [trace_eq_zero_iff hm hcard]
  have hsplit : ∑ i ∈ Finset.range (2 * m), y ^ 2 ^ i
      = (∑ i ∈ Finset.range m, y ^ 2 ^ i) + ∑ i ∈ Finset.range m, y ^ 2 ^ (m + i) := by
    rw [two_mul]
    exact Finset.sum_range_add (fun i => y ^ 2 ^ i) m m
  have hshift : ∀ i, y ^ 2 ^ (m + i) = y ^ 2 ^ i := by
    intro i
    rw [pow_add, pow_mul, hy]
  rw [hsplit, Finset.sum_congr rfl (fun i _ => hshift i)]
  exact CharTwo.add_self_eq_zero _

/-- **Solution count of `y^n = y`** via the unit split: `1 + #{u : Dˣ | u^{n−1} = 1}`. -/
theorem card_pow_fixed (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {y : D // y ^ n = y} = 1 + Nat.card {u : Dˣ // u ^ (n - 1) = 1} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  have hzero : (0 : D) ∈ Finset.univ.filter (fun y : D => y ^ n = y) := by
    simp [zero_pow (by omega : n ≠ 0)]
  have hsplit : Finset.univ.filter (fun y : D => y ^ n = y)
      = insert (0 : D) ((Finset.univ.filter (fun y : D => y ^ n = y)).erase 0) := by
    rw [Finset.insert_erase hzero]
  rw [hsplit, Finset.card_insert_of_notMem (Finset.notMem_erase 0 _), add_comm]
  congr 1
  symm
  refine Finset.card_bij (fun u _ => (↑u : D)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨u.ne_zero, Finset.mem_univ _, ?_⟩
    have : (↑(u ^ (n - 1)) : D) = 1 := by rw [hu.2]; rfl
    rw [Units.val_pow_eq_pow_val] at this
    calc (↑u : D) ^ n = (↑u : D) ^ (n - 1) * ↑u := by
          rw [← pow_succ]
          congr 1
          omega
      _ = ↑u := by rw [this, one_mul]
  · intro u _ v _ huv
    exact Units.ext huv
  · intro y hy
    rw [Finset.mem_erase, Finset.mem_filter] at hy
    obtain ⟨hy0, _, hyn⟩ := hy
    refine ⟨Units.mk0 y hy0, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have hstep : y ^ (n - 1) * y = 1 * y := by
      rw [one_mul, ← pow_succ]
      rw [show n - 1 + 1 = n from by omega]
      exact hyn
    exact mul_right_cancel₀ hy0 hstep

/-- The Frobenius^m-fixed subfield `𝔽_{2^m} ⊆ D`, as an additive subgroup. -/
def frobFixed (D : Type*) [Field D] [CharP D 2] (m : ℕ) : AddSubgroup D where
  carrier := {y : D | y ^ 2 ^ m = y}
  zero_mem' := by
    show (0 : D) ^ 2 ^ m = 0
    exact zero_pow (Nat.pos_of_neZero _).ne'
  add_mem' := fun {a b} ha hb => by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    show (a + b) ^ 2 ^ m = a + b
    rw [add_pow_char_pow, ha, hb]
  neg_mem' := fun {a} ha => by
    show (-a) ^ 2 ^ m = -a
    rw [CharTwo.neg_eq, ha]

omit [Fintype D] in
@[simp] theorem mem_frobFixed [CharP D 2] (m : ℕ) (y : D) :
    y ∈ frobFixed D m ↔ y ^ 2 ^ m = y := Iff.rfl

/-- `#𝔽_{2^m} = 2^m` inside `D = 𝔽_{2^{2m}}` (cyclic `gcd` count on the units). -/
theorem card_frobFixed {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [CharP D 2] : Nat.card ↥(frobFixed D m) = 2 ^ m := by
  classical
  have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h1 : Nat.card ↥(frobFixed D m) = Nat.card {y : D // y ^ 2 ^ m = y} := rfl
  rw [h1, card_pow_fixed (2 ^ m) (by simpa using Nat.pow_le_pow_right two_pos hm)]
  -- units with `u^{2^m − 1} = 1` = kernel of the power map, size `gcd`
  have hker : Nat.card {u : Dˣ // u ^ (2 ^ m - 1) = 1}
      = Nat.card ↥((powMonoidHom (2 ^ m - 1) : Dˣ →* Dˣ).ker) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun u => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply])
  have hcardU : Nat.card Dˣ = 2 ^ (2 * m) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]
  have hdvd : (2 ^ m - 1) ∣ (2 ^ (2 * m) - 1) := by
    simpa [← pow_mul, mul_comm] using Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 2
  rw [hker, IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right hdvd]
  omega


/-- **Trace representation of `𝔽₂`-functionals**: every additive functional `D →+ ZMod 2` is
`x ↦ Tr(w·x)` for some `w` (the trace pairing is perfect, by nondegeneracy + counting). -/
theorem exists_trace_rep {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (e2 : ZMod (ringChar D) ≃+ ZMod 2) (f : D →+ ZMod 2) :
    ∃ w : D, ∀ x : D, f x = e2 (Algebra.trace (ZMod (ringChar D)) D (w * x)) := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  have h2D : ∀ a : D, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  haveI : Finite (D →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : D → ZMod 2)) DFunLike.coe_injective
  haveI : Fintype (D →+ ZMod 2) := Fintype.ofFinite _
  set Φ : D → (D →+ ZMod 2) := fun w => AddMonoidHom.mk'
    (fun x => e2 (Algebra.trace (ZMod (ringChar D)) D (w * x)))
    (fun x x' => by rw [mul_add, map_add, map_add]) with hΦ
  have hinj : Function.Injective Φ := by
    intro w₁ w₂ hw
    by_contra hne
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate D (sub_ne_zero.mpr hne)
    apply hb
    have hpt := DFunLike.congr_fun hw b
    have hpt' : e2 (Algebra.trace (ZMod (ringChar D)) D (w₁ * b))
        = e2 (Algebra.trace (ZMod (ringChar D)) D (w₂ * b)) := hpt
    have htr : Algebra.trace (ZMod (ringChar D)) D (w₁ * b)
        = Algebra.trace (ZMod (ringChar D)) D (w₂ * b) := e2.injective hpt'
    rw [sub_mul, map_sub, htr, sub_self]
  haveI : Fintype D := Fintype.ofFinite D
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_addHom_zmod2 D h2D]
  obtain ⟨w, hw⟩ := hbij.2 f
  exact ⟨w, fun x => by rw [← hw]; rfl⟩

/-- **Artin–Schreier surjectivity onto the fixed field**: every `y` with `y^{2^m} = y` is
`c + c^{2^m}` for some `c` (the map `c ↦ c + c^{2^m}` has kernel and image the fixed field). -/
theorem exists_add_pow_eq {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    {y : D} (hy : y ^ 2 ^ m = y) : ∃ c : D, c + c ^ 2 ^ m = y := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : D →+ D := AddMonoidHom.mk' (fun c => c + c ^ 2 ^ m)
    (fun a b => by rw [add_pow_char_pow]; abel) with hφ
  -- kernel = fixed field
  have hker : φ.ker = frobFixed D m := by
    ext c
    rw [AddMonoidHom.mem_ker, mem_frobFixed]
    show c + c ^ 2 ^ m = 0 ↔ c ^ 2 ^ m = c
    rw [CharTwo.add_eq_zero]
    exact eq_comm
  -- range ⊆ fixed field
  have hrangele : φ.range ≤ frobFixed D m := by
    rintro _ ⟨c, rfl⟩
    rw [mem_frobFixed]
    show (c + c ^ 2 ^ m) ^ 2 ^ m = c + c ^ 2 ^ m
    have hcc : (c ^ 2 ^ m) ^ 2 ^ m = c := by
      rw [← pow_mul, show (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) from by rw [two_mul, pow_add],
        ← hcard]
      exact FiniteField.pow_card c
    rw [add_pow_char_pow, hcc, add_comm]
  -- equal cardinalities force equality
  have hrn : Nat.card ↥φ.range * Nat.card ↥φ.ker = Nat.card D := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
    exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm
  have hkercard : Nat.card ↥φ.ker = 2 ^ m := by rw [hker]; exact card_frobFixed hm hcard
  have hrangecard : Nat.card ↥φ.range = 2 ^ m := by
    have hD : Nat.card D = 2 ^ m * 2 ^ m := by
      rw [Nat.card_eq_fintype_card, hcard, two_mul, pow_add]
    rw [hkercard, hD] at hrn
    have hpos : 0 < 2 ^ m := Nat.pos_of_neZero _
    exact Nat.eq_of_mul_eq_mul_right hpos hrn
  have heq : (φ.range : Set D) = (frobFixed D m : Set D) := by
    refine Set.eq_of_subset_of_ncard_le (fun x hx => hrangele hx) ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    show Nat.card ↥(frobFixed D m) ≤ Nat.card ↥φ.range
    rw [card_frobFixed hm hcard, hrangecard]
  exact (heq ▸ hy : y ∈ (φ.range : Set D))

/-- `2^s − 1 ∣ 2^t − 1` forces `s ∣ t` (Euclidean division on the exponents). -/
theorem dvd_of_two_pow_sub_one_dvd {s t : ℕ} (hs : 1 ≤ s)
    (h : (2 ^ s - 1) ∣ (2 ^ t - 1)) : s ∣ t := by
  by_contra hnd
  have hr0 : t % s ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hrlt : t % s < s := Nat.mod_lt _ (by omega)
  -- decompose `2^t − 1`
  have ht : s * (t / s) + t % s = t := Nat.div_add_mod t s
  have hdvd1 : (2 ^ s - 1) ∣ (2 ^ (s * (t / s)) - 1) := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ s) 1 (t / s)
    rwa [one_pow, ← pow_mul] at this
  have hdecomp : 2 ^ t - 1
      = 2 ^ (t % s) * (2 ^ (s * (t / s)) - 1) + (2 ^ (t % s) - 1) := by
    have hprod : 2 ^ t = 2 ^ (s * (t / s)) * 2 ^ (t % s) := by
      rw [← pow_add, ht]
    have hA : 1 ≤ 2 ^ (s * (t / s)) := Nat.one_le_two_pow
    have hB : 1 ≤ 2 ^ (t % s) := Nat.one_le_two_pow
    generalize hA' : 2 ^ (s * (t / s)) = A at *
    generalize hB' : 2 ^ (t % s) = B at *
    generalize hC' : 2 ^ t = C at *
    have hmul : B * (A - 1) = B * A - B := by
      rw [Nat.mul_sub, mul_one]
    have hBA : B * A = C := by rw [hprod]; ring
    have hCB : B ≤ C := by
      rw [hprod]
      exact Nat.le_mul_of_pos_left _ (by omega)
    rw [hmul, hBA]
    omega
  have hdvd2 : (2 ^ s - 1) ∣ (2 ^ (t % s) - 1) := by
    have hX : (2 ^ s - 1) ∣ 2 ^ (t % s) * (2 ^ (s * (t / s)) - 1) :=
      hdvd1.mul_left _
    have := Nat.dvd_sub h hX
    rwa [hdecomp, Nat.add_sub_cancel_left] at this
  have hlt : 2 ^ (t % s) - 1 < 2 ^ s - 1 := by
    have h1 := Nat.pow_lt_pow_right (a := 2) one_lt_two hrlt
    have h2 : 1 ≤ 2 ^ (t % s) := Nat.one_le_two_pow
    omega
  have hpos : 0 < 2 ^ (t % s) - 1 := by
    have h2r : 2 ≤ 2 ^ (t % s) := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (t % s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact absurd (Nat.le_of_dvd hpos hdvd2) (Nat.not_le.mpr hlt)

/-- **A subring containing the norm-one circle is everything**: a subring of `D = 𝔽_{2^{2m}}`
containing all `2^m+1` norm-one units has 2-power order `> 2^m` whose predecessor divides
`2^{2m}−1` (Lagrange on its unit group), forcing order `2^{2m}`. -/
theorem subring_eq_top_of_normOne_le {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) (S : Subring D)
    (hU : ∀ u : Dˣ, u ^ (2 ^ m + 1) = 1 → (↑u : D) ∈ S) : S = ⊤ := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  have h2S : ∀ x : ↥S, x + x = 0 := fun x => Subtype.ext (CharTwo.add_self_eq_zero _)
  obtain ⟨s, hs⟩ := card_eq_two_pow_of_exp_two h2S
  -- the `2^m+2` elements `{0} ∪ U` inject into `S`
  have hUcount : Nat.card {u : Dˣ // u ^ (2 ^ m + 1) = 1} = 2 ^ m + 1 := by
    have he : Nat.card {u : Dˣ // u ^ (2 ^ m + 1) = 1}
        = Nat.card ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => by
        rw [MonoidHom.mem_ker, powMonoidHom_apply])
    have hdvd : (2 ^ m + 1) ∣ (2 ^ (2 * m) - 1) := by
      refine ⟨2 ^ m - 1, ?_⟩
      rw [show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 from by rw [← pow_mul, mul_comm]]
      simpa using Nat.sq_sub_sq (2 ^ m) 1
    rw [he, IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Fintype.card_units,
      hcard, Nat.gcd_eq_right hdvd]
  have hinj : Function.Injective
      (fun o : Option {u : Dˣ // u ^ (2 ^ m + 1) = 1} =>
        (o.elim (⟨0, S.zero_mem⟩ : ↥S) (fun u => ⟨↑u.1, hU u.1 u.2⟩) : ↥S)) := by
    intro o₁ o₂ ho
    match o₁, o₂ with
    | none, none => rfl
    | none, some u =>
      exact absurd (congrArg Subtype.val ho).symm u.1.ne_zero
    | some u, none =>
      exact absurd (congrArg Subtype.val ho) u.1.ne_zero
    | some u, some v =>
      have : (↑u.1 : D) = ↑v.1 := congrArg Subtype.val ho
      rw [Option.some.injEq]
      exact Subtype.ext (Units.ext this)
  have hle : 2 ^ m + 2 ≤ 2 ^ s := by
    have hcardO := Nat.card_le_card_of_injective _ hinj
    haveI : Fintype {u : Dˣ // u ^ (2 ^ m + 1) = 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option,
      ← Nat.card_eq_fintype_card, hUcount, hs] at hcardO
    omega
  -- the unit group of `S`, Lagrange
  set T : Subgroup Dˣ :=
    { carrier := {u : Dˣ | (↑u : D) ∈ S}
      one_mem' := by
        show ((1 : Dˣ) : D) ∈ S
        rw [Units.val_one]
        exact S.one_mem
      mul_mem' := fun {a b} ha hb => by
        show ((a * b : Dˣ) : D) ∈ S
        rw [Units.val_mul]
        exact S.mul_mem ha hb
      inv_mem' := fun {u} hu => by
        show ((u⁻¹ : Dˣ) : D) ∈ S
        have hord : 0 < orderOf u := orderOf_pos u
        have h1 : u * u ^ (orderOf u - 1) = 1 := by
          rw [← pow_succ', show orderOf u - 1 + 1 = orderOf u from by omega,
            pow_orderOf_eq_one]
        rw [inv_eq_of_mul_eq_one_right h1, Units.val_pow_eq_pow_val]
        exact pow_mem hu _ } with hT
  have hTcard : Nat.card ↥T + 1 = 2 ^ s := by
    rw [← hs]
    have e : Option ↥T ≃ ↥S :=
      { toFun := fun o => o.elim ⟨0, S.zero_mem⟩ (fun u => ⟨↑u.1, u.2⟩)
        invFun := fun x => if hx : (x : D) = 0 then none
          else some ⟨Units.mk0 (x : D) hx, by
            show ((Units.mk0 (x : D) hx : Dˣ) : D) ∈ S
            rw [Units.val_mk0]
            exact x.2⟩
        left_inv := fun o => by
          match o with
          | none => simp
          | some u =>
            have hne : ((⟨↑u.1, u.2⟩ : ↥S) : D) ≠ 0 := u.1.ne_zero
            simp only [Option.elim_some]
            rw [dif_neg hne]
            congr 1
            exact Subtype.ext (Units.ext rfl)
        right_inv := fun x => by
          dsimp only
          by_cases hx : (x : D) = 0
          · rw [dif_pos hx]
            exact Subtype.ext hx.symm
          · rw [dif_neg hx]
            exact Subtype.ext rfl }
    haveI : Fintype ↥T := Fintype.ofFinite _
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card (α := Option _), Fintype.card_option,
      ← Nat.card_eq_fintype_card]
  have hTdvd : Nat.card ↥T ∣ 2 ^ (2 * m) - 1 := by
    have := Subgroup.card_subgroup_dvd_card T
    rwa [Nat.card_eq_fintype_card (α := Dˣ), Fintype.card_units, hcard] at this
  -- pinch: `s ∣ 2m` and `s > m` force `s = 2m`
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hz : s = 0 := by omega
    rw [hz, pow_zero] at hle
    have := Nat.one_le_two_pow (n := m)
    omega
  have hsdvd : s ∣ 2 * m := by
    apply dvd_of_two_pow_sub_one_dvd hs1
    have : Nat.card ↥T = 2 ^ s - 1 := by omega
    rwa [← this]
  have hsm : m < s := by
    have h1 : 2 ^ m < 2 ^ s := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hs2m : s = 2 * m := by
    obtain ⟨k, hk⟩ := hsdvd
    match k with
    | 0 => omega
    | 1 => omega
    | (k + 2) =>
      have hexp : s * (k + 2) = s * k + 2 * s := by ring
      omega
  -- cardinality forces `S = ⊤`
  have hScard : Nat.card ↥S = Nat.card D := by
    rw [hs, hs2m, Nat.card_eq_fintype_card, hcard]
  have hcoe : (S : Set D) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
    exact le_of_eq hScard.symm
  exact SetLike.ext' (by rw [hcoe]; rfl)

/-- Fibres of a group hom over range points have the size of the kernel. -/
theorem card_filter_eq_of_mem_range {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Group H] [DecidableEq H] (f : G →* H) {y : H} (hy : y ∈ f.range) :
    (Finset.univ.filter (fun u : G => f u = y)).card
      = (Finset.univ.filter (fun u : G => u ∈ f.ker)).card := by
  obtain ⟨u₀, rfl⟩ := hy
  refine Finset.card_bij (fun v _ => u₀⁻¹ * v) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hv.2, inv_mul_cancel]
  · intro v _ w _ hvw
    exact mul_left_cancel hvw
  · intro k hk
    rw [Finset.mem_filter, MonoidHom.mem_ker] at hk
    refine ⟨u₀ * k, ?_, by group⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [map_mul, hk.2, mul_one]⟩


/-- **Lemma 6.7 (invariant quadratic forms on a Hermitian line), existence form**: every
nonsingular quadratic form on `D = 𝔽_{2^{2m}}` invariant under the norm-one circle
`U = {u : u^{2^m+1} = 1}` is the Hermitian trace form of some `c` outside the fixed field.
(The adjoint identity holds on a subring containing `U`, hence everywhere; the polar form is
then trace-represented with Frobenius-fixed coefficient, an Artin–Schreier preimage matches the
polars, and the additive `U`-invariant difference vanishes.) -/
theorem hermitian_form_eq_trace_form {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) [Algebra (ZMod (ringChar D)) D]
    (e2 : ZMod (ringChar D) ≃+ ZMod 2)
    (Q : D → ZMod 2) (hQ : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (hU : ∀ u : Dˣ, u ^ (2 ^ m + 1) = 1 → ∀ x : D, Q (↑u * x) = Q x) :
    ∃ c : D, c ^ 2 ^ m ≠ c ∧
      ∀ x : D, Q x = e2 (Algebra.trace (ZMod (ringChar D)) D (c * x ^ (2 ^ m + 1))) := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (ZMod (ringChar D)) 2 := hchar ▸ ZMod.charP (ringChar D)
  have hyq2 : ∀ y : D, (y ^ 2 ^ m) ^ 2 ^ m = y := fun y => by
    rw [← pow_mul, show (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) from by rw [two_mul, pow_add],
      ← hcard]
    exact FiniteField.pow_card y
  have hpz_left : ∀ y : D, polar Q 0 y = 0 := fun y => by
    unfold GQ2.QuadraticFp2.polar
    rw [zero_add, hQ.map_zero, add_zero]
    exact CharTwo.add_self_eq_zero _
  have hpz_right : ∀ x : D, polar Q x 0 = 0 := fun x => by
    unfold GQ2.QuadraticFp2.polar
    rw [add_zero, hQ.map_zero, add_zero]
    exact CharTwo.add_self_eq_zero _
  -- the polar form is `U`-invariant
  have hUB : ∀ (u : Dˣ), u ^ (2 ^ m + 1) = 1 → ∀ x y : D,
      polar Q (↑u * x) (↑u * y) = polar Q x y := by
    intro u hu x y
    unfold GQ2.QuadraticFp2.polar
    rw [← mul_add, hU u hu, hU u hu, hU u hu]
  -- the adjoint identity holds on a subring containing `U`, hence everywhere
  set S : Subring D :=
    { carrier := {d : D | ∀ x y : D, polar Q (d * x) y = polar Q x (d ^ 2 ^ m * y)}
      zero_mem' := fun x y => by
        rw [zero_mul, zero_pow (Nat.pos_of_neZero _).ne', zero_mul, hpz_left, hpz_right]
      one_mem' := fun x y => by rw [one_mul, one_pow, one_mul]
      add_mem' := fun {a b} ha hb x y => by
        rw [add_mul, hQ.polar_add_left, ha, hb, add_pow_char_pow, add_mul,
          ← hQ.polar_add_right]
      mul_mem' := fun {a b} ha hb x y => by
        rw [show a * b * x = a * (b * x) from by ring, ha, hb,
          show b ^ 2 ^ m * (a ^ 2 ^ m * y) = (a * b) ^ 2 ^ m * y from by
            rw [mul_pow]; ring]
      neg_mem' := fun {a} ha => by
        intro x y
        rw [CharTwo.neg_eq]
        exact ha x y } with hS
  have hStop : S = ⊤ := by
    apply subring_eq_top_of_normOne_le hm hcard
    intro u hu x y
    have hval : (↑u : D) * ((↑u : D) ^ 2 ^ m * y) = y := by
      rw [← mul_assoc, ← pow_succ', ← Units.val_pow_eq_pow_val, hu, Units.val_one, one_mul]
    calc polar Q (↑u * x) y
        = polar Q (↑u * x) (↑u * ((↑u : D) ^ 2 ^ m * y)) := by rw [hval]
      _ = polar Q x ((↑u : D) ^ 2 ^ m * y) := hUB u hu x _
  have hadj : ∀ d x y : D, polar Q (d * x) y = polar Q x (d ^ 2 ^ m * y) := by
    intro d x y
    have hd : d ∈ S := hStop ▸ Subring.mem_top d
    exact hd x y
  -- represent the polar form through the trace
  set ℓ : D →+ ZMod 2 := AddMonoidHom.mk' (fun y => polar Q 1 y)
    (fun y y' => hQ.polar_add_right 1 y y') with hℓ
  obtain ⟨c₀, hc₀⟩ := exists_trace_rep hm hcard e2 ℓ
  have hBrep : ∀ x y : D, polar Q x y
      = e2 (Algebra.trace (ZMod (ringChar D)) D (c₀ * (x ^ 2 ^ m * y))) := by
    intro x y
    have h1 : polar Q (x * 1) y = polar Q 1 (x ^ 2 ^ m * y) := hadj x 1 y
    rw [mul_one] at h1
    rw [h1]
    exact hc₀ _
  -- the coefficient is Frobenius-fixed (symmetry of the polar form)
  have hc₀fix : c₀ ^ 2 ^ m = c₀ := by
    have hsymTr : ∀ y : D, Algebra.trace (ZMod (ringChar D)) D (c₀ * y)
        = Algebra.trace (ZMod (ringChar D)) D (c₀ ^ 2 ^ m * y) := by
      intro y
      have h1 : polar Q 1 y = polar Q y 1 := polar_comm Q 1 y
      have h2 := hBrep 1 y
      have h3 := hBrep y 1
      rw [one_pow, one_mul] at h2
      rw [mul_one] at h3
      have h4 : Algebra.trace (ZMod (ringChar D)) D (c₀ * y ^ 2 ^ m)
          = Algebra.trace (ZMod (ringChar D)) D (c₀ ^ 2 ^ m * y) := by
        have h5 := trace_pow_pow hm hcard m (c₀ * y ^ 2 ^ m)
        rw [mul_pow, hyq2 y] at h5
        exact h5.symm
      have h6 : Algebra.trace (ZMod (ringChar D)) D (c₀ * y)
          = Algebra.trace (ZMod (ringChar D)) D (c₀ * y ^ 2 ^ m) :=
        e2.injective (h2.symm.trans (h1.trans h3))
      rw [h6, h4]
    by_contra hne
    have hsumne : c₀ + c₀ ^ 2 ^ m ≠ 0 := fun h0 => hne (CharTwo.add_eq_zero.mp h0).symm
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate D hsumne
    apply hb
    rw [add_mul, map_add, hsymTr b]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨c, hc⟩ := exists_add_pow_eq hm hcard hc₀fix
  set Qc : D → ZMod 2 :=
    fun x => e2 (Algebra.trace (ZMod (ringChar D)) D (c * x ^ (2 ^ m + 1))) with hQcdef
  -- the trace form has the same polar form
  have hQc_polar : ∀ x y : D, polar Qc x y = polar Q x y := by
    intro x y
    rw [hBrep x y]
    show e2 (Algebra.trace (ZMod (ringChar D)) D (c * (x + y) ^ (2 ^ m + 1)))
        + e2 (Algebra.trace (ZMod (ringChar D)) D (c * x ^ (2 ^ m + 1)))
        + e2 (Algebra.trace (ZMod (ringChar D)) D (c * y ^ (2 ^ m + 1)))
        = e2 (Algebra.trace (ZMod (ringChar D)) D (c₀ * (x ^ 2 ^ m * y)))
    rw [← map_add, ← map_add, ← map_add, ← map_add]
    congr 1
    have hexp : c * (x + y) ^ (2 ^ m + 1) + c * x ^ (2 ^ m + 1) + c * y ^ (2 ^ m + 1)
        = c * (x ^ 2 ^ m * y) + c * (x * y ^ 2 ^ m) := by
      have hfr : (x + y) ^ 2 ^ m = x ^ 2 ^ m + y ^ 2 ^ m := add_pow_char_pow x y 2 m
      rw [pow_succ, hfr]
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    rw [hexp, map_add]
    have hswap : Algebra.trace (ZMod (ringChar D)) D (c * (x * y ^ 2 ^ m))
        = Algebra.trace (ZMod (ringChar D)) D (c ^ 2 ^ m * (x ^ 2 ^ m * y)) := by
      have h5 := trace_pow_pow hm hcard m (c * (x * y ^ 2 ^ m))
      rw [mul_pow, mul_pow, hyq2 y] at h5
      exact h5.symm
    rw [hswap, ← map_add, show c * (x ^ 2 ^ m * y) + c ^ 2 ^ m * (x ^ 2 ^ m * y)
        = (c + c ^ 2 ^ m) * (x ^ 2 ^ m * y) from by ring, hc]
  -- the difference is an additive `U`-invariant functional, hence zero
  have hRadd : ∀ x y : D, Q (x + y) + Qc (x + y) = (Q x + Qc x) + (Q y + Qc y) := by
    intro x y
    have h1 : polar Q x y = polar Qc x y := (hQc_polar x y).symm
    unfold GQ2.QuadraticFp2.polar at h1
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1
  set R : D →+ ZMod 2 := AddMonoidHom.mk' (fun x => Q x + Qc x) hRadd with hR
  have hQcU : ∀ (u : Dˣ), u ^ (2 ^ m + 1) = 1 → ∀ x : D, Qc (↑u * x) = Qc x := by
    intro u hu x
    show e2 (Algebra.trace (ZMod (ringChar D)) D (c * (↑u * x) ^ (2 ^ m + 1))) = _
    rw [mul_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, one_mul]
  obtain ⟨w, hw⟩ := exists_trace_rep hm hcard e2 R
  have hkercard : Nat.card ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker) = 2 ^ m + 1 := by
    have hdvd : (2 ^ m + 1) ∣ (2 ^ (2 * m) - 1) := by
      refine ⟨2 ^ m - 1, ?_⟩
      rw [show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 from by rw [← pow_mul, mul_comm]]
      simpa using Nat.sq_sub_sq (2 ^ m) 1
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Fintype.card_units,
      hcard, Nat.gcd_eq_right hdvd]
  have hkerne : Nontrivial ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hkercard]
    have := Nat.one_le_two_pow (n := m)
    omega
  obtain ⟨u₀, hu₀ne⟩ := exists_ne (1 : ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker))
  have hu₀pow : (u₀ : Dˣ) ^ (2 ^ m + 1) = 1 := by
    have := u₀.2
    rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this
  have hu₀ne1 : (u₀ : Dˣ) ≠ 1 := by
    intro h
    exact hu₀ne (Subtype.ext h)
  have hw0 : w = 0 := by
    by_contra hwne
    have huvne : ((u₀ : Dˣ) : D) + 1 ≠ 0 := fun h0 =>
      hu₀ne1 (Units.ext (by rw [CharTwo.add_eq_zero.mp h0, Units.val_one]))
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate D
      (mul_ne_zero hwne huvne)
    apply hb
    have h1 : R ((↑(u₀ : Dˣ) : D) * b) = R b := by
      show Q _ + Qc _ = Q b + Qc b
      rw [hU (u₀ : Dˣ) hu₀pow, hQcU (u₀ : Dˣ) hu₀pow]
    rw [hw, hw] at h1
    have h2 : Algebra.trace (ZMod (ringChar D)) D (w * ((↑(u₀ : Dˣ) : D) * b))
        = Algebra.trace (ZMod (ringChar D)) D (w * b) := e2.injective h1
    rw [show w * ((↑(u₀ : Dˣ) : D) + 1) * b
        = w * ((↑(u₀ : Dˣ) : D) * b) + w * b from by ring, map_add, h2]
    exact CharTwo.add_self_eq_zero _
  have hQeq : ∀ x : D, Q x = Qc x := by
    intro x
    have h1 : Q x + Qc x = 0 := by
      have := hw x
      rwa [hw0, zero_mul, map_zero, map_zero] at this
    exact CharTwo.add_eq_zero.mp h1
  have hcne : c ^ 2 ^ m ≠ c := by
    intro hfix
    have hc₀0 : c₀ = 0 := by
      rw [← hc, hfix]
      exact CharTwo.add_self_eq_zero c
    haveI : Nontrivial D := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hcard]
      have := Nat.one_le_two_pow (n := 2 * m)
      have h4 : (2 : ℕ) ^ 1 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨v, hv⟩ := exists_ne (0 : D)
    obtain ⟨y, hy⟩ := hns v hv
    apply hy
    rw [show polar Q v y = e2 (Algebra.trace (ZMod (ringChar D)) D
        (c₀ * (v ^ 2 ^ m * y))) from hBrep v y, hc₀0, zero_mul, map_zero, map_zero]
  exact ⟨c, hcne, hQeq⟩


end HermitianCount
end GQ2.DeepPart
