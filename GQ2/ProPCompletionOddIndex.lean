/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.ProPCompletionFunctor
import GQ2.ZtwoPowering

/-!
# Odd-index subgroups and pro-2 completion

For a subgroup `H` of a commutative group `A`, suppose that `a ^ m ∈ H` for every `a`, where
`m` is odd.  Then inclusion induces an equivalence of pro-2 completions.

The inverse is explicit.  Since `m` is a unit of `ℤ₂`, send `a : A` to the unique `m`-th root
in `H^(2)` of the canonical class of `a ^ m`.  This formulation isolates the exact algebraic
content of the familiar statement that a finite odd-index subgroup has the same pro-2
completion as its ambient abelian group.
-/

namespace GQ2

noncomputable section

/-- `ℤ₂`-powering distributes over the base whenever multiplication is pointwise commutative.
This variant avoids replacing a pre-existing `Group` instance by a synthetic `CommGroup`
instance, which is useful for bundled profinite groups. -/
lemma zpowZtwo_mul_base_of_mul_comm
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (hcomm : ∀ x y : P, x * y = y * x)
    (x y : P) (u : ℤ_[2]) :
    zpowZtwo hP (x * y) u = zpowZtwo hP x u * zpowZtwo hP y u := by
  let φ : Multiplicative ℤ_[2] →* P :=
    { toFun := fun v ↦ zpowZtwoHom hP x v * zpowZtwoHom hP y v
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul]
        calc
          (zpowZtwoHom hP x a * zpowZtwoHom hP x b) *
              (zpowZtwoHom hP y a * zpowZtwoHom hP y b) =
            zpowZtwoHom hP x a *
              (zpowZtwoHom hP x b * zpowZtwoHom hP y a) *
                zpowZtwoHom hP y b := by group
          _ = zpowZtwoHom hP x a *
              (zpowZtwoHom hP y a * zpowZtwoHom hP x b) *
                zpowZtwoHom hP y b := by
            rw [hcomm (zpowZtwoHom hP x b) (zpowZtwoHom hP y a)]
          _ = (zpowZtwoHom hP x a * zpowZtwoHom hP y a) *
              (zpowZtwoHom hP x b * zpowZtwoHom hP y b) := by group }
  have hφcont : Continuous φ :=
    (zpowZtwoHom hP x).continuous_toFun.mul (zpowZtwoHom hP y).continuous_toFun
  have h := zpowZtwoHom_unique hP (φ := φ) hφcont u
  have h1 : φ (Multiplicative.ofAdd (1 : ℤ_[2])) = x * y := by
    change zpowZtwoHom hP x (Multiplicative.ofAdd 1) *
      zpowZtwoHom hP y (Multiplicative.ofAdd 1) = x * y
    rw [zpowZtwoHom_ofAdd_one, zpowZtwoHom_ofAdd_one]
  rw [h1] at h
  exact h.symm

/-- If every `m`-th power lies in a subgroup `H` and `m` is odd, inclusion induces an
equivalence on pro-2 completions.  Finite odd index is the main application: one takes `m` to
be the index and obtains the power-containment hypothesis from Lagrange's theorem. -/
noncomputable def proTwoCompletionSubgroupEquivOfOddPowerMem
    {A : Type} [CommGroup A] (H : Subgroup A) (m : ℕ) (hmodd : Odd m)
    (hpow : ∀ a : A, a ^ m ∈ H) :
    ContinuousMulEquiv (proPCompletion 2 H) (proPCompletion 2 A) := by
  have hmoddInt : Odd (m : ℤ) := by exact_mod_cast hmodd
  let mUnit : ℤ_[2]ˣ := (isUnit_intCast_of_odd hmoddInt).unit
  have hmUnit : (mUnit : ℤ_[2]) = (m : ℤ_[2]) := by
    exact (isUnit_intCast_of_odd hmoddInt).unit_spec
  let hPH : IsProP 2 (proPCompletion 2 H) := isProP_maxProPQuotient
  let hPA : IsProP 2 (proPCompletion 2 A) := isProP_maxProPQuotient
  let I : ContinuousMonoidHom (proPCompletion 2 H) (proPCompletion 2 A) :=
    proPCompletionMap (p := 2) H.subtype
  let r : A →* proPCompletion 2 H :=
    { toFun := fun a ↦ zpowZtwo hPH
          (proPCompletionMk 2 H ⟨a ^ m, hpow a⟩) ((mUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
      map_one' := by
        have hsub : (⟨(1 : A) ^ m, hpow 1⟩ : H) = 1 := by
          apply Subtype.ext
          simp
        rw [hsub, map_one, zpowZtwo_one_base]
      map_mul' := by
        intro a b
        have hsub : (⟨(a * b) ^ m, hpow (a * b)⟩ : H) =
            ⟨a ^ m, hpow a⟩ * ⟨b ^ m, hpow b⟩ := by
          apply Subtype.ext
          exact mul_pow a b m
        rw [hsub, map_mul, zpowZtwo_mul_base_of_mul_comm hPH
          (proPCompletion_mul_comm (p := 2) (D := H))] }
  let J : ContinuousMonoidHom (proPCompletion 2 A) (proPCompletion 2 H) :=
    proPCompletionLift hPH r
  have hcancelH : ∀ x : proPCompletion 2 H,
      zpowZtwo hPH (x ^ m) ((mUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = x := by
    intro x
    rw [← zpowZtwo_natCast hPH x m, zpowZtwo_zpowZtwo,
      ← hmUnit, ← Units.val_mul, mul_inv_cancel, Units.val_one, zpowZtwo_one_exp]
  have hcancelA : ∀ x : proPCompletion 2 A,
      zpowZtwo hPA (x ^ m) ((mUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = x := by
    intro x
    rw [← zpowZtwo_natCast hPA x m, zpowZtwo_zpowZtwo,
      ← hmUnit, ← Units.val_mul, mul_inv_cancel, Units.val_one, zpowZtwo_one_exp]
  have hleft : ∀ x, J (I x) = x := by
    have hfun : (fun x ↦ J (I x)) = (id : proPCompletion 2 H → _) := by
      apply Continuous.ext_on (denseRange_proPCompletionMk (p := 2) (A := H))
        (J.continuous_toFun.comp I.continuous_toFun) continuous_id
      rintro _ ⟨h, rfl⟩
      change J (I (proPCompletionMk 2 H h)) = proPCompletionMk 2 H h
      rw [show I (proPCompletionMk 2 H h) = proPCompletionMk 2 A h.1 from
        proPCompletionMap_mk H.subtype h, proPCompletionLift_mk]
      dsimp only [r]
      change zpowZtwo hPH
        (proPCompletionMk 2 H ⟨(h.1 : A) ^ m, hpow h.1⟩)
          ((mUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = proPCompletionMk 2 H h
      have hh : (⟨(h.1 : A) ^ m, hpow h.1⟩ : H) = h ^ m := by
        apply Subtype.ext
        rfl
      rw [hh, map_pow, hcancelH]
    exact fun x ↦ congrFun hfun x
  have hright : ∀ y, I (J y) = y := by
    have hfun : (fun y ↦ I (J y)) = (id : proPCompletion 2 A → _) := by
      apply Continuous.ext_on (denseRange_proPCompletionMk (p := 2) (A := A))
        (I.continuous_toFun.comp J.continuous_toFun) continuous_id
      rintro _ ⟨a, rfl⟩
      change I (J (proPCompletionMk 2 A a)) = proPCompletionMk 2 A a
      rw [proPCompletionLift_mk]
      dsimp only [r]
      change I (zpowZtwo hPH
        (proPCompletionMk 2 H ⟨a ^ m, hpow a⟩)
          ((mUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = proPCompletionMk 2 A a
      rw [map_zpowZtwo hPH hPA I,
        show I (proPCompletionMk 2 H ⟨a ^ m, hpow a⟩) =
          proPCompletionMk 2 A (a ^ m) from proPCompletionMap_mk H.subtype _,
        map_pow, hcancelA]
    exact fun y ↦ congrFun hfun y
  exact continuousMulEquivOfBijective I
    (Function.bijective_iff_has_inverse.mpr ⟨J, hleft, hright⟩)

@[simp] theorem proTwoCompletionSubgroupEquivOfOddPowerMem_mk
    {A : Type} [CommGroup A] (H : Subgroup A) (m : ℕ) (hmodd : Odd m)
    (hpow : ∀ a : A, a ^ m ∈ H) (h : H) :
    proTwoCompletionSubgroupEquivOfOddPowerMem H m hmodd hpow
        (proPCompletionMk 2 H h) = proPCompletionMk 2 A h.1 := by
  change proPCompletionMap (p := 2) H.subtype (proPCompletionMk 2 H h) = _
  exact proPCompletionMap_mk H.subtype h

/-! ## Finite-order elements of a profinite pro-2 group -/

/-- Every finite-order element of a profinite pro-2 group is killed by a power of `2`.

After removing the maximal power of `2` from an annihilating exponent, any surviving odd-order
part can be separated from `1` in a finite continuous quotient.  That quotient is a finite
2-group, where a nonidentity element cannot have odd order. -/
theorem exists_twoPower_pow_eq_one_of_isOfFinOrder
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (hx : IsOfFinOrder x) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one] at hx
  obtain ⟨n, hnpos, hxn⟩ := hx
  obtain ⟨k, m, hmodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hnpos)
  let z := x ^ (2 ^ k)
  have hzm : z ^ m = 1 := by
    change (x ^ (2 ^ k)) ^ m = 1
    rw [← pow_mul, hxn]
  refine ⟨k, ?_⟩
  change z = 1
  by_contra hz
  obtain ⟨U, hUsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := ({z}ᶜ : Set P)) isOpen_compl_singleton
    (Set.mem_compl_singleton_iff.mpr fun h ↦ hz h.symm)
  let π : P →* (P ⧸ U.toSubgroup) := QuotientGroup.mk' U.toSubgroup
  have hπz : π z ≠ 1 := fun h ↦
    (Set.mem_compl_singleton_iff.mp
      (hUsub ((QuotientGroup.eq_one_iff z).mp h))) rfl
  have hπzm : (π z) ^ m = 1 := by rw [← map_pow, hzm, map_one]
  have hord : orderOf (π z) ∣ m := orderOf_dvd_of_pow_eq_one hπzm
  have htwo : 2 ∣ orderOf (π z) := (hP U).dvd_orderOf hπz
  exact hmodd.not_two_dvd_nat (htwo.trans hord)

#print axioms proTwoCompletionSubgroupEquivOfOddPowerMem
#print axioms exists_twoPower_pow_eq_one_of_isOfFinOrder

end

end GQ2
