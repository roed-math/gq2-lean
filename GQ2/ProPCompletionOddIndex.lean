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

#print axioms proTwoCompletionSubgroupEquivOfOddPowerMem

end

end GQ2
