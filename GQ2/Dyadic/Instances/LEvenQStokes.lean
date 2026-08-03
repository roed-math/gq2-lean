/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.LRoeStokesBridge
import GQ2.Dyadic.Count.Scalar

/-!
# The exact `q`-dependence of the unramified `L_sq` Stokes complex

The hoped-for transport of the `q = 2` Roe complex to every even tame exponent is false.
On an elementary module on which `tau` acts trivially, the degree-one differential is indeed
independent of the even integer `q`.  The middle Stokes map, however, contains the term

`(q.choose 2) • y_tau (x_tau)`.

Consequently the full Stokes ladder is invariant precisely after fixing the parity of
`q.choose 2`; among even integers this is the same as fixing whether `q` is `0` or `2` modulo
`4`.  In particular the Roe base case transports from `q = 2` to `q ≡ 2 (mod 4)`, but not to
`q ≡ 0 (mod 4)`.  The theorems below make this boundary explicit without any continuous
cohomology or Tate-duality input.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words.LSq Certificates.MProcyclic

/-! ## A generic cohomological transport lemma -/

/-- A three-term quasi-isomorphism only sees its middle map on degree-one cocycles.  Thus two
middle maps which agree on `ker dX1` give equivalent `StokesQuasiIso` predicates. -/
theorem stokesQuasiIso_congr_middle_on_cycles
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
    [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
    [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]
    {dX₀ : X₀ →+ X₁} {dX₁ : X₁ →+ X₂} {dY₀ : Y₀ →+ Y₁} {dY₁ : Y₁ →+ Y₂}
    {φ₀ : X₀ →+ Y₀} {φ₁ ψ₁ : X₁ →+ Y₁} {φ₂ : X₂ →+ Y₂}
    (hmid : ∀ x, dX₁ x = 0 → φ₁ x = ψ₁ x) :
    StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ ↔
      StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ ψ₁ φ₂ := by
  have forward : ∀ {f g : X₁ →+ Y₁},
      (∀ x, dX₁ x = 0 → f x = g x) →
      StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ f φ₂ →
        StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ g φ₂ := by
    intro f g hfg H
    exact
      { h0_inj := H.h0_inj
        h0_surj := H.h0_surj
        h1_inj := by
          intro x hx hg
          apply H.h1_inj x hx
          obtain ⟨y, hy⟩ := hg
          exact ⟨y, hy.trans (hfg x hx).symm⟩
        h1_surj := by
          intro y hy
          obtain ⟨x, z, hx, hsum⟩ := H.h1_surj y hy
          exact ⟨x, z, hx, by rw [← hfg x hx]; exact hsum⟩
        h2_inj := H.h2_inj
        h2_surj := H.h2_surj }
  exact ⟨forward hmid, forward fun x hx ↦ (hmid x hx).symm⟩

/-! ## Binomial parity -/

/-- For an even integer in the `2 mod 4` class, `C(q,2)` is odd. -/
theorem choose_two_odd_of_mod_four_two {q : ℕ} (hq : q % 4 = 2) : Odd (q.choose 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 2 := ⟨q / 4, by omega⟩
  let m := 2 * k + 1
  have hq' : 4 * k + 2 = 2 * m := by simp [m]; ring
  have hchoose : (2 * m).choose 2 = m * (2 * m - 1) := by
    rw [Nat.choose_two_right,
      show 2 * m * (2 * m - 1) = m * (2 * m - 1) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [hq', hchoose]
  have hm : Odd m := ⟨k, by simp [m]⟩
  have hlast : Odd (2 * m - 1) := ⟨m - 1, by simp [m]; omega⟩
  exact hm.mul hlast

/-- For an even integer in the `0 mod 4` class, `C(q,2)` is even. -/
theorem choose_two_even_of_mod_four_zero {q : ℕ} (hq : q % 4 = 0) : Even (q.choose 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k := ⟨q / 4, by omega⟩
  let m := 2 * k
  have hq' : 4 * k = 2 * m := by simp [m]; ring
  have hchoose : (2 * m).choose 2 = m * (2 * m - 1) := by
    rw [Nat.choose_two_right,
      show 2 * m * (2 * m - 1) = m * (2 * m - 1) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [hq', hchoose]
  exact ⟨k * (2 * m - 1), by simp [m]; ring⟩

/-! ## First-order independence -/

/-- On an elementary module with trivial `tau` action, the primal first jet of the tame
relator is independent of the even exponent `q`. -/
theorem heisA_tameRelW_unram
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) :
    (heisEvalZ ⇑t x y E E₂ (tameRelW n q)).a = t.σ⁻¹ • x .tau := by
  have hτm : ∀ a : A, t Generator.tau • a = a := hτ
  have e1 : heisEvalZ ⇑t x y E E₂ (.conj (.gen .tau) (.gen .sigma))
      = ⟨t.σ⁻¹ • x .tau, t.σ⁻¹ • y .tau,
          y .sigma (x .tau) + y .tau (x .sigma), conjR (t .tau) t.σ⟩ := by
    rw [heisEvalZ_conj, heisEvalZ_gen, heisEvalZ_gen, heisConjR_of_trivial _ _ hτm]
    refine HeisLift.ext rfl rfl ?_ rfl
    show (0 : ZMod 2) + y .sigma (x .tau) + y .tau (x .sigma) = _
    rw [zero_add]
  have e2 : heisEvalZ ⇑t x y E E₂ (.inv (.zpow (.gen .tau) (q : ℤ)))
      = ⟨0, 0, (q.choose 2) • y .tau (x .tau), (t .tau ^ q)⁻¹⟩ := by
    have hqa : q • x .tau = 0 := Certificates.even_nsmul_eq_zero hA₂ hq _
    have hql : q • y .tau = (0 : ElemDual A) :=
      Certificates.even_nsmul_eq_zero ElemDual.add_self_eq_zero hq _
    rw [heisEvalZ_inv, heisEvalZ_zpow, heisEvalZ_gen, zpow_natCast,
      heisPow_of_trivial _ hτm]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show -((t .tau ^ q)⁻¹ • q • x .tau) = 0
      rw [hqa, smul_zero, neg_zero]
    · show -((t .tau ^ q)⁻¹ • q • y .tau) = 0
      rw [hql, smul_zero, neg_zero]
    · show q • (0 : ZMod 2) + (q.choose 2) • y .tau (x .tau)
          + (q • y .tau) (q • x .tau) = (q.choose 2) • y .tau (x .tau)
      rw [smul_zero, zero_add, hql, ElemDual.zero_apply, add_zero]
  rw [tameRelW, heisEvalZ_mul, e1, e2, HeisLift.mul_a, smul_zero, add_zero]

/-- The degree-one differential of the resolved `L_sq` family is independent of the even tame
exponent on every unramified elementary module.  This holds for all handle counts. -/
theorem heisD1_lSqFam_even_congr_unram
    {h q r e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) (hr : Even r) :
    heisD1 (A := A) ⇑t (Certificates.LSqStokes.lSqFam h q e)
      = heisD1 ⇑t (Certificates.LSqStokes.lSqFam h r e) := by
  apply AddMonoidHom.ext
  intro x
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
          (Certificates.LSqStokes.lSqFam h q e (0 : Fin 2))).a =
        (FreeGroup.lift (heisGen (⇑t) x 0)
          (Certificates.LSqStokes.lSqFam h r e (0 : Fin 2))).a
    rw [Certificates.LSqStokes.lSqFam_zero,
      Certificates.LSqStokes.lSqFam_zero, ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift,
      heisA_tameRelW_unram t x 0 _ _ hA₂ hτ hq,
      heisA_tameRelW_unram t x 0 _ _ hA₂ hτ hr]
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
          (Certificates.LSqStokes.lSqFam h q e (1 : Fin 2))).a =
        (FreeGroup.lift (heisGen (⇑t) x 0)
          (Certificates.LSqStokes.lSqFam h r e (1 : Fin 2))).a
    rw [Certificates.LSqStokes.lSqFam_one, Certificates.LSqStokes.lSqFam_one]

/-! ## Exact second-order dependence -/

/-- The middle Stokes map is unchanged when the two tame exponents are even and their binomial
coefficients have the same image in `ZMod 2`.  This is the strongest literal invariance
statement: the hypothesis is necessary already for the scalar module. -/
theorem heisEta1_lSqFam_even_congr_unram
    {h q r e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) (hr : Even r)
    (hchoose : (q.choose 2 : ZMod 2) = (r.choose 2 : ZMod 2)) :
    heisEta1 (A := A) ⇑t (Certificates.LSqStokes.lSqFam h q e)
      = heisEta1 (A := A) ⇑t (Certificates.LSqStokes.lSqFam h r e) := by
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  calc
    heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x y =
        (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
          (tameRelW (2 * h + 1) q)).z
          + (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (lSqW h)).z :=
      Certificates.LSqStokes.heisEta1_lSqFam_apply t x y
    _ = (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
          (tameRelW (2 * h + 1) r)).z
          + (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (lSqW h)).z := by
      rw [Certificates.heisZ_tameRelW_unram t x y _ _ hA₂ hτ hq,
        Certificates.heisZ_tameRelW_unram t x y _ _ hA₂ hτ hr]
      simp only [nsmul_eq_mul, hchoose]
    _ = heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h r e) x y :=
      (Certificates.LSqStokes.heisEta1_lSqFam_apply t x y).symm

/-- A cocycle in the unramified `L_sq` complex has zero `tau` coordinate.  This is exactly the
invertible tame Fox row `S^-1 x_tau`; no wild-row calculation is involved. -/
theorem tau_eq_zero_of_lSqFam_cocycle_unram
    {h q e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q)
    (x : Generator (2 * h + 1) → A)
    (hx : heisD1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x = 0) : x .tau = 0 := by
  have hk := congrFun hx (0 : Fin 2)
  change
    (FreeGroup.lift (heisGen (⇑t) x 0)
      (Certificates.LSqStokes.lSqFam h q e (0 : Fin 2))).a = 0 at hk
  rw [Certificates.LSqStokes.lSqFam_zero, ← heisEvalZ_eq_lift,
    heisA_tameRelW_unram t x 0 _ _ hA₂ hτ hq] at hk
  have hs := congrArg (fun a : A ↦ t.σ • a) hk
  rwa [smul_zero, smul_inv_smul] at hs

/-- Although the middle Stokes maps at two even exponents need not be literally equal, they
agree on every degree-one cocycle.  The only possible difference is the tame `tau` diagonal,
and `tau_eq_zero_of_lSqFam_cocycle_unram` kills it. -/
theorem heisEta1_lSqFam_even_congr_on_cocycles_unram
    {h q r e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) (hr : Even r)
    (x : Generator (2 * h + 1) → A)
    (hx : heisD1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x = 0) :
    heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x =
      heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h r e) x := by
  have hxτ := tau_eq_zero_of_lSqFam_cocycle_unram t hA₂ hτ hq x hx
  apply AddMonoidHom.ext
  intro y
  calc
    heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x y =
        (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
          (tameRelW (2 * h + 1) q)).z
          + (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (lSqW h)).z :=
      Certificates.LSqStokes.heisEta1_lSqFam_apply t x y
    _ = (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
          (tameRelW (2 * h + 1) r)).z
          + (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (lSqW h)).z := by
      rw [Certificates.heisZ_tameRelW_unram t x y _ _ hA₂ hτ hq,
        Certificates.heisZ_tameRelW_unram t x y _ _ hA₂ hτ hr, hxτ]
      simp
    _ = heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h r e) x y :=
      (Certificates.LSqStokes.heisEta1_lSqFam_apply t x y).symm

/-- Full Stokes duality transports between even tame exponents with the same binomial parity,
on an unramified elementary module.  Both the primal and contragredient degree-one rows are
transported, as is the middle map; the end maps are independent of the relator words. -/
theorem stokesDuality_lSqFam_even_congr_unram
    {h q r e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) (hr : Even r)
    (hchoose : (q.choose 2 : ZMod 2) = (r.choose 2 : ZMod 2)) :
    StokesDuality ⇑t (Certificates.LSqStokes.lSqFam h q e) A ↔
      StokesDuality ⇑t (Certificates.LSqStokes.lSqFam h r e) A := by
  have hτD : ∀ l : ElemDual A, t.τ • l = l :=
    fun l ↦ smul_elemDual_of_trivial hτ l
  have hdA := heisD1_lSqFam_even_congr_unram (e := e) t hA₂ hτ hq hr
  have hdD := heisD1_lSqFam_even_congr_unram (e := e) t
    ElemDual.add_self_eq_zero hτD hq hr
  have hη := heisEta1_lSqFam_even_congr_unram (e := e) t hA₂ hτ hq hr hchoose
  unfold StokesDuality
  rw [hdA, hdD, hη]

/-- **Cohomological even-`q` invariance.**  On an unramified elementary module, full Stokes
duality is independent of the even tame exponent.  Unlike
`stokesDuality_lSqFam_even_congr_unram`, this theorem imposes no binomial-parity condition: the
middle maps need only agree on cocycles, and the tame row forces their `tau` coordinate to
vanish.  In particular this transports the Roe proof from `q = 2` to the `q = 4` class without
a new Nielsen presentation. -/
theorem stokesDuality_lSqFam_all_even_congr_unram
    {h q r e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) (hr : Even r) :
    StokesDuality ⇑t (Certificates.LSqStokes.lSqFam h q e) A ↔
      StokesDuality ⇑t (Certificates.LSqStokes.lSqFam h r e) A := by
  have hτD : ∀ l : ElemDual A, t.τ • l = l :=
    fun l ↦ smul_elemDual_of_trivial hτ l
  have hdA := heisD1_lSqFam_even_congr_unram (e := e) t hA₂ hτ hq hr
  have hdD := heisD1_lSqFam_even_congr_unram (e := e) t
    ElemDual.add_self_eq_zero hτD hq hr
  have hmid : ∀ x,
      heisD1 (A := A) ⇑t (Certificates.LSqStokes.lSqFam h r e) x = 0 →
      heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x =
        heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h r e) x := by
    intro x hx
    apply heisEta1_lSqFam_even_congr_on_cocycles_unram t hA₂ hτ hq hr x
    rwa [hdA]
  unfold StokesDuality
  rw [hdA, hdD]
  exact stokesQuasiIso_congr_middle_on_cycles hmid

/-- The Roe `q = 2` Stokes ladder transports to every `q = 2 (mod 4)` on an unramified
elementary module. -/
theorem stokesDuality_lSqFam_two_iff_of_mod_four_two
    {h q e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hq4 : q % 4 = 2) :
    StokesDuality ⇑t (Certificates.LSqStokes.lSqFam h 2 e) A ↔
      StokesDuality ⇑t (Certificates.LSqStokes.lSqFam h q e) A := by
  have hq : Even q := by
    obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 2 := ⟨q / 4, by omega⟩
    exact ⟨2 * k + 1, by omega⟩
  apply stokesDuality_lSqFam_even_congr_unram t hA₂ hτ (by decide) hq
  rw [natCast_zmod2_odd (by decide : Odd ((2 : ℕ).choose 2)),
    natCast_zmod2_odd (choose_two_odd_of_mod_four_two hq4)]

/-! ## The obstruction at `q = 4` -/

/-- At `q = 2`, the tame middle term has a `tau`-diagonal. -/
theorem heisZ_tameRelW_two_unram
    {n : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) :
    (heisEvalZ ⇑t x y E E₂ (tameRelW n 2)).z
      = y .sigma (x .tau) + y .tau (x .sigma) + y .tau (x .tau) := by
  rw [Certificates.heisZ_tameRelW_unram t x y E E₂ hA₂ hτ (by decide),
    nsmul_zmod2_odd (by decide)]

/-- At `q = 4`, the tame `tau`-diagonal vanishes.  Thus no literal arbitrary-even-`q`
invariance theorem can hold, even when the action is trivial. -/
theorem heisZ_tameRelW_four_unram
    {n : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) :
    (heisEvalZ ⇑t x y E E₂ (tameRelW n 4)).z
      = y .sigma (x .tau) + y .tau (x .sigma) := by
  rw [Certificates.heisZ_tameRelW_unram t x y E E₂ hA₂ hτ (by decide),
    nsmul_zmod2_even (by decide), add_zero]

/-- The `q = 2` and `q = 4` tame middle terms are unequal as soon as the chosen offsets detect
the `tau` diagonal. -/
theorem heisZ_tameRelW_two_ne_four_unram_of_diag
    {n : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hA₂ : ∀ a : A, a + a = 0)
    (hτ : ∀ a : A, t.τ • a = a) (hdiag : y .tau (x .tau) ≠ 0) :
    (heisEvalZ ⇑t x y E E₂ (tameRelW n 2)).z ≠
      (heisEvalZ ⇑t x y E E₂ (tameRelW n 4)).z := by
  rw [heisZ_tameRelW_two_unram t x y E E₂ hA₂ hτ,
    heisZ_tameRelW_four_unram t x y E E₂ hA₂ hτ]
  intro heq
  apply hdiag
  exact add_left_cancel (heq.trans (add_zero _).symm)

/-- Every `ZMod 2` coefficient module is simple.  The action is necessarily trivial, but the
proof only needs the two-element classification of its additive subgroups. -/
theorem isSimpleModTwo_zmodTwo
    {C : Type*} [Group C] [DistribMulAction C (ZMod 2)] : IsSimpleModTwo C (ZMod 2) := by
  refine ⟨inferInstance, fun W _ ↦ ?_⟩
  by_cases h1 : (1 : ZMod 2) ∈ W
  · right
    apply top_unique
    intro z _
    rcases ZMod.eq_zero_or_eq_one z with rfl | rfl
    · exact W.zero_mem
    · exact h1
  · left
    apply le_antisymm
    · intro z hz
      rw [AddSubgroup.mem_bot]
      rcases ZMod.eq_zero_or_eq_one z with rfl | rfl
      · rfl
      · exact absurd hz h1
    · exact bot_le

/-- The failure of arbitrary-even-`q` invariance occurs on a simple module, not merely on an
artificial nonsimple coefficient system.  Both offsets are supported on `tau`, so the two
middle terms differ by exactly `1 : ZMod 2`. -/
theorem simpleScalar_tameStokes_two_ne_four
    {n : ℕ} {C : Type*} [Group C] [DistribMulAction C (ZMod 2)]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    let x : Generator n → ZMod 2 := fun
      | .sigma => 0
      | .tau => 1
      | .wild _ => 0
    let y : Generator n → ElemDual (ZMod 2) := fun
      | .sigma => 0
      | .tau => AddMonoidHom.id (ZMod 2)
      | .wild _ => 0
    (heisEvalZ ⇑t x y E E₂ (tameRelW n 2)).z ≠
      (heisEvalZ ⇑t x y E E₂ (tameRelW n 4)).z := by
  dsimp only
  apply heisZ_tameRelW_two_ne_four_unram_of_diag t _ _ E E₂
    (fun _ ↦ CharTwo.add_self_eq_zero _) (fun a ↦ Count.smul_zmod2 t.τ a)
  change (1 : ZMod 2) ≠ 0
  decide

end

end GQ2.Dyadic
