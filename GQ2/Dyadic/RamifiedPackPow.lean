/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.RamifiedPack

/-!
# The ramified isotypic pack at a general two-power tame relation

`GQ2/RamifiedPack.lean` is written for the `ℚ₂` tame relation `s⁻¹ t s = t²`.  The dyadic
campaign needs the same package at the general residue cardinality `q = 2 ^ F`, i.e. for the
relation

  `s⁻¹ t s = t ^ 2 ^ F`.

This file carries the three genuinely `q`-dependent leaves across:

* `conj_eq_two_pow_pow` — every conjugate of `t` is still a **2-power** power of `t`.  This is
  the step that forces `q` to be a power of two: the isotype-stability engine
  (`RamifiedPack.smul_mem_ker_aeval`) is the char-2 polynomial Frobenius `P(X^{2^j}) = P(X)^{2^j}`,
  which knows only 2-power twists.  See the module docstring of
  `GQ2/Dyadic/Instances/GammaLSourceArfGeneral.lean` for the explicit `q = 10` refutation of the
  general-even-`q` statement.
* `powOmega2_pow_two_pow_eq_one_pow` — the `U`-kill `U^{2^a} = 1`, `U := powOmega2 s`.
* `card_fixed_powOmega2_pow` — the descent count `#V^U = 2^{r·s_V}`.

The last one needs `F` **odd**, and that is sharp: at `F = 2` (`q = 4`) the count is genuinely
different, see `GQ2/Dyadic/Instances/GammaLSourceArfGeneral.lean`.

The bookkeeping change throughout is uniform: the twist exponent `ω = ω₂(orderOf s)` of the
`q = 2` proofs becomes `F * ω`, because `(s^n)⁻¹ t s^n = t ^ 2 ^ (F * n)`.
-/

namespace GQ2.Dyadic.RamifiedPow

open GQ2 GQ2.RamifiedPack Polynomial

/-! ## Conjugation: every conjugate of `t` is a 2-power power of `t` -/

section Conj

variable {C : Type*} [Group C]

/-- The `2^F`-th root step: if `x ^ 2 ^ F = t` with `x` of the same odd order as `t`, then
`x` is the 2-power power `t ^ 2 ^ (F (φ(d) − 1))` — Euler's `2^{φ(d)} ≡ 1 (mod d)`, raised to
the `F`-th power.  Generalizes `RamifiedPack.eq_two_pow_of_sq_eq` (`F = 1`). -/
theorem eq_two_pow_of_pow_two_pow_eq {t x : C} (hd : Odd (orderOf t)) (hpos : 0 < orderOf t)
    (horder : orderOf x = orderOf t) (F : ℕ) (hx : x ^ 2 ^ F = t) :
    x = t ^ 2 ^ (F * (Nat.totient (orderOf t) - 1)) := by
  have htot : (2 : ℕ) ^ Nat.totient (orderOf t) ≡ 1 [MOD orderOf t] :=
    Nat.ModEq.pow_totient hd.coprime_two_left
  have htotpos : 0 < Nat.totient (orderOf t) := Nat.totient_pos.mpr hpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.totient (orderOf t) = n + 1 :=
    ⟨Nat.totient (orderOf t) - 1, by omega⟩
  have hFtot : (2 : ℕ) ^ (F * Nat.totient (orderOf t)) ≡ 1 [MOD orderOf t] := by
    rw [pow_mul']
    calc ((2 : ℕ) ^ Nat.totient (orderOf t)) ^ F ≡ 1 ^ F [MOD orderOf t] := htot.pow F
      _ = 1 := one_pow F
  have h1 : x ^ 2 ^ (F * Nat.totient (orderOf t)) = x := by
    have hiff : x ^ 2 ^ (F * Nat.totient (orderOf t)) = x ^ 1
        ↔ 2 ^ (F * Nat.totient (orderOf t)) ≡ 1 [MOD orderOf x] := pow_eq_pow_iff_modEq
    rw [horder] at hiff
    simpa using hiff.mpr hFtot
  have hexp : F + F * (Nat.totient (orderOf t) - 1) = F * Nat.totient (orderOf t) := by
    rw [hn]
    simp only [Nat.add_sub_cancel]
    ring
  calc x = x ^ 2 ^ (F * Nat.totient (orderOf t)) := h1.symm
    _ = (x ^ 2 ^ F) ^ 2 ^ (F * (Nat.totient (orderOf t) - 1)) := by
        rw [← pow_mul, ← pow_add, hexp]
    _ = t ^ 2 ^ (F * (Nat.totient (orderOf t) - 1)) := by rw [hx]

/-- **Every element of `C = ⟨s, t⟩` conjugates `t` to a 2-power power of `t`**, at the general
two-power tame relation `s⁻¹ t s = t ^ 2 ^ F`.  Generalizes
`RamifiedPack.conj_eq_two_pow` (`F = 1`). -/
theorem conj_eq_two_pow_pow (s t : C) (F : ℕ)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2 ^ F)
    (hodd : Odd (orderOf t)) (hpos : 0 < orderOf t) (g : C) :
    (∃ j : ℕ, g⁻¹ * t * g = t ^ 2 ^ j) ∧ (∃ j : ℕ, g * t * g⁻¹ = t ^ 2 ^ j) := by
  have hg : g ∈ Subgroup.closure ({s, t} : Set C) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · refine ⟨⟨F, hrel⟩, ?_⟩
      -- the `2^F`-th root `x t x⁻¹ = t ^ 2 ^ (F (φ(d) − 1))`
      have hsc : SemiconjBy x t (x * t * x⁻¹) := by
        show x * t = x * t * x⁻¹ * x
        group
      have hxF : (x * t * x⁻¹) ^ 2 ^ F = t := by
        have h2 : (x * t * x⁻¹) ^ 2 ^ F = x * t ^ 2 ^ F * x⁻¹ :=
          (conj_pow_eq x t (2 ^ F)).symm
        rw [h2, ← hrel]
        group
      exact ⟨F * (Nat.totient (orderOf t) - 1),
        eq_two_pow_of_pow_two_pow_eq hodd hpos hsc.orderOf_eq.symm F hxF⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx'
      exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  | one => exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨j₁, hj₁⟩ := ihx.1
    obtain ⟨j₁', hj₁'⟩ := ihx.2
    obtain ⟨j₂, hj₂⟩ := ihy.1
    obtain ⟨j₂', hj₂'⟩ := ihy.2
    constructor
    · refine ⟨j₂ + j₁, ?_⟩
      calc (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y := by group
        _ = y⁻¹ * t ^ 2 ^ j₁ * y := by rw [hj₁]
        _ = (y⁻¹ * t * y) ^ 2 ^ j₁ := inv_conj_pow_eq y t (2 ^ j₁)
        _ = (t ^ 2 ^ j₂) ^ 2 ^ j₁ := by rw [hj₂]
        _ = t ^ 2 ^ (j₂ + j₁) := by rw [← pow_mul, ← pow_add]
    · refine ⟨j₁' + j₂', ?_⟩
      calc (x * y) * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
        _ = x * t ^ 2 ^ j₂' * x⁻¹ := by rw [hj₂']
        _ = (x * t * x⁻¹) ^ 2 ^ j₂' := conj_pow_eq x t (2 ^ j₂')
        _ = (t ^ 2 ^ j₁') ^ 2 ^ j₂' := by rw [hj₁']
        _ = t ^ 2 ^ (j₁' + j₂') := by rw [← pow_mul, ← pow_add]
  | inv x hx ih =>
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hj⟩ := ih.2
      exact ⟨j, by rwa [inv_inv]⟩
    · obtain ⟨j, hj⟩ := ih.1
      exact ⟨j, by rwa [inv_inv]⟩

/-- Iterating the general two-power tame twist: `(s^n)⁻¹ t s^n = t ^ 2 ^ (F n)`.  Generalizes
`RamifiedPack.inv_pow_conj` (`F = 1`). -/
theorem inv_pow_conj_pow (s t : C) {F : ℕ} (hrel : s⁻¹ * t * s = t ^ 2 ^ F) (n : ℕ) :
    (s ^ n)⁻¹ * t * s ^ n = t ^ 2 ^ (F * n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ s m]
    calc (s ^ m * s)⁻¹ * t * (s ^ m * s)
        = s⁻¹ * ((s ^ m)⁻¹ * t * s ^ m) * s := by group
      _ = s⁻¹ * t ^ 2 ^ (F * m) * s := by rw [ih]
      _ = (s⁻¹ * t * s) ^ 2 ^ (F * m) := inv_conj_pow_eq s t (2 ^ (F * m))
      _ = (t ^ 2 ^ F) ^ 2 ^ (F * m) := by rw [hrel]
      _ = t ^ 2 ^ (F * (m + 1)) := by
          rw [← pow_mul, ← pow_add]
          congr 2
          ring

end Conj

/-! ## The single isotype from bare conjugation data -/

section SingleIsotype

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction C V]

/-- **The single isotype**, with the tame relation replaced by its only consequence: every
element conjugates `t` into a 2-power power of `t`.  Body-identical to
`RamifiedPack.exists_single_isotype` apart from that substitution. -/
theorem exists_single_isotype_of_conj [Finite V] (t : C)
    (hconj : ∀ g : C, ∃ j : ℕ, g⁻¹ * t * g = t ^ 2 ^ j)
    (hpos : 0 < orderOf t)
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : V, v ≠ 0) :
    ∃ P : Polynomial (ZMod 2), P.Monic ∧ Irreducible P
      ∧ P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))
      ∧ ∀ v : V, Polynomial.aeval (actEnd (V := V) t) P v = 0 := by
  classical
  set d := orderOf t with hd
  have hXd : (X ^ d - 1 : Polynomial (ZMod 2)) ≠ 0 := by
    have h := Polynomial.X_pow_sub_C_ne_zero (R := ZMod 2) hpos (1 : ZMod 2)
    rwa [Polynomial.C_1] at h
  have hfac : ∃ Q ∈ UniqueFactorizationMonoid.normalizedFactors
      (X ^ d - 1 : Polynomial (ZMod 2)),
      ∃ v : V, v ≠ 0 ∧ Polynomial.aeval (actEnd (V := V) t) Q v = 0 := by
    by_contra! hcon
    have hinj : ∀ f ∈ (UniqueFactorizationMonoid.normalizedFactors
        (X ^ d - 1 : Polynomial (ZMod 2))).toList.map
          (fun Q => Polynomial.aeval (actEnd (V := V) t) Q),
        Function.Injective f := by
      intro f hf
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hf
      have hQmem := Multiset.mem_toList.mp hQ
      intro a b hab
      by_contra hne
      exact hcon Q hQmem (a - b) (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])
    have hprodinj := list_prod_injective _ hinj
    have hprodeq : ((UniqueFactorizationMonoid.normalizedFactors
          (X ^ d - 1 : Polynomial (ZMod 2))).toList.map
            (fun Q => Polynomial.aeval (actEnd (V := V) t) Q)).prod
        = Polynomial.aeval (actEnd (V := V) t) (X ^ d - 1 : Polynomial (ZMod 2)) := by
      rw [← map_list_prod]
      congr 1
      rw [Multiset.prod_toList]
      have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hXd
      have hmonprod : ((UniqueFactorizationMonoid.normalizedFactors
          (X ^ d - 1 : Polynomial (ZMod 2))).prod).Monic := by
        refine Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
          Polynomial.monic_one (fun Q hQ => ?_)
        have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
        have hmon := Polynomial.monic_normalize (R := ZMod 2)
          (UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ).ne_zero
        rwa [hnorm] at hmon
      have hXdmon : (X ^ d - 1 : Polynomial (ZMod 2)).Monic := by
        have h := Polynomial.monic_X_pow_sub_C (R := ZMod 2) (1 : ZMod 2) (by omega : d ≠ 0)
        rwa [Polynomial.C_1] at h
      exact Polynomial.eq_of_monic_of_associated hmonprod hXdmon hassoc
    rw [hprodeq, aeval_X_pow_orderOf_sub_one] at hprodinj
    obtain ⟨v, hv⟩ := hVne
    refine hv (hprodinj ?_)
    show (0 : Module.End (ZMod 2) V) v = (0 : Module.End (ZMod 2) V) 0
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
  obtain ⟨Q, hQmem, v₀, hv₀ne, hv₀ker⟩ := hfac
  have hQne : Q ≠ 0 :=
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQmem).ne_zero
  refine ⟨Q, ?_, UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQmem,
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQmem, ?_⟩
  · have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQmem
    have hmon := Polynomial.monic_normalize (R := ZMod 2) hQne
    rwa [hnorm] at hmon
  · set K : AddSubgroup V :=
      { carrier := {v : V | Polynomial.aeval (actEnd (V := V) t) Q v = 0}
        zero_mem' := map_zero _
        add_mem' := fun {a b} ha hb => by
          show Polynomial.aeval (actEnd (V := V) t) Q (a + b) = 0
          rw [map_add, show Polynomial.aeval (actEnd (V := V) t) Q a = 0 from ha,
            show Polynomial.aeval (actEnd (V := V) t) Q b = 0 from hb, add_zero]
        neg_mem' := fun {a} ha => by
          show Polynomial.aeval (actEnd (V := V) t) Q (-a) = 0
          rw [map_neg, show Polynomial.aeval (actEnd (V := V) t) Q a = 0 from ha,
            neg_zero] } with hK
    have hstab : ∀ g : C, ∀ w ∈ K, g • w ∈ K := fun g w hw => by
      obtain ⟨j, hj⟩ := hconj g
      exact smul_mem_ker_aeval hj Q w hw
    rcases hsimple K hstab with hbot | htop
    · exact absurd (AddSubgroup.mem_bot.mp (hbot ▸ (hv₀ker : v₀ ∈ K))) hv₀ne
    · exact fun v => show v ∈ K from htop ▸ AddSubgroup.mem_top v

end SingleIsotype

/-! ## The `U`-kill and the descent count at the general two-power relation -/

section Counts

open Polynomial

/-- The arithmetic bookkeeping shared by the two counts: an odd `r` dividing `F · orderOf s`
already divides `F · ω₂(orderOf s)`.  (`r` is coprime to the 2-part of `k`, and the odd part of
`k` divides `ω₂ k`.) -/
theorem odd_dvd_mul_omega2Exp {F k r : ℕ} (hrodd : ¬(2 : ℕ) ∣ r) (hrk : r ∣ F * k) :
    r ∣ F * omega2Exp k := by
  set b := k.factorization 2 with hb
  set k' := k / 2 ^ b with hk'
  have hsplit : 2 ^ b * k' = k := Nat.ordProj_mul_ordCompl_eq_self k 2
  have hrk' : r ∣ 2 ^ b * (F * k') := by
    rw [show 2 ^ b * (F * k') = F * (2 ^ b * k') by ring, hsplit]
    exact hrk
  have hcop : Nat.Coprime r (2 ^ b) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hrodd).symm).pow_right b
  exact (hcop.dvd_of_dvd_mul_left hrk').trans
    (Nat.mul_dvd_mul_left F (oddPart_dvd_omega2Exp k))

/-- Iterated Frobenius on `AdjoinRoot P` (a public copy of the private
`RamifiedPack.frobEquiv_pow_apply`). -/
theorem frobEquiv_pow_apply' (P : Polynomial (ZMod 2)) [Fact (Irreducible P)]
    (hmon : P.Monic) (m : ℕ) (y : AdjoinRoot P) :
    (frobEquiv P hmon ^ m) y = y ^ 2 ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ i ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih,
      show frobEquiv P hmon (y ^ 2 ^ i) = (y ^ 2 ^ i) ^ 2 from rfl, ← pow_mul,
      show 2 ^ i * 2 = 2 ^ (i + 1) from (pow_succ 2 i).symm]

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
variable (t : C) (P : Polynomial (ZMod 2)) [Fact (Irreducible P)]

/-- **`U^{2^a} = 1`** at the general two-power tame relation `s⁻¹ t s = t^{2^F}`.  Generalizes
`RamifiedPack.powOmega2_pow_two_pow_eq_one` (`F = 1`); the twist exponent `ω` there becomes
`F · ω` here, and no parity hypothesis on `F` is needed. -/
theorem powOmega2_pow_two_pow_eq_one_pow [Finite C] [Finite V] (s : C) {F : ℕ}
    (hrel : s⁻¹ * t * s = t ^ 2 ^ F)
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hmon : P.Monic) (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {a r : ℕ} (hr : Odd r) (hfar : P.natDegree = 2 ^ a * r)
    {sV : ℕ} (hsV : 1 ≤ sV) (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    powOmega2 s ^ 2 ^ a = 1 := by
  classical
  have hpos : 0 < orderOf t := orderOf_pos t
  have hdeg : 0 < P.natDegree := by
    rw [hfar]
    exact Nat.mul_pos (Nat.two_pow_pos a) hr.pos
  set k := orderOf s with hk
  set ω := omega2Exp k with hω
  have hU : powOmega2 s = s ^ ω := rfl
  have htk : t ^ 2 ^ (F * k) = t ^ 1 := by
    have h1 := inv_pow_conj_pow s t hrel k
    rw [show s ^ k = 1 from pow_orderOf_eq_one s, inv_one, one_mul, mul_one] at h1
    simpa using h1.symm
  have hxk : AdjoinRoot.root P ^ 2 ^ (F * k) = AdjoinRoot.root P := by
    simpa using root_pow_eq_of_t_pow_eq t P htk hsV e he
  have hfk : P.natDegree ∣ F * k := natDegree_dvd_of_root_pow P hmon hdeg hxk
  have hrk : r ∣ F * k := dvd_trans ⟨2 ^ a, by rw [hfar]; ring⟩ hfk
  have hrodd : ¬(2 : ℕ) ∣ r := by
    rcases hr with ⟨j, hj⟩
    omega
  have hrω : r ∣ F * ω := odd_dvd_mul_omega2Exp hrodd hrk
  have hfd : orderOf t ∣ 2 ^ P.natDegree - 1 :=
    orderOf_t_dvd_two_pow_sub_one t P hmon hpos hdvd hfaith e he
  have hmod_f : (2 : ℕ) ^ P.natDegree ≡ 1 [MOD orderOf t] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hfd).symm
  obtain ⟨c, hc⟩ := hrω
  have hexp : F * (ω * 2 ^ a) = P.natDegree * c := by
    rw [hfar, show F * (ω * 2 ^ a) = (F * ω) * 2 ^ a by ring, hc]
    ring
  have hmod : (2 : ℕ) ^ (F * (ω * 2 ^ a)) ≡ 1 [MOD orderOf t] := by
    calc (2 : ℕ) ^ (F * (ω * 2 ^ a)) = ((2 : ℕ) ^ P.natDegree) ^ c := by rw [hexp, pow_mul]
      _ ≡ 1 ^ c [MOD orderOf t] := hmod_f.pow c
      _ = 1 := one_pow c
  have hWt : t ^ 2 ^ (F * (ω * 2 ^ a)) = t := by
    simpa using
      pow_eq_pow_iff_modEq.mpr (show 2 ^ (F * (ω * 2 ^ a)) ≡ 1 [MOD orderOf t] from hmod)
  set W := powOmega2 s ^ 2 ^ a with hWdef
  have hWs : W = s ^ (ω * 2 ^ a) := by rw [hWdef, hU, ← pow_mul]
  have hconjW : W⁻¹ * t * W = t := by
    rw [hWs, inv_pow_conj_pow s t hrel, hWt]
  have hcomm_t : t * W = W * t := by
    calc t * W = W * (W⁻¹ * t * W) := by group
      _ = W * t := by rw [hconjW]
  have hcomm_s : s * W = W * s := by
    rw [hWs]
    exact ((Commute.refl s).pow_right _).eq
  have hcentral : ∀ g : C, g * W = W * g := by
    intro g
    have hg : g ∈ Subgroup.closure ({s, t} : Set C) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact hcomm_s
      · rw [Set.mem_singleton_iff] at hx'
        subst hx'
        exact hcomm_t
    | one => rw [one_mul, mul_one]
    | mul x y hx hy ihx ihy => exact Commute.mul_left ihx ihy
    | inv x hx ih => exact Commute.inv_left ih
  set Wfix : AddSubgroup V :=
    { carrier := {v : V | W • v = v}
      zero_mem' := smul_zero W
      add_mem' := fun {u₁ u₂} h1 h2 => by
        show W • (u₁ + u₂) = u₁ + u₂
        rw [smul_add, show W • u₁ = u₁ from h1, show W • u₂ = u₂ from h2]
      neg_mem' := fun {u} h => by
        show W • (-u) = -u
        rw [smul_neg, show W • u = u from h] } with hWfixdef
  have hstab : ∀ g : C, ∀ w ∈ Wfix, g • w ∈ Wfix := by
    intro g w hw
    show W • (g • w) = g • w
    rw [← mul_smul, ← hcentral g, mul_smul, show W • w = w from hw]
  have hWorder : orderOf W ∣ 2 ^ (k.factorization 2) := by
    refine dvd_trans ?_ (FoxH.orderOf_powOmega2_dvd_two_pow s)
    exact orderOf_dvd_of_pow_eq_one
      (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
  have hcardV : Nat.card V = 2 ^ (P.natDegree * sV) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, card_adjoinRoot P hmon,
      Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have heven : 2 ∣ Nat.card V := by
    rw [hcardV]
    exact dvd_pow_self 2 (Nat.mul_ne_zero (by omega) (by omega))
  letI : DistribMulAction ↥(Subgroup.zpowers W) V :=
    DistribMulAction.compHom V (Subgroup.zpowers W).subtype
  haveI : Fintype ↥(Subgroup.zpowers W) := Fintype.ofFinite _
  have hp2 : IsPGroup 2 ↥(Subgroup.zpowers W) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hWorder
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  haveI : Fintype ↥(MulAction.fixedPoints ↥(Subgroup.zpowers W) V) := Fintype.ofFinite _
  have hmod2 := hp2.card_modEq_card_fixedPoints V
  have h0mem : (0 : V) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers W) V := fun g => smul_zero g
  have h2dvd : 2 ∣ Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers W) V) := by
    have hV2 : Nat.card V ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr heven
    exact (Nat.modEq_zero_iff_dvd).mp (hmod2.symm.trans hV2)
  have hgt : 1 < Fintype.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers W) V) := by
    rw [← Nat.card_eq_fintype_card]
    have hge1 : 1 ≤ Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers W) V) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨⟨0, h0mem⟩⟩, inferInstance⟩)
    obtain ⟨c', hc'⟩ := h2dvd
    omega
  obtain ⟨x₀, hx₀⟩ := Fintype.exists_ne_of_one_lt_card hgt ⟨0, h0mem⟩
  have hwfix : W • (x₀ : V) = (x₀ : V) := x₀.2 ⟨W, Subgroup.mem_zpowers _⟩
  have hwne : (x₀ : V) ≠ 0 := fun h => hx₀ (Subtype.ext h)
  rcases hsimple Wfix hstab with hbot | htop
  · exact absurd (show (x₀ : V) ∈ Wfix from hwfix)
      (by rw [hbot]; exact fun hmem => hwne (AddSubgroup.mem_bot.mp hmem))
  · exact hfaith W fun v => show v ∈ Wfix from htop ▸ AddSubgroup.mem_top v

/-- **The Frobenius fixed-space count `#V^U = 2^{r·s_V}`** at the general two-power tame
relation `s⁻¹ t s = t^{2^F}` with `F` **odd**.  Generalizes
`RamifiedPack.card_fixed_powOmega2` (`F = 1`).

`F` odd is used twice and is sharp: it makes the descended twist `Frob^{F·ω}` still have order
exactly `2^a` (odd `F·ω` and `r ∣ F·ω`), and it forces `2^a ∣ orderOf s`, without which
`ω₂(orderOf s)` need not be odd.  At `F = 2` the conclusion is false — see
`GQ2/Dyadic/Instances/GammaLSourceArfGeneral.lean`. -/
theorem card_fixed_powOmega2_pow [Finite C] [Finite V] (s : C) {F : ℕ} (hFodd : Odd F)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2 ^ F)
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hmon : P.Monic) (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {a r : ℕ} (hr : Odd r) (ha : 1 ≤ a) (hfar : P.natDegree = 2 ^ a * r)
    {sV : ℕ} (hsV : 1 ≤ sV) (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    Nat.card {v : V // powOmega2 s • v = v} = 2 ^ (r * sV) := by
  classical
  have hpos : 0 < orderOf t := orderOf_pos t
  have hdeg : 0 < P.natDegree := by
    rw [hfar]
    exact Nat.mul_pos (Nat.two_pow_pos a) hr.pos
  set k := orderOf s with hk
  have hkpos : 0 < k := orderOf_pos s
  set ω := omega2Exp k with hω
  set U := powOmega2 s with hUdef
  have hU : U = s ^ ω := rfl
  have htk : t ^ 2 ^ (F * k) = t ^ 1 := by
    have h1 := inv_pow_conj_pow s t hrel k
    rw [show s ^ k = 1 from pow_orderOf_eq_one s, inv_one, one_mul, mul_one] at h1
    simpa using h1.symm
  have hxk : AdjoinRoot.root P ^ 2 ^ (F * k) = AdjoinRoot.root P := by
    simpa using root_pow_eq_of_t_pow_eq t P htk hsV e he
  have hfk : P.natDegree ∣ F * k := natDegree_dvd_of_root_pow P hmon hdeg hxk
  have hrk : r ∣ F * k := dvd_trans ⟨2 ^ a, by rw [hfar]; ring⟩ hfk
  have hrodd : ¬(2 : ℕ) ∣ r := by
    rcases hr with ⟨j, hj⟩
    omega
  have hrω : r ∣ F * ω := odd_dvd_mul_omega2Exp hrodd hrk
  -- `F` odd moves the 2-part of `deg P` from `F · k` onto `k` itself
  have hFnd : ¬(2 : ℕ) ∣ F := by
    rcases hFodd with ⟨j, hj⟩
    omega
  have h2ak : (2 : ℕ) ^ a ∣ F * k :=
    dvd_trans (dvd_trans ⟨r, hfar⟩ (dvd_refl P.natDegree)) hfk
  have hcopF : Nat.Coprime (2 ^ a) F :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hFnd).pow_left a
  have h2k : (2 : ℕ) ∣ k :=
    dvd_trans (dvd_pow_self 2 (by omega : a ≠ 0)) (hcopF.dvd_of_dvd_mul_left h2ak)
  have hv2k : k.factorization 2 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hkpos.ne' h2k).ne'
  have hωodd : Odd ω := Nat.odd_iff.mpr
    ((omega2Exp_modEq_one hkpos.ne' hv2k).of_dvd (dvd_pow_self 2 hv2k))
  have hFωodd : Odd (F * ω) := hFodd.mul hωodd
  have hW1 : U ^ 2 ^ a = 1 :=
    powOmega2_pow_two_pow_eq_one_pow t P s hrel hfaith hsimple hgen hmon hdvd hr hfar hsV e he
  set σ := frobEquiv P hmon ^ (F * ω) with hσ
  have hord : orderOf σ = 2 ^ a := orderOf_frobEquiv_pow P hmon hdeg hFωodd hrω hfar
  set β : (Fin sV → AdjoinRoot P) ≃+ (Fin sV → AdjoinRoot P) :=
    (e.symm.trans (DistribMulAction.toAddEquiv V U⁻¹)).trans e with hβ
  have hβapp : ∀ w, β w = e (U⁻¹ • e.symm w) := fun w => rfl
  have hconj : ∀ v : V, U⁻¹ • (t • v) = (t ^ 2 ^ (F * ω)) • (U⁻¹ • v) := by
    intro v
    have h1 : U⁻¹ * t * U = t ^ 2 ^ (F * ω) := hU ▸ inv_pow_conj_pow s t hrel ω
    calc U⁻¹ • (t • v) = (U⁻¹ * t) • v := (mul_smul _ _ _).symm
      _ = (U⁻¹ * t * U * U⁻¹) • v := by
          rw [show U⁻¹ * t * U * U⁻¹ = U⁻¹ * t from by group]
      _ = (t ^ 2 ^ (F * ω) * U⁻¹) • v := by rw [h1]
      _ = (t ^ 2 ^ (F * ω)) • (U⁻¹ • v) := mul_smul _ _ _
  have hesymm_x : ∀ w : Fin sV → AdjoinRoot P,
      e.symm (AdjoinRoot.root P • w) = t • e.symm w := by
    intro w
    have h1 : e (t • e.symm w) = AdjoinRoot.root P • w := by
      funext j
      show e (t • e.symm w) j = (AdjoinRoot.root P • w) j
      rw [he (e.symm w) j, AddEquiv.apply_symm_apply]
      rfl
    rw [← h1, AddEquiv.symm_apply_apply]
  have hxcase : ∀ w, β (AdjoinRoot.root P • w) = σ (AdjoinRoot.root P) • β w := by
    intro w
    rw [hβapp, hβapp, hesymm_x, hconj]
    have h2 : ∀ v : V, e ((t ^ 2 ^ (F * ω)) • v)
        = (AdjoinRoot.root P ^ 2 ^ (F * ω)) • e v := by
      intro v
      funext j
      show e ((t ^ 2 ^ (F * ω)) • v) j = (AdjoinRoot.root P ^ 2 ^ (F * ω) • e v) j
      rw [equiv_pow_smul t P e he (2 ^ (F * ω)) v j]
      rfl
    rw [h2, hσ, frobEquiv_pow_apply']
  have hsemi := semilinear_of_root_case P σ β hxcase
  have hβord : (⇑β)^[2 ^ a] = id := by
    have hiter : ∀ (i : ℕ) (w : Fin sV → AdjoinRoot P),
        (⇑β)^[i] w = e ((U⁻¹) ^ i • e.symm w) := by
      intro i
      induction i with
      | zero =>
        intro w
        rw [Function.iterate_zero_apply, pow_zero, one_smul, AddEquiv.apply_symm_apply]
      | succ kk ihk =>
        intro w
        rw [Function.iterate_succ_apply', ihk, hβapp, AddEquiv.symm_apply_apply, ← mul_smul,
          ← pow_succ']
    funext w
    rw [hiter (2 ^ a) w, inv_pow, hW1, inv_one, one_smul, AddEquiv.apply_symm_apply]
    rfl
  have hfixiff : ∀ v : V, (U • v = v) ↔ β (e v) = e v := by
    intro v
    rw [hβapp, AddEquiv.symm_apply_apply]
    constructor
    · intro h
      rw [inv_smul_eq_iff.mpr h.symm]
    · intro h
      exact (inv_smul_eq_iff.mp (e.injective h)).symm
  have hcongr : Nat.card {v : V // U • v = v}
      = Nat.card {w : Fin sV → AdjoinRoot P // β w = w} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun v => hfixiff v))
  rw [hcongr, card_fixed_eq P σ β hmon hord hsemi hβord,
    card_fixedField_zpowers P hmon σ hord hfar, ← pow_mul]

end Counts

end GQ2.Dyadic.RamifiedPow
