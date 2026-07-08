import GQ2.FoxHeisenberg
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Separable

/-!
# P-16d6e4aA-P3 — the ramified isotypic pack (the étale route)

Blueprint: `docs/p16d6e4aA-pack-design.md`.  Target: the pack fields of
`SectionSix.prop_6_9_ramified`, discharging `zeroCount_qDouble_ramified_of_faithful`
(the ONE remaining sorry of the `Γ_A` Gauss lane).

This file builds the generic layer, bottom-up:

* §TwoPowerConj — **every conjugate of `t` is `t^{2^j}`** (the refinement of
  `tau_fixed_eq_zero_of_gen`'s conjugation calculus): the `S`-twist is squaring (the
  tame relation), its inverse is the square ROOT `t^{2^{φ(d)−1}}` (Euler — no
  multiplicative-order machinery), and the exponents compose multiplicatively.  This
  is what makes every `𝔽₂`-isotypic component `C`-stable
  (`P(t^{2^j}) = P(t)^{2^j}`, the char-2 polynomial Frobenius — design doc §3).
-/

namespace GQ2

namespace RamifiedPack

/-! ## §TwoPowerConj: conjugates of `t` are 2-power powers of `t` -/

section TwoPowerConj

variable {C : Type*} [Group C]

/-- Conjugation distributes over `ℕ`-powers (the `MulAut.conj`/`map_pow` massage). -/
theorem conj_pow_eq (z t : C) (N : ℕ) : z * t ^ N * z⁻¹ = (z * t * z⁻¹) ^ N := by
  have h := map_pow (MulAut.conj z) t N
  simpa [MulAut.conj_apply, mul_assoc] using h

/-- Conjugation distributes over `ℕ`-powers, inverse flavor. -/
theorem inv_conj_pow_eq (z t : C) (N : ℕ) : z⁻¹ * t ^ N * z = (z⁻¹ * t * z) ^ N := by
  have h := conj_pow_eq z⁻¹ t N
  rwa [inv_inv] at h

/-- The square-root step: if `x² = t` with `x` of the same odd order `d`, then
`x = t^{2^{φ(d)−1}}` — from Euler's `2^{φ(d)} ≡ 1 (mod d)`. -/
theorem eq_two_pow_of_sq_eq {t x : C} (hd : Odd (orderOf t)) (hpos : 0 < orderOf t)
    (horder : orderOf x = orderOf t) (hx2 : x ^ 2 = t) :
    x = t ^ 2 ^ (Nat.totient (orderOf t) - 1) := by
  have hcop : Nat.Coprime 2 (orderOf t) := by
    refine (Nat.prime_two.coprime_iff_not_dvd).mpr ?_
    rcases hd with ⟨k, hk⟩
    omega
  have htot : (2 : ℕ) ^ Nat.totient (orderOf t) ≡ 1 [MOD orderOf t] :=
    Nat.ModEq.pow_totient hcop
  have htotpos : 0 < Nat.totient (orderOf t) := Nat.totient_pos.mpr hpos
  have h1 : x ^ 2 ^ Nat.totient (orderOf t) = x := by
    have hiff : x ^ 2 ^ Nat.totient (orderOf t) = x ^ 1
        ↔ 2 ^ Nat.totient (orderOf t) ≡ 1 [MOD orderOf x] := pow_eq_pow_iff_modEq
    rw [horder] at hiff
    have h2 := hiff.mpr htot
    rwa [pow_one] at h2
  calc x = x ^ 2 ^ Nat.totient (orderOf t) := h1.symm
    _ = (x ^ 2) ^ 2 ^ (Nat.totient (orderOf t) - 1) := by
        rw [← pow_mul]
        congr 1
        obtain ⟨c, hc⟩ : ∃ c, Nat.totient (orderOf t) = c + 1 :=
          ⟨Nat.totient (orderOf t) - 1, by omega⟩
        rw [hc, Nat.add_sub_cancel, pow_succ]
        ring
    _ = t ^ 2 ^ (Nat.totient (orderOf t) - 1) := by rw [hx2]

/-- **Every element of `C = ⟨s, t⟩` conjugates `t` to a 2-power power of `t`** (both
directions): the `S`-twist is squaring (`hrel`), its inverse the Euler square root,
and exponents compose multiplicatively along the closure induction. -/
theorem conj_eq_two_pow (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
    (hodd : Odd (orderOf t)) (hpos : 0 < orderOf t) (g : C) :
    (∃ j : ℕ, g⁻¹ * t * g = t ^ 2 ^ j) ∧ (∃ j : ℕ, g * t * g⁻¹ = t ^ 2 ^ j) := by
  have hg : g ∈ Subgroup.closure ({s, t} : Set C) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · constructor
      · refine ⟨1, ?_⟩
        rw [hrel]
        norm_num
      · -- the square root `x t x⁻¹ = t^{2^{φ(d)−1}}`
        have hsc : SemiconjBy x t (x * t * x⁻¹) := by
          show x * t = x * t * x⁻¹ * x
          group
        have hx2 : (x * t * x⁻¹) ^ 2 = t := by
          have h2 : (x * t * x⁻¹) ^ 2 = x * t ^ 2 * x⁻¹ := by
            rw [pow_two, pow_two]
            group
          rw [h2, ← hrel]
          group
        exact ⟨Nat.totient (orderOf t) - 1,
          eq_two_pow_of_sq_eq hodd hpos hsc.orderOf_eq.symm hx2⟩
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      constructor
      · refine ⟨0, ?_⟩
        rw [show x⁻¹ * x * x = x from by group]
        norm_num
      · refine ⟨0, ?_⟩
        rw [show x * x * x⁻¹ = x from by group]
        norm_num
  | one =>
    constructor
    · refine ⟨0, ?_⟩
      rw [show (1 : C)⁻¹ * t * 1 = t from by group]
      norm_num
    · refine ⟨0, ?_⟩
      rw [show (1 : C) * t * 1⁻¹ = t from by group]
      norm_num
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

end TwoPowerConj

/-! ## §PolyFrobenius: the operator-level char-2 Frobenius and kernel stability

Design doc §3: for `P` over `𝔽₂`, `P(φ^{2^j}) = P(φ)^{2^j}` in the endomorphism
algebra (via `expand` + the trivial Frobenius of `ZMod 2`), so the kernel of `P(t̂)`
is stable under any `g` with `g⁻¹tg = t^{2^j}` — combined with §TwoPowerConj this
makes every isotypic component `C`-stable. -/

section PolyFrobenius

open Polynomial

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction C V]

/-- The action of `t : C` as a `ZMod 2`-linear endomorphism (any additive map is). -/
noncomputable def actEnd (t : C) : Module.End (ZMod 2) V :=
  AddMonoidHom.toZModLinearMap 2 (DistribMulAction.toAddMonoidHom V t)

@[simp] theorem actEnd_apply (t : C) (v : V) : actEnd (V := V) t v = t • v := rfl

/-- `actEnd` turns group powers into endomorphism powers. -/
theorem actEnd_pow (t : C) (n : ℕ) :
    actEnd (V := V) (t ^ n) = (actEnd (V := V) t) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    ext v
    rw [Module.End.one_apply]
    show (1 : C) • v = v
    exact one_smul _ v
  | succ k ih =>
    ext v
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    show (t ^ k * t) • v = actEnd (V := V) (t ^ k) (actEnd (V := V) t v)
    rw [mul_smul]
    rfl

/-- The `𝔽₂`-Frobenius is trivial, so `expand` by `2^j` is literally the `2^j`-th
power of the polynomial. -/
theorem expand_two_pow_eq_pow (P : Polynomial (ZMod 2)) (j : ℕ) :
    Polynomial.expand (ZMod 2) (2 ^ j) P = P ^ 2 ^ j := by
  have h := Polynomial.map_iterateFrobenius_expand (p := 2) P j
  have hid : iterateFrobenius (ZMod 2) 2 j = RingHom.id (ZMod 2) := by
    ext x
    rw [iterateFrobenius_def, RingHom.id_apply]
    have : ∀ (k : ℕ) (y : ZMod 2), y ^ 2 ^ k = y := by
      intro k
      induction k with
      | zero => intro y; rw [pow_zero, pow_one]
      | succ i ih =>
        intro y
        rw [pow_succ, pow_mul, ih, pow_two]
        revert y
        decide
    exact this j x
  rwa [hid, Polynomial.map_id] at h

/-- **The operator-level char-2 Frobenius**: evaluating `P` at the `2^j`-th power of an
endomorphism is the `2^j`-th power of the evaluation. -/
theorem aeval_pow_two_pow (φ : Module.End (ZMod 2) V) (P : Polynomial (ZMod 2)) (j : ℕ) :
    Polynomial.aeval (φ ^ 2 ^ j) P = (Polynomial.aeval φ P) ^ 2 ^ j := by
  calc Polynomial.aeval (φ ^ 2 ^ j) P
      = Polynomial.aeval φ (Polynomial.expand (ZMod 2) (2 ^ j) P) :=
        (Polynomial.expand_aeval _ _ _).symm
    _ = Polynomial.aeval φ (P ^ 2 ^ j) := by rw [expand_two_pow_eq_pow]
    _ = (Polynomial.aeval φ P) ^ 2 ^ j := map_pow _ _ _

/-- Polynomial evaluation transports across the group action by conjugating the
operator. -/
theorem aeval_actEnd_smul (t g : C) (P : Polynomial (ZMod 2)) (v : V) :
    Polynomial.aeval (actEnd (V := V) t) P (g • v)
      = g • (Polynomial.aeval (actEnd (V := V) (g⁻¹ * t * g)) P v) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq, smul_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    show (algebraMap (ZMod 2) (Module.End (ZMod 2) V) a * actEnd (V := V) t ^ n) (g • v)
      = g • ((algebraMap (ZMod 2) (Module.End (ZMod 2) V) a
          * actEnd (V := V) (g⁻¹ * t * g) ^ n) v)
    rw [Module.End.mul_apply, Module.End.mul_apply, ← actEnd_pow, ← actEnd_pow]
    show (algebraMap (ZMod 2) (Module.End (ZMod 2) V) a) ((t ^ n) • (g • v))
      = g • ((algebraMap (ZMod 2) (Module.End (ZMod 2) V) a) (((g⁻¹ * t * g) ^ n) • v))
    have hconj : (t ^ n) • (g • v) = g • (((g⁻¹ * t * g) ^ n) • v) := by
      rw [show (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g from by
          have h := conj_pow_eq g⁻¹ t n
          rw [inv_inv] at h
          exact h.symm,
        ← mul_smul, ← mul_smul]
      congr 1
      group
    rw [hconj]
    show a • (g • (((g⁻¹ * t * g) ^ n) • v)) = g • (a • (((g⁻¹ * t * g) ^ n) • v))
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl
    · rw [zero_smul, zero_smul, smul_zero]
    · rw [one_smul, one_smul]

/-- **Kernel stability** (design doc §3): if `g⁻¹tg = t^{2^j}` then the kernel of any
`P(t̂)` is `g`-stable — `P(t^{2^j}) = P(t)^{2^j}` and powers of a vanishing operator
vanish. -/
theorem smul_mem_ker_aeval {t g : C} {j : ℕ} (hconj : g⁻¹ * t * g = t ^ 2 ^ j)
    (P : Polynomial (ZMod 2)) (v : V)
    (hv : Polynomial.aeval (actEnd (V := V) t) P v = 0) :
    Polynomial.aeval (actEnd (V := V) t) P (g • v) = 0 := by
  rw [aeval_actEnd_smul, hconj, actEnd_pow, aeval_pow_two_pow]
  have hzero : ((Polynomial.aeval (actEnd (V := V) t) P) ^ 2 ^ j) v = 0 := by
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ j = k + 1 := ⟨2 ^ j - 1, by omega⟩
    rw [hk, pow_succ, Module.End.mul_apply, hv, map_zero]
  rw [hzero, smul_zero]

end PolyFrobenius

/-! ## §SingleIsotype: `V` is killed by ONE irreducible factor of `X^d − 1`

Design doc §2–3, with a lighter route than torsion-internal-decomposition: if every
irreducible-factor kernel were `⊥`, every `Q(t̂)` would be injective, so their product
`(X^d − 1)(t̂) = 0` would be injective on `V ≠ 0` — contradiction.  The nonzero kernel
is `C`-stable (§PolyFrobenius + §TwoPowerConj), so `hsimple` promotes it to `⊤`. -/

section SingleIsotype

open Polynomial

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction C V]

/-- A product of injective endomorphisms is injective (`List`-form — `Module.End` is
noncommutative, so no `Multiset.prod`). -/
theorem list_prod_injective (L : List (Module.End (ZMod 2) V))
    (h : ∀ f ∈ L, Function.Injective f) :
    Function.Injective (L.prod : Module.End (ZMod 2) V) := by
  induction L with
  | nil =>
    rw [List.prod_nil]
    intro a b hab
    rwa [Module.End.one_apply, Module.End.one_apply] at hab
  | cons f L ih =>
    rw [List.prod_cons]
    have hcomp : ⇑(f * L.prod) = ⇑f ∘ ⇑(L.prod) := rfl
    rw [show Function.Injective ⇑(f * L.prod)
        ↔ Function.Injective (⇑f ∘ ⇑(L.prod)) from by rw [hcomp]]
    exact (h f (List.mem_cons_self ..)).comp
      (ih fun g hg => h g (List.mem_cons_of_mem f hg))

/-- `(X^d − 1)(t̂) = 0` for `d := orderOf t`. -/
theorem aeval_X_pow_orderOf_sub_one (t : C) :
    Polynomial.aeval (actEnd (V := V) t) (X ^ orderOf t - 1 : Polynomial (ZMod 2)) = 0 := by
  rw [map_sub, map_one, map_pow, Polynomial.aeval_X, ← actEnd_pow, pow_orderOf_eq_one]
  ext v
  show (actEnd (V := V) 1 - (1 : Module.End (ZMod 2) V)) v = (0 : Module.End (ZMod 2) V) v
  rw [LinearMap.sub_apply, LinearMap.zero_apply, Module.End.one_apply]
  show (1 : C) • v - v = 0
  rw [one_smul, sub_self]

/-- **The single isotype** (design doc §2–3): with `C = ⟨s,t⟩`, `t` of odd order, and
`V` a nonzero simple `C`-module, there is ONE monic irreducible `P ∣ X^d − 1` with
`P(t̂) = 0` on all of `V`. -/
theorem exists_single_isotype [Finite V] (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
    (hodd : Odd (orderOf t)) (hpos : 0 < orderOf t)
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
  -- some normalized factor has a nonzero kernel
  have hfac : ∃ Q ∈ UniqueFactorizationMonoid.normalizedFactors
      (X ^ d - 1 : Polynomial (ZMod 2)),
      ∃ v : V, v ≠ 0 ∧ Polynomial.aeval (actEnd (V := V) t) Q v = 0 := by
    by_contra hcon
    push_neg at hcon
    have hinj : ∀ f ∈ (UniqueFactorizationMonoid.normalizedFactors
        (X ^ d - 1 : Polynomial (ZMod 2))).toList.map
          (fun Q => Polynomial.aeval (actEnd (V := V) t) Q),
        Function.Injective f := by
      intro f hf
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hf
      have hQmem := Multiset.mem_toList.mp hQ
      intro a b hab
      have hker : Polynomial.aeval (actEnd (V := V) t) Q (a - b) = 0 := by
        rw [map_sub, hab, sub_self]
      by_contra hne
      exact (hcon Q hQmem (a - b) (sub_ne_zero.mpr hne)) hker
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
  · -- monic: normalized factors over a field are monic
    have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQmem
    have hmon := Polynomial.monic_normalize (R := ZMod 2) hQne
    rwa [hnorm] at hmon
  · -- the kernel is a `C`-stable subgroup, nonzero at `v₀`, hence everything
    set K : AddSubgroup V :=
      { carrier := {v : V | Polynomial.aeval (actEnd (V := V) t) Q v = 0}
        zero_mem' := map_zero _
        add_mem' := fun {a b} ha hb => by
          show Polynomial.aeval (actEnd (V := V) t) Q (a + b) = 0
          rw [map_add]
          rw [show Polynomial.aeval (actEnd (V := V) t) Q a = 0 from ha,
            show Polynomial.aeval (actEnd (V := V) t) Q b = 0 from hb, add_zero]
        neg_mem' := fun {a} ha => by
          show Polynomial.aeval (actEnd (V := V) t) Q (-a) = 0
          rw [map_neg, show Polynomial.aeval (actEnd (V := V) t) Q a = 0 from ha,
            neg_zero] } with hK
    have hstab : ∀ g : C, ∀ w ∈ K, g • w ∈ K := fun g w hw => by
      obtain ⟨j, hj⟩ := (conj_eq_two_pow s t hgen hrel hodd hpos g).1
      exact smul_mem_ker_aeval hj Q w hw
    rcases hsimple K hstab with hbot | htop
    · exfalso
      have hmem : v₀ ∈ K := hv₀ker
      rw [hbot] at hmem
      exact hv₀ne (AddSubgroup.mem_bot.mp hmem)
    · intro v
      have hmem : v ∈ K := by rw [htop]; exact AddSubgroup.mem_top v
      exact hmem

end SingleIsotype

/-! ## §AdjoinRootStructure: `V` is a vector space over `D := AdjoinRoot P`

Design doc §2's payoff: with `P(t̂) = 0` on `V` (§SingleIsotype), `V` is a module over
`𝔽₂[X]/(P) = AdjoinRoot P` — a FIELD — so it is automatically free: `V ≃ D^s`, with
`t` acting as the scalar `root P`.  No Maschke, no complements. -/

section AdjoinRootStructure

open Polynomial

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction C V]

/-- `#(AdjoinRoot P) = 2^{deg P}` for monic `P` over `𝔽₂` (the power basis). -/
theorem card_adjoinRoot (P : Polynomial (ZMod 2)) (hmon : P.Monic) :
    Nat.card (AdjoinRoot P) = 2 ^ P.natDegree := by
  classical
  have hbasis := AdjoinRoot.powerBasisAux' hmon
  rw [Nat.card_congr (hbasis.equivFun).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun]
  simp

/-- **The free `D`-structure** (design doc §2): with `P` monic irreducible killing `t̂`
on `V`, there is an additive equivalence `e : V ≃+ (Fin s → AdjoinRoot P)`, `s ≥ 1`,
under which `t` acts as multiplication by `root P` in every coordinate. -/
theorem exists_isotypic_equiv [Finite V] (t : C) (P : Polynomial (ZMod 2))
    (hirr : Irreducible P)
    (hkill : ∀ v : V, Polynomial.aeval (actEnd (V := V) t) P v = 0)
    (hVne : ∃ v : V, v ≠ 0) :
    ∃ (s : ℕ) (e : V ≃+ (Fin s → AdjoinRoot P)),
      1 ≤ s ∧ ∀ (v : V) (j : Fin s),
        e (t • v) j = AdjoinRoot.root P * e v j := by
  classical
  letI instP : Module (Polynomial (ZMod 2)) V :=
    Module.compHom V (Polynomial.aeval (actEnd (V := V) t)).toRingHom
  haveI hfact := Fact.mk hirr
  have htors : Module.IsTorsionBySet (Polynomial (ZMod 2)) V
      ((Ideal.span {P} : Ideal (Polynomial (ZMod 2))) : Set (Polynomial (ZMod 2))) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    intro v
    show (Polynomial.aeval (actEnd (V := V) t)) P v = 0
    exact hkill v
  letI instD : Module (AdjoinRoot P) V := htors.module
  haveI : Module.Finite (AdjoinRoot P) V := Module.Finite.of_finite
  refine ⟨Module.finrank (AdjoinRoot P) V,
    (Module.finBasis (AdjoinRoot P) V).equivFun.toAddEquiv, ?_, ?_⟩
  · -- `s ≥ 1`: a zero-dimensional space is a subsingleton, contradicting `hVne`
    by_contra hs
    push_neg at hs
    have hzero : Module.finrank (AdjoinRoot P) V = 0 := by omega
    haveI := Module.finrank_zero_iff.mp hzero
    obtain ⟨v, hv⟩ := hVne
    exact hv (Subsingleton.elim v 0)
  · -- `t` acts as the scalar `root P`
    intro v j
    have hroot_smul : (AdjoinRoot.root P) • v = t • v := by
      show (Polynomial.aeval (actEnd (V := V) t)) X v = t • v
      rw [Polynomial.aeval_X]
      rfl
    have hmap := (Module.finBasis (AdjoinRoot P) V).equivFun.map_smul
      (AdjoinRoot.root P) v
    show (Module.finBasis (AdjoinRoot P) V).equivFun (t • v) j
      = AdjoinRoot.root P * (Module.finBasis (AdjoinRoot P) V).equivFun v j
    rw [← hroot_smul, hmap, Pi.smul_apply, smul_eq_mul]

end AdjoinRootStructure

end RamifiedPack

end GQ2
