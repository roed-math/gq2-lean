import GQ2.FoxHeisenberg
import GQ2.QuadraticFp2
import GQ2.TameSimple
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

/-! ## §PackInterface: the `⟨t⟩`-module structure on `Wt := AdjoinRoot P`

The pack-facing layer (design doc §0's field shapes): the `Subgroup.zpowers t`-action on
`D := AdjoinRoot P` by root-multiplication (`rootAction`, through the choice-exponent hom
`zpowHom : ⟨t⟩ →* Dˣ` — well-defined because `root P ^ orderOf t = 1`), the char-2 field
`hWt2` (`adjoinRoot_add_self`), simplicity `hWtsimple` (`isSimpleModTwo_rootAction`: a
`t`-stable additive subgroup of `D = 𝔽₂[root P]` is a `D`-subspace of the line), and the
pack-shaped equivariance `he` (`equiv_zpowers_smul`, upgrading `exists_isotypic_equiv`'s
per-coordinate root-equivariance). -/

section PackInterface

open Polynomial

variable {C : Type*} [Group C] (t : C) (P : Polynomial (ZMod 2))

/-- Char 2 on `AdjoinRoot P`: every element is 2-torsion (the `hWt2` pack field). -/
theorem adjoinRoot_add_self (w : AdjoinRoot P) : w + w = 0 := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [← map_add, show g + g = 0 from by
    ext i
    simp [CharTwo.add_self_eq_zero], map_zero]

/-- Every element of `⟨t⟩` is a ℕ-power of `t` (finite order: reduce the ℤ-exponent
mod `orderOf t`). -/
theorem exists_pow_eq (hpos : 0 < orderOf t) (σ : ↥(Subgroup.zpowers t)) :
    ∃ n : ℕ, (σ : C) = t ^ n := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
  have hd0 : ((orderOf t : ℤ)) ≠ 0 := by exact_mod_cast hpos.ne'
  have htd : t ^ ((orderOf t : ℤ)) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  have hnn : 0 ≤ k % (orderOf t : ℤ) := Int.emod_nonneg k hd0
  refine ⟨(k % (orderOf t : ℤ)).toNat, ?_⟩
  have hsplit : t ^ k = t ^ (k % (orderOf t : ℤ)) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k (orderOf t : ℤ)]
    rw [zpow_add, zpow_mul, htd, one_zpow, one_mul]
  rw [← hk, hsplit, ← zpow_natCast, Int.toNat_of_nonneg hnn]

/-- The choice exponent of an element of `⟨t⟩`: `(σ : C) = t ^ powExp t hpos σ`. -/
noncomputable def powExp (hpos : 0 < orderOf t) (σ : ↥(Subgroup.zpowers t)) : ℕ :=
  (exists_pow_eq t hpos σ).choose

theorem powExp_spec (hpos : 0 < orderOf t) (σ : ↥(Subgroup.zpowers t)) :
    (σ : C) = t ^ powExp t hpos σ :=
  (exists_pow_eq t hpos σ).choose_spec

/-- `root P ^ orderOf t = 1` from `P ∣ X^{orderOf t} − 1` (via `AdjoinRoot.mk_eq_zero`). -/
theorem root_pow_orderOf (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    AdjoinRoot.root P ^ orderOf t = 1 := by
  have h0 : AdjoinRoot.mk P (X ^ orderOf t - 1 : Polynomial (ZMod 2)) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr hdvd
  rw [map_sub, map_one, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h0
  exact h0

variable {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- ℕ-power upgrade of `exists_isotypic_equiv`'s per-coordinate root-equivariance. -/
theorem equiv_pow_smul {s : ℕ} (e : V ≃+ (Fin s → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin s), e (t • v) j = AdjoinRoot.root P * e v j)
    (n : ℕ) (v : V) (j : Fin s) :
    e ((t ^ n) • v) j = AdjoinRoot.root P ^ n * e v j := by
  induction n generalizing v with
  | zero => rw [pow_zero, one_smul, pow_zero, one_mul]
  | succ k ih => rw [pow_succ, mul_smul, ih, he v j, pow_succ, mul_assoc]

variable [Fact (Irreducible P)]

/-- The root is nonzero (else `0 = root^{orderOf t} = 1`). -/
theorem root_ne_zero (hpos : 0 < orderOf t) (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    AdjoinRoot.root P ≠ 0 := by
  intro h
  have h1 := root_pow_orderOf t P hdvd
  rw [h, zero_pow hpos.ne'] at h1
  exact zero_ne_one h1

/-- The root as a unit of the field `AdjoinRoot P`. -/
noncomputable def rootUnit (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) : (AdjoinRoot P)ˣ :=
  Units.mk0 (AdjoinRoot.root P) (root_ne_zero t P hpos hdvd)

@[simp] theorem rootUnit_val (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    ((rootUnit t P hpos hdvd : (AdjoinRoot P)ˣ) : AdjoinRoot P) = AdjoinRoot.root P := rfl

theorem rootUnit_pow_orderOf (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    rootUnit t P hpos hdvd ^ orderOf t = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, rootUnit_val, root_pow_orderOf t P hdvd, Units.val_one]

/-- Well-definedness core: equal `t`-powers give equal `rootUnit`-powers
(`orderOf rootUnit ∣ orderOf t`, then `pow_eq_pow_iff_modEq` both ways). -/
theorem rootUnit_pow_congr (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {m n : ℕ} (h : t ^ m = t ^ n) :
    rootUnit t P hpos hdvd ^ m = rootUnit t P hpos hdvd ^ n := by
  have hord : orderOf (rootUnit t P hpos hdvd) ∣ orderOf t :=
    orderOf_dvd_iff_pow_eq_one.mpr (rootUnit_pow_orderOf t P hpos hdvd)
  exact pow_eq_pow_iff_modEq.mpr ((pow_eq_pow_iff_modEq.mp h).of_dvd hord)

/-- The `⟨t⟩ →* Dˣ` hom `t^k ↦ root^k` (choice-exponent; well-defined by
`rootUnit_pow_congr`). -/
noncomputable def zpowHom (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    ↥(Subgroup.zpowers t) →* (AdjoinRoot P)ˣ where
  toFun σ := rootUnit t P hpos hdvd ^ powExp t hpos σ
  map_one' := by
    show rootUnit t P hpos hdvd ^ powExp t hpos 1 = 1
    have h : t ^ powExp t hpos (1 : ↥(Subgroup.zpowers t)) = t ^ 0 := by
      rw [← powExp_spec t hpos 1, OneMemClass.coe_one, pow_zero]
    rw [rootUnit_pow_congr t P hpos hdvd h, pow_zero]
  map_mul' σ τ := by
    show rootUnit t P hpos hdvd ^ powExp t hpos (σ * τ)
      = rootUnit t P hpos hdvd ^ powExp t hpos σ * rootUnit t P hpos hdvd ^ powExp t hpos τ
    have h : t ^ powExp t hpos (σ * τ) = t ^ (powExp t hpos σ + powExp t hpos τ) := by
      rw [← powExp_spec t hpos (σ * τ), pow_add, ← powExp_spec t hpos σ,
        ← powExp_spec t hpos τ]
      rfl
    rw [rootUnit_pow_congr t P hpos hdvd h, pow_add]

theorem zpowHom_of_pow (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {σ : ↥(Subgroup.zpowers t)} {n : ℕ} (hσ : (σ : C) = t ^ n) :
    zpowHom t P hpos hdvd σ = rootUnit t P hpos hdvd ^ n := by
  show rootUnit t P hpos hdvd ^ powExp t hpos σ = rootUnit t P hpos hdvd ^ n
  refine rootUnit_pow_congr t P hpos hdvd ?_
  rw [← powExp_spec t hpos σ, hσ]

/-- **The `⟨t⟩`-module structure on `Wt := AdjoinRoot P`** (the pack instance argument):
`t^k` acts as multiplication by `root P ^ k`.  Consumers `letI` it. -/
@[reducible] noncomputable def rootAction (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    DistribMulAction ↥(Subgroup.zpowers t) (AdjoinRoot P) :=
  DistribMulAction.compHom (AdjoinRoot P) (zpowHom t P hpos hdvd)

/-- Computation rule for `rootAction` at a ℕ-power presentation of `σ`. -/
theorem rootAction_smul_of_pow (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {σ : ↥(Subgroup.zpowers t)} {n : ℕ} (hσ : (σ : C) = t ^ n) (w : AdjoinRoot P) :
    letI := rootAction t P hpos hdvd
    σ • w = AdjoinRoot.root P ^ n * w := by
  letI := rootAction t P hpos hdvd
  show ((zpowHom t P hpos hdvd σ : (AdjoinRoot P)ˣ) : AdjoinRoot P) * w = _
  rw [zpowHom_of_pow t P hpos hdvd hσ, Units.val_pow_eq_pow_val, rootUnit_val]

/-- The generator acts as root-multiplication. -/
theorem rootAction_gen_smul (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) (w : AdjoinRoot P) :
    letI := rootAction t P hpos hdvd
    (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) • w = AdjoinRoot.root P * w := by
  letI := rootAction t P hpos hdvd
  have h := rootAction_smul_of_pow t P hpos hdvd
    (σ := ⟨t, Subgroup.mem_zpowers t⟩) (n := 1) (by rw [pow_one]) w
  rwa [pow_one] at h

/-- **`Wt` is a simple `⟨t⟩`-module** (the `hWtsimple` pack field): a `t`-stable additive
subgroup of `D = 𝔽₂[root P]` is stable under multiplication by every `mk P g`, hence a
`D`-subspace of the line `D` — so `⊥` or `⊤`. -/
theorem isSimpleModTwo_rootAction (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) :
    letI := rootAction t P hpos hdvd
    FoxH.IsSimpleModTwo ↥(Subgroup.zpowers t) (AdjoinRoot P) := by
  letI := rootAction t P hpos hdvd
  refine ⟨inferInstance, fun W hW => ?_⟩
  -- root-stability from the generator
  have hroot : ∀ w ∈ W, AdjoinRoot.root P * w ∈ W := fun w hw => by
    have h := hW ⟨t, Subgroup.mem_zpowers t⟩ w hw
    rwa [rootAction_gen_smul t P hpos hdvd w] at h
  -- polynomial upgrade: `mk P g * w ∈ W`
  have hpoly : ∀ (g : Polynomial (ZMod 2)), ∀ w ∈ W, AdjoinRoot.mk P g * w ∈ W := by
    intro g
    induction g using Polynomial.induction_on' with
    | add p q hp hq =>
      intro w hw
      rw [map_add, add_mul]
      exact W.add_mem (hp w hw) (hq w hw)
    | monomial n a =>
      intro w hw
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl
      · rw [Polynomial.monomial_zero_right, map_zero, zero_mul]
        exact W.zero_mem
      · rw [← Polynomial.X_pow_eq_monomial, map_pow, AdjoinRoot.mk_X]
        induction n with
        | zero =>
          rw [pow_zero, one_mul]
          exact hw
        | succ k ih =>
          rw [pow_succ', mul_assoc]
          exact hroot _ ih
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr ((AddSubgroup.eq_top_iff' W).mpr fun x => ?_)
    obtain ⟨w₀, hw₀W, hw₀ne⟩ : ∃ w₀ ∈ W, w₀ ≠ (0 : AdjoinRoot P) := by
      by_contra hcon
      refine h ((AddSubgroup.eq_bot_iff_forall W).mpr fun y hy => ?_)
      by_cases hy0 : y = 0
      · exact hy0
      · exact absurd ⟨y, hy, hy0⟩ hcon
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x * w₀⁻¹)
    have hx := hpoly g w₀ hw₀W
    rw [hg, mul_assoc, inv_mul_cancel₀ hw₀ne, mul_one] at hx
    exact hx

/-- **The pack-shaped equivariance `he`**: the per-coordinate root-equivariance of
`exists_isotypic_equiv` upgrades to full `⟨t⟩`-equivariance for the `rootAction`
module structure on `Wt` — `prop_6_9_ramified`'s `he` field verbatim. -/
theorem equiv_zpowers_smul (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {s : ℕ} (e : V ≃+ (Fin s → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin s), e (t • v) j = AdjoinRoot.root P * e v j) :
    letI := rootAction t P hpos hdvd
    ∀ (σ : ↥(Subgroup.zpowers t)) (v : V) (j : Fin s), e ((σ : C) • v) j = σ • e v j := by
  letI := rootAction t P hpos hdvd
  intro σ v j
  obtain ⟨n, hn⟩ := exists_pow_eq t hpos σ
  rw [hn, equiv_pow_smul t P e he n v j, rootAction_smul_of_pow t P hpos hdvd hn]

end PackInterface

/-! ## §SelfReciprocity: `f = deg P` is EVEN (design doc §4)

The nonsingular `t`-invariant polar pairing makes the `t̂`-adjoint `t̂⁻¹`, so `P(t̂) = 0`
forces `P(t̂⁻¹) = 0` (A); transported through the isotypic equivalence this says `x⁻¹` is a
root of `P` in `D = 𝔽₂[x]`, `x := root P` (B); the induced `𝔽₂`-algebra involution
`x ↦ x⁻¹` of `D` is a genuine order-2 element of `Aut(D/𝔽₂)` (nontrivial since `x ≠ 1` —
the ramified exclusion of `P = X + 1`), and `#Aut(D/𝔽₂) = f` (finite fields are Galois:
`GaloisField.instIsGaloisOfFinite`), so Lagrange gives `2 ∣ f` (C).  The numerology
`f = 2^a·r`, `a ≥ 1`, `r` odd then feeds the pack's `hWcard` shape. -/

section SelfReciprocity

open Polynomial QuadraticFp2

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction C V]

omit [Module (ZMod 2) V] in
/-- Invariance of `q` under `t` extends to all powers. -/
theorem q_pow_smul {t : C} {q : V → ZMod 2} (hqt : ∀ v, q (t • v) = q v) (n : ℕ) (v : V) :
    q ((t ^ n) • v) = q v := by
  induction n generalizing v with
  | zero => rw [pow_zero, one_smul]
  | succ k ih => rw [pow_succ, mul_smul, ih (t • v), hqt v]

omit [Module (ZMod 2) V] in
/-- **The adjoint shift**: for `g` preserving `q`, the polar pairing trades `g` on the left
for `g⁻¹` on the right. -/
theorem polar_smul_left_inv {g : C} {q : V → ZMod 2} (hqg : ∀ v, q (g • v) = q v)
    (w v : V) : polar q (g • w) v = polar q w (g⁻¹ • v) := by
  have hinv : ∀ a b : V, polar q (g • a) (g • b) = polar q a b := by
    intro a b
    unfold polar
    rw [← smul_add, hqg, hqg, hqg]
  calc polar q (g • w) v = polar q (g • w) (g • (g⁻¹ • v)) := by rw [smul_inv_smul]
    _ = polar q w (g⁻¹ • v) := hinv w (g⁻¹ • v)

/-- **(A) the operator-adjoint identity**: `B(P(t̂)w, v) = B(w, P(t̂⁻¹)v)` for the polar
pairing of a `t`-invariant quadratic map. -/
theorem polar_aeval_actEnd (t : C) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqt : ∀ v, q (t • v) = q v) (Q : Polynomial (ZMod 2)) (w v : V) :
    polar q (Polynomial.aeval (actEnd (V := V) t) Q w) v
      = polar q w (Polynomial.aeval (actEnd (V := V) t⁻¹) Q v) := by
  induction Q using Polynomial.induction_on' with
  | add p q' hp hq' =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hq.polar_add_left, hp, hq',
      ← hq.polar_add_right]
  | monomial n a =>
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl
    · rw [Polynomial.monomial_zero_right, map_zero, map_zero]
      have h0l : polar q ((0 : Module.End (ZMod 2) V) w) v = 0 := by
        show polar q 0 v = 0
        unfold polar
        rw [zero_add, hq.map_zero, add_zero]
        exact CharTwo.add_self_eq_zero _
      have h0r : polar q w ((0 : Module.End (ZMod 2) V) v) = 0 := by
        show polar q w 0 = 0
        unfold polar
        rw [add_zero, hq.map_zero, add_zero]
        exact CharTwo.add_self_eq_zero _
      rw [h0l, h0r]
    · rw [← Polynomial.X_pow_eq_monomial, map_pow, map_pow, Polynomial.aeval_X,
        Polynomial.aeval_X, ← actEnd_pow, ← actEnd_pow]
      show polar q ((t ^ n) • w) v = polar q w ((t⁻¹ ^ n) • v)
      rw [inv_pow, polar_smul_left_inv (q_pow_smul hqt n) w v]

/-- **(A) closed**: `P(t̂) = 0` forces `P(t̂⁻¹) = 0` (nonsingularity kills the orthogonal
complement of everything). -/
theorem aeval_actEnd_inv_eq_zero (t : C) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (hqt : ∀ v, q (t • v) = q v)
    {P : Polynomial (ZMod 2)} (hkill : ∀ v : V, Polynomial.aeval (actEnd (V := V) t) P v = 0)
    (v : V) : Polynomial.aeval (actEnd (V := V) t⁻¹) P v = 0 := by
  by_contra h0
  obtain ⟨w, hw⟩ := hns _ h0
  refine hw ?_
  rw [polar_comm]
  have h := polar_aeval_actEnd t q hq hqt P w v
  rw [hkill w] at h
  rw [← h]
  unfold polar
  rw [zero_add, hq.map_zero, add_zero]
  exact CharTwo.add_self_eq_zero _

variable (t : C) (P : Polynomial (ZMod 2))

omit [Module (ZMod 2) V] in
/-- Generalized ℕ-power transport (any group element acting per-coordinate as a fixed
scalar). -/
theorem equiv_pow_smul_gen (g : C) (x : AdjoinRoot P) {s : ℕ}
    (e : V ≃+ (Fin s → AdjoinRoot P))
    (hge : ∀ (v : V) (j : Fin s), e (g • v) j = x * e v j) (n : ℕ) (v : V) (j : Fin s) :
    e ((g ^ n) • v) j = x ^ n * e v j := by
  induction n generalizing v with
  | zero => rw [pow_zero, one_smul, pow_zero, one_mul]
  | succ k ih => rw [pow_succ, mul_smul, ih, hge v j, pow_succ, mul_assoc]

variable [Fact (Irreducible P)]

/-- **(B) transport to `D`**: `P(t̂⁻¹) = 0` on `V ≅ D^s` (`s ≥ 1`) evaluates, on the
first basis vector, to `P(x⁻¹) = 0` in `D`. -/
theorem aeval_root_inv_eq_zero (hroot0 : AdjoinRoot.root P ≠ 0)
    {s : ℕ} (hs : 1 ≤ s) (e : V ≃+ (Fin s → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin s), e (t • v) j = AdjoinRoot.root P * e v j)
    (hkill' : ∀ v : V, Polynomial.aeval (actEnd (V := V) t⁻¹) P v = 0) :
    Polynomial.aeval (AdjoinRoot.root P)⁻¹ P = 0 := by
  classical
  -- the inverse acts per-coordinate as `x⁻¹`
  have he_inv : ∀ (v : V) (j : Fin s), e (t⁻¹ • v) j = (AdjoinRoot.root P)⁻¹ * e v j := by
    intro v j
    have h := he (t⁻¹ • v) j
    rw [smul_inv_smul] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hroot0, one_mul]
  -- polynomial transport through `e`
  have hpoly : ∀ (Q : Polynomial (ZMod 2)) (v : V) (j : Fin s),
      e (Polynomial.aeval (actEnd (V := V) t⁻¹) Q v) j
        = Polynomial.aeval (AdjoinRoot.root P)⁻¹ Q * e v j := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      intro v j
      rw [map_add, LinearMap.add_apply, map_add, Pi.add_apply, hp, hq, map_add, add_mul]
    | monomial n a =>
      intro v j
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl
      · rw [Polynomial.monomial_zero_right, map_zero, map_zero]
        show e ((0 : Module.End (ZMod 2) V) v) j = 0 * e v j
        rw [LinearMap.zero_apply, map_zero, Pi.zero_apply, zero_mul]
      · rw [← Polynomial.X_pow_eq_monomial, map_pow, map_pow, Polynomial.aeval_X,
          Polynomial.aeval_X, ← actEnd_pow]
        show e ((t⁻¹ ^ n) • v) j = (AdjoinRoot.root P)⁻¹ ^ n * e v j
        exact equiv_pow_smul_gen P t⁻¹ (AdjoinRoot.root P)⁻¹ e he_inv n v j
  -- evaluate at the first basis vector
  set j₀ : Fin s := ⟨0, hs⟩
  set v₀ : V := e.symm (Pi.single j₀ 1)
  have h := hpoly P v₀ j₀
  rw [hkill' v₀, map_zero, Pi.zero_apply] at h
  have hv₀ : e v₀ j₀ = 1 := by
    show e (e.symm (Pi.single j₀ 1)) j₀ = 1
    rw [AddEquiv.apply_symm_apply]
    exact Pi.single_eq_same j₀ 1
  rw [hv₀, mul_one] at h
  exact h.symm

/-- **(C) `f` is even**: the involution `x ↦ x⁻¹` of `D = AdjoinRoot P` (an `𝔽₂`-algebra
automorphism since `x⁻¹` is again a root of `P`) has order 2 in `Aut(D/𝔽₂)` when `x ≠ 1`,
and finite fields are Galois, so `2 ∣ #Aut = finrank = natDegree P`. -/
theorem even_natDegree_of_aeval_inv_eq_zero (hmon : P.Monic)
    (hroot0 : AdjoinRoot.root P ≠ 0) (hroot1 : AdjoinRoot.root P ≠ 1)
    (h0 : Polynomial.aeval (AdjoinRoot.root P)⁻¹ P = 0) :
    Even P.natDegree := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hbasis := AdjoinRoot.powerBasisAux' hmon
  haveI hfinD : Finite (AdjoinRoot P) := Finite.of_equiv _ hbasis.equivFun.toEquiv.symm
  haveI : Module.Finite (ZMod 2) (AdjoinRoot P) := Module.Finite.of_basis hbasis
  -- the involution as an algebra automorphism
  have h0' : Polynomial.eval₂
      (↑(Algebra.ofId (ZMod 2) (AdjoinRoot P)) : ZMod 2 →+* AdjoinRoot P)
      (AdjoinRoot.root P)⁻¹ P = 0 := by
    rwa [show (↑(Algebra.ofId (ZMod 2) (AdjoinRoot P)) : ZMod 2 →+* AdjoinRoot P)
        = algebraMap (ZMod 2) (AdjoinRoot P) from rfl, ← Polynomial.aeval_def]
  set φA : AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId (ZMod 2) (AdjoinRoot P)) (AdjoinRoot.root P)⁻¹ h0'
    with hφA
  have hφAroot : φA (AdjoinRoot.root P) = (AdjoinRoot.root P)⁻¹ :=
    AdjoinRoot.liftAlgHom_root P (Algebra.ofId (ZMod 2) (AdjoinRoot P)) _ h0'
  have hbij : Function.Bijective φA :=
    Finite.injective_iff_bijective.mp (RingHom.injective (φA : AdjoinRoot P →+* AdjoinRoot P))
  set φ : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P := AlgEquiv.ofBijective φA hbij with hφ
  have hφroot : φ (AdjoinRoot.root P) = (AdjoinRoot.root P)⁻¹ := hφAroot
  -- order exactly 2
  have hφne : φ ≠ 1 := by
    intro h
    have hr : (AdjoinRoot.root P)⁻¹ = AdjoinRoot.root P := by
      rw [← hφroot, h]; rfl
    have hsq : AdjoinRoot.root P * AdjoinRoot.root P = 1 := by
      nth_rewrite 2 [← hr]
      exact mul_inv_cancel₀ hroot0
    have h2 : (1 : AdjoinRoot P) + 1 = 0 := adjoinRoot_add_self P 1
    have hfac : (AdjoinRoot.root P - 1) * (AdjoinRoot.root P + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact hroot1 (sub_eq_zero.mp hc)
    · refine hroot1 ?_
      have := eq_neg_of_add_eq_zero_left hc
      rw [this, neg_eq_of_add_eq_zero_left h2]
  have hφsq : φ * φ = 1 := by
    have hroot2 : ((φ * φ).toAlgHom : AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P)
        (AdjoinRoot.root P)
        = ((1 : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P).toAlgHom :
            AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P) (AdjoinRoot.root P) := by
      show φ (φ (AdjoinRoot.root P)) = AdjoinRoot.root P
      rw [hφroot, map_inv₀, hφroot, inv_inv]
    have hAlg := AdjoinRoot.algHom_ext hroot2
    exact AlgEquiv.ext fun x => DFunLike.congr_fun hAlg x
  have hord : orderOf φ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφsq) hφne
  -- Lagrange in the Galois group (`card_aut_eq_finrank` is `Nat.card`-valued)
  have hdvd : orderOf φ ∣ Nat.card (AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P) :=
    orderOf_dvd_natCard φ
  rw [hord, IsGalois.card_aut_eq_finrank,
    Module.finrank_eq_card_basis hbasis, Fintype.card_fin] at hdvd
  exact even_iff_two_dvd.mpr hdvd

/-- The pack numerology: an even nonzero `f` is `2^a · r` with `a ≥ 1` and `r` odd. -/
theorem exists_two_pow_mul_odd {f : ℕ} (hf0 : f ≠ 0) (hfe : Even f) :
    ∃ a r : ℕ, 1 ≤ a ∧ Odd r ∧ f = 2 ^ a * r := by
  refine ⟨f.factorization 2, ordCompl[2] f, ?_, ?_, ?_⟩
  · exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hf0 (even_iff_two_dvd.mp hfe)
  · have hnd := Nat.not_dvd_ordCompl Nat.prime_two hf0
    exact Nat.odd_iff.mpr (by omega)
  · exact (Nat.mul_div_cancel' (Nat.ordProj_dvd f 2)).symm

end SelfReciprocity

/-! ## §UKill: `U^{2^a} = 1` for `U := powOmega2 s` (design doc §5, common first step)

The 2-primary part `U = s^{ω₂}` of `s`, raised to `2^a`, centralizes `t` — the twist exponent
`2^{ω·2^a}` is `≡ 1 (mod orderOf t)` because `f = deg P ∣ ω·2^a` (via `f ∣ orderOf s` from the
Frobenius order on `D`, and `r ∣ ω` from the `ω₂ ≡ 0`-on-odd-part congruence) and
`orderOf t ∣ 2^f − 1` (Lagrange in `Dˣ`).  Commuting with both generators makes `U^{2^a}`
central; its fixed space is then a nonzero `C`-submodule (the 2-group fixed-point count), so
simplicity + faithfulness kill it. -/

section UKill

open Polynomial

variable {C : Type*} [Group C]

/-- Iterating the tame twist: `(s^n)⁻¹ t s^n = t^{2^n}`. -/
theorem inv_pow_conj (s t : C) (hrel : s⁻¹ * t * s = t ^ 2) (n : ℕ) :
    (s ^ n)⁻¹ * t * s ^ n = t ^ 2 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, inv_one, one_mul, mul_one, pow_one]
  | succ m ih =>
    rw [pow_succ s m]
    calc (s ^ m * s)⁻¹ * t * (s ^ m * s)
        = s⁻¹ * ((s ^ m)⁻¹ * t * s ^ m) * s := by group
      _ = s⁻¹ * t ^ 2 ^ m * s := by rw [ih]
      _ = (s⁻¹ * t * s) ^ 2 ^ m := inv_conj_pow_eq s t (2 ^ m)
      _ = (t ^ 2) ^ 2 ^ m := by rw [hrel]
      _ = t ^ 2 ^ (m + 1) := by
          rw [← pow_mul, show 2 * 2 ^ m = 2 ^ (m + 1) from (pow_succ' 2 m).symm]

variable {V : Type*} [AddCommGroup V] [DistribMulAction C V]
variable (t : C) (P : Polynomial (ZMod 2))

/-- Equal `t`-powers pin equal root-powers (evaluate the isotypic equivalence on the first
basis vector). -/
theorem root_pow_eq_of_t_pow_eq {m n : ℕ} (ht : t ^ m = t ^ n) {sV : ℕ} (hsV : 1 ≤ sV)
    (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    AdjoinRoot.root P ^ m = AdjoinRoot.root P ^ n := by
  classical
  set j₀ : Fin sV := ⟨0, hsV⟩
  set v₀ : V := e.symm (Pi.single j₀ 1)
  have hv₀ : e v₀ j₀ = 1 := by
    show e (e.symm (Pi.single j₀ 1)) j₀ = 1
    rw [AddEquiv.apply_symm_apply]
    exact Pi.single_eq_same j₀ 1
  have h1 := equiv_pow_smul t P e he m v₀ j₀
  have h2 := equiv_pow_smul t P e he n v₀ j₀
  rw [ht, h2, hv₀, mul_one, mul_one] at h1
  exact h1.symm

/-- Equal root-powers pin equal `t`-powers (via faithfulness through the equivalence). -/
theorem t_pow_eq_of_root_pow_eq (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    {m n : ℕ} (hx : AdjoinRoot.root P ^ m = AdjoinRoot.root P ^ n) {sV : ℕ}
    (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    t ^ m = t ^ n := by
  have hsmul : ∀ v : V, (t ^ m) • v = (t ^ n) • v := by
    intro v
    refine e.injective (funext fun j => ?_)
    rw [equiv_pow_smul t P e he m v j, equiv_pow_smul t P e he n v j, hx]
  have hg : ∀ v : V, ((t ^ n)⁻¹ * t ^ m) • v = v := by
    intro v
    rw [mul_smul, hsmul v, inv_smul_smul]
  have h1 := hfaith _ hg
  rw [inv_mul_eq_one] at h1
  exact h1.symm

/-- With a faithful action, the root has the same order as `t`. -/
theorem orderOf_root_eq (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2))) {sV : ℕ}
    (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    orderOf (AdjoinRoot.root P) = orderOf t := by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (root_pow_orderOf t P hdvd))
    (orderOf_dvd_of_pow_eq_one ?_)
  have hx : AdjoinRoot.root P ^ orderOf (AdjoinRoot.root P) = AdjoinRoot.root P ^ 0 := by
    rw [pow_orderOf_eq_one, pow_zero]
  have := t_pow_eq_of_root_pow_eq t P hfaith hx e he
  rwa [pow_zero] at this

variable [Fact (Irreducible P)]

omit [Fact (Irreducible P)] in
/-- `AdjoinRoot P` of a monic polynomial over `𝔽₂` is finite. -/
theorem finite_adjoinRoot (hmon : P.Monic) : Finite (AdjoinRoot P) :=
  Finite.of_equiv _ (AdjoinRoot.powerBasisAux' hmon).equivFun.toEquiv.symm

/-- The Frobenius square map as an `𝔽₂`-algebra endomorphism of `AdjoinRoot P`
(hand-rolled: char 2 makes squaring additive via `adjoinRoot_add_self`). -/
noncomputable def frobAlg : AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P where
  toFun y := y ^ 2
  map_one' := one_pow 2
  map_mul' a b := mul_pow a b 2
  map_zero' := zero_pow (by norm_num)
  map_add' a b := by
    have h : (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + a * b) := by ring
    rw [h, adjoinRoot_add_self P (a * b), add_zero]
  commutes' r := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) r with rfl | rfl
    · rw [map_zero]
      exact zero_pow (by norm_num)
    · rw [map_one]
      exact one_pow 2

/-- The Frobenius as an algebra automorphism (injective self-map of a finite field). -/
noncomputable def frobEquiv (hmon : P.Monic) :
    AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P :=
  haveI := finite_adjoinRoot P hmon
  AlgEquiv.ofBijective (frobAlg P)
    (Finite.injective_iff_bijective.mp
      (RingHom.injective ((frobAlg P : AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P) :
        AdjoinRoot P →+* AdjoinRoot P)))

@[simp] theorem frobEquiv_apply (hmon : P.Monic) (y : AdjoinRoot P) :
    frobEquiv P hmon y = y ^ 2 := rfl

theorem frobEquiv_pow_apply (hmon : P.Monic) (m : ℕ) (y : AdjoinRoot P) :
    (frobEquiv P hmon ^ m) y = y ^ 2 ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ i ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, frobEquiv_apply, ← pow_mul,
      show 2 ^ i * 2 = 2 ^ (i + 1) from (pow_succ 2 i).symm]

/-- **The Frobenius has order exactly `f = deg P`** in `Aut(D/𝔽₂)`: Lagrange bounds it by `f`
(`#Aut = f`, Galois), and `φ^m = 1` makes all `2^f` elements roots of `X^{2^m} − X`, so
`f ≤ m`. -/
theorem orderOf_frobEquiv (hmon : P.Monic) (hdeg : 0 < P.natDegree) :
    orderOf (frobEquiv P hmon) = P.natDegree := by
  classical
  haveI := finite_adjoinRoot P hmon
  haveI : Module.Finite (ZMod 2) (AdjoinRoot P) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasisAux' hmon)
  haveI : Finite (AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P) :=
    Finite.of_injective (fun ψ => (ψ : AdjoinRoot P → AdjoinRoot P)) DFunLike.coe_injective
  set m := orderOf (frobEquiv P hmon) with hm
  have hdvd_f : m ∣ P.natDegree := by
    have h := orderOf_dvd_natCard (frobEquiv P hmon)
    rwa [IsGalois.card_aut_eq_finrank,
      Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' hmon), Fintype.card_fin] at h
  have hmpos : 0 < m := orderOf_pos _
  have hfixall : ∀ y : AdjoinRoot P, y ^ 2 ^ m = y := by
    intro y
    have h1 : (frobEquiv P hmon ^ m) y = y := by
      rw [hm, pow_orderOf_eq_one]
      rfl
    rwa [frobEquiv_pow_apply] at h1
  haveI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : (2 : ℕ) ^ P.natDegree ≤ 2 ^ m := by
    set p : Polynomial (AdjoinRoot P) := X ^ 2 ^ m - X with hp
    have hdegp : p.natDegree = 2 ^ m := by
      have h2m : (1 : WithBot ℕ) < (2 ^ m : ℕ) := by
        exact_mod_cast Nat.one_lt_two_pow_iff.mpr (by omega)
      have hdeg' : p.degree = (2 ^ m : ℕ) := by
        rw [hp, Polynomial.degree_sub_eq_left_of_degree_lt
          (by rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact h2m),
          Polynomial.degree_X_pow]
      exact Polynomial.natDegree_eq_of_degree_eq_some hdeg'
    have hpne : p ≠ 0 := fun h0 => by
      rw [h0, Polynomial.natDegree_zero] at hdegp
      have := Nat.two_pow_pos m
      omega
    have hsub : (Finset.univ : Finset (AdjoinRoot P)) ⊆ p.roots.toFinset := by
      intro y _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne]
      show Polynomial.eval y p = 0
      rw [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hfixall y, sub_self]
    calc (2 : ℕ) ^ P.natDegree = Fintype.card (AdjoinRoot P) := by
          rw [← Nat.card_eq_fintype_card, card_adjoinRoot P hmon]
      _ = (Finset.univ : Finset (AdjoinRoot P)).card := Finset.card_univ.symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = 2 ^ m := hdegp
  have hle : P.natDegree ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  exact Nat.le_antisymm (Nat.le_of_dvd hdeg hdvd_f) hle

/-- A Frobenius power fixing the root fixes everything (`AdjoinRoot.algHom_ext`). -/
theorem frobEquiv_pow_eq_one_of_root (hmon : P.Monic) {m : ℕ}
    (hx : AdjoinRoot.root P ^ 2 ^ m = AdjoinRoot.root P) :
    frobEquiv P hmon ^ m = 1 := by
  have hroot : ((frobEquiv P hmon ^ m).toAlgHom :
        AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P) (AdjoinRoot.root P)
      = ((1 : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P).toAlgHom :
        AdjoinRoot P →ₐ[ZMod 2] AdjoinRoot P) (AdjoinRoot.root P) := by
    show (frobEquiv P hmon ^ m) (AdjoinRoot.root P) = AdjoinRoot.root P
    rw [frobEquiv_pow_apply]
    exact hx
  have hAlg := AdjoinRoot.algHom_ext hroot
  exact AlgEquiv.ext fun y => DFunLike.congr_fun hAlg y

/-- `f = deg P` divides any `m` with `x^{2^m} = x` (Frobenius order pinning). -/
theorem natDegree_dvd_of_root_pow (hmon : P.Monic) (hdeg : 0 < P.natDegree) {m : ℕ}
    (hx : AdjoinRoot.root P ^ 2 ^ m = AdjoinRoot.root P) : P.natDegree ∣ m := by
  have h2 : orderOf (frobEquiv P hmon) ∣ m :=
    orderOf_dvd_of_pow_eq_one (frobEquiv_pow_eq_one_of_root P hmon hx)
  rwa [orderOf_frobEquiv P hmon hdeg] at h2

/-- **Lagrange in `Dˣ`**: `orderOf t ∣ 2^f − 1`. -/
theorem orderOf_t_dvd_two_pow_sub_one (hmon : P.Monic) (hpos : 0 < orderOf t)
    (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1) {sV : ℕ}
    (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    orderOf t ∣ 2 ^ P.natDegree - 1 := by
  classical
  haveI := finite_adjoinRoot P hmon
  haveI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hxu : orderOf (rootUnit t P hpos hdvd) = orderOf t := by
    have h1 : orderOf ((rootUnit t P hpos hdvd : (AdjoinRoot P)ˣ) : AdjoinRoot P)
        = orderOf t := by
      rw [rootUnit_val]
      exact orderOf_root_eq t P hfaith hdvd e he
    exact orderOf_units.symm.trans h1
  have h2 := orderOf_dvd_natCard (rootUnit t P hpos hdvd)
  rw [hxu] at h2
  have h3 : Nat.card ((AdjoinRoot P)ˣ) = 2 ^ P.natDegree - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
      card_adjoinRoot P hmon]
  rwa [h3] at h2

/-- **`U^{2^a} = 1`** (design doc §5, the centrality kill): the `2^a`-th power of the
2-primary part `U = powOmega2 s` centralizes both generators, so its (nonzero) fixed space
is a `C`-submodule; simplicity and faithfulness force `U^{2^a} = 1`. -/
theorem powOmega2_pow_two_pow_eq_one [Finite C] [Finite V] (s : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hmon : P.Monic) (hdvd : P ∣ (X ^ orderOf t - 1 : Polynomial (ZMod 2)))
    {a r : ℕ} (hr : Odd r) (hfar : P.natDegree = 2 ^ a * r)
    {sV : ℕ} (hsV : 1 ≤ sV) (e : V ≃+ (Fin sV → AdjoinRoot P))
    (he : ∀ (v : V) (j : Fin sV), e (t • v) j = AdjoinRoot.root P * e v j) :
    powOmega2 s ^ 2 ^ a = 1 := by
  classical
  have hpos : 0 < orderOf t := orderOf_pos t
  have hdeg : 0 < P.natDegree := by
    rw [hfar]
    rcases hr with ⟨j, hj⟩
    exact Nat.mul_pos (Nat.two_pow_pos a) (by omega)
  set k := orderOf s with hk
  set ω := omega2Exp k with hω
  have hU : powOmega2 s = s ^ ω := rfl
  -- `t^{2^k} = t` from `s^k = 1`
  have htk : t ^ 2 ^ k = t ^ 1 := by
    have h1 := inv_pow_conj s t hrel k
    rw [show s ^ k = 1 from pow_orderOf_eq_one s, inv_one, one_mul, mul_one] at h1
    rw [pow_one]
    exact h1.symm
  -- transport to the root, pin `f ∣ k`
  have hxk : AdjoinRoot.root P ^ 2 ^ k = AdjoinRoot.root P := by
    have h := root_pow_eq_of_t_pow_eq t P htk hsV e he
    rwa [pow_one] at h
  have hfk : P.natDegree ∣ k := natDegree_dvd_of_root_pow P hmon hdeg hxk
  -- `r ∣ ω`
  have hrk : r ∣ k := dvd_trans ⟨2 ^ a, by rw [hfar]; ring⟩ hfk
  have hrodd : ¬(2 : ℕ) ∣ r := by
    rcases hr with ⟨j, hj⟩
    omega
  have hrω : r ∣ ω :=
    dvd_trans (Nat.dvd_ordCompl_of_dvd_not_dvd hrk hrodd) (oddPart_dvd_omega2Exp k)
  -- the twist exponent is trivial mod `orderOf t`
  have hfd : orderOf t ∣ 2 ^ P.natDegree - 1 :=
    orderOf_t_dvd_two_pow_sub_one t P hmon hpos hdvd hfaith e he
  have hmod_f : (2 : ℕ) ^ P.natDegree ≡ 1 [MOD orderOf t] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hfd).symm
  obtain ⟨c, hc⟩ := hrω
  have hexp : ω * 2 ^ a = P.natDegree * c := by
    rw [hc, hfar]
    ring
  have hmod : (2 : ℕ) ^ (ω * 2 ^ a) ≡ 1 [MOD orderOf t] := by
    calc (2 : ℕ) ^ (ω * 2 ^ a) = ((2 : ℕ) ^ P.natDegree) ^ c := by rw [hexp, pow_mul]
      _ ≡ 1 ^ c [MOD orderOf t] := hmod_f.pow c
      _ = 1 := one_pow c
  have hWt : t ^ 2 ^ (ω * 2 ^ a) = t := by
    have h := pow_eq_pow_iff_modEq.mpr (show 2 ^ (ω * 2 ^ a) ≡ 1 [MOD orderOf t] from hmod)
    rwa [pow_one] at h
  -- `W` commutes with the generators, hence is central
  set W := powOmega2 s ^ 2 ^ a with hWdef
  have hWs : W = s ^ (ω * 2 ^ a) := by rw [hWdef, hU, ← pow_mul]
  have hconjW : W⁻¹ * t * W = t := by
    rw [hWs, inv_pow_conj s t hrel, hWt]
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
    | mul x y hx hy ihx ihy =>
      calc x * y * W = x * (W * y) := by rw [mul_assoc, ihy]
        _ = W * (x * y) := by rw [← mul_assoc, ihx, mul_assoc]
    | inv x hx ih =>
      calc x⁻¹ * W = x⁻¹ * W * x * x⁻¹ := by group
        _ = x⁻¹ * (x * W) * x⁻¹ := by rw [mul_assoc x⁻¹ W x, ← ih]
        _ = W * x⁻¹ := by group
  -- the fixed subgroup of `W`
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
  -- the 2-group fixed-point device: a NONZERO fixed vector
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
  -- kill
  rcases hsimple Wfix hstab with hbot | htop
  · exact absurd (show (x₀ : V) ∈ Wfix from hwfix)
      (by rw [hbot]; exact fun hmem => hwne (AddSubgroup.mem_bot.mp hmem))
  · refine hfaith W fun v => ?_
    have hmem : v ∈ Wfix := by rw [htop]; exact AddSubgroup.mem_top v
    exact hmem

end UKill

/-! ## §DescentKit: the `D`-side inputs of the descent count (design doc §5, Route A)

For the twist `σ := frobEquiv^ω` (order `2^a`, since `gcd(ω, f) = r` for odd `ω` with
`r ∣ ω`): the fixed field `F := fixedField ⟨σ⟩` has exactly `2^r` elements (Artin's lemma
`finrank_fixedField_eq_card` + the card tower), and the **vector-valued Dedekind/Artin
independence** engine — a family annihilated by all twisted evaluations `Σᵢ σⁱ(y)•wᵢ = 0`
vanishes — which powers both halves of the `dim_F V^U = s` argument in §5b-ii. -/

section DescentKit

open Polynomial

variable (P : Polynomial (ZMod 2)) [Fact (Irreducible P)]

/-- **Vector-valued Artin independence**: if the powers `σ⁰, …, σ^{m−1}` are pairwise
distinct and `∑ i, σⁱ(y) • wᵢ = 0` for every scalar `y`, then every `wᵢ = 0`.
(Minimal-support descent: a second nonzero index is killed by the `μ`-twist difference
system; a single nonzero index dies at `y = 1`.) -/
theorem artin_vector {M : Type*} [AddCommGroup M] [Module (AdjoinRoot P) M]
    (σ : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P) {m : ℕ}
    (hdist : ∀ i < m, ∀ j < m, σ ^ i = σ ^ j → i = j)
    (w : ℕ → M)
    (h : ∀ y : AdjoinRoot P, ∑ i ∈ Finset.range m, (σ ^ i) y • w i = 0) :
    ∀ i ∈ Finset.range m, w i = 0 := by
  classical
  suffices H : ∀ N : ℕ, ∀ w : ℕ → M,
      ((Finset.range m).filter (fun i => w i ≠ 0)).card ≤ N →
      (∀ y : AdjoinRoot P, ∑ i ∈ Finset.range m, (σ ^ i) y • w i = 0) →
      ∀ i ∈ Finset.range m, w i = 0 from H _ w le_rfl h
  intro N
  induction N with
  | zero =>
    intro w hcard hsum i hi
    by_contra hne
    have hmem : i ∈ (Finset.range m).filter (fun l => w l ≠ 0) :=
      Finset.mem_filter.mpr ⟨hi, hne⟩
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ N ih =>
    intro w hcard hsum i hi
    by_contra hne
    by_cases hone : ∀ j ∈ Finset.range m, j ≠ i → w j = 0
    · -- singleton support: evaluate at `y = 1`
      have h1 := hsum 1
      rw [Finset.sum_eq_single i (fun j hj hji => by rw [hone j hj hji, smul_zero])
        (fun hnotmem => absurd hi hnotmem)] at h1
      rw [map_one, one_smul] at h1
      exact hne h1
    · -- a second nonzero index `j`
      obtain ⟨j, hj, hji, hjne⟩ : ∃ j ∈ Finset.range m, j ≠ i ∧ w j ≠ 0 := by
        by_contra hcon
        refine hone fun j hjm hji => ?_
        by_cases h0 : w j = 0
        · exact h0
        · exact absurd ⟨j, hjm, hji, h0⟩ hcon
      have hσne : σ ^ j ≠ σ ^ i := fun heq =>
        hji (hdist j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi) heq)
      obtain ⟨μ, hμ⟩ := DFunLike.ne_iff.mp hσne
      set w' : ℕ → M := fun l => ((σ ^ l) μ - (σ ^ i) μ) • w l with hw'
      have hsum' : ∀ y : AdjoinRoot P, ∑ l ∈ Finset.range m, (σ ^ l) y • w' l = 0 := by
        intro y
        have expand : ∀ l ∈ Finset.range m, (σ ^ l) y • w' l
            = (σ ^ l) (y * μ) • w l - (σ ^ i) μ • ((σ ^ l) y • w l) := by
          intro l _
          rw [hw']
          show (σ ^ l) y • (((σ ^ l) μ - (σ ^ i) μ) • w l) = _
          rw [smul_smul, mul_sub, sub_smul, map_mul,
            mul_comm ((σ ^ l) y) ((σ ^ i) μ), ← smul_smul, ← smul_smul]
        rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, ← Finset.smul_sum,
          hsum (y * μ), hsum y, smul_zero, sub_zero]
      have hw'i : w' i = 0 := by
        rw [hw']
        show ((σ ^ i) μ - (σ ^ i) μ) • w i = 0
        rw [sub_self, zero_smul]
      have hsupp : ((Finset.range m).filter (fun l => w' l ≠ 0)).card ≤ N := by
        have hsub : (Finset.range m).filter (fun l => w' l ≠ 0)
            ⊆ ((Finset.range m).filter (fun l => w l ≠ 0)).erase i := by
          intro l hl
          rw [Finset.mem_filter] at hl
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hl.1, ?_⟩⟩
          · rintro rfl
            exact hl.2 hw'i
          · intro h0
            refine hl.2 ?_
            rw [hw']
            show ((σ ^ l) μ - (σ ^ i) μ) • w l = 0
            rw [h0, smul_zero]
        have hicard : i ∈ (Finset.range m).filter (fun l => w l ≠ 0) :=
          Finset.mem_filter.mpr ⟨hi, hne⟩
        calc ((Finset.range m).filter (fun l => w' l ≠ 0)).card
            ≤ (((Finset.range m).filter (fun l => w l ≠ 0)).erase i).card :=
              Finset.card_le_card hsub
          _ = ((Finset.range m).filter (fun l => w l ≠ 0)).card - 1 :=
              Finset.card_erase_of_mem hicard
          _ ≤ N := by omega
      have hall := ih w' hsupp hsum' j hj
      rw [hw'] at hall
      have hscal : (σ ^ j) μ - (σ ^ i) μ ≠ 0 := sub_ne_zero.mpr hμ
      refine hjne ?_
      have h5 : ((σ ^ j) μ - (σ ^ i) μ)⁻¹ • (((σ ^ j) μ - (σ ^ i) μ) • w j) = 0 := by
        rw [show ((σ ^ j) μ - (σ ^ i) μ) • w j = 0 from hall, smul_zero]
      rwa [inv_smul_smul₀ hscal] at h5

/-- The twist `frobEquiv^ω` has order exactly `2^a` when `ω` is odd with `r ∣ ω`
(`gcd(f, ω) = r` at `f = 2^a·r`). -/
theorem orderOf_frobEquiv_pow (hmon : P.Monic) (hdeg : 0 < P.natDegree) {ω r aa : ℕ}
    (hωodd : Odd ω) (hrω : r ∣ ω) (hfar : P.natDegree = 2 ^ aa * r) :
    orderOf (frobEquiv P hmon ^ ω) = 2 ^ aa := by
  have hω0 : ω ≠ 0 := by
    rcases hωodd with ⟨c, hc⟩
    omega
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h
    · rw [h0, Nat.mul_zero] at hfar
      omega
    · exact h
  rw [orderOf_pow' _ hω0, orderOf_frobEquiv P hmon hdeg, hfar]
  have hcop : Nat.Coprime (2 ^ aa) ω := by
    refine Nat.Coprime.pow_left aa ?_
    refine Nat.prime_two.coprime_iff_not_dvd.mpr ?_
    rcases hωodd with ⟨c, hc⟩
    omega
  rw [Nat.Coprime.gcd_mul_left_cancel r hcop, Nat.gcd_eq_left hrω,
    Nat.mul_div_assoc _ (dvd_refl r), Nat.div_self hr0, mul_one]

/-- Membership in the fixed field of `⟨σ⟩` is fixedness under `σ` itself. -/
theorem mem_fixedField_zpowers_iff (σ : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P)
    (hσpos : 0 < orderOf σ) (y : AdjoinRoot P) :
    y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ σ y = y := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h σ (Subgroup.mem_zpowers σ)
  · intro hσy g hg
    obtain ⟨n, hn⟩ := exists_pow_eq σ hσpos (⟨g, hg⟩ : ↥(Subgroup.zpowers σ))
    have hgn : g = σ ^ n := hn
    rw [hgn]
    clear hgn hn hg
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ i ihn => rw [pow_succ', AlgEquiv.mul_apply, ihn, hσy]

/-- **The fixed field of the twist has `2^r` elements**: `[D : F] = #⟨σ⟩ = 2^a` (Artin) and
`#D = #F^{[D:F]}` pin `#F = 2^r` at `f = 2^a·r`. -/
theorem card_fixedField_zpowers (hmon : P.Monic) {aa r : ℕ}
    (σ : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P)
    (hord : orderOf σ = 2 ^ aa) (hfar : P.natDegree = 2 ^ aa * r) :
    Nat.card ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) = 2 ^ r := by
  haveI := finite_adjoinRoot P hmon
  haveI : Module.Finite (ZMod 2) (AdjoinRoot P) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasisAux' hmon)
  set F := IntermediateField.fixedField (Subgroup.zpowers σ) with hF
  haveI : Module.Finite ↥F (AdjoinRoot P) := Module.Finite.of_finite
  have h1 : Module.finrank ↥F (AdjoinRoot P) = 2 ^ aa := by
    rw [hF, IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hord]
  have h2 : Nat.card (AdjoinRoot P) = Nat.card ↥F ^ 2 ^ aa := by
    rw [← h1]
    exact Module.natCard_eq_pow_finrank
  rw [card_adjoinRoot P hmon, hfar] at h2
  have h4 : ((2 : ℕ) ^ r) ^ 2 ^ aa = Nat.card ↥F ^ 2 ^ aa := by
    rw [← pow_mul, mul_comm r (2 ^ aa), ← h2]
  exact (Nat.pow_left_injective (Nat.two_pow_pos aa).ne' h4).symm

end DescentKit

/-! ## §DescentCount: `#(fixed points of a σ-semilinear automorphism of D^n) = #F^n`

The abstract Route-A descent (design doc §5): for `β : AddAut (D^n)` that is `σ`-semilinear
(`β(y•w) = σ(y)•β(w)`) with `β^{2^a} = 1` and `σ` of order `2^a`, the fixed set of `β` is an
`F`-form of `D^n` — `F`-independent fixed vectors are `D`-independent (Dedekind shortening) and
the fixed set `D`-spans (the trace projector through the `artin_vector` engine on the quotient) —
so `#Fix(β) = #F^n`. -/

section DescentCount

open Polynomial

variable (P : Polynomial (ZMod 2)) [Fact (Irreducible P)]
variable {n : ℕ} (σ : AdjoinRoot P ≃ₐ[ZMod 2] AdjoinRoot P)
  (β : (Fin n → AdjoinRoot P) ≃+ (Fin n → AdjoinRoot P))

/-- Iterated semilinearity: `β^[i](y•w) = σⁱ(y)•β^[i](w)`. -/
theorem iterate_semilinear
    (hsemi : ∀ (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P), β (y • w) = σ y • β w)
    (i : ℕ) (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P) :
    (⇑β)^[i] (y • w) = (σ ^ i) y • (⇑β)^[i] w := by
  induction i generalizing y w with
  | zero => rw [Function.iterate_zero_apply, pow_zero]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, hsemi, ih, Function.iterate_succ_apply, pow_succ,
      AlgEquiv.mul_apply]

/-- Distinct powers of `σ` below its order. -/
theorem pow_ne_pow_of_orderOf {aa : ℕ} (hord : orderOf σ = 2 ^ aa) :
    ∀ i < 2 ^ aa, ∀ j < 2 ^ aa, σ ^ i = σ ^ j → i = j := by
  intro i hi j hj hij
  have hmod := pow_eq_pow_iff_modEq.mp hij
  rw [hord] at hmod
  have := Nat.ModEq.eq_of_lt_of_lt hmod hi hj
  exact this

/-- The `↥F`-scalar bridge on `D^n`: the subfield scalar acts as its coercion. -/
theorem coe_smul_fixedField (F : IntermediateField (ZMod 2) (AdjoinRoot P))
    (c : ↥F) (w : Fin n → AdjoinRoot P) : (↑c : AdjoinRoot P) • w = c • w := by
  have h := algebraMap_smul (AdjoinRoot P) c w
  rwa [show algebraMap ↥F (AdjoinRoot P) c = (↑c : AdjoinRoot P) from rfl] at h

/-- **The fixed set of `β` as an `↥F`-submodule** of `D^n` (`F := fixedField ⟨σ⟩`):
`σ`-fixed scalars pass through `β`. -/
def fixedSubmodule (hσpos : 0 < orderOf σ)
    (hsemi : ∀ (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P), β (y • w) = σ y • β w) :
    Submodule ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (Fin n → AdjoinRoot P) where
  carrier := {w | β w = w}
  zero_mem' := map_zero β
  add_mem' := fun {w₁ w₂} h1 h2 => by
    show β (w₁ + w₂) = w₁ + w₂
    rw [map_add, show β w₁ = w₁ from h1, show β w₂ = w₂ from h2]
  smul_mem' := fun c w hw => by
    show β (c • w) = c • w
    rw [← coe_smul_fixedField P _ c w, hsemi, show β w = w from hw,
      (mem_fixedField_zpowers_iff P σ hσpos _).mp c.2]

/-- **The Dedekind shortening**: `F`-independent `β`-fixed vectors are `D`-independent. -/
theorem linearIndependent_of_fixed (hσpos : 0 < orderOf σ)
    (hsemi : ∀ (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P), β (y • w) = σ y • β w)
    {ι : Type*} [Fintype ι] (v : ι → (Fin n → AdjoinRoot P))
    (hfix : ∀ i, β (v i) = v i)
    (hindF : LinearIndependent ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) v) :
    LinearIndependent (AdjoinRoot P) v := by
  classical
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ N : ℕ, ∀ g : ι → AdjoinRoot P,
      (Finset.univ.filter (fun j => g j ≠ 0)).card ≤ N →
      ∑ j, g j • v j = 0 → ∀ j, g j = 0 from fun g hg => H _ g le_rfl hg
  intro N
  induction N with
  | zero =>
    intro g hcard hsum j
    by_contra hne
    have hmem : j ∈ Finset.univ.filter (fun l => g l ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩
    have := Finset.card_pos.mpr ⟨j, hmem⟩
    omega
  | succ N ih =>
    intro g hcard hsum i
    by_contra hne
    -- normalize the `i`-coefficient to `1`
    set h : ι → AdjoinRoot P := fun j => (g i)⁻¹ * g j with hh
    have hsum2 : ∑ j, h j • v j = 0 := by
      have : ∑ j, h j • v j = (g i)⁻¹ • ∑ j, g j • v j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hh, smul_smul]
      rw [this, hsum, smul_zero]
    have hhi : h i = 1 := by
      rw [hh]
      exact inv_mul_cancel₀ hne
    -- apply `β`
    have happ : ∑ j, σ (h j) • v j = 0 := by
      have h0 := congrArg β hsum2
      rw [map_sum β (fun j => h j • v j) Finset.univ, map_zero β,
        Finset.sum_congr rfl (fun j _ => by
          show β (h j • v j) = σ (h j) • v j
          rw [hsemi, hfix j])] at h0
      exact h0
    -- subtract
    have hsub : ∑ j, (h j - σ (h j)) • v j = 0 := by
      have : ∀ j ∈ Finset.univ, (h j - σ (h j)) • v j = h j • v j - σ (h j) • v j :=
        fun j _ => sub_smul _ _ _
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hsum2, happ, sub_zero]
    -- the shrunk support
    have hsupp : (Finset.univ.filter (fun j => (h j - σ (h j)) ≠ 0)).card ≤ N := by
      have hsub' : Finset.univ.filter (fun j => (h j - σ (h j)) ≠ 0)
          ⊆ (Finset.univ.filter (fun j => g j ≠ 0)).erase i := by
        intro j hj
        rw [Finset.mem_filter] at hj
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩⟩
        · rintro rfl
          refine hj.2 ?_
          rw [hhi, map_one, sub_self]
        · intro h0
          refine hj.2 ?_
          rw [hh]
          show (g i)⁻¹ * g j - σ ((g i)⁻¹ * g j) = 0
          rw [h0, mul_zero, map_zero, sub_zero]
      have hicard : i ∈ Finset.univ.filter (fun j => g j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
      calc (Finset.univ.filter (fun j => (h j - σ (h j)) ≠ 0)).card
          ≤ ((Finset.univ.filter (fun j => g j ≠ 0)).erase i).card :=
            Finset.card_le_card hsub'
        _ = (Finset.univ.filter (fun j => g j ≠ 0)).card - 1 :=
            Finset.card_erase_of_mem hicard
        _ ≤ N := by omega
    have hall := ih (fun j => h j - σ (h j)) hsupp hsub
    -- every coefficient is `σ`-fixed, giving an `F`-dependency
    set F := IntermediateField.fixedField (Subgroup.zpowers σ) with hF
    have hmemF : ∀ j, h j ∈ F := by
      intro j
      rw [hF, mem_fixedField_zpowers_iff P σ hσpos]
      exact (sub_eq_zero.mp (hall j)).symm
    set c : ι → ↥F := fun j => ⟨h j, hmemF j⟩ with hc
    have hterm : ∀ j, c j • v j = h j • v j := by
      intro j
      have h1 := coe_smul_fixedField P F (c j) (v j)
      have h2 : ((c j : ↥F) : AdjoinRoot P) = h j := rfl
      rw [h2] at h1
      exact h1.symm
    have hFdep : ∑ j, c j • v j = 0 := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      exact hsum2
    have hczero := Fintype.linearIndependent_iff.mp hindF c hFdep i
    have : h i = 0 := by
      have := congrArg Subtype.val hczero
      exact this
    rw [hhi] at this
    exact one_ne_zero this

/-- **The fixed set `D`-spans** (the trace projector through the `artin_vector` engine on the
quotient): every vector lies in the `D`-span of the `β`-fixed set. -/
theorem span_fixed_eq_top {aa : ℕ} (hord : orderOf σ = 2 ^ aa)
    (hsemi : ∀ (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P), β (y • w) = σ y • β w)
    (hβord : (⇑β)^[2 ^ aa] = id) :
    Submodule.span (AdjoinRoot P) {w : Fin n → AdjoinRoot P | β w = w} = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro u
  set M := Submodule.span (AdjoinRoot P) {w : Fin n → AdjoinRoot P | β w = w} with hM
  -- the trace vectors are `β`-fixed
  have htrace : ∀ y : AdjoinRoot P,
      β (∑ i ∈ Finset.range (2 ^ aa), (σ ^ i) y • (⇑β)^[i] u)
        = ∑ i ∈ Finset.range (2 ^ aa), (σ ^ i) y • (⇑β)^[i] u := by
    intro y
    rw [map_sum β _ (Finset.range (2 ^ aa))]
    have hterm : ∀ i ∈ Finset.range (2 ^ aa),
        β ((σ ^ i) y • (⇑β)^[i] u) = (σ ^ (i + 1)) y • (⇑β)^[i + 1] u := by
      intro i _
      rw [hsemi, pow_succ', AlgEquiv.mul_apply, Function.iterate_succ_apply']
    rw [Finset.sum_congr rfl hterm]
    have hwrap : (σ ^ 2 ^ aa) y • (⇑β)^[2 ^ aa] u = (σ ^ 0) y • (⇑β)^[0] u := by
      rw [hβord, ← hord, pow_orderOf_eq_one, pow_zero, Function.iterate_zero]
    calc ∑ i ∈ Finset.range (2 ^ aa), (σ ^ (i + 1)) y • (⇑β)^[i + 1] u
        = (∑ i ∈ Finset.range (2 ^ aa + 1), (σ ^ i) y • (⇑β)^[i] u)
            - (σ ^ 0) y • (⇑β)^[0] u := by
          rw [Finset.sum_range_succ']
          abel
      _ = (∑ i ∈ Finset.range (2 ^ aa), (σ ^ i) y • (⇑β)^[i] u)
            + (σ ^ 2 ^ aa) y • (⇑β)^[2 ^ aa] u - (σ ^ 0) y • (⇑β)^[0] u := by
          rw [Finset.sum_range_succ]
      _ = ∑ i ∈ Finset.range (2 ^ aa), (σ ^ i) y • (⇑β)^[i] u := by
          rw [hwrap]
          abel
  -- kill all quotient classes via the engine
  have hker := artin_vector P σ (pow_ne_pow_of_orderOf P σ hord)
      (fun i => M.mkQ ((⇑β)^[i] u)) (fun y => by
    have hmem : (∑ i ∈ Finset.range (2 ^ aa), (σ ^ i) y • (⇑β)^[i] u) ∈ M := by
      rw [hM]
      exact Submodule.subset_span (htrace y)
    have h1 : M.mkQ (∑ i ∈ Finset.range (2 ^ aa), (σ ^ i) y • (⇑β)^[i] u) = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr hmem
    rw [map_sum M.mkQ _ (Finset.range (2 ^ aa)),
      Finset.sum_congr rfl (fun i _ => M.mkQ.map_smul ((σ ^ i) y) ((⇑β)^[i] u))] at h1
    exact h1)
  have h0 := hker 0 (Finset.mem_range.mpr (Nat.two_pow_pos aa))
  rw [Function.iterate_zero_apply, Submodule.mkQ_apply] at h0
  exact (Submodule.Quotient.mk_eq_zero M).mp h0

/-- **The descent count**: the fixed points of a `σ`-semilinear automorphism of `D^n` of
order dividing `2^a = orderOf σ` number exactly `#F^n`. -/
theorem card_fixed_eq (hmon : P.Monic) {aa : ℕ} (hord : orderOf σ = 2 ^ aa)
    (hsemi : ∀ (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P), β (y • w) = σ y • β w)
    (hβord : (⇑β)^[2 ^ aa] = id) :
    Nat.card {w : Fin n → AdjoinRoot P // β w = w}
      = Nat.card ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ^ n := by
  classical
  haveI := finite_adjoinRoot P hmon
  set F := IntermediateField.fixedField (Subgroup.zpowers σ) with hF
  have hσpos : 0 < orderOf σ := by
    rw [hord]
    exact Nat.two_pow_pos aa
  set Vfix := fixedSubmodule P σ β hσpos hsemi with hVfix
  haveI : Module.Finite ↥F ↥Vfix := Module.Finite.of_finite
  haveI : Module.Finite (AdjoinRoot P) (Fin n → AdjoinRoot P) := Module.Finite.of_finite
  set b := Module.finBasis ↥F ↥Vfix with hb
  set u := Module.finrank ↥F ↥Vfix with hu
  -- (≤) the coerced basis is `D`-independent
  have hind : LinearIndependent (AdjoinRoot P)
      (fun i : Fin u => ((b i : ↥Vfix) : Fin n → AdjoinRoot P)) := by
    refine linearIndependent_of_fixed P σ β hσpos hsemi _ (fun i => (b i).2) ?_
    exact b.linearIndependent.map' Vfix.subtype (Submodule.ker_subtype Vfix)
  have hle : u ≤ n := by
    have h1 := hind.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_fin_fun] at h1
  -- (≥) the coerced basis `D`-spans
  have hge : n ≤ u := by
    have hsub : {w : Fin n → AdjoinRoot P | β w = w} ⊆
        ↑(Submodule.span (AdjoinRoot P)
          (Set.range (fun i : Fin u => ((b i : ↥Vfix) : Fin n → AdjoinRoot P)))) := by
      intro w hw
      have hwmem : w ∈ Vfix := hw
      have hrepr := b.sum_repr ⟨w, hwmem⟩
      have hcoe := congrArg (Vfix.subtype) hrepr
      rw [map_sum Vfix.subtype _ Finset.univ] at hcoe
      have hterm : ∀ i ∈ Finset.univ, Vfix.subtype (b.repr ⟨w, hwmem⟩ i • b i)
          = ((b.repr ⟨w, hwmem⟩ i : AdjoinRoot P)) • ((b i : ↥Vfix) : Fin n → AdjoinRoot P) := by
        intro i _
        rw [map_smul]
        exact (coe_smul_fixedField P F (b.repr ⟨w, hwmem⟩ i) _).symm
      rw [Finset.sum_congr rfl hterm] at hcoe
      rw [show w = Vfix.subtype ⟨w, hwmem⟩ from rfl, ← hcoe]
      exact Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span (Set.mem_range_self i))
    have h2 : Submodule.span (AdjoinRoot P) {w : Fin n → AdjoinRoot P | β w = w}
        ≤ Submodule.span (AdjoinRoot P)
          (Set.range (fun i : Fin u => ((b i : ↥Vfix) : Fin n → AdjoinRoot P))) := by
      rw [Submodule.span_le]
      exact hsub
    rw [span_fixed_eq_top P σ β hord hsemi hβord] at h2
    have h3 : Submodule.span (AdjoinRoot P)
        (Set.range (fun i : Fin u => ((b i : ↥Vfix) : Fin n → AdjoinRoot P))) = ⊤ :=
      top_le_iff.mp h2
    have h4 := finrank_le_of_span_eq_top h3
    rwa [Module.finrank_fin_fun, Fintype.card_fin] at h4
  have huv : u = n := le_antisymm hle hge
  have hcount : Nat.card ↥Vfix = Nat.card ↥F ^ u := by
    rw [hu]
    exact Module.natCard_eq_pow_finrank
  rw [show Nat.card {w : Fin n → AdjoinRoot P // β w = w} = Nat.card ↥Vfix from
    Nat.card_congr (Equiv.subtypeEquivRight (fun w => Iff.rfl)), hcount, huv]

/-- Semilinearity follows from the root case (additive + polynomial bootstrap). -/
theorem semilinear_of_root_case
    (hx : ∀ w, β (AdjoinRoot.root P • w) = σ (AdjoinRoot.root P) • β w) :
    ∀ (y : AdjoinRoot P) (w : Fin n → AdjoinRoot P), β (y • w) = σ y • β w := by
  have hxn : ∀ (m : ℕ) (w : Fin n → AdjoinRoot P),
      β (AdjoinRoot.root P ^ m • w) = σ (AdjoinRoot.root P ^ m) • β w := by
    intro m
    induction m with
    | zero =>
      intro w
      rw [pow_zero, one_smul, map_one, one_smul]
    | succ mm ih =>
      intro w
      rw [pow_succ', mul_smul, hx, ih, smul_smul, ← map_mul]
  intro y w
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_smul, map_add β (AdjoinRoot.mk P p • w) (AdjoinRoot.mk P q • w), hp, hq,
      map_add σ (AdjoinRoot.mk P p) (AdjoinRoot.mk P q), add_smul]
  | monomial mm a' =>
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a' with rfl | rfl
    · rw [Polynomial.monomial_zero_right, map_zero]
      simp
    · rw [← Polynomial.X_pow_eq_monomial, map_pow, AdjoinRoot.mk_X]
      exact hxn mm w

end DescentCount

/-! ## §VUCount: the pack `hVU` — `#V^U = 2^{r·sV}` (design doc §5, assembled) -/

section VUCount

open Polynomial

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
variable (t : C) (P : Polynomial (ZMod 2)) [Fact (Irreducible P)]

/-- **The pack `hVU`**: at a faithful simple isotypic ramified tame action, the fixed
vectors of `U := powOmega2 s` number exactly `2^{r·sV}` — the σ-semilinear descent count
transported through the isotypic equivalence. -/
theorem card_fixed_powOmega2 [Finite C] [Finite V] (s : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
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
    rcases hr with ⟨j, hj⟩
    exact Nat.mul_pos (Nat.two_pow_pos a) (by omega)
  set k := orderOf s with hk
  have hkpos : 0 < k := orderOf_pos s
  set ω := omega2Exp k with hω
  set U := powOmega2 s with hUdef
  have hU : U = s ^ ω := rfl
  -- the divisibility replay (as in `powOmega2_pow_two_pow_eq_one`)
  have htk : t ^ 2 ^ k = t ^ 1 := by
    have h1 := inv_pow_conj s t hrel k
    rw [show s ^ k = 1 from pow_orderOf_eq_one s, inv_one, one_mul, mul_one] at h1
    rw [pow_one]
    exact h1.symm
  have hxk : AdjoinRoot.root P ^ 2 ^ k = AdjoinRoot.root P := by
    have h := root_pow_eq_of_t_pow_eq t P htk hsV e he
    rwa [pow_one] at h
  have hfk : P.natDegree ∣ k := natDegree_dvd_of_root_pow P hmon hdeg hxk
  have hrk : r ∣ k := dvd_trans ⟨2 ^ a, by rw [hfar]; ring⟩ hfk
  have hrodd : ¬(2 : ℕ) ∣ r := by
    rcases hr with ⟨j, hj⟩
    omega
  have hrω : r ∣ ω :=
    dvd_trans (Nat.dvd_ordCompl_of_dvd_not_dvd hrk hrodd) (oddPart_dvd_omega2Exp k)
  -- `ω` is odd
  have h2k : (2 : ℕ) ∣ k :=
    dvd_trans (dvd_trans (dvd_pow_self 2 (by omega : a ≠ 0)) ⟨r, hfar⟩) hfk
  have hv2k : k.factorization 2 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hkpos.ne' h2k).ne'
  have hωodd : Odd ω := by
    have h1 := omega2Exp_modEq_one hkpos.ne' hv2k
    have h2 : ω ≡ 1 [MOD 2] := h1.of_dvd (dvd_pow_self 2 hv2k)
    rw [Nat.odd_iff]
    unfold Nat.ModEq at h2
    omega
  -- `U^{2^a} = 1` (increment 5a)
  have hW1 : U ^ 2 ^ a = 1 :=
    powOmega2_pow_two_pow_eq_one t P s hgen hrel hfaith hsimple hmon hdvd hr hfar hsV e he
  -- the twist and its order
  set σ := frobEquiv P hmon ^ ω with hσ
  have hord : orderOf σ = 2 ^ a := orderOf_frobEquiv_pow P hmon hdeg hωodd hrω hfar
  -- the transported `U⁻¹`-action
  set β : (Fin sV → AdjoinRoot P) ≃+ (Fin sV → AdjoinRoot P) :=
    (e.symm.trans (DistribMulAction.toAddEquiv V U⁻¹)).trans e with hβ
  have hβapp : ∀ w, β w = e (U⁻¹ • e.symm w) := fun w => rfl
  -- semilinearity at the root
  have hconj : ∀ v : V, U⁻¹ • (t • v) = (t ^ 2 ^ ω) • (U⁻¹ • v) := by
    intro v
    have h1 : U⁻¹ * t * U = t ^ 2 ^ ω := by
      rw [hU]
      exact inv_pow_conj s t hrel ω
    calc U⁻¹ • (t • v) = (U⁻¹ * t) • v := (mul_smul _ _ _).symm
      _ = (U⁻¹ * t * U * U⁻¹) • v := by
          rw [show U⁻¹ * t * U * U⁻¹ = U⁻¹ * t from by group]
      _ = (t ^ 2 ^ ω * U⁻¹) • v := by rw [h1]
      _ = (t ^ 2 ^ ω) • (U⁻¹ • v) := mul_smul _ _ _
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
    have h2 : ∀ v : V, e ((t ^ 2 ^ ω) • v) = (AdjoinRoot.root P ^ 2 ^ ω) • e v := by
      intro v
      funext j
      show e ((t ^ 2 ^ ω) • v) j = (AdjoinRoot.root P ^ 2 ^ ω • e v) j
      rw [equiv_pow_smul t P e he (2 ^ ω) v j]
      rfl
    rw [h2, hσ, frobEquiv_pow_apply]
  have hsemi := semilinear_of_root_case P σ β hxcase
  -- the iterate order
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
  -- fixed-set transport
  have hfixiff : ∀ v : V, (U • v = v) ↔ β (e v) = e v := by
    intro v
    rw [hβapp, AddEquiv.symm_apply_apply]
    constructor
    · intro h
      have h2 : U⁻¹ • v = v := by
        conv_lhs => rw [← h]
        rw [inv_smul_smul]
      rw [h2]
    · intro h
      have h2 : U⁻¹ • v = v := e.injective h
      calc U • v = U • (U⁻¹ • v) := by rw [h2]
        _ = v := smul_inv_smul U v
  have hcongr : Nat.card {v : V // U • v = v}
      = Nat.card {w : Fin sV → AdjoinRoot P // β w = w} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun v => hfixiff v))
  rw [hcongr, card_fixed_eq P σ β hmon hord hsemi hβord,
    card_fixedField_zpowers P hmon σ hord hfar, ← pow_mul]

end VUCount

end RamifiedPack

end GQ2
