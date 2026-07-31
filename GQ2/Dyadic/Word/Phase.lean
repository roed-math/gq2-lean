/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.GaussCount.Wall
public import GQ2.OrbitData

@[expose] public section

/-!
# Dyadic campaign, ticket WW4 (phase half): the affine phase interface

The quadratic-form half of WW4 (board spec; **SD1 memo §6 is the ratified baseline** —
`docs/dyadic/sd-design.md`; packet §6 `lem:gauss-translate` / `cor:gauss-count` /
`def:affine-B4`).  Deliverables:

1. **Packet Lem 6.1** (`affine_gauss_translate`, SD1 §6.3's proposed signature): for a
   nonsingular quadratic form `Q` on a finite `𝔽₂`-module and a linear functional `ℓ`, there
   is a **unique polar representative** `y` (`ℓ = B_Q(·, y)`) and the shifted Gauss sum picks
   up exactly the affine phase: `Σ (−1)^{Q+ℓ} = (−1)^{Q(y)}·Σ (−1)^Q`.  Existence is a
   self-contained Fourier double count (`polar_rep_exists`) — no dual-space cardinality
   machinery; the only ingredients are `charSum_eq_zero` and nonsingularity.

2. **Packet Cor 6.2 in the shape the record leaves consume**: the `(dim, ε)`-classification
   and zero counts are delivered as *outputs of the certificate* (`baseSign_dichotomy`,
   `arf_eq_baseSign_iff`, `zeroCount_int_eq`), built **on** the frozen ℚ₂ templates
   `GQ2.QuadraticFp2.zeroCount_of_arf_zero/one` and `gaussSum_eq_pow`
   (`GQ2/GaussCount/Wall.lean`) — reused, not re-proved (the same templates LG5 consumes at
   `LocalGauss/Main.lean:406-439`).

3. **`PhaseCoverCertificate`** (SD1 §6.3's proposed fields, concretized): the per-branch
   affine-phase datum `baseDim`/`baseSign`/`gauss_eq`/`polar_id`/`kappa_id` (+ the §6.3
   comment "the module carries `#W = 2^{2·baseDim}`" made explicit as `card_eq`).  See the
   structure docstring for the exact mapping onto `def:affine-B4`'s three items and the §6.2
   obligation families, and for what is deliberately **not** here (ledger §3.4: no parallel
   B1–B4 record; the phase-cover conversion itself is the generic layer's
   `DeltaChi`/`shChi`/`keystone`/`phaseChi` machinery — nothing to prove, only to feed).

4. **The `SN`-matched degree-`n` Gauss outputs**: `gaussSum_pi` and its two sign-split
   corollaries produce exactly the `standardNumerics` shapes `2^{n·m}` (`SN.gaussRam m`) and
   `(−1)^n·2^{n·m}` (`SN.gaussUnram m`) from the certificate's `(baseSign, baseDim)` pair and
   the degree — no re-derived `2^…` literals for branch lanes to glue.

5. **The one-op normal-form family** `plusFormD d₀ q : (v, w) ↦ d₀(v) + B_q(v, w)` with its
   quadraticity, nonsingularity and Gauss sum (`= #V`, the `c₁`-Lagrangian computation).
   All four non-`L_sq` frozen rows' endpoints land in this family (freeze §§2–5): compact-N
   and compact-M(P=1) at `d₀ := q` (identity CoV), compact-M(P=0) via the block swap, the
   corrected-Npc row at `d₀ := npcQ0 ∘ L_c⁻¹` via the `L_c ⊕ 1` change of variables.  The
   certificate instantiations are `Hessian.lean` milestone 3.

## Row-5 satisfiability constraint (binding, SD1 §6.3)

Every field of `PhaseCoverCertificate` is instantiable from (i) the frozen row's endpoint
polynomial, (ii) a change-of-variables `LinearEquiv` with inverse witness, (iii) per-χ shift
vectors with their `Q`-values.  Nothing presupposes the WC-Mpc analysis: the certificate is
a **certificate input** (`HessianCertificate.affinePhase`), constructed by the WMP-c worker
for the frozen `R(M,pc)` when its lane runs — the shift-vector data enters only through the
*output* lemma `gauss_translate (y)`, which consumes a raw vector and its `Q`-value.

## Axiom prints (recorded at commit time)

Every headline prints **exactly the standard three** (`propext`, `Classical.choice`,
`Quot.sound`) — verified via `#print axioms` for `affine_gauss_translate`,
`polar_rep_exists`, `gaussSum_add_polar`, `gaussSum_prod_add`, `gaussSum_pi_sum`,
`gaussSum_plusFormD`, `nonsingular_plusFormD`, `isQuadraticFp2_plusFormD`,
`PhaseCoverCertificate.gauss_translate`, `PhaseCoverCertificate.gaussSum_pi`,
`PhaseCoverCertificate.baseSign_dichotomy`, `PhaseCoverCertificate.zeroCount_int_eq`.
No sorries, no new axioms; all `decide`s are kernel `decide`s over `𝔽₂` case splits.

Module-style: both imports are module-style.
-/

namespace GQ2.Dyadic

open GQ2.QuadraticFp2

/-! ## `𝔽₂` sign and polar helpers -/

section Helpers

variable {W : Type*} [AddCommGroup W]

/-- Any nonzero element of `𝔽₂` is `1`. -/
theorem zmod2_ne_zero_eq_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases ZMod.eq_zero_or_eq_one a with h0 | h1
  · exact absurd h0 h
  · exact h1

/-- `sign` as the exponential character `(−1)^{val}` — the spelling of packet Lem 6.1's
right-hand side. -/
theorem sign_eq_neg_one_pow_val (a : ZMod 2) : sign a = (-1 : ℤ) ^ a.val := by
  revert a; decide

/-- The polar form of a quadratic map vanishes on `0` in the first slot. -/
theorem polar_zero_left (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q) (w : W) :
    polar Q 0 w = 0 := by
  have h := hq.polar_add_left 0 0 w
  rw [add_zero] at h
  have key : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
  exact key _ h

/-- The polar form of a quadratic map vanishes on `0` in the second slot. -/
theorem polar_zero_right (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q) (v : W) :
    polar Q v 0 = 0 := by
  rw [polar_comm]
  exact polar_zero_left Q hq v

end Helpers

/-! ## Transport along additive maps and equivalences

The change-of-variables toolkit for `HessianCertificate`: quadraticity, nonsingularity, the
Gauss sum and the zero count all transport along the CoV.  Stated for raw additive data to
avoid hom-class friction at instantiation sites. -/

section Transport

variable {W W' : Type*} [AddCommGroup W] [AddCommGroup W']

/-- The polar form of a precomposition with an additive map. -/
theorem polar_comp (Q : W' → ZMod 2) (f : W → W') (hf : ∀ a b, f (a + b) = f a + f b)
    (v w : W) : polar (fun x ↦ Q (f x)) v w = polar Q (f v) (f w) := by
  show Q (f (v + w)) + Q (f v) + Q (f w) = Q (f v + f w) + Q (f v) + Q (f w)
  rw [hf]

/-- Quadraticity transports along an additive map. -/
theorem isQuadraticFp2_comp (Q : W' → ZMod 2) (hq : IsQuadraticFp2 Q) (f : W → W')
    (hf : ∀ a b, f (a + b) = f a + f b) (hf0 : f 0 = 0) :
    IsQuadraticFp2 fun x ↦ Q (f x) := by
  refine ⟨?_, ?_, ?_⟩
  · show Q (f 0) = 0
    rw [hf0, hq.map_zero]
  · intro u v w
    rw [polar_comp Q f hf, polar_comp Q f hf, polar_comp Q f hf, hf, hq.polar_add_left]
  · intro u v w
    rw [polar_comp Q f hf, polar_comp Q f hf, polar_comp Q f hf, hf, hq.polar_add_right]

/-- Nonsingularity transports along an additive equivalence. -/
theorem nonsingular_comp_addEquiv (Q : W' → ZMod 2) (e : W ≃+ W') (hns : Nonsingular Q) :
    Nonsingular fun x ↦ Q (e x) := by
  intro v hv
  have hev : (e v : W') ≠ 0 := fun h ↦ hv (by
    apply e.injective
    rw [h, map_zero])
  obtain ⟨w, hw⟩ := hns (e v) hev
  refine ⟨e.symm w, ?_⟩
  rw [polar_comp Q (⇑e) (fun a b ↦ map_add e a b), e.apply_symm_apply]
  exact hw

end Transport

section EquivTransport

variable {W W' : Type*}

/-- The Gauss sum is invariant under precomposition with an equivalence. -/
theorem gaussSum_comp_equiv [Fintype W] [Fintype W'] (Q : W' → ZMod 2) (e : W ≃ W') :
    gaussSum (fun x ↦ Q (e x)) = gaussSum Q :=
  Fintype.sum_equiv e _ _ fun _ ↦ rfl

/-- The zero count is invariant under precomposition with an equivalence. -/
theorem zeroCount_comp_equiv (Q : W' → ZMod 2) (e : W ≃ W') :
    zeroCount (fun x ↦ Q (e x)) = zeroCount Q :=
  Nat.card_congr (Equiv.subtypeEquiv e fun _ ↦ Iff.rfl)

end EquivTransport

/-! ## Product and power factorization of Gauss sums

The abstract carriers of the `(ε, m, n)`-triple: the degree-`n` block form is an orthogonal
sum of `n` copies of the base form, and its Gauss sum is the `n`-th power — matching the
`standardNumerics` leaves `SN.gaussUnram/gaussRam` (SD1 §1.1) with no arithmetic glue. -/

section Factorization

variable {W W' : Type*}

/-- `sign` turns finite sums into finite products. -/
theorem sign_sum {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) :
    sign (∑ i ∈ s, g i) = ∏ i ∈ s, sign (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, sign_add, ih]

/-- The Gauss sum of an orthogonal direct sum of two forms is the product of the Gauss
sums. -/
theorem gaussSum_prod_add [Fintype W] [Fintype W'] (Q : W → ZMod 2) (Q' : W' → ZMod 2) :
    gaussSum (fun p : W × W' ↦ Q p.1 + Q' p.2) = gaussSum Q * gaussSum Q' := by
  show ∑ p : W × W', sign (Q p.1 + Q' p.2) = (∑ v, sign (Q v)) * ∑ w, sign (Q' w)
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ sign_add _ _

/-- **The degree-`n` Gauss factorization**: the Gauss sum of the `n`-fold orthogonal block
form is the `n`-th power of the base Gauss sum. -/
theorem gaussSum_pi_sum [Fintype W] (Q : W → ZMod 2) (n : ℕ) :
    gaussSum (fun x : Fin n → W ↦ ∑ i, Q (x i)) = gaussSum Q ^ n := by
  show ∑ x : Fin n → W, sign (∑ i, Q (x i)) = (∑ v, sign (Q v)) ^ n
  calc ∑ x : Fin n → W, sign (∑ i, Q (x i))
      = ∑ x : Fin n → W, ∏ i, sign (Q (x i)) :=
        Finset.sum_congr rfl fun x _ ↦ sign_sum _ _
    _ = ∏ _i : Fin n, ∑ v, sign (Q v) := by
        have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset W))
          (fun _ w ↦ sign (Q w))
        rw [Fintype.piFinset_univ] at h
        exact h.symm
    _ = (∑ v, sign (Q v)) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Factorization

/-! ## Packet Lemma 6.1: the affine Gauss translation

`lem:gauss-translate`: the induction consumes *shifted* sums, and the shift is controlled by
the unique polar representative of the linear part.  Existence of the representative is a
Fourier double count over `charSum_eq_zero` — self-contained, no dual-space cardinality. -/

section AffineTranslate

variable {W : Type*} [AddCommGroup W]

open scoped Classical in
/-- The polar character sum in the second slot: full mass on the radical, zero elsewhere.
(For nonsingular `Q` the radical is `{0}`.)  The row/column engine of both the existence
double count and the plus-form Gauss computation. -/
theorem polar_charSum [Fintype W] (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q)
    (hns : Nonsingular Q) (x : W) :
    ∑ y : W, sign (polar Q x y) = if x = 0 then (Fintype.card W : ℤ) else 0 := by
  split_ifs with hx
  · subst hx
    simp only [polar_zero_left Q hq, QuadraticFp2.sign_zero, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  · refine charSum_eq_zero
      (AddMonoidHom.mk' (fun y ↦ polar Q x y) fun a b ↦ hq.polar_add_right x a b) ?_
    obtain ⟨w, hw⟩ := hns x hx
    exact ⟨w, zmod2_ne_zero_eq_one hw⟩

/-- **Existence of the polar representative** (the surjectivity half of packet Lem 6.1): on
a finite group, every additive functional is `B_Q(·, y)` for some `y`.  Fourier double
count: if no `y` works, every column character `x ↦ ℓ(x) + B(x, y)` is nonzero and its sign
sum vanishes; summing over `y` and swapping isolates the radical row `x = 0`, forcing
`#W = 0`. -/
theorem polar_rep_exists [Fintype W] (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q)
    (hns : Nonsingular Q) (ℓ : W →+ ZMod 2) : ∃ y : W, ∀ x, ℓ x = polar Q x y := by
  classical
  by_contra hcon
  push Not at hcon
  have hcol : ∀ y : W, ∑ x, sign (ℓ x + polar Q x y) = 0 := by
    intro y
    obtain ⟨x₀, hx₀⟩ := hcon y
    have hne : ℓ x₀ + polar Q x₀ y ≠ 0 := by
      intro h
      apply hx₀
      have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact key _ _ h
    calc ∑ x, sign (ℓ x + polar Q x y)
        = ∑ x, sign ((ℓ + polarHom Q hq y) x) := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [AddMonoidHom.add_apply, polarHom_apply]
      _ = 0 := charSum_eq_zero _ ⟨x₀, by
          rw [AddMonoidHom.add_apply, polarHom_apply]
          exact zmod2_ne_zero_eq_one hne⟩
  have hswap : ∑ x : W, sign (ℓ x) * ∑ y : W, sign (polar Q x y) = 0 := by
    have h0 : ∑ y : W, ∑ x : W, sign (ℓ x + polar Q x y) = 0 := by
      calc ∑ y : W, ∑ x : W, sign (ℓ x + polar Q x y)
          = ∑ _y : W, (0 : ℤ) := Finset.sum_congr rfl fun y _ ↦ hcol y
        _ = 0 := Finset.sum_const_zero
    rw [Finset.sum_comm] at h0
    calc ∑ x, sign (ℓ x) * ∑ y, sign (polar Q x y)
        = ∑ x, ∑ y, sign (ℓ x) * sign (polar Q x y) :=
          Finset.sum_congr rfl fun x _ ↦ Finset.mul_sum _ _ _
      _ = ∑ x, ∑ y, sign (ℓ x + polar Q x y) :=
          Finset.sum_congr rfl fun x _ ↦
            Finset.sum_congr rfl fun y _ ↦ (sign_add _ _).symm
      _ = 0 := h0
  rw [Finset.sum_congr rfl fun x _ ↦ by rw [polar_charSum Q hq hns x]] at hswap
  rw [Finset.sum_eq_single (0 : W) (fun b _ hb ↦ by rw [if_neg hb, mul_zero])
    (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl, map_zero, QuadraticFp2.sign_zero,
    one_mul] at hswap
  haveI : Nonempty W := ⟨0⟩
  have hpos : (0 : ℤ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  rw [hswap] at hpos
  exact lt_irrefl 0 hpos

/-- **Uniqueness of the polar representative** (the injectivity half): nonsingularity plus
exponent 2. -/
theorem polar_rep_unique (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (h2 : ∀ w : W, w + w = 0) {ℓ : W → ZMod 2} {y y' : W}
    (hy : ∀ x, ℓ x = polar Q x y) (hy' : ∀ x, ℓ x = polar Q x y') : y = y' := by
  by_contra hne
  have hsum_ne : y + y' ≠ 0 := by
    intro h0
    have hyy : y' = y := by
      have h3 : y + (y + y') = y := by rw [h0, add_zero]
      rwa [← add_assoc, h2 y, zero_add] at h3
    exact hne hyy.symm
  obtain ⟨w, hw⟩ := hns (y + y') hsum_ne
  apply hw
  rw [polar_comm, hq.polar_add_right w y y', ← hy w, ← hy' w, CharTwo.add_self_eq_zero]

/-- **The affine Gauss translation at a given representative** (the computational core of
packet Lem 6.1): shifting a form by the polar functional of `y` multiplies the Gauss sum by
the affine phase `(−1)^{Q(y)}`.  Unconditional — a pure reindexing along `x ↦ x + y`. -/
theorem gaussSum_add_polar [Fintype W] (Q : W → ZMod 2) (y : W) :
    gaussSum (fun x ↦ Q x + polar Q x y) = sign (Q y) * gaussSum Q := by
  show ∑ x, sign (Q x + polar Q x y) = sign (Q y) * gaussSum Q
  calc ∑ x, sign (Q x + polar Q x y)
      = ∑ x, sign (Q y) * sign (Q (x + y)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        have key : Q x + polar Q x y = Q y + Q (x + y) := by
          show Q x + (Q (x + y) + Q x + Q y) = Q y + Q (x + y)
          have k : ∀ a b c : ZMod 2, a + (b + a + c) = c + b := by decide
          exact k _ _ _
        rw [key, sign_add]
    _ = sign (Q y) * ∑ x, sign (Q (x + y)) := by rw [← Finset.mul_sum]
    _ = sign (Q y) * gaussSum Q := by
        have hre : ∑ x, sign (Q (x + y)) = ∑ z, sign (Q z) :=
          Equiv.sum_comp (Equiv.addRight y) (fun z ↦ sign (Q z))
        rw [hre]
        rfl

/-- **Packet Lem 6.1** (`lem:gauss-translate`; SD1 §6.3's proposed signature, with
`[Fintype W]` for `[Finite W]` — see the WW4 report): unique polar representative plus
translation.  For every linear functional `ℓ` on a finite nonsingular quadratic
`𝔽₂`-module there is exactly one `y` with `ℓ = B_Q(·, y)`, and the `ℓ`-shifted Gauss sum
is the `(−1)^{Q(y)}`-multiple of the unshifted one. -/
theorem affine_gauss_translate {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (ℓ : W →ₗ[ZMod 2] ZMod 2) :
    ∃! y : W, (∀ x, ℓ x = polar Q x y) ∧
      gaussSum (fun x ↦ Q x + ℓ x) = (-1 : ℤ) ^ (Q y).val * gaussSum Q := by
  have h2 : ∀ w : W, w + w = 0 := fun w ↦ by
    calc w + w = (1 : ZMod 2) • w + (1 : ZMod 2) • w := by rw [one_smul]
      _ = ((1 : ZMod 2) + 1) • w := (add_smul 1 1 w).symm
      _ = (0 : ZMod 2) • w := by rw [(by decide : (1 : ZMod 2) + 1 = 0)]
      _ = 0 := zero_smul _ _
  obtain ⟨y, hy⟩ := polar_rep_exists Q hq hns ℓ.toAddMonoidHom
  refine ⟨y, ⟨fun x ↦ hy x, ?_⟩, ?_⟩
  · have hfun : (fun x ↦ Q x + ℓ x) = fun x ↦ Q x + polar Q x y :=
      funext fun x ↦ by rw [← hy x]; rfl
    rw [hfun, gaussSum_add_polar, sign_eq_neg_one_pow_val]
  · rintro y' ⟨hy', -⟩
    exact polar_rep_unique Q hq hns h2 hy' fun x ↦ hy x

end AffineTranslate

/-! ## The one-op normal-form family `plusFormD`

`plusFormD d₀ q (v, w) = d₀(v) + B_q(v, w)` — the family containing all four non-`L_sq`
frozen endpoints (freeze rows 2–5): the diagonal block `d₀` is a κ⁰-normalized datum
(`q` itself for the compact rows, `npcQ0 ∘ L_c⁻¹` for the corrected-Npc row), the cross
block is the polar pairing.  Its Gauss sum is `#V` regardless of `d₀` (the `c₁`-Lagrangian
computation: the second slot is a full character sum). -/

section PlusForm

variable {V : Type*} [AddCommGroup V]

/-- The one-op plus form `(v, w) ↦ d₀(v) + B_q(v, w)`. -/
def plusFormD (d₀ q : V → ZMod 2) : V × V → ZMod 2 :=
  fun p ↦ d₀ p.1 + polar q p.1 p.2

@[simp] theorem plusFormD_apply (d₀ q : V → ZMod 2) (v w : V) :
    plusFormD d₀ q (v, w) = d₀ v + polar q v w := rfl

/-- The polar form of the plus form: diagonal-block polar plus the two cross pairings. -/
theorem polar_plusFormD (d₀ q : V → ZMod 2) (hq : IsQuadraticFp2 q) (p r : V × V) :
    polar (plusFormD d₀ q) p r
      = polar d₀ p.1 r.1 + polar q p.1 r.2 + polar q r.1 p.2 := by
  have e1 : polar q (p.1 + r.1) (p.2 + r.2)
      = polar q p.1 p.2 + polar q p.1 r.2 + polar q r.1 p.2 + polar q r.1 r.2 := by
    rw [hq.polar_add_left, hq.polar_add_right, hq.polar_add_right]
    ring
  show d₀ (p.1 + r.1) + polar q (p.1 + r.1) (p.2 + r.2)
      + (d₀ p.1 + polar q p.1 p.2) + (d₀ r.1 + polar q r.1 r.2)
    = d₀ (p.1 + r.1) + d₀ p.1 + d₀ r.1 + polar q p.1 r.2 + polar q r.1 p.2
  rw [e1]
  have key : ∀ A B C D E F G : ZMod 2,
      A + (D + E + F + G) + (B + D) + (C + G) = A + B + C + E + F := by decide
  exact key _ _ _ _ _ _ _

/-- The plus form is quadratic whenever its two blocks are. -/
theorem isQuadraticFp2_plusFormD {d₀ q : V → ZMod 2} (hd : IsQuadraticFp2 d₀)
    (hq : IsQuadraticFp2 q) : IsQuadraticFp2 (plusFormD d₀ q) := by
  refine ⟨?_, ?_, ?_⟩
  · show d₀ 0 + polar q 0 0 = 0
    rw [hd.map_zero, polar_zero_left q hq, add_zero]
  · intro u v w
    rw [polar_plusFormD d₀ q hq, polar_plusFormD d₀ q hq, polar_plusFormD d₀ q hq]
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hd.polar_add_left, hq.polar_add_left, hq.polar_add_right]
    ring
  · intro u v w
    rw [polar_plusFormD d₀ q hq, polar_plusFormD d₀ q hq, polar_plusFormD d₀ q hq]
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hd.polar_add_right, hq.polar_add_right, hq.polar_add_left]
    ring

/-- The plus form is nonsingular whenever the cross pairing is — **independently of the
diagonal block** (the cross block pairs both slots).  This is the "one-op normal forms both
branches" magic of the freeze. -/
theorem nonsingular_plusFormD {d₀ q : V → ZMod 2} (hd : IsQuadraticFp2 d₀)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) : Nonsingular (plusFormD d₀ q) := by
  rintro ⟨a, b⟩ hab
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb0
      exact hab (by rw [ha, hb0]; rfl)
    obtain ⟨w, hw⟩ := hns b hb
    refine ⟨(w, 0), ?_⟩
    rw [polar_plusFormD d₀ q hq]
    subst ha
    rw [polar_zero_left d₀ hd, polar_zero_left q hq, zero_add, zero_add, polar_comm]
    exact hw
  · obtain ⟨w, hw⟩ := hns a ha
    refine ⟨(0, w), ?_⟩
    rw [polar_plusFormD d₀ q hq, polar_zero_right d₀ hd, polar_zero_left q hq, zero_add,
      add_zero]
    exact hw

/-- **The plus-form Gauss sum is `#V`** (the `c₁`-Lagrangian computation): the second slot
is a full polar character sum, which kills every `v ≠ 0` and contributes `#V` at the
radical. -/
theorem gaussSum_plusFormD [Fintype V] {d₀ q : V → ZMod 2} (hd : IsQuadraticFp2 d₀)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) :
    gaussSum (plusFormD d₀ q) = Fintype.card V := by
  classical
  show ∑ p : V × V, sign (d₀ p.1 + polar q p.1 p.2) = (Fintype.card V : ℤ)
  rw [Fintype.sum_prod_type]
  calc ∑ v, ∑ w, sign (d₀ v + polar q v w)
      = ∑ v, sign (d₀ v) * ∑ w, sign (polar q v w) := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ ↦ sign_add _ _
    _ = ∑ v, sign (d₀ v) * (if v = 0 then (Fintype.card V : ℤ) else 0) :=
        Finset.sum_congr rfl fun v _ ↦ by rw [polar_charSum q hq hns v]
    _ = (Fintype.card V : ℤ) := by
        rw [Finset.sum_eq_single (0 : V) (fun b _ hb ↦ by rw [if_neg hb, mul_zero])
          (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl, hd.map_zero,
          QuadraticFp2.sign_zero, one_mul]

end PlusForm

/-! ## The per-branch affine-phase certificate

SD1 §6.3's proposed fields, concretized.  The `def:affine-B4` three-item map (§6.1):
item (1) base dims/signs = `baseDim`/`baseSign`/`gauss_eq` (feeding the record's
`gaussZ_unramified/ramified` leaves through `GaussZResidue`'s externally-given
`(m, hcard, G0)`-slots); item (2) the common polar/edge pairing = `polar_id` (the endpoint's
cross block **is** the antisymmetrization of the extraspecial refinement — the `b_q`-block
the `hsep`/`hpartial` families pair against); item (3) is **not** a field — the phase-cover
conversion is the generic layer's `DeltaChi`/`shChi`/`keystone`/`phaseChi` machinery
(`VLiftCount.lean:775-778`, reused untouched) — the certificate only pins the
κ_q⁰-normalization (`kappa_id`: the diagonal block is the κ⁰-datum `diag`, the quantity the
polarization cannot see; `Hessian.lean`'s `kappa0Cocycle_diag_fibre`/`hessSq_of_fibre` are
the evaluation-route side of the same pin).

**No parallel B1–B4 record** (ledger §3.4): the five §6.2 obligation families keep their
`SourceData(N)` shapes verbatim; this certificate is word-side *input data* for discharging
them, not a restatement. -/

section Certificate

variable {C V : Type*} [AddCommGroup V]
variable {W : Type*} [AddCommGroup W] [Fintype W]

/-- **The per-branch affine-phase certificate** (SD1 §6.3; packet Def 6.3's three items,
targeted at the §6.2 families).  Parameters: `dat` = the row's extraspecial factor-set datum
(`κ⁰`-route), `diag` = the row's κ⁰-normalized diagonal-block datum (n = 1 anchors:
`fun v ↦ dat.f v v` for the compact rows via `f_diag`; the `npcQ0`-composite for the
corrected-Npc row), `Qnf` = the frozen row's quadratic normal-form target, `j₀`/`j₁` = the
diagonal/cross block inclusions of the endpoint.

Instantiable from the frozen row's endpoint polynomial, a change-of-variables `LinearEquiv`
with inverse witness, and per-χ shift vectors with their `Q`-values — nothing presupposing
the WC-Mpc analysis (the row-5 constraint; see the module docstring). -/
structure PhaseCoverCertificate (dat : FactorSet C V) (diag : V → ZMod 2)
    (Qnf : W → ZMod 2) (j₀ j₁ : V →+ W) where
  /-- The half-dimension `m`: the normal-form module carries `#W = 2^{2·baseDim}`. -/
  baseDim : ℕ
  /-- The Gauss sign `ε(Qnf) ∈ {±1}` of the normal form (`baseSign_dichotomy`). -/
  baseSign : ℤ
  /-- The §6.3 comment "the module carries `#V = 2^{2·baseDim}`" made explicit — consumed
  verbatim as the record leaves' externally-given `hcard`. -/
  card_eq : Fintype.card W = 2 ^ (2 * baseDim)
  /-- The base Gauss value, via Cor 6.2. -/
  gauss_eq : gaussSum Qnf = baseSign * 2 ^ baseDim
  /-- Item (2): the endpoint's polar block **is** the cup/edge pairing — the
  antisymmetrization of the extraspecial refinement (`= B_q` under
  `IsEquivariantFactorSet.f_polar`). -/
  polar_id : ∀ v w : V, polar Qnf (j₀ v) (j₁ w) = dat.f v w + dat.f w v
  /-- Item (3)'s pin: the diagonal block is the κ⁰-normalized datum `diag` — the quantity
  the polarization alone cannot see (`class2.py`; `f_diag` under the equivariant bundle). -/
  kappa_id : ∀ v : V, Qnf (j₀ v) = diag v

namespace PhaseCoverCertificate

variable {dat : FactorSet C V} {diag : V → ZMod 2} {Qnf : W → ZMod 2} {j₀ j₁ : V →+ W}
variable (Φ : PhaseCoverCertificate dat diag Qnf j₀ j₁)

/-- The Gauss residue `G0 = ε·2^m` — the literal value the record's `gaussZ_*` leaves
consume (`GaussZResidue … G0`, `Phase140/Assembly.lean:145-149`). -/
def G0 : ℤ := Φ.baseSign * 2 ^ Φ.baseDim

theorem gaussSum_eq_G0 : gaussSum Qnf = Φ.G0 := Φ.gauss_eq

/-- **The per-χ translated Gauss value** (packet Lem 6.1 at the certificate): a shift
vector `y` with known `Qnf`-value contributes exactly the affine phase `sign (Qnf y)`.
This is the output the phase machinery consumes from raw per-χ shift data — supply
`y := y_χ` and its `Q`-value; nothing else is needed (the row-5 constraint). -/
theorem gauss_translate (y : W) :
    gaussSum (fun x ↦ Qnf x + polar Qnf x y) = sign (Qnf y) * Φ.G0 := by
  rw [gaussSum_add_polar, Φ.gaussSum_eq_G0]

/-- **The degree-`n` Gauss magnitude from the `(ε, m, n)`-triple**: the `n`-fold block form
evaluates to `ε^n · 2^{n·m}`. -/
theorem gaussSum_pi (n : ℕ) :
    gaussSum (fun x : Fin n → W ↦ ∑ i, Qnf (x i))
      = Φ.baseSign ^ n * 2 ^ (n * Φ.baseDim) := by
  rw [gaussSum_pi_sum, Φ.gauss_eq, mul_pow, ← pow_mul, mul_comm Φ.baseDim n]

/-- The ramified-head shape: `baseSign = 1` gives `2^{n·m}` — verbatim
`standardNumerics n |>.gaussRam baseDim` (SD1 §1.1). -/
theorem gaussSum_pi_of_baseSign_one (h1 : Φ.baseSign = 1) (n : ℕ) :
    gaussSum (fun x : Fin n → W ↦ ∑ i, Qnf (x i)) = 2 ^ (n * Φ.baseDim) := by
  rw [Φ.gaussSum_pi, h1, one_pow, one_mul]

/-- The unramified-head shape: `baseSign = −1` gives `(−1)^n · 2^{n·m}` — verbatim
`standardNumerics n |>.gaussUnram baseDim` (SD1 §1.1). -/
theorem gaussSum_pi_of_baseSign_neg_one (h1 : Φ.baseSign = -1) (n : ℕ) :
    gaussSum (fun x : Fin n → W ↦ ∑ i, Qnf (x i))
      = (-1) ^ n * 2 ^ (n * Φ.baseDim) := by
  rw [Φ.gaussSum_pi, h1]

/-- **Cor 6.2, the `(dim, ε)`-classification**: the certificate's sign is a genuine sign.
(Via the frozen template `gaussSum_eq_pow`.) -/
theorem baseSign_dichotomy (hq : IsQuadraticFp2 Qnf) (hns : Nonsingular Qnf) :
    Φ.baseSign = 1 ∨ Φ.baseSign = -1 := by
  have hpow : (0 : ℤ) < 2 ^ Φ.baseDim := by positivity
  rcases gaussSum_eq_pow Qnf hq hns Φ.card_eq with h | h
  · left
    have h1 : Φ.baseSign * 2 ^ Φ.baseDim = 1 * 2 ^ Φ.baseDim := by
      rw [one_mul]
      exact Φ.gauss_eq.symm.trans h
    exact mul_right_cancel₀ hpow.ne' h1
  · right
    have h1 : Φ.baseSign * 2 ^ Φ.baseDim = -1 * 2 ^ Φ.baseDim := by
      rw [neg_one_mul]
      exact Φ.gauss_eq.symm.trans h
    exact mul_right_cancel₀ hpow.ne' h1

/-- The certificate sign is the Arf invariant, in the frozen `arf` spelling. -/
theorem arf_eq_baseSign_iff (hq : IsQuadraticFp2 Qnf) (hns : Nonsingular Qnf) :
    arf Qnf = 0 ↔ Φ.baseSign = 1 := by
  rw [arf_eq_zero_iff_gaussSum_pos, Φ.gauss_eq]
  constructor
  · intro hpos
    rcases Φ.baseSign_dichotomy hq hns with h | h
    · exact h
    · exfalso
      rw [h] at hpos
      have h2 : (0 : ℤ) < 2 ^ Φ.baseDim := by positivity
      linarith
  · intro h
    rw [h, one_mul]
    positivity

/-- **Cor 6.2, zero counts, in the record-leaf shape**: `#Qnf⁻¹(0) = 2^{2m−1} + ε·2^{m−1}`.
Built **on** the frozen ℚ₂ templates `zeroCount_of_arf_zero/one` — reused, not re-proved
(the LG5 consumption pattern). -/
theorem zeroCount_int_eq (hq : IsQuadraticFp2 Qnf) (hns : Nonsingular Qnf)
    (hm : 1 ≤ Φ.baseDim) :
    (zeroCount Qnf : ℤ)
      = 2 ^ (2 * Φ.baseDim - 1) + Φ.baseSign * 2 ^ (Φ.baseDim - 1) := by
  rcases Φ.baseSign_dichotomy hq hns with h | h
  · have harf : arf Qnf = 0 := (Φ.arf_eq_baseSign_iff hq hns).mpr h
    rw [zeroCount_of_arf_zero Qnf hq hns hm Φ.card_eq harf, h]
    push_cast
    ring
  · have harf : arf Qnf = 1 := by
      rcases ZMod.eq_zero_or_eq_one (arf Qnf) with h0 | h1
      · exfalso
        have hone := (Φ.arf_eq_baseSign_iff hq hns).mp h0
        rw [hone] at h
        norm_num at h
      · exact h1
    rw [zeroCount_of_arf_one Qnf hq hns hm Φ.card_eq harf, h]
    have hle : (2 : ℕ) ^ (Φ.baseDim - 1) ≤ 2 ^ (2 * Φ.baseDim - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    push_cast [Nat.cast_sub hle]
    ring

end PhaseCoverCertificate

end Certificate

end GQ2.Dyadic
