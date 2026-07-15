/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.GaussCount.Wall

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Duality and the Wall sign relation

The kernel-perpendicular identification and the final sign comparison.

See `GQ2.GaussCount` for the paper-facing overview, source citations, and deviations.
-/

open scoped BigOperators

namespace GQ2

namespace QuadraticFp2

private theorem zmod2_ne_zero_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by
  decide

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
