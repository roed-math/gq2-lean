/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GaussZ.FinalGammaA.Kappa

/-!
# Signed-count and even-cardinality bricks

The finite quadratic signed count and the even-dimension consequence of nonsingularity.

See `GQ2.GaussZ.FinalGammaA` for the paper-facing overview, source citations, and deviations.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridge FoxH RStageGammaA WordCoh2 QuadraticFp2

/-! ## A-4.5 bricks: the `V`-indexed signed count and the `qDouble` orientation bridge

En-free pieces of the seam assembly: the `finsum_sign_eq` extraction re-indexed by a plain
finite type (the `x₀`-supported section makes the Gauss domain literally `V`), its two
pinned-count finales (`∓2^m`), and the `U⁻¹`/`U` orientation identification that matches
A-4.4b's Wall double to `qDouble`. -/

section CountBricks

/-- The signed-sum extraction over a plain finite type: with `zeroCount q` and `#V` known,
`∑ᶠ sign(q v) = 2·zeroCount − #V` (the `GaussZLocal.finsum_sign_eq` shape, En-free). -/
theorem finsum_sign_eq_count {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2)
    (zc : ℕ) (hzc : zeroCount q = zc) {n : ℕ} (hn : Nat.card V = n) :
    ∑ᶠ v : V, sign (q v) = 2 * (zc : ℤ) - n := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hsign : ∀ s : ZMod 2, sign s = QuadraticFp2.sign s := by decide
  calc (∑ v : V, sign (q v))
      = ∑ v : V, QuadraticFp2.sign (q v) := Finset.sum_congr rfl fun v _ => hsign _
    _ = 2 * (zc : ℤ) - n := by
        have hge := gaussSum_eq (V := V) q
        unfold QuadraticFp2.gaussSum at hge
        rw [hge, hzc, ← Nat.card_eq_fintype_card, hn]

/-- **The minus finale**: `∑ᶠ sign = −2^m` from the unramified zero count
`2^{2m−1} − 2^{m−1}` (`prop_6_9_unramified` / `zeroCount_of_arf_one`'s value). -/
theorem finsum_sign_eq_neg_of_zeroCount {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2)
    (m : ℕ) (hm : 1 ≤ m) (hzc : zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1))
    (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (q v) = -(2 ^ m : ℤ) := by
  rw [finsum_sign_eq_count q _ hzc hcard]
  have hle : (2 : ℕ) ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast [Nat.cast_sub hle]
  linarith [e1, e2]

/-- **The plus finale**: `∑ᶠ sign = +2^m` from the ramified zero count
`2^{2m−1} + 2^{m−1}` (`prop_6_9_ramified` / `zeroCount_of_arf_zero`'s value). -/
theorem finsum_sign_eq_pos_of_zeroCount {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2)
    (m : ℕ) (hm : 1 ≤ m) (hzc : zeroCount q = 2 ^ (2 * m - 1) + 2 ^ (m - 1))
    (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (q v) = (2 ^ m : ℤ) := by
  rw [finsum_sign_eq_count q _ hzc hcard]
  have e1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast
  linarith [e1, e2]

/-- **The `qDouble` orientation bridge**: for `q` invariant under `U`, the Wall-double twist
reads the same with `U⁻¹` as with `U` — `B(x, U⁻¹•x) = B(x, U•x)` — so A-4.4b's value
`q(v) + B(v, σ₂⁻¹•v)` IS `qDouble q (σ₂ • ·)` at `v`. -/
theorem polar_smul_inv_eq {C : Type*} [Group C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] (q : V → ZMod 2) (U : C) (hUq : ∀ v : V, q (U • v) = q v)
    (x : V) : polar q x (U⁻¹ • x) = polar q x (U • x) := by
  have h1 : q (U⁻¹ • x) = q x := by rw [← hUq (U⁻¹ • x), smul_inv_smul]
  have h2 : q (x + U⁻¹ • x) = q (x + U • x) := by
    calc q (x + U⁻¹ • x) = q (U • (x + U⁻¹ • x)) := (hUq _).symm
      _ = q (U • x + x) := by rw [smul_add, smul_inv_smul]
      _ = q (x + U • x) := by rw [add_comm]
  show q (x + U⁻¹ • x) + q x + q (U⁻¹ • x) = q (x + U • x) + q x + q (U • x)
  rw [h2, h1, hUq x]

end CountBricks

/-! ## The even-dimension fact: nonsingular ⟹ `#V = 2^{2m}`

The c3-G0 package needs `#V = 2^{2m}` — the classical symplectic fact that a nonsingular
alternating pairing forces even dimension, in counting form: split off a hyperbolic pair
`(v, w)` through the surjective pairing hom `u ↦ (B(u,v), B(u,w))` onto `𝔽₂²`; the kernel
is the perpendicular complement, of index exactly `4`, and stays nonsingular. -/

section EvenCard

universe u

theorem card_eq_two_pow_two_mul_of_nonsingular {V : Type u} [AddCommGroup V] [Finite V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hV₂ : ∀ v : V, v + v = 0) :
    ∃ m : ℕ, Nat.card V = 2 ^ (2 * m) := by
  suffices h : ∀ n : ℕ, ∀ (V : Type u) (_ : AddCommGroup V) (_ : Finite V),
      ∀ q : V → ZMod 2, IsQuadraticFp2 q → Nonsingular q → (∀ v : V, v + v = 0) →
      Nat.card V = n → ∃ m : ℕ, Nat.card V = 2 ^ (2 * m) by
    exact h (Nat.card V) V ‹_› ‹_› q hq hns hV₂ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V instG instF q hq hns hV₂ hn
    by_cases hV : ∃ v : V, v ≠ 0
    case neg =>
      push Not at hV
      haveI : Subsingleton V := ⟨fun a b => by rw [hV a, hV b]⟩
      haveI : Inhabited V := ⟨0⟩
      exact ⟨0, by rw [Nat.card_unique]; decide⟩
    case pos =>
      obtain ⟨v, hv⟩ := hV
      obtain ⟨w, hw⟩ := hns v hv
      have hBvw : polar q v w = 1 :=
        ((show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (polar q v w)).resolve_left hw
      have hpz : ∀ x : V, polar q 0 x = 0 := fun x => by
        have h := hq.polar_add_left 0 0 x
        rwa [add_zero, CharTwo.add_self_eq_zero] at h
      -- the pairing hom onto `𝔽₂²`
      set φ : V →+ ZMod 2 × ZMod 2 :=
        { toFun := fun u => (polar q u v, polar q u w)
          map_zero' := by rw [hpz v, hpz w]; rfl
          map_add' := fun a b => by
            show (polar q (a + b) v, polar q (a + b) w) = _
            rw [hq.polar_add_left a b v, hq.polar_add_left a b w]
            rfl } with hφdef
      have hφv : φ v = ((0 : ZMod 2), (1 : ZMod 2)) := by
        show (polar q v v, polar q v w) = _
        rw [polar_self q hq hV₂ v, hBvw]
      have hφw : φ w = ((1 : ZMod 2), (0 : ZMod 2)) := by
        show (polar q w v, polar q w w) = _
        rw [polar_comm q w v, hBvw, polar_self q hq hV₂ w]
      have hφsurj : Function.Surjective ⇑φ := by
        intro p
        rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) p.1 with h1 | h1 <;>
          rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) p.2 with h2 | h2
        · refine ⟨0, ?_⟩
          rw [map_zero]
          exact (Prod.ext h1 h2).symm
        · refine ⟨v, ?_⟩
          rw [hφv]
          exact (Prod.ext h1 h2).symm
        · refine ⟨w, ?_⟩
          rw [hφw]
          exact (Prod.ext h1 h2).symm
        · refine ⟨v + w, ?_⟩
          rw [map_add, hφv, hφw,
            show ((0 : ZMod 2), (1 : ZMod 2)) + ((1 : ZMod 2), (0 : ZMod 2))
              = ((1 : ZMod 2), (1 : ZMod 2)) from by decide]
          exact (Prod.ext h1 h2).symm
      set K := φ.ker with hKdef
      -- the index-4 count
      have hcardV : Nat.card V = 4 * Nat.card ↥K := by
        have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (s := K)
        have h2 : Nat.card (V ⧸ K) = 4 := by
          rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv,
            Nat.card_eq_fintype_card]
          decide
        rw [h1, h2]
      -- the kernel inherits the structure
      have hV₂K : ∀ u : ↥K, u + u = 0 := fun u => Subtype.ext (hV₂ u.1)
      have hqK : IsQuadraticFp2 (fun u : ↥K => q u.1) := by
        refine ⟨hq.map_zero, ?_, ?_⟩
        · intro a b c
          exact hq.polar_add_left a.1 b.1 c.1
        · intro a b c
          exact hq.polar_add_right a.1 b.1 c.1
      -- the correction into the perpendicular complement
      have hcorr : ∀ x : V, ∃ x' : V, polar q x' v = 0 ∧ polar q x' w = 0 ∧
          ∀ u : V, polar q u v = 0 → polar q u w = 0 →
            polar q u x' = polar q u x := by
        intro x
        rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (polar q x v) with h1 | h1 <;>
          rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (polar q x w) with h2 | h2
        · exact ⟨x, h1, h2, fun u _ _ => rfl⟩
        · -- `(B(x,v), B(x,w)) = (0,1)`: correct by `v`
          refine ⟨x + v, ?_, ?_, ?_⟩
          · rw [hq.polar_add_left, h1, polar_self q hq hV₂, add_zero]
          · rw [hq.polar_add_left, h2, hBvw]
            decide
          · intro u hu1 hu2
            rw [hq.polar_add_right, hu1, add_zero]
        · -- `(1,0)`: correct by `w`
          refine ⟨x + w, ?_, ?_, ?_⟩
          · rw [hq.polar_add_left, h1, polar_comm q w v, hBvw]
            decide
          · rw [hq.polar_add_left, h2, polar_self q hq hV₂ w, add_zero]
          · intro u hu1 hu2
            rw [hq.polar_add_right, hu2, add_zero]
        · -- `(1,1)`: correct by `v + w`
          refine ⟨x + (v + w), ?_, ?_, ?_⟩
          · rw [hq.polar_add_left, h1, hq.polar_add_left, polar_self q hq hV₂,
              polar_comm q w v, hBvw]
            decide
          · rw [hq.polar_add_left, h2, hq.polar_add_left, hBvw, polar_self q hq hV₂]
            decide
          · intro u hu1 hu2
            rw [hq.polar_add_right, hq.polar_add_right, hu1, hu2, add_zero, add_zero]
      -- the kernel stays nonsingular
      have hnsK : Nonsingular (fun u : ↥K => q u.1) := by
        intro u hu
        have hu1 : (u : V) ≠ 0 := fun h => hu (Subtype.ext h)
        obtain ⟨x, hx⟩ := hns u.1 hu1
        obtain ⟨x', hx'v, hx'w, hx'pair⟩ := hcorr x
        have hker : φ u.1 = 0 := AddMonoidHom.mem_ker.mp u.2
        have huv : polar q u.1 v = 0 := congrArg Prod.fst hker
        have huw : polar q u.1 w = 0 := congrArg Prod.snd hker
        have hx'mem : x' ∈ K := AddMonoidHom.mem_ker.mpr (by
          show (polar q x' v, polar q x' w) = 0
          rw [hx'v, hx'w]
          rfl)
        refine ⟨⟨x', hx'mem⟩, ?_⟩
        show polar q u.1 x' ≠ 0
        rw [hx'pair u.1 huv huw]
        exact hx
      -- recurse on the kernel
      have hKpos : 0 < Nat.card ↥K := Nat.card_pos
      have hKlt : Nat.card ↥K < n := by
        rw [hcardV] at hn
        omega
      obtain ⟨m, hm⟩ := ih (Nat.card ↥K) hKlt ↥K inferInstance inferInstance
        (fun u : ↥K => q u.1) hqK hnsK hV₂K rfl
      refine ⟨m + 1, ?_⟩
      rw [hcardV, hm, show 2 * (m + 1) = 2 * m + 2 from by ring, pow_add]
      ring

/-- The consumer form: with a nonzero vector, `#V = 2^{2m}` with `m ≥ 1` — the c3-G0
package's cardinality field, derived from the enrichment's nonsingular form. -/
theorem exists_one_le_card_eq_two_pow_of_nonsingular {V : Type*} [AddCommGroup V]
    [Finite V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hV₂ : ∀ v : V, v + v = 0) (hVne : ∃ v : V, v ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card V = 2 ^ (2 * m) := by
  obtain ⟨m, hm⟩ := card_eq_two_pow_two_mul_of_nonsingular q hq hns hV₂
  refine ⟨m, ?_, hm⟩
  rcases Nat.eq_zero_or_pos m with rfl | h
  · exfalso
    obtain ⟨v, hv⟩ := hVne
    have h1 : Nat.card V = 1 := by simpa using hm
    haveI : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hv (Subsingleton.elim v 0)
  · exact h

end EvenCard

end AffineTLift

end SectionEight

end GQ2
