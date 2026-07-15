/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.RegularSummand.Involution

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Equivariant lifting from Lemma 6.11

The projectivity-style lifting consequence of the regular-summand package.
See `GQ2.RegularSummand` for the paper-facing overview and references.
-/

namespace GQ2

/-! ## The consequence: equivariant lifting (`Hom(V, −)`-exactness)

Proved from the summand package fields alone; consumers apply it to the `lemma_6_11` output
(now itself std-3, so the whole chain is `sorryAx`-free).  This is the "deep-count
multiplicativity" input of `docs/orchestration/p15f1-dimcount-scoping.md` §2: every equivariant map out of
`V` lifts along equivariant surjections. -/

section EquivariantLift

variable {C : Type} [Group C]
variable {V W W' : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup W']
  [DistribMulAction C V] [DistribMulAction C W] [DistribMulAction C W']

open scoped Classical

/-- The `(n, x)`-indicator basis vector of the regular module `Fin N → C → ZMod 2`. -/
noncomputable def regBasis (N : ℕ) (n : Fin N) (x : C) : Fin N → C → ZMod 2 :=
  fun m y => if m = n ∧ y = x then 1 else 0

omit [Group C] in
/-- Every element of the regular module is the sum of its coordinates against `regBasis`. -/
theorem regBasis_decomp [Fintype C] {N : ℕ} (F : Fin N → C → ZMod 2) :
    F = ∑ n : Fin N, ∑ x : C, F n x • regBasis N n x := by
  funext m y
  have happ : (∑ n : Fin N, ∑ x : C, F n x • regBasis N n x) m y
      = ∑ n : Fin N, ∑ x : C, (if m = n ∧ y = x then F n x else 0) := by
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    show F n x • (if m = n ∧ y = x then (1 : ZMod 2) else 0) = _
    by_cases h : m = n ∧ y = x
    · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
    · rw [if_neg h, if_neg h, smul_eq_mul, mul_zero]
  rw [happ]
  have hinner : ∀ n : Fin N,
      (∑ x : C, if m = n ∧ y = x then F n x else 0) = if m = n then F n y else 0 := by
    intro n
    by_cases hmn : m = n
    · simp only [hmn, true_and, if_true]
      rw [Finset.sum_ite_eq Finset.univ y (fun x => F n x), if_pos (Finset.mem_univ y)]
    · simp only [hmn, false_and, if_false]
      exact Finset.sum_const_zero
  rw [Finset.sum_congr rfl fun n _ => hinner n,
    Finset.sum_ite_eq Finset.univ m (fun n => F n y), if_pos (Finset.mem_univ m)]

/-- Left translation carries `regBasis N n x` to `regBasis N n (h·x)`. -/
theorem regBasis_translate {N : ℕ} (h : C) (n : Fin N) (x : C) :
    (fun (m : Fin N) (y : C) => regBasis N n x m (h⁻¹ * y)) = regBasis N n (h * x) := by
  funext m y
  show (if m = n ∧ h⁻¹ * y = x then (1 : ZMod 2) else 0)
    = if m = n ∧ y = h * x then 1 else 0
  refine if_congr (and_congr_right fun _ => ?_) rfl rfl
  exact inv_mul_eq_iff_eq_mul

/-- **Equivariant lifting along an equivariant surjection, from a regular-summand package**
(the `Hom(V, −)`-exactness consequence of Lemma 6.11).  `W`, `W'` are 2-torsion
(all consumers are). -/
theorem equivariant_lift_of_regular_summand [Finite C]
    (h2W : ∀ w : W, w + w = 0) (h2W' : ∀ w : W', w + w = 0)
    {N : ℕ} (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V)
    (hι : ∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : V, r (ι v) = v)
    (π : W →+ W') (hπeq : ∀ (h : C) (w : W), π (h • w) = h • π w)
    (hπ : Function.Surjective ⇑π)
    (f : V →+ W') (hfeq : ∀ (h : C) (v : V), f (h • v) = h • f v) :
    ∃ g : V →+ W, (∀ (h : C) (v : V), g (h • v) = h • g v) ∧ ∀ v : V, π (g v) = f v := by
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Module (ZMod 2) W := AddCommGroup.zmodModule fun w => (two_nsmul w).trans (h2W w)
  haveI : Module (ZMod 2) W' := AddCommGroup.zmodModule fun w => (two_nsmul w).trans (h2W' w)
  have hsmul_comm : ∀ (h : C) (z : ZMod 2) (u : W), h • (z • u) = z • (h • u) := by
    intro h z u
    rcases ZMod.eq_zero_or_eq_one z with rfl | rfl <;> simp
  have hπz : ∀ (z : ZMod 2) (u : W), π (z • u) = z • π u := by
    intro z u
    rcases ZMod.eq_zero_or_eq_one z with rfl | rfl <;> simp
  -- `f` transported to the regular module.
  set f' : (Fin N → C → ZMod 2) →+ W' := f.comp r with hf'def
  have hf'eq : ∀ (h : C) (B : Fin N → C → ZMod 2),
      f' (fun n x => B n (h⁻¹ * x)) = h • f' B := by
    intro h B
    show f (r fun n x => B n (h⁻¹ * x)) = h • f (r B)
    rw [hr, hfeq]
  -- choose lifts of the values on the identity-based basis vectors.
  choose w hw using fun n : Fin N => hπ (f' (regBasis N n 1))
  -- the lifted map on the regular module: `G F = Σ_{n,x} F n x • (x • w n)`.
  set G : (Fin N → C → ZMod 2) →+ W := AddMonoidHom.mk'
    (fun F => ∑ n : Fin N, ∑ x : C, F n x • (x • w n))
    (fun F F' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      show ((F + F') n x) • (x • w n) = _
      show (F n x + F' n x) • (x • w n) = _
      rw [add_smul]) with hGdef
  have hGval : ∀ F : Fin N → C → ZMod 2,
      G F = ∑ n : Fin N, ∑ x : C, F n x • (x • w n) := fun _ => rfl
  -- `G` is equivariant.
  have hGeq : ∀ (h : C) (F : Fin N → C → ZMod 2),
      G (fun n x => F n (h⁻¹ * x)) = h • G F := by
    intro h F
    rw [hGval, hGval, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    calc (∑ x : C, F n (h⁻¹ * x) • (x • w n))
        = ∑ x : C, F n (h⁻¹ * (h * x)) • ((h * x) • w n) :=
          (Equiv.sum_comp (Equiv.mulLeft h)
            (fun x : C => F n (h⁻¹ * x) • (x • w n))).symm
      _ = ∑ x : C, F n x • ((h * x) • w n) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [inv_mul_cancel_left]
      _ = ∑ x : C, h • (F n x • (x • w n)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_smul, hsmul_comm]
      _ = h • ∑ x : C, F n x • (x • w n) := (Finset.smul_sum).symm
  -- `π ∘ G = f'` (via the basis decomposition).
  have hπG : ∀ F : Fin N → C → ZMod 2, π (G F) = f' F := by
    intro F
    have hval : π (G F) = ∑ n : Fin N, ∑ x : C, F n x • f' (regBasis N n x) := by
      rw [hGval, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hπz, hπeq, hw]
      congr 1
      have htr : (fun (m : Fin N) (y : C) => regBasis N n 1 m (x⁻¹ * y))
          = regBasis N n x := by
        have h1 := regBasis_translate (C := C) x n 1
        rwa [mul_one] at h1
      rw [← hf'eq x (regBasis N n 1), htr]
    rw [hval]
    conv_rhs => rw [regBasis_decomp (C := C) F]
    rw [map_sum]
    refine (Finset.sum_congr rfl fun n _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases ZMod.eq_zero_or_eq_one (F n x) with hz | hz <;> rw [hz] <;> simp
  -- assemble `g = G ∘ ι`.
  refine ⟨G.comp ι, fun h v => ?_, fun v => ?_⟩
  · show G (ι (h • v)) = h • G (ι v)
    have hιfun : ι (h • v) = fun n x => ι v n (h⁻¹ * x) := by
      funext n x
      exact hι h v n x
    rw [hιfun, hGeq]
  · show π (G (ι v)) = f v
    rw [hπG]
    show f (r (ι v)) = f v
    rw [hri]

end EquivariantLift

end GQ2
