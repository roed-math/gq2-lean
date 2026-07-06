/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.TameQuotient

/-!
# Lemma 6.11: ramified simple modules are split summands of regular modules  (P-15f1)

The **paper node** Lemma 6.11 (§6.3, proof pp. 29–30): a ramified simple faithful module `V`
over the tame image `H_V` is a projective `𝔽₂[H_V]`-module — stated here in the equivalent
consumer shape *`V` is an equivariant split summand of a regular module `𝔽₂[H_V]^N`*.  The
regular module is carried as `Fin N → C → ZMod 2` with the **left-translation action spelled
inline** (`(h • F) n x = F n (h⁻¹x)`), so the statement needs no bespoke action instances.

## Status: sorried paper node (NOT an axiom)

This is the paper's **own** lemma — no single literature theorem states it (it is assembled
from Clifford, Ann. of Math. **38** (1937) 533–550, and Higman, Duke Math. J. **21** (1954)
369–376, plus elementary facts), so per the census hygiene (leaves = literature) it is carried
as a **sorried lemma in the allowlist**, the established P-14 → P-15 pattern (as `lemma_6_17`
itself is).  `sorryAx` flows through every consumer's `#print axioms` until discharged.

## Discharge plan (self-contained finite representation theory, no arithmetic)

1. `P` a Sylow 2-subgroup of `C`: cyclic (embeds in the cyclic `C/⟨c τ⟩-closure` since
   `|⟨c τ⟩|` is odd — `odd_orderOf_tameInertia`).
2. `V|_P` is free over `𝔽₂[P]`: Maschke over the odd inertia (Mathlib
   `MonoidAlgebra.Submodule.exists_isCompl`) + the Clifford weight-orbit argument over a
   finite splitting field `𝔽_{2^T}` (stabilizer of a weight acts by a 2-power-order scalar
   = 1, then faithfulness) + descent via the norm criterion
   (`V` free over `𝔽₂[⟨p⟩] ⟺ N_p(V) = V^p`, `N_p = (1+σ)^{2^a−1}`, Mathlib
   `Module.equiv_directSum_of_isTorsion`).
3. Freeness over `P` ⟹ split summand over `C`: the odd-index relative trace `H/P`
   (the sibling of `LocalKummer.inflationVanishes_of_oddNormal`'s averaging —
   `odd_nsmul_eq_self`, no division).

Ticket: P-15f1 (`docs/p15f1-dimcount-scoping.md` §2; route decision in the board row).
-/

namespace GQ2

/-- **Lemma 6.11 (paper node, §6.3; SORRIED — see the module docstring)**: a ramified simple
faithful 2-torsion module over the tame image is an equivariant split summand of a regular
module.  The regular module `𝔽₂[C]^N` is `Fin N → C → ZMod 2` with the left-translation
action written inline; `ι` is the equivariant embedding, `r` the equivariant retraction.

From this the deep-count multiplicativity (`Hom(V^∨, −)`-exactness) follows —
`equivariant_lift_of_regular_summand` below — which is the sole remaining input to
`lemma_6_17_dim`'s lower bound `#X₊ ≥ 2^m`.  Applied at `V := V^∨` (also ramified simple
faithful) by the consumer. -/
theorem lemma_6_11 {C : Type} [Group C] [TopologicalSpace C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v := by
  sorry

/-! ## The consequence: equivariant lifting (`Hom(V, −)`-exactness)

Proved **without** the sorry from the summand package fields alone; consumers apply it to the
`lemma_6_11` output (so their `#print axioms` carries `sorryAx` through the paper node until
it is discharged).  This is the "deep-count multiplicativity" input of
`docs/p15f1-dimcount-scoping.md` §2: every equivariant map out of `V` lifts along equivariant
surjections. -/

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
(the `Hom(V, −)`-exactness consequence of Lemma 6.11; itself sorry-free — `sorryAx` enters a
consumer's audit only when the package is produced by `lemma_6_11`).  `W`, `W'` are 2-torsion
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
  have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Module (ZMod 2) W := AddCommGroup.zmodModule (fun w => by
    rw [two_nsmul]; exact h2W w)
  haveI : Module (ZMod 2) W' := AddCommGroup.zmodModule (fun w => by
    rw [two_nsmul]; exact h2W' w)
  have hsmul_comm : ∀ (h : C) (z : ZMod 2) (u : W), h • (z • u) = z • (h • u) := by
    intro h z u
    rcases hz2 z with hz | hz <;> rw [hz]
    · rw [zero_smul, zero_smul, smul_zero]
    · rw [one_smul, one_smul]
  have hπz : ∀ (z : ZMod 2) (u : W), π (z • u) = z • π u := by
    intro z u
    rcases hz2 z with hz | hz <;> rw [hz]
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
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
    rcases hz2 (F n x) with hz | hz <;> rw [hz]
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
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
