/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
module

public import GQ2.Dyadic.SqCore.Cores
public import GQ2.Roe.DRWordCoh

@[expose] public section

/-!
# A finite quadratic witness that the square-core relator is not a square

The degree-two initial form of the improved square-core relator is

`y² + [x,s] + Σ [u_j,v_j]`.

This file detects already the rank-three part `y² + [x,s]` in an explicit finite two-group.
The target is a two-dimensional central extension of `V = 𝔽₂³`.  Its two square coordinates
are

`q₁(a) = a₀a₁`,  `q₂(a) = a₂ + a₁a₂`.

The relator has central value `(1,1)`, whereas the two quadratic functions never take `(1,1)`
simultaneously: `q₁(a)=1` forces `a₁=1`, and then `q₂(a)=0`.  Killing all added handle letters
therefore gives, uniformly in the handle count, a finite quotient in which the improved relator
is not a square.  Consequently the relator itself is not a square in the free profinite group.
-/

namespace GQ2.Dyadic.SqCore

open GQ2.DRCoh
open MarkedCore
open Multiplicative

noncomputable section

/-! ## The reusable finite-witness predicate -/

/-- A finite continuous quotient which detects that `w` is not a square. -/
def HasFiniteNonsquareWitness {X : Type} (w : FreeProfiniteGroup X) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : TopologicalSpace Q) (_ : IsTopologicalGroup Q)
      (_ : CompactSpace Q) (_ : T2Space Q) (_ : TotallyDisconnectedSpace Q),
    Finite Q ∧ ∃ f : ContinuousMonoidHom (FreeProfiniteGroup X) Q,
      ∀ q : Q, f w ≠ q ^ 2

/-- A finite nonsquare witness rules out a square in the free profinite group. -/
theorem not_isSquare_of_hasFiniteNonsquareWitness {X : Type} {w : FreeProfiniteGroup X}
    (hw : HasFiniteNonsquareWitness w) : ¬ ∃ z, w = z ^ 2 := by
  rintro ⟨z, rfl⟩
  obtain ⟨Q, _, _, _, _, _, _, _, f, hf⟩ := hw
  exact hf (f z) (by rw [map_pow])

/-! ## The explicit order-32 two-group -/

/-- The elementary abelian quotient on the three core letters. -/
abbrev InitialV := Multiplicative (Fin 3 → ZMod 2)

/-- First central coordinate, with square function `q₁(a)=a₀a₁`. -/
def initialCocycleOne : TwoCocycle InitialV where
  κ a b := toAdd a 0 * toAdd b 1
  norm := by decide
  cocyc a b c := by
    change toAdd a 0 * toAdd b 1 + (toAdd a 0 + toAdd b 0) * toAdd c 1 =
      toAdd a 0 * (toAdd b 1 + toAdd c 1) + toAdd b 0 * toAdd c 1
    ring

/-- Second central coordinate, with square function `q₂(a)=a₂+a₁a₂`. -/
def initialCocycleTwo : TwoCocycle InitialV where
  κ a b := toAdd a 2 * toAdd b 2 + toAdd a 1 * toAdd b 2
  norm := by decide
  cocyc a b c := by
    change (toAdd a 2 * toAdd b 2 + toAdd a 1 * toAdd b 2) +
        ((toAdd a 2 + toAdd b 2) * toAdd c 2 +
          (toAdd a 1 + toAdd b 1) * toAdd c 2) =
      (toAdd a 2 * (toAdd b 2 + toAdd c 2) +
          toAdd a 1 * (toAdd b 2 + toAdd c 2)) +
        (toAdd b 2 * toAdd c 2 + toAdd b 1 * toAdd c 2)
    ring

/-- The finite class-two test group, a two-dimensional central extension of `𝔽₂³`. -/
abbrev InitialFormTarget := FiberProd initialCocycleOne initialCocycleTwo

local instance : TopologicalSpace InitialFormTarget := ⊥
local instance : DiscreteTopology InitialFormTarget := ⟨rfl⟩
local instance : DecidableEq InitialFormTarget :=
  inferInstanceAs (DecidableEq (InitialV × ZMod 2 × ZMod 2))
local instance : Fintype InitialFormTarget :=
  inferInstanceAs (Fintype (InitialV × ZMod 2 × ZMod 2))

/-- The standard basis marking of `V=𝔽₂³`. -/
def initialBasis : Fin 3 → InitialV :=
  ![ofAdd ![1, 0, 0], ofAdd ![0, 1, 0], ofAdd ![0, 0, 1]]

/-- The zero-fibre lift of the standard basis to the two-coordinate central extension. -/
def initialCoreMark : Fin 3 → InitialFormTarget :=
  drLiftFP initialBasis initialCocycleOne initialCocycleTwo

/-- The first central coordinate of a square is `q₁(a)=a₀a₁`; the original fibre coordinate
cancels because it has characteristic two. -/
theorem initialFormTarget_sq_fibA (q : InitialFormTarget) :
    FiberProd.fibA (q ^ 2) = toAdd (FiberProd.base q) 0 * toAdd (FiberProd.base q) 1 := by
  rw [pow_two]
  change q.2.1 + q.2.1 +
      toAdd q.1 0 * toAdd q.1 1 = toAdd q.1 0 * toAdd q.1 1
  linear_combination CharTwo.add_self_eq_zero q.2.1

/-- The second central coordinate of a square is `q₂(a)=a₂+a₁a₂`. -/
theorem initialFormTarget_sq_fibB (q : InitialFormTarget) :
    FiberProd.fibB (q ^ 2) =
      toAdd (FiberProd.base q) 2 +
        toAdd (FiberProd.base q) 1 * toAdd (FiberProd.base q) 2 := by
  rw [pow_two]
  change q.2.2 + q.2.2 +
      (toAdd q.1 2 * toAdd q.1 2 + toAdd q.1 1 * toAdd q.1 2) =
        toAdd q.1 2 + toAdd q.1 1 * toAdd q.1 2
  have hsq : toAdd q.1 2 * toAdd q.1 2 = toAdd q.1 2 := by
    generalize toAdd q.1 2 = a
    revert a
    decide
  rw [hsq]
  linear_combination CharTwo.add_self_eq_zero q.2.2

/-- The rank-three core evaluates to the central vector `(1,1)`. -/
theorem sqWord_initialCoreMark :
    sqWord (initialCoreMark 0) (initialCoreMark 1) (initialCoreMark 2) =
      ((1, 1, 1) : InitialFormTarget) := by
  decide

/-- No square in the finite test group is the central vector `(1,1)`. -/
theorem initialFormTarget_sq_ne_relator (q : InitialFormTarget) :
    q ^ 2 ≠ ((1, 1, 1) : InitialFormTarget) := by
  intro h
  have hA := congrArg (fun x : InitialFormTarget => FiberProd.fibA x) h
  have hB := congrArg (fun x : InitialFormTarget => FiberProd.fibB x) h
  have hA' := (initialFormTarget_sq_fibA q).symm.trans hA
  have hB' := (initialFormTarget_sq_fibB q).symm.trans hB
  change toAdd (FiberProd.base q) 0 * toAdd (FiberProd.base q) 1 = 1 at hA'
  change toAdd (FiberProd.base q) 2 +
      toAdd (FiberProd.base q) 1 * toAdd (FiberProd.base q) 2 = 1 at hB'
  generalize toAdd (FiberProd.base q) 0 = a at hA'
  generalize toAdd (FiberProd.base q) 1 = b at hA' hB'
  generalize toAdd (FiberProd.base q) 2 = c at hB'
  revert a b c
  decide

/-! ## Uniform detection of every stabilized square-core relator -/

/-- Extend the three-letter marking by sending every handle letter to `1`. -/
def initialFormMark (h : ℕ) : Fin (sqRank h) → InitialFormTarget := fun i =>
  if hi : i.1 < 3 then initialCoreMark ⟨i.1, hi⟩ else 1

@[simp] theorem initialFormMark_zero (h : ℕ) : initialFormMark h 0 = initialCoreMark 0 := by
  simp [initialFormMark]

@[simp] theorem initialFormMark_one (h : ℕ) : initialFormMark h 1 = initialCoreMark 1 := by
  have hv : (1 : Fin (sqRank h)).val = 1 := by
    change 1 % sqRank h = 1
    exact Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
  simp only [initialFormMark, hv]
  congr 1

@[simp] theorem initialFormMark_two (h : ℕ) : initialFormMark h 2 = initialCoreMark 2 := by
  have hv : (2 : Fin (sqRank h)).val = 2 := by
    change 2 % sqRank h = 2
    exact Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
  simp only [initialFormMark, hv]
  congr 1

@[simp] theorem initialFormMark_handleU {h : ℕ} (j : Fin h) :
    initialFormMark h (sqHandleIdxU j) = 1 := by
  rw [initialFormMark]
  simp only [sqHandleIdxU]
  split
  · omega
  · rfl

@[simp] theorem initialFormMark_handleV {h : ℕ} (j : Fin h) :
    initialFormMark h (sqHandleIdxV j) = 1 := by
  rw [initialFormMark]
  simp only [sqHandleIdxV]
  split
  · omega
  · rfl

/-- Every stabilized relator evaluates to the same central vector `(1,1)`: the handles die. -/
theorem sqRelWord_initialFormMark (h : ℕ) :
    sqRelWord (initialFormMark h) = ((1, 1, 1) : InitialFormTarget) := by
  rw [sqRelWord, initialFormMark_zero, initialFormMark_one, initialFormMark_two,
    sqWord_initialCoreMark]
  have hh : handleWord
      (fun j => initialFormMark h (sqHandleIdxU j))
      (fun j => initialFormMark h (sqHandleIdxV j)) = 1 := by
    exact handleWord_of_one _ _ (fun j => initialFormMark_handleU j)
      (fun j => initialFormMark_handleV j)
  rw [hh, mul_one]

/-- The classified finite quotient sends `sqRelator h` to the central vector `(1,1)`. -/
theorem freeHomFin_sqRelator_initialFormMark (h : ℕ) :
    freeHomFin (initialFormMark h) (sqRelator h) = ((1, 1, 1) : InitialFormTarget) := by
  rw [sqRelator, map_sqRelWord]
  rw [show (fun i => (freeHomFin (initialFormMark h)) (FreeProfiniteGroup.of i)) =
      initialFormMark h from funext fun i => freeHomFin_of _ i]
  exact sqRelWord_initialFormMark h

/-- The order-32 test target is a finite two-group, hence a pro-two group with its discrete
topology.  This is the factorization input needed to detect nonsquareness after passing from the
free profinite group to its maximal pro-two quotient. -/
theorem isProP_initialFormTarget : IsProP 2 InitialFormTarget := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isProP_of_isPGroup ((IsPGroup.iff_card (p := 2)).mpr ⟨5, ?_⟩)
  rw [Nat.card_eq_fintype_card]
  decide

/-- The improved square-core relator has a concrete finite nonsquare witness, uniformly in `h`. -/
theorem sqRelator_hasFiniteNonsquareWitness (h : ℕ) :
    HasFiniteNonsquareWitness (sqRelator h) := by
  refine ⟨InitialFormTarget, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, freeHomFin (initialFormMark h), ?_⟩
  intro q
  rw [freeHomFin_sqRelator_initialFormMark]
  exact fun heq => initialFormTarget_sq_ne_relator q heq.symm

/-- **Non-power theorem for the improved presentation.**  For every handle count, the explicit
relator `SqCore.sqRelator h` is not a square in the free profinite group.  The separate pro-two
strengthening is proved below using the target's two-group structure. -/
theorem sqRelator_not_square (h : ℕ) : ¬ ∃ z, sqRelator h = z ^ 2 :=
  not_isSquare_of_hasFiniteNonsquareWitness (sqRelator_hasFiniteNonsquareWitness h)

/-! ## The actual free pro-two initial-form statement -/

/-- The finite witness map factored through the maximal pro-two quotient. -/
noncomputable def initialFormProTwoHom (h : ℕ) :
    ContinuousMonoidHom (maxProPQuotient 2 (FreeProfiniteGroup (Fin (sqRank h))))
      InitialFormTarget :=
  (maxProPHomEquiv isProP_initialFormTarget).symm (freeHomFin (initialFormMark h))

/-- The pro-two factorization still sends the relator to the nonsquare central vector `(1,1)`. -/
theorem initialFormProTwoHom_relator (h : ℕ) :
    initialFormProTwoHom h
        (maxProPMk 2 (FreeProfiniteGroup (Fin (sqRank h))) (sqRelator h)) =
      ((1, 1, 1) : InitialFormTarget) := by
  rw [initialFormProTwoHom, maxProPHomEquiv_symm_apply_maxProPMk,
    freeHomFin_sqRelator_initialFormMark]

/-- **Free pro-two non-power theorem.**  The image of the improved relator in the free pro-two
group is not a square.  This is the literal non-power condition used by one-relator pro-two
asphericity/cohomological-dimension theorems. -/
theorem sqRelator_maxProTwo_not_square (h : ℕ) :
    ¬ ∃ z : maxProPQuotient 2 (FreeProfiniteGroup (Fin (sqRank h))),
      maxProPMk 2 (FreeProfiniteGroup (Fin (sqRank h))) (sqRelator h) = z ^ 2 := by
  rintro ⟨z, hz⟩
  have hm := congrArg (initialFormProTwoHom h) hz
  rw [initialFormProTwoHom_relator, map_pow] at hm
  exact initialFormTarget_sq_ne_relator (initialFormProTwoHom h z) hm.symm

end

end GQ2.Dyadic.SqCore
