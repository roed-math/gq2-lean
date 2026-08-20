/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRPWordNielsen

/-!
# Elementary syntactic Nielsen transformations

This module supplies reusable operations on `PWordNielsenPair`: alphabet relabeling,
inversion, composition, and a profinite right transvection.  The latter replaces one
letter `a` by `a * b^γ`, fixes every other letter, and uses exponent `γ⁻¹` for the
inverse substitution.  A specialization embeds `ℤ₂` through `padicOmega2`.

These are presentation-level operations.  They make no reference to a nilpotency class
or to a particular dyadic row, and are intended for changing the word together with a
mobile field marking.
-/

namespace GQ2.Dyadic.Instances.GammaRPWordNielsenElementary

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Instances.GammaRPWordNielsen

/-- Relabel the alphabet by an equivalence. -/
def PWordNielsenPair.ofEquiv {n : ℕ} (e : Generator n ≃ Generator n) :
    PWordNielsenPair n where
  forward g := .gen (e g)
  backward g := .gen (e.symm g)
  backward_forward g := by simp
  forward_backward g := by simp

/-- Swap the forward and backward substitutions. -/
def PWordNielsenPair.symm {n : ℕ} (T : PWordNielsenPair n) :
    PWordNielsenPair n where
  forward := T.backward
  backward := T.forward
  backward_forward := T.forward_backward
  forward_backward := T.backward_forward

/-- The inverse substitutions cancel after evaluation on every word. -/
theorem PWordNielsenPair.backward_forward_word {n : ℕ} (T : PWordNielsenPair n)
    (w : PWord (Generator n)) :
    (freeMarking n).eval (PWord.subst T.backward (PWord.subst T.forward w)) =
      (freeMarking n).eval w := by
  rw [← freeWordHom_eval T.backward (PWord.subst T.forward w)]
  rw [← freeWordHom_eval T.forward w]
  change T.freeEquiv.symm (T.freeEquiv ((freeMarking n).eval w)) = _
  simp

/-- The opposite composite also cancels after evaluation on every word. -/
theorem PWordNielsenPair.forward_backward_word {n : ℕ} (T : PWordNielsenPair n)
    (w : PWord (Generator n)) :
    (freeMarking n).eval (PWord.subst T.forward (PWord.subst T.backward w)) =
      (freeMarking n).eval w := by
  rw [← freeWordHom_eval T.forward (PWord.subst T.backward w)]
  rw [← freeWordHom_eval T.backward w]
  change T.freeEquiv (T.freeEquiv.symm ((freeMarking n).eval w)) = _
  simp

/-- Compose two syntactic Nielsen pairs. -/
def PWordNielsenPair.trans {n : ℕ} (T U : PWordNielsenPair n) :
    PWordNielsenPair n where
  forward g := PWord.subst U.forward (T.forward g)
  backward g := PWord.subst T.backward (U.backward g)
  backward_forward g := by
    rw [← subst_subst T.backward U.backward]
    rw [← freeWordHom_eval T.backward]
    rw [backward_forward_word U]
    rw [freeWordHom_eval]
    exact T.backward_forward g
  forward_backward g := by
    rw [← subst_subst U.forward T.forward]
    rw [← freeWordHom_eval U.forward]
    rw [forward_backward_word T]
    rw [freeWordHom_eval]
    exact U.forward_backward g

/-- Evaluate the free profinite group at an arbitrary profinite marking. -/
noncomputable def freeEvalHom {n : ℕ} {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (t : Marking n G) :
    FreeProfiniteGroup (Generator n) ⟶ ProfiniteGrp.of G :=
  (FreeProfiniteGroup.homEquiv (Generator n) (ProfiniteGrp.of G)).symm ⇑t

@[simp] theorem freeEvalHom_of {n : ℕ} {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (t : Marking n G) (g : Generator n) :
    freeEvalHom t (FreeProfiniteGroup.of g) = t g :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem freeEvalHom_eval {n : ℕ} {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (t : Marking n G) (w : PWord (Generator n)) :
    freeEvalHom t ((freeMarking n).eval w) = t.eval w := by
  rw [Marking.map_eval]
  congr 1
  exact Marking.ext fun g => freeEvalHom_of t g

/-- The first inverse composite cancels at every profinite marking. -/
theorem PWordNielsenPair.backward_forward_eval {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)
    (w : PWord (Generator n)) :
    t.eval (PWord.subst T.backward (PWord.subst T.forward w)) = t.eval w := by
  rw [← freeEvalHom_eval t, ← freeEvalHom_eval t]
  exact congrArg (freeEvalHom t) (backward_forward_word T w)

/-- The opposite inverse composite cancels at every profinite marking. -/
theorem PWordNielsenPair.forward_backward_eval {n : ℕ} (T : PWordNielsenPair n)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G)
    (w : PWord (Generator n)) :
    t.eval (PWord.subst T.forward (PWord.subst T.backward w)) = t.eval w := by
  rw [← freeEvalHom_eval t, ← freeEvalHom_eval t]
  exact congrArg (freeEvalHom t) (forward_backward_word T w)

/-- The forward substitution for a right transvection. -/
def rightShearForward {n : ℕ} (a b : Generator n) (γ : Zhat) :
    Generator n → PWord (Generator n) := fun g =>
  if g = a then .mul (.gen a) (.profPow (.gen b) γ) else .gen g

/-- The inverse substitution for a right transvection. -/
def rightShearBackward {n : ℕ} (a b : Generator n) (γ : Zhat) :
    Generator n → PWord (Generator n) :=
  rightShearForward a b γ⁻¹

/-- Multiplying one letter by a profinite power of another is a Nielsen pair. -/
def PWordNielsenPair.rightShear {n : ℕ} (a b : Generator n) (hab : a ≠ b)
    (γ : Zhat) : PWordNielsenPair n where
  forward := rightShearForward a b γ
  backward := rightShearBackward a b γ
  backward_forward g := by
    classical
    by_cases hg : g = a
    · subst g
      simp [rightShearForward, rightShearBackward, hab.symm, mul_assoc,
        ← zpowHat_mul]
    · simp [rightShearForward, rightShearBackward, hg]
  forward_backward g := by
    classical
    by_cases hg : g = a
    · subst g
      simp [rightShearForward, rightShearBackward, hab.symm, mul_assoc,
        ← zpowHat_mul]
    · simp [rightShearForward, rightShearBackward, hg]

/-- The `ℤ₂` right transvection, embedded in the profinite exponent group. -/
def PWordNielsenPair.rightShearZtwo {n : ℕ} (a b : Generator n)
    (hab : a ≠ b) (k : ℤ_[2]) : PWordNielsenPair n :=
  PWordNielsenPair.rightShear a b hab (padicOmega2 k)

#print axioms PWordNielsenPair.ofEquiv
#print axioms PWordNielsenPair.symm
#print axioms PWordNielsenPair.backward_forward_word
#print axioms PWordNielsenPair.forward_backward_word
#print axioms PWordNielsenPair.trans
#print axioms PWordNielsenPair.backward_forward_eval
#print axioms PWordNielsenPair.forward_backward_eval
#print axioms PWordNielsenPair.rightShear
#print axioms PWordNielsenPair.rightShearZtwo

end

end GQ2.Dyadic.Instances.GammaRPWordNielsenElementary
