/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Reconstruction

/-!
# Characteristic continuous characters

A character fixed by every automorphism can be transported through any
equivalence once it is matched by one equivalence.  This is a pure transport
principle: it does not assert that an arbitrary character is characteristic.
-/

namespace GQ2
noncomputable section

variable {G H A : Type*} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] [Group A] [TopologicalSpace A]

/-- A continuous character fixed by every continuous group automorphism. -/
def IsCharacteristicCharacter (chi : ContinuousMonoidHom G A) : Prop :=
  ∀ u : ContinuousMulEquiv G G, ∀ x, chi (u x) = chi x

/-- Transport characteristicness across one character-compatible equivalence. -/
theorem IsCharacteristicCharacter.of_equiv
    {chiG : ContinuousMonoidHom G A} {chiH : ContinuousMonoidHom H A}
    (hchi : IsCharacteristicCharacter chiG) (e : ContinuousMulEquiv G H)
    (he : ∀ x, chiH (e x) = chiG x) : IsCharacteristicCharacter chiH := by
  intro u y
  let v : ContinuousMulEquiv G G := (e.trans u).trans e.symm
  calc
    chiH (u y) = chiG (e.symm (u y)) := by simpa using he (e.symm (u y))
    _ = chiG (e.symm y) := by simpa [v] using hchi v (e.symm y)
    _ = chiH y := by simpa using (he (e.symm y)).symm

/-- Matching by one equivalence is enough to force matching by every equivalence.
The second equivalence need not preserve any independently chosen marking. -/
theorem IsCharacteristicCharacter.equiv_eq
    {chiG : ContinuousMonoidHom G A} {chiH : ContinuousMonoidHom H A}
    (hchi : IsCharacteristicCharacter chiG) (e₀ e : ContinuousMulEquiv G H)
    (he₀ : ∀ x, chiH (e₀ x) = chiG x) (x : G) : chiH (e x) = chiG x := by
  let u : ContinuousMulEquiv G G := e.trans e₀.symm
  calc
    chiH (e x) = chiH (e₀ (u x)) := by simp [u]
    _ = chiG (u x) := he₀ (u x)
    _ = chiG x := hchi u x

/-- Characteristicness is invariant under a character-compatible equivalence. -/
theorem isCharacteristicCharacter_iff_of_equiv
    (chiG : ContinuousMonoidHom G A) (chiH : ContinuousMonoidHom H A)
    (e : ContinuousMulEquiv G H) (he : ∀ x, chiH (e x) = chiG x) :
    IsCharacteristicCharacter chiG ↔ IsCharacteristicCharacter chiH := by
  constructor
  · exact fun h => h.of_equiv e he
  · intro h
    apply h.of_equiv e.symm
    intro y
    simpa using (he (e.symm y)).symm

#print axioms IsCharacteristicCharacter.of_equiv
#print axioms IsCharacteristicCharacter.equiv_eq
#print axioms isCharacteristicCharacter_iff_of_equiv

end
end GQ2
