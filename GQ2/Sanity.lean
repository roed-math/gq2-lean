import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
Sanity check: the absolute Galois group of `ℚ₂` is expressible with current Mathlib.
`Field.absoluteGaloisGroup K := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`,
which for the characteristic-0 field `ℚ₂` is the genuine `Gal(ℚ₂^sep/ℚ₂) = G_{ℚ₂}`.
-/

open Field

/-- `G_{ℚ₂}`, the absolute Galois group of the 2-adic numbers. -/
noncomputable abbrev GQ2 : Type := absoluteGaloisGroup ℚ_[2]

-- It is a topological group (Krull topology), inheriting Mathlib's instances.
-- (Each check is a separate `Prop` goal, so there is no code generation for the noncomputable
-- Galois-group instances and no local-instance shadowing between the checks.)
example : Nonempty (Group GQ2) := ⟨inferInstance⟩
example : Nonempty (TopologicalSpace GQ2) := ⟨inferInstance⟩
example : Nonempty (IsTopologicalGroup GQ2) := ⟨inferInstance⟩
