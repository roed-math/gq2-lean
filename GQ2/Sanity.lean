import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Data.Padics.PadicNumbers

/-!
Sanity check: the absolute Galois group of `ℚ₂` is expressible with current Mathlib.
`Field.absoluteGaloisGroup K := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`,
which for the characteristic-0 field `ℚ₂` is the genuine `Gal(ℚ₂^sep/ℚ₂) = G_{ℚ₂}`.
-/

open Field

/-- `G_{ℚ₂}`, the absolute Galois group of the 2-adic numbers. -/
noncomputable abbrev GQ2 : Type := absoluteGaloisGroup ℚ_[2]

-- It is a topological group (Krull topology), inheriting Mathlib's instances.
example : Group GQ2 := inferInstance
example : TopologicalSpace GQ2 := inferInstance
example : IsTopologicalGroup GQ2 := inferInstance
