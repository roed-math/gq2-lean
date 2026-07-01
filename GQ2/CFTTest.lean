import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
Smoke test for the `ClassFieldTheory` dependency (kbuzzard/ClassFieldTheory): confirm the local
field API imports and that `ℚ₂` is recognised as a non-archimedean local field.

NOTE: the `IsNonarchimedeanLocalField ℚ_[p]` instance is currently `sorry`'d *upstream* in
ClassFieldTheory, so this only exercises the import/typeclass wiring, not a rigorous proof.
-/

/-- `G_{ℚ₂}` again, plus the fact that `ℚ₂` is a non-archimedean local field (via the imported,
upstream-`sorry`'d instance). -/
example : IsNonarchimedeanLocalField ℚ_[2] := inferInstance
