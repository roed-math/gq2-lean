import GQ2.Dyadic.MarkedCore.NScalingAudit

/-!
# Exact relative boundary equation for the N word

This is an identity in every group and is uniform in the handle tail. It
isolates the equation a relative automorphism must preserve; it does not assert
that the displayed presentation is a proper pro-2 HNN extension or construct
any automorphism.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2

variable {P : Type*} [Group P]

/-- The stable-letter form of the exact N relator, before linearization. -/
theorem nWord_tail_eq_hnn (alpha : ℕ) (a b c d tail : P) :
    nWord alpha a b c d * tail =
      a^(1+2^alpha) * conjP a b * (commP c d * tail) := by
  have he : 2+2^alpha = (1+2^alpha)+1 := by omega
  rw [nWord, he, pow_succ]
  simp [commP, conjP, mul_assoc]

/-- Exact relation-preservation criterion. A unitary Alexander-module map alone
does not discharge this nonlinear relative boundary equation. -/
theorem nWord_tail_eq_one_iff_relativeBoundary (alpha : ℕ) (a b c d tail : P) :
    nWord alpha a b c d * tail = 1 ↔
      conjP a b = (a^(1+2^alpha))⁻¹ * (commP c d * tail)⁻¹ := by
  rw [nWord_tail_eq_hnn]
  constructor
  · intro hr
    calc
      conjP a b = (a^(1+2^alpha))⁻¹ *
          (a^(1+2^alpha) * conjP a b * (commP c d * tail)) *
          (commP c d * tail)⁻¹ := by group
      _ = (a^(1+2^alpha))⁻¹ * (commP c d * tail)⁻¹ := by rw [hr]; group
  · intro hr
    rw [hr]
    group

/-- The same exact criterion with an arbitrary, unchanged handle tail. -/
theorem nWord_handle_eq_one_iff_relativeBoundary (alpha h : ℕ)
    (a b c d : P) (u v : Fin h → P) :
    nWord alpha a b c d * handleWord u v = 1 ↔
      conjP a b = (a^(1+2^alpha))⁻¹ * (commP c d * handleWord u v)⁻¹ :=
  nWord_tail_eq_one_iff_relativeBoundary alpha a b c d _

#print axioms nWord_tail_eq_hnn
#print axioms nWord_tail_eq_one_iff_relativeBoundary
#print axioms nWord_handle_eq_one_iff_relativeBoundary

end GQ2.Dyadic.MarkedCore

