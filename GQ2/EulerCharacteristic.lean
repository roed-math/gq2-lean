import GQ2.Cohomology
import GQ2.Statement
import GQ2.Foundations.Axioms

/-!
# B7 — the local Euler–Poincaré characteristic of `G_ℚ₂`  (ticket T-16, leaf B7)

This file states the **local Euler–Poincaré characteristic formula** for the absolute Galois group
`G_ℚ₂ = Gal(ℚ̄₂ / ℚ₂)` (`GQ2.AbsGalQ2`) as the classical literature leaf `B7` of Theorem 1.2,
together with its immediate consequences as stress tests.

## The axiom (B7)

For a **finite discrete** `G_ℚ₂`-module `M` — the module convention of `GQ2/DiscreteModule.lean`:
`[AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction AbsGalQ2 M]
[ContinuousSMul AbsGalQ2 M] [Finite M]` — the continuous-cochain cohomology groups
`Hⁱ(G_ℚ₂, M)` (`GQ2.ContCoh.H0/H1/H2`, Serre *Galois Cohomology* I §2.2) are **finite** for
`i = 0, 1, 2`, and

  `#H¹ = #H⁰ · #H² · 2 ^ v₂(#M)`,    where `v₂(#M) = padicValNat 2 (Nat.card M)`.

Equivalently the Euler characteristic `χ := #H⁰ · #H² / #H¹` equals `2 ^ (−v₂(#M)) = ‖#M‖_{ℚ₂}`,
the normalized `2`-adic absolute value of `#M`: only the `2`-part of `#M` survives (units have
absolute value `1`), which is exactly the `2 ^ v₂(#M)` factor.  Since `[ℚ₂ : ℚ₂] = 1`, the general
local formula `χ(k, A) = ‖#A‖_k = (#A) ^ (−[k : ℚ_p])` (the `p`-part) specializes to this.

## Citation & conventions

* **NSW [1], Ch. VII §7.3, Theorem (7.3.1) (Tate)**: for a finite `G_k`-module `A` of order prime
  to `char k`, `χ(k, A) = ‖#A‖_k`.  (Cross-refs: Serre, *Galois Cohomology*, Ch. II §5.7, Theorem 5;
  Milne, *Arithmetic Duality Theorems*, Thm I.2.8.)
* Cohomology is continuous-cochain cohomology (`GQ2.ContCoh`, Serre GC I §2.2); modules are the
  discrete-module classes of `GQ2/DiscreteModule.lean`.  `Nat.card` is the cardinality and
  `padicValNat 2 n = v₂(n)` is the `2`-adic valuation of `n`.
* **Finiteness is part of the axiom.**  It is a genuine input of Tate's theorem, not derivable from
  the `ContCoh` API (`H¹, H²` are subquotients of the *infinite* cochain spaces `G → M`, `G×G → M`).
  The `H⁰` clause *is* independently derivable (`H⁰ ≤ M`, and `M` is finite; see `finite_H0`) and is
  retained only to transcribe the literature statement verbatim.

## Used at (paper cross-reference)

Turturean, §9.2 — lifting through an elementary quotient `M`; the strict-decrease step, eq. (145).
For the elementary `𝔽₂`-modules there (`#M = 2 ^ dim M`) this reads `#H¹ = #H⁰ · #H² · #M`
(`card_H1_of_card_eq_two_pow`).

The axiom itself (`GQ2.Foundations.absGalQ2_localEulerCharacteristic`) lives in
`GQ2/Foundations/Axioms.lean` (T-19 consolidation); this file documents its conventions and
derives the consequences below from it.
-/

open GQ2.ContCoh

namespace GQ2.Foundations

/-! ## Consequences / stress tests

(The axiom `absGalQ2_localEulerCharacteristic` is stated in `GQ2/Foundations/Axioms.lean`.) -/

section Consequences

variable (M : Type*) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M]


/-- `B7`: finiteness of `H¹(G_ℚ₂, M)`. -/
theorem finite_H1 : Finite (H1 AbsGalQ2 M) :=
  (absGalQ2_localEulerCharacteristic M).2.1

/-- `B7`: finiteness of `H²(G_ℚ₂, M)`. -/
theorem finite_H2 : Finite (H2 AbsGalQ2 M) :=
  (absGalQ2_localEulerCharacteristic M).2.2.1

/-- `B7`, the Euler-characteristic identity `#H¹ = #H⁰ · #H² · 2 ^ v₂(#M)`. -/
theorem card_H1 : Nat.card (H1 AbsGalQ2 M)
    = Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) * 2 ^ padicValNat 2 (Nat.card M) :=
  (absGalQ2_localEulerCharacteristic M).2.2.2


/-- For a module whose order is a power of `2` (e.g. the elementary `𝔽₂`-modules of §9.2, where
`#M = 2 ^ dim M`), `B7` reads `#H¹ = #H⁰ · #H² · #M`. -/
theorem card_H1_of_card_eq_two_pow {k : ℕ} (hk : Nat.card M = 2 ^ k) :
    Nat.card (H1 AbsGalQ2 M)
      = Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) * Nat.card M := by
  rw [card_H1, hk, padicValNat.prime_pow]


end Consequences

end GQ2.Foundations
