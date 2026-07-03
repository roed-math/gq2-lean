import GQ2.Statement
import GQ2.ProfinitePresentation
import GQ2.Cohomology
import GQ2.HilbertSymbol
import GQ2.Reciprocity

/-!
# The axioms: classical literature inputs of Theorem 1.2  (ticket T-19)

**Every `axiom` of the GQ2 library lives in this file** (enforced by
`scripts/check_axioms.sh`).  Each one is a **classical, published** result that the paper's
proof of Theorem 1.2 rests on — the intended leaves once the paper's own §§3–9 argument is
granted.  The paper's own intermediate propositions (Prop. 1.1, Prop. 3.2, Thm. 4.2,
Lemma 10.1, …) are **not** here — they are the paper's contribution and live as sorried nodes
near `main_surjection_count`.

**How to read this for review (Hill/Buzzard).**  Each `axiom` below is a result that already
exists in the literature; the docstring gives the precise statement, the citation, and the
paper cross-reference.  The B-labels follow `docs/literature-axioms.md` (which also records the
dependency structure, paper App. D).  Current census — five axioms, faithfully stated against
current Mathlib plus this repo's `ContCoh` cohomology:

* **B1** `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` — `G_ℚ₂` top. f.g.
* **B2** `Foundations.cyclotomicCharacter_two_surjective` — 2-adic cyclotomic surjectivity.
* **B5** `localReciprocity` — the local-reciprocity bundle (defs in `GQ2/Reciprocity.lean`).
* **B7** `Foundations.absGalQ2_localEulerCharacteristic` — local Euler characteristic
  (cohomology from `GQ2/Cohomology.lean`).
* **B7′** `HilbertSymbol.hilbertSymbol_dyadic` — the dyadic Hilbert-symbol formula
  (defs in `GQ2/HilbertSymbol.lean`).

The remaining classical inputs are **not yet axiomatized** (statement infrastructure pending,
see `docs/tickets.md`): B3 Demushkin classification (the *definition* `IsDemushkin` is done —
`GQ2/Demushkin.lean`, T-09; the classification statement is T-10/T-11), B4 `G_ℚ₂(2) ≅ D₀`
(T-08), B6 local Tate duality (T-14), B8 the `π₁(ℙ¹∖{0,1,∞})` action (T-12), B9 Evens/Kahn
(T-18).  They are enumerated with precise statements and citations in
`docs/literature-axioms.md`.

Consumers derive consequences by importing this file; the derived stress tests live next to
their definitions (`GQ2/EulerCharacteristic.lean` for B7) or are parametrized over the bundle
and axiom-free (`GQ2/Reciprocity.lean` for B5).  B7′'s faithfulness check (the canonical value
`(-1,-1)₂ = -1`) is an anonymous `example`, kept below next to its axiom.

References (paper's bibliography):
[1] Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2015.  (NSW)
[2] Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
[3] Serre, *Structure de certains pro-p-groupes*, Sém. Bourbaki 252 (1962–64).
[4] Ribes–Zalesskiĭ, *Profinite Groups*, 2nd ed., Springer 2010.  (RZ)
[7] Serre, *Local Fields*, GTM 67, Springer 1979.
[CiA] Serre, *A Course in Arithmetic*, GTM 7, Springer 1973.
-/

open GQ2.ContCoh

namespace GQ2.Foundations

open scoped Classical

/-! ## B1, B2 — leaves stateable against bare Mathlib -/

/-- **[Classical — B1.]** The absolute Galois group of a `p`-adic local field is *topologically
finitely generated* (by `[K : ℚ_p] + 3` elements when `μ_p ⊆ K`).  For `K = ℚ₂` this is the
input `hfgG` that `main_presentation` feeds to `reconstruction`.

Citation: NSW [1], Ch. VII §7.5, Theorem (7.5.14) (Jannsen–Wingberg) — `G_k` has `N+3`
generators (`N=[k:ℚ_p]`) with the tame + one wild relation, so is topologically finitely
generated; also (7.5.11). Original: Jannsen–Wingberg, Invent. Math. 70 (1982/83), 71–98.
(Verified against the NSW PDF in `references/`.)

This is a genuine, faithful Lean statement: it is exactly the topological-finite-generation
predicate used throughout `Reconstruction.lean`. -/
axiom absGalQ2_isTopologicallyFinitelyGenerated :
    ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤

/-- **[Classical — B2.]** The `2`-adic cyclotomic character `Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective,
equivalently `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`.  This is the surjectivity used in the paper's
Lemma 3.6 (cyclotomic powering of the three peripheral inertia classes of `π₁(ℙ¹∖{0,1,∞})`).
Stated here against Mathlib's `cyclotomicCharacter 2` on an algebraic closure of `ℚ`.

Citation: `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ` via `a ↦ (ζ ↦ ζ^a)` (Washington, *Introduction to
Cyclotomic Fields*, 2nd ed., GTM 83, Ch. 2, Theorem 2.5, verified), whence the inverse limit
`Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`. -/
axiom cyclotomicCharacter_two_surjective :
    Function.Surjective
      (cyclotomicCharacter (L := AlgebraicClosure ℚ) 2)

/-! ## B7 — the local Euler–Poincaré characteristic

Statement conventions, citation discussion, and the derived stress tests
(`finite_H1`, `card_H1`, …) are in `GQ2/EulerCharacteristic.lean`, which imports this file. -/

/-- **[Classical — B7 (local Euler–Poincaré characteristic).]**  For every finite discrete
`G_ℚ₂`-module `M`, the continuous cohomology groups `Hⁱ(G_ℚ₂, M)` are finite for `i = 0, 1, 2`,
and

  `#H¹(G_ℚ₂, M) = #H⁰(G_ℚ₂, M) · #H²(G_ℚ₂, M) · 2 ^ v₂(#M)`.

Equivalently `χ := #H⁰ · #H² / #H¹ = ‖#M‖_{ℚ₂} = 2 ^ (−v₂(#M))`.

Citation: **NSW [1], Ch. VII §7.3, Theorem (7.3.1) (Tate)** (`χ(k, A) = ‖#A‖_k`); Serre,
*Galois Cohomology*, Ch. II §5.7 Theorem 5; Milne, *ADT* Thm I.2.8.  Paper: §9.2, eq. (145).
See `GQ2/EulerCharacteristic.lean` for conventions and for the (retained-for-faithfulness)
redundancy of the `H⁰`-finiteness clause. -/
axiom absGalQ2_localEulerCharacteristic (M : Type*) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M] :
    Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
      Nat.card (H1 AbsGalQ2 M)
        = Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) * 2 ^ padicValNat 2 (Nat.card M)

end GQ2.Foundations

namespace GQ2.HilbertSymbol

/-! ## B7′ — the dyadic Hilbert-symbol formula

`hilbertSymbol`, `ε`, `ω`, `unit2`, `unitCoe`, `signOf` and their unconditional theory live in
`GQ2/HilbertSymbol.lean`. -/

/-- **B7′ (dyadic Hilbert symbol), `[Classical.]`.**  Writing `a = 2^α u`, `b = 2^β v` with
`u, v ∈ ℤ₂ˣ`, the Hilbert symbol over `ℚ₂` is
`(a, b)₂ = (-1)^{ε(u) ε(v) + α ω(v) + β ω(u)}`.

Citation: **Serre, *A Course in Arithmetic* [CiA], Ch. III §1.2, Theorem 1** (the `p = 2`
case), with `ε, ω` the residue characters of Ch. II §3.3.  This is exactly the paper's
Lemma 3.5 formula for the cup product on `H¹(ℚ₂, μ₂)`.  Convention: `signOf` sends the
`𝔽₂`-valued exponent to `{±1} = ℤˣ`; every element of `ℚ₂ˣ` has the form `2^α u` (`α ∈ ℤ`,
`u ∈ ℤ₂ˣ`), so this determines the symbol on all of `ℚ₂ˣ × ℚ₂ˣ`. -/
axiom hilbertSymbol_dyadic (α β : ℤ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unit2 ^ α * unitCoe u) (unit2 ^ β * unitCoe v)
      = signOf (ε u * ε v + (α : ZMod 2) * ω v + (β : ZMod 2) * ω u)

/-- Faithfulness check on B7′: the axiom reproduces the canonical value `(-1, -1)₂ = -1` — the
one nontrivial diagonal entry, which anchors the paper's initial cup form `α² + βγ + γβ`.
(Depends on `hilbertSymbol_dyadic`, so this is an `example`, not part of the unconditional
API.) -/
example : hilbertSymbol (unitCoe (-1)) (unitCoe (-1)) = -1 := by
  have h := hilbertSymbol_dyadic 0 0 (-1) (-1)
  rw [zpow_zero, one_mul] at h
  rw [h, ε_neg_one, ω_neg_one]
  decide

end GQ2.HilbertSymbol

namespace GQ2

/-! ## B5 — the local reciprocity bundle

The bundle structure `LocalReciprocity` (with the convention table and the soundness note on
the profinite target of `ν_ur`) is defined in `GQ2/Reciprocity.lean`; its stress tests are
parametrized over an arbitrary bundle and are therefore axiom-free. -/

/-- **The B5 axiom.** Local class field theory for `ℚ₂` provides the reciprocity bundle.

Citation: NSW [1] (7.1.1)/(7.1.5); Serre *Local Fields* [7] Ch. XI–XIII.  Paper: Lemma 3.5,
eq. (13); Prop. 1.1. -/
axiom localReciprocity : LocalReciprocity

end GQ2
