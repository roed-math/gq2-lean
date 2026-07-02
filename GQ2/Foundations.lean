import GQ2.Statement
import GQ2.ProfinitePresentation

/-!
# Classical foundations (the literature "axioms" of Theorem 1.2)

This file collects the **classical, published** results that the paper's proof of Theorem 1.2 rests
on, i.e. the intended `sorry`/`axiom` *leaves* once the paper's own §§3–9 argument is granted.  The
paper's own intermediate propositions (Prop. 1.1, Prop. 3.2, Thm. 4.2, Lemma 10.1, …) are **not**
here — they are the paper's contribution and live as sorried nodes near `main_surjection_count`.
The point of this file is to make the *literature dependencies* explicit and, where Mathlib has the
types, machine-checkable.

**How to read this for review (Hill/Buzzard).**  Each `axiom` below is a result that already exists
in the literature; the docstring gives the precise statement and a citation.  Two of them are stated
faithfully against current Mathlib types (`absGalQ2_isTopologicallyFinitelyGenerated`,
`cyclotomicCharacter_two_surjective`).  The remaining classical inputs (Demushkin classification,
local reciprocity, local Tate duality, local Euler characteristic, the dyadic Hilbert symbol, Evens/
Stiefel–Whitney machinery, the Galois action on `π₁(ℙ¹∖{0,1,∞})`) need infrastructure that Mathlib
does not yet have, so a *faithful* Lean signature cannot be written today; they are enumerated with
precise statements and citations in `docs/literature-axioms.md` (and summarized at the bottom of this
file).  See that document for the full reviewable list and the dependency structure (paper App. D).

References (paper's bibliography):
[1] Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2015.  (NSW)
[2] Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
[3] Serre, *Structure de certains pro-p-groupes*, Sém. Bourbaki 252 (1962–64).
[4] Ribes–Zalesskiĭ, *Profinite Groups*, 2nd ed., Springer 2010.  (RZ)
[7] Serre, *Local Fields*, GTM 67, Springer 1979.
-/

namespace GQ2.Foundations

open scoped Classical

/-! ## Leaves that are faithfully stateable against current Mathlib -/

/-- **[Classical.]** The absolute Galois group of a `p`-adic local field is *topologically finitely
generated* (by `[K : ℚ_p] + 3` elements when `μ_p ⊆ K`).  For `K = ℚ₂` this is the input `hfgG` that
`main_presentation` feeds to `reconstruction`.

Citation: Jannsen–Wingberg, *Die Struktur der absoluten Galoisgruppe `p`-adischer Zahlkörper*,
Invent. Math. 70 (1982/83), 71–98 (the full presentation, so a fortiori finite generation); finite
generation alone is Jannsen, Invent. Math. 70 (1982), 53–69.  Reproduced in NSW [1], Ch. VII §7.5.

This is a genuine, faithful Lean statement: it is exactly the topological-finite-generation
predicate used throughout `Reconstruction.lean`. -/
axiom absGalQ2_isTopologicallyFinitelyGenerated :
    ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤

/-- **[Classical.]** The `2`-adic cyclotomic character `Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective, equivalently
`Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`.  This is the surjectivity used in the paper's Lemma 3.6 (cyclotomic
powering of the three peripheral inertia classes of `π₁(ℙ¹∖{0,1,∞})`).  Stated here against Mathlib's
`cyclotomicCharacter 2` on an algebraic closure of `ℚ`.

Citation: `Gal(ℚ(μ_{p^n})/ℚ) ≅ (ℤ/p^n)ˣ` (Washington, *Introduction to Cyclotomic Fields*, 2nd ed.,
GTM 83, Thm 2.5), whence the inverse limit `Gal(ℚ(μ_{p^∞})/ℚ) ≅ ℤ_pˣ`. -/
axiom cyclotomicCharacter_two_surjective :
    Function.Surjective
      (cyclotomicCharacter (L := AlgebraicClosure ℚ) 2)

end GQ2.Foundations
