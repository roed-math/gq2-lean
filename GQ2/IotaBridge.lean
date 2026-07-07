import GQ2.PhaseObstruction
import GQ2.SectionSix

/-!
# P-16d6e4a, sub-lemma (C): the `ι_Γ ↔ inv_{ℚ₂}` obstruction bridge

The master-count / keystone layer measures the base-class obstruction with the **abstract**
coboundary indicator `iotaB` (`GQ2/PhaseObstruction.lean`); the §6 base-determinant layer
measures it with the **Tate invariant map** `iotaF ∘ H²ofFun` (`GQ2/SectionSix.lean`,
`Q0loc`).  On continuous 2-cocycles over `G_ℚ₂` the two agree, because `#H²(G_ℚ₂,𝔽₂) = 2` and
`iotaF D` is the invariant-map isomorphism.  This is the bridge that lets `prop_6_18`'s
`Q0loc`-Gauss-sum feed the `QZero` source-Gauss residue (P-16d6e4a; design
`docs/p16d6e4a-evaluation-design.md` §1(C)).

`iotaB_eq_iotaF_of_injective` is stated with the injectivity of `iotaF D` as an explicit
hypothesis — a self-contained, reusable form.  The injectivity itself (`iotaF D = D.inv ∘
mapCoeff2 muTwoOfF2`, both factors injective) is the enumerated remaining sub-obligation
`mapCoeff2_injective` (the degree-2 analog of `DeepPart.mapCoeff1_injective`).
-/

namespace GQ2

namespace SectionEight

open ContCoh SectionSix

/-- **The abstract↔invariant obstruction bridge** (P-16d6e4a §1(C)): on a continuous
2-cocycle `φ` over `G_ℚ₂`, the abstract coboundary indicator `iotaB φ` equals the Tate
invariant `iotaF D (H²ofFun φ)`, given `iotaF D` injective.  Both vanish exactly on `B²`, and
a `ZMod 2` value is determined by whether it is `0`. -/
theorem iotaB_eq_iotaF_of_injective (D : TateDuality 2)
    (hinj : Function.Injective (iotaF D))
    {φ : AbsGalQ2 × AbsGalQ2 → ZMod 2} (hφ : φ ∈ Z2 AbsGalQ2 (ZMod 2)) :
    iotaB φ = iotaF D (H2ofFun AbsGalQ2 φ) := by
  rw [H2ofFun_of_mem hφ]
  have hchar : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  refine hchar _ _ ?_
  rw [iotaB_eq_zero_iff, map_eq_zero_iff (iotaF D) hinj, H2mk_eq_zero_iff]

end SectionEight

end GQ2
