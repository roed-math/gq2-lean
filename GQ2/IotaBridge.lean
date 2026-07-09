import GQ2.Phase140.Obstruction
import GQ2.SectionSix
import GQ2.DeepPart

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

/-! ## The injectivity of `iotaF` — `mapCoeff2` of a coefficient bijection

`iotaF D = D.inv ∘ mapCoeff2 muTwoOfF2`; `D.inv` is an `AddEquiv` and `muTwoOfF2` is the
`𝔽₂ ≅ μ₂` coefficient bijection, so the missing piece is the degree-2 analog of
`DeepPart.mapCoeff1_injective` — coboundaries pull back along the (automatically continuous,
discrete-coefficient) inverse.  Homed here rather than `Cohomology.lean` to avoid a
foundational-file rebuild; generic over `AbsGalQ2`-coefficient bijections. -/

/-- **`mapCoeff2` of an equivariant additive bijection is injective** (the degree-2
`DeepPart.mapCoeff1_injective`): a `B²`-witness on the target pulls back along the inverse,
which is continuous because the coefficients are discrete. -/
theorem mapCoeff2_injective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A] [DiscreteTopology B]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    [DistribMulAction AbsGalQ2 B] [ContinuousSMul AbsGalQ2 B]
    (f : A →+ B) (hf : Continuous f)
    (hcompat : ∀ (g : AbsGalQ2) (a : A), f (g • a) = g • f a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    Function.Injective (mapCoeff2 f hf hcompat) := by
  rw [injective_iff_map_eq_zero]
  intro xq
  induction xq using QuotientAddGroup.induction_on with
  | H b =>
    intro hxq
    have hxq' : H2mk AbsGalQ2 B
        (Z2comap (ContinuousMonoidHom.id AbsGalQ2) f hf (fun g n => hcompat g n) b) = 0 := hxq
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp hxq'
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨ψ, hψC, hψ⟩ := AddSubgroup.mem_map.mp hmem
    -- pull the 1-cochain back along `f` (discrete coefficients ⟹ the section is continuous)
    set m : AbsGalQ2 → A := fun g => Function.surjInv hsurj (ψ g) with hm
    have hfm : ∀ g, f (m g) = ψ g := fun g => Function.surjInv_eq hsurj (ψ g)
    show H2mk AbsGalQ2 A b = 0
    refine (QuotientAddGroup.eq_zero_iff b).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine AddSubgroup.mem_map.mpr ⟨m, ?_, ?_⟩
    · show Continuous m
      have hcomp : m = (Function.surjInv hsurj) ∘ ψ := rfl
      rw [hcomp]
      exact continuous_of_discreteTopology.comp hψC
    · -- `δ¹ m = b` pointwise, by `f`-injectivity
      funext p
      apply hinj
      have hLHS : f ((dOne AbsGalQ2 A) m p) = (dOne AbsGalQ2 B) ψ p := by
        show f (p.1 • m p.2 - m (p.1 * p.2) + m p.1)
          = p.1 • ψ p.2 - ψ (p.1 * p.2) + ψ p.1
        rw [map_add, map_sub, hcompat, hfm, hfm, hfm]
      have hRHS := congrFun hψ p
      rw [hLHS, hRHS]
      rfl

/-- `muTwoOfF2` is surjective (`𝔽₂ ≅ μ₂`, via `DeepPart.zmodTwoEquivMuTwo`). -/
theorem muTwoOfF2_surjective : Function.Surjective ⇑SectionSix.muTwoOfF2 := by
  rw [DeepPart.muTwoOfF2_eq]
  exact DeepPart.zmodTwoEquivMuTwo.surjective

/-- **`iotaF D` is injective**: `D.inv` is an equivalence and `mapCoeff2 muTwoOfF2` is
injective (`mapCoeff2_injective` at the `𝔽₂ ≅ μ₂` bijection). -/
theorem iotaF_injective (D : TateDuality 2) : Function.Injective (iotaF D) := by
  have h2 : Function.Injective (mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology
      SectionSix.muTwoOfF2_equivariant) :=
    mapCoeff2_injective _ _ _ DeepPart.muTwoOfF2_injective muTwoOfF2_surjective
  exact D.inv.injective.comp h2

/-- **The abstract↔invariant obstruction bridge, unconditional** (P-16d6e4a §1(C) closed):
`iotaB φ = iotaF D (H²ofFun φ)` on continuous 2-cocycles over `G_ℚ₂`. -/
theorem iotaB_eq_iotaF (D : TateDuality 2)
    {φ : AbsGalQ2 × AbsGalQ2 → ZMod 2} (hφ : φ ∈ Z2 AbsGalQ2 (ZMod 2)) :
    iotaB φ = iotaF D (H2ofFun AbsGalQ2 φ) :=
  iotaB_eq_iotaF_of_injective D (iotaF_injective D) hφ

end SectionEight

end GQ2
