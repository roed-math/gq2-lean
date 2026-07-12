import GQ2.TameQuotient
import GQ2.Tame
import GQ2.Prop32

/-!
# P-15f2c2c3 (N3): the tame 2-quotient factoring + the B10′ orientation package

The `nuT`-factoring brick of the analytic-`hunram` derivation (`docs/p15f2c2c-handoff.md`
§half-(B) step 4).  Three pieces:

* **(i) τ-death in 2-groups** *(pure finite group theory, axiom-free)*: any group hom
  `φ : Ttame →* Q` into a finite `2`-group `Q` kills `tameTau` — `φ tameTau = 1`.  From the
  pushed tame relation `(φ σ)⁻¹ (φ τ) (φ σ) = (φ τ)²`, `Tame.tame_odd_order` gives `orderOf (φ τ)`
  odd; in a `2`-group it is a power of `2`; odd ∧ `2`-power ⟹ `1`.

* **(ii) the factoring** *(axiom-free)*: any **continuous** `φ : Ttame → Q` into a finite discrete
  `2`-group factors through `nuT : Ttame → Ztwo` (the pro-`2` tame character).  [in progress]

* **(iii) `TameUnitOrientation`** *(std-3 + B10′)*: the B10′-clause shape, plus its discharge at
  the axiom witness `boundaryMapsWitness.tameF`.  [in progress]

No new axiom (user decision of record 2026-07-08); (i)+(ii) are std-3.
-/

namespace GQ2

open scoped Classical
open SectionThree

/-! ## (i) τ-death in a finite 2-group -/

/-- **τ-death** (P-15f2c2c3(i)): a group hom from `T_tame` into a finite `2`-group kills the
tame generator `τ`.  The tame relation `σ⁻¹ τ σ = τ²` pushes to `Q`, so `Tame.tame_odd_order`
makes `orderOf (φ τ)` **odd**; in the `2`-group `Q` it is a power of `2`; the only odd power of
`2` is `1`, so `φ τ = 1`.  Pure finite group theory — no topology, no axiom. -/
theorem map_tameTau_eq_one {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (φ : Ttame →* Q) : φ tameTau = 1 := by
  have hrel : (φ tameSigma)⁻¹ * φ tameTau * φ tameSigma = (φ tameTau) ^ 2 := by
    simpa only [conjP, map_mul, map_inv, map_pow] using congrArg φ tame_relation
  have hodd : Odd (orderOf (φ tameTau)) :=
    Tame.tame_odd_order (orderOf_pos (φ tameSigma)).ne' hrel
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) (φ tameTau)
  rw [hk] at hodd
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩))

/-! ## (ii) the factoring: continuous homs into a pro-2 group factor through `nuT`

Both `nuT` and any continuous hom into a pro-2 group factor through the maximal pro-2 quotient
`T_tame(2)`; and `nuT` induces there an isomorphism (its kernel is exactly the pro-2 kernel:
`ker nuT ≤ proPKernel 2 T_tame`).  Composing with `proPKernel_le_ker` gives the factoring. -/

/-- **`τ` dies in the maximal pro-2 quotient** `T_tame(2)`: `maxProPMk 2 T_tame τ = 1`.  By part (i)
`map_tameTau_eq_one`, `τ` lands in every open normal `U` with a `2`-group quotient, hence in the
pro-2 kernel. -/
theorem maxProPMk_tameTau : maxProPMk 2 Ttame tameTau = 1 := by
  refine (quotientMk_eq_one_iff (proPKernel 2 Ttame)).mpr ?_
  rw [proPKernel, Subgroup.mem_iInf]
  rintro ⟨U, hU⟩
  exact (QuotientGroup.eq_one_iff _).mp (map_tameTau_eq_one hU (QuotientGroup.mk' U.toSubgroup))

/-- **`ker ν_t ≤ proPKernel 2 T_tame`**: `maxProPMk : T_tame ↠ T_tame(2)` factors through
`ν_t : T_tame ↠ ℤ₂`.  Build `ρ' : ℤ₂ → T_tame(2)` from the `ẑ`-power hom `ẑ ↦ (maxProPMk σ)^ẑ`
(descended through `ℤ₂ = ẑ(2)`, the target being pro-2), matching `maxProPMk` on `σ` and (via
`maxProPMk_tameTau`) on `τ`; density on `{σ, τ}` gives `maxProPMk = ρ' ∘ ν_t`, so
`ν_t x = 1 ⟹ maxProPMk x = 1 ⟹ x ∈ proPKernel`. -/
theorem ker_nuT_le_proPKernel : GQ2.nuT.toMonoidHom.ker ≤ proPKernel 2 Ttame := by
  set s : maxProPQuotient 2 Ttame := maxProPMk 2 Ttame tameSigma
  let zhatHom : ContinuousMonoidHom Zhat (maxProPQuotient 2 Ttame) :=
    ⟨{ toFun := fun γ => s ^ᶻ γ, map_one' := zpowHat_one s,
       map_mul' := fun a b => zpowHat_mul s a b }, continuous_zpowHat s⟩
  let ρ' : ContinuousMonoidHom Ztwo (maxProPQuotient 2 Ttame) :=
    (maxProPHomEquiv (G := Zhat) isProP_maxProPQuotient).symm zhatHom
  have hρ : ∀ z : Zhat, ρ' (maxProPMk 2 Zhat z) = s ^ᶻ z := fun z => rfl
  have key : ∀ y, (maxProPMk 2 Ttame) y = (ρ'.comp GQ2.nuT) y := by
    refine monoidHom_eq_of_topGen (f := (maxProPMk 2 Ttame).toMonoidHom)
      (g := (ρ'.comp GQ2.nuT).toMonoidHom)
      (maxProPMk 2 Ttame).continuous_toFun (ρ'.comp GQ2.nuT).continuous_toFun topGen_ttame ?_
    rintro z (rfl | rfl)
    · show maxProPMk 2 Ttame tameSigma = ρ' (GQ2.nuT tameSigma)
      rw [nuT_tameSigma, show ztwoOne = maxProPMk 2 Zhat (Zhat.ofInt 1) from rfl, hρ,
        zpowHat_ofInt, zpow_one]
    · show maxProPMk 2 Ttame tameTau = ρ' (GQ2.nuT tameTau)
      rw [nuT_tameTau, map_one, maxProPMk_tameTau]
  intro x hx
  have hnuT : GQ2.nuT x = 1 := hx
  have hmk : maxProPMk 2 Ttame x = 1 := by
    rw [key x]; show ρ' (GQ2.nuT x) = 1; rw [hnuT, map_one]
  exact (QuotientGroup.eq_one_iff x).mp hmk

/-- **The factoring** (P-15f2c2c3(ii)): a continuous hom `φ : T_tame → Q` into a **pro-2** group
kills everything `ν_t` kills — `ν_t x = 1 ⟹ φ x = 1`.  (`ker ν_t ≤ proPKernel 2 T_tame ≤ ker φ`,
the second inclusion by `proPKernel_le_ker`.) -/
theorem map_eq_one_of_nuT_eq_one {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] (hQ : IsProP 2 Q)
    (φ : ContinuousMonoidHom Ttame Q) {x : Ttame} (hx : GQ2.nuT x = 1) : φ x = 1 :=
  proPKernel_le_ker hQ φ (ker_nuT_le_proPKernel hx)

/-- **The factoring, finite discrete 2-group form** — the shape the c2c4 unit-image argument
consumes (`Q` = the `2`-part quotient of `Gal(F₀/ℚ₂)`). -/
theorem map_eq_one_of_nuT_eq_one_finite {Q : Type*} [Group Q] [Finite Q] [TopologicalSpace Q]
    [DiscreteTopology Q] (hQ : IsPGroup 2 Q) (φ : ContinuousMonoidHom Ttame Q) {x : Ttame}
    (hx : GQ2.nuT x = 1) : φ x = 1 :=
  map_eq_one_of_nuT_eq_one (isProP_of_isPGroup hQ) φ hx

/-! ## (iii) the B10′ orientation clause -/

/-- **`TameUnitOrientation`** (P-15f2c2c3(iii)): the B10′ orientation clause for an arbitrary tame
coordinate `tameF : G_ℚ₂ → T_tame` — every local-reciprocity image of a `2`-adic **unit** is killed
by `ν_t ∘ tameF`.  For the axiom bundle's own tame coordinate this is `OrientedTameQuotient`'s
`nuT_recip_unit`; a general `B : BoundaryMaps` carries no reciprocity clause, so the moved
`lemma_6_17_vanish` threads `TameUnitOrientation localReciprocity B.tameF` as one hypothesis
(the `hc`/`hV2` precedent), discharged at `boundaryMapsWitness`. -/
def TameUnitOrientation (R : LocalReciprocity)
    (tameF : ContinuousMonoidHom AbsGalQ2 Ttame) : Prop :=
  ∀ (u : ℤ_[2]ˣ) (g : AbsGalQ2), toAb g = R.recip (unitEmbed u) → GQ2.nuT (tameF g) = 1

end GQ2
