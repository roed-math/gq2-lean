import GQ2.DyadicNielsen
import GQ2.PropOneOneAssembly

/-!
# Prop 3.10, local half: `(Π, ν₂) ≅ (G_{ℚ₂}(2), ν_ur)`  (ticket P-25)

Compose `prop_1_1` (`G_{ℚ₂}(2) ≅ D₀` with `ν_ur(a,s,y) = (−2,1,0)`, `GQ2/PropOneOneAssembly.lean`)
with the Nielsen isomorphism `d0PiEquiv : D₀ ≅ Π` (`GQ2/DyadicNielsen.lean`), and use the seam
`ztwoEquivPadic : Ztwo ≅ Multiplicative ℤ₂` (P-21) for `ι`.  The `ν`-compatibility is a density
argument on `D₀`'s three generators, matching the `prop_1_1` unramified coordinates against
`ν₂(σ,x₀,x₁) = (1,0,0)` transported through `d0PiEquiv` (`d0A ↦ x₀⁻¹σ⁻²`, `d0S ↦ σ`, `d0Y ↦ x₁`).
-/

namespace GQ2

namespace SectionThree

open scoped Classical

/-- `ζ = ztwoEquivPadic ztwoOne = ofAdd 1`. -/
theorem ztwoEquivPadic_ztwoOne :
    ztwoEquivPadic ztwoOne = Multiplicative.ofAdd (1 : ℤ_[2]) :=
  ztwoEquivPadic_ofInt_one

/-- The composite `H = ζ ∘ ν₂ : Π → Multiplicative ℤ₂`.  Pushing `H` (rather than `ζ`) through a
product avoids the `Ztwo`-def barrier: `H`'s `map_*` never expose the `Ztwo` intermediate. -/
noncomputable def zetaNuTwo : ContinuousMonoidHom PiBd (Multiplicative ℤ_[2]) :=
  (⟨ztwoEquivPadic.toMulEquiv.toMonoidHom, ztwoEquivPadic.continuous_toFun⟩ :
    ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp nuTwo

@[simp] lemma zetaNuTwo_piX0 : zetaNuTwo piX0 = 1 := by
  show ztwoEquivPadic (nuTwo piX0) = 1
  rw [nuTwo_piX0]; exact map_one _
@[simp] lemma zetaNuTwo_piX1 : zetaNuTwo piX1 = 1 := by
  show ztwoEquivPadic (nuTwo piX1) = 1
  rw [nuTwo_piX1]; exact map_one _
@[simp] lemma zetaNuTwo_piSigma : zetaNuTwo piSigma = Multiplicative.ofAdd (1 : ℤ_[2]) := by
  show ztwoEquivPadic (nuTwo piSigma) = _
  rw [nuTwo_piSigma, ztwoEquivPadic_ztwoOne]

lemma zetaNuTwo_apply (x : PiBd) : zetaNuTwo x = ztwoEquivPadic (nuTwo x) := rfl

/-- **Prop 3.10, local half** (proved): the boundary group `Π` with `ν₂` is the fully unramified
marked pair `(G_{ℚ₂}(2), ν_ur)`. -/
theorem prop_3_10_local_marked_proved
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] (R : LocalReciprocity) :
    ∃ ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]),
      ι ztwoOne = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2]) ∧
      ∃ e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) PiBd,
        ∀ g : AbsGalQ2,
          R.nu_ur (toAb g) = ι (nuTwo (e (maxProPMk 2 AbsGalQ2 g))) := by
  obtain ⟨e₁, hA, hS, hY⟩ := SectionThree.prop_1_1 (R := R)
  refine ⟨ztwoEquivPadic, ?_, e₁.trans d0PiEquiv, ?_⟩
  · show ztwoEquivPadic (maxProPMk 2 Zhat (Zhat.ofInt 1))
      = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2])
    rw [ztwoEquivPadic_ofInt_one, Int.cast_one]
  -- density lemma on `D₀`: `PropOneOne.nuUrBar ∘ e₁.symm = ζ ∘ ν₂ ∘ d0PiEquiv`
  have key : ∀ d : D0,
      PropOneOne.nuUrBar R (e₁.symm d) = ztwoEquivPadic (nuTwo (d0PiEquiv d)) := by
    have h := monoidHom_eq_of_topGen
      (f := ((PropOneOne.nuUrBar R).comp
        ⟨e₁.symm.toMulEquiv.toMonoidHom, e₁.symm.continuous_toFun⟩).toMonoidHom)
      (g := ((⟨ztwoEquivPadic.toMulEquiv.toMonoidHom, ztwoEquivPadic.continuous_toFun⟩ :
          ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp
        (nuTwo.comp ⟨d0PiEquiv.toMulEquiv.toMonoidHom, d0PiEquiv.continuous_toFun⟩)).toMonoidHom)
      (by exact ((PropOneOne.nuUrBar R).comp _).continuous_toFun)
      (by exact (_root_.ContinuousMonoidHom.comp _ _).continuous_toFun)
      topGen_d0 ?_
    · exact h
    · rintro z (rfl | rfl | rfl)
      · -- `A`: LHS `ofAdd (−2)`, RHS `(ζ²)⁻¹`
        show PropOneOne.nuUrBar R (e₁.symm d0A) = ztwoEquivPadic (nuTwo (d0PiEquiv d0A))
        obtain ⟨gA, hgA⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) (e₁.symm d0A)
        have hgA' : maxProPMk 2 AbsGalQ2 gA = e₁.symm d0A := hgA
        rw [← hgA', PropOneOne.nuUrBar_maxProPMk, hA gA hgA', ← zetaNuTwo_apply, d0PiEquiv_d0A,
          map_mul, map_inv, map_inv, map_pow, zetaNuTwo_piX0, zetaNuTwo_piSigma, inv_one, one_mul,
          ← ofAdd_nsmul, ← ofAdd_neg]
        congr 1
        push_cast [nsmul_eq_mul]; ring
      · -- `S`: both `ofAdd 1`
        show PropOneOne.nuUrBar R (e₁.symm d0S) = ztwoEquivPadic (nuTwo (d0PiEquiv d0S))
        obtain ⟨gS, hgS⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) (e₁.symm d0S)
        have hgS' : maxProPMk 2 AbsGalQ2 gS = e₁.symm d0S := hgS
        rw [← hgS', PropOneOne.nuUrBar_maxProPMk, hS gS hgS', d0PiEquiv_d0S, nuTwo_piSigma,
          ztwoEquivPadic_ztwoOne, Int.cast_one]
      · -- `Y`: both `1`
        show PropOneOne.nuUrBar R (e₁.symm d0Y) = ztwoEquivPadic (nuTwo (d0PiEquiv d0Y))
        obtain ⟨gY, hgY⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) (e₁.symm d0Y)
        have hgY' : maxProPMk 2 AbsGalQ2 gY = e₁.symm d0Y := hgY
        rw [← hgY', PropOneOne.nuUrBar_maxProPMk, hY gY hgY', d0PiEquiv_d0Y, nuTwo_piX1,
          show ztwoEquivPadic (1 : Ztwo) = 1 from map_one _, Int.cast_zero, ofAdd_zero]
  intro g
  have hkey := key (e₁ (maxProPMk 2 AbsGalQ2 g))
  rw [e₁.symm_apply_apply] at hkey
  rw [← PropOneOne.nuUrBar_maxProPMk R g, hkey]
  rfl

end SectionThree

end GQ2
