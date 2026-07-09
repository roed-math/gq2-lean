import GQ2.Reciprocity
import GQ2.BoundaryFrame
import GQ2.BoundaryConstruction
import GQ2.LocalMarked
import GQ2.BoundaryMapsWitness

/-!
# §3 statements, marked-quotient half: Prop. 3.10 and Prop. 3.14  (ticket P-06, P-11 handoff)

Sorried statements of the paper's **Prop. 3.10** (maximal pro-2 quotient of `Γ_A` is `Π`,
eq. (20); marked local identification `(Π, ν₂) ≅ (G_{ℚ₂}(2), ν_ur)`, via Cor. 3.12) and
**Prop. 3.14** (fully marked tame and pro-2 quotients — the eq. (27) boundary epimorphisms),
phrased against P-11's `GQ2/BoundaryFrame.lean` def-layer (`Ttame`, `PiBd`, `nuT`, `nuTwo`,
`BoundaryMaps`), per the board handoff "P-06 states Prop 3.10/3.14 against these defs
(instantiation = P-09/P-10)".

Kept in a **separate file from `GQ2/SectionThree.lean`** only for commit sequencing: this file
imports the (at extraction time, not-yet-committed) `BoundaryFrame.lean`, while the core §3
statements depend only on step-1 modules.  Same logical home: everything here is in namespace
`GQ2.SectionThree`; the companion design note is `docs/section3-extraction.md` §"marked half".

Proof assignments (design note): `prop_3_10_gammaA`, `nuT_surjective`, `nuTwo_surjective` →
P-09; `prop_3_10_local_marked` → P-10 (route: Prop 1.1 + the Nielsen transform of
Prop. 3.11/Cor. 3.12 — not separately stated, they are proof steps — plus the `Z₂`-bridge
below); `prop_3_14` → P-09/P-10 jointly (the `BoundaryMaps` witness).
-/

namespace GQ2

namespace SectionThree

/-! ## Proposition 3.10 — the maximal pro-2 quotient of `Γ_A` is `Π`

Paper (20)/(21): `Π = ⟨σ, x₀, x₁ ∣ x₀^{σ²} x₀ [x₁,σ] = 1⟩_{pro-2}` with
`ν₂(σ, x₀, x₁) = (1, 0, 0)`.  The paper's proof: in a finite 2-group quotient Lemma 3.1
forces `τ = 1` and `ω₂` acts as the identity, so the auxiliary words collapse
(`u_i = x_i`, `d₀ = c₀ = d_g = h_c = 1`, `g₀ = σ²`, `h₀ = x₀^{σ²}x₀`) and relation (6)
becomes the relator of (20); conversely every finite quotient of (20) is admissible with
`τ = 1`. -/

/-- **Prop. 3.10, `Γ_A` half**: the maximal pro-2 quotient of `Γ_A` is `Π`, canonically —
the isomorphism matches the marked generators (`σ ↦ σ`, `x₀ ↦ x₀`, `x₁ ↦ x₁`; `τ` dies).
(Proof ticket P-09: the word-collapse computation above, through the T-06/T-21 bridges.) -/
theorem prop_3_10_gammaA :
    ∃ e : ContinuousMulEquiv (maxProPQuotient 2 GammaA) PiBd,
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.σ)) = piSigma ∧
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.τ)) = 1 ∧
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.x₀)) = piX0 ∧
      e (maxProPMk 2 GammaA (quotientMk NA univMarking.x₁)) = piX1 :=
  prop_3_10_gammaA_proved

/-- **Prop. 3.10, local half = Cor. 3.12 (fully marked form)**: `(Π, ν₂)` is isomorphic to
the fully unramified marked pair `(G_{ℚ₂}(2), ν_ur)`.  The `ℤ₂`-identification between the
two `ν`-targets (`Ztwo = maxProPQuotient 2 ℤ̂` on the boundary side, `Multiplicative ℤ₂` on
the B5 side) is quantified explicitly as a continuous isomorphism `ι` pinned by
`ι(1) = ofAdd 1`; the `ν_ur`-values are read through arbitrary lifts, as in `prop_1_1`.
(Proof ticket P-10: Prop. 1.1 + the Nielsen transform (23)/(24) of Prop. 3.11, plus the
`Ztwo ≅ ℤ₂` bridge — flagged as P-10 infrastructure in the design note.) -/
theorem prop_3_10_local_marked
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] (R : LocalReciprocity) :
    ∃ ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]),
      ι ztwoOne = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2]) ∧
      ∃ e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) PiBd,
        ∀ g : AbsGalQ2,
          R.nu_ur (toAb g) = ι (nuTwo (e (maxProPMk 2 AbsGalQ2 g))) :=
  prop_3_10_local_marked_proved R

/-! ## Proposition 3.14 — fully marked tame and pro-2 quotients

Paper: `ν_t : T_tame ↠ ℤ₂` (`σ ↦ 1, τ ↦ 0`) and `ν₂ : Π ↠ ℤ₂` (eq. (21)); for each source
`Γ ∈ {Γ_A, G_{ℚ₂}}` the tame and maximal pro-2 quotient maps may be chosen with equal
`ν`-composites — the common unramified character `ν_Γ : Γ ↠ ℤ₂`.  The chosen-maps data is
exactly P-11's `BoundaryMaps` bundle (eq. (27)); the two surjectivity claims below are the
`↠`-content of the displayed arrows (flagged in `BoundaryFrame.lean` as P-06/P-09 scope). -/

/- The two surjectivity claims — `ν_t : T_tame ↠ Z₂` (Prop. 3.14's arrow) and
`ν₂ : Π ↠ Z₂` (eq. (21)'s arrow) — are stated and **proved** in `GQ2/Prop32.lean`
(`GQ2.SectionThree.nuT_surjective`, `GQ2.SectionThree.nuTwo_surjective`, ticket P-09). -/

/-- **Prop. 3.14** (with Cor. 3.12 supplying the `G_{ℚ₂}`-side): the eq. (27) boundary data
exists — tame and maximal pro-2 quotient maps for both sources, `ν`-compatible, jointly
surjective onto the fibred boundary, with the `Γ_A`-side taking the marked generator values
and the `G_{ℚ₂}`-side pinned intrinsically (Lemma 3.3 2-core kernel; `proPKernel` kernel).
(Proof tickets P-09/P-10: instantiate `BoundaryMaps`.) -/
theorem prop_3_14 [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty BoundaryMaps :=
  prop_3_14_proved

end SectionThree

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Cor 3.12 = ⟦cor-relativeDemushkin⟧
  * eq. (20) = ⟦eq-Pi⟧
  * eq. (21) = ⟦eq-nu2⟧
  * eq. (27) = ⟦eq-boundarymap⟧
  * Lemma 3.1 = ⟦lem-tamefinite⟧
  * Lemma 3.3 = ⟦lem-o2tame⟧
  * Prop 1.1 = ⟦prop-markedDem⟧
  * Prop 3.10 = ⟦prop-pro2⟧
  * Prop 3.11 = ⟦prop-abstractDemushkin⟧
  * Prop 3.14 = ⟦prop-compatiblemarking⟧
-/
