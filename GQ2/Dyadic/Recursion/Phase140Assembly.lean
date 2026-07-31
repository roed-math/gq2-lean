/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Phase140
import GQ2.Dyadic.Recursion.MasterCount
import GQ2.Phase140.Assembly

/-!
# The (140) residue assembly at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **`b`-typed layer** of `GQ2/Phase140/Assembly.lean` (292 ln), re-typed at the
general `K`-boundary, with the `#H¹` factor parameterized (memo §4.1(c)).

## Finding: 3 of the model's 8 declarations are spine (~150 of 292 ln)

* **boundary-free (consumed by import)** — `Enrichment.descData` (`:47`), `descSigma` (`:71`),
  `descSigma_spec` (`:76`), `descSections` (`:82`), `phaseChi` (`:88`), `card_TCharC_pos`
  (`:101`).  The whole per-`λ` descent construction, including the phase covers themselves, is
  below the boundary.
* **`b`-typed (cloned below)** — `rho0_descData_rhoPrime` (`:117`), `GaussZResidue` (`:145`),
  `hMobst_of_residues` (`:158`), `phase140_from_residues` (`:243`).

## Parameterization delta versus the `ℚ₂` model

This is the file where the memo §4.1(c) chain is consumed, in two places:

1. `hMobst_of_residuesK` takes `hZcard : #Z¹(V) = #V * vH` (model: `= #V * #V`) and calls
   `two_mul_card_centralImageN` (`MasterCount.lean`) in place of the model's
   `two_mul_card_centralImage` — this is that wrapper's **sole consumer**, matching the model's
   sole consumer at `GQ2/Phase140/Assembly.lean:191`.  Its conclusion's inner `#V` becomes `vH`.
2. `phase140_from_residuesK` passes `vH` to `phase140_of_phaseObstructionK` and, because that
   clone dropped the `hWV` pin, **does not pass `enrichment_card_Vmod`** — the model's `hWV`
   witness (`:280`) has no counterpart here.  `Nat.card En.Vmod` continues to play the outer
   `#B¹` role, unchanged (memo §1.3).

`GaussZResidueK`'s `#V · G0` normalization is the **outer** factor and does **not** move (memo
§4.1 non-movers, `Assembly.lean:145-149`).  Everything else is types only and verbatim.

`QuadraticFp2` is deliberately not opened here (see `MasterCount.lean`'s header): it exports a
second `sign`, and a clone outside `namespace GQ2.SectionEight` has no namespace tiebreak.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open AffineTLift CentralObstruction ContCoh

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-! ## The lower-map roundtrip -/

section Transport

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
variable (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- **The lower-map roundtrip** at the `K`-boundary: the `C₀`-descent of the transported lower map
is the original `C`-exact-image map.  Clone of `GQ2.SectionEight.rho0_descData_rhoPrime`
(`GQ2/Phase140/Assembly.lean:117`) — verbatim; `descData`, `liftC0`, `liftC0_mk` and `piBCiso_mk`
are boundary-free and are the model's, by import.

This is what aligns the master count's `ι_Γ(ρ'^*Δ)`-signs with `phaseSignK`'s lift-condition. -/
theorem rho0_descData_rhoPrimeK (ρ : BoundaryLiftsK b F RF.TC) (γ : Γ) :
    rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) γ = ρ.1.1 γ := by
  show liftC0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ γ) = ρ.1.1 γ
  rw [rhoPrimeK_apply]
  obtain ⟨bb, hbb⟩ :=
    QuotientGroup.mk_surjective ((RF.piBCiso (En.radData l h) rfl).symm (ρ.1.1 γ))
  rw [← hbb, liftC0_mk]
  show RF.piBC bb = ρ.1.1 γ
  have h2 : RF.piBCiso (En.radData l h) rfl (QuotientGroup.mk bb) = ρ.1.1 γ := by
    rw [hbb, MulEquiv.apply_symm_apply]
  rw [← RF.piBCiso_mk (En.radData l h) rfl bb]
  exact h2

end Transport

/-! ## The residue assembly -/

section Assembly

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
variable (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

/-- **The source-Gauss residue** at the `K`-boundary.  Clone of
`GQ2.SectionEight.GaussZResidue` (`GQ2/Phase140/Assembly.lean:145`) — verbatim.  The `#V · G0`
normalization is the **outer** `#B¹` factor and is degree-independent, so it does not move
(memo §1.3, §4.1 non-movers). -/
def GaussZResidueK (G0 : ℤ) : Prop :=
  ∀ ρ : BoundaryLiftsK b F RF.TC,
    ∑ᶠ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) c)
      = (Nat.card En.Vmod : ℤ) * G0

variable (Dsc : Descent (En.radData l h))

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The per-`ρ` phase-obstruction identity from the residues** at the `K`-boundary, at an
opaque `#H¹` factor `vH`.  Clone of `GQ2.SectionEight.hMobst_of_residues`
(`GQ2/Phase140/Assembly.lean:158`).

The master count is `two_mul_card_centralImageN` (`MasterCount.lean`) — the `vH`-parameterized
wrapper — in place of the model's `two_mul_card_centralImage`; this call is that wrapper's sole
consumer.  `hZcard`'s inner `#V` becomes `vH`, and so does the conclusion's.  Every other step
(the `±1`-to-signed-liftability rewrite through the roundtrip and the sign bridge) is verbatim. -/
theorem hMobst_of_residuesK
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (vH : ℕ) (G0 : ℤ)
    (hsep : ∀ ρ : BoundaryLiftsK b F RF.TC,
      ∀ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        (∀ χ : ↥(TCharC (En.radData l h)),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
          TLiftable (descSigma_spec En l h Dsc) c)
    (hpartial : ∀ ρ : BoundaryLiftsK b F RF.TC,
      ∀ χ : ↥(TCharC (En.radData l h)), χ ≠ 0 →
        ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
            ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
                (0 : VCocycle (En.descData l h)
                  (rhoPrimeK RF b F (En.radData l h) rfl ρ)))
    (hZcard : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * vH)
    (hGaussZ : ∀ ρ : BoundaryLiftsK b F RF.TC,
      ∑ᶠ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) c)
          = (Nat.card En.Vmod : ℤ) * G0)
    (ρ : BoundaryLiftsK b F RF.TC) :
    2 * (Nat.card ↥(TCharC (En.radData l h)) : ℤ)
        * (Nat.card ↥(Set.range
            (fun f : {f : MLifts (En.radData l h)
                (rhoPrimeK RF b F (En.radData l h) rfl ρ) // f.Central} =>
              redT (rhoPrimeK RF b F (En.radData l h) rfl ρ) f.1)) : ℤ)
      = (Nat.card En.Vmod : ℤ) * ((vH : ℤ)
          + G0 * ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
              phaseSignK RF b F (phaseChi En l h Dsc ζ) ρ) := by
  classical
  have hmc := two_mul_card_centralImageN
    (S := descSections En l h Dsc) (hσ := descSigma_spec En l h Dsc) (Dsc := Dsc)
    (ρ := rhoPrimeK RF b F (En.radData l h) rfl ρ)
    htriv hfg hH2 (hsep ρ)
    (betaChi_affine (descSections En l h Dsc) (descSigma_spec En l h Dsc) htriv hH2)
    (hpartial ρ)
    (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc))
    (shChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) (En.hinv l h))
    (keystone (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) (En.hinv l h)
      htriv hH2)
    vH G0 (hZcard ρ) (hGaussZ ρ)
  -- rewrite each `±1` to the signed liftability through the `phaseChi`-cover
  have hsign : ∀ ζ : ↥(TCharC (En.radData l h)),
      sign (iotaB (pullCoc
          (fun γ => rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) γ)
          (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)))
        = phaseSignK RF b F (phaseChi En l h Dsc ζ) ρ := by
    intro ζ
    have h1 : pullCoc (fun γ => rho0 (En.descData l h)
          (rhoPrimeK RF b F (En.radData l h) rfl ρ) γ)
          (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)
        = pullCoc (⇑(ρ.1.1))
            (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ) := by
      funext p
      show DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ
          (rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) p.1,
            rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) p.2)
        = DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ
            (ρ.1.1 p.1, ρ.1.1 p.2)
      rw [rho0_descData_rhoPrimeK b F En l h ρ p.1, rho0_descData_rhoPrimeK b F En l h ρ p.2]
    rw [h1, sign_iotaB_pullCoc_eq_lift_sign (Y0 := RF.YC) htriv
      (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)
      (DeltaChi_cocycle (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc)
        (En.hinv l h) ζ)
      (DeltaChi_one_left (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc)
        (En.hinv l h) ζ)
      (DeltaChi_one_right (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc)
        (En.hinv l h) ζ)
      ρ.1.1]
    rfl
  rw [show (∑ᶠ ζ : ↥(TCharC (En.radData l h)),
        phaseSignK RF b F (phaseChi En l h Dsc ζ) ρ)
      = ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
          sign (iotaB (pullCoc
            (fun γ => rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) γ)
            (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)))
      from finsum_congr fun ζ => (hsign ζ).symm]
  exact hmc

/-- **The (140) display from the residues** at the `K`-boundary, at an opaque `#H¹` factor `vH`.
Clone of `GQ2.SectionEight.phase140_from_residues` (`GQ2/Phase140/Assembly.lean:243`).

Two deltas versus the model, both from memo §4.1(c): `hZcard`'s inner `#V` is `vH`, and — because
`phase140_of_phaseObstructionK` dropped the `hWV` pin — the model's `enrichment_card_Vmod`
argument (`:280`) is simply **absent**.  `Nat.card En.Vmod` stays as the outer `#B¹` factor.

The conclusion is the `RecursionInputsK.phase140` field (`Recursion.lean:462`) at
`μ := Nat.card En.Vmod * μ₀`. -/
theorem phase140_from_residuesK
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (μ₀ vH : ℕ) (G0 : ℤ)
    (hμ : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) = μ₀)
    (hsep : ∀ ρ : BoundaryLiftsK b F RF.TC,
      ∀ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        (∀ χ : ↥(TCharC (En.radData l h)),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
          TLiftable (descSigma_spec En l h Dsc) c)
    (hpartial : ∀ ρ : BoundaryLiftsK b F RF.TC,
      ∀ χ : ↥(TCharC (En.radData l h)), χ ≠ 0 →
        ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
            ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
                (0 : VCocycle (En.descData l h)
                  (rhoPrimeK RF b F (En.radData l h) rfl ρ)))
    (hZcard : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * vH)
    (hGaussZ : ∀ ρ : BoundaryLiftsK b F RF.TC,
      ∑ᶠ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) c)
          = (Nat.card En.Vmod : ℤ) * G0) :
    2 * (Nat.card ↥(TCharC (En.radData l h)) : ℤ) * zBCK RF b F l h
      = (Nat.card En.Vmod * μ₀ : ℕ)
          * ((vH : ℕ) * exactImageCountK b F RF.TC
            + G0 * ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
                (2 * (nPhaseK RF b F (phaseChi En l h Dsc ζ) : ℤ)
                  - (exactImageCountK b F RF.TC : ℤ))) := by
  classical
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Fintype (BoundaryLiftsK b F RF.TC) := Fintype.ofFinite _
  haveI : Fintype ↥(TCharC (En.radData l h)) := Fintype.ofFinite _
  exact phase140_of_phaseObstructionK RF b F μ₀ G0 (↥(TCharC (En.radData l h)))
    (phaseChi En l h Dsc) l h (En.radData l h) rfl rfl Dsc htriv hfg
    (Nat.card En.Vmod) vH hμ
    (hMobst_of_residuesK b F En l h Dsc htriv hfg hH2 vH G0 hsep hpartial hZcard hGaussZ)

end Assembly

end GQ2.Dyadic
