import GQ2.KeystoneDelta

/-!
# P-16d6e: the generic (140) assembly

The source-generic wiring from the keystone chain (P-16d6c) to the
`RecursionInputs.phase140` field, per `(l, h)` in the zero-edge case:

* **`Enrichment.descData`** — the `DescData (En.radData l h)` repackaging of the enrichment
  (1:1 fields; `ker_piBC` supplies `hkerC0`);
* **`descSigma`/`descSections`** — the chosen descended splitting (`descended_splitting`,
  Lemma 6.21) and normalized count-sections;
* **`phaseChi`** — the per-`(l,h)` phase-cover family
  `ζ ↦ centralCoverOfCocycle (Δ_{ζ,κ_λ})` from the landed `DeltaChi` data;
* **`rho0_descData_rhoPrime`** — the transported lower map's `C₀`-descent is the original
  `C`-lift (`rho0 ∘ rhoPrime = ρ.1.1`), which makes the master count's sign match
  `phaseSign` on the nose through `sign_iotaB_pullCoc_eq_lift_sign`;
* **`hMobst_of_residues`** — the per-`ρ` phase-obstruction identity, from
  `two_mul_card_centralImage` at `Δ := DeltaChi`, `sh := shChi`, `hkey := keystone`;
* **`phase140_from_residues`** — the `phase140`-field display via
  `phase140_of_phaseObstruction`, parametric over the per-source residues
  `{htriv, hfg, hH2, hsep, hpartial, hZcard, hGaussZ, hμ}`.

All source-generic; the per-source leaves discharge the residues.
-/

namespace GQ2

namespace SectionEight

open AffineTLift CentralObstruction ContCoh

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}

/-- **The descent datum of the enrichment** (design §8): the `DescData` repackaging of
`En` at `(l, h)` — `C₀ := C`-stage, `piC₀ := π_{BC}` (kernel `M_B` by `ker_piBC`), and the
descended module/form/factor-set fields verbatim. -/
noncomputable def RecursionFrame.Enrichment.descData (En : RF.Enrichment) (l : RF.DR)
    (h : l ≠ RF.zeroDR) : DescData (En.radData l h) where
  C0 := RF.YC
  piC0 := RF.piBC
  hpiC0 := RF.piBC_surj
  hkerC0 := RF.ker_piBC
  Vmod := En.Vmod
  descend := En.descend
  hdesc_surj := En.descend_surj
  hdesc_ker := En.descend_ker
  hdesc_conj := En.descend_conj
  qbar := En.qbar l h
  hqbar := En.hqbar l h
  hquad := En.hquad l h
  hns := En.hns l h
  dat := En.dat l h
  hdat := En.hdat l h

section PerLambda

variable (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
variable (Dsc : Descent (En.radData l h))

/-- The chosen descended splitting `σ : C₀ →* Q` (Lemma 6.21 in the zero-edge regime). -/
noncomputable def descSigma : (En.descData l h).C0 →* RF.YB ⧸ (En.radData l h).T :=
  (descended_splitting Dsc (En.descData l h)).choose

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
theorem descSigma_spec :
    ∀ cc : (En.descData l h).C0,
      piQbar (En.descData l h) (descSigma En l h Dsc cc) = cc :=
  (descended_splitting Dsc (En.descData l h)).choose_spec

/-- The chosen normalized count-sections over `descSigma`. -/
noncomputable def descSections : CountSections (En.descData l h) (descSigma En l h Dsc) :=
  (countSections_exist (En.descData l h) (descSigma En l h Dsc)).some

/-- **The per-`(l,h)` phase-cover family** (the paper's `ζ ↦ C_{Δ_{ζ,κ_λ}}`): the twisted
product of the landed total scalar phase `Δ_ζ`, with the cocycle law and normalizations
from the keystone file. -/
noncomputable def phaseChi (ζ : ↥(TCharC (En.radData l h))) : CentralCover RF.YC :=
  centralCoverOfCocycle
    (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)
    (DeltaChi_cocycle (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc)
      (En.hinv l h) ζ)
    (DeltaChi_one_left (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc)
      (En.hinv l h) ζ)
    (DeltaChi_one_right (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc)
      (En.hinv l h) ζ)

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The phase index is nonempty: `0 < #(T^∨)^C` (the P-17i strengthening's supplier). -/
theorem card_TCharC_pos : 0 < Nat.card ↥(TCharC (En.radData l h)) := by
  haveI : Nonempty ↥(TCharC (En.radData l h)) := ⟨0⟩
  exact Nat.card_pos

end PerLambda

section Transport

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
variable (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] in
/-- **The lower-map roundtrip**: the `C₀`-descent of the transported lower map is the
original `C`-exact-image map — `rho0 (descData) (rhoPrime ρ) = ρ.1.1`.  This is what aligns
the master count's `ι_Γ(ρ'^*Δ)`-signs with `phaseSign`'s lift-condition at `ρ.1.1`. -/
theorem rho0_descData_rhoPrime (ρ : BoundaryLifts b F RF.TC) (γ : Γ) :
    rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = ρ.1.1 γ := by
  show liftC0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ γ) = ρ.1.1 γ
  rw [RecursionFrame.rhoPrime_apply]
  obtain ⟨bb, hbb⟩ :=
    QuotientGroup.mk_surjective ((RF.piBCiso (En.radData l h) rfl).symm (ρ.1.1 γ))
  rw [← hbb, liftC0_mk]
  show RF.piBC bb = ρ.1.1 γ
  have h2 : RF.piBCiso (En.radData l h) rfl (QuotientGroup.mk bb) = ρ.1.1 γ := by
    rw [hbb, MulEquiv.apply_symm_apply]
  rw [← RF.piBCiso_mk (En.radData l h) rfl bb]
  exact h2

end Transport

section Assembly

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
variable (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

/-- **The source-Gauss residue** (P-16d6e4): the exact `hGaussZ` input of
`phase140_from_residues` — `∑ᶠ c : Z¹_{Γ,ρ'}(V), sign(Q⁰ c) = #V · G0` at every lower map.
By P-16d6e4's layer (I) (`gaussZ_reduction`) this reduces to `∑_{Z¹⧸B¹} sign(Q̄⁰) = G0`, the
(83)-evaluation `G0 = ∓2^m` (P-16d6e4a).  A named abbreviation so the `prop_8_9` ledger stays
readable. -/
def GaussZResidue (G0 : ℤ) : Prop :=
  ∀ ρ : BoundaryLifts b F RF.TC,
    ∑ᶠ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) c)
      = (Nat.card En.Vmod : ℤ) * G0

variable (Dsc : Descent (En.radData l h))

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The per-`ρ` phase-obstruction identity from the residues** (the `hMobst` of the
paper-faithful (140) reducer): the master count `two_mul_card_centralImage` at the keystone
data (`Δ := DeltaChi`, `sh := shChi`, `hkey := keystone`), with each `±1` rewritten to the
signed liftability through the `phaseChi`-cover via the roundtrip and the sign bridge. -/
theorem hMobst_of_residues
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (G0 : ℤ)
    (hsep : ∀ ρ : BoundaryLifts b F RF.TC,
      ∀ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
        (∀ χ : ↥(TCharC (En.radData l h)),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
          TLiftable (descSigma_spec En l h Dsc) c)
    (hpartial : ∀ ρ : BoundaryLifts b F RF.TC,
      ∀ χ : ↥(TCharC (En.radData l h)), χ ≠ 0 →
        ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
            ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
                (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)))
    (hZcard : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * Nat.card En.Vmod)
    (hGaussZ : ∀ ρ : BoundaryLifts b F RF.TC,
      ∑ᶠ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) c)
          = (Nat.card En.Vmod : ℤ) * G0)
    (ρ : BoundaryLifts b F RF.TC) :
    2 * (Nat.card ↥(TCharC (En.radData l h)) : ℤ)
        * (Nat.card ↥(Set.range
            (fun f : {f : MLifts (En.radData l h)
                (RF.rhoPrime b F (En.radData l h) rfl ρ) // f.Central} =>
              redT (RF.rhoPrime b F (En.radData l h) rfl ρ) f.1)) : ℤ)
      = (Nat.card En.Vmod : ℤ) * ((Nat.card En.Vmod : ℤ)
          + G0 * ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
              phaseSign RF b F (phaseChi En l h Dsc ζ) ρ) := by
  classical
  have hmc := two_mul_card_centralImage
    (S := descSections En l h Dsc) (hσ := descSigma_spec En l h Dsc) (Dsc := Dsc)
    (ρ := RF.rhoPrime b F (En.radData l h) rfl ρ)
    htriv hfg hH2 (hsep ρ)
    (betaChi_affine (descSections En l h Dsc) (descSigma_spec En l h Dsc) htriv hH2)
    (hpartial ρ)
    (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc))
    (shChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) (En.hinv l h))
    (keystone (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) (En.hinv l h)
      htriv hH2)
    G0 (hZcard ρ) (hGaussZ ρ)
  -- rewrite each `±1` to the signed liftability through the `phaseChi`-cover
  have hsign : ∀ ζ : ↥(TCharC (En.radData l h)),
      sign (iotaB (pullCoc
          (fun γ => rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ)
          (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)))
        = phaseSign RF b F (phaseChi En l h Dsc ζ) ρ := by
    intro ζ
    have h1 : pullCoc (fun γ => rho0 (En.descData l h)
          (RF.rhoPrime b F (En.radData l h) rfl ρ) γ)
          (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)
        = pullCoc (⇑(ρ.1.1))
            (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ) := by
      funext p
      show DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ
          (rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) p.1,
            rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) p.2)
        = DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ
            (ρ.1.1 p.1, ρ.1.1 p.2)
      rw [rho0_descData_rhoPrime b F En l h ρ p.1, rho0_descData_rhoPrime b F En l h ρ p.2]
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
        phaseSign RF b F (phaseChi En l h Dsc ζ) ρ)
      = ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
          sign (iotaB (pullCoc
            (fun γ => rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ)
            (DeltaChi (descSections En l h Dsc) Dsc (descSigma_spec En l h Dsc) ζ)))
      from finsum_congr fun ζ => (hsign ζ).symm]
  exact hmc

/-- **The (140) display from the residues** (the `RecursionInputs.phase140` field at
`(l, h)`, per-`λ` family `phaseChi`): `phase140_of_phaseObstruction` at the derived
`hMobst`, the μ-torsor input `hμ`, and `hWV := enrichment_card_Vmod`. -/
theorem phase140_from_residues
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (μ₀ : ℕ) (G0 : ℤ)
    (hμ : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) = μ₀)
    (hsep : ∀ ρ : BoundaryLifts b F RF.TC,
      ∀ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
        (∀ χ : ↥(TCharC (En.radData l h)),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
          TLiftable (descSigma_spec En l h Dsc) c)
    (hpartial : ∀ ρ : BoundaryLifts b F RF.TC,
      ∀ χ : ↥(TCharC (En.radData l h)), χ ≠ 0 →
        ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
          betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
            ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
                (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)))
    (hZcard : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * Nat.card En.Vmod)
    (hGaussZ : ∀ ρ : BoundaryLifts b F RF.TC,
      ∑ᶠ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) c)
          = (Nat.card En.Vmod : ℤ) * G0) :
    2 * (Nat.card ↥(TCharC (En.radData l h)) : ℤ) * RF.zBC b F l h
      = (Nat.card En.Vmod * μ₀ : ℕ)
          * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
                (2 * (RF.nPhase b F (phaseChi En l h Dsc ζ) : ℤ)
                  - (exactImageCount b F RF.TC : ℤ))) := by
  classical
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Fintype (BoundaryLifts b F RF.TC) := Fintype.ofFinite _
  haveI : Fintype ↥(TCharC (En.radData l h)) := Fintype.ofFinite _
  exact phase140_of_phaseObstruction RF b F μ₀ G0 (↥(TCharC (En.radData l h)))
    (phaseChi En l h Dsc) l h (En.radData l h) rfl rfl Dsc htriv hfg
    (Nat.card En.Vmod) (enrichment_card_Vmod RF En) hμ
    (hMobst_of_residues b F En l h Dsc htriv hfg hH2 G0 hsep hpartial hZcard hGaussZ)

end Assembly

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.21 = ⟦lem-transgression⟧
-/
