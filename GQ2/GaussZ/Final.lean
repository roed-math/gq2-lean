import GQ2.GaussZ.Local
import GQ2.Phase140.Local

/-!
# P-16d6e4a — the local `GaussZResidue` discharge (the e7 composition)

`gaussZ_reduction` (layer (I), `GaussZReduction.lean`) ∘ the `H¹`-transport
(`h1OfVQuot` + `QZeroBar_eq_Q0loc`, `GaussZLocal.lean`) ∘ the pinned values
(`sum_sign_Q0loc_unramified`/`_ramified`): for every boundary lift `ρ` of the local source,

  `∑ᶠ c : Z¹_{G_ℚ₂,ρ'}(V), sign(Q⁰ c) = #V · G0`,  `G0 = −2^m` (unram) / `+2^m` (ram)

— `GaussZResidue B.bF F En l h G0` verbatim, i.e. `prop_8_9`'s `hGaussZF` at the pinned value
(design: `docs/p16d6e4a-evaluation-design.md` §1 + §"Hypothesis supply").

* The **tame factorization is packaged per boundary lift** (`hpack`): each lower map
  `ρ.1.1 : G_ℚ₂ → Y_C` factors through `B.tameF` by a surjective `c : Ttame → Y_C` carrying
  the *uniform* un/ramified dichotomy on `V`.  This is the single genuinely structural input
  beyond the `En`-form data — the §9 consumer derives it from the block's tame package
  (c3-G0 layer).
* Finiteness of `Z¹` is **σ-free** via the e3 count `hZcard_local` (`#Z¹ = #V² ≠ 0`), so the
  discharge holds at every `(l, h)` — no descent datum needed (`gaussZ_reduction` was
  generalized to a `[Finite Z¹]` hypothesis accordingly).
* The `AbsGalQ2`-module structure on `V` is installed per-`ρ` by the `letI`-pullback along
  the lower map (the `compHom` idiom), making the bridge hypotheses (`hcomp`/`hρ`) `rfl`.
* The `Γ_A` twin (`hGaussZA`) has **no `prop_6_18`-analog** and stays on the `prop_8_9`
  ledger — the sanctioned deferral (design §2), discharged by (83)-for-`Γ_A` or carried to
  the ThmFourTwo consumer.

The two theorems share their spine verbatim (the letI-instances are proof-local, so the
pinned step cannot be abstracted into a common core without Π-over-instances noise).
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh SectionSix

section Composition

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [IsTopologicalGroup AbsGalQ2]

variable (B : BoundaryMaps) (F : BoundaryFrame H E) (En : RF.Enrichment)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [TopologicalSpace Y]
  [DiscreteTopology Y] [IsTopologicalGroup AbsGalQ2] in
/-- **`hGaussZF`, unramified case** (P-16d6e4a): with a per-lift tame package whose inertia
acts trivially on `V`, `GaussZResidue B.bF F En l h (−2^m)` — the `prop_8_9` ledger
hypothesis at the pinned unramified value. -/
theorem gaussZResidue_local_unramified (D6 : TateDuality 2)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hpack : ∀ ρ : BoundaryLifts B.bF F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
      Function.Surjective ⇑c ∧ (∀ g : AbsGalQ2, ρ.1.1 g = c (B.tameF g)) ∧
        ∀ v : En.Vmod, c tameTau • v = v) :
    GaussZResidue B.bF F En l h (-(2 ^ m : ℤ)) := by
  intro ρ
  classical
  obtain ⟨c, hc, hfacρ, hunram⟩ := hpack ρ
  set ρM := RF.rhoPrime B.bF F (En.radData l h) rfl ρ with hρMdef
  -- the module structure on `V` through the lower map (per-`ρ` `letI`-pullback)
  letI instT : TopologicalSpace En.Vmod := ⊥
  haveI instD : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction AbsGalQ2 En.Vmod := DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI instC : ContinuousSMul AbsGalQ2 En.Vmod :=
    ⟨(continuous_of_discreteTopology (f := fun q : RF.YC × En.Vmod => q.1 • q.2)).comp
      ((ρ.1.1.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  -- the same instances re-keyed at the syntactic `descData`-projections (synthesis is
  -- transparency-limited; the values are defeq)
  letI : TopologicalSpace (En.descData l h).Vmod := instT
  haveI : DiscreteTopology (En.descData l h).Vmod := instD
  letI : DistribMulAction AbsGalQ2 (En.descData l h).Vmod := instA
  haveI : ContinuousSMul AbsGalQ2 (En.descData l h).Vmod := instC
  letI : TopologicalSpace (En.descData l h).C0 := (inferInstance : TopologicalSpace RF.YC)
  haveI : DiscreteTopology (En.descData l h).C0 := (inferInstance : DiscreteTopology RF.YC)
  haveI : Finite (En.descData l h).C0 := (inferInstance : Finite RF.YC)
  -- the roundtrip `rho0 ∘ rhoPrime = ρ.1.1` and the bridge hypothesis (`rfl`-flavored)
  have hround : ∀ γ : AbsGalQ2, rho0 (En.descData l h) ρM γ = ρ.1.1 γ := fun γ =>
    rho0_descData_rhoPrime B.bF F En l h ρ γ
  have hcomp : ∀ (γ : AbsGalQ2) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) ρM γ • v := fun γ v =>
    (congrArg (fun cc : (En.descData l h).C0 => cc • v) (hround γ)).symm
  -- finiteness of `Z¹`, σ-free from the e3 count
  haveI hfinZ : Finite (VCocycle (En.descData l h) ρM) :=
    (Nat.card_ne_zero.mp (by
      rw [hZcard_local B.bF F En l h hsimple hVne hnt ρ]
      exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).2
  -- the `V^{C₀} = 0` freeness input
  haveI : Nontrivial (En.descData l h).C0 :=
    show Nontrivial RF.YC from by
      obtain ⟨g, v, hgv⟩ := hnt
      exact ⟨g, 1, fun hg => hgv (by rw [hg]; exact one_smul _ v)⟩
  have hsurjρ' : Function.Surjective fun γ => rho0 (En.descData l h) ρM γ := fun y => by
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (hround γ).trans hγ⟩
  have hfix : ∀ v : (En.descData l h).Vmod,
      (∀ γ : AbsGalQ2, rho0 (En.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple hsurjρ' hsimple hfaith v hv
  -- the transport bijection `Z¹⧸B¹ ≅ H¹` and the form compatibility
  have hbij : Function.Bijective (h1OfVQuot hcomp) :=
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  have hpinned := sum_sign_Q0loc_unramified D6 B c hc ρ.1.1 hfacρ (fun _ _ => rfl) hfaith
    hsimple hVne hunram (En.qbar l h) (En.hquad l h) (En.hns l h) (En.hinv l h)
    (En.dat l h) (En.hdat l h) m hm hcard
  calc ∑ᶠ cc : VCocycle (En.descData l h) ρM, sign (QZero (En.descData l h) ρM cc)
      = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ x, sign (QZeroBar (En.descData l h) ρM htriv_local' x) :=
        gaussZ_reduction htriv_local' hfix
    _ = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ y : H1 AbsGalQ2 En.Vmod, sign (Q0loc D6 (En.dat l h) ρ.1.1 y) := by
        congr 1
        refine finsum_eq_of_bijective (h1OfVQuot hcomp) hbij fun x => ?_
        rw [QZeroBar_eq_Q0loc D6 hcomp ρ.1.1 (fun γ => (hround γ).symm) htriv_local' x]
        rfl
    _ = (Nat.card En.Vmod : ℤ) * (-(2 ^ m : ℤ)) := by rw [hpinned]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [TopologicalSpace Y]
  [DiscreteTopology Y] [IsTopologicalGroup AbsGalQ2] in
/-- **`hGaussZF`, ramified case** (P-16d6e4a): with a per-lift tame package whose inertia
moves `V`, `GaussZResidue B.bF F En l h (+2^m)` — the `prop_8_9` ledger hypothesis at the
pinned ramified value. -/
theorem gaussZResidue_local_ramified (D6 : TateDuality 2) (R : LocalReciprocity)
    (horient : TameUnitOrientation R B.tameF)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hpack : ∀ ρ : BoundaryLifts B.bF F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
      Function.Surjective ⇑c ∧ (∀ g : AbsGalQ2, ρ.1.1 g = c (B.tameF g)) ∧
        ∃ v : En.Vmod, c tameTau • v ≠ v) :
    GaussZResidue B.bF F En l h (2 ^ m : ℤ) := by
  intro ρ
  classical
  obtain ⟨c, hc, hfacρ, hram⟩ := hpack ρ
  set ρM := RF.rhoPrime B.bF F (En.radData l h) rfl ρ with hρMdef
  letI instT : TopologicalSpace En.Vmod := ⊥
  haveI instD : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction AbsGalQ2 En.Vmod := DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI instC : ContinuousSMul AbsGalQ2 En.Vmod :=
    ⟨(continuous_of_discreteTopology (f := fun q : RF.YC × En.Vmod => q.1 • q.2)).comp
      ((ρ.1.1.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  -- the same instances re-keyed at the syntactic `descData`-projections (synthesis is
  -- transparency-limited; the values are defeq)
  letI : TopologicalSpace (En.descData l h).Vmod := instT
  haveI : DiscreteTopology (En.descData l h).Vmod := instD
  letI : DistribMulAction AbsGalQ2 (En.descData l h).Vmod := instA
  haveI : ContinuousSMul AbsGalQ2 (En.descData l h).Vmod := instC
  letI : TopologicalSpace (En.descData l h).C0 := (inferInstance : TopologicalSpace RF.YC)
  haveI : DiscreteTopology (En.descData l h).C0 := (inferInstance : DiscreteTopology RF.YC)
  haveI : Finite (En.descData l h).C0 := (inferInstance : Finite RF.YC)
  have hround : ∀ γ : AbsGalQ2, rho0 (En.descData l h) ρM γ = ρ.1.1 γ := fun γ =>
    rho0_descData_rhoPrime B.bF F En l h ρ γ
  have hcomp : ∀ (γ : AbsGalQ2) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) ρM γ • v := fun γ v =>
    (congrArg (fun cc : (En.descData l h).C0 => cc • v) (hround γ)).symm
  haveI hfinZ : Finite (VCocycle (En.descData l h) ρM) :=
    (Nat.card_ne_zero.mp (by
      rw [hZcard_local B.bF F En l h hsimple hVne hnt ρ]
      exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).2
  haveI : Nontrivial (En.descData l h).C0 :=
    show Nontrivial RF.YC from by
      obtain ⟨g, v, hgv⟩ := hnt
      exact ⟨g, 1, fun hg => hgv (by rw [hg]; exact one_smul _ v)⟩
  have hsurjρ' : Function.Surjective fun γ => rho0 (En.descData l h) ρM γ := fun y => by
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (hround γ).trans hγ⟩
  have hfix : ∀ v : (En.descData l h).Vmod,
      (∀ γ : AbsGalQ2, rho0 (En.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple hsurjρ' hsimple hfaith v hv
  have hbij : Function.Bijective (h1OfVQuot hcomp) :=
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  have hpinned := sum_sign_Q0loc_ramified D6 R B c hc ρ.1.1 hfacρ horient (fun _ _ => rfl)
    hfaith hsimple hram (En.qbar l h) (En.hquad l h) (En.hns l h) (En.hinv l h)
    (En.dat l h) (En.hdat l h) m hm hcard
  calc ∑ᶠ cc : VCocycle (En.descData l h) ρM, sign (QZero (En.descData l h) ρM cc)
      = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ x, sign (QZeroBar (En.descData l h) ρM htriv_local' x) :=
        gaussZ_reduction htriv_local' hfix
    _ = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ y : H1 AbsGalQ2 En.Vmod, sign (Q0loc D6 (En.dat l h) ρ.1.1 y) := by
        congr 1
        refine finsum_eq_of_bijective (h1OfVQuot hcomp) hbij fun x => ?_
        rw [QZeroBar_eq_Q0loc D6 hcomp ρ.1.1 (fun γ => (hround γ).symm) htriv_local' x]
        rfl
    _ = (Nat.card En.Vmod : ℤ) * (2 ^ m : ℤ) := by rw [hpinned]

end Composition

end AffineTLift

end SectionEight

end GQ2
