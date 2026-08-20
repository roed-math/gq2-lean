/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SourceTransport
import GQ2.Dyadic.SourceDataRN

/-!
# Corrected source transport

`SourceTransport` proves that the frozen source record is invariant under a continuous
isomorphism of source groups.  The general-degree campaign uses `SourceDataRN`, whose
R-stage coefficient is corrected to `zRN`; until this module, that record had no transport
theorem.

`SourceDataRN.transport` moves the entire corrected source across an arbitrary continuous
group equivalence.  Exact lifting, Stokes duality, scalar counts, and both determinant branches
are transported by the same precomposition equivalences already proved for the frozen record.
The proof does not inspect the degree-indexed coefficient, so the corrected R-stage formula is
preserved verbatim.

The two congruence lemmas at the end package a recurring dependent-type seam: determinant
certificates depend on both boundary legs and on a proof of their compatibility.  Equality of
the tame and pro-2 homomorphisms gives equality of the resulting boundary maps, independently
of the proof terms.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.Dyadic.SourceTransport
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

noncomputable def SourceDataRN.transport {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (S : SourceDataRN n q P hP nuP SN) {Γ' : ProfiniteGrp}
    (e : ContinuousMulEquiv ((Γ' : Type)) ((S.Γ : Type)))
    (smul' : DistribMulAction ↥Γ' (ZMod 2))
    (hcont' : letI := smul'; ContinuousSMul ↥Γ' (ZMod 2))
    (htriv' : letI := smul'; ∀ (γ : ↥Γ') (m : ZMod 2), γ • m = m) :
    SourceDataRN n q P hP nuP SN where
  Γ := Γ'
  tame := S.tame.comp (e : ContinuousMonoidHom ((Γ' : Type)) ((S.Γ : Type)))
  pro2 := S.pro2.comp (e : ContinuousMonoidHom ((Γ' : Type)) ((S.Γ : Type)))
  compat := fun g => S.compat (e g)
  surj := fun z => by
    obtain ⟨g, hg⟩ := S.surj z
    obtain ⟨a, rfl⟩ := e.surjective g
    exact ⟨a, hg⟩
  ker_pro2 := ker_comp_continuousMulEquiv e S.pro2 S.ker_pro2
  smulZmod2 := smul'
  contSMulZmod2 := hcont'
  htriv := htriv'
  tfg := IsTopologicallyFinGen.of_surjective
    (e.symm : ContinuousMonoidHom ((S.Γ : Type)) ((Γ' : Type))).toMonoidHom
    (e.symm : ContinuousMonoidHom ((S.Γ : Type)) ((Γ' : Type))).continuous_toFun
    e.symm.surjective S.tfg
  exactLifting :=
    ⟨fun RF b₁ F ρ₁ => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F RF.TC).surjective ρ₁
        exact (Nat.card_congr (liftsOverKEquiv e RF b F ρ)).symm.trans
          (S.liftsOver_card RF b F ρ),
      fun Dd hnd ρ₁ hρ₁ => by
        obtain ⟨ρ, rfl⟩ := (precompEquiv e _).surjective ρ₁
        have hρ : Function.Surjective ρ := fun y => by
          obtain ⟨a, ha⟩ := hρ₁ y
          exact ⟨e a, ha⟩
        rw [(Nat.card_congr (Equiv.subtypeEquiv (mLiftsEquiv e Dd ρ)
            fun f => (mLiftsEquiv_central e Dd ρ f).symm)).symm,
          (Nat.card_congr (mLiftsEquiv e Dd ρ)).symm]
        exact S.lem86 Dd hnd ρ hρ,
      fun hE2 hRK hR2 b₁ F => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        simp only [exactImageCountK_comp, mBK_comp]
        exact S.stageR136 hE2 hRK hR2 b F⟩
  stokes :=
    ⟨fun b₁ F En l h ρ₁ => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
        exact (Nat.card_congr
          (tCocycleEquiv e (rhoPrimeK _ b F (En.radData l h) rfl ρ))).symm.trans
          (S.tcocycle_card b F En l h ρ),
      fun b₁ F En l h Dsc ρ₁ c₁ hc => by
        letI := S.smulZmod2
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
        obtain ⟨c, rfl⟩ := (vCocycleEquiv e (En.descData l h)
          (rhoPrimeK _ b F (En.radData l h) rfl ρ)).surjective c₁
        refine (tLiftable_comp (descSigma_spec En l h Dsc) e _ c).mpr
          (S.hsep b F En l h Dsc ρ c fun χ => ?_)
        exact (betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          htriv' S.htriv e _ χ c).symm.trans (hc χ),
      fun b₁ F En l h Dsc ρ₁ χ hχ => by
        letI := S.smulZmod2
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
        obtain ⟨c, hcne⟩ := S.hpartial b F En l h Dsc ρ χ hχ
        refine ⟨vCocycleEquiv e (En.descData l h) _ c, fun heq => hcne ?_⟩
        have h1 := betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          htriv' S.htriv e (rhoPrimeK _ b F (En.radData l h) rfl ρ) χ c
        have h2 := betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          htriv' S.htriv e (rhoPrimeK _ b F (En.radData l h) rfl ρ) χ 0
        exact h1.symm.trans (heq.trans h2),
      fun b₁ F En l h hsimple hVne hnt ρ₁ => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
        exact (Nat.card_congr (vCocycleEquiv e (En.descData l h)
          (rhoPrimeK _ b F (En.radData l h) rfl ρ))).symm.trans
          (S.hZcard b F En l h hsimple hVne hnt ρ)⟩
  scalar :=
    ⟨(Nat.card_congr
        (precompEquiv e (Multiplicative (ZMod 2)))).symm.trans S.homCard,
      by
        letI := S.smulZmod2
        exact (card_H2_comp htriv' S.htriv e).trans S.cardH2⟩
  determinant :=
    ⟨fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram => by
          letI := S.smulZmod2
          exact gaussZResidueK_comp htriv' S.htriv e _ F _ l h _
            (S.determinant.1 T Blk hE2 hq0 hqe F hsimple hVne hnt
              m hm hcard l h hunram),
      fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram => by
          letI := S.smulZmod2
          exact gaussZResidueK_comp htriv' S.htriv e _ F _ l h _
            (S.determinant.2 T Blk hE2 hq0 hqe F hsimple hVne hnt
              m hm hcard l h hram)⟩

theorem sourceBoundaryMapK_congr_pair {q : ℕ} {P Γ : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    {tame tame' : ContinuousMonoidHom Γ (Tq q)}
    {pro2 pro2' : ContinuousMonoidHom Γ P}
    (htame : tame = tame') (hpro2 : pro2 = pro2')
    (compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g))
    (compat' : ∀ g : Γ, nuTq q (tame' g) = nuP (pro2' g)) :
    sourceBoundaryMapK tame pro2 compat = sourceBoundaryMapK tame' pro2' compat' := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Subtype.ext
  exact Prod.ext (DFunLike.congr_fun htame g) (DFunLike.congr_fun hpro2 g)

theorem affineDeterminantCertificate_congr {n q : ℕ} {Γ P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {tame tame' : ContinuousMonoidHom Γ (Tq q)}
    {pro2 pro2' : ContinuousMonoidHom Γ P}
    (compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g))
    (compat' : ∀ g : Γ, nuTq q (tame' g) = nuP (pro2' g))
    (smul : DistribMulAction ↥Γ (ZMod 2))
    (htame : tame = tame') (hpro2 : pro2 = pro2') :
    AffineDeterminantCertificate Γ n q P nuP SN tame pro2 compat smul ↔
      AffineDeterminantCertificate Γ n q P nuP SN tame' pro2' compat' smul := by
  unfold AffineDeterminantCertificate
  rw [sourceBoundaryMapK_congr_pair htame hpro2 compat compat']

#print axioms SourceDataRN.transport
#print axioms sourceBoundaryMapK_congr_pair
#print axioms affineDeterminantCertificate_congr

end GQ2.Dyadic
