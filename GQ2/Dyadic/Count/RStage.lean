/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Compare
import GQ2.Dyadic.Recursion.BlockRStage
import GQ2.RStage.Local

/-!
# The degree-generic R-stage cocycle count

The frozen `R`-stage files prove `#RCocycle = #R^2 * #D_R` separately for `AbsGalQ2`,
`GammaA`, and `GammaR`.  The source-free part of those proofs is uniform: an `RCocycle` is a
continuous additive `1`-cocycle with coefficients in `R = Phi(K)`, and the invariant dual of
`R` has cardinality `#D_R`.

For a degree-`n` admissibly marked presentation, however, the word-complex count contributes
`(standardNumerics n).tMult #R = #R^(n+1)`, not the frozen exponent `2`.  This file records that
actual generic theorem.  Consequently it also isolates the exact obstruction to reusing the
old `RecursionFrame.zR` unchanged at higher degree: only the `n = 1` specialization reduces to
the frame's present `zR` definition.
-/

namespace GQ2.Dyadic.Count

open GQ2.ContCoh GQ2.FoxH GQ2.SectionEight GQ2.SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : MinimalBlock T.LY}

section Count

variable {ι κ : Type*} {Γ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {gen : ι → Γ} {W : κ → PWord ι} {w : κ → FreeGroup ι} {J : Set ι}

/-- **The honest degree-`n` cardinality of the R-stage torsor.**

This is generic in the source presentation and the marked target.  The proof factors the count
as

`RCocycle ~= Z1(Gamma, R) ~= ker(d1_word)`

and then applies the degree-`n` Stokes count.  In particular, the target data alone do not imply
the result: `hpres`, `hres`, `hwild2`, `hd`, and `hend` are genuinely source-cohomological inputs.
-/
theorem rCocycle_cardN {n : ℕ}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (f : ContinuousMonoidHom Γ Y) (hf : Function.Surjective f)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hwild2 : IsWildTwo J
      (fun i => QuotientGroup.mk' Blk.K (f (gen i))))
    (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality (fun i => QuotientGroup.mk' Blk.K (f (gen i))) w
        (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = (standardNumerics n).tMult (Nat.card (Additive ↥Blk.frattiniK))
        * Nat.card (blockFrameImpl T Blk hE2).DR := by
  classical
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  let theta : ContinuousMonoidHom Γ (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f.toMonoidHom, by
      show Continuous fun gamma => QuotientGroup.mk' Blk.K (f gamma)
      exact Continuous.comp continuous_of_discreteTopology f.continuous_toFun⟩
  have htheta_surj : Function.Surjective theta := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨gamma, hgamma⟩ := hf y
    exact ⟨gamma, by show QuotientGroup.mk' Blk.K (f gamma) = c; rw [hgamma, hy]⟩
  letI actG : DistribMulAction Γ (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ theta.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := inferInstance
  haveI : ContinuousSMul Γ (Additive ↥Blk.frattiniK) := by
    refine ⟨?_⟩
    have hfac : (fun p : Γ × Additive ↥Blk.frattiniK => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => q.1 • q.2)
          ∘ (fun p : Γ × Additive ↥Blk.frattiniK => (theta p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcomp : ∀ (gamma : Γ) (a : Additive ↥Blk.frattiniK),
      gamma • a = theta gamma • a := fun _ _ => rfl
  have hA2 : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 :=
    RStageLocal.frattiniK_add_self hRK hR2
  have htheta_apply (gamma : Γ) :
      theta gamma = QuotientGroup.mk' Blk.K (f gamma) := rfl
  have hwild2_theta : IsWildTwo J (fun i => theta (gen i)) := by
    simpa only [htheta_apply] using hwild2
  have hd_theta : StokesDuality (fun i => theta (gen i)) w
      (Additive ↥Blk.frattiniK) := by
    simpa only [htheta_apply] using hd
  have hsmul : ∀ (gamma : Γ) (a : Additive ↥Blk.frattiniK),
      gamma • a = Additive.ofMul
        (⟨f gamma * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * (f gamma)⁻¹,
          RStageLocal.conj_mem_R (f gamma) (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro gamma a
    have h1 : gamma • a
        = (QuotientGroup.mk' Blk.K (f gamma) : Y ⧸ Blk.K) •
          Additive.ofMul (Additive.toMul a) := rfl
    rw [h1]
    exact RStageLocal.conjC_smul_of_mk hRK (f gamma) (Additive.toMul a)
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f
      ≃ ↥(Z1 Γ (Additive ↥Blk.frattiniK)) :=
    { toFun := fun c =>
        ⟨fun gamma => Additive.ofMul ⟨c.u gamma, c.mem gamma⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun gamma =>
              (⟨c.u gamma, c.mem gamma⟩ : ↥Blk.frattiniK)
            exact Continuous.subtype_mk c.cont _
          · intro gamma delta
            rw [hsmul gamma (Additive.ofMul ⟨c.u delta, c.mem delta⟩)]
            refine Additive.toMul.injective (Subtype.ext ?_)
            exact c.crossed gamma delta⟩
      invFun := fun z =>
        { u := fun gamma => ((Additive.toMul (z.1 gamma) : ↥Blk.frattiniK) : Y)
          mem := fun gamma => (Additive.toMul (z.1 gamma)).2
          cont := continuous_subtype_val.comp (mem_Z1_iff.mp z.2).1
          crossed := by
            intro gamma delta
            have hz := (mem_Z1_iff.mp z.2).2 gamma delta
            rw [hsmul gamma (z.1 delta)] at hz
            simpa using congrArg
              (fun a => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) hz }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun gamma => rfl) }
  rw [Nat.card_congr hequiv,
    card_Z1_eq_card_wordZ1 theta hcomp (fun _ => rfl) hpres hres hA2 hwild2_theta,
    tcocycle_card_shape_fixedPts
      (isSelfDualN_of_stokesDuality hdeg hd_theta
        (lower_rel theta (fun _ => rfl) hpres hres) hend)
      (closure_range_lower_eq_top theta (fun _ => rfl) hpres htheta_surj),
    RStageLocal.card_fixedPts_eq_card_RCharSub hRK,
    blockRChar_card T Blk hE2]

/-- `rCocycle_cardN` in the corrected recursion's own coefficient vocabulary. -/
theorem rCocycle_card_standard_zRN {n : ℕ}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (f : ContinuousMonoidHom Γ Y) (hf : Function.Surjective f)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hwild2 : IsWildTwo J
      (fun i => QuotientGroup.mk' Blk.K (f (gen i))))
    (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality (fun i => QuotientGroup.mk' Blk.K (f (gen i))) w
        (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = zRN (blockFrameImpl T Blk hE2) (standardNumerics n) := by
  rw [rCocycle_cardN hE2 hRK hR2 f hf hpres hres hwild2 hdeg hd hend, zRN,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]

/-- Above degree one, the generic `tMult` coefficient is strictly larger than the frozen square
as soon as the coefficient group and the remaining factor are nontrivial. -/
theorem standardNumerics_tMult_ne_sq {n r d : ℕ} (hn : 2 ≤ n) (hr : 1 < r) (hd : 0 < d) :
    (standardNumerics n).tMult r * d ≠ r ^ 2 * d := by
  have hexp : 2 < n + 1 := Nat.lt_succ_of_le hn
  have hp : r ^ 2 < r ^ (n + 1) := Nat.pow_lt_pow_right hr hexp
  have hm : r ^ 2 * d < r ^ (n + 1) * d := Nat.mul_lt_mul_of_pos_right hp hd
  intro h
  exact (Nat.ne_of_lt hm) (by simpa [standardNumerics] using h.symm)

/-- **No-go for the rank-one-calibrated `zR`.**  If the degree-`n` Stokes calculation has been
performed, `n >= 2`, and `R` is nontrivial, its result cannot equal the current
`RecursionFrame.zR`.  The `D_R` factor needs no hypothesis: the frame supplies `zeroDR`, so its
finite carrier is automatically nonempty.

This theorem deliberately does not alter `zR`; it makes the specification mismatch explicit for
the degree-indexed recursion lane to resolve. -/
theorem rCocycle_card_ne_zR_of_cardN {n : ℕ}
    (hE2 : ∀ e : E, e ^ 2 = 1) (f : ContinuousMonoidHom Γ Y)
    (hcard : Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = (standardNumerics n).tMult (Nat.card (Additive ↥Blk.frattiniK))
        * Nat.card (blockFrameImpl T Blk hE2).DR)
    (hn : 2 ≤ n) (hR : 1 < Nat.card (Additive ↥Blk.frattiniK)) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      ≠ (blockFrameImpl T Blk hE2).zR := by
  rw [hcard]
  change (standardNumerics n).tMult (Nat.card (Additive ↥Blk.frattiniK))
      * Nat.card (blockFrameImpl T Blk hE2).DR
    ≠ Nat.card ↥Blk.frattiniK ^ 2 * Nat.card (blockFrameImpl T Blk hE2).DR
  rw [← Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]
  letI : Nonempty (blockFrameImpl T Blk hE2).DR :=
    ⟨(blockFrameImpl T Blk hE2).zeroDR⟩
  exact standardNumerics_tMult_ne_sq hn hR Nat.card_pos

/-- At degree one, `rCocycle_cardN` specializes definitionally to the frozen block frame's
`zR = #R^2 * #D_R`.  This is the precise regression theorem for the old Q2 count. -/
theorem rCocycle_card_one
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (f : ContinuousMonoidHom Γ Y) (hf : Function.Surjective f)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hwild2 : IsWildTwo J
      (fun i => QuotientGroup.mk' Blk.K (f (gen i))))
    (hdeg : Nat.card ι = Nat.card κ + (1 + 1))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality (fun i => QuotientGroup.mk' Blk.K (f (gen i))) w
        (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = (blockFrameImpl T Blk hE2).zR := by
  rw [rCocycle_cardN hE2 hRK hR2 f hf hpres hres hwild2 hdeg hd hend,
    standardNumerics_one_tMult,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]
  rfl

end Count

end GQ2.Dyadic.Count
