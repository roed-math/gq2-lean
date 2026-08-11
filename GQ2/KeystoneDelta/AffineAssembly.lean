/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.KeystoneDelta.ThetaExtraction

/-!
# The graph tie-in, affineness and the keystone assembly

Split off from `GQ2.KeystoneDelta` (design §6).  This file provides:

* the **graph tie-in** (`graph_pmul`, `tDef_eq_JDefT`) and the affineness `haff`
  (`betaChi_affine`): the cup part is additive, the `g`-part a coboundary killed by `ι_Γ`,
  the inflated scalar cancels four-fold;
* **Stage D** — the keystone assembly: the `χ`-edge `γ''_χ` (`gamma2`), the total edge
  `γtot_χ`, the polar-inverse shear family `a_χ` (`achi`) and its crossed-cocycle law, and the
  `Ψ_χ`-normal form (`psi_decomp`).

See `GQ2.KeystoneDelta` for the umbrella module docstring.
-/

namespace GQ2

set_option linter.unusedSectionVars false
variable [lit : LiteratureInputs]

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

/-! ## The graph tie-in and the affineness `haff` (the master count's threaded hypothesis) -/

section Affine

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [DiscreteTopology Bg] in
/-- The graph of a crossed cocycle is `pmul`-multiplicative. -/
theorem graph_pmul (c : VCocycle DD ρ) (γ δ : Γ) :
    pmul (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ)
      = (c.c (γ * δ), rho0 DD ρ (γ * δ)) := by
  unfold pmul
  exact Prod.ext (c.crossed γ δ).symm (map_mul (rho0 DD ρ) γ δ).symm

include hσ in
/-- The `T`-defect of `fLift` is the `J`-defect at the graph. -/
theorem tDef_eq_JDefT (c : VCocycle DD ρ) (p : Γ × Γ) :
    tDef S hσ c p
      = JDefT S hσ (c.c p.1, rho0 DD ρ p.1) (c.c p.2, rho0 DD ρ p.2) := by
  apply Subtype.ext
  show fLift S c p.1 * fLift S c p.2 * (fLift S c (p.1 * p.2))⁻¹
    = Jmap S (c.c p.1, rho0 DD ρ p.1) * Jmap S (c.c p.2, rho0 DD ρ p.2)
      * (Jmap S (pmul (c.c p.1, rho0 DD ρ p.1) (c.c p.2, rho0 DD ρ p.2)))⁻¹
  rw [graph_pmul]
  rfl

variable (DD ρ) in
/-- **The cup part** of the `χ`-obstruction cochain: the `c`-additive component of the
`ω_χ`-decomposition at the graph. -/
noncomputable def cupChi (gχ : DD.Vmod → ZMod 2) (χ : ↥(TCharC D)) (c : VCocycle DD ρ)
    (p : Γ × Γ) : ZMod 2 :=
  χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2))
    + gχ (rho0 DD ρ p.1 • c.c p.2) + gχ (c.c p.2)

include hσ in
/-- **The `chiDef`-decomposition at a splitting of `f_χ`**: cup part + `g`-coboundary part +
inflated scalar. -/
theorem chiDef_decomp (χ : ↥(TCharC D)) (gχ : DD.Vmod → ZMod 2)
    (hg : ∀ v w : DD.Vmod, χ.1 (mDef DD S v w) = gχ (v + w) + gχ v + gχ w)
    (c : VCocycle DD ρ) (p : Γ × Γ) :
    chiDef S hσ χ c p
      = cupChi DD S ρ hσ gχ χ c p
        + (gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
        + χ.1 (uDef DD S (rho0 DD ρ p.1) (rho0 DD ρ p.2)) := by
  show χ.1 (tDef S hσ c p) = _
  rw [tDef_eq_JDefT S hσ c p, chiJDef_eq S hσ χ]
  show χ.1 (mDef DD S (c.c p.1) (rho0 DD ρ p.1 • c.c p.2))
      + χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2))
      + χ.1 (uDef DD S (rho0 DD ρ p.1) (rho0 DD ρ p.2)) = _
  rw [hg (c.c p.1) (rho0 DD ρ p.1 • c.c p.2)]
  unfold cupChi
  have hcr : c.c (p.1 * p.2) = c.c p.1 + rho0 DD ρ p.1 • c.c p.2 := c.crossed p.1 p.2
  rw [hcr]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) (rfl : (0 : ZMod 2) = 0)

include hσ in
/-- The cup part is additive in the cocycle. -/
theorem cupChi_add (χ : ↥(TCharC D)) (gχ : DD.Vmod → ZMod 2)
    (hg : ∀ v w : DD.Vmod, χ.1 (mDef DD S v w) = gχ (v + w) + gχ v + gχ w)
    (c c' : VCocycle DD ρ) (p : Γ × Γ) :
    cupChi DD S ρ hσ gχ χ (c + c') p
      = cupChi DD S ρ hσ gχ χ c p + cupChi DD S ρ hσ gχ χ c' p := by
  unfold cupChi
  have hcc : (c + c').c p.2 = c.c p.2 + c'.c p.2 := rfl
  rw [hcc]
  -- `m_quad` for the conjugation part, `hg` for the two `g`-parts
  have hq := (isEquivariantFactorSet_datChi S hσ χ).m_quad (rho0 DD ρ p.1) (c.c p.2) (c'.c p.2)
  have hg1 : gχ (rho0 DD ρ p.1 • (c.c p.2 + c'.c p.2))
      = gχ (rho0 DD ρ p.1 • c.c p.2) + gχ (rho0 DD ρ p.1 • c'.c p.2)
        + χ.1 (mDef DD S (rho0 DD ρ p.1 • c.c p.2) (rho0 DD ρ p.1 • c'.c p.2)) := by
    rw [smul_add]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hg (rho0 DD ρ p.1 • c.c p.2) (rho0 DD ρ p.1 • c'.c p.2)
  have hg2 : gχ (c.c p.2 + c'.c p.2)
      = gχ (c.c p.2) + gχ (c'.c p.2) + χ.1 (mDef DD S (c.c p.2) (c'.c p.2)) := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hg (c.c p.2) (c'.c p.2)
  -- `m_quad`'s statement in `datChi`-vocabulary
  have hq' : χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2 + c'.c p.2))
      = χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2))
        + χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c'.c p.2))
        + χ.1 (mDef DD S (rho0 DD ρ p.1 • c.c p.2) (rho0 DD ρ p.1 • c'.c p.2))
        + χ.1 (mDef DD S (c.c p.2) (c'.c p.2)) := by
    have hchar : ∀ x a b f1 f2 : ZMod 2, x + a + b = f1 + f2 → x = a + b + f1 + f2 := by decide
    exact hchar _ _ _ _ _ hq
  rw [hq', hg1, hg2]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) (rfl : (0 : ZMod 2) = 0)

include hσ in
omit [DiscreteTopology Bg] in
/-- The cup part vanishes at the zero cocycle. -/
theorem cupChi_zero (χ : ↥(TCharC D)) (gχ : DD.Vmod → ZMod 2) (hg0 : gχ 0 = 0)
    (p : Γ × Γ) :
    cupChi DD S ρ hσ gχ χ (0 : VCocycle DD ρ) p = 0 := by
  unfold cupChi
  show χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) 0) + gχ (rho0 DD ρ p.1 • (0 : DD.Vmod)) + gχ 0 = 0
  rw [conjDef_zero_right, TCharC.map_one, smul_zero, hg0, add_zero, add_zero]

variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The `g`-coboundary part of the `chiDef`-decomposition is a continuous coboundary. -/
theorem gPart_mem_B2 (_hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (gχ : DD.Vmod → ZMod 2) (cx : VCocycle DD ρ) :
    (fun p : Γ × Γ => gχ (cx.c (p.1 * p.2)) + gχ (cx.c p.1) + gχ (cx.c p.2))
      ∈ B2 Γ (ZMod 2) := by
  classical
  refine ⟨fun γ => gχ (cx.c γ), ?_, ?_⟩
  · have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      fun a b h => iV_ofAdd_inj DD h
    have heq : (fun γ => gχ (cx.c γ))
        = (fun q : Bg ⧸ D.T => gχ (Function.invFun
            (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) q))
          ∘ (fun γ => iV DD (Multiplicative.ofAdd (cx.c γ))) := by
      funext γ
      show gχ (cx.c γ)
        = gχ (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
            (iV DD (Multiplicative.ofAdd (cx.c γ))))
      rw [Function.leftInverse_invFun hinj (cx.c γ)]
    rw [heq]
    exact continuous_of_discreteTopology.comp cx.cont
  · funext p
    show p.1 • gχ (cx.c p.2) - gχ (cx.c (p.1 * p.2)) + gχ (cx.c p.1)
      = gχ (cx.c (p.1 * p.2)) + gχ (cx.c p.1) + gχ (cx.c p.2)
    rw [htriv]
    have hchar : ∀ a b cc : ZMod 2, a - b + cc = b + cc + a := by decide
    exact hchar _ _ _

omit [ContinuousSMul Γ (ZMod 2)] in
include hσ in
/-- **The affineness `haff`** (the master count's threaded hypothesis, design §6): `β_χ` is
affine in the cocycle — the cup part is additive, the `g`-part is a coboundary killed by
`ι_Γ`, and the inflated scalar cancels four-fold. -/
theorem betaChi_affine (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ) :
    betaChi S hσ χ (c + c')
      = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ) := by
  classical
  -- split `f_χ` (symmetric, zero-diagonal, normalized cocycle on the exponent-2 `V`)
  obtain ⟨gχ, hg0, hg⟩ := exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => χ.1 (mDef DD S v w))
    (fun v w x => (isEquivariantFactorSet_datChi S hσ χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])
  -- the four-fold sum of the obstruction cochains is a coboundary
  have hsum_mem : (chiDef S hσ χ (c + c') + chiDef S hσ χ c)
      + (chiDef S hσ χ c' + chiDef S hσ χ (0 : VCocycle DD ρ)) ∈ B2 Γ (ZMod 2) := by
    have hfun : (chiDef S hσ χ (c + c') + chiDef S hσ χ c)
        + (chiDef S hσ χ c' + chiDef S hσ χ (0 : VCocycle DD ρ))
        = ((fun p : Γ × Γ => gχ ((c + c').c (p.1 * p.2)) + gχ ((c + c').c p.1)
              + gχ ((c + c').c p.2))
            + (fun p : Γ × Γ => gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2)))
          + ((fun p : Γ × Γ => gχ (c'.c (p.1 * p.2)) + gχ (c'.c p.1) + gχ (c'.c p.2))
            + (fun p : Γ × Γ => gχ ((0 : VCocycle DD ρ).c (p.1 * p.2))
                + gχ ((0 : VCocycle DD ρ).c p.1) + gχ ((0 : VCocycle DD ρ).c p.2))) := by
      funext p
      have h1 := chiDef_decomp S hσ χ gχ hg (c + c') p
      have h2 := chiDef_decomp S hσ χ gχ hg c p
      have h3 := chiDef_decomp S hσ χ gχ hg c' p
      have h4 := chiDef_decomp S hσ χ gχ hg (0 : VCocycle DD ρ) p
      have hcup := cupChi_add S hσ χ gχ hg c c' p
      have hcup0 := cupChi_zero (ρ := ρ) S hσ χ gχ hg0 p
      show chiDef S hσ χ (c + c') p + chiDef S hσ χ c p
          + (chiDef S hσ χ c' p + chiDef S hσ χ (0 : VCocycle DD ρ) p) = _
      linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero,
        show (4 : ZMod 2) = 0 from by decide]); (try ring_nf)))
        h1 + h2 + h3 + h4 + hcup + hcup0
    rw [hfun]
    exact AddSubgroup.add_mem _
      (AddSubgroup.add_mem _ (gPart_mem_B2 hσ htriv gχ (c + c'))
        (gPart_mem_B2 hσ htriv gχ c))
      (AddSubgroup.add_mem _ (gPart_mem_B2 hσ htriv gχ c')
        (gPart_mem_B2 hσ htriv gχ (0 : VCocycle DD ρ)))
  -- assemble through `ι_Γ`-additivity
  have hZ : ∀ cx : VCocycle DD ρ, chiDef S hσ χ cx ∈ Z2 Γ (ZMod 2) :=
    fun cx => chiDef_mem_Z2 S hσ htriv χ cx
  have h12 : betaChi S hσ χ (c + c') + betaChi S hσ χ c
      = iotaB (chiDef S hσ χ (c + c') + chiDef S hσ χ c) :=
    (iotaB_add hH2 (hZ _) (hZ _)).symm
  have h34 : betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ)
      = iotaB (chiDef S hσ χ c' + chiDef S hσ χ (0 : VCocycle DD ρ)) :=
    (iotaB_add hH2 (hZ _) (hZ _)).symm
  have htot : betaChi S hσ χ (c + c') + betaChi S hσ χ c
      + (betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ)) = 0 := by
    rw [h12, h34, ← iotaB_add hH2 (AddSubgroup.add_mem _ (hZ _) (hZ _))
      (AddSubgroup.add_mem _ (hZ _) (hZ _))]
    exact iotaB_of_mem_B2 hsum_mem
  have hchar : ∀ a b cc d : ZMod 2, a + b + (cc + d) = 0 → a = b + cc + d := by decide
  exact hchar _ _ _ _ htot

end Affine

/-! ## Stage D: the keystone assembly (design §6) -/

section Assembly

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable (Dsc : Descent D)
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The splitting data for `f_χ = χ ∘ mDef` exists. -/
theorem gchi_exists (χ : ↥(TCharC D)) : ∃ g : DD.Vmod → ZMod 2, g 0 = 0 ∧
    ∀ v w : DD.Vmod, χ.1 (mDef DD S v w) = g (v + w) + g v + g w :=
  exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => χ.1 (mDef DD S v w))
    (fun v w x => (isEquivariantFactorSet_datChi S hσ χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])

/-- A fixed splitting `g_χ` of `f_χ`. -/
noncomputable def gchi (χ : ↥(TCharC D)) : DD.Vmod → ZMod 2 :=
  Classical.choose (gchi_exists S hσ χ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem gchi_split (χ : ↥(TCharC D)) (v w : DD.Vmod) :
    χ.1 (mDef DD S v w) = gchi S hσ χ (v + w) + gchi S hσ χ v + gchi S hσ χ w :=
  (Classical.choose_spec (gchi_exists S hσ χ)).2 v w

/-- **The `χ`-edge `γ''_χ`** of the zero-form normal form. -/
noncomputable def gamma2 (χ : ↥(TCharC D)) (cc : DD.C0) (x : DD.Vmod) : ZMod 2 :=
  χ.1 (conjDef DD S hσ cc (cc⁻¹ • x)) + gchi S hσ χ x + gchi S hσ χ (cc⁻¹ • x)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γ''_χ(cc)` is additive. -/
theorem gamma2_add (χ : ↥(TCharC D)) (cc : DD.C0) (x y : DD.Vmod) :
    gamma2 S hσ χ cc (x + y) = gamma2 S hσ χ cc x + gamma2 S hσ χ cc y := by
  unfold gamma2
  have hmq := (isEquivariantFactorSet_datChi S hσ χ).m_quad cc (cc⁻¹ • x) (cc⁻¹ • y)
  simp only [datChi] at hmq
  have hg1 := gchi_split S hσ χ x y
  have hg2 := gchi_split S hσ χ (cc⁻¹ • x) (cc⁻¹ • y)
  rw [show cc⁻¹ • (x + y) = cc⁻¹ • x + cc⁻¹ • y from smul_add cc⁻¹ x y]
  have hsm : cc • cc⁻¹ • x = x := smul_inv_smul cc x
  have hsm' : cc • cc⁻¹ • y = y := smul_inv_smul cc y
  rw [hsm, hsm'] at hmq
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hmq + hg1 + hg2

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The dual-crossed law for `γ''_χ`. -/
theorem gamma2_dual_crossed (χ : ↥(TCharC D)) (cc dd : DD.C0) (x : DD.Vmod) :
    gamma2 S hσ χ (cc * dd) x = gamma2 S hσ χ cc x + gamma2 S hσ χ dd (cc⁻¹ • x) := by
  unfold gamma2
  have hmm := (isEquivariantFactorSet_datChi S hσ χ).m_mul cc dd ((cc * dd)⁻¹ • x)
  simp only [datChi] at hmm
  have harg : dd • (cc * dd)⁻¹ • x = cc⁻¹ • x := by
    rw [mul_inv_rev, mul_smul, smul_inv_smul]
  rw [harg] at hmm
  rw [show (cc * dd)⁻¹ • x = dd⁻¹ • cc⁻¹ • x from by rw [mul_inv_rev, mul_smul]] at hmm ⊢
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hmm

/-! ### The total edge and the polar-inverse shear -/

/-- **The total edge** `γtot_χ := γ''_χ + γκ`. -/
noncomputable def gammatot (χ : ↥(TCharC D)) (cc : DD.C0) (x : DD.Vmod) : ZMod 2 :=
  gamma2 S hσ χ cc x + gammakap σ Dsc hσ cc x

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gammatot_add (χ : ↥(TCharC D)) (cc : DD.C0) (x y : DD.Vmod) :
    gammatot S Dsc hσ χ cc (x + y)
      = gammatot S Dsc hσ χ cc x + gammatot S Dsc hσ χ cc y := by
  unfold gammatot
  rw [gamma2_add S hσ χ cc x y, gammakap_add σ Dsc hσ cc x y]
  ring

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem gammatot_dual_crossed (χ : ↥(TCharC D)) (cc dd : DD.C0) (x : DD.Vmod) :
    gammatot S Dsc hσ χ (cc * dd) x
      = gammatot S Dsc hσ χ cc x + gammatot S Dsc hσ χ dd (cc⁻¹ • x) := by
  unfold gammatot
  rw [gamma2_dual_crossed S hσ χ cc dd x, gammakap_dual_crossed σ Dsc hσ cc dd x]
  ring

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Polar-inverse for additive functionals (module-free wrapper). -/
theorem exists_polar_inverse' {q : DD.Vmod → ZMod 2} (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (φ : DD.Vmod → ZMod 2)
    (hφ : ∀ x y : DD.Vmod, φ (x + y) = φ x + φ y) :
    ∃ a : DD.Vmod, ∀ v : DD.Vmod, polar q a v = φ v := by
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact Vmod_exp2 DD v)
  let φL : Module.Dual (ZMod 2) DD.Vmod :=
    { toFun := φ
      map_add' := hφ
      map_smul' := fun c v => by
        rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
        · rw [zero_smul]
          show φ 0 = (RingHom.id (ZMod 2)) 0 • φ v
          have h0 : φ 0 = 0 := by
            have h := hφ 0 0
            rw [add_zero] at h
            exact left_eq_add.mp h
          rw [h0, RingHom.id_apply, zero_smul]
        · rw [one_smul]
          show φ v = (RingHom.id (ZMod 2)) 1 • φ v
          rw [RingHom.id_apply, one_smul] }
  obtain ⟨a, ha⟩ := exists_polar_inverse q hq hns φL
  exact ⟨a, ha⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Polar injectivity: nonsingular forms separate points through the polar pairing. -/
theorem polar_inj {q : DD.Vmod → ZMod 2} (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {a b : DD.Vmod} (h : ∀ v : DD.Vmod, polar q a v = polar q b v) : a = b := by
  by_contra hne
  have hab : a + b ≠ 0 := fun h0 =>
    hne ((add_eq_zero_iff_eq_neg.mp h0).trans (neg_eq_of_add_eq_zero_left (Vmod_exp2 DD b)))
  obtain ⟨w, hw⟩ := hns (a + b) hab
  apply hw
  rw [hq.polar_add_left a b w, h w]
  exact CharTwo.add_self_eq_zero _

/-! ### The shear family `a_χ` and the total scalar phase -/
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Polar equivariance for an invariant form: `B(cc•u, v) = B(u, cc⁻¹•v)`. -/
theorem polar_smul_inv {q : DD.Vmod → ZMod 2} (hinvQ : IsInvariant DD.C0 q)
    (cc : DD.C0) (u v : DD.Vmod) :
    polar q (cc • u) v = polar q u (cc⁻¹ • v) := by
  show q (cc • u + v) + q (cc • u) + q v = q (u + cc⁻¹ • v) + q u + q (cc⁻¹ • v)
  have h1 : cc • u + v = cc • (u + cc⁻¹ • v) := by rw [smul_add, smul_inv_smul]
  rw [h1, hinvQ cc (u + cc⁻¹ • v), hinvQ cc u,
    show q v = q (cc⁻¹ • v) from by
      conv_lhs => rw [show v = cc • cc⁻¹ • v from (smul_inv_smul cc v).symm]
      exact hinvQ cc (cc⁻¹ • v)]

variable (hinvQ : IsInvariant DD.C0 DD.qbar)

/-- **The shear family** `a_χ(cc) := B♭⁻¹(γtot_χ(cc))`. -/
noncomputable def achi (χ : ↥(TCharC D)) (cc : DD.C0) : DD.Vmod :=
  Classical.choose (exists_polar_inverse' (DD := DD) DD.hquad DD.hns
    (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem achi_spec (χ : ↥(TCharC D)) (cc : DD.C0) (v : DD.Vmod) :
    polar DD.qbar (achi S Dsc hσ χ cc) v = gammatot S Dsc hσ χ cc v :=
  Classical.choose_spec (exists_polar_inverse' (DD := DD) DD.hquad DD.hns
    (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc)) v

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `a_χ` is a crossed 1-cocycle (the `ha` of `prop_8_8_target`). -/
theorem achi_crossed (χ : ↥(TCharC D)) (cc dd : DD.C0) :
    achi S Dsc hσ χ (cc * dd) = achi S Dsc hσ χ cc + cc • achi S Dsc hσ χ dd := by
  apply polar_inj (DD := DD) DD.hquad DD.hns
  intro v
  rw [achi_spec, gammatot_dual_crossed S Dsc hσ χ cc dd v, DD.hquad.polar_add_left,
    achi_spec, polar_smul_inv hinvQ, achi_spec]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The kill condition (`hkill` of `prop_8_8_target`). -/
theorem achi_kill (χ : ↥(TCharC D)) (cc : DD.C0) (v : DD.Vmod) :
    polar DD.qbar (achi S Dsc hσ χ cc) v
      + (AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc)) v = 0 := by
  show polar DD.qbar (achi S Dsc hσ χ cc) v + gammatot S Dsc hσ χ cc v = 0
  rw [achi_spec]
  exact CharTwo.add_self_eq_zero _

/-! ### The `Ψ_χ`-normal form -/

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The zero-form `kappa0` in `γ'' + ∂g`-normal form (pair level). -/
theorem kappa0_datChi_decomp (χ : ↥(TCharC D)) (p q : DD.Vmod × DD.C0) :
    kappa0 (datChi DD S hσ χ) p q
      = gamma2 S hσ χ p.2 (p.2 • q.1)
        + (gchi S hσ χ (pmul p q).1 + gchi S hσ χ p.1 + gchi S hσ χ q.1) := by
  show χ.1 (mDef DD S p.1 (p.2 • q.1)) + χ.1 (conjDef DD S hσ p.2 q.1) = _
  unfold gamma2
  rw [inv_smul_smul]
  have hg := gchi_split S hσ χ p.1 (p.2 • q.1)
  have hpm : (pmul p q).1 = p.1 + p.2 • q.1 := rfl
  rw [hpm]
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf))) hg

/-- The total scalar phase input `δtot_χ := e_χ + δκ`. -/
noncomputable def deltatot (χ : ↥(TCharC D)) (cc dd : DD.C0) : ZMod 2 :=
  χ.1 (uDef DD S cc dd) + dkap σ Dsc hσ cc dd

/-- The combined coboundary potential `W_χ`. -/
noncomputable def wtot (χ : ↥(TCharC D)) (x : DD.Vmod × DD.C0) : ZMod 2 :=
  gchi S hσ χ x.1 + gkappa σ Dsc hσ x.1 + ukap σ Dsc hσ x.1 x.2

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The `Ψ_χ`-normal form** (design §6): the full obstruction cochain is
`κ⁰ + Γγtot + inf δtot + ∂W_χ`, pointwise. -/
theorem psi_decomp (χ : ↥(TCharC D)) (p q : DD.Vmod × DD.C0) :
    χ.1 (JDefT S hσ p q) + kfull σ Dsc p q
      = kappa0 DD.dat p q
        + gammatot S Dsc hσ χ p.2 (p.2 • q.1)
        + deltatot S Dsc hσ χ p.2 q.2
        + (wtot S Dsc hσ χ (pmul p q) + wtot S Dsc hσ χ p + wtot S Dsc hσ χ q) := by
  obtain ⟨v, cc⟩ := p
  obtain ⟨w, dd⟩ := q
  have h1 := chiJDef_eq S hσ χ (v, cc) (w, dd)
  have h2 := kappa0_datChi_decomp S hσ χ (v, cc) (w, dd)
  have h3 := theta'_decomp σ Dsc hσ v cc w dd
  -- `θ'` unfolded back to `kfull + κ⁰ + ∂gκ`
  have h4 : theta' σ Dsc hσ ((v, cc) : DD.Vmod × DD.C0) (w, dd)
      = kfull σ Dsc ((v, cc) : DD.Vmod × DD.C0) (w, dd)
        + kappa0 DD.dat ((v, cc) : DD.Vmod × DD.C0) (w, dd)
        + (gkappa σ Dsc hσ (pmul ((v, cc) : DD.Vmod × DD.C0) (w, dd)).1
            + gkappa σ Dsc hσ v + gkappa σ Dsc hσ w) := rfl
  -- `γκ`-value at the calibrated argument
  have h5 : gammakap σ Dsc hσ cc (cc • w)
      = gkraw σ Dsc hσ cc w + ukap σ Dsc hσ (cc • w) cc := by
    unfold gammakap
    rw [inv_smul_smul]
  have hpm : pmul ((v, cc) : DD.Vmod × DD.C0) (w, dd) = (v + cc • w, cc * dd) := rfl
  unfold gammatot deltatot wtot
  rw [hpm] at h2 h4 ⊢
  simp only at h1 h2 h3 h4 ⊢
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf)))
    h1 + h2 + h3 + h4 + h5

end Assembly

end AffineTLift

end SectionEight

end GQ2
