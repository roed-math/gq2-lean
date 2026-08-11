/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.KeystoneDelta.AffineAssembly

/-!
# The keystone and the phase-cover data

Split off from `GQ2.KeystoneDelta` (design §6).  This file provides:

* **Stage E** — the shear cocycle `shChi`, the total scalar phase `DeltaChi`, the generic-Γ
  graph-pullback/coboundary memberships, and **the keystone** (`keystone`): the (135)-Γ
  completed square, whose only Γ-residues are `htriv` and `hH2`;
* **Stage F** — the phase-cover data for `centralCoverOfCocycle`: the Serre identity
  `DeltaChi_cocycle` and the normalizations `DeltaChi_one_left`/`DeltaChi_one_right`.

See `GQ2.KeystoneDelta` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

/-! ## Stage E: the keystone (design §6 — the (135)-Γ completed square)

Pulling the `Ψ_χ`-normal form back along the graph of `c` and completing the square with
`prop_8_8_target` at the shear family `a_χ` yields the master count's `hkey`:

  `β_χ(c) + β_ξ(c) = Q⁰(c + sh_χ) + ι_Γ(ρ'^* Δ_χ)`

at `Δ_χ := DeltaScalar (γtot_χ, δtot_χ, a_χ)` and `sh_χ := a_χ ∘ ρ'`.  The only Γ-residues
are `htriv` and `hH2`; everything else is the C-level data proved above. -/

section Keystone

open SectionSix

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable (Dsc : Descent D)
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
variable (hinvQ : IsInvariant DD.C0 DD.qbar)

/-- **The shear cocycle** `sh_χ := a_χ ∘ ρ'`: the (133) shift-vector family as a crossed
`V`-cocycle (continuity through the discrete `Bg ⧸ M`). -/
noncomputable def shChi (χ : ↥(TCharC D)) : VCocycle DD ρ where
  c := fun γ => achi S Dsc hσ χ (rho0 DD ρ γ)
  cont := by
    haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
    have h : (fun γ => iV DD (Multiplicative.ofAdd (achi S Dsc hσ χ (rho0 DD ρ γ))))
        = (fun x : Bg ⧸ D.M => iV DD (Multiplicative.ofAdd (achi S Dsc hσ χ (liftC0 DD x))))
          ∘ ρ := rfl
    rw [h]
    exact continuous_of_discreteTopology.comp ρ.continuous_toFun
  crossed := fun γ δ => by
    rw [map_mul]
    exact achi_crossed S Dsc hσ hinvQ χ (rho0 DD ρ γ) (rho0 DD ρ δ)

/-- **The total scalar phase family** `Δ_χ` (the (134) total phase `Δ_{χ,κ}`, C-level). -/
noncomputable def DeltaChi (χ : ↥(TCharC D)) : DD.C0 × DD.C0 → ZMod 2 :=
  DeltaScalar DD.dat
    (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
    (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
    (achi S Dsc hσ χ)

variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **Generic-Γ well-formedness of the graph pullback** (Lemma 6.1/(62); the `G_ℚ₂`-bound
ancestor is `SectionSix.graphPullback_mem_Z2`): along a crossed cocycle, the pullback of the
equivariant base datum is a continuous 2-cocycle. -/
theorem graphPullback_mem_Z2_of_cocycle (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (c : VCocycle DD ρ) :
    graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c ∈ Z2 Γ (ZMod 2) := by
  classical
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  refine mem_Z2_iff.mpr ⟨?_, fun g h k => ?_⟩
  · -- continuity: factor through the discrete `(Q × B/M) × (Q × B/M)`
    have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      fun a b hab => iV_ofAdd_inj DD hab
    have heq : graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c
        = (fun t : ((Bg ⧸ D.T) × (Bg ⧸ D.M)) × ((Bg ⧸ D.T) × (Bg ⧸ D.M)) =>
            DD.dat.f
              (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.1.1)
              (liftC0 DD t.1.2
                • Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.2.1)
            + DD.dat.m (liftC0 DD t.1.2)
                (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.2.1))
          ∘ (fun p : Γ × Γ => ((iV DD (Multiplicative.ofAdd (c.c p.1)), ρ p.1),
              (iV DD (Multiplicative.ofAdd (c.c p.2)), ρ p.2))) := by
      funext p
      show DD.dat.f (c.c p.1) (rho0 DD ρ p.1 • c.c p.2) + DD.dat.m (rho0 DD ρ p.1) (c.c p.2)
        = DD.dat.f
            (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
              (iV DD (Multiplicative.ofAdd (c.c p.1))))
            (liftC0 DD (ρ p.1)
              • Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
                  (iV DD (Multiplicative.ofAdd (c.c p.2))))
          + DD.dat.m (liftC0 DD (ρ p.1))
              (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
                (iV DD (Multiplicative.ofAdd (c.c p.2))))
      rw [Function.leftInverse_invFun hinj (c.c p.1), Function.leftInverse_invFun hinj (c.c p.2)]
      rfl
    rw [heq]
    exact continuous_of_discreteTopology.comp
      (((c.cont.comp continuous_fst).prodMk (ρ.continuous_toFun.comp continuous_fst)).prodMk
        ((c.cont.comp continuous_snd).prodMk (ρ.continuous_toFun.comp continuous_snd)))
  · -- the cocycle identity: (59) + (60) + the factor-set identity, in char 2
    rw [htriv]
    show DD.dat.f (c.c h) (rho0 DD ρ h • c.c k) + DD.dat.m (rho0 DD ρ h) (c.c k)
        + (DD.dat.f (c.c g) (rho0 DD ρ g • c.c (h * k)) + DD.dat.m (rho0 DD ρ g) (c.c (h * k)))
      = DD.dat.f (c.c (g * h)) (rho0 DD ρ (g * h) • c.c k)
          + DD.dat.m (rho0 DD ρ (g * h)) (c.c k)
        + (DD.dat.f (c.c g) (rho0 DD ρ g • c.c h) + DD.dat.m (rho0 DD ρ g) (c.c h))
    have hbk : c.c (h * k) = c.c h + rho0 DD ρ h • c.c k := c.crossed h k
    have hbg : c.c (g * h) = c.c g + rho0 DD ρ g • c.c h := c.crossed g h
    have hρm : rho0 DD ρ (g * h) = rho0 DD ρ g * rho0 DD ρ h := map_mul _ g h
    rw [hbk, hbg, hρm, smul_add, ← mul_smul]
    have h59 := DD.hdat.m_quad (rho0 DD ρ g) (c.c h) (rho0 DD ρ h • c.c k)
    have h60 := DD.hdat.m_mul (rho0 DD ρ g) (rho0 DD ρ h) (c.c k)
    have hco := DD.hdat.f_cocycle (c.c g) (rho0 DD ρ g • c.c h)
      ((rho0 DD ρ g * rho0 DD ρ h) • c.c k)
    rw [← mul_smul] at h59
    linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf)))
      h59 + h60 + hco

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The graph-coboundary of any pair potential along a crossed cocycle is a continuous
coboundary (the `∂`-terms of the `Ψ_χ`-pullback). -/
theorem graphCob_mem_B2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (u : DD.Vmod × DD.C0 → ZMod 2) (cx : VCocycle DD ρ) :
    (fun p : Γ × Γ => u (cx.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + u (cx.c p.1, rho0 DD ρ p.1) + u (cx.c p.2, rho0 DD ρ p.2)) ∈ B2 Γ (ZMod 2) := by
  classical
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  refine ⟨fun γ => u (cx.c γ, rho0 DD ρ γ), ?_, ?_⟩
  · have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      fun a b hab => iV_ofAdd_inj DD hab
    have heq : (fun γ => u (cx.c γ, rho0 DD ρ γ))
        = (fun t : (Bg ⧸ D.T) × (Bg ⧸ D.M) =>
            u (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.1,
              liftC0 DD t.2))
          ∘ (fun γ => (iV DD (Multiplicative.ofAdd (cx.c γ)), ρ γ)) := by
      funext γ
      show u (cx.c γ, rho0 DD ρ γ)
        = u (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
            (iV DD (Multiplicative.ofAdd (cx.c γ))), liftC0 DD (ρ γ))
      rw [Function.leftInverse_invFun hinj (cx.c γ)]
      rfl
    rw [heq]
    exact continuous_of_discreteTopology.comp (cx.cont.prodMk ρ.continuous_toFun)
  · funext p
    show p.1 • u (cx.c p.2, rho0 DD ρ p.2) - u (cx.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + u (cx.c p.1, rho0 DD ρ p.1)
      = u (cx.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2)) + u (cx.c p.1, rho0 DD ρ p.1)
        + u (cx.c p.2, rho0 DD ρ p.2)
    rw [htriv]
    have hchar : ∀ a b cc : ZMod 2, a - b + cc = b + cc + a := by decide
    exact hchar _ _ _

include hinvQ in
/-- **The keystone** (Prop 8.8's completed square (135) at Γ-level, design §6): the master
count's `hkey` at `Δ := DeltaChi` and `sh := shChi`.  Only `htriv` and `hH2` are Γ-residues. -/
theorem keystone (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (χ : ↥(TCharC D)) (c : VCocycle DD ρ) :
    betaChi S hσ χ c + betaXi hσ Dsc c
      = QZero DD ρ (c + shChi S Dsc hσ hinvQ χ)
        + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (DeltaChi S Dsc hσ χ)) := by
  classical
  set c₀ : VCocycle DD ρ := c + shChi S Dsc hσ hinvQ χ with hc₀
  -- the completed square at the keystone data
  obtain ⟨w, hw⟩ := prop_8_8_target DD.qbar DD.hquad DD.dat DD.hdat
    (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
    (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
    (achi S Dsc hσ χ) (achi_crossed S Dsc hσ hinvQ χ) (achi_kill S Dsc hσ χ)
  -- the exponent-2 shear collapse: `s_a(graph c₀) = graph c`
  have hcol : ∀ γ' : Γ, shear (achi S Dsc hσ χ) (c₀.c γ', rho0 DD ρ γ')
      = (c.c γ', rho0 DD ρ γ') := by
    intro γ'
    have h1 : c₀.c γ' = c.c γ' + achi S Dsc hσ χ (rho0 DD ρ γ') := by rw [hc₀]; rfl
    show (c₀.c γ' + achi S Dsc hσ χ (rho0 DD ρ γ'), rho0 DD ρ γ') = (c.c γ', rho0 DD ρ γ')
    rw [h1, add_assoc, Vmod_exp2 DD, add_zero]
  -- pointwise: the `Ψ_χ`-pullback of the completed square
  have hpoint : ∀ γ δ : Γ,
      chiDef S hσ χ c (γ, δ) + pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc) (γ, δ)
        = graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c (γ, δ)
            + pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ) (γ, δ)
          + ((w (c₀.c (γ * δ), rho0 DD ρ (γ * δ)) + w (c₀.c γ, rho0 DD ρ γ)
                + w (c₀.c δ, rho0 DD ρ δ))
              + (wtot S Dsc hσ χ (c.c (γ * δ), rho0 DD ρ (γ * δ))
                + wtot S Dsc hσ χ (c.c γ, rho0 DD ρ γ)
                + wtot S Dsc hσ χ (c.c δ, rho0 DD ρ δ))) := by
    intro γ δ
    have hχval : chiDef S hσ χ c (γ, δ)
        = χ.1 (JDefT S hσ (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ)) := by
      have h := tDef_eq_JDefT S hσ c (γ, δ)
      simp only at h
      exact congrArg χ.1 h
    have hξval : pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc) (γ, δ)
        = kfull σ Dsc (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ) := rfl
    have hpsi := psi_decomp S Dsc hσ χ (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ)
    rw [graph_pmul c γ δ] at hpsi
    simp only at hpsi
    have h88 := hw (c₀.c γ, rho0 DD ρ γ) (c₀.c δ, rho0 DD ρ δ)
    rw [hcol γ, hcol δ] at h88
    simp only [gammaEdge, inflScalar, AddMonoidHom.mk'_apply] at h88
    rw [show c₀.c γ + rho0 DD ρ γ • c₀.c δ = c₀.c (γ * δ) from (c₀.crossed γ δ).symm,
      show rho0 DD ρ γ * rho0 DD ρ δ = rho0 DD ρ (γ * δ) from (map_mul (rho0 DD ρ) γ δ).symm]
      at h88
    have hQval : graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c (γ, δ)
        = kappa0 DD.dat (c₀.c γ, rho0 DD ρ γ) (c₀.c δ, rho0 DD ρ δ) := rfl
    have hΔval : pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ) (γ, δ)
        = DeltaScalar DD.dat
            (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
            (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
            (achi S Dsc hσ χ) (rho0 DD ρ γ, rho0 DD ρ δ) := rfl
    linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf)))
      hχval + hξval + hpsi + h88 + hQval + hΔval
  -- memberships
  have hZχ : chiDef S hσ χ c ∈ Z2 Γ (ZMod 2) := chiDef_mem_Z2 S hσ htriv χ c
  have hZξ : pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc) ∈ Z2 Γ (ZMod 2) :=
    pullCoc_mem_Z2 htriv (qOfCocycle DD ρ σ hσ c).1 (fun g h k => xi_cocycle Dsc g h k)
  have hZQ : graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c ∈ Z2 Γ (ZMod 2) :=
    graphPullback_mem_Z2_of_cocycle htriv c₀
  have hBw : (fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
      + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2)) ∈ B2 Γ (ZMod 2) :=
    graphCob_mem_B2 htriv w c₀
  have hBW : (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
      + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
      + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2)) ∈ B2 Γ (ZMod 2) :=
    graphCob_mem_B2 htriv (wtot S Dsc hσ χ) c
  have hBΨ : ((fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2))
      + (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
        + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2))) ∈ B2 Γ (ZMod 2) :=
    AddSubgroup.add_mem _ hBw hBW
  -- the function-level identity
  have hfun : chiDef S hσ χ c + pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc)
      = (graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c
          + pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ))
        + ((fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
            + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2))
          + (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
            + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
            + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2))) := by
    funext p
    obtain ⟨γ, δ⟩ := p
    exact hpoint γ δ
  -- Z²-membership of the Δ-pullback, by subtraction
  have hZΔ : pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ) ∈ Z2 Γ (ZMod 2) := by
    have hrew : pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ)
        = (chiDef S hσ χ c + pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc)
            - graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c)
          - ((fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
              + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2))
            + (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
              + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
              + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2))) := by
      rw [hfun]
      abel
    rw [hrew]
    exact AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ hZχ hZξ) hZQ) (B2_le_Z2 hBΨ)
  -- `ι_Γ`-assembly
  show iotaB (chiDef S hσ χ c) + iotaB (pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc))
    = iotaB (graphPullback DD.dat (fun γ => rho0 DD ρ γ) c₀.c)
      + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (DeltaChi S Dsc hσ χ))
  rw [← iotaB_add hH2 hZχ hZξ, hfun,
    iotaB_add hH2 (AddSubgroup.add_mem _ hZQ hZΔ) (B2_le_Z2 hBΨ),
    iotaB_add hH2 hZQ hZΔ, iotaB_of_mem_B2 hBΨ, add_zero]

end Keystone

/-! ## Stage F: the phase-cover data (design §6, c2)

`centralCoverOfCocycle` consumes a **normalized raw 2-cocycle** on `C₀`.  Here we supply the
three inputs for `Δ_χ`: the Serre identity (`DeltaChi_cocycle` — the completed square on the
`(0,·)`-section minus the bundle/base/coboundary Serre identities) and the two normalizations
(`DeltaChi_one_left`/`right` — from the proved normalization atoms).  All C-level. -/

section PhaseData

open SectionSix

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable (Dsc : Descent D)
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
variable (hinvQ : IsInvariant DD.C0 DD.qbar)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `Θ'` vanishes on `pone`-rows. -/
theorem theta'_pone_left (q : DD.Vmod × DD.C0) : theta' σ Dsc hσ pone q = 0 := by
  unfold theta'
  rw [theta_pone_left, pone_pmul]
  show 0 + (gkappa σ Dsc hσ q.1 + gkappa σ Dsc hσ 0 + gkappa σ Dsc hσ q.1) = 0
  rw [gkappa_zero, zero_add, add_zero]
  exact CharTwo.add_self_eq_zero _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `Θ'` vanishes on `pone`-columns. -/
theorem theta'_pone_right (p : DD.Vmod × DD.C0) : theta' σ Dsc hσ p pone = 0 := by
  unfold theta'
  rw [theta_pone_right, pmul_pone]
  show 0 + (gkappa σ Dsc hσ p.1 + gkappa σ Dsc hσ p.1 + gkappa σ Dsc hσ 0) = 0
  rw [gkappa_zero, zero_add, add_zero]
  exact CharTwo.add_self_eq_zero _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `uσ`-defect normalization, left. -/
theorem uDef_one_left (cc : DD.C0) : uDef DD S 1 cc = 1 := by
  apply Subtype.ext
  show S.uσ 1 * S.uσ cc * (S.uσ (1 * cc))⁻¹ = 1
  rw [S.uσ_one, one_mul, one_mul, mul_inv_cancel]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `uσ`-defect normalization, right. -/
theorem uDef_one_right (cc : DD.C0) : uDef DD S cc 1 = 1 := by
  apply Subtype.ext
  show S.uσ cc * S.uσ 1 * (S.uσ (cc * 1))⁻¹ = 1
  rw [S.uσ_one, mul_one, mul_one, mul_inv_cancel]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γtot_χ(cc)` kills `0`. -/
theorem gammatot_zero (χ : ↥(TCharC D)) (cc : DD.C0) : gammatot S Dsc hσ χ cc 0 = 0 := by
  have h := gammatot_add S Dsc hσ χ cc 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γtot_χ(1) = 0` (the edge is normalized at the identity). -/
theorem gammatot_one (χ : ↥(TCharC D)) (x : DD.Vmod) : gammatot S Dsc hσ χ 1 x = 0 := by
  unfold gammatot
  have h2 : gamma2 S hσ χ 1 x = 0 := by
    unfold gamma2
    rw [inv_one, one_smul, conjDef_one_left, TCharC.map_one, zero_add]
    exact CharTwo.add_self_eq_zero _
  have hk : gammakap σ Dsc hσ 1 x = 0 := by
    unfold gammakap gkraw ukap
    rw [inv_one, one_smul, theta'_VV σ Dsc hσ 0 x, theta'_VV σ Dsc hσ x 0, add_zero]
  rw [h2, hk, add_zero]

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The shear family is normalized: `a_χ(1) = 0`. -/
theorem achi_one (χ : ↥(TCharC D)) : achi S Dsc hσ χ 1 = 0 := by
  have h := achi_crossed S Dsc hσ hinvQ χ 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `δtot_χ` is normalized on the left. -/
theorem deltatot_one_left (χ : ↥(TCharC D)) (cc : DD.C0) : deltatot S Dsc hσ χ 1 cc = 0 := by
  unfold deltatot
  rw [uDef_one_left S cc, TCharC.map_one]
  have hd : dkap σ Dsc hσ 1 cc = 0 := by
    show theta' σ Dsc hσ pone (0, cc) = 0
    exact theta'_pone_left Dsc hσ (0, cc)
  rw [hd, add_zero]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `δtot_χ` is normalized on the right. -/
theorem deltatot_one_right (χ : ↥(TCharC D)) (cc : DD.C0) : deltatot S Dsc hσ χ cc 1 = 0 := by
  unfold deltatot
  rw [uDef_one_right S cc, TCharC.map_one]
  have hd : dkap σ Dsc hσ cc 1 = 0 := by
    show theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) pone = 0
    exact theta'_pone_right Dsc hσ ((0, cc) : DD.Vmod × DD.C0)
  rw [hd, add_zero]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Serre identity for `χ ∘ JDefT`**: the associativity defect of the product lift `Jmap`
conjugates by `Jmap p`, and the `C`-invariance of `χ` kills the conjugation. -/
theorem chiJDefT_serre (χ : ↥(TCharC D)) (p q r : DD.Vmod × DD.C0) :
    χ.1 (JDefT S hσ q r) + χ.1 (JDefT S hσ p (pmul q r))
      = χ.1 (JDefT S hσ (pmul p q) r) + χ.1 (JDefT S hσ p q) := by
  -- the nonabelian defect identity, raw
  have hraw : (JDefT S hσ p q : Bg) * (JDefT S hσ (pmul p q) r : Bg)
      = Jmap S p * (JDefT S hσ q r : Bg) * (Jmap S p)⁻¹ * (JDefT S hσ p (pmul q r) : Bg) := by
    show Jmap S p * Jmap S q * (Jmap S (pmul p q))⁻¹
          * (Jmap S (pmul p q) * Jmap S r * (Jmap S (pmul (pmul p q) r))⁻¹)
        = Jmap S p * (Jmap S q * Jmap S r * (Jmap S (pmul q r))⁻¹) * (Jmap S p)⁻¹
          * (Jmap S p * Jmap S (pmul q r) * (Jmap S (pmul p (pmul q r)))⁻¹)
    rw [pmul_assoc]
    group
  -- lift to the subtype and push through `χ`
  have hsub : JDefT S hσ p q * JDefT S hσ (pmul p q) r
      = (⟨Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹,
          D.hT.conj_mem _ (JDefT S hσ q r).2 _⟩ : ↥D.T)
        * JDefT S hσ p (pmul q r) := by
    apply Subtype.ext
    show (JDefT S hσ p q : Bg) * (JDefT S hσ (pmul p q) r : Bg)
      = Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹ * ↑(JDefT S hσ p (pmul q r))
    exact hraw
  have hkey : χ.1 (JDefT S hσ p q) + χ.1 (JDefT S hσ (pmul p q) r)
      = χ.1 (JDefT S hσ q r) + χ.1 (JDefT S hσ p (pmul q r)) := by
    calc χ.1 (JDefT S hσ p q) + χ.1 (JDefT S hσ (pmul p q) r)
        = χ.1 (JDefT S hσ p q * JDefT S hσ (pmul p q) r) := (TCharC.map_mul χ _ _).symm
      _ = χ.1 ((⟨Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹,
            D.hT.conj_mem _ (JDefT S hσ q r).2 _⟩ : ↥D.T) * JDefT S hσ p (pmul q r)) := by
          rw [hsub]
      _ = χ.1 (⟨Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹,
            D.hT.conj_mem _ (JDefT S hσ q r).2 _⟩ : ↥D.T)
          + χ.1 (JDefT S hσ p (pmul q r)) := TCharC.map_mul χ _ _
      _ = χ.1 (JDefT S hσ q r) + χ.1 (JDefT S hσ p (pmul q r)) := by
          rw [TCharC.conj_invariant χ (Jmap S p) (JDefT S hσ q r)]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hkey

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Serre identity for the `Ψ_χ`-bundle** `κ⁰ + Γγtot + inf δtot`, by the `psi_decomp`
normal form and the three component Serre identities. -/
theorem bundle_serre (χ : ↥(TCharC D)) (p q r : DD.Vmod × DD.C0) :
    (kappa0 DD.dat q r + gammatot S Dsc hσ χ q.2 (q.2 • r.1) + deltatot S Dsc hσ χ q.2 r.2)
      + (kappa0 DD.dat p (pmul q r)
        + gammatot S Dsc hσ χ p.2 (p.2 • (pmul q r).1) + deltatot S Dsc hσ χ p.2 (pmul q r).2)
    = (kappa0 DD.dat (pmul p q) r
        + gammatot S Dsc hσ χ (pmul p q).2 ((pmul p q).2 • r.1)
        + deltatot S Dsc hσ χ (pmul p q).2 r.2)
      + (kappa0 DD.dat p q + gammatot S Dsc hσ χ p.2 (p.2 • q.1)
        + deltatot S Dsc hσ χ p.2 q.2) := by
  have h1 := psi_decomp S Dsc hσ χ q r
  have h2 := psi_decomp S Dsc hσ χ p (pmul q r)
  have h3 := psi_decomp S Dsc hσ χ (pmul p q) r
  have h4 := psi_decomp S Dsc hσ χ p q
  have hj := chiJDefT_serre S hσ χ p q r
  have hk := kfull_serre σ Dsc hσ p q r
  have hpw := pcob_serre (DD := DD) (wtot S Dsc hσ χ) p q r
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero,
    show (4 : ZMod 2) = 0 from by decide]); (try ring_nf)))
    h1 + h2 + h3 + h4 + hj + hk + hpw

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The phase-cover cocycle law** (`hcoc` of `centralCoverOfCocycle`): `Δ_χ` satisfies the
raw Serre identity on `C₀` — the completed square on the `(0,·)`-section, minus the
bundle/base/coboundary Serre identities. -/
theorem DeltaChi_cocycle (χ : ↥(TCharC D)) (g h k : DD.C0) :
    DeltaChi S Dsc hσ χ (h, k) + DeltaChi S Dsc hσ χ (g, h * k)
      = DeltaChi S Dsc hσ χ (g * h, k) + DeltaChi S Dsc hσ χ (g, h) := by
  obtain ⟨w, hw⟩ := prop_8_8_target DD.qbar DD.hquad DD.dat DD.hdat
    (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
    (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
    (achi S Dsc hσ χ) (achi_crossed S Dsc hσ hinvQ χ) (achi_kill S Dsc hσ χ)
  -- the `(0,·)`-section, its shear, and their `pmul`-multiplicativity
  have hsh : ∀ x : DD.C0, shear (achi S Dsc hσ χ) ((0, x) : DD.Vmod × DD.C0)
      = (achi S Dsc hσ χ x, x) := by
    intro x
    show ((0 : DD.Vmod) + achi S Dsc hσ χ x, x) = (achi S Dsc hσ χ x, x)
    rw [zero_add]
  have hpm0 : ∀ x y : DD.C0, pmul ((0, x) : DD.Vmod × DD.C0) (0, y) = (0, x * y) := by
    intro x y
    show ((0 : DD.Vmod) + x • (0 : DD.Vmod), x * y) = (0, x * y)
    rw [smul_zero, add_zero]
  have hpma : ∀ x y : DD.C0,
      pmul ((achi S Dsc hσ χ x, x) : DD.Vmod × DD.C0) (achi S Dsc hσ χ y, y)
        = (achi S Dsc hσ χ (x * y), x * y) := by
    intro x y
    show (achi S Dsc hσ χ x + x • achi S Dsc hσ χ y, x * y)
      = (achi S Dsc hσ χ (x * y), x * y)
    rw [← achi_crossed S Dsc hσ hinvQ χ x y]
  -- four completed squares on the section
  have h1 := hw (0, h) (0, k)
  have h2 := hw (0, g) (0, h * k)
  have h3 := hw (0, g * h) (0, k)
  have h4 := hw (0, g) (0, h)
  simp only [hsh, gammaEdge, inflScalar, AddMonoidHom.mk'_apply, smul_zero, add_zero]
    at h1 h2 h3 h4
  -- the bundle Serre at the sheared section, the base and coboundary Serre on the section
  have hb := bundle_serre S Dsc hσ χ (achi S Dsc hσ χ g, g) (achi S Dsc hσ χ h, h)
    (achi S Dsc hσ χ k, k)
  simp only [hpma] at hb
  have hk0 := kappa0_serre (DD := DD) DD.hdat ((0, g) : DD.Vmod × DD.C0) (0, h) (0, k)
  have hpw := pcob_serre (DD := DD) w ((0, g) : DD.Vmod × DD.C0) (0, h) (0, k)
  simp only [hpm0] at hk0 hpw
  simp only [DeltaChi]
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero,
    show (4 : ZMod 2) = 0 from by decide]); (try ring_nf)))
    h1 + h2 + h3 + h4 + hb + hk0 + hpw

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Left normalization** (`hl` of `centralCoverOfCocycle`): `Δ_χ(1, ·) = 0`. -/
theorem DeltaChi_one_left (χ : ↥(TCharC D)) (cc : DD.C0) :
    DeltaChi S Dsc hσ χ (1, cc) = 0 := by
  show deltatot S Dsc hσ χ 1 cc
      + (DD.dat.f (achi S Dsc hσ χ 1) ((1 : DD.C0) • achi S Dsc hσ χ cc)
        + DD.dat.m 1 (achi S Dsc hσ χ cc))
      + (AddMonoidHom.mk' (gammatot S Dsc hσ χ 1) (gammatot_add S Dsc hσ χ 1))
          ((1 : DD.C0) • achi S Dsc hσ χ cc)
    = 0
  rw [deltatot_one_left S Dsc hσ χ cc, achi_one S Dsc hσ hinvQ χ, one_smul,
    DD.hdat.f_zero_left, DD.hdat.m_one, AddMonoidHom.mk'_apply,
    gammatot_one S Dsc hσ χ (achi S Dsc hσ χ cc)]
  decide

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Right normalization** (`hr` of `centralCoverOfCocycle`): `Δ_χ(·, 1) = 0`. -/
theorem DeltaChi_one_right (χ : ↥(TCharC D)) (cc : DD.C0) :
    DeltaChi S Dsc hσ χ (cc, 1) = 0 := by
  show deltatot S Dsc hσ χ cc 1
      + (DD.dat.f (achi S Dsc hσ χ cc) (cc • achi S Dsc hσ χ 1)
        + DD.dat.m cc (achi S Dsc hσ χ 1))
      + (AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
          (cc • achi S Dsc hσ χ 1)
    = 0
  rw [deltatot_one_right S Dsc hσ χ cc, achi_one S Dsc hσ hinvQ χ, smul_zero,
    DD.hdat.f_zero_right, m_zero (DD := DD) DD.hdat cc, AddMonoidHom.mk'_apply,
    gammatot_zero S Dsc hσ χ cc]
  decide

end PhaseData

end AffineTLift

end SectionEight

end GQ2
