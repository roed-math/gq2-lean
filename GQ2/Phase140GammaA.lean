import GQ2.Phase140Assembly
import GQ2.WordCohBridge
import GQ2.DualityAssembly
import GQ2.FinitelyGenerated
import GQ2.HalfTorsorGammaA
import GQ2.RStageGammaA
import GQ2.Half139Local

/-!
# P-16d6e6: the `Γ_A` (140) counting residues

The candidate-source mirrors of the `G_ℚ₂` (140) counting residues of `GQ2/Phase140Local.lean`.
Where the local file counts `#Z¹_{Γ,ρ'}(V)` with `card_Z1_eq` (the 5.16 local Euler characteristic,
axioms B6/B7), here the same count comes from the **candidate duality** `prop_5_15` (`IsSelfDual`)
through the word-complex bridge `z1Equiv : Z1 GA A ≃+ Z1w (markC ρ')` (`WordCohBridge`) — **no
B-axioms on the word side** (the same swap as `RStageGammaA.hZcount_gammaA`).

* **`hZcard_gammaA`** — `#Z¹_{Γ_A,ρ'}(V) = #V²`, the `Γ_A` twin of `Phase140Local.hZcard_local`.
  The `#fixedPts` factor is `1` by `card_fixedPts_elemDual_eq_one_of_nontrivial` (`V` is a simple
  `𝔽₂[Y_C]`-module with nontrivial action), exactly as in the local file.
* **`hsep` machinery (`hsep_A`)** — the `(T^∨)^C`-separation at `Γ_A` runs the **marking route**
  of P-16d6e5 (`RStageGammaA`) at the `T`-stage, since the local `prop_5_16` cup route
  (`hsep_local`'s stages) has no `Γ_A` analog:
  - `charKer`/`charCover` — the per-character `𝔽₂`-covers `B/ker χ ↠ B/T` of a nonzero
    `χ ∈ (T^∨)^C` (the `T`-stage mirror of `blockFrameImpl.scalarCover`);
  - `exists_lift_charCover` — `β_χ(c) = 0` (`chiDef ∈ B²`) yields a continuous hom lift of
    `g_c` through the `χ`-cover, by the direct `B²`-extraction `g γ := (fLift γ mod ker χ)·z^ψγ`
    — no twisted `H²(Γ,T)` theory;
  then `RStageGammaA.redValues_eq_of_coverLift` + `sep_word` + the `WordLift` correction and
  `Marking.descend` close the separation (increments B/C).

All declarations are std-3 (no B-axioms): the candidate route is axiom-free.
-/

namespace GQ2

namespace Phase140GammaA

open SectionEight AffineTLift CentralObstruction ContCoh WordCohBridge GQ2.FoxH RStageGammaA
  RadicalEdgeGammaA

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

/-- **`hZcard` for `Γ_A`** — `#Z¹_{Γ_A,ρ'}(V) = #V²`.  Mirror of `Phase140Local.hZcard_local` with
the candidate count: the `VCocycle ≃ Z¹_cont(Γ_A, V)` bridge (structurally `Γ`-generic, copied
from the local file), then `z1Equiv` + `prop_5_15` clause 2 (`#Z1w = #V²·#fixedPts`) instead of
`card_Z1_eq`, and the `#fixedPts = 1` factor from the simple nontrivial `Y_C`-action
(`card_fixedPts_elemDual_eq_one_of_nontrivial`).

`hnt` (the nontrivial `Y_C`-action) is REQUIRED — in the `#V = 2 ∧ Y_C = 1` corner
`#(V^∨)^{Y_C} = 2 ≠ 1` and the identity is false; it is discharged at the capstone from the
block's chief-factor structure (same amendment as the local file). -/
theorem hZcard_gammaA
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card En.Vmod * Nat.card En.Vmod := by
  classical
  -- the lower map `θ = ρ.1.1 : Γ_A ↠ Y_C`, retyped against the raw quotient `GA`
  let θ : ContinuousMonoidHom GA RF.YC := ρ.1.1
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  have hroundtrip : ∀ γ : GA,
      rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = θ γ :=
    fun γ => rho0_descData_rhoPrime b F En l h ρ γ
  -- `En.Vmod` (with its `Y_C`-action) as a `GA`-module through `θ`
  letI : TopologicalSpace En.Vmod := ⊥
  haveI : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI actG : DistribMulAction GA En.Vmod := DistribMulAction.compHom En.Vmod θ.toMonoidHom
  have hcomp : ∀ (γ : GA) (v : En.Vmod), γ • v = θ γ • v := fun _ _ => rfl
  haveI : ContinuousSMul GA En.Vmod := by
    constructor
    have hfac : (fun p : GA × En.Vmod => p.1 • p.2)
        = (fun q : RF.YC × En.Vmod => q.1 • q.2) ∘ (fun p : GA × En.Vmod => (θ p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ v : En.Vmod, v + v = 0 := fun v => Vmod_exp2 (En.descData l h) v
  -- the `VCocycle ≃ Z¹_cont(GA, En.Vmod)` bridge (continuity through the `iV ∘ ofAdd` injection)
  have hequiv : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      ≃ ↥(Z1 GA En.Vmod) :=
    { toFun := fun c =>
        ⟨fun γ => (c.c γ : En.Vmod), by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · have hinj : Function.Injective
                (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v)) :=
              fun a a' haa' => iV_ofAdd_inj (En.descData l h) haa'
            have hlc : IsLocallyConstant
                (fun γ => iV (En.descData l h) (Multiplicative.ofAdd (c.c γ : En.Vmod))) :=
              (IsLocallyConstant.iff_continuous _).mpr c.cont
            exact (IsLocallyConstant.desc (α := En.Vmod) (fun γ => (c.c γ : En.Vmod))
              (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v))
              hlc hinj).continuous
          · intro γ δ
            have H := c.crossed γ δ
            rw [hroundtrip γ] at H
            exact H⟩
      invFun := fun z =>
        { c := fun γ => (z.1 γ : (En.descData l h).Vmod)
          cont := by
            have hc : Continuous (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v)) :=
              continuous_of_discreteTopology
            exact hc.comp (mem_Z1_iff.mp z.2).1
          crossed := fun γ δ => by
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hroundtrip γ]
            exact hz }
      left_inv := fun c => by cases c; rfl
      right_inv := fun z => rfl }
  -- the count: `#Z¹(GA, V) = #Z1w(markC θ) = #V² · #fixedPts Y_C (V^∨)` (candidate duality)
  have adm := markC_admissible θ hθs
  rw [Nat.card_congr hequiv, Nat.card_congr (z1Equiv θ hcomp hθs hA₂).toEquiv,
    (GQ2.FoxH.prop_5_15 (markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]
  -- `#fixedPts Y_C (V^∨) = 1` (simple module, nontrivial action)
  obtain ⟨v, hv⟩ := hVne
  have hsimpleMod : IsSimpleModTwo RF.YC En.Vmod :=
    ⟨nontrivial_of_ne (0 : En.Vmod) v (Ne.symm hv), fun W hW => hsimple W (fun g w hw => hW g w hw)⟩
  rw [card_fixedPts_elemDual_eq_one_of_nontrivial hsimpleMod hnt, mul_one, pow_two]

/-! ## The per-character `𝔽₂`-covers of `Q = B/T`  (Γ-generic; the `hsep_A` L4 covers) -/

section CharCover

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- The `ZMod 2` value dichotomy. -/
private theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-- The kernel of a `C`-invariant character, as a subgroup of `↥D.T`. -/
def charKerSub (χ : ↥(TCharC D)) : Subgroup ↥D.T where
  carrier := {t | χ.1 t = 0}
  one_mem' := TCharC.map_one χ
  mul_mem' := fun {a b} ha hb => by
    show χ.1 (a * b) = 0
    rw [TCharC.map_mul χ a b, ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    show χ.1 a⁻¹ = 0
    rw [TCharC.map_inv χ a]
    exact ha

/-- The kernel of `χ`, pushed to a subgroup of `Bg`. -/
def charKer (χ : ↥(TCharC D)) : Subgroup Bg := (charKerSub χ).map D.T.subtype

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem charKer_le (χ : ↥(TCharC D)) : charKer χ ≤ D.T :=
  Subgroup.map_subtype_le _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem mem_charKer_iff (χ : ↥(TCharC D)) (t : ↥D.T) :
    (t : Bg) ∈ charKer χ ↔ χ.1 t = 0 := by
  rw [charKer, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [Subtype.coe_injective hst] at hs
  · intro ht
    exact ⟨t, ht, rfl⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem charKer_normal (χ : ↥(TCharC D)) : (charKer χ).Normal := by
  constructor
  intro n hn g
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr
    ⟨⟨g * (t : Bg) * g⁻¹, D.hT.conj_mem (t : Bg) t.2 g⟩, ?_, rfl⟩
  show χ.1 ⟨g * (t : Bg) * g⁻¹, _⟩ = 0
  rw [TCharC.conj_invariant χ g t]
  exact ht

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem exists_val_one (χ : ↥(TCharC D)) (hχ : χ ≠ 0) : ∃ t : ↥D.T, χ.1 t = 1 := by
  by_contra hall
  refine hχ (Subtype.ext (funext fun t => ?_))
  have h01 : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  exact h01 _ (fun h1 => hall ⟨t, h1⟩)

/-- A witness `t₀ ∈ T` with `χ(t₀) = 1` (for `χ ≠ 0`) — the kernel generator's complement. -/
noncomputable def charWitness (χ : ↥(TCharC D)) (hχ : χ ≠ 0) : ↥D.T :=
  (exists_val_one χ hχ).choose

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem charWitness_spec (χ : ↥(TCharC D)) (hχ : χ ≠ 0) : χ.1 (charWitness χ hχ) = 1 :=
  (exists_val_one χ hχ).choose_spec

/-- **The `χ`-cover** `B ⧸ ker χ ↠ B ⧸ T`: a central double cover with kernel
`T/ker χ ≅ 𝔽₂`, generated by the class of the witness `t₀` (`χ(t₀) = 1`).  The `T`-stage
mirror of `blockFrameImpl.scalarCover`; centrality of the kernel is the `C`-invariance
of `χ`. -/
noncomputable def charCover (χ : ↥(TCharC D)) (hχ : χ ≠ 0) : CentralCover (Bg ⧸ D.T) := by
  haveI hKn : (charKer χ).Normal := charKer_normal χ
  letI : TopologicalSpace (Bg ⧸ charKer χ) := ⊥
  haveI : DiscreteTopology (Bg ⧸ charKer χ) := ⟨rfl⟩
  refine
    { cover := Bg ⧸ charKer χ
      p := QuotientGroup.map (charKer χ) D.T (MonoidHom.id Bg)
        (by rw [Subgroup.comap_id]; exact charKer_le χ)
      surj := ?_
      z := QuotientGroup.mk' (charKer χ) ((charWitness χ hχ : ↥D.T) : Bg)
      z_ne := ?_
      z_sq := ?_
      central := ?_
      ker_eq := ?_ }
  · -- surjectivity
    intro x
    induction x using QuotientGroup.induction_on with
    | _ y => exact ⟨QuotientGroup.mk' (charKer χ) y, rfl⟩
  · -- `z ≠ 1`
    rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    intro hmem
    have h0 := (mem_charKer_iff χ (charWitness χ hχ)).mp hmem
    rw [charWitness_spec χ hχ] at h0
    exact one_ne_zero h0
  · -- `z² = 1`
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hmem : ((charWitness χ hχ * charWitness χ hχ : ↥D.T) : Bg) ∈ charKer χ := by
      rw [mem_charKer_iff, TCharC.map_mul χ, charWitness_spec χ hχ]
      decide
    exact hmem
  · -- centrality: `[y, t₀] ∈ ker χ` by `C`-invariance
    intro x
    refine QuotientGroup.induction_on x (fun y => ?_)
    show QuotientGroup.mk' (charKer χ) ((charWitness χ hχ : ↥D.T) : Bg) * QuotientGroup.mk y
      = QuotientGroup.mk y * QuotientGroup.mk' (charKer χ) ((charWitness χ hχ : ↥D.T) : Bg)
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq]
    have hconj : y⁻¹ * (((charWitness χ hχ)⁻¹ : ↥D.T) : Bg) * y⁻¹⁻¹ ∈ D.T :=
      D.hT.conj_mem _ ((charWitness χ hχ)⁻¹).2 y⁻¹
    have hmem : ((⟨y⁻¹ * (((charWitness χ hχ)⁻¹ : ↥D.T) : Bg) * y⁻¹⁻¹, hconj⟩
        * charWitness χ hχ : ↥D.T) : Bg) ∈ charKer χ := by
      rw [mem_charKer_iff, TCharC.map_mul χ,
        TCharC.conj_invariant χ y⁻¹ (charWitness χ hχ)⁻¹ hconj,
        TCharC.map_inv χ, charWitness_spec χ hχ]
      decide
    have hval : (((charWitness χ hχ : ↥D.T) : Bg) * y)⁻¹
        * (y * ((charWitness χ hχ : ↥D.T) : Bg))
        = ((⟨y⁻¹ * (((charWitness χ hχ)⁻¹ : ↥D.T) : Bg) * y⁻¹⁻¹, hconj⟩
            * charWitness χ hχ : ↥D.T) : Bg) := by
      show _ = y⁻¹ * (((charWitness χ hχ : ↥D.T) : Bg))⁻¹ * y⁻¹⁻¹
        * ((charWitness χ hχ : ↥D.T) : Bg)
      group
    rw [hval]
    exact hmem
  · -- kernel = `⟨z⟩`
    have hker : (QuotientGroup.map (charKer χ) D.T (MonoidHom.id Bg)
        (by rw [Subgroup.comap_id]; exact charKer_le χ)).ker
        = D.T.map (QuotientGroup.mk' (charKer χ)) := by
      ext x
      refine QuotientGroup.induction_on x (fun y => ?_)
      rw [MonoidHom.mem_ker,
        show (QuotientGroup.map (charKer χ) D.T (MonoidHom.id Bg)
          (by rw [Subgroup.comap_id]; exact charKer_le χ)) (↑y) = ((y : Bg) : Bg ⧸ D.T)
          from rfl,
        QuotientGroup.eq_one_iff, Subgroup.mem_map]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨r, hrT, hr⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hr
        rw [show y = r * (r⁻¹ * y) from by group]
        exact D.T.mul_mem hrT (charKer_le χ hr)
    rw [hker]
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro t htT
      rw [Subgroup.mem_comap]
      rcases zmod2_cases (χ.1 ⟨t, htT⟩) with h0 | h1
      · have h1' : QuotientGroup.mk' (charKer χ) t = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact (mem_charKer_iff χ ⟨t, htT⟩).mpr h0
        rw [h1']
        exact one_mem _
      · have h1' : QuotientGroup.mk' (charKer χ) t
            = QuotientGroup.mk' (charKer χ) ((charWitness χ hχ : ↥D.T) : Bg) := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
          have hmem : (((⟨t, htT⟩ : ↥D.T)⁻¹ * charWitness χ hχ : ↥D.T) : Bg) ∈ charKer χ := by
            rw [mem_charKer_iff, TCharC.map_mul χ, TCharC.map_inv χ, h1,
              charWitness_spec χ hχ]
            decide
          exact hmem
        rw [h1']
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map_of_mem _ (charWitness χ hχ).2

/-- The reduction `Bg →* (charCover χ hχ).cover` — the `coverMap` of the `χ`-cover. -/
noncomputable def charCoverMap (χ : ↥(TCharC D)) (hχ : χ ≠ 0) :
    Bg →* (charCover χ hχ).cover :=
  haveI : (charKer χ).Normal := charKer_normal χ
  QuotientGroup.mk' (charKer χ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `χ`-cover covers `π_T` through its reduction. -/
theorem charCover_p_comp (χ : ↥(TCharC D)) (hχ : χ ≠ 0) :
    ((charCover χ hχ).p).comp (charCoverMap χ hχ) = QuotientGroup.mk' D.T := by
  ext y
  rfl

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `T`-elements reduce to the kernel sign `z^{χ(t)}` in the `χ`-cover — the
`pair_coverMap` of the `T`-stage. -/
theorem charCoverMap_coe_eq_zpow (χ : ↥(TCharC D)) (hχ : χ ≠ 0) (t : ↥D.T) :
    charCoverMap χ hχ (t : Bg) = (charCover χ hχ).z ^ (χ.1 t).val := by
  haveI : (charKer χ).Normal := charKer_normal χ
  rcases zmod2_cases (χ.1 t) with h0 | h1
  · rw [h0]
    show QuotientGroup.mk' (charKer χ) (t : Bg) = _ ^ (0 : ZMod 2).val
    rw [ZMod.val_zero, pow_zero, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_charKer_iff χ t).mpr h0
  · rw [h1]
    show QuotientGroup.mk' (charKer χ) (t : Bg)
      = QuotientGroup.mk' (charKer χ) ((charWitness χ hχ : ↥D.T) : Bg) ^ (1 : ZMod 2).val
    rw [ZMod.val_one, pow_one, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hmem : ((t⁻¹ * charWitness χ hχ : ↥D.T) : Bg) ∈ charKer χ := by
      rw [mem_charKer_iff, TCharC.map_mul χ, TCharC.map_inv χ, h1, charWitness_spec χ hχ]
      decide
    exact hmem

/-- `z`-powers add `ZMod 2`-exponents (any central double cover: `z² = 1`). -/
theorem cover_z_pow_val_add {B0 : Type} [Group B0] [Finite B0] (Q : CentralCover B0)
    (a b : ZMod 2) : Q.z ^ ((a + b).val) = Q.z ^ a.val * Q.z ^ b.val := by
  have hz2 : Q.z * Q.z = 1 := Q.z_sq
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [show ((1 : ZMod 2) + 1).val = 0 from rfl, ZMod.val_zero, ZMod.val_one, hz2]

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

/-- **`β_χ(c) = 0` produces a lift through the `χ`-cover** (the `T`-stage
`obs_zero_iff_lifts`, forward direction): a `B²`-witness `ψ` for `χ_* tDef` corrects the
pointwise lift `fLift` into a continuous homomorphism `γ ↦ (fLift γ mod ker χ) · z^{ψγ}`
covering `g_c`. -/
theorem exists_lift_charCover [DistribMulAction Γ (ZMod 2)]
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    (χ : ↥(TCharC D)) (hχ : χ ≠ 0) (c : VCocycle DD ρ)
    (hB2 : chiDef S hσ χ c ∈ B2 Γ (ZMod 2)) :
    ∃ gc : ContinuousMonoidHom Γ (charCover χ hχ).cover,
      ∀ γ, (charCover χ hχ).p (gc γ) = (qOfCocycle DD ρ σ hσ c).1 γ := by
  classical
  obtain ⟨ψ, hψC1, hψeq⟩ := AddSubgroup.mem_map.mp hB2
  have hψcont : Continuous ψ := mem_C1_iff.mp hψC1
  have hzc : ∀ w : (charCover χ hχ).cover, Commute (charCover χ hχ).z w :=
    fun w => (charCover χ hχ).central w
  -- the corrected lift is a homomorphism
  have hmul : ∀ γ δ : Γ,
      charCoverMap χ hχ (fLift S c (γ * δ)) * (charCover χ hχ).z ^ (ψ (γ * δ)).val
        = (charCoverMap χ hχ (fLift S c γ) * (charCover χ hχ).z ^ (ψ γ).val)
          * (charCoverMap χ hχ (fLift S c δ) * (charCover χ hχ).z ^ (ψ δ).val) := by
    intro γ δ
    have hf : fLift S c γ * fLift S c δ = (tDef S hσ c (γ, δ) : Bg) * fLift S c (γ * δ) := by
      show _ = fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹ * fLift S c (γ * δ)
      group
    have hdOne : chiDef S hσ χ c (γ, δ) = ψ δ - ψ (γ * δ) + ψ γ := by
      rw [← hψeq]
      show γ • ψ δ - ψ (γ * δ) + ψ γ = _
      rw [htriv]
    have hval : (chiDef S hσ χ c (γ, δ) + (ψ γ + ψ δ)).val = (ψ (γ * δ)).val := by
      congr 1
      have hkey : ∀ x y z w : ZMod 2, x = y - w + z → x + (z + y) = w := by decide
      exact hkey _ _ _ _ hdOne
    calc charCoverMap χ hχ (fLift S c (γ * δ)) * (charCover χ hχ).z ^ (ψ (γ * δ)).val
        = charCoverMap χ hχ (fLift S c (γ * δ))
            * (charCover χ hχ).z ^ ((chiDef S hσ χ c (γ, δ) + (ψ γ + ψ δ)).val) := by
          rw [hval]
      _ = charCoverMap χ hχ (fLift S c (γ * δ))
            * ((charCover χ hχ).z ^ (chiDef S hσ χ c (γ, δ)).val
              * (charCover χ hχ).z ^ ((ψ γ + ψ δ)).val) := by
          rw [cover_z_pow_val_add]
      _ = (charCover χ hχ).z ^ (chiDef S hσ χ c (γ, δ)).val
            * charCoverMap χ hχ (fLift S c (γ * δ))
            * ((charCover χ hχ).z ^ (ψ γ).val * (charCover χ hχ).z ^ (ψ δ).val) := by
          rw [cover_z_pow_val_add, ← mul_assoc,
            ← ((hzc (charCoverMap χ hχ (fLift S c (γ * δ)))).pow_left
              (chiDef S hσ χ c (γ, δ)).val).eq]
      _ = charCoverMap χ hχ ((tDef S hσ c (γ, δ) : Bg)) * charCoverMap χ hχ (fLift S c (γ * δ))
            * ((charCover χ hχ).z ^ (ψ γ).val * (charCover χ hχ).z ^ (ψ δ).val) := by
          rw [charCoverMap_coe_eq_zpow]
          rfl
      _ = charCoverMap χ hχ (fLift S c γ) * charCoverMap χ hχ (fLift S c δ)
            * ((charCover χ hχ).z ^ (ψ γ).val * (charCover χ hχ).z ^ (ψ δ).val) := by
          rw [← map_mul, ← hf, map_mul]
      _ = (charCoverMap χ hχ (fLift S c γ) * (charCover χ hχ).z ^ (ψ γ).val)
            * (charCoverMap χ hχ (fLift S c δ) * (charCover χ hχ).z ^ (ψ δ).val) :=
          ((hzc (charCoverMap χ hχ (fLift S c δ))).pow_left (ψ γ).val).symm.mul_mul_mul_comm
            (charCoverMap χ hχ (fLift S c γ)) ((charCover χ hχ).z ^ (ψ δ).val)
  refine ⟨⟨MonoidHom.mk'
      (fun γ => charCoverMap χ hχ (fLift S c γ) * (charCover χ hχ).z ^ (ψ γ).val)
      (fun γ δ => hmul γ δ), ?_⟩, ?_⟩
  · -- continuity: a discrete-valued function of the continuous pair `(fLift, ψ)`
    show Continuous fun γ =>
      charCoverMap χ hχ (fLift S c γ) * (charCover χ hχ).z ^ (ψ γ).val
    have hfac : (fun γ =>
        charCoverMap χ hχ (fLift S c γ) * (charCover χ hχ).z ^ (ψ γ).val)
        = (fun p : Bg × ZMod 2 => charCoverMap χ hχ p.1 * (charCover χ hχ).z ^ p.2.val)
          ∘ (fun γ => (fLift S c γ, ψ γ)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp ((fLift_continuous S c).prodMk hψcont)
  · -- covering `g_c`
    intro γ
    show (charCover χ hχ).p
        (charCoverMap χ hχ (fLift S c γ) * (charCover χ hχ).z ^ (ψ γ).val)
      = (qOfCocycle DD ρ σ hσ c).1 γ
    have hz1 : (charCover χ hχ).p (charCover χ hχ).z = 1 := by
      show (charCover χ hχ).p (charCoverMap χ hχ ((charWitness χ hχ : ↥D.T) : Bg)) = 1
      rw [← MonoidHom.comp_apply, charCover_p_comp, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact (charWitness χ hχ).2
    rw [map_mul, map_pow, hz1, one_pow, mul_one, ← MonoidHom.comp_apply, charCover_p_comp]
    exact fLift_mk S hσ c γ

end CharCover

/-! ## L5 descent at the `T`-stage: a relator-free covering marking of `B` descends from `Γ_A`

The `T`-stage mirror of `RStageGammaA.lift_of_relatorFree_marking`, with one new twist: the
covered map `g_Q : Γ_A → B/T` is **not surjective** (its image is the graph-like subgroup of a
`V`-cocycle), so `Marking.push_admissible` does not apply directly.  The fix is a
**corestriction through the classified hom**: the four `B/T`-generator images generate a
subgroup `J̄`, the `F₄`-hom classified by the `J̄`-marking kills `N_A` (compare with
`g_Q ∘ quotientMk` through `toHom_hom_univMarking_map` and transfer the kernel through the
injective subtype), so it descends to a **surjective** `ḡ : Γ_A ↠ J̄` — whose pushed marking
is admissible, feeding the `Pro2Core` chase. -/

section DescendT

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- **The `T`-stage descent** (`hsep_A` L5): a marking of `B` that covers `g_Q`'s marking
through `π_T` and kills both relators descends to a continuous `f : Γ_A → B` with
`π_T ∘ f = g_Q`. -/
theorem mlift_of_relatorFree_marking
    (gQ : ContinuousMonoidHom GA (Bg ⧸ D.T))
    (tHat : Marking Bg)
    (hproj : tHat.map (QuotientGroup.mk' D.T) = Marking.push gQ)
    (htame : tHat.TameRel) (hwild : tHat.WildRel) :
    ∃ f : ContinuousMonoidHom GammaA Bg,
      ∀ γ, QuotientGroup.mk' D.T (f γ) = gQ γ := by
  classical
  have htelem : ∀ t ∈ D.T, t * t = 1 := fun t ht => D.helem t (D.hTM ht)
  -- §1: the generated subgroup of `B` and its marking
  set J : Subgroup Bg := Subgroup.closure {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} with hJ
  have hmemσ : tHat.σ ∈ J := Subgroup.subset_closure (by simp)
  have hmemτ : tHat.τ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₀ : tHat.x₀ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₁ : tHat.x₁ ∈ J := Subgroup.subset_closure (by simp)
  set tJ : Marking ↥J :=
    ⟨⟨tHat.σ, hmemσ⟩, ⟨tHat.τ, hmemτ⟩, ⟨tHat.x₀, hmemx₀⟩, ⟨tHat.x₁, hmemx₁⟩⟩ with htJ
  have hmapJ : tJ.map J.subtype = tHat := by
    refine marking_ext ?_ ?_ ?_ ?_ <;> rfl
  have htameJ : tJ.TameRel := by
    rw [← Marking.tameValue_eq_one_iff]
    have h := Marking.map_tameValue J.subtype tJ
    rw [hmapJ, (Marking.tameValue_eq_one_iff tHat).mpr htame] at h
    exact Subtype.val_injective h.symm
  have hwildJ : tJ.WildRel := by
    rw [← Marking.wildValue_eq_one_iff]
    have h := Marking.map_wildValue J.subtype tJ
    rw [hmapJ, (Marking.wildValue_eq_one_iff tHat).mpr hwild] at h
    exact Subtype.val_injective h.symm
  have hgenJ : tJ.Generates := by
    show Subgroup.closure {tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} = ⊤
    have hpre : ({tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} : Set ↥J)
        = ((↑) : ↥J → Bg) ⁻¹' {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} := by
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> simp [htJ]
      · rintro (h | h | h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
    rw [hpre]
    exact Subgroup.closure_closure_coe_preimage
  -- §2: the corestriction `ḡ : Γ_A ↠ J̄ = ⟨g_Q-generator images⟩ ≤ B/T`
  set Jbar : Subgroup (Bg ⧸ D.T) := Subgroup.closure
    {(Marking.push gQ).σ, (Marking.push gQ).τ, (Marking.push gQ).x₀, (Marking.push gQ).x₁}
    with hJbar
  have hmemσ' : (Marking.push gQ).σ ∈ Jbar := Subgroup.subset_closure (by simp)
  have hmemτ' : (Marking.push gQ).τ ∈ Jbar := Subgroup.subset_closure (by simp)
  have hmemx₀' : (Marking.push gQ).x₀ ∈ Jbar := Subgroup.subset_closure (by simp)
  have hmemx₁' : (Marking.push gQ).x₁ ∈ Jbar := Subgroup.subset_closure (by simp)
  set tbar : Marking ↥Jbar :=
    ⟨⟨(Marking.push gQ).σ, hmemσ'⟩, ⟨(Marking.push gQ).τ, hmemτ'⟩,
      ⟨(Marking.push gQ).x₀, hmemx₀'⟩, ⟨(Marking.push gQ).x₁, hmemx₁'⟩⟩ with htbar
  have hclassbar : univMarking.map (Marking.classify tbar).toMonoidHom = tbar :=
    univMarking_map_toHom (P := ProfiniteGrp.of ↥Jbar) tbar
  -- the classified hom, compared with `g_Q ∘ quotientMk` through the subtype
  set cbar : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Bg ⧸ D.T) :=
    (⟨Jbar.subtype, continuous_subtype_val⟩ :
        ContinuousMonoidHom ↥Jbar (Bg ⧸ D.T)).comp (Marking.classify tbar) with hcbar
  have hcomp : cbar = gQ.comp (quotientMk NA) := by
    have h1 := Marking.toHom_hom_univMarking_map cbar
    have h2 := Marking.toHom_hom_univMarking_map (gQ.comp (quotientMk NA))
    have hpushc : univMarking.map cbar.toMonoidHom
        = univMarking.map (gQ.comp (quotientMk NA)).toMonoidHom := by
      refine marking_ext ?_ ?_ ?_ ?_
      · exact congrArg (fun t : Marking ↥Jbar => (t.σ : Bg ⧸ D.T)) hclassbar
      · exact congrArg (fun t : Marking ↥Jbar => (t.τ : Bg ⧸ D.T)) hclassbar
      · exact congrArg (fun t : Marking ↥Jbar => (t.x₀ : Bg ⧸ D.T)) hclassbar
      · exact congrArg (fun t : Marking ↥Jbar => (t.x₁ : Bg ⧸ D.T)) hclassbar
    rw [← h1, ← h2, hpushc]
  have hker : NA ≤ (Marking.classify tbar).toMonoidHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine Subtype.val_injective ?_
    have h1 : (((Marking.classify tbar).toMonoidHom x : ↥Jbar) : Bg ⧸ D.T) = cbar x := rfl
    rw [h1, hcomp]
    show gQ (quotientMk NA x) = ((1 : ↥Jbar) : Bg ⧸ D.T)
    rw [(quotientMk_eq_one_iff NA).mpr hx, map_one]
    rfl
  set gbar : ContinuousMonoidHom GA ↥Jbar :=
    quotientLift NA (Marking.classify tbar) hker with hgbar
  have hgbar_val : ∀ γ : GA, (gbar γ : Bg ⧸ D.T) = gQ γ := by
    intro γ
    obtain ⟨w, rfl⟩ := quotientMk_surjective NA γ
    show (Marking.classify tbar w : Bg ⧸ D.T) = gQ (quotientMk NA w)
    rw [show (Marking.classify tbar w : Bg ⧸ D.T) = cbar w from rfl, hcomp]
    rfl
  -- `ḡ` hits the four generators, hence is surjective
  have hgbar_gen : ∀ i : Fin 4, gbar (quotientMk NA (FreeProfiniteGroup.of i)) =
      ![tbar.σ, tbar.τ, tbar.x₀, tbar.x₁] i := by
    intro i
    show Marking.classify tbar (FreeProfiniteGroup.of i) = _
    fin_cases i
    · exact congrArg Marking.σ hclassbar
    · exact congrArg Marking.τ hclassbar
    · exact congrArg Marking.x₀ hclassbar
    · exact congrArg Marking.x₁ hclassbar
  have hgenbar : Subgroup.closure ({tbar.σ, tbar.τ, tbar.x₀, tbar.x₁} : Set ↥Jbar) = ⊤ := by
    have hpre : ({tbar.σ, tbar.τ, tbar.x₀, tbar.x₁} : Set ↥Jbar)
        = ((↑) : ↥Jbar → Bg ⧸ D.T) ⁻¹'
          {(Marking.push gQ).σ, (Marking.push gQ).τ, (Marking.push gQ).x₀,
            (Marking.push gQ).x₁} := by
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> simp [htbar]
      · rintro (h | h | h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
    rw [hpre]
    exact Subgroup.closure_closure_coe_preimage
  have hgbar_surj : Function.Surjective ⇑gbar := by
    intro y
    have hy : y ∈ Subgroup.closure ({tbar.σ, tbar.τ, tbar.x₀, tbar.x₁} : Set ↥Jbar) := by
      rw [hgenbar]
      exact Subgroup.mem_top y
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | rfl | rfl | rfl)
      · exact ⟨quotientMk NA (FreeProfiniteGroup.of 0), hgbar_gen 0⟩
      · exact ⟨quotientMk NA (FreeProfiniteGroup.of 1), hgbar_gen 1⟩
      · exact ⟨quotientMk NA (FreeProfiniteGroup.of 2), hgbar_gen 2⟩
      · exact ⟨quotientMk NA (FreeProfiniteGroup.of 3), hgbar_gen 3⟩
    · exact ⟨1, map_one gbar⟩
    · rintro a b - - ⟨γ, rfl⟩ ⟨δ, rfl⟩
      exact ⟨γ * δ, map_mul gbar γ δ⟩
    · rintro a - ⟨γ, rfl⟩
      exact ⟨γ⁻¹, map_inv gbar γ⟩
  -- the pushed marking of `ḡ` is `tbar`, hence admissible
  have hpushbar : Marking.push gbar = tbar := by
    refine marking_ext ?_ ?_ ?_ ?_
    · exact hgbar_gen 0
    · exact hgbar_gen 1
    · exact hgbar_gen 2
    · exact hgbar_gen 3
  have hadmbar : tbar.Admissible := hpushbar ▸ Marking.push_admissible gbar hgbar_surj
  -- §3: the 2-core of `tJ`, through the corestricted comparison `qJ' : J → J̄`
  have hmapJc : J.map (QuotientGroup.mk' D.T)
      = Subgroup.closure
        ((QuotientGroup.mk' D.T) '' {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁}) := by
    rw [hJ, MonoidHom.map_closure]
  have hmemJbar : ∀ j : ↥J, QuotientGroup.mk' D.T (j : Bg) ∈ Jbar := by
    intro j
    have himg : QuotientGroup.mk' D.T (j : Bg)
        ∈ J.map (QuotientGroup.mk' D.T) := Subgroup.mem_map_of_mem _ j.2
    rw [hmapJc] at himg
    refine Subgroup.closure_mono ?_ himg
    rintro x ⟨y, (rfl | rfl | rfl | rfl), rfl⟩
    · exact Or.inl (congrArg Marking.σ hproj)
    · exact Or.inr (Or.inl (congrArg Marking.τ hproj))
    · exact Or.inr (Or.inr (Or.inl (congrArg Marking.x₀ hproj)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Marking.x₁ hproj)))
  set qJ' : ↥J →* ↥Jbar :=
    ((QuotientGroup.mk' D.T).comp J.subtype).codRestrict Jbar (fun j => hmemJbar j) with hqJ'
  have hcoreJ : tJ.Pro2Core := by
    show IsPGroup 2 (Subgroup.normalClosure {tJ.x₀, tJ.x₁})
    haveI hNB : (Subgroup.normalClosure {tbar.x₀, tbar.x₁}).Normal :=
      Subgroup.normalClosure_normal
    haveI hNBc : ((Subgroup.normalClosure {tbar.x₀, tbar.x₁}).comap qJ').Normal :=
      hNB.comap qJ'
    have hcomap : ({tJ.x₀, tJ.x₁} : Set ↥J) ⊆
        ((Subgroup.normalClosure {tbar.x₀, tbar.x₁}).comap qJ' : Set ↥J) := by
      rintro z hz
      rcases hz with rfl | hz
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        have h1 : qJ' tJ.x₀ = tbar.x₀ := Subtype.ext (congrArg Marking.x₀ hproj)
        rw [h1]
        exact Subgroup.subset_normalClosure (by simp)
      · rcases hz with rfl
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        have h1 : qJ' tJ.x₁ = tbar.x₁ := Subtype.ext (congrArg Marking.x₁ hproj)
        rw [h1]
        exact Subgroup.subset_normalClosure (by simp)
    have hle := Subgroup.normalClosure_le_normal hcomap
    intro n
    have hmemNB : qJ' n.1 ∈ Subgroup.normalClosure {tbar.x₀, tbar.x₁} :=
      Subgroup.mem_comap.mp (hle n.2)
    obtain ⟨k, hk⟩ := hadmbar.2.2.2 ⟨qJ' n.1, hmemNB⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (qJ' n.1) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hkQ : QuotientGroup.mk' D.T (((n.1 : ↥J) : Bg)) ^ 2 ^ k = 1 := by
      have h2 : ((qJ' n.1 : ↥Jbar) : Bg ⧸ D.T) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk'
      exact h2
    have hmemT : ((n.1 : ↥J) : Bg) ^ 2 ^ k ∈ D.T := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
      exact hkQ
    have hBgval : ((n.1 : ↥J) : Bg) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul, pow_two]
      exact htelem _ hmemT
    exact Subtype.val_injective (by
      simpa using Subtype.val_injective (by simpa using hBgval :
        ((n.1 ^ 2 ^ (k + 1) : ↥J) : Bg) = ((1 : ↥J) : Bg)))
  have hadmJ : tJ.Admissible := ⟨hgenJ, htameJ, hwildJ, hcoreJ⟩
  -- §4: descend and compare
  set fJ : ContinuousMonoidHom ↥J Bg := ⟨J.subtype, continuous_subtype_val⟩ with hfJ
  refine ⟨fJ.comp (Marking.descend tJ hadmJ), ?_⟩
  intro γ
  obtain ⟨w, rfl⟩ := quotientMk_surjective NA γ
  set c₁ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Bg ⧸ D.T) :=
    (⟨QuotientGroup.mk' D.T, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom Bg (Bg ⧸ D.T)).comp (fJ.comp (Marking.classify tJ)) with hc₁
  set c₂ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Bg ⧸ D.T) :=
    gQ.comp (quotientMk NA) with hc₂
  have hclassify : univMarking.map (Marking.classify tJ).toMonoidHom = tJ :=
    univMarking_map_toHom (P := ProfiniteGrp.of ↥J) tJ
  have hpush : univMarking.map c₁.toMonoidHom = univMarking.map c₂.toMonoidHom := by
    refine marking_ext ?_ ?_ ?_ ?_
    · have h1 : (Marking.classify tJ) univMarking.σ = tJ.σ := congrArg Marking.σ hclassify
      show QuotientGroup.mk' D.T (fJ ((Marking.classify tJ) univMarking.σ))
        = gQ (quotientMk NA univMarking.σ)
      rw [h1]
      exact congrArg Marking.σ hproj
    · have h1 : (Marking.classify tJ) univMarking.τ = tJ.τ := congrArg Marking.τ hclassify
      show QuotientGroup.mk' D.T (fJ ((Marking.classify tJ) univMarking.τ))
        = gQ (quotientMk NA univMarking.τ)
      rw [h1]
      exact congrArg Marking.τ hproj
    · have h1 : (Marking.classify tJ) univMarking.x₀ = tJ.x₀ := congrArg Marking.x₀ hclassify
      show QuotientGroup.mk' D.T (fJ ((Marking.classify tJ) univMarking.x₀))
        = gQ (quotientMk NA univMarking.x₀)
      rw [h1]
      exact congrArg Marking.x₀ hproj
    · have h1 : (Marking.classify tJ) univMarking.x₁ = tJ.x₁ := congrArg Marking.x₁ hclassify
      show QuotientGroup.mk' D.T (fJ ((Marking.classify tJ) univMarking.x₁))
        = gQ (quotientMk NA univMarking.x₁)
      rw [h1]
      exact congrArg Marking.x₁ hproj
  have hc : c₁ = c₂ := by
    have h1 := Marking.toHom_hom_univMarking_map c₁
    have h2 := Marking.toHom_hom_univMarking_map c₂
    rw [← h1, ← h2, hpush]
  exact DFunLike.congr_fun hc w

end DescendT

/-! ## `hsep` for `Γ_A`: the `(T^∨)^C`-separation via the marking route -/

section HsepGammaA

variable (Dsc : Descent (En.radData l h))

/-- **`hsep` for `Γ_A`** — the `(T^∨)^C`-separation at the candidate source: a `V`-coordinate
whose `χ`-obstructions all vanish is `T`-liftable.  The `Γ_A` twin of
`Phase140Local.hsep_local`, by the **marking route** (the local `prop_5_16` `cup20` route has
no `Γ_A` analog): each nonzero invariant character's vanishing obstruction produces a lift
through its `𝔽₂`-cover (`exists_lift_charCover`), which forces `χ`-agreement of the relator
values of a set-lift marking (`redValues_eq_of_coverLift`); `sep_word` (the `prop_5_15`
trace-span) converts total agreement into word-level corrections; the corrected marking kills
both relators (`corrected_tameValue`/`corrected_wildValue` + `T`-elementarity) and descends
(`mlift_of_relatorFree_marking`) to the direct `M`-lift. -/
theorem hsep_gammaA
    (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (hc : ∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) :
    TLiftable (descSigma_spec En l h Dsc) c := by
  classical
  haveI : (En.radData l h).M.Normal := (En.radData l h).hM
  haveI : DiscreteTopology (RF.YB ⧸ (En.radData l h).M) :=
    discreteTopology_quotient (En.radData l h)
  have hσ := descSigma_spec En l h Dsc
  have hρ's : Function.Surjective ⇑(RF.rhoPrime b F (En.radData l h) rfl ρ) :=
    rhoPrime_surjective RF b F (En.radData l h) rfl ρ
  have htelem : ∀ t ∈ (En.radData l h).T, t * t = 1 :=
    fun t ht => (En.radData l h).helem t ((En.radData l h).hTM ht)
  have hA₂ : ∀ a : Additive ↥(En.radData l h).T, a + a = 0 := fun a =>
    Additive.toMul.injective (Subtype.ext (htelem _ (Additive.toMul a).2))
  have hgQ_over : ∀ γ : GA, piQbar (En.descData l h)
      ((qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
        (descSigma En l h Dsc) hσ c).1 γ)
      = rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ :=
    fun γ => (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSigma En l h Dsc) hσ c).2 γ
  -- §1: a set-lift marking of `g_Q` through `π_T`
  obtain ⟨yσ, hyσ⟩ := QuotientGroup.mk'_surjective (En.radData l h).T
    ((Marking.push (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSigma En l h Dsc) hσ c).1).σ)
  obtain ⟨yτ, hyτ⟩ := QuotientGroup.mk'_surjective (En.radData l h).T
    ((Marking.push (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSigma En l h Dsc) hσ c).1).τ)
  obtain ⟨yx₀, hyx₀⟩ := QuotientGroup.mk'_surjective (En.radData l h).T
    ((Marking.push (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSigma En l h Dsc) hσ c).1).x₀)
  obtain ⟨yx₁, hyx₁⟩ := QuotientGroup.mk'_surjective (En.radData l h).T
    ((Marking.push (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSigma En l h Dsc) hσ c).1).x₁)
  set tB : Marking RF.YB := ⟨yσ, yτ, yx₀, yx₁⟩ with htB
  have hproj : tB.map (QuotientGroup.mk' (En.radData l h).T)
      = Marking.push (qOfCocycle (En.descData l h)
        (RF.rhoPrime b F (En.radData l h) rfl ρ) (descSigma En l h Dsc) hσ c).1 :=
    marking_ext hyσ hyτ hyx₀ hyx₁
  -- §2: the relator values live in `T` (the relators die in `B/T` — `g_Q` is a hom)
  have hv₁mem : tB.tameValue ∈ (En.radData l h).T := by
    have hmt := Marking.map_tameValue (QuotientGroup.mk' (En.radData l h).T) tB
    rw [hproj, (Marking.tameValue_eq_one_iff _).mpr (push_tameRel _)] at hmt
    rw [← QuotientGroup.ker_mk' (En.radData l h).T, MonoidHom.mem_ker]
    exact hmt.symm
  have hv₂mem : tB.wildValue ∈ (En.radData l h).T := by
    have hmw := Marking.map_wildValue (QuotientGroup.mk' (En.radData l h).T) tB
    rw [hproj, (Marking.wildValue_eq_one_iff _).mpr (push_wildRel _)] at hmw
    rw [← QuotientGroup.ker_mk' (En.radData l h).T, MonoidHom.mem_ker]
    exact hmw.symm
  set v₁ : ↥(En.radData l h).T := ⟨tB.tameValue, hv₁mem⟩ with hv₁def
  set v₂ : ↥(En.radData l h).T := ⟨tB.wildValue, hv₂mem⟩ with hv₂def
  -- §3: the `C = B/M`-side word-complex package at `markC ρ'`
  have adm := markC_admissible (RF.rhoPrime b F (En.radData l h) rfl ρ) hρ's
  have hsd := GQ2.FoxH.prop_5_15 (markC (RF.rhoPrime b F (En.radData l h) rfl ρ))
    adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2
  -- the `liftC0`-injectivity chase: a `π_T`-lift datum determines the `B/M`-value
  have hliftC0_inj : Function.Injective (liftC0 (En.descData l h)) := by
    intro a a' haa'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a'
    rw [liftC0_mk, liftC0_mk] at haa'
    rw [QuotientGroup.eq]
    have hker : x⁻¹ * y ∈ (En.descData l h).piC0.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haa', inv_mul_cancel]
    rwa [(En.descData l h).hkerC0] at hker
  have hfield : ∀ (y : RF.YB) (γ : GA),
      QuotientGroup.mk' (En.radData l h).T y
        = (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) hσ c).1 γ →
      QuotientGroup.mk (y : RF.YB) = RF.rhoPrime b F (En.radData l h) rfl ρ γ := by
    intro y γ hy
    refine hliftC0_inj ?_
    have h1 : liftC0 (En.descData l h) (QuotientGroup.mk (y : RF.YB))
        = (En.descData l h).piC0 y := liftC0_mk (En.descData l h) y
    have h2 : (En.descData l h).piC0 y
        = piQbar (En.descData l h) (QuotientGroup.mk' (En.radData l h).T y) :=
      (piQbar_mk (En.descData l h) y).symm
    rw [h1, h2, hy]
    exact hgQ_over γ
  -- §4 (L4): every invariant character kills the relator-value sum
  have hv : ∀ lam : ElemDual (Additive ↥(En.radData l h).T),
      (d0 (A := ElemDual (Additive ↥(En.radData l h).T))
        (markC (RF.rhoPrime b F (En.radData l h) rfl ρ))) lam = 0 →
      lam (Additive.ofMul v₁ + Additive.ofMul v₂) = 0 := by
    intro lam hlam
    have hfixmem : lam ∈ fixedPts (RF.YB ⧸ (En.radData l h).M)
        (ElemDual (Additive ↥(En.radData l h).T)) := by
      have hmem : lam ∈ H0w (A := ElemDual (Additive ↥(En.radData l h).T))
          (markC (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
        AddMonoidHom.mem_ker.mpr hlam
      rw [← H0w_eq_fixedPts (markC (RF.rhoPrime b F (En.radData l h) rfl ρ)) adm.1]
      exact hmem
    -- the invariant character `χ_lam ∈ (T^∨)^C`
    have hYconj : ∀ (bb : RF.YB) (t : ↥(En.radData l h).T),
        lam (Additive.ofMul ⟨bb * (t : RF.YB) * bb⁻¹,
          (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩)
        = lam (Additive.ofMul t) := by
      intro bb t
      have hfix := hfixmem (QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M)
      have h1 := congrArg (fun mu : ElemDual (Additive ↥(En.radData l h).T) =>
        mu (Additive.ofMul ⟨bb * (t : RF.YB) * bb⁻¹,
          (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩)) hfix
      have h3 : (QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M)⁻¹
          • Additive.ofMul (⟨bb * (t : RF.YB) * bb⁻¹,
            (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩ : ↥(En.radData l h).T)
          = Additive.ofMul t := by
        apply Additive.toMul.injective
        rw [cActT_toMul]
        apply Subtype.ext
        rw [cactFun_eq (En.radData l h) ((QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M)⁻¹)
          (b := bb⁻¹) rfl]
        show bb⁻¹ * (bb * (t : RF.YB) * bb⁻¹) * bb⁻¹⁻¹ = (t : RF.YB)
        group
      have h2 : ((QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M) • lam)
          (Additive.ofMul ⟨bb * (t : RF.YB) * bb⁻¹,
            (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩)
          = lam (Additive.ofMul t) := by
        rw [ElemDual.smul_apply, h3]
      rw [h2] at h1
      exact h1.symm
    set chiLam : ↥(TCharC (En.radData l h)) := ⟨fun t => lam (Additive.ofMul t),
      ⟨fun t t' => by
        show lam (Additive.ofMul (t * t')) = lam (Additive.ofMul t) + lam (Additive.ofMul t')
        rw [show Additive.ofMul (t * t') = Additive.ofMul t + Additive.ofMul t' from rfl,
          map_add],
       fun bb t => hYconj bb t⟩⟩ with hchiLam
    rw [map_add]
    by_cases hz : chiLam = 0
    · have hlam0 : ∀ t : ↥(En.radData l h).T, lam (Additive.ofMul t) = 0 := by
        intro t
        have h0 := congrArg (fun ξ : ↥(TCharC (En.radData l h)) => ξ.1 t) hz
        simpa using h0
      rw [hlam0 v₁, hlam0 v₂, add_zero]
    · -- nonzero: the cover lift forces `χ`-agreement of the two relator values
      have hB2 : chiDef (descSections En l h Dsc) hσ chiLam c
          ∈ B2 GammaA (ZMod 2) :=
        iotaB_eq_zero_iff.mp (hc chiLam)
      obtain ⟨gc, hgc⟩ := exists_lift_charCover htriv_gammaA (descSections En l h Dsc) hσ
        chiLam hz c hB2
      have hkey := redValues_eq_of_coverLift (charCover chiLam hz)
        (QuotientGroup.mk' (En.radData l h).T) (charCoverMap chiLam hz)
        (charCover_p_comp chiLam hz)
        (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) hσ c).1 gc hgc tB hproj
      -- `v₁ v₂⁻¹ ∈ ker χ`
      have hmemK : ((v₁ * v₂⁻¹ : ↥(En.radData l h).T) : RF.YB) ∈ charKer chiLam := by
        have h1 : charCoverMap chiLam hz (((v₁ * v₂⁻¹ : ↥(En.radData l h).T) : RF.YB)) = 1 := by
          show charCoverMap chiLam hz (tB.tameValue * tB.wildValue⁻¹) = 1
          rw [map_mul, map_inv, hkey, mul_inv_cancel]
        have h2 : (((v₁ * v₂⁻¹ : ↥(En.radData l h).T) : RF.YB))
            ∈ (charCoverMap chiLam hz).ker := MonoidHom.mem_ker.mpr h1
        haveI : (charKer chiLam).Normal := charKer_normal chiLam
        rwa [show (charCoverMap chiLam hz).ker = charKer chiLam from
          QuotientGroup.ker_mk' (charKer chiLam)] at h2
      have hchival := (mem_charKer_iff chiLam (v₁ * v₂⁻¹)).mp hmemK
      rw [TCharC.map_mul chiLam, TCharC.map_inv chiLam] at hchival
      exact hchival
  -- §5: the separation delivers word-level corrections
  have hsep := sep_word (markC (RF.rhoPrime b F (En.radData l h) rfl ρ))
    adm.2.1 adm.2.2.1 adm.1 hsd hA₂ (Additive.ofMul v₁, Additive.ofMul v₂) hv
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hsep
  -- §6 (L5): the corrected marking kills both relators and still covers `g_Q`
  letI actYB : DistribMulAction RF.YB (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom (Additive ↥(En.radData l h).T)
      (QuotientGroup.mk' (En.radData l h).M)
  have hjmul : ∀ a b' : Additive ↥(En.radData l h).T,
      ((Additive.toMul (a + b') : ↥(En.radData l h).T) : RF.YB)
        = ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB)
          * ((Additive.toMul b' : ↥(En.radData l h).T) : RF.YB) :=
    fun _ _ => rfl
  have hjconj : ∀ (y : RF.YB) (a : Additive ↥(En.radData l h).T),
      ((Additive.toMul (y • a) : ↥(En.radData l h).T) : RF.YB)
        = y * ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB) * y⁻¹ := by
    intro y a
    have h1 : (y • a : Additive ↥(En.radData l h).T)
        = (QuotientGroup.mk' (En.radData l h).M y) • a := rfl
    rw [h1]
    have h2 := congrArg Subtype.val
      (cActT_toMul (En.radData l h) (QuotientGroup.mk' (En.radData l h).M y) a)
    rw [h2]
    exact cactFun_eq (En.radData l h) (QuotientGroup.mk' (En.radData l h).M y) rfl
      (Additive.toMul a)
  have hmarkC : markC (RF.rhoPrime b F (En.radData l h) rfl ρ)
      = tB.map (QuotientGroup.mk' (En.radData l h).M) := by
    refine marking_ext ?_ ?_ ?_ ?_
    · exact (hfield tB.σ gammaGen.σ (congrArg Marking.σ hproj)).symm
    · exact (hfield tB.τ gammaGen.τ (congrArg Marking.τ hproj)).symm
    · exact (hfield tB.x₀ gammaGen.x₀ (congrArg Marking.x₀ hproj)).symm
    · exact (hfield tB.x₁ gammaGen.x₁ (congrArg Marking.x₁ hproj)).symm
  have hbase : d1Fun (markC (RF.rhoPrime b F (En.radData l h) rfl ρ)) x = d1Fun tB x := by
    rw [hmarkC]
    exact d1Fun_base_change (QuotientGroup.mk' (En.radData l h).M) (fun _ _ => rfl) tB x
  have hd1 : d1Fun tB x = (Additive.ofMul v₁, Additive.ofMul v₂) := by
    rw [← hbase]
    exact hx
  set tHat : Marking RF.YB :=
    ⟨((Additive.toMul (x 0) : ↥(En.radData l h).T) : RF.YB) * tB.σ,
      ((Additive.toMul (x 1) : ↥(En.radData l h).T) : RF.YB) * tB.τ,
      ((Additive.toMul (x 2) : ↥(En.radData l h).T) : RF.YB) * tB.x₀,
      ((Additive.toMul (x 3) : ↥(En.radData l h).T) : RF.YB) * tB.x₁⟩ with htHat
  have htameHat : tHat.TameRel := by
    rw [← Marking.tameValue_eq_one_iff]
    rw [show tHat.tameValue
        = ((Additive.toMul ((d1Fun tB x).1) : ↥(En.radData l h).T) : RF.YB) * tB.tameValue from
      corrected_tameValue (fun a => ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB))
        hjmul hjconj tB x, hd1]
    show ((v₁ : RF.YB)) * tB.tameValue = 1
    exact htelem _ hv₁mem
  have hwildHat : tHat.WildRel := by
    rw [← Marking.wildValue_eq_one_iff]
    rw [show tHat.wildValue
        = ((Additive.toMul ((d1Fun tB x).2) : ↥(En.radData l h).T) : RF.YB) * tB.wildValue from
      corrected_wildValue (fun a => ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB))
        hjmul hjconj tB x, hd1]
    show ((v₂ : RF.YB)) * tB.wildValue = 1
    exact htelem _ hv₂mem
  have hprojHat : tHat.map (QuotientGroup.mk' (En.radData l h).T)
      = Marking.push (qOfCocycle (En.descData l h)
        (RF.rhoPrime b F (En.radData l h) rfl ρ) (descSigma En l h Dsc) hσ c).1 := by
    have hker : ∀ a : Additive ↥(En.radData l h).T,
        QuotientGroup.mk' (En.radData l h).T
          ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB) = 1 := by
      intro a
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (Additive.toMul a).2
    refine marking_ext ?_ ?_ ?_ ?_
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 0) : ↥(En.radData l h).T) : RF.YB) * tB.σ) = _
      rw [map_mul, hker, one_mul]
      exact hyσ
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 1) : ↥(En.radData l h).T) : RF.YB) * tB.τ) = _
      rw [map_mul, hker, one_mul]
      exact hyτ
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 2) : ↥(En.radData l h).T) : RF.YB) * tB.x₀) = _
      rw [map_mul, hker, one_mul]
      exact hyx₀
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 3) : ↥(En.radData l h).T) : RF.YB) * tB.x₁) = _
      rw [map_mul, hker, one_mul]
      exact hyx₁
  -- §7: descend and package as the `M`-lift
  obtain ⟨f₀, hf₀⟩ := mlift_of_relatorFree_marking
    (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSigma En l h Dsc) hσ c).1 tHat hprojHat htameHat hwildHat
  refine ⟨⟨f₀, fun γ => ?_⟩, ?_⟩
  · exact hfield (f₀ γ) γ (hf₀ γ)
  · refine Subtype.ext (DFunLike.ext _ _ fun γ => ?_)
    rw [redTLift_apply]
    exact hf₀ γ

end HsepGammaA

end Phase140GammaA

end GQ2
