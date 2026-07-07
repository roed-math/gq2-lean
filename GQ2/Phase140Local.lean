import GQ2.Phase140Assembly
import GQ2.Half139Local

/-!
# P-16d6e3: the local (140) residues for `G_ℚ₂`

Discharge, for the local source `Γ = G_ℚ₂ = AbsGalQ2`, the per-source residues consumed by the
source-generic `phase140_from_residues` (P-16d6e2, `GQ2/Phase140Assembly.lean`): `hsep`,
`hpartial`, `hZcard`, and `hμ` (the `T`-cocycle count).  `hGaussZ` is the deeper P-16d6e4 lane
(kept as a hypothesis here); `htriv`/`hH2` are discharged locally (`htriv_local'` /
`card_H2_zmod2_eq_two`).

**Status (Opus, 2026-07-07)**: the assembly `phase140_local` is VALIDATED end-to-end against
`phase140_from_residues` (`lake build` green).  **PROVED** (all std-3 + B6 + B7 where cohomological,
no sorryAx): `htriv_local'`, `vFixedPts_eq_one`, the two **counting** residues
**`tcocycle_card_local`** (the `hμ` supplier) and **`hZcard_local`**, AND — the deep separation
residue — **`hsep_local`** (all 7 stages: `Additive T` module → `tDef ∈ Z²` → dual/`hpair` →
`cup20`-bridge with the `χ↔n∈TCharC` invariance transport → `bijective_cup20` injectivity → B²-
extraction → the direct `M`-lift `f γ = ψγ·fLift γ`).  Remaining `sorry`: `hpartial_local` only
(the nondegeneracy residue; recipe in-file — couples to `hsep`'s stages 1–4 infrastructure).
**⚠ statement finding**: `hZcard_local` gained `hnt : ∃ g v, g•v≠v` (the ledger
`hsimple`/`hfaith`/`hVne` is insufficient — see `hZcard_local`), which the capstone ledger must add.

The four residues follow two worked patterns already landed for the local source:

* the **counting** residues `hμ` and `hZcard` mirror `hMcountM_local`
  (`GQ2/Half139Local.lean`): build the additive `𝔽₂`-module of the layer (`T` resp. `V`) with
  the `ρ'`-conjugation `AbsGalQ2`-action, bridge the crossed cocycles to `Z¹_cont`, apply
  `card_Z1_eq` (5.16 clause (ii), B7), and evaluate the `fixedPts` factor;
* the **separation** residues `hsep` and `hpartial` mirror `hsep_hom_local`
  (`GQ2/RStageLocal.lean`): the `(T^∨)^C`-perfectness of the `T`-obstruction pairing from
  `prop_5_16` cup clauses (vi)/(iv)/(v) + a `B²`-extraction.

All four are `∀ ρ`-parametric over the `C`-boundary lifts, in exactly the shape
`phase140_from_residues` consumes; the assembly `phase140_local` wires them (plus the ledger
`hGaussZ`) into the `RecursionInputs.phase140`-field display.

Axioms (audit at close): `⊆ {B6, B7}` — B6/B7 via `card_Z1_eq` / `card_H2_eq_fixedPts`, exactly
as in `hMcountM_local`/`hZcount_local`.
-/

namespace GQ2

namespace SectionEight

open CentralObstruction AffineTLift ContCoh LocalLiftingDuality FoxH QuadraticFp2

/-- The `G_ℚ₂`-action on `𝔽₂` is trivial (any group action on `ZMod 2` fixes both elements).
A self-contained copy of `RStageLocal.htriv_local`, inlined to keep this leaf's imports lean. -/
theorem htriv_local' [DistribMulAction AbsGalQ2 (ZMod 2)] (γ : AbsGalQ2) (m : ZMod 2) :
    γ • m = m := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz m with rfl | rfl
  · exact smul_zero γ
  · by_contra hne
    have h1 : γ • (1 : ZMod 2) = 0 := by
      rcases hz (γ • (1 : ZMod 2)) with h | h
      · exact h
      · exact absurd h hne
    have h2 : (1 : ZMod 2) = γ⁻¹ • (0 : ZMod 2) := by rw [← h1, inv_smul_smul]
    rw [smul_zero] at h2
    exact one_ne_zero h2

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  {RF : RecursionFrame T Blk}

section LocalResidues

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
  [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
variable (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l h))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
  [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)] in
/-- Conjugation of `T`-elements only depends on the `M`-coset of the conjugator (`M` abelian
centralizes `T ≤ M`).  Inlined `T`-analogue of `RadicalEdgeLocal.conj_eq_of_mk_eq`. -/
private theorem conj_eq_of_mk_eq_T {Bg : Type} [Group Bg] [Finite Bg] {D : RadicalCoverData Bg}
    {b b' : Bg} (hh : (QuotientGroup.mk b : Bg ⧸ D.M) = QuotientGroup.mk b') (t : ↥D.T) :
    b * t.1 * b⁻¹ = b' * t.1 * b'⁻¹ := by
  have hm : b⁻¹ * b' ∈ D.M := (QuotientGroup.eq (s := D.M)).mp hh
  have hcomm := D.hcomm _ hm _ (D.hTM t.2)
  calc b * t.1 * b⁻¹
      = b * (t.1 * (b⁻¹ * b') * (b⁻¹ * b')⁻¹) * b⁻¹ := by group
    _ = b * ((b⁻¹ * b') * t.1 * (b⁻¹ * b')⁻¹) * b⁻¹ := by rw [← hcomm]
    _ = b' * t.1 * b'⁻¹ := by group

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [DistribMulAction AbsGalQ2 (ZMod 2)]
  [ContinuousSMul AbsGalQ2 (ZMod 2)] in
/-- **The `T`-cocycle count for `G_ℚ₂`** (the `hμ` supplier, P-16d6e3): the crossed-`T`-cocycle
count is the `card_Z1_eq` closed form `#T² · #(T^∨)^{YB/M_B}`, which is **`ρ`-independent** (the RHS
sees only the frame-level datum `En.radData l h`, not `ρ`) — so the capstone reads off `μ₀` and
`hμ := fun ρ => tcocycle_card_local … ρ`.  Mirrors `hMcountM_local` steps 1–3 at
`A := Additive (En.radData l h).T`, but with a **direct** `TCocycle ≃ Z¹_cont` bridge (`TCocycle`
stores continuity into `Bg` directly, and is always nonempty — no torsor/`Nonempty` detour). -/
theorem tcocycle_card_local (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (Additive ↥(En.radData l h).T) ^ 2
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T))) := by
  classical
  have hρ's : Function.Surjective (RF.rhoPrime b F (En.radData l h) rfl ρ) :=
    rhoPrime_surjective RF b F (En.radData l h) rfl ρ
  -- `T = (En.radData l h).T` as an additive `𝔽₂`-space with the `ρ'`-conjugation action
  letI : CommGroup ↥(En.radData l h).T :=
    { (inferInstance : Group ↥(En.radData l h).T) with
      mul_comm := fun a b => Subtype.ext ((En.radData l h).hcomm _ ((En.radData l h).hTM a.2) _
        ((En.radData l h).hTM b.2)) }
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) :=
    (inferInstance : TopologicalSpace ↥(En.radData l h).T)
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) :=
    ⟨(inferInstance : DiscreteTopology ↥(En.radData l h).T).eq_bot⟩
  haveI : Finite (Additive ↥(En.radData l h).T) := (inferInstance : Finite ↥(En.radData l h).T)
  letI actC : DistribMulAction (RF.YB ⧸ (En.radData l h).M) (Additive ↥(En.radData l h).T) :=
    { smul := fun c t => Additive.ofMul
        ⟨Quotient.out c * (Additive.toMul t).1 * (Quotient.out c)⁻¹,
          (En.radData l h).hT.conj_mem _ (Additive.toMul t).2 _⟩
      one_smul := fun t => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (1 : RF.YB ⧸ (En.radData l h).M) * (Additive.toMul t).1
            * (Quotient.out (1 : RF.YB ⧸ (En.radData l h).M))⁻¹ = (Additive.toMul t).1
        have h1 : (Quotient.out (1 : RF.YB ⧸ (En.radData l h).M)) ∈ (En.radData l h).M := by
          have := QuotientGroup.out_eq' (1 : RF.YB ⧸ (En.radData l h).M)
          rwa [QuotientGroup.eq_one_iff] at this
        rw [(En.radData l h).hcomm _ h1 _ ((En.radData l h).hTM (Additive.toMul t).2)]; group
      mul_smul := fun c c' t => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (c * c') * (Additive.toMul t).1 * (Quotient.out (c * c'))⁻¹
          = Quotient.out c * (Quotient.out c' * (Additive.toMul t).1 * (Quotient.out c')⁻¹)
              * (Quotient.out c)⁻¹
        rw [show Quotient.out c * (Quotient.out c' * (Additive.toMul t).1 * (Quotient.out c')⁻¹)
              * (Quotient.out c)⁻¹
            = (Quotient.out c * Quotient.out c') * (Additive.toMul t).1
              * (Quotient.out c * Quotient.out c')⁻¹ from by group]
        exact conj_eq_of_mk_eq_T (by rw [QuotientGroup.out_eq', QuotientGroup.mk_mul,
          QuotientGroup.out_eq', QuotientGroup.out_eq']) (Additive.toMul t)
      smul_zero := fun c => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out c * (1 : RF.YB) * (Quotient.out c)⁻¹ = 1
        group
      smul_add := fun c t t' => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out c * ((Additive.toMul t).1 * (Additive.toMul t').1) * (Quotient.out c)⁻¹
          = (Quotient.out c * (Additive.toMul t).1 * (Quotient.out c)⁻¹)
              * (Quotient.out c * (Additive.toMul t').1 * (Quotient.out c)⁻¹)
        group }
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom (Additive ↥(En.radData l h).T)
      (RF.rhoPrime b F (En.radData l h) rfl ρ).toMonoidHom
  have hcomp : ∀ (γ : AbsGalQ2) (a : Additive ↥(En.radData l h).T),
      γ • a = (RF.rhoPrime b F (En.radData l h) rfl ρ) γ • a := fun _ _ => rfl
  -- the action at a representative `b` of `ρ'(γ)`
  have hsmul : ∀ (γ : AbsGalQ2) (bb : RF.YB) (a : Additive ↥(En.radData l h).T),
      QuotientGroup.mk bb = RF.rhoPrime b F (En.radData l h) rfl ρ γ →
      γ • a = Additive.ofMul (⟨bb * (Additive.toMul a).1 * bb⁻¹,
        (En.radData l h).hT.conj_mem _ (Additive.toMul a).2 _⟩ : ↥(En.radData l h).T) := by
    intro γ bb a hbb
    apply Additive.toMul.injective; apply Subtype.ext
    show Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ) * (Additive.toMul a).1
        * (Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ))⁻¹
      = bb * (Additive.toMul a).1 * bb⁻¹
    exact conj_eq_of_mk_eq_T (by rw [QuotientGroup.out_eq', hbb]) (Additive.toMul a)
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥(En.radData l h).T) := by
    constructor
    have hfac : (fun p : AbsGalQ2 × Additive ↥(En.radData l h).T => p.1 • p.2)
        = (fun cq : (RF.YB ⧸ (En.radData l h).M) × ↥(En.radData l h).T =>
            Additive.ofMul (⟨Quotient.out cq.1 * cq.2.1 * (Quotient.out cq.1)⁻¹,
              (En.radData l h).hT.conj_mem _ cq.2.2 _⟩ : ↥(En.radData l h).T))
          ∘ (fun p : AbsGalQ2 × Additive ↥(En.radData l h).T =>
              ((RF.rhoPrime b F (En.radData l h) rfl ρ p.1 : RF.YB ⧸ (En.radData l h).M),
                Additive.toMul p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      (((RF.rhoPrime b F (En.radData l h) rfl ρ).continuous_toFun.comp continuous_fst).prodMk
        continuous_snd)
  have hA₂ : ∀ a : Additive ↥(En.radData l h).T, a + a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) * (Additive.toMul a) = 1
    exact Subtype.ext ((En.radData l h).helem _ ((En.radData l h).hTM (Additive.toMul a).2))
  -- the direct `TCocycle ≃ Z¹_cont(AbsGalQ2, Additive T)` bridge
  have hequiv : TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      ≃ ↥(Z1 AbsGalQ2 (Additive ↥(En.radData l h).T)) :=
    { toFun := fun u =>
        ⟨fun γ => Additive.ofMul ⟨u.u γ, u.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun γ => (⟨u.u γ, u.mem γ⟩ : ↥(En.radData l h).T)
            exact Continuous.subtype_mk u.cont _
          · intro γ δ
            rw [hsmul γ (Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ))
                (Additive.ofMul ⟨u.u δ, u.mem δ⟩) (QuotientGroup.out_eq' _)]
            apply Additive.toMul.injective
            apply Subtype.ext
            show u.u (γ * δ)
              = u.u γ * (Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ) * u.u δ
                  * (Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ))⁻¹)
            exact u.crossed γ δ (Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ))
              (QuotientGroup.out_eq' _)⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥(En.radData l h).T)).1
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := by
            have hz := (mem_Z1_iff.mp z.2).1
            exact continuous_subtype_val.comp hz
          crossed := by
            intro γ δ bb hbb
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ bb (z.1 δ) hbb] at hz
            have := congrArg (fun a => ((Additive.toMul a : ↥(En.radData l h).T)).1) hz
            simpa using this }
      left_inv := fun u => by cases u; rfl
      right_inv := fun z => Subtype.ext (funext fun γ => rfl) }
  exact (Nat.card_congr hequiv).trans (card_Z1_eq hρ's hcomp hA₂)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
  [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)] in
/-- **No `YC`-invariant functionals on `V`**: `#(V^∨)^{YC} = 1` — the `fixedPts` factor of the
`hZcard` `card_Z1_eq` count.  From `DualityAssembly.card_fixedPts_elemDual_eq_one_of_nontrivial`,
packaging the ledger `hsimple`/`hVne` as `IsSimpleModTwo RF.YC En.Vmod` and the nontrivial action
`hnt`.  (Self-contained; no cocycle bridge needed — the crux of `hZcard_local`.) -/
theorem vFixedPts_eq_one
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) :
    Nat.card (fixedPts RF.YC (ElemDual En.Vmod)) = 1 := by
  obtain ⟨v, hv⟩ := hVne
  have hsimpleMod : IsSimpleModTwo RF.YC En.Vmod :=
    ⟨nontrivial_of_ne (0 : En.Vmod) v (Ne.symm hv),
      fun W hW => hsimple W (fun g w hw => hW g w hw)⟩
  exact card_fixedPts_elemDual_eq_one_of_nontrivial hsimpleMod hnt

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [DistribMulAction AbsGalQ2 (ZMod 2)]
  [ContinuousSMul AbsGalQ2 (ZMod 2)] in
/-- **`hZcard` for `G_ℚ₂`** — `#Z¹_{Γ,ρ'}(V) = #V²`.  Mirrors `hMcountM_local` at `A := En.Vmod`
(which already carries the `RF.YC`-action of the enrichment) with the descent lower map
`rho0 = ρ.1.1` (`rho0_descData_rhoPrime`, surjective since `ρ` is a `ContSurj`), building the
`VCocycle ≃ Z¹_cont(AbsGalQ2, En.Vmod)` bridge and applying `card_Z1_eq`
(5.16 clause (ii)) to get `#V² · #fixedPts RF.YC (ElemDual En.Vmod)`; the `fixedPts` factor is `1`
by **`vFixedPts_eq_one` (PROVED above)**.  Only the bridge + module-instance setup remain (the
`hMcountM_local` steps 1–3 pattern at `A := En.Vmod`).

**⚠ statement amendment (P-16d6e3, `docs/section10`-style finding)**: `hnt` (the nontrivial action)
is REQUIRED and is NOT derivable from `hsimple`/`hfaith`/`hVne` alone — in the corner `#V = 2 ∧
YC = 1` the ledger is satisfiable (`𝔽₂` is a faithful — vacuously — simple `𝔽₂[1]`-module) yet
`#(V^∨)^{YC} = 2 ≠ 1`, so `hZcard` is FALSE there.  `hnt` (equivalently `Nontrivial RF.YC`, via
`hfaith`) rules it out and is discharged at the capstone from the block's chief-factor structure
(the ramified regular summand has a nontrivial `YC`-action).  The capstone ledger must add it.
(`hfaith` is then no longer needed *here* — `hnt` subsumes it — but is kept in `phase140_local`'s
signature as part of the ledger, where the capstone uses it to produce `hnt`.) -/
theorem hZcard_local
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card En.Vmod * Nat.card En.Vmod := by
  classical
  -- the descent lower map `rho0 = ρ.1.1 : Γ ↠ RF.YC` (surjective since `ρ` is a `ContSurj`)
  have hroundtrip : ∀ γ : AbsGalQ2,
      rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = ρ.1.1 γ :=
    rho0_descData_rhoPrime b F En l h ρ
  -- `En.Vmod` (with its `RF.YC`-action) as a `Z¹`-module through `ρ.1.1`; `card_Z1_eq` needs the
  -- acting group to carry a topology, so it is `RF.YC` (not the topology-free `(descData).C0`).
  letI : TopologicalSpace En.Vmod := ⊥
  haveI : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI actG : DistribMulAction AbsGalQ2 En.Vmod :=
    DistribMulAction.compHom En.Vmod (ρ.1.1).toMonoidHom
  have hcomp : ∀ (γ : AbsGalQ2) (v : En.Vmod), γ • v = ρ.1.1 γ • v := fun _ _ => rfl
  haveI : ContinuousSMul AbsGalQ2 En.Vmod := by
    constructor
    have hfac : (fun p : AbsGalQ2 × En.Vmod => p.1 • p.2)
        = (fun q : RF.YC × En.Vmod => q.1 • q.2) ∘ (fun p : AbsGalQ2 × En.Vmod => (ρ.1.1 p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ v : En.Vmod, v + v = 0 := fun v => Vmod_exp2 (En.descData l h) v
  -- the `VCocycle ≃ Z¹_cont(AbsGalQ2, En.Vmod)` bridge (continuity through `iV∘ofAdd`, an injection
  -- between discrete spaces, via `IsLocallyConstant.desc`; `iV`-domains annotated `En.Vmod` so the
  -- discreteness resolves against the outer instance, not the search-opaque `(descData).Vmod`)
  have hequiv : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      ≃ ↥(Z1 AbsGalQ2 En.Vmod) :=
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
  rw [Nat.card_congr hequiv, card_Z1_eq ρ.1.2 hcomp hA₂,
    vFixedPts_eq_one En hsimple hVne hnt, mul_one, pow_two]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 1600000 in
/-- **`hsep` for `G_ℚ₂`** — the `(T^∨)^C`-separation: a `V`-coordinate with all `χ`-obstructions
`betaChi χ c = 0` is `T`-liftable.  The converse of the generic `betaChi_of_tliftable`
(`VLiftCount.lean`); the `hsep_hom_local` pattern (`prop_5_16` cup clause (vi) `cup20`-bijectivity
+ `B²`-extraction) at the `T`-module through the `M`-lift obstruction.

**EXECUTABLE RECIPE (7 stages, mirroring `RStageLocal.hsep_hom_local` at the T-layer; all lemma
names verified to exist):**
1. **Module.**  `A := Additive ↥(En.radData l h).T` with the `rhoPrime`-conjugation
   `AbsGalQ2`-action — REUSE `tcocycle_card_local`'s setup verbatim (`conj_eq_of_mk_eq_T`,
   `tCommGroup`, `actC`/`actG`, `hcomp`, `hsmul`, `ContinuousSMul`, `hA₂`), same module as the
   T-count.  **✅ LANDED in-proof below** (the `sorry` is only for Stages 2–7).
2. **T-valued defect cocycle** `tDefZ2 : (fun p => Additive.ofMul (tDef S hσ c p)) ∈ Z2 AbsGalQ2 A`
   — extract from `chiDef_mem_Z2`'s `hraw`/`hsub` (`VLiftCount.lean:234-252`), BEFORE pushing
   through `χ`; the `γ•` in the `Z2` identity is conjugation by `fLift γ` (a rep of `ρ'γ`, so
   `= actG`-action by `conj_eq_of_mk_eq_T`).
3. **Dual module** `ElemDual A` + `hpair` — copy `hsep_hom_local:466-486` (`compHom θ`, `⊥`
   topology, `hpair` via `htriv_local'` + `ElemDual.smul_apply` + `inv_smul_smul`).
4. **`cup20`-values vanish** `∀ n : H0 AbsGalQ2 (ElemDual A), cup20 (dualEval A) hpair (H2mk … ⟨_,tDefZ2⟩) n = 0`:
   `cup20 [tDef] n = H2mk (fun gd => dualEval (tDef gd) ((gd.1*gd.2)•n))` (congrArg H2mk, as in
   `hsep_hom_local:hred`); `n.2`-invariance ⟹ `= H2mk (fun gd => n(tDef gd)) = H2mk (chiDef χ_n c)`
   where `χ_n : ↥(TCharC D) := ⟨fun t => n.1 (Additive.ofMul t), ⟨additivity, conj-inv via θ-surj⟩⟩`
   (the `hYinv` transport, `hsep_hom_local:493-512`); then `hc χ_n : betaChi χ_n c = 0` gives
   `chiDef χ_n c ∈ B²` (`iotaB_eq_zero_iff`), so `H2mk (chiDef χ_n c) = 0` (`H2mk_eq_zero_iff`).
5. **Class vanishes** `H2mk … ⟨_,tDefZ2⟩ = 0` via `(bijective_cup20_dualEval hA₂ htriv_local' hpair).1`
   (injectivity) + `map_zero` + `AddMonoidHom.ext` over stage 4.
6. **B²-extraction**: `(QuotientAddGroup.eq_zero_iff _).mp` + `mem_addSubgroupOf` ⟹
   `ψ : AbsGalQ2 → A` continuous with `dOne ψ = tDef` (`hsep_hom_local:541-543`).
7. **Direct lift** (the genuinely NEW part — no `homLift_of_split` for the abstract-`D` `MLifts`
   layer): `f γ := (Additive.toMul (ψ γ) : Bg) * fLift S c γ`; a continuous hom over `ρ'`
   (`dOne ψ = tDef` cancels the `fLift`-defect, exponent-2 kills the sign as in `:554-563`;
   `ψ ∈ T ⊆ M` so `mk_M (f γ) = mk_M (fLift γ) = ρ'γ`), and `mk_T (f γ) = mk_T (fLift γ) =
   (qOfCocycle c) γ` (since `ψ ∈ T`) ⟹ `redTLift f = qOfCocycle c` ⟹ `TLiftable`.  Bespoke ~40 lines. -/
theorem hsep_local
    (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (hc : ∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) :
    TLiftable (descSigma_spec En l h Dsc) c := by
  classical
  haveI : (En.radData l h).M.Normal := (En.radData l h).hM
  letI : Inv (RF.YB ⧸ (En.radData l h).M) := inferInstance
  -- STAGE 1: `T = (En.radData l h).T` as an additive `𝔽₂`-space with the `ρ'`-conjugation action
  -- (identical to `tcocycle_card_local`'s module setup)
  letI : CommGroup ↥(En.radData l h).T :=
    { (inferInstance : Group ↥(En.radData l h).T) with
      mul_comm := fun a b => Subtype.ext ((En.radData l h).hcomm _ ((En.radData l h).hTM a.2) _
        ((En.radData l h).hTM b.2)) }
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) :=
    (inferInstance : TopologicalSpace ↥(En.radData l h).T)
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) :=
    ⟨(inferInstance : DiscreteTopology ↥(En.radData l h).T).eq_bot⟩
  haveI : Finite (Additive ↥(En.radData l h).T) := (inferInstance : Finite ↥(En.radData l h).T)
  letI actC : DistribMulAction (RF.YB ⧸ (En.radData l h).M) (Additive ↥(En.radData l h).T) :=
    { smul := fun cc t => Additive.ofMul
        ⟨Quotient.out cc * (Additive.toMul t).1 * (Quotient.out cc)⁻¹,
          (En.radData l h).hT.conj_mem _ (Additive.toMul t).2 _⟩
      one_smul := fun t => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (1 : RF.YB ⧸ (En.radData l h).M) * (Additive.toMul t).1
            * (Quotient.out (1 : RF.YB ⧸ (En.radData l h).M))⁻¹ = (Additive.toMul t).1
        have h1 : (Quotient.out (1 : RF.YB ⧸ (En.radData l h).M)) ∈ (En.radData l h).M := by
          have := QuotientGroup.out_eq' (1 : RF.YB ⧸ (En.radData l h).M)
          rwa [QuotientGroup.eq_one_iff] at this
        rw [(En.radData l h).hcomm _ h1 _ ((En.radData l h).hTM (Additive.toMul t).2)]; group
      mul_smul := fun cc cc' t => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out (cc * cc') * (Additive.toMul t).1 * (Quotient.out (cc * cc'))⁻¹
          = Quotient.out cc * (Quotient.out cc' * (Additive.toMul t).1 * (Quotient.out cc')⁻¹)
              * (Quotient.out cc)⁻¹
        rw [show Quotient.out cc * (Quotient.out cc' * (Additive.toMul t).1 * (Quotient.out cc')⁻¹)
              * (Quotient.out cc)⁻¹
            = (Quotient.out cc * Quotient.out cc') * (Additive.toMul t).1
              * (Quotient.out cc * Quotient.out cc')⁻¹ from by group]
        exact conj_eq_of_mk_eq_T (by rw [QuotientGroup.out_eq', QuotientGroup.mk_mul,
          QuotientGroup.out_eq', QuotientGroup.out_eq']) (Additive.toMul t)
      smul_zero := fun cc => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out cc * (1 : RF.YB) * (Quotient.out cc)⁻¹ = 1
        group
      smul_add := fun cc t t' => by
        apply Additive.toMul.injective; apply Subtype.ext
        show Quotient.out cc * ((Additive.toMul t).1 * (Additive.toMul t').1) * (Quotient.out cc)⁻¹
          = (Quotient.out cc * (Additive.toMul t).1 * (Quotient.out cc)⁻¹)
              * (Quotient.out cc * (Additive.toMul t').1 * (Quotient.out cc)⁻¹)
        group }
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom (Additive ↥(En.radData l h).T)
      (RF.rhoPrime b F (En.radData l h) rfl ρ).toMonoidHom
  have hcomp : ∀ (γ : AbsGalQ2) (a : Additive ↥(En.radData l h).T),
      γ • a = (RF.rhoPrime b F (En.radData l h) rfl ρ) γ • a := fun _ _ => rfl
  -- the action at a representative `bb` of `ρ'(γ)`
  have hsmul : ∀ (γ : AbsGalQ2) (bb : RF.YB) (a : Additive ↥(En.radData l h).T),
      QuotientGroup.mk bb = RF.rhoPrime b F (En.radData l h) rfl ρ γ →
      γ • a = Additive.ofMul (⟨bb * (Additive.toMul a).1 * bb⁻¹,
        (En.radData l h).hT.conj_mem _ (Additive.toMul a).2 _⟩ : ↥(En.radData l h).T) := by
    intro γ bb a hbb
    apply Additive.toMul.injective; apply Subtype.ext
    show Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ) * (Additive.toMul a).1
        * (Quotient.out (RF.rhoPrime b F (En.radData l h) rfl ρ γ))⁻¹
      = bb * (Additive.toMul a).1 * bb⁻¹
    exact conj_eq_of_mk_eq_T (by rw [QuotientGroup.out_eq', hbb]) (Additive.toMul a)
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥(En.radData l h).T) := by
    constructor
    have hfac : (fun p : AbsGalQ2 × Additive ↥(En.radData l h).T => p.1 • p.2)
        = (fun cq : (RF.YB ⧸ (En.radData l h).M) × ↥(En.radData l h).T =>
            Additive.ofMul (⟨Quotient.out cq.1 * cq.2.1 * (Quotient.out cq.1)⁻¹,
              (En.radData l h).hT.conj_mem _ cq.2.2 _⟩ : ↥(En.radData l h).T))
          ∘ (fun p : AbsGalQ2 × Additive ↥(En.radData l h).T =>
              ((RF.rhoPrime b F (En.radData l h) rfl ρ p.1 : RF.YB ⧸ (En.radData l h).M),
                Additive.toMul p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      (((RF.rhoPrime b F (En.radData l h) rfl ρ).continuous_toFun.comp continuous_fst).prodMk
        continuous_snd)
  have hA₂ : ∀ a : Additive ↥(En.radData l h).T, a + a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) * (Additive.toMul a) = 1
    exact Subtype.ext ((En.radData l h).helem _ ((En.radData l h).hTM (Additive.toMul a).2))
  -- STAGE 2a: `mk_M (fLift γ) = ρ'γ`  (`mV ∈ M` kills its coset; `uσ` is a `piC0`-section; `liftC0` inj)
  have hfLmk : ∀ γ : AbsGalQ2,
      (QuotientGroup.mk (fLift (descSections En l h Dsc) c γ) : RF.YB ⧸ (En.radData l h).M)
        = RF.rhoPrime b F (En.radData l h) rfl ρ γ := by
    have hinj : Function.Injective (liftC0 (En.descData l h)) := by
      intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H bx =>
        induction y using QuotientGroup.induction_on with
        | H by' =>
          rw [liftC0_mk, liftC0_mk] at hxy
          apply (QuotientGroup.eq (s := (En.radData l h).M)).mpr
          rw [← (En.descData l h).hkerC0, MonoidHom.mem_ker, map_mul, map_inv, hxy,
            inv_mul_cancel]
    intro γ
    apply hinj
    rw [liftC0_mk]
    show (En.descData l h).piC0 ((descSections En l h Dsc).mV (c.c γ)
          * (descSections En l h Dsc).uσ
              (rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ))
        = rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ
    rw [map_mul,
      MonoidHom.mem_ker.mp (show ((descSections En l h Dsc).mV (c.c γ) : RF.YB)
          ∈ (En.descData l h).piC0.ker by
        rw [(En.descData l h).hkerC0]; exact ((descSections En l h Dsc).mV (c.c γ)).2),
      one_mul, ← piQbar_mk (En.descData l h), (descSections En l h Dsc).piT_uσ,
      descSigma_spec En l h Dsc]
  -- STAGE 2b: the T-valued defect is a `Z²(Γ, Additive T)` cocycle
  have tDefZ2 : (fun p : AbsGalQ2 × AbsGalQ2 =>
      Additive.ofMul (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c p))
      ∈ Z2 AbsGalQ2 (Additive ↥(En.radData l h).T) := by
    refine mem_Z2_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_of_discreteTopology (f := Additive.ofMul)).comp
        (tDef_continuous (descSections En l h Dsc) (descSigma_spec En l h Dsc) c)
    · intro γ δ ε
      rw [hsmul γ (fLift (descSections En l h Dsc) c γ)
          (Additive.ofMul (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (δ, ε)))
          (hfLmk γ)]
      apply Additive.toMul.injective
      apply Subtype.ext
      show fLift (descSections En l h Dsc) c γ
            * (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (δ, ε) : RF.YB)
            * (fLift (descSections En l h Dsc) c γ)⁻¹
            * (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ * ε) : RF.YB)
          = (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ * δ, ε) : RF.YB)
            * (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ) : RF.YB)
      have hraw : (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ) : RF.YB)
            * (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ * δ, ε) : RF.YB)
          = fLift (descSections En l h Dsc) c γ
              * (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (δ, ε) : RF.YB)
              * (fLift (descSections En l h Dsc) c γ)⁻¹
              * (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ * ε) : RF.YB) := by
        show fLift (descSections En l h Dsc) c γ * fLift (descSections En l h Dsc) c δ
              * (fLift (descSections En l h Dsc) c (γ * δ))⁻¹
              * (fLift (descSections En l h Dsc) c (γ * δ) * fLift (descSections En l h Dsc) c ε
                  * (fLift (descSections En l h Dsc) c (γ * δ * ε))⁻¹)
            = fLift (descSections En l h Dsc) c γ
                * (fLift (descSections En l h Dsc) c δ * fLift (descSections En l h Dsc) c ε
                    * (fLift (descSections En l h Dsc) c (δ * ε))⁻¹)
                * (fLift (descSections En l h Dsc) c γ)⁻¹
              * (fLift (descSections En l h Dsc) c γ * fLift (descSections En l h Dsc) c (δ * ε)
                  * (fLift (descSections En l h Dsc) c (γ * (δ * ε)))⁻¹)
        rw [show γ * δ * ε = γ * (δ * ε) from mul_assoc γ δ ε]
        group
      rw [← hraw]
      exact (En.radData l h).hcomm _
        ((En.radData l h).hTM
          (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ)).2) _
        ((En.radData l h).hTM
          (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ * δ, ε)).2)
  -- STAGE 3: the dual module `ElemDual (Additive T)` with the pairing equivariance `hpair`
  letI actGD : DistribMulAction AbsGalQ2 (FoxH.ElemDual (Additive ↥(En.radData l h).T)) :=
    DistribMulAction.compHom _ (RF.rhoPrime b F (En.radData l h) rfl ρ).toMonoidHom
  letI : TopologicalSpace (FoxH.ElemDual (Additive ↥(En.radData l h).T)) := ⊥
  haveI : DiscreteTopology (FoxH.ElemDual (Additive ↥(En.radData l h).T)) := ⟨rfl⟩
  haveI : ContinuousSMul AbsGalQ2 (FoxH.ElemDual (Additive ↥(En.radData l h).T)) := by
    refine ⟨?_⟩
    have hfacD : (fun p : AbsGalQ2 × FoxH.ElemDual (Additive ↥(En.radData l h).T) => p.1 • p.2)
        = (fun q : (RF.YB ⧸ (En.radData l h).M) × FoxH.ElemDual (Additive ↥(En.radData l h).T) =>
            q.1 • q.2)
          ∘ (fun p => (RF.rhoPrime b F (En.radData l h) rfl ρ p.1, p.2)) := by
      funext p; rfl
    rw [hfacD]
    exact continuous_of_discreteTopology.comp
      (((RF.rhoPrime b F (En.radData l h) rfl ρ).continuous_toFun.comp continuous_fst).prodMk
        continuous_snd)
  have hpair : ∀ (γ : AbsGalQ2) (a : Additive ↥(En.radData l h).T)
      (lam : FoxH.ElemDual (Additive ↥(En.radData l h).T)),
      FoxH.dualEval _ (γ • a) (γ • lam) = γ • FoxH.dualEval _ a lam := by
    intro γ a lam
    rw [htriv_local' γ (FoxH.dualEval _ a lam)]
    show ((RF.rhoPrime b F (En.radData l h) rfl ρ γ) • lam)
        ((RF.rhoPrime b F (En.radData l h) rfl ρ γ) • a) = lam a
    rw [FoxH.ElemDual.smul_apply, inv_smul_smul]
  -- STAGE 4: the `cup20`-values of `[tDef]` all vanish
  have hcup : ∀ n : ↥(H0 AbsGalQ2 (FoxH.ElemDual (Additive ↥(En.radData l h).T))),
      cup20 (FoxH.dualEval _) hpair
        (H2mk AbsGalQ2 (Additive ↥(En.radData l h).T) ⟨_, tDefZ2⟩) n = 0 := by
    intro n
    -- 4a. `n`-invariance ⟹ the induced character is `Bg`-conjugation-invariant (`∈ TCharC`)
    have hconjinv : ∀ (bb : RF.YB) (t : ↥(En.radData l h).T),
        n.1 (Additive.ofMul (⟨bb * (t : RF.YB) * bb⁻¹,
              (En.radData l h).hT.conj_mem t.1 t.2 bb⟩ : ↥(En.radData l h).T))
          = n.1 (Additive.ofMul t) := by
      intro bb t
      obtain ⟨γ, hγ⟩ :=
        rhoPrime_surjective RF b F (En.radData l h) rfl ρ (QuotientGroup.mk bb)
      have hconj : (RF.rhoPrime b F (En.radData l h) rfl ρ γ)⁻¹
            • Additive.ofMul (⟨bb * (t : RF.YB) * bb⁻¹,
                (En.radData l h).hT.conj_mem t.1 t.2 bb⟩ : ↥(En.radData l h).T)
          = Additive.ofMul t := by
        apply Additive.toMul.injective
        apply Subtype.ext
        show Quotient.out ((RF.rhoPrime b F (En.radData l h) rfl ρ γ)⁻¹)
            * (bb * (t : RF.YB) * bb⁻¹)
            * (Quotient.out ((RF.rhoPrime b F (En.radData l h) rfl ρ γ)⁻¹))⁻¹
          = (t : RF.YB)
        rw [conj_eq_of_mk_eq_T (D := En.radData l h)
            (show (QuotientGroup.mk (Quotient.out
                    ((RF.rhoPrime b F (En.radData l h) rfl ρ γ)⁻¹)) : RF.YB ⧸ (En.radData l h).M)
                = QuotientGroup.mk bb⁻¹ by
              rw [QuotientGroup.out_eq', QuotientGroup.mk_inv, hγ])
            (⟨bb * (t : RF.YB) * bb⁻¹,
              (En.radData l h).hT.conj_mem t.1 t.2 bb⟩ : ↥(En.radData l h).T)]
        group
      have h1 : (γ • n.1) (Additive.ofMul (⟨bb * (t : RF.YB) * bb⁻¹,
              (En.radData l h).hT.conj_mem t.1 t.2 bb⟩ : ↥(En.radData l h).T))
          = n.1 (Additive.ofMul t) := by
        show n.1 ((RF.rhoPrime b F (En.radData l h) rfl ρ γ)⁻¹
            • Additive.ofMul (⟨bb * (t : RF.YB) * bb⁻¹,
                (En.radData l h).hT.conj_mem t.1 t.2 bb⟩ : ↥(En.radData l h).T))
          = n.1 (Additive.ofMul t)
        rw [hconj]
      rw [n.2 γ] at h1
      exact h1
    -- 4b. the induced character `χ_n ∈ TCharC`
    let χn : ↥(TCharC (En.radData l h)) :=
      ⟨fun t => n.1 (Additive.ofMul t),
        ⟨fun t t' => by
          show n.1 (Additive.ofMul (t * t'))
            = n.1 (Additive.ofMul t) + n.1 (Additive.ofMul t')
          exact map_add n.1 (Additive.ofMul t) (Additive.ofMul t'), hconjinv⟩⟩
    -- 4c. the cup value is `H2mk (chiDef χ_n c)`, which vanishes since `betaChi χ_n c = 0`
    have hval : cup20 (FoxH.dualEval _) hpair
        (H2mk AbsGalQ2 (Additive ↥(En.radData l h).T) ⟨_, tDefZ2⟩) n
        = H2mk AbsGalQ2 (ZMod 2)
          ⟨chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χn c,
            chiDef_mem_Z2 (descSections En l h Dsc) (descSigma_spec En l h Dsc)
              htriv_local' χn c⟩ := by
      apply congrArg (H2mk AbsGalQ2 (ZMod 2))
      apply Subtype.ext
      funext gd
      show FoxH.dualEval _
          (Additive.ofMul (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c gd))
          ((gd.1 * gd.2) • n.1)
        = χn.1 (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c gd)
      rw [n.2 (gd.1 * gd.2)]
      rfl
    rw [hval, H2mk_eq_zero_iff]
    exact (iotaB_eq_zero_iff).mp (hc χn)
  -- STAGE 5: injectivity of `cup20` forces the `T`-defect class to vanish
  have hzero : H2mk AbsGalQ2 (Additive ↥(En.radData l h).T) ⟨_, tDefZ2⟩ = 0 := by
    apply (bijective_cup20_dualEval hA₂ htriv_local' hpair).1
    show cup20 (FoxH.dualEval _) hpair _ = cup20 (FoxH.dualEval _) hpair 0
    rw [map_zero]
    exact AddMonoidHom.ext fun n => hcup n
  -- STAGE 6: `B²`-extraction — a continuous splitting cochain `ψ` with `dOne ψ = tDef`
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hzero
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨ψ, hψC1, hψeq⟩ := hmem
  -- STAGE 7: `f γ := ψγ · fLift γ` is a genuine `M`-lift with `redTLift f = qOfCocycle c`.
  -- The split relation `dOne ψ = tDef` (via the `fLift`-conjugation action + `T` abelian/exp-2)
  -- makes `f` a homomorphism; `ψ ∈ T` keeps it over `ρ'` and its `T`-reduction `= qOfCocycle c`.
  have hψT : ∀ γ, ((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB) ∈ (En.radData l h).T :=
    fun γ => (Additive.toMul (ψ γ)).2
  have hsplitT : ∀ γ δ : AbsGalQ2,
      ((Additive.toMul (γ • ψ δ) : ↥(En.radData l h).T) : RF.YB)
        * ((Additive.toMul (ψ (γ * δ)) : ↥(En.radData l h).T) : RF.YB)⁻¹
        * ((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB)
        = (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ) : RF.YB) := by
    intro γ δ
    have hdo := congrFun hψeq (γ, δ)
    have h := congrArg (fun a : Additive ↥(En.radData l h).T =>
      ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB)) hdo
    simpa only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_add, toMul_sub, toMul_ofMul,
      Subgroup.coe_mul, Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_inv, mul_assoc] using h
  have hconjT : ∀ γ δ : AbsGalQ2,
      ((Additive.toMul (γ • ψ δ) : ↥(En.radData l h).T) : RF.YB)
        = fLift (descSections En l h Dsc) c γ
            * ((Additive.toMul (ψ δ) : ↥(En.radData l h).T) : RF.YB)
            * (fLift (descSections En l h Dsc) c γ)⁻¹ := by
    intro γ δ
    rw [hsmul γ (fLift (descSections En l h Dsc) c γ) (ψ δ) (hfLmk γ)]
    rfl
  -- the split relation `fLγ·pδ·fLγ⁻¹ = tDefγδ·pγ⁻¹·p(γδ)`
  have hsplit : ∀ γ δ : AbsGalQ2,
      fLift (descSections En l h Dsc) c γ * ((Additive.toMul (ψ δ) : ↥(En.radData l h).T) : RF.YB)
          * (fLift (descSections En l h Dsc) c γ)⁻¹
        = (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ) : RF.YB)
            * ((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB)⁻¹
            * ((Additive.toMul (ψ (γ * δ)) : ↥(En.radData l h).T) : RF.YB) := by
    intro γ δ
    have hs := hsplitT γ δ
    rw [hconjT γ δ] at hs
    rw [← hs]; group
  -- `T`-arithmetic helpers (`T` abelian; `T` has exponent 2)
  have hcomm2 : ∀ x y : RF.YB, x ∈ (En.radData l h).T → y ∈ (En.radData l h).T → x * y = y * x :=
    fun x y hx hy =>
      (En.radData l h).hcomm x ((En.radData l h).hTM hx) y ((En.radData l h).hTM hy)
  have hsq : ∀ x : RF.YB, x ∈ (En.radData l h).T → x * x = 1 :=
    fun x hx => (En.radData l h).helem x ((En.radData l h).hTM hx)
  -- assemble the `M`-lift `f γ = ψγ · fLift γ`
  refine ⟨⟨⟨MonoidHom.mk'
      (fun γ => ((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB)
        * fLift (descSections En l h Dsc) c γ) ?_,
      ?_⟩, ?_⟩, ?_⟩
  · -- map_mul: the homomorphism property, from the split relation + `T` abelian/exp-2
    intro γ δ
    have htd : fLift (descSections En l h Dsc) c γ * fLift (descSections En l h Dsc) c δ
        = (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ) : RF.YB)
            * fLift (descSections En l h Dsc) c (γ * δ) := by
      show _ = (fLift (descSections En l h Dsc) c γ * fLift (descSections En l h Dsc) c δ
          * (fLift (descSections En l h Dsc) c (γ * δ))⁻¹) * fLift (descSections En l h Dsc) c (γ * δ)
      group
    set pγ := ((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB) with hpγ
    set pδ := ((Additive.toMul (ψ δ) : ↥(En.radData l h).T) : RF.YB) with hpδ
    set pe := ((Additive.toMul (ψ (γ * δ)) : ↥(En.radData l h).T) : RF.YB) with hpe
    set td := (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ) : RF.YB) with htdd
    have htdT : td ∈ (En.radData l h).T :=
      (tDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) c (γ, δ)).2
    have hTarith : pγ * td * pγ⁻¹ * pe * td = pe := by
      rw [hcomm2 pγ td (hψT γ) htdT, mul_inv_cancel_right,
        hcomm2 td pe htdT (hψT (γ * δ)), mul_assoc, hsq td htdT, mul_one]
    symm
    calc (pγ * fLift (descSections En l h Dsc) c γ) * (pδ * fLift (descSections En l h Dsc) c δ)
        = pγ * (fLift (descSections En l h Dsc) c γ * pδ * (fLift (descSections En l h Dsc) c γ)⁻¹)
            * (fLift (descSections En l h Dsc) c γ * fLift (descSections En l h Dsc) c δ) := by group
      _ = pγ * (td * pγ⁻¹ * pe) * (td * fLift (descSections En l h Dsc) c (γ * δ)) := by
            rw [hsplit γ δ, htd]
      _ = (pγ * td * pγ⁻¹ * pe * td) * fLift (descSections En l h Dsc) c (γ * δ) := by group
      _ = pe * fLift (descSections En l h Dsc) c (γ * δ) := by rw [hTarith]
  · -- continuity
    exact (continuous_subtype_val.comp (continuous_of_discreteTopology.comp hψC1)).mul
      (fLift_continuous (descSections En l h Dsc) c)
  · -- over `ρ'`: `mk_M (f γ) = ρ'γ`  (`ψγ ∈ T ⊆ M`)
    intro γ
    show (QuotientGroup.mk (((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB)
        * fLift (descSections En l h Dsc) c γ) : RF.YB ⧸ (En.radData l h).M)
      = RF.rhoPrime b F (En.radData l h) rfl ρ γ
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr ((En.radData l h).hTM (hψT γ)), one_mul, hfLmk γ]
  · -- `redTLift f = qOfCocycle c`  (`ψγ ∈ T` ⟹ `mk_T (f γ) = mk_T (fLift γ) = qOfCocycle γ`)
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro γ
    show (QuotientGroup.mk (((Additive.toMul (ψ γ) : ↥(En.radData l h).T) : RF.YB)
        * fLift (descSections En l h Dsc) c γ) : RF.YB ⧸ (En.radData l h).T)
      = (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) (descSigma_spec En l h Dsc) c).1 γ
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (hψT γ), one_mul,
      show (QuotientGroup.mk (fLift (descSections En l h Dsc) c γ) : RF.YB ⧸ (En.radData l h).T)
        = piT (D := En.radData l h) (fLift (descSections En l h Dsc) c γ) from rfl,
      fLift_mk (descSections En l h Dsc) (descSigma_spec En l h Dsc) c γ]

/-- **`hpartial` for `G_ℚ₂`** — nondegeneracy of the obstruction pairing in the character:
every nonzero `χ ∈ (T^∨)^C` is detected by some `V`-coordinate.  Cup-duality clauses (iv)/(v) of
`prop_5_16`.

**RECIPE**: `d(c) := betaChi χ c - betaChi χ 0` is ADDITIVE in `c` (`betaChi_affine`,
`KeystoneDelta.lean:1172`), so the goal `∃ c, d(c) ≠ 0` is "the additive map `d : VCocycle → 𝔽₂`
is nonzero".  `d` is the cup pairing of `χ` (as `H⁰(ElemDual A)`, via the stage-4 `χ ↔ n`
identification of `hsep_local`) against the class-of-`c`-defect in `H¹`/`H²`; by the perfect
`(1,1)`/`(0,2)` pairings (`bijective_cup11_dualEval` / `bijective_cup02_dualEval`, clauses (iv)/(v),
`LocalLiftingDuality.lean:359/409`) a NONZERO `χ` is detected by some class — i.e. `d ≠ 0`.
Contrapositive form: if `d = 0` (all `c` give `betaChi χ c = betaChi χ 0`) then `χ = 0` by the
injectivity half of the perfect pairing, contradicting `hχ`.  The `∂`-surjectivity (that the
`c ↦ defect-class` map hits enough of `H¹`/`H²` to realize the pairing) is the substantive step,
dual to `hsep`'s `bijective_cup20` injectivity.  Couples to `hsep_local`'s stage-1–4 infrastructure
(same module `A`, dual, and `χ ↔ n` bridge). -/
theorem hpartial_local
    (ρ : BoundaryLifts b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))) (hχ : χ ≠ 0) :
    ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) := by
  sorry

end LocalResidues

/-! ## The local (140) display -/

/-- **The `RecursionInputs.phase140` field for `G_ℚ₂`** (P-16d6e3 assembly): the source-generic
`phase140_from_residues` (P-16d6e2) with `htriv`/`hH2` discharged locally and the four per-source
residues supplied by the lemmas above.  `hGaussZ` is threaded from the P-16d6e4 lane; `μ₀`/`G0` and
the module-ledger hypotheses (`hsimple`/`hfaith`/`hVne`) are the `prop_8_9` ledger, fed at the
capstone (`Prop89Close`). -/
theorem phase140_local
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l h))
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (μ₀ : ℕ) (G0 : ℤ)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (_hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (hμ : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) = μ₀)
    (hGaussZ : ∀ ρ : BoundaryLifts b F RF.TC,
      ∑ᶠ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
        sign (QZero (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) c)
          = (Nat.card En.Vmod : ℤ) * G0) :
    2 * (Nat.card ↥(TCharC (En.radData l h)) : ℤ) * RF.zBC b F l h
      = (Nat.card En.Vmod * μ₀ : ℕ)
          * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : ↥(TCharC (En.radData l h)),
                (2 * (RF.nPhase b F (phaseChi En l h Dsc ζ) : ℤ)
                  - (exactImageCount b F RF.TC : ℤ))) :=
  phase140_from_residues b F En l h Dsc htriv_local' hfg
    (card_H2_zmod2_eq_two htriv_local') μ₀ G0 hμ
    (fun ρ => hsep_local b F En l h Dsc ρ)
    (fun ρ => hpartial_local b F En l h Dsc ρ)
    (fun ρ => hZcard_local b F En l h hsimple hVne hnt ρ)
    hGaussZ

end SectionEight

end GQ2
