/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.LedgerGammaR
import GQ2.FinitelyGenerated
import GQ2.Reconstruction
import GQ2.Roe.Supply
import GQ2.RStage.GammaR
import GQ2.CardH2GammaA

/-!
# The nonzero variation class over `Γ_R`, `#H²(Γ_R, 𝔽₂) = 2`, and Lemma 8.6

The `Γ_R` twin of `GQ2/HalfTorsorGammaA.lean`, and the delivery point of two `SourceData`
leaves for the Roe candidate:

* `exists_nonzero_varCoc_gammaR` — assembling the `Γ_R` ledger identity with the `prop_5_15_R`
  self-duality: from `NoDescent`, there is a crossed `T`-cocycle `u` whose variation class
  `[varCoc u] ∈ H²(Γ_R, 𝔽₂)` is nonzero (the `hvar` input to `CentralObstruction.half_count`);
* `card_H2_gammaR_eq_two` — `#H²(Γ_R, 𝔽₂) = 2`: `WordCoh2R.obsH2_R_injective` gives `≤ 2`, the
  nonzero variation class gives surjectivity;
* `card_H2_gammaR` — the same **unconditionally**, over the packaged `GammaR` with its canonical
  trivial action.  The `NoDescent` hypothesis is discharged against the *source-free* `D₈` witness
  `CardH2GammaA.datum`/`datum_noDescent`, reused verbatim (`RadicalCoverData` carries no `Γ`); only
  the surjection `Γ_R ↠ 𝔽₂²/⟨s̄⟩` is rebuilt, by descending `CardH2GammaA.qmark` through
  `Marking.descendR`.  **This is the `SourceData.cardH2` leaf** — the `hcard_R` residue that
  `RStageGammaR.stageR136_gammaR_of_hcard` and `hsep_hom_gammaR` thread;
* `half_torsor_gammaR` / `lemma_8_6_gammaR` — **the `SourceData.lem86` leaf** (obligation ii.4):
  with a nonzero radical edge, exactly half of the unrestricted `M`-lifts of a lower epimorphism
  `ρ : Γ_R ↠ B/M` satisfy the central relation.

The two `example`s at the end are stated in the **verbatim field types** of `GQ2.SourceData`
specialised at `Γ := GammaR` (the `RStage/GammaR.lean` spelling discipline), so that any drift
between these declarations and the structure is caught here rather than in R32's `sourceR`.
-/

namespace GQ2

namespace SectionEight

namespace LedgerGammaR

open CentralObstruction ContCoh WordCohBridgeR FoxH WordCoh2R MixedBObsR RadicalEdgeGammaA

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

/-- **The nonzero variation class over `Γ_R`** (the Γ_R half-torsor proof).  For a lower
epimorphism `ρ : Γ_R ↠ B/M` with nonzero radical edge (`NoDescent`), there is a crossed
`T`-cocycle `u` whose variation class is a nonzero element of `H²(Γ_R, 𝔽₂)`. -/
theorem exists_nonzero_varCoc_gammaR (D : RadicalCoverData Bg) (S : TComplement D)
    (hedge : D.NoDescent) (ρ : ContinuousMonoidHom GR (Bg ⧸ D.M)) (hρ : Function.Surjective ρ)
    [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m) :
    ∃ u : TCocycle D ρ, H2mk GR (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ ≠ 0 := by
  haveI := discreteTopology_quotient D
  -- ===== the `GR`-modules on `T`, `T^∨` via the `ρ`-pullback =====
  letI actGA : DistribMulAction GR (Additive ↥D.T) :=
    DistribMulAction.compHom (Additive ↥D.T) ρ.toMonoidHom
  have hcompat : ∀ (γ : GR) (a : Additive ↥D.T), γ • a = ρ γ • a := fun _ _ => rfl
  have hactGA : ∀ (γ : GR) (s : Additive ↥D.T),
      Additive.toMul (γ • s) = cactFun D (ρ γ) (Additive.toMul s) :=
    fun γ s => cActT_toMul D (ρ γ) s
  haveI : ContinuousSMul GR (Additive ↥D.T) := by
    constructor
    have hfac : (fun p : GR × Additive ↥D.T => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × Additive ↥D.T => cq.1 • cq.2)
          ∘ (fun p : GR × Additive ↥D.T => ((ρ p.1 : Bg ⧸ D.M), p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI actGAD : DistribMulAction GR (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom (ElemDual (Additive ↥D.T)) ρ.toMonoidHom
  have hcompatD : ∀ (γ : GR) (l : ElemDual (Additive ↥D.T)), γ • l = ρ γ • l := fun _ _ => rfl
  haveI : ContinuousSMul GR (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac : (fun p : GR × ElemDual (Additive ↥D.T) => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => cq.1 • cq.2)
          ∘ (fun p : GR × ElemDual (Additive ↥D.T) => ((ρ p.1 : Bg ⧸ D.M), p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ a : Additive ↥D.T, a + a = 0 := fun a =>
    Additive.toMul.injective (Subtype.ext (D.helem _ (D.hTM (Additive.toMul a).2)))
  have hA₂D : ∀ l : ElemDual (Additive ↥D.T), l + l = 0 := fun l => l.add_self_eq_zero
  -- ===== the shifted-edge dual cocycle and its nonzero `H¹`-class =====
  obtain ⟨φf, hφf, hφne⟩ := exists_phiF_R D S ρ hcompat hcompatD hρ hedge
  -- ===== `prop_5_15_R`: the perfect pairing detects `[φf] ≠ 0` =====
  have adm := markC_admissible_R ρ hρ
  obtain ⟨P, hP, _hleft, hright⟩ :=
    (FoxH.prop_5_15_R (markC_R ρ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.2
  set yφ : H1wR (A := ElemDual (Additive ↥D.T)) (markC_R ρ) :=
    h1EquivR ρ hcompatD hρ hA₂D (H1mk GR (ElemDual (Additive ↥D.T)) φf) with hyφdef
  have hyφne : yφ ≠ 0 := fun h =>
    hφne ((h1EquivR ρ hcompatD hρ hA₂D).injective (by rw [map_zero]; exact h))
  obtain ⟨hx, hPne⟩ := hright yφ hyφne
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective hx
  -- `evalR φf` is a word cocycle representing `yφ`
  set yZ1w : Z1wR (A := ElemDual (Additive ↥D.T)) (markC_R ρ) :=
    ⟨evalR φf, eval_mem_Z1wR ρ hcompatD φf⟩ with hyZ1wdef
  have hyeq : h1wMkR (markC_R ρ) yZ1w = yφ := rfl
  have hmixne : mixedB_R (markC_R ρ) x.val (evalR φf) ≠ 0 := by
    have := hP x yZ1w
    rw [hyeq] at this
    rwa [← this]
  -- ===== the primal crossed cocycle `u` from `w = ofZ1wR x` =====
  set w : Z1 GR (Additive ↥D.T) := ofZ1wR ρ hcompat hρ hA₂ x with hwdef
  have hevalw : evalR w = x.val := congrArg Subtype.val (toZ1wRHom_ofZ1wR ρ hcompat hρ hA₂ x)
  set u : TCocycle D ρ :=
    { u := fun γ => ((Additive.toMul (w.1 γ) : ↥D.T) : Bg)
      mem := fun γ => (Additive.toMul (w.1 γ)).2
      cont := continuous_subtype_val.comp ((mem_Z1_iff.mp w.2).1)
      crossed := by
        intro γ δ b hb
        have hw := (mem_Z1_iff.mp w.2).2 γ δ
        show ((Additive.toMul (w.1 (γ * δ)) : ↥D.T) : Bg)
          = ((Additive.toMul (w.1 γ) : ↥D.T) : Bg)
            * (b * ((Additive.toMul (w.1 δ) : ↥D.T) : Bg) * b⁻¹)
        rw [hw]
        show ((Additive.toMul (w.1 γ + γ • w.1 δ) : ↥D.T) : Bg) = _
        rw [show Additive.toMul (w.1 γ + γ • w.1 δ)
            = Additive.toMul (w.1 γ) * Additive.toMul (γ • w.1 δ) from rfl,
          Subgroup.coe_mul, hactGA, cactFun_eq D (ρ γ) hb] } with hudef
  have hu : ∀ γ, u.u γ = ((Additive.toMul (w.1 γ) : ↥D.T) : Bg) := fun _ => rfl
  -- ===== assemble: the variation class is nonzero =====
  refine ⟨u, varCoc_class_ne_zero_R D S ρ hcompat hcompatD htriv w φf hφf u hu ?_⟩
  rw [hevalw]
  exact hmixne

/-- **`#H²(Γ_R, 𝔽₂) = 2`** (the Γ_R half-torsor proof `hcard`).  The obstruction injection
`obsH2_R : H² ↪ 𝔽₂` (c2) gives `≤ 2`; the nonzero variation class makes it surjective, hence a
bijection. -/
theorem card_H2_gammaR_eq_two (D : RadicalCoverData Bg) (S : TComplement D)
    (hedge : D.NoDescent) (ρ : ContinuousMonoidHom GR (Bg ⧸ D.M)) (hρ : Function.Surjective ρ)
    [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m) :
    Nat.card (H2 GR (ZMod 2)) = 2 := by
  obtain ⟨u, hu⟩ := exists_nonzero_varCoc_gammaR D S hedge ρ hρ htriv
  have hinj := obsH2_R_injective htriv
  set a := H2mk GR (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ with hadef
  have hne : obsH2_R htriv a ≠ 0 := fun h => hu ((injective_iff_map_eq_zero _).mp hinj _ h)
  have hy2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hsurj : Function.Surjective (obsH2_R htriv) := by
    intro y
    rcases hy2 y with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨a, (hy2 _).resolve_left hne⟩
  rw [Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- **Lemma 8.6, `Γ_R` source** (the Γ_R half-torsor proof): with a nonzero radical edge, exactly
half of the unrestricted `M`-lifts of a lower epimorphism `ρ : Γ_R ↠ B/M` satisfy the central
relation.  The abstract half-count `CentralObstruction.half_count` fed by the nonzero variation
class (`exists_nonzero_varCoc_gammaR`) and `#H² = 2` (`card_H2_gammaR_eq_two`); the counted set is
finite because `Γ_R` is topologically finitely generated. -/
theorem half_torsor_gammaR (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GammaR (Bg ⧸ D.M)) (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  classical
  -- retype `ρ` against the raw quotient `Γ_R = F₄ ⧸ N_R` (defeq to `↑GammaR`) so the `GR`-machinery
  -- and its instances resolve
  let ρ0 : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) (Bg ⧸ D.M) := ρ
  haveI : TotallyDisconnectedSpace (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
    inferInstanceAs (TotallyDisconnectedSpace (GammaR : Type))
  have hfg : ∃ s : Finset (FreeProfiniteGroup (Fin 4) ⧸ NR),
      (Subgroup.closure (s : Set (FreeProfiniteGroup (Fin 4) ⧸ NR))).topologicalClosure = ⊤ :=
    gammaR_topologicallyFinitelyGenerated
  haveI : Finite (ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) Bg) :=
    finite_continuousMonoidHom hfg Bg
  haveI : Finite (MLifts D ρ0) := by unfold MLifts; exact Subtype.finite
  obtain ⟨S⟩ := tComplement_nonempty D
  letI actZ : DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NR) (ZMod 2) :=
    { smul := fun _ m => m
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  haveI : ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NR) (ZMod 2) := ⟨continuous_snd⟩
  have htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NR) (m : ZMod 2), x • m = m := fun _ _ => rfl
  obtain ⟨u, hvar⟩ := exists_nonzero_varCoc_gammaR D S hedge ρ0 hρ htriv
  have hcard := card_H2_gammaR_eq_two D S hedge ρ0 hρ htriv
  exact half_count D ρ0 S htriv u hvar hcard

/-- **Lemma 8.6, `Γ_R` source** ⟦lem-radicaledge⟧ — the `SourceData.lem86` leaf (obligation ii.4).
`Γ_R` twin of `SectionEight.lemma_8_6_gammaA` (`GQ2/SectionEight/Partition.lean`), stated over the
packaged `GammaR`; the content is `half_torsor_gammaR`. -/
theorem lemma_8_6_gammaR (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GammaR (Bg ⧸ D.M)) (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  half_torsor_gammaR D hedge ρ hρ

/-! ## `#H²(Γ_R, 𝔽₂) = 2`, unconditionally

The `NoDescent` hypothesis of `card_H2_gammaR_eq_two` is discharged exactly as on the `Γ_A` side
(`GQ2/CardH2GammaA.lean`), against the same concrete witness `𝔽₂ → D₈ → 𝔽₂²` with `T = M = ⟨s̄⟩`
and `q ≡ 0`.  That witness is **source-free** — `RadicalCoverData Bg` binds only `[Group Bg]
[Finite Bg]`, no `Γ` — so `CardH2GammaA.datum` and `CardH2GammaA.datum_noDescent` are reused
verbatim.  Only the surjection onto `𝔽₂²/⟨s̄⟩` is `Γ`-specific and rebuilt here: the same order-2
marking `CardH2GammaA.qmark`, now shown `AdmissibleR` (its Roe wild relation is automatic — both
wild generators are trivial, `Marking.wildRelR_of_trivial_wild`) and descended through
`Marking.descendR`. -/

section Unconditional

open CardH2GammaA DihedralGroup

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ Mlayer) :=
  (discreteTopology_quotient datum : DiscreteTopology (Base ⧸ datum.M))

/-- `CardH2GammaA.qmark` is `R`-admissible.  `Generates`, `TameRel` and `Pro2Core` are the
`Γ_A`-side clauses re-proved verbatim (`CardH2GammaA.qmark_admissible` is `private`); the Roe wild
relation replaces `Γ_A`'s and is automatic since both wild generators are trivial. -/
private theorem qmark_admissibleR : qmark.AdmissibleR := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Generates: `[r̄]` alone generates the order-2 quotient
    show Subgroup.closure {qmark.σ, qmark.τ, qmark.x₀, qmark.x₁} = ⊤
    rw [eq_top_iff]; intro x _
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    rcases quotient_cases b with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.subset_closure (by left; rfl)
  · -- TameRel: `τ = 1`
    show conjP (1 : Base ⧸ Mlayer) (QuotientGroup.mk (r 1)) = (1 : Base ⧸ Mlayer) ^ 2
    rw [conjP, mul_one, inv_mul_cancel, one_pow]
  · -- WildRelR: trivial wild generators
    exact Marking.wildRelR_of_trivial_wild qmark rfl rfl
      (powOmega2_eq_one_of_odd (by
        show Odd (orderOf (1 : Base ⧸ Mlayer)); rw [orderOf_one]; decide))
  · -- Pro2Core: `⟨x₀,x₁⟩ = ⟨1,1⟩` normally closes to `⊥`
    show IsPGroup 2 (Subgroup.normalClosure {qmark.x₀, qmark.x₁})
    have hbot : Subgroup.normalClosure ({qmark.x₀, qmark.x₁} : Set (Base ⧸ Mlayer)) = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.normalClosure_le_normal ?_
      rintro x (rfl | rfl) <;> exact Subgroup.mem_bot.mpr rfl
    rw [hbot]; exact IsPGroup.of_bot

/-- The chosen surjection `ρ_R : Γ_R ↠ 𝔽₂²/⟨s̄⟩`, by descending `qmark` through
`Marking.descendR`. -/
noncomputable def rhoR : ContinuousMonoidHom GR (Base ⧸ Mlayer) :=
  Marking.descendR qmark qmark_admissibleR

theorem rhoR_surjective : Function.Surjective rhoR :=
  Marking.descendR_surjective qmark qmark_admissibleR

/-- **`#H²(Γ_R, 𝔽₂) = 2`, unconditionally**, over the raw quotient `GR`. -/
theorem card_H2_gammaR_unit [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m) :
    Nat.card (H2 GR (ZMod 2)) = 2 :=
  card_H2_gammaR_eq_two datum (tComplement_nonempty datum).some datum_noDescent
    rhoR rhoR_surjective htriv

/-- **`#H²(Γ_R, 𝔽₂) = 2`** over the packaged `GammaR`, with its canonical trivial action
(`RStageGammaR.instDistribMulActionGammaR`) — **the `SourceData.cardH2` leaf**, and the exact
`hcard_R` residue threaded by `RStageGammaR.hsep_hom_gammaR` and
`RStageGammaR.stageR136_gammaR_of_hcard`.  Bridges `card_H2_gammaR_unit` across the
`GR ≡ GammaR` defeq, mirroring `CardH2GammaA.card_H2_gammaA`. -/
theorem card_H2_gammaR : Nat.card (H2 GammaR (ZMod 2)) = 2 := by
  letI : DistribMulAction GR (ZMod 2) := RStageGammaR.instDistribMulActionGammaR
  letI : ContinuousSMul GR (ZMod 2) := ⟨continuous_snd⟩
  exact card_H2_gammaR_unit (fun _ _ => rfl)

end Unconditional

/-! ### `SourceData` field-type smoke tests (R31 spelling discipline) -/

/-- Smoke test for the `SourceData.cardH2` field at `Γ := GammaR` — stated in the verbatim field
type (`letI := smulZmod2; Nat.card (H2 Γ (ZMod 2)) = 2`), with `smulZmod2` discharged by the
registered global instance, exactly the `inferInstance` route `BoundaryMaps.sourceA` takes. -/
example : letI := (inferInstance : DistribMulAction (GammaR : Type) (ZMod 2));
    Nat.card (H2 GammaR (ZMod 2)) = 2 :=
  card_H2_gammaR

/-- Smoke test for the `SourceData.lem86` field at `Γ := GammaR` — stated in the verbatim field
type, and filled the way `BoundaryMaps.sourceA` fills it with `lemma_8_6_gammaA`. -/
example : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg), D.NoDescent →
    ∀ (ρ : ContinuousMonoidHom GammaR (Bg ⧸ D.M)), Function.Surjective ρ →
      2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  fun D hedge ρ hρ => lemma_8_6_gammaR D hedge ρ hρ

end LedgerGammaR

end SectionEight

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 8.6 = ⟦lem-radicaledge⟧ — `lemma_8_6_gammaR`, over `Γ_R`.
  * Definition 1.1 = ⟦def:GammaR⟧ — `Marking.descendR`/`AdmissibleR`, in `rhoR`.
-/
