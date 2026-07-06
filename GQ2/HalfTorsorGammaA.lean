import GQ2.LedgerGammaA
import GQ2.FinitelyGenerated
import GQ2.Reconstruction

/-!
# The nonzero variation class over `Γ_A` (P-16c4 deliverable)

Assembling the ledger identity with the `prop_5_15` self-duality: from `NoDescent`, there is a
crossed `T`-cocycle `u` whose variation class `[varCoc u] ∈ H²(Γ_A, 𝔽₂)` is nonzero.  This is the
`hvar` input to the abstract half-torsor count `CentralObstruction.n` (P-16c5).
-/

namespace GQ2

namespace SectionEight

namespace LedgerGammaA

open CentralObstruction ContCoh WordCohBridge FoxH WordCoh2 MixedBObs RadicalEdgeGammaA

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

/-- **The nonzero variation class over `Γ_A`** (P-16c4).  For a lower epimorphism `ρ : Γ_A ↠ B/M`
with nonzero radical edge (`NoDescent`), there is a crossed `T`-cocycle `u` whose variation class
is a nonzero element of `H²(Γ_A, 𝔽₂)`. -/
theorem exists_nonzero_varCoc_gammaA (D : RadicalCoverData Bg) (S : TComplement D)
    (hedge : D.NoDescent) (ρ : ContinuousMonoidHom GA (Bg ⧸ D.M)) (hρ : Function.Surjective ρ)
    [DistribMulAction GA (ZMod 2)] [ContinuousSMul GA (ZMod 2)]
    (htriv : ∀ (x : GA) (m : ZMod 2), x • m = m) :
    ∃ u : TCocycle D ρ, H2mk GA (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ ≠ 0 := by
  haveI := discreteTopology_quotient D
  -- ===== the `GA`-modules on `T`, `T^∨` via the `ρ`-pullback =====
  letI actGA : DistribMulAction GA (Additive ↥D.T) :=
    DistribMulAction.compHom (Additive ↥D.T) ρ.toMonoidHom
  have hcompat : ∀ (γ : GA) (a : Additive ↥D.T), γ • a = ρ γ • a := fun _ _ => rfl
  have hactGA : ∀ (γ : GA) (s : Additive ↥D.T),
      Additive.toMul (γ • s) = cactFun D (ρ γ) (Additive.toMul s) := fun γ s => cActT_toMul D (ρ γ) s
  haveI : ContinuousSMul GA (Additive ↥D.T) := by
    constructor
    have hfac : (fun p : GA × Additive ↥D.T => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × Additive ↥D.T => cq.1 • cq.2)
          ∘ (fun p : GA × Additive ↥D.T => ((ρ p.1 : Bg ⧸ D.M), p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI actGAD : DistribMulAction GA (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom (ElemDual (Additive ↥D.T)) ρ.toMonoidHom
  have hcompatD : ∀ (γ : GA) (l : ElemDual (Additive ↥D.T)), γ • l = ρ γ • l := fun _ _ => rfl
  haveI : ContinuousSMul GA (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac : (fun p : GA × ElemDual (Additive ↥D.T) => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => cq.1 • cq.2)
          ∘ (fun p : GA × ElemDual (Additive ↥D.T) => ((ρ p.1 : Bg ⧸ D.M), p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ a : Additive ↥D.T, a + a = 0 := fun a =>
    Additive.toMul.injective (Subtype.ext (D.helem _ (D.hTM (Additive.toMul a).2)))
  have hA₂D : ∀ l : ElemDual (Additive ↥D.T), l + l = 0 := fun l => by
    ext a; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l a)
  -- ===== the shifted-edge dual cocycle and its nonzero `H¹`-class =====
  obtain ⟨φf, hφf, hφne⟩ := exists_phiF D S ρ hcompat hcompatD hρ hedge
  -- ===== `prop_5_15`: the perfect pairing detects `[φf] ≠ 0` =====
  have adm := markC_admissible ρ hρ
  obtain ⟨P, hP, _hleft, hright⟩ :=
    (FoxH.prop_5_15 (markC ρ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.2
  set yφ : H1w (A := ElemDual (Additive ↥D.T)) (markC ρ) :=
    h1Equiv ρ hcompatD hρ hA₂D (H1mk GA (ElemDual (Additive ↥D.T)) φf) with hyφdef
  have hyφne : yφ ≠ 0 := fun h =>
    hφne ((h1Equiv ρ hcompatD hρ hA₂D).injective (by rw [map_zero]; exact h))
  obtain ⟨hx, hPne⟩ := hright yφ hyφne
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective hx
  -- `eval φf` is a word cocycle representing `yφ`
  set yZ1w : Z1w (A := ElemDual (Additive ↥D.T)) (markC ρ) :=
    ⟨eval φf, eval_mem_Z1w ρ hcompatD φf⟩ with hyZ1wdef
  have hyeq : h1wMk (markC ρ) yZ1w = yφ := rfl
  have hmixne : mixedB (markC ρ) x.val (eval φf) ≠ 0 := by
    have := hP x yZ1w
    rw [hyeq] at this
    rw [← this]
    exact hPne
  -- ===== the primal crossed cocycle `u` from `w = ofZ1w x` =====
  set w : Z1 GA (Additive ↥D.T) := ofZ1w ρ hcompat hρ hA₂ x with hwdef
  have hevalw : eval w = x.val := congrArg Subtype.val (toZ1wHom_ofZ1w ρ hcompat hρ hA₂ x)
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
  refine ⟨u, varCoc_class_ne_zero D S ρ hcompat hcompatD htriv w φf hφf u hu ?_⟩
  rw [hevalw]
  exact hmixne

/-- **`#H²(Γ_A, 𝔽₂) = 2`** (P-16c4 `hcard`).  The obstruction injection `obsH2 : H² ↪ 𝔽₂` (c2)
gives `≤ 2`; the nonzero variation class makes it surjective, hence a bijection. -/
theorem card_H2_gammaA_eq_two (D : RadicalCoverData Bg) (S : TComplement D)
    (hedge : D.NoDescent) (ρ : ContinuousMonoidHom GA (Bg ⧸ D.M)) (hρ : Function.Surjective ρ)
    [DistribMulAction GA (ZMod 2)] [ContinuousSMul GA (ZMod 2)]
    (htriv : ∀ (x : GA) (m : ZMod 2), x • m = m) :
    Nat.card (H2 GA (ZMod 2)) = 2 := by
  obtain ⟨u, hu⟩ := exists_nonzero_varCoc_gammaA D S hedge ρ hρ htriv
  have hinj := obsH2_injective htriv
  set a := H2mk GA (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ with hadef
  have hne : obsH2 htriv a ≠ 0 := fun h => hu ((injective_iff_map_eq_zero _).mp hinj _ h)
  have hy2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hsurj : Function.Surjective (obsH2 htriv) := by
    intro y
    rcases hy2 y with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · refine ⟨a, ?_⟩
      rcases hy2 (obsH2 htriv a) with h | h
      · exact absurd h hne
      · exact h
  rw [Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- **Lemma 8.6, `Γ_A` source** (P-16c5): with a nonzero radical edge, exactly half of the
unrestricted `M`-lifts of a lower epimorphism `ρ : Γ_A ↠ B/M` satisfy the central relation.
The abstract half-count `CentralObstruction.half_count` fed by the nonzero variation class
(`exists_nonzero_varCoc_gammaA`) and `#H² = 2` (`card_H2_gammaA_eq_two`); the counted lift set is
finite because `Γ_A` is topologically finitely generated. -/
theorem half_torsor_gammaA (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GammaA (Bg ⧸ D.M)) (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  classical
  -- retype `ρ` against the raw quotient `Γ_A = F₄ ⧸ N_A` (defeq to `↑GammaA`) so the `GA`-machinery
  -- and its instances resolve
  let ρ0 : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) (Bg ⧸ D.M) := ρ
  haveI : TotallyDisconnectedSpace (FreeProfiniteGroup (Fin 4) ⧸ NA) :=
    inferInstanceAs (TotallyDisconnectedSpace (GammaA : Type))
  have hfg : ∃ s : Finset (FreeProfiniteGroup (Fin 4) ⧸ NA),
      (Subgroup.closure (s : Set (FreeProfiniteGroup (Fin 4) ⧸ NA))).topologicalClosure = ⊤ :=
    gammaA_topologicallyFinitelyGenerated
  haveI : Finite (ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) Bg) :=
    finite_continuousMonoidHom hfg Bg
  haveI : Finite (MLifts D ρ0) := by unfold MLifts; exact Subtype.finite
  obtain ⟨S⟩ := tComplement_nonempty D
  letI actZ : DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) :=
    { smul := fun _ m => m
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  haveI : ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) := ⟨continuous_snd⟩
  have htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NA) (m : ZMod 2), x • m = m := fun _ _ => rfl
  obtain ⟨u, hvar⟩ := exists_nonzero_varCoc_gammaA D S hedge ρ0 hρ htriv
  have hcard := card_H2_gammaA_eq_two D S hedge ρ0 hρ htriv
  exact half_count D ρ0 S htriv u hvar hcard

end LedgerGammaA

end SectionEight

end GQ2

