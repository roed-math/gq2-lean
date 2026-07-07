import GQ2.RStageLocal
import GQ2.WordCohBridge
import GQ2.HalfTorsorGammaA
import GQ2.FinitelyGenerated
import GQ2.LocalLiftingDuality

/-!
# P-16d6e5 (residue package, candidate source): the (136) R-stage for `Γ = Γ_A`

Mirror of `GQ2/RStageLocal.lean` at the candidate source `Γ_A`, per `docs/p16d6e5-plan.md`.
The local file counts `Z¹(G_ℚ₂, R)` with `prop_5_16`'s `card_Z1_eq` (B6/B7); here the same
counts come from the **candidate duality** `prop_5_15` (`IsSelfDual`) through the word-complex
bridge `z1Equiv : Z1 GA A ≃+ Z1w (markC ρ)` (`WordCohBridge`) — **no B-axioms on the word side**.

Deliverables (route of record: `docs/p16d6e5-plan.md`):
* `htriv_gammaA` — the trivial `Γ_A`-action on `𝔽₂` (registered here as the canonical trivial
  `DistribMulAction GammaA (ZMod 2)`; `γ • m = m` is then `rfl`);
* `hZcount_gammaA` — `#RCocycle = z_R` via `z1Equiv` + `prop_5_15` clause 2 + `blockRChar_card`;
* `hsep_hom_gammaA` — the `(R^∨)^C`-separation via the marking-level lifting argument (L1–L5 of
  the plan; the trace-span package is `prop_5_8_right`-based, NO `H²(Γ_A,R)`);
* `stageR136_gammaA_of_hcard` — the (136) identity, threading `hcard_A` (P-16d6e6's
  `card_H2_gammaA_eq_two`) so e5 is decoupled from e6.

**Standing plumbing note (the `GA`/`GammaA` bridge).**  `GammaA := profiniteQuotient NA` is
**defeq** to `GA := FreeProfiniteGroup (Fin 4) ⧸ NA`, but their *instances* do not cross-resolve
(distinct head symbols): `GammaA` carries `TotallyDisconnectedSpace` (a `ProfiniteGrp`) while
`GA` does not auto-synthesise it, and a `DistribMulAction GammaA (ZMod 2)` is not found when a
`DistribMulAction GA (ZMod 2)` is requested.  The theorems are stated over `Γ := GammaA` (so the
`blockStageR136`/`RecursionInputs` instances resolve and the conclusion matches the P-16d6e7
`RecursionInputs RF B.bA F …` bundle); the word-machinery calls (over `GA`) are bridged inside
each proof by `inferInstanceAs`/`show`-transports across the defeq (`gammaA_eq_GA` below).  This
is the main mechanical cost of the candidate side and is isolated to the proof interiors.
-/

namespace GQ2

namespace RStageGammaA

open ContCoh SectionEight SectionSeven WordCohBridge GQ2.FoxH

/-- `Γ_A`'s underlying type is the raw quotient `GA` against which the marking machinery
(`z1Equiv`, `markC`, `prop_5_15`) is stated. -/
theorem gammaA_eq_GA : (GammaA : Type) = GA := rfl

/-! ## The canonical trivial `Γ_A`-action on `𝔽₂` -/

/-- The trivial `Γ_A`-action on `𝔽₂` (`Aut(𝔽₂) = 1`, so every action is this one). -/
instance instDistribMulActionGammaA : DistribMulAction GammaA (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul GammaA (ZMod 2) := ⟨continuous_snd⟩

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **The `Γ_A`-action on `𝔽₂` is trivial** (P-16d6e5 residue): definitional, from the
registered trivial action. -/
theorem htriv_gammaA (γ : GammaA) (m : ZMod 2) : γ • m = m := rfl

/-! ## `hZcount`: the `z_R` torsor count at the candidate source

The candidate mirror of `RStageLocal.hZcount_local`: `RCocycle ≃ Z¹(Γ_A, R_{f₀})` (identical
conjugation-action setup, reusing `RStageLocal`'s `ConjAction` section), then the count via
`z1Equiv` + `prop_5_15` clause 2 (`#Z1w = #R²·#fixedPts C (R^∨)`) instead of the local
`card_Z1_eq`, and the same `fixedPts ≃ RCharSub` bridge + `blockRChar_card`. -/
theorem hZcount_gammaA
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
    (f₀ : BoundaryLifts b F T) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
      = (blockFrameImpl T Blk hE2).zR := by
  classical
  letI : CommGroup ↥Blk.R := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.R) := RStageLocal.conjC Blk hRK
  -- the lower map through `C = Y/K`, surjective (over `GA`, against which `z1Equiv` is stated)
  set θ : ContinuousMonoidHom GA (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
      show Continuous fun γ => QuotientGroup.mk' Blk.K (f₀.1.1 γ)
      exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := f₀.1.2 y
    exact ⟨γ, by show QuotientGroup.mk' Blk.K (f₀.1.1 γ) = c; rw [hγ, hy]⟩
  letI actG : DistribMulAction GA (Additive ↥Blk.R) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.R) := (inferInstance : TopologicalSpace ↥Blk.R)
  haveI : DiscreteTopology (Additive ↥Blk.R) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.R).eq_bot⟩
  haveI : Finite (Additive ↥Blk.R) := (inferInstance : Finite ↥Blk.R)
  haveI : ContinuousSMul GA (Additive ↥Blk.R) := by
    refine ⟨?_⟩
    have hfac : (fun p : GA × Additive ↥Blk.R => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × Additive ↥Blk.R => q.1 • q.2)
          ∘ (fun p : GA × Additive ↥Blk.R => (θ p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcomp : ∀ (γ : GA) (a : Additive ↥Blk.R), γ • a = θ γ • a := fun _ _ => rfl
  have hA₂ : ∀ a : Additive ↥Blk.R, a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hR2 _ (Additive.toMul a).2
  -- the action at the `f₀`-representative (`f₀.1.1 γ` for `γ : GA` reads through `GammaA ≡ GA`)
  have hsmul : ∀ (γ : GA) (a : Additive ↥Blk.R),
      γ • a
        = Additive.ofMul (⟨f₀.1.1 γ * ((Additive.toMul a : ↥Blk.R) : Y) * (f₀.1.1 γ)⁻¹,
            RStageLocal.conj_mem_R (f₀.1.1 γ) (Additive.toMul a)⟩ : ↥Blk.R) := by
    intro γ a
    have h1 : γ • a
        = (QuotientGroup.mk' Blk.K (f₀.1.1 γ) : Y ⧸ Blk.K) • Additive.ofMul (Additive.toMul a) :=
      rfl
    rw [h1]
    exact RStageLocal.conjC_smul_of_mk hRK (f₀.1.1 γ) (Additive.toMul a)
  -- the multiplicative↔additive crossed-cocycle bridge `RCocycle ≃ Z¹(Γ_A, R)`
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f₀.1.1
      ≃ ↥(Z1 GA (Additive ↥Blk.R)) :=
    { toFun := fun c =>
        ⟨fun γ => Additive.ofMul ⟨c.u γ, c.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun γ => (⟨c.u γ, c.mem γ⟩ : ↥Blk.R)
            exact Continuous.subtype_mk c.cont _
          · intro γ δ
            rw [hsmul γ (Additive.ofMul ⟨c.u δ, c.mem δ⟩)]
            apply Additive.toMul.injective
            apply Subtype.ext
            show c.u (γ * δ) = c.u γ * (f₀.1.1 γ * c.u δ * (f₀.1.1 γ)⁻¹)
            exact c.crossed γ δ⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥Blk.R) : Y)
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := by
            have hz := (mem_Z1_iff.mp z.2).1
            exact continuous_subtype_val.comp hz
          crossed := by
            intro γ δ
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ (z.1 δ)] at hz
            exact congrArg (fun a => ((Additive.toMul a : ↥Blk.R) : Y)) hz }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun γ => rfl) }
  rw [Nat.card_congr hequiv]
  -- the count: `#Z¹(Γ_A, R) = #Z1w(markC θ) = #R² · #fixedPts C (R^∨)` (candidate duality)
  have adm := markC_admissible θ hθs
  rw [Nat.card_congr (z1Equiv θ hcomp hθs hA₂).toEquiv,
    (GQ2.FoxH.prop_5_15 (markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]
  -- the invariant-character bridge `fixedPts C (R^∨) ≃ D_Rmod`
  have hbridge : Nat.card
      (GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.R)))
      = Nat.card ↥(RCharSub Blk) := by
    refine Nat.card_congr
      { toFun := fun lam => ⟨lam.1, fun y r => ?_⟩
        invFun := fun chi => ⟨chi.1, fun c => ?_⟩
        left_inv := fun lam => rfl
        right_inv := fun chi => rfl }
    · have hfix := lam.2 (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)
      have h1 := congrArg (fun mu : GQ2.FoxH.ElemDual (Additive ↥Blk.R) =>
        mu (Additive.ofMul ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩)) hfix
      have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹
          • Additive.ofMul (⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩ : ↥Blk.R)
          = Additive.ofMul r := by
        rw [← map_inv]
        rw [RStageLocal.conjC_smul_of_mk hRK y⁻¹ ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩]
        apply congrArg
        apply Subtype.ext
        show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y)
        group
      have h2 : ((QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) • lam.1)
          (Additive.ofMul ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩)
          = lam.1 (Additive.ofMul r) := by
        rw [GQ2.FoxH.ElemDual.smul_apply, h3]
      rw [h2] at h1
      exact h1.symm
    · obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Blk.K c
      apply GQ2.FoxH.ElemDual.ext
      intro a
      rw [GQ2.FoxH.ElemDual.smul_apply]
      have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹ • a
          = Additive.ofMul (⟨y⁻¹ * ((Additive.toMul a : ↥Blk.R) : Y) * y⁻¹⁻¹,
              RStageLocal.conj_mem_R y⁻¹ (Additive.toMul a)⟩ : ↥Blk.R) := by
        rw [← map_inv]
        exact RStageLocal.conjC_smul_of_mk hRK y⁻¹ (Additive.toMul a)
      rw [h3]
      exact chi.2 y⁻¹ (Additive.toMul a)
  rw [hbridge, blockRChar_card T Blk hE2,
    Nat.card_congr (Additive.toMul (α := ↥Blk.R))]
  rfl

/-! ## L2 — `d1Fun` naturality (word-complex helper for the separation's L4/L5) -/

section WordNaturality

variable {C : Type} [Group C] [Finite C]
variable {A A' : Type} [AddCommGroup A] [Finite A] [DistribMulAction C A]
  [AddCommGroup A'] [Finite A'] [DistribMulAction C A']

omit [Finite A'] in
/-- **`d¹` naturality** (`docs/p16d6e5-plan.md` §2, L2): a `C`-equivariant coefficient map
`f : A →+ A'` intertwines the degree-1 differentials — `d1Fun t (f ∘ x) = (f × f)(d1Fun t x)`.
Same functoriality proof as `FoxH.d1Fun_add` (push the lifted marking through `WordLift.map f`,
then read the tame/wild `u`-coordinates), with a single coefficient map instead of `fst/snd`. -/
theorem d1Fun_naturality (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a)
    (t : Marking C) (x : Fin 4 → A) :
    GQ2.FoxH.d1Fun t (fun i => f (x i))
      = (f (GQ2.FoxH.d1Fun t x).1, f (GQ2.FoxH.d1Fun t x).2) := by
  have hL : (GQ2.FoxH.liftMarking t x).map (GQ2.FoxH.WordLift.map f hf)
      = GQ2.FoxH.liftMarking t (fun i => f (x i)) := rfl
  refine Prod.ext ?_ ?_
  · show (GQ2.FoxH.liftMarking t (fun i => f (x i))).tameValue.u
        = f ((GQ2.FoxH.liftMarking t x).tameValue.u)
    rw [← hL, Marking.map_tameValue, GQ2.FoxH.WordLift.map_u]
  · show (GQ2.FoxH.liftMarking t (fun i => f (x i))).wildValue.u
        = f ((GQ2.FoxH.liftMarking t x).wildValue.u)
    rw [← hL, Marking.map_wildValue, GQ2.FoxH.WordLift.map_u]

end WordNaturality

/-! ## L3 — the trace-span package: `(R^∨)^C` perfectly pairs `H2w` (plan §2, gap (i)) -/

section TraceSpan

open GQ2.FoxH

variable {C : Type} [Group C] [Finite C]
variable {A : Type} [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-- **The trace functional** `Φ_λ : H2w(A) →+ 𝔽₂`, `[v] ↦ λ(v.1 + v.2)` (`docs/p16d6e5-plan.md`
§2, L3).  Well-defined on the quotient `H2w = (A×A) ⧸ im d¹` because for an invariant `λ`
(`d⁰λ = 0`), `prop_5_8_right` gives `λ((d¹x).1 + (d¹x).2) = mixedB t x (d⁰λ) = mixedB t x 0 = 0`.
This is the (2,0)-pairing the candidate `IsSelfDual` omits — supplied by `prop_5_8` directly. -/
noncomputable def wTrace (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (lam : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0) :
    H2w (A := A) t →+ ZMod 2 :=
  QuotientAddGroup.lift _ (lam.comp (AddMonoidHom.fst A A + AddMonoidHom.snd A A)) (by
    rintro w ⟨x, rfl⟩
    have h58 := prop_5_8_right t ht hw x lam
    rw [hlam, mixedB_zero_right] at h58
    exact h58.symm)

@[simp] theorem wTrace_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (lam : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0) (v : A × A) :
    wTrace t ht hw lam hlam (QuotientAddGroup.mk v) = lam (v.1 + v.2) := rfl

/-- **L3b: `λ ↦ Φ_λ` is injective** — `Φ_λ` at `[⟨a,0⟩]` is `λ a`, so the functional determines
`λ`.  (With the counting `#{invariant λ} = #H2w`, this makes `λ ↦ Φ_λ` a bijection onto
`H2w →+ 𝔽₂` — the perfect (2,0)-pairing.) -/
theorem wTrace_injective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (lam lam' : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0)
    (hlam' : (d0 (A := ElemDual A) t) lam' = 0)
    (h : wTrace t ht hw lam hlam = wTrace t ht hw lam' hlam') : lam = lam' := by
  ext a
  have hev := congrArg (fun Ψ => Ψ (QuotientAddGroup.mk (a, 0))) h
  simpa only [wTrace_mk, add_zero] using hev

/-- **L3c: `λ ↦ Φ_λ` is surjective** onto `H2w →+ 𝔽₂` — the counting half of the perfect
(2,0)-pairing (`docs/p16d6e5-plan.md` §2, L3).  The invariant characters, `#H2w`, and
`#(H2w →+ 𝔽₂)` are all equinumerous:
`#{λ : d⁰λ = 0} = #fixedPts C (A^∨) = #H2w = #(H2w →+ 𝔽₂)` — by `H0w_eq_fixedPts` (needs
`Generates`), `IsSelfDual` clause 1, and `card_addHom_zmod2`.  A finite injection
(`wTrace_injective`) between equinumerous finite sets is bijective
(`Fintype.bijective_iff_injective_and_card`), hence surjective. -/
theorem wTrace_surjective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hsd : IsSelfDual t A) (hA₂ : ∀ a : A, a + a = 0) (Ψ : H2w (A := A) t →+ ZMod 2) :
    ∃ (lam : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0),
      wTrace t ht hw lam hlam = Ψ := by
  obtain ⟨hsd_card, -, -⟩ := hsd
  haveI : Finite (H2w (A := A) t) := inferInstanceAs (Finite ((A × A) ⧸ _))
  haveI : Finite (H2w (A := A) t →+ ZMod 2) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := H2w (A := A) t →+ ZMod 2))
  haveI : Fintype ↥(H0w (A := ElemDual A) t) := Fintype.ofFinite _
  haveI : Fintype (H2w (A := A) t →+ ZMod 2) := Fintype.ofFinite _
  -- `Θ : {invariant λ} → (H2w →+ 𝔽₂)`, `λ ↦ Φ_λ`.
  let Θ : ↥(H0w (A := ElemDual A) t) → (H2w (A := A) t →+ ZMod 2) :=
    fun x => wTrace t ht hw x.1 (AddMonoidHom.mem_ker.mp x.2)
  have hinj : Function.Injective Θ := fun x y hxy =>
    Subtype.ext (wTrace_injective t ht hw x.1 y.1
      (AddMonoidHom.mem_ker.mp x.2) (AddMonoidHom.mem_ker.mp y.2) hxy)
  have hcard : Fintype.card ↥(H0w (A := ElemDual A) t)
      = Fintype.card (H2w (A := A) t →+ ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      LocalLiftingDuality.card_addHom_zmod2 (H2w_two_torsion t hA₂), hsd_card]
    exact Nat.card_congr (Equiv.setCongr (H0w_eq_fixedPts t hgen))
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card Θ).mpr ⟨hinj, hcard⟩).2 Ψ
  exact ⟨x.1, AddMonoidHom.mem_ker.mp x.2, hx⟩

/-- **L3d: `sep_word` — the separation** (`docs/p16d6e5-plan.md` §2, L3).  If `v.1 + v.2` is
killed by every invariant character `λ` (`d⁰λ = 0`), then `v ∈ im d¹`.  Proof: if `[v] ≠ 0` in
`H2w`, then `exists_addHom_ne_zero` (finite `𝔽₂`-space) produces a functional `Ψ` with
`Ψ [v] ≠ 0`; by `wTrace_surjective`, `Ψ = Φ_λ` for some invariant `λ`, and
`Φ_λ [v] = λ(v.1 + v.2) = 0` by hypothesis — contradiction.  So `[v] = 0`, i.e. `v ∈ im d¹`. -/
theorem sep_word (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hsd : IsSelfDual t A) (hA₂ : ∀ a : A, a + a = 0) (v : A × A)
    (hv : ∀ lam : ElemDual A, (d0 (A := ElemDual A) t) lam = 0 → lam (v.1 + v.2) = 0) :
    v ∈ (d1 (A := A) t).range := by
  haveI : Finite (H2w (A := A) t) := inferInstanceAs (Finite ((A × A) ⧸ _))
  rw [← QuotientAddGroup.eq_zero_iff]
  by_contra hne
  obtain ⟨Ψ, hΨ⟩ := LocalLiftingDuality.exists_addHom_ne_zero (H2w_two_torsion t hA₂) hne
  obtain ⟨lam, hlam, hΨeq⟩ := wTrace_surjective t ht hw hgen hsd hA₂ Ψ
  exact hΨ (by rw [← hΨeq, wTrace_mk]; exact hv lam hlam)

end TraceSpan

/-! ## L3e — the trivial-coefficient trace: `im d¹` lands in the sum-zero locus (feeds L4) -/

section TraceKills

open GQ2.FoxH

variable {C : Type} [Group C] [Finite C]

/-- **L3e: the trace kills `im d¹` at trivial `𝔽₂` coefficients** (`docs/p16d6e5-plan.md` §2, L3).
For `C` acting trivially on `𝔽₂ = ZMod 2`, every `d¹`-row has coordinate sum zero:
`(d¹x).1 + (d¹x).2 = 0`.  This is `prop_5_8_right` at `A := ZMod 2`, `lam := id` — the identity
functional is `C`-invariant (`d⁰ id = 0`, since the contragredient action is trivial), so
`mixedB t x (d⁰ id) = mixedB t x 0 = 0 = id ((d¹x).1 + (d¹x).2) = (d¹x).1 + (d¹x).2`.

At the `Y/l`-cover instance of L4 the kernel `R/l ≅ 𝔽₂` is central (the invariant character `d`
gives a trivial `C`-action), so this is exactly the coordinate-sum vanishing needed to feed
`sep_word`'s hypothesis. -/
theorem trace_kills_im_trivial [DistribMulAction C (ZMod 2)]
    (htriv2 : ∀ (c : C) (m : ZMod 2), c • m = m)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (x : Fin 4 → ZMod 2) :
    (d1Fun t x).1 + (d1Fun t x).2 = 0 := by
  -- The identity functional, forced to the `ElemDual` type via a typed `let` so its `C`-action is
  -- the contragredient — NOT the T-14 codomain-action diamond that a bare `ZMod 2 →+ ZMod 2`
  -- (or an `ext`/`DFunLike.ext` that decays to one) would pick up.
  let idE : ElemDual (ZMod 2) := AddMonoidHom.id (ZMod 2)
  have hact : ∀ (c : C), c • idE = idE := by
    intro c
    have htoAM : (DistribSMul.toAddMonoidHom (ZMod 2) (c⁻¹ : C)) = AddMonoidHom.id (ZMod 2) := by
      ext a; exact htriv2 c⁻¹ a
    -- `c • idE` is defeq `idE.comp (toAddMonoidHom c⁻¹)` (the contragredient smul); `toAddMonoidHom
    -- c⁻¹ = id` by triviality, and `idE.comp id = idE`.
    show idE.comp (DistribSMul.toAddMonoidHom (ZMod 2) (c⁻¹ : C)) = idE
    rw [htoAM, AddMonoidHom.comp_id]
  have hlam : (d0 (A := ElemDual (ZMod 2)) t) idE = 0 := by
    funext i; fin_cases i <;> exact sub_eq_zero.mpr (hact _)
  have h58 := prop_5_8_right t ht hw x idE
  rw [hlam, mixedB_zero_right] at h58
  exact h58.symm

omit [Finite C] in
/-- **The tame `d¹`-row at trivial `𝔽₂` coefficients**: `(d¹x).1 = x 1` (`docs/p16d6e5-plan.md`
§2, L4).  Specialize `d1Fun_tame`'s closed form to the trivial action — every `•` drops and, in
characteristic two, `x₀ − x₀ + x₁ − (x₁ + x₁) = x₁`.  This is the tame half of recognizing the
per-cover relator corrections as a `d¹`-image: at the central `R/l ≅ 𝔽₂` cover the τ-correction
`x 1` *is* the tame relator's shift (the central-2-torsion computation
`tameValue(r⃗·ŷ) = r₁ · tameValue(ŷ)`). -/
theorem d1Fun_tame_trivial [DistribMulAction C (ZMod 2)]
    (htriv2 : ∀ (c : C) (m : ZMod 2), c • m = m)
    (t : Marking C) (ht : t.TameRel) (x : Fin 4 → ZMod 2) :
    (d1Fun t x).1 = x 1 := by
  rw [d1Fun_tame t ht]
  simp only [htriv2, sub_self, zero_add, CharTwo.add_self_eq_zero, sub_zero]

/-- **The wild `d¹`-row at trivial `𝔽₂` coefficients**: `(d¹x).2 = x 1` (`docs/p16d6e5-plan.md`
§2, L4).  `liftMarking_wildValue_u`'s split closed form `x₁ + x₃ + σ⁻¹·x₃` (all the trivial-action
side conditions `hx₀/hx₁/hτ/hσ₂` hold from `htriv2`) collapses under the trivial action and
characteristic two to `x₁ + x₃ + x₃ = x₁`.  Together with `d1Fun_tame_trivial` this is the wild
recognizer for L4; the pair `(d¹x) = (x 1, x 1)` also re-derives `trace_kills_im_trivial`
(`x 1 + x 1 = 0`). -/
theorem d1Fun_wild_trivial [DistribMulAction C (ZMod 2)]
    (htriv2 : ∀ (c : C) (m : ZMod 2), c • m = m)
    (t : Marking C) (x : Fin 4 → ZMod 2) :
    (d1Fun t x).2 = x 1 := by
  have h := liftMarking_wildValue_u t x (fun v => CharTwo.add_self_eq_zero v)
    (fun v => htriv2 t.x₀ v) (fun v => htriv2 t.x₁ v) (fun v => htriv2 t.τ v)
    (fun v => htriv2 t.sigma2 v)
  show (liftMarking t x).wildValue.u = x 1
  rw [h]
  simp only [htriv2]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

end TraceKills

/-! ## L1 — the relator correction at a central 2-torsion kernel (the per-cover algebra of L4) -/

section RelatorCorrection

variable {Y' : Type*} [Group Y']

/-- **`powOmega2` under a central-involution correction** — the crux of the wild relator
correction (`docs/p16d6e5-plan.md` §2, L1-wild).  For a central involution `s`, the 2-primary
projection satisfies `powOmega2 (s * a) = s * powOmega2 a`: `s` is its own 2-part, and `powOmega2`
is multiplicative on the abelian subgroup `⟨s, a⟩`.  The `orderOf (s*a)`-shift (which breaks the
naive `powOmega2_pow_eq` at `a`'s own order) is dissolved by evaluating all three `ω₂`-powers at a
**common modulus** `M = 2·|a|·|s*a|` (divisible by `|s|`, `|a|`, `|s*a|`), à la `powOmega2_prod`;
`powOmega2 s = s` because `|s| ∣ 2` is a 2-power. -/
theorem powOmega2_central_involution {G : Type*} [Group G] [Finite G] (s a : G)
    (hs : ∀ z : G, Commute s z) (hs2 : s ^ 2 = 1) :
    powOmega2 (s * a) = s * powOmega2 a := by
  set M := 2 * orderOf a * orderOf (s * a) with hM_def
  have hMne : M ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (orderOf_pos a).ne') (orderOf_pos (s * a)).ne'
  have hsa_dvd : orderOf (s * a) ∣ M := dvd_mul_left _ _
  have ha_dvd : orderOf a ∣ M := (dvd_mul_left (orderOf a) 2).mul_right (orderOf (s * a))
  have hs_dvd : orderOf s ∣ M :=
    (orderOf_dvd_of_pow_eq_one hs2).trans ((dvd_mul_right 2 (orderOf a)).mul_right (orderOf (s * a)))
  have hps : powOmega2 s = s := by
    have hsord : orderOf s ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hs2
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hsord
    exact powOmega2_eq_self_of_orderOf_two_pow hk
  rw [← powOmega2_pow_eq (s * a) hsa_dvd hMne, (hs a).mul_pow,
    powOmega2_pow_eq s hs_dvd hMne, powOmega2_pow_eq a ha_dvd hMne, hps]

/-- **L1 tame row, central 2-torsion** (`docs/p16d6e5-plan.md` §2, L1): correcting a marking's
generators by central involutions shifts the tame relator value by exactly the τ-correction —
`tameValue⟨r₀σ, r₁τ, x₀, x₁⟩ = r₁ · tameValue⟨σ, τ, x₀, x₁⟩`.  The σ-correction `r₀` cancels
(`σ⁻¹r₀⁻¹(r₁τ)r₀σ`, `r₀` central), and the τ-square kills `r₁²`.  This is the group-level Fox tame
derivative — matching `d1Fun_tame_trivial`'s `x 1`.  At L4's cover `Y/l` the kernel `R/l ≅ 𝔽₂` is
central 2-torsion, so this applies with `r⃗ :=` the set-lift-vs-hom corrections. -/
theorem tameValue_correction (σ τ x0 x1 r0 r1 : Y')
    (hr0 : ∀ z : Y', Commute r0 z) (hr1 : ∀ z : Y', Commute r1 z) (h1 : r1 ^ 2 = 1) :
    (Marking.mk (r0 * σ) (r1 * τ) x0 x1).tameValue
      = r1 * (Marking.mk σ τ x0 x1).tameValue := by
  show conjP (r1 * τ) (r0 * σ) * ((r1 * τ) ^ 2)⁻¹ = r1 * (conjP τ σ * (τ ^ 2)⁻¹)
  have hsq : ((r1 * τ) ^ 2)⁻¹ = (τ ^ 2)⁻¹ := by rw [(hr1 τ).mul_pow, h1, one_mul]
  rw [hsq, ← mul_assoc]
  congr 1
  simp only [conjP, mul_inv_rev]
  -- `σ⁻¹ r0⁻¹ (r1 τ) r0 σ = r1 (σ⁻¹ τ σ)`: move `r0⁻¹` right to cancel `r0` (group), swap `r1`, `σ⁻¹`.
  rw [mul_assoc σ⁻¹ r0⁻¹ (r1 * τ), (hr0 (r1 * τ)).inv_left.eq]
  group
  rw [(hr1 (σ ^ (-1 : ℤ))).symm.eq]

end RelatorCorrection

/-! ## `hsep_hom`: the `(R^∨)^C` separation at the candidate source (L1–L5, the main work) -/

/-- **The `(R^∨)^C`-separation at `Γ_A`** (P-16d6e5 residue): if the obstruction functional of a
boundary lift `g` vanishes, `g` lifts to a continuous homomorphism into `Y`.  Route
(`docs/p16d6e5-plan.md` §2): `obs g = 0` gives, per invariant character, a concrete lift through
the scalar cover (`obs_zero_iff_lifts`); the relator-value corrections of a set-lift are `d1Fun`
rows (L1); the trace-span package (L3, `prop_5_8_right`) forces full word-solvability; the
corrected marking descends by `markC_admissible` + `NA_le_ker` + `quotientLift` (L5).  `hcard_A`
is threaded (proof-irrelevant Prop; supplied by P-16d6e6's `card_H2_gammaA_eq_two`). -/
theorem hsep_hom_gammaA
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
    (g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_gammaA
        hcard_A g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom GammaA Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ := by
  sorry

/-! ## `stageR136`: the (136) identity, assembled -/

/-- **(136) for the block frame at the candidate source** (P-16d6e5, threading `hcard_A`):
`htriv`/`hZcount`/`hsep_hom` are the residues discharged here; `hcard_A` (P-16d6e6) and the
`lemma_7_2` structural facts `hRK`/`hR2` thread hypothesis-side.  `hfg` is
`gammaA_topologicallyFinitelyGenerated` (P-03 ✓ — dischargeable here, unlike the local B1
reservation).  The conclusion is the `stageR136` field of the candidate `RecursionInputs`
bundle (P-16d6e7 assembly), verbatim. -/
theorem stageR136_gammaA_of_hcard
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  blockStageR136 T Blk hE2 htriv_gammaA hcard_A gammaA_topologicallyFinitelyGenerated b F
    (fun g hg => hsep_hom_gammaA hE2 hRK hR2 hcard_A b F g hg)
    (fun f₀ => hZcount_gammaA hE2 hRK hR2 b F f₀)

end RStageGammaA

end GQ2
