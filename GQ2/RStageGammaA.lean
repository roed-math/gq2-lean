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

/-- **Conjugation under central corrections** (`docs/p16d6e5-plan.md` §2, L1-wild building block):
`conjP (rₐ·x) (r_g·g) = rₐ · conjP x g` for central `rₐ, r_g` — the conjugating correction `r_g`
cancels (`g⁻¹r_g⁻¹…r_g g`), the conjugated correction `rₐ` survives.  Used for `z0 = conjP x₀ σ₂`,
`x₁^σ`, `dg = conjP d₀ g₀`, and the `x₀^g₀` factor of `h₀`. -/
theorem conjP_central_correction (x g ra rg : Y')
    (hra : ∀ z : Y', Commute ra z) (hrg : ∀ z : Y', Commute rg z) :
    conjP (ra * x) (rg * g) = ra * conjP x g := by
  simp only [conjP, mul_inv_rev]
  rw [mul_assoc g⁻¹ rg⁻¹ (ra * x), (hrg (ra * x)).inv_left.eq]
  group
  rw [(hra (g ^ (-1 : ℤ))).symm.eq]

/-- **Commutators are insensitive to central corrections** (`docs/p16d6e5-plan.md` §2, L1-wild
building block): `commP (rₐ·a) (r_b·b) = commP a b` for central `rₐ, r_b` — both corrections cancel
in the commutator (`a⁻¹rₐ⁻¹ b⁻¹r_b⁻¹ rₐa r_bb`, all central factors pair off).  Used for
`c0 = commP d₀ z₀` and `h_c = commP dg d₀` — these two auxiliary words are correction-free. -/
theorem commP_central_correction (a b ra rb : Y')
    (hra : ∀ z : Y', Commute ra z) (hrb : ∀ z : Y', Commute rb z) :
    commP (ra * a) (rb * b) = commP a b := by
  simp only [commP, mul_inv_rev]
  -- Cancel `ra⁻¹…ra` (move `ra⁻¹` right, `group`), then swap `rb⁻¹` past `a` and cancel `rb⁻¹…rb`.
  rw [mul_assoc a⁻¹ ra⁻¹ (b⁻¹ * rb⁻¹), (hra (b⁻¹ * rb⁻¹)).inv_left.eq]
  group
  rw [mul_assoc (a ^ (-1 : ℤ) * b ^ (-1 : ℤ)) (rb ^ (-1 : ℤ)) a, ((hrb a).zpow_left (-1 : ℤ)).eq]
  group

end RelatorCorrection

/-! ## L1-wild — the auxiliary-word correction chain (mechanical, from the building blocks) -/

section WildCorrection

variable {Y' : Type*} [Group Y'] {t : Marking Y'} {r0 r1 r2 r3 : Y'}

/-- The marking with each generator corrected by a central involution (`docs/p16d6e5-plan.md`
§2, L1).  The wild relator value shifts by exactly `r₁` — proved word-by-word below. -/
def corrMark (t : Marking Y') (r0 r1 r2 r3 : Y') : Marking Y' :=
  ⟨r0 * t.σ, r1 * t.τ, r2 * t.x₀, r3 * t.x₁⟩

@[simp] lemma corrMark_σ : (corrMark t r0 r1 r2 r3).σ = r0 * t.σ := rfl
@[simp] lemma corrMark_τ : (corrMark t r0 r1 r2 r3).τ = r1 * t.τ := rfl
@[simp] lemma corrMark_x₀ : (corrMark t r0 r1 r2 r3).x₀ = r2 * t.x₀ := rfl
@[simp] lemma corrMark_x₁ : (corrMark t r0 r1 r2 r3).x₁ = r3 * t.x₁ := rfl

/-- A product of central involutions is a central involution. -/
private lemma central_mul_comm {a b : Y'} (ha : ∀ z : Y', Commute a z)
    (hb : ∀ z : Y', Commute b z) : ∀ z : Y', Commute (a * b) z := fun z => (ha z).mul_left (hb z)

/-- Two factors sharing the same central-involution correction are jointly correction-free:
`(c·a)(c·b) = a·b`.  Pairs up `h₀`'s six factors. -/
private lemma central_pair {c a b : Y'} (hc : ∀ z : Y', Commute c z) (hcsq : c ^ 2 = 1) :
    (c * a) * (c * b) = a * b := by
  rw [(hc a).symm.mul_mul_mul_comm c b, ← pow_two, hcsq, one_mul]

/-- The square of a product of two central involutions is `1`. -/
private lemma central_mul_sq {a b : Y'} (ha : ∀ z : Y', Commute a z) (ha2 : a ^ 2 = 1)
    (hb2 : b ^ 2 = 1) : (a * b) ^ 2 = 1 := by rw [(ha b).mul_pow, ha2, hb2, mul_one]

/-- `σ₂ = powOmega2 σ` picks up the σ-correction `r₀`. -/
theorem corrMark_sigma2 [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr0sq : r0 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).sigma2 = r0 * t.sigma2 := by
  show powOmega2 ((corrMark t r0 r1 r2 r3).σ) = r0 * powOmega2 t.σ
  rw [corrMark_σ]; exact powOmega2_central_involution r0 t.σ hr0 hr0sq

/-- `u₀ = powOmega2 (x₀τ)` picks up `r₂r₁` (the `x₀`- and `τ`-corrections combine centrally). -/
theorem corrMark_u0 [Finite Y'] (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z)
    (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).u0 = (r2 * r1) * t.u0 := by
  show powOmega2 ((corrMark t r0 r1 r2 r3).x₀ * (corrMark t r0 r1 r2 r3).τ)
    = (r2 * r1) * powOmega2 (t.x₀ * t.τ)
  rw [corrMark_x₀, corrMark_τ, (hr1 t.x₀).symm.mul_mul_mul_comm r2 t.τ]
  exact powOmega2_central_involution (r2 * r1) (t.x₀ * t.τ)
    (central_mul_comm hr2 hr1) (central_mul_sq hr2 hr2sq hr1sq)

/-- `u₁ = powOmega2 (x₁τ)` picks up `r₃r₁`. -/
theorem corrMark_u1 [Finite Y'] (hr1 : ∀ z : Y', Commute r1 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr1sq : r1 ^ 2 = 1) (hr3sq : r3 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).u1 = (r3 * r1) * t.u1 := by
  show powOmega2 ((corrMark t r0 r1 r2 r3).x₁ * (corrMark t r0 r1 r2 r3).τ)
    = (r3 * r1) * powOmega2 (t.x₁ * t.τ)
  rw [corrMark_x₁, corrMark_τ, (hr1 t.x₁).symm.mul_mul_mul_comm r3 t.τ]
  exact powOmega2_central_involution (r3 * r1) (t.x₁ * t.τ)
    (central_mul_comm hr3 hr1) (central_mul_sq hr3 hr3sq hr1sq)

/-- `g₀ = σ₂²` is correction-free (`r₀²` kills the σ₂-correction). -/
theorem corrMark_g0 [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr0sq : r0 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).g0 = t.g0 := by
  show (corrMark t r0 r1 r2 r3).sigma2 ^ 2 = t.sigma2 ^ 2
  rw [corrMark_sigma2 hr0 hr0sq, (hr0 t.sigma2).mul_pow, hr0sq, one_mul]

/-- `z₀ = x₀^σ₂ = conjP x₀ σ₂` picks up `r₂` (the conjugating σ₂-correction `r₀` cancels). -/
theorem corrMark_z0 [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr2 : ∀ z : Y', Commute r2 z)
    (hr0sq : r0 ^ 2 = 1) : (corrMark t r0 r1 r2 r3).z0 = r2 * t.z0 := by
  show conjP (corrMark t r0 r1 r2 r3).x₀ (corrMark t r0 r1 r2 r3).sigma2 = r2 * conjP t.x₀ t.sigma2
  rw [corrMark_x₀, corrMark_sigma2 hr0 hr0sq]
  exact conjP_central_correction t.x₀ t.sigma2 r2 r0 hr2 hr0

/-- `d₀ = u₀ x₀⁻¹` picks up `r₁` (the `r₂` from `u₀` meets `r₂⁻¹` from `x₀⁻¹`). -/
theorem corrMark_d0 [Finite Y'] (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z)
    (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).d0 = r1 * t.d0 := by
  show (corrMark t r0 r1 r2 r3).u0 * (corrMark t r0 r1 r2 r3).x₀⁻¹ = r1 * (t.u0 * t.x₀⁻¹)
  rw [corrMark_u0 hr1 hr2 hr1sq hr2sq, corrMark_x₀, mul_inv_rev,
    show r2 * r1 * t.u0 * (t.x₀⁻¹ * r2⁻¹) = r2 * (r1 * t.u0 * t.x₀⁻¹) * r2⁻¹ from by group,
    (hr2 (r1 * t.u0 * t.x₀⁻¹)).eq]
  group

/-- Conjugation by a correction-free element (the `rg = 1` case of `conjP_central_correction`):
`conjP (rₐ·x) g = rₐ · conjP x g`.  Used for `dg = conjP d₀ g₀` and `h₀`'s `x₀^g₀` factor. -/
theorem conjP_central_left (x g ra : Y') (hra : ∀ z : Y', Commute ra z) :
    conjP (ra * x) g = ra * conjP x g := by
  have h := conjP_central_correction x g ra 1 hra (fun z => Commute.one_left z)
  rwa [one_mul] at h

/-- `c₀ = commP d₀ z₀` is correction-free (`commP` kills the `r₁`, `r₂` corrections). -/
theorem corrMark_c0 [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr1 : ∀ z : Y', Commute r1 z)
    (hr2 : ∀ z : Y', Commute r2 z) (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).c0 = t.c0 := by
  show commP (corrMark t r0 r1 r2 r3).d0 (corrMark t r0 r1 r2 r3).z0 = commP t.d0 t.z0
  rw [corrMark_d0 hr1 hr2 hr1sq hr2sq, corrMark_z0 hr0 hr2 hr0sq]
  exact commP_central_correction t.d0 t.z0 r1 r2 hr1 hr2

/-- `dg = d₀^g₀ = conjP d₀ g₀` picks up `r₁` (from `d₀`; `g₀` is correction-free). -/
theorem corrMark_dg [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr1 : ∀ z : Y', Commute r1 z)
    (hr2 : ∀ z : Y', Commute r2 z) (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).dg = r1 * t.dg := by
  show conjP (corrMark t r0 r1 r2 r3).d0 (corrMark t r0 r1 r2 r3).g0 = r1 * conjP t.d0 t.g0
  rw [corrMark_d0 hr1 hr2 hr1sq hr2sq, corrMark_g0 hr0 hr0sq]
  exact conjP_central_left t.d0 t.g0 r1 hr1

/-- `h_c = commP dg d₀` is correction-free (`commP` kills the two `r₁` corrections). -/
theorem corrMark_hc [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr1 : ∀ z : Y', Commute r1 z)
    (hr2 : ∀ z : Y', Commute r2 z) (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).hc = t.hc := by
  show commP (corrMark t r0 r1 r2 r3).dg (corrMark t r0 r1 r2 r3).d0 = commP t.dg t.d0
  rw [corrMark_dg hr0 hr1 hr2 hr0sq hr1sq hr2sq, corrMark_d0 hr1 hr2 hr1sq hr2sq]
  exact commP_central_correction t.dg t.d0 r1 r1 hr1 hr1

/-- `h₀ = x₀^g₀·x₀·dg·d₀·d₀²·h_c` is correction-free — the six factors pair into three
correction-free `central_pair`s: `(r₂·,r₂·)`, `(r₁·,r₁·)`, and `(d₀², h_c)` (already free). -/
theorem corrMark_h0 [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z) (hr1 : ∀ z : Y', Commute r1 z)
    (hr2 : ∀ z : Y', Commute r2 z) (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).h0 = t.h0 := by
  show conjP (corrMark t r0 r1 r2 r3).x₀ (corrMark t r0 r1 r2 r3).g0 * (corrMark t r0 r1 r2 r3).x₀
      * (corrMark t r0 r1 r2 r3).dg * (corrMark t r0 r1 r2 r3).d0 * (corrMark t r0 r1 r2 r3).d0 ^ 2
      * (corrMark t r0 r1 r2 r3).hc
    = conjP t.x₀ t.g0 * t.x₀ * t.dg * t.d0 * t.d0 ^ 2 * t.hc
  rw [corrMark_g0 hr0 hr0sq, corrMark_x₀, corrMark_dg hr0 hr1 hr2 hr0sq hr1sq hr2sq,
    corrMark_d0 hr1 hr2 hr1sq hr2sq, corrMark_hc hr0 hr1 hr2 hr0sq hr1sq hr2sq,
    conjP_central_left t.x₀ t.g0 r2 hr2, (hr1 t.d0).mul_pow, hr1sq, one_mul,
    show r2 * conjP t.x₀ t.g0 * (r2 * t.x₀) * (r1 * t.dg) * (r1 * t.d0) * t.d0 ^ 2 * t.hc
      = (r2 * conjP t.x₀ t.g0) * (r2 * t.x₀) * ((r1 * t.dg) * (r1 * t.d0)) * (t.d0 ^ 2 * t.hc)
      from by group,
    central_pair hr2 hr2sq, central_pair hr1 hr1sq]
  group

/-- **L1 wild row, central 2-torsion** (`docs/p16d6e5-plan.md` §2, L1-wild): the wild relator value
shifts by exactly the τ-correction `r₁` — `wildValue(r⃗·ŷ) = r₁ · wildValue ŷ`.  `h₀` and `c₀` are
correction-free; `u₁⁻¹` contributes `(r₃r₁)⁻¹` and `x₁^σ` contributes `r₃`, whose `r₃`'s cancel,
leaving `r₁⁻¹ = r₁`.  Matches `d1Fun_wild_trivial`'s `x 1`. -/
theorem wildValue_correction [Finite Y'] (hr0 : ∀ z : Y', Commute r0 z)
    (hr1 : ∀ z : Y', Commute r1 z) (hr2 : ∀ z : Y', Commute r2 z) (hr3 : ∀ z : Y', Commute r3 z)
    (hr0sq : r0 ^ 2 = 1) (hr1sq : r1 ^ 2 = 1) (hr2sq : r2 ^ 2 = 1) (hr3sq : r3 ^ 2 = 1) :
    (corrMark t r0 r1 r2 r3).wildValue = r1 * t.wildValue := by
  have hr1inv : r1⁻¹ = r1 := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hr1sq])
  show (corrMark t r0 r1 r2 r3).h0 * (corrMark t r0 r1 r2 r3).u1⁻¹
      * conjP (corrMark t r0 r1 r2 r3).x₁ (corrMark t r0 r1 r2 r3).σ * (corrMark t r0 r1 r2 r3).c0
    = r1 * (t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0)
  rw [corrMark_h0 hr0 hr1 hr2 hr0sq hr1sq hr2sq, corrMark_u1 hr1 hr3 hr1sq hr3sq, corrMark_x₁,
    corrMark_σ, corrMark_c0 hr0 hr1 hr2 hr0sq hr1sq hr2sq,
    conjP_central_correction t.x₁ t.σ r3 r0 hr3 hr0, mul_inv_rev, mul_inv_rev, hr1inv]
  -- centrals `r1, r3⁻¹, r3`: cancel `r3⁻¹·r3`, pull `r1` to the front.
  rw [show t.h0 * (t.u1⁻¹ * (r1 * r3⁻¹)) * (r3 * t.x₁ ^c t.σ) * t.c0
      = t.h0 * t.u1⁻¹ * r1 * (r3⁻¹ * r3) * (t.x₁ ^c t.σ) * t.c0 from by group,
    inv_mul_cancel, mul_one, (hr1 (t.h0 * t.u1⁻¹)).symm.eq]
  group

end WildCorrection

/-! ## Relator death along any continuous hom from `Γ_A`; marking extensionality (L4/L5) -/

section PushDescent

/-- Four-field extensionality for markings. -/
theorem marking_ext {G : Type*} {s t : Marking G} (h0 : s.σ = t.σ) (h1 : s.τ = t.τ)
    (h2 : s.x₀ = t.x₀) (h3 : s.x₁ = t.x₁) : s = t := by
  cases s; cases t
  cases h0; cases h1; cases h2; cases h3
  rfl

variable {G' : Type} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] [Finite G']

omit [DiscreteTopology G'] [Finite G'] in
/-- **Relators die along any continuous hom from `Γ_A`, tame** (`docs/p16d6e5-plan.md` §2, L4 —
NO surjectivity, unlike `markC_admissible`): the pushed marking of any `f : Γ_A →ₜ* G'` satisfies
the tame relation, because the tame relator word lies in `N_A` (`tameRelator_mem_NA`). -/
theorem push_tameRel (f : ContinuousMonoidHom GA G') : (Marking.push f).TameRel :=
  (Marking.map_tameRelator_eq_one_iff (f.comp (quotientMk NA)) univMarking).mp <| by
    show f (quotientMk NA univMarking.tameRelator) = 1
    rw [(quotientMk_eq_one_iff NA).mpr tameRelator_mem_NA, map_one]

/-- **Relators die along any continuous hom from `Γ_A`, wild** (`wildRelator_mem_NA`). -/
theorem push_wildRel (f : ContinuousMonoidHom GA G') : (Marking.push f).WildRel :=
  (Marking.map_wildRelator_eq_one_iff (f.comp (quotientMk NA)) univMarking).mp <| by
    show f (quotientMk NA univMarking.wildRelator) = 1
    rw [(quotientMk_eq_one_iff NA).mpr wildRelator_mem_NA, map_one]

end PushDescent

/-! ## The `WordLift` multiplication/base-change calculus — the general relator correction

The landed L1 (`tameValue_correction`/`wildValue_correction`) handles corrections by **central**
involutions — the per-cover algebra of L4.  L5 additionally needs the **general** correction at
`Y` itself (corrections in the non-central `R`), which factors through the lift group
`A ⋊ Y = WordLift`: evaluating the relators at `liftMarking t x` and pushing through the
*multiplication homomorphism* `(u, g) ↦ j u · g` (a hom exactly because the action is realized
by conjugation) yields `value(j(x)·t) = j(d¹-row) · value(t)` — the group-level Fox rows, with
no new word expansion.  `d1Fun_base_change` transports the `d¹`-row between the `Y`-conjugation
action and the `C = Y/K`-action of the word complex (`sep_word` lives at `markC θ : Marking C`). -/

section WordLiftMul

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]

/-- The base projection `A ⋊ G →* G` of the lift group. -/
def projW : WordLift A G →* G where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `liftMarking` projects back onto the base marking (structure eta). -/
theorem liftMarking_map_projW (t : Marking G) (x : Fin 4 → A) :
    (liftMarking t x).map projW = t := rfl

/-- The base coordinate of the evaluated tame relator is the base tame relator value. -/
theorem liftMarking_tameValue_g (t : Marking G) (x : Fin 4 → A) :
    ((liftMarking t x).tameValue).g = t.tameValue := by
  have h := Marking.map_tameValue (projW (A := A) (G := G)) (liftMarking t x)
  rw [liftMarking_map_projW] at h
  exact h.symm

/-- The base coordinate of the evaluated wild relator (finite: the `ω₂`-push). -/
theorem liftMarking_wildValue_g [Finite G] [Finite A] (t : Marking G) (x : Fin 4 → A) :
    ((liftMarking t x).wildValue).g = t.wildValue := by
  have h := Marking.map_wildValue (projW (A := A) (G := G)) (liftMarking t x)
  rw [liftMarking_map_projW] at h
  exact h.symm

/-- **The multiplication homomorphism** `A ⋊ G →* G` of a conjugation-realized coefficient
module: `(u, g) ↦ j u · g`, for `j : A → G` multiplicative with `j (g • a) = g · (j a) · g⁻¹`. -/
def mulW (j : A → G) (hjmul : ∀ a b : A, j (a + b) = j a * j b)
    (hjconj : ∀ (g : G) (a : A), j (g • a) = g * j a * g⁻¹) : WordLift A G →* G where
  toFun p := j p.u * p.g
  map_one' := by
    have hj0 : j 0 = 1 := by
      have h := hjmul 0 0
      rw [add_zero] at h
      exact left_eq_mul.mp h
    show j (0 : A) * (1 : G) = 1
    rw [hj0, one_mul]
  map_mul' p q := by
    show j (p.u + p.g • q.u) * (p.g * q.g) = j p.u * p.g * (j q.u * q.g)
    rw [hjmul, hjconj]
    group

/-- **The general relator correction, tame**: left-multiplying a marking's generators by the
`j`-realizations of coefficients `x` multiplies the tame relator value by `j` of the tame
`d¹`-row.  (Evaluate the relator in `A ⋊ G` and push through `mulW`.) -/
theorem corrected_tameValue (j : A → G) (hjmul : ∀ a b : A, j (a + b) = j a * j b)
    (hjconj : ∀ (g : G) (a : A), j (g • a) = g * j a * g⁻¹) (t : Marking G) (x : Fin 4 → A) :
    (Marking.mk (j (x 0) * t.σ) (j (x 1) * t.τ) (j (x 2) * t.x₀) (j (x 3) * t.x₁)).tameValue
      = j ((d1Fun t x).1) * t.tameValue := by
  have hmark : (liftMarking t x).map (mulW j hjmul hjconj)
      = Marking.mk (j (x 0) * t.σ) (j (x 1) * t.τ) (j (x 2) * t.x₀) (j (x 3) * t.x₁) := rfl
  rw [← hmark, Marking.map_tameValue]
  show j ((liftMarking t x).tameValue).u * ((liftMarking t x).tameValue).g = _
  rw [liftMarking_tameValue_g]
  rfl

/-- **The general relator correction, wild.** -/
theorem corrected_wildValue [Finite G] [Finite A] (j : A → G)
    (hjmul : ∀ a b : A, j (a + b) = j a * j b)
    (hjconj : ∀ (g : G) (a : A), j (g • a) = g * j a * g⁻¹) (t : Marking G) (x : Fin 4 → A) :
    (Marking.mk (j (x 0) * t.σ) (j (x 1) * t.τ) (j (x 2) * t.x₀) (j (x 3) * t.x₁)).wildValue
      = j ((d1Fun t x).2) * t.wildValue := by
  have hmark : (liftMarking t x).map (mulW j hjmul hjconj)
      = Marking.mk (j (x 0) * t.σ) (j (x 1) * t.τ) (j (x 2) * t.x₀) (j (x 3) * t.x₁) := rfl
  rw [← hmark, Marking.map_wildValue]
  show j ((liftMarking t x).wildValue).u * ((liftMarking t x).wildValue).g = _
  rw [liftMarking_wildValue_g]
  rfl

/-- Base change of the lift group along `f : G →* C` when the `G`-action is the `f`-pullback. -/
def baseW {C : Type*} [Group C] [DistribMulAction C A] (f : G →* C)
    (hcompat : ∀ (g : G) (a : A), g • a = f g • a) : WordLift A G →* WordLift A C where
  toFun p := ⟨p.u, f p.g⟩
  map_one' := WordLift.ext rfl (map_one f)
  map_mul' p q := WordLift.ext
    (by show p.u + p.g • q.u = p.u + f p.g • q.u; rw [hcompat]) (map_mul f _ _)

/-- **`d¹` base change**: the word differential only sees the action, so it is computed by the
pushed marking — `d1Fun (t.map f) x = d1Fun t x` when the `G`-action is pulled back along `f`. -/
theorem d1Fun_base_change [Finite G] [Finite A] {C : Type*} [Group C] [DistribMulAction C A]
    (f : G →* C) (hcompat : ∀ (g : G) (a : A), g • a = f g • a) (t : Marking G) (x : Fin 4 → A) :
    d1Fun (t.map f) x = d1Fun t x := by
  have hmark : (liftMarking t x).map (baseW f hcompat) = liftMarking (t.map f) x := rfl
  refine Prod.ext ?_ ?_
  · show ((liftMarking (t.map f) x).tameValue).u = ((liftMarking t x).tameValue).u
    rw [← hmark, Marking.map_tameValue]
    rfl
  · show ((liftMarking (t.map f) x).wildValue).u = ((liftMarking t x).wildValue).u
    rw [← hmark, Marking.map_wildValue]
    rfl

end WordLiftMul

/-! ## L4 core: a cover lift forces equal reduced relator values -/

section CoverLift

variable {B0 : Type} [Group B0] [Finite B0] [TopologicalSpace B0] [DiscreteTopology B0]

omit [TopologicalSpace Y] [DiscreteTopology Y] [DiscreteTopology B0] in
/-- **The per-cover L4 core** (`docs/p16d6e5-plan.md` §2, L4), abstractly over a bare central
cover: if `g_B` lifts through `Q` (via `gc`), then any set-lift marking `tY` of `g_B` has equal
tame and wild relator values after reduction along `red`.  Both `tY.map red` and the lift's
pushed marking cover `g_B`'s marking, so they differ by corrections in the **central 2-torsion**
kernel (`CentralCover.central`/`z_sq`); the landed L1 (`tameValue_correction`/
`wildValue_correction`) evaluates both reduced relator values to the same `r̄₁`. -/
private theorem redValues_eq_of_coverLift (Q : CentralCover B0) (piB : Y →* B0)
    (red : Y →* Q.cover) (hred_p : Q.p.comp red = piB)
    (gB : ContinuousMonoidHom GA B0)
    (gc : ContinuousMonoidHom GA Q.cover) (hgc : ∀ γ, Q.p (gc γ) = gB γ)
    (tY : Marking Y) (hproj : tY.map piB = Marking.push gB) :
    red tY.tameValue = red tY.wildValue := by
  have hred_p' : ∀ y : Y, Q.p (red y) = piB y := fun y => DFunLike.congr_fun hred_p y
  -- the lift's marking; its relators die (the relator words lie in `N_A`)
  have htame1 : (Marking.push gc).tameValue = 1 :=
    (Marking.tameValue_eq_one_iff _).mpr (push_tameRel gc)
  have hwild1 : (Marking.push gc).wildValue = 1 :=
    (Marking.wildValue_eq_one_iff _).mpr (push_wildRel gc)
  -- both markings cover `g_B`'s marking: the field discrepancies live in `ker Q.p`
  have hpr : ∀ (a : Y) (w : Q.cover), Q.p (red a) = Q.p w → red a * w⁻¹ ∈ Q.p.ker := by
    intro a w h
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hσ' : Q.p (red tY.σ) = Q.p (Marking.push gc).σ := by
    rw [hred_p']
    have h1 : piB tY.σ = (Marking.push gB).σ := congrArg Marking.σ hproj
    rw [h1]
    exact (hgc gammaGen.σ).symm
  have hτ' : Q.p (red tY.τ) = Q.p (Marking.push gc).τ := by
    rw [hred_p']
    have h1 : piB tY.τ = (Marking.push gB).τ := congrArg Marking.τ hproj
    rw [h1]
    exact (hgc gammaGen.τ).symm
  have hx₀' : Q.p (red tY.x₀) = Q.p (Marking.push gc).x₀ := by
    rw [hred_p']
    have h1 : piB tY.x₀ = (Marking.push gB).x₀ := congrArg Marking.x₀ hproj
    rw [h1]
    exact (hgc gammaGen.x₀).symm
  have hx₁' : Q.p (red tY.x₁) = Q.p (Marking.push gc).x₁ := by
    rw [hred_p']
    have h1 : piB tY.x₁ = (Marking.push gB).x₁ := congrArg Marking.x₁ hproj
    rw [h1]
    exact (hgc gammaGen.x₁).symm
  have hmem0 : red tY.σ * ((Marking.push gc).σ)⁻¹ ∈ Q.p.ker := hpr tY.σ _ hσ'
  have hmem1 : red tY.τ * ((Marking.push gc).τ)⁻¹ ∈ Q.p.ker := hpr tY.τ _ hτ'
  have hmem2 : red tY.x₀ * ((Marking.push gc).x₀)⁻¹ ∈ Q.p.ker := hpr tY.x₀ _ hx₀'
  have hmem3 : red tY.x₁ * ((Marking.push gc).x₁)⁻¹ ∈ Q.p.ker := hpr tY.x₁ _ hx₁'
  -- kernel elements are central involutions (`⟨z⟩`, `z` central of square one)
  have hcen : ∀ w : Q.cover, w ∈ Q.p.ker → ∀ z : Q.cover, Commute w z := by
    intro w hw z
    rw [Q.ker_eq] at hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact Commute.zpow_left (Q.central z) n
  have hsq : ∀ w : Q.cover, w ∈ Q.p.ker → w ^ 2 = 1 := by
    intro w hw
    rw [pow_two]
    exact Q.sq_eq_one_of_mem_ker hw
  -- the reduced set-lift marking is the corrected lift marking
  have hcorr : tY.map red = corrMark (Marking.push gc)
      (red tY.σ * ((Marking.push gc).σ)⁻¹) (red tY.τ * ((Marking.push gc).τ)⁻¹)
      (red tY.x₀ * ((Marking.push gc).x₀)⁻¹) (red tY.x₁ * ((Marking.push gc).x₁)⁻¹) := by
    refine marking_ext ?_ ?_ ?_ ?_
    · exact (inv_mul_cancel_right _ _).symm
    · exact (inv_mul_cancel_right _ _).symm
    · exact (inv_mul_cancel_right _ _).symm
    · exact (inv_mul_cancel_right _ _).symm
  -- both reduced relator values are the τ-correction `r̄₁` (L1 at the central 2-torsion kernel)
  have hredT : red tY.tameValue = red tY.τ * ((Marking.push gc).τ)⁻¹ := by
    have h := Marking.map_tameValue red tY
    rw [hcorr] at h
    rw [← h,
      show corrMark (Marking.push gc) (red tY.σ * ((Marking.push gc).σ)⁻¹)
          (red tY.τ * ((Marking.push gc).τ)⁻¹) (red tY.x₀ * ((Marking.push gc).x₀)⁻¹)
          (red tY.x₁ * ((Marking.push gc).x₁)⁻¹)
        = Marking.mk (red tY.σ * ((Marking.push gc).σ)⁻¹ * (Marking.push gc).σ)
            (red tY.τ * ((Marking.push gc).τ)⁻¹ * (Marking.push gc).τ)
            (red tY.x₀ * ((Marking.push gc).x₀)⁻¹ * (Marking.push gc).x₀)
            (red tY.x₁ * ((Marking.push gc).x₁)⁻¹ * (Marking.push gc).x₁) from rfl,
      tameValue_correction _ _ _ _ _ _ (hcen _ hmem0) (hcen _ hmem1) (hsq _ hmem1),
      show (Marking.mk (Marking.push gc).σ (Marking.push gc).τ
            (red tY.x₀ * ((Marking.push gc).x₀)⁻¹ * (Marking.push gc).x₀)
            (red tY.x₁ * ((Marking.push gc).x₁)⁻¹ * (Marking.push gc).x₁)).tameValue
          = (Marking.push gc).tameValue from rfl,
      htame1, mul_one]
  have hredW : red tY.wildValue = red tY.τ * ((Marking.push gc).τ)⁻¹ := by
    have h := Marking.map_wildValue red tY
    rw [hcorr] at h
    rw [← h,
      wildValue_correction (hcen _ hmem0) (hcen _ hmem1) (hcen _ hmem2) (hcen _ hmem3)
        (hsq _ hmem0) (hsq _ hmem1) (hsq _ hmem2) (hsq _ hmem3),
      hwild1, mul_one]
  rw [hredT, hredW]

end CoverLift

/-! ## L5 descent: a relator-free covering marking of `Y` descends from `Γ_A` -/

section Descend

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [TopologicalSpace E] [DiscreteTopology E] [Finite E] in
/-- **L5, the descent** (`docs/p16d6e5-plan.md` §2, L5): a marking of `Y` that covers `g_B`'s
marking through `π_B` and kills both relators descends to a continuous `φ : Γ_A → Y` with
`π_B ∘ φ = g_B`.  The marking generates a subgroup `J ≤ Y` on which it is **admissible**
(`Generates` by construction; `TameRel`/`WildRel` by subtype injectivity; `Pro2Core` pointwise —
`qJ = π_B ∘ ι` maps the normal closure into `g_B`'s admissible one and the kernel is `R`,
2-torsion by `hR2`), hence `Marking.descend` applies; the projection identity holds because two
`F₄`-classified homs with equal pushed markings agree (`toHom_hom_univMarking_map`). -/
private theorem lift_of_relatorFree_marking (hE2 : ∀ e : E, e ^ 2 = 1)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (gB : ContinuousMonoidHom GA (blockFrameImpl T Blk hE2).YB)
    (hsurj : Function.Surjective gB)
    (tHat : Marking Y)
    (hproj : tHat.map (blockFrameImpl T Blk hE2).piB = Marking.push gB)
    (htame : tHat.TameRel) (hwild : tHat.WildRel) :
    ∃ φ : ContinuousMonoidHom GammaA Y,
      ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = gB γ := by
  classical
  -- the generated subgroup and its marking
  set J : Subgroup Y := Subgroup.closure {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} with hJ
  have hmemσ : tHat.σ ∈ J := Subgroup.subset_closure (by simp)
  have hmemτ : tHat.τ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₀ : tHat.x₀ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₁ : tHat.x₁ ∈ J := Subgroup.subset_closure (by simp)
  set tJ : Marking ↥J :=
    ⟨⟨tHat.σ, hmemσ⟩, ⟨tHat.τ, hmemτ⟩, ⟨tHat.x₀, hmemx₀⟩, ⟨tHat.x₁, hmemx₁⟩⟩ with htJ
  have hmapJ : tJ.map J.subtype = tHat := by
    refine marking_ext ?_ ?_ ?_ ?_ <;> rfl
  -- the relations, by subtype injectivity
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
  -- generation: the closure of the generators inside their own closure is everything
  have hgenJ : tJ.Generates := by
    show Subgroup.closure {tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} = ⊤
    have hpre : ({tJ.σ, tJ.τ, tJ.x₀, tJ.x₁} : Set ↥J)
        = ((↑) : ↥J → Y) ⁻¹' {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} := by
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
  -- the 2-core, pointwise: push into `g_B`'s admissible marking, kernel-side `R` is 2-torsion
  have hcoreJ : tJ.Pro2Core := by
    show IsPGroup 2 (Subgroup.normalClosure {tJ.x₀, tJ.x₁})
    have hadmB : (Marking.push gB).Admissible := Marking.push_admissible gB hsurj
    set qJ : ↥J →* (blockFrameImpl T Blk hE2).YB :=
      ((blockFrameImpl T Blk hE2).piB).comp J.subtype with hqJ
    haveI hNB : (Subgroup.normalClosure
        {(Marking.push gB).x₀, (Marking.push gB).x₁}).Normal := Subgroup.normalClosure_normal
    haveI hNBc : ((Subgroup.normalClosure
        {(Marking.push gB).x₀, (Marking.push gB).x₁}).comap qJ).Normal := hNB.comap qJ
    have hcomap : ({tJ.x₀, tJ.x₁} : Set ↥J) ⊆
        ((Subgroup.normalClosure
          {(Marking.push gB).x₀, (Marking.push gB).x₁}).comap qJ : Set ↥J) := by
      rintro z hz
      rcases hz with rfl | hz
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        have h1 : qJ tJ.x₀ = (Marking.push gB).x₀ := congrArg Marking.x₀ hproj
        rw [h1]
        exact Subgroup.subset_normalClosure (by simp)
      · rcases hz with rfl
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        have h1 : qJ tJ.x₁ = (Marking.push gB).x₁ := congrArg Marking.x₁ hproj
        rw [h1]
        exact Subgroup.subset_normalClosure (by simp)
    have hle := Subgroup.normalClosure_le_normal hcomap
    intro n
    have hmemNB : qJ n.1 ∈ Subgroup.normalClosure
        {(Marking.push gB).x₀, (Marking.push gB).x₁} :=
      Subgroup.mem_comap.mp (hle n.2)
    obtain ⟨k, hk⟩ := hadmB.2.2.2 ⟨qJ n.1, hmemNB⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (qJ n.1) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    -- the `Y`-value: the `2^k`-th power lands in `R = ker π_B`, whose elements square to `1`
    have hYval : ((n.1 : Y)) ^ 2 ^ (k + 1) = 1 := by
      have hmemR : ((n.1 : Y)) ^ 2 ^ k ∈ Blk.R := by
        rw [← (blockFrameImpl T Blk hE2).ker_piB, MonoidHom.mem_ker, map_pow]
        exact hk'
      rw [pow_succ, pow_mul, pow_two]
      exact hR2 _ hmemR
    exact Subtype.val_injective (by
      simpa using Subtype.val_injective (by simpa using hYval :
        ((n.1 ^ 2 ^ (k + 1) : ↥J) : Y) = ((1 : ↥J) : Y)))
  have hadmJ : tJ.Admissible := ⟨hgenJ, htameJ, hwildJ, hcoreJ⟩
  -- descend and project
  set φY : ContinuousMonoidHom ↥J Y := ⟨J.subtype, continuous_subtype_val⟩ with hφY
  refine ⟨φY.comp (Marking.descend tJ hadmJ), ?_⟩
  intro γ
  obtain ⟨w, rfl⟩ := quotientMk_surjective NA γ
  -- both sides are `F₄`-classified with the same pushed marking
  set c₁ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (blockFrameImpl T Blk hE2).YB :=
    (⟨(blockFrameImpl T Blk hE2).piB, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom Y (blockFrameImpl T Blk hE2).YB).comp
      (φY.comp (Marking.classify tJ)) with hc₁
  set c₂ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (blockFrameImpl T Blk hE2).YB :=
    gB.comp (quotientMk NA) with hc₂
  have hclassify : univMarking.map (Marking.classify tJ).toMonoidHom = tJ :=
    univMarking_map_toHom (P := ProfiniteGrp.of ↥J) tJ
  have hpush : univMarking.map c₁.toMonoidHom = univMarking.map c₂.toMonoidHom := by
    refine marking_ext ?_ ?_ ?_ ?_
    · have h1 : (Marking.classify tJ) univMarking.σ = tJ.σ := congrArg Marking.σ hclassify
      show (blockFrameImpl T Blk hE2).piB (φY ((Marking.classify tJ) univMarking.σ))
        = gB (quotientMk NA univMarking.σ)
      rw [h1]
      exact congrArg Marking.σ hproj
    · have h1 : (Marking.classify tJ) univMarking.τ = tJ.τ := congrArg Marking.τ hclassify
      show (blockFrameImpl T Blk hE2).piB (φY ((Marking.classify tJ) univMarking.τ))
        = gB (quotientMk NA univMarking.τ)
      rw [h1]
      exact congrArg Marking.τ hproj
    · have h1 : (Marking.classify tJ) univMarking.x₀ = tJ.x₀ := congrArg Marking.x₀ hclassify
      show (blockFrameImpl T Blk hE2).piB (φY ((Marking.classify tJ) univMarking.x₀))
        = gB (quotientMk NA univMarking.x₀)
      rw [h1]
      exact congrArg Marking.x₀ hproj
    · have h1 : (Marking.classify tJ) univMarking.x₁ = tJ.x₁ := congrArg Marking.x₁ hclassify
      show (blockFrameImpl T Blk hE2).piB (φY ((Marking.classify tJ) univMarking.x₁))
        = gB (quotientMk NA univMarking.x₁)
      rw [h1]
      exact congrArg Marking.x₁ hproj
  have hc : c₁ = c₂ := by
    have h1 := Marking.toHom_hom_univMarking_map c₁
    have h2 := Marking.toHom_hom_univMarking_map c₂
    rw [← h1, ← h2, hpush]
  exact DFunLike.congr_fun hc w

end Descend

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
