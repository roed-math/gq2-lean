import GQ2.RStageLocal
import GQ2.WordCohBridge
import GQ2.HalfTorsorGammaA
import GQ2.FinitelyGenerated

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
