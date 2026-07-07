import GQ2.RadicalEdgeBridge
import GQ2.BlockFrameBounds
import GQ2.FinitelyGenerated

/-!
# P-17i infrastructure: the `M`-stage lane of the §9 master induction

`thm_4_2`'s `R = ⊥` lane applies `mStage_partition` (P-17f) to the block frame at both sources
and solves the two partition identities against the induction hypothesis.  This file provides
the lane's inputs (design note `docs/section9-extraction.md` §P-17i; handoff
`docs/p17i-handoff.md` §5.2):

* **target transports** — `exactImageCount_congr` (count invariance along an iso of marked
  targets), the `⊤`-stratum evaluation `SectionEight.exactImageCountOn_top`, and the `R = ⊥`
  collapse `SectionEight.RecursionFrame.exactImageCount_TB_of_R_bot` (`π_B` is then an iso, so
  `e(𝒴_B) = e(𝒴)` — the design note's "`R = ⊥ ⟹ piB` iso" transport);
* **the degenerate-head case** — `exactImageCount_eq_zero_of_not_headSurj`: a boundary lift
  composes to a surjection `Γ ↠ H` through the frame head, so an uncovered head kills both
  counts (this discharges `mStage_partition`'s `hhead` via a case split at the top of the
  lane, since `b_{Γ_A}`/`b_{G_ℚ₂}` are onto `∂bd`);
* **the stratum bound** — `card_stratum_mStage_lt`: a proper `C`-onto stratum of `𝒴_B`
  *itself* (no central cover) has marked kernel `< |L_Y|`, valid for **every** `R` (the
  cover version `card_stratum_LB_lt` needs `R ≠ ⊥`, so the `R = ⊥` lane cannot use it);
* **the per-source multiplicity counts** (`mStage_partition`'s `hmult`, `mult = |M_B|²`) —
  the unrestricted-`B`-lift count `#LiftsOver(ρ) = |M_B|²` over every lower map, the
  `Enrichment`-free analogue of `Half139Local.hMcountM_local` (the `R = ⊥` lane has no
  radical edge and `blockEnrichment` is gated, so the count is stated on
  `RecursionFrame.LiftsOver` directly).
-/

namespace GQ2

open SectionEight SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-! ## Count transport along an iso of marked targets -/

/-- **Exact-image counts transport along an isomorphism of marked targets**: a `MulEquiv`
`e : Y₁ ≃* Y₂` intertwining heads and decorations induces a bijection of the boundary-lift
sets (continuity is free — the targets are discrete). -/
theorem exactImageCount_congr {Y₁ Y₂ : Type}
    [Group Y₁] [TopologicalSpace Y₁] [DiscreteTopology Y₁] [Finite Y₁]
    [Group Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] [Finite Y₂]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T₁ : MarkedTarget H E Y₁) (T₂ : MarkedTarget H E Y₂) (e : Y₁ ≃* Y₂)
    (hhead : ∀ y : Y₁, T₂.piY (e y) = T₁.piY y)
    (htheta : ∀ y : Y₁, T₂.thetaY (e y) = T₁.thetaY y) :
    exactImageCount b F T₁ = exactImageCount b F T₂ := by
  refine Nat.card_congr
    { toFun := fun f =>
        ⟨⟨⟨e.toMonoidHom.comp f.1.1.toMonoidHom,
            (continuous_of_discreteTopology (f := ⇑e)).comp f.1.1.continuous_toFun⟩,
          e.surjective.comp f.1.2⟩,
        fun γ => ?_⟩
      invFun := fun g =>
        ⟨⟨⟨e.symm.toMonoidHom.comp g.1.1.toMonoidHom,
            (continuous_of_discreteTopology (f := ⇑e.symm)).comp g.1.1.continuous_toFun⟩,
          e.symm.surjective.comp g.1.2⟩,
        fun γ => ?_⟩
      left_inv := fun f => Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ =>
        e.symm_apply_apply _))
      right_inv := fun g => Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ =>
        e.apply_symm_apply _)) }
  · show (T₂.piY (e (f.1.1 γ)), T₂.thetaY (e (f.1.1 γ))) = F.frameMap (b γ)
    rw [hhead, htheta]
    exact f.2 γ
  · show (T₁.piY (e.symm (g.1.1 γ)), T₁.thetaY (e.symm (g.1.1 γ))) = F.frameMap (b γ)
    rw [← hhead (e.symm (g.1.1 γ)), ← htheta (e.symm (g.1.1 γ)), e.apply_symm_apply]
    exact g.2 γ

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] in
/-- The `⊤`-stratum always carries the full head. -/
theorem MarkedTarget.top_head_surjective {Y : Type} [Group Y] [Finite Y]
    (T : MarkedTarget H E Y) :
    Function.Surjective (T.piY.comp (⊤ : Subgroup Y).subtype) := fun h => by
  obtain ⟨y, hy⟩ := T.piY_surjective h
  exact ⟨⟨y, Subgroup.mem_top y⟩, hy⟩

/-- **Evaluation of the totalized stratum count at `⊤`**: the `⊤`-stratum is the ambient
target (transport along `↥⊤ ≃* Y`). -/
theorem SectionEight.exactImageCountOn_top {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (b : ContinuousMonoidHom Γ ↥boundarySubgroup)
    (F : BoundaryFrame H E) (T : MarkedTarget H E Y) :
    exactImageCountOn b F T ⊤ = exactImageCount b F T := by
  simp only [exactImageCountOn]
  rw [dif_pos T.top_head_surjective]
  exact exactImageCount_congr b F _ T Subgroup.topEquiv (fun y => rfl) (fun y => rfl)

/-- **`R = ⊥` collapses the `B`-stage**: `π_B` is then an isomorphism (`ker π_B = R = ⊥`), so
the `B`-stage target has the ambient exact-image count.  The `M`-stage lane's `⊤`-stratum
feed (design note: "`R = ⊥ ⟹ piB` iso ⟹ `e(b, TB) = e(b, T)`"). -/
theorem SectionEight.RecursionFrame.exactImageCount_TB_of_R_bot {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hR : Blk.R = ⊥) :
    exactImageCount b F RF.TB = exactImageCount b F T := by
  have hinj : Function.Injective RF.piB := by
    rw [← MonoidHom.ker_eq_bot_iff, RF.ker_piB]
    exact hR
  exact (exactImageCount_congr b F T RF.TB (MulEquiv.ofBijective RF.piB ⟨hinj, RF.piB_surj⟩)
    (fun y => DFunLike.congr_fun RF.TB_head y) (fun y => DFunLike.congr_fun RF.TB_theta y)).symm

/-! ## The degenerate-head case -/

/-- **Degenerate head ⟹ zero count** (any source): a boundary lift `f` has
`π_Y ∘ f = (frameMap ∘ b).1` with `π_Y ∘ f` onto `H`, so an uncovered frame head admits no
lift at all.  Both sources are killed simultaneously, which is how the `M`-stage lane
discharges `mStage_partition`'s `hhead` hypothesis (a case split on the head's
surjectivity). -/
theorem exactImageCount_eq_zero_of_not_headSurj {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (b : ContinuousMonoidHom Γ ↥boundarySubgroup)
    (F : BoundaryFrame H E) (T : MarkedTarget H E Y)
    (hns : ¬ Function.Surjective (fun x : ↥boundarySubgroup => (F.frameMap x).1)) :
    exactImageCount b F T = 0 := by
  haveI : IsEmpty (BoundaryLifts b F T) := by
    refine ⟨fun f => hns ?_⟩
    have hsurj : Function.Surjective (fun γ : Γ => T.piY (f.1.1 γ)) :=
      T.piY_surjective.comp f.1.2
    have heq : (fun γ : Γ => T.piY (f.1.1 γ))
        = (fun x : ↥boundarySubgroup => (F.frameMap x).1) ∘ ⇑b := by
      funext γ
      exact congrArg Prod.fst (f.2 γ)
    rw [heq] at hsurj
    exact hsurj.of_comp
  rw [exactImageCount]
  exact Nat.card_of_isEmpty

/-! ## The `M`-stage stratum bound

The `R = ⊥` lane feeds the IH at the proper `C`-onto strata of `𝒴_B` itself; the (148) bound
`card_stratum_LB_lt` is the *cover* version and requires `R ≠ ⊥`, so the lane needs its own
bound — which in exchange holds for every `R`. -/

/-- **`M`-stage stratum bound**: a proper (`J ≠ ⊤`) `C`-onto (`J.map π_{BC} = ⊤`) stratum of
the `B`-stage target has marked kernel `< |L_Y|`.  Properness against `C`-ontoness forces
`L_B ⊓ J` to have index `≥ 2` in `L_B` (if `L_B ≤ J` then `M_B ≤ J`, and `C`-ontoness pulls
all of `B` into `J`), and `|L_B| ≤ |L_Y|` by (145a). -/
lemma card_stratum_mStage_lt {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (J : Subgroup (blockFrameImpl T Blk hE2).YB) (hJtop : J ≠ ⊤)
    (hJC : J.map (blockFrameImpl T Blk hE2).piBC = ⊤)
    (hJ : Function.Surjective ((blockFrameImpl T Blk hE2).TB.piY.comp J.subtype)) :
    Nat.card ↥(((blockFrameImpl T Blk hE2).TB.stratum J hJ).LY) < Nat.card ↥T.LY := by
  set LB := (blockFrameImpl T Blk hE2).TB.LY with hLB
  -- the stratum kernel is `L_B ⊓ J`
  have key : Nat.card ↥(((blockFrameImpl T Blk hE2).TB.stratum J hJ).LY)
      = Nat.card ↥(LB ⊓ J) := by
    rw [show ((blockFrameImpl T Blk hE2).TB.stratum J hJ).LY = LB.subgroupOf J from rfl,
      card_subgroupOf_eq_inf]
  -- `L_B ≰ J`: else `M_B ≤ J`, and `C`-ontoness pulls all of `B` into `J`
  have hproper : ¬ LB ≤ J := by
    intro hle
    refine hJtop (top_unique fun y _ => ?_)
    have hy : (blockFrameImpl T Blk hE2).piBC y ∈ J.map (blockFrameImpl T Blk hE2).piBC := by
      rw [hJC]
      exact Subgroup.mem_top _
    obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hy
    have hk : j⁻¹ * y ∈ (blockFrameImpl T Blk hE2).MB := by
      rw [← (blockFrameImpl T Blk hE2).ker_piBC]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hj, inv_mul_cancel])
    have hyJ : y = j * (j⁻¹ * y) := by group
    rw [hyJ]
    exact mul_mem hjJ (hle (blockFrameImpl_MB_le_TB_LY T Blk hE2 hk))
  -- Lagrange inside `L_B`: `2·|L_B ⊓ J| ≤ |L_B|`
  have hlag : Nat.card ↥(LB ⊓ J) * (J.subgroupOf LB).index = Nat.card ↥LB := by
    have hc : Nat.card ↥(LB ⊓ J) = Nat.card ↥(J.subgroupOf LB) := by
      rw [card_subgroupOf_eq_inf, inf_comm]
    rw [hc]
    exact Subgroup.card_mul_index _
  have hidx2 : 2 ≤ (J.subgroupOf LB).index := by
    have hne1 : (J.subgroupOf LB).index ≠ 1 := fun h1 =>
      hproper (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1))
    have hne0 : (J.subgroupOf LB).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have h2c : 2 * Nat.card ↥(LB ⊓ J) ≤ Nat.card ↥LB := by
    calc 2 * Nat.card ↥(LB ⊓ J) = Nat.card ↥(LB ⊓ J) * 2 := by ring
      _ ≤ Nat.card ↥(LB ⊓ J) * (J.subgroupOf LB).index := by gcongr
      _ = Nat.card ↥LB := hlag
  -- `|L_B| ≤ |L_Y|` by (145a) (`|R| ≥ 1`)
  have hLBle : Nat.card ↥LB ≤ Nat.card ↥T.LY := by
    rw [hLB]
    calc Nat.card ↥(blockFrameImpl T Blk hE2).TB.LY
        ≤ Nat.card ↥(blockFrameImpl T Blk hE2).TB.LY * Nat.card ↥Blk.R :=
          Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card ↥T.LY := card_LB_mul T Blk hE2
  have hpos : 0 < Nat.card ↥(LB ⊓ J) := Nat.card_pos
  rw [key]
  omega

/-! ## The per-source multiplicity count, local side

`mStage_partition`'s `hmult` at `mult = |M_B|²` for `Γ = G_ℚ₂`: over every lower boundary
lift `ρ`, the unrestricted `B`-lift set `LiftsOver ρ` has exactly `|M_B|²` elements.  This is
the `Enrichment`-free analogue of `Half139Local.hMcountM_local` — same five-step route
(additive `M`-module with the `ρ`-conjugation action; `Z¹`-torsor bridge with nonemptiness
from `#H² = 1`; `card_Z1_eq` [B7]; `#fixedPts = 1` from `lemma_7_1_dual`) with the quotient
`Y_B ⧸ M` replaced by `Y_C` itself (`π_{BC}` has kernel `M_B`, `RecursionFrame.ker_piBC`) and
the coset section `Quotient.out` replaced by `Function.surjInv π_{BC}`.  Stated on
`RecursionFrame.LiftsOver` directly because the `R = ⊥` lane has no radical datum (and
`blockEnrichment` is gated on P-17d).

Axioms: `std-3 + B6 + B7` (B6 via `card_H2_eq_fixedPts`, B7 via `card_Z1_eq`) — as for
`hMcountM_local`. -/

section LocalCount

open ContCoh LocalLiftingDuality FoxH

/-- **`hmult` for `G_ℚ₂`** (the `M`-stage multiplicity): `#LiftsOver(ρ) = |M_B|²` over every
lower boundary lift `ρ` of the `C`-stage target. -/
theorem SectionEight.RecursionFrame.liftsOver_card_local
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
    (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2 := by
  classical
  -- `M_B` is normal (the kernel of `π_{BC}`) and elementary abelian
  haveI hMBn : RF.MB.Normal := RF.ker_piBC ▸ RF.piBC.normal_ker
  have hcomm : ∀ x ∈ RF.MB, ∀ y ∈ RF.MB, x * y = y * x := by
    intro x hx y hy
    have hxy := RF.MB_elem _ (mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
          rw [inv_eq_of_mul_eq_one_right (RF.MB_elem _ hy),
            inv_eq_of_mul_eq_one_right (RF.MB_elem _ hx)]
  -- conjugation of `M_B`-elements only depends on the `π_{BC}`-image of the conjugator
  have hconj_eq : ∀ {u v : RF.YB}, RF.piBC u = RF.piBC v → ∀ m : ↥RF.MB,
      u * m.1 * u⁻¹ = v * m.1 * v⁻¹ := by
    intro u v huv m
    have hm : u⁻¹ * v ∈ RF.MB := by
      rw [← RF.ker_piBC]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, huv, inv_mul_cancel])
    have hcm := hcomm _ hm _ m.2
    calc u * m.1 * u⁻¹
        = u * (m.1 * (u⁻¹ * v) * (u⁻¹ * v)⁻¹) * u⁻¹ := by group
      _ = u * ((u⁻¹ * v) * m.1 * (u⁻¹ * v)⁻¹) * u⁻¹ := by rw [← hcm]
      _ = v * m.1 * v⁻¹ := by group
  -- the set-section of `π_{BC}` and the lower map
  set ρc := ρ.1.1 with hρcdef
  set sec : RF.YC → RF.YB := Function.surjInv RF.piBC_surj with hsecdef
  have hsec : ∀ c, RF.piBC (sec c) = c := fun c => Function.surjInv_eq RF.piBC_surj c
  -- `M_B` as an additive `𝔽₂`-space with the `ρ`-conjugation action
  letI : CommGroup ↥RF.MB :=
    { (inferInstance : Group ↥RF.MB) with
      mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actC : DistribMulAction RF.YC (Additive ↥RF.MB) :=
    { smul := fun c m => Additive.ofMul
        ⟨sec c * (Additive.toMul m).1 * (sec c)⁻¹,
          hMBn.conj_mem _ (Additive.toMul m).2 _⟩
      one_smul := fun m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec 1 * (Additive.toMul m).1 * (sec 1)⁻¹ = (Additive.toMul m).1
        have h1 : sec 1 ∈ RF.MB := by
          rw [← RF.ker_piBC]
          exact MonoidHom.mem_ker.mpr (hsec 1)
        rw [hcomm _ h1 _ (Additive.toMul m).2]; group
      mul_smul := fun c c' m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec (c * c') * (Additive.toMul m).1 * (sec (c * c'))⁻¹
          = sec c * (sec c' * (Additive.toMul m).1 * (sec c')⁻¹) * (sec c)⁻¹
        rw [show sec c * (sec c' * (Additive.toMul m).1 * (sec c')⁻¹) * (sec c)⁻¹
            = (sec c * sec c') * (Additive.toMul m).1 * (sec c * sec c')⁻¹ from by group]
        exact hconj_eq (by rw [hsec, map_mul, hsec, hsec]) (Additive.toMul m)
      smul_zero := fun c => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec c * (1 : RF.YB) * (sec c)⁻¹ = 1
        group
      smul_add := fun c m m' => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec c * ((Additive.toMul m).1 * (Additive.toMul m').1) * (sec c)⁻¹
          = (sec c * (Additive.toMul m).1 * (sec c)⁻¹)
              * (sec c * (Additive.toMul m').1 * (sec c)⁻¹)
        group }
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥RF.MB) :=
    DistribMulAction.compHom (Additive ↥RF.MB) ρc.toMonoidHom
  have hcomp : ∀ (γ : AbsGalQ2) (a : Additive ↥RF.MB), γ • a = ρc γ • a := fun _ _ => rfl
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥RF.MB) := by
    constructor
    have hfac : (fun p : AbsGalQ2 × Additive ↥RF.MB => p.1 • p.2)
        = (fun cq : RF.YC × ↥RF.MB =>
            Additive.ofMul (⟨sec cq.1 * cq.2.1 * (sec cq.1)⁻¹,
              hMBn.conj_mem _ cq.2.2 _⟩ : ↥RF.MB))
          ∘ (fun p : AbsGalQ2 × Additive ↥RF.MB => (ρc p.1, Additive.toMul p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρc.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ a : Additive ↥RF.MB, a + a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) * (Additive.toMul a) = 1
    exact Subtype.ext (RF.MB_elem _ (Additive.toMul a).2)
  -- Step 3: `#Z¹ = |M_B|² · #fixedPts` (`card_Z1_eq`, B7 Euler char)
  have key := card_Z1_eq ρ.1.2 hcomp hA₂
  -- Step 4: `#fixedPts = 1` ⟵ `lemma_7_1_dual` (the `(M^∨)^C = 0` group theory, std-3)
  have hfix : Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1 := by
    have hzero : ∀ lam : ElemDual (Additive ↥RF.MB),
        (∀ g : RF.YC, g • lam = lam) → lam = 0 := by
      intro lam hlam
      by_contra hlamne
      have hinv : ∀ (c : RF.YC) (a : Additive ↥RF.MB), lam (c • a) = lam a := by
        intro c a
        have h2 : (c⁻¹ • lam) a = lam a := by rw [hlam c⁻¹]
        rwa [ElemDual.smul_apply, inv_inv] at h2
      have hmem : ∀ k : ↥Blk.K, RF.piB k.1 ∈ RF.MB := by
        intro k
        rw [RF.MB_eq]; exact Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩
      -- `s : Blk.K ↠ M_B` and the character `φ = lam ∘ s : Blk.K →* μ₂`
      let s : ↥Blk.K →* ↥RF.MB :=
        (RF.piB.comp Blk.K.subtype).codRestrict RF.MB (fun k => hmem k)
      have hs : ∀ k : ↥Blk.K, (s k).1 = RF.piB k.1 := fun _ => rfl
      have hs_surj : Function.Surjective s := by
        intro m
        obtain ⟨k, hk, hkeq⟩ := (RF.MB_eq ▸ m.2 : m.1 ∈ Blk.K.map RF.piB)
        exact ⟨⟨k, hk⟩, Subtype.ext hkeq⟩
      let φ : ↥Blk.K →* Multiplicative (ZMod 2) :=
        { toFun := fun k => Multiplicative.ofAdd (lam (Additive.ofMul (s k)))
          map_one' := by simp
          map_mul' := fun a b => by simp [map_mul] }
      have hφ_apply : ∀ k, φ k = Multiplicative.ofAdd (lam (Additive.ofMul (s k))) := fun _ => rfl
      have hφne : φ ≠ 1 := by
        intro hφ1
        apply hlamne
        ext a
        show lam a = 0
        obtain ⟨k, hk⟩ := hs_surj (Additive.toMul a)
        have h0 : lam (Additive.ofMul (s k)) = 0 := by
          have hk1 : φ k = 1 := by rw [hφ1]; rfl
          have := congrArg Multiplicative.toAdd hk1
          simpa [hφ_apply] using this
        rw [hk] at h0
        exact h0
      have hφsurj : Function.Surjective φ := by
        intro y
        rcases eq_or_ne y 1 with rfl | hy
        · exact ⟨1, map_one φ⟩
        · obtain ⟨k, hk⟩ := not_forall.mp (fun hh => hφne (MonoidHom.ext hh))
          refine ⟨k, ?_⟩
          have hpin : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd 1 := by
            decide
          rw [hpin _ hk, hpin _ hy]
      set X : Subgroup Y := φ.ker.map Blk.K.subtype with hXdef
      have hXK : X ≤ Blk.K := by rw [hXdef]; exact Subgroup.map_subtype_le _
      have hRX : Blk.R ≤ X := by
        intro r hr
        have hrK : r ∈ Blk.K := frattiniLike_le Blk.K hr
        refine Subgroup.mem_map.mpr ⟨⟨r, hrK⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker, hφ_apply]
        have hs1 : s ⟨r, hrK⟩ = 1 := Subtype.ext (by
          rw [hs]
          show RF.piB r = 1
          exact (RF.ker_piB.symm ▸ hr : r ∈ RF.piB.ker))
        rw [hs1]; simp
      have hXnormal : X.Normal := by
        rw [hXdef]
        refine ⟨fun x hx y => ?_⟩
        obtain ⟨k, hkker, hkeq⟩ := Subgroup.mem_map.mp hx
        have hxK : x ∈ Blk.K := hkeq ▸ k.2
        have hyk : y * x * y⁻¹ ∈ Blk.K := Blk.hK.conj_mem x hxK y
        refine Subgroup.mem_map.mpr ⟨⟨y * x * y⁻¹, hyk⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker] at hkker ⊢
        rw [hφ_apply] at hkker ⊢
        have hconj : Additive.ofMul (s ⟨y * x * y⁻¹, hyk⟩)
            = (RF.piBC (RF.piB y)) • Additive.ofMul (s ⟨x, hxK⟩) := by
          have hact : (RF.piBC (RF.piB y)) • Additive.ofMul (s ⟨x, hxK⟩)
              = Additive.ofMul (⟨sec (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1
                  * (sec (RF.piBC (RF.piB y)))⁻¹,
                  hMBn.conj_mem _ (s ⟨x, hxK⟩).2 _⟩ : ↥RF.MB) := rfl
          rw [hact]
          congr 1
          apply Subtype.ext
          rw [hs]
          show RF.piB (y * x * y⁻¹)
            = sec (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1 * (sec (RF.piBC (RF.piB y)))⁻¹
          rw [hs, map_mul, map_mul, map_inv]
          exact (hconj_eq (hsec (RF.piBC (RF.piB y))) ⟨RF.piB x, hmem ⟨x, hxK⟩⟩).symm
        rw [hconj, hinv]
        have hkx : s ⟨x, hxK⟩ = s k := congrArg s (Subtype.ext hkeq.symm)
        rw [hkx]; exact hkker
      have hidx : (X.subgroupOf Blk.K).index = 2 := by
        have hcm : X.subgroupOf Blk.K = φ.ker := by
          rw [hXdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective Blk.K.subtype_injective]
        show Nat.card (↥Blk.K ⧸ (X.subgroupOf Blk.K)) = 2
        rw [hcm, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
        simp
      exact absurd ⟨X, hXnormal, hRX, hXK, hidx⟩ (lemma_7_1_dual Blk)
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
      ⟨⟨0, fun c => smul_zero c⟩⟩⟩
  -- Step 2: the `Z¹`-torsor bridge (`LiftsOver` nonempty from `#H² = 1`, then `≃ Z¹`)
  have htorsor : Nat.card (RF.LiftsOver b F ρ)
      = Nat.card (Z1 AbsGalQ2 (Additive ↥RF.MB)) := by
    -- **Nonemptiness**: `#H²(G_ℚ₂, M_B) = 1` kills the lift obstruction (extension splitting).
    have hne : Nonempty (RF.LiftsOver b F ρ) := by
      haveI : IsTopologicalAddGroup (Additive ↥RF.MB) :=
        { continuous_add := continuous_of_discreteTopology
          continuous_neg := continuous_of_discreteTopology }
      -- a continuous set-section of `Y_B ↠ Y_C` under the lower map
      set sρ : AbsGalQ2 → RF.YB := fun γ => sec (ρc γ) with hsρdef
      have hsρ_cont : Continuous sρ :=
        (continuous_of_discreteTopology (f := sec)).comp ρc.continuous_toFun
      have hsρ_mk : ∀ γ, RF.piBC (sρ γ) = ρc γ := fun γ => hsec _
      -- the action = conjugation by the section value
      have hsmul_s : ∀ (γ : AbsGalQ2) (a : Additive ↥RF.MB),
          γ • a = Additive.ofMul (⟨sρ γ * (Additive.toMul a).1 * (sρ γ)⁻¹,
              hMBn.conj_mem _ (Additive.toMul a).2 _⟩ : ↥RF.MB) := fun γ a => rfl
      -- the factor set `c(γ,δ) = sρ γ · sρ δ · sρ(γδ)⁻¹ ∈ M_B`
      have hc_mem : ∀ p : AbsGalQ2 × AbsGalQ2,
          sρ p.1 * sρ p.2 * (sρ (p.1 * p.2))⁻¹ ∈ RF.MB := by
        intro p
        rw [← RF.ker_piBC]
        exact MonoidHom.mem_ker.mpr (by
          rw [map_mul, map_mul, map_inv, hsρ_mk, hsρ_mk, hsρ_mk, ← map_mul, mul_inv_cancel])
      set c : AbsGalQ2 × AbsGalQ2 → Additive ↥RF.MB :=
        fun p => Additive.ofMul ⟨sρ p.1 * sρ p.2 * (sρ (p.1 * p.2))⁻¹, hc_mem p⟩ with hcdef
      have hc_Z2 : c ∈ Z2 AbsGalQ2 (Additive ↥RF.MB) := by
        rw [mem_Z2_iff]
        refine ⟨?_, ?_⟩
        · have hg : Continuous (fun p : AbsGalQ2 × AbsGalQ2 =>
              sρ p.1 * sρ p.2 * (sρ (p.1 * p.2))⁻¹) :=
            (continuous_of_discreteTopology (f := fun t : RF.YB × RF.YB × RF.YB =>
                t.1 * t.2.1 * t.2.2⁻¹)).comp
              ((hsρ_cont.comp continuous_fst).prodMk ((hsρ_cont.comp continuous_snd).prodMk
                (hsρ_cont.comp (continuous_fst.mul continuous_snd))))
          exact hg.subtype_mk _
        · intro x y z
          rw [hsmul_s x (c (y, z))]
          apply Additive.toMul.injective
          -- both sides are products in the `CommGroup` `↥M_B`; reorder, then compare in `Y_B`
          show (⟨sρ x * (sρ y * sρ z * (sρ (y * z))⁻¹) * (sρ x)⁻¹, _⟩ : ↥RF.MB)
              * ⟨sρ x * sρ (y * z) * (sρ (x * (y * z)))⁻¹, _⟩
            = ⟨sρ (x * y) * sρ z * (sρ ((x * y) * z))⁻¹, _⟩
              * ⟨sρ x * sρ y * (sρ (x * y))⁻¹, _⟩
          rw [mul_comm (⟨sρ (x * y) * sρ z * (sρ ((x * y) * z))⁻¹, _⟩ : ↥RF.MB) _]
          apply Subtype.ext
          show sρ x * (sρ y * sρ z * (sρ (y * z))⁻¹) * (sρ x)⁻¹
              * (sρ x * sρ (y * z) * (sρ (x * (y * z)))⁻¹)
            = sρ x * sρ y * (sρ (x * y))⁻¹ * (sρ (x * y) * sρ z * (sρ ((x * y) * z))⁻¹)
          rw [mul_assoc x y z]; group
      -- `#H² = 1` ⟹ `c` is a coboundary
      have hH2 : Nat.card (H2 AbsGalQ2 (Additive ↥RF.MB)) = 1 :=
        (card_H2_eq_fixedPts ρ.1.2 hcomp hA₂).trans hfix
      haveI : Subsingleton (H2 AbsGalQ2 (Additive ↥RF.MB)) :=
        (Nat.card_eq_one_iff_unique.mp hH2).1
      have hcB2 : c ∈ B2 AbsGalQ2 (Additive ↥RF.MB) := by
        have h0 : H2mk AbsGalQ2 (Additive ↥RF.MB) ⟨c, hc_Z2⟩ = 0 := Subsingleton.elim _ _
        exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
      obtain ⟨ψ, hψc, hψ⟩ := hcB2
      -- the lift `f γ = (toMul (ψ γ))⁻¹ · sρ γ`
      set ψ' : AbsGalQ2 → RF.YB := fun γ => (Additive.toMul (ψ γ)).1 with hψ'def
      have hψ'mem : ∀ γ, ψ' γ ∈ RF.MB := fun γ => (Additive.toMul (ψ γ)).2
      -- read off the coboundary identity in `Y_B` (the `toMul`/`.1` reductions are defeq)
      have hrel : ∀ x y : AbsGalQ2,
          sρ x * ψ' y * (sρ x)⁻¹ * (ψ' (x * y))⁻¹ * ψ' x = sρ x * sρ y * (sρ (x * y))⁻¹ := by
        intro x y
        have hxy_eq : x • ψ y - ψ (x * y) + ψ x = c (x, y) := congrFun hψ (x, y)
        rw [hsmul_s x (ψ y)] at hxy_eq
        have hxy := congrArg (fun a : Additive ↥RF.MB => (Additive.toMul a).1) hxy_eq
        simpa [hcdef, hψ'def, div_eq_mul_inv, mul_assoc] using hxy
      refine ⟨⟨MonoidHom.mk' (fun γ => (ψ' γ)⁻¹ * sρ γ) (fun x y => ?_), ?_⟩, ?_⟩
      · -- homomorphism: from `hrel` + `ψ'x, ψ'(xy) ∈ M_B` commuting
        have hcm : Commute (ψ' (x * y)) (ψ' x) := hcomm _ (hψ'mem (x * y)) _ (hψ'mem x)
        show (ψ' (x * y))⁻¹ * sρ (x * y) = (ψ' x)⁻¹ * sρ x * ((ψ' y)⁻¹ * sρ y)
        have hs_xy : sρ (x * y) = (ψ' x)⁻¹ * ψ' (x * y) * sρ x * (ψ' y)⁻¹ * sρ y := by
          have e : sρ (x * y)
              = (sρ x * ψ' y * (sρ x)⁻¹ * (ψ' (x * y))⁻¹ * ψ' x)⁻¹ * (sρ x * sρ y) := by
            rw [hrel x y]; group
          rw [e]; group
        rw [hs_xy]
        rw [show (ψ' (x * y))⁻¹ * ((ψ' x)⁻¹ * ψ' (x * y) * sρ x * (ψ' y)⁻¹ * sρ y)
            = ((ψ' (x * y))⁻¹ * (ψ' x)⁻¹ * ψ' (x * y)) * (sρ x * (ψ' y)⁻¹ * sρ y) from by
              group,
          show (ψ' (x * y))⁻¹ * (ψ' x)⁻¹ * ψ' (x * y) = (ψ' x)⁻¹ from by
            rw [mul_assoc, (hcm.symm.inv_left).eq, ← mul_assoc, inv_mul_cancel, one_mul]]
        group
      · -- continuity
        have hψ'cont : Continuous ψ' :=
          (continuous_of_discreteTopology
            (f := fun a : Additive ↥RF.MB => (Additive.toMul a).1)).comp hψc
        exact (continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1⁻¹ * p.2)).comp
          (hψ'cont.prodMk hsρ_cont)
      · -- over `ρ`
        intro γ
        show RF.piBC ((ψ' γ)⁻¹ * sρ γ) = ρc γ
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp (RF.ker_piBC ▸ hψ'mem γ), inv_one, one_mul,
          hsρ_mk]
    obtain ⟨f₀⟩ := hne
    -- the `G_ℚ₂`-action on `M_B` is conjugation by the lift `f₀ γ` of `ρ γ`
    have hsmul : ∀ (γ : AbsGalQ2) (a : Additive ↥RF.MB),
        γ • a = Additive.ofMul (⟨f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹,
              hMBn.conj_mem _ (Additive.toMul a).2 _⟩ : ↥RF.MB) := by
      intro γ a
      rw [hcomp]
      apply Additive.toMul.injective; apply Subtype.ext
      show sec (ρc γ) * (Additive.toMul a).1 * (sec (ρc γ))⁻¹
        = f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹
      exact hconj_eq (by rw [hsec, f₀.2 γ]) (Additive.toMul a)
    have hmemf : ∀ (f : RF.LiftsOver b F ρ) (γ : AbsGalQ2),
        f.1 γ * (f₀.1 γ)⁻¹ ∈ RF.MB := by
      intro f γ
      rw [← RF.ker_piBC]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, f.2 γ, f₀.2 γ, mul_inv_cancel])
    refine Nat.card_congr
      { toFun := fun f => ⟨fun γ => Additive.ofMul ⟨f.1 γ * (f₀.1 γ)⁻¹, hmemf f γ⟩, ?_⟩
        invFun := fun c => ⟨⟨MonoidHom.mk'
            (fun γ => (Additive.toMul (c.1 γ)).1 * f₀.1 γ) ?_, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- forward lands in `Z¹`
      rw [mem_Z1_iff]
      refine ⟨?_, ?_⟩
      · have hg : Continuous (fun γ : AbsGalQ2 => f.1 γ * (f₀.1 γ)⁻¹) :=
          (continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1 * p.2⁻¹)).comp
            (f.1.continuous_toFun.prodMk f₀.1.continuous_toFun)
        exact hg.subtype_mk (hmemf f)
      · intro g s
        rw [hsmul g (Additive.ofMul ⟨f.1 s * (f₀.1 s)⁻¹, hmemf f s⟩)]
        apply Additive.toMul.injective; apply Subtype.ext
        show f.1 (g * s) * (f₀.1 (g * s))⁻¹
          = f.1 g * (f₀.1 g)⁻¹ * (f₀.1 g * (f.1 s * (f₀.1 s)⁻¹) * (f₀.1 g)⁻¹)
        rw [map_mul, map_mul]; group
    · -- inverse is a hom
      intro g h
      show (Additive.toMul (c.1 (g * h))).1 * f₀.1 (g * h)
        = (Additive.toMul (c.1 g)).1 * f₀.1 g * ((Additive.toMul (c.1 h)).1 * f₀.1 h)
      rw [(mem_Z1_iff.mp c.2).2 g h, map_mul, hsmul g (c.1 h)]
      show (Additive.toMul (c.1 g)).1 * (f₀.1 g * (Additive.toMul (c.1 h)).1 * (f₀.1 g)⁻¹)
          * (f₀.1 g * f₀.1 h) = _
      group
    · -- inverse is continuous
      exact (continuous_of_discreteTopology
          (f := fun p : Additive ↥RF.MB × RF.YB => (Additive.toMul p.1).1 * p.2)).comp
        ((mem_Z1_iff.mp c.2).1.prodMk f₀.1.continuous_toFun)
    · -- inverse lands over `ρ`
      intro γ
      show RF.piBC ((Additive.toMul (c.1 γ)).1 * f₀.1 γ) = ρc γ
      have hcker : RF.piBC ((Additive.toMul (c.1 γ)).1) = 1 := by
        have hmem : ((Additive.toMul (c.1 γ)).1 : RF.YB) ∈ RF.piBC.ker := by
          rw [RF.ker_piBC]
          exact (Additive.toMul (c.1 γ)).2
        exact MonoidHom.mem_ker.mp hmem
      rw [map_mul, hcker, one_mul, f₀.2 γ]
    · -- left inverse
      intro f
      apply Subtype.ext; apply ContinuousMonoidHom.ext; intro γ
      show f.1 γ * (f₀.1 γ)⁻¹ * f₀.1 γ = f.1 γ
      group
    · -- right inverse
      intro c
      apply Subtype.ext; funext γ
      show Additive.ofMul (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩
          : ↥RF.MB) = c.1 γ
      rw [show (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩ : ↥RF.MB)
          = Additive.toMul (c.1 γ) from Subtype.ext (by group)]
      rfl
  rw [htorsor, key, hfix, mul_one]
  rfl

end LocalCount

end GQ2
