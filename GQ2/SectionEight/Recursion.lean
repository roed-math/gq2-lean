/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionEight.Partition

/-!
# §8: the closed exact-image recursion (Proposition 8.9)

The `RecursionFrame` on a §7 block, its derived layer and `Enrichment`, the boxed system
`ClosedRecursion` (displays (136)–(142)), the source-side input bundle `RecursionInputs`,
and the assembly steps `partition137_of`, `prop_8_9_aux`, `stageR136_of`.
-/

open scoped Pointwise

namespace GQ2

namespace SectionEight

open QuadraticFp2

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]


/-! ## Proposition 8.9: the closed exact-image recursion  (displays (136)–(142))

Target-side data: the §7 block on `𝒴` with `B = Y/R`, `C = Y/K`, carried as a
`RecursionFrame` (quotient targets pinned by spec fields; the scalar characters
`λ ∈ D_R = (R^∨)^C` indexed by a finite type with a distinguished `0`, nonzero `λ`
carrying their scalar central covers `p_λ : B_λ ↠ B`).  The boxed equations are the
fields of the source-generic `ClosedRecursion`; `prop_8_9` asserts the system for **both
sources with one shared** `(μ, G⁰, phase family)` — which is exactly how the §9 induction
consumes it (the paper pins `μ = |B¹(V)||Z¹(T)|` via 5.15/5.16, `G⁰` as the Gauss sum of
the 7.4 form, and the family as the `Δ_{χ,κ}`-covers of (134); that pinning is the O-half's
construction, a flagged deviation). -/

section Recursion

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- **The §8 recursion frame** on a marked target with a §7 block: the two quotient stages
`B = Y/R`, `C = Y/K` as boundary-framed targets (pinned to `𝒴` by the spec fields), the
connecting epimorphism, the images of `M = K/R` and `T = T₀`, and the scalar character
index `D_R` with its central covers. -/
structure RecursionFrame (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) where
  /-- The `B`-stage group (paper `B = Y/R`). -/
  YB : Type
  [groupB : Group YB]
  [finiteB : Finite YB]
  [topoB : TopologicalSpace YB]
  [discB : DiscreteTopology YB]
  /-- The projection `Y ↠ B`. -/
  piB : Y →* YB
  piB_surj : Function.Surjective piB
  ker_piB : piB.ker = Blk.frattiniK
  /-- The `B`-stage boundary-framed target. -/
  TB : MarkedTarget H E YB
  TB_head : TB.piY.comp piB = T.piY
  TB_theta : TB.thetaY.comp piB = T.thetaY
  /-- The `C`-stage group (paper `C = Y/K`). -/
  YC : Type
  [groupC : Group YC]
  [finiteC : Finite YC]
  [topoC : TopologicalSpace YC]
  [discC : DiscreteTopology YC]
  /-- The projection `Y ↠ C`. -/
  piC : Y →* YC
  piC_surj : Function.Surjective piC
  ker_piC : piC.ker = Blk.K
  /-- The `C`-stage boundary-framed target. -/
  TC : MarkedTarget H E YC
  TC_head : TC.piY.comp piC = T.piY
  TC_theta : TC.thetaY.comp piC = T.thetaY
  /-- The connecting map `B ↠ C`. -/
  piBC : YB →* YC
  piBC_comp : piBC.comp piB = piC
  /-- The image of `M = K/R` in `B`. -/
  MB : Subgroup YB
  MB_eq : MB = Blk.K.map piB
  /-- The image of `T = T₀ = (K ⊓ S)·R` in `B`. -/
  TBsub : Subgroup YB
  TBsub_eq : TBsub = ((Blk.K ⊓ Blk.S) ⊔ Blk.frattiniK).map piB
  /-- The scalar character index `D_R = (R^∨)^C`, with distinguished `0`. -/
  DR : Type
  [fintypeDR : Fintype DR]
  zeroDR : DR
  /-- `D_R` has the size of the set of `λ`-kernels: `Y`-normal subgroups of `R` of relative
  index ≤ 2 (`λ = 0 ↔ R' = R`; `Y`-normality = `C`-invariance, the `lemma_7_1_dual`
  encoding). -/
  card_DR : Nat.card DR = Nat.card {R' : Subgroup Y //
    R'.Normal ∧ R' ≤ Blk.frattiniK ∧ R'.relIndex Blk.frattiniK ≤ 2}
  /-- The scalar central cover `p_λ : B_λ ↠ B` of each nonzero `λ` (paper §7.1: the pushout
  `K_λ = K/ker λ`, realized as `Y/ker λ ↠ Y/R`). -/
  scalarCover : (l : DR) → l ≠ zeroDR → CentralCover YB

attribute [instance] RecursionFrame.groupB RecursionFrame.finiteB RecursionFrame.topoB
  RecursionFrame.discB RecursionFrame.groupC RecursionFrame.finiteC RecursionFrame.topoC
  RecursionFrame.discC RecursionFrame.fintypeDR

namespace RecursionFrame

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)

/-- `z_R = |Z¹_{Γ,ρ}(R)| = 2^{2·dim R + dim D_R}` (paper, before (136)), in card form:
`|R|² · |D_R|`. -/
noncomputable def zR : ℕ := (Nat.card ↥Blk.frattiniK) ^ 2 * Nat.card RF.DR

open scoped Classical in
/-- `m_{Γ,λ}(B)` (paper, before (136)): for `λ = 0`, `e_Γ(B)`; for `λ ≠ 0`, the number of
boundary-framed exact-image maps onto `B` whose `λ`-scalar pushout vanishes — i.e. which
lift through `p_λ` (`liftableCount` at the top stratum). -/
noncomputable def mB (l : RF.DR) : ℕ :=
  if h : l = RF.zeroDR then exactImageCount b F RF.TB
  else Nat.card {f : BoundaryLifts b F RF.TB //
    ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
      ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = f.1.1 γ}

open scoped Classical in
/-- `m_{Γ,λ}(J)` for a proper exact-image stratum `J < B` (the summands of (137), computed
by (138)): boundary-framed exact-image maps onto the `J`-stratum lifting through `p_λ`. -/
noncomputable def mJ (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
    (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)) : ℕ :=
  liftableCount b F RF.TB (RF.scalarCover l h) J hJ

open scoped Classical in
/-- `m_{Γ,λ}(J)`, totalized over all subgroups (`0` when `J` misses the `H`-head — such
strata carry no boundary lifts, so the totalization is faithful). -/
noncomputable def mJOn (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB) : ℕ :=
  if hJ : Function.Surjective (RF.TB.piY.comp J.subtype) then RF.mJ b F l h J hJ else 0

/-- `Z_{Γ,λ}(B/C)` (paper, (137)): all `p_λ`-compatible lifts of boundary-framed
exact-image maps to `C`, **without** imposing generation in `B` — pairs of an exact-image
`ρ` onto the `C`-target and a boundary-compatible continuous lift `m` into `B` over it that
is `λ`-compatible (lifts through the scalar cover).

**Encoding correction (deviation from the earlier encoding).**  The original encoding
took the cover-valued lift `g` itself as the pair datum; since the boundary equation of the
pulled-back target only constrains `p_λ ∘ g`, each `λ`-compatible `B`-lift `m` carries
exactly `#Hom(Γ,𝔽₂)` cover lifts (the `z`-scalar twists), so that encoding overcounts the
paper's `Z_{Γ,λ}(B/C)` by the factor `8` and contradicts (139) as displayed.  The corrected
datum is the `B`-lift `m` with the **existence** of a cover lift — matching `m_{Γ,λ}`'s
`∃`-form and the paper's "compatible lifts … without imposing generation". -/
noncomputable def zBC (l : RF.DR) (h : l ≠ RF.zeroDR) : ℕ :=
  Nat.card {pr : BoundaryLifts b F RF.TC × ContinuousMonoidHom Γ RF.YB //
    (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧
      IsBoundaryLift b F RF.TB pr.2 ∧
      ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
        ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ}

/-- `n_{Γ,0}(ζ)` for a phase cover `C_ζ ↠ C` ((141)/(142)): boundary-framed exact-image
maps onto the `C`-target that lift through the cover. -/
noncomputable def nPhase (Cζ : CentralCover RF.YC) : ℕ :=
  Nat.card {f : BoundaryLifts b F RF.TC //
    ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = f.1.1 γ}

/-- **The `B`-stage projection of a boundary lift** (the Prop. 8.9 assembly, the (136) fibration map):
composing an exact-image boundary lift onto `Y` with `π_B : Y ↠ B`.  Surjectivity is
inherited (`π_B` epi), continuity is free (`Y` discrete), and the boundary equation
transports along the spec fields `TB_head`/`TB_theta`. -/
noncomputable def liftB (f : BoundaryLifts b F T) : BoundaryLifts b F RF.TB :=
  ⟨⟨⟨RF.piB.comp f.1.1.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑RF.piB)).comp f.1.1.continuous_toFun⟩,
    RF.piB_surj.comp f.1.2⟩,
   fun γ => by
     show (RF.TB.piY (RF.piB (f.1.1 γ)), RF.TB.thetaY (RF.piB (f.1.1 γ))) = F.frameMap (b γ)
     have h1 : RF.TB.piY (RF.piB (f.1.1 γ)) = T.piY (f.1.1 γ) :=
       DFunLike.congr_fun RF.TB_head (f.1.1 γ)
     have h2 : RF.TB.thetaY (RF.piB (f.1.1 γ)) = T.thetaY (f.1.1 γ) :=
       DFunLike.congr_fun RF.TB_theta (f.1.1 γ)
     rw [h1, h2]
     exact f.2 γ⟩

/-! ### The frame-enrichment layer

`RecursionFrame` pins the stages and the scalar covers only as bare group data; the
(139)/(140) analyses use more.  First the **derived layer facts** — normality and
elementarity of `M_B`/`T_B`, forced by `ker π_B = R = Φ(K)` — then the `Enrichment`
structure carrying what the frame does not determine: per nonzero `λ`, the square form of
`p_λ` on `M_B` (§7.4; block-level constructibility = `mForm_of_qbar` in
`GQ2/FrameEnrichment.lean`), and the descended module `V ≅ M_B/T_B` over the `C`-stage
with the form `q̄_λ` and its fixed equivariant factor-set datum (`κ⁰_{q̄_λ}`, Lemma 6.1 —
the relative hypothesis of `lemma_6_21`, consumed by Lemma 8.7/Prop 8.8, the Prop. 8.9 assembly).
`Enrichment.radData` assembles the per-`λ` Lemma 8.6 datum; `radData_noDescent_iff`
aligns its descent clause with the (139)/(140) case split (the Prop. 8.9 assembly's hand-off to
`lemma_8_6_local`/`_gammaA`). -/

section DerivedLayer

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]

/-- `M_B ◁ B`: image of the normal `K` under the surjection `π_B`. -/
theorem MB_normal : RF.MB.Normal := by
  rw [RF.MB_eq]
  exact Subgroup.Normal.map Blk.hK RF.piB RF.piB_surj

/-- `M_B` has exponent 2: squares of `K` lie in `Φ(K) = ker π_B`. -/
theorem MB_elem : ∀ m ∈ RF.MB, m * m = 1 := by
  intro m hm
  rw [RF.MB_eq] at hm
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
  rw [← map_mul]
  exact MonoidHom.mem_ker.mp (by rw [RF.ker_piB]; exact sq_mem_frattiniLike hk)

/-- `M_B` is abelian: commutators of `K` lie in `Φ(K) = ker π_B`. -/
theorem MB_comm : ∀ m ∈ RF.MB, ∀ m' ∈ RF.MB, m * m' = m' * m := by
  intro m hm m' hm'
  rw [RF.MB_eq] at hm hm'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hm'
  have hc : (k' * k)⁻¹ * (k * k') ∈ RF.piB.ker := by
    rw [RF.ker_piB]
    have he : (k' * k)⁻¹ * (k * k') = k⁻¹ * k'⁻¹ * k⁻¹⁻¹ * k'⁻¹⁻¹ := by group
    rw [he]
    exact comm_mem_frattiniLike (inv_mem hk) (inv_mem hk')
  have h1 := MonoidHom.mem_ker.mp hc
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [← map_mul, ← map_mul]
  exact h1.symm

/-- `T_B` is already the `K ∩ S`-image: the `R`-factor of `T₀ = (K∩S)·R` dies in `B`. -/
theorem TBsub_eq_mapKS : RF.TBsub = (Blk.K ⊓ Blk.S).map RF.piB := by
  have h0 : Blk.frattiniK.map RF.piB = ⊥ := (Subgroup.map_eq_bot_iff _).mpr RF.ker_piB.ge
  rw [RF.TBsub_eq, Subgroup.map_sup, h0, sup_bot_eq]

/-- `T_B ◁ B`: image of the normal `K ∩ S` under the surjection `π_B`. -/
theorem TBsub_normal : RF.TBsub.Normal := by
  rw [RF.TBsub_eq_mapKS]
  exact Subgroup.Normal.map (@Subgroup.normal_inf_normal _ _ Blk.K Blk.S Blk.hK Blk.hS)
    RF.piB RF.piB_surj

/-- `T_B ≤ M_B` (`(K ∩ S) ⊔ R ≤ K`, via `lemma_7_1_head`). -/
theorem TBsub_le_MB : RF.TBsub ≤ RF.MB := by
  rw [RF.TBsub_eq, RF.MB_eq]
  exact blockT_map_le_blockM_map Blk RF.piB

/-- `ker π_{BC} = M_B`: the connecting map `B ↠ C` has the `M`-layer as kernel. -/
theorem ker_piBC : RF.piBC.ker = RF.MB := by
  rw [RF.MB_eq]
  ext bb
  constructor
  · intro hbb
    obtain ⟨y, rfl⟩ := RF.piB_surj bb
    have hy : RF.piC y = 1 :=
      (DFunLike.congr_fun RF.piBC_comp y).symm.trans (MonoidHom.mem_ker.mp hbb)
    refine ⟨y, ?_, rfl⟩
    have hy' : y ∈ RF.piC.ker := MonoidHom.mem_ker.mpr hy
    rwa [RF.ker_piC] at hy'
  · rintro ⟨k, hk, rfl⟩
    have h2 : RF.piC k = 1 := MonoidHom.mem_ker.mp (by rw [RF.ker_piC]; exact hk)
    exact MonoidHom.mem_ker.mpr ((DFunLike.congr_fun RF.piBC_comp k).trans h2)

/-- `π_{BC}` is surjective (it covers the surjection `π_C`). -/
theorem piBC_surj : Function.Surjective RF.piBC := by
  have h : Function.Surjective (RF.piBC.comp RF.piB) := by
    rw [RF.piBC_comp]
    exact RF.piC_surj
  rw [MonoidHom.coe_comp] at h
  exact h.of_comp

/-- **The head factors through `π_{BC}`**: `π^C_Y ∘ π_{BC} = π^B_Y` (the spec fields + `π_B`
epi).  Exported for the D5 boundary-framing argument (the Prop. 8.9 assembly/d6). -/
theorem headBC : RF.TC.piY.comp RF.piBC = RF.TB.piY := by
  have h1 : (RF.TC.piY.comp RF.piBC).comp RF.piB = RF.TB.piY.comp RF.piB := by
    rw [MonoidHom.comp_assoc, RF.piBC_comp, RF.TC_head, RF.TB_head]
  exact (MonoidHom.cancel_right RF.piB_surj).mp h1

/-- **The decoration factors through `π_{BC}`**: `θ^C_Y ∘ π_{BC} = θ^B_Y`. -/
theorem thetaBC : RF.TC.thetaY.comp RF.piBC = RF.TB.thetaY := by
  have h1 : (RF.TC.thetaY.comp RF.piBC).comp RF.piB = RF.TB.thetaY.comp RF.piB := by
    rw [MonoidHom.comp_assoc, RF.piBC_comp, RF.TC_theta, RF.TB_theta]
  exact (MonoidHom.cancel_right RF.piB_surj).mp h1

end DerivedLayer

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Boundary-framing rides free over `ρ`** (the Prop. 8.9 assembly, D5): a continuous hom into `B` lying
over a boundary-framed `C`-lift `ρ` is itself boundary-framed — both boundary components
factor through `π_{BC}`.  This is why the `IsBoundaryLift` clause of `zBC`'s pairs is
redundant, and no `θ|_T` hypotheses are needed in the count. -/
theorem isBoundaryLift_of_over (f : ContinuousMonoidHom Γ RF.YB)
    (ρ : BoundaryLifts b F RF.TC) (hover : ∀ γ, RF.piBC (f γ) = ρ.1.1 γ) :
    IsBoundaryLift b F RF.TB f := by
  intro γ
  have h1 : RF.TB.piY (f γ) = RF.TC.piY (ρ.1.1 γ) := by
    rw [← hover γ]; exact (DFunLike.congr_fun RF.headBC (f γ)).symm
  have h2 : RF.TB.thetaY (f γ) = RF.TC.thetaY (ρ.1.1 γ) := by
    rw [← hover γ]; exact (DFunLike.congr_fun RF.thetaBC (f γ)).symm
  rw [h1, h2]
  exact ρ.2 γ

/-- **The frame enrichment** (the Prop. 8.9 assembly): the per-`λ` data of the §8 analyses that the bare
frame does not determine.  Square-form block: the form `q_λ` of the scalar cover on `M_B`
(cover square relation, `T_B` in the polar radical, vanishing on `T_B`) — with the derived
layer facts above, exactly a per-`λ` Lemma 8.6 datum (`radData`); §7.4 supplies it for the
concrete block (`mForm_of_qbar`).  Descended block: the module `V ≅ M_B/T_B` over the
`C`-stage with the descended form `q̄_λ` (quadratic, nonsingular, invariant — Prop 7.4's
output) and a **fixed equivariant factor-set datum** for it (Lemma 6.1's `κ⁰_{q̄_λ}` — the
relative hypothesis of `lemma_6_21`, consumed by Lemma 8.7/Prop 8.8). -/
structure Enrichment where
  /-- The square form of the scalar cover `p_λ` on `M_B`. -/
  q : (l : RF.DR) → l ≠ RF.zeroDR → ↥RF.MB → ZMod 2
  /-- The cover square relation: `x̃² = z^{q_λ(x)}` over `M_B`. -/
  hq : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (x : (RF.scalarCover l h).cover)
    (hx : (RF.scalarCover l h).p x ∈ RF.MB),
    x * x = (RF.scalarCover l h).z ^ (q l h ⟨(RF.scalarCover l h).p x, hx⟩).val
  /-- `T_B` lies in the polar radical of `q_λ`. -/
  hrad : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (t : RF.YB) (ht : t ∈ RF.TBsub)
    (m : RF.YB) (hm : m ∈ RF.MB),
    polarMul (q l h) (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩)
      ⟨t, RF.TBsub_le_MB ht⟩ ⟨m, hm⟩ = 0
  /-- `q_λ` vanishes on `T_B`. -/
  hTzero : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (t : RF.YB) (ht : t ∈ RF.TBsub),
    q l h ⟨t, RF.TBsub_le_MB ht⟩ = 0
  /-- The descended module `V ≅ M_B/T_B` (abstract carrier; the concrete frame will take
  Prop 7.4's `P/S`-side model, where `q̄_λ` already lives). -/
  Vmod : Type
  [addV : AddCommGroup Vmod]
  [finV : Finite Vmod]
  /-- The `C`-stage action (conjugation, descended through `ker π_{BC} = M_B`). -/
  [actV : DistribMulAction RF.YC Vmod]
  /-- The descent surjection `M_B ↠ V`. -/
  descend : ↥RF.MB →* Multiplicative Vmod
  descend_surj : Function.Surjective descend
  /-- `ker(descend) = T_B`. -/
  descend_ker : ∀ m : ↥RF.MB, descend m = 1 ↔ (m : RF.YB) ∈ RF.TBsub
  /-- `descend` intertwines `B`-conjugation with the action through `π_{BC}`. -/
  descend_conj : ∀ (bb : RF.YB) (m : ↥RF.MB) (hm : bb * ↑m * bb⁻¹ ∈ RF.MB),
    descend ⟨bb * ↑m * bb⁻¹, hm⟩
      = Multiplicative.ofAdd (RF.piBC bb • Multiplicative.toAdd (descend m))
  /-- The descended form `q̄_λ` on `V`. -/
  qbar : (l : RF.DR) → l ≠ RF.zeroDR → Vmod → ZMod 2
  /-- `q_λ = q̄_λ ∘ descend`. -/
  hqbar : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (m : ↥RF.MB),
    q l h m = qbar l h (Multiplicative.toAdd (descend m))
  /-- `q̄_λ` is quadratic (polar form biadditive). -/
  hquad : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), QuadraticFp2.IsQuadraticFp2 (qbar l h)
  /-- `q̄_λ` is nonsingular on `V` (Prop 7.4's nondegeneracy). -/
  hns : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), QuadraticFp2.Nonsingular (qbar l h)
  /-- `q̄_λ` is `C`-invariant (Prop 7.4's `Y`-invariance, descended). -/
  hinv : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), QuadraticFp2.IsInvariant RF.YC (qbar l h)
  /-- The fixed equivariant factor-set datum for `q̄_λ` (Lemma 6.1's base class). -/
  dat : (l : RF.DR) → l ≠ RF.zeroDR → FactorSet RF.YC Vmod
  /-- … satisfying Lemma 6.1's identities for `q̄_λ`. -/
  hdat : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), IsEquivariantFactorSet (qbar l h) (dat l h)

attribute [instance] Enrichment.addV Enrichment.finV Enrichment.actV

variable {RF}

/-- The per-`λ` **Lemma 8.6 datum** assembled from the enrichment: cover `p_λ`, layers
`M_B`/`T_B`, with normality and elementarity derived from the frame and the block. -/
def Enrichment.radData (E : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) :
    RadicalCoverData RF.YB where
  C := RF.scalarCover l h
  M := RF.MB
  hM := RF.MB_normal
  T := RF.TBsub
  hT := RF.TBsub_normal
  hTM := RF.TBsub_le_MB
  helem := RF.MB_elem
  hcomm := RF.MB_comm
  q := E.q l h
  hq := E.hq l h
  hrad := E.hrad l h
  hTzero := E.hTzero l h

end RecursionFrame

open scoped Classical in
/-- **The boxed system of Prop 8.9** for one source `(Γ, b)` and shared data
`(μ, G⁰, phase family)`: the displays (136)–(140), with (141)/(142) folded into (140)
through the `n_{Γ,0}`-liftability form of the signed phase sum (flagged deviation, cf. the
(100)-into-(105) precedent), and all divisions multiplied out. -/
structure ClosedRecursion {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC) : Prop where
  /-- **(136)**, multiplied out: `|D_R| · e_Γ(Y) = z_R · Σ_{λ ∈ D_R} (2 m_{Γ,λ}(B) − e_Γ(B))`. -/
  eq136 : (Nat.card RF.DR : ℤ) * exactImageCount b F T
    = RF.zR * ∑ᶠ l : RF.DR,
        (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB)
  /-- **(137)**, additively: `Z_{Γ,λ}(B/C) = m_{Γ,λ}(B) + Σ_{J < B, J ↠ C} m_{Γ,λ}(J)` (the
  exact-image subtraction; strata missing the `H`-head contribute `0` through the
  totalized `mJOn`).  **Index-set correction.**  The paper's
  sum runs over the proper strata **surjecting onto `C`** (`J ↠ C`) — the `C`-level
  component of a `Z`-pair forces the image stratum onto `C`, and proper `C`-missing strata
  can carry nonzero `m_{Γ,λ}(J)`, so the unrestricted sum would overcount. -/
  eq137 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (RF.zBC b F l h : ℤ) = RF.mB b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (RF.mJOn b F l h J : ℤ)
  /-- **(138)**: each proper summand of (137) opens into the eight-lift partition of the
  `λ`-cover (Lemma 8.3's (124), instantiated at `p_λ`). -/
  eq138 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
      (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)),
    8 * RF.mJ b F l h J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup (RF.scalarCover l h).cover |
          J'.map (RF.scalarCover l h).p = J},
          exactImageCountOn b F ((RF.scalarCover l h).pullTarget RF.TB) J'
  /-- **(139)**: when the `λ`-cover has nonzero radical edge (operationally: no descent to
  `B/T`, cf. `RadicalCoverData.NoDescent`), the compatible-lift count is the half-torsor
  value `2^{2 dim M − 1} e_Γ(C)`, i.e. `2 · Z_{Γ,λ}(B/C) = |M|² · e_Γ(C)`. -/
  eq139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC
  /-- **(140)–(142)**, folded: when the `λ`-cover descends (radical edge zero), the
  compatible-lift count is the constrained Gauss value over the **per-`λ`** phase family
  (paper (134): the classes `Δ_{χ,κ}` carry the scalar-pushout class `κ = κ_λ` of the
  `λ`-cover — a per-`λ`, rather than shared, family, matching the paper; see
  `docs/orchestration/p16d6e-assembly-plan.md` §1A):
  `2^{r+1} Z_{Γ,λ}(B/C) = μ (2^d e_Γ(C) + G⁰ Σ_{ζ ∈ D_T} (2 n_{Γ,0}(ζ_λ) − e_Γ(C)))`, with
  `2^{r+1} = 2|D_T|` and `2^d = |M|/|T| = |V|`. -/
  eq140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * RF.zBC b F l h
        = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (RF.nPhase b F (phase l h ζ) : ℤ) - exactImageCount b F RF.TC))

section Partition137

open scoped Classical

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  (RF : RecursionFrame T Blk)
  (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
  (l : RF.DR) (h : l ≠ RF.zeroDR)

/-- The set of `B`-level lifts underlying `Z_{Γ,λ}(B/C)`: boundary-framed continuous homs
`m : Γ → B` that are `C`-surjective (`π_{BC} ∘ m` onto) and `λ`-compatible (lift through the
scalar cover `p_λ`).  A `Z`-pair is determined by its `m`, so `Z_{Γ,λ}(B/C)` counts this set
(`partition137_zBC_eq_card`); stratifying it by the exact image proves (137). -/
private abbrev partition137Set : Type :=
  {m : ContinuousMonoidHom Γ RF.YB //
    (IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)) ∧
      ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
        ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = m γ}

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), pair elimination**: a `Z`-pair for the `λ`-cover is determined by its `B`-level
lift `m` (its `C`-component is `π_{BC} ∘ m`), so `Z_{Γ,λ}(B/C)` is the cardinality of
`partition137Set`. -/
private theorem partition137_zBC_eq_card :
    RF.zBC b F l h = Nat.card (partition137Set RF b F l h) := by
  refine Nat.card_congr ⟨fun pr => ⟨pr.1.2, ⟨pr.2.2.1, ?_⟩, pr.2.2.2⟩,
    fun m => ⟨(⟨⟨⟨RF.piBC.comp m.1.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp m.1.continuous_toFun⟩,
      m.2.1.2⟩,
      fun γ => by
        show (RF.TC.piY (RF.piBC (m.1 γ)), RF.TC.thetaY (RF.piBC (m.1 γ)))
          = F.frameMap (b γ)
        have h1 : RF.TC.piY (RF.piBC (m.1 γ)) = RF.TB.piY (m.1 γ) :=
          DFunLike.congr_fun RF.headBC (m.1 γ)
        have h2 : RF.TC.thetaY (RF.piBC (m.1 γ)) = RF.TB.thetaY (m.1 γ) :=
          DFunLike.congr_fun RF.thetaBC (m.1 γ)
        rw [h1, h2]
        exact m.2.1.1 γ⟩, m.1), fun γ => rfl, m.2.1.1, m.2.2⟩,
    fun pr => ?_, fun m => ?_⟩
  · have hfun : ⇑RF.piBC ∘ ⇑pr.1.2 = ⇑pr.1.1.1.1 := funext fun γ => pr.2.1 γ
    rw [hfun]
    exact pr.1.1.1.2
  · obtain ⟨⟨f, m⟩, hcompat, hbd, hg⟩ := pr
    refine Subtype.ext (Prod.ext ?_ rfl)
    refine Subtype.ext (Subtype.ext ?_)
    apply ContinuousMonoidHom.ext
    intro γ
    exact hcompat γ
  · exact Subtype.ext rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), top stratum**: the fibre of `partition137Set` over the full image `⊤` is `m_B`
(the `p_λ`-liftable boundary lifts onto `B`). -/
private theorem partition137_card_fiber_top :
    Nat.card {m : partition137Set RF b F l h // m.1.toMonoidHom.range = ⊤}
      = RF.mB b F l := by
  rw [RecursionFrame.mB, dif_neg h]
  refine Nat.card_congr ⟨fun m => ⟨⟨⟨m.1.1, fun y => ?_⟩, m.1.2.1.1⟩, m.1.2.2⟩,
    fun f => ⟨⟨f.1.1.1, ⟨f.1.2, RF.piBC_surj.comp f.1.1.2⟩, f.2⟩, ?_⟩,
    fun m => Subtype.ext (Subtype.ext rfl),
    fun f => Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  · have hy : y ∈ m.1.1.toMonoidHom.range := by rw [m.2]; trivial
    exact hy
  · rw [MonoidHom.range_eq_top]
    exact f.1.1.2

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), proper stratum**: the fibre over a proper, `C`-onto, head-surjective stratum
`J` is `m_{Γ,λ}(J)` (via the corestriction/inclusion equivalence to the stratum lifts). -/
private theorem partition137_card_fiber_stratum (J : Subgroup RF.YB)
    (hJc : J.map RF.piBC = ⊤)
    (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : partition137Set RF b F l h // m.1.toMonoidHom.range = J}
      = RF.mJ b F l h J hJh := by
  rw [RecursionFrame.mJ, liftableCount]
  have hmem : ∀ (m : partition137Set RF b F l h), m.1.toMonoidHom.range = J →
      ∀ γ, m.1 γ ∈ J := by
    intro m hm γ
    have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
    rwa [hm] at this
  refine Nat.card_congr ⟨fun m =>
    ⟨⟨⟨cmhCodRestrict m.1.1 J (hmem m.1 m.2), fun j => ?_⟩, fun γ => ?_⟩, ?_⟩,
    fun f => ⟨⟨cmhInclude J f.1.1.1, ⟨fun γ => f.1.2 γ, ?_⟩, ?_⟩, ?_⟩,
    fun m => Subtype.ext (Subtype.ext rfl),
    fun f => Subtype.ext (Subtype.ext (Subtype.ext (by
      apply ContinuousMonoidHom.ext
      intro γ
      exact Subtype.ext rfl)))⟩
  · -- corestriction surjective onto `↥J`
    have hj : (j : RF.YB) ∈ m.1.1.toMonoidHom.range := by rw [m.2]; exact j.2
    obtain ⟨γ, hγ⟩ := hj
    exact ⟨γ, Subtype.ext hγ⟩
  · -- stratum boundary equation (definitional transport)
    exact m.1.2.1.1 γ
  · -- the ∃g condition transports
    obtain ⟨g, hg⟩ := m.1.2.2
    exact ⟨g, fun γ => hg γ⟩
  · -- `C`-surjectivity of the included map, from `J ↠ C`
    intro c
    have hc : c ∈ J.map RF.piBC := by rw [hJc]; trivial
    obtain ⟨y, hyJ, hyc⟩ := Subgroup.mem_map.mp hc
    obtain ⟨γ, hγ⟩ := f.1.1.2 ⟨y, hyJ⟩
    exact ⟨γ, by
      show RF.piBC ((f.1.1.1 γ : RF.YB)) = c
      rw [hγ, hyc]⟩
  · -- the ∃g condition transports back
    obtain ⟨g, hg⟩ := f.2
    exact ⟨g, fun γ => hg γ⟩
  · -- the included map has range exactly `J`
    have h1 : (cmhInclude J f.1.1.1).toMonoidHom.range
        = f.1.1.1.toMonoidHom.range.map J.subtype := MonoidHom.range_comp _ _
    rw [h1, MonoidHom.range_eq_top.mpr f.1.1.2, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), `C`-missing strata are empty**: the `C`-component of a `Z`-pair is onto `C`, so
no `partition137Set` element has an image whose `π_{BC}`-map misses `C`. -/
private theorem partition137_card_fiber_eq_zero_of_not_map (J : Subgroup RF.YB)
    (hJc : J.map RF.piBC ≠ ⊤) :
    Nat.card {m : partition137Set RF b F l h // m.1.toMonoidHom.range = J} = 0 := by
  have hE : IsEmpty {m : partition137Set RF b F l h // m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJc
    rw [← hm, ← MonoidHom.range_comp]
    rw [MonoidHom.range_eq_top]
    intro c
    obtain ⟨γ, hγ⟩ := m.2.1.2 c
    exact ⟨γ, hγ⟩
  exact Nat.card_of_isEmpty

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), head-missing strata are empty**: a `partition137Set` element is boundary-framed,
so if its image missed the `H`-head the boundary map's head would too, contradicting `hhead`. -/
private theorem partition137_card_fiber_eq_zero_of_not_head
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1)) (J : Subgroup RF.YB)
    (hJh : ¬ Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : partition137Set RF b F l h // m.1.toMonoidHom.range = J} = 0 := by
  have hE : IsEmpty {m : partition137Set RF b F l h // m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJh
    intro hh
    obtain ⟨γ, hγ⟩ := hhead hh
    have hmemJ : m.1 γ ∈ J := by
      have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
      rwa [hm] at this
    refine ⟨⟨m.1 γ, hmemJ⟩, ?_⟩
    show RF.TB.piY (m.1 γ) = hh
    have hbd := m.2.1.1 γ
    have := congrArg Prod.fst hbd
    simpa [hγ] using this
  exact Nat.card_of_isEmpty

end Partition137

open scoped Classical in
/-- **The (137) partition** (the Prop. 8.9 assembly item 2): the `partition137` input of `RecursionInputs`,
derived outright.  A `Z`-pair is determined by its `B`-level lift `m` (the `C`-component is
`π_{BC} ∘ m`); stratifying by the exact image `J = im m` gives the top stratum (`m_B`, at
`J = ⊤`) plus the proper `C`-onto strata (`m_J`, via the corestriction equivalence), while
`C`-missing strata are empty (the pair's `C`-component is onto) and head-missing strata are
empty by the boundary-frame head surjectivity `hhead` — matching `mJOn`'s zero branch. -/
theorem partition137_of {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    (RF.zBC b F l h : ℤ) = RF.mB b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (RF.mJOn b F l h J : ℤ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLifts b F RF.TB) := finite_boundaryLifts b F RF.TB hfg
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Finite (Subgroup RF.YB) :=
    Finite.of_injective (fun J : Subgroup RF.YB => (J : Set RF.YB)) SetLike.coe_injective
  haveI : Fintype (Subgroup RF.YB) := Fintype.ofFinite _
  -- ===== Step 1: eliminate the pair — `Z` is a set of `B`-level lifts =====
  set Mset := partition137Set RF b F l h with hMsetdef
  haveI : Finite Mset := Subtype.finite
  have e1 : RF.zBC b F l h = Nat.card Mset := partition137_zBC_eq_card RF b F l h
  -- ===== Step 2: stratify by the exact image =====
  have e2 : Nat.card Mset
      = ∑ J : Subgroup RF.YB, Nat.card {m : Mset // m.1.toMonoidHom.range = J} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun m : Mset => m.1.toMonoidHom.range)).symm, Nat.card_sigma]
  -- ===== Step 3: the fibres (top `m_B`, proper `m_J`, empty off the `C`/`H` heads) =====
  have htop : Nat.card {m : Mset // m.1.toMonoidHom.range = ⊤} = RF.mB b F l :=
    partition137_card_fiber_top RF b F l h
  have hstr : ∀ (J : Subgroup RF.YB) (_hJc : J.map RF.piBC = ⊤)
      (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)),
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = RF.mJ b F l h J hJh :=
    fun J hJc hJh => partition137_card_fiber_stratum RF b F l h J hJc hJh
  have hemptyC : ∀ (J : Subgroup RF.YB), J.map RF.piBC ≠ ⊤ →
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = 0 :=
    fun J hJc => partition137_card_fiber_eq_zero_of_not_map RF b F l h J hJc
  have hemptyH : ∀ (J : Subgroup RF.YB),
      ¬ Function.Surjective (RF.TB.piY.comp J.subtype) →
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = 0 :=
    fun J hJh => partition137_card_fiber_eq_zero_of_not_head RF b F l h hhead J hJh
  -- ===== Step 4: assemble =====
  set fib : Subgroup RF.YB → ℕ :=
    fun J => Nat.card {m : Mset // m.1.toMonoidHom.range = J} with hfibdef
  set S : Finset (Subgroup RF.YB) :=
    ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤).filter
      (fun J => J.map RF.piBC = ⊤) with hSdef
  have hsplit : ∑ J : Subgroup RF.YB, fib J
      = fib ⊤ + ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ ⊤)]
  have hrest : ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J
      = ∑ J ∈ S, fib J := by
    rw [hSdef,
      ← Finset.sum_filter_add_sum_filter_not
        ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤)
        (fun J => J.map RF.piBC = ⊤) fib]
    have hz : ∑ J ∈ ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤).filter
          (fun J => ¬ J.map RF.piBC = ⊤), fib J = 0 := by
      refine Finset.sum_eq_zero fun J hJ => ?_
      exact hemptyC J (Finset.mem_filter.mp hJ).2
    rw [hz, add_zero]
  have hmatch : ∀ J ∈ S, fib J = RF.mJOn b F l h J := by
    intro J hJ
    rw [hSdef] at hJ
    obtain ⟨hJne, hJc⟩ := Finset.mem_filter.mp hJ
    rw [RecursionFrame.mJOn]
    by_cases hJh : Function.Surjective (RF.TB.piY.comp J.subtype)
    · rw [dif_pos hJh]
      exact hstr J hJc hJh
    · rw [dif_neg hJh]
      exact hemptyH J hJh
  -- convert the RHS finsum to the same Finset sum
  have hsetconv : {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤} = ↑S := by
    rw [hSdef]
    ext J
    simp [Finset.mem_erase, and_comm]
  have hfinsum : ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
        (RF.mJOn b F l h J : ℤ)
      = ∑ J ∈ S, (RF.mJOn b F l h J : ℤ) := by
    rw [hsetconv, finsum_mem_coe_finset]
  -- the `ℕ`-level identity
  have hnat : RF.zBC b F l h = RF.mB b F l + ∑ J ∈ S, RF.mJOn b F l h J := by
    calc RF.zBC b F l h = Nat.card Mset := e1
      _ = ∑ J : Subgroup RF.YB, fib J := e2
      _ = fib ⊤ + ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J := hsplit
      _ = RF.mB b F l + ∑ J ∈ S, fib J := by
          have htop' : fib ⊤ = RF.mB b F l := htop
          rw [htop', hrest]
      _ = RF.mB b F l + ∑ J ∈ S, RF.mJOn b F l h J := by
          rw [Finset.sum_congr rfl hmatch]
  -- final computation over `ℤ`
  rw [hfinsum, hnat]
  push_cast
  ring

open scoped Classical in
/-- **The source-side input bundle of the Prop 8.9 assembly** (the Prop. 8.9 assembly skeleton).  Each field
is one gated derivation of the boxed recursion, with its intended supplier recorded; the
displays **(137) and (138) are *not* inputs** — `prop_8_9_aux` discharges them from the
proved `partition137_of` and `lemma_8_3`.

* `stageR136` — the final `R`-lifting stage: Fourier inversion (125)/`lemma_8_4` over `D_R`,
  the `z_R` torsor multiplicity (5.15/5.16 numerics at the abelian `R`), and the automatic
  surjectivity of `R`-lifts (`GQ2.eq_top_of_map_frattini_quotient_top`, proved).
* `half139` — the nonzero-edge half count: the `zBC ↔ MLifts` fibration bridge composed with
  the half-torsor Lemma 8.6 (`lemma_8_6_local` **proved** for the `G_ℚ₂` source;
  `lemma_8_6_gammaA` = the Γ_A half-torsor proof, gated on the Prop. 5.15 proof).
* `phase140` — the zero-edge constrained-Gauss value: the descended `V ⋊ C` splitting
  (`lemma_6_21`, proved), Lemma 8.7's affine `T`-lifting, the completed-square identity
  (135)/Prop 8.8, and `lemma_8_5`, summed over lower exact-image maps. -/
structure RecursionInputs {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC) : Prop where
  /-- The (136)-stage identity (gated: `lemma_8_4` + `z_R` numerics + Frattini lift
  surjectivity). -/
  stageR136 : (Nat.card RF.DR : ℤ) * exactImageCount b F T
    = RF.zR * ∑ᶠ l : RF.DR,
        (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB)
  /-- The (139) half count (gated: the `zBC` bridge + the source's Lemma 8.6). -/
  half139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC
  /-- The (140) constrained-Gauss value (gated: 8.5 + 8.7 + (135)/8.8 + 6.21/6.22 chain);
  per-`λ` phase family per the paper's `Δ_{χ,κ_λ}` (the Prop. 8.9 assembly amendment). -/
  phase140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * RF.zBC b F l h
        = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (RF.nPhase b F (phase l h ζ) : ℤ) - exactImageCount b F RF.TC))

open scoped Classical in
/-- **The Prop 8.9 assembly step** (the Prop. 8.9 assembly): given the source-side input bundle, the boxed
system holds — with **(138) discharged from the proved `lemma_8_3`** (the eight-lift
partition, instantiated at each scalar cover `p_λ` over the `B`-stage target).  The
side conditions (`Γ` profinite + t.f.g. `hfg`, `#Hom(Γ,𝔽₂) = 8`) are exactly `lemma_8_3`'s;
both real sources satisfy them (`lemma_8_2` and the boundary-frame data). -/
theorem prop_8_9_aux {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (inp : RecursionInputs RF b F μ G0 DT phase) :
    ClosedRecursion RF b F μ G0 DT phase where
  eq136 := inp.stageR136
  eq137 := partition137_of RF hfg b F hhead
  eq138 := fun l h => lemma_8_3 hfg b F RF.TB (RF.scalarCover l h) hscalar
  eq139 := inp.half139
  eq140 := inp.phase140

open scoped Classical in
/-- **The (136) stage, combinatorial core** (the Prop. 8.9 assembly item 1): the `stageR136` input of
`RecursionInputs` follows from an **obstruction-module datum** for the `R`-stage.  Given

* an `𝔽₂`-module `W` with an obstruction map `o` on the `B`-stage lifts whose vanishing
  detects liftability to `Y` (`hobs`),
* an identification `e : D_R ≃ W^∨` with `e 0 = 0` matching the scalar-pushout counts
  (`hmB` — "`λ_* o = 0` iff the lift factors through the `λ`-cover"), and
* the constant fibre size `z_R` over liftable points (`hfib` — the `R`-lift torsor count;
  its nonempty-fibre surjectivity onto `Y` is `GQ2.eq_top_of_map_frattini_quotient_top`),

the display (136) follows by the `liftB`-fibration and the Fourier engine `lemma_8_4`.
The three inputs are the analytic residue of the stage: `W`/`o`/`e` come from the concrete
`R`-stage obstruction theory, `hfib` from the 5.15/5.16 `Z¹`-numerics of the source
interface. -/
theorem stageR136_of {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (o : BoundaryLifts b F RF.TB → W)
    (e : RF.DR ≃ Module.Dual (ZMod 2) W)
    (he0 : e RF.zeroDR = 0)
    (hmB : ∀ (l : RF.DR), l ≠ RF.zeroDR →
      RF.mB b F l = Nat.card {g : BoundaryLifts b F RF.TB // e l (o g) = 0})
    (hobs : ∀ g : BoundaryLifts b F RF.TB,
      o g = 0 ↔ ∃ f : BoundaryLifts b F T, RF.liftB b F f = g)
    (hfib : ∀ g : BoundaryLifts b F RF.TB, o g = 0 →
      Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
  classical
  haveI : Finite (BoundaryLifts b F T) := finite_boundaryLifts b F T hfg
  haveI : Finite (BoundaryLifts b F RF.TB) := finite_boundaryLifts b F RF.TB hfg
  haveI : Fintype (BoundaryLifts b F RF.TB) := Fintype.ofFinite _
  -- Step 1 (fibration): `e_Γ(Y) = z_R · #{o = 0}`.
  have h1 : exactImageCount b F T
      = RF.zR * Nat.card {g : BoundaryLifts b F RF.TB // o g = 0} := by
    have hsig : exactImageCount b F T
        = ∑ g : BoundaryLifts b F RF.TB,
            Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} := by
      rw [exactImageCount,
        Nat.card_congr (Equiv.sigmaFiberEquiv (RF.liftB b F)).symm, Nat.card_sigma]
    rw [hsig]
    have hterm : ∀ g : BoundaryLifts b F RF.TB,
        Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g}
          = if o g = 0 then RF.zR else 0 := by
      intro g
      by_cases hg : o g = 0
      · rw [if_pos hg]
        exact hfib g hg
      · rw [if_neg hg]
        have hempty : IsEmpty {f : BoundaryLifts b F T // RF.liftB b F f = g} := by
          constructor
          rintro ⟨f, hf⟩
          exact hg ((hobs g).mpr ⟨f, hf⟩)
        exact Nat.card_of_isEmpty
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 2 (Fourier): `lemma_8_4` at the obstruction map.
  have h2 := lemma_8_4 (X := BoundaryLifts b F RF.TB) (W := W) o
  haveI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod 2) W => (φ : W → ZMod 2))
      DFunLike.coe_injective
  haveI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  -- Step 3 (reindex the character sum along `e`, matching `m_B`).
  have h3 : ∑ᶠ φ : Module.Dual (ZMod 2) W,
        (2 * (Nat.card {g : BoundaryLifts b F RF.TB // φ (o g) = 0} : ℤ)
          - Nat.card (BoundaryLifts b F RF.TB))
      = ∑ᶠ l : RF.DR, (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Equiv.sum_comp e (fun φ =>
        2 * (Nat.card {g : BoundaryLifts b F RF.TB // φ (o g) = 0} : ℤ)
          - Nat.card (BoundaryLifts b F RF.TB))]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = RF.zeroDR
    · subst hl
      rw [he0]
      have hall : Nat.card {g : BoundaryLifts b F RF.TB //
          (0 : Module.Dual (ZMod 2) W) (o g) = 0} = Nat.card (BoundaryLifts b F RF.TB) := by
        refine Nat.card_congr (Equiv.subtypeUnivEquiv fun g => ?_)
        simp
      have hmB0 : RF.mB b F RF.zeroDR = exactImageCount b F RF.TB := by
        rw [RecursionFrame.mB, dif_pos rfl]
      rw [hall, hmB0, exactImageCount]
    · rw [hmB l hl]
      rfl
  -- Assemble in `ℤ`.
  have hcardDR : (Nat.card RF.DR : ℤ) = Nat.card (Module.Dual (ZMod 2) W) := by
    exact_mod_cast Nat.card_congr e
  calc (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = (Nat.card RF.DR : ℤ)
        * (RF.zR * Nat.card {g : BoundaryLifts b F RF.TB // o g = 0}) := by
        rw [h1]; push_cast; ring
    _ = RF.zR * ((Nat.card (Module.Dual (ZMod 2) W) : ℤ)
        * Nat.card {g : BoundaryLifts b F RF.TB // o g = 0}) := by
        rw [← hcardDR]; ring
    _ = RF.zR * ∑ᶠ φ : Module.Dual (ZMod 2) W,
          (2 * (Nat.card {g : BoundaryLifts b F RF.TB // φ (o g) = 0} : ℤ)
            - Nat.card (BoundaryLifts b F RF.TB)) := by
        rw [h2]
    _ = RF.zR * ∑ᶠ l : RF.DR, (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
        rw [h3]

/-! **Proposition 8.9 (closed exact-image recursion)** — statement **relocated** to
`GQ2/Prop89Close.lean` (`GQ2.SectionEight.prop_8_9`), the Prop. 8.9 assembly capstone leaf (the
`thm_4_2`-relocation pattern: the statement is specialized to the concrete block frame
`blockFrameImpl T Blk hE2`, which this file cannot name — it sits above `BlockFrameImpl.lean`
in the import order).  Two reviewed statement actions at the relocation
(`docs/orchestration/p16d6e-assembly-plan.md` §1):

* the phase family is **per-`λ`** (`phase : (l : DR) → l ≠ zeroDR → DT → CentralCover YC`) —
  the paper's (134) classes `Δ_{χ,κ}` carry the scalar-pushout class `κ = κ_λ` of the
  `λ`-cover, so the shared-family draft form was a transcription deviation (Bug-3 of the
  c-lane family; a shared family would force an unproven `zBC`-l-independence);
* the frame is the **concrete block frame** with hypothesis ledger
  `{hE2, hfgF (B1 → the §9 induction), hheadA, hheadF, hsimple, hfaith, hVne, hG0indep}` and the §9 induction
  strengthening `0 < Nat.card DT` in the conclusion — general-`RF` (136) is not provable
  (no axioms tie the bare frame's `DR`/`zR`/`mB` to obstruction theory; the Prop. 8.9 assembly built the
  R-stage against `blockFrameImpl` by decision), and SectionNine's inductive branch consumes
  the proposition exactly at `blockFrame = blockFrameImpl`. -/

end Recursion

end SectionEight

end GQ2
