/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Block.FrameImpl
import GQ2.RStage.ObstructionBuild

/-!
# The concrete R-stage obstruction datum + (136) for `blockFrame`

Builds `RObstructionData (blockFrameImpl T Blk hE2)` — the (136) `stageR136` datum — against the
concrete §7-block frame (the §9 induction ✓, `blockFrameImpl`), and wires it into `stageR136_ofRSepData`
to produce the (136) identity `blockStageR136`.

Concrete covers (`blockFrameImpl`): `YB = Y/R`, `piB = mk' R`, `scalarCover l h` = the cover
`Y/l ↠ Y/R` (`cover = Y/l.1`, `p = map l.1 R id`, `z = mk' l.1 r₀`).  So `coverMap l h = mk' l.1`
and `coverMap_lifts` is `map ∘ mk' = mk'`.

**a-DRmod / a-assemble** (std-3): `blockRObstructionData` — the full `(R^∨)^C` character duality.

**a-residues** (`blockStageR136`): `hE2` is discharged from the frame argument; the source residues
`htriv`/`hcard`/`hfg`/`hZcount`/`hsep_hom` are threaded as hypotheses (supplied by the Prop. 8.9 assembly
assembly / the §9 induction, where `Γ = GammaA`/`AbsGalQ2` carry the concrete trivial action and the 5.15/5.16
numerics).  `hZcount` (the `z_R = #R²·#D_R` torsor count) and `hsep_hom` (the `(R^∨)^C`-separation)
are the two irreducible source cores — see the notes on `blockStageR136`.
-/

namespace GQ2

open SectionEight SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- The R-stage compat covers of the concrete block frame: `coverMap l h = mk' l.1`. -/
noncomputable def blockRCoverData (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    RCoverData (blockFrameImpl T Blk hE2) where
  coverMap := fun l _h => haveI : (l.1).Normal := l.2.1; QuotientGroup.mk' l.1
  coverMap_lifts := fun l _h => by
    haveI : (l.1).Normal := l.2.1
    ext y
    rfl

/-! ## A-DRmod: `D_Rmod` as the Y-invariant `𝔽₂`-characters of `R` -/

open scoped Classical

variable {L : Subgroup Y}

/-- **Y-invariant `𝔽₂`-characters of `R = Blk.frattiniK = Φ(K)`** (`(R^∨)^C`): additive homs
`R → 𝔽₂` fixed by `Y`-conjugation.  Their kernels are exactly the index-≤2 `Y`-normal
subgroups of `R`, i.e. `D_R`; this submodule is the `𝔽₂`-realization `D_Rmod`. -/
def RCharSub (Blk : SectionSeven.MinimalBlock L) :
    Submodule (ZMod 2) (Additive ↥Blk.frattiniK →+ ZMod 2) where
  carrier := {χ | ∀ (y : Y) (r : ↥Blk.frattiniK),
    χ (Additive.ofMul ⟨y * (r : Y) * y⁻¹,
        (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 y⟩)
      = χ (Additive.ofMul r)}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {χ ψ} hχ hψ y r => by
    simp only [AddMonoidHom.add_apply, hχ y r, hψ y r]
  smul_mem' := fun c {χ} hχ y r => by
    simp only [AddMonoidHom.smul_apply, hχ y r]

/-- `D_Rmod` is finite. -/
instance (Blk : SectionSeven.MinimalBlock L) : Finite ↥(RCharSub Blk) := by
  haveI : Finite (Additive ↥Blk.frattiniK →+ ZMod 2) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Additive ↥Blk.frattiniK →+ ZMod 2))
  infer_instance

/-- The kernel of a character `χ`, as a subgroup of `↥Blk.frattiniK`. -/
def RCharKerSub (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    Subgroup ↥Blk.frattiniK where
  carrier := {r | χ.1 (Additive.ofMul r) = 0}
  one_mem' := map_zero χ.1
  mul_mem' := fun {a b} ha hb => by
    show χ.1 (Additive.ofMul (a * b)) = 0
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
      map_add, ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    show χ.1 (Additive.ofMul a⁻¹) = 0
    rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a from rfl, map_neg, ha, neg_zero]

/-- `χ` as a `MonoidHom ↥R →* Multiplicative 𝔽₂` (for the kernel/index calculus). -/
def RCharMulHom (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    ↥Blk.frattiniK →* Multiplicative (ZMod 2) where
  toFun r := Multiplicative.ofAdd (χ.1 (Additive.ofMul r))
  map_one' := by
    show Multiplicative.ofAdd (χ.1 (Additive.ofMul (1 : ↥Blk.frattiniK))) = 1
    rw [show Additive.ofMul (1 : ↥Blk.frattiniK) = 0 from rfl, map_zero]; rfl
  map_mul' := fun a b => by
    show Multiplicative.ofAdd (χ.1 (Additive.ofMul (a * b))) = _ * _
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add]; rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
theorem RCharKerSub_eq_ker (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    RCharKerSub Blk χ = (RCharMulHom Blk χ).ker := by
  ext r
  rw [MonoidHom.mem_ker]
  show χ.1 (Additive.ofMul r) = 0 ↔ Multiplicative.ofAdd (χ.1 (Additive.ofMul r)) = 1
  rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq]

/-- The kernel of `χ`, pushed to a subgroup of `Y`. -/
def RCharKer (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) : Subgroup Y :=
  (RCharKerSub Blk χ).map Blk.frattiniK.subtype

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
private theorem RCharKer_le (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    RCharKer Blk χ ≤ Blk.frattiniK :=
  Subgroup.map_subtype_le _

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
private theorem RCharKer_normal (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (RCharKer Blk χ).Normal := by
  constructor
  intro n hn g
  rw [RCharKer, Subgroup.mem_map] at hn ⊢
  obtain ⟨r, hr, rfl⟩ := hn
  refine ⟨⟨g * (r : Y) * g⁻¹,
      (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 g⟩, ?_, rfl⟩
  show χ.1 (Additive.ofMul ⟨g * (r : Y) * g⁻¹, _⟩) = 0
  rwa [χ.2 g r]

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
private theorem RCharKer_relIndex_le (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (RCharKer Blk χ).relIndex Blk.frattiniK ≤ 2 := by
  have h1 : (RCharKer Blk χ).relIndex Blk.frattiniK = (RCharKerSub Blk χ).index := by
    rw [Subgroup.relIndex, RCharKer, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective Blk.frattiniK.subtype_injective]
  rw [h1, RCharKerSub_eq_ker, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq
    (by rw [Nat.card_eq_fintype_card]; rfl)

/-- The `D_R` index type of the concrete frame `blockFrameImpl` (defeq to its `.DR`). -/
abbrev BlockDRsub (Blk : SectionSeven.MinimalBlock L) : Type :=
  {R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.frattiniK ∧ R'.relIndex Blk.frattiniK ≤ 2}

/-- **The inverse direction**: the index-≤2 indicator character `r ↦ [r ∉ R']` of a `D_R`
element, as an additive hom (additive by `mul_mem_iff_of_index_two`, with the `index ≤ 2`
case-split covering `R' = R` — the zero character). -/
noncomputable def RCharOfHom (Blk : SectionSeven.MinimalBlock L) (R' : BlockDRsub Blk) :
    Additive ↥Blk.frattiniK →+ ZMod 2 where
  toFun r := if ((Additive.toMul r : ↥Blk.frattiniK) : Y) ∈ R'.1 then 0 else 1
  map_zero' := by
    show (if ((Additive.toMul (0 : Additive ↥Blk.frattiniK) : ↥Blk.frattiniK) : Y) ∈ R'.1
      then (0 : ZMod 2) else 1) = 0
    exact if_pos (one_mem R'.1)
  map_add' a b := by
    show (if ((Additive.toMul a * Additive.toMul b : ↥Blk.frattiniK) : Y) ∈ R'.1
        then (0 : ZMod 2) else 1)
      = (if ((Additive.toMul a : ↥Blk.frattiniK) : Y) ∈ R'.1 then 0 else 1)
        + (if ((Additive.toMul b : ↥Blk.frattiniK) : Y) ∈ R'.1 then 0 else 1)
    have hidx : (R'.1.subgroupOf Blk.frattiniK).index ≤ 2 := R'.2.2.2
    rcases Nat.lt_or_ge (R'.1.subgroupOf Blk.frattiniK).index 2 with hlt | hge
    · have h1 : (R'.1.subgroupOf Blk.frattiniK).index = 1 := by
        have hne0 : (R'.1.subgroupOf Blk.frattiniK).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        lia
      have htop : R'.1.subgroupOf Blk.frattiniK = ⊤ := Subgroup.index_eq_one.mp h1
      have hmem : ∀ x : ↥Blk.frattiniK, (x : Y) ∈ R'.1 := fun x => by
        have hx : x ∈ R'.1.subgroupOf Blk.frattiniK := htop ▸ Subgroup.mem_top x
        rwa [Subgroup.mem_subgroupOf] at hx
      rw [if_pos (hmem _), if_pos (hmem _), if_pos (hmem _), add_zero]
    · have h2 : (R'.1.subgroupOf Blk.frattiniK).index = 2 := le_antisymm hidx hge
      have hkey := mul_mem_iff_of_index_two h2 (Additive.toMul a) (Additive.toMul b)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hkey
      by_cases h1 : ((Additive.toMul a : ↥Blk.frattiniK) : Y) ∈ R'.1 <;>
        by_cases h2' : ((Additive.toMul b : ↥Blk.frattiniK) : Y) ∈ R'.1 <;>
        simp only [Subgroup.coe_mul, hkey, h1, h2', if_true, if_false, iff_true, iff_false,
          iff_self] <;> decide

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `RCharOfHom R'` is Y-invariant, hence a member of `RCharSub` — from `R'.Normal`. -/
theorem RCharOf_mem (Blk : SectionSeven.MinimalBlock L) (R' : BlockDRsub Blk) :
    RCharOfHom Blk R' ∈ RCharSub Blk := by
  intro y r
  show (if ((⟨y * (r : Y) * y⁻¹,
        (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 y⟩ :
          ↥Blk.frattiniK) : Y)
      ∈ R'.1 then (0 : ZMod 2) else 1)
    = if ((r : ↥Blk.frattiniK) : Y) ∈ R'.1 then 0 else 1
  by_cases hrl : ((r : ↥Blk.frattiniK) : Y) ∈ R'.1
  · rw [if_pos (R'.2.1.conj_mem _ hrl y), if_pos hrl]
  · have hnot : y * (r : Y) * y⁻¹ ∉ R'.1 := fun h => hrl (by
      have hc := R'.2.1.conj_mem _ h y⁻¹
      rwa [show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y) from by group] at hc)
    rw [if_neg hnot, if_neg hrl]

/-- The inverse map `D_R → D_Rmod`: `R' ↦` its index-≤2 indicator character. -/
noncomputable def RCharOf (Blk : SectionSeven.MinimalBlock L) (R' : BlockDRsub Blk) :
    ↥(RCharSub Blk) := ⟨RCharOfHom Blk R', RCharOf_mem Blk R'⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
/-- A character is the indicator of its own kernel (`𝔽₂`-valued). -/
theorem RChar_eq_ind (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk))
    (r : ↥Blk.frattiniK) :
    χ.1 (Additive.ofMul r) = if r ∈ RCharKerSub Blk χ then 0 else 1 := by
  by_cases h : r ∈ RCharKerSub Blk χ
  · rwa [if_pos h]
  · rw [if_neg h]
    exact ((by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) _).resolve_left h

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Right inverse**: the kernel of the indicator character of `R'` is `R'`. -/
theorem RCharKer_RCharOf (Blk : SectionSeven.MinimalBlock L) (R' : BlockDRsub Blk) :
    RCharKer Blk (RCharOf Blk R') = R'.1 := by
  have hker : RCharKerSub Blk (RCharOf Blk R') = R'.1.subgroupOf Blk.frattiniK := by
    ext r
    rw [Subgroup.mem_subgroupOf]
    show (if ((r : ↥Blk.frattiniK) : Y) ∈ R'.1 then (0 : ZMod 2) else 1) = 0
      ↔ ((r : ↥Blk.frattiniK) : Y) ∈ R'.1
    by_cases h : ((r : ↥Blk.frattiniK) : Y) ∈ R'.1 <;> simp [h]
  rw [RCharKer, hker, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr R'.2.2.1]

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
/-- **Injectivity** of `χ ↦ ker χ`: a character is determined by its kernel. -/
theorem RCharKer_inj (Blk : SectionSeven.MinimalBlock L) :
    Function.Injective (fun χ : ↥(RCharSub Blk) => RCharKer Blk χ) := by
  intro χ χ' hker
  have hsub : RCharKerSub Blk χ = RCharKerSub Blk χ' := by
    have h := congrArg (fun S => S.comap Blk.frattiniK.subtype) hker
    simpa only [RCharKer,
      Subgroup.comap_map_eq_self_of_injective Blk.frattiniK.subtype_injective] using h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  show χ.1 (Additive.ofMul (Additive.toMul a)) = χ'.1 (Additive.ofMul (Additive.toMul a))
  rw [RChar_eq_ind, RChar_eq_ind, hsub]

/-! ## A-DRmod: assembling the `(R^∨)^C` bijection and `pair` -/

/-- **The `(R^∨)^C` bijection** `D_Rmod ≃ D_R`: `χ ↦ ker χ` (inverse `R' ↦` its indicator).
Codomain is the concrete frame's `.DR` (so the assembly's `pair_coverMap` types align). -/
noncomputable def blockToDR (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    ↥(RCharSub Blk) ≃ (blockFrameImpl T Blk hE2).DR :=
  Equiv.ofBijective
    (fun χ => ⟨RCharKer Blk χ, RCharKer_normal Blk χ, RCharKer_le Blk χ,
      RCharKer_relIndex_le Blk χ⟩)
    ⟨fun _ _ h => RCharKer_inj Blk (Subtype.ext_iff.mp h),
     fun R' => ⟨RCharOf Blk R', Subtype.ext (RCharKer_RCharOf Blk R')⟩⟩

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
@[simp] private theorem blockToDR_coe (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) (χ : ↥(RCharSub Blk)) :
    (blockToDR T Blk hE2 χ).1 = RCharKer Blk χ := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] in
/-- The zero character's kernel is all of `R` (`= zeroDR`). -/
theorem RCharKer_zero (Blk : SectionSeven.MinimalBlock L) : RCharKer Blk 0 = Blk.frattiniK := by
  have hsub : RCharKerSub Blk 0 = ⊤ := by
    ext r
    simp only [Subgroup.mem_top, iff_true]
    rfl
  rw [RCharKer, hsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-! ## A-assemble: the concrete R-stage obstruction datum `blockRObstructionData` -/

/-- **The concrete R-stage obstruction datum** for the §7-block frame (the Prop. 8.9 assembly): assembles
`blockRCoverData` with the `(R^∨)^C` module `D_Rmod = RCharSub`, the bijection `blockToDR`, and
`pair =` the submodule inclusion, whose `pair_coverMap` matches the cover kernel-sign `zsign`
(`= [r ∉ ker d]`).  This is the `RObstructionData` input to `stageR136_ofRSepData`. -/
noncomputable def blockRObstructionData (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1) :
    RObstructionData (blockFrameImpl T Blk hE2) where
  toRCoverData := blockRCoverData T Blk hE2
  DRmod := ↥(RCharSub Blk)
  toDR := blockToDR T Blk hE2
  h0 := by
    refine (blockToDR T Blk hE2).symm_apply_eq.mpr (Subtype.ext ?_)
    show Blk.frattiniK = (blockToDR T Blk hE2 0).1
    rw [blockToDR_coe, RCharKer_zero]
  pair := (RCharSub Blk).subtype
  pair_coverMap := fun d h r => by
    haveI hN : (RCharKer Blk d).Normal := RCharKer_normal Blk d
    have hmem : (QuotientGroup.mk' (RCharKer Blk d) (r : Y) = 1) ↔ (r ∈ RCharKerSub Blk d) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, RCharKer, Subgroup.mem_map]
      constructor
      · rintro ⟨s, hs, hsr⟩
        rwa [Subtype.coe_injective hsr] at hs
      · intro hr
        exact ⟨r, hr, rfl⟩
    have hcov : (blockRCoverData T Blk hE2).coverMap (blockToDR T Blk hE2 d) h (r : Y)
        = QuotientGroup.mk' (RCharKer Blk d) (r : Y) := rfl
    rw [Submodule.subtype_apply, RChar_eq_ind, hcov]
    by_cases hr : r ∈ RCharKerSub Blk d
    · rw [if_pos hr, hmem.mpr hr]
      exact (CentralObstruction.zsign_one _).symm
    · rw [if_neg hr]
      have hne : QuotientGroup.mk' (RCharKer Blk d) (r : Y) ≠ 1 := fun hc => hr (hmem.mp hc)
      exact (if_neg hne).symm

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The `(R^∨)^C = D_R` cardinality bridge.**  The `Y`-invariant `𝔽₂`-characters of `R`
(`RCharSub = D_Rmod = (R^∨)^C`) are equinumerous with the R-stage index type `D_R` of the concrete
frame, since `blockToDR` is a bijection.  So the `z_R = #R²·#D_R` torsor count's `#D_R` factor is
the intrinsic invariant-character count `#(R^∨)^C` — the shape the 5.15/5.16 Euler characteristic
`#Z¹(Γ,R) = #R²·#(R^∨)^C` produces, which is what a `hZcount` discharge targets. -/
theorem blockRChar_card (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    Nat.card ↥(RCharSub Blk) = Nat.card (blockFrameImpl T Blk hE2).DR :=
  Nat.card_congr (blockToDR T Blk hE2)

/-! ## A-residues → (136): wiring `blockRObstructionData` into `stageR136_ofRSepData` -/

section StageR136

open ContCoh

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **the Prop. 8.9 assembly (136) for the concrete §7-block frame.**  Instantiates the abstract R-stage finish
line `stageR136_ofRSepData` at the concrete frame `blockFrameImpl` with the concrete obstruction
datum `blockRObstructionData` (the full `(R^∨)^C` character duality, std-3).  `hE2` is discharged
from the frame's own argument; the remaining inputs are the source residues threaded by the
the Prop. 8.9 assembly:

* `htriv` — the trivial `Γ`-action on `𝔽₂` (`fun _ _ => rfl` once `Γ = GammaA`/`AbsGalQ2`);
* `hcard` — `#H²(Γ,𝔽₂) = 2` (props 5.15/5.16);
* `hfg` — `Γ` topologically finitely generated (`GammaA` via the finite-generation proof; `AbsGalQ2` via B1, reserved to
  the §9 induction — kept hypothesis-side);
* `hsep_hom` — **the `(R^∨)^C`-separation** `obs g = 0 ⟹ g` has a homomorphism lift to `Y`.  This
  is the Γ-specific arithmetic duality `D_R = (R^∨)^C ≅ H²_{Γ,ρ}(R)^∨` — the `R`-instance of the
  duality the paper displays for the phase module `T` (p. 42 top), used implicitly by Prop 8.9 (the
  `z_R` display and the Fourier inversion over `D_R`): `obs g d = ⟨d, ob(g)⟩` pairs `d` with the
  full `R`-obstruction, and the perfect pairing forces `ob(g) = 0` (hence a lift) once every `d`
  kills it.  Props 5.15/5.16, NOT abstract; discharged per-Γ at assembly alongside `hZcount`.
  Prefer consuming via `blockStageR136_ofSplitCriterion` below, which pre-discharges all the frame
  plumbing and leaves only the cochain-level split criterion.
* `hZcount` — **the `z_R` torsor count** `#RCocycle = z_R = #R²·#D_R = |Z¹_{Γ,ρ}(R)|` (the 5.15/5.16
  numeric for the `R`-extension, the (139)-`hMcount` analogue).

The conclusion is the `stageR136` field of `RecursionInputs` verbatim (for the Prop. 8.9 assembly). -/
theorem blockStageR136 (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hsep_hom : ∀ g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv hcard g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLifts b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) = (blockFrameImpl T Blk hE2).zR) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  stageR136_ofRSepData (RF := blockFrameImpl T Blk hE2) b F
    (blockRObstructionData T Blk hE2) htriv hcard hfg hE2 hsep_hom hZcount

/-! ### The per-`Γ` residue interface: the split criterion

`hsep_hom_of_splitCriterion` strips the last frame-generic layer off `hsep_hom`: the obstruction
functional and its `H²(Γ,𝔽₂)` classes (`obs_zero_iff_pairClass_zero`), the degenerate `d = 0`
character, and the split-cochain → hom-lift assembly (`homLift_of_split`) are all discharged here,
so a source supplies only the **split criterion** — the `(R^∨)^C`-separation at the cochain level:
*if every invariant character `d` sends the `R`-valued section defect of `g` to a coboundary class
in `H²(Γ,𝔽₂)`, then the defect splits by a continuous `R`-cochain.*  On the local source this is
`prop_5_16` clause 6 (`cup20` bijectivity, i.e. pushforward-injectivity `H²(Γ,R_ρ) ↪ ((R^∨)^C)^∨`,
since `cup20 c φ = [φ ∘ c]` for invariant `φ`) plus `B²`-extraction at the `compHom` action (the
`slift`-conjugation action on `R` factors through `C = Y/K` by `lemma_7_2`'s `K`-centrality); on
the candidate source it is the §5 word-complex route (`docs/orchestration/p16d6a-handoff.md` §3). -/
omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [ContinuousSMul Γ (ZMod 2)] in
theorem hsep_hom_of_splitCriterion {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hsplit : ∀ g : ContinuousMonoidHom Γ RF.YB,
      (∀ d : D.DRmod, H2mk Γ (ZMod 2)
          ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2)),
            pairDefect_mem_Z2_all RF D htriv g d⟩ = 0) →
        ∃ c : Γ → ↥Blk.frattiniK, Continuous (fun γ => ((c γ : Y))) ∧
          ∀ γ δ, (c (γ * δ) : Y)
            = (c γ : Y) * (slift RF (g γ) * (c δ : Y) * (slift RF (g γ))⁻¹)
                * (rDefect RF g γ δ : Y)) :
    ∀ g : BoundaryLifts b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, RF.piB (φ γ) = g.1.1 γ := by
  intro g hg
  have hall : ∀ d : D.DRmod, H2mk Γ (ZMod 2)
      ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g.1.1 gd.1 gd.2)),
        pairDefect_mem_Z2_all RF D htriv g.1.1 d⟩ = 0 := by
    intro d
    by_cases h : D.toDR d = RF.zeroDR
    · -- `d = 0`: the pushed cochain is the zero cocycle
      have hd : d = 0 := by rw [← D.h0, ← h, Equiv.symm_apply_apply]
      subst hd
      have hz : (⟨fun gd => D.pair 0 (Additive.ofMul (rDefect RF g.1.1 gd.1 gd.2)),
          pairDefect_mem_Z2_all RF D htriv g.1.1 0⟩ : ↥(Z2 Γ (ZMod 2))) = 0 := by
        apply Subtype.ext
        funext gd
        simp only [map_zero, AddMonoidHom.zero_apply]
        rfl
      rw [hz, map_zero]
    · -- `d ≠ 0`: `obs g d = 0` is exactly the class-vanishing
      exact (obs_zero_iff_pairClass_zero RF D htriv hcard g.1.1 d h).mp
        (LinearMap.congr_fun hg d)
  obtain ⟨c, hc, hs⟩ := hsplit g.1.1 hall
  exact homLift_of_split RF g.1.1 c hc hs

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136) for the block frame, from the split criterion** — `blockStageR136` with `hsep_hom`
pre-discharged by `hsep_hom_of_splitCriterion`.  The per-`Γ` inputs are now exactly the source's
5.15/5.16 duality package: the numerics `hcard`/`hfg`, the **split criterion** `hsplit` (the
`(R^∨)^C`-separation at the cochain level), and the torsor count `hZcount`. -/
theorem blockStageR136_ofSplitCriterion (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hsplit : ∀ g : ContinuousMonoidHom Γ (blockFrameImpl T Blk hE2).YB,
      (∀ d : (blockRObstructionData T Blk hE2).DRmod, H2mk Γ (ZMod 2)
          ⟨fun gd => (blockRObstructionData T Blk hE2).pair d
              (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g gd.1 gd.2)),
            pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
              htriv g d⟩ = 0) →
        ∃ c : Γ → ↥Blk.frattiniK, Continuous (fun γ => ((c γ : Y))) ∧
          ∀ γ δ, (c (γ * δ) : Y)
            = (c γ : Y) * (slift (blockFrameImpl T Blk hE2) (g γ) * (c δ : Y)
                  * (slift (blockFrameImpl T Blk hE2) (g γ))⁻¹)
                * (rDefect (blockFrameImpl T Blk hE2) g γ δ : Y))
    (hZcount : ∀ f₀ : BoundaryLifts b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) = (blockFrameImpl T Blk hE2).zR) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  blockStageR136 T Blk hE2 htriv hcard hfg b F
    (hsep_hom_of_splitCriterion (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
      htriv hcard b F hsplit) hZcount

end StageR136

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 8.9 = ⟦thm-closedrecursion⟧ (= theorem 8.17 in current tex)
-/
