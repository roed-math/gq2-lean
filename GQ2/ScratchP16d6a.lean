import GQ2.BlockFrameImpl
import GQ2.RStageObstructionBuild

/-!
# P-16d6a (banked WIP): the concrete R-stage obstruction datum for `blockFrame`

Builds `RObstructionData (blockFrameImpl T Blk hE2)` — the (136) `stageR136` datum — against the
concrete §7-block frame (P-17c ✓, `blockFrameImpl`).  Not yet spliced.

Concrete covers (`blockFrameImpl`): `YB = Y/R`, `piB = mk' R`, `scalarCover l h` = the cover
`Y/l ↠ Y/R` (`cover = Y/l.1`, `p = map l.1 R id`, `z = mk' l.1 r₀`).  So `coverMap l h = mk' l.1`
and `coverMap_lifts` is `map ∘ mk' = mk'`.
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
  coverMap := fun l _h => by
    haveI : (l.1).Normal := l.2.1
    exact QuotientGroup.mk' l.1
  coverMap_lifts := fun l _h => by
    haveI : (l.1).Normal := l.2.1
    ext y
    rfl

/-! ## a-DRmod: `D_Rmod` as the Y-invariant `𝔽₂`-characters of `R` -/

open scoped Classical

variable {L : Subgroup Y}

/-- **Y-invariant `𝔽₂`-characters of `R = Blk.R = Φ(K)`** (`(R^∨)^C`): additive homs
`R → 𝔽₂` fixed by `Y`-conjugation.  Their kernels are exactly the index-≤2 `Y`-normal
subgroups of `R`, i.e. `D_R`; this submodule is the `𝔽₂`-realization `D_Rmod`. -/
def RCharSub (Blk : SectionSeven.MinimalBlock L) :
    Submodule (ZMod 2) (Additive ↥Blk.R →+ ZMod 2) where
  carrier := {χ | ∀ (y : Y) (r : ↥Blk.R),
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
  haveI : Finite (Additive ↥Blk.R → ZMod 2) := inferInstance
  haveI : Finite (Additive ↥Blk.R →+ ZMod 2) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Additive ↥Blk.R →+ ZMod 2))
  infer_instance

/-- The kernel of a character `χ`, as a subgroup of `↥Blk.R`. -/
def RCharKerSub (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) : Subgroup ↥Blk.R where
  carrier := {r | χ.1 (Additive.ofMul r) = 0}
  one_mem' := by
    show χ.1 (Additive.ofMul 1) = 0
    rw [show Additive.ofMul (1 : ↥Blk.R) = 0 from rfl, map_zero]
  mul_mem' := fun {a b} ha hb => by
    show χ.1 (Additive.ofMul (a * b)) = 0
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
      map_add, ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    show χ.1 (Additive.ofMul a⁻¹) = 0
    rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a from rfl, map_neg, ha, neg_zero]

/-- `χ` as a `MonoidHom ↥R →* Multiplicative 𝔽₂` (for the kernel/index calculus). -/
def RCharMulHom (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    ↥Blk.R →* Multiplicative (ZMod 2) where
  toFun r := Multiplicative.ofAdd (χ.1 (Additive.ofMul r))
  map_one' := by
    show Multiplicative.ofAdd (χ.1 (Additive.ofMul (1 : ↥Blk.R))) = 1
    rw [show Additive.ofMul (1 : ↥Blk.R) = 0 from rfl, map_zero]; rfl
  map_mul' := fun a b => by
    show Multiplicative.ofAdd (χ.1 (Additive.ofMul (a * b))) = _ * _
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add]; rfl

theorem RCharKerSub_eq_ker (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    RCharKerSub Blk χ = (RCharMulHom Blk χ).ker := by
  ext r
  rw [MonoidHom.mem_ker]
  show χ.1 (Additive.ofMul r) = 0 ↔ Multiplicative.ofAdd (χ.1 (Additive.ofMul r)) = 1
  rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq]

/-- The kernel of `χ`, pushed to a subgroup of `Y`. -/
def RCharKer (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) : Subgroup Y :=
  (RCharKerSub Blk χ).map Blk.R.subtype

theorem RCharKer_le (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    RCharKer Blk χ ≤ Blk.R := by
  rw [RCharKer]; exact Subgroup.map_subtype_le _

theorem RCharKer_normal (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (RCharKer Blk χ).Normal := by
  constructor
  intro n hn g
  rw [RCharKer, Subgroup.mem_map] at hn ⊢
  obtain ⟨r, hr, rfl⟩ := hn
  refine ⟨⟨g * (r : Y) * g⁻¹,
      (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 g⟩, ?_, rfl⟩
  show χ.1 (Additive.ofMul ⟨g * (r : Y) * g⁻¹, _⟩) = 0
  rw [χ.2 g r]
  exact hr

theorem RCharKer_relIndex_le (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (RCharKer Blk χ).relIndex Blk.R ≤ 2 := by
  have h1 : (RCharKer Blk χ).relIndex Blk.R = (RCharKerSub Blk χ).index := by
    rw [Subgroup.relIndex, RCharKer, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective Blk.R.subtype_injective]
  rw [h1, RCharKerSub_eq_ker, Subgroup.index_ker]
  calc Nat.card (RCharMulHom Blk χ).range
      ≤ Nat.card (Multiplicative (ZMod 2)) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl

/-- The `D_R` index type of the concrete frame `blockFrameImpl` (defeq to its `.DR`). -/
abbrev BlockDR (Blk : SectionSeven.MinimalBlock L) : Type :=
  {R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}

/-- **The inverse direction**: the index-≤2 indicator character `r ↦ [r ∉ R']` of a `D_R`
element, as an additive hom (additive by `mul_mem_iff_of_index_two`, with the `index ≤ 2`
case-split covering `R' = R` — the zero character). -/
noncomputable def RCharOfHom (Blk : SectionSeven.MinimalBlock L) (R' : BlockDR Blk) :
    Additive ↥Blk.R →+ ZMod 2 where
  toFun r := if ((Additive.toMul r : ↥Blk.R) : Y) ∈ R'.1 then 0 else 1
  map_zero' := by
    show (if ((Additive.toMul (0 : Additive ↥Blk.R) : ↥Blk.R) : Y) ∈ R'.1
      then (0 : ZMod 2) else 1) = 0
    exact if_pos (one_mem R'.1)
  map_add' a b := by
    show (if ((Additive.toMul a * Additive.toMul b : ↥Blk.R) : Y) ∈ R'.1 then (0 : ZMod 2) else 1)
      = (if ((Additive.toMul a : ↥Blk.R) : Y) ∈ R'.1 then 0 else 1)
        + (if ((Additive.toMul b : ↥Blk.R) : Y) ∈ R'.1 then 0 else 1)
    have hidx : (R'.1.subgroupOf Blk.R).index ≤ 2 := R'.2.2.2
    rcases Nat.lt_or_ge (R'.1.subgroupOf Blk.R).index 2 with hlt | hge
    · have h1 : (R'.1.subgroupOf Blk.R).index = 1 := by
        have hne0 : (R'.1.subgroupOf Blk.R).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have htop : R'.1.subgroupOf Blk.R = ⊤ := Subgroup.index_eq_one.mp h1
      have hmem : ∀ x : ↥Blk.R, (x : Y) ∈ R'.1 := fun x => by
        have hx : x ∈ R'.1.subgroupOf Blk.R := htop ▸ Subgroup.mem_top x
        rwa [Subgroup.mem_subgroupOf] at hx
      rw [if_pos (hmem _), if_pos (hmem _), if_pos (hmem _), add_zero]
    · have h2 : (R'.1.subgroupOf Blk.R).index = 2 := le_antisymm hidx hge
      have hkey := mul_mem_iff_of_index_two h2 (Additive.toMul a) (Additive.toMul b)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hkey
      by_cases h1 : ((Additive.toMul a : ↥Blk.R) : Y) ∈ R'.1 <;>
        by_cases h2' : ((Additive.toMul b : ↥Blk.R) : Y) ∈ R'.1 <;>
        simp only [Subgroup.coe_mul, hkey, h1, h2', if_true, if_false, iff_true, iff_false,
          iff_self] <;> decide

/-- `RCharOfHom R'` is Y-invariant, hence a member of `RCharSub` — from `R'.Normal`. -/
theorem RCharOf_mem (Blk : SectionSeven.MinimalBlock L) (R' : BlockDR Blk) :
    RCharOfHom Blk R' ∈ RCharSub Blk := by
  intro y r
  show (if ((⟨y * (r : Y) * y⁻¹,
        (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 y⟩ : ↥Blk.R) : Y)
      ∈ R'.1 then (0 : ZMod 2) else 1)
    = if ((r : ↥Blk.R) : Y) ∈ R'.1 then 0 else 1
  simp only [Subgroup.coe_mk]
  by_cases hrl : ((r : ↥Blk.R) : Y) ∈ R'.1
  · rw [if_pos (R'.2.1.conj_mem _ hrl y), if_pos hrl]
  · have hnot : y * (r : Y) * y⁻¹ ∉ R'.1 := fun h => hrl (by
      have hc := R'.2.1.conj_mem _ h y⁻¹
      rwa [show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y) from by group] at hc)
    rw [if_neg hnot, if_neg hrl]

/-- The inverse map `D_R → D_Rmod`: `R' ↦` its index-≤2 indicator character. -/
noncomputable def RCharOf (Blk : SectionSeven.MinimalBlock L) (R' : BlockDR Blk) :
    ↥(RCharSub Blk) := ⟨RCharOfHom Blk R', RCharOf_mem Blk R'⟩

/-- A character is the indicator of its own kernel (`𝔽₂`-valued). -/
theorem RChar_eq_ind (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) (r : ↥Blk.R) :
    χ.1 (Additive.ofMul r) = if r ∈ RCharKerSub Blk χ then 0 else 1 := by
  by_cases h : r ∈ RCharKerSub Blk χ
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) (χ.1 (Additive.ofMul r)) with h0 | h1
    · exact absurd h0 h
    · exact h1

/-- **Right inverse**: the kernel of the indicator character of `R'` is `R'`. -/
theorem RCharKer_RCharOf (Blk : SectionSeven.MinimalBlock L) (R' : BlockDR Blk) :
    RCharKer Blk (RCharOf Blk R') = R'.1 := by
  have hker : RCharKerSub Blk (RCharOf Blk R') = R'.1.subgroupOf Blk.R := by
    ext r
    rw [Subgroup.mem_subgroupOf]
    show (if ((r : ↥Blk.R) : Y) ∈ R'.1 then (0 : ZMod 2) else 1) = 0 ↔ ((r : ↥Blk.R) : Y) ∈ R'.1
    by_cases h : ((r : ↥Blk.R) : Y) ∈ R'.1 <;> simp [h]
  rw [RCharKer, hker, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr R'.2.2.1]

/-- **Injectivity** of `χ ↦ ker χ`: a character is determined by its kernel. -/
theorem RCharKer_inj (Blk : SectionSeven.MinimalBlock L) :
    Function.Injective (fun χ : ↥(RCharSub Blk) => RCharKer Blk χ) := by
  intro χ χ' hker
  have hsub : RCharKerSub Blk χ = RCharKerSub Blk χ' := by
    have h := congrArg (fun S => S.comap Blk.R.subtype) hker
    simpa only [RCharKer,
      Subgroup.comap_map_eq_self_of_injective Blk.R.subtype_injective] using h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  show χ.1 (Additive.ofMul (Additive.toMul a)) = χ'.1 (Additive.ofMul (Additive.toMul a))
  rw [RChar_eq_ind, RChar_eq_ind, hsub]

/-! ## a-DRmod: assembling the `(R^∨)^C` bijection and `pair` -/

/-- **The `(R^∨)^C` bijection** `D_Rmod ≃ D_R`: `χ ↦ ker χ` (inverse `R' ↦` its indicator). -/
noncomputable def blockToDR (Blk : SectionSeven.MinimalBlock L) :
    ↥(RCharSub Blk) ≃ BlockDR Blk :=
  Equiv.ofBijective
    (fun χ => ⟨RCharKer Blk χ, RCharKer_normal Blk χ, RCharKer_le Blk χ,
      RCharKer_relIndex_le Blk χ⟩)
    ⟨fun _ _ h => RCharKer_inj Blk (Subtype.ext_iff.mp h),
     fun R' => ⟨RCharOf Blk R', Subtype.ext (RCharKer_RCharOf Blk R')⟩⟩

@[simp] theorem blockToDR_coe (Blk : SectionSeven.MinimalBlock L) (χ : ↥(RCharSub Blk)) :
    (blockToDR Blk χ).1 = RCharKer Blk χ := rfl

/-- The zero character's kernel is all of `R` (`= zeroDR`). -/
theorem RCharKer_zero (Blk : SectionSeven.MinimalBlock L) : RCharKer Blk 0 = Blk.R := by
  have hsub : RCharKerSub Blk 0 = ⊤ := by
    ext r
    simp only [Subgroup.mem_top, iff_true]
    show (0 : ↥(RCharSub Blk)).1 (Additive.ofMul r) = 0
    rfl
  rw [RCharKer, hsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end GQ2
