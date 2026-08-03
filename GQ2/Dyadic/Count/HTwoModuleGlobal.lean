/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModule

/-!
# The global module-valued degree-two obstruction

This file assembles the finite-level relator fibres from `Count.HTwoModule` into a
choice-independent additive obstruction on continuous module-valued `2`-cocycles.
Unlike the scalar construction, every finite level carries both a cocycle and proof
that the level lies in the kernel of the prescribed action.  Keeping that proof in
`ModuleLevelFactor` makes the quotient action, and hence every pullback comparison,
explicit.

The construction closes the global bookkeeping part of the module-coefficient `H²`
comparison:

* `moduleObsAt_congr` proves independence of the finite factorization;
* `moduleObsFun_add` proves additivity after passing to a common refinement;
* `moduleObsFam` is the resulting homomorphism
  `Z²_cont(G,A) →+ (rel → A)`.

The optional descent theorem at the end assumes exactly the target-local resolver
needed to identify finite-level coboundaries with `heisD1`.  It does not assert the
reflection/splitting direction required for injectivity.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

/-! ## 1. Action-compatible finite factor data -/

section LevelFactor

variable {G C A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]

/-- A finite factorization of a normalized module cocycle, including the proof that
the level is contained in the kernel of the lower action.  The latter determines the
quotient action on `A`; it is data, rather than an inferred side condition. -/
structure ModuleLevelFactor (rho : ContinuousMonoidHom G C) (κ : G × G → A) where
  /-- The finite open normal level. -/
  V : OpenNormalSubgroup G
  /-- The level is contained in the action kernel. -/
  hV : V.toSubgroup ≤ rho.toMonoidHom.ker
  /-- The descended normalized cocycle, for the action induced through `rho`. -/
  z : @ModuleTwoCocycle (G ⧸ V.toSubgroup) A _ _
    (DistribMulAction.compHom A (quotientActionHom rho V hV))
  /-- Inflation recovers the original normalized cocycle. -/
  hfact :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    ∀ x y : G, κ (x, y) =
      z.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y)

/-- The factorization theorem in packaged form. -/
theorem nonempty_moduleLevelFactor (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) (f : Z2 G A) :
    Nonempty (ModuleLevelFactor rho (moduleNormalize f.1)) := by
  obtain ⟨V, hV, z, hz⟩ := exists_moduleTwoCocycle_factor rho hcompat f
  exact ⟨⟨V, hV, z, hz⟩⟩

/-- Canonical projection from a finer open normal level to a coarser one. -/
noncomputable def moduleLvlProj {V V' : OpenNormalSubgroup G}
    (h : V'.toSubgroup ≤ V.toSubgroup) :
    (G ⧸ V'.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map V'.toSubgroup V.toSubgroup (MonoidHom.id _)
    (by rw [Subgroup.comap_id]; exact h)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A] in
theorem moduleLvlProj_comp {V V' : OpenNormalSubgroup G}
    (h : V'.toSubgroup ≤ V.toSubgroup) :
    (moduleLvlProj h).comp (QuotientGroup.mk' V'.toSubgroup) =
      QuotientGroup.mk' V.toSubgroup := by
  ext g
  rw [moduleLvlProj, MonoidHom.comp_apply, QuotientGroup.map_mk']
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A] in
theorem moduleLvlProj_mk {V V' : OpenNormalSubgroup G}
    (h : V'.toSubgroup ≤ V.toSubgroup) (g : G) :
    moduleLvlProj h (QuotientGroup.mk' V'.toSubgroup g) =
      QuotientGroup.mk' V.toSubgroup g := by
  rw [← MonoidHom.comp_apply, moduleLvlProj_comp]

/-- A canonical level projection is compatible with the quotient actions induced by
`rho`. -/
theorem moduleLvlProj_smul (rho : ContinuousMonoidHom G C)
    {V V' : OpenNormalSubgroup G} (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (hV' : V'.toSubgroup ≤ rho.toMonoidHom.ker)
    (h : V'.toSubgroup ≤ V.toSubgroup) (q : G ⧸ V'.toSubgroup) (a : A) :
    letI : DistribMulAction (G ⧸ V'.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V' hV')
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    q • a = moduleLvlProj h q • a := by
  induction q using QuotientGroup.induction_on with
  | H g =>
      change quotientActionHom rho V' hV' (QuotientGroup.mk' V'.toSubgroup g) • a =
        quotientActionHom rho V hV
          (moduleLvlProj h (QuotientGroup.mk' V'.toSubgroup g)) • a
      rw [moduleLvlProj_mk, quotientActionHom_mk, quotientActionHom_mk]

end LevelFactor

/-! ## 2. Additivity of finite-level relator fibres -/

section RelatorAdditivity

variable {X : Type*} {L A : Type} [Group L] [TopologicalSpace L]
  [DiscreteTopology L] [Finite L] [AddCommGroup A] [DistribMulAction L A] [Finite A]

/-- The fibre product of two module extensions over their common base. -/
def moduleFiberProdSubgroup (z₁ z₂ : ModuleTwoCocycle L A) :
    Subgroup (ModuleExt z₁ × ModuleExt z₂) where
  carrier := {p | p.1.g = p.2.g}
  one_mem' := rfl
  mul_mem' := by
    intro p q hp hq
    change p.1.g = p.2.g at hp
    change q.1.g = q.2.g at hq
    change (p.1 * q.1).g = (p.2 * q.2).g
    simp only [ModuleExt.mul_g]
    rw [hp, hq]
  inv_mem' := by
    intro p hp
    change p.1.g = p.2.g at hp
    change p.1⁻¹.g = p.2⁻¹.g
    simp only [ModuleExt.inv_g]
    rw [hp]

/-- The carrier of the fibre product of two module extensions. -/
abbrev ModuleFiberProd (z₁ z₂ : ModuleTwoCocycle L A) :=
  ↥(moduleFiberProdSubgroup z₁ z₂)

namespace ModuleFiberProd

variable {z₁ z₂ : ModuleTwoCocycle L A}

instance : TopologicalSpace (ModuleFiberProd z₁ z₂) := ⊥
instance : DiscreteTopology (ModuleFiberProd z₁ z₂) := ⟨rfl⟩

/-- First extension projection. -/
def pr1 : ModuleFiberProd z₁ z₂ →* ModuleExt z₁ where
  toFun p := p.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Second extension projection. -/
def pr2 : ModuleFiberProd z₁ z₂ →* ModuleExt z₂ where
  toFun p := p.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Add the two fibre coordinates.  The cocycles add because both components have
the same base coordinate. -/
def prSum : ModuleFiberProd z₁ z₂ →* ModuleExt (z₁ + z₂) where
  toFun p := ⟨p.1.1.u + p.1.2.u, p.1.1.g⟩
  map_one' := ModuleExt.ext (add_zero 0) rfl
  map_mul' p q := by
    apply ModuleExt.ext
    · have hp : p.1.1.g = p.1.2.g := by
        have hp' := p.property
        change p.1.1.g = p.1.2.g at hp'
        exact hp'
      have hq : q.1.1.g = q.1.2.g := by
        have hq' := q.property
        change q.1.1.g = q.1.2.g at hq'
        exact hq'
      change (p.1.1 * q.1.1).u + (p.1.2 * q.1.2).u =
        (p.1.1.u + p.1.2.u) + p.1.1.g • (q.1.1.u + q.1.2.u) +
          (z₁ + z₂).κ p.1.1.g q.1.1.g
      simp only [ModuleExt.mul_u, ModuleTwoCocycle.add_κ, smul_add]
      rw [hp, hq]
      abel
    · rfl

/-- Simultaneous zero-fibre lift to the fibre product. -/
def lift (m : X → L) (z₁ z₂ : ModuleTwoCocycle L A) :
    X → ModuleFiberProd z₁ z₂ := fun x =>
  ⟨(ModuleExt.lift z₁ m x, ModuleExt.lift z₂ m x), by
    change (ModuleExt.lift z₁ m x).g = (ModuleExt.lift z₂ m x).g
    rfl⟩

end ModuleFiberProd

omit [TopologicalSpace L] [DiscreteTopology L] in
/-- Relator fibres are additive in the normalized module cocycle. -/
theorem moduleRel_add (W : PWord X) (m : X → L)
    (z₁ z₂ : ModuleTwoCocycle L A) :
    moduleRel W m (z₁ + z₂) = moduleRel W m z₁ + moduleRel W m z₂ := by
  let F1 : ContinuousMonoidHom (ModuleFiberProd z₁ z₂) (ModuleExt z₁) :=
    ⟨ModuleFiberProd.pr1, continuous_of_discreteTopology⟩
  let F2 : ContinuousMonoidHom (ModuleFiberProd z₁ z₂) (ModuleExt z₂) :=
    ⟨ModuleFiberProd.pr2, continuous_of_discreteTopology⟩
  let Fs : ContinuousMonoidHom (ModuleFiberProd z₁ z₂) (ModuleExt (z₁ + z₂)) :=
    ⟨ModuleFiberProd.prSum, continuous_of_discreteTopology⟩
  have h1 := PWord.map_eval F1 (ModuleFiberProd.lift m z₁ z₂) W
  have h2 := PWord.map_eval F2 (ModuleFiberProd.lift m z₁ z₂) W
  have hs := PWord.map_eval Fs (ModuleFiberProd.lift m z₁ z₂) W
  have e1 : (fun x => F1 (ModuleFiberProd.lift m z₁ z₂ x)) = ModuleExt.lift z₁ m := rfl
  have e2 : (fun x => F2 (ModuleFiberProd.lift m z₁ z₂ x)) = ModuleExt.lift z₂ m := rfl
  have es : (fun x => Fs (ModuleFiberProd.lift m z₁ z₂ x)) = ModuleExt.lift (z₁ + z₂) m := by
    funext x
    exact ModuleExt.ext (add_zero 0) rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [es] at hs
  show (PWord.eval (ModuleExt.lift (z₁ + z₂) m) W).u =
    (PWord.eval (ModuleExt.lift z₁ m) W).u +
      (PWord.eval (ModuleExt.lift z₂ m) W).u
  rw [← hs, ← h1, ← h2]
  rfl

end RelatorAdditivity

/-! ## 3. Refinement-independent relator fibres -/

section ObstructionAt

variable {iota rel : Type*}
  {G C A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]

/-- Quotients by open subgroups are discrete.  We keep this local because the topology is
only needed to evaluate profinite words at a finite level. -/
local instance moduleQuotientDiscreteTopology (V : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- The relator-fibre vector computed from one action-compatible factorization. -/
noncomputable def moduleObsAt (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) {κ : G × G → A}
    (F : ModuleLevelFactor rho κ) : rel → A :=
  letI : DistribMulAction (G ⧸ F.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho F.V F.hV)
  fun k => moduleRel (W k)
    (fun i => QuotientGroup.mk' F.V.toSubgroup (gen i)) F.z

/-- The obstruction at a level can be computed at any finer action-compatible level,
using the pulled-back module cocycle. -/
theorem moduleObsAt_eq_comap (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) {κ : G × G → A}
    (F : ModuleLevelFactor rho κ) (V' : OpenNormalSubgroup G)
    (hV' : V'.toSubgroup ≤ rho.toMonoidHom.ker)
    (h : V'.toSubgroup ≤ F.V.toSubgroup) :
    moduleObsAt W gen rho F =
      letI : DistribMulAction (G ⧸ F.V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho F.V F.hV)
      letI : DistribMulAction (G ⧸ V'.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V' hV')
      fun k => moduleRel (W k)
        (fun i => QuotientGroup.mk' V'.toSubgroup (gen i))
        (F.z.comap (moduleLvlProj h) (moduleLvlProj_smul rho F.hV hV' h)) := by
  letI : DistribMulAction (G ⧸ F.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho F.V F.hV)
  letI : DistribMulAction (G ⧸ V'.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V' hV')
  funext k
  change moduleRel (W k) (fun i => QuotientGroup.mk' F.V.toSubgroup (gen i)) F.z = _
  have hm : (fun i => QuotientGroup.mk' F.V.toSubgroup (gen i)) =
      fun i => moduleLvlProj h (QuotientGroup.mk' V'.toSubgroup (gen i)) := by
    funext i
    exact (moduleLvlProj_mk h (gen i)).symm
  rw [hm]
  exact moduleRel_comap (W k)
    (fun i => QuotientGroup.mk' V'.toSubgroup (gen i)) F.z
    (moduleLvlProj h) (moduleLvlProj_smul rho F.hV hV' h)

/-- **Choice independence.**  Two action-compatible finite factorizations give the
same relator vector.  The proof compares their pullbacks at the intersection level;
the induced action there is the single action descended from `rho`. -/
theorem moduleObsAt_congr (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) {κ : G × G → A}
    (F₁ F₂ : ModuleLevelFactor rho κ) :
    moduleObsAt W gen rho F₁ = moduleObsAt W gen rho F₂ := by
  let V' : OpenNormalSubgroup G := F₁.V ⊓ F₂.V
  have h1 : V'.toSubgroup ≤ F₁.V.toSubgroup :=
    fun x hx => SetLike.le_def.mp inf_le_left hx
  have h2 : V'.toSubgroup ≤ F₂.V.toSubgroup :=
    fun x hx => SetLike.le_def.mp inf_le_right hx
  have hV' : V'.toSubgroup ≤ rho.toMonoidHom.ker := fun x hx => F₁.hV (h1 hx)
  rw [moduleObsAt_eq_comap W gen rho F₁ V' hV' h1,
    moduleObsAt_eq_comap W gen rho F₂ V' hV' h2]
  letI : DistribMulAction (G ⧸ F₁.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho F₁.V F₁.hV)
  letI : DistribMulAction (G ⧸ F₂.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho F₂.V F₂.hV)
  letI : DistribMulAction (G ⧸ V'.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V' hV')
  have hz : F₁.z.comap (moduleLvlProj h1)
        (moduleLvlProj_smul rho F₁.hV hV' h1) =
      F₂.z.comap (moduleLvlProj h2)
        (moduleLvlProj_smul rho F₂.hV hV' h2) := by
    apply ModuleTwoCocycle.ext
    funext a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V'.toSubgroup a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective V'.toSubgroup b
    simp only [ModuleTwoCocycle.comap_κ, moduleLvlProj_mk]
    rw [← F₁.hfact x y, ← F₂.hfact x y]
  rw [hz]

end ObstructionAt

/-! ## 4. The additive global obstruction -/

section GlobalObstruction

variable {iota rel : Type*}
  {G C A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]

local instance moduleGlobalQuotientDiscreteTopology (V : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- The global obstruction, computed at an arbitrary action-compatible factorization.
`moduleObsAt_congr` makes the choice definitionally irrelevant to every theorem. -/
noncomputable def moduleObsFun (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (f : Z2 G A) : rel → A :=
  moduleObsAt W gen rho (nonempty_moduleLevelFactor rho hcompat f).some

/-- The global obstruction may be computed using any compatible factorization. -/
theorem moduleObsFun_eq (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (f : Z2 G A) (F : ModuleLevelFactor rho (moduleNormalize f.1)) :
    moduleObsFun W gen rho hcompat f = moduleObsAt W gen rho F :=
  moduleObsAt_congr W gen rho _ F

/-- **Additivity of the global module obstruction.**  The two chosen finite levels are
pulled back to their intersection, where their quotient actions are literally the same
action induced through `rho`; `moduleRel_add` then reads the sum cocycle fibrewise. -/
theorem moduleObsFun_add (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (f f' : Z2 G A) :
    moduleObsFun W gen rho hcompat (f + f') =
      moduleObsFun W gen rho hcompat f + moduleObsFun W gen rho hcompat f' := by
  let F := (nonempty_moduleLevelFactor rho hcompat f).some
  let F' := (nonempty_moduleLevelFactor rho hcompat f').some
  let V : OpenNormalSubgroup G := F.V ⊓ F'.V
  have hF : V.toSubgroup ≤ F.V.toSubgroup :=
    fun x hx => SetLike.le_def.mp inf_le_left hx
  have hF' : V.toSubgroup ≤ F'.V.toSubgroup :=
    fun x hx => SetLike.le_def.mp inf_le_right hx
  have hV : V.toSubgroup ≤ rho.toMonoidHom.ker := fun x hx => F.hV (hF hx)
  letI : DistribMulAction (G ⧸ F.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho F.V F.hV)
  letI : DistribMulAction (G ⧸ F'.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho F'.V F'.hV)
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  let z := F.z.comap (moduleLvlProj hF) (moduleLvlProj_smul rho F.hV hV hF)
  let z' := F'.z.comap (moduleLvlProj hF') (moduleLvlProj_smul rho F'.hV hV hF')
  let Fsum : ModuleLevelFactor rho (moduleNormalize (f + f').1) :=
    { V := V
      hV := hV
      z := z + z'
      hfact := by
        intro x y
        change moduleNormalize (f.1 + f'.1) (x, y) = (z + z').κ _ _
        rw [congrFun (moduleNormalize_add f.1 f'.1) (x, y)]
        simp only [Pi.add_apply, ModuleTwoCocycle.add_κ, z, z',
          ModuleTwoCocycle.comap_κ, moduleLvlProj_mk]
        rw [← F.hfact x y, ← F'.hfact x y] }
  rw [moduleObsFun_eq W gen rho hcompat (f + f') Fsum,
    moduleObsFun_eq W gen rho hcompat f F,
    moduleObsFun_eq W gen rho hcompat f' F',
    moduleObsAt_eq_comap W gen rho F V hV hF,
    moduleObsAt_eq_comap W gen rho F' V hV hF']
  funext k
  change moduleRel (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) (z + z') =
    moduleRel (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) z +
      moduleRel (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) z'
  exact moduleRel_add (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) z z'

/-- The choice-independent finite-level construction as an additive homomorphism. -/
noncomputable def moduleObsFam (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) :
    Z2 G A →+ (rel → A) :=
  AddMonoidHom.mk' (moduleObsFun W gen rho hcompat)
    (moduleObsFun_add W gen rho hcompat)

end GlobalObstruction

/-! ## 5. The finite-to-global coboundary bridge -/

section CoboundaryFactor

variable {G C A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C]
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction C A]

/-- A continuous module-valued `1`-cochain factors through a finite quotient contained
in the kernel of the prescribed action. -/
theorem exists_moduleOneCochain_factor (rho : ContinuousMonoidHom G C)
    (psi : G → A) (hpsi : Continuous psi) :
    ∃ V : OpenNormalSubgroup G, ∃ hV : V.toSubgroup ≤ rho.toMonoidHom.ker,
      ∃ lam : G ⧸ V.toSubgroup → A,
        ∀ x : G, psi x = lam (QuotientGroup.mk' V.toSubgroup x) := by
  obtain ⟨U, hU⟩ := GQ2.Dyadic.WordCoh.exists_openNormalSubgroup_factor_two
    (fun p : G × G => psi p.1) (hpsi.comp continuous_fst)
  let K : OpenNormalSubgroup G := moduleActionKerON rho
  let V : OpenNormalSubgroup G := U ⊓ K
  have hVU : V.toSubgroup ≤ U.toSubgroup :=
    fun x hx => SetLike.le_def.mp inf_le_left hx
  have hVK : V.toSubgroup ≤ rho.toMonoidHom.ker := by
    intro x hx
    have hxK : x ∈ K.toSubgroup := SetLike.le_def.mp inf_le_right hx
    exact hxK
  refine ⟨V, hVK, fun q => Quotient.liftOn q psi ?_, ?_⟩
  · intro x₁ x₂ hx
    have hxV : x₁⁻¹ * x₂ ∈ V.toSubgroup := QuotientGroup.leftRel_apply.mp hx
    have hu := hU x₁ x₁ _ (hVU hxV) 1 (one_mem U.toSubgroup)
    rw [mul_inv_cancel_left, mul_one] at hu
    exact hu.symm
  · intro x
    rfl

end CoboundaryFactor

section DifferentialBaseChange

variable {iota rel : Type*} {G C A : Type}
  [Group G] [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Changing the lower group without changing its action on `A` does not change the
word differential.  This is the `A`-coordinate of base change between the two split
semidirect products. -/
theorem heisD1_eq_of_action_map (pi : G →* C) [DistribMulAction G A]
    (hact : ∀ (g : G) (a : A), g • a = pi g • a)
    (m : iota → G) (c : iota → C) (hc : ∀ i, pi (m i) = c i)
    (w : rel → FreeGroup iota) :
    heisD1 (A := A) m w = heisD1 (A := A) c w := by
  ext a k
  rw [heisD1_eq_lift_foxLift_u, heisD1_eq_lift_foxLift_u]
  have hmap := map_freeGroup_lift (baseMap pi hact) (foxLift m a) (w k)
  have hgen : (fun i => baseMap pi hact (foxLift m a i)) = foxLift c a := by
    funext i
    exact baseMap_foxLift pi hact hc a i
  rw [hgen] at hmap
  exact congrArg WordLift.u hmap

end DifferentialBaseChange

/-! ## 6. Partial assembly: descent without reflection -/

section PartialAssembly

variable {iota rel : Type*} {Gamma A C : Type*}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction Gamma A]
  [Group C] [DistribMulAction C A]
  (c : iota → C) (w : rel → FreeGroup iota)

/-- The part of `ModuleH2WordData` needed to descend the obstruction through `B²`.
The sole missing field is the converse/reflection theorem supplied by splitting the
twisted semidirect extension. -/
structure ModuleH2WordDescentData where
  /-- The additive relator obstruction. -/
  obstruction : Z2 Gamma A →+ (rel → A)
  /-- Coboundaries map into the word-coboundary range. -/
  map_coboundary : ∀ f : Z2 Gamma A, f.1 ∈ B2 Gamma A →
    obstruction f ∈ (heisD1 (A := A) c w).range

variable {c w}

/-- Adjoin exactly the remaining reflection/splitting theorem to obtain the full
module `H²` comparison data. -/
def ModuleH2WordDescentData.withReflection
    (D : ModuleH2WordDescentData (Gamma := Gamma) (A := A) c w)
    (reflects : ∀ f : Z2 Gamma A,
      D.obstruction f ∈ (heisD1 (A := A) c w).range → f.1 ∈ B2 Gamma A) :
    ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w where
  obstruction := D.obstruction
  map_coboundary := D.map_coboundary
  reflects_coboundary := reflects

end PartialAssembly

section GlobalCoboundary

variable {iota rel : Type*} {G C A : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {c : iota → C} {J : Set iota}

local instance moduleCoboundaryQuotientDiscreteTopology (V : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- **Global `map_coboundary`.**  A continuous module coboundary has relator
obstruction in the image of the word differential.

The resolver hypothesis is deliberately target-local: the coboundary calculation is
performed in `A ⋊ (G/V)` at the finite level through which its splitting cochain
factors.  No reflection or splitting theorem is used here. -/
theorem moduleObsFam_B2_mem_range (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hc : ∀ i, rho (gen i) = c i)
    (hresLevel : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W w (WordLift A (G ⧸ V.toSubgroup)))
    {f : Z2 G A} (hf : f.1 ∈ B2 G A) :
    moduleObsFam W gen rho hcompat f ∈ (heisD1 (A := A) c w).range := by
  rw [B2, AddSubgroup.mem_map] at hf
  obtain ⟨psi, hpsiC1, hpsiEq⟩ := hf
  have hpsi : Continuous psi := mem_C1_iff.mp hpsiC1
  have hf1 : f.1 = dOne G A psi := hpsiEq.symm
  let psi0 : G → A := fun g => psi g - psi 1
  obtain ⟨V, hV, lam, hlam⟩ :=
    exists_moduleOneCochain_factor rho psi0 (hpsi.sub continuous_const)
  have hlam1 : lam 1 = 0 := by
    have h := hlam 1
    rw [show QuotientGroup.mk' V.toSubgroup (1 : G) = 1 from map_one _] at h
    change psi 1 - psi 1 = lam 1 at h
    simpa using h.symm
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  have hfactor : ∀ x y : G, moduleNormalize f.1 (x, y) =
      (ModuleTwoCocycle.coboundary lam hlam1).κ
        (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y) := by
    intro x y
    change moduleNormalize f.1 (x, y) =
      rhoV (QuotientGroup.mk' V.toSubgroup x) •
          lam (QuotientGroup.mk' V.toSubgroup y) -
        lam (QuotientGroup.mk' V.toSubgroup (x * y)) +
          lam (QuotientGroup.mk' V.toSubgroup x)
    rw [show rhoV (QuotientGroup.mk' V.toSubgroup x) = rho x from
      quotientActionHom_mk rho V hV x]
    rw [← hcompat]
    rw [← hlam x, ← hlam y, ← hlam (x * y), hf1]
    simp [moduleNormalize, psi0, dOne, smul_sub]
    abel
  let Fcb : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := ModuleTwoCocycle.coboundary lam hlam1
      hfact := hfactor }
  change moduleObsFun W gen rho hcompat f ∈ (heisD1 (A := A) c w).range
  rw [moduleObsFun_eq W gen rho hcompat f Fcb]
  let m : iota → G ⧸ V.toSubgroup :=
    fun i => QuotientGroup.mk' V.toSubgroup (gen i)
  have hrel : ∀ k, PWord.eval m (W k) = 1 :=
    fun k => hpres.rel (GQ2.quotientMk V.toSubgroup) k
  have hfinite := moduleRelFam_coboundary_mem_range W w m lam hlam1
    (hresLevel V hV) hrel
  obtain ⟨a, ha⟩ := hfinite
  refine ⟨a, ?_⟩
  have hcV : ∀ i, rhoV (m i) = c i := by
    intro i
    rw [show rhoV (m i) = rho (gen i) from quotientActionHom_mk rho V hV (gen i)]
    exact hc i
  have hd : heisD1 (A := A) m w = heisD1 (A := A) c w :=
    heisD1_eq_of_action_map rhoV (fun _ _ => rfl) m c hcV w
  rw [← hd]
  exact ha

/-- The global obstruction and its proved descent law, packaged so that the only
remaining input for `ModuleH2WordData` is reflection via a splitting theorem. -/
noncomputable def globalModuleH2WordDescentData
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hc : ∀ i, rho (gen i) = c i)
    (hresLevel : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W w (WordLift A (G ⧸ V.toSubgroup))) :
    ModuleH2WordDescentData (Gamma := G) (A := A) c w where
  obstruction := moduleObsFam W gen rho hcompat
  map_coboundary := fun _ hf =>
    moduleObsFam_B2_mem_range hpres rho hcompat hc hresLevel hf

end GlobalCoboundary

end GQ2.Dyadic.Count
