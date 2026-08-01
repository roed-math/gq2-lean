/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Count.Spike
import GQ2.CentralObstruction
import GQ2.VCocycle

/-!
# Dyadic campaign, ticket CB-1: the comparison isomorphism

CB-S (`GQ2/Dyadic/Count/Spike.lean`) proved the *arithmetic* of the count clause degree-generically
over the word complex.  What was missing — and what CB-S's report named the count-bridge lane's
real risk — is the **vocabulary**: the recursion consumes `TCocycle`/`VCocycle` counts, the word
lane produces `heisD1.ker`/`heisD0.ker` counts, and nothing in the repository connected the two.
This file builds that connection.

## The chain

The comparison is two hops, exactly as at `ℚ₂` (memo §1.2 names the second one "the bridge's
spine"), but here both are built **once, generically**, instead of three times inline:

```
TCocycle D ρ  ≃  Z¹(Γ, Additive T)  ≃+  ↥(heisD1 c w).ker
   §4 tcocycleEquivZ1                §3 z1Equiv
VCocycle DD ρ ≃  Z¹(Γ, DD.Vmod)     ≃+  ↥(heisD1 c w).ker
   §6 vcocycleEquivZ1                §3 z1Equiv
```

* **§1** the observation that makes hop 2 cheap: `heisD1` is the `A`-offset of the word evaluation
  in the *split* group `A ⋊ C`, so `Z¹w` is exactly the set of offset vectors whose Fox lifted
  marking kills the relator family (`mem_ker_heisD1_iff`).  Only the `.a`-coordinate of the
  Heisenberg lift is involved, and `GQ2.FoxH.agHom` projects it off.
* **§2** `IsMarkedPresentation` — the *only* new hypothesis this file introduces: `Γ` is presented
  by the marking modulo the relator family, witnessed at finite discrete targets.  Three fields,
  all of them things a branch supplies about its own `Γ_R`; §2 also proves the rigidity lemma
  (`eq_of_eqOn_gen`) that makes the presented hom unique.
* **§3** `z1Equiv : Z¹(Γ, A) ≃+ ↥(heisD1 c w).ker`, and `h1Equiv` descending it to `H¹`.
* **§4/§6** the two recursion-vocabulary bridges, generic in `Γ` (the `ℚ₂` copies are inline and
  `AbsGalQ2`-specific: `Phase140/{GammaA,GammaR}/Foundation.lean`, `Phase140/Local.lean:195`).
* **§5/§7** the payoff: `tcocycle_cardN` and `hZcardN`, the two `SourceDataN` field values over
  the abstract carrier, each **one rewrite** off CB-S's `IsSelfDualN`.
* **§8** the N0 / `√−2` instantiation, composed with CB-S's `sqrtNegTwo_cardZ1`.

## What is *not* re-proved here

No count.  Every cardinality in §5/§7/§8 is CB-S's, transported.  The arithmetic
(`card_wordZ1_of_degree`, `tcocycle_card_shape`, `hZcard_shape_of_simple`) is imported, not
redone — per the ticket's instruction that the transport, not the arithmetic, is the gap.

## Departure from the `ℚ₂` construction

`WordCohBridge.z1Equiv` (492 ln) builds an explicit inverse: `liftMarking`, `NA_le_ker_classify`,
`liftHom`, and two round-trip lemmas.  That is unnecessary.  The forward map is additive and its
injectivity and surjectivity are *both* one application of the presentation interface, so
`AddEquiv.ofBijective` does the rest.  This is why §3 is ~100 lines rather than ~400, and why the
inverse is noncomputable here and constructive there — the counts do not care.

## Import discipline

Plain-import: `GQ2.Dyadic.Count.Spike` is plain (it imports the plain `Recursion.Numerics` and
`Certificates.N0`), so this file is plain too.  `GQ2.CentralObstruction` and `GQ2.VCocycle` supply
`TCocycle`/`VCocycle`; both are already in the `ℚ₂` stack the spike reaches through
`GQ2.DualityAssembly`, so **the `DualityAssembly` leaf CB-S flagged costs this file nothing extra**
— see the report.

Axioms: no new axioms, no `sorry`, no `decide`.  Every headline prints exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight.CentralObstruction GQ2.SectionEight.AffineTLift

/-! ## §1. The `WordLift` model of the word complex

`heisD1 c w x k` is the `.a`-coordinate of the Heisenberg evaluation of `w k` at primal offsets
`x` and *zero* dual offsets.  The Heisenberg group's `.a`-rule and the split group's `.u`-rule are
the same rule (`GQ2.FoxH.agHom` is a homomorphism precisely for that reason), so the whole of `d¹`
lives in `A ⋊ C`.  Consequences: `d¹x = 0` is *literally* "the lifted marking `i ↦ (xᵢ, cᵢ)` kills
the relator family", and every statement below is about homomorphisms out of `FreeGroup ι`. -/

section WordLiftModel

variable {ι ρ : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A]

/-- The `A ⋊ C`-valued word evaluation at the **Fox lifted marking** `i ↦ (xᵢ, cᵢ)` is the primal
projection of the Heisenberg evaluation at zero dual offsets. -/
theorem lift_foxLift_eq (c : ι → C) (x : ι → A) :
    FreeGroup.lift (foxLift c x)
      = (agHom (A := A) (C := C)).comp
        (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A))) := by
  apply FreeGroup.ext_hom
  intro i
  rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  rfl

/-- **`d¹` is the `A`-offset of the split word evaluation.** -/
theorem heisD1_eq_lift_foxLift_u (c : ι → C) (w : ρ → FreeGroup ι) (x : ι → A) (k : ρ) :
    heisD1 (A := A) c w x k = (FreeGroup.lift (foxLift c x) (w k)).u := by
  rw [heisD1_apply, lift_foxLift_eq]
  rfl

/-- The base coordinate of the split word evaluation is the word evaluation at the lower marking:
the lifted marking really does lift `c`. -/
theorem lift_foxLift_g (c : ι → C) (x : ι → A) (r : FreeGroup ι) :
    (FreeGroup.lift (foxLift c x) r).g = FreeGroup.lift c r := by
  have h : (WordLift.baseProj (A := A) (C := C)).comp (FreeGroup.lift (foxLift c x))
      = FreeGroup.lift c := by
    apply FreeGroup.ext_hom
    intro i
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    rfl
  exact congrArg (fun φ : FreeGroup ι →* C => φ r) h

/-- **The split characterization of `Z¹w`**: at a marking killing the relator family, the word
cocycles are exactly the offset vectors whose lifted marking kills the family in `A ⋊ C`.

This is the statement that turns the comparison isomorphism into an application of a presentation's
universal property, and it is degree-generic: no `Fin 4`, no `A × A`, no marking arity. -/
theorem mem_ker_heisD1_iff {c : ι → C} {w : ρ → FreeGroup ι}
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (x : ι → A) :
    x ∈ (heisD1 (A := A) c w).ker ↔ ∀ k, FreeGroup.lift (foxLift c x) (w k) = 1 := by
  simp only [AddMonoidHom.mem_ker, funext_iff, Pi.zero_apply]
  refine forall_congr' fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · refine WordLift.ext ?_ ?_
    · rw [WordLift.one_u, ← heisD1_eq_lift_foxLift_u]
      exact hk
    · rw [WordLift.one_g, lift_foxLift_g]
      exact hr k
  · rw [heisD1_eq_lift_foxLift_u, hk, WordLift.one_u]

end WordLiftModel

/-! ## §2. The marked-presentation interface

The one hypothesis this file adds.  It says exactly what "`Γ = ⟨ι ∣ w⟩` as a profinite group"
means *for the purposes of degree-≤1 cohomology*, and no more: the letters generate topologically,
the relators die, and relator-killing markings of finite discrete groups extend.  Nothing about
free profinite groups, normal closures or `PWord` resolution appears — a branch discharges the
interface however it likes (`GQ2.presentationLift` is the intended route for
`GQ2.Dyadic.GammaR n q R`).

Compare the `ℚ₂` ancestor, which hard-codes the presentation *by using the carrier*:
`WordCohBridge` is built over the literal `FreeProfiniteGroup (Fin 4) ⧸ NA`, so `NA_le_ker_classify`
must be reproved per relator.  Abstracting the property instead of the carrier is what makes the
degree-generic statement possible at all. -/

section Presentation

variable {ι ρ : Type*}

/-- **`Γ` is presented by the marking `gen` modulo the relator family `w`**, witnessed at finite
discrete targets.

The `Finite`/`DiscreteTopology` binders on `Q` make the field as *weak* as possible — the only
target this file ever instantiates it at is the split group `A ⋊ C` of a finite discrete module
over a finite discrete lower group — so a branch has the least to prove. -/
structure IsMarkedPresentation (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (gen : ι → Γ) (w : ρ → FreeGroup ι) : Prop where
  /-- The marked letters topologically generate `Γ`. -/
  gen_top : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤
  /-- Every relator of the family dies at the marking. -/
  rel : ∀ k, FreeGroup.lift gen (w k) = 1
  /-- Every relator-killing marking of a finite discrete group is the restriction along `gen` of a
  continuous hom out of `Γ` (necessarily unique, by `gen_top` and `eq_of_eqOn_gen`). -/
  extend : ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (f : ι → Q), (∀ k, FreeGroup.lift f (w k) = 1) →
      ∃ φ : ContinuousMonoidHom Γ Q, ∀ i, φ (gen i) = f i

/-- **Rigidity**: a continuous hom out of `Γ` into a Hausdorff group is determined by its values on
the marked letters.  This is the uniqueness half of the presentation, and it is what makes both
`toZ1w_injective` and the base-compatibility step of `toZ1w_surjective` one-liners. -/
theorem eq_of_eqOn_gen {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {gen : ι → Γ} (hgen : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤)
    {Q : Type} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {φ ψ : ContinuousMonoidHom Γ Q} (h : ∀ i, φ (gen i) = ψ (gen i)) : φ = ψ := by
  have hle : Subgroup.closure (Set.range gen) ≤ φ.toMonoidHom.eqLocus ψ.toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact h i
  have hcl : IsClosed ((φ.toMonoidHom.eqLocus ψ.toMonoidHom : Subgroup Γ) : Set Γ) :=
    isClosed_eq φ.continuous_toFun ψ.continuous_toFun
  have hall := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [hgen] at hall
  exact DFunLike.ext _ _ fun γ => hall (Subgroup.mem_top γ)

end Presentation

/-! ## §3. The comparison isomorphism

The ticket's `z1Equiv`, and CB1 memo §1.2's "bridge's spine" in degree-generic form.

The `ℚ₂` ancestors (`WordCohBridge.z1Equiv`, `WordCohBridgeR.z1EquivR`) construct the inverse by
hand: an admissible marking of `A ⋊ C`, `NA_le_ker_classify`, `Marking.descend`, two round-trip
lemmas.  None of that is needed.  §1 says the forward map's image is cut out by *exactly* the
condition `IsMarkedPresentation.extend` discharges, and §2's rigidity gives injectivity, so the map
is bijective and `AddEquiv.ofBijective` finishes.  The price is that the inverse is noncomputable;
no count notices. -/

section Comparison

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A] [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
  {gen : ι → Γ} {w : ρ → FreeGroup ι} {c : ι → C}
  (rho : ContinuousMonoidHom Γ C) (hcompat : ∀ (γ : Γ) (a : A), γ • a = rho γ • a)
  (hc : ∀ i, rho (gen i) = c i)

include hcompat in
/-- The split-group hom `γ ↦ (z γ, ρ γ)` attached to a continuous crossed cocycle: the cocycle
identity **is** the `A ⋊ C` product law read on the offset slot. -/
def wordHom (z : Z1 Γ A) : ContinuousMonoidHom Γ (WordLift A C) where
  toFun γ := ⟨z.1 γ, rho γ⟩
  map_one' := by
    ext
    · show z.1 1 = 0
      exact Z1_apply_one z
    · show rho 1 = 1
      exact map_one rho
  map_mul' γ δ := by
    have hz := (mem_Z1_iff.mp z.2).2 γ δ
    ext
    · show z.1 (γ * δ) = z.1 γ + rho γ • z.1 δ
      rw [hz, hcompat]
    · show rho (γ * δ) = rho γ * rho δ
      exact map_mul rho γ δ
  continuous_toFun := by
    have hg : Continuous fun γ : Γ => ((z.1 γ, rho γ) : A × C) :=
      ((mem_Z1_iff.mp z.2).1).prodMk rho.continuous_toFun
    exact (continuous_of_discreteTopology
      (f := (WordLift.equivProd (A := A) (C := C)).symm)).comp hg

/-- The base projection of the split group, as a continuous hom (the group is discrete). -/
def baseProjC : ContinuousMonoidHom (WordLift A C) C :=
  ⟨WordLift.baseProj, continuous_of_discreteTopology⟩

omit [DiscreteTopology C] [Finite C] [TopologicalSpace A] [DiscreteTopology A] [Finite A] in
@[simp] theorem baseProjC_apply (p : WordLift A C) : baseProjC (A := A) (C := C) p = p.g := rfl

/-- **Evaluation at the marked letters** — the forward map of the comparison. -/
def evalGen (t : ι → Γ) (z : Z1 Γ A) : ι → A := fun i => z.1 (t i)

omit [IsTopologicalGroup Γ] [Finite C] [Finite A] [ContinuousSMul Γ A]
  [DiscreteTopology (WordLift A C)] in
include hc in
/-- The Fox lifted marking at `evalGen z` is `wordHom z` restricted to the marked letters. -/
theorem foxLift_evalGen (z : Z1 Γ A) :
    foxLift c (evalGen gen z) = fun i => wordHom rho hcompat z (gen i) :=
  funext fun i => WordLift.ext rfl (hc i).symm

omit [IsTopologicalGroup Γ] [Finite C] [Finite A] [ContinuousSMul Γ A]
  [DiscreteTopology (WordLift A C)] in
include hc in
/-- The split word evaluation at `evalGen z` is `wordHom z` of the word's value in `Γ`. -/
theorem lift_foxLift_evalGen (z : Z1 Γ A) (r : FreeGroup ι) :
    FreeGroup.lift (foxLift c (evalGen gen z)) r
      = wordHom rho hcompat z (FreeGroup.lift gen r) := by
  have h : FreeGroup.lift (foxLift c (evalGen gen z))
      = (wordHom rho hcompat z).toMonoidHom.comp (FreeGroup.lift gen) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact congrFun (foxLift_evalGen rho hcompat hc z) i
  exact congrArg (fun φ : FreeGroup ι →* WordLift A C => φ r) h

omit [IsTopologicalGroup Γ] [DiscreteTopology C] [Finite C] in
include hc in
/-- The lower marking is the pushforward of the presented marking along `ρ`. -/
theorem lift_lower (r : FreeGroup ι) : FreeGroup.lift c r = rho (FreeGroup.lift gen r) := by
  have h : FreeGroup.lift c = rho.toMonoidHom.comp (FreeGroup.lift gen) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact (hc i).symm
  exact congrArg (fun φ : FreeGroup ι →* C => φ r) h

omit [DiscreteTopology C] [Finite C] in
include hc in
/-- **The relator hypothesis of the whole word lane, for free.**  `hr` is the input every CB-S
theorem takes; a presented `Γ` supplies it, so no branch has to re-verify relator death downstream
of the marking. -/
theorem lower_rel (hpres : IsMarkedPresentation Γ gen w) (k : ρ) :
    FreeGroup.lift c (w k) = 1 := by
  rw [lift_lower rho hc, hpres.rel k, map_one]

omit [Finite C] [Finite A] [ContinuousSMul Γ A] [DiscreteTopology (WordLift A C)] in
include hcompat hc in
/-- **Forward: the evaluation lands in `Z¹w`.**  Each relator dies in `Γ`, so its lifted word value
is `wordHom z 1 = 1`, whose offset is `0`. -/
theorem evalGen_mem_ker (hpres : IsMarkedPresentation Γ gen w) (z : Z1 Γ A) :
    evalGen gen z ∈ (heisD1 (A := A) c w).ker := by
  refine (mem_ker_heisD1_iff (lower_rel rho hc hpres) _).mpr fun k => ?_
  rw [lift_foxLift_evalGen rho hcompat hc z, hpres.rel k, map_one]

include hcompat hc in
/-- The forward map, bundled additively. -/
noncomputable def toZ1w (hpres : IsMarkedPresentation Γ gen w) :
    Z1 Γ A →+ ↥(heisD1 (A := A) c w).ker :=
  AddMonoidHom.mk'
    (fun z => ⟨evalGen gen z, evalGen_mem_ker rho hcompat hc hpres z⟩)
    (fun _ _ => Subtype.ext (funext fun _ => rfl))

omit [Finite C] [Finite A] [ContinuousSMul Γ A] [DiscreteTopology (WordLift A C)] in
@[simp] theorem toZ1w_coe (hpres : IsMarkedPresentation Γ gen w) (z : Z1 Γ A) :
    (toZ1w rho hcompat hc hpres z : ι → A) = fun i => z.1 (gen i) := rfl

omit [ContinuousSMul Γ A] in
include hcompat hc in
/-- **Injective**, by §2's rigidity: two cocycles agreeing on the marked letters have `wordHom`s
agreeing on the marked letters, hence equal `wordHom`s, hence are equal. -/
theorem toZ1w_injective (hpres : IsMarkedPresentation Γ gen w) :
    Function.Injective (toZ1w rho hcompat hc hpres) := by
  intro z z' hzz
  have hgen : ∀ i, wordHom rho hcompat z (gen i) = wordHom rho hcompat z' (gen i) := fun i =>
    WordLift.ext (congrFun (congrArg Subtype.val hzz) i) rfl
  have heq := eq_of_eqOn_gen hpres.gen_top hgen
  exact Subtype.ext (funext fun γ =>
    congrArg (fun φ : ContinuousMonoidHom Γ (WordLift A C) => (φ γ).u) heq)

omit [ContinuousSMul Γ A] in
include hcompat hc in
/-- **Surjective**, by the presentation: §1 says a word cocycle *is* a relator-killing marking of
`A ⋊ C`, so `extend` produces the hom; rigidity identifies its base coordinate with `ρ`, which is
exactly what makes its offset coordinate a crossed cocycle. -/
theorem toZ1w_surjective (hpres : IsMarkedPresentation Γ gen w) :
    Function.Surjective (toZ1w rho hcompat hc hpres) := by
  rintro ⟨x, hx⟩
  obtain ⟨φ, hφ⟩ := hpres.extend (foxLift c x)
    ((mem_ker_heisD1_iff (lower_rel rho hc hpres) x).mp hx)
  have hbase : (baseProjC (A := A) (C := C)).comp φ = rho := by
    refine eq_of_eqOn_gen hpres.gen_top fun i => ?_
    show (φ (gen i)).g = rho (gen i)
    rw [hφ i, hc i]
    rfl
  have hg : ∀ γ : Γ, (φ γ).g = rho γ := fun γ =>
    congrArg (fun σ : ContinuousMonoidHom Γ C => σ γ) hbase
  refine ⟨⟨fun γ => (φ γ).u, mem_Z1_iff.mpr
    ⟨continuous_of_discreteTopology.comp φ.continuous_toFun, fun γ δ => ?_⟩⟩,
    Subtype.ext (funext fun i => congrArg WordLift.u (hφ i))⟩
  show (φ (γ * δ)).u = (φ γ).u + γ • (φ δ).u
  rw [map_mul φ γ δ, WordLift.mul_u, hg γ, hcompat]

include hcompat hc in
/-- **The comparison isomorphism** — the ticket's deliverable, and the degree-generic replacement
for `WordCohBridge.z1Equiv` (`Fin 4`-indexed, `Γ_A`-specific) and `WordCohBridgeR.z1EquivR`.

Continuous crossed `A`-cocycles of a `(ι, w)`-presented profinite group are exactly the word
cocycles of the pushed marking `c = ρ ∘ gen`.  Nothing in the statement mentions the arity of the
marking or the number of relators; the `ℚ₂` `4` and `2` are `Nat.card ι` and `Nat.card ρ`. -/
noncomputable def z1Equiv (hpres : IsMarkedPresentation Γ gen w) :
    Z1 Γ A ≃+ ↥(heisD1 (A := A) c w).ker :=
  AddEquiv.ofBijective (toZ1w rho hcompat hc hpres)
    ⟨toZ1w_injective rho hcompat hc hpres, toZ1w_surjective rho hcompat hc hpres⟩

omit [ContinuousSMul Γ A] in
@[simp] theorem z1Equiv_coe (hpres : IsMarkedPresentation Γ gen w) (z : Z1 Γ A) :
    ((z1Equiv rho hcompat hc hpres z : ↥(heisD1 (A := A) c w).ker) : ι → A)
      = fun i => z.1 (gen i) := rfl

omit [ContinuousSMul Γ A] in
include hcompat hc in
/-- The cardinality form: **this is the equation the whole count lane transports along.** -/
theorem card_Z1_eq_card_wordZ1 (hpres : IsMarkedPresentation Γ gen w) :
    Nat.card (Z1 Γ A) = Nat.card ↥(heisD1 (A := A) c w).ker :=
  Nat.card_congr (z1Equiv rho hcompat hc hpres).toEquiv

/-! ### The `H¹` descent

`z1Equiv` carries continuous coboundaries onto the image of `d⁰`, because `δ⁰m` evaluated at the
marked letter `gen i` is `gen i • m − m = cᵢ • m − m = (d⁰m)ᵢ` — the two coboundary maps are the
*same formula* read through `hc`. -/

include hcompat hc in
/-- The comparison carries `B¹(Γ, A)` exactly onto `im d⁰`. -/
theorem map_B1 (hpres : IsMarkedPresentation Γ gen w) :
    ((B1 Γ A).addSubgroupOf (Z1 Γ A)).map (z1Equiv rho hcompat hc hpres).toAddMonoidHom
      = (heisD0 (A := A) c).range.addSubgroupOf (heisD1 (A := A) c w).ker := by
  have hcob : ∀ (m : A) (z : Z1 Γ A), dZero Γ A m = z.1 → evalGen gen z = heisD0 (A := A) c m := by
    intro m z hm
    funext i
    show z.1 (gen i) = c i • m - m
    rw [← hm]
    show gen i • m - m = c i • m - m
    rw [hcompat, hc i]
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨z, ⟨m, hm⟩, rfl⟩
    exact ⟨m, (hcob m z hm).symm⟩
  · rintro ⟨m, hm⟩
    refine ⟨⟨dZero Γ A m, B1_le_Z1 ⟨m, rfl⟩⟩, ⟨m, rfl⟩, Subtype.ext ?_⟩
    show evalGen gen (⟨dZero Γ A m, B1_le_Z1 ⟨m, rfl⟩⟩ : Z1 Γ A) = y.1
    rw [hcob m _ rfl, hm]

include hcompat hc in
/-- **`H¹` of a presented `Γ` is the word complex's `H¹`** — the degree-generic `h1Equiv`
(CB1 memo §3.4's second half). -/
noncomputable def h1Equiv (hpres : IsMarkedPresentation Γ gen w) :
    H1 Γ A ≃+ StokesH1 (heisD0 (A := A) c) (heisD1 (A := A) c w) :=
  QuotientAddGroup.congr _ _ (z1Equiv rho hcompat hc hpres) (map_B1 rho hcompat hc hpres)

end Comparison

end GQ2.Dyadic.Count
