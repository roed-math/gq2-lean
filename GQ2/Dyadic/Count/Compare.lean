/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Count.Spike
import GQ2.CentralObstruction
import GQ2.VCocycle
import GQ2.RadicalEdge.GammaA

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
* **§8** the N0 / `√−2` instantiation, at CB-S's degree bookkeeping (`nCompact_degree`, deficiency
  `2h + 2`) and N0's own `sqrtNegTwo_isStokesEndpoint` — the recursion-vocabulary counterpart of
  CB-S's `sqrtNegTwo_cardZ1`, which is the same value read on the word side.

## What is *not* re-proved here

No count.  Every cardinality in §5/§7/§8 is CB-S's, transported.  The arithmetic
(`card_wordZ1_of_degree`, `tcocycle_card_shape`, `hZcard_shape_of_simple`) is imported, not
redone — per the ticket's instruction that the transport, not the arithmetic, is the gap.

## Departure from the `ℚ₂` construction

`WordCohBridge.z1Equiv` (492 ln) builds an explicit inverse: `liftMarking`, `NA_le_ker_classify`,
`liftHom`, and two round-trip lemmas.  That is unnecessary.  The forward map is additive and its
injectivity and surjectivity are *both* one application of the presentation interface, so
`AddEquiv.ofBijective` does the rest.  This is why §3 (including `h1Equiv`) is 240 lines rather
than 492, and why the inverse is noncomputable here and constructive there — the counts do not
care.

## Import discipline

Plain-import: `GQ2.Dyadic.Count.Spike` is plain (it imports the plain `Recursion.Numerics` and
`Certificates.N0`), so this file is plain too.

`GQ2.DualityAssembly` — the leaf CB-S flagged for a hoist — **costs this file nothing**: it is
already in the spike's closure.  Measured import delta over the spike: 128 → 146 `GQ2` modules,
of which the driver is `GQ2.RadicalEdge.GammaA` (with `Prop23`, `SectionSeven.*`,
`LocalLiftingDuality`, `WordCohBridge` behind it).  That import is not decorative: it carries
`cActT`, the campaign's **canonical** conjugation action of `Bg ⧸ D.M` on `Additive ↥D.T`, which
is the very instance `SourceDataN.tcocycle_card` is stated against.  Re-declaring it here would
have produced an instance diamond at CB-4, so the import is the correct trade.  Note that
`LocalLiftingDuality` (which *consumes* B6/B7) arrives in the closure without any print moving:
every headline below is still std-3.

`GQ2.CentralObstruction` and `GQ2.VCocycle` supply `TCocycle`/`VCocycle`.

## Verified against the consumer (for CB-4)

Both field values were checked by stating the **verbatim `SourceDataN` field goal** — in the
recursion's own vocabulary (`RF.YB`, `En.radData l h`, `En.descData l h`, `rhoPrimeK`,
`BoundaryLiftsK`) — and closing it with the theorem below.  Both close.  The recipes:

* `tcocycle_card` ← `tcocycle_cardN`, with three `letI`s and **nothing else**:
  ```
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) := ⊥
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) := ⟨rfl⟩
  letI : DistribMulAction Γ (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom _ (rhoPrimeK RF b F (En.radData l h) rfl ρ).toMonoidHom
  exact tcocycle_cardN (rhoPrimeK RF b F (En.radData l h) rfl ρ) (fun _ _ => rfl) hc …
  ```
  The `hcomp` argument is `rfl` — the `cActT` instance imported here **is** the one the field is
  stated against, so no transport is needed.
* `hZcard` ← `hZcardN` at `E := RF.YC`, `theta := ρ.1.1`, with `hround` discharged for free by the
  already-landed `rho0_descData_rhoPrimeK` (`GQ2/Dyadic/Recursion/Phase140Assembly.lean:77`):
  ```
  fun γ v => congrArg (fun g : RF.YC => g • v) (rho0_descData_rhoPrimeK b F En l h ρ γ)
  ```
  ⚠ **One extra `letI` is needed**, and it is a pre-existing seam of the recursion's vocabulary,
  not one this file introduces: `En.Vmod` and `(En.descData l h).Vmod` are definitionally equal but
  not syntactically so, so instance search does not find `DistribMulAction RF.YC` on the latter.
  Add `letI : DistribMulAction RF.YC (En.descData l h).Vmod := (inferInstance : DistribMulAction
  RF.YC En.Vmod)`.  (The `ℚ₂` proofs lean on the same defeq, but implicitly, through `rw`.)
  `hsimple` is the record's own binder plus `hVne`: `⟨nontrivial_of_ne 0 v hv.symm, hsimple⟩`.

Axioms: no new axioms, no `sorry`, no `decide`.  Every headline prints exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`) — two (`lift_foxLift_g`, `lift_lower`) print a
strict subset.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction GQ2.SectionEight.AffineTLift
open GQ2.SectionEight.RadicalEdgeGammaA

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

/-- The **admissibility side condition** on a marking `f : ι → Q`: the normal closure of the
images of the *distinguished* letters `J ⊆ ι` — for the campaign's alphabet, the wild letters
`x₀, …, x_n` — is a `2`-group.

This is the marking-level reading of `GQ2.Dyadic.IsAdmissibleU`'s second clause, and it is the
only thing separating the two presentation classes below. -/
def IsWildTwo (J : Set ι) {Q : Type*} [Group Q] (f : ι → Q) : Prop :=
  IsPGroup 2 (Subgroup.normalClosure (f '' J))

/-- **`Γ` is presented by `gen` modulo `w`, admissibly** — the *restricted* presentation class,
and the one the campaign's `Γ_R` actually satisfies.

Clauses (i) `gen_top` and (ii) `rel` are `IsMarkedPresentation`'s verbatim; the two classes share
them.  Clause (iii) `extend` is `IsMarkedPresentation`'s **weakened**: only markings that
additionally satisfy `IsWildTwo J` are required to extend.  Hence
`IsMarkedPresentation.toAdmissible`: the plain class implies this one, for *every* `J`.

⚠ The weakening is forced, and the converse fails.  `GQ2.Dyadic.GammaR n q R` is the **admissible
limit** `F ⧸ N_R`, the pro-`2` clause on the wild part being part of its definition
(`GQ2/Dyadic/AdmissibleR.lean` §3).  The plain clause (iii) is *equivalent* to being the bare
two-relator presentation `GammaBare`, and over that group the wild part is never pro-`2`
(`Count/Wild.lean` §4).  CB-W's `ℤ/3` markings kill both relators and provably do **not** extend
over `Γ_R`; `IsWildTwo` is exactly what excludes them
(`Count/Presentation.lean`, `testMarking_not_isWildTwo`). -/
structure IsAdmissibleMarkedPresentation (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (gen : ι → Γ) (w : ρ → FreeGroup ι) (J : Set ι) : Prop where
  /-- The marked letters topologically generate `Γ`. -/
  gen_top : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤
  /-- Every relator of the family dies at the marking. -/
  rel : ∀ k, FreeGroup.lift gen (w k) = 1
  /-- Every relator-killing **admissible** marking of a finite discrete group is the restriction
  along `gen` of a continuous hom out of `Γ` (necessarily unique, by `gen_top` and
  `eq_of_eqOn_gen`).  The `IsWildTwo J` hypothesis is the whole difference from
  `IsMarkedPresentation.extend`. -/
  extend : ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (f : ι → Q), (∀ k, FreeGroup.lift f (w k) = 1) → IsWildTwo J f →
      ∃ φ : ContinuousMonoidHom Γ Q, ∀ i, φ (gen i) = f i

/-- **The plain class implies the restricted one**, for every choice of distinguished letters:
dropping a hypothesis of `extend` is a weakening.  This is the precise sense in which the two
classes are the same statement with clause (iii) restricted — and the reason nothing downstream of
`IsAdmissibleMarkedPresentation` is closed to a branch that can supply the plain form (e.g. any
branch working over `GammaBare`). -/
theorem IsMarkedPresentation.toAdmissible {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {gen : ι → Γ} {w : ρ → FreeGroup ι}
    (h : IsMarkedPresentation Γ gen w) (J : Set ι) :
    IsAdmissibleMarkedPresentation Γ gen w J :=
  ⟨h.gen_top, h.rel, fun f hf _ => h.extend f hf⟩

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

/-! ### Admissibility of the Fox lifted marking

The restricted `extend` is applied at exactly one family of markings: the Fox lifted markings
`foxLift c x : ι → A ⋊ C` of §1.  Their admissibility is **not** automatic — it is an extension
statement, and both halves of the extension have to be `2`-groups:

* the base coordinate contributes the normal closure of `c '' J` in `C`;
* the offset coordinate contributes a subgroup of `A`.

So `z1Equiv` below acquires exactly two side conditions, `hA₂` (the module is `2`-torsion, the
campaign's standing `∀ a : A, a + a = 0` — `GQ2/LocalLiftingDuality.lean:222`) and `hwild2`
(the *lower* marking is admissible).  Both are honest: with `A = ℤ/3` and `c` CB-W's `ℤ/3`
marking, the lifted marking is a genuine non-extending relator-killer. -/

section AdmissibleLift

variable {ι : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- In the split group `A ⋊ C` over a `2`-torsion module, an element with trivial base coordinate
squares to `1`: `(u, 1)² = (u + u, 1) = 1`. -/
theorem sq_eq_one_of_g_eq_one (hA₂ : ∀ a : A, a + a = 0) {p : WordLift A C} (hp : p.g = 1) :
    p ^ 2 = 1 := by
  rw [pow_two]
  refine WordLift.ext ?_ ?_
  · show p.u + p.g • p.u = 0
    rw [hp, one_smul, hA₂]
  · show p.g * p.g = 1
    rw [hp, one_mul]

/-- The base projection carries the lifted marking's normal closure into the lower marking's. -/
theorem normalClosure_foxLift_le_comap (J : Set ι) (c : ι → C) (x : ι → A) :
    Subgroup.normalClosure ((foxLift c x) '' J)
      ≤ (Subgroup.normalClosure (c '' J)).comap (WordLift.baseProj (A := A) (C := C)) :=
  Subgroup.normalClosure_le_normal <| by
    rintro _ ⟨i, hi, rfl⟩
    exact Subgroup.subset_normalClosure ⟨i, hi, rfl⟩

/-- **The Fox lifted marking is admissible** as soon as the module is `2`-torsion and the lower
marking is admissible.  This is the one place the restricted clause (iii) is fed, and it is an
extension argument: kill the base coordinate by the lower marking's `2`-power, then kill what is
left — an element of `A` — by squaring. -/
theorem isWildTwo_foxLift {J : Set ι} {c : ι → C} (hA₂ : ∀ a : A, a + a = 0)
    (hwild2 : IsWildTwo J c) (x : ι → A) : IsWildTwo J (foxLift c x) := by
  rintro ⟨p, hp⟩
  have hbase : WordLift.baseProj (A := A) (C := C) p ∈ Subgroup.normalClosure (c '' J) :=
    normalClosure_foxLift_le_comap J c x hp
  obtain ⟨k, hk⟩ := hwild2 ⟨_, hbase⟩
  have hk' : (p ^ 2 ^ k).g = 1 := by
    have := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [show (p ^ 2 ^ k).g = WordLift.baseProj (A := A) (C := C) (p ^ 2 ^ k) from rfl, map_pow]
    exact this
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_succ, pow_mul]
  exact sq_eq_one_of_g_eq_one hA₂ hk'

end AdmissibleLift

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
  {gen : ι → Γ} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}
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
theorem lower_rel (hpres : IsAdmissibleMarkedPresentation Γ gen w J) (k : ρ) :
    FreeGroup.lift c (w k) = 1 := by
  rw [lift_lower rho hc, hpres.rel k, map_one]

omit [Finite C] in
include hc in
/-- **Generation transports to the lower marking.**  If the letters topologically generate `Γ` and
`ρ` is onto the finite discrete `C`, then the pushed marking generates `C` *algebraically* — the
`hgen` input of CB-S's `fixedPts` bridge (`card_ker_heisD0_eq_card_fixedPts`), which is otherwise
an extra obligation on every branch.  Discreteness of `C` is what upgrades "topologically
generates" to "generates". -/
theorem closure_range_lower_eq_top (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hsurj : Function.Surjective rho) : Subgroup.closure (Set.range c) = ⊤ := by
  set H := Subgroup.closure (Set.range c) with hH
  have hle : Subgroup.closure (Set.range gen) ≤ H.comap rho.toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, (hc i).symm⟩
  have hcl : IsClosed ((H.comap rho.toMonoidHom : Subgroup Γ) : Set Γ) := by
    show IsClosed (⇑rho ⁻¹' (H : Set C))
    exact IsClosed.preimage rho.continuous_toFun (isClosed_discrete _)
  have hall := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [hpres.gen_top] at hall
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨γ, rfl⟩ := hsurj x
  exact hall (Subgroup.mem_top γ)

omit [Finite C] [Finite A] [ContinuousSMul Γ A] [DiscreteTopology (WordLift A C)] in
include hcompat hc in
/-- **Forward: the evaluation lands in `Z¹w`.**  Each relator dies in `Γ`, so its lifted word value
is `wordHom z 1 = 1`, whose offset is `0`. -/
theorem evalGen_mem_ker (hpres : IsAdmissibleMarkedPresentation Γ gen w J) (z : Z1 Γ A) :
    evalGen gen z ∈ (heisD1 (A := A) c w).ker := by
  refine (mem_ker_heisD1_iff (lower_rel rho hc hpres) _).mpr fun k => ?_
  rw [lift_foxLift_evalGen rho hcompat hc z, hpres.rel k, map_one]

include hcompat hc in
/-- The forward map, bundled additively. -/
noncomputable def toZ1w (hpres : IsAdmissibleMarkedPresentation Γ gen w J) :
    Z1 Γ A →+ ↥(heisD1 (A := A) c w).ker :=
  AddMonoidHom.mk'
    (fun z => ⟨evalGen gen z, evalGen_mem_ker rho hcompat hc hpres z⟩)
    (fun _ _ => Subtype.ext (funext fun _ => rfl))

omit [Finite C] [Finite A] [ContinuousSMul Γ A] [DiscreteTopology (WordLift A C)] in
@[simp] theorem toZ1w_coe (hpres : IsAdmissibleMarkedPresentation Γ gen w J) (z : Z1 Γ A) :
    (toZ1w rho hcompat hc hpres z : ι → A) = fun i => z.1 (gen i) := rfl

omit [ContinuousSMul Γ A] in
include hcompat hc in
/-- **Injective**, by §2's rigidity: two cocycles agreeing on the marked letters have `wordHom`s
agreeing on the marked letters, hence equal `wordHom`s, hence are equal. -/
theorem toZ1w_injective (hpres : IsAdmissibleMarkedPresentation Γ gen w J) :
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
exactly what makes its offset coordinate a crossed cocycle.

⚠ This is the **only** consumer of clause (iii), so it is the only place the restriction bites:
the marking handed to `extend` is `foxLift c x`, and its admissibility has to be *proved*.
`isWildTwo_foxLift` does that from the two side conditions `hA₂`/`hwild2`, which are therefore
exactly the price of the weakening — nothing else in §3 changes. -/
theorem toZ1w_surjective (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hA₂ : ∀ a : A, a + a = 0) (hwild2 : IsWildTwo J c) :
    Function.Surjective (toZ1w rho hcompat hc hpres) := by
  rintro ⟨x, hx⟩
  obtain ⟨φ, hφ⟩ := hpres.extend (foxLift c x)
    ((mem_ker_heisD1_iff (lower_rel rho hc hpres) x).mp hx)
    (isWildTwo_foxLift hA₂ hwild2 x)
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
marking or the number of relators; the `ℚ₂` `4` and `2` are `Nat.card ι` and `Nat.card ρ`.

⚠ The presentation hypothesis is the **restricted** one, and the two side conditions are the
exact price: `hA₂` says the coefficient module is `2`-torsion, `hwild2` that the *lower* marking
`c` is admissible.  Both are consumed in one place, `toZ1w_surjective`; the injectivity half is
untouched, since rigidity never invokes clause (iii). -/
noncomputable def z1Equiv (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hA₂ : ∀ a : A, a + a = 0) (hwild2 : IsWildTwo J c) :
    Z1 Γ A ≃+ ↥(heisD1 (A := A) c w).ker :=
  AddEquiv.ofBijective (toZ1w rho hcompat hc hpres)
    ⟨toZ1w_injective rho hcompat hc hpres,
      toZ1w_surjective rho hcompat hc hpres hA₂ hwild2⟩

omit [ContinuousSMul Γ A] in
@[simp] theorem z1Equiv_coe (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hA₂ : ∀ a : A, a + a = 0) (hwild2 : IsWildTwo J c) (z : Z1 Γ A) :
    ((z1Equiv rho hcompat hc hpres hA₂ hwild2 z : ↥(heisD1 (A := A) c w).ker) : ι → A)
      = fun i => z.1 (gen i) := rfl

omit [ContinuousSMul Γ A] in
include hcompat hc in
/-- The cardinality form: **this is the equation the whole count lane transports along.** -/
theorem card_Z1_eq_card_wordZ1 (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hA₂ : ∀ a : A, a + a = 0) (hwild2 : IsWildTwo J c) :
    Nat.card (Z1 Γ A) = Nat.card ↥(heisD1 (A := A) c w).ker :=
  Nat.card_congr (z1Equiv rho hcompat hc hpres hA₂ hwild2).toEquiv

/-! ### The `H¹` descent

`z1Equiv` carries continuous coboundaries onto the image of `d⁰`, because `δ⁰m` evaluated at the
marked letter `gen i` is `gen i • m − m = cᵢ • m − m = (d⁰m)ᵢ` — the two coboundary maps are the
*same formula* read through `hc`. -/

include hcompat hc in
/-- The comparison carries `B¹(Γ, A)` exactly onto `im d⁰`. -/
theorem map_B1 (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hA₂ : ∀ a : A, a + a = 0) (hwild2 : IsWildTwo J c) :
    ((B1 Γ A).addSubgroupOf (Z1 Γ A)).map
        (z1Equiv rho hcompat hc hpres hA₂ hwild2).toAddMonoidHom
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
noncomputable def h1Equiv (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hA₂ : ∀ a : A, a + a = 0) (hwild2 : IsWildTwo J c) :
    H1 Γ A ≃+ StokesH1 (heisD0 (A := A) c) (heisD1 (A := A) c w) :=
  QuotientAddGroup.congr _ _ (z1Equiv rho hcompat hc hpres hA₂ hwild2)
    (map_B1 rho hcompat hc hpres hA₂ hwild2)

end Comparison

/-! ## §4. The `TCocycle` bridge

The recursion's `T`-cocycles are continuous crossed cocycles valued in `Additive ↥D.T`, for the
conjugation action `cActT` of `Bg ⧸ D.M` — the campaign's canonical instance
(`GQ2/RadicalEdge/GammaA.lean:100`), which is also the one `SourceDataN.tcocycle_card` is stated
against.  `TCocycle` stores continuity *into `Bg`*, so the bridge is a repackaging with no torsor
detour; the only work is that the crossed law is stated at an arbitrary representative `b` of
`ρ γ` while the action uses `Quotient.out`, which `cactFun_eq` reconciles.

At `ℚ₂` this equivalence is written **three times**: twice anonymously inside proofs
(`Phase140/{GammaA,GammaR}/Foundation.lean`) and once as a `private` `AbsGalQ2`-specific def
(`Phase140/Local.lean:195`).  It is generic in `Γ`; here it is written once. -/

section TCocycleBridge

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)]
  (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (hcomp : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)

omit [DiscreteTopology Bg] [IsTopologicalGroup Γ] [TopologicalSpace (Additive ↥D.T)]
  [DiscreteTopology (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)] in
include hcomp in
/-- The `Γ`-action on `Additive ↥D.T`, read at an arbitrary representative of `ρ γ`. -/
theorem smul_eq_conj (γ : Γ) (bb : Bg) (a : Additive ↥D.T)
    (hbb : QuotientGroup.mk bb = rho γ) :
    γ • a = Additive.ofMul (⟨bb * (Additive.toMul a).1 * bb⁻¹,
      D.hT.conj_mem _ (Additive.toMul a).2 _⟩ : ↥D.T) := by
  rw [hcomp γ a]
  apply Additive.toMul.injective
  rw [cActT_toMul]
  exact Subtype.ext (cactFun_eq D (rho γ) hbb (Additive.toMul a))

include hcomp in
/-- **`TCocycle D ρ ≃ Z¹(Γ, Additive T)`**, generic in `Γ`. -/
noncomputable def tcocycleEquivZ1 : TCocycle D rho ≃ ↥(Z1 Γ (Additive ↥D.T)) where
  toFun u :=
    ⟨fun γ => Additive.ofMul ⟨u.u γ, u.mem γ⟩, by
      refine mem_Z1_iff.mpr ⟨?_, fun γ δ => ?_⟩
      · exact (IsLocallyConstant.desc (α := Additive ↥D.T)
          (fun γ => Additive.ofMul (⟨u.u γ, u.mem γ⟩ : ↥D.T))
          (fun a : Additive ↥D.T => ((Additive.toMul a : ↥D.T) : Bg))
          ((IsLocallyConstant.iff_continuous _).mpr u.cont)
          fun a a' haa' => Additive.toMul.injective (Subtype.ext haa')).continuous
      · rw [smul_eq_conj rho hcomp γ (Quotient.out (rho γ))
          (Additive.ofMul ⟨u.u δ, u.mem δ⟩) (QuotientGroup.out_eq' _)]
        apply Additive.toMul.injective
        apply Subtype.ext
        show u.u (γ * δ) = u.u γ * (Quotient.out (rho γ) * u.u δ * (Quotient.out (rho γ))⁻¹)
        exact u.crossed γ δ (Quotient.out (rho γ)) (QuotientGroup.out_eq' _)⟩
  invFun z :=
    { u := fun γ => ((Additive.toMul (z.1 γ) : ↥D.T) : Bg)
      mem := fun γ => (Additive.toMul (z.1 γ)).2
      cont := (((IsLocallyConstant.iff_continuous _).mpr (mem_Z1_iff.mp z.2).1).comp
        fun a : Additive ↥D.T => ((Additive.toMul a : ↥D.T) : Bg)).continuous
      crossed := by
        intro γ δ bb hbb
        have hz := (mem_Z1_iff.mp z.2).2 γ δ
        rw [smul_eq_conj rho hcomp γ bb (z.1 δ) hbb] at hz
        exact congrArg (fun a : Additive ↥D.T => ((Additive.toMul a : ↥D.T) : Bg)) hz }
  left_inv u := by cases u; rfl
  right_inv z := Subtype.ext (funext fun _ => rfl)

end TCocycleBridge

/-! ## §5. `SourceDataN.tcocycle_card`, over the abstract carrier

The first of the two field values.  The proof is three rewrites and **no cohomology**: §4 moves
into `Z¹`, §3 moves into the word complex, and CB-S's `tcocycle_card_shape_fixedPts` reads off the
value.  The `hgen` input CB-S's `fixedPts` bridge needs is supplied by §3's
`closure_range_lower_eq_top`, so a branch never sees it. -/

section TCocycleCount

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)]
  [TopologicalSpace (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
  {gen : ι → Γ} {w : κ → FreeGroup ι} {c : ι → Bg ⧸ D.M} {J : Set ι}
  (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (hcomp : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
  (hc : ∀ i, rho (gen i) = c i)

omit [ContinuousSMul Γ (Additive ↥D.T)] in
include hcomp hc in
/-- **The `SourceDataN.tcocycle_card` value, degree-generically.**

`#Z¹_{Γ,ρ}(T) = SN.tMult #T · #(T^∨)^{Bg/M}` for `SN = standardNumerics n`, from one
`StokesDuality` payload at a degree-`n` marked presentation.  This is the shape
`GQ2/Dyadic/SourceDataN.lean:229` asks for, with `Bg := RF.YB`, `D := En.radData l h` and
`ρ := rhoPrimeK RF b F …`; at `n = 1` it is the frozen `#T² · #(T^∨)^{Y_B/M}` of
`Phase140/GammaA/Foundation.lean:113`, whose `²` was `|ι| − |ρ|`. -/
theorem tcocycle_cardN {n : ℕ} (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hT₂ : ∀ a : Additive ↥D.T, a + a = 0) (hwild2 : IsWildTwo J c)
    (hsurj : Function.Surjective rho) (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hd : StokesDuality c w (Additive ↥D.T)) (hend : IsStokesEndpoint w) :
    Nat.card (TCocycle D rho)
      = (standardNumerics n).tMult (Nat.card (Additive ↥D.T))
        * Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) := by
  rw [Nat.card_congr (tcocycleEquivZ1 rho hcomp),
    card_Z1_eq_card_wordZ1 rho hcomp hc hpres hT₂ hwild2,
    tcocycle_card_shape_fixedPts
      (isSelfDualN_of_stokesDuality hdeg hd (lower_rel rho hc hpres) hend)
      (closure_range_lower_eq_top rho hc hpres hsurj)]

end TCocycleCount

/-! ## §6. The `VCocycle` bridge

The `V`-side mirror of §4.  `VCocycle` carries no topology on `V`, storing continuity through the
injection `iV ∘ ofAdd` into the discrete `Bg ⧸ D.T`; the bridge therefore transports local
constancy across that injection in one direction and composes with it in the other.  The acting
group `E` is kept abstract (at `ℚ₂` it is `RF.YC`), linked to the recursion's own `rho0` by the
`hround` hypothesis — the generic form of `rho0_descData_rhoPrime`. -/

section VCocycleBridge

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {E : Type} [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction E DD.Vmod] [DistribMulAction Γ DD.Vmod] [ContinuousSMul Γ DD.Vmod]
  {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)} (theta : ContinuousMonoidHom Γ E)
  (hround : ∀ (γ : Γ) (v : DD.Vmod), rho0 DD rho γ • v = theta γ • v)
  (hact : ∀ (γ : Γ) (v : DD.Vmod), γ • v = theta γ • v)

include hround hact in
/-- **`VCocycle DD ρ ≃ Z¹(Γ, V)`**, generic in `Γ` and in the acting group. -/
def vcocycleEquivZ1 : VCocycle DD rho ≃ ↥(Z1 Γ DD.Vmod) where
  toFun u :=
    ⟨fun γ => u.c γ, by
      refine mem_Z1_iff.mpr ⟨?_, fun γ δ => ?_⟩
      · exact (IsLocallyConstant.desc (α := DD.Vmod) (fun γ => u.c γ)
          (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
          ((IsLocallyConstant.iff_continuous _).mpr u.cont)
          fun a a' haa' => iV_ofAdd_inj DD haa').continuous
      · rw [hact γ (u.c δ), ← hround γ (u.c δ)]
        exact u.crossed γ δ⟩
  invFun z :=
    { c := fun γ => z.1 γ
      cont := (continuous_of_discreteTopology
        (f := fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))).comp (mem_Z1_iff.mp z.2).1
      crossed := fun γ δ => by
        rw [hround γ (z.1 δ), ← hact γ (z.1 δ)]
        exact (mem_Z1_iff.mp z.2).2 γ δ }
  left_inv _ := rfl
  right_inv _ := rfl

end VCocycleBridge

/-! ## §7. `SourceDataN.hZcard`, over the abstract carrier

The second field value, from the **same** `IsSelfDualN` — memo §1.5's design instruction in
miniature, now with the vocabulary attached.  The outer `#V` stays literal and the inner factor
`SN.h1Mult #V` is the one that moves (SD-R3's shape rule); CB-S proved the side condition
"the dual has no invariants" from the record's own `hsimple`/`hnt`, so nothing extra is needed. -/

section VCocycleCount

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {E : Type} [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction E DD.Vmod] [DistribMulAction Γ DD.Vmod] [ContinuousSMul Γ DD.Vmod]
  [TopologicalSpace (WordLift DD.Vmod E)] [DiscreteTopology (WordLift DD.Vmod E)]
  {gen : ι → Γ} {w : κ → FreeGroup ι} {c : ι → E} {J : Set ι}
  {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)} (theta : ContinuousMonoidHom Γ E)
  (hround : ∀ (γ : Γ) (v : DD.Vmod), rho0 DD rho γ • v = theta γ • v)
  (hact : ∀ (γ : Γ) (v : DD.Vmod), γ • v = theta γ • v)
  (hc : ∀ i, theta (gen i) = c i)

omit [ContinuousSMul Γ DD.Vmod] in
include hround hact hc in
/-- **The `SourceDataN.hZcard` value, degree-generically**: `#Z¹(V) = #V · SN.h1Mult #V`.

The shape `GQ2/Dyadic/SourceDataN.lean:274` asks for.  `hsimple`/`hnt` are the record's own
binders; at `n = 1` this is the frozen `#V · #V` of `Phase140/GammaA/Foundation.lean:48`. -/
theorem hZcardN {n : ℕ} (hpres : IsAdmissibleMarkedPresentation Γ gen w J)
    (hV₂ : ∀ v : DD.Vmod, v + v = 0) (hwild2 : IsWildTwo J c)
    (hsurj : Function.Surjective theta) (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hd : StokesDuality c w DD.Vmod) (hend : IsStokesEndpoint w)
    (hsimple : IsSimpleModTwo E DD.Vmod) (hnt : ∃ (g : E) (v : DD.Vmod), g • v ≠ v) :
    Nat.card (VCocycle DD rho)
      = Nat.card DD.Vmod * (standardNumerics n).h1Mult (Nat.card DD.Vmod) := by
  rw [Nat.card_congr (vcocycleEquivZ1 theta hround hact),
    card_Z1_eq_card_wordZ1 theta hact hc hpres hV₂ hwild2,
    hZcard_shape_of_simple
      (isSelfDualN_of_stokesDuality hdeg hd (lower_rel theta hc hpres) hend)
      (closure_range_lower_eq_top theta hc hpres hsurj) hsimple hnt]

end VCocycleCount

/-! ## §8. The N0 / `√−2` instantiation

CB-S's §7 closed the *value* bridge at N0 (`sqrtNegTwo_cardZ1`: deficiency `2h + 2`, so `n = 2`
at `h = 0`, and `standardNumerics 2`'s `tMult T = T³` on the nose).  §5 now carries that value
into the recursion's vocabulary: at the `√−2` pilot the `T`-cocycle count is a `SourceDataN`
field value, not a word-complex statement. -/

section N0

open GQ2.Dyadic.Certificates

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)]
  [TopologicalSpace (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]

omit [ContinuousSMul Γ (Additive ↥D.T)] in
/-- **The `T`-cocycle count at branch N0**, in the recursion's vocabulary: at the compact-`N`
family `nCompactFam α h q e` the deficiency is `2h + 2`, so the count is
`SN.tMult #T · #(T^∨)^{Bg/M}` for `SN = standardNumerics (2h + 2)`. -/
theorem nCompact_tcocycle_card {α h q e : ℕ} {gen : Generator (2 + 2 * h) → Γ}
    {J : Set (Generator (2 + 2 * h))}
    {t : Marking (2 + 2 * h) (Bg ⧸ D.M)} (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
    (hcomp : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
    (hc : ∀ i, rho (gen i) = t i)
    (hpres : IsAdmissibleMarkedPresentation Γ gen (nCompactFam α h q e) J)
    (hT₂ : ∀ a : Additive ↥D.T, a + a = 0) (hwild2 : IsWildTwo J (⇑t))
    (hsurj : Function.Surjective rho)
    (hd : StokesDuality (⇑t) (nCompactFam α h q e) (Additive ↥D.T))
    (hend : IsStokesEndpoint (nCompactFam α h q e)) :
    Nat.card (TCocycle D rho)
      = (standardNumerics (2 * h + 2)).tMult (Nat.card (Additive ↥D.T))
        * Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) :=
  tcocycle_cardN rho hcomp hc hpres hT₂ hwild2 hsurj (nCompact_degree h) hd hend

omit [ContinuousSMul Γ (Additive ↥D.T)] in
/-- **The `√−2` pilot** (`(α, h, q, e) = (2, 0, 2, 3)`, `n = 2 = [ℚ₂(√−2) : ℚ₂]`): the
`SourceDataN.tcocycle_card` field value for AS2's branch, with N0's own endpoint certificate and
CB-S's value bridge composed in.  Nothing here is fudged: `standardNumerics 2`'s `tMult T = T³`
**is** the deficiency `2h + 2 + 1 = 3` of the two-relator compact-`N` presentation. -/
theorem sqrtNegTwo_tcocycle_card {gen : Generator 2 → Γ} {J : Set (Generator 2)}
    {t : Marking 2 (Bg ⧸ D.M)}
    (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
    (hcomp : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
    (hc : ∀ i, rho (gen i) = t i)
    (hpres : IsAdmissibleMarkedPresentation Γ gen (nCompactFam 2 0 2 3) J)
    (hT₂ : ∀ a : Additive ↥D.T, a + a = 0) (hwild2 : IsWildTwo J (⇑t))
    (hsurj : Function.Surjective rho)
    (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) (Additive ↥D.T)) :
    Nat.card (TCocycle D rho)
      = (standardNumerics 2).tMult (Nat.card (Additive ↥D.T))
        * Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) :=
  nCompact_tcocycle_card (h := 0) rho hcomp hc hpres hT₂ hwild2 hsurj hd
    sqrtNegTwo_isStokesEndpoint

end N0

/-! ### The `V`-side twin at N0

Same branch, same degree bookkeeping, the other field.  Stated over the abstract acting group `E`
(at the recursion `E = RF.YC`), so it composes with §7 exactly as the `T`-side does with §5. -/

section N0V

open GQ2.Dyadic.Certificates

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {E : Type} [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction E DD.Vmod] [DistribMulAction Γ DD.Vmod]
  [TopologicalSpace (WordLift DD.Vmod E)] [DiscreteTopology (WordLift DD.Vmod E)]

/-- **The `V`-cocycle count at branch N0**: `#Z¹(V) = #V · SN.h1Mult #V` for
`SN = standardNumerics (2h + 2)`. -/
theorem nCompact_hZcard {α h q e : ℕ} {gen : Generator (2 + 2 * h) → Γ}
    {J : Set (Generator (2 + 2 * h))}
    {t : Marking (2 + 2 * h) E} {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
    (theta : ContinuousMonoidHom Γ E)
    (hround : ∀ (γ : Γ) (v : DD.Vmod), rho0 DD rho γ • v = theta γ • v)
    (hact : ∀ (γ : Γ) (v : DD.Vmod), γ • v = theta γ • v)
    (hc : ∀ i, theta (gen i) = t i)
    (hpres : IsAdmissibleMarkedPresentation Γ gen (nCompactFam α h q e) J)
    (hV₂ : ∀ v : DD.Vmod, v + v = 0) (hwild2 : IsWildTwo J (⇑t))
    (hsurj : Function.Surjective theta)
    (hd : StokesDuality (⇑t) (nCompactFam α h q e) DD.Vmod)
    (hend : IsStokesEndpoint (nCompactFam α h q e))
    (hsimple : IsSimpleModTwo E DD.Vmod) (hnt : ∃ (g : E) (v : DD.Vmod), g • v ≠ v) :
    Nat.card (VCocycle DD rho)
      = Nat.card DD.Vmod * (standardNumerics (2 * h + 2)).h1Mult (Nat.card DD.Vmod) :=
  hZcardN theta hround hact hc hpres hV₂ hwild2 hsurj (nCompact_degree h) hd hend hsimple hnt

/-- **The `√−2` pilot, `V`-side**: the `SourceDataN.hZcard` field value for AS2's branch at
`n = 2`, so `h1Mult V = V²` and the count is `#V³` — the degree-`2` replacement for the frozen
`ℚ₂` `#V · #V`. -/
theorem sqrtNegTwo_hZcard {gen : Generator 2 → Γ} {J : Set (Generator 2)} {t : Marking 2 E}
    {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)} (theta : ContinuousMonoidHom Γ E)
    (hround : ∀ (γ : Γ) (v : DD.Vmod), rho0 DD rho γ • v = theta γ • v)
    (hact : ∀ (γ : Γ) (v : DD.Vmod), γ • v = theta γ • v)
    (hc : ∀ i, theta (gen i) = t i)
    (hpres : IsAdmissibleMarkedPresentation Γ gen (nCompactFam 2 0 2 3) J)
    (hV₂ : ∀ v : DD.Vmod, v + v = 0) (hwild2 : IsWildTwo J (⇑t))
    (hsurj : Function.Surjective theta)
    (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) DD.Vmod)
    (hsimple : IsSimpleModTwo E DD.Vmod) (hnt : ∃ (g : E) (v : DD.Vmod), g • v ≠ v) :
    Nat.card (VCocycle DD rho)
      = Nat.card DD.Vmod * (standardNumerics 2).h1Mult (Nat.card DD.Vmod) :=
  nCompact_hZcard (h := 0) theta hround hact hc hpres hV₂ hwild2 hsurj hd
    sqrtNegTwo_isStokesEndpoint hsimple hnt

end N0V

end GQ2.Dyadic.Count
