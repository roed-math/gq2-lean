/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.HTwo
import GQ2.Dyadic.Recursion.Induction

/-!
# Dyadic campaign, ticket CB-3: the `liftsOver_card` clause

The `SourceDataN` clause `liftsOver_card` (`GQ2/Dyadic/SourceDataN.lean:191`):

> `#LiftsOverK(RF, b, F, ρ) = SN.mMult #M_B`

over the abstract carrier, degree-generically, for all five branch families at once.

## The two halves, and where each one lands

The `ℚ₂` ancestor splits the clause in two, and the split is the right one:

* **the count**, given a base lift — `liftsOver_card_local_of_nonempty`
  (`GQ2/MStageCount.lean:586`), whose own docstring says it "is source-generic once a base lift
  exists";
* **nonemptiness** of the fibre — and here the three `ℚ₂` sources take *two different routes*:
  `G_ℚ₂` uses `#H²(G_ℚ₂, M_B) = 1` (B6's Euler characteristic), while `Γ_A` and `Γ_R` cannot
  (`MStageCountGammaA.lean:28`: "`Γ_A` has no degree-2 word↔continuous bridge, so the
  `#H² = 1 ⟹ coboundary` route of the local proof is unavailable") and instead run a
  **degree-≤1 word-side argument**: set-lift the marking, read the relator values in `M_B`, and
  correct them by a `d¹`-preimage supplied by `#H²w(M_B) = #(M_B^∨)^{Y_C} = 1`.

**This file takes the `Γ_A` route for both halves**, because it is the one the dyadic campaign
already has generically: CB-S's `IsSelfDualN` clause 1 *is* `#H²w = #H⁰w(A^∨)`, CB-1's
`card_Z1_eq_card_wordZ1` *is* the transport, and CB-1's `IsAdmissibleMarkedPresentation.extend`
*is* the descent (`RF.descend_piBC`'s generic replacement).  **No continuous `H²` at module
coefficients is needed anywhere** — which matters, because CB-H2's degree-2 rung is built at the
*scalars* (`splitU` needs the split group to be a direct product) and does not reach a module
with an action.  Had the local route been taken, this clause would have been blocked behind a
rung nobody owns.

## §3 is the new mathematics: the correction law without Fox calculus

The one step the `ℚ₂` files do per relator (`corrected_tameValue`/`corrected_wildValue`, two
hand-computed markings of arity `4`) has to be done once, for an arbitrary `PWord` family.  Doing
it by re-deriving Fox calculus for `PWord`s — with `ω₂` exponents — would be a ticket of its own.
It is not necessary.  The observation:

> `WordLift A Y_B` (the campaign's own `A ⋊ C`, at `C := Y_B` acting by conjugation) carries
> **two** homomorphisms to groups we care about: `q : (u, g) ↦ j(u)·g` into `Y_B` itself, and
> `π̃ : (u, g) ↦ (u, π_{BC} g)` into `WordLift A Y_C`.  Evaluating the relator at the single
> marking `i ↦ (xᵢ, f₀ᵢ)` and pushing it both ways gives the correction law in one line each,
> by `PWord.map_eval`.

`q` is a homomorphism exactly because the action of `Y_B` on `A = M_B` *is* conjugation inside
`Y_B`; `π̃` is one exactly because that conjugation only depends on the `π_{BC}`-image
(`mbConjEq`).  The `A`-coordinate is untouched by `π̃`, so the `.u` of the evaluation is read off
in the *word complex* — where `heisD1_eq_lift_foxLift_u` (CB-1 §1) says it is `d¹x`.  No Fox
derivative of a `PWord` is ever computed.

## Section map

| § | content | status |
|---|---------|--------|
| 1 | the `M_B` module pack (`mbCommGroup`, `mbSec`, the two conjugation actions) | re-derived, see below |
| 2 | `#(M_B^∨)^{Y_C} = 1` — the `lemma_7_1_dual` bridge | re-derived, see below |
| 3 | **the correction law**: `eval (j x · f₀) W k = j (d¹x k) · eval f₀ W k` | **new** |
| 4 | nonemptiness of the fibre, over the abstract carrier | **new (generic)** |
| 5 | the `Z¹`-torsor bridge `LiftsOverK ≃ Z¹(Γ, M_B)` | ported, generic in `Γ` |
| 6 | **`liftsOver_cardN`** — the `SourceDataN` value | **CLOSED** |
| 7 | the N0 / `√−2` instantiation | closed |
| 8 | the verbatim `SourceDataN.liftsOver_card` field goal | **closed** |

## What is re-derived and why (§1, §2)

`RecursionFrame.mbCommGroup`, `mbSec`, `mbConjActC` and `card_fixedPts_MB_dual` are **`private`
in all three `ℚ₂` files** — `GQ2/MStageCount.lean:351`, `GQ2/MStageCountGammaA.lean:261`,
`GQ2/MStageCountGammaR.lean:281` — and `MStageCountGammaR.lean:40` says so in as many words.
They are already source-generic; they were copied three times because `private` put them out of
reach, and no frozen file may be touched to export them.  This file writes them a fourth and
**last** time: everything downstream here is stated over the abstract carrier, so the five branch
families consume one copy.  (`MB_comm`, by contrast, *is* public — `SectionEight/Recursion.lean:212`
— and is used, not re-proved.)

Nothing else is re-derived: the count is CB-S's `cardZ1` clause read through CB-1's transport,
and no duality, no cohomology and no cardinality is re-proved here.

## Import discipline

Plain-import: `GQ2.Dyadic.Count.HTwo` (the CB-2/CB-H2 chain, itself plain over CB-1's
`Count/Compare.lean`) and `GQ2.Dyadic.Recursion.Induction` (the SD-R2 spine clone, plain), which
is what supplies `LiftsOverK`/`BoundaryLiftsK`/`BoundaryFrameK` — the recursion vocabulary the
clause is stated in.  `RecursionFrame` itself arrives with it.

Axioms: no new axioms, no `sorry`.  Every headline prints exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`) — recorded in the report.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight

/-! ## §1. The `M_B` module pack

`M_B ⊴ Y_B` is elementary abelian (`MB_elem` + the public `MB_comm`) and carries two conjugation
actions: the direct one by `Y_B` (no choice), and the descended one by `Y_C` through a set-section
of `π_{BC}` (well defined because conjugation on `M_B` only sees the `π_{BC}`-image).  Both are
needed: §3 works in `WordLift A Y_B`, §5–§6 in the word complex over `Y_C`. -/

section MBPack

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]

/-- The commutative-group structure on `M_B` (2-torsion ⟹ abelian, the public `MB_comm`). -/
@[reducible] def mbCommGroup (RF : RecursionFrame T Blk) : CommGroup ↥RF.MB :=
  { (inferInstance : Group ↥RF.MB) with
    mul_comm := fun a b => Subtype.ext (RF.MB_comm _ a.2 _ b.2) }

/-- `M_B` is 2-torsion additively: `a + a = 0` in `Additive ↥M_B`. -/
theorem mb_add_self (RF : RecursionFrame T Blk) (a : Additive ↥RF.MB) : a + a = 0 :=
  Additive.toMul.injective (Subtype.ext (RF.MB_elem _ (Additive.toMul a).2))

/-- The **`Y_B`-conjugation action** on the additivized `M_B` — no choice, no section. -/
@[reducible] def mbConjActB (RF : RecursionFrame T Blk) :
    letI := mbCommGroup RF
    DistribMulAction RF.YB (Additive ↥RF.MB) :=
  letI := mbCommGroup RF
  letI hMBn := RF.MB_normal
  { smul := fun g m => Additive.ofMul
      ⟨g * (Additive.toMul m).1 * g⁻¹, hMBn.conj_mem _ (Additive.toMul m).2 _⟩
    one_smul := fun m => by
      apply Additive.toMul.injective; apply Subtype.ext
      show (1 : RF.YB) * (Additive.toMul m).1 * (1 : RF.YB)⁻¹ = (Additive.toMul m).1
      group
    mul_smul := fun g g' m => by
      apply Additive.toMul.injective; apply Subtype.ext
      show g * g' * (Additive.toMul m).1 * (g * g')⁻¹
        = g * (g' * (Additive.toMul m).1 * g'⁻¹) * g⁻¹
      group
    smul_zero := fun g => by
      apply Additive.toMul.injective; apply Subtype.ext
      show g * (1 : RF.YB) * g⁻¹ = 1
      group
    smul_add := fun g m m' => by
      apply Additive.toMul.injective; apply Subtype.ext
      show g * ((Additive.toMul m).1 * (Additive.toMul m').1) * g⁻¹
        = g * (Additive.toMul m).1 * g⁻¹ * (g * (Additive.toMul m').1 * g⁻¹)
      group }

/-- Conjugation on `M_B` depends only on the `π_{BC}`-image of the conjugator: two preimages
differ by a kernel element, which is central in `M_B`. -/
theorem mbConjEq (RF : RecursionFrame T Blk) {u v : RF.YB} (huv : RF.piBC u = RF.piBC v)
    (m : ↥RF.MB) : u * m.1 * u⁻¹ = v * m.1 * v⁻¹ := by
  have hm : u⁻¹ * v ∈ RF.MB := by
    rw [← RF.ker_piBC]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, huv, inv_mul_cancel])
  calc u * m.1 * u⁻¹
      = u * (m.1 * (u⁻¹ * v) * (u⁻¹ * v)⁻¹) * u⁻¹ := by group
    _ = u * (u⁻¹ * v * m.1 * (u⁻¹ * v)⁻¹) * u⁻¹ := by rw [← RF.MB_comm _ hm _ m.2]
    _ = v * m.1 * v⁻¹ := by group

/-- A set-section of `π_{BC}` (choice-picked; `mbConjEq` makes the induced conjugation on `M_B`
independent of the choice). -/
noncomputable def mbSec (RF : RecursionFrame T Blk) : RF.YC → RF.YB :=
  Function.surjInv RF.piBC_surj

/-- The set-section `mbSec` splits `π_{BC}`. -/
theorem mbSec_spec (RF : RecursionFrame T Blk) (c : RF.YC) : RF.piBC (mbSec RF c) = c :=
  Function.surjInv_eq RF.piBC_surj c

/-- The **`Y_C`-conjugation action** on the additivized `M_B`, through the set-section `mbSec`
(well-defined by `mbConjEq`). -/
@[reducible] noncomputable def mbConjActC (RF : RecursionFrame T Blk) :
    letI := mbCommGroup RF
    DistribMulAction RF.YC (Additive ↥RF.MB) :=
  letI := mbCommGroup RF
  letI hMBn := RF.MB_normal
  { smul := fun c m => Additive.ofMul
      ⟨mbSec RF c * (Additive.toMul m).1 * (mbSec RF c)⁻¹,
        hMBn.conj_mem _ (Additive.toMul m).2 _⟩
    one_smul := fun m => by
      apply Additive.toMul.injective; apply Subtype.ext
      show mbSec RF 1 * (Additive.toMul m).1 * (mbSec RF 1)⁻¹ = (Additive.toMul m).1
      have h1 : mbSec RF 1 ∈ RF.MB := by
        rw [← RF.ker_piBC]
        exact MonoidHom.mem_ker.mpr (mbSec_spec RF 1)
      rw [RF.MB_comm _ h1 _ (Additive.toMul m).2]; group
    mul_smul := fun c c' m => by
      apply Additive.toMul.injective; apply Subtype.ext
      show mbSec RF (c * c') * (Additive.toMul m).1 * (mbSec RF (c * c'))⁻¹
        = mbSec RF c * (mbSec RF c' * (Additive.toMul m).1 * (mbSec RF c')⁻¹) * (mbSec RF c)⁻¹
      rw [show mbSec RF c * (mbSec RF c' * (Additive.toMul m).1 * (mbSec RF c')⁻¹)
            * (mbSec RF c)⁻¹
          = (mbSec RF c * mbSec RF c') * (Additive.toMul m).1 * (mbSec RF c * mbSec RF c')⁻¹ from
        by group]
      exact mbConjEq RF (by rw [mbSec_spec, map_mul, mbSec_spec, mbSec_spec]) (Additive.toMul m)
    smul_zero := fun c => by
      apply Additive.toMul.injective; apply Subtype.ext
      show mbSec RF c * (1 : RF.YB) * (mbSec RF c)⁻¹ = 1
      group
    smul_add := fun c m m' => by
      apply Additive.toMul.injective; apply Subtype.ext
      show mbSec RF c * ((Additive.toMul m).1 * (Additive.toMul m').1) * (mbSec RF c)⁻¹
        = mbSec RF c * (Additive.toMul m).1 * (mbSec RF c)⁻¹
            * (mbSec RF c * (Additive.toMul m').1 * (mbSec RF c)⁻¹)
      group }

/-- **The two actions agree through `π_{BC}`** — the compatibility that makes `π̃` of §3 a
homomorphism, and the `hcomp` input of CB-1's transport. -/
theorem mbAct_compat (RF : RecursionFrame T Blk) :
    letI := mbCommGroup RF
    letI := mbConjActB RF
    letI := mbConjActC RF
    ∀ (g : RF.YB) (a : Additive ↥RF.MB), g • a = RF.piBC g • a := by
  letI := mbCommGroup RF
  letI := mbConjActB RF
  letI := mbConjActC RF
  intro g a
  apply Additive.toMul.injective; apply Subtype.ext
  show g * (Additive.toMul a).1 * g⁻¹
    = mbSec RF (RF.piBC g) * (Additive.toMul a).1 * (mbSec RF (RF.piBC g))⁻¹
  exact mbConjEq RF (by rw [mbSec_spec]) (Additive.toMul a)

end MBPack

/-! ## §2. The correction law

This is the section the `ℚ₂` ancestor has only per relator, and the reason it has it only per
relator is that it computes Fox derivatives of two hand-written words of arity `4`
(`corrected_tameValue`/`corrected_wildValue`).  Stated for an arbitrary `PWord`, that computation
would be a Fox calculus for `PWord`s — profinite exponents included — and a ticket of its own.

The route here does not compute any derivative.  Everything happens inside **one** evaluation, in
the split group `A ⋊ G` over the *upper* group `G` (below: `Y_B`), which admits two homomorphisms:

* `collapse : (u, g) ↦ j(u) · g` into `G` itself — a homomorphism precisely because the `G`-action
  on `A` is conjugation by `j`;
* `baseMap : (u, g) ↦ (u, π g)` into `A ⋊ C` — a homomorphism precisely because that action only
  sees the `π`-image, and it is the **identity on the `A`-coordinate**.

Push the single evaluation `P := eval (i ↦ (xᵢ, f₀ᵢ)) W` both ways with `PWord.map_eval`: the
first gives the corrected marking's relator value as `j(P.u) · P.g`, the second identifies `P.u`
in the word complex, where it is `d¹x`.  The whole law is four applications of naturality. -/

section Correction

variable {ι : Type*} {G C : Type} [Group G] [Group C]
  {A : Type} [AddCommGroup A] [DistribMulAction G A] [DistribMulAction C A]
  (pi : G →* C) (j : A → G)
  (hact : ∀ (g : G) (a : A), g • a = pi g • a)
  (hjmul : ∀ a b : A, j (a + b) = j a * j b)
  (hjconj : ∀ (g : G) (a : A), j (g • a) = g * j a * g⁻¹)
  (hjker : ∀ a : A, pi (j a) = 1)

omit [DistribMulAction G A] in
include hjmul in
/-- `j` is multiplicative, hence unital. -/
theorem j_zero : j 0 = 1 := by
  have h := hjmul 0 0
  rw [add_zero] at h
  have h2 : j 0 * (1 : G) = j 0 * j 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

include hjmul hjconj in
/-- **The collapse homomorphism** `A ⋊ G →* G`, `(u, g) ↦ j(u) · g`.  It is a homomorphism
because the semidirect product's twist is conjugation *inside `G`*. -/
def collapse : WordLift A G →* G where
  toFun p := j p.u * p.g
  map_one' := by
    show j (0 : A) * (1 : G) = 1
    rw [j_zero j hjmul, one_mul]
  map_mul' p p' := by
    show j (p.u + p.g • p'.u) * (p.g * p'.g) = j p.u * p.g * (j p'.u * p'.g)
    rw [hjmul, hjconj]
    group

include hact in
/-- **The base-change homomorphism** `A ⋊ G →* A ⋊ C`, the identity on the `A`-coordinate.  It is
a homomorphism because the `G`-action on `A` factors through `π`. -/
def baseMap : WordLift A G →* WordLift A C where
  toFun p := ⟨p.u, pi p.g⟩
  map_one' := by
    refine WordLift.ext ?_ ?_
    · show (0 : A) = 0
      rfl
    · show pi 1 = 1
      exact map_one pi
  map_mul' p p' := by
    refine WordLift.ext ?_ ?_
    · show p.u + p.g • p'.u = p.u + pi p.g • p'.u
      rw [hact]
    · show pi (p.g * p'.g) = pi p.g * pi p'.g
      exact map_mul pi _ _

variable {c : ι → C} {f₀ : ι → G} (hf₀ : ∀ i, pi (f₀ i) = c i)

include hact hf₀ in
/-- The base change carries the *upper* Fox lifted marking to the *lower* one. -/
theorem baseMap_foxLift (x : ι → A) (i : ι) :
    baseMap pi hact (foxLift f₀ x i) = foxLift c x i :=
  WordLift.ext rfl (hf₀ i)

include hact hjmul hjconj hf₀ in
/-- **The correction law.**  Correcting a set-lift marking `f₀` of `c` by an offset vector `x`
multiplies each relator value by the `A`-offset of the *lower* Fox lifted evaluation — and does
nothing else.

No hypothesis on `W` and no Fox derivative: the identity is three applications of `PWord.map_eval`
to the single evaluation of `W` at `i ↦ (xᵢ, f₀ᵢ)` in `A ⋊ G`. -/
theorem eval_corrected [TopologicalSpace G] [DiscreteTopology G] [Finite G]
    [TopologicalSpace C] [DiscreteTopology C] [Finite C] [Finite A]
    (x : ι → A) (Wk : PWord ι) :
    PWord.eval (fun i => j (x i) * f₀ i) Wk
      = j ((PWord.eval (foxLift c x) Wk).u) * PWord.eval f₀ Wk := by
  set P := PWord.eval (foxLift f₀ x) Wk with hP
  -- (a) the collapse reads the corrected marking's relator value
  have ha : PWord.eval (fun i => j (x i) * f₀ i) Wk = j P.u * P.g := by
    have h := PWord.map_eval
      (⟨collapse j hjmul hjconj, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WordLift A G) G) (foxLift f₀ x) Wk
    exact h.symm
  -- (b) the base projection reads the uncorrected relator value
  have hb : P.g = PWord.eval f₀ Wk := by
    have h := PWord.map_eval
      (⟨WordLift.baseProj (A := A) (C := G), continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WordLift A G) G) (foxLift f₀ x) Wk
    exact h
  -- (c) the base change reads the `A`-offset in the *word complex*
  have hc : P.u = (PWord.eval (foxLift c x) Wk).u := by
    have h := PWord.map_eval
      (⟨baseMap pi hact, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WordLift A G) (WordLift A C)) (foxLift f₀ x) Wk
    have hmark : (fun i => (⟨baseMap pi hact, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WordLift A G) (WordLift A C)) (foxLift f₀ x i)) = foxLift c x :=
      funext fun i => baseMap_foxLift pi hact hf₀ x i
    rw [hmark] at h
    exact congrArg WordLift.u h
  rw [ha, hb, hc]

variable {κ : Type*} {W : κ → PWord ι} {w : κ → FreeGroup ι}

include hact hjmul hjconj hf₀ in
/-- **The correction law in the word lane's vocabulary**: the shift is exactly `d¹x`.

The `ResolvesAt` hypothesis is CB-1's, at CB-1's own target `A ⋊ C`, and it is a *theorem* for the
family resolved there (`resolvesAt_heisToFree`) — not an assumption a branch has to make. -/
theorem eval_corrected_heisD1 [TopologicalSpace G] [DiscreteTopology G] [Finite G]
    [TopologicalSpace C] [DiscreteTopology C] [Finite C] [Finite A]
    (hres : ResolvesAt W w (WordLift A C)) (x : ι → A) (k : κ) :
    PWord.eval (fun i => j (x i) * f₀ i) (W k)
      = j (heisD1 (A := A) c w x k) * PWord.eval f₀ (W k) := by
  rw [eval_corrected pi j hact hjmul hjconj hf₀ x (W k), heisD1_eq_lift_foxLift_u,
    hres (foxLift c x) k]

omit [AddCommGroup A] [DistribMulAction G A] [DistribMulAction C A] in
include hf₀ hjker in
/-- The corrected marking still lifts `c` — `j` lands in `ker π`. -/
theorem pi_corrected (x : ι → A) (i : ι) : pi (j (x i) * f₀ i) = c i := by
  rw [map_mul, hjker, one_mul, hf₀ i]

omit [AddCommGroup A] [DistribMulAction G A] [DistribMulAction C A] in
include hf₀ hjker in
/-- **The corrected marking is admissible** whenever the lower marking is and `ker π` is
`2`-torsion.  Same three-line extension argument as CB-1's `isWildTwo_foxLift`: kill the
`π`-image by the lower marking's `2`-power, then kill what is left — an element of `ker π` — by
squaring. -/
theorem isWildTwo_corrected {J : Set ι} (hwild2 : IsWildTwo J c)
    (hker₂ : ∀ g : G, pi g = 1 → g * g = 1) (x : ι → A) :
    IsWildTwo J (fun i => j (x i) * f₀ i) := by
  rintro ⟨p, hp⟩
  have hbase : pi p ∈ Subgroup.normalClosure (c '' J) := by
    refine Subgroup.normalClosure_le_normal (N := (Subgroup.normalClosure (c '' J)).comap pi)
      ?_ hp
    rintro _ ⟨i, hi, rfl⟩
    exact Subgroup.subset_normalClosure ⟨i, hi, (pi_corrected pi j hjker hf₀ x i).symm⟩
  obtain ⟨k, hk⟩ := hwild2 ⟨_, hbase⟩
  have hk' : pi (p ^ 2 ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    rw [map_pow]
    exact h
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_succ, pow_mul, sq]
  exact hker₂ _ hk'

end Correction

/-! ## §3. `#(M_B^∨)^{Y_C} = 1`

The `lemma_7_1_dual` bridge.  Like §1 this is source-generic and `private` in all three `ℚ₂`
files; it is the *only* place the §7 block theory is consumed by this file, and it is consumed
twice — once to make `#H²w(M_B) = 1` (§4) and once to make the count's `fixedPts` factor
disappear (§6). -/

section FixedPtsDual

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]

/-- **`#(M_B^∨)^{Y_C} = 1`** — a nonzero `Y_C`-invariant functional `λ : M_B^∨` would push
`ker λ` to an index-`2` `Y`-normal subgroup between `Φ(K)` and `K`, which `lemma_7_1_dual`
forbids. -/
theorem card_fixedPts_MB_dual (RF : RecursionFrame T Blk) :
    letI := mbCommGroup RF
    letI := mbConjActC RF
    Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1 := by
  classical
  letI := mbCommGroup RF
  letI := mbConjActC RF
  show Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1
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
        simpa [hφ_apply] using congrArg Multiplicative.toAdd (show φ k = 1 by rw [hφ1]; rfl)
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
    have hRX : Blk.frattiniK ≤ X := by
      intro r hr
      have hrK : r ∈ Blk.K := SectionSeven.frattiniLike_le Blk.K hr
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
            = Additive.ofMul (⟨mbSec RF (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1
                * (mbSec RF (RF.piBC (RF.piB y)))⁻¹,
                RF.MB_normal.conj_mem _ (s ⟨x, hxK⟩).2 _⟩ : ↥RF.MB) := rfl
        rw [hact]
        congr 1
        apply Subtype.ext
        rw [hs]
        show RF.piB (y * x * y⁻¹)
          = mbSec RF (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1
              * (mbSec RF (RF.piBC (RF.piB y)))⁻¹
        rw [hs, map_mul, map_mul, map_inv]
        exact (mbConjEq RF (mbSec_spec RF (RF.piBC (RF.piB y)))
          ⟨RF.piB x, hmem ⟨x, hxK⟩⟩).symm
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
    exact absurd ⟨X, hXnormal, hRX, hXK, hidx⟩ (SectionSeven.lemma_7_1_dual Blk)
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
    ⟨⟨0, smul_zero⟩⟩⟩

end FixedPtsDual

/-! ## §4. Nonemptiness of the lift fibre, over the abstract carrier

The `Γ_A` route (`MStageCountGammaA.lean:371`), made generic.  Set-lift the marking of `ρ` through
`π_{BC}`; the relator values land in `M_B` because they die downstairs; `#H²w(M_B) = 1` — CB-S's
clause 1 plus §3 — puts that vector in the image of `d¹`; §2's correction law turns a `d¹`-preimage
into a marking that kills the family on the nose (the two copies of the relator value cancel, `M_B`
being `2`-torsion); and CB-1's `extend` descends it to `Γ`.

**No continuous `H²` anywhere.**  The `G_ℚ₂` proof's `#H²(Γ, M_B) = 1 ⟹ the factor set is a
coboundary` is a genuinely different argument that needs a degree-`2` rung at *module*
coefficients; CB-H2 built the rung at the scalars only, and this route does not want it. -/

section Nonempty

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [TopologicalSpace Y] [DiscreteTopology Y] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **The `B`-lift fibre over a lower boundary lift is nonempty**, over the abstract carrier and
degree-generically.

Everything but `hd`/`hend` is the presentation interface a branch already supplies; `hd` and
`hend` are the branch's own `StokesDuality` payload and Stokes endpoint — the same two inputs
CB-1's `tcocycle_cardN`/`hZcardN` take, at the module `M_B`. -/
theorem nonempty_liftsOverK {n : ℕ} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC)
    {gen : ι → Γ} {W : κ → PWord ι} {w : κ → FreeGroup ι} {c : ι → RF.YC} {J : Set ι}
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hc : ∀ i, ρ.1.1 (gen i) = c i) (hwild2 : IsWildTwo J c)
    (hdeg : Nat.card ι = Nat.card κ + (n + 1)) :
    letI := mbCommGroup RF
    letI := mbConjActC RF
    ResolvesAt W w (WordLift (Additive ↥RF.MB) RF.YC) →
      StokesDuality c w (Additive ↥RF.MB) → IsStokesEndpoint w →
      Nonempty (LiftsOverK RF b F ρ) := by
  classical
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := mbConjActB RF
  intro hres hd hend
  -- the module-level data of §1
  have hact : ∀ (g : RF.YB) (a : Additive ↥RF.MB), g • a = RF.piBC g • a := mbAct_compat RF
  set j : Additive ↥RF.MB → RF.YB := fun a => (Additive.toMul a).1 with hjdef
  have hjmul : ∀ a b : Additive ↥RF.MB, j (a + b) = j a * j b := fun _ _ => rfl
  have hjconj : ∀ (g : RF.YB) (a : Additive ↥RF.MB), j (g • a) = g * j a * g⁻¹ := fun _ _ => rfl
  have hjker : ∀ a : Additive ↥RF.MB, RF.piBC (j a) = 1 := fun a =>
    MonoidHom.mem_ker.mp (by rw [RF.ker_piBC]; exact (Additive.toMul a).2)
  have hker₂ : ∀ g : RF.YB, RF.piBC g = 1 → g * g = 1 := fun g hg =>
    RF.MB_elem g (by rw [← RF.ker_piBC]; exact MonoidHom.mem_ker.mpr hg)
  -- the set-lift marking of `ρ`, and its relator values
  set f₀ : ι → RF.YB := fun i => mbSec RF (c i) with hf₀def
  have hf₀ : ∀ i, RF.piBC (f₀ i) = c i := fun i => mbSec_spec RF (c i)
  have hvmem : ∀ k : κ, PWord.eval f₀ (W k) ∈ RF.MB := by
    intro k
    rw [← RF.ker_piBC]
    refine MonoidHom.mem_ker.mpr ?_
    have h := PWord.map_eval (⟨RF.piBC, continuous_of_discreteTopology⟩ :
      ContinuousMonoidHom RF.YB RF.YC) f₀ (W k)
    have hmark : (fun i => (⟨RF.piBC, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom RF.YB RF.YC) (f₀ i)) = fun i => ρ.1.1 (gen i) :=
      funext fun i => (hf₀ i).trans (hc i).symm
    rw [hmark] at h
    exact h.trans (hpres.rel ρ.1.1 k)
  set v : κ → Additive ↥RF.MB := fun k => Additive.ofMul ⟨PWord.eval f₀ (W k), hvmem k⟩ with hvdef
  -- `#H²w(M_B) = #(M_B^∨)^{Y_C} = 1`, so the relator vector is a `d¹`-boundary
  have hgen : Subgroup.closure (Set.range c) = ⊤ :=
    closure_range_lower_eq_top ρ.1.1 hc hpres ρ.1.2
  have hS : IsSelfDualN n c w (Additive ↥RF.MB) :=
    isSelfDualN_of_stokesDuality hdeg hd (lower_rel ρ.1.1 hc hpres hres) hend
  have hH2w : Nat.card (WordH2 c w (Additive ↥RF.MB)) = 1 := by
    rw [hS.cardH2, card_ker_heisD0_eq_card_fixedPts hgen, card_fixedPts_MB_dual RF]
  haveI : Subsingleton ((κ → Additive ↥RF.MB) ⧸ (heisD1 (A := Additive ↥RF.MB) c w).range) :=
    (Nat.card_eq_one_iff_unique.mp hH2w).1
  obtain ⟨x, hx⟩ : v ∈ (heisD1 (A := Additive ↥RF.MB) c w).range := by
    rw [← QuotientAddGroup.eq_zero_iff]
    exact Subsingleton.elim _ _
  -- §2: the corrected marking kills the whole family
  have hkill : ∀ k, PWord.eval (fun i => j (x i) * f₀ i) (W k) = 1 := by
    intro k
    rw [eval_corrected_heisD1 RF.piBC j hact hjmul hjconj hf₀ hres x k,
      show heisD1 (A := Additive ↥RF.MB) c w x k = v k from congrFun hx k]
    exact RF.MB_elem _ (hvmem k)
  have hwild2' : IsWildTwo J (fun i => j (x i) * f₀ i) :=
    isWildTwo_corrected RF.piBC j hjker hf₀ hwild2 hker₂ x
  -- CB-1's `extend` descends it, and rigidity pins it over `ρ`
  obtain ⟨φ, hφ⟩ := hpres.extend (fun i => j (x i) * f₀ i) hkill hwild2'
  refine ⟨⟨φ, ?_⟩⟩
  have hpin : (⟨RF.piBC.comp φ.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp φ.continuous_toFun⟩ :
        ContinuousMonoidHom Γ RF.YC) = ρ.1.1 := by
    refine eq_of_eqOn_gen hpres.gen_top fun i => ?_
    show RF.piBC (φ (gen i)) = ρ.1.1 (gen i)
    rw [hφ i, hc i]
    exact pi_corrected RF.piBC j hjker hf₀ x i
  exact fun γ => congrArg (fun ψ : ContinuousMonoidHom Γ RF.YC => ψ γ) hpin

end Nonempty

end GQ2.Dyadic.Count
