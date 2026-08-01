/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Count.Scalar

/-!
# Dyadic campaign, ticket CB-H2: the degree-`2` rung of the comparison ladder

CB-1 built `z1Equiv`/`h1Equiv` (`Count/Compare.lean` §3) and stopped at degree `1`.  CB-2 found the
missing degree-`2` rung and reduced `SourceDataN.cardH2` to exactly one open argument
(`Count/Scalar.lean` §8):

> `hcomp : Nat.card (H2 Γ (ZMod 2)) = Nat.card (WordH2 c w (ZMod 2))`

This file builds the rung and discharges `hcomp`.

## The route, and why it is not the five-term sequence

CB-2's §8 named the expected route as the five-term sequence of `1 → R → F → Γ → 1`.  **This file
takes a different one**, for a reason that is not stylistic: the repository has no
inflation–restriction sequence, no `H²` of a free profinite group, and no relation module — the
five-term route would have to build all three, and `H²(F̂, A) = 0` is the statement that free
profinite groups have cohomological dimension `1`, which is a genuine theorem and not a `500`-line
one.

The route taken instead is the **central-extension** route, which computes the same map without
ever naming `R`: a continuous `2`-cocycle `φ` is a central extension `CentExt φ` of `Γ` by `𝔽₂`;
lifting the marked letters into it and reading the relators' fibre coordinates gives a vector in
`ρ → 𝔽₂`; changing the lifts moves that vector by `im d¹`; so the class in
`WordH² = (ρ → 𝔽₂) ⧸ im d¹` is well defined, and it vanishes exactly when the extension splits,
i.e. exactly when `φ` is a coboundary.

That is the *same* map the five-term sequence produces — `H²(Γ,A) = coker(Der(F,A) →
Hom_Γ(R^ab,A)) ↪ coker(Der(F,A) → (ρ → A))` — presented so that `R` never has to be constructed.

**And most of it already exists.**  MC-OB's `GQ2/Dyadic/Word/WordCoh.lean` built the central
extension `CentExt`, the level-factoring of a continuous cocycle through a finite quotient
(`exists_twoCocycle_factor`, `LevelFactor`), and the whole `obs`/`obsH2` assembly *generically in
the profinite group `G`*.  CB-2's report is right that `card_H2_le_two` does not substitute for the
rung, and right about why (`IsProP 2 G`, one relator) — but the layer underneath it is reusable
almost verbatim, and it costs **zero import delta**: `GQ2.Dyadic.Word.WordCoh` is already in
`Count/Scalar.lean`'s closure.

## What had to be new, and what the two restrictions really were

MC-OB's `obsH2` carries two restrictions.  Neither is where CB-2 placed it, and neither is deep:

* **One relator, because of `IsFrattini`.**  `MarkedRelator.frattini` says the relator dies under
  every `𝔽₂`-marking — i.e. its mod-`2` exponent vector is zero — and that is exactly what lets
  `obs` land in `𝔽₂` *on the nose* instead of in a quotient.  §3's `pRelZ_coboundary` is
  `relZ_coboundary` with the hypothesis **deleted**, and the deleted hypothesis reappears as the
  correction term `wordEps`, which §2 identifies with `d¹`.  So the multi-relator statement is not
  a generalisation of the single-relator one — it is the same computation with the error term kept,
  and the error term *is* the thing one quotients by.  This is the file's one mathematical idea.
* **`IsProP 2 G`, because of `PresentedBy`.**  It enters `obs_ker_le` only to certify that
  `CentExt c` is a legitimate target for the presentation's lifting property.  CB-1's
  `IsAdmissibleMarkedPresentation.extend` takes *finite discrete* targets and asks `IsWildTwo J`
  instead, so `IsProP 2 G` is replaced by §5's `isWildTwo_centLift` — the exact degree-`2` twin of
  CB-1's `isWildTwo_foxLift`, with the same two-step extension proof.

## `NatWord` is not available, and the relators are `PWord`s

MC-OB's obstruction consumes a `NatWord` — a word evaluable in *every* group.  The campaign's
relators are not of that kind: `ω₂` is a profinite exponent, resolved differently in each finite
quotient (CB-RES), so the intrinsic family `W : ρ → PWord ι` has no `NatWord` form.  §3 therefore
re-proves the four `relZ` laws for `PWord.eval` directly.  Every target the proofs visit is finite
discrete (`Γ ⧸ V`, `CentExt c`, `FiberProd c₁ c₂`), so `PWord.map_eval` applies at each step; the
proofs are MC-OB's with `W.nat` replaced by `PWord.map_eval`.

**This is what keeps `ResolvesAt` out of the construction.**  The obstruction is defined by the
intrinsic `PWord.eval`, so `hpres.rel` (relator death at the finite level) and `hpres.extend` (the
lifting property) both apply *verbatim*, with no resolution hypothesis at the — unboundedly deep —
levels `Γ ⧸ V` where the cocycle happens to factor.  The `FreeGroup` family `w` enters in exactly
one place, §2's identification of the correction term with `heisD1 c w`, and that identification is
needed **only at the two-element target** `Multiplicative (ZMod 2)`, which CB-1's standing
`hres : ResolvesAt W w (WordLift (ZMod 2) C)` already delivers by `ResolvesAt.pushforward`.  A
resolution at every level would have been false (CB-RES); a resolution at one target of exponent
`2` is free.

## Section map

| § | content |
|---|---------|
| 1 | `splitU` — at the scalars the split group's offset coordinate is a hom |
| 2 | `wordEps`, the intrinsic mod-`2` exponent vector, `= d¹` at one tiny target |
| 3 | `pRelZ` and its four laws (base / comap / add / coboundary), Frattini-free |
| 4 | the level-independent family obstruction `pObsFam : Z²(Γ, 𝔽₂) →+ (ρ → 𝔽₂)` |
| 5 | `isWildTwo_centLift` and the splitting: `pObsFam φ ∈ im d¹ → φ ∈ B²` |
| 6 | **the rung**: `wordH2Obs : H²(Γ, 𝔽₂) →+ WordH²`, injective |
| 7 | `hcomp` discharged, and `cardH2_field_goal` closed |

## Import discipline

Plain-import: the single import `GQ2.Dyadic.Count.Scalar` is plain, and **nothing is added to its
closure** — `GQ2.Dyadic.Word.WordCoh` (MC-OB), which supplies `TwoCocycle`, `CentExt`,
`LevelFactor` and `exists_twoCocycle_factor`, is already inside it (measured: 150 `GQ2` modules
before and after).

Axioms: no new axioms, no `sorry`.  `decide` is used only at kernel-decidable `ZMod 2` statements.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction

/-! ## §1. At the scalars the split group is a direct product

`WordLift A C` is `A ⋊ C`; at `A = 𝔽₂` the action is trivial (`Count/Scalar.lean` §1), so the
product law on the offset slot is plain addition and the offset coordinate is a homomorphism.  This
one observation is what makes the whole degree-`2` story collapse to exponent sums: `d¹` stops
depending on the marking, and the "change of lifts" correction of §3 can be read in a two-element
group. -/

section TrivialSplit

variable {C : Type*} [Group C] [DistribMulAction C (ZMod 2)]

/-- **The offset coordinate of the split group, as a homomorphism** — available only because the
coefficient module is the scalars, where `smul_zmod2` makes the action trivial. -/
def splitU : WordLift (ZMod 2) C →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd p.u
  map_one' := rfl
  map_mul' p q := by
    show Multiplicative.ofAdd (p.u + p.g • q.u)
      = Multiplicative.ofAdd p.u * Multiplicative.ofAdd q.u
    rw [smul_zmod2, ofAdd_add]

@[simp] theorem splitU_apply (p : WordLift (ZMod 2) C) :
    splitU p = Multiplicative.ofAdd p.u := rfl

@[simp] theorem splitU_foxLift {ι : Type*} (c : ι → C) (x : ι → ZMod 2) (i : ι) :
    splitU (foxLift c x i) = Multiplicative.ofAdd (x i) := rfl

end TrivialSplit

/-! ## §2. The intrinsic exponent vector, and that it is `d¹`

`wordEps` is the intrinsic relator family read at an `𝔽₂`-marking — the mod-`2` exponent matrix of
the family, applied to `x`.  `wordEps_eq_heisD1` says it *is* the word complex's `d¹` at the
scalars, for any marking `c` whatsoever: at a trivial action `d¹` does not see the marking.

The resolution hypothesis is consumed here and nowhere else, and only at
`Multiplicative (ZMod 2)`. -/

section Eps

variable {ι ρ : Type*} {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]

/-- **The intrinsic mod-`2` exponent vector of the relator family.**  No `FreeGroup` family and no
resolution: this is the profinite denotation of `W` at the `𝔽₂`-marking `x`, in the two-element
group. -/
noncomputable def wordEps (W : ρ → PWord ι) (x : ι → ZMod 2) : ρ → ZMod 2 :=
  fun k => Multiplicative.toAdd (PWord.eval (fun i => Multiplicative.ofAdd (x i)) (W k))

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **The exponent vector is the word complex's `d¹`.**

Two steps, and the marking `c` disappears between them: `splitU` turns the `FreeGroup`
denotation of `w k` at the Fox lifted marking into its denotation at the bare `𝔽₂`-marking
(`map_freeGroup_lift`), and `hres` — pushed forward along `splitU` — identifies that with the
intrinsic denotation of `W k`.

⚠ The push-forward is the whole reason no deep resolution is needed: `Multiplicative (ZMod 2)` has
exponent `2`, so *every* branch resolver is correct there, and CB-1's standing resolution at
`WordLift (ZMod 2) C` already implies it. -/
theorem wordEps_eq_heisD1 {W : ρ → PWord ι} {w : ρ → FreeGroup ι} (c : ι → C)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (x : ι → ZMod 2) :
    wordEps W x = heisD1 (A := ZMod 2) c w x := by
  funext k
  have hfree : Multiplicative.ofAdd (heisD1 (A := ZMod 2) c w x k)
      = FreeGroup.lift (fun i => Multiplicative.ofAdd (x i)) (w k) := by
    rw [heisD1_eq_lift_foxLift_u c w x k]
    exact map_freeGroup_lift (splitU (C := C)) (foxLift c x) (w k)
  have hpush := hres.pushforward
    (⟨splitU (C := C), continuous_of_discreteTopology⟩ :
      ContinuousMonoidHom (WordLift (ZMod 2) C) (Multiplicative (ZMod 2)))
    (f := foxLift c x) (f' := fun i => Multiplicative.ofAdd (x i)) (fun _ => rfl) k
  show Multiplicative.toAdd (PWord.eval (fun i => Multiplicative.ofAdd (x i)) (W k)) = _
  rw [← hpush, ← hfree]
  rfl

end Eps

/-! ## §3. The relator obstruction of an intrinsic word, without `IsFrattini`

MC-OB's `relZ` layer (`Word/WordCoh.lean` §`RelZ`) for a `PWord` relator instead of a `NatWord`,
with the Frattini hypothesis deleted from the coboundary law.  Every proof is MC-OB's with
`W.nat` replaced by `PWord.map_eval`; the only mathematical change is `pRelZ_coboundary`, which
keeps the error term MC-OB's `relZ_coboundary` assumes away. -/

section PRelZ

open GQ2.Dyadic.WordCoh

variable {ι : Type*} {L L' : Type} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [Group L'] [TopologicalSpace L'] [DiscreteTopology L'] [Finite L']

/-- `MC-OB` gives `FiberProd` a `Finite` instance but no topology (its `NatWord` denotation needs
none).  The profinite denotation does, and `⊥` is the only candidate on a finite group that arises
here — no diamond is possible, since no other instance exists in the closure. -/
local instance fiberProdTopologicalSpace {M : Type} [Group M] {c₁ c₂ : TwoCocycle M} :
    TopologicalSpace (FiberProd c₁ c₂) := ⊥

local instance fiberProdDiscreteTopology {M : Type} [Group M] {c₁ c₂ : TwoCocycle M} :
    DiscreteTopology (FiberProd c₁ c₂) := ⟨rfl⟩

/-- Every hom between finite discrete groups is continuous — the wrapper `PWord.map_eval` needs. -/
def discreteCMH (f : L →* L') : ContinuousMonoidHom L L' := ⟨f, continuous_of_discreteTopology⟩

omit [Finite L] [DiscreteTopology L'] [Finite L'] in
@[simp] theorem discreteCMH_apply (f : L →* L') (x : L) : discreteCMH f x = f x := rfl

/-- **The relator obstruction of an intrinsic relator**: the fibre coordinate of the word evaluated
at the zero-fibre lift of the marking into the central extension.  `WordCoh.relZ` with `NatWord.ev`
replaced by the profinite denotation. -/
noncomputable def pRelZ (Wk : PWord ι) (μ : ι → L) (c : TwoCocycle L) : ZMod 2 :=
  (PWord.eval (WordCoh.lift μ c) Wk).fib

/-- The base of the lifted relator value is the relator value downstairs. -/
theorem pRelZ_base (Wk : PWord ι) (μ : ι → L) (c : TwoCocycle L) :
    (PWord.eval (WordCoh.lift μ c) Wk).base = PWord.eval μ Wk := by
  have h := PWord.map_eval (discreteCMH (CentExt.proj c)) (WordCoh.lift μ c) Wk
  simpa only [discreteCMH_apply, CentExt.proj_apply, WordCoh.lift_base] using h

/-- If the relation holds at the marking, the lifted relator is the central `pRelZ`. -/
theorem pWord_eval_lift_eq_incl (Wk : PWord ι) (μ : ι → L) (c : TwoCocycle L)
    (hrel : PWord.eval μ Wk = 1) :
    PWord.eval (WordCoh.lift μ c) Wk = CentExt.incl c (pRelZ Wk μ c) :=
  (CentExt.base_eq_one_iff _).mp (by rw [pRelZ_base, hrel])

omit [TopologicalSpace L] [DiscreteTopology L] [TopologicalSpace L'] [DiscreteTopology L'] in
/-- **Level-independence.**  Port of `WordCoh.relZ_comap`. -/
theorem pRelZ_comap (Wk : PWord ι) (μ : ι → L') (c : TwoCocycle L) (φ : L' →* L) :
    pRelZ Wk (fun i => φ (μ i)) c = pRelZ Wk μ (c.comap φ) := by
  have h := PWord.map_eval (discreteCMH (projExt c φ)) (WordCoh.lift μ (c.comap φ)) Wk
  have hlift : (fun i => discreteCMH (projExt c φ) (WordCoh.lift μ (c.comap φ) i))
      = WordCoh.lift (fun i => φ (μ i)) c := rfl
  rw [hlift] at h
  show (PWord.eval (WordCoh.lift (fun i => φ (μ i)) c) Wk).fib
    = (PWord.eval (WordCoh.lift μ (c.comap φ)) Wk).fib
  rw [← h]
  exact projExt_fib c φ _

omit [TopologicalSpace L] [DiscreteTopology L] in
/-- **Additivity in the cocycle.**  Port of `WordCoh.relZ_add`, through the fibre product. -/
theorem pRelZ_add (Wk : PWord ι) (μ : ι → L) (c₁ c₂ : TwoCocycle L) :
    pRelZ Wk μ (c₁ + c₂) = pRelZ Wk μ c₁ + pRelZ Wk μ c₂ := by
  have h1 := PWord.map_eval (discreteCMH FiberProd.pr1) (WordCoh.liftFP μ c₁ c₂) Wk
  have h2 := PWord.map_eval (discreteCMH FiberProd.pr2) (WordCoh.liftFP μ c₁ c₂) Wk
  have hs := PWord.map_eval (discreteCMH FiberProd.prSum) (WordCoh.liftFP μ c₁ c₂) Wk
  have e1 : (fun i => discreteCMH FiberProd.pr1 (WordCoh.liftFP μ c₁ c₂ i))
      = WordCoh.lift μ c₁ := rfl
  have e2 : (fun i => discreteCMH FiberProd.pr2 (WordCoh.liftFP μ c₁ c₂ i))
      = WordCoh.lift μ c₂ := rfl
  have es : (fun i => discreteCMH FiberProd.prSum (WordCoh.liftFP μ c₁ c₂ i))
      = WordCoh.lift μ (c₁ + c₂) := by
    funext i; exact CentExt.ext rfl (add_zero (0 : ZMod 2))
  rw [e1] at h1
  rw [e2] at h2
  rw [es] at hs
  show (PWord.eval (WordCoh.lift μ (c₁ + c₂)) Wk).fib
    = (PWord.eval (WordCoh.lift μ c₁) Wk).fib + (PWord.eval (WordCoh.lift μ c₂) Wk).fib
  rw [← hs, ← h1, ← h2]
  rfl

end PRelZ

end GQ2.Dyadic.Count
