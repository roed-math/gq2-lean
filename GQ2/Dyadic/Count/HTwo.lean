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
noncomputable def pEps (Wk : PWord ι) (x : ι → ZMod 2) : ZMod 2 :=
  Multiplicative.toAdd (PWord.eval (fun i => Multiplicative.ofAdd (x i)) Wk)

/-- The exponent vector of a whole family — the shape `d¹` has. -/
noncomputable def wordEps (W : ρ → PWord ι) (x : ι → ZMod 2) : ρ → ZMod 2 :=
  fun k => pEps (W k) x

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
local instance fiberProdTopologicalSpace {M : Type} [Group M] {c₁ c₂ : WordCoh.TwoCocycle M} :
    TopologicalSpace (WordCoh.FiberProd c₁ c₂) := ⊥

local instance fiberProdDiscreteTopology {M : Type} [Group M] {c₁ c₂ : WordCoh.TwoCocycle M} :
    DiscreteTopology (WordCoh.FiberProd c₁ c₂) := ⟨rfl⟩

/-- Every hom between finite discrete groups is continuous — the wrapper `PWord.map_eval` needs. -/
def discreteCMH (f : L →* L') : ContinuousMonoidHom L L' := ⟨f, continuous_of_discreteTopology⟩

omit [Finite L] [DiscreteTopology L'] [Finite L'] in
@[simp] theorem discreteCMH_apply (f : L →* L') (x : L) : discreteCMH f x = f x := rfl

/-- **The relator obstruction of an intrinsic relator**: the fibre coordinate of the word evaluated
at the zero-fibre lift of the marking into the central extension.  `WordCoh.relZ` with `NatWord.ev`
replaced by the profinite denotation. -/
noncomputable def pRelZ (Wk : PWord ι) (μ : ι → L) (c : WordCoh.TwoCocycle L) : ZMod 2 :=
  (PWord.eval (WordCoh.lift μ c) Wk).fib

/-- The base of the lifted relator value is the relator value downstairs. -/
theorem pRelZ_base (Wk : PWord ι) (μ : ι → L) (c : WordCoh.TwoCocycle L) :
    (PWord.eval (WordCoh.lift μ c) Wk).base = PWord.eval μ Wk := by
  have h := PWord.map_eval (discreteCMH (WordCoh.CentExt.proj c)) (WordCoh.lift μ c) Wk
  simpa only [discreteCMH_apply, WordCoh.CentExt.proj_apply, WordCoh.lift_base] using h

/-- If the relation holds at the marking, the lifted relator is the central `pRelZ`. -/
theorem pWord_eval_lift_eq_incl (Wk : PWord ι) (μ : ι → L) (c : WordCoh.TwoCocycle L)
    (hrel : PWord.eval μ Wk = 1) :
    PWord.eval (WordCoh.lift μ c) Wk = WordCoh.CentExt.incl c (pRelZ Wk μ c) :=
  (WordCoh.CentExt.base_eq_one_iff _).mp (by rw [pRelZ_base, hrel])

omit [TopologicalSpace L] [DiscreteTopology L] [TopologicalSpace L'] [DiscreteTopology L'] in
/-- **Level-independence.**  Port of `WordCoh.relZ_comap`. -/
theorem pRelZ_comap (Wk : PWord ι) (μ : ι → L') (c : WordCoh.TwoCocycle L) (φ : L' →* L) :
    pRelZ Wk (fun i => φ (μ i)) c = pRelZ Wk μ (c.comap φ) := by
  have h := PWord.map_eval (discreteCMH (WordCoh.projExt c φ)) (WordCoh.lift μ (c.comap φ)) Wk
  have hlift : (fun i => discreteCMH (WordCoh.projExt c φ) (WordCoh.lift μ (c.comap φ) i))
      = WordCoh.lift (fun i => φ (μ i)) c := rfl
  rw [hlift] at h
  show (PWord.eval (WordCoh.lift (fun i => φ (μ i)) c) Wk).fib
    = (PWord.eval (WordCoh.lift μ (c.comap φ)) Wk).fib
  rw [← h]
  exact WordCoh.projExt_fib c φ _

omit [TopologicalSpace L] [DiscreteTopology L] in
/-- **Additivity in the cocycle.**  Port of `WordCoh.relZ_add`, through the fibre product. -/
theorem pRelZ_add (Wk : PWord ι) (μ : ι → L) (c₁ c₂ : WordCoh.TwoCocycle L) :
    pRelZ Wk μ (c₁ + c₂) = pRelZ Wk μ c₁ + pRelZ Wk μ c₂ := by
  have h1 := PWord.map_eval (discreteCMH WordCoh.FiberProd.pr1) (WordCoh.liftFP μ c₁ c₂) Wk
  have h2 := PWord.map_eval (discreteCMH WordCoh.FiberProd.pr2) (WordCoh.liftFP μ c₁ c₂) Wk
  have hs := PWord.map_eval (discreteCMH WordCoh.FiberProd.prSum) (WordCoh.liftFP μ c₁ c₂) Wk
  have e1 : (fun i => discreteCMH WordCoh.FiberProd.pr1 (WordCoh.liftFP μ c₁ c₂ i))
      = WordCoh.lift μ c₁ := rfl
  have e2 : (fun i => discreteCMH WordCoh.FiberProd.pr2 (WordCoh.liftFP μ c₁ c₂ i))
      = WordCoh.lift μ c₂ := rfl
  have es : (fun i => discreteCMH WordCoh.FiberProd.prSum (WordCoh.liftFP μ c₁ c₂ i))
      = WordCoh.lift μ (c₁ + c₂) := by
    funext i; exact WordCoh.CentExt.ext rfl (add_zero (0 : ZMod 2))
  rw [e1] at h1
  rw [e2] at h2
  rw [es] at hs
  show (PWord.eval (WordCoh.lift μ (c₁ + c₂)) Wk).fib
    = (PWord.eval (WordCoh.lift μ c₁) Wk).fib + (PWord.eval (WordCoh.lift μ c₂) Wk).fib
  rw [← hs, ← h1, ← h2]
  rfl

/-- **The coboundary law, with the Frattini hypothesis deleted.**

MC-OB's `relZ_coboundary` assumes `W.IsFrattini` and concludes `relZ = lam (relator)`.  Delete the
hypothesis and the induced `𝔽₂`-marking `i ↦ lam (μ i)` no longer kills the word: what survives is
its exponent-sum `pEps`, and the law acquires that term.

**This is the whole difference between the single-relator and multi-relator theories.**  With
`IsFrattini` the correction vanishes and the obstruction lands in `𝔽₂` on the nose; without it the
obstruction is well defined only modulo the correction — and §2 says the correction is exactly the
word complex's `d¹`, so "modulo the correction" is `WordH²`. -/
theorem pRelZ_coboundary (Wk : PWord ι) (μ : ι → L) (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    pRelZ Wk μ (WordCoh.coboundaryCocycle lam hlam1)
      = lam (PWord.eval μ Wk) + pEps Wk (fun i => lam (μ i)) := by
  set cb := WordCoh.coboundaryCocycle lam hlam1 with hcb
  set θ : WordCoh.CentExt cb →* Multiplicative (ZMod 2) := (WordCoh.fibHom0 (L := L)).comp (WordCoh.Psi lam hlam1) with hθ
  have h := PWord.map_eval (discreteCMH θ) (WordCoh.lift μ cb) Wk
  have hgen : (fun i => discreteCMH θ (WordCoh.lift μ cb i))
      = fun i => Multiplicative.ofAdd (lam (μ i)) := by
    funext i
    show Multiplicative.ofAdd ((WordCoh.Psi lam hlam1 (WordCoh.lift μ cb i)).fib) = _
    rw [WordCoh.Psi_fib, WordCoh.lift_fib, WordCoh.lift_base, zero_add]
  rw [hgen] at h
  have hlhs : discreteCMH θ (PWord.eval (WordCoh.lift μ cb) Wk)
      = Multiplicative.ofAdd (pRelZ Wk μ cb + lam (PWord.eval μ Wk)) := by
    show Multiplicative.ofAdd ((WordCoh.Psi lam hlam1 (PWord.eval (WordCoh.lift μ cb) Wk)).fib) = _
    rw [WordCoh.Psi_fib, pRelZ_base]
    rfl
  have hsum : pRelZ Wk μ cb + lam (PWord.eval μ Wk) = pEps Wk (fun i => lam (μ i)) :=
    Multiplicative.ofAdd.injective (hlhs.symm.trans h)
  have key : ∀ a b c : ZMod 2, a + b = c → a = b + c := by decide
  exact key _ _ _ hsum

end PRelZ

/-! ## §4. The level-independent family obstruction

MC-OB's `LevelFactor.obs` / `obs_congr` / `obsFun` / `obsFun_add` layer, for the intrinsic relator
family.  `LevelFactor` itself — the statement that a continuous `2`-cochain is inflated from a
finite level — is about the cochain and not about the word, so it is **reused verbatim**, and with
it `exists_twoCocycle_factor` and `nonempty_levelFactor_normalize`.  Only the obstruction attached
to a factorization has to be rebuilt. -/

section Obstruction

open GQ2.Dyadic.WordCoh

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]

/-- The quotient by an open subgroup of a profinite group is discrete.  MC-OB establishes this by a
`haveI` at each use; making it an instance is what lets `pRelZ` be applied at a level without
threading it. -/
local instance quotientDiscreteTopology (V : OpenNormalSubgroup Γ) :
    DiscreteTopology (Γ ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- The canonical projection between two levels, one refining the other.  (MC-OB's `levelProj` is
`private`.) -/
noncomputable def lvlProj {V V' : OpenNormalSubgroup Γ} (h : V'.toSubgroup ≤ V.toSubgroup) :
    (Γ ⧸ V'.toSubgroup) →* (Γ ⧸ V.toSubgroup) :=
  QuotientGroup.map V'.toSubgroup V.toSubgroup (MonoidHom.id _)
    (by rw [Subgroup.comap_id]; exact h)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] in
theorem lvlProj_comp {V V' : OpenNormalSubgroup Γ} (h : V'.toSubgroup ≤ V.toSubgroup) :
    (lvlProj h).comp (QuotientGroup.mk' V'.toSubgroup) = QuotientGroup.mk' V.toSubgroup := by
  ext g
  rw [lvlProj, MonoidHom.comp_apply, QuotientGroup.map_mk']
  rfl

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] in
theorem lvlProj_mk {V V' : OpenNormalSubgroup Γ} (h : V'.toSubgroup ≤ V.toSubgroup) (g : Γ) :
    lvlProj h (QuotientGroup.mk' V'.toSubgroup g) = QuotientGroup.mk' V.toSubgroup g := by
  rw [← MonoidHom.comp_apply, lvlProj_comp]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- The (unique, CB-2 §1) action of the carrier on the scalars is trivial.  Pinned at `Γ` because
`smul_zmod2`'s group is implicit, and MC-OB's `htriv` slot would otherwise leave it a metavariable
during instance search. -/
theorem smulTrivZmod2 (x : Γ) (m : ZMod 2) : x • m = m := smul_zmod2 x m

/-- **The obstruction vector of a factorization**: the intrinsic relator family, read in the
central extension of the finite level at the projected marking. -/
noncomputable def pObsAt (W : ρ → PWord ι) (gen : ι → Γ) {κ : Γ × Γ → ZMod 2}
    (F : WordCoh.LevelFactor κ) : ρ → ZMod 2 :=
  fun k => pRelZ (W k) (fun i => QuotientGroup.mk' F.V.toSubgroup (gen i)) F.c

omit [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)] in
/-- The obstruction may be computed at any finer level, through the pulled-back cocycle. -/
theorem pObsAt_eq_comap (W : ρ → PWord ι) (gen : ι → Γ) {κ : Γ × Γ → ZMod 2} (F : WordCoh.LevelFactor κ)
    (V' : OpenNormalSubgroup Γ) (proj : (Γ ⧸ V'.toSubgroup) →* (Γ ⧸ F.V.toSubgroup))
    (hproj : proj.comp (QuotientGroup.mk' V'.toSubgroup) = QuotientGroup.mk' F.V.toSubgroup) :
    pObsAt W gen F
      = fun k => pRelZ (W k) (fun i => QuotientGroup.mk' V'.toSubgroup (gen i)) (F.c.comap proj) := by
  funext k
  rw [← pRelZ_comap (W k) (fun i => QuotientGroup.mk' V'.toSubgroup (gen i)) F.c proj]
  show pRelZ (W k) (fun i => QuotientGroup.mk' F.V.toSubgroup (gen i)) F.c
    = pRelZ (W k) (fun i => proj (QuotientGroup.mk' V'.toSubgroup (gen i))) F.c
  congr 1
  funext i
  rw [← MonoidHom.comp_apply, hproj]

omit [DistribMulAction Γ (ZMod 2)] in
/-- **Well-definedness**: the obstruction depends only on the cochain, not on the factorization.
Port of `LevelFactor.obs_congr`, compared at the meet of the two levels. -/
theorem pObsAt_congr (W : ρ → PWord ι) (gen : ι → Γ) {κ : Γ × Γ → ZMod 2}
    (F₁ F₂ : WordCoh.LevelFactor κ) : pObsAt W gen F₁ = pObsAt W gen F₂ := by
  set V' : OpenNormalSubgroup Γ := F₁.V ⊓ F₂.V with hV
  have h1 : V'.toSubgroup ≤ F₁.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have h2 : V'.toSubgroup ≤ F₂.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_right hx
  rw [pObsAt_eq_comap W gen F₁ V' (lvlProj h1) (lvlProj_comp h1),
    pObsAt_eq_comap W gen F₂ V' (lvlProj h2) (lvlProj_comp h2)]
  have hcc : F₁.c.comap (lvlProj h1) = F₂.c.comap (lvlProj h2) := by
    apply WordCoh.TwoCocycle.ext'
    funext a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V'.toSubgroup a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective V'.toSubgroup b
    rw [WordCoh.TwoCocycle.comap_κ, WordCoh.TwoCocycle.comap_κ, lvlProj_mk, lvlProj_mk, lvlProj_mk, lvlProj_mk,
      ← F₁.hfact g h, ← F₂.hfact g h]
  rw [hcc]

/-- **The family obstruction of a continuous `2`-cocycle**, computed at any factorization of its
normalization. -/
noncomputable def pObsFun (W : ρ → PWord ι) (gen : ι → Γ) (φ : Z2 Γ (ZMod 2)) : ρ → ZMod 2 :=
  pObsAt W gen (WordCoh.nonempty_levelFactor_normalize smulTrivZmod2 φ).some

theorem pObsFun_eq (W : ρ → PWord ι) (gen : ι → Γ) (φ : Z2 Γ (ZMod 2))
    (F : WordCoh.LevelFactor (WordCoh.normalizeCochain φ.1)) : pObsFun W gen φ = pObsAt W gen F :=
  pObsAt_congr W gen _ F

/-- **Additivity.**  Port of `obsFun_add`: the sum of two factorizations is a factorization of the
sum at the meet of the levels, and `pRelZ_add` reads off the value there. -/
theorem pObsFun_add (W : ρ → PWord ι) (gen : ι → Γ) (φ ψ : Z2 Γ (ZMod 2)) :
    pObsFun W gen (φ + ψ) = pObsFun W gen φ + pObsFun W gen ψ := by
  set Fφ := (WordCoh.nonempty_levelFactor_normalize smulTrivZmod2 φ).some with hFφ
  set Fψ := (WordCoh.nonempty_levelFactor_normalize smulTrivZmod2 ψ).some with hFψ
  set V' : OpenNormalSubgroup Γ := Fφ.V ⊓ Fψ.V with hV
  have h1 : V'.toSubgroup ≤ Fφ.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have h2 : V'.toSubgroup ≤ Fψ.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_right hx
  have hnorm : WordCoh.normalizeCochain (φ.1 + ψ.1) = WordCoh.normalizeCochain φ.1 + WordCoh.normalizeCochain ψ.1 := by
    funext p; simp only [WordCoh.normalizeCochain, Pi.add_apply, Pi.sub_apply]; abel
  have hFsum : pObsFun W gen (φ + ψ)
      = fun k => pRelZ (W k) (fun i => QuotientGroup.mk' V'.toSubgroup (gen i))
          (Fφ.c.comap (lvlProj h1) + Fψ.c.comap (lvlProj h2)) := by
    refine pObsFun_eq W gen (φ + ψ)
      ⟨V', Fφ.c.comap (lvlProj h1) + Fψ.c.comap (lvlProj h2), ?_⟩
    intro x y
    rw [WordCoh.TwoCocycle.add_κ, WordCoh.TwoCocycle.comap_κ, WordCoh.TwoCocycle.comap_κ, lvlProj_mk, lvlProj_mk,
      lvlProj_mk, lvlProj_mk, ← Fφ.hfact x y, ← Fψ.hfact x y]
    show WordCoh.normalizeCochain (φ.1 + ψ.1) (x, y)
      = WordCoh.normalizeCochain φ.1 (x, y) + WordCoh.normalizeCochain ψ.1 (x, y)
    rw [hnorm, Pi.add_apply]
  rw [pObsFun_eq W gen φ Fφ, pObsFun_eq W gen ψ Fψ, hFsum,
    pObsAt_eq_comap W gen Fφ V' (lvlProj h1) (lvlProj_comp h1),
    pObsAt_eq_comap W gen Fψ V' (lvlProj h2) (lvlProj_comp h2)]
  funext k
  exact pRelZ_add (W k) _ _ _

/-- **The family obstruction homomorphism** `Z²_cont(Γ, 𝔽₂) →+ (ρ → 𝔽₂)`.  The degree-`2` analogue
of CB-1's `toZ1w`, before descent. -/
noncomputable def pObsFam (W : ρ → PWord ι) (gen : ι → Γ) : Z2 Γ (ZMod 2) →+ (ρ → ZMod 2) :=
  AddMonoidHom.mk' (pObsFun W gen) (pObsFun_add W gen)

end Obstruction


end GQ2.Dyadic.Count
