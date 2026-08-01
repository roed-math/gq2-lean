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

/-- The quotient by an open subgroup of a profinite group is discrete.  MC-OB establishes this by a
`haveI` at each use; making it an instance is what lets `pRelZ` be applied at a level without
threading it.  Declared at namespace level so that §4–§7 all see it. -/
local instance quotientDiscreteTopology {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

section Obstruction

open GQ2.Dyadic.WordCoh

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]

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

omit [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)] in
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



/-! ## §5. The shift law, the admissible central lift, and the splitting

The three ingredients of injectivity.  All three are degree-`2` twins of things CB-1 did at degree
`1`: the shift law is `mem_ker_heisD1_iff` ("a word cocycle *is* a relator-killing marking of the
split group") read in the *twisted* group instead of the split one; `isWildTwo_centLift` is
`isWildTwo_foxLift` with the offset slot replaced by the central fibre; and the splitting is
`toZ1w_surjective`'s use of clause (iii), at the same marking. -/

section Splitting

variable {ι ρ : Type*}

/-- **An element of the central fibre squares to `1`** — the `2`-torsion input of the admissibility
argument, and the twisted-group analogue of CB-1's `sq_eq_one_of_g_eq_one`. -/
theorem centExt_sq_eq_one {L : Type} [Group L] {c : WordCoh.TwoCocycle L}
    {p : WordCoh.CentExt c} (hp : p.base = 1) : p ^ 2 = 1 := by
  rw [pow_two, (WordCoh.CentExt.base_eq_one_iff p).mp hp]
  refine WordCoh.CentExt.ext (one_mul 1) ?_
  show p.fib + p.fib + c.κ 1 1 = 0
  rw [c.κ_one_left, add_zero]
  exact (by decide : ∀ z : ZMod 2, z + z = 0) p.fib

/-- **The central lift of an admissible marking is admissible.**

The degree-`2` twin of CB-1's `isWildTwo_foxLift`, and — this is the point — the *replacement for
MC-OB's `IsProP 2 G`*.  MC-OB certifies `CentExt c` as a legitimate target for its `PresentedBy`
by proving the whole group pro-`2` (`isProP_CentExt`), which forces `G` itself to be pro-`2`.
CB-1's `extend` asks far less: only that the **wild part** of the marking generate a `2`-group.
That survives the central extension by the same two-step argument as at degree `1` — kill the base
coordinate by the lower marking's `2`-power, then kill the leftover fibre element by squaring. -/
theorem isWildTwo_centLift {L : Type} [Group L] {J : Set ι} {μ : ι → L}
    (hwild : IsWildTwo J μ) (c : WordCoh.TwoCocycle L) (a : ι → ZMod 2) :
    IsWildTwo J (fun i => WordCoh.CentExt.incl c (a i) * WordCoh.lift μ c i) := by
  rintro ⟨p, hp⟩
  have hle : Subgroup.normalClosure
      ((fun i => WordCoh.CentExt.incl c (a i) * WordCoh.lift μ c i) '' J)
      ≤ (Subgroup.normalClosure (μ '' J)).comap (WordCoh.CentExt.proj c) :=
    Subgroup.normalClosure_le_normal <| by
      rintro _ ⟨i, hi, rfl⟩
      show WordCoh.CentExt.proj c _ ∈ Subgroup.normalClosure (μ '' J)
      rw [map_mul]
      show (1 : L) * μ i ∈ Subgroup.normalClosure (μ '' J)
      rw [one_mul]
      exact Subgroup.subset_normalClosure ⟨i, hi, rfl⟩
  obtain ⟨k, hk⟩ := hwild ⟨_, hle hp⟩
  have hk' : (p ^ 2 ^ k).base = 1 := by
    have h := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    rw [show (p ^ 2 ^ k).base = WordCoh.CentExt.proj c (p ^ 2 ^ k) from rfl, map_pow]
    exact h
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_succ, pow_mul]
  exact centExt_sq_eq_one hk'

/-- The **central shift** `(p, z) ↦ incl z · p`.  A homomorphism precisely because the fibre is
central, which is why the direct product — and not a semidirect one — is the right domain. -/
def shiftMul {L : Type} [Group L] (c : WordCoh.TwoCocycle L) :
    WordCoh.CentExt c × Multiplicative (ZMod 2) →* WordCoh.CentExt c where
  toFun q := WordCoh.CentExt.incl c (Multiplicative.toAdd q.2) * q.1
  map_one' := by
    show WordCoh.CentExt.incl c 0 * 1 = 1
    rw [WordCoh.CentExt.incl_zero, one_mul]
  map_mul' q r := by
    refine WordCoh.CentExt.ext ?_ ?_
    · simp only [Prod.fst_mul, WordCoh.CentExt.mul_base, WordCoh.CentExt.incl_base, one_mul]
    · simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, WordCoh.CentExt.mul_fib,
        WordCoh.CentExt.mul_base, WordCoh.CentExt.incl_base, WordCoh.CentExt.incl_fib, one_mul,
        c.κ_one_left]
      abel

/-- **The shift law.**  Moving every lift by the central `a i` moves the relator value by the
central `pEps a` — and §2 says `pEps` is `d¹`.  So the obstruction vector is well defined exactly
modulo `im d¹`, which is the definition of `WordH²`.

The proof is three applications of `PWord.map_eval` at the finite discrete direct product
`CentExt c × Multiplicative 𝔽₂`: the two projections read off the unshifted value and the exponent
sum, and `shiftMul` puts them back together. -/
theorem pWord_eval_shift {L : Type} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
    (Wk : PWord ι) (μ : ι → L) (c : WordCoh.TwoCocycle L) (a : ι → ZMod 2) :
    PWord.eval (fun i => WordCoh.CentExt.incl c (a i) * WordCoh.lift μ c i) Wk
      = WordCoh.CentExt.incl c (pEps Wk a) * PWord.eval (WordCoh.lift μ c) Wk := by
  set n : ι → WordCoh.CentExt c × Multiplicative (ZMod 2) :=
    fun i => (WordCoh.lift μ c i, Multiplicative.ofAdd (a i)) with hn
  have h1 := PWord.map_eval
    (discreteCMH (MonoidHom.fst (WordCoh.CentExt c) (Multiplicative (ZMod 2)))) n Wk
  have h2 := PWord.map_eval
    (discreteCMH (MonoidHom.snd (WordCoh.CentExt c) (Multiplicative (ZMod 2)))) n Wk
  have hs := PWord.map_eval (discreteCMH (shiftMul c)) n Wk
  have e1 : (fun i => discreteCMH
      (MonoidHom.fst (WordCoh.CentExt c) (Multiplicative (ZMod 2))) (n i))
      = WordCoh.lift μ c := rfl
  have e2 : (fun i => discreteCMH
      (MonoidHom.snd (WordCoh.CentExt c) (Multiplicative (ZMod 2))) (n i))
      = fun i => Multiplicative.ofAdd (a i) := rfl
  have es : (fun i => discreteCMH (shiftMul c) (n i))
      = fun i => WordCoh.CentExt.incl c (a i) * WordCoh.lift μ c i := rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [es] at hs
  rw [← hs]
  show WordCoh.CentExt.incl c (Multiplicative.toAdd (PWord.eval n Wk).2) * (PWord.eval n Wk).1 = _
  rw [show (PWord.eval n Wk).1 = PWord.eval (WordCoh.lift μ c) Wk from h1,
    show (PWord.eval n Wk).2 = PWord.eval (fun i => Multiplicative.ofAdd (a i)) Wk from h2]
  rfl

end Splitting

/-! ## §6. The rung

`pObsFam` composed with the quotient by `im d¹`, descended through `B²`.  The two halves of
injectivity are §5b (coboundaries hit `im d¹`) and §5c (nothing else does). -/

section Assembly

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **A continuous coboundary has its obstruction in `im d¹`.**

MC-OB's `obs_B2_eq_zero` proves the obstruction is *zero*, and needs `IsFrattini` to do it.  Delete
the hypothesis and §3's `pRelZ_coboundary` leaves the exponent-sum term, which §2 identifies with
`d¹` — so the conclusion weakens from `= 0` to `∈ im d¹`, and that is exactly the weakening
`WordH²` absorbs.  The relator term still vanishes, by clause (ii) of the presentation read at the
factoring level. -/
theorem pObsFam_B2_mem_range (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) {x : Z2 Γ (ZMod 2)}
    (hx : x.1 ∈ B2 Γ (ZMod 2)) :
    pObsFam W gen x ∈ (heisD1 (A := ZMod 2) c w).range := by
  rw [B2, AddSubgroup.mem_map] at hx
  obtain ⟨ψ, hψc, hψeq⟩ := hx
  have hψcont : Continuous ψ := mem_C1_iff.mp hψc
  have hx1 : x.1 = dOne Γ (ZMod 2) ψ := hψeq.symm
  obtain ⟨V, lam, hlamfact⟩ := WordCoh.exists_oneCochain_factor (ψ - fun _ => ψ 1)
    (hψcont.sub continuous_const)
  have hlam1 : lam 1 = 0 := by
    have h := hlamfact 1
    rw [show QuotientGroup.mk' V.toSubgroup (1 : Γ) = 1 from map_one _] at h
    rw [← h]
    simp
  have hfact : ∀ p q : Γ, WordCoh.normalizeCochain x.1 (p, q)
      = (WordCoh.coboundaryCocycle lam hlam1).κ (QuotientGroup.mk' V.toSubgroup p)
          (QuotientGroup.mk' V.toSubgroup q) := by
    intro p q
    show WordCoh.normalizeCochain x.1 (p, q)
      = lam (QuotientGroup.mk' V.toSubgroup p) + lam (QuotientGroup.mk' V.toSubgroup q)
        + lam (QuotientGroup.mk' V.toSubgroup p * QuotientGroup.mk' V.toSubgroup q)
    rw [← map_mul (QuotientGroup.mk' V.toSubgroup) p q, ← hlamfact p, ← hlamfact q,
      ← hlamfact (p * q), hx1]
    simp only [WordCoh.normalizeCochain, Pi.sub_apply, dOne, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, smulTrivZmod2, mul_one, CharTwo.sub_eq_add]
    abel
  refine ⟨fun i => lam (QuotientGroup.mk' V.toSubgroup (gen i)), ?_⟩
  rw [← wordEps_eq_heisD1 c hres]
  funext k
  show pEps (W k) _ = pObsFun W gen x k
  rw [pObsFun_eq W gen x ⟨V, WordCoh.coboundaryCocycle lam hlam1, hfact⟩]
  show _ = pRelZ (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i))
    (WordCoh.coboundaryCocycle lam hlam1)
  have hrelk : PWord.eval (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) (W k) = 1 :=
    hpres.rel (GQ2.quotientMk V.toSubgroup) k
  rw [pRelZ_coboundary, hrelk, hlam1, zero_add]

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **The splitting: nothing but a coboundary has its obstruction in `im d¹`.**

The degree-`2` twin of CB-1's `toZ1w_surjective`, and the **only** consumer of clause (iii).  If
the obstruction is `d¹a`, then shifting the lifts by `a` kills every relator in the central
extension (the shift law plus `z + z = 0`), so clause (iii) — whose admissibility side condition is
§5's `isWildTwo_centLift` — produces a continuous section of the extension, and MC-OB's
`cocycle_mem_B2` reads the cocycle off it as a coboundary.

⚠ `hwildLevel` is the one hypothesis this file adds beyond CB-1's, and it is CB-1's own `hwild2` at
*every* finite level rather than at the single marking target `C`: the wild letters generate a
pro-`2` normal subgroup of `Γ`.  For `GQ2.Dyadic.GammaR` that is part of the definition
(`AdmissibleR` §3).  It is what replaces MC-OB's `IsProP 2 G`, which asked the *whole* group to be
pro-`2` and is false here. -/
theorem mem_B2_of_pObsFam_mem_range (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup Γ,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) {φ : Z2 Γ (ZMod 2)}
    (hφ : pObsFam W gen φ ∈ (heisD1 (A := ZMod 2) c w).range) : φ.1 ∈ B2 Γ (ZMod 2) := by
  obtain ⟨a, ha⟩ := hφ
  set F := (WordCoh.nonempty_levelFactor_normalize smulTrivZmod2 φ).some with hF
  have hobs : ∀ k, pRelZ (W k) (fun i => QuotientGroup.mk' F.V.toSubgroup (gen i)) F.c
      = pEps (W k) a := by
    intro k
    have h := congrFun (ha.trans (pObsFun_eq W gen φ F)) k
    rw [← wordEps_eq_heisD1 c hres a] at h
    exact h.symm
  set m : ι → WordCoh.CentExt F.c := fun i => WordCoh.CentExt.incl F.c (a i)
    * WordCoh.lift (fun j => QuotientGroup.mk' F.V.toSubgroup (gen j)) F.c i with hm
  have hrel : ∀ k, PWord.eval m (W k) = 1 := by
    intro k
    have hrelk : PWord.eval (fun j => QuotientGroup.mk' F.V.toSubgroup (gen j)) (W k) = 1 :=
      hpres.rel (GQ2.quotientMk F.V.toSubgroup) k
    rw [hm, pWord_eval_shift, pWord_eval_lift_eq_incl (W k) _ F.c hrelk, hobs k, ← pow_two]
    exact centExt_sq_eq_one rfl
  obtain ⟨sect, hsect⟩ := hpres.extend m hrel (isWildTwo_centLift (hwildLevel F.V) F.c a)
  have hbase : ∀ g : Γ, (sect g).base = QuotientGroup.mk' F.V.toSubgroup g := by
    have hcomp : (⟨WordCoh.CentExt.proj F.c, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WordCoh.CentExt F.c) (Γ ⧸ F.V.toSubgroup)).comp sect
          = GQ2.quotientMk F.V.toSubgroup := by
      refine eq_of_eqOn_gen hpres.gen_top fun i => ?_
      show WordCoh.CentExt.proj F.c (sect (gen i)) = _
      rw [hsect i, hm]
      show (WordCoh.CentExt.incl F.c (a i) * WordCoh.lift _ F.c i).base = _
      rw [WordCoh.CentExt.mul_base, WordCoh.CentExt.incl_base, one_mul]
      rfl
    exact fun g => DFunLike.congr_fun hcomp g
  have hnB2 : WordCoh.normalizeCochain φ.1 ∈ B2 Γ (ZMod 2) := by
    have heq : WordCoh.normalizeCochain φ.1
        = fun p : Γ × Γ => F.c.κ (sect p.1).base (sect p.2).base := by
      funext p
      rw [hbase, hbase]
      exact F.hfact p.1 p.2
    rw [heq]
    exact WordCoh.cocycle_mem_B2 smulTrivZmod2 sect
  have hconst : φ.1 = WordCoh.normalizeCochain φ.1 + fun _ => φ.1 (1, 1) := by
    funext p
    simp only [WordCoh.normalizeCochain, Pi.sub_apply, Pi.add_apply]
    abel
  rw [hconst]
  exact AddSubgroup.add_mem _ hnB2 (WordCoh.const2_mem_B2 smulTrivZmod2 (φ.1 (1, 1)))

section Rung

variable [Fintype ι] [Fintype ρ] [DecidableEq ι]

/-- **The rung, before descent**: the obstruction vector read modulo `im d¹`. -/
noncomputable def wordH2Obs (W : ρ → PWord ι) (gen : ι → Γ) (c : ι → C) (w : ρ → FreeGroup ι) :
    Z2 Γ (ZMod 2) →+ WordH2 c w (ZMod 2) :=
  (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range).comp (pObsFam W gen)

/-- **THE RUNG.**  The degree-`2` analogue of CB-1's `h1Equiv`: for a presented profinite `Γ`,
continuous `2`-cohomology with scalar coefficients embeds in the word complex's `H²`.

⚠ Unlike degree `1` this is an **injection and not an isomorphism**, and that is not a defect of
the proof: the cokernel is the module of identities among the relators, which is nonzero for a
presentation that is not aspherical.  §7 shows the injection is all the count clause needs. -/
noncomputable def h2Word (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) :
    H2 Γ (ZMod 2) →+ WordH2 c w (ZMod 2) :=
  QuotientAddGroup.lift _ (wordH2Obs W gen c w) fun _ hx =>
    (QuotientAddGroup.eq_zero_iff _).mpr
      (pObsFam_B2_mem_range hpres hres c (AddSubgroup.mem_addSubgroupOf.mp hx))

omit [TopologicalSpace C] [DiscreteTopology C] [Fintype ι] [Fintype ρ] [DecidableEq ι] in
@[simp] theorem h2Word_mk (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) (φ : Z2 Γ (ZMod 2)) :
    h2Word hpres hres c (H2mk Γ (ZMod 2) φ) = wordH2Obs W gen c w φ := rfl

omit [TopologicalSpace C] [DiscreteTopology C] [Fintype ι] [Fintype ρ] [DecidableEq ι] in
/-- **The rung is injective.** -/
theorem h2Word_injective (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup Γ,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) :
    Function.Injective (h2Word (w := w) hpres hres c) := by
  rw [injective_iff_map_eq_zero]
  intro y
  induction y using QuotientAddGroup.induction_on with | H φ =>
  intro hy
  refine (QuotientAddGroup.eq_zero_iff φ).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  exact mem_B2_of_pObsFam_mem_range hpres hwildLevel hres c
    ((QuotientAddGroup.eq_zero_iff _).mp hy)

omit [TopologicalSpace C] [DiscreteTopology C] [Fintype ι] [DecidableEq ι] in
/-- `H²(Γ, 𝔽₂)` is finite, being embedded in the finite `WordH²`. -/
theorem finite_H2_of_presented (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup Γ,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) : Finite (H2 Γ (ZMod 2)) :=
  Finite.of_injective _ (h2Word_injective (w := w) hpres hwildLevel hres c)

omit [TopologicalSpace C] [DiscreteTopology C] [Fintype ι] [DecidableEq ι] in
/-- **The cardinality form of the rung** — the inequality half of CB-2's `hcomp`. -/
theorem card_H2_le_card_wordH2 (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup Γ,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C) :
    Nat.card (H2 Γ (ZMod 2)) ≤ Nat.card (WordH2 c w (ZMod 2)) :=
  Nat.card_le_card_of_injective _ (h2Word_injective (w := w) hpres hwildLevel hres c)

end Rung

end Assembly

/-! ## §7. `hcomp` discharged, and the `SourceDataN` field goal closed

The rung gives `≤`; `#WordH²(𝔽₂) = 2` (CB-2 §4) and nontriviality give `=`.

**On the nontriviality input.**  It is not an artefact of taking the injection instead of an
isomorphism — no comparison theorem can avoid it, because `H²(Γ, 𝔽₂) = 0` is *consistent* with
every other hypothesis in sight (a free profinite `Γ` satisfies all of them).  What pins it down is
a source-side witness, and the campaign already has to produce exactly one: `SourceDataN.lem86`'s
`hvar`, a nonzero variation class (CB-2 §9, `lem86N`).  `nontrivial_H2_of_ne_zero` turns that
witness into this hypothesis, so **`cardH2` and `lem86` share their one non-generic input** — which
sharpens CB-2's scheduling note: `lem86` is not merely downstream of `cardH2`, the two consume the
same witness. -/

section FieldGoal

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace C]
  [DiscreteTopology C] [Finite C] [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)] in
/-- **A nonzero class makes `H²` nontrivial** — the bridge from `lem86`'s `hvar` to `cardH2`'s
missing half. -/
theorem nontrivial_H2_of_ne_zero {φ : Z2 Γ (ZMod 2)} (h : H2mk Γ (ZMod 2) φ ≠ 0) :
    Nontrivial (H2 Γ (ZMod 2)) :=
  ⟨⟨H2mk Γ (ZMod 2) φ, 0, h⟩⟩

variable [Fintype ι] [Fintype ρ] [DecidableEq ι]

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **CB-2's `hcomp`, discharged.**

`Count/Scalar.lean` §8 left `cardH2` one argument short and named it: the degree-`2` comparison
`#H²(Γ, 𝔽₂) = #WordH²(𝔽₂)`.  This is that argument. -/
theorem cardH2_comp (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup Γ,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C)
    (hnt : Nontrivial (H2 Γ (ZMod 2))) (hd : StokesDuality c w (ZMod 2))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card (H2 Γ (ZMod 2)) = Nat.card (WordH2 c w (ZMod 2)) := by
  haveI := finite_H2_of_presented (w := w) hpres hwildLevel hres c
  have hw2 : Nat.card (WordH2 c w (ZMod 2)) = 2 := card_wordH2_zmod2 hd hr hend
  have hle : Nat.card (H2 Γ (ZMod 2)) ≤ 2 :=
    le_of_le_of_eq (card_H2_le_card_wordH2 hpres hwildLevel hres c) hw2
  exact (cardH2_of_le_two hle hnt).trans hw2.symm

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **`SourceDataN.cardH2`, over the abstract carrier, with no open argument.**  CB-2's `cardH2N`
with its `hcomp` supplied. -/
theorem cardH2N_closed (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup Γ,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (c : ι → C)
    (hnt : Nontrivial (H2 Γ (ZMod 2))) (hd : StokesDuality c w (ZMod 2))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card (H2 Γ (ZMod 2)) = 2 :=
  cardH2N (cardH2_comp hpres hwildLevel hres c hnt hd hr hend) hd hr hend

end FieldGoal

/-- **`SourceDataN.cardH2`, verbatim** (`GQ2/Dyadic/SourceDataN.lean:184`), including the record's
own `letI := smulZmod2` — **closed**, with no `hcomp` argument.

This is CB-2's `cardH2_field_goal` with its single open argument discharged; the recipe for CB-4 is
this theorem, and the inputs beyond CB-2's are exactly two: `hwildLevel` (the wild part of the
carrier is pro-`2` — part of `GammaR`'s definition) and `hnt` (the nonzero class that `lem86`
already needs). -/
theorem cardH2_field_goal_closed {Gam : ProfiniteGrp} {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    [DecidableEq ι] {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    {gen : ι → (Gam : Type)} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}
    (smulZmod2 : DistribMulAction (Gam : Type) (ZMod 2))
    (hpres : IsAdmissibleMarkedPresentation (Gam : Type) gen W J)
    (hwildLevel : ∀ V : OpenNormalSubgroup (Gam : Type),
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hres : ResolvesAt W w (WordLift (ZMod 2) C))
    (hnt : letI := smulZmod2; Nontrivial (H2 (Gam : Type) (ZMod 2)))
    (hd : StokesDuality c w (ZMod 2)) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) :
    letI := smulZmod2
    Nat.card (H2 Gam (ZMod 2)) = 2 := by
  letI := smulZmod2
  exact cardH2_field_goal smulZmod2
    (cardH2_comp hpres hwildLevel hres c hnt hd hr hend) hd hr hend

end GQ2.Dyadic.Count
