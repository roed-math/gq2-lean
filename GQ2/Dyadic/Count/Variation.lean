/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Count.Frozen
import GQ2.Dyadic.Count.HTwo

/-!
# Dyadic campaign, ticket CB-VAR: the nonzero variation class

CB-H2 built the degree-`2` rung `h2Word : H²(Γ, 𝔽₂) ↪ WordH²` and discharged `hcomp`, leaving
`SourceDataN.cardH2` two honest inputs (`Count/HTwo.lean` §7):

* `hwildLevel` — the pushed marking is admissible at *every* finite level;
* `Nontrivial (H2 Γ (ZMod 2))` — which CB-H2 showed **no comparison theorem can avoid**, because
  `H² = 0` is consistent with every other hypothesis in sight (a free profinite `Γ` satisfies
  them all).

This file discharges the first outright and reduces the second to the *same* witness that
`SourceDataN.lem86` needs — CB-H2's sharpening, that `cardH2` and `lem86` share their one
non-generic input rather than merely being ordered.

## The route, and the one thing that made it cheap

The `ℚ₂` ancestors produce `hvar` in five steps
(`GQ2/HalfTorsorGamma{A,R}.lean`, `GQ2/Ledger Gamma{A,R}.lean`, `GQ2/MixedBObs.lean`):

1. from `NoDescent`, a dual `1`-cocycle `φf` carrying the radical edge, nonzero in `H¹`;
2. the comparison `h1Equiv` moves `[φf]` into the word complex;
3. `prop_5_15`'s **perfect pairing** produces a primal class pairing nontrivially against it;
4. the primal class pulls back to `w : Z¹(Γ, T)`, whose graph is a `T`-cocycle `u`;
5. the **ledger identity** `obs(varCoc u) = mixedB` transfers the nonzero pairing value onto the
   variation class.

Every one of the five is `Γ`-generic *as mathematics*, and the dyadic campaign already owns three
of them generically: (2) is CB-1's `h1Equiv`, (3) is CB-S's `IsSelfDualN.pairing` — the third
clause of the degree-generic `IsSelfDual` package, out of one `StokesDuality` payload — and (4) is
`z1Equiv.symm` composed with CB-1's `tcocycleEquivZ1`.  What was missing was (1) and (5); §5 and
§6 build them, at `pObsFam` in place of `obs` and `heisEta1` in place of `mixedB`.

## The level question answers itself

The ledger identity is read in the **Heisenberg lift** `H(A) ⋊ C`, so the word lane's family must
resolve the intrinsic relators *there*, not only at the split group `A ⋊ C` where CB-1 needs it.
That looks like a new obligation and is not one, for a reason CB-FR's §8.2 already established:
the resolution is taken at the *target's own exponent*, and

> `A ⋊ C` and `A^∨ ⋊ C` are both **subgroups** of `H(A) ⋊ C` (§2)

so a single level `N = exp(H(A) ⋊ C)` kills all three targets at once, and it is automatically
even (the Heisenberg centre contributes an element of order `2`).  Hence §2's
`heisLevel_ne_zero_and_even` and `orderOf_dvd_heisExponent`, and hence the five branch rows'
matched `(hres, hend)` pairs at that one level with **no hypothesis about the target at all** —
`Count/Frozen.lean` §10's theorems are already generic in the level, which is exactly what makes
this ticket's instantiation three lines a row rather than a re-derivation.

## Section map

| § | content |
|---|---------|
| 1 | `hwildLevel` for `Γ_R`, from `AdmissibleR` §3 — CB-H2's first owed input, discharged |
| 2 | the Heisenberg level: two subgroup embeddings, one exponent, evenness for free |
| 3 | the Heisenberg `2`-cocycle `kappaHeisN` and `CentExt ≅ H(A) ⋊ C` |
| 4 | `pObsFam` of an **inflated** cocycle (the degree-generic `MixedBObs.obs_inflation`) |
| 5 | the **ledger identity**: the traced obstruction of `varCoc` is `heisEta1` |
| 6 | the shifted-edge dual cocycle `phiVar`, `Γ`-generic (the `ℚ₂` `exists_phiF`) |
| 7 | **the nonzero variation class**, `Γ`-generic |
| 8 | the three clauses it unblocks: `cardH2`, `lem86`, `stageR136` |
| 9 | the five frozen branch families |

## Import discipline

Plain-import.  Two imports, both plain and both already in the campaign's `Count` closure:
`Count.Frozen` (the five frozen families and their level-generic matched pairs) and `Count.HTwo`
(the rung).  `Frozen` already imports `Presentation`, which imports `Compare`, which carries
`CentralObstruction`/`RadicalEdge.GammaA`, so the radical-cover vocabulary (`RadicalCoverData`,
`TCocycle`, `varCoc`, `edge`, `edgeQ`) arrives with no new module.

Axioms: no new axioms, no `sorry`.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction
open GQ2.SectionEight.RadicalEdgeGammaA

/-! ## §1. `hwildLevel` for `Γ_R`

CB-H2's `cardH2_field_goal_closed` asks that the marking pushed to *every* finite level be
admissible.  At `Γ_R` this is not an extra assumption at all: the pro-`2` condition on the wild
part is literally one of the two clauses of `GQ2.Dyadic.IsAdmissibleU`, and GR1 already carried it
to every open normal subgroup (`AdmissibleR` §4, `isPGroup_two_wildNormalClosure`).

The only content here is the set identity `f '' J = (mk' V) '' (range wild-gen)`, which is
`image_wildAlphabet` twice.  Compare `Count/Presentation.lean` §5, which does the same at a
*surjection onto a finite group*; the level form is the special case `ρ = mk' V`, but stating it
that way would force `Γ ⧸ V` to carry a `Finite` instance it does not need. -/

section WildLevel

variable {n q : ℕ} {R : PWord (Generator n)}

/-- **CB-H2's `hwildLevel`, discharged at `Γ_R`.**  For every open normal `V ≤ Γ_R` the marking
`i ↦ [gen i] ∈ Γ_R ⧸ V` is admissible.

This is exactly CB-1's `hwild2` read at every level, and it is part of `Γ_R`'s *definition*: the
admissible limit's second clause is the pro-`2` condition on the wild part, transported to `V` by
GR1's `isPGroup_two_wildNormalClosure`. -/
theorem hwildLevel_gammaR (V : OpenNormalSubgroup ((GammaR n q R) : Type)) :
    IsWildTwo (wildAlphabet n)
      (fun i => QuotientGroup.mk' V.toSubgroup (gammaGen n q R i)) := by
  show IsPGroup 2 (Subgroup.normalClosure
    ((fun i => QuotientGroup.mk' V.toSubgroup (gammaGen n q R i)) '' wildAlphabet n))
  have hset : (fun i => QuotientGroup.mk' V.toSubgroup (gammaGen n q R i)) '' wildAlphabet n
      = (QuotientGroup.mk' V.toSubgroup) ''
          (Set.range fun i : Fin (n + 1) => gammaGen n q R (Generator.wild i)) := by
    rw [image_wildAlphabet, ← Set.range_comp]
    rfl
  rw [hset]
  exact isPGroup_two_wildNormalClosure V

end WildLevel

/-! ## §2. One level for all three targets

The comparison `z1Equiv` is read at the split group `A ⋊ C`; its dual twin at `A^∨ ⋊ C`; §5's
ledger identity at the Heisenberg lift `H(A) ⋊ C`.  Three targets, and the word lane's family has
to resolve the intrinsic relators at each of them — a resolution being *target-local* and, at a
badly chosen target, false (CB-RES).

They are the same question, because the first two groups are **subgroups of the third**: the
zero-dual, zero-centre slice and the zero-primal, zero-centre slice are both closed under the
Heisenberg product (the central defect `λ(g • a')` needs a primal *and* a dual coordinate to be
nonzero, and each slice kills one of them).  So a single level `N = exp(H(A) ⋊ C)` kills all
three, and `Count/Frozen.lean` §10 — whose rows are already generic in the level — supplies each
branch's matched `(hres, hend)` pair there.

Evenness, which the Stokes endpoint needs (`odd_omega2Exp`), is free for a different reason than
at CB-FR's split target: there it was the `2`-torsion of `Additive ↥D.T`; here it is the
Heisenberg **centre**, which is a copy of `ZMod 2` in every `H(A) ⋊ C` whatsoever. -/

section HeisLevel

open GQ2.Dyadic.WordCoh

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The primal slice** `A ⋊ C ↪ H(A) ⋊ C`, `(a, g) ↦ (a, 0, 0, g)`.  A homomorphism because
the Heisenberg central defect `λ(g • a')` vanishes when the left dual coordinate does. -/
noncomputable def heisPrim : WordLift A C →* HeisLift A C where
  toFun p := ⟨p.u, 0, 0, p.g⟩
  map_one' := rfl
  map_mul' p q := by
    refine HeisLift.ext rfl ?_ ?_ rfl
    · show (0 : ElemDual A) = 0 + p.g • (0 : ElemDual A)
      rw [smul_zero, add_zero]
    · show (0 : ZMod 2) = 0 + 0 + (0 : ElemDual A) (p.g • q.u)
      rw [ElemDual.zero_apply, add_zero, add_zero]

/-- **The dual slice** `A^∨ ⋊ C ↪ H(A) ⋊ C`, `(λ, g) ↦ (0, λ, 0, g)`.  A homomorphism because the
central defect vanishes when the right primal coordinate does. -/
noncomputable def heisDual : WordLift (ElemDual A) C →* HeisLift A C where
  toFun p := ⟨0, p.u, 0, p.g⟩
  map_one' := rfl
  map_mul' p q := by
    refine HeisLift.ext ?_ rfl ?_ rfl
    · show (0 : A) = 0 + p.g • (0 : A)
      rw [smul_zero, add_zero]
    · show (0 : ZMod 2) = 0 + 0 + p.u (p.g • (0 : A))
      rw [smul_zero, map_zero, add_zero, add_zero]

theorem heisPrim_injective : Function.Injective (heisPrim (A := A) (C := C)) :=
  fun _ _ h => WordLift.ext (congrArg HeisLift.a h) (congrArg HeisLift.g h)

theorem heisDual_injective : Function.Injective (heisDual (A := A) (C := C)) :=
  fun _ _ h => WordLift.ext (congrArg HeisLift.l h) (congrArg HeisLift.g h)

/-- **The Heisenberg centre**, `(0, 0, 1, 1)`: an element of order exactly `2` in every
`H(A) ⋊ C`.  This is what makes the common level even at no cost. -/
theorem orderOf_heisCentre : orderOf (⟨0, 0, 1, 1⟩ : HeisLift A C) = 2 := by
  have hsq : (⟨0, 0, 1, 1⟩ : HeisLift A C) ^ 2 = 1 := by
    rw [pow_two]
    refine HeisLift.ext ?_ ?_ ?_ (one_mul 1)
    · show (0 : A) + (1 : C) • (0 : A) = 0
      rw [smul_zero, add_zero]
    · show (0 : ElemDual A) + (1 : C) • (0 : ElemDual A) = 0
      rw [smul_zero, add_zero]
    · show (1 : ZMod 2) + 1 + (0 : ElemDual A) ((1 : C) • (0 : A)) = 0
      rw [ElemDual.zero_apply, add_zero]
      decide
  have hne : (⟨0, 0, 1, 1⟩ : HeisLift A C) ≠ 1 := by
    intro h
    have hz : (1 : ZMod 2) = 0 := congrArg HeisLift.z h
    exact absurd hz (by decide)
  rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _
    (orderOf_dvd_of_pow_eq_one hsq)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

/-- Every element of the Heisenberg lift is killed by the level (definitionally). -/
theorem orderOf_heisLift_dvd (x : HeisLift A C) :
    orderOf x ∣ Monoid.exponent (HeisLift A C) := Monoid.order_dvd_exponent x

/-- **The split group is killed by the Heisenberg level** — the primal slice is a subgroup. -/
theorem orderOf_wordLift_dvd_heisExponent (x : WordLift A C) :
    orderOf x ∣ Monoid.exponent (HeisLift A C) := by
  rw [← orderOf_injective (heisPrim (A := A) (C := C)) heisPrim_injective x]
  exact Monoid.order_dvd_exponent _

/-- **The dual split group is killed by the same level** — the dual slice is a subgroup. -/
theorem orderOf_wordLiftDual_dvd_heisExponent (x : WordLift (ElemDual A) C) :
    orderOf x ∣ Monoid.exponent (HeisLift A C) := by
  rw [← orderOf_injective (heisDual (A := A) (C := C)) heisDual_injective x]
  exact Monoid.order_dvd_exponent _

variable [Finite A] [Finite C]

/-- The common level: the Heisenberg lift's own exponent. -/
theorem heisExponent_ne_zero : Monoid.exponent (HeisLift A C) ≠ 0 :=
  Monoid.exponent_ne_zero_of_finite

/-- **The Heisenberg level is nonzero and even** — CB-FR §8.2's `splitLevel_ne_zero_and_even` for
this ticket's target, and with a *better* source for the evenness: the Heisenberg centre, which
needs no hypothesis on `A` at all. -/
theorem heisLevel_ne_zero_and_even :
    Monoid.exponent (HeisLift A C) ≠ 0
      ∧ (Monoid.exponent (HeisLift A C)).factorization 2 ≠ 0 := by
  refine ⟨heisExponent_ne_zero, ?_⟩
  have hdvd : 2 ∣ Monoid.exponent (HeisLift A C) := by
    rw [← orderOf_heisCentre (A := A) (C := C)]
    exact Monoid.order_dvd_exponent _
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two heisExponent_ne_zero hdvd
  omega

end HeisLevel

/-- `HeisLift` carries no topology anywhere in the repository, and the profinite denotation
`PWord.eval` needs one.  `⊥` is the only candidate on a finite group and no diamond is possible.
(The same device as `Count/HTwo.lean` §3's `fiberProdTopologicalSpace`.) -/
local instance heisTopologicalSpace {C : Type} [Group C] {A : Type} [AddCommGroup A] :
    TopologicalSpace (HeisLift A C) := ⊥

local instance heisDiscreteTopology {C : Type} [Group C] {A : Type} [AddCommGroup A] :
    DiscreteTopology (HeisLift A C) := ⟨rfl⟩

-- CB-H2 §4's discreteness of a finite level.  Its instance attribute is `local`, so it is
-- re-enabled here rather than redeclared (the declaration itself is already in this namespace).
attribute [local instance] GQ2.Dyadic.Count.quotientDiscreteTopology

/-! ## §3. The Heisenberg `2`-cocycle, and `pRelZ` at it

`GQ2/MixedBObs.lean`'s two definitions, restated over the dyadic `WordCoh.TwoCocycle` (the `ℚ₂`
copy is a different structure — `Word/WordCoh.lean`'s own dedup note lists all three) and with the
`Fin 4` marking replaced by an arbitrary alphabet.

The content is one observation: `κ((a,λ),g)((a',λ'),g') = λ(g • a')` **is** the central defect of
the Heisenberg multiplication, so `CentExt kappaHeisN` and `H(A) ⋊ C` are the same group, and the
`WordCoh` fibre coordinate is the Stokes central coordinate `.z`. -/

section Kappa

open GQ2.Dyadic.WordCoh

variable {ι : Type*} {C : Type} [Group C] {A : Type} [AddCommGroup A] [DistribMulAction C A]

/-- **The Heisenberg `2`-cocycle** on the base semidirect product `(A × A^∨) ⋊ C`:
`κ(p, q) = p.λ(p.g • q.a)`. -/
noncomputable def kappaHeisN : WordCoh.TwoCocycle (WordLift (A × ElemDual A) C) where
  κ p q := p.u.2 (p.g • q.u.1)
  norm := by simp [WordLift.one_u]
  cocyc a b c := by
    show a.u.2 (a.g • b.u.1) + (a * b).u.2 ((a * b).g • c.u.1)
        = a.u.2 (a.g • (b * c).u.1) + b.u.2 (b.g • c.u.1)
    simp only [WordLift.mul_u, WordLift.mul_g, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, map_add, ElemDual.add_apply, smul_add, mul_smul, ElemDual.smul_apply,
      inv_smul_smul]
    abel

/-- **The structural isomorphism** `CentExt kappaHeisN →* H(A) ⋊ C`, `((a,λ),g; z) ↦ (a,λ,z,g)`.
A homomorphism *precisely* because `kappaHeisN`'s defect is the Heisenberg central term. -/
noncomputable def PhiHeisN : WordCoh.CentExt (kappaHeisN (A := A) (C := C)) →* HeisLift A C where
  toFun p := ⟨p.base.u.1, p.base.u.2, p.fib, p.base.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The paired base marking of `(A × A^∨) ⋊ C`: the letters carry the offsets `(x i, y i)` over
`c`.  `MixedBObs.mBaseMarking` at an arbitrary alphabet. -/
def heisBase (c : ι → C) (x : ι → A) (y : ι → ElemDual A) : ι → WordLift (A × ElemDual A) C :=
  fun i => ⟨(x i, y i), c i⟩

theorem phiHeisN_lift (c : ι → C) (x : ι → A) (y : ι → ElemDual A) (i : ι) :
    PhiHeisN (WordCoh.lift (heisBase c x y) kappaHeisN i) = heisGen c x y i := rfl

variable [Finite A] [Finite C]

/-- **`pRelZ` at the Heisenberg cocycle is the Stokes central coordinate.**  The degree-generic,
alphabet-generic, `PWord`-valued `MixedBObs.mixedB_eq_relZPair`: instead of matching two traced
sums by naturality of `Marking.map_{tame,wild}Value`, one application of `PWord.map_eval` along
`PhiHeisN` does it for an arbitrary intrinsic word. -/
theorem pRelZ_kappaHeisN (Wk : PWord ι) (c : ι → C) (x : ι → A) (y : ι → ElemDual A) :
    pRelZ Wk (heisBase c x y) kappaHeisN = (PWord.eval (heisGen c x y) Wk).z := by
  have h := PWord.map_eval (discreteCMH (PhiHeisN (A := A) (C := C)))
    (WordCoh.lift (heisBase c x y) kappaHeisN) Wk
  have hgen : (fun i => discreteCMH (PhiHeisN (A := A) (C := C))
      (WordCoh.lift (heisBase c x y) kappaHeisN i)) = heisGen c x y := rfl
  rw [hgen] at h
  show (PWord.eval (WordCoh.lift (heisBase c x y) kappaHeisN) Wk).fib = _
  rw [← h]
  rfl

end Kappa

/-! ## §4. The obstruction of an inflated cocycle

`MixedBObs.obs_inflation` for CB-H2's family obstruction: if a continuous `2`-cocycle on `Γ` is
*pointwise* pulled back from a finite group along a continuous hom, its obstruction vector is the
relator obstruction of the pushed marking.

This packages the whole `LevelFactor` computation once, so §5's ledger identity is a rewrite.  The
level used is the hom's own kernel, so no factorization has to be chosen or compared. -/

section Inflation

open GQ2.Dyadic.WordCoh

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  {L : Type} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]

/-- The kernel of a continuous hom into a finite discrete group, as an open normal subgroup. -/
def kerON (H : ContinuousMonoidHom Γ L) : OpenNormalSubgroup Γ where
  toSubgroup := H.toMonoidHom.ker
  isOpen' := by
    have hset : (H.toMonoidHom.ker : Subgroup Γ).carrier = H ⁻¹' {1} := by
      ext g; simp
    show IsOpen (H.toMonoidHom.ker : Subgroup Γ).carrier
    rw [hset]
    exact (isOpen_discrete ({1} : Set L)).preimage H.continuous_toFun

/-- **The obstruction of an inflated cocycle.**  If `φ(a, b) = κ(H a, H b)` for a continuous
`H : Γ → L` into a finite discrete group and a `2`-cocycle `κ` on `L`, then the family obstruction
is the relator obstruction of the pushed marking `H ∘ gen`. -/
theorem pObsFam_inflation (W : ρ → PWord ι) (gen : ι → Γ) (H : ContinuousMonoidHom Γ L)
    (κ : WordCoh.TwoCocycle L) (φ : Z2 Γ (ZMod 2))
    (hφ : ∀ a b, φ.1 (a, b) = κ.κ (H a) (H b)) :
    pObsFam W gen φ = fun k => pRelZ (W k) (fun i => H (gen i)) κ := by
  set V := kerON H with hV
  set Hbar := QuotientGroup.kerLift H.toMonoidHom with hHbar
  have hHbarmk : ∀ g : Γ, Hbar (QuotientGroup.mk' V.toSubgroup g) = H g := fun g =>
    QuotientGroup.kerLift_mk H.toMonoidHom g
  have hnorm : φ.1 (1, 1) = 0 := by rw [hφ, map_one, κ.norm]
  have hfact : ∀ x y : Γ, WordCoh.normalizeCochain φ.1 (x, y)
      = (κ.comap Hbar).κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y) := by
    intro x y
    rw [WordCoh.TwoCocycle.comap_κ, hHbarmk, hHbarmk, ← hφ]
    show φ.1 (x, y) - φ.1 (1, 1) = φ.1 (x, y)
    rw [hnorm, sub_zero]
  show pObsFun W gen φ = _
  rw [pObsFun_eq W gen φ ⟨V, κ.comap Hbar, hfact⟩]
  show (fun k => pRelZ (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) (κ.comap Hbar)) = _
  funext k
  rw [← pRelZ_comap (W k) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) κ Hbar]
  exact congrArg (fun μ : ι → L => pRelZ (W k) μ κ) (funext fun i => hHbarmk (gen i))

end Inflation

end GQ2.Dyadic.Count
