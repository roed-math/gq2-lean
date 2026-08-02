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

/-- **The scalar slice** `𝔽₂ ⋊ C ↪ H(A) ⋊ C`, `(m, g) ↦ (0, 0, m, g)` — the *centre* times the
base, not a coefficient slice.  At the scalars the source is a direct product (CB-2 §1), and the
Heisenberg centre is central, so the two multiplications agree. -/
noncomputable def heisScal [DistribMulAction C (ZMod 2)] :
    WordLift (ZMod 2) C →* HeisLift A C where
  toFun p := ⟨0, 0, p.u, p.g⟩
  map_one' := rfl
  map_mul' p q := by
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show (0 : A) = 0 + p.g • (0 : A)
      rw [smul_zero, add_zero]
    · show (0 : ElemDual A) = 0 + p.g • (0 : ElemDual A)
      rw [smul_zero, add_zero]
    · show p.u + p.g • q.u = p.u + q.u + (0 : ElemDual A) (p.g • (0 : A))
      rw [ElemDual.zero_apply, add_zero, smul_zmod2]

theorem heisScal_injective [DistribMulAction C (ZMod 2)] :
    Function.Injective (heisScal (A := A) (C := C)) :=
  fun _ _ h => WordLift.ext (congrArg HeisLift.z h) (congrArg HeisLift.g h)

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

/-- **The scalar split group is killed by the same level** — CB-2's coefficient module, which is
where CB-1's `z1Equiv` and CB-H2's rung are both read. -/
theorem orderOf_wordLiftScal_dvd_heisExponent [DistribMulAction C (ZMod 2)]
    (x : WordLift (ZMod 2) C) : orderOf x ∣ Monoid.exponent (HeisLift A C) := by
  rw [← orderOf_injective (heisScal (A := A) (C := C)) heisScal_injective x]
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

/-! ## §5. The ledger identity

The `ℚ₂` half-torsor proof's fifth step (`LedgerGamma{A,R}.obs_varCoc_eq_mixedB`), degree-generic
and word-generic.  Two components:

* §5a, the **detection functional**: at the scalars `∑_k` kills `im d¹`, so it descends to
  `WordH²(𝔽₂) →+ 𝔽₂`.  This is the degree-generic replacement for `ℚ₂`'s `obsH2`, and it is
  cheaper for CB-2's reason — at trivial action `d⁰ = 0` on the dual side, so the second chain
  condition `heisEta2 ∘ d¹ = heisEta1 ∘ d⁰` has a *zero* right-hand side.
* §5b, the **identity**: `varCoc u` is pointwise the Heisenberg cocycle pulled back along the graph
  of the pair `(z, φ)`, so §4 computes its obstruction vector as the relator `z`-coordinates, and
  §3 identifies those with the traced Stokes pairing `heisEta1`.

Together: a nonzero pairing value forces the variation class to be nonzero. -/

section Ledger

open GQ2.Dyadic.WordCoh

/-! ### §5a. The detection functional -/

section Detect

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] {C : Type*} [Group C]
  [DistribMulAction C (ZMod 2)] {c : ι → C} {w : ρ → FreeGroup ι}

/-- The identity functional, as an element of `ElemDual (ZMod 2)`.  It exists only because the
coefficient module *is* the scalars — this is what makes §5a a two-line argument. -/
def idDual : ElemDual (ZMod 2) := AddMonoidHom.id (ZMod 2)

@[simp] theorem idDual_apply (m : ZMod 2) : idDual m = m := rfl

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] in
/-- **At the scalars the dual `d⁰` vanishes** — `Aut(𝔽₂) = 1`, so the contragredient action on
`ElemDual (ZMod 2)` is trivial too.  CB-2 §1's observation, one degree up on the dual side. -/
theorem heisD0_idDual (c : ι → C) : heisD0 (A := ElemDual (ZMod 2)) c idDual = 0 := by
  funext i
  show heisD0 (A := ElemDual (ZMod 2)) c idDual i = 0
  refine ElemDual.ext fun m => ?_
  rw [heisD0_apply, ElemDual.sub_apply, ElemDual.smul_apply, idDual_apply, idDual_apply,
    smul_zmod2, sub_self, ElemDual.zero_apply]

/-- **At the scalars the traced sum kills `im d¹`.**

`heisEta2 (d¹x) λ = heisEta1 x (d⁰λ)` (the second Stokes chain condition) has both sides
computable here: the right one because `Aut(𝔽₂) = 1` makes the contragredient action on
`ElemDual (ZMod 2)` trivial, so `d⁰λ = 0`, and `heisEta1 x 0 = 0` because a Heisenberg word with
zero dual offsets has zero central coordinate (`heisWord_zero_dual`).  The left one is
`λ(∑_k (d¹x)_k)`, and taking `λ = id` — available because the module *is* `𝔽₂` — reads off the
sum. -/
theorem sum_heisD1_zmod2 (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (x : ι → ZMod 2) : ∑ k, heisD1 (A := ZMod 2) c w x k = 0 := by
  have hchain := heisEta2_comp_d1 c w hr hend x idDual
  rw [heisD0_idDual] at hchain
  have hzero : heisEta1 c w x (0 : ι → ElemDual (ZMod 2)) = 0 := by
    show (∑ k, (FreeGroup.lift (heisGen c x (0 : ι → ElemDual (ZMod 2))) (w k)).z) = 0
    exact Finset.sum_eq_zero fun k _ => (heisWord_zero_dual c x (w k)).2
  rw [hzero] at hchain
  exact hchain

/-- **The detection criterion**: a vector with nonzero traced sum is nonzero in `WordH²(𝔽₂)`. -/
theorem wordH2Mk_ne_zero_of_sum (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) {v : ρ → ZMod 2} (hv : ∑ k, v k ≠ 0) :
    (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range v : WordH2 c w (ZMod 2)) ≠ 0 := by
  intro h0
  obtain ⟨x, rfl⟩ := (QuotientAddGroup.eq_zero_iff v).mp h0
  exact hv (sum_heisD1_zmod2 hr hend x)

end Detect

/-! ### §5b. The identity -/

section Identity

variable {ι ρ : Type*} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (Additive ↥D.T)] [DistribMulAction Γ (ElemDual (Additive ↥D.T))]
  [TopologicalSpace (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))]
  (S : TComplement D) (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (hcompat : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
  (hcompatD : ∀ (γ : Γ) (l : ElemDual (Additive ↥D.T)), γ • l = rho γ • l)

include hcompat hcompatD in
/-- **The graph hom** of a primal/dual pair of cocycles into the Heisenberg base
`(T × T^∨) ⋊ (Bg ⧸ M)`.  `LedgerGammaA.pairHom`, `Γ`-generic and built directly (CB-1's `wordHom`
would need the product module's own instance block). -/
noncomputable def pairHomN (z : Z1 Γ (Additive ↥D.T)) (φ : Z1 Γ (ElemDual (Additive ↥D.T))) :
    ContinuousMonoidHom Γ (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) where
  toFun γ := ⟨(z.1 γ, φ.1 γ), rho γ⟩
  map_one' :=
    WordLift.ext (Prod.ext (Z1_apply_one z) (Z1_apply_one φ)) (map_one rho)
  map_mul' γ δ := by
    refine WordLift.ext (Prod.ext ?_ ?_) (map_mul rho γ δ)
    · show z.1 (γ * δ) = z.1 γ + rho γ • z.1 δ
      rw [(mem_Z1_iff.mp z.2).2 γ δ, hcompat]
    · show φ.1 (γ * δ) = φ.1 γ + rho γ • φ.1 δ
      rw [(mem_Z1_iff.mp φ.2).2 γ δ, hcompatD]
  continuous_toFun := by
    haveI := discreteTopology_quotient D
    have hg : Continuous fun γ : Γ => (((z.1 γ, φ.1 γ), rho γ) :
        (Additive ↥D.T × ElemDual (Additive ↥D.T)) × (Bg ⧸ D.M)) :=
      (((mem_Z1_iff.mp z.2).1).prodMk ((mem_Z1_iff.mp φ.2).1)).prodMk rho.continuous_toFun
    exact (continuous_of_discreteTopology (f := (WordLift.equivProd
      (A := Additive ↥D.T × ElemDual (Additive ↥D.T)) (C := Bg ⧸ D.M)).symm)).comp hg

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)]
  [DiscreteTopology (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))] in
include hcompat hcompatD in
/-- **The variation cochain is the Heisenberg cocycle, inflated.**  The `ℚ₂` proof's `hunfold`,
verbatim once `GA` is a variable: `varCoc u (a, b) = φ(a)(ρa · z(b)) = κ(H a, H b)`. -/
theorem varCoc_eq_kappaHeisN (u : TCocycle D rho) (z : Z1 Γ (Additive ↥D.T))
    (φ : Z1 Γ (ElemDual (Additive ↥D.T)))
    (hφ : ∀ (γ : Γ) (s : Additive ↥D.T),
      (φ.1 γ) s = edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s)))
    (hu : ∀ γ, u.u γ = ((Additive.toMul (z.1 γ) : ↥D.T) : Bg)) (a b : Γ) :
    varCoc D rho S u (a, b)
      = kappaHeisN.κ (pairHomN rho hcompat hcompatD z φ a)
          (pairHomN rho hcompat hcompatD z φ b) := by
  show edgeQ D S (rho a) ⟨u.u b, u.mem b⟩ = (φ.1 a) (rho a • z.1 b)
  rw [hφ, ← hcompat, inv_smul_smul]
  exact congrArg (edgeQ D S (rho a)) (Subtype.ext (hu b))

include hcompat hcompatD in
/-- **The ledger identity, intrinsic form.**  The family obstruction of the variation cocycle is
the vector of relator central coordinates of the Heisenberg-lifted marking.

`Γ`-generic, alphabet-generic, and stated over the *intrinsic* `PWord` relators — no resolution
is used yet, which is what lets the resolution be chosen once, at §7, and at a level §2 supplies
for free. -/
theorem pObsFam_varCoc (W : ρ → PWord ι) (gen : ι → Γ) (u : TCocycle D rho)
    (z : Z1 Γ (Additive ↥D.T)) (φ : Z1 Γ (ElemDual (Additive ↥D.T)))
    (hφ : ∀ (γ : Γ) (s : Additive ↥D.T),
      (φ.1 γ) s = edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s)))
    (hu : ∀ γ, u.u γ = ((Additive.toMul (z.1 γ) : ↥D.T) : Bg)) :
    pObsFam W gen ⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smulTrivZmod2 u⟩
      = fun k => (PWord.eval (heisGen (fun i => rho (gen i))
          (fun i => z.1 (gen i)) (fun i => φ.1 (gen i))) (W k)).z := by
  haveI := discreteTopology_quotient D
  rw [pObsFam_inflation W gen (pairHomN rho hcompat hcompatD z φ) kappaHeisN
    ⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smulTrivZmod2 u⟩
    (fun a b => varCoc_eq_kappaHeisN S rho hcompat hcompatD u z φ hφ hu a b)]
  funext k
  exact pRelZ_kappaHeisN (W k) (fun i => rho (gen i)) (fun i => z.1 (gen i))
    (fun i => φ.1 (gen i))

end Identity

/-! ### §6. The shifted-edge dual cocycle, `Γ`-generic

`GQ2/LedgerGammaA.lean`'s `exists_phiF` with `GA` turned back into a variable.  Nothing in that
argument is about `Γ_A`: it constructs `φf γ = (s ↦ ε̄(ργ)(γ⁻¹ · s))` from the radical-cover data
alone, proves it is a continuous dual `1`-cocycle by factoring through `ρ` into the *finite*
`Bg ⧸ M`, and proves its class nonzero by contraposition against
`CentralObstruction.not_noDescent_of_edge_trivial`, which is already `Γ`-free.

The `ℚ₂` file writes it twice (`Γ_A` and `Γ_R`, ~200 lines each, `55%` textually identical —
CB1 memo §3.1's measurement).  Here it is written once. -/

section PhiVar

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (Additive ↥D.T)] [DistribMulAction Γ (ElemDual (Additive ↥D.T))]
  (S : TComplement D) (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (hcompat : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
  (hcompatD : ∀ (γ : Γ) (l : ElemDual (Additive ↥D.T)), γ • l = rho γ • l)

omit [IsTopologicalGroup Γ] [DiscreteTopology Bg]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))] in
/-- Additivity of the shifted-edge functional in its argument. -/
theorem phiVar_add (γ : Γ) (s s' : Additive ↥D.T) :
    edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • (s + s')))
      = edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s))
        + edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s')) := by
  have hmulcast : Additive.toMul ((γ⁻¹ : Γ) • (s + s'))
      = Additive.toMul ((γ⁻¹ : Γ) • s) * Additive.toMul ((γ⁻¹ : Γ) • s') := by
    rw [smul_add]; rfl
  rw [hmulcast]
  exact edge_add D S (Quotient.out (rho γ)) _ _

omit [IsTopologicalGroup Γ] [DiscreteTopology Bg]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))] in
/-- **The shifted-edge dual `1`-cochain** `γ ↦ (s ↦ ε̄(ργ)(γ⁻¹ · s))`. -/
noncomputable def phiVar (γ : Γ) : ElemDual (Additive ↥D.T) :=
  (AddMonoidHom.mk' (fun s => edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s)))
    (phiVar_add S rho γ) : Additive ↥D.T →+ ZMod 2)

omit [IsTopologicalGroup Γ] [DiscreteTopology Bg]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))] in
@[simp] theorem phiVar_apply (γ : Γ) (s : Additive ↥D.T) :
    phiVar S rho γ s = edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s)) := rfl

omit [IsTopologicalGroup Γ] [DiscreteTopology Bg]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))] in
include hcompat in
/-- Transport of the `Γ`-action on `T` through `ρ` to the conjugation action `cactFun`. -/
theorem toMul_smul_eq_cactFun (γ : Γ) (s : Additive ↥D.T) :
    Additive.toMul (γ • s) = cactFun D (rho γ) (Additive.toMul s) := by
  rw [hcompat]; exact cActT_toMul D (rho γ) s

omit [IsTopologicalGroup Γ] [DiscreteTopology Bg]
  [TopologicalSpace (ElemDual (Additive ↥D.T))]
  [DiscreteTopology (ElemDual (Additive ↥D.T))] in
include hcompat hcompatD in
/-- Pointwise formula for the dual `Γ`-action: `(γ • l) a = l (γ⁻¹ · a)`. -/
theorem dual_smul_apply (γ : Γ) (l : ElemDual (Additive ↥D.T)) (a : Additive ↥D.T) :
    (γ • l) a = l (γ⁻¹ • a) := by
  rw [hcompatD, ElemDual.smul_apply, hcompat γ⁻¹ a, map_inv]

omit [IsTopologicalGroup Γ] [DiscreteTopology Bg]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))] in
include hcompat in
/-- The crossed additive relation for the shifted-edge functional across a product. -/
theorem phiVar_edgeQ_mul (γ δ : Γ) (s : Additive ↥D.T) :
    edgeQ D S (rho (γ * δ)) (Additive.toMul ((γ * δ)⁻¹ • s))
      = edgeQ D S (rho γ) (Additive.toMul (γ⁻¹ • s))
        + edgeQ D S (rho δ) (Additive.toMul (δ⁻¹ • (γ⁻¹ : Γ) • s)) := by
  have hactGA := toMul_smul_eq_cactFun rho hcompat
  have hγ : (QuotientGroup.mk (Quotient.out (rho γ)) : Bg ⧸ D.M) = rho γ :=
    QuotientGroup.out_eq' _
  have hδ : (QuotientGroup.mk (Quotient.out (rho δ)) : Bg ⧸ D.M) = rho δ :=
    QuotientGroup.out_eq' _
  have hγδrep : (QuotientGroup.mk (Quotient.out (rho γ) * Quotient.out (rho δ)) : Bg ⧸ D.M)
      = rho (γ * δ) := by rw [QuotientGroup.mk_mul, hγ, hδ, map_mul]
  rw [edgeQ_eq D S (rho (γ * δ)) hγδrep, edge_mul]
  have h2 : edge D S (Quotient.out (rho γ))
        ⟨Quotient.out (rho δ) * (Additive.toMul ((γ * δ)⁻¹ • s)).1 * (Quotient.out (rho δ))⁻¹,
          conj_mem_T D (Quotient.out (rho δ)) (Additive.toMul ((γ * δ)⁻¹ • s))⟩
      = edgeQ D S (rho γ) (Additive.toMul (γ⁻¹ • s)) := by
    rw [edgeQ_eq D S (rho γ) hγ]
    congr 1
    apply Subtype.ext
    show Quotient.out (rho δ) * (Additive.toMul ((γ * δ)⁻¹ • s)).1 * (Quotient.out (rho δ))⁻¹
        = (Additive.toMul (γ⁻¹ • s)).1
    have hsplit : Additive.toMul ((γ * δ)⁻¹ • s)
        = cactFun D (rho δ⁻¹) (Additive.toMul (γ⁻¹ • s)) := by
      rw [hactGA, show ((γ * δ)⁻¹ : Γ) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ, map_mul,
        cactFun_mul, ← hactGA]
    rw [hsplit]
    have hδinv : (QuotientGroup.mk ((Quotient.out (rho δ))⁻¹) : Bg ⧸ D.M) = rho δ⁻¹ := by
      rw [QuotientGroup.mk_inv, hδ, map_inv]
    rw [cactFun_eq D (rho δ⁻¹) hδinv]
    group
  have h1 : edge D S (Quotient.out (rho δ)) (Additive.toMul ((γ * δ)⁻¹ • s))
      = edgeQ D S (rho δ) (Additive.toMul (δ⁻¹ • (γ⁻¹ : Γ) • s)) := by
    rw [edgeQ_eq D S (rho δ) hδ]
    congr 1
    rw [mul_inv_rev, mul_smul]
  rw [h1, h2]

omit [IsTopologicalGroup Γ] in
include hcompat hcompatD in
/-- **The shifted-edge cochain is a dual `1`-cocycle.**  Continuity is the whole reason the
formula is written with `γ⁻¹ • s` rather than with a representative: it makes the cochain factor
through `ρ` into the finite discrete `Bg ⧸ M`. -/
theorem phiVar_mem_Z1 : phiVar S rho ∈ Z1 Γ (ElemDual (Additive ↥D.T)) := by
  haveI := discreteTopology_quotient D
  have hactGA := toMul_smul_eq_cactFun rho hcompat
  have hsmulD := dual_smul_apply rho hcompat hcompatD
  have hcrossZ := phiVar_edgeQ_mul S rho hcompat
  rw [mem_Z1_iff]
  refine ⟨?_, ?_⟩
  · have hΦadd : ∀ (c : Bg ⧸ D.M) (s s' : Additive ↥D.T),
        edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul (s + s')).1
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul (s + s'))⟩
          = edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩
            + edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
      intro c s s'
      have hsplit : (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul (s + s')).1
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul (s + s'))⟩ : ↥D.T)
          = (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩ : ↥D.T)
            * ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
        apply Subtype.ext
        show Quotient.out (c⁻¹ : Bg ⧸ D.M)
            * ((Additive.toMul s).1 * (Additive.toMul s').1)
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹
          = (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
            * (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
        group
      rw [hsplit]
      exact edge_add D S (Quotient.out c) _ _
    have hfac : phiVar S rho = (fun c : Bg ⧸ D.M =>
        (AddMonoidHom.mk' (fun s : Additive ↥D.T =>
          edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩) (hΦadd c)
          : ElemDual (Additive ↥D.T))) ∘ (fun γ : Γ => (rho γ : Bg ⧸ D.M)) := by
      funext γ
      refine DFunLike.ext _ _ fun s => ?_
      rw [phiVar_apply]
      show edgeQ D S (rho γ) (Additive.toMul ((γ⁻¹ : Γ) • s))
        = edgeQ D S (rho γ) ⟨Quotient.out ((rho γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
            * (Quotient.out ((rho γ)⁻¹ : Bg ⧸ D.M))⁻¹,
            conj_mem_T D (Quotient.out ((rho γ)⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩
      refine congrArg (edgeQ D S (rho γ)) (Subtype.ext ?_)
      rw [hactGA]
      show Quotient.out (rho γ⁻¹) * (Additive.toMul s).1 * (Quotient.out (rho γ⁻¹))⁻¹
        = Quotient.out ((rho γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
          * (Quotient.out ((rho γ)⁻¹ : Bg ⧸ D.M))⁻¹
      rw [map_inv]
    rw [hfac]
    exact continuous_of_discreteTopology.comp rho.continuous_toFun
  · intro γ δ
    refine DFunLike.ext _ _ fun s => ?_
    have hz := hcrossZ γ δ s
    show (phiVar S rho (γ * δ)) s = (phiVar S rho γ + γ • phiVar S rho δ) s
    rw [ElemDual.add_apply, hsmulD]
    simpa only [phiVar_apply] using hz

omit [IsTopologicalGroup Γ] in
include hcompat hcompatD in
/-- **The shifted-edge class is nonzero exactly when the cover does not descend.**  A coboundary
would give an additive `ℓ : T → 𝔽₂` trivializing the edge, and `not_noDescent_of_edge_trivial`
builds the descending complement from it. -/
theorem phiVar_ne_zero (hρ : Function.Surjective rho) (hedge : D.NoDescent) :
    H1mk Γ (ElemDual (Additive ↥D.T))
        ⟨phiVar S rho, phiVar_mem_Z1 S rho hcompat hcompatD⟩ ≠ 0 := by
  have hsmulD := dual_smul_apply rho hcompat hcompatD
  have hactGA := toMul_smul_eq_cactFun rho hcompat
  intro h0
  have hmem : phiVar S rho ∈ B1 Γ (ElemDual (Additive ↥D.T)) := by
    have h1 := (QuotientAddGroup.eq_zero_iff _).mp h0
    rwa [AddSubgroup.mem_addSubgroupOf] at h1
  obtain ⟨lam, hlam⟩ := hmem
  set ℓ : ↥D.T → ZMod 2 :=
    fun t => (lam : ElemDual (Additive ↥D.T)) (Additive.ofMul t) with hℓdef
  have hℓadd : ∀ t t' : ↥D.T, ℓ (t * t') = ℓ t + ℓ t' := by
    intro t t'
    show (lam : ElemDual (Additive ↥D.T)) (Additive.ofMul (t * t')) = _
    rw [show Additive.ofMul (t * t')
        = Additive.ofMul t + Additive.ofMul t' from rfl, map_add]
  refine (not_noDescent_of_edge_trivial D S ℓ hℓadd ?_) hedge
  intro b t
  obtain ⟨γ, hγ⟩ := hρ (QuotientGroup.mk b)
  have hlamγ := congrFun hlam γ
  have hval := congrArg
    (fun ψ : ElemDual (Additive ↥D.T) => ψ ((γ : Γ) • Additive.ofMul t)) hlamγ
  have hL : (dZero Γ (ElemDual (Additive ↥D.T)) lam γ) ((γ : Γ) • Additive.ofMul t)
      = lam (Additive.ofMul t) - lam ((γ : Γ) • Additive.ofMul t) := by
    show ((γ • lam - lam : ElemDual (Additive ↥D.T))) ((γ : Γ) • Additive.ofMul t) = _
    rw [ElemDual.sub_apply, hsmulD, inv_smul_smul]
  have hR : (phiVar S rho γ) ((γ : Γ) • Additive.ofMul t) = edge D S b t := by
    rw [phiVar_apply, ← edgeQ_eq D S (rho γ) hγ.symm t]
    refine congrArg (edgeQ D S (rho γ)) ?_
    exact inv_smul_smul γ (Additive.ofMul t)
  rw [hL, hR] at hval
  have hbt : Additive.ofMul (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T)
      = (γ : Γ) • Additive.ofMul t := by
    have hcast : (γ : Γ) • Additive.ofMul t = Additive.ofMul (cactFun D (rho γ) t) :=
      Additive.toMul.injective (by rw [hactGA]; rfl)
    rw [hcast]
    exact congrArg Additive.ofMul (Subtype.ext (cactFun_eq D (rho γ) hγ.symm t).symm)
  show edge D S b t = ℓ (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T) + ℓ t
  rw [hℓdef]
  show edge D S b t
    = lam (Additive.ofMul (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T)) + lam (Additive.ofMul t)
  rw [hbt, ← hval]
  exact (by decide : ∀ a e : ZMod 2, a - e = e + a) _ _

end PhiVar

end Ledger

/-! ## §7. The nonzero variation class, `Γ`-generic

The five steps assembled.  The output is exactly `Count/Scalar.lean` §9's `hvar` slot, and by
CB-H2 §7 the same witness is `cardH2`'s missing nontriviality — so **one theorem unblocks three
clauses**.

What it consumes, and from whom:

| input | owner |
|---|---|
| `hpres`, `hwild2` | CB-MP/CB-TR (`isAdmissibleMarkedPresentation_gammaR`, `isWildTwo_of_gammaGen`) |
| `hresS/hresP/hresD/hresH` | the word lane, all four at the **one** level of §2 |
| `hd`, `hr`, `hend` | the branch's Stokes payload — the *only* duality input |
| `hedge`, `hρ` | the radical-cover datum (source-free: `CardH2GammaA.datum` is reused verbatim) |

⚠ Note what is **not** here: no `hcomp`, no `#H²w = 2`, no `IsSelfDual` count clause.  §5a detects
nonvanishing by the traced sum alone, so the *count* half of the duality package is never used —
only clause 3, the pairing. -/

section NonzeroVariation

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)]
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [TopologicalSpace (ElemDual (Additive ↥D.T))] [DiscreteTopology (ElemDual (Additive ↥D.T))]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)]
  [DistribMulAction Γ (ElemDual (Additive ↥D.T))] [ContinuousSMul Γ (ElemDual (Additive ↥D.T))]
  [TopologicalSpace (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
  [TopologicalSpace (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))]
  [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
  [TopologicalSpace (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))]
  [DiscreteTopology (WordLift (Additive ↥D.T × ElemDual (Additive ↥D.T)) (Bg ⧸ D.M))]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → (Bg ⧸ D.M)} {J : Set ι}
  (S : TComplement D) (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (hcompat : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)
  (hcompatD : ∀ (γ : Γ) (l : ElemDual (Additive ↥D.T)), γ • l = rho γ • l)
  (hc : ∀ i, rho (gen i) = c i)

omit [ContinuousSMul Γ (Additive ↥D.T)] in
include hcompat hcompatD hc in
/-- **The nonzero variation class** — the dyadic campaign's `exists_nonzero_varCoc_gamma{A,R}`,
over an abstract presented carrier and an arbitrary branch word.

Given a radical cover that does not descend and a surjection `ρ : Γ ↠ Bg ⧸ M`, there is a crossed
`T`-cocycle `u` whose variation class is a nonzero element of `H²(Γ, 𝔽₂)`. -/
theorem exists_nonzero_varCoc
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J) (hwild2 : IsWildTwo J c)
    (hresS : ResolvesAt W w (WordLift (ZMod 2) (Bg ⧸ D.M)))
    (hresP : ResolvesAt W w (WordLift (Additive ↥D.T) (Bg ⧸ D.M)))
    (hresD : ResolvesAt W w (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)))
    (hresH : ResolvesAt W w (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)))
    (hd : StokesDuality c w (Additive ↥D.T)) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w)
    (hedge : D.NoDescent) (hρ : Function.Surjective rho) :
    ∃ u : TCocycle D rho,
      H2mk Γ (ZMod 2) ⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smul_zmod2 u⟩ ≠ 0 := by
  classical
  haveI := discreteTopology_quotient D
  have hT₂ : ∀ a : Additive ↥D.T, a + a = 0 := radT_add_self D
  have hD₂ : ∀ l : ElemDual (Additive ↥D.T), l + l = 0 := fun l => l.add_self_eq_zero
  -- 1. the shifted-edge dual cocycle, nonzero in `H¹`
  set φ : Z1 Γ (ElemDual (Additive ↥D.T)) :=
    ⟨phiVar S rho, phiVar_mem_Z1 S rho hcompat hcompatD⟩ with hφdef
  have hφne : H1mk Γ (ElemDual (Additive ↥D.T)) φ ≠ 0 :=
    phiVar_ne_zero S rho hcompat hcompatD hρ hedge
  -- 2. transport into the word complex
  set y : WordH1 c w (ElemDual (Additive ↥D.T)) :=
    h1Equiv rho hcompatD hc hpres hresD hD₂ hwild2 (H1mk Γ (ElemDual (Additive ↥D.T)) φ) with hydef
  have hyne : y ≠ 0 := fun h =>
    hφne ((h1Equiv rho hcompatD hc hpres hresD hD₂ hwild2).injective (by rw [map_zero]; exact h))
  -- 3. the perfect pairing produces a primal partner
  obtain ⟨P, hPval, _hleft, hright⟩ := pairing_clause hd hr hend
  obtain ⟨h, hPne⟩ := hright y hyne
  obtain ⟨x, rfl⟩ := stokesH1Mk_surjective (heisD0 (A := Additive ↥D.T) c) (heisD1 c w) h
  -- 4. pull the primal class back to a continuous crossed cocycle, then to a `T`-cocycle
  set z : Z1 Γ (Additive ↥D.T) :=
    (z1Equiv rho hcompat hc hpres hresP hT₂ hwild2).symm x with hzdef
  have hzx : (fun i => z.1 (gen i)) = (x : ι → Additive ↥D.T) := by
    have := (z1Equiv rho hcompat hc hpres hresP hT₂ hwild2).apply_symm_apply x
    exact congrArg Subtype.val this
  refine ⟨(tcocycleEquivZ1 rho hcompat).symm z, ?_⟩
  set u : TCocycle D rho := (tcocycleEquivZ1 rho hcompat).symm z with hudef
  have hu : ∀ γ, u.u γ = ((Additive.toMul (z.1 γ) : ↥D.T) : Bg) := fun _ => rfl
  -- 5. the ledger: the traced obstruction is the pairing value, which is nonzero
  have hyv : (y : WordH1 c w (ElemDual (Additive ↥D.T)))
      = stokesH1Mk _ _ ⟨fun i => φ.1 (gen i),
          evalGen_mem_ker rho hcompatD hc hpres hresD φ⟩ := rfl
  have hpair : heisEta1 c w (fun i => z.1 (gen i)) (fun i => φ.1 (gen i)) ≠ 0 := by
    rw [hzx]
    rw [hyv, hPval] at hPne
    exact hPne
  have hobs : pObsFam W gen ⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smul_zmod2 u⟩
      = fun k => (FreeGroup.lift (heisGen c (fun i => z.1 (gen i))
          (fun i => φ.1 (gen i))) (w k)).z := by
    rw [pObsFam_varCoc S rho hcompat hcompatD W gen u z φ (fun _ _ => rfl) hu]
    funext k
    rw [hresH _ k]
    exact congrArg (fun t : ι → (Bg ⧸ D.M) =>
      (PWord.eval (heisGen t (fun i => z.1 (gen i)) (fun i => φ.1 (gen i))) (W k)).z)
      (funext hc)
  have hsum : ∑ k, pObsFam W gen
      ⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smul_zmod2 u⟩ k ≠ 0 := by
    rw [hobs]
    exact hpair
  -- 6. a coboundary would put the obstruction in `im d¹`, whose traced sum is zero
  intro h0
  refine hsum ?_
  have hB2 : (⟨varCoc D rho S u, varCoc_mem_Z2 D rho S smul_zmod2 u⟩ : Z2 Γ (ZMod 2)).1
      ∈ B2 Γ (ZMod 2) :=
    AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  obtain ⟨v, hv⟩ := pObsFam_B2_mem_range (w := w) hpres hresS c hB2
  rw [← hv]
  exact sum_heisD1_zmod2 hr hend v

end NonzeroVariation

end GQ2.Dyadic.Count
