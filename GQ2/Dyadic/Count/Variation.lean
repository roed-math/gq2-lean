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

end GQ2.Dyadic.Count
