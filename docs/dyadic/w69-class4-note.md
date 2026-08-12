# W69: the class-four calculus, and the class-four obligation

Lane W69-CLASS4.  New module `GQ2/Dyadic/SqCore/GradedClassFour.lean`; no edits to existing
files.  Prefixes `cfour` / `classFour` / `sqClassFour`.

## 0.  Headline

**`SqClassClearingSupply h 4` is NOT discharged, and it is NOT refuted.**  What this wave
commits is the class-four calculus, the class-four relator, and a reduction of the whole
class-four obligation to a single identity in `Q4 = levelQuot (DSq h) 4`:

> **`cfour_supply_of_eichDefect`**: if `cfourEichDefect nu' j = 1` at every selected marking and
> every handle, then `SqClassClearingSupply h 4` - with the **trivial** dressing.

`cfourEichDefect nu' j` is the class-four Eichler defect, the amount by which the two cleared
handle letters miss the plain handle bracket.  So the class-four attack surface is one element
of one abelian group, not a word problem.

All declarations pin to the standard three axioms (several to strict subsets); no `sorry`, no
new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 1.  The `Q4` calculus (module §1)

`Q4` is not class two.  Write `Y = lambdaImage G 2 4` for the image of `gamma_2` and
`Z = zLayer G 3` for the central involutive layer.  Wave 68 used two facts about `Q3`, both of
which fail at `Q4`; here is what replaces them.

* **Bimultiplicativity is not lost outright.**  It survives verbatim **against a `Y`-slot**
  (`cfour_commP_left_hom`, `cfour_commP_right_hom`), because the correction term of the free
  identity is then a bracket with a central element.  That is exactly the amount of
  `commP_mul_left_of_three` a class-four run still has.
* **`⁅gamma_2, gamma_2⁆ <= gamma_4`** (`cfour_commutator_lambdaTwo`), so `Y` is abelian in `Q4`
  (`cfour_commP_lambdaTwo`).  This is the one place the topology is used: the annihilator
  `{g | commP v g in gamma_4}` of a `gamma_2`-element is a **closed** subgroup (a preimage of the
  closed `gamma_4`) containing every square (the bracket already lies in the exponent-two `Z`)
  and every commutator (`cfourCommHom` is a homomorphism into the *abelian* `Z`), hence contains
  `twoCentralSucc top = gamma_2`.
* **The fourth-power map is not a homomorphism**: `cfour_pow_four_mul` gives
  `(p q)^4 = p^4 q^4 (commP q p)^2`.  Its defect is the *square of a bracket*, and that is
  precisely the shape that cancels in the analysis of §5 below.

The whole section is written in `commP` and never writes the element commutator notation `⁅ , ⁆`.

> **[Corrected W72-HOUSE.]**  This paragraph originally read "The element commutator notation
> `⁅ , ⁆` does not elaborate inside `GQ2.Dyadic.SqCore` (the `Bracket G G` instance is not
> synthesizable there, checked in isolation)", and offered that as the *reason* for writing
> `commP`.  It is **false**, and this is where the error entered the campaign: waves 70 and 71
> then repeated it in four further places.  `Bracket G G` is not synthesizable in *any* file, at
> *any* namespace, until that file writes `open scoped commutatorElement`, because mathlib makes
> `commutatorElement` a scoped instance on purpose (`Mathlib/Algebra/Group/Commutator.lean`).
> Nothing about `GQ2.Dyadic.SqCore` is involved; 17 files in that very directory open the
> instance and use the bracket.  The full diagnosis is the header of
> `GQ2/Dyadic/SqCore/Cores.lean` (landed `f82cb316`, wave 70).  Note also that `commP` and the
> bracket are **different functions**, `commP a b = ⁅a⁻¹, b⁻¹⁆`, which is the actual reason this
> lane's `commP` spelling is right.

## 2.  The relator modulo `gamma_4` (module §2)

> **`cfour_sqWord`**: `sqWord s x y = commP s x * x^4 * y^2 * commP y (commP y s)` in `Q4`.

Against wave 68's `bridge_sqWord` (`= commP s x * y^2`) the two extra terms are exactly the two
class-three collapses that fail one class up: the **fourth power** `x^4` (present as
`((x^2)^2)^-1`; only the *inverse* may be dropped, since `x^4` lies in `Z`) and the **triple
bracket** `commP y (commP y s)` (at class three `conjP y s` differed from `y` by a central
factor and the term collapsed).  Hence `cfour_sqRelWord`.

## 3.  The relator lives in an abelian group (module §3)

Every factor of `cfour_sqRelWord` lies in `Y` (`cfour_sqRelWord_mem_lambdaTwo`), and `Y` is
abelian.  **The class-four obligation may therefore be reordered at will.**  This is what
replaces wave 68's "everything in sight is central", and it is what keeps the class-four
computation finite instead of a bracket jungle.

## 4.  The undressed frame is the whole obligation (module §4)

> **`cfour_relator_base`**: `sqRelWord (levelMk 4 . sqArbBase h nu' j) = cfourEichDefect nu' j`.

With the trivial dressing the class-four relator is *exactly* the Eichler defect.  Every other
factor - the fourth power and the triple bracket included - is absorbed by `dsq_relation` on the
nose, and **no commutativity is used for that step**.  Wave 68's handle surgery needed its
inserted factor to be central; §3 supplies `Commute` instead, and
`cfour_prod_map_update` / `cfour_handleWord_update` are the weakened restatements.

## 5.  The knobs, and where the difficulty actually is (module §5)

What a dressing correction taken **inside `gamma_2`** buys, slot by slot:

| slot | knob | name |
| --- | --- | --- |
| `sigma` | `commP c (m 1)` | `cfour_dress_zero` |
| `x0` | `commP (m 0) c` | `cfour_dress_one` |
| `x1` | `c^2 * commP c (m 2)` | `cfour_dress_two` |

The `x0`-slot's **fourth power buys nothing** (`cfour_pow_four_dress`: both `c^4` and the
`cfour_pow_four_mul` defect die for `c` in `Y`), and the triple bracket buys nothing either
(`cfour_triple_dress_zero`).  Note the asymmetry: `x1` is the only slot of the relator carrying
a square, so it is the only source of squares, and its square arrives **bundled** with a bracket
against `m 2`.

**ANALYSIS, NOT COMMITTED** - none of the following is formalised; it is recorded because it is
what a class-four run should attack next.  In the graded layer `gamma_3/gamma_4`, which for the
free pro-2 group on `V = G/gamma_2` decomposes as `V^[4] (+) (Lambda^2 V)^[2] (+) L_3(V)`:

* **The fourth-power obstruction cancels.**  A wave-68-shaped dressing has
  `A = u^{nu'(v)} v^{nu'(u)} w^{-2 nu'(u) nu'(v)}`, and its `A^4` term contributes
  `(u^4)^{nu'(v)} (v^4)^{nu'(u)}`.  Writing `u^2 = c w^{2 nu'(u)}` and `v^2 = d w^{2 nu'(v)}`
  with `c, d` of exactly trivial rows, each handle letter contributes one copy of `w^4` to the
  power `nu'(u) nu'(v)`; the two copies cancel because `w^4` has order two.  So a class-four run
  is **not** blocked by `dsqSigma_pow_four_not_mem_twoCentralSeries_four`.  Wave 68's §10 is
  correct that the fourth power cannot be *discarded from the relator*; the present point is
  that its contribution to the *defect* cancels between the two handle letters.  Those are
  different claims and it is easy to conflate them.
* **The delicate point is the `x1`-bundle.**  The squares a class-four witness needs are only
  available together with a bracket against `x1`, and `x1` is not in the span of the other frame
  slots modulo `gamma_2` (the other slots span `sigma, x0, u_i, v_i`).  The apparent shortfall is
  repaired by Jacobi: `⁅⁅c, x1⁆, g⁆` re-expands into brackets whose outer slot is not `x1` -
  except in the direction `⁅⁅x1, g⁆, x1⁆`, which is instead reached by a correction whose square
  part involves `x1`.  Such a correction exists at **every** selected marking, because the
  `x1`-coordinate functional is never in the span of `lambda` and `nu'` modulo 2: killing `x0`
  forces the `lambda`-coefficient to vanish (`lambda(x0) = 1`), and then `nu'(sigma) = 1`
  forces the other.
* Consequently the honest expectation is that **class four is true**, by a witness that is wave
  68's dressing corrected by an explicit `gamma_2`-valued, exactly-row-trivial tuple.  Nothing
  here is a proof, and no negative result is claimed anywhere in this wave.

What is missing to formalise the above is a graded-layer decomposition of `gamma_3/gamma_4`
**on the tower**.  The tree has this kind of material only on slices today
(`GradedStageFour*`, `GradedFive*`), and building the tower version is the natural W70 ticket.

## 6.  The obligation, exactly (module §6)

* **`cfour_supply_iff`**: `SqClassClearingSupply h 4` iff at every selected marking and handle
  some admissible dressing makes `sqRelWord` **equal to 1** in `Q4`.  This moves the residual
  into the quotient where §1 to §5 live.
* **`cfour_supply_of_eichDefect`**: the entire obligation is `cfourEichDefect nu' j = 1`.
* `ClassFourResidual h` (`forall k, 5 <= k -> ...`) and `cfour_residual_of_classFour`: the
  remainder, stated honestly.  The class-four instance enters as a **hypothesis**, so this wave
  asserts no new equivalence with `SqLamMarkTransitivity`; `bridgeFinal_residual_iff` remains the
  standing statement.

## 7.  Verification record

* The shared olean cache does **not** contain wave 68's `GradedBridge.olean`, so the bare
  `lake env lean` invocation cannot run from the worktree root; verification of record was done
  through the standing full-mirror harness, which exists for exactly this.
* `scripts/mirror.sh sweep` (5753 artifacts), then
  `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedBridge` (regenerated clean, 54 pins, std-3),
  then `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedClassFour`, then
  `scripts/mirror.sh check GQ2/Dyadic/SqCore/GradedClassFour.lean` - clean, in that order.
* Axiom pins: 59 `#print axioms`, one per declaration, every declaration
  `[propext, Classical.choice, Quot.sound]` or
  a subset (`cfour_comm_self`, `cfour_comm_one`, `cfour_one_comm`, `cfour_commute_of_comm` are
  `[propext]` only; the two list-surgery lemmas are `[propext, Quot.sound]`).
* Imports added: `GQ2.Dyadic.SqCore.GradedBridge` only.
* Independent restatement check (scratch, not committed): the fully spelled-out
  `SqClassClearingSupply h 4` - with `twoCentralSeries (DSq h) 4` written out and no definition
  hiding anything - is discharged by `cfour_supply_of_eichDefect` from a fully spelled-out
  Eichler-defect hypothesis; `cfour_sqWord` typechecks against `sqWord` written out as
  `(conjP x s)^-1 (x^3)^-1 y^2 commP y (conjP y s)`; and `cfour_commutator_lambdaTwo` typechecks
  against the raw `v^-1 w^-1 v w in gamma_4`.
* Base `ee7b25dc`; lane branch `claude/w69-class4`.
