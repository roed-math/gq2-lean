# W65-HFAM: what `Hfam` is after this wave

Wave 65, Fable lane, against `bc37cbba`.  Working tree `claude/w65-hfam`.  The ticket held
for Fable across eleven Opus-only waves: the even route's one remaining supply, per branch,

    Hfam : forall k >= 3, forall T : Tuple (stage word, table) (G_K(2), chi_cyc) k,
             exists F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F.

New modules: `GQ2/Dyadic/Instances/EvenFamilyConstruct.lean` (942 lines) and
`GQ2/Dyadic/Instances/EvenFamilyStatus.lean` (475 lines).  No committed file was edited.

## Verdict, in one sentence

`Hfam` is **constructed on both presented cores at every stage tuple** (census-free, std-3),
its relator-kill conjunct is **a theorem everywhere** and so leaves the route's statement of
demand, and at every real field it is **proved equivalent to the even oriented equivalence
itself** over the two arithmetic binders, so the supply the campaign has carried is not an
input to the even classification: it *is* the even classification, restated one station
earlier, and the residual open question is exactly the endpoint, now in a named arithmetic
form (twisted-cocycle mod-2 surjectivity).

## 1. The relator kill is free (`EvenFamilyConstruct` sections 1, 2)

The even relator words close in the word-lift group `Z_2 x| Z_2^x` at their value tables for
*every* offset vector: that is precisely `isLabuteOrientationDatumN_nUnit` and
`..M_mUnit` (committed) plus the committed handle lemma
(`evenFam_{n,m}RelWord_wordLift`).  Consequently, by the clone of the L kill,

* `evenFam_relatorKill{N,M}`: **every** derivation family over an even stage tuple kills the
  relator; and
* `evenFam_exists_kill_iff_nonempty{N,M}`: `Hfam`'s inner pair collapses to
  `Nonempty (EvenKernelDerivationFamily T)`.

The kill is stated once, generically, for any word datum with a universally closed table
(`evenFam_word_mem_derivKer`, `evenFam_relatorKill_of_univ`).

## 2. The model cores satisfy `Hfam` outright (`EvenFamilyConstruct` sections 3 to 5)

`evenFam_modelHfam{N,M}` (std-3, census-free): for every `alpha >= 2`, `h`, every level
`k >= 3` and **every** stage tuple of the even word data over `D_{N,M}(alpha, h)` itself, the
family exists and kills the relator.  This is `Hfam`'s statement verbatim with the field
carrier replaced by the model, and it is strictly stronger than the L template's model-side
artefact (`sqDerivModel` plus transport at the canonical marking only): the odd route has no
at-every-tuple analogue.

Ingredients, all new this wave:

* the model derivations `evenFamDerivModel{N,M}` at every precision and offset (the
  `sqDerivModel` clone; existence is the universal closure through `redWL`);
* a mod-2 parity calculus: the offset of any `WL`-valued continuous homomorphism reduces mod
  2 to an `F_2`-valued homomorphism factoring through the level-two quotient
  (`evenFamParityHom`, `evenFamParityLevel`, `evenFam_two_dvd_u_iff`);
* pure counting on the level-two quotient: with order `2^n` and a generating `n`-family,
  every slot carries a Kronecker dual functional (`evenFam_exists_levelTwo_dual`; an
  `(n-1)`-subfamily spans at most `2^(n-1)` classes, so the distinguished class survives to
  the quotient, which the span of its image identifies with `F_2`);
* the count itself is the committed Demushkin package: EV-1e plus the EV-1b rank identity
  give `|levelQuot D_{N,M}(alpha,h) 2| = 2^(4+2h)` (`evenFam_card_levelTwo_D{N,M}`,
  needing `alpha >= 2` exactly as EV-1e does).

## 3. `Hfam` at a field IS the endpoint (`EvenFamilyStatus`)

Transport: a field stage tuple pulls back along an oriented equivalence through the committed
`levelQuotCongr` (`evenFamTuplePullback`, generic in the word datum), and the model family
pushes forward (`evenFamFamilyTransport`).  Hence

* `evenFam_hfam{N,M}_of_orientedEquiv` (std-3): an oriented equivalence at `(alpha, h)`
  delivers `Hfam` at that depth, at every level and every tuple;

and, against the committed wave-58 endpoints, the **status re-cut** (all at exactly the
endpoint set `S`, matched element-wise in the same elaboration):

* `hfamFinal_status{N,M}_atDepth`: over `hrange` and the degree, single-depth `Hfam` iff
  `Nonempty (OrientedContinuousMulEquiv (chi{N,M} alpha h) chiCycKTwo)`;
* `hfamFinal_family{N,M}_iff_orientedEquiv`: the artefact's guarded `family` field iff the
  endpoint;
* `hfamFinal_carried{N,M}_iff_orientedEquiv`: the whole wave-58 artefact
  `EvenRouteFinalCarried{N,M} h K` iff the endpoint;
* `hfamFinal_not_family{N,M}_iff`: a refutation of `Hfam` at a field is a proof that the
  field is not oriented-equivalent to the even core.  The wave-56 failure mode (a published
  supply refuted by a sibling lane) is structurally impossible for `Hfam`.

Consequences for how the campaign should speak about the even route: "the even route closes
if `Hfam` holds" is true but no longer informative; the honest sentence is that **the even
route's remaining content is the even classification itself**, and everything between `Hfam`
and the endpoint (the climb, the shadow argument, the seam, the flips, the residual supply)
is now known to cost nothing and to lose nothing.

## 4. The residual, named and exactly costed

`EvenFamParitySupply` (generic in the even word datum): exact-fibre lifts and, per
non-twisted slot `i0 /= 1`, a continuous `chi`-twisted one-cocycle at precision `2^(k+1)`,
odd at the `i0` lift, even at the other non-twisted lifts.  Per tuple it is equivalent to the
family (`evenFam_nonempty_family_iff_paritySupply`; std-3 plus
`absGalQ2_isTopologicallyFinitelyGenerated`, exactly as the odd cocycle bridge), and

* `hfamFinal_parity{N,M}_iff_orientedEquiv`: the all-stage parity supply at a field iff the
  even classification there.

So the single open question of the even route, in its sharpest known form: **for `G_K(2)` at
an even field on a branch at depth `alpha`, produce, at every stage, twisted one-cocycles at
precision `2^(k+1)` whose mod-2 reductions realize the dual basis of the non-twisted slots.**
Mod 2 the twist dies, so this is surjectivity of `Z^1(chi mod 2^(k+1)) -> Z^1(F_2)` onto the
prescribed coordinates: higher Kummer theory at `K`.  On the model cores that surjectivity
holds because homomorphisms are free on the presentation (this wave); at a field it is
arithmetic.  Nothing else remains: word combinatorics, tail calculus, relator kill, seam,
and stratum bookkeeping are all closed.

## 5. Axiom discipline

Forty pins in `EvenFamilyConstruct.lean`: all std-3 or `[propext, Quot.sound]`.
Twenty-three pins in `EvenFamilyStatus.lean`: transport and hfam-from-endpoint at std-3;
parity bridge at std-3 plus the one finite-generation census axiom; every `hfamFinal` status
theorem at exactly the seven-element endpoint set `S`, printed side by side with
`evenRouteFinal_orientedEquiv{N,M}_atDepth` in the same run.  Nothing exceeds what the
committed endpoints already carry; no `markedRecipAt`.

## 6. What a successor wave should do

1. Attack `EvenFamParitySupply` at the three model fields, starting at `KSqrtNegTwo`
   (`N`, depth 2, `h = 0`): the mod-2 target there is `H^1(G_K(2), F_2)`, dimension 4, and
   the needed surjectivity is of `Z^1` twisted at precision `2^(k+1)` onto four prescribed
   dual functionals.  The repo's `FiniteTwoLocalReciprocityHigherKummer*` modules are the
   natural quarry; nothing in them is yet in this binder shape.
2. Alternatively, prove the classification at one even field by any route (as the odd lane
   did at degree one through the pivot seed); `hfamFinal_carried{N,M}_iff_orientedEquiv`
   then discharges the artefact there with no further even-route work.
3. Do not spend effort weakening `Hfam`: this wave shows there is no slack to remove.
