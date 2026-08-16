# W86-LADDER5: the converse settled, a rung given its exact shape, the first class-five term

Lane W86-LADDER5, worktree `claude/w86-ladder5`, based on `f0de6ad5`, shared cache at the
wave-85 umbrella (4373 jobs).  Verification of record: `scripts/mirror.sh` (sweep, gen, check).
**No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/MpcLadder.lean`, declaration prefix `mpcLad` (namespace
`GQ2.Dyadic.Instances.MpcLad`), **not registered in `GQ2.lean`** (housekeeping owns that).  No
existing module was edited.

---

## 1.  The headline

**`MpcPivShift 2` is still open.  This lane neither built `M6` nor refuted it.**  What moved:

1. **Wave 85's open question is answered, and the answer is yes.**  Wave 85 §9.2 asked whether a
   class-`(j+2)` solution has to be a `λ_j`-move away from a class-`(j+1)` one, and called it
   "what would turn the engine into a decision procedure".  It has to be, because it already is
   one: `mpcWordSet` is antitone, so a class-`(j+2)` solution *is* a class-`(j+1)` solution, and
   the identity move has trivial increment.  Hence `mpcLad_nonempty_iff`, an **iff** at every
   class.

2. **The one-step supply hypothesis loses its `∀`.**  `mpcLad_shift_of_exists_supply` needs
   supply at *one* class-`(j+1)` solution per class, where wave 85's
   `mpcBld_shift_of_full_supply` asked for it at every one.

3. **The engine gains a refutation route.**  `mpcLad_eq_empty_of_no_supply`: a supply failure
   proved over the whole class-`(j+1)` solution set proves `mpcWordSet (j+2) = ∅`, which is the
   only shape wave 84 admits for a negative claim.  [W86-HOUSE scope: a negative claim about the
   ANSATZ.  An empty `mpcWordSet` does not by itself refute `MpcPivShift 2`; that step needs the
   ansatz to be exhaustive among the markings `mpcOrb_shift_iff_marking` quantifies over, which
   is not proved.  Wave 84's admissibility naming carried the same inversion.  See
   `docs/dyadic/w86-house-note.md`.]

4. **A rung has an exact shape, not just an exact price.**  The increment map is a homomorphism
   (`mpcLad_incr_hom`) into the central involutive layer (`mpcLad_incr_mem_zLayer`), so the
   reachable increments are an `𝔽₂`-subspace `mpcLadReachSub` that does not move along the orbit
   (`mpcLad_reach_base_indep`), and the defects of a `λ_j`-orbit are exactly one coset of it
   (`mpcLad_defect_orbit`).

5. **The first exact class-five term of the `M6` defect** (`mpcLad_pow_letC_five`), with a
   correction to what wave 85's class-four calculus lifts.

## 2.  The converse, and what it does and does not buy (§2 of the module)

⭐⭐⭐ `mpcLad_nonempty_iff`:

    (mpcWordSet (j+2)).Nonempty  ↔  ∃ p ∈ mpcWordSet (j+1), MpcLadSupply j p

where `MpcLadSupply j p` says some reachable `λ_j`-move of the four corrections kills `p`'s
defect into `λ_{j+2}`.  The backward direction is wave 85's `mpcBld_step`.  The forward
direction is `mpcLad_supply_of_mem`, whose whole content is `mpcLad_incr_one`: the identity move
has increment `1`.

**Read the triviality correctly.**  Wave 85's caution, as prose, reads "a class-`(j+2)` solution
need not be a `λ_j`-move away from a class-`(j+1)` one".  That sentence is false; what is true,
and is what the caution was protecting against, is the *other* half: a failed supply at one
chosen `p` is no evidence, because the witness may be a different `p`.  §2 puts the exact price
on that half.  `mpcLad_eq_empty_of_no_supply` needs the failure at **every** class-`(j+1)`
solution, and then and only then it is a proof of emptiness.

**What the converse does not buy.**  It does not reduce the `∃ p` to a distinguished `p`.  The
search is now exact and two-sided, but it is still a search over `mpcWordSet (j+1)`, and §3 says
precisely how much of that set one point sees.

## 3.  A rung's exact shape (§3)

Every factor of `mpcBldIncr` lands in `Z_{j+1} = λ_{j+1}/λ_{j+2}`, which is central of exponent
two in `Q_{j+2}` (`mpcLad_incr_mem_zLayer`).  On that layer:

⭐⭐⭐ `mpcLad_incr_hom`: for reachable moves, `Incr(u·u') = Incr(u)·Incr(u')` exactly.  The four
slots contribute a square and four brackets, and each is additive because its correction term is
either a bracket against a central element or a bracket of two `λ`-images that dies two layers
down.  No lower bound on `j` is needed: the `λ₂`-side conditions come free from the carriers
`mpcWordCorr` and `mpcWordCorrC`, which both sit inside `λ₂`.

Consequences, all in the module:

* `mpcLadReachSub j t n` is a genuine `Subgroup` of `λ_{j+1}/λ_{j+2}`, elementary abelian
  (`mpcLad_reach_sq`);
* `mpcLad_reach_base_indep`: rebasing `t` and `n` by a `λ_j`-move changes no increment, so the
  subgroup depends on the orbit and not on the representative;
* ⭐⭐⭐ `mpcLad_defect_orbit`: the defects reachable from `p` by `λ_j`-moves are exactly the coset
  `defect(p) · mpcLadReach j p.2.1 p.2.2.2`.

So: **within one `λ_j`-orbit a rung is a single `𝔽₂`-linear membership test.  Between orbits
nothing is claimed**, and that is where the remaining search lives.  The orbit space of
`mpcWordSet (j+1)` under `λ_j`-moves is not shown to be a point, and two orbits can in principle
carry different cosets; this lane has no example either way, and the honest reading is that the
`∃ p` of §2 cannot be reduced further by this argument.

## 4.  The first exact class-five term (§4), and one correction to wave 85

Wave 85's class-four calculus rests on two collapses that are exactly class-four facts: the
letter's `B̄⁻⁴` factor is central in `Q₄`, and a fourth power is central there.  In `Q₅` neither
holds: `p⁴` is only a `λ₃`-image (`cfive_pow_four_mem_lambdaThree`) and `p⁸` is what is central.
The class-five replacement for one of the four factors of `mWord` is computed here.

⭐⭐ `mpcLad_pow_letC_five`, in `Q₅`, for any `μ ∈ Y = λ₂/λ₅`:

    (q²·r·μ)⁴ = r⁴ · (q⁸ · μ⁴ · ⁅μ,r⁆² · ⁅r,q²⁆²)

All four extra factors are central of order dividing two, which is why `mpcBld_pow_letC` reads
`(q²·r·μ)⁴ = r⁴` one class down.  Two of them, `q⁸` and `⁅r,q²⁆²`, involve neither the correction
nor the `D̄`-letter: they come from the row shift `B̄²` alone and are therefore **present in the
class-four witness itself** (`m = 1`).  Transported to the `M6` `C̄₀`-letter on `D_M 2 0`
(`mpcLad_letC_pow_five`), the class-five reading of that factor is

    C̄₀⁴ · B̄⁸ · m⁴ · ⁅m, C̄₀⁆² · ⁅C̄₀, B̄²⁆² .

**The correction, stated precisely so it is not misread.**  Wave 85 §4 records that "the
row-shifted fourth power `(q²·r·μ)⁴` does not see the increment at all, uniformly in the class".
That claim is about `mpcBld_incr_pivot`, which is proved in `Q_{j+2}` for arbitrary `j`, and it
**stands**: a `λ_j`-factor on the `C̄₀`-letter still costs the fourth power nothing.  What does
not lift is the *absolute* statement `mpcBld_pow_letC`, a `Q₄` fact whose proof squares
`λ₂`-images into the central layer.  The two are easy to conflate and they are not the same
claim; `mpcLad_pow_letC_five` is the class-five form of the second, and the first needs no
repair.

The supporting class-five calculus is committed with it: `mpcLad_five_vanish` (`⁅λ₂, λ₃⁆` dies in
`Q₅`, which is `cfive_commutator_lambdaTwo` at `k = 3` read downstairs), `mpcLad_five_sq_split`,
`mpcLad_five_sq_drop`, `mpcLad_five_commP_sq_drop`.

## 5.  The class-five rung, named (§5)

`mpcLad_nonempty_five_iff`: `(mpcWordSet 5).Nonempty ↔ ∃ p ∈ mpcWordSet 4, MpcLadSupply 3 p`,
with the class-four solution set known nonempty (`mpcBld_nonempty_four`, witness `mpcLadW4`).
So the campaign's next question now has a name and a shape:

> **is there a class-four solution whose defect lies in the `𝔽₂`-subspace `mpcLadReach 3`?**

`mpcLad_five_empty_of_no_supply` is the negative half.  Neither answer is claimed here.

## 6.  What did not land, plainly

**Ticket T1 is only partly discharged.**  The class-five defect of the class-four witness is
**not** in closed form.  `mWord` has four factors; this lane computes one of them exactly (the
pivot fourth power, §4) and leaves the other three (`a²`, `⁅a,b⁆`, `⁅c,d⁆`) open.  A hand
derivation carried out in the lane suggests every `λ₃`-valued term cancels, as it must, and the
class-five defect is a product of central brackets including `⁅q⁴,p⁆`, `⁅r,q²⁆²` and the
commutators incurred while reordering; **none of that is formalized and none of it is claimed
here**.  Finishing it is the obvious next lane, and §4's calculus is what it needs.

**Ticket T3 does not apply.**  `M6` did not close and no rung was proved empty, so no
`mpcLad_shift : MpcPivShift 2` exists, the fifth row's clause-free tied branch datum was not
composed, and the scoreboard was not re-run.  Nothing in this lane changes any producer, binder
or axiom set, so the board would print unchanged.

## 7.  Axiom pins

Per declaration, in the module's §6 and reproduced by `mirror.sh gen`.  **All forty-nine public
declarations of `MpcLadder.lean` are on the standard three** (`propext`, `Classical.choice`,
`Quot.sound`).  **This lane introduces no axiom.**

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 8.  What is next

1. **The remaining three class-five factors.**  `a² = (p·z·σ)²` with `z = (q⁴)⁻¹` no longer
   central, `⁅a,b⁆`, and `⁅c,d⁆`.  §4's calculus (`mpcLad_five_*`) is the toolkit; each is the
   class-four proof with `Z` replaced by `λ₃` and a central residue collected.
2. **Then the class-five decision**, via `mpcLad_nonempty_five_iff`: compare the assembled defect
   against `mpcLadReach 3`.  Both outcomes are now usable, which they were not before this lane:
   a hit gives a class-five solution by `mpcBld_step`, and a proof that *no* class-four solution
   is hit gives `mpcWordSet 5 = ∅` by `mpcLad_five_empty_of_no_supply`.
3. **The orbit space is the one structural gap left in the engine.**  §3 reduces a rung to one
   linear test per `λ_j`-orbit.  Whether `mpcWordSet (j+1)` is a single orbit, or how many it
   has, is untouched, and it is what stands between the engine and a finite decision procedure.
4. **Housekeeping**: `MpcLadder.lean` needs registering in `GQ2.lean`, and wave 85 §7's two stale
   prose sites are still open (this lane edited neither).
