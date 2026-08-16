# W88-SIX: the class-six calculus, and where the kills live

Lane W88-SIX, worktree `claude/w88-six`, based on `ad8c2b62`, shared cache at the wave-87
umbrella (4379 jobs).  Verification of record: `scripts/mirror.sh` (sweep, gen, check).
**No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/MpcSix.lean`, declaration prefix `mpcSx` (namespace
`GQ2.Dyadic.Instances.MpcSx`), **not registered in `GQ2.lean`** (housekeeping owns that).  No
existing module was edited.  Eighty public declarations.

---

## 1.  The headline

**The class-six rung is not climbed, and it is not refuted.**  What lands is the machinery the
decision needs and the pattern the decision should follow:

1. the class-six defect of the `M6` ansatz **in closed form** (`mpcSx_mWord_six`), at trivial
   pivot correction;
2. the class-six defect of the wave-87 class-five witness (`mpcSx_w5_defect`);
3. **the marked carrier**, a uniform-in-class formalization of where both climbed kills live,
   with a shift-producer sharper than the one in the tree (`mpcSx_shift_of_marked_supply`).

`MpcPivShift 2` is untouched, and this lane makes **no negative claim of any kind**.  In
particular nothing here is evidence that the class-six rung is unreachable; the computation was
carried as far as the defect and stopped there, and wave 84 §5's control (a stalled walk proves
nothing) applies to that stop exactly as it does to any other.

## 2.  The scope of the positive claims

Two scopes, both load bearing.

**(a) The ansatz.**  `mpcWordSet k` is the class-`k` solution set of the **ansatz**, the fixed
shape `(Ā·B̄⁻⁴·s, B̄·t, B̄²·C̄₀·m, D̄·n)`.  The W86-HOUSE discipline stands unchanged and was not
needed in the negative direction here, nothing negative having been proved.
`mpcSx_shift_of_marked_supply` concludes `MpcPivShift 2` itself and not a statement about the
ansatz, which is sound because it is a **sufficient** condition; the exhaustiveness gap would
arise only for a converse, and no converse is claimed.

**(b) The pivot correction is trivial in §3 to §6.**  `mpcLad_pow_letC_five` and
`mpcFv_comm_letCD` carry a general `μ ∈ Y`; the class-six analogues `mpcSx_pow_letC` and
`mpcSx_comm_letCD` take `μ = 1`, and the assembly `mpcSx_mWord_six` inherits that.  This is not a
loss for the rung, because **both climbed witnesses have a trivial pivot correction**:
`mpcLadW4 = (W, W, 1, 1)` and `mpcFvW5 = (W, W·B̄⁴, 1, B̄⁴·⁅B̄²,D̄⁆)`, so the pivot slot has never
been used by the ladder.  The general-`μ` class-six statement is **open**, and nothing in this
lane is evidence about it either way.

## 3.  The class-six layer calculus (§0)

Four layers instead of class five's three, read in `Q₆`:

* `Y = λ₂/λ₆`, where every bracket lands;
* `L = λ₃/λ₆`, where `⁅Y, G⁆`, `Y²` and `p⁴` land;
* `M = λ₄/λ₆`, where `⁅L, G⁆`, `⁅Y, Y⁆`, `L²` and `p⁸` land;
* `Z = λ₅/λ₆`, central of exponent two, where `⁅M, G⁆`, `⁅L, Y⁆`, `M²` and `p¹⁶` land.

⭐⭐ The single fact every cancellation reduces to is `mpcSx_vanish_four`: **`⁅M, Y⁆ = 1` in
`Q₆`**, the instance `k = 4` of `cfive_commutator_lambdaTwo`.  It replaces class five's
`⁅L, Y⁆ = 1` one layer deeper, and the displacement is the whole difference between the two
waves: at class six the class-five proofs of `L`-abelianness and `⁅L, Y⁆ = 1` are unavailable, so
an `L`-valued factor is moved by paying an explicit `Z`-term instead of for free.  **This is a
statement about the available proof, not about `L`**: nothing in the lane asserts `⁅L, Y⁆ ≠ 1`,
and the scope is the one `GradedClassFive`'s own header uses for the same kind of claim.  A useful
consequence recorded on the way: `M` is abelian in `Q₆` (`mpcSx_mcomm'`).

Both hazards the wave-87 note predicted are confirmed and located.  `q⁸` stops being central: it
is an `M`-element (`mpcSx_pow_eight_mem`) and `q¹⁶` is what is central (`mpcSx_pow_sixteen_mem`).
And `p⁴` "sinks a layer" in the sense that matters: its index is still `λ₃` (`mpcSx_pow_four_mem`)
but `λ₃` is now two layers above the bottom instead of one, so the class-five collapses that used
`⁅λ₃, λ₂⁆ = 1` are gone.

## 4.  The four factors (§1 to §4)

Each is the class-five lemma times an explicit product of central involutions, and each new term
dies at class five for one reason, `⁅L, Y⁆ = 1`.

⭐ `mpcSx_sq_letA`:

    (p·z·σ)² = p²·(σ²·⁅σ,p⁆)·(z²·⁅z,p⁆)·(⁅σ,z⁆·⁅⁅σ,p⁆,z⁆·⁅⁅σ,p⁆,σ⁆) .

⭐ `mpcSx_comm_letAB`:

    ⁅p·z·σ, q·τ⁆ = ⁅p,q⁆·(⁅p,τ⁆·⁅σ,q⁆)·(⁅σ,τ⁆·⁅z,q⁆·⁅⁅p,q⁆,σ⁆·⁅⁅p,q⁆,τ⁆)
                        ·(⁅⁅p,τ⁆,z⁆·⁅z,τ⁆·⁅⁅p,τ⁆,σ⁆·⁅⁅p,q⁆,z⁆·⁅⁅σ,q⁆,τ⁆·⁅⁅p,τ⁆,⁅p,q⁆⁆) .

⭐ `mpcSx_pow_letC` (at `μ = 1`):

    (q²·r)⁴ = r⁴·(q⁸·⁅r,q²⁆²)·(⁅r²,q⁴⁆·⁅⁅r,q²⁆,r²⁆·⁅⁅r,q²⁆,q⁴⁆·⁅⁅r,q²⁆,r⁆²) .

⭐ `mpcSx_comm_letCD` (at `μ = 1`):

    ⁅q²·r, w·ν⁆ = ⁅r,w⁆·(⁅r,ν⁆·⁅q²,w⁆)·(⁅q²,ν⁆·⁅⁅q²,w⁆,r⁆·⁅⁅r,w⁆,ν⁆)
                       ·(⁅⁅r,ν⁆,⁅r,w⁆⁆·⁅⁅q²,w⁆,⁅r,w⁆⁆·⁅⁅q²,ν⁆,r⁆·⁅⁅q²,w⁆,ν⁆) .

**Three of these new terms are not bracket terms at all, they are reordering terms**: the last
term of `mpcSx_comm_letAB` and the first two of `mpcSx_comm_letCD`, each carried when the marked
bracket is moved to the front of its own factor past an `L`-term.  Class five performs those
moves for free; these identities price them.  **No claim is made that the price is nonzero** in
`D_M 2 0` or anywhere else; what is committed is that the class-five reason for dropping the
terms is a class-five fact.

The `C̄₀`/`D̄` statement also lists its two `L`-terms in the order `⁅r,ν⁆·⁅q²,w⁆`, the opposite of
`mpcFv_comm_letCD`'s; the exchange is free at class five and is priced here, so the order was
chosen to spend two swaps rather than three.

## 5.  The assembly, and why it is no longer free (§5)

⭐⭐⭐ `mpcSx_mWord_six`:

    mWord 2 (p·z·σ) (q·τ) (q²·r) (w·ν) = mWord 2 p q r w · (E₁·E₂·E₃·E₄·(C₁·C₂))

with `E₁` to `E₄` the four corrections above and

    C₁ = ⁅E₁, ⁅p,q⁆·r⁴·⁅r,w⁆⁆ ,   C₂ = ⁅E₂, r⁴·⁅r,w⁆⁆ .

**A correction to `MpcFive` §4, carefully scoped.**  That section records "the assembly costs
nothing", and the reason it gives is exact and exactly class-five: every correction lies in `L`,
`L` is abelian, `L` commutes with `Y`.  All three rest on `⁅L, Y⁆ = 1`, which is a class-five
fact, so **one class up the reason is unavailable** and the assembly has to be priced rather than
dropped.  The pivot correction `E₃` is `M`-valued and still passes free; the two `L`-valued
corrections `E₁` and `E₂` are priced at `C₁` and `C₂`.

Two things are claimed and a third is not.  Claimed: `C₁` and `C₂` are terms of **no letter**, so
a builder who computes the four factors of §4 and multiplies them has not computed the defect;
and the identity is exact with them present.  **Not claimed: that `C₁` and `C₂` are nonzero.**
They are `⁅L, Y⁆`-terms and land in `Z`; whether they vanish in `D_M 2 0` is not decided here and
was not needed.  The distinction is the one wave 70's `GradedClassFive` header draws for its own
"not surviving" group, and it is the distinction between "the class-five proof delivers nothing
here" and "the class-five conclusion is false here".

The wave-87 note's §8 item 4 anticipated the shape of this ("the general defect is only
`L`-valued") but not the consequence; the consequence is that the assembly itself acquires terms
that no letter contains.

## 6.  The witness's class-six defect (§6)

⭐⭐ `mpcSx_w5_defect`: the closed form of §5 transported to `D_M 2 0` and evaluated at
`mpcFvW5`, the marked relator dying on the way by `mpcOrb_relation`.

Unlike `mpcFv_witness_defect` this is **not** collapsed to a short product of survivors, and the
reason is structural rather than a matter of effort: at class five the witness's defect had to
lie in `λ₄/λ₅` because the witness was a class-four solution, so the collapse was forced and
three terms had to remain.  Here the a-priori bound is only `λ₅/λ₆`, which is the whole layer the
defect lives in, so nothing is forced and the cancellation has to be done by hand.  It was not
done.

## 7.  Where the kills live (§7): the wave's strategic content

Both climbed rungs used corrections of one shape.  Wave 85's class-four move is `(W, W, 1, 1)`
with `W = ⁅D̄, B̄⁆`; wave 87's class-five move is `(1, B̄⁴, 1, B̄⁴·⁅B̄², D̄⁆)`.  Every entry lies in

    mpcSxMarked = ⟨ B̄², all commutators ⟩ ,

and `mpcSx_w4_marked`, `mpcSx_ut_marked`, `mpcSx_un_marked` are the three checks.  Writing
`mpcSxKill j = mpcSxMarked ⊓ λ_j`, three theorems make that definition worth having.

⭐⭐ **(i) Marked and `j ≥ 2` layers down implies legal, uniform in `j`** (`mpcSx_kill_le_corr`).
The χ-half of legality is the one depth does not give, and this lane proves it does not:
`mpcSx_dmD_sq_not_corr` exhibits `D̄² ∈ λ₂` with `χ_M(D̄²) = mUnit 2 ^ 2 ≠ 1`
(`mpcSx_chi_dmD_sq`, from `mUnit 2 · (1 − 2²) = 1` and `9 ≠ 1` in `ℤ₂`).  So `λ₂ ⊄ mpcWordCorr`,
and the legality lemma has content.  This corrects a natural guess a continuation might make, that
the χ-condition is free once one is deep enough in the tower.

⭐⭐ **(ii) The marked supply never runs out** (`mpcSx_pow_mem_kill`): `B̄^(2^(k+1))` is marked and
lies `k+2` layers down, so `mpcSxKill j` carries a `B̄`-power at every class from two up.  This is
what a uniform-in-class argument needs and it is what the two climbed moves used.

⭐⭐⭐ **(iii) The narrowed shift-producer** (`mpcSx_shift_of_marked_supply`):

    (∀ j ≥ 3, ∃ p ∈ mpcWordSet (j+1), ∃ u v ∈ mpcSxKill j,
       mpcLadDefect p · ⁅Ā,u⁆ · ⁅C̄₀,v⁆ ∈ λ_{j+2})  →  MpcPivShift 2 .

Two narrowings against `mpcBld_shift_of_bracket_supply`, both easing the hypothesis: that one
quantifies over **every** `g ∈ λ_{j+1}` (its own W86-HOUSE block records the gap) and over
arbitrary corrections in `mpcWordCorr ⊓ λ_j`; this one asks for the defect of one solution and
for marked corrections only.  It is **not vacuous**: `mpcSx_marked_supply_three` is wave 87's own
move read in this form, so the criterion is met at `j = 3`.

**What §7 does not claim.**  It does not claim the defect lies in the marked span at every class,
and it does not claim the marked carrier is the whole story.  `MpcSxMarkedSix` is exactly the
class-six instance of the first question and it is open.

## 8.  The decision, as a named obstruction (§8)

Outcome (c) of the ticket.  Two Props, the second sufficient for the first:

* `MpcSxRungSix`: the class-six defect of `mpcFvW5` lies in `mpcLadReach 4`.  By
  `mpcLad_defect_orbit` this is the whole question inside `mpcFvW5`'s own `λ₄`-orbit, and its
  left-hand side is `mpcSx_w5_defect`'s closed form.
* `MpcSxMarkedSix`: §7's pattern at `j = 4`, the shape both climbed rungs took.  It is the
  narrower of the two in the strong sense: `mpcSx_rungSix_of_markedSix` derives the membership
  itself, through `mpcSx_marked_mem_reach`, and not only the supply.

`mpcSx_nonempty_six_of_rungSix` and `mpcSx_nonempty_six_of_markedSix` climb the rung from either.

Outcomes (a) and (b) were not reached.  For (b) the orbit-space gap would still bind: a
non-membership proved at `mpcFvW5` says nothing beyond that quadruple's own `λ₄`-orbit, so it
would not empty `mpcWordSet 6` and would not even refute the ansatz.

## 9.  Axiom pins

Per declaration, in the module's §9 and reproduced by `mirror.sh gen`.  **All eighty** public
declarations are on the standard three (`propext`, `Classical.choice`, `Quot.sound`);
there is no split this wave, unlike `MpcFive` §7 where `mpcFv_commP_self` came out on `propext`
alone.  **This lane introduces no axiom.**

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 10.  What is next

1. **The class-six decision.**  `MpcSxMarkedSix` first, since it is narrower and is the shape
   both climbed rungs took; `MpcSxRungSix` if that fails.  The work is the evaluation of
   `mpcSx_w5_defect`'s closed form at the witness, and the two things that make it easier than it
   looks are that `⁅z, B̄⁆ = 1` (powers of the same letter commute, which kills `E₂`'s `⁅z,q⁆`
   outright) and that the answer is known in advance to lie in `λ₅/λ₆`.
2. **General `μ`.**  §3 and §4 are at trivial pivot correction.  Lifting them is bounded work in
   the same style and would make `mpcSx_mWord_six` the full class-six analogue of
   `mpcFv_mWord_five`.  Nobody has needed it yet.
3. **The orbit space** remains the one structural gap in the engine (wave 86 §3), untouched here
   and needed for any emptiness claim.
4. **Housekeeping**: `MpcSix.lean` needs registering in `GQ2.lean`, as do `MpcFive.lean` and
   `MpcLadder.lean` if those items are still open.
5. **Do not read the assembly as free.**  §5 is the second time in three waves that a
   class-five convenience has been at issue at a neighbouring class (wave 87 corrected wave 86's
   reordering claim in the other direction, finding that no commutator is incurred at class
   five).  The general rule the two share: at class `c` the layer that commutes freely with `Y`
   is `λ_{c-2}`, and every statement that says "this commutes" should name the layer it is
   commuting in.  A continuation that wants `C₁ = C₂ = 1` has to prove it; it is not in the
   tree.
