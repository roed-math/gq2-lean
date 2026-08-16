# W87-FIVE: the class-five rung is climbed

Lane W87-FIVE, worktree `claude/w87-five`, based on `1541635f`, shared cache at the wave-86
umbrella (4376 jobs).  Verification of record: `scripts/mirror.sh` (sweep, gen, check).
**No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/MpcFive.lean`, declaration prefix `mpcFv` (namespace
`GQ2.Dyadic.Instances.MpcFv`), **not registered in `GQ2.lean`** (housekeeping owns that).  No
existing module was edited.

---

## 1.  The headline

**The class-five rung of the `M6` ladder is climbed.**  `mpcFv_nonempty_five` proves
`(mpcWordSet 5).Nonempty`, with the explicit witness

    mpcFvW5 = (⁅D̄,B̄⁆,  ⁅D̄,B̄⁆·B̄⁴,  1,  B̄⁴·⁅B̄², D̄⁆)

(`mpcFv_w5_mem`).  So the residue of `MpcPivShift 2` starts at class **six**, not five, and wave
86's open question ("is there a class-four solution whose defect lies in the `𝔽₂`-subspace
`mpcLadReach 3`?") is answered **yes**, at the wave-84 witness's own orbit.

The route was ticket T1 then T2, both discharged:

1. The three remaining factors of `mWord` at class five (§1-§3 of the module).
2. The class-five defect in closed form, general (`mpcFv_mWord_five`) and on `D_M 2 0`
   (`mpcFv_defect_five`).
3. The defect of the class-four witness, three central involutions (`mpcFv_witness_defect`).
4. Outcome **(a)** of T2: membership, by an explicit reachable move.

**`MpcPivShift 2` is still open.**  This lane neither proved nor refuted it, and makes no
negative claim of any kind.

## 2.  The scope of the positive claim

`mpcWordSet 5` is the class-five solution set of the **ansatz**: the fixed shape
`(Ā·B̄⁻⁴·s, B̄·t, B̄²·C̄₀·m, D̄·n)` with corrections in `mpcWordCorr` / `mpcWordCorrC`.  Its
nonemptiness is one rung of `mpcLad_shift_of_exists_supply`, whose hypothesis is supply at
**every** class from three up; one class does not produce `MpcPivShift 2`.

The W86-HOUSE ansatz-scoping discipline is the mirror image of this and stands unchanged: an
**empty** `mpcWordSet k` would refute the ANSATZ and not `MpcPivShift 2`, because the ansatz is
not proved exhaustive among the markings `mpcOrb_shift_iff_marking` quantifies over.  Nothing in
this lane needed that discipline in the negative direction, since nothing negative was proved; it
is recorded in `mpcFv_nonempty_five`'s docstring in the positive form, a nonempty rung being a
statement about the ansatz too.

## 3.  The three factors (§1-§3 of the module)

Each is the class-four lemma of `MpcBuild.lean` times an explicit product of central corrections,
and every extra term dies at class four for one reason: `⁅Y,Y⁆ = 1` in `Q₄`, whereas in `Q₅` it
is only central.  Throughout, `Y = λ₂/λ₅`, `L = λ₃/λ₅`, `Z = λ₄/λ₅`.

⭐ `mpcFv_sq_letA` (the `Ā`-letter square, where `z = (B̄⁴)⁻¹` is an `L`-element and no longer
central):

    (p·z·σ)² = p²·(σ²·⁅σ,p⁆)·(z²·⁅z,p⁆) .

⭐ `mpcFv_comm_letAB`:

    ⁅p·z·σ, q·τ⁆ = ⁅p,q⁆·(⁅p,τ⁆·⁅σ,q⁆)·(⁅σ,τ⁆·⁅z,q⁆·⁅⁅p,q⁆,σ⁆·⁅⁅p,q⁆,τ⁆) .

⭐ `mpcFv_comm_letCD`:

    ⁅q²·r·μ, w·ν⁆ = ⁅r,w⁆·(⁅q,w⁆²·⁅⁅q,w⁆,q⁆·⁅r,ν⁆·⁅μ,w⁆)
                         ·(⁅q²,ν⁆·⁅μ,ν⁆·⁅⁅q²,w⁆,r⁆·⁅⁅r,w⁆,μ⁆·⁅⁅r,w⁆,ν⁆) .

The fourth factor, the pivot letter's fourth power, is wave 86's `mpcLad_pow_letC_five` and was
consumed as it stands.  The supporting class-five layer calculus is in §0 of the module.

## 4.  The assembly, and why it is free (§4)

⭐⭐⭐ `mpcFv_mWord_five`, the analogue of `mpcBld_mWord_four` one class up:

    mWord 2 (p·z·σ) (q·τ) (q²·r·μ) (w·ν) = mWord 2 p q r w · (E₁·E₂·E₃·E₄)

with the four corrections read off §3 above.  **The assembly costs nothing**, and the reason is
worth having in the record: every correction lies in `L`, `L` is abelian (because `L ⊆ Y` and
`⁅Y,L⁆ = 1`), `L` commutes with `Y`, and the three marked parts a correction has to pass are
`⁅p,q⁆ ∈ Y`, `r⁴ ∈ L` and `⁅r,w⁆ ∈ Y`.  So no commutator is incurred while collecting.  One class
down the same statement is free for the cruder reason that all four corrections are central.

**A correction to the W86-LADDER5 note.**  Its §6 hand derivation says the class-five defect is
"a product of central brackets including `⁅q⁴,p⁆`, `⁅r,q²⁆²` and the commutators incurred while
reordering".  The first two terms are right (see §5).  The third phrase is not: **no commutator
is incurred while reordering**, by the paragraph above.  The third survivor is `⁅⁅B̄²,D̄⁆, C̄₀⁆`,
and it is a term of the `C̄₀`/`D̄` bracket, not a reordering cost.  The hand derivation's headline
claim, that all `λ₃`-valued terms cancel and the residue is central, is correct **at the witness**
and is now formalized; it is **not** a statement about the general defect, which is only
`L`-valued (`mpcFv_mWord_five`).  It holds at the witness because the witness is a class-four
solution and so its defect already lies in `λ₄`.

## 5.  The witness's defect (§5)

⭐⭐⭐ `mpcFv_witness_defect`.  At `s = t = ⁅D̄,B̄⁆`, `m = n = 1`, in `Q₅`:

    ⁅B̄⁴, Ā⁆ · ⁅C̄₀, B̄²⁆² · ⁅⁅B̄², D̄⁆, C̄₀⁆ ,

three central involutions.  The three cancelling `λ₃`-valued pairs are the two `Ā`-brackets
against `W = ⁅D̄,B̄⁆`, the `W`-square against `⁅B̄,D̄⁆²`, and `⁅W, B̄⁆` against `⁅⁅B̄,D̄⁆, B̄⁆`.

Of wave 86's two predicted terms (`B̄⁸` and `⁅C̄₀,B̄²⁆²`, both present already at `m = 1`), only
the second survives: `B̄⁸` cancels against the head letter's `z² = ((B̄⁴)⁻¹)²`, the same central
involution.  The other two survivors come from factors wave 86 did not compute.

`mpcFv_defect_five` is the general statement this specialises, the analogue of
`mpcBld_defect_four`: the ansatz's core word modulo `λ₅` is a twenty-two-term product in the
marked generators and the four corrections.

## 6.  The decision (§6)

The move is read straight off the three survivors.  `mpcBldIncr`'s `B̄`-slot buys `⁅Ā, u⁆` and its
`D̄`-slot buys `⁅C̄₀, v⁆`, so take

* `us = 1`, `ut = B̄⁴`, `um = 1`, `un = B̄⁴·⁅B̄², D̄⁆`  (`mpcFvUt`, `mpcFvUn`, `mpcFv_move`),

using `⁅Ā, B̄⁴⁆ = ⁅B̄⁴, Ā⁆`, `⁅C̄₀, B̄⁴⁆ = ⁅C̄₀, B̄²⁆²` (`mpcFv_commP_pow_four_right`) and
`⁅C̄₀, ⁅B̄²,D̄⁆⁆ = ⁅⁅B̄²,D̄⁆, C̄₀⁆`.  The six factors are central involutions and pair off
(`mpcFv_supply_kill`).  The head and pivot slots are left alone.

Both corrections are legal, which is the one arithmetic input: they lie in `λ₃`, and they are
χ-trivial because `χ_M(B̄) = -1` has order two, so `χ_M(B̄⁴) = 1` (`mpcFv_chi_b4`), and every
bracket is χ-trivial (`mpcBld_chi_commP`).  `um = 1` is trivially row-invisible, so the pivot
slot's extra `mpcWordCorrC` condition costs nothing.

Then `mpcFv_supply_witness : MpcLadSupply 3 mpcLadW4` and, through wave 86's
`mpcLad_nonempty_five_iff`, `mpcFv_nonempty_five`.

**Wave 86's structural gap was not needed.**  The orbit space of `mpcWordSet (j+1)` under
`λ_j`-moves is still not shown to be a point; the class-five rung was hit inside the wave-84
witness's own orbit, so the `∃ p` of `mpcLad_nonempty_iff` was discharged by exhibiting one `p`.
The gap will matter again the moment a rung has to be shown **empty**.

## 7.  Axiom pins

Per declaration, in the module's §7 and reproduced by `mirror.sh gen`.  Forty-eight of the
forty-nine public declarations are on the standard three (`propext`, `Classical.choice`,
`Quot.sound`); the forty-ninth, `mpcFv_commP_self`, is on `propext` alone, a strict subset (it is
a `group`-closed identity in an abstract group and touches no quotient).  **This lane introduces
no axiom.**

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 8.  What is next

1. **Class six.**  `mpcLad_nonempty_iff 4` is the next rung: is there a class-five solution whose
   defect lies in `mpcLadReach 4`?  `mpcFvW5` is the starting point, and its class-six defect
   needs the class-six analogue of §3-§4, where `q⁸` stops being central and `p⁴` sinks a further
   layer.  Whether that computation stays this tractable is not known; §0's calculus is written
   at `5` throughout and would need re-deriving.
2. **The orbit space** remains the one structural gap in the engine (wave 86 §3).  It was not
   needed here and will be needed for any emptiness claim.
3. **Housekeeping**: `MpcFive.lean` needs registering in `GQ2.lean`, as does `MpcLadder.lean` if
   wave 86's item is still open.
4. **The general defect is only `L`-valued.**  §4 of the module records this: at class four the
   defect is central and a rung is one `𝔽₂`-linear equation, and that cheap reading does not
   lift.  What restores linearity is `mpcLad_defect_orbit`, a statement about increments and not
   about defects, and a future wave should not conflate the two.
