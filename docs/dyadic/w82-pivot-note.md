# W82-PIVOT: the last clause on the five-row selector, and what it actually is

Lane W82-PIVOT, the `ε = true` pivot at `ℚ₂(√−10)`.  Produced against tree `a45bc557` on branch
`claude/w82-pivot`, shared cache at the wave-81 umbrella (4361 jobs).  Verification of record:
`scripts/mirror.sh` (sweep, check).  **No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/MpcPivot.lean`, declaration prefix `mpcPiv` (namespace
`GQ2.Dyadic.Instances.MpcPiv`).  Nothing else was touched; the module is **not yet registered in
`GQ2.lean`** (housekeeping owns that).

---

## 1.  The headline, in two halves

**The acceptance statement lands with no clause, and it is not the pivot.**

> `mpcPiv_genAsmBranch_sqrtNegTen (B) : ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0`
>
> carries nothing at all.  But `GenAsmBranch` does not pin `nuP` to the row's canonical marking,
> so this is a weaker object than every previous row's branch datum.  §4 below.

**The pivot itself does not land, and the lane says exactly what it is.**

> `mpcPiv_genAsmBranch_sqrtNegTen_of_shift (hshift : MpcPivShift 2) (B) : ...`
>
> is the same statement **at the row's own canonical marking `mpcNu 2 1 1`**, over one abstract
> move on `D_M 2 0` and nothing else: MC1 §5.3's family `M6`, `Y_c : C̄₀ ↦ B̄^{2c₁}·C̄₀`
> (`docs/dyadic/mc-design.md:211`), at parameter `c₁ = 1`.  No level, no `λ`-value, no arithmetic:
> those are all theorems now.

Three things fell out on the way, all of them corrections or sharpenings of the record.

## 2.  The `ker χ_M` image is now exact (wave 80 §3.3's missing identity)

Wave 80 §3.3 displayed

    ν'(ker χ_M) = ⟨ν'(C̄₀), 2·ν'(B̄)⟩          (α = 2)

and reported: "The displayed identity for `ν'(ker χ_M)` is not a theorem of this tree ... it needs
the **structure** of `ℤ₂ˣ` as `⟨−1⟩ × 5^{ℤ₂}`, not merely its generation."  Wave 81 landed that
structure (`mpcNorm_free_unique`).  The identity is now a theorem in **both** directions, at
**every** marking of `D_M 2 0`, with no level hypothesis:

* `mpcPiv_kerChi_le`: `χ_M(x) = 1 → ∃ m y, ν'(x) = m·ν'(C̄₀) + 2y·ν'(B̄)`;
* `mpcPiv_kerChi_ge`: every such combination is attained, by the explicit class `C̄₀^m·B̄^{2y}`.

The `⊆` half is §1's trap run at the marking's **own** pivot value instead of at the hardcoded
`4` of `mpcNorm_compSub`: the four generators then land in the span with no hypothesis at all
(`mpcPiv_gens_mem`), because `ν'(Ā) = −2·ν'(C̄₀)` is the frame relation `nu_dmA_eq`.  This is the
one place wave 81's freeness pays off twice: once to force the `(−1)`-exponent even, once to kill
the `(mUnit 2)`-exponent.

## 3.  The trapping route is exhausted structurally, not merely at one counterexample

From the identity, both rows in one line each.

* **`ε = false`** (`mpcPiv_pivot_of_even_dmB`): `ν'(B̄)` even puts `2·ν'(B̄)` in `4ℤ₂`, so a
  `ker χ_M` class of value `2` forces `v₂(ν'(C̄₀)) = 1`.  Wave 81's `mpcNorm_pivot_of_even_dmB`
  re-proved from the identity rather than from a bespoke trap.
* **`ε = true`** (`mpcPiv_kerChi_full_of_odd_dmB`): `ν'(B̄)` odd makes the right-hand side `2ℤ₂`
  **whatever `ν'(C̄₀)` is**.  Concretely: for every `z`, the class `B̄^{2y}` with `y = ν'(B̄)⁻¹z`
  already has `χ_M = 1` and `ν' = 2z`.

The second is the sharp form of wave 80 §3.3's hand counterexample `(−8, 1, 4, 1)`.  Wave 80
exhibited **one** marking on which the argument fails; this says the *technique* fails, for a
reason: the lower half of the level is satisfied by the `B̄`-column alone, so it can never
contradict anything on this row.  Equivalently, and this is the honest statement of the
obstruction:

> the image of `(χ_M, ν')` in `ℤ₂ˣ × ℤ₂` does not depend on `ν'(C̄₀)` once `ν'(B̄)` is odd and
> `ν'(C̄₀)` is even, because `ν'(C̄₀)·ℤ₂ ⊆ 2·ν'(B̄)·ℤ₂` outright.

So **no** argument that sees only the image can decide the pivot: not the level (either half),
not the two `λ`-values, not surjectivity, and not any refinement of the wave-80 trap.  That
closes the "sharper trap" direction for good.

## 4.  What the branch datum actually asserts (a correction to the interface reading)

`GenAsmBranch` (`GeneralAssembly.lean:207`) has four fields: `pres`, `hdeg`, `nuP`, `hnuP`,
`realization`.  The marking `nuP` is documented there as "the core's `Ztwo` marking (a
construction, not an obligation)", and `MarkedCoreRealization` (`LabuteInterface.lean:313`) has
exactly two fields, an equivalence `genAsmCore pres ≃ G_K(2)` and `ztwoIota ∘ nuP = ν_ur ∘ equiv`.
There is **no orientation clause and no normal-form clause**.  Hence, at a fixed row:

> `∃ G : GenAsmBranch K B, G.pres = S` says: `[K : ℚ₂] = S.degree`, and `genAsmCore S ≃ G_K(2)`
> as topological groups, and *some* surjective marking is `ν_ur`-compatible along it.

Given the equivalence, the marking is free: take `nuP := ztwoIota.symm ∘ (ν_ur ∘ e)`, which is
surjective by `mpcRow_surjective_nuPullbackM`.  That is `mpcPiv_genAsmBranch_sqrtNegTen`, and it
costs no clause and no `peripheralCyclotomicAction` (B8 enters only through the M3 scaling row of
`mpcCert_markedMatching`, i.e. only through *normalizing* a marking).

**This is a real deflation and it must not be over-read.**  What the untied datum drops is the
only thing the rest of the assembly uses the marking for:

* `GenAsmRowResidual.cand` is `WordCertificate ... G.nuP ...`, and the committed producer on this
  row is `Instances.MProcyclicCore.mpcWordCertificate α r p q`, which lives at `mpcNu α r p`;
* `exactLifting`, `stokes` and `determinant` are all stated at `G.nuP` as well;
* the selector's `Matches` conditions read the row's `(r, ε, η)` against the field's own `λ`-data.

So a lane that consumes `mpcPiv_genAsmBranch_sqrtNegTen` inherits an unserved `cand` block.  The
statement to build on is `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`.  Both are in the module, with
the warning in the second one's docstring.

## 5.  The pivot as an orbit question, with both implications

`fieldId_chosenEquivM_sqrtNegTen` is a `Nonempty.some`: nothing is known about it beyond
orientation.  So a pivot at *that* equivalence is either true at every oriented equivalence or
unprovable, and the target the branch datum actually consumes is the pivot at *some* oriented
equivalence.  The two are related by one fact, `mpcPiv_transport`: oriented equivalences form a
torsor under the χ-preserving automorphisms of `D_M α 0` (`e ↦ e.symm ∘ e'` is χ-preserving; and
`e ∘ Ψ` is oriented for χ-preserving `Ψ`, which is `mpcPiv_comp`).  Hence

> `mpcPiv_pivot_iff_orbit`:  (∃ oriented `e'`, `ν'_{e'}(C̄₀) = γ·2^r`)  ↔
> (∃ χ-preserving `Ψ`, `ν'_e(Ψ(C̄₀)) = γ·2^r`),
>
> for the chosen `e` and any `r`.  Both directions, no arithmetic, uniform in `α` and `K`.

This is the sharpest named statement the lane can make, and it converts the question completely:
the `√−10` pivot is **not** a fact about `ℚ₂(√−10)` that some finer norm computation will yield;
it is the question of whether the χ-preserving orbit of `C̄₀` reaches `ν`-valuation one.

## 6.  Which move, and why the two routes are not symmetric

Writing `b = ν'(B̄)`, `c = ν'(C̄₀)`, `d = ν'(D̄)` at the chosen equivalence (`a = −2c` is forced),
the χ-preserving automorphisms move `C̄₀` inside

    ν'(Ψ C̄₀) = γ₁·b + γ₂·c,      γ₁ even, γ₂ a unit,

the evenness of `γ₁` because `χ_M(B̄) = −1` and the unit `γ₂` because `Ψ` is invertible.  The tree
carries `γ₁ = 0` (that is M3 scaling, `mScalingHypothesis_zero`) and nothing else: M1, M2 and M5
all fix the `C̄₀`-row.  One nonzero `γ₁` is enough, and only one:

> `MpcPivShift α`: a χ-preserving automorphism with `ν'(Ψ C̄₀) = ν'(C̄₀) + 2·ν'(B̄)` at every
> marking.  `mpcPiv_orbit_of_shift` case-splits on the parity of `c/2`: if it is odd the chosen
> equivalence already has the pivot; if it is even, one application adds `2b` with `b` odd and
> lands on valuation exactly one.

That move is also **necessary**, not merely sufficient, and this is what makes the reduction
sharp.  `mpcPiv_orbit_shape` is `mpcPiv_kerChi_le` read at `Ψ(C̄₀)` (which lies in `ker χ_M`
because `Ψ` preserves `χ_M`): *every* χ-preserving automorphism moves the pivot row inside
`ν'(C̄₀)ℤ₂ + 2ν'(B̄)ℤ₂`.  And `mpcPiv_shift_necessary`: if the chosen marking misses the pivot
outright (`ν'(C̄₀) ∈ 4ℤ₂`) then any `Ψ` achieving it has an **odd** `B̄`-coefficient on its
`C̄₀`-row.  So the row lands **iff** the `M6` direction is available at some odd parameter: the
first summand above is M3 scaling, which the tree has and which cannot change a valuation.

`MpcPivShift` **is** MC1 §5.3's `M6` at `c₁ = 1` (`docs/dyadic/mc-design.md:211`,
`Y_c : C̄₀ ↦ B̄^{2c₁}·C̄₀`).  The tree's own ruling on it is negative and explicit
(`CoreMixM.lean` §7): `⟨M4, M6, M7⟩` are "structurally obstructed rather than merely unbuilt
(they are not symplectic, hence not reachable by any relator-preserving word automorphism), so no
widening of the generating set produces them."  A hand check agrees with the "not symplectic"
half: with `ω(Ā,B̄) = ω(C̄₀,D̄) = 1`, the abelianised `M6` (`C̄₀ ↦ C̄₀ + 2c₁B̄`, forced companion
`Ā ↦ Ā − 4c₁B̄` from `2Ā + 4C̄₀` fixed) has `ω(Ā', C̄₀') = 2c₁ ≠ 0`.  Note also that `mc-design`
§5.3's own text is in tension with this ruling ("they *are* in the stabilizer (verified by direct
isometry computation)"), and that the obstruction is a `ℤ₂`-level one: `M6` **is** symplectic mod
`2` (mod 2 it is the identity), and the `F₃`-level relator computation leaves `2Λ²` of slack
because the relator `Ā²[Ā,B̄]C̄₀^{2^α}[C̄₀,D̄]` is not in the commutator subgroup.  So the ruling is
plausible but not, on this tree, a proof.

**The fork this leaves is clean, and it is the whole remaining content of the row:**

* if `MpcPivShift 2` is **true**, the row lands at the canonical marking, via
  `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`, and `v₂(ν'(C̄₀))` is not an invariant;
* if it is **false** (the `CoreMixM` §7 ruling), then `v₂(ν'(C̄₀))` **is** an invariant of the
  field, wave 80's counterexample marking `(−8, 1, 4, 1)` is not realizable at `ℚ₂(√−10)`, and the
  pivot must be *computed*.  §3 says the computation cannot go through the image of `(χ_M, ν')`,
  so it has to see the relator: the natural candidate is the `ℤ/4`-valued quadratic refinement
  `Q(ν') = b² + 2d² + 2bc − cd` of the Demushkin form, whose class mod `4` is invariant under M1,
  M2, M3 and M5 (checked by hand at the canonical marking: `5 + 12k + 4k²`, `5 + 4e + 8e²`,
  `3 + 2γ`, `5 − 24k + 16k²`, all `≡ 1 mod 4`) and is `1` exactly when the pivot holds and `3`
  when it fails.  Whether `Q mod 4` has an arithmetic reading at `K` (a Hilbert-symbol or
  Weil-index invariant of the unramified class) is the next question, and it is *not* one this
  lane can answer.

### The certificate route, closed

The ticket's other candidate was to run the certificate machinery backwards.  It gives nothing,
for two reasons, both checkable in the tree:

1. **There is no committed certificate to run backwards.**  The only producers of
   `MarkedCoreCertificateMpc` at a field are `mpcCert_marked_matching_certificate_KTwoMpc` and
   `mpcCert_marked_matching_certificate_Mpc`, and both consume `MpcMarkedData`, i.e. the pivot.
   `mpcCert_isEmpty_certificateM_of_level` rules out the compact `M` certificate at `B.r = 1`.
2. **Even given one, it pins nothing new.**  A certificate says `ν'(u(C̄₀)) = 2^r` for a
   χ-preserving `u`; since `C̄₀ ∈ ker χ_M` already, the level gives `ν'(C̄₀) ∈ 2^rℤ₂` and §3 says
   the orbit of `C̄₀` inside `ker χ_M` is exactly what is unknown.  The committed necessity
   directions (`mpcCert_level_le_of_pivot`, `mpcCert_level_le_of_certificate`) both land on
   `B.r ≤ r`, never on `v₂(ν'(C̄₀))`.

## 7.  The five-row scoreboard

| row | field | `pres` | branch datum over the bundles alone | at the canonical marking? |
| --- | --- | --- | --- | --- |
| 1 | `ℚ₂(√−2)` | `.N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | yes |
| 2 | `ℚ₂(√2)` | `.M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | yes |
| 3 | `ℚ₂(√5)` | `.M0 2 0` | **no**: `fieldUni_TwoIsUniformizer KSqrtFive` | (yes, once it lands) |
| 4 | `ℚ₂(√10)` | `.Mpc 2 1 false .one 0` | `mpcNorm_genAsmBranch_sqrtTen` | yes |
| 5 | `ℚ₂(√−10)` | `.Mpc 2 1 true .one 0` | `mpcPiv_genAsmBranch_sqrtNegTen` | **no**: needs `MpcPivShift 2` |

So four of the five rows carry a branch datum at the row's canonical marking over the bundles
alone; row 3 carries none (unchanged by this lane: it wants the unramifiedness of `ℚ₂(√5)` in the
repository's norm-only idiom); and row 5 now carries an untied one unconditionally plus a tied one
over a single abstract move.

### What the flagship still needs

Unchanged from wave 81 §6, and this lane touches none of it.  Per row, given the branch datum `G`
and an oriented tame quotient `T`, `GenAsmRowResidual G T` has four fields, of which wave 80 wired
`determinant` (`mpcRow_genAsmRowResidual_of_counting`).  The three record blocks left are

1. `exactLifting`: ASK ledger field 3 at `G_K`;
2. `stokes`: ASK ledger field 4 at `G_K`;
3. `cand`: the candidate-side `WordCertificate` over the row's own slot (the surviving Gauss-`Z`
   obligation, `SqrtNeg2.PilotDet`, lives here).

To which this lane adds one line of fine print: all three are stated **at `G.nuP`**, so they are
served by the committed per-row producers only for a branch datum at the row's canonical marking.

## 8.  Axiom pins

Per declaration, recorded in the module's §7.  Three sets, all already committed; **this lane
introduces no axiom**.

* **Standard three** on §1 through §5 and on `mpcPiv_rows_sqrtNegTen`.  So the exact `ker χ_M`
  image, both row criteria, the orbit equivalence and the shift criterion are axiom-free.
* **Plus the even route's endpoint set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on `mpcPiv_genAsmBranch_sqrtNegTen`, through
  `fieldId_chosenEquivM_sqrtNegTen`.
* **Plus `peripheralCyclotomicAction`** on `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`: wave 81's
  set on `mpcNorm_genAsmBranch_sqrtNegTen_of_pivot`, exactly.  The gap between the last two
  bullets is itself a fact worth keeping: B8 enters the row only through the M3 scaling row of
  `mpcCert_markedMatching`, that is, only through normalizing the marking.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 9.  What is next

1. **Decide `MpcPivShift 2`** (§6).  It is a statement about `D_M 2 0` alone, so it is a
   `MarkedCore` ticket, not a `Fields` one, and it is the whole of the `√−10` row.  Two
   sub-tickets, either of which settles it: (a) build `M6` at `c₁ = 1` by the `dmRealizesWide`
   recipe (a marking `m : Fin 4 → D_M 2 0` with `mRelWord 2 m = 1` and unipotent-mod-2 image
   system, then `profinite_hopfian`); (b) prove the `CoreMixM` §7 ruling, i.e. exhibit an
   automorphism invariant that `M6` moves.  The `ℤ/4`-valued `Q = b² + 2d² + 2bc − cd` of §6 is
   the candidate for (b), and proving it is invariant is the same kind of relator computation.
2. **If (b) wins**, the row needs an arithmetic reading of `Q mod 4` at `ℚ₂(√−10)`, and §3 says
   it cannot come from the norm group alone.  This is the only place in the five rows where the
   remaining mathematics is not already localized.
3. **`fieldUni_TwoIsUniformizer KSqrtFive`** (row 3), still open and unchanged by this lane.
4. **Register `GQ2/Dyadic/Instances/MpcPivot.lean`** in `GQ2.lean` (housekeeping), together with
   wave 81's `MpcNormValues.lean` if that is still pending.
5. **Do not build on `mpcPiv_genAsmBranch_sqrtNegTen`** without reading §4.
