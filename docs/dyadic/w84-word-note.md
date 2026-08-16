# W84-WORD: the M6 identity, one equation and four rungs of its ladder

Lane W84-WORD, the last selector clause: decide `MpcPivShift 2`, the `M6` move
`C̄₀ ↦ B̄²·C̄₀` on `D_M 2 0`, which is the whole residue of the `ℚ₂(√−10)` row.  Produced
against tree `45f9c42d` on branch `claude/w84-word`, shared cache at the wave-83 umbrella
(4367 jobs).  Verification of record: `scripts/mirror.sh` (sweep, gen, check).  **No `lake`
command was run.**

One new module: `GQ2/Dyadic/Instances/MpcWord.lean`, declaration prefix `mpcWord` (namespace
`GQ2.Dyadic.Instances.MpcWord`).  Nothing else was touched; the module is **not yet registered
in `GQ2.lean`** (housekeeping owns that).

---

## 1.  The headline

**`MpcPivShift 2` is still open.  This lane neither built `M6` nor refuted it.**  What it did:

1. reduced the residue from a four-clause marking to **one word identity with no side
   conditions left that a builder has to think about** (`mpcWord_shift_of_word`);
2. proved that the identity is decided **at a finite class**: solvable at every class of the
   two-central tower implies solvable outright (`mpcWord_shift_of_forall_class`), so there is
   no inverse-limit step for an obstruction to hide in;
3. proved that **classes at most three cost nothing** (`mpcWord_mem_three`), so the residual
   starts at class four;
4. pushed the evidence, off-tree and exactly, from class three (wave 83's depth) to **class
   six**, *with calibration*, and found no obstruction;
5. **corrected the calibration story**: the class-by-class walk demonstrably produces false
   stalls, and this lane exhibits one on a move that is a theorem of the tree.  So the stalls
   wave 83 reported, and the one this lane's narrow ansatz produces at class six, carry no
   information.

The acceptance target of this lane, the tied `√−10` datum with no clause, is **not met**.  The
five-row scoreboard is unchanged from wave 83 (§7 below), re-run against the mirror.

## 2.  The residue is one equation (§1 to §3 of the module)

Wave 83's `mpcOrb_shift_iff_marking` charges a builder four clauses: the core-word relation,
topological generation, the four χ-values, and the `C̄₀`-row shift.  For the ansatz shape

    a = Ā·B̄⁻⁴·s,   b = B̄·t,   c = B̄²·C̄₀·m,   d = D̄·n

three of the four are free, and this lane discharges them:

* **generation** is the pro-2 Frattini criterion.  `mpcWordFrat` is the intersection of the
  index-two open normal subgroups; if `s, t, m, n` lie in it then all four letters are
  congruent to the marked generators modulo every such subgroup (`B̄⁴` and `B̄²` are squares),
  and `eq_top_of_forall_not_le_index_p` promotes that to `⊤` (`mpcWord_gen`);
* **the four χ-values** are `χ_M(B̄)^{±even} = 1` plus `χ_M(s) = χ_M(t) = χ_M(m) = χ_M(n) = 1`;
* **the row shift** is `2·ν'(B̄)` on the nose once `m` is invisible to every `ℤ₂`-character.

⭐ `mpcWord_shift_of_word`: with those hypotheses, the single identity

    mWord 2 (Ā·B̄⁻⁴·s) (B̄·t) (B̄²·C̄₀·m) (D̄·n) = 1

yields `MpcPivShift 2`, hence `mpcPiv_genAsmBranch_sqrtNegTen_of_shift` with no clause.  The
carrier is fed by the tower: `mpcWord_lambdaTwo_le_frat` says `λ₂ ≤ mpcWordFrat`, so a builder
may work with `twoCentralSeries (DM 2 0) 2` throughout and never mention index-two subgroups.

## 3.  The identity is decided at a finite class (§5, §6)

`mpcWordSet k` is the set of quadruples of corrections, in the two carriers
`mpcWordCorr = λ₂ ∩ ker χ_M` and `mpcWordCorrC = mpcWordCorr ∩ (row kernel)`, whose core-word
value lies in `twoCentralSeries (DM 2 0) k`.  Only the last clause sees `k`, so the family is
nested; every clause is closed; the correction space is compact.  With the tower separation
`⨅ k, twoCentralSeries (DM 2 0) k = ⊥` (`iInf_twoCentralSeries` through
`dm_topologicallyFinGen_zero` and `isProP_DM`) this gives

⭐ `mpcWord_shift_of_forall_class`: **if every class-`k` solution set is nonempty then
`MpcPivShift 2` holds.**

This is the W67-LIMIT template applied one functor over.  Read contrapositively it is the
useful direction for a refutation: **if `M6` is false then the ansatz already fails at some
finite class, in a finite 2-group.**  Nothing can be lost in the limit.

## 4.  The per-class extension record

### 4.1  Classes at most three: a theorem, and free

⭐ `mpcWord_mem_three`: *every* quadruple of `λ₂`-corrections lands in `λ₃`.  Modulo `λ₃` the
four letters are the marked generators times central involutions (`B̄⁴ ∈ λ₃` dies, `B̄²` and
each correction are central of order two), and `mpcWord_mWord_center` says central factors of
the right order drop out of `mWord`, so the word collapses onto `mpcOrb_relation`.  Hence
`mpcWord_nonempty_of_le_three`, and

⭐ `mpcWord_shift_of_forall_class_four`: the residue is the class-`k` solvability for `k ≥ 4`
alone.

### 4.2  Class four: the obstruction in closed form, and an explicit kill

Computing the ansatz modulo `λ₄` by hand (**not formalized**; every term below is a `λ₃`-class,
and `λ₃` is central modulo `λ₄`):

    mWord 2 a b c d  ≡  s²·[s,Ā]·[Ā,t]·[s,B̄]·[C̄₀,n]·[m,D̄]·[B̄,D̄]²·[[B̄,D̄],B̄]   (mod λ₄).

So the **class-four obstruction of the bare ansatz** (`s = t = m = n = 1`) is

    [B̄,D̄]² · [[B̄,D̄],B̄],

and since `[B̄,D̄]² ∈ λ₄` already, the live part is the single element `[[B̄,D̄],B̄]`.  It is
killed by

    s = t = [D̄,B̄] = commP D̄ B̄ = [B̄,D̄]⁻¹,   m = n = 1 :

`[s,B̄] = [[B̄,D̄],B̄]⁻¹` clears the defect, `[s,Ā] = [[B̄,D̄],Ā]⁻¹` is the new residue, and
`[Ā,t] = [[B̄,D̄],Ā]` clears that.  Note both handles are touched, exactly as wave 83 §9.1
predicted from the odd `[B̄,D̄]` exponent at `γ₃`.

**Verified independently** by exact `𝔽₂` linear algebra in the Magnus model (Jennings and
Zassenhaus: for `p = 2` the dimension subgroups are the two-central series, so `x ∈ λ_k` iff
`μ(x) − 1` lies in `I^k + (μ(R) − 1)`, and the test at truncation `k−1` is exact).  The bare
ansatz has residue `BBD + DBB`, which is precisely `μ([[B̄,D̄],B̄]) − 1`; with `s = t = [D̄,B̄]`
the residue is zero.  Scripts are throwaway, not part of the tree.

### 4.3  Classes five and six: no obstruction found

Carrying the class-four solution and solving each next rung exactly (the increments admissible
at class `k` are the elements of `λ_j`, `j ≤ k−2`, whose effect on every lower class vanishes,
and their class-`k` effect is `𝔽₂`-linear, so each rung is a genuine linear-algebra question,
not a guess):

| class | narrow ansatz (`s,t,m,n ∈ λ₂`) | widened ansatz (`t, n` may carry χ-legal `Ā`, `C̄₀`) |
| --- | --- | --- |
| 3 | free (theorem) | solved |
| 4 | solved, `s = t = [D̄,B̄]` | solved |
| 5 | solved | solved |
| 6 | walk stalls | **solved** |

The widening is legitimate: `MpcPivShift` constrains only the `C̄₀` row, so the `B̄` and `D̄`
letters may carry any χ-trivial factor, and modulo the Frattini subgroup the χ-trivial
generators are exactly `Ā` and `C̄₀`.  Generation still holds for the widened shape (the four
images still span `𝔽₂⁴`), so it is a valid route to `MpcPivShift 2`; it is simply not the shape
this lane formalized.

## 5.  The calibration, and why no negative conclusion may be drawn

Wave 83 §5 recorded that its depth-4 stalls could not be trusted because `M3` stalled with
them, and asked for calibration.  This lane ran it, in both directions, on the same harness:

* **positive control `M3`** (`C̄₀ ↦ C̄₀^5`, a theorem of the tree from B8, `MScaling.lean`):
  clears every class through six.
* **positive control `M5`** (`B̄ ↦ B̄·C̄₀`, a theorem of the tree, `mMixFamily_coreMix`):
  **STALLS at class five** in the widened harness, and at class *four* in the narrow one.
  `M5` is realized.  So the harness demonstrably produces false stalls, and a stall is not
  evidence of anything.
* **negative control** (`C̄₀ ↦ B̄·C̄₀`, the χ-forbidden odd shift): stalls at class three, i.e.
  the harness does reject what must be rejected, and rejects it early.
* **trivial control** (identity): clear at every class.

So the table in §4.3 has exactly one honest reading: **no obstruction to `M6` exists at classes
three through six, and the class-six stall of the narrow shape says nothing** (the same walk
kills `M5`).  In particular this lane does **not** claim the narrow shape is too narrow; it
claims only that the widened shape gets further under the same walk, which is what a builder
should try first.

## 6.  A structural remark on where the obstruction would have to live

Hand computation, **not formalized**, recorded because it explains the shape of every rung.
The Fox derivatives of the relator `R = Ā²[Ā,B̄]C̄₀⁴[C̄₀,D̄]` in `ℤ₂[[G]]` are

    ∂R/∂Ā = 1 + ĀB̄⁻¹,  ∂R/∂B̄ = ĀB̄⁻¹(Ā−1),
    ∂R/∂C̄₀ = ĀĀ^{B̄}(1 + C̄₀ + C̄₀² + C̄₀³D̄⁻¹),  ∂R/∂D̄ = ĀĀ^{B̄}C̄₀³D̄⁻¹(C̄₀−1),

and the right ideal `J` they generate is the kernel of the **χ-twisted augmentation**
`g ↦ χ_M(g)`: the four conditions are `χ(Ā) = 1`, `χ(B̄) = −1`, `χ(C̄₀) = 1` and
`3 + χ(D̄)⁻¹ = 0`, i.e. `χ(D̄) = −1/3 = (1 − 2²)⁻¹ = mUnit 2`, which is exactly `chiM_dmD`.
So `ℤ₂[[G]]/J ≅ ℤ₂`, the corank is one, and the linearized correction map at every stage misses
exactly one functional.  This is the "χ-twisted Fox row" already named in `mWord`'s docstring,
and it is the reason each rung above is a single linear condition rather than a system.

It also disposes of one hope: since only `χ` survives, **there is no bilinear invariant beyond
the mod-2 cup form** that could separate the two cases, which is consistent with wave 83 §4 and
with `H²(G, ℤ/4) ≅ ℤ/2` for this core (`q = 2`).

## 7.  The five-row scoreboard, from the Lean

Re-run against the mirror by `#check` (not read off the notes), at this lane's tree.

| row | field | `pres` | branch datum over the bundle alone | tied? |
| --- | --- | --- | --- | --- |
| 1 | `ℚ₂(√−2)` | `.N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | yes |
| 2 | `ℚ₂(√2)` | `.M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | yes |
| 3 | `ℚ₂(√5)` | `.M0 2 0` | `fieldFive_genAsmBranch_sqrtFive` | yes |
| 4 | `ℚ₂(√10)` | `.Mpc 2 1 false .one 0` | `mpcNorm_genAsmBranch_sqrtTen` | yes |
| 5 | `ℚ₂(√−10)` | `.Mpc 2 1 true .one 0` | `mpcPiv_genAsmBranch_sqrtNegTen` | **no**: tied form still needs `MpcPivShift 2` |

Unchanged from wave 83.  What changed is what row 5 costs: it is now one word identity whose
first four rungs are climbed and whose failure, if any, is a finite-class fact.

## 8.  Axiom pins

Per declaration, recorded in the module's §9 and reproduced by `mirror.sh gen`.  **All
twenty-three declarations of this module are on the standard three** (`propext`,
`Classical.choice`, `Quot.sound`).  **This lane introduces no axiom.**  A construction fed
through `mpcWord_shift_of_word` would carry, on the `√−10` row, exactly wave 81's set through
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift`, and nothing more.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 9.  What is next

1. **Build `M6` in the widened shape.**  The `B̄` and `D̄` letters may carry χ-legal `Ā` and
   `C̄₀` factors; that shape climbs one class further than the Frattini-only one under the same
   walk.  The Lean-side cost is a widened `mpcWord_gen` (the four images still span mod the
   Frattini subgroup) and a widened `mpcWordCorr` for the `t` and `n` slots.
2. **Formalize class four.**  The witness is explicit (`s = t = commP D̄ B̄`, `m = n = 1`) and
   the computation is a `λ₄` calculation of the kind `gTower_*` already supports
   (`gTower_sq_congr`, `gTower_comm_near_add`, `cfive_commutator_lambdaTwo`).  That would turn
   §4.2 from a checked hand computation into `(mpcWordSet 4).Nonempty`.

   > **[W86-HOUSE, as of `f0de6ad5`:** DONE, by wave 85's `Instances/MpcBuild.lean`
   > (`mpcBld_mem_four_witness`, `mpcBld_nonempty_four`), with exactly this witness. So this
   > note's present-tense claims that "the residual starts at class four" (§1 item 3, §4.1's
   > starred line) and that §4.2's computation is "not formalized" (§4.2 preamble) are all
   > superseded: the residue starts at class FIVE
   > (`mpcBld_shift_of_forall_class_five`).**]**
3. **Do not read a class-by-class stall as evidence.**  §5 shows the walk kills `M5`, which is
   a theorem.  Any future negative claim must come either from an invariant or from an
   exhaustive class-`k` search, not from a greedy ladder; and by §3 an exhaustive class-`k`
   search *is* decisive if it comes out empty.
4. **`CoreMixM` §7's ruling remains unusable as an input**, per wave 83 §9.2.  This lane edits
   no existing module, so the two stale quotations are still there.
