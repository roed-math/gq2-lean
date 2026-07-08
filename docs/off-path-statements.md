# Proved paper statements OFF the main-theorem path

Statements from the paper that are **formalized and proved** in this repository but are *not*
in the dependency cone of any headline deliverable (`main_presentation_literal`,
`main_surjection_count'`, `thm_4_2`, `prop_8_9`, `lemma_6_17_vanish_final`).  They were kept
in the 2026-07-08 dead-code prune precisely because they are paper content — useful when
rewriting the paper (each is a formally verified claim you can cite), even though the final
proof route does not consume them.

Line numbers are as of the 2026-07-08 prune; re-locate with `rg -n '<name>' GQ2/`.

| Paper node | Lean name | Location | What it says |
|---|---|---|---|
| Lemma 3.5 (symbol form) | `lemma_3_5_hilbert_ledger` | `GQ2/SectionThree.lean:1301` | The "initial form" clause of Lemma 3.5 in Hilbert-symbol vocabulary. |
| Lemma 3.7 / eq. (15) | `lemma_3_7` | `GQ2/AnabelianBridge.lean:838` | For every `u ∈ ℤ₂ˣ` there is a continuous automorphism `Ψ_u` (unit-rescaling of the wild pair). |
| Prop. 3.2, `Γ_A` side | `prop_3_2_gammaA` | `GQ2/Prop32.lean:500` | The quotient of `Γ_A` by `W_A` is `T_tame`. |
| Prop. 3.2, local side | `prop_3_2_local` | `GQ2/Prop32.lean:1289` | The tame quotient of `G_{ℚ₂}` (Ax = B10). |
| Prop. 3.10, local half = Cor. 3.12 | `prop_3_10_local_marked` | `GQ2/SectionThreeMarked.lean:59` | `(Π, ν₂) ≅ (G_{ℚ₂}(2), ν_ur)` fully marked. |
| Prop. 3.14 | `prop_3_14`, `prop_3_14_proved` | `GQ2/SectionThreeMarked.lean:85`, `GQ2/BoundaryMapsWitness.lean:500` | The eq. (27) boundary data exists (`Nonempty BoundaryMaps`). The live route instead uses the explicit witness `boundaryMapsWitness` directly. |
| Prop 5.16 | `prop_5_16`, `prop_5_16_bundle` | `GQ2/LocalLiftingDuality.lean:563`, `:515` | Local lifting duality for a finite elementary module with `G_ℚ₂`-action (all six clauses). |
| Cor. 5.17 (numerics) | `cor_5_17_card` | `GQ2/LocalLiftingDuality.lean:590` | The obstruction-space cardinality corollary. |
| Lemma 6.6 / eq. (86) | `lemma_6_6` | `GQ2/SectionSix.lean:208` | Wall doubling for a nonsingular `q` and an orthogonal operator. |
| Lemma 6.13, `D₈` claim | `lemma_6_13_dihedral` | `GQ2/SectionSix.lean:498` | The fibre extension of the universal two-point class is dihedral. |
| Lemma 6.13 / eq. (96) | `lemma_6_13_evens` | `GQ2/SectionSix.lean:567` | The explicit two-point cocycle `κ_J` on `E ⋊ J` represents the Evens class. |
| Lemma 7.1, radical clause | `lemma_7_1_radical` | `GQ2/SectionSeven.lean:409` | `T₀ = (K ∩ S)·R` is the unique maximal `Y`-normal subgroup. |
| Lemma 7.3 | `lemma_7_3` | `GQ2/SectionSeven.lean:760` | Decorations vanish on the block. |
| Lemma 8.5 / eq. (126) | `lemma_8_5` | `GQ2/SectionEight.lean:216` | Constrained quadratic Gauss transform, multiplied-out form. |
| Lemma 8.5, aggregated | `lemma_8_5_aggregated` | `GQ2/RecursionSplice.lean:255` | The summed constrained-Gauss identity (`hgauss` level 1). |
| Lemma 8.7, count form | `lemma_8_7_count` | `GQ2/AffineTLift.lean:711` | Central `M`-lifts sharing a `T`-reduction: the fibre count. |
| Prop 8.9, reduced form | `prop_8_9_of` | `GQ2/RecursionSplice.lean:43` | Prop 8.9 from per-source `RecursionInputs` + shared witness (the splice backbone; the live route proves `prop_8_9` directly in `GQ2/Prop89Close.lean`). |
| eqs. (136)–(140) | `RecursionInputs.eq136` … `.eq140` | `GQ2/SectionEight.lean:1640–1675` | The boxed recursion system as structure fields (consumed by `prop_8_9_of`; the live route populates them at `:1963` but reads them through its own wiring). |

**Why they are off-path.**  Late reshapes picked more direct routes: `prop_8_9` was proved
directly at `Prop89Close.lean` (bypassing the `prop_8_9_of` splice backbone), Prop 3.14's
`Nonempty` form was superseded by the explicit `boundaryMapsWitness`, and the §5.16/§6/§7
side statements feed proofs of statements that themselves got more economical routes.
