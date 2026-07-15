# §10 crosswalk — tame-frame exhaustion and equation (154)

This note maps paper §10 to the completed Lean development in `GQ2/SectionTen.lean` and
`GQ2/SectionTenSources.lean`. It records the representation choices and statement amendments that
matter when revising or reviewing the paper.

## Statement map

| Paper object or result | Lean encoding |
|---|---|
| `O₂(G)` | `SectionTen.twoCore`, with `twoCore_normal`, `twoCore_isPGroup`, and `le_twoCore` |
| Image of the pro-2 wild subgroup lies in `O₂(G)` | `isPGroup_map_of_isProP` followed by `le_twoCore` |
| The §10 marked target `(G,O₂(G),π,0)` | `tameTarget G : MarkedTarget (G ⧸ twoCore G) E₀ G` |
| A tame boundary frame with trivial decoration | `tameFrame α hα : BoundaryFrame H E₀` |
| Finite family of tame frames onto `G/O₂(G)` | `TameFrames G` |
| Lemma 10.1, exhaustion and disjointness | `SectionTen.lemma_10_1` |
| Summed count identity | `SectionTen.card_contSurj_eq` |
| Equation (154) | `SectionTen.eq_154` |
| Theorem 1.2, count form | `SectionTen.main_surjection_count'` |

All declarations in the table are proved. The capstone's transitive trust base is reported by
`GQ2/AxiomLedger.lean` and `atlas-audit.md`.

## Encoding decisions and deviations

1. **`O₂(G)` is constructed rather than cited.** Mathlib has no ready `pCore` definition for this
   use. Lean defines
   `twoCore := sSup {N | N.Normal ∧ IsPGroup 2 N}` and proves normality, the 2-group property,
   and its universal property. The argument uses directedness through the second isomorphism
   theorem and closure of finite 2-groups under extensions.
2. **“For either source” becomes a generic theorem.** `lemma_10_1` and `card_contSurj_eq` are
   stated for a source `(Γ,b)` with a surjective tame coordinate and pro-2 kernel. The local and
   `Γ_A` sides then supply those hypotheses separately. This keeps the exhaustion argument
   independent of the source-specific constructions.
3. **Uniqueness and disjointness are represented by an equivalence.** The paper's assertion that a
   surjection determines a unique tame boundary frame is encoded as
   `ContSurj Γ G ≃ (α : TameFrames G) × BoundaryLifts b (tameFrame α) (tameTarget G)`.
   This single sigma-equivalence provides the partition, uniqueness, and fibre identification.
4. **The trivial decoration group is `PUnit`.** The group `E₀ := PUnit` has exponent two
   definitionally, so the `hE2` hypothesis of `thm_4_2` is discharged by `fun _ => rfl`.
5. **The count is a finite sum over the subtype of tame frames.** Finiteness of the index uses
   topological finite generation of `Ttame`; finiteness of each fibre uses
   `finite_boundaryLifts` and finite generation of the source.
6. **Equation (154) and the final finite count are separate declarations.** `eq_154` compares the
   two source counts. Then `main_surjection_count'` composes its symmetry with `prop_2_3`, which
   identifies the `Γ_A` count with `admissibleCount`.
7. **The capstone lives downstream of the statement modules.** Proving the count theorem in
   `Statement.lean` would introduce an import cycle through the §§4–9 machinery. The theorem is
   therefore implemented in `SectionTenSources.lean`, while upstream declarations consume the
   appropriate hypothesis or downstream theorem. This is an architectural placement, not a
   mathematical change.
8. **Topology hypotheses are explicit where they are used.** Compactness makes the continuous
   surjective tame coordinate a quotient map, which is needed to descend the induced frame.
   Total disconnectedness supplies finiteness of the continuous-hom and boundary-lift spaces.
   The source instances are intentionally theorem binders rather than new global instances.
9. **The quotient head is proved discrete.** `DiscreteTopology (G ⧸ twoCore G)` follows from
   `discreteTopology_iff_forall_isOpen` and openness in the coinduced quotient topology; the proof
   does not rely on an accidental definitional instance.

## Proof assembly

For each tame frame, `thm_4_2` equates the exact-image count for the `Γ_A` boundary map and the
local boundary map. `card_contSurj_eq` expresses each global count as the sum of those framewise
counts. Summing the pointwise equality gives `eq_154`; `prop_2_3` then converts the `Γ_A` side to
admissible marked quadruples.

This formulation makes the only genuinely source-specific inputs visible: the two tame-coordinate
surjectivity/kernel packages and the per-frame theorem from §9.
