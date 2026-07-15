# §9 crosswalk — terminal case and master induction

This note maps paper §9 (Lemmas 9.1–9.4, displays (143)–(153), and the Theorem 4.2 endgame) to the
completed Lean proof. The public [`GQ2/SectionNine.lean`](../GQ2/SectionNine.lean) module is an
umbrella over the terminal and induction developments; Theorem 4.2 itself is in
[`GQ2/ThmFourTwo.lean`](../GQ2/ThmFourTwo.lean) because it consumes the full §§5–9 stack.

## Statement map

| Paper node | Lean encoding | Principal module |
|---|---|---|
| Lemma 9.1, coprime subdirect product | `FiniteGroup.coprime_fiber_product` | `FiniteGroupLemmas.lean` |
| Lemma 9.2, Schur–Zassenhaus splitting | `FiniteGroup.oddOrder_twoQuotient_split`, `SectionNine.lemma_9_2_core` | `FiniteGroupLemmas.lean`, `SectionNine/Terminal.lean` |
| §9.1 terminal comparison | `SectionNine.terminal_count_eq` | `SectionNine/Induction.lean` |
| Lemma 6.3 class used in §9.3 | `SectionNine.kappa0_exists` | `SectionNine/Induction.lean` |
| Concrete §7→§8 frame | `SectionNine.blockFrame` | `SectionNine/Induction.lean` |
| Concrete enrichment | `SectionNine.blockEnrichment` | `Block/Enrichment.lean` |
| §9.2 `M`-stage partition | `SectionNine.mStage_partition` | `SectionNine/Induction.lean` |
| Lemma 9.4 size bounds | `card_LB_lt`, `card_LC_lt`, and the pullback/phase bounds | `Block/FrameBounds.lean` and consumers |
| §9.3 arithmetic solver | `SectionNine.count_eq_of_closedRecursion` | `SectionNine/Induction.lean` |
| Theorem 4.2 | `GQ2.thm_4_2`, `GQ2.thm_4_2_stratum` | `ThmFourTwo.lean` |

All listed results are proved. Lemma 9.3's obstruction-dual content is not exposed as a separate
paper-numbered theorem: it is the `(W,o,e)` obstruction datum supplied to the §8 `stageR136`
construction. Displays (146), (147), (149), (151), and (152) likewise enter through the already
packaged Proposition 8.9 recursion identities.

## Statement corrections and representation choices

### The decoration group must have exponent two

`thm_4_2` takes

```lean
hE2 : ∀ e : E, e ^ 2 = 1
```

The paper's induction descends the decoration through a block using Lemma 7.3, whose target is an
elementary abelian 2-group. The terminal case also kills an odd complement through the decoration,
which needs the same 2-primary condition. The original Lean skeleton allowed an arbitrary finite
commutative group `E`, broader than the paper's operative setting. Section 10 uses only the trivial
decoration group, so the correction is invisible at the final consumer.

### The `M`-stage theorem is source-generic

`mStage_partition` accepts the multiplicity and its value as hypotheses. The local and `Γ_A`
consumers supply the relevant `|Z¹(M)|=2^{2 dim M}` calculations from their respective
Propositions 5.15 and 5.16 packages. This avoids hiding source-specific cohomology inside the
combinatorial partition theorem.

### The recursion solver takes semantic IH atoms

`count_eq_of_closedRecursion` is deliberately arithmetic. It assumes agreement of:

- the lower target counts `e(T_B)` and `e(T_C)`;
- the pullback-stratum counts appearing in (138); and
- the phase-cover liftable counts.

The master induction derives each atom from a strict kernel-size bound and the induction
hypothesis. Keeping these inputs explicit separates group-theoretic descent from cancellation in
the boxed recursion equations.

### `kappa0_exists` uses the paper's simple tame hypotheses

The theorem includes `FoxH.IsSimpleModTwo C V` and `ActsThroughTame C V`. The stronger claim for an
arbitrary finite module is false: the relevant extension
`1 → V^∨ → Aut(E_f) → O(q) → 1` need not split after pullback. The corrected statement is the
paper's Lemma 6.3 situation—a simple, self-dual tame module—and those hypotheses are available at
the sole block-enrichment consumer. The counterexample analysis and route design are preserved in
[`orchestration/p17e-kappa0-scoping.md`](orchestration/p17e-kappa0-scoping.md).

### Theorem 4.2 is placed downstream

The theorem's statement belongs conceptually to the boundary-frame layer, but its proof needs
minimal blocks, §8 recursion data, source-specific Gauss counts, and the terminal comparison.
Keeping it in `ThmFourTwo.lean` avoids an import cycle while preserving the public name
`GQ2.thm_4_2`.

## Proof architecture

The proof is strong induction on `|L_Y|`, the order of the marked kernel of the target.

### Terminal lane

If `L_Y` is a scalar stack, the odd complement centralizes the 2-primary kernel. Schur–Zassenhaus
splitting and the marked maximal pro-2 comparison reduce both sources to the same terminal
presentation. `terminal_count_eq` packages the resulting correspondence.

### Nonscalar block selection

Otherwise `SectionSeven.exists_minimalBlock` chooses the first nonscalar chief block. From it Lean
constructs `blockFrame`, the quotient targets `T_B` and `T_C`, and the enrichment needed by
Proposition 8.9.

### `M`-stage lane

When the relevant Frattini-like subgroup is trivial, `mStage_partition` expresses the exact-image
count as a common multiplicity times counts for proper quotient strata. Lemma 9.4 gives strict
kernel-size bounds, so the induction hypothesis identifies every source pair; cancellation yields
the target equality.

### `R`-stage lane

In the remaining case, `prop_8_9` supplies matching closed-recursion systems for the two sources.
The induction hypothesis identifies the `T_B`, `T_C`, pullback-stratum, and phase-cover terms. The
solver then compares equations (136)–(140) and cancels their nonzero finite cardinality factors.

The phase-cover term is expanded using Lemma 8.3, and the strict bound in (153) ensures that its
proper strata lie below the induction parameter. Nonemptiness of the phase index is part of the
constructed witness, so the (140) coefficient is genuinely nonzero.

## Trust-base flow

B1 supplies topological finite generation on the local side when Lemma 8.3 is applied to phase
covers. The terminal comparison uses the marked pro-2 and peripheral-action inputs. Local duality,
Euler characteristic, Evens–Kahn, and the Hilbert/norm inputs enter through the §§6–8 ingredients.
The exact transitive set is kernel-checked by `GQ2/AxiomLedger.lean`; §9 does not introduce a new
axiom or a new source assumption.
