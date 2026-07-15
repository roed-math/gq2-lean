# §8 crosswalk — half-torsors, affine lifting, and closed recursion

This note maps paper §8 (Lemmas 8.2–8.7, Proposition 8.8, Proposition 8.9, and displays
(124)–(142)) to the completed Lean development. It records the mathematical representation choices
and the corrections discovered while proving the recursion.

The public umbrella [`GQ2/SectionEight.lean`](../GQ2/SectionEight.lean) re-exports the focused
modules under `GQ2/SectionEight/`; deeper source-specific assembly is in `AffineTLift.lean`,
`RadicalEdge/`, and `Prop89Close.lean`.

## Statement map

| Paper node | Lean encoding | Principal module |
|---|---|---|
| Lemma 8.2, candidate source | `SectionEight.lemma_8_2_gammaA` | `SectionEight/ScalarCount.lean` |
| Lemma 8.2, local source | `SectionEight.lemma_8_2_local` | `SectionEight/ScalarCount.lean` |
| Lemma 8.2, scalar twisting | `scalarTwist` and its boundary-lift lemmas | `SectionEight/Covers.lean` |
| Lemma 8.3 / (124) | `SectionEight.lemma_8_3` | `SectionEight/Partition.lean` |
| Lemma 8.4 / (125) | `SectionEight.lemma_8_4` | `SectionEight/Fourier.lean` |
| Lemma 8.5 / (126) | `SectionEight.lemma_8_5` | `SectionEight/Fourier.lean` |
| Lemma 8.6, two sources | `lemma_8_6_gammaA`, `lemma_8_6_local` | `SectionEight/Partition.lean`, `RadicalEdge/` |
| Lemma 8.7 | `lemma_8_7_count` | `AffineTLift.lean` |
| Proposition 8.8 | `prop_8_8_target` | `AffineTLift.lean` |
| Proposition 8.9 / (136)–(142) | `SectionEight.prop_8_9` | `Prop89Close.lean` |

All of these results are proved. `RecursionFrame`, `ClosedRecursion`, and `RecursionInputs` in
`SectionEight/Recursion.lean` provide the common vocabulary for the boxed recursion identities.

## Representation choices

1. **Denominators are cleared over `ℤ`.** Displays (125), (126), (136), (139), and (140) are
   expressed in multiplied-out integer form. Display (137) is additive (`Z = m + Σ`) rather than
   using truncated natural-number subtraction.
2. **The vector `a_χ` in (126) is data with its defining specification.** `lemma_8_5` assumes
   `B_Q(a_χ,x)=χ(Lx)` directly. Nonsingularity is not needed once such a vector has been supplied,
   so it does not appear in the theorem statement.
3. **Liftability represents obstruction vanishing.** Phrases such as “the scalar pushout
   vanishes”, “the pullback cover splits”, and “unobstructed” are encoded as existence of a
   continuous lift through a central cover. This matches the torsor argument used by the paper and
   avoids inserting a second layer of `H²` quotient plumbing into the statement API.
4. **Lemma 8.6 uses an operational edge condition.** The paper's `H¹(C,T^∨)` edge is represented by
   `RadicalCoverData.NoDescent`: the absence of a normal complement to the relevant preimage. The
   variation cocycle is proof-internal; the public theorem exposes the equivalent descent
   criterion and half-count needed downstream.
5. **Lemma 8.6 is source-specific.** Its local proof uses local duality, while the `Γ_A` proof uses
   the candidate-side lifting-duality package. A generic statement would merely replace those
   concrete constructions by a large abstract duality hypothesis.
6. **The `D_R` and scalar-cover data are pinned by their properties.** The recursion frame records
   the normal subgroups, scalar covers, and quotient targets together with the kernel, head, and
   decoration equations the proof actually consumes. It does not force a particular quotient
   constructor into every statement.
7. **Displays (140)–(142) are folded.** Display (141) is substituted into (140), while (142) is the
   Lemma 8.3 partition applied to the phase covers. The shared phase package is existentially
   quantified outside the source split, exactly matching what the §9 comparison needs.
8. **Cardinalities replace dimension bookkeeping.** The factor `2^d` is represented by the exact
   quotient cardinality `|M|/|T|`; the terms `2^{2 dim M}` and `z_R` become `|M|²` and
   `|R|²|D_R|`.

## Corrections exposed by the proof

### The `zBC` object must live at the `B` level

The first encoding stored a cover-valued lift. But the boundary equation constrains only its image
in `B`, and every compatible `B`-lift has `|Hom(Γ,𝔽₂)|` scalar-twisted cover lifts. Counting the
cover maps therefore overcounts the paper's `Z_{Γ,λ}(B/C)` by that factor. The corrected
`RecursionFrame.zBC` stores a `B`-level lift together with existence of a cover lift.

### Display (137) sums only over strata surjecting onto `C`

An unrestricted sum includes strata whose image misses `C`, even though their corresponding
`Z`-slice is empty. `ClosedRecursion.eq137` therefore uses exactly the paper's restricted index.

### Proposition 8.9 requires the §7/§6 enrichment data

A bare `RecursionFrame` permits arbitrary central covers, for which (139) and (140) are false. The
proved theorem also takes `RF.Enrichment`, which packages:

- the square forms on the restrictions to `M_B`, including the radical and vanishing properties
  supplied by Proposition 7.4; and
- the fixed equivariant base class `κ⁰_{q̄_λ}` required by the Lemma 6.1/6.21 construction.

This is a statement correction, not implementation convenience: the paper's argument uses these as
standing data. `FrameEnrichment.lean` constructs the block-level instance.

### Lemma 8.7 is counted at cocycle level

The paper packages the multiplicity as `|B¹(V)|·|Z¹(T)|`. Lean's `lemma_8_7_count` fixes a
`T`-reduction and counts central `M`-lifts in that fibre, obtaining the `|Z¹(T)|` factor directly.
The residual `|B¹(V)|` appears in the enumeration of the `V`-coordinate base and remains inside the
global multiplicity `μ`. No quotient-set representatives for cohomology classes are needed.

### Proposition 8.8 keeps the full normalized phase

`prop_8_8_target` is the finite-target cochain identity obtained from `lemma_6_22`. Its phase is

`Δ = δ + Θ⁰_q̄(a) + γ ⌣ a`.

The printed display (134) omits the cup term `γ ⌣ a`; the Lean proof shows that it belongs in the
normalized phase. The count theorem is unaffected because Proposition 8.9 existentially packages
the phase covers built from this corrected `Δ`. This manuscript correction is also recorded in
[`paper-errata.md`](paper-errata.md).

### Phase covers are genuine twisted products

`centralCoverOfCocycle δ` constructs the normalized central extension
`𝔽₂ ×_δ C₀`, with multiplication `(s,c)(t,d)=(s+t+δ(c,d),cd)`. `phaseFamily` lifts this to the
family indexed by `(T^∨)^C`. Thus the phase package is a constructed family of central covers, not
an uninterpreted cardinality parameter.

### The bridge for (139) is an explicit fibre equivalence

`RadicalEdge.Bridge.half139_of` fibres `zBC` over a lower exact-image map `ρ : Γ ↠ C` and uses
`liftsOver_equiv` / `centralOver_equiv` to identify that fibre with the corresponding `MLifts`
space. The two numerical inputs are precisely Lemma 8.6's half-torsor count and the unrestricted
`M`-lift count from Propositions 5.15/5.16.

## Completed proof architecture

- Lemma 8.3 is the torsor partition: lifts through a central double cover form a torsor under
  continuous `𝔽₂`-characters. Freeness and transitivity are packaged by `fiberLiftEquiv`.
- Lemma 8.6 combines that torsor with a nonzero linear obstruction functional; a finite
  `𝔽₂`-space then splits into two equal fibres.
- Lemmas 8.4 and 8.5 provide the Fourier and constrained-Gauss identities used in (136) and (140).
- The affine-lifting layer supplies the `T`-reduction fibres, completed-square phase, and phase
  covers.
- `prop_8_9` assembles the local and candidate source data into one `ClosedRecursion` witness,
  which §9 consumes without comparing the two sources' cohomology spaces directly.
