# §3 crosswalk — tame quotients and marked pro-2 presentations

This note maps Proposition 1.1, Proposition 3.2, Lemmas 3.4–3.8, and displays (8)–(18) to
the completed Lean development. It also records the places where the paper's cited or implicit
infrastructure is represented by a different but equivalent Lean interface.

## Statement map

| Paper node | Lean encoding | Principal module |
|---|---|---|
| Tame presentation and Lemma 3.1 | `Ttame`, `tameSigma`, `tameTau`, `tame_relation`, `Tame` | `TameQuotient.lean`, `Tame.lean` |
| Proposition 3.2, `Γ_A` side | `prop_3_2_gammaA` | `Prop32.lean` |
| Proposition 3.2, local side | `LocalTameQuotient`, `prop_3_2_local` | `Prop32.lean` |
| Lemma 3.3, maximal pro-2 wild subgroup | `LocalTameQuotient.maximal` and the `twoCore` lemmas | `Prop32.lean`, `SectionTen.lean` |
| Display (9)/(11), marked abelianization | `BDecomposition`, `b_decomposition` | `SectionThree.lean` |
| Lemma 3.5, marked reciprocity rows | `lemma_3_5_marked_abelianization` and the `Reciprocity` lemmas | `SectionThree.lean`, `Reciprocity.lean` |
| Lemma 3.5, Hilbert/initial-form ledger | `lemma_3_5_hilbert_ledger` | `SectionThree.lean` |
| Lemma 3.5, injectivity | `lemma_3_5_injective` | `SectionThree.lean` |
| Lemma 3.6 | encoded by the B8 interface `peripheralCyclotomicAction` | `Foundations/Axioms.lean` |
| Lemma 3.7 / (15) | `lemma_3_7` | `AnabelianBridge/Construction.lean` |
| Proposition 3.8 | `prop_3_8_lift`, `prop_3_8_classification` | `AnabelianBridge/` |
| Proposition 1.1 / (4) | `prop_1_1` | `PropOneOneAssembly.lean` |
| Proposition 3.10 | `prop_3_10_gammaA`, `prop_3_10_local_marked` | `SectionThreeMarked.lean` |
| Proposition 3.14 / (27) | `prop_3_14`, `prop_3_14_proved`, `boundaryMapsWitness` | `SectionThreeMarked.lean`, `BoundaryMapsWitness.lean` |

All declarations in the table are proved. The local side of Proposition 3.2 uses the cited tame
quotient interface B10; Proposition 1.1 uses the marked Demushkin/orientation and peripheral-action
interfaces B3c and B8.

## Absorbed paper nodes

### Lemma 3.4

The paper's proof of Lemma 3.4 is a citation to Labute's classification. The Lean formalization
does not introduce a second theorem merely to repeat that citation. Its consumed content is carried
by `dyadicOrientation`, the composite B3c interface that supplies a marked rank-three Demushkin
model with the normalized orientation values. The formerly separate B4 presentation axiom was
deleted after the ledger showed it had no consumers.

The assertion that this model has the classical Demushkin `q=2` invariant is explanatory rather
than a separate formal object: no downstream theorem uses a formalized Demushkin classification
predicate.

### Lemma 3.6

`peripheralCyclotomicAction` is the group-theoretic conclusion of Lemma 3.6, expressed directly in
the pro-2 peripheral presentation. It is an encoded/composite literature interface rather than a
verbatim theorem statement; [`literature-axioms.md`](literature-axioms.md) explains the Stix input
and the cyclotomic-surjectivity convention it bundles.

### Reciprocity rows in Lemma 3.5

The values of `ν_ur` and `χ_cyc` on the marked square classes, together with the abelianized
relation, are proved as parameterized consequences of `LocalReciprocity` in `Reciprocity.lean`.
They are not restated as additional axioms.

## Encoding choices

### The tame group and wild core are shared definitions

`Ttame` is the profinite presentation on `σ,τ` with `τ^σ=τ²`. The §3 development uses the same
definition as the later boundary-frame layer. Likewise `SectionThree.wildPart` is definitionally
the global `wildCore`, the normal closure of the two wild generators. This deduplication lets the
pro-2 and closedness facts flow to both Proposition 3.2 and §10 without conversion lemmas.

### Local wild inertia is intrinsic

Mathlib does not provide the ramification-theoretic wild inertia subgroup needed here. The local
interface therefore characterizes it as the maximal closed normal pro-2 subgroup. This is exactly
the intrinsic content of Lemma 3.3 and uniquely pins the quotient used in Proposition 3.2.

### “Canonical” is pinned only where downstream mathematics needs it

On the `Γ_A` side the quotient map is pinned on the marked generators. On the local side the
maximal wild subgroup is canonical, while a particular isomorphism of the quotient with `Ttame` is
not. The later counting theorem sums over all tame frames, so changing that isomorphism permutes the
indexing set and does not alter a count.

### The marked abelianization is a bundle

`BDecomposition` records a continuous isomorphism

`D₀^{ab} ≃ ℤ/2 × ℤ₂ × ℤ₂`

pinning the coordinates `(t,S̄,Ȳ)`, with `t=Ā+2S̄`. Statements about the automorphisms
`α_{u,b}` are parameterized by this bundle. Continuity of power maps makes the group-theoretic
coordinate action agree with the paper's `ℤ₂`-module notation.

### The initial form is represented by its Hilbert-symbol ledger

`lemma_3_5_hilbert_ledger` records the six pairings on the square-class basis
`(-1,2,-3)`. Under the dual basis this is the quadratic initial form `α²+βγ+γβ` of the
Demushkin relator. No Zassenhaus graded-Lie API is introduced, because downstream proofs consume
only the pairing values.

### Proposition 1.1 is an isomorphism with marked rows

The theorem existentially packages an isomorphism from the maximal pro-2 quotient to `D₀`, together
with the `ν_ur` values read through arbitrary lifts to the absolute Galois group. The relation and
topological generation follow by transporting the corresponding facts from `D₀`; they are not
duplicated as fields.

## Infrastructure developed to prove the statements

### 2-adic powering and Frattini control

Lemma 3.7 and Proposition 3.8 require power maps by arbitrary elements of `ℤ₂`, not merely integer
powers. `ZtwoPowering.lean` identifies the 2-primary factor of `ℤ̂`, constructs the action on pro-2
groups, and proves odd-power bijectivity. `FrattiniCriterion.lean` supplies the principle that a
map inducing a surjection on the Frattini quotient is surjective. These results were proved in the
repository rather than added to the axiom census.

### The anabelian bridge

The proof of `lemma_3_7` pushes the B8 peripheral identity along a map from the two-generator
peripheral group into `D₀`. The three peripheral rows combine into the conjugation identity needed
for the Demushkin relator check. This avoids formalizing the paper's intermediate Tietze/HNN
elimination as a separate presentation theorem. Surjectivity follows from the Frattini criterion,
and profinite Hopficity upgrades the endomorphism to an automorphism.

The B8 embedding of `ℤ₂` into `ℤ̂` is pinned by its 2-primary projection. Merely requiring
continuity and the value at `1` would not determine the action at general `u`; the projection field
is therefore a load-bearing part of the encoded interface.

### Marked reciprocity is already strong enough

The marked abelianization is proved from the existing local reciprocity bundle. Injectivity uses
the descended `ν_ur` and cyclotomic coordinates. Surjectivity uses the dense reciprocity image and
the square-class generation

`ℚ₂ˣ = ⟨-4,2,-3⟩ · (ℚ₂ˣ)²`,

proved by a 2-adic Hensel argument and mod-8 unit analysis. Thus no additional “reciprocity induces
the pro-2 abelianization” axiom is needed.

### The marked boundary layer is kept downstream

`SectionThreeMarked.lean` imports the boundary-frame definitions and records both halves of
Proposition 3.10 and the existence form of Proposition 3.14. The explicit
`boundaryMapsWitness` is the form consumed by the final route. Proposition 3.11's Nielsen moves and
Remark 3.13 remain proof steps rather than standalone API declarations.

The `Z₂` seam is explicit: the boundary character targets the maximal pro-2 quotient of `ℤ̂`, while
local reciprocity targets multiplicative `ℤ₂`; the marked isomorphism identifies their normalized
generators.

## Paper-facing consequences

- The local tame quotient is a cited classical input, but maximality of the wild pro-2 subgroup is
  proved in Lean.
- The peripheral action is a composite interface and should be cited as such, not as a literal
  transcription of one line in Stix.
- The theorem numbers in the rewritten paper may move; the stable Lean identifiers are the names in
  the statement map and the semantic crosswalk in [`paper-api.md`](paper-api.md).
