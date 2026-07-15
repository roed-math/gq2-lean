# §§6–7 crosswalk — quadratic forms, local arithmetic, and minimal blocks

This note maps the paper's §§6–7 statements to the completed Lean development and records the
statement corrections exposed during proof. The principal public modules are `GQ2/SectionSix.lean`
and the [`GQ2/SectionSeven.lean`](../GQ2/SectionSeven.lean) umbrella, with focused proofs in the
quadratic, Kummer, Shapiro, duality, and block submodules.

## Statement and display map

| Lean declaration | Paper node | Role |
|---|---|---|
| `graphPullback_mem_Z2` | Lemma 6.1 / (62) | The pulled-back equivariant base cocycle is a 2-cocycle. |
| `lemma_6_6` | Lemma 6.6 / (86) | Wall doubling and the rank of `im(1+U)`. |
| `lemma_6_8` | Lemma 6.8 / (87), (88) | Isotypic decomposition data and cardinality consequences. |
| `prop_6_9_unramified`, `prop_6_9_ramified` | Proposition 6.9 / (91) | The two branches of the base quadratic Gauss count. |
| `lemma_6_13_dihedral` | Lemma 6.13 | The two-point fibre extension is `D₈`. |
| `lemma_6_13_evens` | Lemma 6.13 / (96) | The two-point cocycle represents the Evens class. |
| `lemma_6_14` | Lemma 6.14 / (102) | Independence of the chosen representative and factor-set realization. |
| `lemma_6_15_square`, `_free`, `_involution` | Lemma 6.15 / (103)–(105) | The three corestriction word types. |
| `lemma_6_16` | Lemma 6.16 / (110)–(114) | Deep-unit Evens-norm vanishing. |
| `lemma_6_17_dim`, `lemma_6_17_vanish_final` | Lemma 6.17 | The deep half has the right size and the local quadratic form vanishes on it. |
| `prop_6_18_ramified`, `prop_6_18_unramified` | Proposition 6.18 / (115) | Dyadic determinant and zero-count theorem. |
| `lemma_6_21` | Lemma 6.21 / (116) | Splitting consequence of the transgression calculation. |
| `lemma_6_22` | Lemma 6.22 / (121)–(123) | Shear formula, exact up to an explicit coboundary. |
| `exists_minimalBlock` | §7 opening | Choice of the first nonscalar block. |
| `lemma_7_1_radical`, `_head`, `_dual` | Lemma 7.1 | Radical, head, and dual subgroup properties. |
| `lemma_7_2` | Lemma 7.2 | Central elementary radical and exponent-four kernel. |
| `lemma_7_3` | Lemma 7.3 | Decorations vanish on the block kernel. |
| `prop_7_4` | Proposition 7.4 | The descended nonsingular head form `q̄_λ`. |

## Foundational representations

### Quadratic forms

A quadratic form is a function `q : V → ZMod 2` together with `IsQuadraticFp2 q`; its polar form
is required to be biadditive. The total function `arf` is defined by the majority of zero and
one values. In the nonsingular even-dimensional case used by the paper, this agrees with the
classical Arf invariant through the zero-count formula. This avoids choosing a symplectic basis.

### Canonical transversals

Shapiro and corestriction formulas use Lean's canonical `Quotient.out` transversal. The paper proves
independence from a transversal; fixing the canonical representative removes a choice parameter
from every public statement. Independence needed for the proof is established internally.

### Total class formers

`H1ofFun` and `H2ofFun` send a raw function to its cohomology class when it is a continuous
cocycle, and to zero otherwise. This keeps definitions total while theorems separately establish
the cocycle conditions of the concrete functions.

### Representative independence of `Q⁰_loc`

`Q⁰_loc` uses `Quotient.out` representatives. The key observation is
`graphPullback(b)=φ_b^*κ⁰` on `V⋊C`; changing the representative conjugates `φ_b` by an inner
automorphism. `innerConj` proves that such conjugation changes the cocycle by a coboundary, yielding
`RepIndependence.repIndep` and `lemma_6_14` without a new axiom.

### Deep units

Deepness is encoded with the spectral norm in `AlgebraicClosure ℚ_[2]`: an element has the form
`A=1+2b` with `‖b‖<1`, and the relevant elements are fixed by the finite extension's fixing
subgroup. The condition `v_K(A-1)≥e+1` becomes the norm inequality and avoids duplicating a
ramification-index API.

### Ramified versus unramified action

The lower action factors through `Ttame`. Ramifiedness means that the image of `tameTau` acts
nontrivially on the simple module; unramifiedness means it acts trivially. This is the exact
finite-module distinction consumed by Propositions 6.9 and 6.18.

### Finite-target block language

Section 7 is phrased in terms of normal subgroups of the finite target `Y`, rather than quotient
module objects. For example, the vanishing of `(M^∨)^C` is represented by the absence of a
`Y`-normal index-two subgroup of `K` above `R`. Proposition 7.4 existentially packages `q̄_λ`
together with its square formula, invariance, nonsingularity, and nonvanishing.

## Statement corrections exposed during proof

### A normalized factor set includes associativity

`IsEquivariantFactorSet` includes the additive 2-cocycle equation `f_cocycle`. Without it the
extension multiplication need not be associative and `graphPullback` need not be a cocycle. The
first statement extraction had recorded normalization and equivariance but omitted this condition.

### Lemma 6.16 requires the finite-dyadic and Kummer data it uses

The Lean theorem carries finite-dimensionality of the dyadic base, a quadratic generator
`δ²=d`, the fixing-subgroup characterization of the extension, and coordinates `A=u+vδ` for the
deep unit. These are exactly the data invoked by the paper's sentence “write `L=k(√d)` and
`a=u+v√d`”. Making them explicit avoids rebuilding infinite Galois correspondence inside the
local arithmetic lemma.

### Proposition 7.4 needs the framed tame head

The theorem assumes a surjective framed target `π : Y → H` and a continuous surjection
`Ttame → H`. Its proof needs `H¹(H_V,V^∨)=0`, which holds for the tame heads in the paper but is
false for arbitrary finite action groups. The original extracted statement dropped this standing
§7 hypothesis; the corrected Lean theorem restores it.

### Lemma 6.21 is relative to a fixed equivariant base class

The paper assumes a zero-section-normalized equivariant class `κ⁰_q`. The first consequence-form
extraction omitted it, making the splitting statement stronger than the transgression argument.
The theorem now takes `dat : FactorSet C V` and `hdat : IsEquivariantFactorSet q dat`, the concrete
Lean form of that fixed class. The full diagnosis is retained in
[`orchestration/p15i-transgression-gap.md`](orchestration/p15i-transgression-gap.md).

### The classical inputs must apply over a general finite dyadic base

Lemma 6.16 is applied over an intermediate finite extension, not only over `ℚ₂`. The Evens–Kahn and
Hilbert/norm interfaces are therefore stated for finite dyadic bases. This is a genuine scope
requirement of the paper's proof; it cannot be replaced by restriction from `ℚ₂`, which reaches
only a small part of the square-class space.

## Intentional folds and abstractions

- Proposition 6.5 is proof-internal to the candidate-side evaluation; its output is the
  unramified/ramified definition used by Proposition 6.9.
- Corollary 6.19 assembles earlier source interfaces and adds no independent statement needed by
  downstream code.
- Display (100) is folded into `lemma_6_15_involution`, the composite formula actually consumed.
- Lemma 6.21 exposes the splitting consequence; its `d₂` identity is the proof mechanism.
- Lemma 7.1's head clause is stored as `R ≤ K ⊓ S`; the advertised quotient isomorphism then follows
  from the second isomorphism theorem and the block-generation equation.
- The isotypic decomposition and field-size relations used in Lemma 6.8 are theorem hypotheses.
  Deriving them from simplicity is the adjacent representation-theory argument, implemented where
  needed rather than baked into the display-level theorem.
- `lemma_6_22` is an explicit cochain identity modulo a coboundary rather than an opaque equality
  in `H²`; this exposes the correction term used by Proposition 8.8.

## The transgression proof

The proof of `lemma_6_21` constructs the polar equivalence `B_q^♭ : V ≃ V^∨`, identifies the fibre
antisymmetrization with the polar form, and proves the cochain identity
`δ(mixedA)=B_q^♭ f`. The raw `mixedA` is not additive; its defect is cancelled by the correction
provided by the fixed equivariant `κ⁰_q` datum. The corrected primitive is additive, so
`B_q^♭`-bijectivity produces the required `V`-valued cochain and hence a splitting section.

This explains why the restored base-class hypothesis is load-bearing and why no separate spectral
sequence formalization is needed in the final Lean proof.

## Downstream use

- Propositions 6.9 and 6.18 provide the base Gauss values used by §8's Fourier calculation.
- Lemmas 6.21 and 6.22 construct the affine-lifting and phase-cover data of Proposition 8.8.
- The §7 minimal block supplies the `T`, `M`, `V`, and `q̄_λ` data used by the §8 recursion and §9
  induction.
- Lemmas 6.16 and 6.17 are internal to the ramified Proposition 6.18 route.
