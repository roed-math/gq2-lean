# W361: literal polynomial inverses in the original Fox records

Status: both source modules checked at default Lean limits, with every public
declaration at most `propext`, `Classical.choice`, and `Quot.sound`. No original
grammar, certificate record, frozen fixture, or acceptance contract was changed.

## What is now produced

`Instances/TameSplicePolynomialFoxCertificates.lean` supplies
`pairSplice_FoxCertificate_unramified_identity` and
`mobileSplice_FoxCertificate_unramified_identity`.

`Instances/TameSpliceRamifiedPolynomialFoxCertificates.lean` supplies
`pairSplice_FoxCertificate_ramified_identity` and
`mobileSplice_FoxCertificate_ramified_identity`, through the generic
`tameSplice_FoxCertificate_ramified_identity`.

These are actual values of the **original** `FoxCertificate` record, not merely
additive-equivalence elimination statements. Their types bind the exact
normalized, prime-corrected, spliced pair/mobile word, its marking, and the
pinned resolver at `4 * Monoid.exponent C`. The records contain the operation
lists, formal inverse witnesses, literal identity-pivot target, and proof of
the full all-cochain matrix equality.

The scalar records already supplied by `TameSpliceFoxCertificates` have target
`(x_tau, 0)` and the single subtraction of the first row from the second. Thus
all three action sectors now have original-format fully reduced records.

## Unramified operations

Write `S` for sigma action, `D = 1-S^-1`, and let `2k+1` be the **order of the
actual action permutation** of sigma. Its oddness follows from the hypothesis
that the two-primary projection of sigma acts trivially; odd ambient element
order is not assumed.

The formal expression

`P_S = S^-1 + S^-3 + ... + S^-(2k-1)`

uses only `FoxCoeff.zero`, `add`, and the existing integer-power generator
atoms. It is not a new inverse atom. Both identities `P_S D = 1` and
`D P_S = 1` are proved.

The actual full rows are

`(S^-1 x_tau, x_tau + D x_2)`.

The record lists, in order:

1. Scale the first row by `S`, carrying `S^-1` as inverse.
2. Subtract the first row from the second.
3. Scale the second row by `P_S`, carrying `D` as inverse.

There are no column operations. The target is literally
`⟨FoxRowNormalForm.single .tau, .single (.wild (x2Idx h))⟩`.

The concrete source producers retain exponent-two coefficients, trivial wild
and tau action, fixed-point-free sigma action, trivial two-primary sigma
action, and **actual changed-word** relator death. They do not require death of
the unspliced or unnormalized word. Handle rank is arbitrary.

## Ramified operations and composition order

Write `T` for tau action. The actual operator blocks are

`U = S^-1 (T-1)`, `D = -S^-1`, `L = S^-1 - sum_{i<q} T^i`.

Now let `2k+1` be the order of the actual tau action permutation. Its oddness
follows from trivial two-primary tau action. In exponent two,

`P_T = T + T^3 + ... + T^(2k-1)`

is the inverse of `T-1`. The formal inverse of `U` is

`U^-1 = P_T ∘ S`.

**Sigma is applied first.** The proof does not commute `S` and `T`. All norm and
polynomial sums are recursively constructed in the unchanged coefficient
grammar. The record performs the single formal column transvection

`x_sigma ↦ x_sigma - U^-1 (L x_tau)`

and then scales the two rows by `U^-1` and `-S`, carrying `U` and `D` as their
respective formal inverses. Both scale products are proved in both orders. The
column operation has the ordinary distinct-generator witness sigma ≠ tau.

The target is literally
`⟨FoxRowNormalForm.single .sigma, .single (.wild (x2Idx h))⟩`.

The full projected-head hypotheses are retained: a surjective finite head
projection inducing the same coefficient action, projected wild generators
equal to one, the tame relation, fixed-point-free tau action, and trivial
two-primary tau action. Wild elements need not themselves be one in the
original head group. No raw or changed relator-death hypothesis is added in
this sector. Concrete pair/mobile producers discharge the structural endpoint
and tame-specialization premises; neither takes an unknown matrix premise.

## Scope and edge cases

The two modules have 12 and 20 public declarations respectively. The formal
expression factories themselves are axiom-free. All remaining public pins
are bounded by the standard three Lean axioms.

The coefficient group can be zero. In that case the action order is one,
`k=0`, and the empty polynomial evaluates to the unique endomorphism, which is
also the identity of the zero group. No nonzero-module premise is hidden.

The polynomial length varies with the finite action order, not with a bounded
list of field classes or handle ranks. This adds original-record content; it
does not itself claim owner approval of the staged compositional publication
appendix or migrate the frozen one-tree export grammar.
