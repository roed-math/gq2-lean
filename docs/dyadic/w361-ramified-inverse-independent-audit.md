# W361 independent inverse and Fox-matrix audit

2026-09-17. Read-only review of the proof modules; no production source was
changed. **No mathematical or source-hypothesis defect was found.** The
conclusions below concern the exported conditional matrix identities, not an
automatic discharge of all field hypotheses or approval of an appendix format.

## Polynomial inverse and its period

`SigmaNormalFoxPolynomialInverse.lean` proves, for an exponent-two additive
group and a fixed-point-free action S, that an odd action period m = 2k+1 gives

```text
P = S^-1 + S^-3 + ... + S^-(2k-1),
(1-S^-1) P = P (1-S^-1) = Id.
```

The full cyclic norm is zero because its value is S-invariant. Partitioning
that norm into its constant term and adjacent odd/even powers gives
`Id + P + S^-1 P = 0`. Exponent two supplies the required signs. The left
inverse is proved as well as the right inverse, using that P is a polynomial
in S. `polynomialPivotEquiv` therefore needs no finiteness once the period and
fixed-point-free hypotheses are supplied. Its identification with the older
`oneSubInvAction` uses the latter's finite-module interface.

The canonical finite period is **the order of the action permutation**
`MulAction.toPermHom C A sigma`, not the order of sigma in C. The proof maps
`powOmega2 sigma` to that permutation and proves its two-primary projection is
one. This justifies odd action order even when sigma itself has an additional
even-order kernel component. The final action-polynomial theorem explicitly
requires trivial action of `powOmega2 sigma`; fixed-point-freeness alone would
not justify odd action order and is not used to assert it here.

The zero module is valid. Its action order is one, k=0, and P is the empty
sum. The identity map on the zero module is the zero map, so both inverse
identities hold. More generally a period-one action together with the stated
fixed-point-free condition forces every vector to be zero. A scratch Lean
probe checked this edge and the period-one equivalence without adding a
nontriviality premise. No dimension or positive-rank conclusion is claimed.

## Ramified composition order

Write S and T for sigma and tau actions. The literal rows are

```text
d(x) = (U x_sigma + L x_tau, D x_2),
U = S^-1 ∘ (T-Id),       U^-1 = (T-Id)^-1 ∘ S,
D = -S^-1,              D^-1 = -S,
L = S^-1 - N_q(T),      N_q(T) = sum_(0<=i<q) T^i.
```

`AddEquiv.trans` is used in exactly this order. No commutation of S and T is
silently assumed. `columnShear U L` replaces the sigma coordinate by
`x_sigma - U^-1(L(x_tau))`; its inverse adds that term. Thus this is the domain
coordinate operation `x -> C(x)`, and the actual identity is

```text
diag(U^-1,D^-1) ∘ d ∘ C (x) = (x_sigma,x_2).
```

It is not an identity obtained by postcomposing d with a column operation or
by reversing `U^-1` and L. Both the shear and row scaling are additive
equivalences with displayed inverses. The only abstract pivot requiring
finiteness is `T-Id`, made invertible by finite fixed-point-freeness. The norm
term L is retained completely. These statements also permit the zero module.

## Actual ramified source and projection dependencies

`TameSpliceRamifiedFoxNormal.tameSplice_ramified_rows` is an equality on **all
cochains**, not just cocycles or sigma/tau-normal cochains. Its proof uses the
full projected Heisenberg shadow identity and then the already proved literal
compact-M row. The concrete pair/mobile wrappers discharge tame specialization
and endpoint conditions for their actual normalized, prime-corrected splice
words. They do not assume a matrix as an extra hypothesis.

The supplied hypotheses remain important:

- finite C, projected group D and coefficient group A; exponent-two A;
- a surjective `pi : C ->* D`, with the C-action equal to the D-action through pi;
- actual projected wild bases `pi(t.x i)=1` (not necessarily `t.x i=1` in C);
- the tame relation in C, nonzero even q;
- fixed-point-free tau action and trivial action of `powOmega2 tau`.

The proof transfers fixed-point-freeness and the two-primary-action condition
to D explicitly. Surjectivity is used essentially in the resolver argument:
`exponent D` divides `exponent C`. Consequently the same pinned level
`4 * exponent C` resolves the projected primal/dual word lifts and Heisenberg
lifts, including the pure-sigma evaluations used in shadow annihilation. There
is no unsupported switch to a smaller resolver and no faithful-action premise
hidden behind the word "projected".

No raw or spliced relator-death premise is required by these ramified wrappers;
the tame relation and the structural shadow hypotheses suffice for this
first-jet identity. Pair parameters require `1 <= alpha` and `j : Fin h`.
Mobile parameters permit every r, p, unit eta and h, including h=0. Selected
field unit equations such as the actual D value are separate source-coverage
facts, not silently inferred by the matrix theorem.

## Full unramified refinement

The stable `TameShadowTauColumn.lean` and
`Instances/TameSpliceUnramifiedFoxRows.lean` were also reviewed. They prove the
previously opaque tau coefficient is literally Id. Hence the actual pair and
mobile source rows are, on all cochains,

```text
d(x) = (S^-1 x_tau, x_tau + (Id-S^-1) x_2).
```

The shadow calculation first proves its tau-only jets vanish while retaining
the original word's base action. Death of the **changed splice** then makes
the remaining prefix action trivial. Neither the structural raw word nor the
compact template is assumed to die in C. The wrapper's `hr` still explicitly
requires both changed-family relators to die; this is appropriate for an
actual finite quotient representation and must not be erased in prose.

The other hypotheses are finite C/A, exponent-two A, trivial tau/wild action,
fixed-point-free sigma action and trivial `powOmega2 sigma` action. Here the
zero sigma column is validly deduced from chain-square because the sigma
coboundary block is surjective. That argument is **not** reused in the scalar
sector, where it would give no information. Scalar columns have their own
direct exponent proof in `TameSpliceScalarFoxNormal`.

## Staged proof-packet amendment

The amendment keeps the correct existential quantifier order: the selected
original branch, exact word/core/nu and certificate precede the reconstructed
equivalence; only the realization is calibrated. Original cyclotomic marking
is retained by characteristicness, not inferred from the calibrated maximal
pro-two square. The explicit warning against pointwise preservation of an
arbitrarily prescribed realization is necessary and present. The standing
`RamifiedIData K` scope and inherited axiom boundary are also present.

One citation clarification is recommended, not a mathematical correction:
Section 1 should cite
`FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange`
as its direct combined anchor. That theorem retains original G, exact
`SelectedWordProfile`, whole certificate and `AlignedMarkedFieldEquiv` in one
witness. `SelectedWordFinal` by itself records the calibrated G; its separate
use alongside `MarkedFinal` is mathematically sufficient but less literal.

No current matrix statement in the amendment overstates these exports: it
requests an appendix connecting evaluated rows and operations, and expressly
does not assert that format has been adopted. Future inserted matrices must
retain the sector hypotheses above, use action order rather than ambient
order in the inverse polynomial, and distinguish changed-word death in the
unramified sector from its absence in the ramified sector.

## Verification record

Independent default-limit source checks passed for
`SigmaNormalFoxPolynomialInverse`, `SigmaRamifiedFoxElimination`,
`TameSpliceRamifiedFoxNormal`, and `TameSpliceUnramifiedFoxRows`.
`/private/tmp/W361RamifiedInverseAudit.lean` checks the period-one edge and
prints the supplemental helper/dependency axiom footprints. Every reviewed
new declaration has at most `propext`, `Classical.choice`, and `Quot.sound`.
No code changes, new assumptions, axiom declarations, options or placeholders
were introduced by this audit. This is a source/interface check, not a new
whole-tree build or release sign-off.
