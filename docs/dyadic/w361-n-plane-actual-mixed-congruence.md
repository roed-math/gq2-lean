# W361 — actual uniform mixed-power and relative correction congruences

Checked arithmetic-free group identities, 2026-09-17. These are additive
research results, not a producer of the strong N-plane scaling hypothesis.

## Mixed powers in the actual group tower

`GQ2/Roe/Labute/MixedPowerCongruence.lean` works for an arbitrary
topological group, with the existing one-based lower two-central series
`lambda_1=G`. It assumes neither freeness, finiteness, compactness, nor a
pro-two hypothesis. The repository convention is
`[x,y]=x^-1*y^-1*x*y`.

For every `m>=1`, `commP_pow_two_level` proves

\[
[v^{2^m},g]=[v,g]^{2^m}[[v,g],v]^{2^{m-1}}
\quad\text{in }G/\lambda_{m+3}.
\]

`commP_pow_two_congruence` gives the equivalent literal subgroup-membership
statement. The exceptional triple term is not omitted at larger depths.
The proof uses the exact group square-commutator identity in the initial
quotient, then the existing square lift and grading estimates uniformly.
No finite collection of classes is tested or substituted for induction.

For `x in lambda_j`, `j>=2`, `commP_pow_two_level_of_mem` additionally gives

\[
[x^{2^n},g]=[x,g]^{2^n}
\quad\text{in }G/\lambda_{j+n+2}.
\]

The module exposes two reusable infrastructure lemmas: iterated squaring
raises depth by its iteration count, and equality in the level `k` quotient
implies equality of squares in the level `k+1` quotient.

## An actual uniform relative correction word

`GQ2/Dyadic/MarkedCore/NPlaneMixedGroupKernel.lean` defines, for arbitrary
`a,b,v,g` and `n>=0`,

\[
q=[v,g],\quad p=q^{2^n},\quad w=v^{2^{n+1}},\quad
r=(q[g,b])^{2^n},\quad s=[v,b]^{2^n}.
\]

Its checked `nMixedCorrectionWord_level` proves

\[
[w,g]\,p^2\,[p,b]\,[r,v]\,[s,g]=1
\quad\text{in }G/\lambda_{n+4}.
\]

All four correction elements `w,p,r,s` lie in `lambda_(n+2)`.
The initial cancellation follows from the existing Hall–Witt theorem in
the actual fourth quotient. The induction squares every contribution and
uses the two-central bounds to kill all cross terms; the same formula
therefore holds at every correction depth.

The five-factor expression groups the ordinary-slot, head-slot,
b-slot, partner(v)-slot, and partner(g)-slot contributions. In the
head/b pair the two `[p,a]` contributions cancel because they lie in the
central exponent-two top layer. The accompanying unsuppressed-head
version records that literal order for later derivative assembly.
Its exact public name is `nMixedCorrectionWord_with_head_level`.

## Actual arbitrary-rank derivative and relator adapter

`GQ2/Dyadic/MarkedCore/NPlaneKernelTupleDerivative.lean` now assembles the
literal ordered tuple from `NPlaneKernelTuple` with the actual derivative
from `NPlaneFilteredDerivative`, its multiplicativity, and the uniformly
paired alphabet from `NPlaneFilteredSlots`.

`nPlaneKernelTuple_filteredDerivative` assumes an arbitrary topological
group, `n>=0`, arbitrary `h`, a marking `letter : Fin(coreRank h) -> G`,
and indices `i!=0`, `v!=1`. It proves

\[
D_{\bar{\mathrm{letter}}}
 \bigl(\overline{\mathrm{nPlaneKernelTuple}(n,0,1,i,v,
                  \mathrm{letter},\mathrm{nPartner})}\bigr)=1
 \quad\text{in }G/\lambda_{n+4}.
\]

The correction entries lie in `lambda_(n+2)`. No distinct-support premise
is used: multiplication of derivative values handles all coincident
slots, including `v=0`, `nPartner i=0`, and `v=nPartner i` when the two
stated exclusions permit them. The paired alphabet is the actual
arbitrary-rank N alphabet, not an assumed comparison with a generic
derivative.

`nPlaneKernelTuple_nRelWord` then proves that applying the tuple preserves
the literal `nRelWord alpha` in that quotient, for every `alpha>=2` and
every `h`. This adapter retains the existing relator-shift theorem's
compact Hausdorff totally disconnected hypotheses. It does not assume
that the initial relator is already trivial.

## Exact remaining seam

These results remove the global mixed-Lie representation problem from
these particular identities and discharge the actual tuple-to-derivative
adapter. They do not themselves prove that the
unrestricted derivative image contains every required error, select a
relative correction at every stage, construct the filtered limit, or
give a relator-preserving free pro-two automorphism. The integral
ordinary-row and orientation controls are supplied by the separate
checked tuple module. The unresolved task is still the image/correction
existence argument and its convergent iteration, not these cancellation
identities.

`MixedPowerCongruence` was checked with the pinned Lean compiler and
project defaults, warning-free, with eight public axiom pins exactly
`propext`, `Classical.choice`, and `Quot.sound`. The shared-cache check is
not advertised as a new clean transitive build. Parent integration owns
the final source-only closure verification.

`NPlaneMixedGroupKernel` was separately checked and cached under the same
defaults, warning-free, with all four public theorem pins exactly those
same standard three axioms. Both new source modules are stable for
integration.

The actual tuple-to-derivative and relator adapter was also checked under
the defaults, warning-free, with both public pins exactly the standard
three. There are no new axioms, placeholders, resource-limit overrides,
or additional source-certificate assumptions in these modules.
