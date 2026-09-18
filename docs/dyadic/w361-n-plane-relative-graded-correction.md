# W361 — a uniform relative mixed-Lie correction identity

Independent mathematical calculation, 2026-09-17, coordinated with the N
research lane. This is a proposed refinement of the general correction
argument, not a Lean theorem for the full free pro-two group and not an
assumed capstone premise. There is no nilpotency-class enumeration here.

## 1. Setting and the exceptional square term

Let F be free pro-two on `a,b,c,d,u_j,v_j`, with descending 2-central
filtration `F_1=F`, `F_(n+1)=F_n^2 [F_n,F]`. Write L for its associated
mixed Lie algebra over F2, and pi for the degree-raising square operation.
Let the partner involution s exchange `a,b`, `c,d`, and `u_j,v_j`.

For corrections `t_i` in degree `j-1`, where `j>=3`, the N relation's
linearized correction has the form

\[
\delta(t)=\pi t_a+[t_a,a]+[t_a,b]+[a,t_b]
 +[t_c,d]+[c,t_d]
 +\sum_j([t_{u_j},v_j]+[u_j,t_{v_j}]).
\]

The ordinary bracket terms are symmetric in characteristic two. There are
two traps: the head derivative includes both `ad_a` and `ad_b`, and for
degree-one v,g one has

\[
[\pi v,g]=\pi[v,g]+[[v,g],v].
\]

Above degree one, pi is additive and commutes with the applicable bracket.
Consequently, for every `m>=1`,

\[
[\pi^m v,g]=\pi^m[v,g]+\pi^{m-1}[[v,g],v].
\]

The exceptional term persists after multiplication by higher pi powers;
it cannot simply be omitted for `j>3`. These conventions agree with the
mixed-square identities and N derivative in [Labute, *Classification of
Demushkin Groups*, Proposition 2 on printed p. 113 and section 4.1 on
pp. 124–126](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/3045C3866BBC24C718D94C18F8F68E58/S0008414X00054158a.pdf/classification-of-demushkin-groups.pdf).

## 2. Explicit kernel vector with a prescribed ordinary row

Fix a slot `i != a`, let `g=s(i)`, and fix a degree-one **basis vector**
`v != b`. Thus `g != b` too. Put

\[
m=j-2\ge1,\qquad P=\pi^{m-1},\qquad q=[v,g],\qquad p=Pq.
\]

Starting with the zero correction vector k, make these additive assignments:

| Slot | Increment |
|---|---|
| i | `pi^m v` |
| a | `p` |
| b | `p` |
| s(v) | `P(q+[g,b])` |
| s(g) | `P[v,b]` |

Repeated slots mean sums, not overwrites. In particular `s(g)=i`.
Because `v,g != b`, neither of the last two slots is a. The formulas also
allow `v=a`, `g=a`, or `v=g`.

The contribution from the first slot is

\[
\pi^m q+P[q,v].
\]

The head and b increments together contribute

\[
\pi^m q+P[q,b],
\]

because the two `P[q,a]` terms cancel. The final increments contribute

\[
P[q,v]+P[[g,b],v]+P[[v,b],g].
\]

Jacobi gives `[[g,b],v]+[[v,b],g]=[[v,g],b]=[q,b]` in characteristic two.
Every term therefore cancels and **delta(k)=0**.

All increments except the chosen `pi^m v` are pi powers of commutators.
Thus k changes precisely that ordinary graded row, while all compensating
increments have ordinary row zero. Summing such vectors handles arbitrary
ordinary rows in every non-head slot, provided the b-coordinate of each row
vanishes. No basis-vector independence beyond the stated mixed-Lie setup is
used in the cancellation, so coincident-slot cases cause no exception.

As an independent algebra check, the base identity was expanded exactly in
the free associative algebra `F2[p]<a,b,v,g>`, using
`pi(v)=p*v+v*v` for degree-one v and `pi(q)=p*q` for commutators q. All
monomials cancel. Multiplication by the formal factor P supplies arbitrary
m. This symbolic check is not a finite group experiment or a substitute
for the filtered-group realization below.

## 3. How this could refine the general normalization proof

There is a cleaner invariant than only the common DN-character kernel.
Let `W=closure[F,F]`. Start with the free basis which replaces c by
`c^kappa` and fixes all other generators. Since kappa is odd, it has the
same Frattini basis and the same canonical orientation values. The
standard N word evaluated on this basis has exactly the original **full
free abelianization**, namely `(2+2^alpha)*a`. The initial relator error
therefore lies in `W intersect F_3`.

Suppose at a stage the error lies in `W intersect F_j`, and the usual
orientation-crossed derivation condition supplies a degree `j-1`
correction. Projection of its derivative to ordinary associated graded
abelianization is just `pi*ab(t_a)`. All bracket contributions vanish
there. Since pi is injective on that ordinary graded module, error
abelianization zero forces the head row to be zero. Corrections lie in
the orientation kernel, so their ordinary b-coordinates are zero.
The kernel vectors above remove every other ordinary row without changing
the derivative.

One must then lift the resulting classes by actual elements of
`W intersect F_(j-1)`. The expected elementary argument is exact:
an element of `F_(j-1)` with ordinary graded row zero has abelianization
divisible by `2^(j-1)`. Remove those abelianization coordinates by pure
generator `2^(j-1)`-powers in `F_j`. This leaves its degree `j-1` class
unchanged and puts the resulting representative in W.

Using those representatives preserves every full abelianization row and
therefore keeps the next error in W. The canonical orientation values
also persist, so the standard N word continues to be killed by every
orientation-crossed derivation. This is the mechanism by which the
unrestricted correction criterion could be iterated relatively.

The following bridges still require explicit development and verification
before asserting a new group-automorphism theorem:

1. The strict ordinary-abelianization filtration and exact W lifting just
   described, with the chosen topology and index conventions.
2. The unrestricted correction criterion for every changing basis, and
   the identification of its graded derivative with the displayed delta.
3. The inductive error and crossed-derivation invariants after choosing
   the W-valued representatives.
4. Convergence of the corrected bases, preservation of the literal
   relator and full abelianization in the limit, and the resulting
   continuous automorphism and descent.

Update: the new checked `MarkedCore/FreeProTwoCharacterCorrection.lean`
now supplies the exact representative part without assuming an
abelianization isomorphism. Its
`exists_freeTwo_characterZero_same_twoCentralClass` takes `x in F_m`
and coordinate divisibility by `2^m`, and produces a representative in
the same `F_(m+1)` coset killed by every ordinary Z2 character.
`freeTwo_characterZero_commutative` also makes it invisible to every
commutative pro-two target, including orientation. For this argument use
`m=j-1`. Connecting zero ordinary graded row to that explicit divisibility
premise is still required; the representative construction itself is no
longer merely a proposed step. No identification of this common kernel
with a separately constructed commutator quotient is needed to use those
two APIs.

If those bridges are proved, the argument treats every handle rank at
once and preserves the literal relator, not merely the isomorphism class
of its quotient. At present the explicit delta-kernel identity is the
independently checked new calculation; the complete filtered/profinite
theorem is not claimed here.

## 4. Checked Lean artifact and exact input boundary

`GQ2/Dyadic/MarkedCore/NPlaneMixedLieKernel.lean` is now banked and cached.
It compiles warning-free at default limits. Its ten public audit pins use
only subsets of `[propext, Classical.choice, Quot.sound]`; the algebraic
cancellation itself uses only `propext`. No axiom, option, or admitted proof
was introduced.

The checked setting is deliberately abstract:

- A `LieRing L` with `forall x, x+x=0`.
- Additive maps `P,H : L ->+ L`, with
  `P[[x,y],z]=[P[x,y],z]` for all x,y,z.
- The single mixed relation
  `[w,g]=H(P[v,g])+P[[v,g],v]`.
- An arbitrary finite index type and an involutive partner map with
  `partner(a)=b`, `a!=b`, `i!=a`, and `v!=b`.

`nMixedDerivative_kernelVector` proves that the explicit five-increment
vector is in the full derivative kernel. `nMixedKernelVector_row` proves
that any additive row map killing the powered commutators sees exactly
the single prescribed row. `nMixedDerivative_row` computes ordinary
projection as `Hbar(row(t_a))`, given its explicit commuting-square equality
at that head correction (not a global intertwining assumption) and
bracket-vanishing hypotheses. `nMixedDerivative_headRow_eq_zero` then
proves the head-row constraint assuming `Hbar` is injective.

These hypotheses describe actual algebraic operations, not an assumed
group lift. In the intended positive associated graded Lie algebra,
`P` is the pi power on commutator degrees and `H` is pi on correction
degree; any extension to a total additive map must be supplied explicitly.
The mixed square is not additive on degree one, so simply calling it a
global additive endomorphism is invalid. An additive extension from the
degree-at-least-two part can serve the kernel calculation; the separate
head-row equality is only required at the actual correction, whose degree
is at least two. No global ordinary-square intertwining in degree one is
assumed by the final API.
Their mixed identity and the injectivity of the ordinary square map
must be connected to the concrete free pro-two filtration. The file does
not contain that instantiation, the exact representative construction,
the inductive normalization, or its limit. Those are precisely the
remaining bridges listed in section 3.

## 5. Later W361 update: the actual group identity and adapter are checked

The abstract Lie artifact above remains correctly scoped, but the kernel
calculation no longer needs its proposed global associated-graded adapter.
The new `Roe/Labute/MixedPowerCongruence` proves the exceptional power
identity in actual two-central quotients at every depth. The new
`MarkedCore/NPlaneMixedGroupKernel` proves the five-factor cancellation
directly by Hall–Witt and uniform square transport. Finally,
`MarkedCore/NPlaneKernelTupleDerivative` proves that the actual ordered
tuple has trivial **actual arbitrary-rank N derivative**, and preserves
the literal N relator in the relevant quotient. Repeated slots are
allowed; the only ordinary-slot restrictions are `i!=0` and `v!=1`.

See [the actual group audit](w361-n-plane-actual-mixed-congruence.md) for
the exact statements, hypotheses, and verification. Thus the derivative
identification and this concrete kernel construction in item 2 above are
now checked. The unrestricted all-rank derivative image/correction
criterion and the resulting convergent normalization remain separate;
no strong N-plane scaling theorem is asserted by this update.
