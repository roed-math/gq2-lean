# W361: strong N-plane scaling — bounded general investigation

Historical research checkpoint, 2026-09-17. The body below records six checked,
rank-uniform intermediate modules from when strong N-plane scaling was open.
That gap is now closed by the integrated, unconditional theorem
`nPlaneScalingHypothesis_general` in `NPlaneGeneralScaling.lean`, for every
`alpha >= 2` and every handle rank. The later
`nStabParam_fullFrame_lift_general` also realizes the specified torsion-sensitive
core rows with identity handles. See `w361-n-general-scaling-audit.md`,
`w361-n-full-row-independent-audit.md`, and `w361-final-verification.md` for
the subsequent proofs and current verification status. These results do not
assert the broader arbitrary handle-mixing stabilizer statement. The completed
selected-field presentation does not depend on that broader statement.

## Exact target and the failed shortcut

For every valid N exponent `alpha ≥ 2`, every handle rank `h`, and every
`kappa : Z₂ˣ`, `NPlaneScalingHypothesis alpha h` asks for **one** continuous
automorphism of `DN alpha h` which preserves the orientation and, for **every**
continuous character to additive Z₂, scales the selected `sigma` coordinate by
`kappa`, fixes `x2`, and fixes every other ordinary-character coordinate. The
quantifier order is `∀ kappa, ∃ Psi, ∀ f`; a correction depending on `f` is not
enough. The weak `NScalingHypothesis` is already supplied by the SL₂ construction,
but that construction scales the companion coordinate inversely.

The naive B8 construction multiplies every handle U-row by `kappa`. Its handle
blocks have determinant `kappa`, so subsequent within-handle SL₂ corrections
cannot make all those blocks identities. `NScalingAudit` records this genuine
failure of that candidate. It is not a nonexistence proof for strong scaling.
Nor does the mod-two cup form alone impose an integral symplectic obstruction.

## Checked result 1: an invisible head correction absorbs the central defect

`GQ2/Dyadic/MarkedCore/NPlaneCentralCorrection.lean` has three public pins, all
exactly the standard three Lean axioms. Write

```
e = 2 + 2^alpha,       z = [c,d],
R = a^e [a,b] [c,d] · handleTail.
```

For `alpha ≥ 2`, `e` is twice a unit, so the module proves
`∃ s : Z₂, s*e + kappa = 1`. In any pro-two target in which `z` is central,
the substitution `a ↦ z^s a`, `c ↦ c^kappa` preserves the **exact** displayed
relator, for an arbitrary unchanged handle tail. Every ordinary Z₂ character
kills `z`, so it sees the prescribed scaling on `c` and no change to `a`.

This is conditional on centrality of the selected commutator. Centrality is not
asserted in `DN`, and the substitution is not asserted to be an automorphism.
Its significance is that the simplest central/determinant obstruction can be
absorbed by a correction invisible to all the ordinary characters at once.

## Checked result 2: a concrete integral two-evaluation isometry

`GQ2/Dyadic/MarkedCore/NPlaneUnitaryShadow.lean` has eighteen standard-three pins.
It constructs the ring

```
S = {(u,w) in Z₂ × Z₂ : u ≡ w (mod 2)}
```

with involution `(u,w)* = (w,u)`, rather than assuming a matrix-lifting premise.
The unit `(1,kappa)` gives a skew-unitary selected-plane automorphism with
first-evaluation matrix `diag(kappa,1)`, while every handle is literally fixed.
For the actual N orientation value `v = -(1+2^alpha)^(-1)`, it also proves the
integral interpolation equation `1+a*(v-1)=kappa`; the same affine polynomial
takes every odd argument to a unit. No identification of this ring with a
quotient of the actual group Alexander module is asserted in that module.

## Checked result 3: the construction exists over the completed ring itself

`GQ2/Dyadic/MarkedCore/NPlanePowerSeries.lean` has twenty-four standard-three pins.
Here `Lambda = Z₂[[X]]` carries the coefficientwise p-adic topology, and
`B = 1+X` is an explicitly exhibited unit. For every odd unit `v`, the module
constructs a continuous Z₂-algebra involution

```
B* = v B^(-1),       X* = v(1+X)^(-1)-1.
```

The substitution is legitimate even though its constant coefficient is not
zero: `v-1` is topologically nilpotent. The proof constructs the required linear
topology of Z₂ from ideal norm balls and uses convergent power-series evaluation.
Involutivity is proved on the dense polynomial subring and then by continuity.

Choose the checked affine coefficient `a` above, and set `g = 1+aX`. This is a
unit because its constant coefficient is one. For the form

```
J_v(x,y) = x1* y2 - x2* y1,
```

the map `diag(g*,g^(-1))` is an actual Lambda-linear automorphism preserving
`J_v`. Ordinary constant-coefficient evaluation gives `diag(kappa,1)`, since
the constant coefficient of `g*` is `1+a*(v-1)=kappa`. The public theorem
`exists_nSeriesFullPlaneScale` adds any finite number of hyperbolic handle
planes and fixes all those handle vectors literally.

This removes a possible integrality objection to this **coefficient-module
construction**. It does not identify the constructed free module or form with
the Alexander module/intersection pairing of `DN`. In particular, the torsion
head, the choice of left/right module convention, and any coupling to it have
not been transported through such an identification. It also does not lift
the resulting isometry to an automorphism of a free pro-two group or of `DN`.

## Checked result 4: the exact nonlinear boundary equation

`GQ2/Dyadic/MarkedCore/NPlaneRelativeBoundary.lean` has three pins using only
`propext` and `Quot.sound`. With `H = [c,d] · handleTail`, it proves, in every
group and at arbitrary handle rank,

```
a^e [a,b] H = 1
  iff
b^(-1) a b = a^(-(1+2^alpha)) H^(-1).
```

This is the exact stable-letter boundary equation before any abelianization.
It is not a theorem that a proposed pro-two HNN decomposition is proper. If a
relative substitution fixes `b`, its new `a'` and `H'` must satisfy this same
equation. A unitary module identity alone does not imply it.

## Precise remaining bridge

A viable completion must supply more than the constructed matrix:

1. Identify the relevant actual N Alexander object, orientation involution,
   head/torsion relations, and selected free hyperbolic part with the proposed
   coefficient model, including the ordinary-character specialization.
2. Realize the chosen unitary transformation by a continuous free pro-two
   substitution with the required ordinary abelianization and orientation.
3. Correct that substitution to preserve the closed normal subgroup of the
   actual relator, or preserve an appropriate exact relative boundary, **without
   changing the prescribed ordinary-character rows**. Then verify descent and
   invertibility. Merely preserving a linearized relation does not suffice.

The parameter convention also needs care. With deck action
`B(a)=b^(-1)ab`, the head relation in the orientation-kernel abelianization is
`(B+1+2^alpha)a=0`, whose root is `B=v^(-1)`. The completed-ring involution
is constructed for every odd parameter, but the identification of its parameter
with the actual N pairing must not be silently assumed.

## Checked group-level tools added after the coefficient construction

`GQ2/Dyadic/MarkedCore/FreeProTwoCommutatorShear.lean` has nine standard-three
pins. At arbitrary finite rank it constructs a genuine continuous automorphism
of the free pro-two group taking `c` to `c[c,b]^s` and fixing the other marked
generators, for every `s : Z₂`. It is simultaneously invisible to every ordinary
Z₂ character on every group element. The proof uses the pro-two Frattini
criterion and profinite Hopficity. No relative boundary is asserted to be
preserved. In particular, a discrete-free-group restriction of determinants to
monomials cannot be imported without proof into this larger automorphism group.

`GQ2/Dyadic/MarkedCore/FreeProTwoCharacterCorrection.lean` has ten standard-three
pins. It constructs all coordinate characters and proves the exact formula
expressing any ordinary character through them, using the free universal
property rather than assuming an abelianization identification. If all
coordinates of `x` are divisible by a natural number `d`, and a closed subgroup
H contains all generator d-th powers, it constructs `x'` with
`x^(-1)x' in H` and **every** ordinary character killing `x'`. Normality of H
is not required. The concrete corollary is

```
x in F_m,  and  2^m divides every coordinate of x
  implies
there is x' in F_m with x^(-1)x' in F_(m+1)
and every ordinary character kills x'.
```

The extra divisibility hypothesis is essential and remains explicit. The same
file proves that such a character-zero element is killed by every continuous
homomorphism into a commutative pro-two target, including the orientation-unit
target. This supplies the exact-representative seam, not the missing relative
graded-image theorem.

`GQ2/Dyadic/MarkedCore/FreeProTwoUnitPower.lean` adds twelve standard-three
pins. For every finite free rank, selected generator, and `kappa : Z₂ˣ`, it
constructs the genuine free pro-two automorphism `c ↦ c^kappa`, fixing every
other marked generator, with explicit inverse given by `kappa⁻¹`. The same
automorphism has the exact selected diagonal row under every ordinary character;
an all-element coordinate formula is also proved. For the N word at every
handle rank and every alpha, provided only that the selected index is not the
torsion head `0`, the literal initial error

```
nRelWord alpha (unitPowerMark c kappa) * (nRelWord alpha originalMark)^(-1)
```

lies in `F_3` and is killed by every homomorphism to every abelian group.
The filtration proof uses that a unit power differs from the original generator
by a square, whose image is central modulo `F_3`; it does not enumerate ranks
or filtration classes. This now supplies the initial approximation of the
relative-correction proposal below. It does not assert that this error is one.

`GQ2/Dyadic/MarkedCore/FreeNOrientation.lean` adds seven standard-three pins.
The canonical free orientation sends `b` (index 1) to `nUnit alpha` and every
other generator to one. The exact commutative-coordinate formula identifies
it with `nUnit alpha` raised to the ordinary b-coordinate. The previously
established `nUnit_zpowZtwo_injective` theorem then proves, for `alpha >= 2`,
that its kernel equals the kernel of that ordinary coordinate. Thus an
orientation-kernel correction has **zero integral b-coordinate**, justifying
the omission of `v=b` in the relative kernel-vector construction. No new
p-adic analytic input is assumed. The initial power automorphism preserves
this orientation whenever its selected generator is not b, and its N relator
error lies in the orientation kernel whenever the selected generator is not a.

`GQ2/Dyadic/MarkedCore/NPlaneKernelTuple.lean` adds six audit pins contained
in the standard-three set. It constructs the actual five-factor multiplicative
tuple agreed with the mixed-group calculation, uniformly for any index type
with decidable equality. Coincident slots multiply in order. For parameter n,
every entry lies in `F_(n+2)`; under any ordinary Z₂ character the only nonzero
row is slot i, with value `2^(n+1) f(v)`. The stronger abelian-target formula
is also literal. The tuple has canonical N orientation one when `v` is not b.
These are actual group depth and row theorems, not a derivative assertion.

`GQ2/Dyadic/MarkedCore/NPlaneCrossedDefect.lean` adds four standard-three
pins. Exact canonical orientation values imply that every crossed-derivation
lift to `WordLift Z₂ Z₂Units` kills the actual N word and the actual defect
between two such markings. This holds at every handle rank without assuming
either a basis or a filtration condition. The required basis remains part of
the separate, unproved unrestricted stage-image theorem. Its precise
theorem-shaped gap and local support map are recorded in
`w361-n-plane-unrestricted-stage-gap.md`.

`GQ2/Dyadic/MarkedCore/NPlaneKernelDiagonal.lean` adds seven standard-three
pins connecting the tuple to the **current** marking. If the current free
tuple has exact diagonal coordinate weights `u_v : Z₂ˣ`, its kernel tuple
has coefficient `2^(n+1) u_v` at the selected slot/coordinate pair and zero
elsewhere. The coefficient is not silently replaced by `2^(n+1)`. The
initial unit-power marking supplies these equations with weight kappa at the
scaled generator and one elsewhere. Exact current orientation rows supply
orientation-one correction factors, independently of the original literal
generator marking. Neither the coordinate equations nor this adapter assert
an unrestricted stage preimage.

`GQ2/Dyadic/MarkedCore/NPlaneRowRefinement.lean` adds two standard-three
pins assembling the finite all-row interpolation in the actual closed N
derivative-kernel subgroup. Its input is an existing depth-`n+2` correction
tuple with exact zero head coordinates and orientation one, at a current
marking with diagonal unit coordinate weights. It produces a correction at
the same depth, killed by every ordinary character and by the orientation,
with the same actual relator value in `Q_(n+4)`. Non-head divisibility is
derived from filtration depth; the finite tuple group's pro-two property is
proved, not carried. The initial correction's existence and the separate
head cleanup remain outside this theorem. This closes the all-row assembly
without making a derivative-image claim.

`GQ2/Dyadic/MarkedCore/NPlaneFreeStageTransfer.lean` adds five standard-three
pins. It constructs the canonical surjective free-group map to DN and proves
its orientation compatibility. An actual free automorphism with the prescribed
diagonal coordinates, canonical orientation rows and relator error in lambda_k
then yields the literal DN stage consumed by `NPlaneCompactness`. All ordinary
characters are handled simultaneously, and Frattini generation follows from
the supplied free basis and quotient surjectivity. This transfer does not
produce free stages; it removes the remaining conditional interface between
such stages and the existing compactness endpoint.

## New uniform relative-correction candidate

The independent note `w361-n-plane-relative-graded-correction.md` gives a more
direct proposed route than identifying a full Alexander pairing. Its new
`NPlaneMixedLieKernel` module checks an explicit graded derivative-kernel
vector, including the exceptional mixed-square term in degree three and
coincident index slots. The vector can remove a prescribed ordinary row from
every non-head correction slot without changing the derivative. The head row
is constrained instead by ordinary abelianization and injectivity of its square
map. This is an abstract mixed-Lie theorem, not an instantiated free-group stage
theorem.

Starting with `c ↦ c^kappa` keeps the full free abelianization of the N relator
unchanged. The intended refinement is to take Labute's successive corrections,
remove their ordinary graded rows by those kernel vectors, and then use the
exact representative theorem above. This would preserve all ordinary rows at
every stage. The concrete group derivative, unrestricted stage-image result,
filtration-to-row translation, error invariants, and limiting automorphism
still need to be assembled and checked. The strong hypothesis remains unproved;
the new calculation is not being substituted for those obligations.

## Primary-source check and limitation

Labute's [Classification of Demushkin Groups (1967)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/3045C3866BBC24C718D94C18F8F68E58/S0008414X00054158a.pdf/classification-of-demushkin-groups.pdf),
§4 and Theorem 5, uses the orientation kernel and its completed module in the
N-form normalization. Its iterative corrections lie in the orientation kernel;
the statement does not additionally put them in the common kernel of all
ordinary Z₂ characters. The classification theorem therefore cannot be cited
as a ready-made lift preserving our specified integral rows. A relative
correction theorem, or a new proof of that extra property, is still needed.

## Verification boundary

All thirteen modules were checked at default limits, warning-free, and their own
oleans were generated with the campaign runner. There are 110 public audit pins,
all contained in the standard three-axiom set. No old hypothesis, axiom,
certificate, or selected-presentation endpoint was changed. There is no claim
here either proving or disproving `NPlaneScalingHypothesis`.
