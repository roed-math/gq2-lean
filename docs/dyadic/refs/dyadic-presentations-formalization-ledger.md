# Dyadic presentations: formalization ledger

**Input reviewed:** `dyadic-presentations.tex`, July 2026 revision  
**Companion mathematical supplement:** `dyadic-presentations-formalization-proof.tex`  
**Goal:** a final Lean theorem whose only axioms are explicitly named classical local-field inputs, with no field-specific presentation-isomorphism axiom and no unchecked symbolic calculation.

## 1. Executive status

The revision fixes the definite compact-word error from the previous draft: both compact families now use

\[
x_2^{-\sigma}(x_2\tau)^{\omega_2}
\]

rather than the first-order-singular expression with \(\sigma_2\).

The all-fields theorem is still not proved by the uploaded TeX. The missing work is now sharply localized:

1. **Marked rank-four Demuškin automorphism lifting** for the standard \(M_\alpha\) and \(N_\alpha\) cores.
2. **Reflected Fox/Stokes/Hessian certificates** for the five genuinely relevant word rows: \(L\), \(N_0\), \(N_{\mathrm{pc}}\), \(M_0\), and \(M_{\mathrm{pc}}\).
3. **Field-generic packaging** of the already used deep-unit determinant argument.
4. **Degree-\(n\) parameterization** of the existing source-generic exact-image theorem.

The finite-target induction itself need not be redesigned. The current `gq2-lean` repository already has a pluggable `SourceData` record and a source-generic `thm_4_2_of_sources`; the degree-one constants in the record need to become parameters.

## 2. A new arithmetic correction

### 2.1 The sign-Frobenius row is not part of the ramified-\(i\) branch

For type \(M_\alpha\), write

\[
C=\langle-1\rangle\times\langle u\rangle,
\qquad u=(1-2^\alpha)^{-1}\in1+4\mathbf Z_2,
\]

and

\[
\lambda(-1)=\epsilon2^{r-1},\qquad \lambda(u)=\eta.
\]

If \(\eta\) is even, surjectivity forces \(r=1\) and \(\epsilon=1\). Then \(\ker\lambda=\langle u\rangle\), so the unramified quadratic cyclotomic quotient is the quotient on which \(-1\) acts nontrivially and \(1+4\mathbf Z_2\) acts trivially. Its fixed field is \(K(i)\). Therefore \(K(i)/K\) is unramified.

**Consequence:** under the paper’s hypothesis that \(K(i)/K\) is ramified, \(\eta\) must be odd. The sign row should be removed from the ramified-\(i\) assembly. The new theorem needs only compact and procyclic \(M_\alpha\) words.

### 2.2 Correct branch for \(\mathbf Q_2(\sqrt{-10})\)

The unique unramified quadratic extension of \(K=\mathbf Q_2(\sqrt{-10})\) is

\[
K(\sqrt5)=K(\sqrt{-2}),
\]

because \((-2)/5=(-10)/25\) is a square in \(K\). The corresponding character on \(\mathbf Z_2^\times\) is nontrivial on both \(-1\) and the procyclic generator congruent to \(5\bmod8\). Since \((-3)^{-1}\equiv5\bmod8\), the parameters are

\[
r=1,\qquad \epsilon=1,\qquad \eta=1.
\]

So the general **procyclic** \(M_2\) word applies. The field-specific relative-norm word may still be retained as an alternative, but it should not be described as a specialization of the sign row.

The general procyclic word with \((r,\epsilon,\eta)=(1,1,1)\) gives the same small-target counts as the field-specific alternative:

| target | count |
|---|---:|
| \(S_3\) | 6 |
| \(D_8\) | 1568 |
| \(A_4\) | 120 |

These counts are regressions, not proofs.

## 3. Corrections required in the mathematical interfaces

### 3.1 B1: boundary

The proof should be decomposed into theorem-level lemmas:

- finite tame inertia has odd order;
- `O2(T_q)=1`;
- the admissible wild subgroup is exactly `O2(Γ_R)`;
- the maximal pro-2 specialization kills \(\tau\) and sends \(\sigma_2\) to \(\sigma\);
- the relative Goursat common quotient is both pro-odd and pro-2, hence trivial.

These proofs are supplied in the companion supplement.

### 3.2 B2: exact lifting semantics

Use a literal defect theorem:

```lean
structure ExactLiftingSemantics
    (P : DyadicPresentation n) where
  d0 : A →ₗ[...] (Generator n → A)
  d1 : (Generator n → A) →ₗ[...] (A × A)
  chain : d1.comp d0 = 0
  defect_change : ...
  lift_iff_defect_mem_range : ...
  lifts_torsor_ker : ...
  natural : ...
  exact_coefficients : ...
```

The admissibility condition contributes no additional equation because the inverse image of a finite normal 2-subgroup through an elementary 2-extension is again a finite 2-group.

### 3.3 B3: nonsplit coefficients

The draft’s composition-series sentence becomes valid only after constructing a natural chain map

\[
\eta_A:C^\bullet(A)\to\operatorname{Hom}(C^\bullet(A^\vee),\mathbf F_2)[-2]
\]

that commutes with short exact coefficient sequences. Then use mapping cones or the two long exact sequences and the five lemma. Equality of dimensions on simple modules is not enough.

### 3.4 B4 must be affine

One unshifted Gauss sum does not identify every determinant fiber used in the exact-image recursion. For nonsingular \(Q\), a phase \(\ell=B_Q(-,y)\) satisfies

\[
\sum_x(-1)^{Q(x)+\ell(x)}=(-1)^{Q(y)}\sum_x(-1)^{Q(x)}.
\]

The missing sign must be matched by either:

- a boundary-marked quadratic isometry, or
- the source-independent phase-cover recursion already used in `gq2-lean`.

Do not define the source interface only by equality of the zero-phase sums. Reuse the actual fields of `GQ2/SourceData.lean`: half-torsor, phase separation, phase nondegeneracy, cocycle cardinality, and the two Gauss-residue leaves.

## 4. Existing Lean work that should be reused

The following paths in `roed-math/gq2-lean` already implement much of the generic architecture.

| Existing path | Reusable content | Required change |
|---|---|---|
| `GQ2/SourceData.lean` | Pluggable source record; boundary and seven exact-image supply families | Replace degree-one constants by parameter fields; generalize four marked generators to `Generator n` |
| `GQ2/ThmFourTwo.lean` | Source-generic strong induction and final finite-target comparison | Keep recursion unchanged; adapt to generalized source record |
| `GQ2/Roe/MarkedMatching.lean` | Abstract marked matching engine | Generalize the abelian matching object from rank three to rank four plus handles |
| `GQ2/Roe/MarkedPro2.lean` | Labute isomorphism + orientation + marking correction route | Add the two rank-four automorphism-lifting instances |
| `GQ2/Roe/Labute/Assembly.lean` | Rank-three source-specific Labute assembly | Use as the model for `M` and `N` core files, not as evidence that the rank-four theorem is done |
| `GQ2/Roe/Gauss.lean` | Finite quadratic/Gauss infrastructure | Parameterize the total dimension and sign |
| `GQ2/Roe/Hessian.lean` | Reflected Hessian organization | Extend the word syntax to `n+3` generators and profinite powers |
| `GQ2/DetRamified.lean` | Ramified determinant reduction to deep dimension and deep vanishing | Make the field and degree parameters explicit |
| `GQ2/DeepPart/Q0locLayer.lean` | Quadraticity, cup-product polarization, nonsingularity/deep subspace | Generalize the local source type from \(G_{\mathbf Q_2}\) to an arbitrary dyadic Tate-duality source |
| `GQ2/AnabelianBridge/Classification.lean` | Explicit rank-three orientation-preserving abelian automorphisms | Build rank-four `M` and `N` analogues |

## 5. Correct theorem decomposition

### 5.1 `MarkedCoreCertificate`

```lean
structure MarkedCoreCertificate
    (K : DyadicField) (P : ProTwoCore K.params.n) where
  abstractEquiv : ContinuousMulEquiv P.group K.maxProTwo
  orientation : K.chi.comp abstractEquiv.toHom = P.chi
  correction : ContinuousMulEquiv P.group P.group
  correction_chi : P.chi.comp correction.toHom = P.chi
  correction_nu :
    K.nu.comp (abstractEquiv.toHom.comp correction.toHom) = P.nu
```

Do not formalize the draft’s larger free-relator theorem unless it becomes useful elsewhere. It is enough to prove that the required abelian marking correction lies in the image of `Aut(P.group)`.

### 5.2 `WordCertificate`

```lean
structure WordCertificate
    (K : DyadicField) (P : ProTwoCore K.params.n)
    (R : PWord (Generator K.params.n)) where
  tameSpecialization : specializeTame R = 1
  proTwoSpecialization : specializeProTwo R = P.word
  exactLifting : ExactLiftingSemantics R
  stokes : StokesDualityCertificate R
  scalar : ScalarHilbertCertificate K R
  determinant : AffineDeterminantCertificate K R
```

### 5.3 Final theorem

```lean
theorem candidate_equiv_absoluteGalois
    (core : MarkedCoreCertificate K P)
    (word : WordCertificate K P R)
    (local : DyadicLocalInput K) :
    Nonempty (ContinuousMulEquiv (candidateGroup K R) K.absoluteGalois)
```

The proof should only assemble the certificates and call the generalized source theorem.

## 6. Local determinant theorem

### 6.1 Well-definedness and polarization

For cohomologous cocycles, graph homomorphisms into \(V\rtimes H\) are conjugate by \(V\); inner automorphisms act trivially on cohomology. The polarization is

\[
B_Q(x,y)=\operatorname{inv}_K(x\smile_{b_q}y),
\]

and is nonsingular by Tate duality.

### 6.2 Unramified sign

For \(E=\mathbf F_{2^{2e}}\), \(E_0=\mathbf F_{2^e}\), and \(x^*=x^{2^e}\), one Hermitian line has

\[
Q_a(x)=\operatorname{Tr}_{E_0/\mathbf F_2}(a x x^*)
\]

and

\[
\sum_{x\in E}(-1)^{Q_a(x)}
=1+(2^e+1)\sum_{t\ne0}(-1)^{\operatorname{Tr}(at)}
=-2^e.
\]

An orthogonal sum of rank \(n\) has sign \((-1)^n\).

### 6.3 Ramified sign

Package the proof into four exact leaves:

1. projective inflation-restriction/Kummer identification;
2. no ramified simple in the middle or valuation pieces of the dyadic square-class filtration;
3. deep part has dimension \(n\dim V/2\) and polar form zero;
4. normalized Shapiro-Evens/deep-unit theorem makes the quadratic function itself zero there.

The deep part is then a totally singular Lagrangian, so the Gauss sign is positive.

Delete the draft phrase “when the inertia order is even”: finite tame inertia in residue characteristic two has odd order.

## 7. Word-certificate acceptance tests

For every branch, the repository should contain a generated appendix with:

1. the exact syntax tree;
2. the two specialization reductions;
3. the evaluated Fox Jacobian;
4. a list of invertible row and column operations;
5. the reduced normal matrix;
6. the Stokes chain identity;
7. the extraspecial Hessian;
8. the change of variables to quadratic normal form;
9. the affine phase-cover certificate;
10. a hash tying the generated TeX formula to the Lean syntax tree.

Expected normal-form endpoints:

| branch | quadratic endpoint |
|---|---|
| \(L\) | existing \(n=1\) core plus hyperbolic handles |
| compact \(N\) | \(q(c_0)+b_q(c_0,c_1)\) |
| noncompact \(N\) | \(Q_0(c_0)+b_q(c_1,L_c c_0)\), with explicit invertible \(L_c\) |
| compact \(M\) | the two projector cases claimed in the draft, each with explicit change of variables |
| procyclic \(M\) | self-replicated raw determinant cancellation plus canonical split form, including every \(T\)-dependent central term |

The phrase “the nonsingular core matrices below” must be replaced by the actual matrices.

## 8. Degree-\(n\) source record

The current source record contains degree-one values such as

- `#Hom_cont(Γ,F₂) = 8`,
- `#Z¹(Γ,V) = |V|²`,
- lift multiplicities `|M|²` and `|T|² × fixedPts`,
- the degree-one Gauss magnitude.

Do not scatter replacements throughout the induction. Add numerical fields to a parameterized source record, for example:

```lean
structure SourceNumerics (n : Nat) where
  homScalar : Nat
  homScalar_eq : homScalar = 2 ^ (n + 2)
  z1Simple : ∀ V, Nat
  z1Simple_eq : ... = Nat.card V ^ (n + 1)
  gaussMagnitude : ∀ V, Int
  ...
```

Then define the two source instances from their cohomology packages. The recursion should consume only equality of the two sources’ leaves, not rederive the formulas.

## 9. Implementation order

1. `Dyadic/Parameters.lean`: branch data, semantic generators, profinite exponents, `ω₂` finite evaluation.
2. `Dyadic/TameBoundary.lean`: all B1 lemmas and relative Goursat.
3. `Dyadic/ArithmeticBranches.lean`: eliminate the sign row; add the corrected \(\sqrt{-10}\) instance.
4. `Dyadic/LocalGauss.lean`: group-generic determinant construction and arbitrary-degree sign.
5. `Dyadic/SourceDataN.lean`: parameterize the existing source record and prove the compatibility adapter.
6. `Dyadic/MarkedCore/M.lean` and `N.lean`: rank-four abelian classification and automorphism lifting.
7. `Dyadic/WordSyntax.lean`, `Fox.lean`, `Stokes.lean`, `Hessian.lean`.
8. Branch certificates in this order: compact \(N_2\), compact \(M_2\), noncompact \(N\), procyclic \(M\), odd \(L\).
9. Final field theorem, followed by `#print axioms` reports.

## 10. Merge gates

Every merge must pass all of the following.

- No `sorryAx`.
- No new axiom asserting a presentation is isomorphic to a local absolute Galois group.
- No checked-in theorem whose proof is a finite-target test.
- Full \(\mathbf Z_2\)-valued unramified marking, not just mod 2.
- Candidate and paper formulas generated from one expression tree.
- Explicit Fox and Hessian certificate replay.
- Affine phase interface, not only the base Gauss sum.
- `n=1` wrappers recover the current \(G_{\mathbf Q_2}\) theorem.
- `Q₂(√-10)` uses the procyclic row.
- `#print axioms` contains only named literature interfaces documented in a trust-boundary file.

## 11. What can be claimed now

The following theorem is justified by the supplement:

> For every ramified-\(i\) dyadic field and every proposed branch word, a marked-core certificate plus a reflected word certificate plus the standard local input package implies that the candidate group is the absolute Galois group.

The uploaded TeX does **not yet provide** the two rank-four marked-core certificates or the reflected universal word certificates. Therefore its unconditional Theorems 5.1, 5.3, 5.4, and 1.1 should remain conditional until those artifacts are added.
