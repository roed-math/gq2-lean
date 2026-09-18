# W361: arbitrary-diagonal wall polar inverse

Status: checked additive artifact, 2026-09-17. This is not an approval or a migration of
the frozen appendix format.

`GQ2/Dyadic/Instances/WordPhaseWallHandlePolarInverse.lean` imports the checked
`WordPhaseWallHandleCertificates` and works uniformly at every handle count. Write

\[
Q(x_0,x_1,(u_j,v_j))=d_0(x_0)+B_q(x_0,x_1)+\sum_jB_q(u_j,v_j).
\]

For any supplied additive operator \(L\) with
\(B_{d_0}(v,w)=B_q(Lv,w)\), the file defines the additive equivalence

\[
J_L(x_0,x_1,(u_j,v_j))=(Lx_0+x_1,x_0,(v_j,u_j)),
\quad
J_L^{-1}(y_0,y_1,(u_j,v_j))=(y_1,y_0-Ly_1,(v_j,u_j)).
\]

`polar_wallHandlePhase_eq_coordinatePairing_of_adjoint` identifies the actual polar
form of \(Q\) with the coordinatewise \(B_q\)-pairing evaluated on \(J_Lx,y\).
`coordinatePairing_eq_wallPolar_inverse_of_adjoint` solves the reverse equation with
the displayed inverse. This supplied-operator layer needs no finiteness or
nonsingularity hypothesis.

For the finite nonsingular case, no adjoint premise remains. `polarDualEquiv` constructs
the perfect additive pairing from `polar_rep_exists` and nonsingularity;
`diagonalPolarAdjoint` is the inverse polar-duality map composed with the polar map of
\(d_0\). `diagonalPolarAdjoint_spec` proves the required identity and
`diagonalPolarAdjoint_unique` proves uniqueness. The final APIs are:

* `canonicalWallPolarEquiv`;
* `polar_wallHandlePhase_eq_coordinatePairing`;
* `canonicalWallPolarEquiv_symm_apply`;
* `coordinatePairing_eq_wallPolar_inverse`.

Their hypotheses are `[AddCommGroup V] [Finite V]`, quadratic \(d_0,q\), and
nonsingular \(q\). No extra exponent-two, scalar-module, basis, or inverse-operator
hypothesis is used. The inverse construction is canonical by uniqueness, although its
Lean definition uses classical finite polar duality rather than a chosen coordinate basis.

There are also literal matrices over the generally noncommutative ring
`AddMonoid.End V`:

\[
H_L=\begin{pmatrix}L&1\\1&0\end{pmatrix},\qquad
H_L^{-1}=\begin{pmatrix}0&1\\1&-L\end{pmatrix}.
\]

Both multiplication identities are checked. `canonicalWallPolarEquiv_self` recovers
the earlier compact polar operator when \(d_0=q\).

## Scope

This is a polar factorization, not a quadratic phase equivalence to the compact
\(d_0=q\) form. It retains the actual diagonal \(d_0\); equal polar forms alone do not
identify phases or their affine translates. Actual source-word use still goes through
the separately proved additive normal-coordinate and full-value phase comparison for
that word. In particular, it does not replace the actual full-offset Npc diagonal by
the old Gate-E slice.

The source and cached `.olean` compile under default options, without warnings. All
23 public axiom pins are subsets of the standard three. No axiom, placeholder, option
override, legacy source, umbrella, or generated acceptance artifact was changed.

## Independent generic denotation audit

`Word/GeneralTemplateLN.lean` was read in full and checked independently with default
Lean. All ten public pins are standard-three. Its list argument preserves the original
ordered handle interpreter; the L theorem preserves the rank-zero omitted-handle-node
convention. The Npc integer numerator/denominator theorem is a syntax identity, whereas
well-formedness still requires oddness. `denote_rawNpc_display` uses an exact
`NpcDisplayFor`, not a congruence or an assertion that all two-adic units have a finite
rational display. No semantic mismatch was found.
