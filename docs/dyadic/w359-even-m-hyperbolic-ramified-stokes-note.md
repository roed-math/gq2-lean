# W359: full hyperbolic ramified Stokes transport

W359 closes ramified Stokes duality for the complete two-relator family obtained from compact
`M` by the W356 hyperbolic Nielsen substitution.  The theorem is uniform in `alpha`, `q`, the
handle rank, the finite acting group, and the elementary coefficient module.

The key point is conceptual: both relators are transported.  Evaluation of the transported
family at the original marking is exactly evaluation of compact `M` at the induced marking.
The induced marking preserves `tau`, promotes the chosen handle `U` to `sigma`, and has trivial
wild action under the original sigma/wild hypotheses.  The landed compact-`M` ramified Stokes
theorem and its unconditional normal-pairing separation therefore apply directly.

Public endpoint:

- `stokesDuality_headHandleHyperbolicFullFamily_ramified`

The endpoint assumes only characteristic two, even `q`, the ramified action conditions, and
death of the two transported relators.  It has no Hessian, nilpotency-class, field, or
finite-stage premise.  Its printed axiom set is exactly
`[propext, Classical.choice, Quot.sound]`.
