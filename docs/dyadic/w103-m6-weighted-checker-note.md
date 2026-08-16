# Wave 103: checked class-six word infrastructure

Wave 103 replaces the prospect of an opaque class-six calculation with a small reflected
derivation checker whose soundness is proved in Lean.

`CWord` is a four-generator syntax with multiplication, inverse, square, and the paper
commutator.  Its computed depth follows the exact two-central filtration rules.  The theorem
`eval_mem_twoCentralSeries` proves that every reflected word lies at that depth, which makes
deletion of depth-six terms sound in the sixth level quotient.

`Model` exposes only two semantic facts: the fixed compact-M relation and erasure beyond
class five.  `towerModel` constructs the quotient semantics for any topological group, and
`dmModel` discharges the relation for `DM 2 0` from the existing orbit theorem.

`Deriv.check` is a Boolean proof replay language with congruence, transitivity, group laws,
the compact-M relation, swapping, and checked deep deletion.  `Deriv.sound` proves that every
accepted derivation is an actual equality in the model.  The module includes a nested example
that deletes a weight-six commutator inside a product.

This infrastructure does not assert the sparse certificate equality yet.  The remaining
work is to add the finite collection identities used by the concrete trace, reflect the
closed defect and increment, replay the trace with `check = true`, and bridge the evaluations
to `MpcMkC6CertificateKill`.
