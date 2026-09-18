# W361: exact exported Fox input binding

`GQ2/Dyadic/Instances/TameSpliceFoxTemplateInputBinding.lean` complements
`TameSpliceFoxTemplateBinding` with six full input-matrix identities:

```
GeneralFoxTemplate.scalar_pair_input
GeneralFoxTemplate.scalar_mobile_input
GeneralFoxTemplate.unramified_pair_input
GeneralFoxTemplate.unramified_mobile_input
GeneralFoxTemplate.ramified_pair_input
GeneralFoxTemplate.ramified_mobile_input
```

Each is equality of additive homomorphisms on **all generator cochains**:

```
(profile.inputMatrix q k).toHom actualInterpretation
  = foxJacobian actualMarking pinnedResolver tameRelW actualSourceWord.
```

The resolver is the actual omega-pinned level `4 * exponent C`. The scalar and
unramified profiles use `TameSym.splitEnd`; the ramified profile uses
`TameSym.ramifiedEnd`. The nonscalar `k` is respectively
`sigmaActionHalfPeriod(t,A)` or `tauActionHalfPeriod(t,A)`, exactly as in the
existing operation/target signature bridge. The input expressions happen not to
depend on k, but no unrelated period is substituted into the statement.

All six retain finite C and A, an exponent-two additive coefficient group, and
the actual C-action. The source words retain the complete parameters alpha, h,
nonzero even q, nuP, selected pair handle or arbitrary mobile unit eta, and all
mobile r/p values. The Fox identities require `alpha >= 1`; the downstream
combined analytic publication packet retains its stronger `alpha >= 2` scope.

Sector premises are unchanged:

* scalar: trivial action of every generator;
* unramified: trivial wild and tau actions, sigma fixed-point-free with trivial
  two-primary action, and death of the actual pinned changed-word family;
* ramified: compatible surjective projection to a finite head, wild head one,
  the actual tame relation, and tau fixed-point-free with trivial two-primary
  action.

No public supplied row identity, raw-word death, commuting sigma/tau, selected
handle unit equation, or mobile unit-head equation is added. Those last two
equations belong to the structural core certificate, not these first-jet
identities. The ramified specialization and endpoint premises are discharged
internally by the concrete source producers.

The proof composes the typed profile evaluation, the previously proved concrete
all-cochain rows, and `foxJacobian_pinned_apply`. Its last ramified step is only
additive rearrangement of the sigma/tau row, without commuting the actions.

All six public declarations compile warning-free at the default Lean settings
and have exactly the standard three axioms (`propext`, `Classical.choice`,
`Quot.sound`). This is a semantic bridge for a staged publication packet, not
approval of a replacement frozen gate or of a frozen-M word theorem.
