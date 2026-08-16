# Wave 100: ramified compact-M source comparison

Wave 100 assembles the honest ramified graph phase and the ramified Fox normal form into a
complete handle-free source-to-word phase comparison.

`wPcMComparison_ramifiedNatural` keeps the coordinate order naturally produced by the
compact-M word.  Its proof isolates resolver construction, the tame relation, the expensive
first-row specialization, and the lower relations into small declarations that all elaborate
within the default heartbeat budget.

`wPcMComparison_ramifiedHead` adds the projected faithful-head hypotheses used at the
boundary.  Oddness and fixed-point-freeness are stated on projected tau for the Hessian,
while the source `powOmega2` action is supplied separately for the Fox row.  A surjective
semidirect projection constructs the exact source-exponent resolver.

The exported phase equivalence removes the empty handle coordinates and swaps the two
remaining blocks.  Its target is therefore the same `plusFormD qbar qbar` used by the
unramified comparison.  The next boundary theorem can split on the tame action without
exposing the analytic distinction in its result type.
