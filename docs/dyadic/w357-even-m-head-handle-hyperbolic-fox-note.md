# W357 — the hyperbolic source has the general ramified Fox row

W356 repaired both directions of the promoted handle at second order.  W357 proves that the
same finite Nielsen transformation also preserves the first-order row needed by the existing
all-rank normal-form machinery.

After substitution, the compact marking sends its wild letters to products of the original
`sigma` and wild letters.  Under the same sigma-trivial and wild-trivial hypotheses used by
W356, every transformed compact wild letter acts trivially.  The public compact-M ramified
Fox theorem therefore applies directly.  Its sole surviving coefficient is the selected
handle pivot; the displaced `x₂ - sigma⁻¹ x₂` term is zero under sigma triviality.

`EvenMHeadHandleHyperbolicFox` exports:

* `foxD_headHandleHyperbolicW_ram`, the exact rank-uniform Fox identity;
* `headHandleHyperbolicRawFamily`, the reflected two-relator family;
* `isHeadHandlePairRamRow_hyperbolicRaw`, which feeds that family to the existing
  `headHandlePairRamNormalForm_of_row` theorem.

All public declarations pin to `propext`, `Classical.choice`, and `Quot.sound`.  No finite
class or handle count is fixed.  The remaining analytic seam is second-order: prove that the
new compact sigma offset is orthogonal to the compact core when the compact `x₂` coordinate
vanishes, then assemble the unchanged core, promoted hyperbolic plane, and remaining handles.
