# W97: exact marked range surface for the M6 ladder

Date: 2026-08-16

## Result

`GQ2/Dyadic/Instances/MpcMarkedRange.lean` turns the corrected W94/W95 picture into the exact
formal API needed by the uniform proof.  It does not identify the cost range with an
oversized Fox kernel.

`MpcMkCostDomain j` is the product of the three marked carriers and the derived pivot
carrier.  `mpcMkCost` is the exact `mpcBldIncr` map into the next central layer.  Its map laws
use the existing increment homomorphism theorem and the legality of full marked moves.

For a class-`(j+1)` solution, `mpcMkDefectTop` places its defect in the same layer.  The theorem
`mpcMk_fullSupply_iff_mem_costRange` proves that full marked supply is exactly membership of
this defect in the fiberwise cost range.

## Corrected induction target

`MpcMkGood j` means that some class-`(j+1)` solution has its top defect in its own marked cost
range.  The module proves:

* `MpcMkGood 3` from the existing class-five move;
* `MpcMkGood 4` from a full marked W5 supply;
* `MpcMkGood 4` directly from the sparse certificate's sole Q6 equality;
* `MpcPivShift 2` from `MpcMkGood 4` and successor propagation for all `j >= 4`.

The successor remains an explicit hypothesis.  This is the narrow mathematical theorem still
needed:

```text
MpcMkGood j -> MpcMkGood (j + 1), for j >= 4.
```

It concerns only recursively arising defects.  The class-six cost image has codimension five,
so equality with a codimension-one chi-Fox kernel or the at-most-codimension-four coordinate
derivation envelope would be false.

## Verification surface

All ten declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The module
introduces no axiom, `sorry`, `native_decide`, or option override.
