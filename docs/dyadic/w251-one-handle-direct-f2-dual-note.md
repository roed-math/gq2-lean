# W251: elementary dual detection of the direct obstruction

W251 proves that the W249 finite coordinate cokernel is elementary abelian.  Its obstruction
can therefore be tested by `ZMod 2`-valued additive functionals rather than complex
Pontryagin characters.

Every elementary functional kills the obstruction exactly when a direct correction exists.
Conversely, no direct correction exists exactly when one elementary functional detects the
obstruction.  Uniform elementary-functional vanishing is equivalent to the W246 correction
supply and therefore implies `MpcPivShiftH 2 1`.

All declarations use only the standard `propext`, `Classical.choice`, and `Quot.sound`
axioms.  This is a finite-linear reformulation, not a vanishing theorem: the remaining
calculation must either annihilate the target against every `F2` functional or produce one
detecting functional.
