# W252: ambient elementary-dual detection

W252 pulls the W251 elementary-dual obstruction back from the coordinate cokernel to the
ambient central layer.  A direct correction exists exactly when every `ZMod 2`-valued
functional that annihilates the four-coordinate span also kills the direct target.

Failure is equally concrete: no correction exists exactly when one ambient elementary
functional annihilates the span but detects the target.  The uniform ambient vanishing
condition is equivalent to the W246 correction supply and implies `MpcPivShiftH 2 1`.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The remaining
calculation is now phrased entirely inside the finite central layer; the next useful step is
to replace span annihilation by the four literal coordinate-row conditions from W248.
