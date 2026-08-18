# W228: the two coordinate equations reduce modulo two

W227 reduces the residual neutrality problem to filling the two-generator digit plane
`(ZMod 4)^2`. W228 proves the finite Nakayama step directly for this plane.

If a subgroup of `(ZMod 4)^2` surjects after coordinatewise reduction to `(ZMod 2)^2`,
then it contains lifts of the two parity basis vectors. Squaring those lifts gives the two
generators of the reduction kernel. The lifts can therefore be corrected inside the subgroup
to the two standard `ZMod 4` generators, so the original subgroup is the whole digit plane.
The converse follows from surjectivity of reduction.

Applied to the CABD interaction row, full `ZMod 4` range is equivalent to full mod-two range.
The latter is expanded into two literal parity CABD equations. Thus the neutrality half of the
one-handle climb is now a two-row `F_2` spanning problem rather than two exact mod-four
equations. Together with ordinary-relative coordinate coverage, a uniform parity supply
implies `MpcPivShiftH 2 1`.

No parity relation is asserted here. The remaining work is to derive the two parity basis rows
from the graded relator interaction, alongside the already-separated ordinary-relative
coverage problem.
