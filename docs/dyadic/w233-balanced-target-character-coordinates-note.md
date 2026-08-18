# W233: target characters are finite mod-four coefficient pairs

W231 and W232 express the exact selected-target obstruction through complex characters of a
finite neutrality cokernel. W233 pulls those characters back to the explicit two-digit plane.

Every character of `(ZMod 4) × (ZMod 4)` is determined by two coefficients `(a,b)`. A target
therefore fails constrained coverage exactly when some target digit pair and coefficient pair
define a plane character which is nontrivial on the target but trivial on every CABD interaction
row. The converse is honest: a coefficient character annihilating those rows descends through
the neutrality quotient.

Thus abstract character detection, finite coefficient detection, constrained-span failure, and
the pointwise obstruction to the next balanced stage are all equivalent. The remaining problem
is no longer an unspecified dual group: it is the finite task of excluding these mod-four
coefficient detectors at one selectable point per rung.
