# W343: equivalent even-M source models still force the pivot

W341 proved that an adapted tame/pro-2 boundary on the standard compact-M or Mpc source cannot
alter its distinguished-`C` pivot.  W342 then transported the boundary-independent analytic
core across arbitrary continuous source equivalences, testing the more general possibility of
rewriting the presentation and installing a new boundary at the same time.

W343 closes that route.  `isProP_ker_comp_continuousMulEquiv` proves that precomposition by a
continuous group equivalence preserves a pro-`p` kernel.  Therefore any
`FlexibleModelSourceRN` for the standard compact-M or displayed-Mpc candidate transports back
to an adapted boundary on the standard source, where W341 applies.

The two public consequences are uniform in the number of handles:

- `mCompact_flexibleModelSource_forces_cPivot` forces the compact-M unit pivot;
- `mpc_flexibleModelSource_forces_cPivot` forces the exact Mpc `2^r` pivot for every honest
  display.

All three declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

Thus boundary replacement, presentation rewrites, and replacement by an equivalent source
group cannot repair a missing pivot while retaining the same standard candidate group.  The
remaining general fork is now selector-level: either prove that the obstructed selector branch
cannot arise for the relevant field data, or change the actual candidate group/branch chosen
there.  Further word-by-word or class-by-class analytic calculations cannot resolve this
structural obstruction.
