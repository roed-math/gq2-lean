# W334: changed-word even-M assembly

W334 closes the analytic and assembly layers for a genuinely changed even-M normal form.

For compact M and displayed procyclic M, `EvenMChangedWordCertificate` first constructs the
complete corrected certificate from an arbitrary exact pro-2 boundary map.  It then applies
that result to any normalized presentation whose candidate group is tame-compatibly equivalent
to the standard analytic word.  All four declarations have the standard trust base.

`EvenMChangedWordFieldFinal` places the adapted presentation directly on the field maximal
pro-2 quotient.  Its two data packets contain exactly:

* an adapted word;
* a normalized `CorePresentation` of the field core;
* tame specialization of that word; and
* a tame-compatible equivalence to the corresponding standard compact-M or displayed-Mpc
  candidate group.

Each packet supplies the corrected residual and the final general-K equivalence.  The final
equivalences inherit only the established general-assembly arithmetic axioms.

This is the honest response to W323.  The obstructed odd-residue compact-M pattern cannot be
solved by silently presenting the unchanged canonical word at a new core: the word must be
allowed to move with the generators.  The sole even-M campaign problem is now the uniform
group-theoretic construction of one of these changed-word field packets from the intrinsic
mobile pivot.  No nilpotency-class table, distinguished-C pivot, determinant, or Gauss-sum
premise remains in that task.
