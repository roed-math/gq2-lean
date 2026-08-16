# W157: selected general-h compact-N row

The family-selected compact-N branch now reaches a tied corrected RN row at every handle count.

For a selector equality `S.branch = .N0 alpha`, validity supplies `2 <= alpha`, the level equation
supplies `B.r = 0`, and the degree equation identifies the selected presentation with the field
degree.  `n0GenAsmBranch_of_familySelection_tied` combines those facts with W156's general-h
level-zero realization and the canonical surjective `nNuZtwo` marking.

`n0RowResidualRN_of_familySelection` then applies the uniform compact-N corrected word
certificate.  No determinant, primitive-pair, handle-normalization, or ASK premise remains.  The
only surviving field datum is the ordinary oriented `DN` equivalence.

Both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The next analytic frontier is compact-M branch-free determinant supply beyond handle count zero.
