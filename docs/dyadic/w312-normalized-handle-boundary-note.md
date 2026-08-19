# W312: one normalized-handle supply is the remaining M boundary

W312 packages the general consequence of W309–W311.  Every range-matching family selection
satisfies `EvenCanonicalOrNormalizedHandleBoundary`: compact M and epsilon-false procyclic M
have either the already-consumed exact C pivot or the same normalized handle pivot, while all
other selected rows are already closed.

`NormalizedMHandleResidualSupply` is now the exact remaining even-family interface.  It asks
that the normalized handle form produce the selected corrected RN residual for the compact and
positive-level words.  The two clauses distinguish word families, not degree classes; their
pivot data are identical.  The dispatcher
`hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_normalizedHandleSupply` then closes the
whole selected family.

This boundary also prevents an invalid shortcut.  The normalized handle marking is not being
asserted conjugate to the canonical C marking: characteristic orientation rules out that
unrestricted transitivity.  The next work is therefore an honest uniform certificate or field
argument for this alternate normal form.
