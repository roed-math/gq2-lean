# W361 selected-word precision audit

## Finding

The preceding fully marked existential theorem was mathematically useful but its statement
retained only the selected degree, not the source constructor. This was a genuine loss of
information in the packaging: the canonical bridge discarded `G.pres = selectedPresentation S`,
and the M bridge returned complete data whose `word` field was arbitrary in its public type.
Their proofs did build the intended words, but that fact was not a theorem conclusion.

## Checked strengthening

`Instances/FieldFamilySpliceSelectedWord.lean` adds `SelectedWordProfile FF S G` and proves
`hasSelectedWordCertificate_of_matchesRange` and its range-selector specialization. The profile
retains literal word equality as `HEq`, together with explicit alphabet-degree and core
equalities. On splice branches it also retains equality of the actual `nuP` marking.

| Selected branch | Actual word retained by the profile |
| --- | --- |
| L | Exact `selectedPresentation S` word/core, hence the selected `lSqW` |
| N0 | Exact selected canonical compact-N word/core |
| Npc | Exact selected displayed Npc word/core, preserving its display and parameters |
| M0 | Exact selected canonical M0 word/core, or `headHandlePairSpliceW` with the selected alpha and handle count and an actual unit-U marking |
| Mpc | `tameSplice (mpcMobileTameCorrectedW ...) (mCompactW ...)`, retaining selected alpha, r, epsilon, `p epsilon r`, and handle count |

For Mpc the mobile unit is the actual D-coordinate `etaD`, not silently identified with the
selected display unit `eta`. The conclusion records both `nuP(D) = etaD` (through `ztwoIota`)
and `etaD = eta + 2^r * w` for some two-adic `w`. This is exactly the selected residue relation
used by the constructor. No equality with the frozen Mpc word is claimed.

`Instances/FieldFamilySpliceSelectedWordFinal.lean` proves that this profile is unchanged by
`alignedBranch` definitionally. `SelectedWordMarkedFieldData` then retains the profile, actual
word certificate, exact selected degree, field equivalence, and all literal tame, pro-two,
maximal-pro-two, cyclotomic, and full-nu equations simultaneously. Its `degree_eq_field` theorem
identifies the alphabet degree with the field degree.

The bare endpoint is
`nonempty_selectedWordMarkedFieldData_ramifiedI K RI`; there is also an odd-degree corollary.
It retains the standing ramified-i scope and calibrates only the existential realization, not
an arbitrary previously fixed realization. Cyclotomic compatibility is still proved through
the original pre-reconstruction character and characteristicness, as in the preceding marked
endpoint.

## Trust and exclusions

Both modules compile with default Lean settings and no new axioms. The source producer uses
standard three plus the inherited Hilbert norm criterion, peripheral cyclotomic action, Tate
duality, and absolute-Galois finite-generation/Euler foundations. The fully marked canonical
endpoint additionally uses the established local reciprocity, marked reciprocity, oriented tame
quotient, and relative Stiefel-Whitney constructors, exactly as the preceding canonical marked
endpoint.

This result does not assert a frozen M-word repair, a pointwise fixed-input core-realization
theorem, equality of `etaD` with a selected representative, or coverage outside ramified-i.
