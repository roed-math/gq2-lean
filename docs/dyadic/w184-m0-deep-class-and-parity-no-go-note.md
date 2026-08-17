# W184: the depth-two odd-residue compact-M pivot is impossible

W184 identifies the intrinsic compact-M distinguished `D` class with the deep cyclotomic digit
and follows the depth-two arithmetic through to a selected-field no-go.

## The transported D class

`GQ2/Dyadic/Instances/M0FieldUniformizerDeepClass.lean` proves that, under any oriented
compact-M identification, `m0FieldDCharacter` is exactly `evenDeepDigitChar`.  On cohomology,
the transported distinguished class is therefore `evenDeepClass alpha`.

At `alpha = 2`, the deep class is the mod-eight omega class, whose field Kummer class is `[2]`.
Consequently intrinsic uniformizer-D placement is equivalent to

`[2] = [pi]`,

or literally to `2 / pi` being a square.  The discrete valuation of `2 / pi` is `e - 1`, so this
condition forces the absolute ramification index `e` to be odd.  A selected M0 presentation has
even degree.  With odd residue degree `f`, the fundamental identity `n = e f` forces `e` even,
and hence rules out depth-two uniformizer-D placement.

All declarations in this module use only `propext`, `Classical.choice`, and `Quot.sound`.

## The intrinsic pivot also vanishes

`GQ2/Dyadic/Instances/M0FieldPivotParityNoGo.lean` strengthens the placement obstruction to the
actual intrinsic C-pivot.  If `e` is even, write `2` as a square times a norm-one unit.  For a
spectrally unramified quadratic Kummer extension, the repository's proved unit-norm surjectivity
then represents `2` by the quadratic norm form.  The Hilbert cup of the unramified class with
`[2]` is therefore zero.

Odd residue degree already supplies the unramified Kummer realization from W180.  Combining it
with the selected branch's even degree gives

`not_m0FieldPivotUnit_two_of_familySelection_odd_residue`.

Thus the earlier odd-residue M0 residual theorem remains a correct conditional implication, but
at `alpha = 2` its intrinsic placement/pivot route cannot be instantiated.  This is a genuine
arithmetic obstruction, not a missing frame normalization or an unproved selector lemma.  The
pivot no-go inherits the existing Hilbert/norm criterion and Tate-duality foundations; it adds no
new axiom.

## Updated frontier

- For depth-two M0 with odd residue degree, do not search for uniformizer-D placement or the
  canonical C-pivot: both are impossible.
- The remaining compact-M questions lie at deeper `alpha`, different residue parity, or in a
  branch realization that does not require the refuted canonical depth-two pivot.
- The Mpc and odd-L fronts are unchanged: neutral fixed-C graded reachability, and local
  odd-cyclotomic Frobenius conjugacy followed by the normalized profinite Frobenius coordinate.

## Verification

- `lake build GQ2`: 4,530 jobs, success.
- Fresh umbrella scoreboard: 1,119 modules, all W184 rows registered.
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: success; 45,104 tracked declarations,
  no `sorryAx`, no unknown non-standard axiom use, and no terminal violation.
