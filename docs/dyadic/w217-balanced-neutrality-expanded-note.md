# W217: the expanded neutral-C equation

W217 unfolds W216's four finite shift rows. The surviving relation is now an equality in
`Q_(k+1)` between the bracket of the chosen relative `C` correction against the current `D`
letter and a product consisting of:

- the square of the `A` correction;
- its brackets against the current `A` and `B` letters;
- the `B` correction bracketed against the current `A` letter; and
- the `D` correction bracketed against the current `C` letter.

`neutralityObstruction_eq_one_iff_expanded_CABD` combines this formula with the exact source
condition from W216: the solving `C` correction must represent the selected target class
modulo genuinely character-neutral corrections.

This is a graded-calculation handoff. It contains no subgroup-span language and asserts no
solution. Both public theorems have exactly the standard axiom set `propext`,
`Classical.choice`, and `Quot.sound`.
