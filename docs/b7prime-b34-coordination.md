# B7′-3 ∥ B7′-4 — parallel-lane coordination

**Read this before starting B7′-3 or B7′-4.**  The plan (`b7prime-proof-plan.md` §3) routed
B7′-2/3/4/5 through the single shared file `GQ2/HilbertSymbolDyadic.lean`.  B7′-3 (necessity) and
B7′-4 (sufficiency) are **independent parallel lanes**, and two agents editing/creating one file in
parallel produces whole-file merge conflicts (the pain the B12 lane hit).  This note replaces the
one-file layout with a **separate-file split** — the merge-safe pattern B12-2 used — so the two
lanes never touch the same file.

## File ownership

| Lane | Owns (new file) | Imports | Namespace |
|---|---|---|---|
| **B7′-3** (necessity) | `GQ2/HilbertSymbolNecessity.lean` | `GQ2.HilbertSymbolDyadic` + `GQ2.DyadicSquares` | `GQ2.HilbertSymbol` |
| **B7′-4** (sufficiency) | `GQ2/HilbertSymbolSufficiency.lean` | `GQ2.HilbertSymbolDyadic` + `GQ2.DyadicSquares` | `GQ2.HilbertSymbol` |

Both files sit strictly upstream of `Foundations/Axioms.lean` (they only reach `HilbertSymbol`,
`DyadicSquares`, Mathlib), so the B7′-5 flip stays the zero-churn B11/B12 pattern.

## Rules

1. **Each agent works only in its own file.**  Never edit the other lane's file.
2. **`GQ2/HilbertSymbolDyadic.lean` is edited by B7′-3 only** (shared helpers — see below).
   **B7′-4: do not edit `HilbertSymbolDyadic.lean`; import it.**  If B7′-4 discovers it needs a new
   shared helper there, flag it on the board / to the human rather than editing the file, so there
   is a single writer.
3. **`GQ2.lean` registration:** each agent adds exactly ONE import line for its own file, adjacent
   to the existing `import GQ2.HilbertSymbolDyadic` (currently line 26).  Suggested order to
   minimise churn — B7′-3's line immediately after `HilbertSymbolDyadic`, B7′-4's immediately after
   B7′-3's.  If both land on the same line a trivial "keep both" resolve is all that's needed.
4. **Namespace `GQ2.HilbertSymbol`** in both files.  Public names are disjoint by construction
   (necessity engine + −1 leaves vs. sufficiency glue + +1 leaves).  Keep internal helpers
   **`private`** — file-local, so no cross-file clash even on an identical name.
5. **Gates (per the board):** own files only, print the staged set; `lean_verify` = std-3 on every
   new decl; **no `native_decide`** (guard-enforced — plain `decide`, small moduli); `check_axioms`
   green; **census stays 13** (the decrement is B7′-5, user-gated).

## Shared helpers (in `HilbertSymbolDyadic.lean`, owned by B7′-3)

Both lanes bridge the axiom's `unit2`/`unitCoe` wrappers to raw coercions.  B7′-3 has added these
(committed before B7′-4 starts, both `rfl`):

```lean
theorem unit2_coe : ((unit2 : ℚ_[2]ˣ) : ℚ_[2]) = 2
theorem unitCoe_coe (u : ℤ_[2]ˣ) : ((unitCoe u : ℚ_[2]ˣ) : ℚ_[2]) = ((u : ℤ_[2]) : ℚ_[2])
```

The **necessity engine** (`exists_int_triple`, `exists_primitive_triple`,
`not_isHilbertSolvable_of_mod`) lives in B7′-3's file and is **not** needed by B7′-4 (sufficiency
proves solvability, it never refutes it).  So the only cross-lane dependency is the two coercion
lemmas above.

## Leaf split (plan §1 — 18 residue leaves + the freebie family)

* **B7′-3 owns the 11 −1 leaves** (`hilbertSymbol … = -1`): unit·unit `{3,3}, {3,7}, {7,7}`;
  `(u, 2v)` at `u₀=3, v₀∈{1,5}`, `u₀=5, v₀∈{1,3,5,7}`, `u₀=7, v₀∈{3,7}`.  Each: unfold
  `hilbertSymbol`, apply `not_isHilbertSolvable_of_mod` at `k = 3`, discharge the `ZMod 8`
  obstruction by `decide`.  Coercion seams via `unit2_coe`/`unitCoe_coe` + `push_cast`.
* **B7′-4 owns the 7 +1 witness leaves + the `u₀ = 1` freebie family** (`hilbertSymbol … = 1`):
  `hilbertSymbol_eq_one_of_value` (Hensel value glue, from `DyadicSquares.isSquare_of_toZModPow_eq_one`)
  with the explicit witnesses in plan §1, and `hilbertSymbol_isSquare_left` (already in
  `HilbertSymbolDyadic`) for the freebies.

## B7′-5 (assembly) — new file, downstream of both

The capstone cannot append to either engine file (each would have to import the other).  B7′-5
should be a **new file** `GQ2/HilbertSymbolDyadicClose.lean` importing **both** engine files +
`HilbertSymbolDyadic`, running the dispatch pyramid (parity → `comm` → `hilbertSymbol_neg_mul_right`
for the `(1,1)` family → residue `rcases` into the 18 leaves + freebies) and proving the byte-exact
capstone `hilbertSymbol_dyadic'`, then the census flip.

## Deviation note

This adds three files beyond the plan's "two new files only"
(`HilbertSymbolNecessity`, `HilbertSymbolSufficiency`, `HilbertSymbolDyadicClose`).  Justification:
merge-safety for the B7′-3 ∥ B7′-4 parallel lanes — the same rationale as B12-2's
`KummerKrullBridge.lean`.  Consolidating the engines back into `HilbertSymbolDyadic.lean` is an
optional later cleanup once the lane is complete and the tree is quiet.
