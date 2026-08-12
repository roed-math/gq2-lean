# W68: the class-three clearing supply, on the tower

Lane W68-BRIDGE.  New module `GQ2/Dyadic/SqCore/GradedBridge.lean`; no edits to existing files.
Prefixes `bridge` / `sqClassThree` / `bridgeFinal`.

## 0.  Headline

The campaign's number-one item is discharged, at the full quantifier:

> **`sqClassThree_supply : forall h, SqClassClearingSupply h 3`**

that is: for every `h`, every selected marking `nu'` and every handle `j`, there is a dressing
`a` with exactly trivial `lambda`- and `nu'`-rows, mod-2 independent frame, and
`sqRelWord (sqArbFrame h nu' j a)` in `twoCentralSeries (DSq h) 3`.  Hence

> **`bridgeFinal_residual_iff`**:
> `SqLamMarkTransitivity h  <->  forall k, 4 <= k -> SqClassClearingSupply h k`
> (`BridgeFinalResidual h`), and **`bridgeFinal_limResidual_iff`**:
> `LimFinalResidual h <-> BridgeFinalResidual h`.

**The residual now starts at class four.**  All 54 declarations pin to the standard three
axioms; no `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`.

## 1.  The route taken, and why

Route **(b)** of the ticket: rerun the witness computation directly in `levelQuot (DSq h) 3`.
Route (a) - transporting `GradedContain`'s binder witness through the selection family - was
not needed and was not used.  **No binder, no test carrier `SqU4 gr3R`, no census, no
`GradedSelect`, no `GradedContainFour`.**  The reason is that the class-three question is much
smaller than the wave-50/51 sweeps suggested when read on the tower rather than on a slice:

* `Roe/Labute/Levelwise.lean` already commits the class-two calculus of `Q3 = levelQuot G 3`:
  every square and every `commP` lands in the central exponent-two layer `Z2 = zLayer G 2`, and
  `commP` is bimultiplicative there (`commP_mem_zLayer_two`, `sq_mem_zLayer_two`,
  `commP_mul_left_of_three`, `commP_mul_right_of_three`, `zLayer_commute`, `zLayer_inv_self`,
  `zLayer_sq`).  W68 adds only thin consequences (§1 of the module).
* Therefore **`bridge_sqWord`**: `sqWord a b c = commP a b * c^2` in `Q3`.  Both correction
  factors of the free identity die - `((b^2)^2)^-1` because `b^2` is already central of order
  two, and `commP c (conjP c a)` because `conjP c a = c * commP c a` differs from `c` by a
  central factor.  Consequently **`bridge_sqRelWord`**: mod `gamma_3` the relator is
  `commP m0 m1 * m2^2 * prod_j commP m_U m_V`, a *bilinear* expression in the slots read mod
  `gamma_2`.

So the class-three obligation is a single identity in the bracket group, and the whole problem
is two lines of `F_2` linear algebra.

## 2.  The mechanism, and the witness

Write `w = sqPivot h = sigma * x0^{-c0}`, `cU = nu'(u_j)`, `cV = nu'(v_j)`.

**The defect.**  The undressed frame `sqArbBase` fails the identity by exactly the Eichler
twist.  The two cleared handle letters are `sqEichU = w^{-cU} * u_j` and
`sqEichV = v_j * w^{-cV}`, so (`bridge_comm_eich`, `bridge_handle_comm`)

```
commP (pi sqEichU) (pi sqEichV) = commP u_j v_j * (commP w^{cU} v_j * commP u_j w^{cV}).
```

**The fix.**  Dress the `sigma`-slot and the `x0`-slot by the *same* element and leave every
other slot alone.  Then `commP (sigma A) (x0 A) = commP sigma x0 * commP (sigma*x0) A`
(`bridge_comm_common_dress`: the `A`-`A` term is a self-bracket), and **`sigma*x0` IS the pivot
modulo `gamma_2`** (`bridge_sigma_x0_eq_pivot`: `c0 = sqPivotExp` is a unit, so
`x0 * x0^{c0} = x0^{1+c0}` is an even power, hence a square).  With

```
bridgeDress = u_j^{cV} * v_j^{cU} * w^{-2 cU cV}
```

`commP w (pi bridgeDress)` equals the handle defect on the nose (`bridge_defect_eq`), by the
one transport lemma **`bridge_comm_zpow_eq`**: *a bracket reads a `Z_2`-power through its
exponent's parity only*, so the exponent may be moved from one slot of the bracket to the
other.  The two defects are then the same element of `Z2`, which has exponent two, so they
cancel: **`bridge_relator_mem`**.

Three points worth recording.

* The witness is **`h`-uniform and marking-uniform**, with no parity case split: writing the
  exponents in `Z_2` rather than in `F_2` avoids the four-case analysis the `F_2` picture
  suggests.  There is no spot-checked instance anywhere in this wave.
* The `x1`-slot is taken undressed, and that is the only choice that can work.  ANALYSIS, NOT
  COMMITTED: in `gamma_2/gamma_3 = V (+) Lambda^2 V` the squaring map contributes the
  `V`-component, which no bracket can cancel, so the `x1`-slot's class mod `gamma_2` is pinned;
  and the alternative "kill the relator outright rather than match the relator class" costs a
  dimension and so fails mod-2 independence.  None of this is formalised - the committed proof
  simply takes the `x1` dressing trivial and never needs the converse.
* The third factor `w^{-2 cU cV}` of the dressing is a **pure row correction**: an even pivot
  power, invisible mod `gamma_2`, present only so that both rows vanish exactly.

**Mod-2 independence** (`bridge_modTwoIndep`) needs no selectedness: an index-two open normal
subgroup swallowing every slot swallows `sigma * x0^{-1}`, hence the pivot (via
`mul_mem_iff_of_index_two` and the odd-exponent lemma, `c0` being a unit), hence the two pivot
powers, hence both handle letters, hence the dressing, hence `sigma` and `x0` - against
`exists_sqGen_notMem`.

## 3.  The row-lifting verdict: NOT obstructed

The ticket's row-lifting question - can a dressing prescribed mod `gamma_k` with admissible row
data be corrected inside its coset to *exact* rows, i.e. how large is the joint image of
`(nuLam, nu')` on `ker (levelMk (DSq h) k) = gamma_k` - has a clean answer.

> **`bridge_row_image`**: at every selected marking and every `m`, `gamma_{m+1}` contains
> elements with `lambda`-row exactly `2^m a` and `nu'`-row exactly `2^m b`, for every
> `a, b` in `Z_2`.

So the joint image contains the **full square** `2^{k-1} Z_2 x 2^{k-1} Z_2`.  (The matching
upper bound - `lambda(gamma_k)` contained in `2^{k-1} Z_2` - is standard but is NOT committed
here; only the containment is, and it is the direction a coset repair consumes.)  The two
witnesses are row-independent by construction: `x0` has `lambda = 1` and `nu' = 0` exactly (the
second by selectedness), the pivot `w` has `lambda = 0` and `nu' = 1` exactly.  **Both rows can
be corrected independently without leaving the coset, so the row-lifting step of
`w67-limit-note.md` §4.2 is not an obstruction at any class.**

This wave never invokes the lemma: `bridgeDress` is written so its rows cancel on the nose
(`bridge_nuLam_dress`, `bridge_nu_dress`), and no coset repair is performed.  The verdict is
committed because the ticket asked for it and because `k >= 4` will consume it.

## 4.  What class four needs

The argument above uses exactly **two** class-specific inputs about `Q3`, both supplied by
`Levelwise`, and **neither survives one class up**:

1. `commP` is bimultiplicative in `Q3`.  It is not in `Q4`; `Levelwise`'s
   `commP_mul_left_of_three` / `commP_mul_right_of_three` are `Q3`-only, and the triple
   brackets of `zLayer G 3` are exactly what obstructs.
2. `(q^2)^2 = 1` in `Q3`.  In `Q4` this is **false** for `D_sq h`.  `bridge_pow_four_iff`
   isolates it as an equivalence: `(forall q : levelQuot G 4, (q^2)^2 = 1)` iff
   `(forall g : G, g^4 in twoCentralSeries G 4)`; and the tree already refutes the right-hand
   side at `g = sigma`, by
   `GQ2.ContCoh.dsqSigma_pow_four_not_mem_twoCentralSeries_four (h) : dsqSigma h ^ 4 not-in
   twoCentralSeries (DSq h) 4` (`Count/LowerTwoCentralJenningsDegreeThree.lean:575`).

**Verified out of band** (not committed into the lane file, because no `SqCore` module imports
a `Count` module today and W68 did not want to be the first): with the extra import,
`exists b : levelQuot (DSq h) 4, (b^2)^2 <> 1` follows from that refutation in two lines.

So a class-four run **cannot be the present argument with `3` replaced by `4`**.  Concretely
the class-four relator identity must carry the `x0`-slot's fourth power `((m1^2)^2)^-1`, which
`bridge_sqWord` does not see, plus the `commP c (conjP c a)` term, which is a genuine triple
bracket one class up.  `GradedContainFour`'s slice-level results
(`sqRelWord_conFourDress_of_rel`, `conFour_contain_odd/even`) are the natural input, and the
bridge they need is the same transport this wave built (`bridge_comm_zpow_eq` generalises to
`gamma_k`-shadows verbatim; `bridge_row_image` is already stated at every class).

## 5.  Statements landed

| name | statement |
| --- | --- |
| `bridge_sqWord` | `sqWord a b c = commP a b * c^2` in `levelQuot G 3` |
| `bridge_sqRelWord` | the relator mod `gamma_3` is bilinear plus the `x1`-square |
| `bridge_comm_zpow_eq` | a bracket moves a `Z_2`-exponent across its two slots |
| `bridge_sigma_x0_eq_pivot` | `sigma * x0 = u * w` with `u` in `gamma_2` |
| `bridge_comm_common_dress` | `commP (s a) (x a) = commP s x * commP (s x) a` |
| `bridge_comm_eich` | the Eichler-twisted handle bracket |
| `bridge_defect_eq` | core defect = handle defect |
| `bridge_relator_mem` | the dressed relator lies in `twoCentralSeries (DSq h) 3` |
| `bridge_modTwoIndep` | the dressed frame is mod-2 independent |
| **`sqClassThree_supply`** | **`forall h, SqClassClearingSupply h 3`** |
| **`bridgeFinal_residual_iff`** | **`SqLamMarkTransitivity h <-> BridgeFinalResidual h`** |
| `bridgeFinal_limResidual_iff` | `LimFinalResidual h <-> BridgeFinalResidual h` |
| `bridge_row_image` | the joint row image on `gamma_{m+1}` contains `2^m Z_2 x 2^m Z_2` |
| `bridge_pow_four_iff` | the class-four fourth-power condition, isolated |

## 6.  Verification record

* Verification of record, from the worktree root:
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
  GQ2/Dyadic/SqCore/GradedBridge.lean` - clean, no `sorry`, no new axioms.
* Axiom pins: 54 `#print axioms`, every declaration `[propext, Classical.choice, Quot.sound]`
  or a subset (`bridge_comm_self`, `bridge_comm_of_commute`, `bridge_central_shuffle` are
  `[propext]` only; the two list-surgery lemmas are `[propext, Quot.sound]`).  This matches the
  machinery consumed: `GradedLimit` and the tower and `Levelwise` facts are all std-3.
* Full-mirror collision test: `scripts/mirror.sh sweep` (5743 artifacts), then
  `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedBridge` - generated clean against the complete
  cache mirror.
* Independent restatement check (scratch, not committed): the fully spelled-out form of
  `SqClassClearingSupply h 3` - with `twoCentralSeries (DSq h) 3` written out and no definition
  hiding anything - is discharged by `sqClassThree_supply h`; and both residual equivalences
  type-check against the expanded `forall k, 4 <= k -> ...` form.
* Imports added: `GQ2.Roe.Labute.Levelwise` (for the committed `Q3` class-two calculus)
  alongside `GQ2.Dyadic.SqCore.GradedLimit`.
* Base `2b063dfa`; lane branch `claude/w68-bridge`.
