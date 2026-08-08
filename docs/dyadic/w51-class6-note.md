# W51: the corank at class 6, and the exhaustion of the class-5 grid

**Wave W51, worker W51-SWEEP6.  OFF-LEAN.  No Lean was written, edited or built.**

This continues `docs/dyadic/w50-depth-sweep.md`, whose §9.1 ranked the follow-ups to the
depth-4/5 sweep of the arbitrary-dressing residual (`SqArbRelWord 1`, equivalently
`SqLamMarkTransitivity 1`).  Item 1 on that list was **watch the corank at class 6**: at every
level and every marking W50 measured, the dressing-defect map `δ_j` had corank exactly
`d + 1 = 6`, and a level where that corank *grows* is the only place in this computation where
a refutation could first appear.  Item 2 was to finish the class-5 marking grid.

---

## 0.  Headline

| question | answer |
|---|---|
| **(a)** the one number: does `corank(δ)` grow at class 6? | **No.  It stays `d + 1 = 6`.**  At `L₆` the defect map has rank **2668 of 2674**, corank **6**, at every marking measured, exactly as at `L₃`, `L₄`, `L₅`.  No refutation appears where one could first have appeared. |
| **(b)** is that a sample? | **Not for the corank.**  `δ_j` and its image depend on `(t,s)` only mod 2 (§2.4, verified directly at class 6), and all four parity classes were measured.  The corank verdict covers every uncleared marking. |
| **(c)** does the relator's defect still land in `im δ`? | **Yes, 85 / 85** at class 6 (24 markings, every level exercised), against a random-vector control of **235 / 16000 = 1.47 %**, matching the `2⁻⁶ = 1.56 %` a codimension-6 image predicts. |
| **(d)** class-5 grid | **Finished, and now exhaustive: 1023 of 1023 uncleared markings, all solvable, 0 infeasible** (§4).  W50 had 72. |
| **(e)** anything new at `h = 2`? | `corank = d + 1 = 8` now also at `L₅` (3688 / 3696), one class deeper than W50 reached (§5.5). |
| **(f)** was class 6 reachable at all? | **Yes, in 1835 s and 1.0 GB.**  `Q_6` has order `2^3596` and layers `5, 14, 49, 175, 679, 2674`.  W50's bare `pQuotient(G,2,6)` had not finished in ~50 min; the incremental `pQuotientProcess`/`NextClass` route gets there in half an hour (§5.1). |

So the single number W50 flagged as the place a refutation could first hide has been read, and
it did not move:

> **`corank(δ_j) = d + 1` at every level `L₃ … L₆` at `h = 1` (d = 5), and at every level
> `L₃ … L₅` at `h = 2` (d = 7).**

As a by-product, all 24 class-6 markings are **solvable**: an explicit `m` with `R(m) = 1` in a
group of order `2^3596`.  This is positive evidence for the residual and, as always, not a
proof of it (§6).

---

## 1.  Tools

| tool | version | used for |
|---|---|---|
| **Magma** | **V2.29-4** (`/Applications/Magma/magma`) | `pQuotientProcess`/`NextClass`, pc arithmetic, `EchelonForm`/`Rank`/`IsConsistent` over `GF(2)` |

No GAP was needed.  (For the record, the W50 note is right: there is no standalone `gap`
binary here, the shell name `gap` being an alias for `git apply`, and GAP 4.14.0 is reachable
only as `sage -gap`.  Magma's `pQuotient` is the same ANU algorithm ANUPQ wraps, and the
bottleneck this wave removed was never in the p-quotient engine, so nothing was gained by
switching engines.)

All randomness is seeded (`SetSeed(1)`).  Everything ran locally; no remote machine was used.

---

## 2.  Method: replacing `K ∩ P_j` by a graded generating set

W50's cost model (its §10) was ~70 s per class-5 marking, of which the three
`K meet P_j` subgroup intersections were ~6 s each, and it identified those intersections,
at order `2^{3500+}`, as the wall standing in front of class 6.  §9.1 prescribed the way
round: use an explicit generating set instead.  That is what `scripts/w51_class6/w51_corank.m`
does, and it turned out to be worth far more than expected (§3.3).

### 2.1  The recursion

Write `L_w = P_w/P_{w+1}` for the layers of the lower exponent-2 central series of `Q`, and
`K_w = (K ∩ P_w)P_{w+1}/P_{w+1}` for the graded pieces of `K = ker λ ∩ ker ν′`.  Then

```
S_w  :=  [L_{w-1}, L_1]  +  span{ b² : b a basis of K_{w-1} }
```

with `S_1 = span(Ū, V̄, t̄)` (and, at `h = 2`, also the second handle's two letters).

`S_w ⊆ K_w`: `[P_{w-1}, Q] ⊆ [Q,Q] ⊆ K` and `[P_{w-1},Q] ⊆ P_w`, while squares of elements of
`K ∩ P_{w-1}` lie in `K ∩ P_w`.  Squaring is additive modulo `[L_{w-1}, L_1]` (the correction
`[y,x]` in `(xy)² = x²y²[y,x]` lies in `[L_{w-1},L_1]`), so the span of the squares of a basis
really is the image of the whole square map, not just of the basis.

The commutator half `[L_{w-1}, L_1]` is **marking-independent**, exactly as §9.1 predicted, so
`w51_grid.m` hoists it out of the marking loop and computes it once.

### 2.2  Why the generating set is *exactly* `K_w`, not merely contained in it

This is the part that has to be right, because a `S_w` that is too small shrinks the domain of
`δ`, which inflates the corank and would manufacture a spurious refutation lead.  The
computation certifies itself:

* `λ(σ) = c₀` is a 2-adic unit, `λ(x₀) = 1`, `ν′(σ) = 1`, `ν′(x₀) = 0`, and the minor
  `det [[c₀,1],[1,0]] = −1` is a unit.  Put `p = σ^{2^{w-1}}` and `q = x₀^{2^{w-1}}`, both in
  `P_w`.  Then `λ(p) = c₀·2^{w-1}` and `λ(q) = 2^{w-1}` are nonzero in `ℤ/2^c` for `w ≤ c`, and
  `ν′(pq) = 2^{w-1}` is nonzero.  So none of `p`, `q`, `pq` lies in `K`: the plane they span in
  `L_w` meets `K_w` trivially, and therefore **`codim K_w ≥ 2`**.  This argument is pure
  algebra and is independent of `(t,s)`.
* Hence if the computation finds both
  `dim S_w = dim L_w − 2` **and** `S_w + ⟨p,q⟩ = L_w`,
  then `dim K_w ≤ dim L_w − 2 = dim S_w ≤ dim K_w`, so `S_w = K_w` **exactly**.

Both conditions are checked at every level of every marking and reported in the `cert` column.
They held everywhere in this wave: every `cert` printed `true`.

### 2.3  Two further changes that made class 6 reachable

* **Layer coordinates off the exponent vector.**  The pc generators of a `pQuotient` are
  weight-graded and `P_w` is the corresponding tail subgroup; the scripts assert this
  (`NPCgens(P[w]) = n − ofs[w]`, plus a membership check at each boundary) rather than assume
  it.  So the image of `x ∈ P_w` in `L_w` is just the slice `Eltseq(x)[ofs_w+1 .. ofs_{w+1}]`
  reduced mod 2, and no quotient group has to be constructed at all.  Cross-checked against
  W50's honest `quo< P[w] | P[w+1] >` coordinate on 25 random elements of every layer at
  classes 4 and 5: **0 mismatches**.
* **Basis representatives are single pc elements.**  W50's `LayerBasis` recovered group
  representatives from an `EchelonForm` transformation matrix, so a representative was a
  product of up to `#gens` pc elements; every later `Rel(m·b)` then had to collect that long
  word.  Here a basis is extracted as a *subset* of the candidate list (the pivot columns of
  the transposed matrix), so every representative is a single commutator, square or generator.
  This is what actually bought the speedup in §3.3.

### 2.4  The corank depends on the marking only mod 2

W50 recorded that `im δ` is marking-dependent, with `(2,1)` the lone marking whose image
coincided with `(0,1)`'s and eight others differing.  There is a reason for the pattern, and it
sharpens the result:

* `δ_j` depends on `m` only through `m mod P₂` (W50 §5.1), and the corrections applied at each
  level lie in `P₂`, so this stays true all the way up.
* `m mod P₂` depends on `(t,s)` only mod 2: `U = w^{-t}u` and `V = v·w^{-s}` with
  `w = σ·x₀^{-c₀}` and `c₀` odd.
* `K_w` is determined by `K_1 = span(x̄₁, ū + t·w̄, v̄ + s·w̄)` through the §2.1 recursion, so it
  too is a function of `(t mod 2, s mod 2)` alone.

So **`δ_j`, its image and not merely its rank, is a function of the parity class of `(t,s)`.**
The scripts test this directly rather than taking it on trust: `im δ` is stored per
`(level, t mod 2, s mod 2)` and every later marking of the same parity is compared against it.
At class 4 the four parity classes give four distinct images and `(2,1)` reproduces `(0,1)`'s
exactly, which is precisely W50's one coincidence, now explained.

The consequence matters for what a class-6 verdict is worth: **four parity classes exhaust the
corank question at a given class**, so a short marking list is not a sample with respect to
*that* number.  (The relator's own defect is *not* a mod-2 object: it depends on `(t,s)`
fully, so the containment question of §5.2 genuinely does have to be sampled.)

---

## 3.  Validation: the new route reproduces W50 before it is trusted anywhere new

The generating-set route was validated at class 4 and class 5 against W50's `K meet P_j`
route **before** being pointed at class 6, as the ticket required.  Runs:
`scripts/w51_class6/results/ck_c4.txt` and `ck_c5.txt` (`verify:=1`).

### 3.1  The subgroup itself

At every level the two routes are compared as *subspaces of the layer*, not merely by
dimension:

| class | level | `dim(K ∩ P_w)` layer, W50 route | gen-set `dim S_w` | **spans equal?** | W50 route cost |
|---|---|---|---|---|---|
| 4 | L₁ | 3 | 3 | **yes** | 0.00 s |
| 4 | L₂ | 12 | 12 | **yes** | 0.10 s |
| 4 | L₃ | 47 | 47 | **yes** | 0.10 s |
| 5 | L₁ | 3 | 3 | **yes** | 0.01 s |
| 5 | L₂ | 12 | 12 | **yes** | 6.4–7.6 s |
| 5 | L₃ | 47 | 47 | **yes** | 6.2–6.9 s |
| 5 | L₄ | 173 | 173 | **yes** | 5.3–6.1 s |

The dimensions `3, 12, 47, 173` are W50's (§6.3), and the class-5 timings reproduce its
"`K meet P_j` about 6 s per level".  `Index(Q,K) = 4^c` was re-asserted at both classes and
holds, so the model of W50 §2.4 (the Φ(K)-closure model, not the abelian-class preimage that
misled W48) is the one in use here too.

### 3.2  The defect map

| class | level | target `dim L_j` | domain | `rank δ` | **corank** | defect in `im δ` | W50's numbers |
|---|---|---|---|---|---|---|---|
| 4 | L₃ | 49 | 5 × 12 = 60 | 43 | **6** | yes | 43 / 49, corank 6 ✓ |
| 4 | L₄ | 175 | 5 × 47 = 235 | 169 | **6** | yes | 169 / 175, corank 6 ✓ |
| 5 | L₃ | 49 | 60 | 43 | **6** | yes | ✓ |
| 5 | L₄ | 175 | 235 | 169 | **6** | yes | ✓ |
| 5 | L₅ | 679 | 5 × 173 = 865 | 673 | **6** | yes | 673 / 679, corank 6 ✓ |

Every number matches W50 exactly, at all three markings tried at each class
(`(0,1)`, `(1,1)`, `(3,5)`), and every marking ends with `R(m) = 1` in the quotient.
The coordinate cross-check (§2.3) reported 0 mismatches in 25 random elements of each of the
10 layers involved.  Only after all of this was class 6 attempted.

### 3.3  The cost, which is the point

| | W50 | W51 | ratio |
|---|---|---|---|
| build `Q_5` (order 2^922) | 150 s (`pQuotient(G,2,5)`) | **16 s** (`pQuotientProcess` + `NextClass`) | ~9× |
| one class-5 marking, all three levels | ~70 s | **~0.5–0.9 s** | ~100× |
| remaining class-5 grid (951 markings) | ~15 CPU-hours (estimate) | **677 s measured** | ~80× |

Two independent causes, both in §2.3: the `K meet P_j` intersections disappear, and basis
representatives stay short so that every subsequent collection in the pc group is cheap.  The
second is the larger effect: dropping the intersections alone would only have taken 70 s to
about 52 s.

---

## 4.  Result: the class-5 grid is now exhaustive

`scripts/w51_class6/results/grid_c5.txt`, driver `w51_grid.m`.

| class | `(t,s)` range | markings probed | solvable | INFEASIBLE |
|---|---|---|---|---|
| 5 | `(ℤ/32)²` | **1023 of 1023 uncleared, exhaustive** | **1023** | **0** |

W50 had banked 72; this wave did the remaining 951 in 677 s.  By W50 §2.2 every selected
marking at `h = 1` is `nuSel 1 0 t s` for a unique `(t,s) ∈ ℤ₂²`, and only `(t,s)` mod `2^c`
survives in the class-`c` quotient, so sweeping all of `(ℤ/32)²` **exhausts the binder of
`SqLamMarkTransitivity 1`** at class 5.  The class-5 row of W50's headline therefore upgrades
from a valuation-stratified sample to a complete statement about `Q_5`, joining classes 3
and 4.

Uniformity across all 951 new markings:

| level pattern | markings | `rank δ` / target at the levels exercised | corank | defect in `im δ` | cert |
|---|---|---|---|---|---|
| corrections needed at L₃, L₄, L₅ | 905 | 43/49, 169/175, 673/679 | 6, 6, 6 | yes | true |
| already trivial at L₃ | 39 | 169/175, 673/679 | 6, 6 | yes | true |
| already trivial at L₃ and L₄ | 7 | 673/679 | 6 | yes | true |

**No infeasible marking, no marking with corank ≠ 6, no failed certificate, and the relator's
defect landed in `im δ` at every level of every one of the 951.**  That is
`905·3 + 39·2 + 7·1 = 2800` independent (marking, level) containment events, each at odds
`2^{-6}` if it were chance.

---

## 5.  Class 6

### 5.1  The quotient

`c6build.m`, output `results/c6build.txt`, confirmed independently by the corank run's own
build:

| class | order | layer ranks | cumulative build |
|---|---|---|---|
| 5 | 2^922 | 5, 14, 49, 175, 679 | 16 s |
| **6** | **2^3596** | **5, 14, 49, 175, 679, 2674** | **1835 s**, ~1.0 GB |

W50 predicted "`dim L₆` is a few thousand and the group is of order roughly `2^{3500}`"; the
measured 2674 and `2^3596` sit inside that.  The layer ratios continue to climb slowly:
2.8, 3.5, 3.57, 3.88, **3.94**.

The reason W50 hit a wall here and this wave did not is *not* the `K ∩ P_j` fix; that fix
matters for the marking loop, not for the quotient.  It is that `pQuotient(G, 2, 6)` called
cold is much slower than walking the tower with `pQuotientProcess` and `NextClass`; the same
gap is visible one class down, where the cold call takes 150 s and the incremental route 16 s.

### 5.2  The corank, and the containment

`w51_corank.m`, outputs `results/ck_c6.txt` and `results/ck_c6b.txt`.  **24 markings across two
independent runs**, each of which built its own `Q_6` from scratch (three builds in total,
counting `c6build.m`, all agreeing on order `2^3596` and layers `5, 14, 49, 175, 679, 2674`).

* run A, 8 markings placing at least two in each of the four parity classes of §2.4:
  `(0,1)`, `(1,0)`, `(1,1)`, `(0,2)`, `(2,1)`, `(1,2)`, `(3,5)`, `(2,2)`;
* run B, 16 more chosen for valuation spread and depth: `(0,4)`, `(4,0)`, `(4,4)`, `(8,8)`,
  `(1,4)`, `(5,7)`, `(3,3)`, `(7,7)`, `(0,8)`, `(16,16)`, `(2,4)`, `(9,15)`, `(12,20)`,
  `(31,31)`, `(6,6)`, `(15,9)`.

Every row below was identical at all 24, and **all 24 markings are solvable**.

| level | target `dim L_j` | domain `5·dim K_{j-1}` | `rank δ` | **corank** | defect in `im δ` | cert |
|---|---|---|---|---|---|---|
| L₃ | 49 | 5 × 12 = 60 | 43 | **6** | yes | true |
| L₄ | 175 | 5 × 47 = 235 | 169 | **6** | yes | true |
| L₅ | 679 | 5 × 173 = 865 | 673 | **6** | yes | true |
| **L₆** | **2674** | **5 × 677 = 3385** | **2668** | **6** | **yes** | **true** |

The graded `K` came out as `3, 12, 47, 173, 677` against layers `5, 14, 49, 175, 679`:
codimension 2 at every level, and the §2.2 certificate held at all five, so those are the
genuine `K_w` and not an under-approximation.  That is the load-bearing check: an
under-approximated domain is exactly what would have produced a false report of corank growth.

**The control.**  At `L₆`, per marking, 2000 random vectors of the 2674-dimensional layer were
tested for membership in `im δ`: **33, 32, 31, 20, 28, 39, 30, 22, total 235 of 16000, or
1.47 %**, against the `2⁻⁶ = 1.5625 %` (250 of 16000) that a codimension-6 image predicts.  So
the layer really is 6-corank.

**The containment.**  Across both runs the relator's own defect landed in `im δ` at
**85 out of 85** (marking, level) pairs.  (85 rather than 24 × 4, because at 7 of the deeper
markings the relator was already trivial at `L₃` and/or `L₄` and no map was needed there: the
level counts are 17, 21, 23, 24 at `L₃ … L₆`.)  That is what a random vector does 1.5 % of the
time.

### 5.3  The parity reduction, confirmed at class 6

The §2.4 prediction is that `im δ` is a function of `(t mod 2, s mod 2)` alone.  At class 6, at
**every** level including `L₆`:

| parity of `(t,s)` | reference marking | the others, all reporting **same** |
|---|---|---|
| (0,0) | `(0,2)` | `(2,2)`, `(0,4)`, `(4,0)`, `(4,4)`, `(8,8)`, `(0,8)`, `(16,16)`, `(2,4)`, `(12,20)`, `(6,6)` |
| (0,1) | `(0,1)` | `(2,1)` |
| (1,0) | `(1,0)` | `(1,2)`, `(1,4)` |
| (1,1) | `(1,1)` | `(3,5)`, `(5,7)`, `(3,3)`, `(7,7)`, `(9,15)`, `(31,31)`, `(15,9)` |

**57 same-parity comparisons, 0 differing**, and the four parity references are four distinct
subspaces.  Note that the confirmations include deep-valuation markings such as `(16,16)`,
`(31,31)`, `(12,20)` and `(9,15)`, so the reduction is not an artefact of small `(t,s)`.

This is what licenses reading the class-6 corank off 24 markings as a statement about all
1023: the corank is constant on parity classes, and all four classes were measured.

### 5.4  What was *not* done at class 6

`verify:=1`, the direct comparison against `K meet P_j`, was **not** run at class 6.  At
class 5 those intersections cost 5–8 s per level at order `2^922`; at order `2^3596` they are
the wall the whole method was built to avoid, and the point of §2.2 is that the generating-set
route does not need them to be certain.  The certificate is a proof, not a spot-check, and it
was validated against the intersection route at two lower classes first (§3).

### 5.5  `h = 2` at class 5

`w51_h2.m`, output `results/h2_c5.txt`.  `D_sq 2` (rank `d = 7`, two handle pairs); W50 got
`corank = 8` at `L₃` and `L₄` and stopped at class 4.

| | order | layer ranks | build |
|---|---|---|---|
| `Q_5` for `D_sq 2` | **2^4534** | 7, 27, 132, 672, **3696** | 1760 s, ~1.4 GB |

| level | target | domain `7·dim K_{j-1}` | `rank δ` | **corank** | defect in `im δ` |
|---|---|---|---|---|---|
| L₃ | 132 | 7 × 25 = 175 | 124 | **8** | yes |
| L₄ | 672 | 7 × 130 = 910 | 664 | **8** | yes |
| **L₅** | **3696** | **7 × 670 = 4690** | **3688** | **8** | **yes** |

Six markings, all six solvable, all certificates true, defect in image 18 / 18.  So `d + 1`
holds at both handle counts and at every level either has been measured at:

| | `d` | L₃ | L₄ | L₅ | L₆ |
|---|---|---|---|---|---|
| `h = 1` | 5 | 6 | 6 | 6 | **6** |
| `h = 2` | 7 | 8 | 8 | **8** | n/a |

W50's reading that "the second handle changes nothing qualitatively" survives one class deeper.

---

## 6.  Limitations: what was exhausted and what was sampled

* **Exhausted.**
  * The **class-5 marking grid**, all 1023 uncleared `(t,s)` mod 32 at `h = 1` (§4).  By
    W50 §2.2 that is the entire quantifier of `SqLamMarkTransitivity 1` at class 5, not a
    sample of it.
  * The **corank at class 6**, in the following precise sense: by §2.4 the map `δ_j` and its
    image depend on the marking only through `(t mod 2, s mod 2)`, this wave verified that
    dependence directly at classes 4, 5 and 6, and all four parity classes were measured.  So
    the corank verdict covers every marking, not only the ones listed.
  * The **generating-set certificate** at every level of every marking computed, at every
    class: the two conditions of §2.2 were checked each time, never assumed.
* **Sampled.**
  * The **containment** of the relator's own defect in `im δ`.  This one is genuinely
    marking-dependent (the defect is not a mod-2 object), so it is a sample at class 6:
    24 markings and 85 (marking, level) pairs at class 6, against 1023 markings exhaustively at class 5.
  * The **random-vector control** at class 6, 2000 draws per marking.
* **Not attempted.**
  * **Class 7.**  The class-5-to-6 step cost a factor of about 115 in time over the
    class-4-to-5 step; a seventh layer would be of dimension roughly 10⁴ and the group of
    order about `2^{14000}`.  On the same scaling that is tens of CPU-hours for the quotient
    alone, outside this wave's budget.  It is not obviously out of reach for a wave that wants
    it, and the linear algebra at that size would still be unremarkable.
  * A **second engine.**  GAP/ANUPQ through `sage -gap` would give an independent p-quotient
    implementation.  The W51 numbers at classes 4 and 5 agree with W50's, but both are Magma.
* **What a positive verdict is worth, unchanged from W50 §9.**  A class-`c` certificate says
  the class-`c` quotient admits the clearing automorphism.  The residual needs it in the
  inverse limit, and no finite class can supply that.  The value of this wave is the *absence*
  of a refutation one class deeper than anyone had looked, plus the sharpened structure
  (§2.4, §5.3).

---

## 7.  Reproduction

Run everything with `scripts/w51_class6` as the working directory; the scripts
`load "../w50_depth_sweep/c0.m"` by relative path for the 2-adic constant `c₀`, and write
their output with `PrintFile` to the name given by `out:=`, flushed line by line so that an
interrupted run still leaves its measurements behind.

```
scripts/w51_class6/
  c6build.m       the tower to class 6, incremental and timed
                  magma -b out:=../../data/c6build.txt c6build.m
  w51_corank.m    the corank probe (cls, marks, out, verify, ctrl)
                  magma -b cls:=5 marks:="0,1;1,1;3,5" out:=../../data/ck_c5.txt verify:=1 w51_corank.m
                  magma -b cls:=6 marks:="0,1;1,0;1,1;0,2;2,1;1,2;3,5;2,2" ctrl:=2000 out:=../../data/ck_c6.txt verify:=0 w51_corank.m
  w51_grid.m      the class-5 grid continuation (lo, hi, out)
                  magma -b lo:=0 hi:=1000 out:=../../data/grid_c5.txt w51_grid.m
  w51_h2.m        the h = 2 corank at class 5 (cls, marks, out)
                  magma -b cls:=5 marks:="0,1;1,0;1,1;0,2;2,1;3,5" out:=../../data/h2_c5.txt w51_h2.m
  results/        the output files quoted in this memo
```

`verify:=1` turns on the comparison against W50's `K meet P_j` route and the layer-coordinate
cross-check; it is affordable at class 4 and class 5 and was not run at class 6 (§5.4).
`ctrl:=N` adds the random-vector control at the deepest level.

Measured budgets on this machine (16 cores, six Lean agents sharing it, every job
`nice -n 10`), for the record and for the next wave's planning:

| job | wall | peak RSS |
|---|---|---|
| tower to class 5 (incremental) | 16 s | ~100 MB |
| tower to class 6 (incremental) | **1835 s** | ~1.0 GB |
| tower to class 6 (bare `pQuotient`, W50's `c6size.m`) | **did not finish in ~50 min / ~700 MB** | n/a |
| one class-5 marking, all levels | 0.5–0.9 s | n/a |
| the 951-marking class-5 grid | 677 s | ~150 MB |
