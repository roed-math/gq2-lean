# W53: the d-1 cut identified, and a correction to the W52 bookkeeping

**Wave W53, worker W53-DCUT.**  Off-Lean only: `scripts/w53_dcut/` (Magma V2.29-4, local,
seeded).  No Lean landing, by design (§7).  Continues `docs/dyadic/w52-vanish-note.md` §7
item 1, the open structural item of W52: `corank(δ_j) = d + 1 = 2 + (d − 1)`, where the 2 is
the proved canonical pair `λ, ν` and the `d − 1` was unexplained.

---

## 0.  Headline

| question | answer |
|---|---|
| what is the `d − 1` block? | **The cokernel of the graded Fox form on the FULL dressing domain** (§2).  It has nothing to do with `K`: `corank(Δ_j : (L_{j-1})^d → L_j) = d − 1` exactly, at every level, for every basis of Fox rows and every single Frobenius slot.  Certified for `d = 2 … 6`, classes 3 to 5, in the free ambient, and for the campaign's own relator at `h = 1, 2`. |
| so what is the `+2`? | **Exactly the codimension of `K`** (§3).  The corrected bookkeeping is `corank(Δ\|_{K^d}) = corank(Δ_full) + codim K`, verified at `codim K = 1, 2, 3`: `d + 1` is `(d − 1) + 2` and the 2 is the `λ, ν` pair only because `K` has codimension 2.  The residue `dim K_j/im` is `d − 1` **independent of** `codim K`. |
| an explicit basis of the cokernel? | **Yes** (§2.2, §3.2).  `L_j/im Δ_full` has basis the pure powers `β_i^{2^{j-1}} = F^{j-1}(β_i)` of the Fox rows, `i ≠ s`, with the single relation at the Frobenius slot `s`.  `K_j/im(Δ\|_K)` has basis the bracket powers `[β_i, β_s]^{2^{j-2}} = F^{j-2}([β_i, β_s])`, `i ≠ s`, which lie in `K_j`; adding `σ^{2^{j-1}}, x_0^{2^{j-1}}` (the `λ, ν` duals) gives a basis of the full `(d+1)`-dimensional cokernel. |
| are they the duals of the power-type components? | **Yes, in the precise sense conjectured.**  The `d − 1` functionals live on the *pure-power space* `P_j = L_j/[L_{j-1}, V]`, on which `v ↦ F^{j-1}(v)` is a linear isomorphism from `V` (§1.2).  They are the duals of the Frobenius-image coordinates, killed only along the Frobenius-slot row. |
| does any dressing family supply the block? | **No family of any kind.**  The `d − 1` functionals annihilate `im Δ` on the *full* domain, so no commutator family, no conjugation family, no power family and no combination of them can supply a single one of those `d − 1` dimensions (§3.1).  The `λ, ν` block, by contrast, *is* supplied, by power dressings exactly: `rank φ = codim K` at every level (§3.3). |
| a correction to W52 | **`w52-vanish-note.md` §1.4 states that "on the full domain `(L_{j-1})^d` the form is onto `L_j`". It is not.**  Measured corank there is `d − 1` at every level and every marking, in the campaign's own `Q` as well as in the free ambient (§4).  The identity `corank = 2d − dim proj(ker Δ_full)` of that subsection, and the numbers `ker full = 21, projection = 4`, do not reproduce; the corrected bookkeeping of §3 does. |
| is the block generic in the word? | **Upstairs yes, downstairs no** (§5).  In the free ambient `d − 1` holds for *every* basis of Fox rows and every single Frobenius slot, with no exception in 1081 scored assertions.  Inside the relator's own quotient the ambient carries the relator's initial form and can cut one more dimension: over random even words with full Fox rank and one Frobenius slot, 20 of 23 gave `d − 2` and only the 3 whose Frobenius row lands in `[L_{j-1}, V]` gave `d − 1`.  The relator is one of those 3, by an exact alignment (§4.2). |

---

## 1.  The pure-power space, and the exact power identity

Work in `L = ⊕_w L_w`, `L_w = P_w/P_{w+1}` for the lower exponent-2 central series, `V = L_1`,
`F : L_w → L_{w+1}` the squaring map (`F` is linear for `w ≥ 2`, since the polarization term
`[x,y]` sits in degree `2w > w + 1`).  Write `Δ_j(z) = Σ_i [z_i, β_i] + Σ_{i∈S} F(z_i)` for
the graded Fox form of W52 §1.1, with `β_1, …, β_d ∈ V` the mod-2 Fox rows at the marking and
`S` the set of slots where `e_i/2` is odd.  For this relator `|S| = 1`, `S = {x_1}`; write
`s` for that slot.

### 1.1  The identity

> **`[x^{2^k}, y] = F^k([x, y]) + F^{k-1}(ad(x)^2 (y))`   in `L_{j}`, for `x, y ∈ V`, `k = j − 2 ≥ 1`.**

Machine-checked at every level, every basis pair, `d = 2 … 6`: **0 mismatches**.  The naive
restricted-Lie form `[F(x), y] = ad(x)^2(y)`, which is what a graded restricted Lie algebra
with `deg F = 0` would give and what W52 §1.3 used informally, is **false** here: it failed on
`2, 6, 12, 20, 30` of the `d^2` basis pairs at `d = 2, 3, 4, 5, 6`.  The error term `F^k([x,y])`
is not a nuisance: it is exactly the term that carries the `d − 1` cut.

### 1.2  The pure-power space

Two consequences, both certified:

* `F^{j-2}([v, w]) ∈ [L_{j-1}, V]` for all `v, w ∈ V` (rearrange §1.1), so
  **`π : V → P_j := L_j/[L_{j-1}, V]`,  `π(v) = F^{j-1}(v) mod [L_{j-1}, V]`, is linear.**
  Linearity checked exhaustively over all `2^d` vectors: 0 failures.
* In the free ambient `π` is an isomorphism: `dim P_j = d` and `rank π = d`, at every level,
  `d = 2 … 6`.  `P_j` is the *pure-power space* of the layer: what survives of `L_j` after all
  brackets are discarded.

This is the space the `d − 1` block lives in, and the reason "power-type" is the right word
for it.

---

## 2.  The theorem: the cokernel of the full-domain form

### 2.1  The number

> **For `β` a basis of `V` and `|S| = 1`: `corank(Δ_j : (L_{j-1})^d → L_j) = d − 1`, at every
> level `j ≥ 3`.**

Free ambient, `codim K` playing no role at all:

| `d` | layers (class 4) | `corank Δ_full` at `L₃`, `L₄` | class-5 layers | `corank Δ_full` at `L₃ … L₅` |
|---|---|---|---|---|
| 2 | 2, 3, 5, 8 | 1, 1 | 2, 3, 5, 8, 14 | 1, 1, 1 |
| 3 | 3, 6, 14, 32 | 2, 2 | 3, 6, 14, 32, 80 | 2, 2, 2 |
| 4 | 4, 10, 30, 90 | 3, 3 | 4, 10, 30, 90, 294 | 3, 3, 3 |
| 5 | 5, 15, 55, 205 | 4, 4 | 5, 15, 55, 205, 829 | 4, 4, 4 |
| 6 | 6, 21, 91, 406 | 5, 5 | (not run) | |

Identity frame plus 8 random full-rank frames per rank at class 4, 5 at class 5, each with a
random Frobenius slot.  Controls, reported and not scored: with `S = ∅` the corank is `d`, not
`d − 1` (the whole Frobenius direction is missed); with `|S| ≥ 2` it is still `d − 1` in the
free ambient; with a rank-deficient frame it blows up and **grows with the level** (`d = 4`,
`rank β = 3`: 6 at `L₃`, 12 at `L₄`), so full Fox rank is not a convenience hypothesis.

### 2.2  The basis

> **`{ β_i^{2^{j-1}} : i ≠ s }` is a basis of `L_j / im Δ_full`.**

Equivalently, the linear map `𝔽₂^{slots} → coker(Δ_full)`, `e_i ↦ [F^{j-1}(β_i)]`, is onto with
kernel exactly the line `⟨e_s⟩`.  Three descriptions were checked to agree modulo the image,
at every level and every frame:

| element | reading |
|---|---|
| `c1_i = [β_i^{2^{j-2}}, β_s]` | the power dressing `F^{j-2}(β_i)` of the Frobenius slot, paired |
| `c2_i = [β_i, β_s]^{2^{j-2}}` | the Frobenius power of the bracket of the two rows |
| `c4_i = β_i^{2^{j-1}}` | the pure power of the Fox row |

with `c1_i + c2_i`, `c1_i + c4_i` and `c3_i := F^{j-3}(ad(β_i)^2(β_s))` all **in** the image.
The two witnesses are group identities, not fits:

* `c4_s ∈ im`: dress **every** slot `i` by `β_i^{2^{j-2}}`.  Every pairing `[β_i^{2^{j-2}}, β_i]`
  vanishes because `[x^{2^k}, x] = 1`, and only the Frobenius slot's `F`-term survives, so
  `Δ(z) = β_s^{2^{j-1}}` **exactly**.  (Checked in the group at every level and marking of §4.)
* `c1_i + c4_i ∈ im`: dress the Frobenius slot alone by `β_i^{2^{j-2}}`.
* `c3_i ∈ im`: it is `[[β_i, β_s], β_i]` up to `F`-powers, a bracket against a non-Frobenius row.

So the cokernel is the pure-power space of the Fox rows modulo the one relation coming from the
Frobenius slot, which is the sharp form of "the `d − 1` are the duals of the power-type
components".

---

## 3.  The corrected bookkeeping, and where `λ, ν` come from

### 3.1  The identity

> **`corank(Δ\|_{K^d}) = corank(Δ_full) + codim K`, and `dim K_j / im(Δ\|_{K^d}) = corank(Δ_full)`.**

Certified at `codim K = 1, 2, 3` (each whenever `codim K < d`) for every `d` and level.  For
the campaign, `codim K = 2` and
`corank(Δ_full) = d − 1`, which is the measured `d + 1`.  The residue inside `K_j` is `d − 1`
for **all three** codimensions, so the `d − 1` is not a `K`-phenomenon in any way.

The consequence worth stating plainly: the `d − 1` functionals annihilate `im Δ` on the full
domain `(L_{j-1})^d`.  Any dressing family whatever, commutator, conjugation (W52 §1.3), power
substitution, or any sum of them, lands inside `im Δ_full`, hence is annihilated.  W52 §7 asked
whether power-substitution families could supply the missing kernel directions.  They cannot
supply the block; what they do is supply the `λ, ν` block, and only that (§3.3).

### 3.2  The explicit cokernel basis

`im(Δ|_{K^d}) ⊆ K_j` at every level (re-asserted here, W52 §2), and

> **basis of `L_j / im(Δ\|_{K^d})`  =  `{ [β_i, β_s]^{2^{j-2}} : i ≠ s }`  ∪  `{ p_a^{2^{j-1}} : a = 1 … codim K }`,**

the first `d − 1` lying in `K_j` and forming a basis of the residue `K_j/im`, the last `codim K`
spanning `L_j/K_j`.  For the campaign, `p_1 = σ`, `p_2 = x_0`, and the two are precisely the
`λ, ν` duals of W52 §1.2.  This is checked as a basis (correct rank, correct kernel, membership
in `K_j`), not merely as a spanning set.

### 3.3  What the power dressings do

Let `φ` be the map recording the `Δ`-values of the `codim K` power dressings modulo
`im(Δ|_{K^d})`.  Then **`rank φ = codim K`** at every level, every frame, every codimension.
So restricting the sweep from `(L_{j-1})^d` to `(K_{j-1})^d` costs exactly `codim K`, and the
lost directions are the pure powers of the `K`-complement, that is `λ` and `ν`.  That is the
whole content of the `+2`.

---

## 4.  The campaign instance (`w53_camp.m`)

Same tower, markings, greedy lift and containment test as `w52_fox.m`, with the general handle
count.  Everything above holds inside the campaign's own group, along its own clearing orbit.

| `h` | `d` | class | layers | `K` layers | `corank Δ\|_K` | `corank Δ_full` | residue | `rank φ` |
|---|---|---|---|---|---|---|---|---|
| 1 | 5 | 4 | 5, 14, 49, 175 | 3, 12, 47, 173 | **6** at `L₃, L₄` | **4** | 4 | 2 |
| 1 | 5 | 5 | 5, 14, 49, 175, 679 | 3, 12, 47, 173, 677 | **6** at `L₃ … L₅` | **4** | 4 | 2 |
| 2 | 7 | 4 | 7, 27, 132, 672 | 5, 25, 130, 670 | **8** at `L₃, L₄` | **6** | 6 | 2 |

Markings `(0,1), (1,0), (1,1)` at `h = 1` class 4 and `h = 2`, and `(0,1), (1,1), (0,2), (3,5)`
at `h = 1` class 5.  Also re-asserted at every level: the graded Fox form against honest group
collection (0 mismatches), the conjugation family in `ker Δ` (0 failures), the relator's defect
in `im(Δ|_K)`, and `R(m) = 1` at the end of the lift.  The cokernel bases of §2.2 and §3.2 hold
with kernel exactly the `x_1` slot.

### 4.1  The correction to W52 §1.4

The full-domain corank is `4 = d − 1`, not `0`.  `w52-vanish-note.md` §1.4 asserts the form is
onto there and derives `corank(δ|_K) = 2d − dim proj(ker Δ_full)`; with `corank(Δ_full) = d − 1`
that derivation is void and the correct statement is §3.1.  Concretely, at `h = 1` class 4,
`L₃`: `dim L₃ = 49`, `dim (L₂)^5 = 70`, `rank Δ_full = 45`, so `dim ker Δ_full = 25`, not the
21 quoted; the restricted numbers (`rank 43`, `ker 17`, `corank 6`) do reproduce exactly.  The
`d − 1` value quoted there is right; the route to it was not.

### 4.2  Why the relator sits at `d − 1` and not `d − 2`

Inside `Q` the ambient is not free, and the pure-power space is smaller: the relator's initial
form is `ρ = F(x̄₁) + [x̄₀, σ̄] + [ū, v̄] ∈ L₂`, so `F(ρ) = 0` in `L₃` forces `F^{j-1}(x̄₁)` into
`[L_{j-1}, V]`.  Measured: `dim P_j = d − 1 = 4` in `Q` (against `d = 5` in the free ambient),
and `F^{j-1}(β_{x_1})` is **in** `[L_{j-1}, V]`.  The two effects cancel exactly: the pure-power
space loses one dimension, and the Frobenius-slot relation of §2.2 becomes vacuous because the
relator's Frobenius row is precisely the direction its own initial form kills.  This is why the
campaign sees `d − 1` and not `d − 2`.

---

## 5.  Genericity in the word (`w53_rand.m`)

40 random even words per marking, markings `(0,1)` and `(1,1)`, class 4, in the campaign's `Q`,
Fox rows by W52's walker and Frobenius pattern from the halved exponent vector, plus `R` itself
through the same driver.  The form was cross-checked against honest group collection for the
words with `W(m) ∈ P₃`, which without a stage-A gate is `R` alone at each marking (4 level
instances, 0 mismatches); the broad honest-row validation on gate-passing random words is
W52 §2 and is not repeated here.  Scored for every full-Fox-rank word, 164 assertions,
**0 failures**:

* `im(Δ|_K) ⊆ K_j`;
* `corank(Δ|_K) = corank(Δ_full) + 2`;
* `dim K_j/im(Δ|_K) = corank(Δ_full)`;
* for `|S| = 1`, the two cokernel bases of §2.2 and §3.2 have the predicted ranks, a common
  kernel, and that kernel contains the Frobenius slot.

The *value* of `corank(Δ_full)` in `Q`, over the full-rank single-Frobenius-slot words:

| Frobenius row `β_s` | words (both markings) | `corank Δ_full` |
|---|---|---|
| `F^{j-1}(β_s) ∈ [L_{j-1}, V]` | 3 | `4 = d − 1` |
| `F^{j-1}(β_s) ∉ [L_{j-1}, V]` | 20 | `3 = d − 2` |

Perfect correlation, at `L₃` and `L₄`, with `dim P_j = 4` throughout: **`corank(Δ_full) = dim P_j − [π(β_s) ≠ 0]`**
for every one of the 23 word-derived frames.  (For abstract random frames in `Q` that do not
arise as a word's Fox rows, this formula failed in 4 of 24 trials, so it is recorded as measured
for word-derived frames only.  In the free ambient it is exact and reduces to `d − 1`.)

Reading: the `d − 1` is **universal upstairs**, a property of the graded Fox form of any
full-rank frame with one Frobenius slot in the free layers; a relator quotient can only shrink
it, by the part of the relator's graded ideal that survives to the pure-power space; and this
relator does not shrink it, by the alignment of §4.2.  The `λ, ν` block, by contrast, is the
same subspace `L_j/K_j` for every word, and the number `rank φ = 2` never moves.  Also recorded:
the subspace `im(Δ_full)` itself is different for essentially every word (35 and 34 distinct
subspaces among the 41 words at the two markings, the same counts at `L₃` and `L₄`) and, in the
free ambient, is not determined by `β_s` alone.  So the block is uniform in *description*, not literally the same subspace.

---

## 6.  What is measured and what is proved

**Proved (in Lean, from earlier waves):** nothing in this note.  The `λ, ν` half of the
splitting is W52's committed material (`GradedVanish.lean`); the conjugation-family identity is
`vanShift_commP`/`vanShift_commP_eq_zero`.

**Measured (this wave, exact linear algebra over `𝔽₂`, no sampling in the free ambient):**
1081 scored assertions in the free sweeps (574 at class 4, 507 at class 5) and 198 in the
campaign and word sweeps (9 + 16 + 9 + 164), **0 failures**: the power identity §1.1, the linearity and injectivity of `π` §1.2, the corank
`d − 1` §2.1, the cokernel bases §2.2 and §3.2 with their exact kernels, the bookkeeping
identity §3.1, `rank φ = codim K` §3.3, the campaign instance §4, and the word sweep §5.  The
free-ambient statements are exhaustive over the stated ranks, levels and codimensions and over
all `2^d` vectors where a linearity check is involved; the frames are identity plus random, so
the frame direction is sampled, not exhausted.

**Not measured:** ranks `d > 6`, levels beyond `L₅`, and `|S| ≥ 2` inside the relator quotient
(where the free-ambient `d − 1` degrades to `d − 2`; the relator has `|S| = 1` so this is not on
the campaign's path).

---

## 7.  Why no Lean this wave, and what the next wave should prove

Everything above is a statement about the graded layers `L_w = P_w/P_{w+1}` of the lower
exponent-2 central series and about the Frobenius `F` between them.  The campaign's Lean world
is the class-three *slice* (`SqU4 R` of `GradedThree`/`GradedVanish`), which models the lower
**central** series: its `γ₂`-dressings are commutators, and the layer's Frobenius appears there
only as multiplication by the even exponent weights `(−4, 2)`.  The power dressings of §2.2 and
§3.3 are exactly the dressings the slice cannot represent: over a ring where `2 ≠ 0` the square
`m_k^2` has abelian column `2·(m_k).a ≠ 0`, so it is not `IsGaTwo` and `sqRelWord_vanDress_f`
does not apply to it; the slice sees the `d − 1` block only through the single selection bit of
W52 §3.  A Lean statement of any of §1 to §3 needs the graded
exponent-2 layers as objects, which do not exist in this development.  Writing an abstract
`𝔽₂`-linear-algebra restatement instead would formalize the bookkeeping and leave out all the
content.  Hence a measured-only landing.

In value order, for the next wave:

1. **`corank(Δ_j) = d − 1` in the free layers, as a theorem.**  The statement: for `L` the
   graded layers of the free pro-2 group of rank `d`, `β` a basis of `V`, `s` a single Frobenius
   slot, the map `Δ_j(z) = Σ_i [z_i, β_i] + F(z_s)` on `(L_{j-1})^d` has cokernel of dimension
   `d − 1`, with `{β_i^{2^{j-1}} : i ≠ s}` a basis.  Both halves are now concrete:
   * *the relations* are the group identities of §2.2, all elementary: `[x^{2^k}, x] = 1` gives
     `β_s^{2^{j-1}} ∈ im`, and the exact power identity §1.1 gives the rest;
   * *the independence* is the only real content, and it is a statement about the free graded
     object: `π : V → L_j/[L_{j-1}, V]` is an isomorphism, and `im Δ_full + [L_{j-1}, V] = L_j`
     with `im Δ_full ∩ [L_{j-1}, V]` of the right codimension.  This is where a Lean development
     would have to build the layers.
2. **The bookkeeping identity §3.1** as a lemma once (1) exists: `corank(Δ|_{K^d}) = corank(Δ_full) + codim K`,
   whose only content beyond linear algebra is `rank φ = codim K`, i.e. that the power dressings
   of the `K`-complement are independent modulo `im(Δ|_{K^d})`.  Together with (1) this proves
   the campaign's `corank = d + 1` at every level, in one stroke, for all handle counts.
3. **The exact power identity §1.1** deserves a Lean home at the true-layer level whenever such
   a level exists; it is the correct replacement for the naive `[F(x), y] = ad(x)^2(y)` that W52
   §1.3 used informally, and W52's own conjugation identity should be restated with it.
4. **Repair `w52-vanish-note.md` §1.4** (see §4.1): the "onto on the full domain" claim and the
   corank identity derived from it are wrong, and the class-3 numbers quoted there
   (`ker full = 21`, `projection = 4`) do not reproduce.  Nothing else in that note depends on
   them; §1.2, §2, §3, §5 and §6 stand.

---

## 8.  Reproduction

Working directory `scripts/w53_dcut/`; the campaign scripts `load "../w50_depth_sweep/c0.m"`.

```
w53_free.m   the universal (free-ambient) structure sweep  (ds, cls, kcs, nt, seed, out)
             magma -b ds:="2,3,4,5,6" cls:=4 kcs:="1,2,3" nt:=8 seed:=1 out:=results/w53free_c4.txt w53_free.m
             magma -b ds:="2,3,4,5"   cls:=5 kcs:="1,2,3" nt:=5 seed:=2 out:=results/w53free_c5.txt w53_free.m
w53_camp.m   the campaign ambient, general handle count    (h, cls, marks, out)
             magma -b h:=1 cls:=4 marks:="0,1;1,0;1,1"     out:=results/w53camp_h1c4.txt w53_camp.m
             magma -b h:=1 cls:=5 marks:="0,1;1,1;0,2;3,5" out:=results/w53camp_h1c5.txt w53_camp.m
             magma -b h:=2 cls:=4 marks:="0,1;1,1;1,0"     out:=results/w53camp_h2c4.txt w53_camp.m
w53_rand.m   genericity in the word                        (cls, marks, nw, seed, out)
             magma -b cls:=4 marks:="0,1;1,1" nw:=40 seed:=1 out:=results/w53rand_c4.txt w53_rand.m
results/     committed outputs quoted above; every file ends in a SUMMARY line with the
             number of scored assertions and the number of failures (all zero)
```

Budgets (16 cores, `nice -n 10`, sharing with concurrent agents): `w53_free` class 4 about
2 minutes (dominated by `d = 6`), class 5 about 4 minutes (dominated by `d = 5`, whose free
class-5 quotient has 1109 pc generators); `w53_camp` `h = 1` class 4 under a second, class 5
about 25 s, `h = 2` class 4 about 15 s; `w53_rand` about 9 s.
