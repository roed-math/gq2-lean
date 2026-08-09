# W52: the corank vanishing explained, the identity, and its first committed instance

**Wave W52, worker W52-VANISH.**  Lean: `GQ2/Dyadic/SqCore/GradedVanish.lean` (committed,
std-3, census unchanged).  Off-Lean: `scripts/w52_vanish/` (Magma V2.29-4, local, seeded).
Continues `docs/dyadic/w51-class6-note.md` §8 item 1 and `docs/dyadic/w50-depth-sweep.md`
§9.1 item 3: explain why `corank(δ_j) = d + 1` at every level and why the relator's defect
always lands in `im δ`.

---

## 0.  Headline

| question | answer |
|---|---|
| what IS `δ_j`, structurally? | **The graded Fox form** (§1): `δ_j(z) = Σ_i [z_i, β_i] + F(z_{x₁})` in the layer, with `β_i` the mod-2 abelianized Fox rows of the relator at the marking, which for this relator are **the marking letters permuted by `(σ x₀)(u v)` with `x₁` fixed**, and the Frobenius in the `x₁` slot only.  Machine-checked row by row: **0 mismatches in 5525 rows** at classes 4 and 5, all four parity classes, and on random words (§2). |
| why mod-2 in the marking? | Immediate from the form: the `β_i` and `F` read only mod-2 data of the marking.  W51 §2.4 is a corollary of §1, and its class-3 slice form is now a committed theorem (`vanShift_decomp`, `vanShift_congr_two`). |
| where does `d + 1` come from? | `d + 1 = 2 + (d − 1)`, and the two parts have different explanations (§3).  **The 2 is canonical and proven**: `λ_{j+1}` and `ν_{j+1}` kill `im δ` and kill the relator's defect, at every level (machine-verified as `im δ ⊆ K_{j+1}`, `defect ∈ K_{j+1}`, everywhere).  **The d − 1 is generic**: the measured corank equals `d + 1` for every full-Fox-rank even word, not just the relator (§4). |
| is the *containment* generic too? | **No.  It is a property of THIS relator.**  The discrimination experiment (§4): 48 random admissible words through the identical pipeline; 36 die at the exhaustive class-2 gate; the 12 that pass show the *same* corank 6 but their defect lands in the image only 1 time in 13, the chance rate of a codimension-6 subspace.  The relator: 4/4 here, ~2900/2900 across waves. |
| the identity behind the kernel | The conjugation family `z_i = [m_i, c]` lies in `ker δ` at every level; the mechanism is char-2 Jacobi plus the mixed Frobenius identity plus the class-2 relation `ρ(m̄) = 0` (§1.3).  Committed at class 3 **with its exact error term**: `vanShift_commP` evaluates the shift on the conjugation family as an explicit combination of the relator's own five lower rows; `vanShift_commP_eq_zero` is the vanishing on the class-2 solution locus. |
| is the containment path-dependent? | **No**: 120/120 containment events along random clearing orbits (random GL₂ stage-A survivor, random point of the solution torsor at every level), three markings, class 4 (§5).  Whatever forces the containment is a property of the whole torsor. |

---

## 1.  The identity: the graded Fox form of the dressing-defect map

Work in `Q = pQuotient(D_sq h, 2, c)` with lower exponent-2 central series `P_j`, layers
`L_j = P_j/P_{j+1}`, Frobenius `F : L_j → L_{j+1}` (squaring), commutator pairing
`[·,·] : L_j × L_1 → L_{j+1}`.  Note `L_{j+1} = [L_j, L_1] + F(L_j)` by definition of the
series.

### 1.1  The form

For a word `W` with even exponent vector `e`, a frame `m` with `W(m) ∈ P_j`, and dressings
`z ∈ (L_{j-1})^d` (the map of the sweeps restricts to `z ∈ (K_{j-1})^d`):

> **`δ(z) = W(m·z)·W(m)⁻¹ = Σ_i [z_i, β_i] + Σ_{i : e_i/2 odd} F(z_i)`  in `L_j`,**

where `β_i ∈ L_1` is the image of the Fox derivative `∂W/∂x_i` under
`ℤ[F₅] → ℤ[Q] → L_1 ⊗ 𝔽₂` (sum of the mod-2 prefix classes), evaluated at the marking.
This is the layer shadow of the committed literal defect formula (`Word/Fox.lean`,
`foxDefect_eq`, packet Prop. 4.1).

For **this relator** `R = (x₀^σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ][u,v]` the rows compute by hand to

> `β_σ = m̄(x₀)`, `β_{x₀} = m̄(σ)`, `β_{x₁} = m̄(x₁)`, `β_u = m̄(v)`, `β_v = m̄(u)`,

the permutation `(σ x₀)(u v)` with `x₁` fixed, and `e/2 = (0, −2, 1, 0, 0)` puts the
Frobenius in the `x₁` slot only.  (The committed `sqRelWord_selRefine` already showed the
`(u v)` swap in its two handle pairings; the σ- and x₀-slot pairings are new.)

### 1.2  Immediate consequences

* **Mod-2 dependence** (= W51 §2.4): `δ` reads the marking only through `m̄ mod 2`, hence
  only through `(t mod 2, s mod 2)`.
* **The two canonical cokernel functionals.**  `λ` and `ν′` kill commutators, and
  `λ(F z) = 2λ(z)`, so `λ_{j+1}(δ(z)) = λ_j(z_{x₁}) = 0` on `K`-dressings, same for `ν`.
  Hence **`im δ ⊆ K_{j+1}`**, of codimension 2 in `L_{j+1}`.  The relator's defect also
  lies in `K_{j+1}` (both rows kill the abelian collapse: `−4·1 + 2·2 = 0`, `−4·0 = 0`).
  So 2 of the `d + 1` functionals are canonical, marking-independent, and proven, and the
  defect passes them for the abelian reason.
* **The codimension bookkeeping** now reads: corank `d + 1` in `L_{j+1}` = codimension 2 of
  `K_{j+1}` plus codimension `d − 1` of `im δ` **inside** `K_{j+1}`.  The measured numbers
  agree at every level either handle count was measured at: `47−43 = 173−169 = 677−673 =
  2672−2668 = 4 = d−1` at `h = 1`, and `130−124 = 6 = d−1` at `h = 2`.

### 1.3  The kernel identity (Jacobi/Fox)

For `c ∈ L_{j-2}` the **conjugation family** `z(c)_i = [m̄_i, c]` satisfies `δ(z(c)) = 0`:
with the permuted rows this is

`Σ_i [[m̄_i, c], β_i] + F([m̄_{x₁}, c]) = [c, [β_{x₀}, β_σ] + F(β_{x₁}) + [β_v, β_u]] = [c, ρ(m̄)] = 0`,

using char-2 Jacobi, the mixed identity `[z, F(w)] = F([z,w]) + [[z,w],w]`, and the class-2
relation `ρ(m̄) = 0` (stage-A survival).  It is the graded shadow of `R(m^g) = R(m)^g` and
the layer instance of the committed `foxD_coboundary` (`d¹ ∘ d⁰ = 0`).  All components are
commutators, so the family lies inside `(K_{j-1})^d`: it explains a slab of `ker δ` but not
the corank.

### 1.4  The corank reduction

> **CORRECTED BY W53-DCUT (2026-08-09).**  The surjectivity claim below is FALSE: on the
> full domain the form is NOT onto `L_j` (the span argument ignores that the Frobenius
> slot ties the power contribution to a single coordinate).  W53 measured
> `corank(Delta_full) = d - 1` at every level, with explicit basis the pure powers
> `beta_i^(2^(j-1))` of the Fox rows, `i` away from the Frobenius slot; the corrected
> bookkeeping is `corank(delta restricted) = corank(Delta_full) + codim K`, which settles
> the campaign's `corank = d + 1` at every level in one stroke and identifies the
> `d - 1` block as the duals of the Frobenius-image components, generic in the relator.
> The derived identity and the quoted kernel numbers in this subsection do not reproduce
> (`rank Delta_full = 45`, `ker = 25` at `h = 1`, `L_3`); the restricted numbers (43/17/6)
> do reproduce exactly.  Nothing else in this note depends on this subsection.  See
> `w53-dcut-note.md` for the full account and the statement the next wave should prove.

The original (erroneous) text follows for the record.  On the **full** domain
`(L_{j-1})^d` the form is onto `L_j` (the `β_i` span `L_1` by
`SqModTwoIndep`, and `L_j = [L_{j-1}, L_1] + F(L_{j-1})`), so

> `corank(δ) = 2d − dim proj_{(L/K)^d}(ker Δ_full)`,

and `corank = d + 1` is equivalent to: **the projection of `ker Δ_full` to
`(L_{j-1}/K_{j-1})^d ≅ 𝔽₂^{2d}` has dimension exactly `d − 1`.**  Measured at `L₃`:
`ker` full `= 21`, restricted `= 17`, projection `= 4 = d − 1`.  The x₁-slot constraint
(§1.2) gives `≤ 2d − 2` for free; the remaining `d − 1` cut is the open structural item
(§7).

---

## 2.  Validation: the form is exact in the layer (`w52_fox.m`)

Per marking, per level, every honest row (group collection `R(m·z_ib)·R(m)⁻¹`) was compared
with the formula row `[b, β_i]·(b² if x₁-slot)`:

| class | markings | levels | rows compared | mismatches |
|---|---|---|---|---|
| 4 | (0,1), (1,0), (1,1) | L₃, L₄ | 885 | **0** |
| 5 | (0,1), (1,1), (0,2), (3,5) | L₃, L₄, L₅ | 4640 | **0** |

Also at every (marking, level): `im δ ⊆ K_{j+1}` **true**, defect `∈ K_{j+1}` **true**, and
the conjugation family evaluated through the formula vanished for every basis `c` (0
failures in 329 instances).  The K-generating-set certificates of W51 §2.2 were asserted
throughout.  Random words: the general-`W` form (Fox rows by the walker) matched the honest
rows on every random word that reached stage B (`form-mism 0` in `w52rand_c4.txt`).

---

## 3.  What `d + 1` is

* **2, canonical, proven** (§1.2): `λ_{j+1}`, `ν_{j+1}`.  Marking-independent.  The defect
  passes them by the abelian collapse.  This pair is exactly the codimension of `K_{j+1}`,
  which is why the sweeps' per-level numbers always show `im δ` of codimension `d − 1` in
  the graded `K`.
* **`d − 1`, marking-dependent mod 2, generic** (§4): the residual cut inside `K_{j+1}`.
  At class 3 the slice sees exactly one bit of it, the selection bit, and its vanishing on
  the relator is the committed `selConWit_even`/`selCon_contain`.  At `h = 1` it is 4
  bits; they move with `(t mod 2, s mod 2)` because the whole form does (§1.2).

---

## 4.  The discrimination experiment (`w52_rand.m`): this relator, or all words?

Random words `W = C₁·A·C₂` (`C_i` products of conjugated random commutators, `A` fixing an
abelianization killed by both rows exactly: `R`'s own `(0,−4,2,0,0)`, or `0`, or the handle
vector `(0,0,0,2s,−2t)`), through the **identical** pipeline in the same `Q₄`: exhaustive
stage A over the 8⁵ level-one codes with the rank-5 frame condition, then the greedy lift
with `W` playing `R`'s role in both the defect and the map.  24 words per marking, markings
`(0,1)` and `(1,1)`, seed 1; `R` itself as word 0 through the same driver.

| outcome | `R` | 48 random words |
|---|---|---|
| stage-A gate | 6 survivors (the GL₂ torsor) | **36 empty**, 12 with exactly 6 survivors |
| corank at levels reached | 6, 6 | **6 at every level reached** (all 12 had full-rank Fox rows) |
| defect in `im δ` | 4/4 events | **1/13 events** (11 stuck at L₃, 1 passed L₃ then stuck at L₄) |
| solvable to class 4 | yes, both markings | **0 of 48** |

Reading:

* **The corank `d + 1` is generic.**  Every gate-passing word, all with mod-2 Fox rows of
  full rank 5, produced corank exactly 6 at every level it reached.  The corank is linear
  algebra of the graded Fox form of *any* full-rank even word, not a property of `R`.  (A
  proof of `corank = d + 1` from the form alone is thereby the right target, and nothing
  about it will use `R` beyond `SqModTwoIndep` and the Frobenius pattern; §7.)
* **The containment is not generic.**  1/13 is the chance rate `2⁻⁶ ≈ 1.6 %` of a
  codimension-6 subspace (P ≈ 18 % to see ≥ 1 hit in 13).  What separates `R` is not the
  map but the *target*: `R` is a relation of the group, so its defect is a pure dressing
  artefact, while a random word's defect carries the word's own class, which is generic in
  the layer.
* Also worth recording: 3/4 of random admissible words cannot pass class 2 at all, against
  an exhaustive gate.  The class-2 gate is itself a strong filter that `R` passes at every
  marking by the committed `GradedTwo` closed forms.

---

## 5.  Torsor invariance (`w52_orbit.m`)

The sweeps always take the first stage-A survivor and the particular solution at each
level.  120 random clearing orbits (random survivor among the six GL₂ codes, random point
of `x₀ + ker δ` at every level), three markings, class 4: **containment 120/120, all
orbits end at `R(m) = 1`.**  The containment is a property of the whole solution torsor,
so a proof may (and the class-3 committed one does) exhibit any convenient section.

---

## 6.  The Lean landing: `GQ2/Dyadic/SqCore/GradedVanish.lean`

Class-3 slice (the committed `SqU4` test group), over any commutative ring, all handle
counts, no cleared hypotheses; 480 lines; all prints std-3 or axiom-free.

* **§1–§2 the five-slot dressing action**: `vanDress`, `vanShift`,
  `sqRelWord_vanDress_a..f`.  Dressing *every* slot by `γ₂`-elements moves the relator's
  six rows by: nothing (abelian rows), the even exponent weights `(−4, 2)` (class-2 rows;
  the slice image of the Frobenius part), and the affine form `vanShift` (class-3 row),
  whose pairing coefficients exhibit the permuted-letter pattern of §1.1.  Extends the
  committed `sqRelWord_selRefine` (four slots, exponent slots `γ₃`-only) to the full frame;
  the σ-slot and `γ₂`-exponent-slot pairings are the new terms.
* **§3 the vanishing identity**: `vanShift_commP` evaluates the shift on the conjugation
  family as an explicit combination of the relator's own five lower rows (proof: word
  functoriality of conjugation against the closed form, then `linear_combination`; no
  polynomial expansion), and `vanShift_commP_eq_zero` is the vanishing on the class-2
  solution locus.  This commits §1.3 at class 3 with the error term exhibited.
* **§4 the parity collapse**: `vanShift_decomp` splits `vanShift` exactly as the plus-signs
  pairing form `vanShiftPar` (which reads only the marking's outer abelian columns, in the
  permuted-letter pattern) plus `2·vanShiftEven`; `vanShift_map` and `vanShift_congr_two`
  derive that under any ring map killing 2 the action reads only the mod-2 columns.  This
  commits W51 §2.4 at the slice.

---

## 7.  What remains for the general-level proof

In value order:

1. **The `d − 1` cut, structurally.**  By §1.4 the whole corank statement is: the
   projection of `ker Δ_full` to `𝔽₂^{2d}` has dimension `d − 1`.  The needed kernel
   elements have power-type components (`F^{j-1}σ̄`, `F^{j-1}x̄₀` coordinates), which no
   commutator family supplies; candidate sources are power-substitution families
   `x_i ↦ x_i^{1+2^{j-1}}` paired across slots.  This is now a concrete, finite question
   about the graded Fox form, generic in the word (§4), and nothing about it samples.
2. **The containment as a theorem.**  The right statement, by §4 and §5: for the
   *relator*, the defect of any `K`-dressed frame lies in `im δ` at every level, along the
   whole torsor.  A proof at class 4 would be the first beyond the committed class-3 one;
   the stage-abstraction machinery of W52-LIFT (`GradedLift`/`GradedFour`) is the natural
   carrier, and the graded Fox form gives the map in closed form there.
3. **Class 6 at `h = 2`**, only as a spot check of `d + 1 = 8` one level deeper; the
   generic-corank reading of §4 lowers the value of more depth.
4. The mixed identity `[z, F(w)] = F([z,w]) + [[z,w],w]` and the two-slot Jacobi mechanism
   of §1.3 deserve a Lean home at the true-layer level (not the slice) when a graded-layer
   formalization exists; the slice instance is committed.

---

## 8.  Reproduction

Working directory `scripts/w52_vanish/`; all scripts `load "../w50_depth_sweep/c0.m"`.

```
w52_fox.m    the graded-form row validation + structure tests (cls, marks, out)
             magma -b cls:=4 marks:="0,1;1,0;1,1" out:=results/w52fox_c4.txt w52_fox.m
             magma -b cls:=5 marks:="0,1;1,1;0,2;3,5" out:=results/w52fox_c5.txt w52_fox.m
w52_rand.m   the discrimination experiment (cls, marks, nw, seed, out)
             magma -b cls:=4 marks:="0,1;1,1" nw:=8 seed:=1 out:=results/w52rand_c4.txt w52_rand.m
w52_orbit.m  torsor invariance (cls, marks, no, seed, out)
             magma -b cls:=4 marks:="0,1;1,1;3,5" no:=20 seed:=7 out:=results/w52orbit_c4.txt w52_orbit.m
results/     committed outputs quoted above
```

Budgets (16 cores, `nice -n 10`, sharing with concurrent agents): `w52_fox` class 4 in
~5 s, class 5 in ~70 s; `w52_rand` ~6 min (dominated by 49 exhaustive 8⁵ stage-A scans);
`w52_orbit` ~50 s.  Verification of the Lean file:
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
GQ2/Dyadic/SqCore/GradedVanish.lean` from the worktree root, plus the full-mirror collision
test (olean generated into a cache mirror, `import GQ2` + the module, every public name
checked; passed).
