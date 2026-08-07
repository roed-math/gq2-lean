# W50 — the depth-4/5 nilpotent-quotient sweep of the arbitrary-dressing residual

**Wave W50, worker W50-SWEEP.  OFF-LEAN.  No Lean was written, edited or built.**

The campaign's last odd-lane residual is `SqLamMarkTransitivity h`, equivalently
`SqClearingStep h`, equivalently (`sqArbRelWord_iff_clearingStep`, `sqArbRelWord_one_iff`)
the arbitrary-dressing word equation `SqArbRelWord h`.  The **discrete** analogue of the
statement is false — the ν′-row pair transforms in SL₂(ℤ) under the handle mapping-class
moves and its invariant cannot be killed — yet every finite-quotient probe so far passes.
The existing evidence stopped at the class-3 / order-32 horizon (all 2-groups of order ≤ 32;
85 random class-three homs over ℤ/4, ℤ/8, ℤ/16).  This sweep goes to **class 4 and class 5**
of the universal pro-2 quotient tower of `D_sq 1`.

---

## 0.  Headline

| question | answer |
|---|---|
| **(a)** does the dressing system stay solvable at every uncleared selected marking, at class 4 and class 5? | **Yes.**  Class 3: 63/63.  Class 4: 255/255 (exhaustive in (t,s) mod 16).  Class 5: 103/103 sampled (of 1023). |
| **(b)** structure of the survivor set | Level one is **not** a coset: it is a `GL₂(𝔽₂)`-torsor on the handle block, times a **forced** core dressing.  Every deeper level is a genuine affine coset — the solution set of an 𝔽₂-linear system — of dimension 17 (L₃), 66 (L₄), 192 (L₅). |
| **(c)** any infeasible marking (= refutation lead)? | **None found.**  Zero infeasible markings at every class and every marking probed. |

The sweep does have discriminating power.  With the dressings restricted to any one block —
handle-only (that is the discrete/SL₂ regime), core-only, σ/x₀-only, x₀-only — it returns
**INFEASIBLE at 60 of 63 markings at class 3 and at all 63 at class 4**; and it reproduces
the committed `D₄` / `D₈` refutations of the restricted `U`/`V`-word families while seeing
the arbitrary family survive every one of them.  So "solvable" is a measurement, not an
artefact of a harness that always says yes.

---

## 1.  Tools

| tool | version | used for |
|---|---|---|
| **Magma** | **V2.29-4** (`/Applications/Magma/magma`) | `pQuotient` (the ANU p-quotient algorithm), pc arithmetic, subgroup intersections, `EchelonForm`/`IsConsistent` over `GF(2)` |
| **Python 3** | 3.13 (miniforge), **no third-party packages** | the 2-adic constants, the independent class-two model, the graded closed-form checks, the dihedral calibration |

⚠ **GAP is not installed on this machine.**  The name `gap` in the interactive shell is an
alias for `git apply`; there is no GAP binary under `/usr/local`, `/opt/homebrew`,
`/Applications` or the conda prefixes.  Magma's `pQuotient` is the same ANU algorithm that
ANUPQ wraps, so nothing was lost.  `sympy` is also absent; the 2-adic arithmetic is plain
integer arithmetic modulo `2^N`.

All randomness is seeded (`SetSeed(1)` in Magma, `random.Random(20260807)` in Python).

---

## 2.  The model, extracted from the Lean sources

Everything below was read off the code, not off prose.

### 2.1  The group

`GQ2/Dyadic/SqCore/Cores.lean`:

```
sqWord s x y   = (conjP x s)⁻¹ * (x^3)⁻¹ * y^2 * commP y (conjP y s)
sqRelWord m    = sqWord (m 0) (m 1) (m 2) * handleWord …
conjP x g = g⁻¹xg      commP x y = x⁻¹y⁻¹xy      (GQ2/Words.lean)
handleWord u v = ∏_{j<h} commP (u j) (v j)       (MarkedCore/Cores.lean)
```

At `h = 1`, on `σ, x₀, x₁, u, v` (`sqRank 1 = 5`):

```
R  =  (x₀^σ)⁻¹ · x₀⁻³ · x₁² · [x₁, x₁^σ] · [u,v]
   =  σ⁻¹x₀⁻¹σ · x₀⁻³ · x₁ · σ⁻¹x₁⁻¹σ · x₁ · σ⁻¹x₁σ · u⁻¹v⁻¹uv
```

Magma's `x^g = g⁻¹xg` and `(a,b) = a⁻¹b⁻¹ab` agree with `conjP`/`commP` on the nose, so the
relator transcribes letter for letter.

### 2.2  The two rows

* `λ = nuLam` (`SqCore/HandleMixFixesCore.lean:234`) is the χ-exponent row
  `λ(σ,x₀,x₁,u,v) = (c₀, 1, 2, 0, 0)`, where `c₀ = sqPivotExp` (`SqCore/Certificate.lean:156`)
  is the 2-adic unit with `X^{c₀} = S`.
* `ν′ = nuSel 1 0 t s` (`SqCore/HandleEichler.lean:547`) is `(1, 0, 0, t, s)`.
  `ν′(x₁) = 2ν′(x₀) = 0` is forced by the core.

`c₀` was computed from scratch (`padic_c0.py`): Hensel-lift `X` from `Z³+2Z²+1`, set
`S = −X³/(X²+X+1)`, `Y = −X²`, and `c₀ = log S / log X` on `1+4ℤ₂`.  Committed anchors
reproduce: `X ≡ 5`, `S ≡ 13`, `Y ≡ 7 (mod 16)` and `Y² = X⁴` (`YvalUnit_sq_eq`).
`c₀ ≡ 7 (mod 32)`, `≡ 231 (mod 256)`, `= 2478564816510346471 (mod 2^64)` — odd, as
`isUnit_sqPivotExp` requires.

### 2.3  The frame

`SqCore/Certificate.lean`, `SqCore/LamFrames.lean`, `SqCore/ArbFrames.lean`:

```
w   = σ · x₀^{−c₀}                       λ(w) = 0,  ν′(w) = 1
U   = w^{−t} · u   (sqEichU)             V = v · w^{−s}   (sqEichV)
t̄   = x₀⁻² x₁                            the ℤ/2-torsion generator of H₁
base = (σ, x₀, x₁, U, V)                 sqArbBase
m i  = base i · a i ,  a i ∈ K = ker λ ∩ ker ν′        sqArbFrame
```

### 2.4  The two constraints, enforced

1. **`SqModTwoIndep`** (`ArbFrames.lean` §2).  The five slot images must be independent in
   `H₁ ⊗ 𝔽₂`.  In a quotient `Q` of `D_sq 1` this is checked as rank 5 of the matrix of the
   slots in `Q/P₂(Q) = 𝔽₂⁵`.  Sound as a *necessary* condition: an index-2 open normal
   subgroup of `Q` pulls back to one of `D_sq 1`.
2. **`Φ(K) = ⟨Φ(Ū), Φ(V̄), Φ(t̄), [Im Φ, Im Φ]⟩`** — **not** the preimage of the abelianised
   `K`.  The sweep builds `K := sub<Q | U, V, t̄, DerivedSubgroup(Q)>` and **asserts**
   `Index(Q,K) = 4^c` at every class, which is exactly the index of `ker λ ∩ ker ν′` in the
   class-`c` quotient (where `Q^ab = ℤ/2 × (ℤ/2^c)^4`, so both rows are seen mod `2^c`).
   The assertion passes at `c = 3, 4, 5`, so on the *p-quotients* the two models coincide —
   which they need not do on a general small test group, and that is the W48 trap.

   Together with a one-line algebraic argument this **proves** the model rather than
   assuming it.  `⊆`: `λ(U) = −t·λ(w) + λ(u) = 0` and `ν′(U) = −t·ν′(w) + ν′(u) = −t + t = 0`;
   likewise for `V`; `λ(t̄) = 2 − 2 = 0` and `ν′(t̄) = 0`; and `[Q,Q]` dies under every
   homomorphism to an abelian group.  So `K ⊆ ker λ ∩ ker ν′`.  `=`: the `(σ,x₀)` minor of
   the two rows is `det [[c₀,1],[1,0]] = −1`, a 2-adic unit, so `(λ,ν′) : Q^ab → (ℤ/2^c)²`
   is surjective and `ker λ ∩ ker ν′` has index exactly `4^c` — which the assertion confirms
   is the index of `K`.  Hence equality.  (Both halves of that argument are independent of
   `(t,s)`, which is why `w50_sweep2.m` runs the index assertion once per class rather than
   once per marking, while `w50_sweep.m` runs it at every marking; both pass.)
   ⚠ The larger, wrong model is the preimage of the
   abelianised `K` computed in a quotient where `λ` and `ν′` are only seen modulo a *smaller*
   power of 2 than `ker Φ` reaches; on the class-`c` p-quotient that gap is exactly zero,
   which is why the two agree here and need not agree on a small test group.

### 2.5  What is actually decided

`sqLamMarkTransitivity_iff_frames` / `sqArbRelWord_of_clearingStep` make the existential
equivalent to: *find `m : Fin 5 → D_sq 1` with `R(m) = 1`, `m` generating, `λ(m i) = λ(gen i)`
and `ν′(m i) = ν_sq(gen i)`.*  Pushed into a finite quotient `Q` that is exactly

> **∃ ψ ∈ Aut(Q) with `λ∘ψ = λ` and `ν′∘ψ = ν_sq`.**

A **positive** verdict in `Q` is a certificate *about `Q`* (positive evidence for the residual,
never a proof of it).  A **negative** verdict in `Q` would refute `SqArbRelWord 1`, hence
`SqLamMarkTransitivity 1`, outright.

---

## 3.  The three cross-validations

| # | committed fact | check | result |
|---|---|---|---|
| (a) | `CommFrames.lean`: the abelian collapse is `(m₁⁴)⁻¹m₂²`, frame `ℤ/2·t ⊕ ℤ₂σ̄ ⊕ ℤ₂x̄₀` | `AbelianQuotientInvariants(G)` | `[2,0,0,0,0]` = `ℤ/2 ⊕ ℤ₂⁴`, and `Q_c^ab = [2, 2^c, 2^c, 2^c, 2^c]` — **matches** |
| (b) | `GradedTwo.lean`, `SqHeis.sqWord_c = −4x.c + 2y.c + (s.a·x.b − x.a·s.b) + 10(x.a·x.b) + y.a·y.b − 8(x.a·y.b)`, and `sqHeisDefect` | `graded_crosscheck.py`: `SqHeis` built over `ℤ/64`, closed form vs direct word evaluation, 4000 random markings | **0 mismatches** (both `sqWord_c` and `sqRelWord_c` at `h=1`) |
| (c) | `GradedThree.lean`: `SqU4`, `u4Comm3`, `sqU4Core`, `sqU4Defect`, `SqU4.sqRelWord_f`, `sqU4_top_range` | same script: `U₄(ℤ/64)`, closed form vs direct evaluation, 4000 markings | **0 mismatches**; the two class-two rows are recovered as `GradedTwo`'s defect pulled back through `toHeisAB`/`toHeisBC` (0 mismatches each); the adjustable set of the class-three coordinate is exactly `2R` (`sqU4_top_range`); the σ-slot's and both handle slots' class-three coordinates cancel outright (`GradedThree` finding 3) |

A fourth, unplanned validation fell out: the level-one survivor analysis reproduces
`sqArbFrame_x0_dressing_forced` (`GradedTwo` §6) **exactly** — see §6.2.

---

## 4.  The quotient tower

`pQuotient(D_sq 1, 2, c)`, Magma 2.29-4:

| class `c` | order | layer ranks `dim P_i/P_{i+1}` | `Q^ab` | build time |
|---|---|---|---|---|
| 1 | 2^5 | 5 | (ℤ/2)^5 | < 0.01 s |
| 2 | 2^19 | 5, 14 | ℤ/2 × (ℤ/4)^4 | < 0.01 s |
| 3 | 2^68 | 5, 14, 49 | ℤ/2 × (ℤ/8)^4 | < 0.01 s |
| 4 | 2^243 | 5, 14, 49, 175 | ℤ/2 × (ℤ/16)^4 | 0.2 s |
| 5 | **2^922** | 5, 14, 49, 175, 679 | ℤ/2 × (ℤ/32)^4 | 150 s |

Layer 2 has rank 14 = 15 − 1: the single relator eats exactly one dimension of
`Λ²(𝔽₂⁵) ⊕ 𝔽₂⁵`, as `GradedTwo`'s "`r̄ = 2·t̄` is a non-torsion vector" argument predicts.

Because `Q_c^ab` has exponent `2^c` on its free part, **`(t,s)` matters exactly mod `2^c`**:
8 values each at class 3, 16 at class 4, 32 at class 5.

---

## 5.  Method

### 5.1  The filtration trick that makes this tractable

`Aut(Q_5)` for a group of order `2^922` is out of reach, and `|K|^5 ≈ 2^4600` forbids brute
force.  The exponent vector of the relator is `(0, −4, 2, 0, 0)` — **all even** — and that is
what buys the whole computation:

> If every `z i` lies in `P_j(Q)` then `R(m·z) ≡ R(m) (mod P_{j+1})`, because `z i` is central
> mod `P_{j+1}` and `Π z i^{e_i} = z₁^{−4} z₂^{2} ∈ P_{j+1}`.

Consequently the defect map

```
δ_j : (K ∩ P_j / K ∩ P_{j+1})^5  ⟶  P_{j+1}/P_{j+2}          δ_j(z) = R(m·z)·R(m)⁻¹
```

is well defined and **𝔽₂-linear** (the `[z_i, z_l]` terms lie in `P_{2j} ⊆ P_{j+2}` for
`j ≥ 2`, and the squaring map on a layer is a Frobenius), and it depends on `m` only through
`m mod P₂`.  Killing the relator becomes one Gaussian elimination per class.

⚠ The code does **not** rely on that linearity argument being right.  After solving the
linear system it re-evaluates `R(m)` in the group and **asserts** `R(m) ∈ P_{j+1}`; a
non-linear `δ` would trip that assertion.  It never tripped, across roughly 600 solves.

### 5.2  Stage A — the level-one enumeration (the class-two balance gate)

Modulo `K ∩ P₂`, a dressing `a i` is `U^α V^β t̄^γ` with `(α,β,γ) ∈ 𝔽₂³` — 8 choices per slot,
`8^5 = 32768` codes.  Whether `R(m) ∈ P₃` is decided in `Q_2` (order 2^19), where `P₃ = 1`;
it depends on `(t,s)` only mod 4, so the 16 residues are cached.  `SqModTwoIndep` is imposed
here.  This stage is **exhaustive**.

That the 8 codes are a complete set of coset representatives is not an assumption: `K`'s
image in `Q/P₂ = 𝔽₂⁵` is the span of `Ū, V̄, t̄`, which is 3-dimensional (they hit the
independent basis directions `ū`, `v̄`, `x̄₁`), so `K/(K ∩ P₂)` has order exactly 8 and the
eight products `U^α V^β t̄^γ` enumerate it bijectively.  Higher powers `U², V²` lie in
`K ∩ P₂` and are absorbed by Stage B.

### 5.3  Stage B — the lift

For each Stage-A survivor, for `j = 3 … c`: if `R(m) ∉ P_{j+1}`, build a basis of
`(K ∩ P_{j−1})P_j/P_j` (echelon form of the pc generators of `K ∩ P_{j−1}` in
`quo<P_{j−1}|P_j>`, with group representatives recovered from the transformation matrix),
assemble the `5·dim` rows of `δ_{j−1}`, and solve `x·A = R(m)⁻¹` with `IsConsistent`.
Apply the correction, assert `R(m) ∈ P_{j+1}`, continue.

Every accepted witness is then **audited**: `R(m) = 1` exactly, rank 5 of the Frattini
matrix, and `base i⁻¹ · m i ∈ K` for all five slots.

### 5.4  Soundness

* A **solvable** verdict is a full certificate for the class-`c` quotient: an explicit `m`
  with `R(m)=1`, generating, and legal dressings.  Independent of everything in §5.1.
* An **infeasible** verdict would need the greedy to be complete.  It is **not** guaranteed
  to be: `δ` is *not* surjective (corank exactly 6 at every level, see §6.3), so a failure at
  level `j+1` could in principle be repaired by a different choice inside `ker δ_j`, and the
  sweep does not backtrack into that kernel.  **No infeasible verdict arose in the main
  sweep**, so this never mattered for the headline.  It matters only for the restricted-regime
  probe of §8, and there the 48 cases whose class-two gate is *empty* are exact — Stage A is
  an exhaustive enumeration, so an empty gate is a certificate, no search involved.
  Had the main sweep produced an infeasible marking, the ticket's "verify twice" rule would
  have required a full backtracking re-run plus an independent (non-Magma) confirmation
  before it could be reported; it did not, so no such witness exists to report.

---

## 6.  Results

### 6.1  The main sweep

| class | `(t,s)` range | markings probed | **solvable** | **INFEASIBLE** |
|---|---|---|---|---|
| 3 | `(ℤ/8)²` | 63 (exhaustive, all uncleared) | **63** | **0** |
| 4 | `(ℤ/16)²` | 255 (exhaustive, all uncleared) | **255** | **0** |
| 5 | `(ℤ/32)²` | 103 sampled (of 1023) | **103** | **0** |

The class-5 sample is `t,s ∈ [0..7]` exhaustively (63 markings) plus a valuation-stratified
tail of 40: `(0,8),(8,0),(8,8),(0,16),(16,0),(16,16),(1,8),(8,1),(1,16),(16,1),(3,8),(8,3),
(2,16),(16,2),(4,8),(8,4),(12,20),(20,12),(9,15),(15,9),(5,11),(11,5),(31,31),(31,1),(1,31),
(17,17),(24,8),(8,24),(28,4),(4,28),(8,16),(16,8),(0,24),(24,0),(2,8),(8,2),(6,10),(10,6),
(13,26),(26,13)` — covering every 2-adic valuation pair `(v₂(t), v₂(s))` with
`min ≤ 4`, both parities, and the deepest uncleared rows.

### 6.2  Structure of the survivor set (question **b**)

**Level one is rigid, and it is where the mathematics is.**  For *every* `(t,s)` there are
exactly **6** survivors out of 32768, with this shape:

```
a₀ (σ-slot)  = U^{−s} V^{t}          (mod squares)      ← forced
a₁ (x₀-slot) = U^{−s} V^{t}          (mod squares)      ← forced, = GradedTwo §6
a₂ (x₁-slot) = 1                     (mod squares)      ← forced
(a₃, a₄)     : the handle pair (U,V) transformed by an arbitrary element of GL₂(𝔽₂)
```

The `x₀`-slot value is **exactly** `sqArbFrame_x0_dressing_forced`'s `U^{−s}V^{t}`
(`GradedTwo` §6), reproduced by two independent implementations.  `GradedTwo`'s forcing
theorem carries the gauge hypothesis `a 2 = a 1 ^ 2`; the sweep shows the `x₁`-slot is forced
to be trivial mod squares, which is that gauge, and additionally that the **σ-slot carries
the same forced dressing** — a constraint the class-two forcing theorem does not state.

**Audit of the class-4 run** (all 255 markings), showing how uniform the witness is:

| level-one witness actually used | markings |
|---|---|
| `a₀ = a₁ = 1` (t, s both even) | 63 |
| `a₀ = a₁ = V` (t odd, s even) | 64 |
| `a₀ = a₁ = U` (t even, s odd) | 64 |
| `a₀ = a₁ = UV` (t, s both odd) | 64 |

with `a₂ = a₃ = a₄ = 1` throughout — the sweep takes the first `GL₂(𝔽₂)` survivor, which is
the identity, so **the handle block never has to move**; its freedom is spare capacity.  Of
the 255, 240 needed corrections at both `L₃` and `L₄`, 12 only at `L₄`, and 3 — `(0,8)`,
`(8,0)`, `(8,8)` — needed none at all (the undressed base frame already kills the relator in
`Q_4`).

⚠ **The survivor set is therefore *not* an affine coset at level one.**  Its handle block is
a `GL₂(𝔽₂) ≅ S₃` torsor — a non-abelian 6-element subset of `𝔽₂⁴` whose differences span a
4-dimensional space.  Any earlier "the survivors form a coset" reading must be about the
deeper levels, where it is exactly right: the level-`j` solution set is
`x₀ + ker δ_{j−1}`, a genuine affine coset.

`GL₂(𝔽₂)` here is the **mod-2 shadow of the SL₂ that obstructs the discrete case** — see §8.

### 6.3  The defect map, level by level (uniform across every marking and every class)

| level | target `dim L_j` | domain `5·dim(K∩P_{j−1} layer)` | `rank δ` | `dim ker` | corank in target |
|---|---|---|---|---|---|
| L₃ | 49 | 5 × 12 = 60 | 43 | 17 | **6** |
| L₄ | 175 | 5 × 47 = 235 | 169 | 66 | **6** |
| L₅ | 679 | 5 × 173 = 865 | 673 | 192 | **6** |

The corank is **exactly 6 at every level and every marking**: six 𝔽₂-functionals on each
layer that no dressing can move.  The relator's defect always lands in the 43-/169-/673-
dimensional image — never in the 6-dimensional complement.  At `h = 2` (rank 7) the same
measurement gives corank `132 − 124 = 8`, so across both handle counts

> **corank(δ_j) = d + 1**,  `d = sqRank h = 3 + 2h` the number of generators,

at every level measured.  Whether that persists at class 6 is the obvious next probe, and it
is the one number to watch: a level at which the corank *grows* is where a refutation could
first hide.

**And that is not luck.**  `w50_coker.m` measures it (class 4, ten markings, both levels):

* the defect lies in `im δ` — **20 / 20**;
* a **random** vector of the layer lies in `im δ` — **32 / 2000 ≈ 1.6 %**, matching the
  `2⁻⁶ = 1.56 %` a codimension-6 subspace predicts;
* ⚠ the image is **marking-dependent**: `im δ` for `(1,0)`, `(1,1)`, `(1,2)`, `(3,5)`,
  `(2,2)`, `(0,2)`, `(5,7)`, `(1,4)` all differ from `(0,1)`'s (only `(2,1)` coincides).
  There is therefore **no single canonical codimension-6 obstruction space**; the six
  unreachable functionals move with the marking.

Over the whole sweep this "hit" occurred at roughly 600 independent (marking, level) pairs
with a per-event chance probability of `1/64`.  The vanishing of the obstruction is a
structural identity of this presentation, not a numerical coincidence — which is precisely
why no refutation is visible at class 4 or 5, and why looking for one in the cokernel of a
*single* level is the wrong search.

Per-slot anatomy at `L₃`, marking `(t,s)=(1,1)` (which slot-coordinates the defect reads):

```
rank of δ restricted to one slot   (σ, x₀, x₁, u, v) = (12, 12, 12, 11, 11)
joint rank 43 of 49                (domain dim per slot = 12)
```

The three core slots inject; the two handle slots each lose one dimension.  No single slot
gets past rank 12, so the 43 is genuinely joint — the defect reads all five slots.

### 6.4  The `h = 2` spot-check

`w50_h2.m`.  `D_sq 2` is rank 7 with the same single relator plus a second handle;
`ν′ = nuSel 2 j t s` puts `(t,s)` on handle `j` and `0` on the other, and the other handle's
rows are preserved for free (`nu_sqArbFrame_handleU_ne`), so the conditions are literally the
same three.  `K/(K ∩ P₂)` is now 5-dimensional (basis `U, V, t̄, u′, v′`), so the level-one
space is `32^7 ≈ 3.4·10¹⁰` and exhaustive enumeration is out; the search seeds with the
`h = 1` structure (σ and x₀ carrying the forced `U^{−s}V^{t}`, x₁ undressed) over both handle
blocks, plus 3000 random tuples.

| class | quotient | layer ranks | markings (both handles) | solvable | INFEASIBLE |
|---|---|---|---|---|---|
| 2 | 2^34 | 7, 27 | 30 (all, `(t,s)` mod 4) | **30** | **0** |
| 3 | 2^166 | 7, 27, 132 | 126 (all, `(t,s)` mod 8) | **126** | **0** |
| 4 | 2^838 | 7, 27, 132, 672 | 30 sampled (`t,s ∈ [0..3]`) | see §6.1 note | **0** |

The seeded level-one candidate always yields 6 survivors — the same `GL₂(𝔽₂)` handle torsor
as at `h = 1` — and the defect map has corank `132 − 124 = 8` at `L₃`.  Together with the
`h = 1` corank of 6 this gives **corank = (number of generators) + 1** at every level
measured, i.e. `d + 1` for the rank-`d = 3 + 2h` core.

---

## 7.  Calibration reproductions

### 7.1  The dihedral controls (`calibration_dihedral.py`, pure Python — a second route)

`DihedralGroup n` implemented with mathlib's multiplication rules.  Anchors verified first:
`commP (sr 1) (sr 0) = r 2`, `sqWord (sr 0) 1 (r 1) = r 2`, `sqRelWord (refMark) = 1`
(`EichRefutation.lean` §2).

Counting **killing configurations** = homomorphisms `φ : D_sq 1 → D` (i.e. 5-tuples killing
the relator) for which *no* member of the family kills the relator:

**`D₄ = DihedralGroup 4` (order 8), all 16896 homomorphisms:**

| `(t,s)` | V-family `sqEichFrame` | T-family `sqEichFrameT` | two-letter `sqEichFrameUV` | **arbitrary** |
|---|---|---|---|---|
| (0,1) | **2688** | 0 | 0 | **0** |
| (1,0) | 0 | **2688** | 0 | **0** |
| (1,1) | **2688** | **2688** | 0 | **0** |
| (1,2) | 0 | **2688** | 0 | **0** |
| (2,1) | **2688** | 0 | 0 | **0** |
| (0,0) | 0 | 0 | 0 | **0** |

**`D₈ = DihedralGroup 8` (order 16), all 229376 *surjective* homomorphisms:**

| `(t,s)` | V-family | T-family | two-letter `UV` | **arbitrary** |
|---|---|---|---|---|
| (1,1) | 62208 | 61184 | **9728** | **0** |
| (0,1) | 57088 | 12288 | 6144 | **0** |
| (1,0) | 14336 | 57088 | 7168 | **0** |

This is exactly the committed pattern:

* the `V`-family dies on `D₄` at `ν′ = nuSel h j 0 1` (`refHom_sqRelWord_sqEichFrame`),
  the transposed `T`-family at `(1,0)`;
* the **two-letter** family survives every `D₄` probe and needs the **order-16** group —
  precisely UVFrames' "instead of killing a letter, identify the two", which is why
  `not_sqEichRelWordUV` is stated with the `D₈` witness at `ν′ = nuSel h j 1 1`;
* the **arbitrary family is killed by nothing, anywhere** — the discriminating control that
  `sqArbRelWord_iff_clearingStep` predicts.

⚠ The ticket's figure "16 killing configs on `DihedralGroup 8` at `(t,s)=(1,1)` for the
restricted family" does not match a raw hom count in any normalisation I could reconstruct
(9728 = 16 × 608 surjective homs; `|Aut(D₈)| = 32`, giving 304 orbits).  W45 evidently
counted a smaller parametrised object.  The **qualitative** control — nonzero for the
restricted family, exactly zero for the arbitrary one — reproduces, and that is what
validates the harness.

### 7.2  The W48 forced-alone dressing

`a₁ = U^{−s}V^{t}`, all other slots undressed, tested in the **full** class-3 quotient
`Q_3` (order 2^68) at all 63 uncleared `(t,s)` mod 8:

```
class-two   failures : 48 / 63       (exactly the (t,s) with t or s odd)
class-three failures : 60 / 63       (all but (0,4), (4,0), (4,4))
```

⚠ The number **60** coincides with the ticket's "0/60 failure" but the *sense* is opposite.
The reconciliation is §6.2: the class-two balance forces the `x₀`-slot dressing **and** an
equal `σ`-slot dressing; `a₁` alone is necessary, not sufficient.  W48's positive result is
about the *particular* class-three test group `SqU4(ℤ/8)` (order 2^18), one quotient among
many; `Q_3` is the universal one and is strictly stronger.  Both statements can hold at once,
and the sweep confirms `SqU4`'s closed forms exactly (§3(c)).

---

## 8.  The discrete-shadow probe

`w50_regime.m` runs the same lift with the set of **dressable slots** restricted at level one
and at every deeper level alike.  Both runs use the same 63 markings, `t,s ∈ [0..7]`:

| regime | dressable slots | class 3: solvable / INFEASIBLE | class 4: solvable / INFEASIBLE | level-one gate |
|---|---|---|---|---|
| `handle` — the discrete/SL₂ regime | u, v | 3 / **60** | **0 / 63** | *empty* at 48 markings |
| `core` | σ, x₀, x₁ | 3 / **60** | **0 / 63** | 1 survivor always |
| `sigmax0` | σ, x₀ | 3 / **60** | **0 / 63** | 1 survivor always |
| `x0` | x₀ | 3 / **60** | **0 / 63** | empty at 48, 1 at 15 |
| **`full`** = `SqArbRelWord` | all five | **63 / 0** | **63 / 0** | 6 survivors always |

The three markings solvable in a restricted regime at class 3 are `(0,4), (4,0), (4,4)` — the
rows already in the deepest layer *at that class*.  At class 4 the rows are read mod 16, they
are no longer deepest, and **every** restricted regime fails at **every** marking.

Per-slot anatomy of the defect at the full regime, marking `(t,s)=(1,1)`:

| level | target dim | domain dim per slot | per-slot ranks (σ, x₀, x₁, u, v) | joint |
|---|---|---|---|---|
| L₃ | 49 | 12 | 12, 12, 12, 11, 11 | 43 |
| L₄ | 175 | 47 | 47, 47, 47, 46, 46 | 169 |

The three core slots inject; each handle slot loses exactly one dimension; no single slot
reaches beyond its own domain dimension, so the joint rank is genuinely joint.

**Reading.**  The obstruction that kills the discrete case is *visible*: with the handle pair
alone — the mapping-class / SL₂ regime — the system is infeasible at 60 of 63 markings at
class 3 and at **all 63** at class 4, and at 48 of them the class-two gate is literally empty
(an exhaustive, certificate-grade negative).  The escape is **not** an enlargement of the
handle action: it is the pivot-mixing
core dressing `U^{−s}V^{t}` on the σ- and x₀-slots, which has no discrete counterpart because
it moves core letters by handle-derived elements.  And neither block suffices alone: the
core-only regime passes level one (with the forced dressing) but fails the class-three linear
solve at the same 60 markings.  **The pro-2 escape is an irreducibly joint core + handle
move.**

**Transitivity (the question the W50-SELECT sibling needs).**  A solvable verdict at `(t,s)`
*is* an automorphism `ψ` of `Q_c` with `λ∘ψ = λ` and `ν′∘ψ = ν_sq`.  Since every uncleared
marking is solvable, the λ-preserving subgroup of `Aut(Q_c)` acts **transitively** on the set
of selected ν′-rows, carrying every `(t,s)` to `(0,0)`.  So:

> **The SL₂-invariant leaves no shadow on the ν′-row orbit at class 3, 4 or 5.  The pro-2
> automorphism group already acts transitively there.**  The shadow survives only as a
> constraint on *which dressings* realise the transitivity — the forced core dressing and
> the `GL₂(𝔽₂)` handle torsor of §6.2 — not as an invariant of the orbit.

Any Lean-side argument must therefore put its pro-2 input into the *existence of the
core-mixing automorphism*, not into a row-orbit computation: the row orbit is already full at
every finite class the sweep can reach.

### 8.1  What this hands to W50-SELECT

Concretely, three things the Lean side can take as measured facts about the finite quotients
(none of them is a proof about `D_sq 1`, all of them are constraints any proof must respect):

1. **Do not look for a row invariant.**  At class 3, 4 and 5 the λ-preserving automorphisms
   already move every selected ν′-row onto `ν_sq`.  A Lean argument shaped as "the SL₂
   invariant obstructs / does not obstruct the ν′-row" cannot be the whole story: at finite
   class there is nothing left to obstruct.
2. **The shape of the witness is essentially forced, and it is known.**  The class-two
   balance pins the σ- and x₀-slot dressings to `U^{−s}V^{t}` and the x₁-slot to the trivial
   class; the only level-one freedom is `GL₂(𝔽₂)` on the handle pair, and the sweep never
   needs it — the identity works at all 255 class-4 markings.  A constructive Lean witness
   should start from `a₀ = a₁ = U^{−s}V^{t}`, `a₂ = a₃ = a₄ = 1`, with the remaining
   corrections in `K ∩ [G,G]G²`-depth.  ⭐ Note that this is `GradedTwo` §6's forced `a₁`
   **plus the same dressing on the σ-slot** — the σ-slot condition is not in the Lean
   corpus and is, on this evidence, part of the correct ansatz.
3. **The hard content is a joint core+handle statement.**  Restricting the dressings to
   either block alone is infeasible at every marking at class 4.  Any decomposition of the
   residual that treats the core moves and the handle moves separately will not close.

---

## 9.  Limitations — what was exhausted and what was sampled

* **Exhausted.**  Class 3 and class 4: every uncleared selected marking, `(t,s)` mod `2^c`.
  Stage A (the level-one / class-two gate) at every marking and every class: all `8^5` codes.
  The dihedral calibration: all homomorphisms to `D₄`, all surjective ones to `D₈`.
* **Sampled.**  Class 5: 103 of 1023 uncleared markings (§6.1).  The sample is
  valuation-stratified, not random; the uniformity of the level-one survivor set (always 6,
  depending on `(t,s)` only mod 4) and of the rank table (always 43/49, 169/175, 673/679)
  across all 421 markings computed makes an outlier among the remaining 920 unlikely but
  **not excluded**.
* **`h = 2` (the optional spot-check) — done, see §6.4**, but at a reduced marking sample at
  class 4.
* **Not attempted.**  Class 6.  `dim L₆` for this group is several thousand; the layer-basis
  and defect-matrix steps scale, but the `K ∩ P_j` intersections at order `2^{4000+}` do not
  within this budget.
* **Greedy completeness.**  §5.4: negative verdicts from the *restricted-regime* probe are
  greedy, except the 48 empty-gate cases which are exact.  This does not touch the headline,
  which is entirely positive.
* **What a positive verdict is worth.**  Nothing about `D_sq 1` itself.  A class-`c`
  certificate says the class-`c` quotient admits the clearing automorphism; the residual
  needs it in the inverse limit.  The value of the sweep is the *absence* of a refutation at
  a depth where one was plausibly expected, plus the structure in §6.2–§6.3 and §8.

---

## 10.  Reproduction

Budget, measured on this machine (16 cores, several jobs sharing it): Stage-A cache ~3 s;
class 3 whole sweep < 1 min; class 4 whole sweep ~15 min; class 5 ~70 s **per marking** (the
`pQuotient` itself takes 150 s and `K meet P_j` about 6 s per level); `h = 2` class 4 ~30 s
per marking; the `D₈` calibration ~20 min in pure Python.

Run everything with `scripts/w50_depth_sweep` as the working directory — the Magma scripts
`load "c0.m"` by relative path, and they write their output with `PrintFile` to the name
given by the `out:=` parameter.  `c0.m` is regenerated by
`python3 padic_c0.py --magma > c0.m` (it is committed so that a Magma-only reproduction needs
no Python); plain `python3 padic_c0.py` prints the committed anchors instead.

```
scripts/w50_depth_sweep/
  padic_c0.py               the 2-adic constants X, S, Y, c0;  python3 padic_c0.py
  c0.m                      C0 := sqPivotExp mod 2^64 (generated by the above)
  sizes2.m                  the quotient tower           magma -b cmax:=5 sizes2.m
  w50_sweep.m               main sweep, exhaustive       magma -b cls:=4 out:=res_c4.txt w50_sweep.m
  w50_sweep2.m              main sweep, sampled          magma -b cls:=5 mode:=sample out:=res_c5.txt w50_sweep2.m
                            (mode = full | sample | tail)
  w50_regime.m              discrete-shadow probe        magma -b cls:=4 out:=reg_c4.txt w50_regime.m
  w50_coker.m               cokernel anatomy             magma -b cls:=4 out:=coker_c4.txt w50_coker.m
  w50_h2.m                  the h = 2 spot-check         magma -b cls:=3 out:=h2_c3.txt w50_h2.m
                            (optional tmax:=4 to shrink the marking grid)
  survivors.m               survivor structure + the W48 forced-alone run
  indep_class2.py           independent class-two model (no group-theory library at all)
  graded_crosscheck.py      cross-validations (b) and (c)
  calibration_dihedral.py   the D4 / D8 controls
  results/                  every output file quoted above
```
