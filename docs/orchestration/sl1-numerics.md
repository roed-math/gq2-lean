# SL1-N — numerics: the uniform SL1 mechanism (2026-07-26)

Ticket SL1-N of the SL-campaign (`sl-campaign-plan.md` §2).  Numerics only — no Lean was
touched.  Harness: `docs/orchestration/harness-sl1/sl1_climb.py` (core) and
`sl1_report.py` (all experiments), built on the spike's `span_model.py` /
`sl1_hunt*.py`.  Python 3, no dependencies.

## 0. Verdict

| deliverable | status |
|---|---|
| 1. greedy triple refinement, climb `k = 3 → 5` | **DONE**, and pushed to `k = 6`; never stalls, all clauses verified at every level, both directions, both `S^P_3` mod-2 classes |
| 2. functional pattern at `k = 4, 5`, both directions | **CONFIRMED** for direction 1 exactly as conjectured; direction 2 is the mirror with a *different ad-direction letter* — see §3, this is the one place where the naive reading of the conjecture is wrong |
| 3. the `φ(δ)`-pinning identity | **FOUND, and it is not a sum — it is a TRANSPOSITION**: `δ(T) = e_q·T_p^{2^{k-1}} + e_p·T_q^{2^{k-1}}` in the coker.  §4 |
| 4. `P`-violating controls at `k = 4` (and 5) | **DONE** — all four fresh-digit patterns installed on demand; `δ ∉ span` in every non-zero case |
| 5. report | this file |
| bonus | the two functionals have a **closed form as θ-crossed derivations** (§6) — a `ContinuousMonoidHom`-free, Lyndon-basis-free definition that is almost certainly what L should formalize |

Head-line numbers: **0 mismatches** in 536 + 712 independently sampled triples
(§4.3, §4.4), **0 stalls** in the climb, and the spike's k = 3 dichotomy reproduced
exhaustively over all 168 mod-2 classes in both directions.

## 1. Model and calibration

Everything is computed in the free pro-2 group `F₃` on the **tower letters** via truncated
Magnus expansion mod `2^K` (`K = k + 6`), with `Z_j(F)` coordinates
`bit_w(v) = (coeff_w(μ v) / 2^{j-|w|}) mod 2` for `|w| ≤ j`, and
`Z_k(D) = Z_k(F)/R_k`, `R_k` = the span of the level-`k` layer of the **presenting**
relator.  `δ(T)` = the class of the **tested** relator word at `T`, after an explicit
descent correction by relator atoms at levels `2 … k−1`.

| | direction 1 | direction 2 |
|---|---|---|
| tower | `D_R = F(s,x,y)/N(drWord)` | `D₀ = F(a,s,y)/N(d0Word)` |
| presenting relator | `r₂ = (x^s)⁻¹x⁻³y²[y,y^s]` | `r₀ = a²s⁴[s,y]` |
| tested relator | `d0Word(T) = T₀²T₁⁴[T₁,T₂]` | `drWord(T)` |
| `d̄` | `dbarWordR0 = w₀²[w₀,T₀][w₁,T₂][w₂,T₁]` | `dbarWordR2 = w₂²[w₂,T₂][w₀,T₁][w₁,T₀]` |
| χ-targets | `(−1, 1, η)` | `(S, X, Y)` |
| tail slots `(p,q)` | `(1, 2)` | `(0, 1)` |
| "automatic" slot | `0` | `2` |

Calibration (`sl1_report.py calib`), matching spike §2.3 exactly:

| dir | k | `N_k` | `rk R_k` | `dim Z_k(D)` | spike | `rk(R_k + Im d̄)` | coker | tails add |
|---|---|---|---|---|---|---|---|---|
| 1 | 3 | 14 | 4 | 10 | 10 | 12 | 2 | 2 |
| 1 | 4 | 32 | 12 | 20 | 20 | 30 | 2 | 2 |
| 1 | 5 | 80 | 36 | 44 | 44 | 78 | 2 | 2 |
| 2 | 3 | 14 | 4 | 10 | 10 | 12 | 2 | 2 |
| 2 | 4 | 32 | 12 | 20 | 20 | 30 | 2 | 2 |
| 2 | 5 | 80 | 36 | 44 | 44 | 78 | 2 | 2 |

`d̄` is exactly `𝔽₂`-linear in the modification in these coordinates (0 mismatches in 144
randomized additivity checks), so the linear model is faithful.

### 1.1 The mod-2 seed census (all 168 classes, both directions)

`sl1_report.py census`.  Both clauses (relator kill in `Q₃`, χ mod 8) depend only on the
mod-2 class, so this is exhaustive.  In each direction exactly **6** of the 168 classes
kill the relator and exactly **2** of those satisfy `P` — the spike's census, reproduced.

* dir 1 good classes: `T = (y, s·x, s)` and `T = (y, s·x, x)`;
* dir 2 good classes: `T = (y, s·y, a)` and `T = (s·y, y, a)`.

**A structural fact that falls out and that the Lean proof needs** (§4.5): in *all* 12
relator-killing classes the mod-2 abelianization coefficient of the ad-direction letter
`c` (dir 1: `y`; dir 2: `a`) satisfies

    ab_c(T_i) = 1 if i = the automatic slot, 0 otherwise.

Since a triple in `S⁰_k` restricts to a relator-killing generating triple in `Q₃`, this
holds at **every** level `k ≥ 3` and the k = 3 census is a complete proof of it.

## 2. The greedy level climb (deliverable 1)

`climb` in `sl1_climb.py`.  Given `T ∈ S^P_k` as free words:

1. **SL1 solve.**  Solve `d̄_T(w) = δ(T)` in `Z_k(D)` for a `λ_{k-1}`-modification `w`
   (`Solver` tracks the combination, so `w` is recovered slotwise).  Set `T ← T·w`;
   the shift formula then kills the relator in `Q_{k+1}` (verified each time).
2. **SL2 digit fix.**  Compute the two fresh χ-digits at `2^k` and cancel them with the
   memo §1.2 witness moves (powers of the *current* triple words, so their `d̄` is `1`
   definitionally).  Verified: `d̄(move) = 0` exactly, at every level, both directions.
3. **Verify** generation, relator kill in `Q_{k+1}`, χ mod `2^{k+1}`, Frattini class
   preserved.

Results — **no stalls anywhere**:

| dir/class | seed | 3→4 | 4→5 | 5→6 |
|---|---|---|---|---|
| 1 / A | `(y, sx, s)` | digits after solve `[0,0,0]`, moves `(0,0)`, lens `[5,6,3]` | `[0,0,0]`, `(0,0)`, `[21,14,23]` | lens `[101,1722,1729]` |
| 1 / B | `(y, sx, x)` | `[0,1,1]`, `(0,1)`, `[5,32,33]` | `[0,1,0]`, `(1,0)`, `[9,236,45]` | — |
| 2 / A | `(y, sy, a)` | `[1,0,0]`, `(1,0)`, `[17,6,3]` | `[1,0,0]`, `(1,0)`, `[119,16,7]` | lens `[985,2084,153]` |
| 2 / B | `(sy, y, a)` | `[1,0,0]`, `(1,0)`, `[20,5,5]` | `[1,0,0]`, `(1,0)`, `[96,9,15]` | — |

Two facts worth recording for L4a/SL2:

* **the automatic digit is automatic**: after the SL1 solve, the fresh χ-digit of the
  automatic slot (dir 1: slot 0; dir 2: slot 2) was `0` in *every* climb and in every one
  of the 1200+ sampled triples.  This is memo §1.1's mechanism, and it is what makes the
  two-dimensional coker match the two free digits.
* **the memo §1.2 move effects are exactly as designed**, at every level `k = 3,4,5`:
  dir 1 `(0,1,0)` and `(0,1,1)`; dir 2 `(1,0,0)` and `(0,1,0)`; and `d̄(move) = 0`
  *exactly* (not merely modulo something), so the moves never disturb step 1.

## 3. The coker functionals (deliverable 2)

For a Lyndon word `l`, write `π^m·[l]` for the PBW basis element
`bracketing(l)^{2^{k-|l|}}` of `Z_k(F)`.  Define the **column**

    col(z; ad c)  =  { π^{k-1-m} (ad c)^m (z)  :  m = 0 … k−1 }   ⊂  PBW-dual basis.

**Verdict: the conjectured pattern is confirmed, with the ad-direction identified.**
At every `k = 3, 4, 5` (and `k = 6`, spot-checked), for both `S^P` mod-2 classes and in
both directions, the annihilator of `R_k + Im d̄_T` in the PBW-dual basis is exactly

    ⟨ col(z₁; ad c),  col(z₂; ad c) ⟩,

where **`c` = the squared generator of the tower's own presenting relator** and
`{z₁,z₂}` = the other two tower letters:

| direction | tower | presenting relator | ad-direction `c` | roots `{z₁,z₂}` |
|---|---|---|---|---|
| 1 | `D_R` | `r₂`, squared letter `y` | `y` | `{s, x}` |
| 2 | `D₀` | `r₀`, squared letter `a` | `a` | `{s, y}` |

Explicit supports (`sl1_report.py funs`):

* dir 1, `k = 5`: `col(s; ad y) = {π⁴s, π³[s,y], π²[[s,y],y], π[[[s,y],y],y], [[[[s,y],y],y],y]}`
  and the same with `x`.  Lyndon words `z y^m`, **left**-nested brackets.
* dir 2, `k = 5`: `col(s; ad a) = {π⁴s, π³[a,s], π²[a,[a,s]], π[a,[a,[a,s]]], [a,[a,[a,[a,s]]]]}`
  and the same with `y`.  Lyndon words `a^m z`, **right**-nested brackets.

**The direction-2 asymmetry (documented as requested).**  The ticket's hypothesis reads
"`(ad y)^m(z)`, `z ∈ {s,x}`".  That is right in direction 1.  In direction 2 the letter
called `y` is a **root**, not the ad-direction: the ad-direction is `a`.  The invariant
statement is the relator one above.  A second, purely notational consequence: because
`a < s, y` while `s, x < y`, the Lyndon normal forms and the bracket nestings are mirrored
(`a^m z` right-nested vs `z y^m` left-nested).  Same Lie elements `(ad c)^m(z)` up to sign
(irrelevant in char 2), different PBW words — anyone matching this against the repo's
basis conventions must not assume the direction-1 shape.

**The columns are `T`-independent** (this is the important structural point): the same two
subsets of the PBW-dual basis annihilate `R_k + Im d̄_T` for *every* relator-killing
generating triple — including all four `P`-violating classes at `k = 3` and all 700+
sampled deviation triples.  Their pairing with the tails is

    φ^z( T_i^{2^{k-1}} )  =  ab_z(T_i)         (the mod-2 abelianization coefficient),

verified on every sample.  So the "column-vs-tail" transition matrix is the `2×2`
sub-matrix of the triple's mod-2 abelianization on (root letters) × (tail slots); it is
invertible precisely because `T` generates and `ab_c(T_i) = [i = auto]` (§1.1).

## 4. The pinning identity (deliverable 3)

### 4.1 Setting

Let `T` be a generating triple killing the tested relator in `Q_k` (i.e. `T ∈ S⁰_k`,
`k ≥ 3`).  Every such `T` has χ̂-depth `≥ k−1` (asserted on every sample; spike §2.4), so

    χ(T_i) · target_i⁻¹  ≡  1 + 2^{k-1}·e_i   (mod 2^k),      e_i ∈ 𝔽₂

is well defined, and `T ∈ S^P_k ⟺ e = 0`.  Write `(p,q)` for the tail slots and
`t_i = T_i^{2^{k-1}}` for the tails.

### 4.2 The identity

    **e_auto = 0 always**, and in `Z_k(D) / Im d̄_T`:

        δ(T)  =  t_p^{e_q} · t_q^{e_p}.

That is: **the coker coordinates of the defect are the two top χ-deviation digits, with
the slots TRANSPOSED.**  Equivalently, in the canonical (T-independent) functionals,

    φ^z( δ(T) )  =  e_p·ab_z(T_q)  +  e_q·ab_z(T_p)      for each root z.       (*)

This is the regression asked for.  It is not `φ₀ = e₀+e₁`-style: the map
`(e_p,e_q) ↦ (coeff of t_p, coeff of t_q)` is the **swap** matrix `[[0,1],[1,0]]`, which is
invertible — that is exactly *why* the spike's dichotomy is sharp:

    δ(T) ∈ Im d̄_T + R_k  ⟺  e_p = e_q = 0  ⟺  T ∈ S^P_k        (given e_auto = 0).

### 4.3 Evidence — controlled installs

`sl1_report.py regress`.  Climbing from level `k` with a prescribed fresh-digit pattern
`want` produces level-`(k+1)` triples realizing every `e`.  All 32 installs
(2 directions × 2 classes × {3→4, 4→5} × 4 patterns) satisfy (*):

| dir | e (installed) | `φ_cols(δ)` class A | class B | coker coords `(c_p,c_q)` | cross prediction |
|---|---|---|---|---|---|
| 1 | `(0,0,0)` | `(0,0)` | `(0,0)` | `(0,0)` | `(0,0)` ✓ |
| 1 | `(0,0,1)` | `(1,1)` | `(1,1)` | `(1,0)` | `(e₂,e₁) = (1,0)` ✓ |
| 1 | `(0,1,0)` | `(1,0)` | `(0,1)` | `(0,1)` | `(0,1)` ✓ |
| 1 | `(0,1,1)` | `(0,1)` | `(1,0)` | `(1,1)` | `(1,1)` ✓ |
| 2 | `(0,0,0)` | `(0,0)` | `(0,0)` | `(0,0)` | `(0,0)` ✓ |
| 2 | `(0,1,0)` | `(0,1)` | `(1,1)` | `(1,0)` | `(e₁,e₀) = (1,0)` ✓ |
| 2 | `(1,0,0)` | `(1,1)` | `(0,1)` | `(0,1)` | `(0,1)` ✓ |
| 2 | `(1,1,0)` | `(1,0)` | `(1,0)` | `(1,1)` | `(1,1)` ✓ |

(The raw `φ_cols` values differ between the two mod-2 classes — they are read through
that class's abelianization — while the **coker coordinates are class-independent**.  This
is why the identity must be stated in the tail basis, or in the form (*), and not as a
fixed pair of bits.)

### 4.4 Evidence — broad sampling

`sl1_report.py sample` (712 triples) and an independent earlier run of the same design
(624 triples), plus the explicit-formula checker (536 triples): **0 mismatches**, every
triple also passing the `e_auto = 0` and dichotomy assertions.  Families sampled at
`k = 3, 4, 5`, both directions, both classes:

* **`S^P_k`-orbit** — random `λ_{k-1}`-moves.  These preserve all three clauses
  (`sPR*_mul_mem`), verified for every sample; `φ(δ) = 0` and `δ ∈ span` throughout.
* **alternative SL1 solutions** — the climb re-run with a random element of
  `ker d̄` added to the solved modification (kernel dim 10 at `k = 4`, 28 at `k = 5`).
  Every alternative refinement again lands in `S^P_{k+1}`, with `φ(δ) = 0`.
* **mid-depth deviation moves** — `λ_{k-2}`-modifications lying in the kernel of the
  level-`(k−1)` `d̄` (so the relator clause survives at level `k`) but moving the top
  χ-digit.  These realize all four `(e_p,e_q)` patterns and all satisfy (*).

e-patterns realized by the `sample` families (counts summed over the two mod-2 classes;
`k = 3` has no deviation family, since `λ_{k-2} = λ₁` is outside the calculus — the `k = 3`
deviation data is the exhaustive census of §1.1 instead).  `e_auto = 1` **never** occurred
in any of the ~1900 triples examined:

| dir | k | `(0,0,0)` | other patterns |
|---|---|---|---|
| 1 | 3 | 52 | — (census supplies `(0,1,0)`, `(0,1,1)`) |
| 1 | 4 | 112 | `(0,0,1)` 14, `(0,1,0)` 10, `(0,1,1)` 16 |
| 1 | 5 | 111 | `(0,0,1)` 17, `(0,1,0)` 13, `(0,1,1)` 11 |
| 2 | 3 | 52 | — (census supplies `(0,1,0)`, `(1,0,0)`) |
| 2 | 4 | 110 | `(0,1,0)` 10, `(1,0,0)` 12, `(1,1,0)` 20 |
| 2 | 5 | 116 | `(0,1,0)` 10, `(1,0,0)` 11, `(1,1,0)` 15 |

### 4.5 The Lean skeleton this licenses

1. span theorem (already frozen): `Z_k(D) = Im d̄_T + ⟨t_p, t_q⟩`, so
   `δ(T) = d̄_T(w)·t_p^α·t_q^β` for some `α,β ∈ 𝔽₂`;
2. apply `φ^{z₁}, φ^{z₂}` (which kill `Im d̄_T` and `R_k`):
   `φ^z(δ) = α·ab_z(T_p) + β·ab_z(T_q)`;
3. the matrix `[ab_z(T_i)]` (roots × tail slots) is invertible over `𝔽₂` — from generation
   plus `ab_c(T_i) = [i = auto]` (§1.1, exhaustive at k = 3 hence at all `k`);
4. hence `(α,β)` is determined by `(φ^{z₁}(δ), φ^{z₂}(δ))`;
5. **the one analytic input**: `T ∈ S^P_k ⟹ φ^z(δ(T)) = 0` (the `e = 0` case of (*));
6. therefore `α = β = 0`, i.e. `δ(T) ∈ Im d̄_T` — SL1.

Step 5 is the whole content, and §6 gives the shape in which to attack it.

## 5. Controls (deliverable 4)

`P`-violating-but-relator-deep triples at `k = 4` and `k = 5` are produced on demand by
climbing with a **wrong digit fix** (`want ≠ (0,0)` in `climb`), i.e. by choosing the
digit-move combination that installs a `1`.  Each such `T'`:

* generates and kills the tested relator in `Q_{k+1}` (verified),
* has χ̂-depth exactly `k` (not `k+1`),
* has `δ(T') ∉ R_{k+1} + Im d̄_{T'}` — the SL1 solve **fails**, exactly as the spike's
  census predicts, and the failure is measured by (*).

The `k = 3` exhaustive census (§1.1) is the sharpest control: 4 `P`-violating classes per
direction, all with `δ ∉ span`, all matching (*) — table in `sl1_report.py census`.

## 6. Closed form: the functionals are θ-crossed derivations (bonus)

The columns are not just Lyndon-dual bookkeeping.  Fix the ad-direction letter `c` and a
root `z`, and define on the free group

    θ : F₃ → ℤ₂ˣ,  θ(c) = −1,  θ(other letters) = 1,
    D_z : F₃ → ℤ₂,  D_z(z) = 1,  D_z(other letters) = 0,
                    D_z(u·v) = D_z(u)·θ(v) + D_z(v)      (a θ-crossed hom / twisted Fox
                                                           derivative, ξ_z on the left).

Then, verified on the whole PBW basis at `k = 3, 4, 5` in both directions, and on every
`δ`, relator atom, `d̄`-atom and tail encountered:

    **φ^z(v)  =  the (k−1)-st 2-adic digit of D_z(v)**,    for `v ∈ λ_k`.

Facts making this attractive to formalize:

* `D_z(v) ≡ 0 mod 2^{k-1}` for `v ∈ λ_k` (holds on every sample; it is the filtration
  bound `2^{k-|w|}·2^{|w|-1}`), so the digit is defined;
* **θ kills both presenting relators** (each has exponent 2 in its squared letter:
  `θ(r₀) = (−1)²·1⁴ = 1`, `θ(r₂) = 1⁻⁴·(−1)² = 1`), so θ descends to the towers;
* `D_z(r) = ±4` for the presenting relator `r` (dir 1, `z = s`: `4`; `z = x`: `−4`;
  dir 2, `z = s`: `4`; `z = y`: `0`).  Together with the step rules
  `D(u²) = D(u)(θ(u)+1)` and `D([u,g]) = D(u)(θ(g)−1)`, every level-`j` relator atom has
  `D` divisible by `2^j`; at `j = k` that kills `R_k` at the digit — an elementary
  replacement for the "Magnus-ideal valuation statement" the plan hoped for;
* the same two rules kill `Im d̄_T` **exactly** (not just at the digit) once
  `θ(T_auto) = −1` and `θ(T_p) = θ(T_q) = +1`, which is precisely §1.1's census fact:
  the `w₀²[w₀,T_auto]` atom gives `2D(w₀) + D(w₀)(θ(T_auto)−1) = 0` and the two cross
  atoms give `D(w)(θ(T_i)−1) = 0`;
* any `θ(c)` with `v₂(θ(c)−1) = 1` gives the same functional (`tval = 3` and `tval = −1`
  both verified), so the choice `−1` costs nothing;
* closed form on the tested relator word (exact, verified on every sample):
  dir 1 `D_z(d0Word(T)) = 4·D_z(T₁)`; dir 2 `D_z(drWord(T)) = 4·(D_z(T₀) − D_z(T₁))`.

## 7. Why the identity is crossed

The `2^{k-2}`-power SL2 witnesses of memo §1.2, taken **one power lower** (`2^{k-3}`), are
`λ_{k-2}`-modifications that (i) still kill their own `d̄`-bracket, (ii) flip a *top* χ
digit `e_i`, and (iii) shift `δ` by exactly the crossed tail.  Verified at `k = 4, 5`,
both directions, both classes (`sl1_report.py witness`):

| direction | move | `e` | `δ` picks up |
|---|---|---|---|
| 1 | slot 1 `←` `T₂^{2^{k-3}}` | `(0,1,0)` | `t_2` |
| 1 | slots 1,2 `←` `(T₁T₂)^{2^{k-3}}` | `(0,1,1)` | `t_1·t_2` |
| 2 | slot 0 `←` `T₁^{2^{k-3}}` | `(1,0,0)` | `t_1` |
| 2 | slot 1 `←` `T₀^{2^{k-3}}` | `(0,1,0)` | `t_0` |

The mechanism, in one line: the modification is a `2^{k-3}`-power **of another slot's
word** (it has to be — only a slot whose χ-target `τ` has `v₂(τ−1) = 2` can move the top
digit), and the relator's `±4` exponent at the modified slot turns that `2^{k-3}`-power
into a `2^{k-1}`-power — i.e. into the *other* slot's tail.  For dir 1: `(T₁v)⁴ ⊇ v⁴ =
T₂^{2^{k-1}}`; for dir 2: `(x^s)⁻¹x⁻³ ⊇ v⁻⁴ = T₀^{2^{k-1}}`.  (The remaining dir-2 case,
slot 0 modified by a `T₁`-power, has vanishing first-order shift and picks its tail up
from the conjugation terms; verified numerically, not derived here.)

## 8. Surprises, caveats, traps

1. **The identity is a transposition, not a sum.**  Anyone guessing
   `φ_i(δ) = e_i` will get a consistent-looking picture at `k = 3` in direction 1 (see
   trap 3) and then fail.
2. **Direction 2's ad-direction is `a`, not `y`** (§3).  The invariant is "the presenting
   relator's squared letter".
3. **`k = 3`, direction 1, is degenerate for regression purposes**: only three of the four
   `(e_p,e_q)` patterns occur among the 168 mod-2 classes — `(e₁,e₂) = (0,1)` is not
   realized — so the k = 3 census alone does *not* determine the map.  It was the `k = 4`
   controlled installs that pinned it.  (Direction 2 at `k = 3` also realizes only three.)
4. **The descent correction is not cosmetic**: `φ^z(δ(T))` must be evaluated on the
   *corrected* representative in `λ_k(F)`.  Applying `D_z` to the raw relator word at `T`
   gives a different digit in roughly half the samples (the level-`(k−1)` relator atoms
   used in the correction have `D` divisible by exactly `2^{k-1}`).  In Lean this is the
   free-preimage/`span_descent` step, not an extra hypothesis — but a harness that skips
   it will produce wrong bits.
5. **`e_auto = 0` is load-bearing and empirically exceptionless** (~1900 triples).  It is
   memo §1.1's argument one level down: relator kill in `Q_k` forces
   `χ(T_auto)²·χ(T_other)^{±4} ∈ 1 + 2^kℤ₂`, hence `e_auto ≡ 0`.  Without it the coker
   (dimension 2) could not separate three free digits.
6. **`Im d̄_T` and the tails depend on `T` only through its mod-2 (Frattini) class**, and
   the climb preserves that class — so the entire functional picture is fixed along a
   climb.  Only `δ` moves.
7. `sl1_fun.py` (the earlier harness) crashes in its crossed-`D` section with
   `StopIteration` at `unit_i = next(...)`: the Fox row of the presenting relator has no
   odd entry.  Left as-is (not owned by this ticket); the functional half of that file is
   correct and its `k = 3` output is reproduced here.

## 9. Reproduction

```
cd docs/orchestration/harness-sl1
python3 sl1_report.py calib      # tower dims, additivity, SL2 move effects      (~3 s)
python3 sl1_report.py census     # the 168-class k=3 census + pinning table      (<1 s)
python3 sl1_report.py funs       # coker functionals at k=3..5, both directions  (~8 s)
python3 sl1_report.py cross      # the theta-crossed-derivation closed form      (~1 s)
python3 sl1_report.py regress    # the four controlled digit installs            (~30 s)
python3 sl1_report.py witness    # the 2^{k-3} deviation witnesses               (~8 s)
python3 sl1_report.py sample     # 712 sampled triples, all identity checks      (~9 min)
python3 sl1_report.py all 5      # everything
```

`sl1_climb.py` holds the model (`Ctx`), the climb (`climb`), the seed census
(`seed_census`, `good_seeds`), the modification-kernel machinery (`move_kernel`), the
canonical functionals (`column`, `coker_coords`, `roots_and_addir`) and the closed form
(`theta_D`, `crossed_digit`).  `k = 6` runs work (`sl1_report.py funs 6`, a few minutes)
and were used for the §3 spot-check.
