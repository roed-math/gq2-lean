# W81-NORMS: the four norm-character values, and the pivot at `ℚ₂(√10)`

Lane W81-NORMS, the last selector arithmetic at the two procyclic fields.  Produced against tree
`6f2916f3` on branch `claude/w81-norms`, shared cache at the wave-80 umbrella (4358 jobs).
Verification of record: `scripts/mirror.sh` (sweep, gen, check).  **No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/MpcNormValues.lean`, declaration prefix `mpcNorm`
(namespace `GQ2.Dyadic.Instances.MpcNorm`).  Nothing else was touched; the module is **not yet
registered in `GQ2.lean`** (housekeeping owns that).

---

## 1.  The headline

**All four values land, they agree with the frozen rows, and the pivot lands at `ℚ₂(√10)`.**

> The `ε = false` row is now a branch datum **over the bundles alone**:
> `mpcNorm_genAsmBranch_sqrtTen` carries no clause at all.  The `ε = true` row carries exactly
> one, the pivot, and §5 below shows the obstruction is real rather than a gap in the argument.

Three further things fell out:

* **`B.r = 1` is unconditional at both procyclic fields** (`mpcNorm_level_sqrt{Ten,NegTen}`),
  which closes the first of wave 78 §2.3's two claims in full.
* **The freeness of `ℤ₂ˣ` as `⟨−1⟩ × (mUnit 2)^{ℤ₂}`** (T1) is a theorem, in the uniqueness form
  the pivot consumes, and it is four short lemmas over the tree's own `zpowZtwo` calculus.
* **The lane uses no Hilbert symbol.**  `hilbertSymbol_normCriterion_finiteDyadic` does not occur
  in the axiom set of any of the four values, of the level, of the freeness, or of the abstract
  pivot criterion.  Wave 80 §4.2's prediction ("the lane that closes this does not need a symbol
  calculator at all") is confirmed.

## 2.  The four values, checked against the hand computation

The predecessor's four hand-computed targets were relayed as
`(2,±10)₂ = −1`, `(−2,10)₂ = −1` versus `(−2,−10)₂ = +1` with `(−1,−10)₂ = −1`, and
`(5,±10)₂ = −1`.  **Every one of them is confirmed by the formalization**, and the formalization
derives them independently: it never reads a symbol, it computes the norm group directly.

| landed name | field | selector reading | frozen row wants |
| --- | --- | --- | --- |
| `mpcNorm_noUnitKerChi_sqrtTen` | `ℚ₂(√10)` | `2` is not a norm | `r = 1` ✓ |
| `mpcNorm_lambdaOne_negOne_sqrtTen` | `ℚ₂(√10)` | `λ(−1) = 0` | `p false 1 = 0` ✓ |
| `mpcNorm_noUnitKerChi_sqrtNegTen` | `ℚ₂(√−10)` | `2` is not a norm | `r = 1` ✓ |
| `mpcNorm_lambdaOne_negOne_sqrtNegTen` | `ℚ₂(√−10)` | `λ(−1) = 1` | `p true 1 = 1` ✓ |
| `mpcNorm_lambdaOne_mUnit_sqrtNegTen` | `ℚ₂(√−10)` | `λ(5) = 1` | `η = .one` ✓ |

**No disagreement was found**, at any of the four values or against `Main.lean:122-138`
(`.Mpc 2 1 false 1` and `.Mpc 2 1 true 1`).  The parity inversion between the two fields is
localized precisely: it is `mpcNorm_residue_negFive` versus `mpcNorm_residue_five`, the unit part
of `N(√a) = −a` being `≡ 3 (mod 8)` at `a = 10` and `≡ 5 (mod 8)` at `a = −10`.

## 3.  How the arithmetic runs (T2)

Wave 80 §4.2's four-step chain, taken in order, plus one step it did not name.

### 3.1  The value group (step 3), landed

`mpcNorm_exists_decomp`: at `K = ℚ₂(√a)` with `v(a)` odd and `‖a‖ = ‖2‖`, every `x : Kˣ` is
`u·(√a)^n` with `‖u‖ = 1` and `n : ℤ`.  The exponent is read off the `x = t + s√a` representation
through `Fields.lean` §4's separation lemma, so no valuation on `K` is constructed; the analogue
one field down is `MarkedRecipBundle.exists_bot_decomp` with `2` in place of `√a`.

### 3.2  The norm form (step 4), landed

`mpcNorm_repr_of_norm_one`: a **spectral** unit is `t + s√a` with `‖t‖ = 1` and `‖s‖ ≤ 1`, the
integrality of `s` coming from `fieldUni_norm_le_one_of_mul_sqrtIn_lt_one` (the value group of
`ℚ₂` is coarser than `K`'s), not from an assumption.  Then `mpcNorm_norm_quadElt` gives
`N(t + s√a) = t² − a s²` with **no** `s ≠ 0` side condition, and `mpcNorm_residue_spectral_unit`
reduces mod `8`:

> `N(u) ≡ 1`, `1 − a` or `1 − 4a (mod 8)`, and it is always a unit because `a` is even.

At `a = 10` that is `{1, 7}` and at `a = −10` it is `{1, 3}`.  Two `decide`s in `ZMod 8` are the
entire arithmetic content of the lane.

### 3.3  The master identity, the step wave 80 did not name

`mpcNorm_recip_values`: **one** integer carries both coordinates of `rec_K x`.  Writing `w₀` for
the unit part of `N(√a) = −a`,

    χ_K(rec_K x) = (w · w₀ⁿ)⁻¹        ν_ur(rec_K x) = −n,

with `w` the norm of the spectral part.  This is what locks the parity of `ν_ur` to the residue
of `χ_K`: it needs `fieldUni_chi_recip_of_norm` at an **integer** exponent
(`mpcNorm_chi_recip_of_norm`), the `ℕ`-version being blind to the negative powers of `√a` that
`Kˣ` actually contains.

### 3.4  The descent (steps 1 and 2), landed, and cheaper than advertised

Wave 80 worried that `ker χ` is closed, not open, so density does not preserve it.  The fix is
not to preserve it: `mpcNorm_recip_approx` matches an arbitrary `g : G_K^{ab}` by some `rec_K x`
in **both** residues at once,

    χ mod 8   and   ν_ur mod 2,

because both are fibres of `toZModPow`, which are open (`GQ2.isOpen_preimage_toZModPow`), and
both `χ_K` and `ν_ur` are continuous.  The one missing continuity, `chiCycKAb`, is three tokens:
it is a quotient lift of the continuous `chiCycK`, exactly as `continuous_inclAbK` is of
`continuous_inclHomK` (`mpcNorm_continuous_chiCycKAb`).

That is enough because **both target `Prop`s are congruences**: `MpcNoUnitKerChi` asks for a
parity, `MpcLambdaOne` asks for a parity, and `χ(g) = u` implies `χ(g) ≡ u (mod 8)`.

### 3.5  The collision, and four `decide`s

`mpcNorm_collision`: for every `g`,

    χ(g) · w · w₀ⁿ ≡ 1 (mod 8)     and     ν_ur(g) ≡ −n (mod 2),

with `w` in the three-residue set.  Modulo `8` an even power of a unit is invisible
(`mpcNorm_unit_sq_mod_eight`), so `w₀ⁿ` sees only the parity of `n`.  `mpcNorm_parity` then turns
"only one parity survives" into the `Prop`, and the surviving-parity check is finite:

| field | `az mod 8` | `w₀ mod 8` | `w mod 8` | `χ` if `n` even | `χ` if `n` odd |
| --- | --- | --- | --- | --- | --- |
| `ℚ₂(√10)` | `2` | `3` | `{1, 7}` | `{1, 7}` | `{3, 5}` |
| `ℚ₂(√−10)` | `6` | `5` | `{1, 3}` | `{1, 3}` | `{5, 7}` |

`χ = 1` is in the even row and not the odd one at both fields (that is `MpcNoUnitKerChi`);
`χ = −1 ≡ 7` is even at `ℚ₂(√10)` and odd at `ℚ₂(√−10)` (that is the `λ(−1)` inversion); and
`χ = mUnit 2 ≡ 5` is odd at `ℚ₂(√−10)` (that is `λ(5) = 1`).

## 4.  T1: the freeness of `ℤ₂ˣ`

Wave 80 §3.3 named this the single missing input, correctly.  **Only the uniqueness half is
needed**, and that is the half the tree lacks:

> `mpcNorm_free_unique`: `(−1)^s · (mUnit 2)^t = 1` forces `s` even **and** `t = 0`.

Three lines of tree API do it: `(mUnit 2)^t` lies in the closed subgroup `1 + 4ℤ₂` for every `t`
(`zpowZtwo_mem_topologicalClosure` against `mpcNorm_oneModFour`), `(−1)^s` is `±1` by the parity
of `s`, and `−1 ≢ 1 (mod 4)`; the residual `(mUnit 2)^t = 1` is killed by the tree's own
`zpowZtwo_injective_neg_three_inv`.  **Generation is never used**, so `imChiM 2 = ⊤` is not a
prerequisite for the pivot after all.

## 5.  The pivot: `ℚ₂(√10)` yes, `ℚ₂(√−10)` no, and the reason is one word

`mpcNorm_pivot_of_even_dmB` is the criterion, at the `α = 2` core and at any transported marking:

* `ν'(C̄₀)` even (the level),
* `ν'(B̄)` **even**,
* some `x` with `χ_M(x) = 1` and `ν'(x) = 2` (the level's lower half),

imply `ν'(C̄₀)` has `2`-adic valuation exactly one.  The proof runs wave 80 §3.3's argument
without ever naming `ker χ_M`, which is what made that route look expensive:

1. `mpcNorm_compSub`: the `ℤ₂`-span of `(−1, ν'(B̄))`, `(mUnit 2, ν'(D̄))` and `(1, 4)` inside
   `ℤ₂ˣ × ℤ₂`.  It is the range of a continuous hom on the compact `ℤ₂³`, hence closed.
2. All four marked generators land in it under `Φ = (χ_M, ν')`: `B̄` and `D̄` by construction, and
   `Ā` and `C̄₀` because their `ν'`-values lie in `4ℤ₂` (`nu_dmA_eq` and the failure assumption).
   `dm_topGen`, through the target-agnostic `mpcNorm_mem_of_gens`, then traps the **whole image**.
3. `mpcNorm_exists_kerChiM` (the `≥` companion of `mpcCert_chiKerLevel_of_level`) supplies
   `Φ(x) = (1, 2)`, and freeness excludes it: `s` even and `t = 0` leave `2y·ν'(B̄) + 4u`, which
   is in `4ℤ₂` **because `ν'(B̄)` is even**.

At `ℚ₂(√10)` the `λ`-value is `0`, so `ν'(B̄)` is even and the pivot lands
(`mpcNorm_pivot_sqrtTen`).  At `ℚ₂(√−10)` the `λ`-value is `1`, so `ν'(B̄)` is **odd**, step 3
gives nothing, and wave 80 §3.3's hand counterexample `(−8, 1, 4, 1)` says no repair of *this*
argument can help: the `ε = true` pivot is independent of the level, both `λ`-values and
surjectivity.  It has to come from the certificate side, or from a sharper description of which
markings `D_M 2 0` admits.

## 6.  T3: the five-row scoreboard

| row | field | `pres` | branch datum | still carried |
| --- | --- | --- | --- | --- |
| 1 | `ℚ₂(√−2)` | `.N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | **nothing** |
| 2 | `ℚ₂(√2)` | `.M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | **nothing** |
| 3 | `ℚ₂(√5)` | `.M0 2 0` | `fieldUni_genAsmBranch_sqrtFive_of_unramified` | `fieldUni_TwoIsUniformizer KSqrtFive` |
| 4 | `ℚ₂(√10)` | `.Mpc 2 1 false .one 0` | `mpcNorm_genAsmBranch_sqrtTen` | **nothing** |
| 5 | `ℚ₂(√−10)` | `.Mpc 2 1 true .one 0` | `mpcNorm_genAsmBranch_sqrtNegTen_of_pivot` | the pivot |

So **four of the five rows' branch data now stand over the bundles alone**, and the two open
items are of completely different kinds: row 3 wants the unramifiedness of `ℚ₂(√5)` in the
repository's norm-only idiom (`Fields.lean` §4's value-group work all runs under
`Odd a.valuation`, which fails at `a = 5`), and row 5 wants the `ε = true` pivot of §5.

### What the flagship still needs, per row

Given a row's branch datum `G` and an oriented tame quotient `T`, `GenAsmRowResidual G T` has
four fields, of which wave 80 wired one (`determinant`, by
`mpcRow_genAsmRowResidual_of_counting`).  The remaining **three obligation blocks** are the same
at every row and are untouched by this lane:

1. `exactLifting`: ASK ledger field 3 at `G_K`;
2. `stokes`: ASK ledger field 4 at `G_K`;
3. `cand`: the candidate-side `WordCertificate` over the row's own slot (the surviving Gauss-`Z`
   obligation, `SqrtNeg2.PilotDet`, lives here).

## 7.  Axiom pins

Per declaration, recorded in the module's §12.  Three sets, all already committed; **this lane
introduces no axiom**.

* **Standard three** on §1 through §8, §10 and §11's abstract criterion, and on
  `mpcNorm_level_sqrt{Ten,NegTen}`.  So the four values, the two levels, the freeness of `ℤ₂ˣ`
  and the pivot criterion are **axiom-free**, and in particular
  `hilbertSymbol_normCriterion_finiteDyadic` occurs in none of them.
* **Plus the even route's endpoint set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on `mpcNorm_pivot_sqrtTen` and the four
  `rowData`/`genAsmBranch` declarations, through `fieldId_chosenEquivM_sqrt*` in the statement.
  Identical to wave 80's.
* **Plus `peripheralCyclotomicAction`** on the branch data.  `mpcNorm_genAsmBranch_sqrtTen` sits
  at **exactly** the axiom set of `mpcRow_genAsmBranch_sqrtTen`: removing all three of its inputs
  costs no axiom.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 8.  What is next

1. **The `ε = true` pivot** at `ℚ₂(√−10)` (§5).  Not from the marking side: wave 80's
   counterexample is decisive against every argument that sees only the level, the two
   `λ`-values and surjectivity.  The two live routes are the certificate side and a
   classification of the markings `D_M 2 0` admits.
2. **`fieldUni_TwoIsUniformizer KSqrtFive`** (row 3), still open and unchanged by this lane.
3. **Register `GQ2/Dyadic/Instances/MpcNormValues.lean`** in `GQ2.lean` (housekeeping).
4. **The three obligation blocks** (§6), which are now the whole of what the general row residual
   owes at every row.
5. Reusable beyond the two rows: `mpcNorm_exists_decomp`, `mpcNorm_repr_of_norm_one` and
   `mpcNorm_residue_spectral_unit` are stated for **every** ramified quadratic `ℚ₂(√a)` with
   `v(a)` odd and `‖a‖ = ‖2‖`, so `ℚ₂(√±2)`'s norm groups are one instantiation away should any
   lane want them.
