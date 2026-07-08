# P-15b remaining core — scoping (2026-07-04, Fable)

Status of `GQ2/GaussSigns.lean` (sorry-free, all std-3, in `GQ2.lean`): the **assembly and
arithmetic layers** of Lemma 6.8 / Proposition 6.9 are done and consume P-15a's now-complete
Wall doubling.  What remains is the genuine §6.2 representation-theory core.  This note pins down
exactly what is left and the concrete route, so a focused session can pick it up.

> **UNRAMIFIED SIDE ✅ FULLY LANDED (2026-07-04).**  `GQ2.SectionSix.prop_6_9_unramified` is
> proved (`#print axioms` = std-3, census 12) via the operator crux
> `GaussSigns.irreducible_operator_pow_ne_one` → `prop_6_9_unramified_of_cyclic` → SectionSix
> splice (`V` exponent 2 by Cauchy; `Hf` cyclic by `SectionThree.gen_ttame_quotient` + `c τ = 1`).
> **Only the RAMIFIED side (Lemma 6.8 + `prop_6_9_ramified`) remains** — see the Ramified section
> below.  KEY: the unramified free-action shortcut does NOT transfer to the ramified case — a
> free odd-order action forces `arf = 1` (negative sign), but ramified `q_U` has `arf = 0`
> (positive sign), so there is provably no such action.  Ramified genuinely needs the Hermitian
> model.

## What is proved (consumable now)

* `arf_qDouble_eq_zero` — Lemma 6.8's final clause: `arf q = s ∧ k ≡ s (mod 2) ⟹ arf(q_U) = 0`.
* `zeroCount_qDouble_of_arf_zero` — Prop 6.9 **ramified** count from `arf(q_U) = 0`.
* `arf_eq_one_of_dvd` — the Arf pinch: `n ∣ zeroCount−1`, `n ∣ #V−zeroCount`, `n ∤ 2^m−1` ⟹ `arf q = 1`.
* `card_dvd_of_freeAction` / `card_dvd_card_subtype_of_free` — free finite-group action ⟹ `#U` divides the cardinality of any stable subtype (orbit-stabilizer + `selfEquivSigmaOrbits`).
* `prop_6_9_unramified_of_free` — Prop 6.9 **unramified** from a free `q`-preserving action of a group `U` with `#U ∤ 2^m−1`.
* `prop_6_9_unramified_of_abelian` — the unramified branch reduced to **abelian invariance**: a finite abelian `Hf` acting faithfully, simply, `q`-invariantly, with `#Hf ∤ 2^m−1`, gives the count.  (Freeness on `V∖0` is proved internally from abelian + simple + faithful.)
* `central_two_pow_smul_eq_one` — central 2-power element on a nontrivial faithful simple exp-2 module is trivial (oddness source).

## Remaining gap — two concrete facts (unramified)

`prop_6_9_unramified` (frozen in `SectionSix.lean`) follows from `prop_6_9_unramified_of_abelian`
once we supply, for the tame image `Hf` (`c : Ttame ↠ Hf`, `c tameTau = 1`):

### (U1) `Hf` is abelian.  **Reachable now.**
`GQ2.gen_ttame_quotient c.toMonoidHom c.continuous hc : Subgroup.closure {c tameSigma, c tameTau} = ⊤`.
With `c tameTau = 1`, `closure {c σ, 1} = closure {c σ} = zpowers (c σ) = ⊤`, so `Hf` is cyclic,
hence abelian.  (~20–30 lines; `Subgroup.closure_singleton`/`zpowers`, `Subgroup.eq_top_iff'`,
a group with `zpowers g = ⊤` is `Commute`-everywhere.)

### (U2) `#Hf ∤ 2^m − 1`.  ✅ **DONE 2026-07-04** (`GQ2/GaussSigns.lean`, std-3).
Landed as `irreducible_operator_pow_ne_one` (+ helpers `minpoly_irreducible_of_noInvariant`,
`finrank_eq_natDegree_minpoly`) and packaged into **`prop_6_9_unramified_of_cyclic`**, which
reduces the whole unramified case to "`Hf` cyclic" (a single generator `g`).  The `Module.AEval'`
worry never materialised — the cyclic bridge went through `LinearMap`-surjection `p ↦ aeval T p·v`
with kernel `span {minpoly}`, then `Submodule.Quotient.restrictScalarsEquiv` +
`finrank_quotient_span_eq_natDegree`.  Remaining for unramified 6.9: **only (U1)** below + the
SectionSix splice.  The original route (kept for reference):
`V` is a simple faithful `𝔽₂[Hf]`-module with `#V = 2^{2m}`; equivalently (cyclic `Hf = ⟨g⟩`)
`T := (g • ·) : V →ₗ[𝔽₂] V` has `minpoly 𝔽₂ T` **irreducible of degree `2m`** and `T^{#Hf} = 1`,
so `minpoly T ∣ X^{#Hf} − 1`.  If `#Hf ∣ 2^m − 1` then `X^{#Hf}−1 ∣ X^{2^m−1}−1`, whose 𝔽₂-
irreducible factors all have degree `∣ m` (roots lie in `𝔽_{2^m}`), contradicting `deg = 2m`.

Formalization sub-steps + Mathlib anchors (**both hard facts CONFIRMED present 2026-07-04**):
1. `Module 𝔽₂ V` via `AddCommGroup.zmodModule` (from exponent 2); `T := DistribMulAction.toLinearMap` or hand-built `LinearMap` — feed as `Module.End (ZMod 2) V`.
2. `finrank 𝔽₂ V = 2m` from `#V = 2^{2m}` (`Module.card_eq_pow_finrank`, `ZMod.card`).
3. **`finrank 𝔽₂ V = (minpoly 𝔽₂ T).natDegree`** for the simple (⟹ cyclic) module.  NO one-liner; the bridge to build: `V` as `𝔽₂[X]`-module via `Module.AEval' T` (`Mathlib/Algebra/Polynomial/Module/AEval.lean`; `X • m = T m`), which is cyclic+torsion (`Module.AEval.isTorsion_of_finiteDimensional`), so `V ≃ₗ AdjoinRoot (minpoly T)`; then **`AdjoinRoot.powerBasis` + `powerBasis_dim`** (`Mathlib/RingTheory/AdjoinRoot.lean:701,725`) ⟹ `finrank = natDegree`.  Alt tower: give `V` an `A := AdjoinRoot(minpoly T)`-module structure, `finrank_𝔽₂ V = natDegree(minpoly)·dim_A V` and `dim_A V = 1` (simple over field `A`, `isSimpleModule_iff_finrank_eq_one`).  **~60–100 ln, the one real assembly cost of (U2).**
4. `minpoly T` irreducible: module-irreducible ⟹ minpoly irreducible — if `minpoly = f·g` proper then `ker(f(T))` is a nonzero proper `T`-invariant subspace (T commutes with `f(T)`; `f(T)≠0`, not injective).  ~20 ln; or via `(minpoly)` maximal ⟺ irreducible in the PID `𝔽₂[X]`.
5. `T^{#Hf} = 1` from `g^{#Hf} = 1` (`orderOf_dvd_card`/`pow_card_eq_one`), so `minpoly T ∣ X^{#Hf}−1` (`minpoly.dvd`, `aeval` of `X^{#Hf}-1` at `T` is `0`).  Under `#Hf ∣ 2^m−1`: `X^{#Hf}−1 ∣ X^{2^m−1}−1 ∣ X^{2^m}−X = X^{(Nat.card 𝔽₂)^m}−X`.
6. **irreducible `f ∣ X^{2^m}−X` over `𝔽₂` ⟹ `f.natDegree ∣ m`** — CONFIRMED: **`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`** (`Mathlib/FieldTheory/Finite/Extension.lean:161`), `Nat.card (ZMod 2) = 2`.  Gives `natDegree(minpoly) ∣ m`; with step 3 `= 2m` ⟹ `2m ∣ m`, contra (`m ≥ 1`).

Est (U2): ~120–180 lines; the ONLY real friction is step 3's `Module.AEval'`/`AdjoinRoot` iso
(both hard math facts, steps 3-`powerBasis` and 6, are confirmed Mathlib one-liners).  Cleanest
target: an operator-form lemma `irreducible_operator_pow_ne_one` (V a fin-dim `𝔽₂`-space,
`finrank = 2m`, `T : End` with no proper invariant subspace ⟹ `T^{2^m−1} ≠ 1`), then in
`prop_6_9_unramified_of_abelian`-land `#Hf ∣ 2^m−1 ⟹ g^{2^m−1}=1 ⟹ T^{2^m−1}=id`, contra.

Honest alternative that ALSO yields Lemma 6.8's (87): build `D = Module.End 𝔽₂[Hf] V` as a field
(`Module.End.instDivisionRing` + `littleWedderburn`), `#D = #V` (commutative `R` ⟹ `V` 1-dim
over `D`), involution `d ↦ d*` from `B` (fixed field `D₀ = 𝔽_{2^m}`), norm-one `U` of order
`2^m+1` — heavier, but gives Hermitian-line forms for 6.8 too.

## Ramified (6.8 + 6.9-ramified)

`prop_6_9_ramified` = `zeroCount_qDouble_of_arf_zero ∘ lemma_6_8`'s output (`arf(q_U)=0`), but
`lemma_6_8`'s isotypic hypotheses (`Wt`, `e`, `he`, `s`, `r`, `a`) are NOT hypotheses of
`prop_6_9_ramified` — constructing them from faithful-simple-ramified is the Clifford-theory core.

### ✅ Lemma 6.8 (87) `arf q = s` — CORE DONE, Hermitian-diagonalization-free (2026-07-04)

The **key discovery**: (87) does NOT need Hermitian diagonalization.  `arf q = s (mod 2)` is
forced by the *same* free-action machinery as the unramified case, run with a **dual pinch**.
Landed in `GQ2/GaussSigns.lean` (std-3):
* `arf_eq_zero_of_dvd` — dual of `arf_eq_one_of_dvd` (`n ∤ 2^m+1 ⟹ arf = 0`).
* `two_pow_mod`, `not_dvd_sub_one_of_odd`, `not_dvd_add_one_of_even` — `2^{m'}+1 ∣ 2^{m'·s}∓1` by parity of `s`.
* `free_zeroCount_dvds` — free action ⟹ the two zero-count divisibilities (factored out).
* **`arf_eq_of_free_norm_one`** — norm-one group of order `2^{m'}+1` acting freely on `V∖0`
  preserving `q`, `#V = 2^{2·m'·s}` ⟹ `arf q = s`.  (`s` odd ⟹ `2^{m'}+1 ∤ 2^{m'·s}−1` ⟹ pinch to 1;
  `s` even ⟹ `∤ 2^{m'·s}+1` ⟹ dual pinch to 0.)  This IS Lemma 6.8 (87), sans the group.

### Remaining for (87): `⟨T⟩` as the free group — NO involution/norm-one needed (2026-07-04)

**Better than the norm-one construction**: the general engine **`arf_eq_of_free`** (landed,
std-3) accepts ANY finite `U` acting freely with `#U ∣ 2^{2m'}−1`, `#U ∤ 2^{m'}−1`, `#U > 2`.  So
`⟨T⟩` (tame inertia, `T = c tameTau`) itself serves as `U`, **eliminating `D`'s involution and the
norm-one subgroup entirely** (`arf_eq_of_free_norm_one` is now just the `#U = 2^{m'}+1` special
case).  The remaining pieces (all with tools already in `GaussSigns`, modulo gap (1) below):
* **`⟨T⟩` acts diagonally on `V ≅ Wt^{⊕s}`, freely on `V∖0`, preserving `q`**: the diagonal action
  is `he` itself (`e` is `⟨T⟩`-equivariant); free because `T` fixes only `0` in the simple faithful
  `Wt` (`fix T` is a `⟨T⟩`-submodule `≠ Wt`, so `= ⊥` by simplicity); `q`-preserving since `T ∈ Hf`
  and `q` is `Hf`-invariant.
* **`ord(T) ∣ 2^{2m'}−1`** (= `2^f−1`): `T` is a unit of the field `𝔽₂[T] ≅ AdjoinRoot(minpoly T)`
  (`minpoly_irreducible_of_noInvariant` gives irreducibility; the field has `2^f−1` units), so
  `T^{2^f−1} = 1` (`FiniteField.pow_card_sub_one_eq_one`), i.e. `ord(T) ∣ 2^f−1`.
* **`ord(T) ∤ 2^{m'}−1`** (= `2^{f/2}−1`): exactly `irreducible_operator_pow_ne_one` (`T`
  irreducible on the `2m' = f`-dim `Wt` ⟹ `T^{2^{m'}−1} ≠ 1`).
* **`ord(T) > 2`**: `T ≠ 1` (`hram`) and tame ⟹ odd order ⟹ `ord(T) ≥ 3`.
All four need only `Wt` simple + faithful + exponent-2 (gap (1)); the field-order step is the one
new sub-lemma (~60 ln, `AdjoinRoot` field + `pow_card_sub_one_eq_one`).  ~150 ln total for (87)
once `lemma_6_8` is amended.

### ⚠ STATEMENT GAPS in the frozen `lemma_6_8` (flag for P-20 amendment)

Re-reading `lemma_6_8`'s hypotheses (P-14 statement) surfaced two omissions that block the proof
and need documented amendments (faithful to the paper's isotypic data, cf. extraction note 6):
1. **`Wt` simple** as `⟨T⟩ = zpowers (c tameTau)`-module is NOT stated — required for `D = End(Wt)`
   to be a division ring (Schur).  Add e.g. `hWtsimple : ∀ W' : AddSubgroup Wt, (∀ t, ∀ w ∈ W', (t:_) • w ∈ W') → W' = ⊥ ∨ W' = ⊤`.
2. **`S`-action compatibility with `e`** is NOT stated — `he` only covers `⟨T⟩ = zpowers (c tameTau)`,
   but (88) (`#V^U`, `rank(1+U)`, `U = powOmega2 (c tameSigma)`) needs how `S = c tameSigma` interacts
   with the `Wt^s` decomposition (the weight/Frobenius-cycle structure).  Without it (88) is
   underdetermined.  Add the `ω₂`-cycle data or an `S`-semilinear compatibility for `e`.

### (88) `#V^U = 2^{rs}`, `rank(1+U) ≡ s` — needs gap (2) resolved first

The `ω₂`-cycle count (weight spaces form one Frobenius cycle of length `2^a`, `r` cycles, `U^{2^a}=1`
by centrality+simplicity, `U`-fixed = `E₀`-component ⟹ `dim = rs`).  Blocked on statement gap (2).
Conjunct (4) `arf(q_U)=0` then follows from (87)+(88b) via `GaussSigns.arf_qDouble_eq_zero`.

## Statement-layer flag for P-20

The frozen `prop_6_9_unramified` / `prop_6_9_ramified` do **not** carry the End-field / isotypic
data that `lemma_6_8` carries.  Proving them exactly as stated forces the Schur/Clifford layer
internally; a documented amendment (adding the data as hypotheses, à la `lemma_6_16`'s Kummer
presentation) is the lighter-weight alternative and matches how the 6.17/6.18 consumers actually
have the data concretely.
