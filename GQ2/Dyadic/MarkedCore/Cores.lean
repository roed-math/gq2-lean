/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Demushkin
public import GQ2.PeripheralAction
public import GQ2.Roe.CrossedDerivation

@[expose] public section

/-!
# The rank-four marked cores `M_α`, `N_α`: words, presentations, characters, frames

**Ticket MC2** of the dyadic campaign (lane MC), implementing the MC1 design memo
`docs/dyadic/mc-design.md` §6.1.  The two standard even-rank Labute families of the packet
(`refs/dyadic-presentations-formalization-proof.tex` §7–§8; draft `refs/dyadic-presentations.tex`
§2.2, eqs. `Mpc-core`:302 and `Ncompact-core`:328) are

```
P_M(α) = A²[A,B]·C₀^{2^α}[C₀,D]        (Labute letters a,b,c,d = A,B,C₀,D)
P_N(α) = x₀^{2+2^α}[x₀,x₁]·[σ,x₂]      (Labute letters a,b,c,d = x₀,x₁,σ,x₂)
```

with `α ≥ 2` (`GQ2/Dyadic/Parameters.lean` `LabuteType.M/N`, validity `2 ≤ α`), together with
`h` appended hyperbolic handles `∏_{j<h}[u_j, v_j]` for the general even rank `4 + 2h`
(draft :347).  Repo conventions throughout: `x ^ g = g⁻¹xg` (`GQ2.conjP`),
`[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`).

## Contents

* **§1 Word shapes.**  `mWord`, `nWord`, `handleWord`, and the full relator shapes
  `mRelWord`/`nRelWord` on a marking `Fin (coreRank h) → G`; naturality (`map_mWord`, …),
  abelian collapse (`mWord_comm`, …) and the **three-term peripheral factorisations**
  (`mWord_triple`, `mWord_innerTriple`, `nWord_triple`, `nWord_innerTriple`) of memo §1.2 —
  the workhorse for the S2 lifting stratum.
* **§2 The orientation calculus.**  The crossed-derivation evaluation of both core words at
  `WordLift ℤ₂ ℤ₂ˣ`-lifts (`mWord_wordLift`, `nWord_wordLift`) and the extraction of the
  canonical orientations in **closed form** (memo V3 — no Hensel root, contrast
  `GQ2/Roe/OrientationRoot.lean`):

  ```
  χ_M(A, B, C₀, D)  = (1, −1, 1, u),   u = (1 − 2^α)⁻¹
  χ_N(x₀, x₁, σ, x₂) = (1, v, 1, 1),   v = −(1 + 2^α)⁻¹
  ```

  plus the **handle lemma** (memo §4.2): a `[u_j, v_j]` factor with `χ(u_j) = χ(v_j) = 1`
  contributes `0` to every derivation coefficient and `1` to the character relation.
* **§3 The presented cores.**  `DM`/`DN` by `profinitePresentation` + `maxProPQuotient` on the
  `GQ2/Roe/DRPresentation.lean` pattern, the marked generators, the relations, the universal
  properties `mLiftHom`/`nLiftHom`, topological generation (`dm_topGen`, the `dr_topGen`
  pattern) and hom-extensionality (`dm_hom_ext`).
* **§4 Characters.**  `chiM`/`chiN : D_P → ℤ₂ˣ` and `nuM`/`nuN : D_P → ℤ₂` in closed form.
* **§5 Abelianization frames.**  `MDecomposition` / `NDecomposition`: the two 4-frames of memo
  §2.1/§3.1.  `M`: `ℤ/2·t ⊕ ℤ₂³` with `t = Ā·C̄₀^{2^{α−1}}` and the **forced row**
  `Ā ↦ (1, 0, −m, 0)`, `m = 2^{α−1}` — a re-index of `BDecomposition`
  (`GQ2/SectionThree.lean:422`) under `2 ↦ m`.  `N`: the α-free frame whose torsion generator
  is the *marked* generator `x̄₀`, with **no forced row**.
* **§6 The exponent / normal-form lemma** (memo §4.1(2), R2): the rank-three `decide` route
  (`drRelZ_drCC`, `GQ2/Roe/DRDemushkin.lean:339`) does **not** survive a relator exponent
  `2^α`.  Replaced by the reusable *mod-4 diagonal exponent rule* `diagCoeff_mod_four`
  (`C(k,2) mod 2` depends only on `k mod 4`) and its group-level companion
  `pow_centralExt` — stated at the level of exponents and words, for reuse by the five
  branch-word tickets.
* **§7 The two MC2 assets of memo §10.**  `isFreePro2Pair` (the "free pro-2 of rank 2" shape
  for the peripheral pairs) and the generic **B8 transport lemma** `peripheralTriple_scaling`,
  which consumes `PeripheralCyclotomicAction` (`GQ2/PeripheralAction.lean:92`) verbatim.

## Rank parameterisation (deviation from the memo's `n`, recorded)

The memo writes `D_{P,α,n}` with `n + 2` generators and `n = 2 + 2h` even.  Encoding `n` as a
bare `ℕ` would make `Fin (n+2)`'s indices `2`, `3` wrap for `n < 2`; we therefore carry the
**handle count** `h : ℕ` and set `coreRank h = 4 + 2h`, which is the memo's `n + 2` under
`n = 2 + 2h`.  All statements are otherwise verbatim; `demushkinRank = coreRank h` is the
memo's `n + 2` and `card H¹ = 2 ^ coreRank h` is its `2^{n+2}`.
-/

open CategoryTheory Multiplicative

namespace GQ2

open FoxH

namespace Dyadic

namespace MarkedCore

/-! ## §1 The word shapes -/

section Words

variable {G : Type*} [Group G]

/-- The **`M_α` core word shape** `a²[a,b]·c^{2^α}[c,d]` (draft eq. `Mpc-core`, Labute letters
`a,b,c,d = A,B,C₀,D`), as a word in any group with the repo conventions `x ^ g = g⁻¹xg`
(`conjP`) and `[x,y] = x⁻¹y⁻¹xy` (`commP`).  Evaluated at the free profinite generators it is
the relator `mRelator`; at `WordLift`-lifts it computes the χ-twisted Fox row (§2). -/
def mWord (α : ℕ) (a b c d : G) : G :=
  a ^ 2 * commP a b * c ^ (2 ^ α) * commP c d

/-- The **`N_α` core word shape** `a^{2+2^α}[a,b]·[c,d]` (draft eq. `Ncompact-core`, Labute
letters `a,b,c,d = x₀,x₁,σ,x₂`). -/
def nWord (α : ℕ) (a b c d : G) : G :=
  a ^ (2 + 2 ^ α) * commP a b * commP c d

/-- **`h` hyperbolic handles** `∏_{j<h} [u_j, v_j]` (draft :347), in the fixed left-to-right
order of `List.finRange h`.  (`Finset.prod` is unavailable: `G` is not commutative.) -/
def handleWord {h : ℕ} (u v : Fin h → G) : G :=
  ((List.finRange h).map fun j => commP (u j) (v j)).prod

@[simp] theorem handleWord_zero (u v : Fin 0 → G) : handleWord u v = 1 := rfl

end Words

/-! ### The generator index type

The core letters are `0, 1, 2, 3`; the `j`-th handle pair is `(4 + 2j, 5 + 2j)`. -/

/-- The number of generators of the rank-`(4 + 2h)` core: the memo's `n + 2` under
`n = 2 + 2h`. -/
def coreRank (h : ℕ) : ℕ := 4 + 2 * h

instance instNeZeroCoreRank (h : ℕ) : NeZero (coreRank h) := ⟨by simp [coreRank]⟩

@[simp] theorem coreRank_zero : coreRank 0 = 4 := rfl

/-- The first letter of the `j`-th handle pair. -/
def handleIdxU {h : ℕ} (j : Fin h) : Fin (coreRank h) :=
  ⟨4 + 2 * j, by have := j.isLt; simp only [coreRank]; omega⟩

/-- The second letter of the `j`-th handle pair. -/
def handleIdxV {h : ℕ} (j : Fin h) : Fin (coreRank h) :=
  ⟨5 + 2 * j, by have := j.isLt; simp only [coreRank]; omega⟩

section RelWords

variable {G : Type*} [Group G] {h : ℕ}

/-- The **full `M_α` relator shape** on a marking of `Fin (coreRank h)`: the core word on the
first four letters times the `h` handles on the remaining `2h`. -/
def mRelWord (α : ℕ) (m : Fin (coreRank h) → G) : G :=
  mWord α (m 0) (m 1) (m 2) (m 3) *
    handleWord (fun j => m (handleIdxU j)) (fun j => m (handleIdxV j))

/-- The **full `N_α` relator shape** on a marking of `Fin (coreRank h)`. -/
def nRelWord (α : ℕ) (m : Fin (coreRank h) → G) : G :=
  nWord α (m 0) (m 1) (m 2) (m 3) *
    handleWord (fun j => m (handleIdxU j)) (fun j => m (handleIdxV j))

end RelWords

/-! ### Naturality

All four shapes use only `*`, `⁻¹`, `^` (no `ω₂`-powers), so they push through any
monoid-hom-like map unconditionally — the `map_drWord` pattern
(`GQ2/Roe/DRPresentation.lean:89`). -/

section Naturality

variable {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]

/-- **Naturality of `mWord`** (the `map_drWord` clone). -/
theorem map_mWord (φ : F) (α : ℕ) (a b c d : G) :
    φ (mWord α a b c d) = mWord α (φ a) (φ b) (φ c) (φ d) := by
  simp only [mWord, commP, map_mul, map_inv, map_pow]

/-- **Naturality of `nWord`**. -/
theorem map_nWord (φ : F) (α : ℕ) (a b c d : G) :
    φ (nWord α a b c d) = nWord α (φ a) (φ b) (φ c) (φ d) := by
  simp only [nWord, commP, map_mul, map_inv, map_pow]

/-- **Naturality of `handleWord`**. -/
theorem map_handleWord (φ : F) {k : ℕ} (u v : Fin k → G) :
    φ (handleWord u v) = handleWord (fun j => φ (u j)) (fun j => φ (v j)) := by
  rw [handleWord, handleWord, ← List.prod_hom _ φ, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, commP, map_mul, map_inv]

variable {h : ℕ}

/-- **Naturality of the full `M_α` relator shape**. -/
theorem map_mRelWord (φ : F) (α : ℕ) (m : Fin (coreRank h) → G) :
    φ (mRelWord α m) = mRelWord α fun i => φ (m i) := by
  rw [mRelWord, map_mul, map_mWord, map_handleWord, mRelWord]

/-- **Naturality of the full `N_α` relator shape**. -/
theorem map_nRelWord (φ : F) (α : ℕ) (m : Fin (coreRank h) → G) :
    φ (nRelWord α m) = nRelWord α fun i => φ (m i) := by
  rw [nRelWord, map_mul, map_nWord, map_handleWord, nRelWord]

end Naturality

/-! ### Abelian collapse — the relation vectors `ρ_M`, `ρ_N` (memo §2.1, §3.1) -/

section AbelianCollapse

variable {G : Type*} [CommGroup G]

/-- **Abelian collapse of `mWord`** (memo §2.1): the commutators die, leaving the relation
vector `ρ_M = 2Ā + 2^α C̄₀`. -/
theorem mWord_comm (α : ℕ) (a b c d : G) : mWord α a b c d = a ^ 2 * c ^ (2 ^ α) := by
  rw [mWord, commP_eq_one, commP_eq_one, mul_one, mul_assoc, one_mul]

/-- **Abelian collapse of `nWord`** (memo §3.1): the relation vector
`ρ_N = (2 + 2^α)·x̄₀`. -/
theorem nWord_comm (α : ℕ) (a b c d : G) : nWord α a b c d = a ^ (2 + 2 ^ α) := by
  rw [nWord, commP_eq_one, commP_eq_one, mul_one, mul_one]

/-- **Abelian collapse of `handleWord`** (memo §4.2): handles are invisible on the
abelianization, so they leave the relation vector — hence `q = 2` and the frame's first
coordinate — unchanged. -/
theorem handleWord_comm {k : ℕ} (u v : Fin k → G) : handleWord u v = 1 := by
  rw [handleWord, List.prod_eq_one]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact commP_eq_one _ _

variable {h : ℕ}

/-- **Abelian collapse of the full `M_α` relator**: `ρ_M = 2Ā + 2^α C̄₀`, handles included. -/
theorem mRelWord_comm (α : ℕ) (m : Fin (coreRank h) → G) :
    mRelWord α m = m 0 ^ 2 * m 2 ^ (2 ^ α) := by
  rw [mRelWord, handleWord_comm, mul_one, mWord_comm]

/-- **Abelian collapse of the full `N_α` relator**: `ρ_N = (2 + 2^α)·x̄₀`. -/
theorem nRelWord_comm (α : ℕ) (m : Fin (coreRank h) → G) :
    nRelWord α m = m 0 ^ (2 + 2 ^ α) := by
  rw [nRelWord, handleWord_comm, mul_one, nWord_comm]

end AbelianCollapse

/-! ### The three-term (peripheral) normal form — memo §1.2

Both relators collapse to a product of **three** factors equal to `1`, twice nested.  This is
the shape the B8 transport lemma of §7 consumes: `Δ = ⟨P, T | −⟩` with `P·T·C = 1`
(`GQ2/PeripheralAction.lean:83`) maps to any such triple.  The rank-three precedent is
`A²S⁴[S,Y] = A²·S³·S^Y` (`lambdaHom`, `GQ2/AnabelianBridge/Construction.lean:486`). -/

section Triples

variable {G : Type*} [Group G]

/-- The **outer peripheral head** of `P_M`: `w_M = A·A^B`. -/
def mHead (a b : G) : G := a * conjP a b

/-- The **outer peripheral head** of `P_N`: `w_N = x₀^{1+2^α}·x₀^{x₁}`. -/
def nHead (α : ℕ) (a b : G) : G := a ^ (1 + 2 ^ α) * conjP a b

/-- **The outer three-term factorisation of `P_M`** (memo §1.2):
`P_M = (A·A^B) · C₀^{2^α−1} · C₀^D`.  (The exponent `2^α − 1` is a `ℕ`-subtraction; it is the
intended `2^α − 1` because `1 ≤ 2^α`.) -/
theorem mWord_triple (α : ℕ) (a b c d : G) :
    mWord α a b c d = mHead a b * c ^ (2 ^ α - 1) * conjP c d := by
  have hpow : c ^ (2 ^ α) = c ^ (2 ^ α - 1) * c := by
    rw [← pow_succ]
    congr 1
    have : 1 ≤ 2 ^ α := Nat.one_le_two_pow
    omega
  simp only [mWord, mHead, conjP, commP, hpow]
  group

/-- **The inner three-term factorisation of `P_M`** (memo §1.2): `A · A^B · w_M⁻¹ = 1`. -/
theorem mWord_innerTriple (a b : G) : a * conjP a b * (mHead a b)⁻¹ = 1 := by
  rw [mHead, mul_inv_cancel]

/-- **The outer three-term factorisation of `P_N`** (memo §1.2):
`P_N = w_N · σ⁻¹ · σ^{x₂}`. -/
theorem nWord_triple (α : ℕ) (a b c d : G) :
    nWord α a b c d = nHead α a b * c⁻¹ * conjP c d := by
  have hpow : a ^ (2 + 2 ^ α) = a ^ (1 + 2 ^ α) * a := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [nWord, nHead, conjP, commP, hpow]
  group

/-- **The inner three-term factorisation of `P_N`** (memo §1.2):
`x₀^{1+2^α} · x₀^{x₁} · w_N⁻¹ = 1`. -/
theorem nWord_innerTriple (α : ℕ) (a b : G) :
    a ^ (1 + 2 ^ α) * conjP a b * (nHead α a b)⁻¹ = 1 := by
  rw [nHead, mul_inv_cancel]

/-- **The handle three-term identity**: `[c, d] = c⁻¹ · c^d`, so every hyperbolic handle is
itself a peripheral pair (this is what makes the handle transvections stratum-S1 lifts,
memo §3.5/§4.2). -/
theorem commP_eq_inv_mul_conjP (c d : G) : commP c d = c⁻¹ * conjP c d := by
  rw [commP, conjP]
  group

end Triples

end MarkedCore

end Dyadic

end GQ2
