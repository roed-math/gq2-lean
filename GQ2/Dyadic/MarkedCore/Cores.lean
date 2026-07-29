/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.BoundaryFrame
public import GQ2.Demushkin
public import GQ2.PeripheralAction
public import GQ2.Roe.CrossedDerivation
public import GQ2.Roe.DRWordCoh

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

/-! ## §2 The orientation calculus

The χ-twisted crossed-derivation calculus of `GQ2/Roe/CrossedDerivation.lean` applied to the two
rank-four core words.  A pair (character value, derivation value) is a point of
`WordLift ℤ₂ ℤ₂ˣ` whose multiplication *is* the crossed-derivation product rule
`D(gh) = Dg + χ(g)Dh`; the two atomic rules are `conjP_wordLift` (:79) and `commP_wordLift`
(:91), and the power rule is `WordLift.pow_u` (the geometric sum).

The memo's calibration (§1.3) reproduces `chiD0G`'s `(−1, 1, (−3)⁻¹)` from the ℚ₂ relator
`A²S⁴[S,Y]`; the same calculus applied here gives the two **closed-form** orientations of memo
V3 — no analogue of `GQ2/Roe/OrientationRoot.lean`'s Hensel root is needed. -/

/-- The **norm (geometric) sum** `N_n(X) = 1 + X + ⋯ + X^{n−1}` — the coefficient the `n`-th
power of a generator contributes to its own Fox row (`WordLift.pow_u`). -/
noncomputable def normSum (X : ℤ_[2]) (n : ℕ) : ℤ_[2] := ∑ i ∈ Finset.range n, X ^ i

@[simp] theorem normSum_one_base (n : ℕ) : normSum 1 n = (n : ℤ_[2]) := by
  simp [normSum]

theorem normSum_two (X : ℤ_[2]) : normSum X 2 = 1 + X := by
  simp [normSum, Finset.sum_range_succ]

/-- **The power rule at `WordLift ℤ₂ ℤ₂ˣ`-lifts**: `⟨D, X⟩ ^ n = ⟨N_n(X)·D, X^n⟩`
(`WordLift.pow_u`, the norm projector). -/
theorem pow_wordLift (X : ℤ_[2]ˣ) (D : ℤ_[2]) (n : ℕ) :
    (⟨D, X⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ n = ⟨normSum (X : ℤ_[2]) n * D, X ^ n⟩ := by
  ext
  · rw [WordLift.pow_u, normSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Units.smul_def, smul_eq_mul, Units.val_pow_eq_pow_val]
  · rw [WordLift.pow_g]

/-! ### The handle lemma (memo §4.2)

A hyperbolic handle `[u_j, v_j]` with `χ(u_j) = χ(v_j) = 1` contributes **zero** to every
derivation coefficient and **one** to the character relation.  Hence appending handles leaves
the orientation values on the core letters unchanged and forces `χ ≡ 1` on all handle letters. -/

/-- **The handle lemma, atomic form**: `D[u, v] = 0` and `χ([u,v]) = 1` when
`χ(u) = χ(v) = 1`. -/
theorem commP_wordLift_one (Du Dv : ℤ_[2]) :
    commP (⟨Du, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dv, 1⟩ = 1 := by
  rw [commP_wordLift]
  ext
  · simp
  · simp [commP_eq_one]

/-- **The handle lemma** (memo §4.2): the whole handle block is invisible to the crossed
derivation once every handle letter carries `χ = 1`. -/
theorem handleWord_wordLift_one {k : ℕ} (Du Dv : Fin k → ℤ_[2]) :
    handleWord (fun j => (⟨Du j, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)) (fun j => ⟨Dv j, 1⟩) = 1 := by
  rw [handleWord, List.prod_eq_one]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact commP_wordLift_one _ _

/-! ### The `M_α` Fox row -/

/-- The `D_A`-coefficient of `D(P_M)` (memo §2.2(i), row `D_A`), in **raw** (pre-cancellation)
form — what the word evaluation literally produces. -/
noncomputable def mCoeffA (Xa Xb : ℤ_[2]ˣ) : ℤ_[2] :=
  normSum (Xa : ℤ_[2]) 2 + (Xa : ℤ_[2]) ^ 2 * ((Xa⁻¹ : ℤ_[2]ˣ) * ((Xb⁻¹ : ℤ_[2]ˣ) - 1))

/-- The `D_B`-coefficient of `D(P_M)` (memo §2.2(i), row `D_B`). -/
noncomputable def mCoeffB (Xa Xb : ℤ_[2]ˣ) : ℤ_[2] :=
  (Xa : ℤ_[2]) ^ 2 * ((Xb⁻¹ : ℤ_[2]ˣ) * (1 - (Xa⁻¹ : ℤ_[2]ˣ)))

/-- The `D_{C₀}`-coefficient of `D(P_M)` (memo §2.2(i), row `D_C`): the geometric sum `N_{2^α}`
plus the `[C₀, D]`-term. -/
noncomputable def mCoeffC (α : ℕ) (Xa Xc Xd : ℤ_[2]ˣ) : ℤ_[2] :=
  (Xa : ℤ_[2]) ^ 2 * normSum (Xc : ℤ_[2]) (2 ^ α)
    + (Xa : ℤ_[2]) ^ 2 * (Xc : ℤ_[2]) ^ (2 ^ α) * ((Xc⁻¹ : ℤ_[2]ˣ) * ((Xd⁻¹ : ℤ_[2]ˣ) - 1))

/-- The `D_D`-coefficient of `D(P_M)` (memo §2.2(i), row `D_D`). -/
noncomputable def mCoeffD (α : ℕ) (Xa Xc Xd : ℤ_[2]ˣ) : ℤ_[2] :=
  (Xa : ℤ_[2]) ^ 2 * (Xc : ℤ_[2]) ^ (2 ^ α) * ((Xd⁻¹ : ℤ_[2]ˣ) * (1 - (Xc⁻¹ : ℤ_[2]ˣ)))

/-- **The `P_M`-evaluation identity** — the master computation of memo §2.2(i).  Evaluating the
`M_α` core word at the crossed-derivation lifts `A, B, C₀, D ↦ ⟨D_•, X_•⟩` gives derivation
component `mCoeffA·D_A + mCoeffB·D_B + mCoeffC·D_C + mCoeffD·D_D` and character component
`X_A²·X_C^{2^α}` (the character relation). -/
theorem mWord_wordLift (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) (Da Db Dc Dd : ℤ_[2]) :
    mWord α (⟨Da, Xa⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Db, Xb⟩ ⟨Dc, Xc⟩ ⟨Dd, Xd⟩
      = ⟨mCoeffA Xa Xb * Da + mCoeffB Xa Xb * Db
          + mCoeffC α Xa Xc Xd * Dc + mCoeffD α Xa Xc Xd * Dd,
        Xa ^ 2 * Xc ^ (2 ^ α)⟩ := by
  rw [mWord, pow_wordLift, pow_wordLift, commP_wordLift, commP_wordLift]
  ext
  · simp only [WordLift.mul_u, WordLift.mul_g, Units.smul_def, smul_eq_mul, Units.val_mul,
      Units.val_pow_eq_pow_val, commP_eq_one, Units.val_one, mCoeffA, mCoeffB, mCoeffC, mCoeffD]
    ring
  · simp only [WordLift.mul_g, commP_eq_one, mul_one]

/-! ### The `N_α` Fox row -/

/-- The `D_{x₀}`-coefficient of `D(P_N)` (memo §3.2(i), row `D_{x₀}`). -/
noncomputable def nCoeffA (α : ℕ) (Xa Xb : ℤ_[2]ˣ) : ℤ_[2] :=
  normSum (Xa : ℤ_[2]) (2 + 2 ^ α)
    + (Xa : ℤ_[2]) ^ (2 + 2 ^ α) * ((Xa⁻¹ : ℤ_[2]ˣ) * ((Xb⁻¹ : ℤ_[2]ˣ) - 1))

/-- The `D_{x₁}`-coefficient of `D(P_N)` (memo §3.2(i), row `D_{x₁}`). -/
noncomputable def nCoeffB (α : ℕ) (Xa Xb : ℤ_[2]ˣ) : ℤ_[2] :=
  (Xa : ℤ_[2]) ^ (2 + 2 ^ α) * ((Xb⁻¹ : ℤ_[2]ˣ) * (1 - (Xa⁻¹ : ℤ_[2]ˣ)))

/-- The `D_σ`-coefficient of `D(P_N)` (memo §3.2(i), row `D_σ`). -/
noncomputable def nCoeffC (α : ℕ) (Xa Xc Xd : ℤ_[2]ˣ) : ℤ_[2] :=
  (Xa : ℤ_[2]) ^ (2 + 2 ^ α) * ((Xc⁻¹ : ℤ_[2]ˣ) * ((Xd⁻¹ : ℤ_[2]ˣ) - 1))

/-- The `D_{x₂}`-coefficient of `D(P_N)` (memo §3.2(i), row `D_{x₂}`). -/
noncomputable def nCoeffD (α : ℕ) (Xa Xc Xd : ℤ_[2]ˣ) : ℤ_[2] :=
  (Xa : ℤ_[2]) ^ (2 + 2 ^ α) * ((Xd⁻¹ : ℤ_[2]ˣ) * (1 - (Xc⁻¹ : ℤ_[2]ˣ)))

/-- **The `P_N`-evaluation identity** — the master computation of memo §3.2(i).  Note the third
row: the `[σ, x₂]` factor contributes zero to every coefficient once `χ(σ) = χ(x₂) = 1`; that is
the handle lemma (`commP_wordLift_one`) read off this identity. -/
theorem nWord_wordLift (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) (Da Db Dc Dd : ℤ_[2]) :
    nWord α (⟨Da, Xa⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Db, Xb⟩ ⟨Dc, Xc⟩ ⟨Dd, Xd⟩
      = ⟨nCoeffA α Xa Xb * Da + nCoeffB α Xa Xb * Db
          + nCoeffC α Xa Xc Xd * Dc + nCoeffD α Xa Xc Xd * Dd,
        Xa ^ (2 + 2 ^ α)⟩ := by
  rw [nWord, pow_wordLift, commP_wordLift, commP_wordLift]
  ext
  · simp only [WordLift.mul_u, WordLift.mul_g, Units.smul_def, smul_eq_mul, Units.val_mul,
      Units.val_pow_eq_pow_val, commP_eq_one, Units.val_one, nCoeffA, nCoeffB, nCoeffC, nCoeffD]
    ring
  · simp only [WordLift.mul_g, commP_eq_one, mul_one]

/-! ### The two orientation units `u`, `v`

`1 ± 2^α` is odd, hence a unit of `ℤ₂` (`isUnit_one_add_two_mul`,
`GQ2/ZtwoPowering.lean:491`), for every `α ≥ 1`.  These are the packet's `u` (§8 line 765) and
the draft's `v` (line 333). -/

/-- The unit `1 − 2^α ∈ ℤ₂ˣ` (`α ≥ 1`; at `α = 0` the `ℕ`-subtraction in the definition makes
the value `−1`, which is never used). -/
noncomputable def oneSubTwoPow (α : ℕ) : ℤ_[2]ˣ :=
  (isUnit_one_add_two_mul (-(2 : ℤ_[2]) ^ (α - 1))).unit

/-- The unit `1 + 2^α ∈ ℤ₂ˣ` (`α ≥ 1`). -/
noncomputable def onePlusTwoPow (α : ℕ) : ℤ_[2]ˣ :=
  (isUnit_one_add_two_mul ((2 : ℤ_[2]) ^ (α - 1))).unit

theorem oneSubTwoPow_val {α : ℕ} (hα : 1 ≤ α) :
    (oneSubTwoPow α : ℤ_[2]) = 1 - 2 ^ α := by
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
  rw [oneSubTwoPow, IsUnit.unit_spec, Nat.add_sub_cancel]
  ring

theorem onePlusTwoPow_val {α : ℕ} (hα : 1 ≤ α) :
    (onePlusTwoPow α : ℤ_[2]) = 1 + 2 ^ α := by
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
  rw [onePlusTwoPow, IsUnit.unit_spec, Nat.add_sub_cancel]
  ring

/-- **The `M_α` orientation unit** `u = (1 − 2^α)⁻¹` (memo §2.2(i), V3).  It lies in
`1 + 2^α ℤ₂` with depth exactly `α`; `im χ_M = ⟨−1⟩ × ⟨u⟩` is packet §8's `C`. -/
noncomputable def mUnit (α : ℕ) : ℤ_[2]ˣ := (oneSubTwoPow α)⁻¹

/-- **The `N_α` orientation unit** `v = −(1 + 2^α)⁻¹` (memo §3.2(i), V3).  `im χ_N = ⟨v⟩` is
procyclic — the decisive `M`/`N` separator (memo V2/§3.2(i)). -/
noncomputable def nUnit (α : ℕ) : ℤ_[2]ˣ := -(onePlusTwoPow α)⁻¹

/-- The defining equation of `u`: `u·(1 − 2^α) = 1`. -/
theorem mUnit_mul {α : ℕ} (hα : 1 ≤ α) : (mUnit α : ℤ_[2]) * (1 - 2 ^ α) = 1 := by
  rw [mUnit, ← oneSubTwoPow_val hα, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- The defining equation of `v`: `v·(1 + 2^α) = −1`. -/
theorem nUnit_mul {α : ℕ} (hα : 1 ≤ α) : (nUnit α : ℤ_[2]) * (1 + 2 ^ α) = -1 := by
  have hinv : ((onePlusTwoPow α)⁻¹ : ℤ_[2]ˣ) * (onePlusTwoPow α : ℤ_[2]ˣ) = 1 := inv_mul_cancel _
  have hval := congrArg Units.val hinv
  rw [Units.val_mul, Units.val_one] at hval
  rw [nUnit, ← onePlusTwoPow_val hα, Units.val_neg]
  linear_combination -hval

/-! ### The Labute descent conditions and the closed-form orientations

`IsLabuteOrientationDatum` pattern (`GQ2/Roe/CrossedDerivation.lean:183`): a character-value
tuple is a *Labute orientation datum* when the lifted word dies for **every** choice of
derivation generator-values — equivalently, the character kills the relator and every crossed
derivation into `ℤ₂(χ)` kills it. -/

/-- **The Labute descent condition for `P_M`**. -/
def IsLabuteOrientationDatumM (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) : Prop :=
  ∀ Da Db Dc Dd : ℤ_[2],
    mWord α (⟨Da, Xa⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Db, Xb⟩ ⟨Dc, Xc⟩ ⟨Dd, Xd⟩ = 1

/-- **The Labute descent condition for `P_N`**. -/
def IsLabuteOrientationDatumN (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) : Prop :=
  ∀ Da Db Dc Dd : ℤ_[2],
    nWord α (⟨Da, Xa⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Db, Xb⟩ ⟨Dc, Xc⟩ ⟨Dd, Xd⟩ = 1

/-- **Extraction of the five equations for `P_M`** — the character relation plus the four Fox
coefficients (the `isLabuteOrientationDatum_iff` clone). -/
theorem isLabuteOrientationDatumM_iff_coeffs (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) :
    IsLabuteOrientationDatumM α Xa Xb Xc Xd ↔
      (Xa ^ 2 * Xc ^ (2 ^ α) = 1 ∧ mCoeffA Xa Xb = 0 ∧ mCoeffB Xa Xb = 0 ∧
        mCoeffC α Xa Xc Xd = 0 ∧ mCoeffD α Xa Xc Xd = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hg := congrArg WordLift.g (h 0 0 0 0)
      rw [mWord_wordLift] at hg
      exact hg
    · have hu := congrArg WordLift.u (h 1 0 0 0)
      rw [mWord_wordLift] at hu
      simpa using hu
    · have hu := congrArg WordLift.u (h 0 1 0 0)
      rw [mWord_wordLift] at hu
      simpa using hu
    · have hu := congrArg WordLift.u (h 0 0 1 0)
      rw [mWord_wordLift] at hu
      simpa using hu
    · have hu := congrArg WordLift.u (h 0 0 0 1)
      rw [mWord_wordLift] at hu
      simpa using hu
  · rintro ⟨hchar, hA, hB, hC, hD⟩ Da Db Dc Dd
    rw [mWord_wordLift]
    ext
    · simp only [hA, hB, hC, hD, zero_mul, add_zero, WordLift.one_u]
    · simp only [hchar, WordLift.one_g]

/-- **Extraction of the five equations for `P_N`**. -/
theorem isLabuteOrientationDatumN_iff_coeffs (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) :
    IsLabuteOrientationDatumN α Xa Xb Xc Xd ↔
      (Xa ^ (2 + 2 ^ α) = 1 ∧ nCoeffA α Xa Xb = 0 ∧ nCoeffB α Xa Xb = 0 ∧
        nCoeffC α Xa Xc Xd = 0 ∧ nCoeffD α Xa Xc Xd = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hg := congrArg WordLift.g (h 0 0 0 0)
      rw [nWord_wordLift] at hg
      exact hg
    · have hu := congrArg WordLift.u (h 1 0 0 0)
      rw [nWord_wordLift] at hu
      simpa using hu
    · have hu := congrArg WordLift.u (h 0 1 0 0)
      rw [nWord_wordLift] at hu
      simpa using hu
    · have hu := congrArg WordLift.u (h 0 0 1 0)
      rw [nWord_wordLift] at hu
      simpa using hu
    · have hu := congrArg WordLift.u (h 0 0 0 1)
      rw [nWord_wordLift] at hu
      simpa using hu
  · rintro ⟨hchar, hA, hB, hC, hD⟩ Da Db Dc Dd
    rw [nWord_wordLift]
    ext
    · simp only [hA, hB, hC, hD, zero_mul, add_zero, WordLift.one_u]
    · simp only [hchar, WordLift.one_g]

/-! #### Clearing the Fox coefficients -/

private theorem one_sub_inv_val_eq_zero_iff (X : ℤ_[2]ˣ) :
    (1 : ℤ_[2]) - ((X⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 0 ↔ X = 1 := by
  refine ⟨fun hx => ?_, fun hx => by rw [hx]; simp⟩
  have hx' : (X⁻¹ : ℤ_[2]ˣ) = 1 := Units.ext (by rw [Units.val_one]; linear_combination -hx)
  exact inv_eq_one.mp hx'

private theorem mCoeffB_eq (Xa Xb : ℤ_[2]ˣ) :
    mCoeffB Xa Xb = ((Xa ^ 2 * Xb⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - ((Xa⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
  simp only [mCoeffB, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem mCoeffD_eq (α : ℕ) (Xa Xc Xd : ℤ_[2]ˣ) :
    mCoeffD α Xa Xc Xd
      = ((Xa ^ 2 * Xc ^ (2 ^ α) * Xd⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - ((Xc⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
  simp only [mCoeffD, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem nCoeffB_eq (α : ℕ) (Xa Xb : ℤ_[2]ˣ) :
    nCoeffB α Xa Xb
      = ((Xa ^ (2 + 2 ^ α) * Xb⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - ((Xa⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
  simp only [nCoeffB, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem nCoeffD_eq (α : ℕ) (Xa Xc Xd : ℤ_[2]ˣ) :
    nCoeffD α Xa Xc Xd
      = ((Xa ^ (2 + 2 ^ α) * Xd⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - ((Xc⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
  simp only [nCoeffD, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- **The canonical orientation of `M_α`, in closed form** (memo §2.2(i), V3):
`χ_M(A, B, C₀, D) = (1, −1, 1, u)` with `u = (1 − 2^α)⁻¹`.  **No Hensel root** — contrast the
rank-three `GQ2/Roe/OrientationRoot.lean`.

(The `α ≥ 2` validity bound of `GQ2/Dyadic/Parameters.lean` is *not* needed for the equivalence:
at `α = 0` both sides are false, since `1 − 2^0 = 0` is not a unit.) -/
theorem isLabuteOrientationDatumM_iff (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) :
    IsLabuteOrientationDatumM α Xa Xb Xc Xd ↔
      (Xa = 1 ∧ Xb = -1 ∧ Xc = 1 ∧ (Xd : ℤ_[2]) * (1 - 2 ^ α) = 1) := by
  rw [isLabuteOrientationDatumM_iff_coeffs]
  constructor
  · rintro ⟨-, hA, hB, hC, hD⟩
    have hXa : Xa = 1 := by
      rw [mCoeffB_eq, Units.mul_right_eq_zero] at hB
      exact (one_sub_inv_val_eq_zero_iff Xa).mp hB
    subst hXa
    have hXc : Xc = 1 := by
      rw [mCoeffD_eq, Units.mul_right_eq_zero] at hD
      exact (one_sub_inv_val_eq_zero_iff Xc).mp hD
    subst hXc
    refine ⟨rfl, ?_, rfl, ?_⟩
    · simp only [mCoeffA, normSum_two, Units.val_one, inv_one, one_pow, one_mul] at hA
      have hb : (Xb⁻¹ : ℤ_[2]ˣ) = -1 := Units.ext (by
        rw [Units.val_neg, Units.val_one]; linear_combination hA)
      rw [← inv_inv Xb, hb, inv_neg, inv_one]
    · simp only [mCoeffC, Units.val_one, inv_one, one_pow, one_mul, normSum_one_base] at hC
      have hdd := Units.mul_inv Xd
      push_cast at hC
      linear_combination hdd - (Xd : ℤ_[2]) * hC
  · rintro ⟨rfl, rfl, rfl, hd⟩
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · simp only [mCoeffA, normSum_two, Units.val_one, inv_one, one_pow, one_mul,
        Units.val_neg, inv_neg]
      ring
    · simp only [mCoeffB, Units.val_one, inv_one, one_pow, sub_self, mul_zero]
    · simp only [mCoeffC, Units.val_one, inv_one, one_pow, one_mul, normSum_one_base]
      have hdd := Units.inv_mul Xd
      push_cast
      linear_combination (-((Xd⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * hd + (1 - (2 : ℤ_[2]) ^ α) * hdd
    · simp only [mCoeffD, Units.val_one, inv_one, one_pow, one_mul, sub_self, mul_zero]

/-- **The canonical orientation of `N_α`, in closed form** (memo §3.2(i), V3):
`χ_N(x₀, x₁, σ, x₂) = (1, v, 1, 1)` with `v = −(1 + 2^α)⁻¹`. -/
theorem isLabuteOrientationDatumN_iff (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) :
    IsLabuteOrientationDatumN α Xa Xb Xc Xd ↔
      (Xa = 1 ∧ (Xb : ℤ_[2]) * (1 + 2 ^ α) = -1 ∧ Xc = 1 ∧ Xd = 1) := by
  rw [isLabuteOrientationDatumN_iff_coeffs]
  constructor
  · rintro ⟨-, hA, hB, hC, hD⟩
    have hXa : Xa = 1 := by
      rw [nCoeffB_eq, Units.mul_right_eq_zero] at hB
      exact (one_sub_inv_val_eq_zero_iff Xa).mp hB
    subst hXa
    have hXc : Xc = 1 := by
      rw [nCoeffD_eq, Units.mul_right_eq_zero] at hD
      exact (one_sub_inv_val_eq_zero_iff Xc).mp hD
    subst hXc
    have hXd : Xd = 1 := by
      simp only [nCoeffC, Units.val_one, inv_one, one_pow, one_mul] at hC
      have hc' : (Xd⁻¹ : ℤ_[2]ˣ) = 1 := Units.ext (by
        rw [Units.val_one]; linear_combination hC)
      exact inv_eq_one.mp hc'
    refine ⟨rfl, ?_, rfl, hXd⟩
    simp only [nCoeffA, Units.val_one, inv_one, one_pow, one_mul, normSum_one_base] at hA
    have hbb := Units.mul_inv Xb
    push_cast at hA
    linear_combination (Xb : ℤ_[2]) * hA - hbb
  · rintro ⟨rfl, hb, rfl, rfl⟩
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · simp only [nCoeffA, Units.val_one, inv_one, one_pow, one_mul, normSum_one_base]
      have hbb := Units.inv_mul Xb
      push_cast
      linear_combination ((Xb⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hb - (1 + (2 : ℤ_[2]) ^ α) * hbb
    · simp only [nCoeffB, Units.val_one, inv_one, one_pow, sub_self, mul_zero]
    · simp only [nCoeffC, Units.val_one, inv_one, one_pow, sub_self, mul_zero]
    · simp only [nCoeffD, Units.val_one, inv_one, one_pow, sub_self, mul_zero]

/-- **The `M_α` orientation exists**, with the memo's closed-form values `(1, −1, 1, u)`. -/
theorem isLabuteOrientationDatumM_mUnit {α : ℕ} (hα : 1 ≤ α) :
    IsLabuteOrientationDatumM α 1 (-1) 1 (mUnit α) :=
  (isLabuteOrientationDatumM_iff α 1 (-1) 1 (mUnit α)).mpr ⟨rfl, rfl, rfl, mUnit_mul hα⟩

/-- **The `N_α` orientation exists**, with the memo's closed-form values `(1, v, 1, 1)`. -/
theorem isLabuteOrientationDatumN_nUnit {α : ℕ} (hα : 1 ≤ α) :
    IsLabuteOrientationDatumN α 1 (nUnit α) 1 1 :=
  (isLabuteOrientationDatumN_iff α 1 (nUnit α) 1 1).mpr ⟨rfl, nUnit_mul hα, rfl, rfl⟩

/-- **Uniqueness of the `M_α` orientation datum** (memo V3: the descent system is *determined*;
no branch analysis and no Hensel uniqueness input is needed). -/
theorem isLabuteOrientationDatumM_unique {α : ℕ} (hα : 1 ≤ α) {Xa Xb Xc Xd : ℤ_[2]ˣ}
    (h : IsLabuteOrientationDatumM α Xa Xb Xc Xd) :
    Xa = 1 ∧ Xb = -1 ∧ Xc = 1 ∧ Xd = mUnit α := by
  obtain ⟨h1, h2, h3, h4⟩ := (isLabuteOrientationDatumM_iff α Xa Xb Xc Xd).mp h
  refine ⟨h1, h2, h3, Units.ext ?_⟩
  have hne : ((1 : ℤ_[2]) - 2 ^ α) ≠ 0 := by
    rw [← oneSubTwoPow_val hα]
    exact (oneSubTwoPow α).ne_zero
  exact mul_right_cancel₀ hne (h4.trans (mUnit_mul hα).symm)

/-- **Uniqueness of the `N_α` orientation datum**. -/
theorem isLabuteOrientationDatumN_unique {α : ℕ} (hα : 1 ≤ α) {Xa Xb Xc Xd : ℤ_[2]ˣ}
    (h : IsLabuteOrientationDatumN α Xa Xb Xc Xd) :
    Xa = 1 ∧ Xb = nUnit α ∧ Xc = 1 ∧ Xd = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := (isLabuteOrientationDatumN_iff α Xa Xb Xc Xd).mp h
  have hne : ((1 : ℤ_[2]) + 2 ^ α) ≠ 0 := by
    rw [← onePlusTwoPow_val hα]
    exact (onePlusTwoPow α).ne_zero
  exact ⟨h1, Units.ext (mul_right_cancel₀ hne (h2.trans (nUnit_mul hα).symm)), h3, h4⟩

end MarkedCore

end Dyadic

end GQ2
