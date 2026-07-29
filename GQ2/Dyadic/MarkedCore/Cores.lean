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

/-! ## §3 The presented cores `D_M`, `D_N`

Built exactly as `GQ2/Roe/DRPresentation.lean` builds `D_R` and `GQ2/DyadicPresentation.lean`
builds `D₀`: the relator as a word in the free profinite group on `Fin (coreRank h)`, the full
profinite presentation, then the **maximal pro-2 quotient** (the packet's `D_P` is pro-2, and
the bare presentation is not — its abelianization carries an odd part).

The presentation-level plumbing (topological generation, hom-extensionality, the universal
property) is relator-independent and is proved once, generically, in `§3.1`. -/

section Generic

variable {n : ℕ}

/-- The **one-relator pro-2 group** `⟨x₀, …, x_{n−1} | r⟩_{pro-2}` — the encoding used for
`D₀`, `D_R`, and both marked cores. -/
noncomputable def presPro2 (r : FreeProfiniteGroup (Fin n)) : ProfiniteGrp :=
  maxProPQuotient 2 (profinitePresentation {r})

/-- The marked generators of `presPro2 r`. -/
noncomputable def presGen (r : FreeProfiniteGroup (Fin n)) (i : Fin n) : presPro2 r :=
  maxProPMk 2 (profinitePresentation {r})
    (quotientMk (relatorSubgroup {r}) (FreeProfiniteGroup.of i))

/-- `presPro2 r` is pro-2. -/
theorem isProP_presPro2 (r : FreeProfiniteGroup (Fin n)) : IsProP 2 (presPro2 r : Type) :=
  isProP_maxProPQuotient

/-- The composite surjection `F_n ↠ presPro2 r`. -/
private noncomputable def presQ (r : FreeProfiniteGroup (Fin n)) :
    FreeProfiniteGroup (Fin n) →* (presPro2 r : Type) :=
  (maxProPMk 2 (profinitePresentation {r})).toMonoidHom.comp
    (quotientMk (relatorSubgroup {r})).toMonoidHom

private lemma presQ_of (r : FreeProfiniteGroup (Fin n)) (i : Fin n) :
    presQ r (FreeProfiniteGroup.of i) = presGen r i := rfl

private lemma continuous_presQ (r : FreeProfiniteGroup (Fin n)) : Continuous (presQ r) :=
  (maxProPMk 2 (profinitePresentation {r})).continuous_toFun.comp
    (quotientMk (relatorSubgroup {r})).continuous_toFun

private lemma presQ_surjective (r : FreeProfiniteGroup (Fin n)) :
    Function.Surjective (presQ r) :=
  (quotientMk_surjective (proPKernel 2 (profinitePresentation {r}))).comp
    (quotientMk_surjective (relatorSubgroup {r}))

/-- The free generators of a free profinite group on a `Fin n` topologically generate
(the `GQ2/Roe/DRAbelianization.lean:113` argument, stated at general rank). -/
theorem freeProfiniteFin_topGen (n : ℕ) :
    (Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := Fin n)))).topologicalClosure
      = ⊤ := by
  set g : FreeGroup (Fin n) →* FreeProfiniteGroup (Fin n) :=
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup (Fin n)))).hom with hg
  have hrange : Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := Fin n))) = g.range := by
    have h1 : Set.range (FreeProfiniteGroup.of (X := Fin n))
        = ⇑g '' Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  rw [hrange]
  have hdense : DenseRange g := ProfiniteGrp.ProfiniteCompletion.denseRange _
  rw [SetLike.ext'_iff]
  simpa only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, MonoidHom.coe_range]
    using hdense.closure_range

/-- **Topological generation** (the `dr_topGen` pattern): the marked generators topologically
generate `presPro2 r`. -/
theorem presPro2_topGen (r : FreeProfiniteGroup (Fin n)) :
    (Subgroup.closure (Set.range (presGen r))).topologicalClosure = ⊤ := by
  have himg : presQ r '' Set.range (FreeProfiniteGroup.of (X := Fin n)) = Set.range (presGen r) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => presQ_of r i)
  have := (presQ_surjective r).denseRange.topologicalClosure_map_subgroup (continuous_presQ r)
    (freeProfiniteFin_topGen n)
  rwa [MonoidHom.map_closure, himg] at this

/-- **Hom-extensionality** (the `dr_hom_ext` pattern): two continuous homs into a Hausdorff
topological group agreeing on the marked generators agree everywhere. -/
theorem presPro2_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] (r : FreeProfiniteGroup (Fin n))
    (φ ψ : ContinuousMonoidHom (presPro2 r : Type) A)
    (hgen : ∀ i, φ (presGen r i) = ψ (presGen r i)) : φ = ψ := by
  have hsub : Set.EqOn φ ψ (Subgroup.closure (Set.range (presGen r))) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hgen i
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, ha]
  have hdense : Dense ((Subgroup.closure (Set.range (presGen r))) : Set (presPro2 r : Type)) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, presPro2_topGen,
      Subgroup.coe_top]
  exact ContinuousMonoidHom.ext fun z =>
    (hsub.closure φ.continuous_toFun ψ.continuous_toFun) (hdense z)

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- The free continuous hom `F_n → H` determined by a marking. -/
noncomputable def freeHomFin (m : Fin n → H) :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin n)) H :=
  ((FreeProfiniteGroup.homEquiv (Fin n) (ProfiniteGrp.of H)).symm m).hom

omit [T2Space H] in
@[simp] theorem freeHomFin_of (m : Fin n → H) (i : Fin n) :
    freeHomFin m (FreeProfiniteGroup.of i) = m i :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- **Universal property of `presPro2 r`** (the `d0LiftHom`/`drLiftHom` clone): a marking of a
pro-2 group killing the relator classifies a continuous hom out of `presPro2 r`. -/
noncomputable def presLiftHom (r : FreeProfiniteGroup (Fin n)) (hH : IsProP 2 H)
    (m : Fin n → H) (hrel : freeHomFin m r = 1) :
    ContinuousMonoidHom (presPro2 r : Type) H :=
  (maxProPHomEquiv hH).symm
    (quotientLift (relatorSubgroup {r}) (freeHomFin m)
      (by
        refine Subgroup.topologicalClosure_minimal _
          (Subgroup.normalClosure_le_normal ?_) ?_
        · intro w hw
          rw [Set.mem_singleton_iff.mp hw, SetLike.mem_coe, MonoidHom.mem_ker]
          exact hrel
        · have hker : ((freeHomFin m).toMonoidHom.ker : Set (FreeProfiniteGroup (Fin n)))
              = ⇑(freeHomFin m) ⁻¹' {1} := by
            ext w
            simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
              Set.mem_singleton_iff]
            rfl
          rw [hker]
          exact isClosed_singleton.preimage (freeHomFin m).continuous_toFun))

@[simp] theorem presLiftHom_gen (r : FreeProfiniteGroup (Fin n)) (hH : IsProP 2 H)
    (m : Fin n → H) (hrel : freeHomFin m r = 1) (i : Fin n) :
    presLiftHom r hH m hrel (presGen r i) = m i := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 (profinitePresentation {r})
    (quotientMk (relatorSubgroup {r}) (FreeProfiniteGroup.of i))) = m i
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (freeHomFin_of m i)

end Generic

/-! ### §3.2 The two cores -/

/-- The **`M_α` relator** `A²[A,B]C₀^{2^α}[C₀,D]·∏[u_j,v_j]` as a word in
`FreeProfiniteGroup (Fin (coreRank h))`. -/
noncomputable def mRelator (α h : ℕ) : FreeProfiniteGroup (Fin (coreRank h)) :=
  mRelWord α FreeProfiniteGroup.of

/-- The **`N_α` relator** `x₀^{2+2^α}[x₀,x₁][σ,x₂]·∏[u_j,v_j]`. -/
noncomputable def nRelator (α h : ℕ) : FreeProfiniteGroup (Fin (coreRank h)) :=
  nRelWord α FreeProfiniteGroup.of

/-- **`D_{M,α,h}`** (memo §6.1 `DM`): the pro-2 group `⟨A, B, C₀, D, u, v | P_M(α)·∏[u_j,v_j]⟩`
of rank `coreRank h = 4 + 2h` (the memo's `n + 2`). -/
noncomputable def DM (α h : ℕ) : ProfiniteGrp := presPro2 (mRelator α h)

/-- **`D_{N,α,h}`** (memo §6.1 `DN`). -/
noncomputable def DN (α h : ℕ) : ProfiniteGrp := presPro2 (nRelator α h)

/-- The marked generators of `D_M` (the memo's `dmGen`). -/
noncomputable def dmGen (α h : ℕ) (i : Fin (coreRank h)) : DM α h := presGen (mRelator α h) i

/-- The marked generators of `D_N`. -/
noncomputable def dnGen (α h : ℕ) (i : Fin (coreRank h)) : DN α h := presGen (nRelator α h) i

/-- `A ∈ D_M`. -/
noncomputable def dmA (α h : ℕ) : DM α h := dmGen α h 0
/-- `B ∈ D_M`. -/
noncomputable def dmB (α h : ℕ) : DM α h := dmGen α h 1
/-- `C₀ ∈ D_M`. -/
noncomputable def dmC (α h : ℕ) : DM α h := dmGen α h 2
/-- `D ∈ D_M`. -/
noncomputable def dmD (α h : ℕ) : DM α h := dmGen α h 3

/-- `x₀ ∈ D_N` — the **marked** torsion generator of the `N`-frame (memo §3.1). -/
noncomputable def dnX0 (α h : ℕ) : DN α h := dnGen α h 0
/-- `x₁ ∈ D_N`. -/
noncomputable def dnX1 (α h : ℕ) : DN α h := dnGen α h 1
/-- `σ ∈ D_N`. -/
noncomputable def dnSigma (α h : ℕ) : DN α h := dnGen α h 2
/-- `x₂ ∈ D_N`. -/
noncomputable def dnX2 (α h : ℕ) : DN α h := dnGen α h 3

/-- `D_M` is pro-2. -/
theorem isProP_DM (α h : ℕ) : IsProP 2 (DM α h : Type) := isProP_presPro2 _

/-- `D_N` is pro-2. -/
theorem isProP_DN (α h : ℕ) : IsProP 2 (DN α h : Type) := isProP_presPro2 _

/-- The `M_α` relation already in the *full* profinite presentation. -/
private theorem mFull_relation (α h : ℕ) :
    mRelWord α (fun i => quotientMk (relatorSubgroup {mRelator α h})
      (FreeProfiniteGroup.of i)) = 1 := by
  have hr := relator_quotientMk_eq_one {mRelator α h} rfl
  rw [mRelator, map_mRelWord] at hr
  exact hr

/-- The `N_α` relation already in the *full* profinite presentation. -/
private theorem nFull_relation (α h : ℕ) :
    nRelWord α (fun i => quotientMk (relatorSubgroup {nRelator α h})
      (FreeProfiniteGroup.of i)) = 1 := by
  have hr := relator_quotientMk_eq_one {nRelator α h} rfl
  rw [nRelator, map_nRelWord] at hr
  exact hr

/-- **The `M_α` relation holds in `D_M`**. -/
theorem dm_relation (α h : ℕ) : mRelWord α (dmGen α h) = 1 := by
  have key := map_mRelWord (maxProPMk 2 (profinitePresentation {mRelator α h})) α
    (fun i => quotientMk (relatorSubgroup {mRelator α h}) (FreeProfiniteGroup.of i))
  rw [mFull_relation, map_one] at key
  exact key.symm

/-- **The `N_α` relation holds in `D_N`**. -/
theorem dn_relation (α h : ℕ) : nRelWord α (dnGen α h) = 1 := by
  have key := map_nRelWord (maxProPMk 2 (profinitePresentation {nRelator α h})) α
    (fun i => quotientMk (relatorSubgroup {nRelator α h}) (FreeProfiniteGroup.of i))
  rw [nFull_relation, map_one] at key
  exact key.symm

/-- **Topological generation of `D_M`** (memo §6.1 `dm_topGen`; the `dr_topGen` pattern). -/
theorem dm_topGen (α h : ℕ) :
    (Subgroup.closure (Set.range (dmGen α h))).topologicalClosure = ⊤ :=
  presPro2_topGen _

/-- **Topological generation of `D_N`**. -/
theorem dn_topGen (α h : ℕ) :
    (Subgroup.closure (Set.range (dnGen α h))).topologicalClosure = ⊤ :=
  presPro2_topGen _

/-- **Hom-extensionality for `D_M`** (memo §6.1 `dm_hom_ext`). -/
theorem dm_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    {α h : ℕ} (φ ψ : ContinuousMonoidHom (DM α h : Type) A)
    (hgen : ∀ i, φ (dmGen α h i) = ψ (dmGen α h i)) : φ = ψ :=
  presPro2_hom_ext _ φ ψ hgen

/-- **Hom-extensionality for `D_N`**. -/
theorem dn_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    {α h : ℕ} (φ ψ : ContinuousMonoidHom (DN α h : Type) A)
    (hgen : ∀ i, φ (dnGen α h i) = ψ (dnGen α h i)) : φ = ψ :=
  presPro2_hom_ext _ φ ψ hgen

section Lifts

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `D_M`** (memo §6.1 `mLiftHom`): a marking of a pro-2 group killing
the `M_α` relator word classifies a continuous hom `D_M → H`. -/
noncomputable def mLiftHom (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : mRelWord α m = 1) : ContinuousMonoidHom (DM α h : Type) H :=
  presLiftHom (mRelator α h) hH m (by
    have hm : (fun i => (freeHomFin m) (FreeProfiniteGroup.of i)) = m :=
      funext (freeHomFin_of m)
    rw [mRelator, map_mRelWord, hm]
    exact hrel)

/-- **Universal property of `D_N`** (memo §6.1 `nLiftHom`). -/
noncomputable def nLiftHom (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : nRelWord α m = 1) : ContinuousMonoidHom (DN α h : Type) H :=
  presLiftHom (nRelator α h) hH m (by
    have hm : (fun i => (freeHomFin m) (FreeProfiniteGroup.of i)) = m :=
      funext (freeHomFin_of m)
    rw [nRelator, map_nRelWord, hm]
    exact hrel)

@[simp] theorem mLiftHom_gen (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : mRelWord α m = 1) (i : Fin (coreRank h)) :
    mLiftHom α h hH m hrel (dmGen α h i) = m i := presLiftHom_gen _ _ _ _ _

@[simp] theorem nLiftHom_gen (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : nRelWord α m = 1) (i : Fin (coreRank h)) :
    nLiftHom α h hH m hrel (dnGen α h i) = m i := presLiftHom_gen _ _ _ _ _

end Lifts

/-! ## §4 The standard characters `χ_P`, `ν_P`

Both are built by the universal property (`mLiftHom`/`nLiftHom`) out of a **marking** that is
the four core values followed by `1` on every handle letter (the handle lemma of §2 says that
is forced for `χ`).  The relator check is the abelian collapse `mRelWord_comm`/`nRelWord_comm`,
since both targets are commutative. -/

/-! ### Index arithmetic for `Fin (coreRank h)` -/

theorem coreVal_zero (h : ℕ) : ((0 : Fin (coreRank h)) : ℕ) = 0 := by
  show 0 % coreRank h = 0
  exact Nat.zero_mod _

theorem coreVal_one (h : ℕ) : ((1 : Fin (coreRank h)) : ℕ) = 1 := by
  show 1 % coreRank h = 1
  exact Nat.mod_eq_of_lt (by simp only [coreRank]; omega)

theorem coreVal_two (h : ℕ) : ((2 : Fin (coreRank h)) : ℕ) = 2 := by
  show 2 % coreRank h = 2
  exact Nat.mod_eq_of_lt (by simp only [coreRank]; omega)

theorem coreVal_three (h : ℕ) : ((3 : Fin (coreRank h)) : ℕ) = 3 := by
  show 3 % coreRank h = 3
  exact Nat.mod_eq_of_lt (by simp only [coreRank]; omega)

theorem handleIdxU_val {h : ℕ} (j : Fin h) : ((handleIdxU j : Fin (coreRank h)) : ℕ)
    = 4 + 2 * j := rfl

theorem handleIdxV_val {h : ℕ} (j : Fin h) : ((handleIdxV j : Fin (coreRank h)) : ℕ)
    = 5 + 2 * j := rfl

/-- A handle block all of whose letters are trivial is trivial. -/
theorem handleWord_of_one {G : Type*} [Group G] {k : ℕ} (u v : Fin k → G)
    (hu : ∀ j, u j = 1) (hv : ∀ j, v j = 1) : handleWord u v = 1 := by
  rw [handleWord, List.prod_eq_one]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  rw [hu, hv, commP, inv_one, one_mul, one_mul, one_mul]

/-- **The standard marking shape**: four core values, `1` on every handle letter.  Every
character of a marked core built in this file has this shape (memo §4.2: the handle lemma
forces `χ ≡ 1` on the handle letters). -/
def coreMark {G : Type*} [Group G] {h : ℕ} (a b c d : G) : Fin (coreRank h) → G :=
  fun i =>
    if (i : ℕ) = 0 then a else
    if (i : ℕ) = 1 then b else
    if (i : ℕ) = 2 then c else
    if (i : ℕ) = 3 then d else 1

section CoreMark

variable {G : Type*} [Group G] {h : ℕ} (a b c d : G)

@[simp] theorem coreMark_zero : (coreMark (h := h) a b c d) 0 = a := by
  simp only [coreMark, coreVal_zero]
  norm_num

@[simp] theorem coreMark_one : (coreMark (h := h) a b c d) 1 = b := by
  simp only [coreMark, coreVal_one]
  norm_num

@[simp] theorem coreMark_two : (coreMark (h := h) a b c d) 2 = c := by
  simp only [coreMark, coreVal_two]
  norm_num

@[simp] theorem coreMark_three : (coreMark (h := h) a b c d) 3 = d := by
  simp only [coreMark, coreVal_three]
  norm_num

@[simp] theorem coreMark_handleU (j : Fin h) : coreMark a b c d (handleIdxU j) = 1 := by
  simp only [coreMark, handleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem coreMark_handleV (j : Fin h) : coreMark a b c d (handleIdxV j) = 1 := by
  simp only [coreMark, handleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The full relator on a standard marking is the core word: the handles are all trivial. -/
theorem mRelWord_coreMark (α : ℕ) : mRelWord α (coreMark (h := h) a b c d) = mWord α a b c d := by
  rw [mRelWord, coreMark_zero, coreMark_one, coreMark_two, coreMark_three,
    handleWord_of_one _ _ (fun j => coreMark_handleU a b c d j)
      (fun j => coreMark_handleV a b c d j), mul_one]

/-- The full `N`-relator on a standard marking is the core word. -/
theorem nRelWord_coreMark (α : ℕ) : nRelWord α (coreMark (h := h) a b c d) = nWord α a b c d := by
  rw [nRelWord, coreMark_zero, coreMark_one, coreMark_two, coreMark_three,
    handleWord_of_one _ _ (fun j => coreMark_handleU a b c d j)
      (fun j => coreMark_handleV a b c d j), mul_one]

end CoreMark

/-! ### The canonical orientations `χ_M`, `χ_N` -/

/-- **`χ_M : D_M → ℤ₂ˣ`** (memo §2.2(i)): the canonical Labute orientation of `M_α`, with the
closed-form generator values `(A, B, C₀, D) ↦ (1, −1, 1, u)`, `u = (1 − 2^α)⁻¹`, and `1` on
every handle letter. -/
noncomputable def chiM (α h : ℕ) : ContinuousMonoidHom (DM α h : Type) ℤ_[2]ˣ :=
  mLiftHom α h isProP_two_unitsPadicInt (coreMark 1 (-1) 1 (mUnit α)) (by
    rw [mRelWord_comm, coreMark_zero, coreMark_two, one_pow, one_pow, one_mul])

/-- **`χ_N : D_N → ℤ₂ˣ`** (memo §3.2(i)): generator values `(x₀, x₁, σ, x₂) ↦ (1, v, 1, 1)`,
`v = −(1 + 2^α)⁻¹`. -/
noncomputable def chiN (α h : ℕ) : ContinuousMonoidHom (DN α h : Type) ℤ_[2]ˣ :=
  nLiftHom α h isProP_two_unitsPadicInt (coreMark 1 (nUnit α) 1 1) (by
    rw [nRelWord_comm, coreMark_zero, one_pow])

@[simp] theorem chiM_dmA (α h : ℕ) : chiM α h (dmA α h) = 1 := by
  rw [dmA, chiM, mLiftHom_gen, coreMark_zero]
@[simp] theorem chiM_dmB (α h : ℕ) : chiM α h (dmB α h) = -1 := by
  rw [dmB, chiM, mLiftHom_gen, coreMark_one]
@[simp] theorem chiM_dmC (α h : ℕ) : chiM α h (dmC α h) = 1 := by
  rw [dmC, chiM, mLiftHom_gen, coreMark_two]
@[simp] theorem chiM_dmD (α h : ℕ) : chiM α h (dmD α h) = mUnit α := by
  rw [dmD, chiM, mLiftHom_gen, coreMark_three]
@[simp] theorem chiM_handleU (α h : ℕ) (j : Fin h) : chiM α h (dmGen α h (handleIdxU j)) = 1 := by
  rw [chiM, mLiftHom_gen, coreMark_handleU]
@[simp] theorem chiM_handleV (α h : ℕ) (j : Fin h) : chiM α h (dmGen α h (handleIdxV j)) = 1 := by
  rw [chiM, mLiftHom_gen, coreMark_handleV]

@[simp] theorem chiN_dnX0 (α h : ℕ) : chiN α h (dnX0 α h) = 1 := by
  rw [dnX0, chiN, nLiftHom_gen, coreMark_zero]
@[simp] theorem chiN_dnX1 (α h : ℕ) : chiN α h (dnX1 α h) = nUnit α := by
  rw [dnX1, chiN, nLiftHom_gen, coreMark_one]
@[simp] theorem chiN_dnSigma (α h : ℕ) : chiN α h (dnSigma α h) = 1 := by
  rw [dnSigma, chiN, nLiftHom_gen, coreMark_two]
@[simp] theorem chiN_dnX2 (α h : ℕ) : chiN α h (dnX2 α h) = 1 := by
  rw [dnX2, chiN, nLiftHom_gen, coreMark_three]
@[simp] theorem chiN_handleU (α h : ℕ) (j : Fin h) : chiN α h (dnGen α h (handleIdxU j)) = 1 := by
  rw [chiN, nLiftHom_gen, coreMark_handleU]
@[simp] theorem chiN_handleV (α h : ℕ) (j : Fin h) : chiN α h (dnGen α h (handleIdxV j)) = 1 := by
  rw [chiN, nLiftHom_gen, coreMark_handleV]

/-- **`χ_M` is the canonical Labute orientation** of the `M_α` core: its generator values form
a Labute orientation datum (memo §2.2(i)). -/
theorem chiM_isLabuteOrientationDatum {α : ℕ} (h : ℕ) (hα : 1 ≤ α) :
    IsLabuteOrientationDatumM α (chiM α h (dmA α h)) (chiM α h (dmB α h))
      (chiM α h (dmC α h)) (chiM α h (dmD α h)) := by
  rw [chiM_dmA, chiM_dmB, chiM_dmC, chiM_dmD]
  exact isLabuteOrientationDatumM_mUnit hα

/-- **`χ_N` is the canonical Labute orientation** of the `N_α` core (memo §3.2(i)). -/
theorem chiN_isLabuteOrientationDatum {α : ℕ} (h : ℕ) (hα : 1 ≤ α) :
    IsLabuteOrientationDatumN α (chiN α h (dnX0 α h)) (chiN α h (dnX1 α h))
      (chiN α h (dnSigma α h)) (chiN α h (dnX2 α h)) := by
  rw [chiN_dnX0, chiN_dnX1, chiN_dnSigma, chiN_dnX2]
  exact isLabuteOrientationDatumN_nUnit hα

/-! ### The unramified markings `ν_M`, `ν_N`

Packet normalisation `ν_P(σ) = 1`, `ν_P(x_i) = 0` (memo §6.1), with `σ` the **third** letter in
both memo namings (`C₀` for `M`, `σ` itself for `N`).  For `M` the `A`-value is *forced* by the
abelianized relation `2Ā + 2^αC̄₀ = 0`: `ν_M(A) = −m`, `m = 2^{α−1}` — memo §2.6 at `r = 0`,
where the free consistency check `ν(t) = ν(A) + mν(C₀) = 0` is exactly this equation.

**Deviation (recorded):** the memo writes the target as `Ztwo = maxProPQuotient 2 ℤ̂`
(`GQ2/BoundaryFrame.lean:162`, the `nuDR` pattern).  We land in `Multiplicative ℤ_[2]`, to which
`Ztwo` is continuously isomorphic by `ztwoEquivPadic` (`GQ2/ZtwoPowering.lean:302`); the
additive `ℤ₂`-form is what the frame computations of memo §2.6/§3.6 consume. -/

/-- **`ν_M : D_M → ℤ₂`** (memo §6.1, §2.6 at the compact row `r = 0`): `A ↦ −2^{α−1}`,
`B ↦ 0`, `C₀ ↦ 1`, `D ↦ 0`, handles `↦ 0`.  The `A`-value is forced by `2Ā + 2^αC̄₀ = 0`. -/
noncomputable def nuM (α h : ℕ) (hα : 1 ≤ α) :
    ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]) :=
  mLiftHom α h PropOneOne.isProP_two_multPadicInt
    (coreMark (ofAdd (-(2 : ℤ_[2]) ^ (α - 1))) (ofAdd 0) (ofAdd 1) (ofAdd 0)) (by
      obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
      rw [mRelWord_comm, coreMark_zero, coreMark_two,
        ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero]
      congr 1
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one, pow_succ]
      push_cast
      ring)

/-- **`ν_N : D_N → ℤ₂`** (memo §3.6, compact row `r = 0`): `x₀ ↦ 0`, `x₁ ↦ 0`, `σ ↦ 1`,
`x₂ ↦ 0`, handles `↦ 0`.  No forced row. -/
noncomputable def nuN (α h : ℕ) : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]) :=
  nLiftHom α h PropOneOne.isProP_two_multPadicInt
    (coreMark (ofAdd 0) (ofAdd 0) (ofAdd 1) (ofAdd 0)) (by
      rw [nRelWord_comm, coreMark_zero, ← ofAdd_nsmul, ← ofAdd_zero]
      congr 1
      simp)

@[simp] theorem nuM_dmA (α h : ℕ) (hα : 1 ≤ α) : nuM α h hα (dmA α h) = ofAdd (-(2 : ℤ_[2]) ^ (α - 1)) := by
  rw [dmA, nuM, mLiftHom_gen, coreMark_zero]
@[simp] theorem nuM_dmB (α h : ℕ) (hα : 1 ≤ α) : nuM α h hα (dmB α h) = ofAdd 0 := by
  rw [dmB, nuM, mLiftHom_gen, coreMark_one]
@[simp] theorem nuM_dmC (α h : ℕ) (hα : 1 ≤ α) : nuM α h hα (dmC α h) = ofAdd 1 := by
  rw [dmC, nuM, mLiftHom_gen, coreMark_two]
@[simp] theorem nuM_dmD (α h : ℕ) (hα : 1 ≤ α) : nuM α h hα (dmD α h) = ofAdd 0 := by
  rw [dmD, nuM, mLiftHom_gen, coreMark_three]

@[simp] theorem nuN_dnX0 (α h : ℕ) : nuN α h (dnX0 α h) = ofAdd 0 := by
  rw [dnX0, nuN, nLiftHom_gen, coreMark_zero]
@[simp] theorem nuN_dnX1 (α h : ℕ) : nuN α h (dnX1 α h) = ofAdd 0 := by
  rw [dnX1, nuN, nLiftHom_gen, coreMark_one]
@[simp] theorem nuN_dnSigma (α h : ℕ) : nuN α h (dnSigma α h) = ofAdd 1 := by
  rw [dnSigma, nuN, nLiftHom_gen, coreMark_two]
@[simp] theorem nuN_dnX2 (α h : ℕ) : nuN α h (dnX2 α h) = ofAdd 0 := by
  rw [dnX2, nuN, nLiftHom_gen, coreMark_three]

/-- **The `ν(t) = 0` consistency check for `M`** (memo §2.6): the torsion generator
`t = A·C₀^{2^{α−1}}` of the `M`-frame has `ν_M(t) = ν_M(A) + 2^{α−1}·ν_M(C₀) = 0`, as it must
(`t` is torsion and `ℤ₂` is torsion-free).  This is a free check on the whole change of
variables, and it passes. -/
theorem nuM_torsionGen (α h : ℕ) (hα : 1 ≤ α) :
    nuM α h hα (dmA α h * dmC α h ^ (2 ^ (α - 1))) = 1 := by
  rw [map_mul, map_pow, nuM_dmA, nuM_dmC, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero]
  congr 1
  simp

/-! ## §6 The exponent / normal-form lemma  (memo §4.1(2), risk R2)

The rank-three cup Gram is proved by `revert v w; decide` — a finite evaluation of the relator
in a 16-element central extension over all 64 coordinate pairs (`drRelZ_drCC`,
`GQ2/Roe/DRDemushkin.lean:339`).  **With a relator exponent `2^α` that is not a finite check**,
so the memo budgets an *exponent lemma* instead.  This section supplies it, stated at the level
of exponents and words — not per core — so that the five branch-word tickets can reuse it:

* `diagCoeff k = C(k,2) mod 2` is the fibre contribution of a `k`-th power, and
  **`diagCoeff` depends only on `k mod 4`** (`diagCoeff_mod_four`) — the memo's mod-4 diagonal
  rule.  Hence `diagCoeff (2^α) = 0` for `α ≥ 2` (no `C₀`-diagonal) and
  `diagCoeff (2 + 2^α) = 1` (an `x₀`-diagonal), exactly memo §2.2(iii)/§3.2(iii);
* `centLift_pow_fib` is the group-level companion: in a central extension of an elementary
  abelian group, `x^k` contributes `diagCoeff k · κ(x,x)` to the fibre;
* `commP_centLift_fib` is the hyperbolic companion: `[x,y]` contributes `κ(x,y) + κ(y,x)`;
* `mWord_centLift_fib` / `nWord_centLift_fib` / `mRelWord_centLift_fib` assemble them into the
  **α-independent Gram value** `[[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]` (⊕ handle
  hyperbolics), for **both** cores in their own bases (memo V4).

The generic central-extension algebra is `GQ2.DRCoh` (`GQ2/Roe/DRWordCoh.lean:51–140`), which is
generic in the base group `L`; only its `relZ`/`obsH2` layer is `D_R`-specific. -/

/-! ### The mod-4 diagonal exponent rule -/

/-- **The diagonal exponent coefficient** `C(k,2) mod 2`: the number of "carries" that a `k`-th
power contributes to the central fibre of a class-two extension. -/
def diagCoeff (k : ℕ) : ZMod 2 := (k.choose 2 : ℕ)

@[simp] theorem diagCoeff_zero : diagCoeff 0 = 0 := by simp [diagCoeff]
@[simp] theorem diagCoeff_one : diagCoeff 1 = 0 := by simp [diagCoeff]
@[simp] theorem diagCoeff_two : diagCoeff 2 = 1 := by simp [diagCoeff]

/-- Pascal's rule for the diagonal coefficient: `C(k+1,2) = C(k,2) + k`. -/
theorem diagCoeff_succ (k : ℕ) : diagCoeff (k + 1) = diagCoeff k + (k : ZMod 2) := by
  simp only [diagCoeff, Nat.choose_succ_succ k 1, Nat.choose_one_right, Nat.cast_add]
  ring

/-- **Period four**: `C(k+4,2) ≡ C(k,2) (mod 2)` (the difference is `4k + 6`). -/
theorem diagCoeff_add_four (k : ℕ) : diagCoeff (k + 4) = diagCoeff k := by
  have h : ∀ j : ℕ, diagCoeff (j + 1) = diagCoeff j + (j : ZMod 2) := diagCoeff_succ
  rw [show k + 4 = k + 1 + 1 + 1 + 1 by ring, h, h, h, h]
  push_cast
  ring_nf
  rw [show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide]
  ring

private theorem diagCoeff_add_four_mul (k q : ℕ) : diagCoeff (k + 4 * q) = diagCoeff k := by
  induction q with
  | zero => simp
  | succ n ih => rw [show k + 4 * (n + 1) = k + 4 * n + 4 by ring, diagCoeff_add_four, ih]

/-- **The mod-4 diagonal exponent rule** (memo §2.2(iii), §4.1(2)) — the reusable replacement
for the rank-three `decide`: the diagonal (Bockstein) contribution of an exponent `k` depends
only on `k mod 4`.  Concretely `k ≡ 0, 1 (mod 4)` contributes `0` and `k ≡ 2, 3 (mod 4)`
contributes `1`. -/
theorem diagCoeff_mod_four (k : ℕ) : diagCoeff k = diagCoeff (k % 4) := by
  conv_lhs => rw [← Nat.mod_add_div k 4]
  rw [diagCoeff_add_four_mul]

/-- **`2^α` contributes no diagonal entry for `α ≥ 2`** (`2^α ≡ 0 mod 4`) — memo §2.2(iii):
this is why `G_M` has no `C₀`-diagonal, uniformly in `α`. -/
theorem diagCoeff_two_pow {α : ℕ} (hα : 2 ≤ α) : diagCoeff (2 ^ α) = 0 := by
  have h4 : 2 ^ α % 4 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 from rfl]
    exact Nat.mul_mod_left _ _
  rw [diagCoeff_mod_four, h4, diagCoeff_zero]

/-- **`2 + 2^α` contributes a diagonal entry for `α ≥ 2`** (`2 + 2^α ≡ 2 mod 4`) — memo
§3.2(iii): this is the `x₀`-Bockstein of `G_N`, uniformly in `α`. -/
theorem diagCoeff_two_add_two_pow {α : ℕ} (hα : 2 ≤ α) : diagCoeff (2 + 2 ^ α) = 1 := by
  have h4 : (2 + 2 ^ α) % 4 = 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 from rfl, Nat.add_mul_mod_self_right]
  rw [diagCoeff_mod_four, h4, diagCoeff_two]

/-! ### The central extension: lifts, powers, commutators -/

section CentExt

open DRCoh

variable {L : Type*} [Group L] {c : DRCoh.TwoCocycle L}

/-- The **offset-zero lift** of a group element into the central extension (the `drLift`
pattern, `GQ2/Roe/DRWordCoh.lean:402`). -/
def centLift (c : DRCoh.TwoCocycle L) (x : L) : DRCoh.CentExt c := (x, 0)

@[simp] theorem centLift_base (x : L) : (centLift c x).base = x := rfl
@[simp] theorem centLift_fib (x : L) : (centLift c x).fib = 0 := rfl

theorem centExt_one_base : (1 : DRCoh.CentExt c).base = 1 := rfl
theorem centExt_one_fib : (1 : DRCoh.CentExt c).fib = 0 := rfl
theorem centExt_inv_base (p : DRCoh.CentExt c) : p⁻¹.base = p.base⁻¹ := rfl
theorem centExt_inv_fib (p : DRCoh.CentExt c) :
    p⁻¹.fib = p.fib + c.κ p.base p.base⁻¹ := rfl

/-- The base coordinate is multiplicative on powers (`proj` is a homomorphism). -/
theorem centExt_pow_base (p : DRCoh.CentExt c) (k : ℕ) : (p ^ k).base = p.base ^ k :=
  map_pow (DRCoh.CentExt.proj c) p k

/-- **Fibres add across a factor with trivial base** — the reason the relator's fibre is the
plain sum of its factors' fibres (every factor of `P_M`, `P_N` has trivial base in the
elementary abelian quotient). -/
theorem fib_mul_of_base_one {p q : DRCoh.CentExt c} (hp : p.base = 1) :
    (p * q).fib = p.fib + q.fib := by
  rw [DRCoh.CentExt.mul_fib, hp, c.κ_one_left, add_zero]

private theorem base_mul_eq_one {p q : DRCoh.CentExt c} (hp : p.base = 1) (hq : q.base = 1) :
    (p * q).base = 1 := by rw [DRCoh.CentExt.mul_base, hp, hq, one_mul]

/-- **Fibres add across a list of trivial-base factors.** -/
theorem prod_fib_of_bases_one (l : List (DRCoh.CentExt c)) (hl : ∀ p ∈ l, p.base = 1) :
    l.prod.fib = (l.map DRCoh.CentExt.fib).sum := by
  induction l with
  | nil => exact centExt_one_fib
  | cons p t ih =>
      rw [List.prod_cons, fib_mul_of_base_one (hl p (List.mem_cons_self ..)),
        ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)), List.map_cons, List.sum_cons]

/-- **The exponent rule** (memo §4.1(2)): in a central extension, the `k`-th power of an
offset-zero lift contributes exactly `C(k,2)·κ(x,x)` to the fibre, provided `κ(x^i, x)` is
linear in `i` along `⟨x⟩` (automatic for a cup cocycle, `IsCupCocycle` below).  Combined with
`diagCoeff_mod_four` this is the **α-uniform** replacement for the rank-three `decide`. -/
theorem centLift_pow_fib {x : L} (hx : ∀ i : ℕ, c.κ (x ^ i) x = (i : ZMod 2) * c.κ x x)
    (k : ℕ) : ((centLift c x) ^ k).fib = diagCoeff k * c.κ x x := by
  induction k with
  | zero => rw [pow_zero, centExt_one_fib, diagCoeff_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, DRCoh.CentExt.mul_fib, ih, centLift_fib, centExt_pow_base, centLift_base,
        hx n, diagCoeff_succ]
      ring

/-- **The commutator rule, raw form**: the fibre of `[x, y]` at offset-zero lifts, in terms of
five `κ`-values. -/
theorem commP_centLift_fib (x y : L) :
    (commP (centLift c x) (centLift c y)).fib
      = c.κ x x⁻¹ + c.κ y y⁻¹ + c.κ x⁻¹ y⁻¹ + c.κ (x⁻¹ * y⁻¹) x
        + c.κ (x⁻¹ * y⁻¹ * x) y := by
  simp only [commP, DRCoh.CentExt.mul_fib, DRCoh.CentExt.mul_base, centExt_inv_base,
    centExt_inv_fib, centLift_base, centLift_fib, zero_add]
  ring

end CentExt

/-! ### The cup-cocycle hypotheses and the two Gram computations -/

/-- The hypotheses under which the §6 Gram computation runs: the base group is **elementary
abelian** (the mod-2 Frattini quotient of the core) and the cocycle is **bi-additive** — the
shape of a cup cocycle `κ(a, b) = ⟨v, a⟩·⟨w, b⟩` (the rank-three `drCC`,
`GQ2/Roe/DRDemushkin.lean:272`). -/
structure IsCupCocycle {L : Type*} [Group L] (c : DRCoh.TwoCocycle L) : Prop where
  /-- The base group is abelian. -/
  comm : ∀ z w : L, z * w = w * z
  /-- The base group has exponent two. -/
  expTwo : ∀ z : L, z * z = 1
  /-- `κ` is additive in its first argument. -/
  addLeft : ∀ z w t : L, c.κ (z * w) t = c.κ z t + c.κ w t
  /-- `κ` is additive in its second argument. -/
  addRight : ∀ z w t : L, c.κ z (w * t) = c.κ z w + c.κ z t

namespace IsCupCocycle

open DRCoh

variable {L : Type*} [Group L] {c : DRCoh.TwoCocycle L} (hc : IsCupCocycle c)
include hc

theorem inv_eq (z : L) : z⁻¹ = z := by
  rw [inv_eq_iff_mul_eq_one]; exact hc.expTwo z

theorem pow_two_eq_one (z : L) : z ^ 2 = 1 := by rw [pow_two]; exact hc.expTwo z

theorem pow_even_eq_one (z : L) (k : ℕ) : z ^ (2 * k) = 1 := by
  rw [pow_mul, hc.pow_two_eq_one, one_pow]

/-- Linearity of `κ` along a procyclic subgroup — the hypothesis of `centLift_pow_fib`. -/
theorem kappa_pow_left (x : L) (i : ℕ) : c.κ (x ^ i) x = (i : ZMod 2) * c.κ x x := by
  induction i with
  | zero => rw [pow_zero, c.κ_one_left, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, hc.addLeft, ih, Nat.cast_add, Nat.cast_one]; ring

/-- **The hyperbolic (commutator) contribution**: `[x, y]` contributes `κ(x,y) + κ(y,x)` to the
fibre — the off-diagonal entries of the cup Gram. -/
theorem commP_fib (x y : L) :
    (commP (centLift c x) (centLift c y)).fib = c.κ x y + c.κ y x := by
  have hxy : x * y * x = y := by rw [hc.comm x y, mul_assoc, hc.expTwo, mul_one]
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  rw [commP_centLift_fib, hc.inv_eq, hc.inv_eq, hxy, hc.addLeft]
  linear_combination h2 (c.κ x x) + h2 (c.κ y y)

theorem commP_base (x y : L) : (commP (centLift c x) (centLift c y)).base = 1 := by
  have hxy : x * y * x = y := by rw [hc.comm x y, mul_assoc, hc.expTwo, mul_one]
  show commP x y = 1
  rw [commP, hc.inv_eq, hc.inv_eq, hxy, hc.expTwo]

theorem pow_even_base (x : L) (k : ℕ) : ((centLift c x) ^ (2 * k)).base = 1 := by
  rw [centExt_pow_base, centLift_base, hc.pow_even_eq_one]

/-- **The `M_α` Gram value** (memo §2.2(iii)) — the α-independent matrix
`[[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]`: the square `a²` gives the diagonal Bockstein,
`[a,b]` and `[c,d]` the two hyperbolic pairs, and `c^{2^α}` gives **nothing** because
`2^α ≡ 0 (mod 4)` for `α ≥ 2` (`diagCoeff_two_pow`). -/
theorem mWord_centLift_fib {α : ℕ} (hα : 2 ≤ α) (a b d e : L) :
    (mWord α (centLift c a) (centLift c b) (centLift c d) (centLift c e)).fib
      = c.κ a a + (c.κ a b + c.κ b a) + (c.κ d e + c.κ e d) := by
  have hsq : ((centLift c a) ^ 2).base = 1 := hc.pow_even_base a 1
  have hpow : ((centLift c d) ^ (2 ^ α)).base = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ α = 2 * k := ⟨2 ^ (α - 1), by
      obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; ring⟩
    rw [hk]; exact hc.pow_even_base d k
  rw [mWord, fib_mul_of_base_one (base_mul_eq_one (base_mul_eq_one hsq (hc.commP_base a b)) hpow),
    fib_mul_of_base_one (base_mul_eq_one hsq (hc.commP_base a b)),
    fib_mul_of_base_one hsq,
    centLift_pow_fib (hc.kappa_pow_left a), centLift_pow_fib (hc.kappa_pow_left d),
    hc.commP_fib, hc.commP_fib, diagCoeff_two, diagCoeff_two_pow hα, one_mul, zero_mul]
  ring

/-- **The `N_α` Gram value** (memo §3.2(iii)) — the *same* matrix in its own basis: here the
diagonal comes from `x₀^{2+2^α}` because `2 + 2^α ≡ 2 (mod 4)`
(`diagCoeff_two_add_two_pow`). -/
theorem nWord_centLift_fib {α : ℕ} (hα : 2 ≤ α) (a b d e : L) :
    (nWord α (centLift c a) (centLift c b) (centLift c d) (centLift c e)).fib
      = c.κ a a + (c.κ a b + c.κ b a) + (c.κ d e + c.κ e d) := by
  have hpow : ((centLift c a) ^ (2 + 2 ^ α)).base = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, 2 + 2 ^ α = 2 * k := ⟨1 + 2 ^ (α - 1), by
      obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; ring⟩
    rw [hk]; exact hc.pow_even_base a k
  rw [nWord, fib_mul_of_base_one (base_mul_eq_one hpow (hc.commP_base a b)),
    fib_mul_of_base_one hpow,
    centLift_pow_fib (hc.kappa_pow_left a), hc.commP_fib, hc.commP_fib,
    diagCoeff_two_add_two_pow hα, one_mul]

/-- **The handle contribution**: each hyperbolic handle adds its own off-diagonal pair. -/
theorem handleWord_centLift_fib {k : ℕ} (u v : Fin k → L) :
    (handleWord (fun j => centLift c (u j)) (fun j => centLift c (v j))).fib
      = ∑ j, (c.κ (u j) (v j) + c.κ (v j) (u j)) := by
  rw [handleWord, prod_fib_of_bases_one, List.map_map, Fin.sum_univ_def]
  · congr 1
    refine List.map_congr_left fun j _ => ?_
    exact hc.commP_fib (u j) (v j)
  · intro p hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    exact hc.commP_base (u j) (v j)

/-- **The full `M_α` relator Gram value**, handles included — the memo's `G_M ⊕ (h hyperbolic
blocks)`, α-independent. -/
theorem mRelWord_centLift_fib {α h : ℕ} (hα : 2 ≤ α) (m : Fin (coreRank h) → L) :
    (mRelWord α (fun i => centLift c (m i))).fib
      = c.κ (m 0) (m 0) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  have hbase : (mWord α (centLift c (m 0)) (centLift c (m 1)) (centLift c (m 2))
      (centLift c (m 3))).base = 1 := by
    have hsq : ((centLift c (m 0)) ^ 2).base = 1 := hc.pow_even_base (m 0) 1
    have hpow : ((centLift c (m 2)) ^ (2 ^ α)).base = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ α = 2 * k := ⟨2 ^ (α - 1), by
        obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]; ring⟩
      rw [hk]; exact hc.pow_even_base (m 2) k
    exact base_mul_eq_one (base_mul_eq_one (base_mul_eq_one hsq (hc.commP_base _ _)) hpow)
      (hc.commP_base _ _)
  rw [mRelWord, fib_mul_of_base_one hbase, hc.mWord_centLift_fib hα,
    hc.handleWord_centLift_fib]

/-- **The full `N_α` relator Gram value**, handles included. -/
theorem nRelWord_centLift_fib {α h : ℕ} (hα : 2 ≤ α) (m : Fin (coreRank h) → L) :
    (nRelWord α (fun i => centLift c (m i))).fib
      = c.κ (m 0) (m 0) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  have hbase : (nWord α (centLift c (m 0)) (centLift c (m 1)) (centLift c (m 2))
      (centLift c (m 3))).base = 1 := by
    have hpow : ((centLift c (m 0)) ^ (2 + 2 ^ α)).base = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, 2 + 2 ^ α = 2 * k := ⟨1 + 2 ^ (α - 1), by
        obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]; ring⟩
      rw [hk]; exact hc.pow_even_base (m 0) k
    exact base_mul_eq_one (base_mul_eq_one hpow (hc.commP_base _ _)) (hc.commP_base _ _)
  rw [nRelWord, fib_mul_of_base_one hbase, hc.nWord_centLift_fib hα,
    hc.handleWord_centLift_fib]

end IsCupCocycle

end MarkedCore

end Dyadic

end GQ2
