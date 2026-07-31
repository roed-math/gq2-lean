/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.M
public import GQ2.Dyadic.MarkedCore.N

@[expose] public section

/-!
# MC-VAR: the cup-isometry variance dictionary between the `M`- and `N`-cores

**Ticket MC-VAR** of the dyadic campaign (lane MC) — the adjudication of the apparent
*variance discrepancy* between MC3 (`M.lean`) and MC4 (`N.lean`), which state the mod-2
cup-isometry clause of the Smith–Witt stabilizer with opposite-looking transposes:

* `M.lean` (`IsMStabilizer`, §4): `M̄ᵀ · G_M · M̄ = G_M`;
* `N.lean` (`NRows.IsCupIsometry`, §4): `M̄ · G_N · M̄ᵀ = G_N`.

**Verdict: the two are the same condition.**  There is no variance disagreement — the two
files store the frame endomorphism in transposed layouts, and each pairs its layout with the
matching transpose:

* `mFrameMatrix B ξ i j` is the `j`-th coordinate of the image of the `i`-th frame vector, so
  its **rows** are the images (`M.lean:825–835`);
* `NRows.mat R i j = nMod2 (R.col j) i` is the `i`-th coordinate of the image of the `j`-th
  basis vector, so its **columns** are the images (`N.lean:837–839`).

Writing `A` for the column-layout matrix (`N.lean`'s) and `M̄ = Aᵀ` for the row-layout one
(`M.lean`'s), both clauses read `A · G · Aᵀ = G`.  `mCupIsometry_iff_nCupForm` and
`nCupForm_iff_mul_transpose` are that dictionary; `mFrameMatrix_transpose_eq_nMatOf` is its
sharpest instance — the transpose of `M.lean`'s frame matrix at a classified parameter is
**literally** an `N.lean` `nMatOf`, with `N`-parameters read off the `M`-parameters.

## Which condition is correct, from the repo's own cup semantics

`Cores.lean`'s `IsCupCocycle` layer fixes the semantics: a cup cocycle is `κ(a, b) = ⟨v,a⟩·⟨w,b⟩`
for **covectors** `v, w ∈ H¹` (`Cores.lean:1333–1336`), and the relator's fibre value
(`mRelWord_centLift_fib`, `nRelWord_centLift_fib`) is `v₀w₀ + (v₀w₁ + v₁w₀) + (v₂w₃ + v₃w₂) + …`
— i.e. exactly `nCupForm v w`.  So `nCupForm` eats **`H¹` covectors in the dual basis**, and the
Gram is the Gram in that dual basis (as `Rank3.lean:209` also states for `sqCore_cupGram`).

An automorphism `φ` acts on `H¹` by precomposition: if `φ̄(e_j) = Σ_i A_{ij} e_i` on `H₁`, then
`φ*(x_i) = Σ_j A_{ij} x_j`, so the coordinate vector of `φ*(x_i)` is **row `i` of `A`**.  Hence

```text
φ preserves the cup form  ⟺  ∀ i j, ⟨φ*(x_i), φ*(x_j)⟩ = ⟨x_i, x_j⟩  ⟺  A · G · Aᵀ = G,
```

which is `N.lean`'s clause verbatim on `NRows.mat`, and `M.lean`'s clause verbatim on `M̄ = Aᵀ`.
Both files are right.

## The two counterexample claims

Both hold, in each file's own layout, and they are the **same** counterexample seen twice: the
`τ`-parameter of family M1 (`B ↦ A^k·B`, `mLambdaEquiv`) and of family N1 (`x₁ ↦ x₀^k·x₁`,
`dnTauBEquiv`) — both honest, exact, axiom-free automorphisms.

* `mFrameMatrix_cupIsometry` — in `M.lean`'s layout, every classified parameter is an isometry,
  `τ` unconstrained; `mFrameMatrix_flip_forces_tau` — the flipped clause forces `τ = 0`.
* `nMatOf_famN1_cupIsometry` — in `N.lean`'s layout, family N1 is an isometry for every `τ`;
  `nMatOf_transpose_cup_forces_tau` — the flipped clause forces `τ = 0`.
* `nMatOf_famN1_variance_differs` — one matrix satisfying one variance and refuting the other,
  so the distinction is real and not an artifact of the presentation.

## What MC5 must know

The `Prop`s are interchangeable; the **matrices are not**.  A frame endomorphism has two
matrices, transposes of each other, and every consumer must say which it holds:

| object | layout | side |
|---|---|---|
| `mFrameMatrix B ξ` (`M.lean`) | rows = images | `H₁` (row-vector action) |
| `NRows.mat R` (`N.lean`), `nMatOf` | columns = images | `H₁` (column-vector action) |
| `MStabParam.act` (`M.lean`) | — | `H₁` frame coordinate vectors |
| `NStabParam.nuAction`, `nCoreMat T` (`N.lean`) | — | `H¹` ν-frame vectors, so `T = gᵀ` |

`NStabParam.nuAction`'s `nCoreMat P.g.transpose` is the same phenomenon on the lifted side and
is already correct as written (`N.lean:1706–1712`).

## Axiom hygiene

Every declaration here is std-3 (`propext`, `Classical.choice`, `Quot.sound`); no census axiom,
no new binder, no `sorry`.  Census unchanged at 11.
-/

open Multiplicative

namespace GQ2

namespace Dyadic

namespace MarkedCore

/-! ## §1 The dictionary

Pure `𝔽₂` linear algebra on the shared Gram: transposing the matrix exchanges the two clauses. -/

section Dictionary

/-- The two cores' Gram matrices are **the same** `𝔽₂`-matrix — `mGram` as a `Matrix` and `nGram`
as a bare `Fin 4 → Fin 4 → ZMod 2` (memo §2.2(iii) = §3.2(iii), MC2's `mWord_centLift_fib` and
`nWord_centLift_fib` deliver the same value in each core's own basis). -/
theorem mGram_eq_nGram : mGram = Matrix.of nGram := rfl

/-- **The bridge identity.**  The `(i,j)` entry of `M̄ᵀ·G·M̄` is the cup pairing of the `i`-th and
`j`-th **columns** of `M̄`, i.e. of the `i`-th and `j`-th rows of `M̄ᵀ`.  (`M.lean`'s
`mCupIsometry_entry` is this at `M̄ = mFrameMatrix B ξ`, written out in terms of `M̄`'s rows.) -/
theorem nCupForm_transpose_eq (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    nCupForm (M.transpose i) (M.transpose j) = (M.transpose * mGram * M) i j := by
  simp only [nCupForm, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, mGram_00,
    mGram_01, mGram_02, mGram_03, mGram_10, mGram_11, mGram_12, mGram_13, mGram_20, mGram_21,
    mGram_22, mGram_23, mGram_30, mGram_31, mGram_32, mGram_33]
  ring

/-- **The dictionary, `M`-side reading.**  `M.lean`'s clause on `M̄` is `N.lean`'s clause on the
rows of `M̄ᵀ`.  This is the lemma MC5 cites to move a hypothesis from one file's vocabulary to
the other's. -/
theorem mCupIsometry_iff_nCupForm (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    M.transpose * mGram * M = mGram
      ↔ ∀ i j, nCupForm (M.transpose i) (M.transpose j) = nGram i j := by
  constructor
  · intro h i j
    rw [nCupForm_transpose_eq, h]
    rfl
  · intro h
    ext i j
    rw [← nCupForm_transpose_eq, h]
    rfl

/-- **The dictionary, `N`-side reading.**  `N.lean`'s clause on a matrix `A` whose *rows* are the
pullback covectors is the matrix equation `A·G·Aᵀ = G`. -/
theorem nCupForm_iff_mul_transpose (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    (∀ i j, nCupForm (A i) (A j) = nGram i j) ↔ A * mGram * A.transpose = mGram := by
  have h := mCupIsometry_iff_nCupForm A.transpose
  rw [Matrix.transpose_transpose] at h
  exact h.symm

/-- `N.lean`'s cup clause on a frame endomorphism, as a matrix equation. -/
theorem nRows_isCupIsometry_iff (R : NRows) :
    R.IsCupIsometry ↔ Matrix.of R.mat * mGram * (Matrix.of R.mat).transpose = mGram :=
  nCupForm_iff_mul_transpose _

/-- **`N.lean`'s cup clause is `M.lean`'s cup clause on the transposed matrix.**  Both sides are
the same equation; the statement exists so that a consumer holding one can produce the other by
`rw` rather than by re-deriving it. -/
theorem nRows_isCupIsometry_iff_mStyle (R : NRows) :
    R.IsCupIsometry ↔
      (Matrix.of R.mat).transpose.transpose * mGram * (Matrix.of R.mat).transpose = mGram := by
  rw [Matrix.transpose_transpose, nRows_isCupIsometry_iff]

end Dictionary

/-! ## §2 The `M`-side frame matrix, transposed, is an `N`-side `nMatOf`

The concrete half of the dictionary, on the objects the two tickets actually built. -/

section FrameMatrix

variable {α : ℕ}

/-- **The four rows of `M.lean`'s frame matrix at a classified parameter.**  `β` and `γ` are units
so their parities are `1`; the `B̄`-components of `φ(C̄₀)` and `φ(D̄)` are even so theirs are `0`;
the `t`-row is `mXi_fixes_t`. -/
theorem mFrameMatrix_of_realizes (hα : 1 ≤ α) (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) {p : MStabParam} (hp : p.Realizes B ξ) :
    mFrameMatrix B ξ = Matrix.of ![![1, 0, 0, 0], ![p.tau, 1, mParityZ p.bc, 0],
      ![0, 0, 1, 0], ![mParityZ p.bc, 0, mParityZ p.e, 1]] := by
  have h0 : ∀ j, mFrameMatrix B ξ 0 j = ![(1 : ZMod 2), 0, 0, 0] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_zero, mXi_fixes_t hα B ξ, B.map_t]
    fin_cases j <;> simp [mRedTwo]
  have h1 : ∀ j, mFrameMatrix B ξ 1 j = ![p.tau, 1, mParityZ p.bc, 0] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_one, hp.1]
    fin_cases j <;> simp [mRedTwo, mParityZ_of_isUnit p.beta.isUnit]
  have h2 : ∀ j, mFrameMatrix B ξ 2 j = ![(0 : ZMod 2), 0, 1, 0] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_two, hp.2.1]
    fin_cases j <;> simp [mRedTwo, mParityZ_of_isUnit p.gamma.isUnit]
  have h3 : ∀ j, mFrameMatrix B ξ 3 j = ![mParityZ p.bc, 0, mParityZ p.e, 1] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_three, hp.2.2]
    fin_cases j <;> simp [mRedTwo]
  ext i j
  fin_cases i
  · exact h0 j
  · exact h1 j
  · exact h2 j
  · exact h3 j

/-- **The two cores' matrices are transposes of one shape.**  The transpose of `M.lean`'s frame
matrix at a classified parameter `p` is *literally* an `N.lean` `nMatOf`, at the reduced
parameters `(τ, τ_σ, τ_{x₂}, p, q, g₁, g₂, h₁, h₂) = (τ, 0, B̄_c, B̄_c, 0, 1, ē, 0, 1)`.  This is
the cross-file evidence that the two tickets classified the same object in transposed layouts:
`M.lean`'s Witt coupling `t`-component of `φ(D̄) = B_c mod 2` is `N.lean`'s coupling
`p̄ = τ_{x₂}·ḡ₁ + τ_σ·ḡ₂`, and `M.lean`'s unit `γ` is `N.lean`'s `det ḡ = 1`. -/
theorem mFrameMatrix_transpose_eq_nMatOf (hα : 1 ≤ α) (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) {p : MStabParam} (hp : p.Realizes B ξ) :
    (mFrameMatrix B ξ).transpose
      = Matrix.of (nMatOf p.tau 0 (mParityZ p.bc) (mParityZ p.bc) 0 1 (mParityZ p.e) 0 1) := by
  rw [mFrameMatrix_of_realizes hα B ξ hp]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Soundness in `M.lean`'s variance** — the converse of `mStabilizer_classification`'s Witt
half: every classified parameter really is an isometry, with `τ` unconstrained.  Proved through
the dictionary and `N.lean`'s `𝔽₂` decision procedure `nCup_iff_mod2`, which is the same finite
check the `M`-side would need. -/
theorem mFrameMatrix_cupIsometry (hα : 1 ≤ α) (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) {p : MStabParam} (hp : p.Realizes B ξ) :
    (mFrameMatrix B ξ).transpose * mGram * mFrameMatrix B ξ = mGram := by
  rw [mCupIsometry_iff_nCupForm, mFrameMatrix_transpose_eq_nMatOf hα B ξ hp]
  exact (nCup_iff_mod2 _ _ _ _ _ _ _ _ _).mpr ⟨by ring, by ring, by ring⟩

/-- **MC3's counterexample claim, verified.**  The *other* variance — `M̄·G_M·M̄ᵀ = G_M` on
`M.lean`'s row-layout matrix — forces `τ = 0`.  The offending entry is `(0,1)`: it reads
`τ + 1 = 1`. -/
theorem mFrameMatrix_flip_forces_tau (hα : 1 ≤ α) (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) {p : MStabParam} (hp : p.Realizes B ξ)
    (hflip : mFrameMatrix B ξ * mGram * (mFrameMatrix B ξ).transpose = mGram) : p.tau = 0 := by
  rw [← nCupForm_iff_mul_transpose] at hflip
  have h := hflip 0 1
  rw [mFrameMatrix_of_realizes hα B ξ hp] at h
  simpa [nCupForm, nGram] using h

/-- Family M1 (`Λ_k : B ↦ A^k·B`, the axiom-free `mLambdaEquiv`) has `τ = k mod 2`, so the
variance refuted by `mFrameMatrix_flip_forces_tau` would keep only its even members. -/
theorem mFamM1_tau (α : ℕ) (k : ℤ_[2]) : (mFamM1 α k).tau = mParityZ k := rfl

end FrameMatrix

/-! ## §3 The same adjudication on the `N`-side

Family N1 is `dnTauBEquiv` — exact, axiom-free, and ν-invisible — so `τ` must be free; it is,
in `N.lean`'s layout, and it is not in the transposed one. -/

section NSide

/-- Family **N1** (`τ` free, identity `(σ̄, x̄₂)`-block) satisfies `N.lean`'s cup clause for every
`τ`. -/
theorem nMatOf_famN1_cupIsometry (τ : ZMod 2) : ∀ i j,
    nCupForm (nMatOf τ 0 0 0 0 1 0 0 1 i) (nMatOf τ 0 0 0 0 1 0 0 1 j) = nGram i j :=
  (nCup_iff_mod2 _ _ _ _ _ _ _ _ _).mpr ⟨by ring, by ring, by ring⟩

/-- **MC4's counterexample claim, verified.**  Transposing `N.lean`'s column-layout matrix turns
its cup clause into one that forces `τ = 0` — the `(0,1)` entry again reads `τ + 1 = 1`. -/
theorem nMatOf_transpose_cup_forces_tau (τ τσ τx p q g₁ g₂ h₁ h₂ : ZMod 2)
    (hflip : ∀ i j,
      nCupForm ((Matrix.of (nMatOf τ τσ τx p q g₁ g₂ h₁ h₂)).transpose i)
        ((Matrix.of (nMatOf τ τσ τx p q g₁ g₂ h₁ h₂)).transpose j) = nGram i j) : τ = 0 := by
  have h := hflip 0 1
  simpa [nCupForm, nMatOf, nGram] using h

/-- Family N1 at `τ = 1` therefore fails the flipped clause outright. -/
theorem nMatOf_famN1_transpose_not_cupIsometry :
    ¬ ∀ i j, nCupForm ((Matrix.of (nMatOf 1 0 0 0 0 1 0 0 1)).transpose i)
      ((Matrix.of (nMatOf 1 0 0 0 0 1 0 0 1)).transpose j) = nGram i j :=
  fun h => absurd (nMatOf_transpose_cup_forces_tau 1 0 0 0 0 1 0 0 1 h) (by decide)

/-- **The two variances are genuinely different conditions** — a single matrix satisfying
`A·G·Aᵀ = G` and refuting `Aᵀ·G·A = G`.  (`G` is symmetric but `G⁻¹ ≠ G`, so nothing forces the
two to agree.)  This is why the choice of layout has to be recorded rather than guessed, and it
is the *only* thing that ever separated MC3's report from MC4's. -/
theorem nMatOf_famN1_variance_differs :
    Matrix.of (nMatOf 1 0 0 0 0 1 0 0 1) * mGram
        * (Matrix.of (nMatOf 1 0 0 0 0 1 0 0 1)).transpose = mGram
      ∧ (Matrix.of (nMatOf 1 0 0 0 0 1 0 0 1)).transpose * mGram
          * Matrix.of (nMatOf 1 0 0 0 0 1 0 0 1) ≠ mGram :=
  ⟨(nCupForm_iff_mul_transpose _).mp (nMatOf_famN1_cupIsometry 1),
    fun h => nMatOf_famN1_transpose_not_cupIsometry ((mCupIsometry_iff_nCupForm _).mp h)⟩

end NSide

end MarkedCore

end Dyadic

end GQ2
