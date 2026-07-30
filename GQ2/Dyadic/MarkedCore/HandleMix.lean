/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.Cores

@[expose] public section

/-!
# Handle mixing, step 1: splitting the handle block, commutator expansion, exact transvections

**Ticket HM1** of the dyadic campaign (lane MC), implementing the `HandleMixLift` spike memo
`docs/dyadic/handlemixlift-spike.md` §7's first row.  The spike proved, at the mathematical
level, that the handle↔core mixing automorphisms consumed by the marked-stabilization
ν-correction exist, are explicit, fix the relator **on the nose** and are available with
arbitrary 2-adic parameters — with no new axiom and no appeal to compactness of `Aut(D_P)`.
This file lands the three purely algebraic ingredient families that the remaining discharge
tickets HM2–HM5 consume.  Repo conventions throughout, as in `Cores.lean`: `x ^ g = g⁻¹xg`
(`GQ2.conjP`), `[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`).

## Contents, and the memo section each part serves

* **§1 Splitting the handle block** (memo §4.1: `ζ_j := ∏_{i<j}[u_i,v_i]`).  `handlePrefix`
  and `handleSuffix` cut `Cores.lean`'s `handleWord` at an arbitrary index, with the headline
  three-term decomposition

  ```
  handleWord u v = handlePrefix u v j * commP (u j) (v j) * handleSuffix u v (j+1)
  ```

  (`handleWord_split`), together with the boundary values, the one-step recurrences, the two
  **congruence** lemmas (`handlePrefix_congr`, `handleSuffix_congr`: the blocks depend only on
  the handles they actually contain — this is what makes `Φ_j` fix `ζ_j` and the trailing
  block), naturality (`map_handlePrefix`, `map_handleSuffix`, the `map_handleWord` pattern) and
  the abelian collapse (`handlePrefix_comm`, `handleSuffix_comm`).

* **§2 The two commutator expansion identities** (memo *Conventions* and §3.1):

  ```
  [xz, y] = [x,y]^z · [z,y]        (commP_mul_left)
  [x, yz] = [x,z] · [x,y]^z        (commP_mul_right)
  ```

  plus the three `Commute`-hypothesis collapses they specialise to
  (`commP_eq_one_of_commute`, `commP_pre_mul_left_of_commute`,
  `commP_pre_mul_right_of_commute`, `commP_mul_right_of_commute`).  These are the
  substitution calculus behind memo §3.1's diagnosis of the naive candidate and behind §5.1's
  transvection rows.

* **§3 The exact transvections with 2-adic exponents** (memo §5.1, §5.2).  The four rows of
  memo §5.1 are *exact* automorphism data for **every** `k : ℤ_[2]`, not just `k : ℤ`, because
  `zpowZtwo hP y k` commutes with `y` (`commute_zpowZtwo_self`).  The `τ` family:

  | memo | Lean |
  |---|---|
  | `τ_σ(k) : a ↦ σ^k·a`, `τ_{v_j}(k) : u_j ↦ v_j^k·u_j` | `commP_zpowZtwo_pre_mul_left` |
  | `τ_{u_j}(k) : v_j ↦ u_j^k·v_j`, `τ_a(k) : σ ↦ a^k·σ` | `commP_zpowZtwo_pre_mul_right` |
  | MC1 §3.5's `[σ, x₂σ^k] = [σ,x₂]^{σ^k}` | `commP_mul_zpowZtwo_right` |

  assembled at the three word levels of `Cores.lean`: the handle block
  (`handleWord_tau_u`, `handleWord_tau_v`), the two rank-four core words (`mWord_tau_b`,
  `mWord_tau_d`, `nWord_tau_b`, `nWord_tau_c`, `nWord_tau_d`) and the full relators
  (`mRelWord_tau_handleU`/`V`, `nRelWord_tau_handleU`/`V`).

  **The two absent rows are the memo's, not an oversight.**  There is no `mWord_tau_a` /
  `nWord_tau_a` (the relator's `a²` resp. `a^{2+2^α}` factor is not commutator-protected) and
  no `mWord_tau_c` — the `c^{2^α}` factor of `P_M` blocks every transvection that moves `c`,
  which is precisely memo §5.1's `τ_a(k)` ✗ row and memo §6.4's residue 2 (the `M`-side unit
  hypothesis `ν'(c̄) ∈ ℤ₂ˣ`).

## What HM2/HM3 consume from here

* **HM2** (`Φ_j` as a substitution, `Φ_j(P) = P`, the explicit inverse, `thetaEquiv` assembly):
  `handleWord_split` to reduce `Φ_j(P) = P` to memo §4.1's local identity at handle `j`;
  `handlePrefix_congr` / `handleSuffix_congr` to see that `Φ_j` fixes `ζ_j` and the trailing
  block; `commP_mul_left` / `commP_mul_right` for the reduced-word bookkeeping.
  *Recorded spike result (HM1's acceptance test, verified in scratch, not committed):* memo
  §4.1's identity is `group`-provable from this file's API alone, at general handle count `h`
  **and** general handle index `j` — i.e. `Φ_j` fixes the surface part `[a,σ]·∏_j[u_j,v_j]`.
  The proof is: `handleWord_split` at `j` on both sides, `handlePrefix_congr` /
  `handleSuffix_congr` to discharge the two untouched blocks (the update at `j` is invisible to
  them), `Function.update_self`, then `simp only [commP, conjP]; group`.  The same one-liner
  closes memo §4.4's `Φ^M_j` and memo §6.5's `N` core-mixing element in the reduced form
  `[c,Φ(d)]·ζ·[Φ(u),v] = [c,d]·ζ·[u,v]` with `ζ` an arbitrary group element.  So HM2's
  word-level obligation needs no search — only the assembly of the substitution into a
  `ContinuousMulEquiv`.
* **HM3** (frame action of `Φ_j`, `E_j`, `E'_j`; `N² = 0`; `θ_w`-conjugation; `SL₂ = E₂` over
  `ℤ₂`): the whole `τ` family of §3 — `E_j := τ_{v_j}(1) ∘ τ_σ(1) ∘ Φ_j` and
  `S_j := τ_{v_j}(1) ∘ τ_{u_j}(−1) ∘ τ_{v_j}(1)` are built from it, and memo §5.2's
  `θ_w = diag(w, w⁻¹)` is a product of `τ_{u_j}`, `τ_{v_j}` with 2-adic exponents, which is
  exactly why no compactness of `Aut(D_P)` and no B8 is needed.
-/

namespace GQ2

namespace Dyadic

namespace MarkedCore

/-! ## §1 Splitting the handle block  (memo §4.1)

`Cores.lean`'s `handleWord u v = ∏_{j<h}[u_j,v_j]` is a `List.prod` over `List.finRange h`, so
cutting it at an index is `List.take`/`List.drop`.  The cut point is a bare `ℕ` (not a
`Fin h`), which makes the boundary cases `m = 0` and `m = h` — memo §4.1's `ζ_0 = 1` and the
empty trailing block — uniform. -/

section Split

variable {G : Type*} [Group G] {h : ℕ}

/-- The **intervening handle block** `ζ_m = ∏_{i<m}[u_i, v_i]` of memo §4.1 (`ζ_0 = 1`, and
`ζ_m = handleWord u v` once `h ≤ m`). -/
def handlePrefix (u v : Fin h → G) (m : ℕ) : G :=
  (((List.finRange h).take m).map fun j => commP (u j) (v j)).prod

/-- The **trailing handle block** `∏_{m ≤ i}[u_i, v_i]`: what follows the cut at `m`. -/
def handleSuffix (u v : Fin h → G) (m : ℕ) : G :=
  (((List.finRange h).drop m).map fun j => commP (u j) (v j)).prod

/-! ### Index bookkeeping for the two cuts -/

/-- A handle index in the first `m` entries of `List.finRange h` has value `< m`. -/
theorem mem_take_finRange {m : ℕ} {i : Fin h} (hi : i ∈ (List.finRange h).take m) :
    (i : ℕ) < m := by
  have hmem : i ∈ List.finRange h := List.mem_finRange i
  rw [List.mem_take_iff_idxOf_lt hmem] at hi
  simpa using hi

/-- A handle index past the first `m` entries of `List.finRange h` has value `≥ m`. -/
theorem mem_drop_finRange {m : ℕ} {i : Fin h} (hi : i ∈ (List.finRange h).drop m) :
    m ≤ (i : ℕ) := by
  have hmem : i ∈ List.finRange h := List.mem_finRange i
  rw [← Nat.not_lt]
  intro hlt
  have htake : i ∈ (List.finRange h).take m := by
    rw [List.mem_take_iff_idxOf_lt hmem]
    simpa using hlt
  exact List.disjoint_take_drop (List.nodup_finRange h) (le_refl m) htake hi

/-! ### Boundary values and the two one-step recurrences -/

@[simp] theorem handlePrefix_zero (u v : Fin h → G) : handlePrefix u v 0 = 1 := rfl

@[simp] theorem handleSuffix_zero (u v : Fin h → G) : handleSuffix u v 0 = handleWord u v := rfl

/-- Past the last handle the prefix is the whole block (memo §4.1's `ζ_h`). -/
theorem handlePrefix_of_le (u v : Fin h → G) {m : ℕ} (hm : h ≤ m) :
    handlePrefix u v m = handleWord u v := by
  rw [handlePrefix, handleWord, List.take_of_length_le (by simpa using hm)]

/-- Past the last handle the trailing block is empty. -/
theorem handleSuffix_of_le (u v : Fin h → G) {m : ℕ} (hm : h ≤ m) :
    handleSuffix u v m = 1 := by
  rw [handleSuffix, List.drop_of_length_le (by simpa using hm), List.map_nil, List.prod_nil]

/-- **The cut is a factorisation**: prefix times suffix is the whole handle block. -/
theorem handlePrefix_mul_handleSuffix (u v : Fin h → G) (m : ℕ) :
    handlePrefix u v m * handleSuffix u v m = handleWord u v := by
  rw [handlePrefix, handleSuffix, ← List.prod_append, ← List.map_append,
    List.take_append_drop, handleWord]

/-- The prefix recurrence `ζ_{m+1} = ζ_m · [u_m, v_m]`. -/
theorem handlePrefix_succ (u v : Fin h → G) {m : ℕ} (hm : m < h) :
    handlePrefix u v (m + 1) = handlePrefix u v m * commP (u ⟨m, hm⟩) (v ⟨m, hm⟩) := by
  have hlist : (List.finRange h).take (m + 1)
      = (List.finRange h).take m ++ [(⟨m, hm⟩ : Fin h)] := by
    rw [← List.take_concat_get' _ m (by simpa using hm)]
    simp
  rw [handlePrefix, handlePrefix, hlist, List.map_append, List.prod_append]
  simp

/-- The suffix recurrence: the trailing block at `m` peels off its first handle. -/
theorem handleSuffix_succ (u v : Fin h → G) {m : ℕ} (hm : m < h) :
    handleSuffix u v m = commP (u ⟨m, hm⟩) (v ⟨m, hm⟩) * handleSuffix u v (m + 1) := by
  have hlist : (List.finRange h).drop m
      = (⟨m, hm⟩ : Fin h) :: (List.finRange h).drop (m + 1) := by
    rw [← List.cons_getElem_drop_succ (h := by simpa using hm)]
    simp
  rw [handleSuffix, handleSuffix, hlist, List.map_cons, List.prod_cons]

/-- **The handle splitting lemma** (memo §4.1) — the shape every mixing element is written
against: at each handle index `j` the block factors as intervening prefix `ζ_j`, the `j`-th
commutator, and the trailing block. -/
theorem handleWord_split (u v : Fin h → G) (j : Fin h) :
    handleWord u v
      = handlePrefix u v j * commP (u j) (v j) * handleSuffix u v ((j : ℕ) + 1) := by
  rw [← handlePrefix_mul_handleSuffix u v (j : ℕ), handleSuffix_succ u v j.isLt, mul_assoc]

/-! ### Congruence: each block sees only its own handles

This is what makes memo §4.1's `Φ_j` fix `ζ_j` and the trailing block: `Φ_j` moves only the
letters `a` and `u_j`, so every handle other than the `j`-th is untouched. -/

/-- The handle block depends only on the `h` commutators, not on the letters separately. -/
theorem handleWord_congr {u v u' v' : Fin h → G}
    (huv : ∀ i : Fin h, commP (u i) (v i) = commP (u' i) (v' i)) :
    handleWord u v = handleWord u' v' := by
  rw [handleWord, handleWord, List.map_congr_left fun i _ => huv i]

/-- **`ζ_m` sees only the handles below `m`.** -/
theorem handlePrefix_congr {u v u' v' : Fin h → G} (m : ℕ)
    (huv : ∀ i : Fin h, (i : ℕ) < m → commP (u i) (v i) = commP (u' i) (v' i)) :
    handlePrefix u v m = handlePrefix u' v' m := by
  rw [handlePrefix, handlePrefix,
    List.map_congr_left fun i hi => huv i (mem_take_finRange hi)]

/-- **The trailing block sees only the handles from `m` on.** -/
theorem handleSuffix_congr {u v u' v' : Fin h → G} (m : ℕ)
    (huv : ∀ i : Fin h, m ≤ (i : ℕ) → commP (u i) (v i) = commP (u' i) (v' i)) :
    handleSuffix u v m = handleSuffix u' v' m := by
  rw [handleSuffix, handleSuffix,
    List.map_congr_left fun i hi => huv i (mem_drop_finRange hi)]

end Split

/-! ### Naturality of the two blocks (the `map_handleWord` pattern) -/

section SplitNaturality

variable {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H] {h : ℕ}

/-- **Naturality of `handlePrefix`**. -/
theorem map_handlePrefix (φ : F) (u v : Fin h → G) (m : ℕ) :
    φ (handlePrefix u v m) = handlePrefix (fun j => φ (u j)) (fun j => φ (v j)) m := by
  rw [handlePrefix, handlePrefix, ← List.prod_hom _ φ, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, commP, map_mul, map_inv]

/-- **Naturality of `handleSuffix`**. -/
theorem map_handleSuffix (φ : F) (u v : Fin h → G) (m : ℕ) :
    φ (handleSuffix u v m) = handleSuffix (fun j => φ (u j)) (fun j => φ (v j)) m := by
  rw [handleSuffix, handleSuffix, ← List.prod_hom _ φ, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, commP, map_mul, map_inv]

end SplitNaturality

/-! ### Abelian collapse of the two blocks

Both blocks are products of commutators, so both die on the abelianization — the frame-level
input to HM3 (`handleWord_comm`, `Cores.lean:233`, for the whole block). -/

section SplitAbelian

variable {G : Type*} [CommGroup G] {h : ℕ}

theorem handlePrefix_comm (u v : Fin h → G) (m : ℕ) : handlePrefix u v m = 1 := by
  rw [handlePrefix, List.prod_eq_one]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact commP_eq_one _ _

theorem handleSuffix_comm (u v : Fin h → G) (m : ℕ) : handleSuffix u v m = 1 := by
  rw [handleSuffix, List.prod_eq_one]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact commP_eq_one _ _

end SplitAbelian

/-! ## §2 The two commutator expansion identities  (memo *Conventions*, §3.1)

In the repo's conventions `x ^ g = g⁻¹xg`, `[x,y] = x⁻¹y⁻¹xy`, so the two substitution rules
are `[xz,y] = [x,y]^z·[z,y]` and `[x,yz] = [x,z]·[x,y]^z`.  Deliberately **not** `simp`
lemmas: they are directional expansions (memo §3.1 reads the naive candidate's defect off
them), and `group` closes the reduced-word identities they are used to structure. -/

section Expansion

variable {G : Type*} [Group G]

/-- **Expansion in the first letter**: `[xz, y] = [x,y]^z · [z,y]` (memo *Conventions*). -/
theorem commP_mul_left (x z y : G) : commP (x * z) y = conjP (commP x y) z * commP z y := by
  simp only [commP, conjP]
  group

/-- **Expansion in the second letter**: `[x, yz] = [x,z] · [x,y]^z` (memo *Conventions*). -/
theorem commP_mul_right (x y z : G) : commP x (y * z) = commP x z * conjP (commP x y) z := by
  simp only [commP, conjP]
  group

/-- Commuting letters have trivial commutator — the `CommGroup` lemma `commP_eq_one`
(`GQ2/Roe/Words.lean:217`) with the hypothesis localised to the pair. -/
theorem commP_eq_one_of_commute {x y : G} (hxy : Commute x y) : commP x y = 1 := by
  have hyx : y⁻¹ * x = x * y⁻¹ := hxy.symm.inv_left.eq
  rw [commP, mul_assoc x⁻¹ y⁻¹ x, hyx]
  group

/-- **The left exact-transvection collapse**: pre-multiplying the *first* letter by anything
commuting with the *second* leaves the commutator unchanged.  Memo §5.1's rows
`τ_σ(k) : a ↦ σ^k·a` (factor `[a,σ]`) and `τ_{v_j}(k) : u_j ↦ v_j^k·u_j` (factor
`[u_j,v_j]`). -/
theorem commP_pre_mul_left_of_commute {y z : G} (hzy : Commute z y) (x : G) :
    commP (z * x) y = commP x y := by
  rw [commP_mul_left, commP_eq_one_of_commute hzy, conjP, mul_one, inv_mul_cancel, one_mul]

/-- **The right exact-transvection collapse**: pre-multiplying the *second* letter by anything
commuting with the *first* leaves the commutator unchanged.  Memo §5.1's rows
`τ_{u_j}(k) : v_j ↦ u_j^k·v_j` and `τ_a(k) : σ ↦ a^k·σ`. -/
theorem commP_pre_mul_right_of_commute {x z : G} (hxz : Commute x z) (y : G) :
    commP x (z * y) = commP x y := by
  rw [commP_mul_right, commP_eq_one_of_commute hxz, conjP, mul_one, inv_mul_cancel, mul_one]

/-- **Post-multiplying the second letter conjugates**: `[x, yz] = [x,y]^z` when `z` commutes
with `x`.  This is MC1 §3.5's `[σ, x₂σ^k] = [σ,x₂]^{σ^k}`, the S1 stratum's other shape. -/
theorem commP_mul_right_of_commute {x z : G} (hxz : Commute x z) (y : G) :
    commP x (y * z) = conjP (commP x y) z := by
  rw [commP_mul_right, commP_eq_one_of_commute hxz, one_mul]

end Expansion

/-! ## §3 The exact transvections with 2-adic exponents  (memo §5.1, §5.2)

Memo §5.1's four rows are exact for **every** `k ∈ ℤ₂`, not merely for `k ∈ ℤ`, and the reason
is one line: `zpowZtwo hP y k` commutes with `y`, because `u ↦ zpowZtwo hP y u` is a monoid hom
out of the *commutative* group `Multiplicative ℤ₂` (`zpowZtwo_add`) pinned at `y`
(`zpowZtwo_one_exp`).  Memo V4/§5.2: this is what removes the need for compactness of
`Aut(D_P)` — and for B8 — from the whole handle-mixing construction. -/

section Transvections

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]

/-- **The 2-adic power of `x` commutes with `x`** — the engine of memo §5.1's exactness. -/
theorem commute_zpowZtwo_self (hP : IsProP 2 P) (x : P) (k : ℤ_[2]) :
    Commute (zpowZtwo hP x k) x := by
  have hr : zpowZtwo hP x k * x = zpowZtwo hP x (k + 1) := by
    rw [zpowZtwo_add, zpowZtwo_one_exp]
  have hl : x * zpowZtwo hP x k = zpowZtwo hP x (1 + k) := by
    rw [zpowZtwo_add, zpowZtwo_one_exp]
  show zpowZtwo hP x k * x = x * zpowZtwo hP x k
  rw [hr, hl, add_comm]

/-- **`τ_σ(k)` and `τ_{v_j}(k)`** (memo §5.1 rows 1–2): pre-multiplying the first letter of a
commutator by a 2-adic power of the second letter is exact. -/
theorem commP_zpowZtwo_pre_mul_left (hP : IsProP 2 P) (x y : P) (k : ℤ_[2]) :
    commP (zpowZtwo hP y k * x) y = commP x y :=
  commP_pre_mul_left_of_commute (commute_zpowZtwo_self hP y k) x

/-- **`τ_{u_j}(k)` and `τ_a(k)`** (memo §5.1 rows 3–4): pre-multiplying the second letter of a
commutator by a 2-adic power of the first letter is exact. -/
theorem commP_zpowZtwo_pre_mul_right (hP : IsProP 2 P) (x y : P) (k : ℤ_[2]) :
    commP x (zpowZtwo hP x k * y) = commP x y :=
  commP_pre_mul_right_of_commute (commute_zpowZtwo_self hP x k).symm y

/-- **MC1 §3.5 with a 2-adic exponent**: `[x, y·x^k] = [x,y]^{x^k}`. -/
theorem commP_mul_zpowZtwo_right (hP : IsProP 2 P) (x y : P) (k : ℤ_[2]) :
    commP x (y * zpowZtwo hP x k) = conjP (commP x y) (zpowZtwo hP x k) :=
  commP_mul_right_of_commute (commute_zpowZtwo_self hP x k).symm y

/-! ### The `τ` family at the handle block (memo §5.1, the intra-handle `SL₂(ℤ₂)`)

Memo §5.1: the two intra-handle transvections `τ_{v_j}(k) : u_j ↦ v_j^k·u_j` and
`τ_{u_j}(k) : v_j ↦ u_j^k·v_j` fix the handle block exactly, and their frame actions
`ū_j ↦ ū_j + k v̄_j`, `v̄_j ↦ v̄_j + k ū_j` generate `SL₂(ℤ₂)` on each handle plane (elementary
matrices generate `SL₂` over a local ring) — memo §5.2's `θ_w = diag(w, w⁻¹)` is a product of
these.  HM3 consumes the two lemmas below as the *exactness* half of that statement. -/

variable {h : ℕ}

/-- **`τ_{v_j}(k)` at the handle block**: replacing `u_j` by `v_j^k · u_j` fixes
`handleWord`. -/
theorem handleWord_tau_u (hP : IsProP 2 P) (u v : Fin h → P) (j : Fin h) (k : ℤ_[2]) :
    handleWord (Function.update u j (zpowZtwo hP (v j) k * u j)) v = handleWord u v := by
  refine handleWord_congr fun i => ?_
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, commP_zpowZtwo_pre_mul_left]
  · rw [Function.update_of_ne hij]

/-- **`τ_{u_j}(k)` at the handle block**: replacing `v_j` by `u_j^k · v_j` fixes
`handleWord`. -/
theorem handleWord_tau_v (hP : IsProP 2 P) (u v : Fin h → P) (j : Fin h) (k : ℤ_[2]) :
    handleWord u (Function.update v j (zpowZtwo hP (u j) k * v j)) = handleWord u v := by
  refine handleWord_congr fun i => ?_
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, commP_zpowZtwo_pre_mul_right]
  · rw [Function.update_of_ne hij]

/-! ### The `τ` family at the two rank-four core words (memo §5.1's `τ_σ`)

**Naming convention for the whole `τ` family.**  A Lean name's suffix is the letter that
*moves*, whereas the memo's subscript is the letter whose power is *used*: `handleWord_tau_u`
moves `u_j` by a power of `v_j` and so is the memo's `τ_{v_j}(k)`; `mWord_tau_d` moves `d` by a
power of `c` and so is its `τ_c(k)`.

Which letters admit an exact transvection depends on which letters carry a *non*-commutator
factor of the relator, and this is memo §6.1's hypothesis in `Cores.lean`'s letters:

* `mWord α a b c d = a²·[a,b]·c^{2^α}·[c,d]` — `a` is blocked by `a²` and `c` by `c^{2^α}`, so
  only `b` and `d` move.  The missing `mWord_tau_c` is memo §6.4's residue 2.
* `nWord α a b c d = a^{2+2^α}·[a,b]·[c,d]` — only `a` is blocked, so `b`, `c` and `d` all
  move: memo §4.4's "`N` is the easy case, not the hard one". -/

/-- `τ_a(k)` on the `M`-core's `(a,b)` pair: `b ↦ a^k·b` is exact. -/
theorem mWord_tau_b (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k : ℤ_[2]) :
    mWord α a (zpowZtwo hP a k * b) c d = mWord α a b c d := by
  rw [mWord, mWord, commP_zpowZtwo_pre_mul_right]

/-- `τ_c(k)` on the `M`-core's `(c,d)` pair: `d ↦ c^k·d` is exact.  The mirror substitution
`c ↦ d^k·c` is **not** — `c^{2^α}` blocks it (memo §6.4). -/
theorem mWord_tau_d (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k : ℤ_[2]) :
    mWord α a b c (zpowZtwo hP c k * d) = mWord α a b c d := by
  rw [mWord, mWord, commP_zpowZtwo_pre_mul_right]

/-- `τ_a(k)` on the `N`-core's `(a,b)` pair: `b ↦ a^k·b` is exact. -/
theorem nWord_tau_b (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k : ℤ_[2]) :
    nWord α a (zpowZtwo hP a k * b) c d = nWord α a b c d := by
  rw [nWord, nWord, commP_zpowZtwo_pre_mul_right]

/-- `τ_d(k)` on the `N`-core's `(c,d)` pair: `c ↦ d^k·c` is exact — the row unavailable for
`M`.  For `N` this is memo §5.1's `τ_σ(k)` proper (`(c,d) = (σ, x₂)`). -/
theorem nWord_tau_c (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k : ℤ_[2]) :
    nWord α a b (zpowZtwo hP d k * c) d = nWord α a b c d := by
  rw [nWord, nWord, commP_zpowZtwo_pre_mul_left]

/-- `τ_c(k)` on the `N`-core's `(c,d)` pair: `d ↦ c^k·d` is exact. -/
theorem nWord_tau_d (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k : ℤ_[2]) :
    nWord α a b c (zpowZtwo hP c k * d) = nWord α a b c d := by
  rw [nWord, nWord, commP_zpowZtwo_pre_mul_right]

end Transvections

/-! ### The `τ` family at the full relators

To move a single handle letter of a marking `m : Fin (coreRank h) → G` one updates `m` at
`handleIdxU j` or `handleIdxV j`.  The four core letters `0,1,2,3` and the other handles are
untouched — that is the content of the index lemmas below, and it is what turns the handle-block
statements `handleWord_tau_u`/`_v` into relator statements. -/

section MarkingIndex

variable {h : ℕ}

/-- `handleIdxU` is injective. -/
theorem handleIdxU_injective : Function.Injective (handleIdxU (h := h)) := by
  intro i j hij
  have h1 := handleIdxU_val (h := h) i
  have h2 := handleIdxU_val (h := h) j
  rw [hij, h2] at h1
  exact Fin.ext (by omega)

/-- `handleIdxV` is injective. -/
theorem handleIdxV_injective : Function.Injective (handleIdxV (h := h)) := by
  intro i j hij
  have h1 := handleIdxV_val (h := h) i
  have h2 := handleIdxV_val (h := h) j
  rw [hij, h2] at h1
  exact Fin.ext (by omega)

/-- The two handle letters of a pair never collide: `4 + 2i` is even, `5 + 2j` is odd. -/
theorem handleIdxU_ne_handleIdxV (i j : Fin h) :
    (handleIdxU i : Fin (coreRank h)) ≠ handleIdxV j := by
  intro hij
  have h1 := handleIdxU_val (h := h) i
  have h2 := handleIdxV_val (h := h) j
  rw [hij, h2] at h1
  omega

/-- Handle letters are never core letters: `handleIdxU j` has index `4 + 2j ≥ 4`. -/
theorem handleIdxU_ne_of_val_lt (j : Fin h) {i : Fin (coreRank h)} (hi : (i : ℕ) < 4) :
    (handleIdxU j : Fin (coreRank h)) ≠ i := by
  intro hij
  rw [← hij, handleIdxU_val] at hi
  omega

/-- Handle letters are never core letters: `handleIdxV j` has index `5 + 2j ≥ 4`. -/
theorem handleIdxV_ne_of_val_lt (j : Fin h) {i : Fin (coreRank h)} (hi : (i : ℕ) < 4) :
    (handleIdxV j : Fin (coreRank h)) ≠ i := by
  intro hij
  rw [← hij, handleIdxV_val] at hi
  omega

end MarkingIndex

/-! The six `Function.update` lemmas below are pure index bookkeeping and hold for a marking
into any type — no group structure is used. -/

section MarkingUpdate

variable {G : Type*} {h : ℕ}

/-- Updating a marking at a handle-`U` letter leaves the four core letters alone. -/
theorem update_handleIdxU_core (m : Fin (coreRank h) → G) (j : Fin h) (w : G)
    {i : Fin (coreRank h)} (hi : (i : ℕ) < 4) :
    Function.update m (handleIdxU j) w i = m i :=
  Function.update_of_ne (Ne.symm (handleIdxU_ne_of_val_lt j hi)) _ _

/-- Updating a marking at a handle-`V` letter leaves the four core letters alone. -/
theorem update_handleIdxV_core (m : Fin (coreRank h) → G) (j : Fin h) (w : G)
    {i : Fin (coreRank h)} (hi : (i : ℕ) < 4) :
    Function.update m (handleIdxV j) w i = m i :=
  Function.update_of_ne (Ne.symm (handleIdxV_ne_of_val_lt j hi)) _ _

/-- Updating at `handleIdxU j` updates the handle-`U` marking function at `j` only. -/
theorem update_handleIdxU_comp_U (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    (fun i => Function.update m (handleIdxU j) w (handleIdxU i))
      = Function.update (fun i => m (handleIdxU i)) j w := by
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · rw [Function.update_of_ne (fun hc => hij (handleIdxU_injective hc)),
      Function.update_of_ne hij]

/-- Updating at `handleIdxU j` leaves the handle-`V` marking function alone. -/
theorem update_handleIdxU_comp_V (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    (fun i => Function.update m (handleIdxU j) w (handleIdxV i)) = fun i => m (handleIdxV i) := by
  funext i
  exact Function.update_of_ne (Ne.symm (handleIdxU_ne_handleIdxV j i)) _ _

/-- Updating at `handleIdxV j` leaves the handle-`U` marking function alone. -/
theorem update_handleIdxV_comp_U (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    (fun i => Function.update m (handleIdxV j) w (handleIdxU i)) = fun i => m (handleIdxU i) := by
  funext i
  exact Function.update_of_ne (handleIdxU_ne_handleIdxV i j) _ _

/-- Updating at `handleIdxV j` updates the handle-`V` marking function at `j` only. -/
theorem update_handleIdxV_comp_V (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    (fun i => Function.update m (handleIdxV j) w (handleIdxV i))
      = Function.update (fun i => m (handleIdxV i)) j w := by
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · rw [Function.update_of_ne (fun hc => hij (handleIdxV_injective hc)),
      Function.update_of_ne hij]

end MarkingUpdate

section MarkingRelWord

variable {G : Type*} [Group G] {h : ℕ}

/-- **Structure of a handle-`U` update of the `M_α` relator**: the core word is untouched and
only the handle-`U` marking function moves. -/
theorem mRelWord_update_handleIdxU (α : ℕ) (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    mRelWord α (Function.update m (handleIdxU j) w)
      = mWord α (m 0) (m 1) (m 2) (m 3) *
        handleWord (Function.update (fun i => m (handleIdxU i)) j w)
          (fun i => m (handleIdxV i)) := by
  rw [mRelWord, update_handleIdxU_comp_U, update_handleIdxU_comp_V,
    update_handleIdxU_core m j w (by rw [coreVal_zero]; omega),
    update_handleIdxU_core m j w (by rw [coreVal_one]; omega),
    update_handleIdxU_core m j w (by rw [coreVal_two]; omega),
    update_handleIdxU_core m j w (by rw [coreVal_three]; omega)]

/-- **Structure of a handle-`V` update of the `M_α` relator**. -/
theorem mRelWord_update_handleIdxV (α : ℕ) (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    mRelWord α (Function.update m (handleIdxV j) w)
      = mWord α (m 0) (m 1) (m 2) (m 3) *
        handleWord (fun i => m (handleIdxU i))
          (Function.update (fun i => m (handleIdxV i)) j w) := by
  rw [mRelWord, update_handleIdxV_comp_U, update_handleIdxV_comp_V,
    update_handleIdxV_core m j w (by rw [coreVal_zero]; omega),
    update_handleIdxV_core m j w (by rw [coreVal_one]; omega),
    update_handleIdxV_core m j w (by rw [coreVal_two]; omega),
    update_handleIdxV_core m j w (by rw [coreVal_three]; omega)]

/-- **Structure of a handle-`U` update of the `N_α` relator**. -/
theorem nRelWord_update_handleIdxU (α : ℕ) (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    nRelWord α (Function.update m (handleIdxU j) w)
      = nWord α (m 0) (m 1) (m 2) (m 3) *
        handleWord (Function.update (fun i => m (handleIdxU i)) j w)
          (fun i => m (handleIdxV i)) := by
  rw [nRelWord, update_handleIdxU_comp_U, update_handleIdxU_comp_V,
    update_handleIdxU_core m j w (by rw [coreVal_zero]; omega),
    update_handleIdxU_core m j w (by rw [coreVal_one]; omega),
    update_handleIdxU_core m j w (by rw [coreVal_two]; omega),
    update_handleIdxU_core m j w (by rw [coreVal_three]; omega)]

/-- **Structure of a handle-`V` update of the `N_α` relator**. -/
theorem nRelWord_update_handleIdxV (α : ℕ) (m : Fin (coreRank h) → G) (j : Fin h) (w : G) :
    nRelWord α (Function.update m (handleIdxV j) w)
      = nWord α (m 0) (m 1) (m 2) (m 3) *
        handleWord (fun i => m (handleIdxU i))
          (Function.update (fun i => m (handleIdxV i)) j w) := by
  rw [nRelWord, update_handleIdxV_comp_U, update_handleIdxV_comp_V,
    update_handleIdxV_core m j w (by rw [coreVal_zero]; omega),
    update_handleIdxV_core m j w (by rw [coreVal_one]; omega),
    update_handleIdxV_core m j w (by rw [coreVal_two]; omega),
    update_handleIdxV_core m j w (by rw [coreVal_three]; omega)]

end MarkingRelWord

section MarkingTransvections

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- **`τ_{v_j}(k)` on the full `M_α` relator**: `u_j ↦ v_j^k·u_j` fixes `mRelWord`. -/
theorem mRelWord_tau_handleU (hP : IsProP 2 P) (α : ℕ) (m : Fin (coreRank h) → P) (j : Fin h)
    (k : ℤ_[2]) :
    mRelWord α (Function.update m (handleIdxU j)
        (zpowZtwo hP (m (handleIdxV j)) k * m (handleIdxU j))) = mRelWord α m := by
  rw [mRelWord_update_handleIdxU,
    handleWord_tau_u hP (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) j k, mRelWord]

/-- **`τ_{u_j}(k)` on the full `M_α` relator**: `v_j ↦ u_j^k·v_j` fixes `mRelWord`. -/
theorem mRelWord_tau_handleV (hP : IsProP 2 P) (α : ℕ) (m : Fin (coreRank h) → P) (j : Fin h)
    (k : ℤ_[2]) :
    mRelWord α (Function.update m (handleIdxV j)
        (zpowZtwo hP (m (handleIdxU j)) k * m (handleIdxV j))) = mRelWord α m := by
  rw [mRelWord_update_handleIdxV,
    handleWord_tau_v hP (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) j k, mRelWord]

/-- **`τ_{v_j}(k)` on the full `N_α` relator**. -/
theorem nRelWord_tau_handleU (hP : IsProP 2 P) (α : ℕ) (m : Fin (coreRank h) → P) (j : Fin h)
    (k : ℤ_[2]) :
    nRelWord α (Function.update m (handleIdxU j)
        (zpowZtwo hP (m (handleIdxV j)) k * m (handleIdxU j))) = nRelWord α m := by
  rw [nRelWord_update_handleIdxU,
    handleWord_tau_u hP (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) j k, nRelWord]

/-- **`τ_{u_j}(k)` on the full `N_α` relator**. -/
theorem nRelWord_tau_handleV (hP : IsProP 2 P) (α : ℕ) (m : Fin (coreRank h) → P) (j : Fin h)
    (k : ℤ_[2]) :
    nRelWord α (Function.update m (handleIdxV j)
        (zpowZtwo hP (m (handleIdxU j)) k * m (handleIdxV j))) = nRelWord α m := by
  rw [nRelWord_update_handleIdxV,
    handleWord_tau_v hP (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) j k, nRelWord]

end MarkingTransvections

end MarkedCore

end Dyadic

end GQ2
