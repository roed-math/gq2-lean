/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.TwoCentralTower
import GQ2.Roe.DRPresentation
import GQ2.Roe.Words
import GQ2.DyadicPresentation
import GQ2.SectionThree
import GQ2.Roe.ChiR
import GQ2.ZtwoPowering
import GQ2.Roe.DRAbelianization
import GQ2.DyadicNielsen

/-!
# Levelwise triple sets, the invariant `P`, the defect, and the `k₀ = 3` base cases
(L-campaign ticket L1/L3)

**Statements final (ticket L1); fills tickets L3 (base cases, witnesses, numeric pins,
χ-evaluations) and L4a (defect calculus: lift-independence, membership, restriction).**
Design record: `docs/orchestration/labute-l1-design.md`; sources: `labute-plan.md` §2.1–2.3
and `labute-spike.md` §2.4 (the STATEMENT FREEZE for the sets), §3.1, §3.4, §4.

Fix the two presented pro-2 groups `D_R = ⟨s,x,y | r₂⟩` (`GQ2/Roe/DRPresentation.lean`) and
`D₀ = ⟨A,S,Y | r₀⟩` (`GQ2/DyadicPresentation.lean`), their λ-towers
(`GQ2/Roe/Labute/TwoCentralTower.lean`), and the χ-data:

* direction 1 (**`r₀`-triples in the `D_R`-tower**): triples `T : Fin 3 → Qₖ(D_R)` in the
  `(A, S, Y)`-slots; character `χ_R = chiR` (`GQ2/Roe/ChiR.lean`); χ-targets
  `(−1, 1, η)` with `η = (1−4)⁻¹ = (−3)⁻¹` (`etaUnit`);
* direction 2 (**`r₂`-triples in the `D₀`-tower**): triples in the `(s, x, y)`-slots;
  character `χ₀ = chiD0pres` — built here from the presentation via `d0LiftHom` at
  `(−1, 1, η)`, **not** the B3c-bundle character (`GQ2/Roe/MarkedMatching.lean`'s `chiD0G`
  is Galois-side and census-forbidden in this lane, plan §8); χ-targets `(S, X, Y) =
  (SvalUnit, rootXUnit, YvalUnit)` (`GQ2/Roe/ChiR.lean`, tickets R10/R11).

The **levelwise sets** (spike §2.4, FINAL FORM):
`S⁰ₖ` (`sZeroR0`/`sZeroR2`): relator-killing generating triples mod `λₖ`;
`S^P_ₖ` (`sPR0`/`sPR2`): the `S⁰ₖ`-triples satisfying the invariant `P` — the χ-congruence
`χ̄ₖ(Tᵢ) = targetᵢ mod 2^k` (modulus `m(k) = k`, via `chiLevel`).

The **defect** `δ(T) ∈ Zₖ ⊆ Q_{k+1}` (plan §2.2, spike §2.1): the relator value of the
canonical lift; independent of the lift (`defectR0_eq_of_lift` — no `k`-threshold: only
centrality and exponent-2 of the kernel are used, relator exponent sums even both sides).

**Base cases** `k₀ = 3` (spike §2.4, §3.1, §3.4): explicit witnesses in `Q₃` (order
`2^8 = 256`), stated on named generator words so L3 can discharge by transport to a
concrete 256-element model + `decide`/structured verification (plan §2.3); the mod-8 and
mod-`2^9` numeric pins of the χ-targets are frozen as separate statements (spike §4.1).

Convention note: all word shapes are repo-convention (`commP`/`conjP`, board §10); see the
convention paragraph in `TwoCentralTower.lean`.
-/

namespace GQ2.Roe.Labute

/-! ## The `r₀` word shape

`drWord` exists in-tree (`GQ2/Roe/DRPresentation.lean`); its `r₀`-mirror is defined here
in the same style.  `d0Word (m 0) (m 1) (m 2)` is definitionally the relator expression of
`d0LiftHom` (`GQ2/SectionThree.lean:444`), so triples killing `d0Word` classify continuous
homs `D₀ → H` with no rewriting. -/

/-- The **dyadic relator word shape** `d0Word a s y = a² · s⁴ · [s, y]` (`r₀ = A²S⁴[S,Y]`,
Serre 252 Cor. 4.4; repo convention `[s,y] = commP s y = s⁻¹y⁻¹sy`), as a word in any
group — the `r₀`-mirror of `GQ2.drWord`. -/
def d0Word {G : Type*} [Group G] (a s y : G) : G :=
  a ^ 2 * s ^ 4 * commP s y

/-- Naturality of the `r₀` word shape under any monoid-hom-like map (mirror of
`map_drWord`). -/
theorem map_d0Word {F G H : Type*} [Group G] [Group H] [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (a s y : G) :
    φ (d0Word a s y) = d0Word (φ a) (φ s) (φ y) := by
  simp only [d0Word, commP, map_mul, map_inv, map_pow]

/-- Abelian collapse (smoke): in a commutative group `d0Word a s y = a²s⁴` — the
abelianized relation `2ā + 4s̄ = 0`, pinning the exponents `(2, 4, 0)`. -/
theorem d0Word_comm {G : Type*} [CommGroup G] (a s y : G) :
    d0Word a s y = a ^ 2 * s ^ 4 := by
  rw [d0Word, commP_eq_one, mul_one]

/-- The relator dies on the marked generators of `D₀` (smoke; definitional repackaging of
`d0_relation`). -/
theorem d0Word_eq_one : d0Word d0A d0S d0Y = 1 := d0_relation

/-! ## The χ-data: `η`, the presentation-side `χ₀`, and the pinned targets -/

/-- The 2-adic unit `−3` (odd, hence a unit; same recipe as
`GQ2.unitNegThree`, replicated here to keep this lane free of the Galois-side files —
plan §8). -/
noncomputable def negThreeUnit : ℤ_[2]ˣ :=
  (isUnit_intCast_of_odd (⟨-2, by ring⟩ : Odd (-3 : ℤ))).unit

/-- Value pin for `negThreeUnit` (smoke). -/
@[simp] theorem negThreeUnit_val : ((negThreeUnit : ℤ_[2]ˣ) : ℤ_[2]) = -3 := by
  rw [negThreeUnit, IsUnit.unit_spec]
  push_cast
  ring

/-- **The secondary-depth unit** `η = (1 − 4)⁻¹ = (−3)⁻¹` (Labute Théorème 4 case (2) at
`f = 2`: orientation values `(−1, 1, (1−2^f)⁻¹)`; spike §2.4).  `η ≡ 5 (mod 8)` — the
`f = 2` discriminator (`η′ = (1−8)⁻¹ ≡ 1 (mod 8)` for the `f = 3` control, spike §3.2) —
is pinned through `chiTargetR0_three` below. -/
noncomputable def etaUnit : ℤ_[2]ˣ := negThreeUnit⁻¹

/-- **The presentation-side canonical orientation of `D₀`**: `χ₀ : D₀ → ℤ₂ˣ` with
generator values `(A, S, Y) ↦ (−1, 1, η)`, built by the universal property `d0LiftHom` at
the triple `(−1, 1, η)` (the relator dies since `ℤ₂ˣ` is abelian: `(−1)²·1⁴·[1,η] = 1`).

This is the `χ₀` of the levelwise χ-clause in direction 2.  It deliberately does **not**
reuse `chiD0G` (`GQ2/Roe/MarkedMatching.lean`), which is assembled from the B3c Galois
bundle: the L-campaign must stay census-free (plan §8), so every `D₀`-side fact comes from
the presentation. -/
noncomputable def chiD0pres : ContinuousMonoidHom (D0 : Type) ℤ_[2]ˣ :=
  SectionThree.d0LiftHom isProP_two_unitsPadicInt ![-1, 1, etaUnit] (by
    show (-1 : ℤ_[2]ˣ) ^ 2 * (1 : ℤ_[2]ˣ) ^ 4 * commP (1 : ℤ_[2]ˣ) etaUnit = 1
    rw [commP_eq_one, neg_one_sq, one_pow, mul_one, mul_one])

/-- `χ₀(A) = −1`.  Fill: L3 (replicate the `SectionThree.d0LiftHom_A` evaluation pattern of
`GQ2/SectionThree.lean`). -/
theorem chiD0pres_d0A : chiD0pres d0A = -1 := by
  show ((maxProPHomEquiv isProP_two_unitsPadicInt).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = -1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-- `χ₀(S) = 1`.  Fill: L3. -/
theorem chiD0pres_d0S : chiD0pres d0S = 1 := by
  show ((maxProPHomEquiv isProP_two_unitsPadicInt).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-- `χ₀(Y) = η`.  Fill: L3. -/
theorem chiD0pres_d0Y : chiD0pres d0Y = etaUnit := by
  show ((maxProPHomEquiv isProP_two_unitsPadicInt).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2))) = etaUnit
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-- χ-targets, direction 1 (`r₀`-triples in the `D_R`-tower, `(A,S,Y)`-slots):
`(−1, 1, η)` (spike §2.4). -/
noncomputable def chiTargetUnitsR0 : Fin 3 → ℤ_[2]ˣ := ![-1, 1, etaUnit]

/-- χ-targets, direction 2 (`r₂`-triples in the `D₀`-tower, `(s,x,y)`-slots):
`(S, X, Y)` — the Hensel-root orientation values of `χ_R` (spike §2.4; `X ≡ 5 (mod 16)`,
`S = −X³/(X²+X+1)`, `Y = −X²`; `GQ2/Roe/OrientationRoot.lean`, `GQ2/Roe/ChiR.lean`). -/
noncomputable def chiTargetUnitsR2 : Fin 3 → ℤ_[2]ˣ := ![SvalUnit, rootXUnit, YvalUnit]

/-- The mod-`2^k` reductions of the direction-1 targets — the right-hand sides of the
invariant `P` at level `k`. -/
noncomputable def chiTargetR0 (k : ℕ) : Fin 3 → (ZMod (2 ^ k))ˣ := fun i =>
  Units.map (PadicInt.toZModPow k).toMonoidHom (chiTargetUnitsR0 i)

/-- The mod-`2^k` reductions of the direction-2 targets. -/
noncomputable def chiTargetR2 (k : ℕ) : Fin 3 → (ZMod (2 ^ k))ˣ := fun i =>
  Units.map (PadicInt.toZModPow k).toMonoidHom (chiTargetUnitsR2 i)

/-! ### Numeric pins (spike §4.1: anchors to bake into statements)

Mod `8` (level `k₀ = 3`, load-bearing for L3's base-case checks) and mod `2^9` (stress).
Independently re-verified during L1: `X ≡ 437`, `S ≡ 253`, `Y ≡ 7`, `η ≡ 341 (mod 512)`;
mod 8 these are `(5, 5, 7)` and `η ≡ 5` — the `f = 2` content. -/

/-- The defining relation of `η` in any mod-`2^k` shadow: `η · (−3) = 1`.  The shadows of
`etaUnit` are pinned by this together with a `decide` over `ZMod (2^k)` (the in-tree
`rootX_toZModPow_*` idiom). -/
private theorem etaUnit_toZModPow_mul (k : ℕ) :
    PadicInt.toZModPow k ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) * (-3) = 1 := by
  have h : ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) * ((negThreeUnit : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [etaUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h' := congrArg (PadicInt.toZModPow (p := 2) k) h
  rw [map_mul, map_one, negThreeUnit_val] at h'
  simpa only [map_neg, map_ofNat] using h'

/-- Direction-1 targets mod `8`: `(−1, 1, η) ≡ (7, 1, 5)`.  Fill: L3. -/
theorem chiTargetR0_three (i : Fin 3) :
    (chiTargetR0 3 i : ZMod (2 ^ 3)) = ![7, 1, 5] i := by
  have heta : PadicInt.toZModPow 3 ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 :=
    (by decide : ∀ z : ZMod (2 ^ 3), z * (-3) = 1 → z = 5) _ (etaUnit_toZModPow_mul 3)
  have hneg : (-1 : ZMod (2 ^ 3)) = 7 := by decide
  fin_cases i <;> simp [chiTargetR0, chiTargetUnitsR0, heta, hneg]

/-- The mod-`2^k` shadow of the Hensel root `X` is pinned by its defining equation
`X³ + 2X² + 1 = 0`: the root is unique mod `2^k` (the reduction mod 2 has the simple root
`1`), so a `decide` over `ZMod (2^k)` identifies it.  In-tree idiom of
`GQ2/Roe/OrientationRoot.lean`'s `rootX_toZModPow_four`. -/
private theorem rootX_toZModPow_eq {k : ℕ} {c : ZMod (2 ^ k)}
    (h : ∀ r : ZMod (2 ^ k), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = c) :
    PadicInt.toZModPow k rootX = c := by
  have h0 := congrArg (PadicInt.toZModPow (p := 2) k) rootX_isRoot
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at h0
  exact h _ h0

/-- The mod-`2^k` shadow of `S` from `Sval_mul_denom` (`S·(X²+X+1) = −X³`) once the shadow
of `X` is known: the denominator is odd, hence invertible, so a `decide` pins `S`. -/
private theorem Sval_toZModPow_eq {k : ℕ} {r : ZMod (2 ^ k)} (hr : PadicInt.toZModPow k rootX = r)
    {c : ZMod (2 ^ k)} (h : ∀ z : ZMod (2 ^ k), z * (r ^ 2 + r + 1) = -r ^ 3 → z = c) :
    PadicInt.toZModPow k Sval = c := by
  have h0 := congrArg (PadicInt.toZModPow (p := 2) k) Sval_mul_denom
  simp only [map_mul, map_add, map_pow, map_one, map_neg, hr] at h0
  exact h _ h0

/-- The mod-`2^k` shadow of `Y = −X²` from the shadow of `X`. -/
private theorem Yval_toZModPow_eq {k : ℕ} {r : ZMod (2 ^ k)} (hr : PadicInt.toZModPow k rootX = r) :
    PadicInt.toZModPow k Yval = -r ^ 2 := by
  rw [Yval_eq, map_neg, map_pow, hr]

/-- Direction-2 targets mod `8`: `(S, X, Y) ≡ (5, 5, 7)`.  Fill: L3. -/
theorem chiTargetR2_three (i : Fin 3) :
    (chiTargetR2 3 i : ZMod (2 ^ 3)) = ![5, 5, 7] i := by
  have hX : PadicInt.toZModPow 3 rootX = 5 := rootX_toZModPow_eq (by decide)
  have hS : PadicInt.toZModPow 3 Sval = 5 := Sval_toZModPow_eq hX (by decide)
  have hY : PadicInt.toZModPow 3 Yval = 7 := by rw [Yval_toZModPow_eq hX]; decide
  fin_cases i <;>
    simp [chiTargetR2, chiTargetUnitsR2, val_SvalUnit, val_rootXUnit, val_YvalUnit, hS, hX, hY]

set_option maxRecDepth 4000 in
/-- Direction-1 targets mod `2^9` (stress): `(−1, 1, η) ≡ (511, 1, 341)`.  Fill: L3.

The `decide`s below are kernel checks over the 512 residues (plan §2.3's budget question:
they pass comfortably; `native_decide` is not used anywhere in this file).  Only the
elaborator's recursion budget needs raising. -/
theorem chiTargetR0_nine (i : Fin 3) :
    (chiTargetR0 9 i : ZMod (2 ^ 9)) = ![511, 1, 341] i := by
  have heta : PadicInt.toZModPow 9 ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) = 341 :=
    (by decide : ∀ z : ZMod (2 ^ 9), z * (-3) = 1 → z = 341) _ (etaUnit_toZModPow_mul 9)
  have hneg : (-1 : ZMod (2 ^ 9)) = 511 := by decide
  fin_cases i <;> simp [chiTargetR0, chiTargetUnitsR0, heta, hneg]

set_option maxRecDepth 4000 in
/-- Direction-2 targets mod `2^9` (stress): `(S, X, Y) ≡ (253, 437, 7)` — the spike's
level-9 numerics, re-verified by hand during L1.  Fill: L3. -/
theorem chiTargetR2_nine (i : Fin 3) :
    (chiTargetR2 9 i : ZMod (2 ^ 9)) = ![253, 437, 7] i := by
  have hX : PadicInt.toZModPow 9 rootX = 437 := rootX_toZModPow_eq (by decide)
  have hS : PadicInt.toZModPow 9 Sval = 253 := Sval_toZModPow_eq hX (by decide)
  have hY : PadicInt.toZModPow 9 Yval = 7 := by rw [Yval_toZModPow_eq hX]; decide
  fin_cases i <;>
    simp [chiTargetR2, chiTargetUnitsR2, val_SvalUnit, val_rootXUnit, val_YvalUnit, hS, hX, hY]

/-- Naturality of the mod-`2^k` unit reductions of `ℤ₂ˣ` in `k`: reading the mod-`2^{k+1}`
reduction of a 2-adic unit mod `2^k` gives the mod-`2^k` reduction
(`PadicInt.cast_toZModPow` at the level of unit groups).  Both target families are
reductions of fixed units, so their naturality is this lemma. -/
private theorem units_map_castHom_toZModPow (k : ℕ) (u : ℤ_[2]ˣ) :
    Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k))).toMonoidHom
        (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom u) =
      Units.map (PadicInt.toZModPow k).toMonoidHom u := by
  ext
  simp

/-- Naturality of the direction-1 targets in `k` (consumed by the restriction maps).
Fill: L3 (from `PadicInt.zmod_cast_comp_toZModPow`-style compatibility). -/
theorem chiTargetR0_castHom (k : ℕ) (i : Fin 3) :
    Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k))).toMonoidHom
      (chiTargetR0 (k + 1) i) = chiTargetR0 k i :=
  units_map_castHom_toZModPow k (chiTargetUnitsR0 i)

/-- Naturality of the direction-2 targets in `k`.  Fill: L3. -/
theorem chiTargetR2_castHom (k : ℕ) (i : Fin 3) :
    Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k))).toMonoidHom
      (chiTargetR2 (k + 1) i) = chiTargetR2 k i :=
  units_map_castHom_toZModPow k (chiTargetUnitsR2 i)

/-! ## The levelwise sets (spike §2.4, FINAL FORM) -/

/-- **`S⁰ₖ`, direction 1**: `r₀`-relator-killing generating triples in
`Qₖ(D_R) = D_R/λₖ` — the strict levelwise set *without* the χ-clause (plan §2.1;
generation is a clause, not an afterthought — spike §3.5). -/
def sZeroR0 (k : ℕ) : Set (Fin 3 → levelQuot (DR : Type) k) :=
  {T | d0Word (T 0) (T 1) (T 2) = 1 ∧ Subgroup.closure (Set.range T) = ⊤}

/-- **`S^P_ₖ`, direction 1** (spike §2.4, the frozen main object): the `S⁰ₖ`-triples
satisfying the invariant `P` — the χ-congruence `χ̄_R,ₖ(Tᵢ) = targetᵢ` at modulus
`2^k = 2^{m(k)}`. -/
def sPR0 (k : ℕ) : Set (Fin 3 → levelQuot (DR : Type) k) :=
  {T | T ∈ sZeroR0 k ∧ ∀ i, chiLevel chiR k (T i) = chiTargetR0 k i}

/-- **`S⁰ₖ`, direction 2**: `r₂`-relator-killing generating triples in `Qₖ(D₀)`
(word shape `drWord`, `GQ2/Roe/DRPresentation.lean`). -/
def sZeroR2 (k : ℕ) : Set (Fin 3 → levelQuot (D0 : Type) k) :=
  {T | drWord (T 0) (T 1) (T 2) = 1 ∧ Subgroup.closure (Set.range T) = ⊤}

/-- **`S^P_ₖ`, direction 2**: the χ-clause runs through the presentation-side `χ₀`
(`chiD0pres`) against the Hensel-root targets. -/
def sPR2 (k : ℕ) : Set (Fin 3 → levelQuot (D0 : Type) k) :=
  {T | T ∈ sZeroR2 k ∧ ∀ i, chiLevel chiD0pres k (T i) = chiTargetR2 k i}

/-! ## Central-shift calculus (the mechanism behind lift-independence)

Two lifts of the same level-`k` triple differ coordinatewise by elements of `Zₖ`, which is
central of exponent 2 in `Q_{k+1}`.  Shifting a slot by a central `z` therefore multiplies
the relator value by `z` to the slot's *exponent sum*; both relator words have even
exponent sums (`r₀ = A²S⁴[S,Y]`: `(2, 4, 0)`; `r₂`: `(0, −4, 2)`), so every shift cancels.
The generic `commP`/`conjP` steps live in `H`; the layer facts specialize them. -/

section CentralShift

variable {H : Type*} [Group H] {z : H}

/-- A central factor in the first slot of a `commP` cancels. -/
theorem commP_central_left (hz : ∀ w : H, Commute z w) (a b : H) :
    commP (z * a) b = commP a b := by
  have h : z⁻¹ * b⁻¹ = b⁻¹ * z⁻¹ := (hz b).inv_inv.eq
  calc commP (z * a) b = a⁻¹ * (z⁻¹ * b⁻¹) * (z * a * b) := by simp only [commP]; group
    _ = a⁻¹ * (b⁻¹ * z⁻¹) * (z * a * b) := by rw [h]
    _ = commP a b := by simp only [commP]; group

/-- A central factor in the second slot of a `commP` cancels. -/
theorem commP_central_right (hz : ∀ w : H, Commute z w) (a b : H) :
    commP a (z * b) = commP a b := by
  have h : z⁻¹ * a = a * z⁻¹ := (hz a).inv_left.eq
  calc commP a (z * b) = a⁻¹ * b⁻¹ * (z⁻¹ * a) * (z * b) := by simp only [commP]; group
    _ = a⁻¹ * b⁻¹ * (a * z⁻¹) * (z * b) := by rw [h]
    _ = commP a b := by simp only [commP]; group

/-- A central factor in the conjugated slot passes through the conjugation. -/
theorem conjP_central_left (hz : ∀ w : H, Commute z w) (a b : H) :
    conjP (z * a) b = z * conjP a b := by
  have h : b⁻¹ * z = z * b⁻¹ := (hz b).inv_right.symm.eq
  calc conjP (z * a) b = b⁻¹ * z * a * b := by simp only [conjP]; group
    _ = z * b⁻¹ * a * b := by rw [h]
    _ = z * conjP a b := by simp only [conjP]; group

/-- A central factor in the conjugator cancels. -/
theorem conjP_central_right (hz : ∀ w : H, Commute z w) (a b : H) :
    conjP a (z * b) = conjP a b := by
  have h : z⁻¹ * a = a * z⁻¹ := (hz a).inv_left.eq
  calc conjP a (z * b) = b⁻¹ * (z⁻¹ * a) * (z * b) := by simp only [conjP]; group
    _ = b⁻¹ * (a * z⁻¹) * (z * b) := by rw [h]
    _ = conjP a b := by simp only [conjP]; group

/-- Two central involutive factors cancel across a product of inverses (the `r₂` shape
`(conjP x s)⁻¹ · (x³)⁻¹`, where both slots carry the same shift). -/
theorem inv_mul_inv_central (hz : ∀ w : H, Commute z w) (hz2 : z * z = 1) (u v : H) :
    (z * u)⁻¹ * (z * v)⁻¹ = u⁻¹ * v⁻¹ := by
  have h : z⁻¹ * v⁻¹ = v⁻¹ * z⁻¹ := (hz v).inv_inv.eq
  calc (z * u)⁻¹ * (z * v)⁻¹ = u⁻¹ * (z⁻¹ * v⁻¹) * z⁻¹ := by group
    _ = u⁻¹ * (v⁻¹ * z⁻¹) * z⁻¹ := by rw [h]
    _ = u⁻¹ * v⁻¹ * (z * z)⁻¹ := by rw [mul_inv_rev]; group
    _ = u⁻¹ * v⁻¹ := by rw [hz2, inv_one, mul_one]

end CentralShift

section LayerShift

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}

/-- `Zₖ`-elements commute with everything in `Q_{k+1}` (`zLayer_le_center`). -/
theorem zLayer_commute {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k)
    (w : levelQuot G (k + 1)) : Commute z w :=
  (commute_iff_eq z w).mpr (Subgroup.mem_center_iff.mp (zLayer_le_center G k hz) w).symm

/-- `Zₖ` has exponent 2, so its elements are their own inverses. -/
theorem zLayer_inv_self {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact zLayer_sq G hz)

/-- Two lifts of the same level-`k` class differ by a left `Zₖ`-factor. -/
theorem exists_zLayer_mul {x y : levelQuot G (k + 1)}
    (h : levelProj G k x = levelProj G k y) : ∃ z ∈ zLayer G k, x = z * y := by
  refine ⟨x * y⁻¹, ?_, by group⟩
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

/-- Generation is inherited along the tower: `levelProj` is surjective, so it carries a
generating family of `Q_{k+1}` to a generating family of `Qₖ`. -/
theorem closure_range_levelProj {ι : Type*} {T : ι → levelQuot G (k + 1)}
    (hgen : Subgroup.closure (Set.range T) = ⊤) :
    Subgroup.closure (Set.range fun i => levelProj G k (T i)) = ⊤ := by
  have h := congrArg (Subgroup.map (levelProj G k)) hgen
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ (levelProj_surjective G k),
    ← Set.range_comp] at h
  exact h

/-- **`r₀` is insensitive to `Zₖ`-shifts**: exponent sums `(2, 4, 0)` are even and the
commutator absorbs central factors in both slots. -/
theorem d0Word_zLayer_shift {z₀ z₁ z₂ : levelQuot G (k + 1)} (h₀ : z₀ ∈ zLayer G k)
    (h₁ : z₁ ∈ zLayer G k) (h₂ : z₂ ∈ zLayer G k) (a s y : levelQuot G (k + 1)) :
    d0Word (z₀ * a) (z₁ * s) (z₂ * y) = d0Word a s y := by
  have e0 : (z₀ * a) ^ 2 = a ^ 2 := by
    rw [(zLayer_commute h₀ a).mul_pow, zLayer_sq G h₀, one_mul]
  have e1 : (z₁ * s) ^ 4 = s ^ 4 := by
    rw [(zLayer_commute h₁ s).mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      zLayer_sq G h₁, one_pow, one_mul]
  simp only [d0Word, e0, e1, commP_central_left (zLayer_commute h₁),
    commP_central_right (zLayer_commute h₂)]

/-- **`r₂` is insensitive to `Zₖ`-shifts**: exponent sums `(0, −4, 2)` are even; the
`x`-slot shift survives conjugation and cubing but appears twice, and the `s`- and
`y`-slot shifts are absorbed by the conjugation and the commutator. -/
theorem drWord_zLayer_shift {z₀ z₁ z₂ : levelQuot G (k + 1)} (h₀ : z₀ ∈ zLayer G k)
    (h₁ : z₁ ∈ zLayer G k) (h₂ : z₂ ∈ zLayer G k) (s x y : levelQuot G (k + 1)) :
    drWord (z₀ * s) (z₁ * x) (z₂ * y) = drWord s x y := by
  have hx : conjP (z₁ * x) (z₀ * s) = z₁ * conjP x s := by
    rw [conjP_central_right (zLayer_commute h₀), conjP_central_left (zLayer_commute h₁)]
  have hy : conjP (z₂ * y) (z₀ * s) = z₂ * conjP y s := by
    rw [conjP_central_right (zLayer_commute h₀), conjP_central_left (zLayer_commute h₂)]
  have hcomm : commP (z₂ * y) (z₂ * conjP y s) = commP y (conjP y s) := by
    rw [commP_central_left (zLayer_commute h₂), commP_central_right (zLayer_commute h₂)]
  have h3 : (z₁ * x) ^ 3 = z₁ * x ^ 3 := by
    rw [(zLayer_commute h₁ x).mul_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ,
      zLayer_sq G h₁, one_mul]
  have h2 : (z₂ * y) ^ 2 = y ^ 2 := by
    rw [(zLayer_commute h₂ y).mul_pow, zLayer_sq G h₂, one_mul]
  have hz2 : z₁ * z₁ = 1 := by rw [← pow_two]; exact zLayer_sq G h₁
  simp only [drWord, hx, hy, hcomm, h3, h2]
  rw [inv_mul_inv_central (zLayer_commute h₁) hz2]

end LayerShift

/-! ## The defect (plan §2.2; spike §2.1) -/

/-- **The defect `δ(T) ∈ Q_{k+1}(D_R)`, direction 1**: the `r₀`-relator value of the
canonical lift of `T`.  For `T ∈ S⁰ₖ` it lands in `Zₖ` (`defectR0_mem_zLayer`) and is
independent of the choice of lift (`defectR0_eq_of_lift`) — the q = 2 pathology makes it a
genuinely second-order obstruction (plan §2.2). -/
noncomputable def defectR0 (k : ℕ) (T : Fin 3 → levelQuot (DR : Type) k) :
    levelQuot (DR : Type) (k + 1) :=
  d0Word (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
    (canonLift (DR : Type) k (T 2))

/-- **Lift-independence of the defect, direction 1** (plan §2.2: all relator exponent
sums are even and commutators absorb central factors; no relator-kill hypothesis and no
`k`-threshold is needed).  Any coordinatewise lift computes `δ(T)`.  Fill: L4a. -/
theorem defectR0_eq_of_lift (k : ℕ) (T : Fin 3 → levelQuot (DR : Type) k)
    (T' : Fin 3 → levelQuot (DR : Type) (k + 1))
    (hT' : ∀ i, levelProj (DR : Type) k (T' i) = T i) :
    d0Word (T' 0) (T' 1) (T' 2) = defectR0 k T := by
  have key : ∀ i, ∃ z ∈ zLayer (DR : Type) k, T' i = z * canonLift (DR : Type) k (T i) :=
    fun i => exists_zLayer_mul (G := (DR : Type)) (by rw [hT', levelProj_canonLift])
  obtain ⟨z₀, h₀, e₀⟩ := key 0
  obtain ⟨z₁, h₁, e₁⟩ := key 1
  obtain ⟨z₂, h₂, e₂⟩ := key 2
  rw [e₀, e₁, e₂]
  exact d0Word_zLayer_shift h₀ h₁ h₂ _ _ _

/-- The defect of a relator-killing triple lies in the graded layer `Zₖ`
(minimal hypothesis: only the relator clause of `S⁰ₖ` is consumed).  Fill: L4a. -/
theorem defectR0_mem_zLayer (k : ℕ) {T : Fin 3 → levelQuot (DR : Type) k}
    (hrel : d0Word (T 0) (T 1) (T 2) = 1) :
    defectR0 k T ∈ zLayer (DR : Type) k := by
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, defectR0, map_d0Word]
  simpa only [levelProj_canonLift] using hrel

/-- **The defect, direction 2** (`r₂`-relator value of the canonical lift in the
`D₀`-tower). -/
noncomputable def defectR2 (k : ℕ) (T : Fin 3 → levelQuot (D0 : Type) k) :
    levelQuot (D0 : Type) (k + 1) :=
  drWord (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
    (canonLift (D0 : Type) k (T 2))

/-- Lift-independence of the defect, direction 2 (`r₂` exponent sums `(0, −4, 2)` are
even; same central-kernel calculus).  Fill: L4a. -/
theorem defectR2_eq_of_lift (k : ℕ) (T : Fin 3 → levelQuot (D0 : Type) k)
    (T' : Fin 3 → levelQuot (D0 : Type) (k + 1))
    (hT' : ∀ i, levelProj (D0 : Type) k (T' i) = T i) :
    drWord (T' 0) (T' 1) (T' 2) = defectR2 k T := by
  have key : ∀ i, ∃ z ∈ zLayer (D0 : Type) k, T' i = z * canonLift (D0 : Type) k (T i) :=
    fun i => exists_zLayer_mul (G := (D0 : Type)) (by rw [hT', levelProj_canonLift])
  obtain ⟨z₀, h₀, e₀⟩ := key 0
  obtain ⟨z₁, h₁, e₁⟩ := key 1
  obtain ⟨z₂, h₂, e₂⟩ := key 2
  rw [e₀, e₁, e₂]
  exact drWord_zLayer_shift h₀ h₁ h₂ _ _ _

/-- The direction-2 defect of a relator-killing triple lies in `Zₖ`.  Fill: L4a. -/
theorem defectR2_mem_zLayer (k : ℕ) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hrel : drWord (T 0) (T 1) (T 2) = 1) :
    defectR2 k T ∈ zLayer (D0 : Type) k := by
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, defectR2, map_drWord]
  simpa only [levelProj_canonLift] using hrel

/-! ## Restriction maps (plan §2.1 item 2: all three clauses weaken) -/

/-- **Restriction `S^P_{k+1} → S^P_ₖ`, direction 1**: projecting a level-`(k+1)` triple
along the tower lands in the level-`k` set (relator: hom-push; generation: surjectivity
of `levelProj`; χ-clause: `chiLevel_levelProj` + `chiTargetR0_castHom`).  Fill: L4a. -/
theorem sPR0_levelProj {k : ℕ} {T : Fin 3 → levelQuot (DR : Type) (k + 1)}
    (hT : T ∈ sPR0 (k + 1)) :
    (fun i => levelProj (DR : Type) k (T i)) ∈ sPR0 k := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  refine ⟨⟨?_, closure_range_levelProj hgen⟩, fun i => ?_⟩
  · rw [← map_d0Word, hrel, map_one]
  · rw [chiLevel_levelProj, hchi i, chiTargetR0_castHom]

/-- Restriction `S^P_{k+1} → S^P_ₖ`, direction 2.  Fill: L4a. -/
theorem sPR2_levelProj {k : ℕ} {T : Fin 3 → levelQuot (D0 : Type) (k + 1)}
    (hT : T ∈ sPR2 (k + 1)) :
    (fun i => levelProj (D0 : Type) k (T i)) ∈ sPR2 k := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  refine ⟨⟨?_, closure_range_levelProj hgen⟩, fun i => ?_⟩
  · rw [← map_drWord, hrel, map_one]
  · rw [chiLevel_levelProj, hchi i, chiTargetR2_castHom]

/-! ## Base-case calculus (level-2 λ-calculus in `Q₃`, and generation transfer)

The base-case memberships are discharged **structurally** — plan §2.3's sanctioned route
("the witness's relator value traced through the λ-quotient presentation"), not by
enumerating a 256-element model, and with no `native_decide`.  Everything reduces to
inputs frozen upstream:

* `Z₂ = λ₂/λ₃` is central in `Q₃` (`zLayer_le_center`) and has exponent 2 (`zLayer_sq`);
* squares and `commP`-commutators of `G` land in `Z₂` (`sq_mem_twoCentralSucc`,
  `commP_mem_twoCentralSucc`, both proven in `TwoCentralTower.lean`);
* `λₖ` is open (`isOpen_twoCentralSeries`), which converts the presentations'
  *topological* generation into the plain-closure clause of `S⁰ₖ`.

Consequently the relator clause is exactly the spike's §2.2 first-order bookkeeping:
fourth powers die, the `S⁴`/`[y,yˢ]` blocks are inert, and the surviving cross term is
pinned against the source relator one layer down. -/

section BaseCalculus

variable {H : Type*} [Group H]

/-- `conjP` in terms of `commP` (repo convention `conjP x g = g⁻¹xg`, `commP x y =
x⁻¹y⁻¹xy`). -/
private theorem conjP_eq_mul_commP (x g : H) : conjP x g = x * commP x g := by
  simp only [conjP, commP]; group

/-- Left expansion of `commP` over a product. -/
private theorem commP_mul_left (a b c : H) :
    commP (a * b) c = conjP (commP a c) b * commP b c := by
  simp only [conjP, commP]; group

/-- Right expansion of `commP` over a product. -/
private theorem commP_mul_right (a b c : H) :
    commP a (b * c) = commP a c * conjP (commP a b) c := by
  simp only [conjP, commP]; group

/-- `commP` is self-inverse under slot exchange. -/
private theorem commP_inv (a b : H) : (commP a b)⁻¹ = commP b a := by
  simp only [commP]; group

@[simp] private theorem commP_self (a : H) : commP a a = 1 := by
  simp only [commP]; group

@[simp] private theorem conjP_one_left (g : H) : conjP (1 : H) g = 1 := by
  simp only [conjP]; group

/-- A `commP` against a commuting element is trivial. -/
private theorem commP_eq_one_of_commute {x y : H} (h : Commute x y) : commP x y = 1 := by
  have hxy : x * y = y * x := h.eq
  simp only [commP]
  calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * (y⁻¹ * (x * y)) := by group
    _ = x⁻¹ * (y⁻¹ * (y * x)) := by rw [hxy]
    _ = 1 := by group

end BaseCalculus

section LevelThree

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Squares of `G`-images land in `Z₂ ≤ Q₃`. -/
private theorem levelMk_sq_mem_zLayer (g : G) : levelMk G 3 g ^ 2 ∈ zLayer G 2 :=
  ⟨g ^ 2, sq_mem_twoCentralSucc (Subgroup.mem_top g), map_pow (levelMk G 3) g 2⟩

/-- `commP`-commutators of `G`-images land in `Z₂ ≤ Q₃`. -/
private theorem levelMk_commP_mem_zLayer (a b : G) :
    commP (levelMk G 3 a) (levelMk G 3 b) ∈ zLayer G 2 :=
  ⟨commP a b, commP_mem_twoCentralSucc (Subgroup.mem_top a) b,
    Marking.map_commP (levelMk G 3) a b⟩

/-- `Z₂`-elements are central in `Q₃`, so conjugation fixes them. -/
private theorem conjP_of_mem_zLayer {z : levelQuot G 3} (hz : z ∈ zLayer G 2)
    (g : levelQuot G 3) : conjP z g = z := by
  have hc := Subgroup.mem_center_iff.mp (zLayer_le_center G 2 hz) g
  rw [conjP, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]

/-- A `commP` against a `Z₂`-element is trivial (centrality). -/
private theorem commP_of_mem_zLayer_right (a : levelQuot G 3) {z : levelQuot G 3}
    (hz : z ∈ zLayer G 2) : commP a z = 1 :=
  commP_eq_one_of_commute (Subgroup.mem_center_iff.mp (zLayer_le_center G 2 hz) a)

/-- Fourth powers of `G`-images die in `Q₃` (`λ₂² ⊆ λ₃`). -/
private theorem levelMk_pow_four (g : G) : levelMk G 3 g ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact zLayer_sq G (levelMk_sq_mem_zLayer g)

/-- The mod-`2^k` *value* of a level shadow on a residue — the form the χ-clause checks
reduce to after `Units.ext`. -/
private theorem chiLevel_levelMk_val (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (k : ℕ) (g : G) :
    ((chiLevel χ k (levelMk G k g) : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))
      = PadicInt.toZModPow k ((χ g : ℤ_[2]ˣ) : ℤ_[2]) := rfl

/-- **Generation transfer**: if `S` topologically generates `G` and `λₖ` is open, the
image of `S` generates `Qₖ` as a plain subgroup — the form the `S⁰ₖ`-clause asks for. -/
private theorem closure_image_levelMk_eq_top {k : ℕ}
    (hopen : IsOpen ((twoCentralSeries G k : Subgroup G) : Set G))
    {S : Set G} (hS : (Subgroup.closure S).topologicalClosure = ⊤) :
    Subgroup.closure (levelMk G k '' S) = ⊤ := by
  set K : Subgroup (levelQuot G k) := Subgroup.closure (levelMk G k '' S) with hKdef
  have hlam : twoCentralSeries G k ≤ K.comap (levelMk G k) := by
    intro g hg
    have h1 : levelMk G k g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    simp only [Subgroup.mem_comap, h1, one_mem]
  have hPopen : IsOpen ((K.comap (levelMk G k) : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono hlam hopen
  have hSP : Subgroup.closure S ≤ K.comap (levelMk G k) := by
    rw [Subgroup.closure_le]
    exact fun g hg => Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hPtop : K.comap (levelMk G k) = ⊤ := by
    have h := Subgroup.topologicalClosure_minimal _ hSP
      (Subgroup.isClosed_of_isOpen _ hPopen)
    rw [hS] at h
    exact top_le_iff.mp h
  ext q
  obtain ⟨g, rfl⟩ := levelMk_surjective G k q
  simpa using (hPtop ▸ Subgroup.mem_top g : g ∈ K.comap (levelMk G k))

/-! ### Class-2 calculus in `Q₃`

Every `commP` and every square of `Q₃` lands in the central exponent-2 layer `Z₂`, so `Q₃`
has class `≤ 2`: `commP` is bimultiplicative and squaring is quadratic.  These are the two
facts that cut `Z₂` down from the `Q₃ × Q₃`-worth of generators supplied by
`λ₂ = cl(λ₁²[λ₁, λ₁])` to the squares and pairwise brackets of a generating triple. -/

/-- Every `commP` in `Q₃` lands in `Z₂`. -/
theorem commP_mem_zLayer_two (p q : levelQuot G 3) : commP p q ∈ zLayer G 2 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 3 p
  obtain ⟨b, rfl⟩ := levelMk_surjective G 3 q
  exact levelMk_commP_mem_zLayer a b

/-- Every square in `Q₃` lands in `Z₂`. -/
theorem sq_mem_zLayer_two (p : levelQuot G 3) : p ^ 2 ∈ zLayer G 2 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 3 p
  exact levelMk_sq_mem_zLayer a

@[simp] private theorem commP_one_left3 (p : levelQuot G 3) : commP 1 p = 1 := by
  simp only [commP]; group

@[simp] private theorem commP_one_right3 (p : levelQuot G 3) : commP p 1 = 1 := by
  simp only [commP]; group

/-- **`commP` is multiplicative in the left slot** (class 2: the conjugation in
`commP_mul_left` acts on a central element). -/
theorem commP_mul_left_of_three (p q r : levelQuot G 3) :
    commP (p * q) r = commP p r * commP q r := by
  rw [commP_mul_left, conjP_of_mem_zLayer (commP_mem_zLayer_two p r)]

/-- **`commP` is multiplicative in the right slot** (class 2). -/
theorem commP_mul_right_of_three (p q r : levelQuot G 3) :
    commP p (q * r) = commP p r * commP p q := by
  rw [commP_mul_right, conjP_of_mem_zLayer (commP_mem_zLayer_two p q)]

/-- `commP` inverts in the left slot. -/
theorem commP_inv_left_of_three (p r : levelQuot G 3) : commP p⁻¹ r = (commP p r)⁻¹ := by
  have h := commP_mul_left_of_three p p⁻¹ r
  rw [mul_inv_cancel, commP_one_left3] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- `commP` inverts in the right slot. -/
theorem commP_inv_right_of_three (p r : levelQuot G 3) : commP p r⁻¹ = (commP p r)⁻¹ := by
  have h := commP_mul_right_of_three p r r⁻¹
  rw [mul_inv_cancel, commP_one_right3] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **Squaring is quadratic in `Q₃`**: `(pq)² = p²q²[p, q]⁻¹`. -/
theorem sq_mul_of_three (p q : levelQuot G 3) :
    (p * q) ^ 2 = p ^ 2 * q ^ 2 * (commP p q)⁻¹ := by
  have hz : ∀ w, Commute (commP p q) w := zLayer_commute (commP_mem_zLayer_two p q)
  have hqp : q * p = p * q * (commP p q)⁻¹ := by simp only [commP]; group
  calc (p * q) ^ 2 = p * (q * p) * q := by rw [pow_two]; group
    _ = p * (p * q * (commP p q)⁻¹) * q := by rw [hqp]
    _ = p * p * q * ((commP p q)⁻¹ * q) := by group
    _ = p * p * q * (q * (commP p q)⁻¹) := by rw [(hz q).inv_left.eq]
    _ = p ^ 2 * q ^ 2 * (commP p q)⁻¹ := by rw [pow_two, pow_two]; group

/-- **Every bracket of `Q₃` lies in a subgroup holding the six generator brackets.**
Bimultiplicativity in both slots turns the closure induction on each argument into
bookkeeping over the nine generator pairs. -/
theorem commP_mem_of_gens {a b c : levelQuot G 3}
    (hgen : Subgroup.closure ({a, b, c} : Set (levelQuot G 3)) = ⊤)
    {K : Subgroup (levelQuot G 3)} (hab : commP a b ∈ K) (hac : commP a c ∈ K)
    (hbc : commP b c ∈ K) (p q : levelQuot G 3) : commP p q ∈ K := by
  have hgens : ∀ w ∈ ({a, b, c} : Set (levelQuot G 3)), ∀ v, commP v w ∈ K := by
    intro w hw v
    have hv : v ∈ Subgroup.closure ({a, b, c} : Set (levelQuot G 3)) := by rw [hgen]; trivial
    induction hv using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
      rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
        first
          | (rw [commP_self]; exact K.one_mem)
          | exact hab
          | exact hac
          | exact hbc
          | (rw [← commP_inv]; exact K.inv_mem hab)
          | (rw [← commP_inv]; exact K.inv_mem hac)
          | (rw [← commP_inv]; exact K.inv_mem hbc)
    | one => rw [commP_one_left3]; exact K.one_mem
    | mul u v _ _ hu hv => rw [commP_mul_left_of_three]; exact K.mul_mem hu hv
    | inv u _ hu => rw [commP_inv_left_of_three]; exact K.inv_mem hu
  have hq : q ∈ Subgroup.closure ({a, b, c} : Set (levelQuot G 3)) := by rw [hgen]; trivial
  induction hq using Subgroup.closure_induction with
  | mem u hu => exact hgens u hu p
  | one => rw [commP_one_right3]; exact K.one_mem
  | mul u v _ _ hu hv => rw [commP_mul_right_of_three]; exact K.mul_mem hv hu
  | inv u _ hu => rw [commP_inv_right_of_three]; exact K.inv_mem hu

/-- **Every square of `Q₃` lies in a subgroup holding the three generator squares and the
six generator brackets** (`sq_mul_of_three` for the product step). -/
theorem sq_mem_of_gens {a b c : levelQuot G 3}
    (hgen : Subgroup.closure ({a, b, c} : Set (levelQuot G 3)) = ⊤)
    {K : Subgroup (levelQuot G 3)} (ha : a ^ 2 ∈ K) (hb : b ^ 2 ∈ K) (hc : c ^ 2 ∈ K)
    (hab : commP a b ∈ K) (hac : commP a c ∈ K) (hbc : commP b c ∈ K) (p : levelQuot G 3) :
    p ^ 2 ∈ K := by
  have hp : p ∈ Subgroup.closure ({a, b, c} : Set (levelQuot G 3)) := by rw [hgen]; trivial
  induction hp using Subgroup.closure_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    exacts [ha, hb, hc]
  | one => rw [one_pow]; exact K.one_mem
  | mul u v _ _ hu hv =>
    rw [sq_mul_of_three]
    exact K.mul_mem (K.mul_mem hu hv) (K.inv_mem (commP_mem_of_gens hgen hab hac hbc u v))
  | inv u _ hu => rw [inv_pow]; exact K.inv_mem hu

/-- **Layer generation at level 3.**  A subgroup `K` of `Q₃` containing the squares and the
pairwise brackets of a topologically generating triple contains the whole layer `Z₂`.
`λ₂ = cl(λ₁²[λ₁, λ₁])` offers one generator of `Z₂` per square and per commutator of `Q₃`;
the class-2 calculus reduces those to the three squares and three brackets, and the openness
of `λ₃` makes the preimage of `K` closed, so it absorbs the topological closure. -/
theorem zLayer_two_le_of_gens (hopen : IsOpen ((twoCentralSeries G 3 : Subgroup G) : Set G))
    {a b c : levelQuot G 3}
    (hgen : Subgroup.closure ({a, b, c} : Set (levelQuot G 3)) = ⊤)
    {K : Subgroup (levelQuot G 3)} (ha : a ^ 2 ∈ K) (hb : b ^ 2 ∈ K) (hc : c ^ 2 ∈ K)
    (hab : commP a b ∈ K) (hac : commP a c ∈ K) (hbc : commP b c ∈ K) :
    zLayer G 2 ≤ K := by
  have hlam : twoCentralSeries G 3 ≤ K.comap (levelMk G 3) := by
    intro g hg
    have h1 : levelMk G 3 g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    simp only [Subgroup.mem_comap, h1, one_mem]
  have hclosed : IsClosed ((K.comap (levelMk G 3) : Subgroup G) : Set G) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono hlam hopen)
  rw [show zLayer G 2 = (twoCentralSeries G 2).map (levelMk G 3) from rfl,
    Subgroup.map_le_iff_le_comap,
    show twoCentralSeries G 2 = twoCentralSucc (⊤ : Subgroup G) from rfl, twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hclosed
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, -, rfl⟩
    simpa only [SetLike.mem_coe, Subgroup.mem_comap, map_pow] using
      sq_mem_of_gens hgen ha hb hc hab hac hbc (levelMk G 3 g)
  · rw [Subgroup.commutator_le]
    intro u _ v _
    have h := commP_mem_of_gens hgen hab hac hbc (levelMk G 3 u)⁻¹ (levelMk G 3 v)⁻¹
    rw [commP] at h
    rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    simpa using h

end LevelThree

/-- `D_R` is topologically generated by the finite set `{s, x, y}` (local packaging of
`dr_topGen`; `Assembly.lean`'s `drFinsetTopGen` is the same statement, replicated here to
keep this file upstream of the assembly). -/
private theorem drFg : ∃ s : Finset (DR : Type),
    (Subgroup.closure (s : Set (DR : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{drS, drX, drY}, ?_⟩
  have h : (({drS, drX, drY} : Finset (DR : Type)) : Set (DR : Type))
      = ({drS, drX, drY} : Set (DR : Type)) := by simp
  rw [h]
  exact dr_topGen

/-- `D₀` is topologically generated by the finite set `{A, S, Y}` (local packaging of
`SectionThree.topGen_d0`). -/
private theorem d0Fg : ∃ s : Finset (D0 : Type),
    (Subgroup.closure (s : Set (D0 : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{d0A, d0S, d0Y}, ?_⟩
  have h : (({d0A, d0S, d0Y} : Finset (D0 : Type)) : Set (D0 : Type))
      = ({d0A, d0S, d0Y} : Set (D0 : Type)) := by simp
  rw [h]
  exact SectionThree.topGen_d0

/-- The `D_R`-tower levels are open. -/
private theorem isOpen_dr (k : ℕ) :
    IsOpen ((twoCentralSeries (DR : Type) k : Subgroup (DR : Type)) : Set (DR : Type)) :=
  isOpen_twoCentralSeries (DR : Type) drFg isProP_DR k

/-- The `D₀`-tower levels are open. -/
private theorem isOpen_d0 (k : ℕ) :
    IsOpen ((twoCentralSeries (D0 : Type) k : Subgroup (D0 : Type)) : Set (D0 : Type)) :=
  isOpen_twoCentralSeries (D0 : Type) d0Fg SectionThree.d0_isProP k

/-- The three marked generators generate every `D_R`-tower level. -/
private theorem closure_drGens_eq_top (k : ℕ) :
    Subgroup.closure (levelMk (DR : Type) k '' {drS, drX, drY}) = ⊤ :=
  closure_image_levelMk_eq_top (isOpen_dr k) dr_topGen

/-- The three marked generators generate every `D₀`-tower level. -/
private theorem closure_d0Gens_eq_top (k : ℕ) :
    Subgroup.closure (levelMk (D0 : Type) k '' {d0A, d0S, d0Y}) = ⊤ :=
  closure_image_levelMk_eq_top (isOpen_d0 k) SectionThree.topGen_d0

/-! ## Base cases at `k₀ = 3` (spike §2.4, §3.1, §3.4)

The level-3 witnesses live in `Q₃` of order `2^8 = 256`; L3 discharges membership by
transport to a concrete 256-element model and `decide`/structured verification
(plan §2.3), checking the χ-clause mod `8` against `chiTargetR0_three`/`chiTargetR2_three`.

Level-4 stress vectors (spike §3.4, NOT frozen as statements — optional extra greens for
L3, words recorded for reproducibility; repo convention `[s,y] = s⁻¹y⁻¹sy`):
* direction 1, level 4: `t₁ = y·s·x⁻¹·s·x·s⁻¹·y⁻¹·s·y·x⁻¹·y⁻¹·x·y`, `t₂ = s·x·[s,y]`,
  `t₃ = x·[s,y]` (χ-depths `(6, 5, 5)`).
* direction 2, level 4: the spike's `witness_words.txt` triple of lengths `(12, 7, 11)`
  with χ-depths `(4, 5, 6)`. -/

/-- **The `D_R` relator read in `Q₃`**: it collapses to `y² = [x, s]` (repo `commP`).
The `[y, yˢ]` block is inert (a `commP` against the `Z₂`-element `[y, s]`), `x⁴ = 1` in `Q₃`
(`λ₂² ⊆ λ₃`), and `conjP x s = x · [x, s]`, so the two surviving terms are `y²` and the
cross term `[x, s]`.  This is the single linear relation that cuts `dim Z₂` from `6` to
`5`; it is what makes `|Q₃| = 2⁸` rather than `2⁹`. -/
theorem levelMk_drY_sq :
    levelMk (DR : Type) 3 drY ^ 2
      = commP (levelMk (DR : Type) 3 drX) (levelMk (DR : Type) 3 drS) := by
  set s := levelMk (DR : Type) 3 drS with hs
  set x := levelMk (DR : Type) 3 drX with hx
  set y := levelMk (DR : Type) 3 drY with hy
  have hrel : drWord s x y = 1 := by
    rw [hs, hx, hy, ← map_drWord (levelMk (DR : Type) 3), dr_relation, map_one]
  have hzys : commP y s ∈ zLayer (DR : Type) 2 := levelMk_commP_mem_zLayer drY drS
  have hx4 : x ^ 4 = 1 := levelMk_pow_four drX
  have hyys : commP y (conjP y s) = 1 := by
    rw [conjP_eq_mul_commP, commP_mul_right, commP_self, conjP_one_left, mul_one]
    exact commP_of_mem_zLayer_right y hzys
  set c := commP x s with hc
  have h : (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s) = 1 := hrel
  rw [hyys, mul_one, conjP_eq_mul_commP, ← hc] at h
  have hstep : (x * c)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 = c⁻¹ * ((x ^ 4)⁻¹ * y ^ 2) := by group
  rw [hstep, hx4, inv_one, one_mul] at h
  exact (inv_mul_eq_one.mp h).symm

/-- The direction-1 base witness in `Q₃(D_R)` (spike §3.1/§3.4): the `(A,S,Y)`-slot
triple `(y, s·x, x)` — mod-8 χ-values `(7, 1, 5)`, matching `chiTargetR0_three`. -/
noncomputable def witnessR0 : Fin 3 → levelQuot (DR : Type) 3 :=
  ![levelMk (DR : Type) 3 drY, levelMk (DR : Type) 3 (drS * drX), levelMk (DR : Type) 3 drX]

/-- The `r₀`-relator dies at the direction-1 witness.  Spike §2.2's bookkeeping, traced
levelwise: `(s·x)⁴` is a square of a `λ₂`-element hence inert, `[s·x, x] ≡ [s, x]` by
left-expansion plus centrality, and the source relator `r₂` pins `y² = [x, s]` — the two
surviving terms are mutually inverse. -/
private theorem witnessR0_relator :
    d0Word (witnessR0 0) (witnessR0 1) (witnessR0 2) = 1 := by
  show d0Word (levelMk (DR : Type) 3 drY) (levelMk (DR : Type) 3 (drS * drX))
    (levelMk (DR : Type) 3 drX) = 1
  set s := levelMk (DR : Type) 3 drS with hs
  set x := levelMk (DR : Type) 3 drX with hx
  set y := levelMk (DR : Type) 3 drY with hy
  have hsx : levelMk (DR : Type) 3 (drS * drX) = s * x := map_mul _ _ _
  rw [hsx]
  have hzsx : commP s x ∈ zLayer (DR : Type) 2 := levelMk_commP_mem_zLayer drS drX
  have hsx4 : (s * x) ^ 4 = 1 := by rw [← hsx]; exact levelMk_pow_four _
  -- the source relator pins `y²` against the surviving cross term
  have hy2 : y ^ 2 = commP x s := levelMk_drY_sq
  rw [d0Word, hsx4, mul_one, commP_mul_left, commP_self, mul_one,
    conjP_of_mem_zLayer hzsx, hy2, ← commP_inv, inv_mul_cancel]

/-- The direction-1 witness generates `Q₃`: the three entries recover `s`, `x`, `y`, which
generate every tower level (`closure_drGens_eq_top`). -/
private theorem witnessR0_gen : Subgroup.closure (Set.range witnessR0) = ⊤ := by
  set K := Subgroup.closure (Set.range witnessR0) with hK
  have hy : levelMk (DR : Type) 3 drY ∈ K := Subgroup.subset_closure ⟨0, rfl⟩
  have hsx : levelMk (DR : Type) 3 (drS * drX) ∈ K := Subgroup.subset_closure ⟨1, rfl⟩
  have hx : levelMk (DR : Type) 3 drX ∈ K := Subgroup.subset_closure ⟨2, rfl⟩
  have hs : levelMk (DR : Type) 3 drS ∈ K := by
    have h := K.mul_mem hsx (K.inv_mem hx)
    rwa [map_mul, mul_assoc, mul_inv_cancel, mul_one] at h
  rw [eq_top_iff, ← closure_drGens_eq_top 3, Subgroup.closure_le]
  rintro q ⟨g, hg, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  exacts [hs, hx, hy]

/-- The χ-clause at the direction-1 witness: mod-8 values `(Y, S·X, X) ≡ (7, 1, 5)` match
`chiTargetR0_three`. -/
private theorem witnessR0_chi (i : Fin 3) :
    chiLevel chiR 3 (witnessR0 i) = chiTargetR0 3 i := by
  have hX : PadicInt.toZModPow 3 rootX = 5 := rootX_toZModPow_eq (by decide)
  have hS : PadicInt.toZModPow 3 Sval = 5 := Sval_toZModPow_eq hX (by decide)
  have hY : PadicInt.toZModPow 3 Yval = 7 := by rw [Yval_toZModPow_eq hX]; decide
  refine Units.ext ?_
  rw [chiTargetR0_three i]
  fin_cases i
  · show PadicInt.toZModPow 3 ((chiR drY : ℤ_[2]ˣ) : ℤ_[2]) = 7
    rw [chiR_drY, val_YvalUnit, hY]
  · show PadicInt.toZModPow 3 ((chiR (drS * drX) : ℤ_[2]ˣ) : ℤ_[2]) = 1
    rw [map_mul, Units.val_mul, map_mul, chiR_drS, chiR_drX, val_SvalUnit, val_rootXUnit,
      hS, hX]
    decide
  · show PadicInt.toZModPow 3 ((chiR drX : ℤ_[2]ˣ) : ℤ_[2]) = 5
    rw [chiR_drX, val_rootXUnit, hX]

/-- **Base case, direction 1** (spike §2.4: `S^P₃ ≠ ∅` by explicit witness).  Fill: L3
(`decide`/structured verification in a 256-element model of `Q₃`). -/
theorem witnessR0_mem : witnessR0 ∈ sPR0 3 :=
  ⟨⟨witnessR0_relator, witnessR0_gen⟩, witnessR0_chi⟩

/-- `S^P₃ ≠ ∅`, direction 1 (packaging; not a fill target). -/
theorem sPR0_three_nonempty : (sPR0 3).Nonempty := ⟨witnessR0, witnessR0_mem⟩

/-- The direction-2 base witness in `Q₃(D₀)` (spike §3.1/§3.4): the `(s,x,y)`-slot triple
`(S·Y, Y, A)` — mod-8 χ₀-values `(5, 5, 7)`, matching `chiTargetR2_three`. -/
noncomputable def witnessR2 : Fin 3 → levelQuot (D0 : Type) 3 :=
  ![levelMk (D0 : Type) 3 (d0S * d0Y), levelMk (D0 : Type) 3 d0Y, levelMk (D0 : Type) 3 d0A]

/-- The `r₂`-relator dies at the direction-2 witness.  Mirror of `witnessR0_relator`:
`Y⁴` is inert, the `x`-block collapses to the single cross term `[Y, S]`, the `[A, A^{SY}]`
block is inert, and the source relator `r₀` pins `A² = [Y, S]`. -/
private theorem witnessR2_relator :
    drWord (witnessR2 0) (witnessR2 1) (witnessR2 2) = 1 := by
  show drWord (levelMk (D0 : Type) 3 (d0S * d0Y)) (levelMk (D0 : Type) 3 d0Y)
    (levelMk (D0 : Type) 3 d0A) = 1
  set a := levelMk (D0 : Type) 3 d0A with ha
  set sg := levelMk (D0 : Type) 3 d0S with hsg
  set yv := levelMk (D0 : Type) 3 d0Y with hyv
  have hsy : levelMk (D0 : Type) 3 (d0S * d0Y) = sg * yv := map_mul _ _ _
  rw [hsy]
  have hrel : d0Word a sg yv = 1 := by
    rw [ha, hsg, hyv, ← map_d0Word (levelMk (D0 : Type) 3), d0Word_eq_one, map_one]
  have hzys : commP yv sg ∈ zLayer (D0 : Type) 2 := levelMk_commP_mem_zLayer d0Y d0S
  have hzasy : commP a (sg * yv) ∈ zLayer (D0 : Type) 2 := by
    rw [← hsy, ha]; exact levelMk_commP_mem_zLayer d0A (d0S * d0Y)
  have hsg4 : sg ^ 4 = 1 := levelMk_pow_four d0S
  have hyv4 : yv ^ 4 = 1 := levelMk_pow_four d0Y
  -- the `[A, A^{SY}]` block is inert
  have haa : commP a (conjP a (sg * yv)) = 1 := by
    rw [conjP_eq_mul_commP, commP_mul_right a a (commP a (sg * yv)), commP_self,
      conjP_one_left, mul_one]
    exact commP_of_mem_zLayer_right a hzasy
  -- the conjugation collapses to the single surviving cross term
  have hcv : conjP yv (sg * yv) = yv * commP yv sg := by
    rw [conjP_eq_mul_commP, commP_mul_right yv sg yv, commP_self, one_mul,
      conjP_of_mem_zLayer hzys]
  -- the source relator pins `A²`
  have ha2 : a ^ 2 = commP yv sg := by
    have h : a ^ 2 * sg ^ 4 * commP sg yv = 1 := hrel
    rw [hsg4, mul_one, ← commP_inv yv sg] at h
    exact mul_inv_eq_one.mp h
  rw [drWord, hcv, haa, mul_one]
  have hstep : (yv * commP yv sg)⁻¹ * (yv ^ 3)⁻¹ * a ^ 2
      = (commP yv sg)⁻¹ * ((yv ^ 4)⁻¹ * a ^ 2) := by group
  rw [hstep, hyv4, inv_one, one_mul, ha2, inv_mul_cancel]

/-- The direction-2 witness generates `Q₃`. -/
private theorem witnessR2_gen : Subgroup.closure (Set.range witnessR2) = ⊤ := by
  set K := Subgroup.closure (Set.range witnessR2) with hK
  have hsy : levelMk (D0 : Type) 3 (d0S * d0Y) ∈ K := Subgroup.subset_closure ⟨0, rfl⟩
  have hy : levelMk (D0 : Type) 3 d0Y ∈ K := Subgroup.subset_closure ⟨1, rfl⟩
  have ha : levelMk (D0 : Type) 3 d0A ∈ K := Subgroup.subset_closure ⟨2, rfl⟩
  have hs : levelMk (D0 : Type) 3 d0S ∈ K := by
    have h := K.mul_mem hsy (K.inv_mem hy)
    rwa [map_mul, mul_assoc, mul_inv_cancel, mul_one] at h
  rw [eq_top_iff, ← closure_d0Gens_eq_top 3, Subgroup.closure_le]
  rintro q ⟨g, hg, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  exacts [ha, hs, hy]

/-- The χ-clause at the direction-2 witness: mod-8 values `(S·Y, Y, A) ↦ (5, 5, 7)` under
`χ₀`, matching `chiTargetR2_three`. -/
private theorem witnessR2_chi (i : Fin 3) :
    chiLevel chiD0pres 3 (witnessR2 i) = chiTargetR2 3 i := by
  have heta : PadicInt.toZModPow 3 ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 :=
    (by decide : ∀ z : ZMod (2 ^ 3), z * (-3) = 1 → z = 5) _ (etaUnit_toZModPow_mul 3)
  refine Units.ext ?_
  rw [chiTargetR2_three i]
  fin_cases i
  · show PadicInt.toZModPow 3 ((chiD0pres (d0S * d0Y) : ℤ_[2]ˣ) : ℤ_[2]) = 5
    rw [map_mul, Units.val_mul, map_mul, chiD0pres_d0S, chiD0pres_d0Y]
    simp only [Units.val_one, map_one, one_mul]
    exact heta
  · show PadicInt.toZModPow 3 ((chiD0pres d0Y : ℤ_[2]ˣ) : ℤ_[2]) = 5
    rw [chiD0pres_d0Y, heta]
  · show PadicInt.toZModPow 3 ((chiD0pres d0A : ℤ_[2]ˣ) : ℤ_[2]) = 7
    rw [chiD0pres_d0A]
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]
    decide

/-- **Base case, direction 2**.  Fill: L3. -/
theorem witnessR2_mem : witnessR2 ∈ sPR2 3 :=
  ⟨⟨witnessR2_relator, witnessR2_gen⟩, witnessR2_chi⟩

/-- `S^P₃ ≠ ∅`, direction 2 (packaging; not a fill target). -/
theorem sPR2_three_nonempty : (sPR2 3).Nonempty := ⟨witnessR2, witnessR2_mem⟩

/-! ### Tower-size regression pins (spike §1 table; L1 stress contract for L3)

`log₂|Q₂| = 3`, `log₂|Q₃| = 8`, `dim Z₁ = 3` — identical for both towers (f-blind,
spike §1), so pinned on the `D_R`-side only. -/

section TowerSizes

/-! `Q₂` is the Frattini quotient of `D_R`: squares and commutators lie in `λ₂`, so `Q₂` is
abelian of exponent 2, and it is generated by the three marked generators — whence
`|Q₂| ≤ 2³`.  The elementary-abelian marking `(s, x, y) ↦` standard basis of `(ℤ/2)³` —
a `drLiftHom` at a concrete finite 2-group with the relator killed by the house `decide`
pattern (`DRPresentation.lean`'s `drWord_zmod8`/`drWord_d4`) — gives the matching lower
bound. -/

/-- The elementary-abelian marking target `(ℤ/2)³`. -/
private abbrev VR : Type := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)

private def vrS : VR := Multiplicative.ofAdd (1, 0, 0)
private def vrX : VR := Multiplicative.ofAdd (0, 1, 0)
private def vrY : VR := Multiplicative.ofAdd (0, 0, 1)

private theorem isProP_two_VR : IsProP 2 VR :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 3)
    (by rw [Nat.card_eq_fintype_card]; decide))

private theorem card_VR : Nat.card VR = 8 := by rw [Nat.card_eq_fintype_card]; decide

/-- The `r₂`-relator dies at the elementary-abelian marking. -/
private theorem drWord_VR : drWord vrS vrX vrY = 1 := by decide

/-- The elementary-abelian marking of `D_R`. -/
private noncomputable def psiR : ContinuousMonoidHom (DR : Type) VR :=
  drLiftHom isProP_two_VR ![vrS, vrX, vrY] (by show drWord vrS vrX vrY = 1; exact drWord_VR)

@[simp] private theorem psiR_drS : psiR drS = vrS := drLiftHom_S _ _ _
@[simp] private theorem psiR_drX : psiR drX = vrX := drLiftHom_X _ _ _
@[simp] private theorem psiR_drY : psiR drY = vrY := drLiftHom_Y _ _ _

/-- `λ₂` dies under the marking: its target is abelian of exponent 2, and the kernel is
closed, so it absorbs the whole topological closure. -/
private theorem twoCentralSeries_two_le_ker_psiR :
    twoCentralSeries (DR : Type) 2 ≤ psiR.toMonoidHom.ker := by
  have hker : IsClosed ((psiR.toMonoidHom.ker : Subgroup (DR : Type)) : Set (DR : Type)) := by
    have h : ((psiR.toMonoidHom.ker : Subgroup (DR : Type)) : Set (DR : Type))
        = psiR ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      rfl
    rw [h]
    exact isClosed_singleton.preimage psiR.continuous_toFun
  refine Subgroup.topologicalClosure_minimal _ ?_ hker
  rw [sup_le_iff]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro v ⟨g, -, rfl⟩
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_pow]
    exact (by decide : ∀ w : VR, w ^ 2 = 1) _
  · rw [Subgroup.commutator_le]
    intro g _ h _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    exact (by decide : ∀ a b : VR, a * b * a⁻¹ * b⁻¹ = 1) _ _

/-- In a group of exponent 2, powers depend only on the parity of the exponent. -/
private theorem pow_eq_pow_mod_two {H : Type*} [Group H] (hexp : ∀ a : H, a ^ 2 = 1) (a : H)
    (n : ℕ) : a ^ n = a ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, mul_comm 2 (n / 2), pow_mul, hexp, one_mul]

/-- `commP a b = 1` is commutation. -/
private theorem mul_comm_of_commP_eq_one {H : Type*} [Group H] {a b : H} (h : commP a b = 1) :
    a * b = b * a := by
  have h' : a⁻¹ * b⁻¹ * a * b = 1 := h
  calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
    _ = b * a := by rw [h', mul_one]

/-- Every element of `Q₂` squares to `1` (`λ₁² ⊆ λ₂`). -/
private theorem levelQuot_two_sq (q : levelQuot (DR : Type) 2) : q ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := levelMk_surjective (DR : Type) 2 q
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (sq_mem_twoCentralSucc (Subgroup.mem_top g))

/-- `Q₂` is abelian (`[λ₁, λ₁] ⊆ λ₂`). -/
private theorem levelQuot_two_mul_comm (a b : levelQuot (DR : Type) 2) : a * b = b * a := by
  obtain ⟨g, rfl⟩ := levelMk_surjective (DR : Type) 2 a
  obtain ⟨h, rfl⟩ := levelMk_surjective (DR : Type) 2 b
  refine mul_comm_of_commP_eq_one ?_
  rw [← Marking.map_commP]
  exact (QuotientGroup.eq_one_iff _).mpr (commP_mem_twoCentralSucc (Subgroup.mem_top g) h)

/-- **An abelian group of exponent 2 on three generators has at most `2³` elements.**
Stated abstractly (the word bookkeeping is done once, over a variable group, so the
commutative normalisation never meets the quotient's instance stack). -/
private theorem card_le_eight_of_three_gens {H : Type*} [Group H] [Finite H]
    (hc : ∀ u v : H, u * v = v * u) (hsq : ∀ u : H, u ^ 2 = 1) {a b c : H}
    (hgen : Subgroup.closure ({a, b, c} : Set H) = ⊤) : Nat.card H ≤ 8 := by
  letI : CommGroup H := { ‹Group H› with mul_comm := hc }
  have hword : ∀ q : H, ∃ i j k : ℕ, q = a ^ i * b ^ j * c ^ k := by
    intro q
    have hq : q ∈ Subgroup.closure ({a, b, c} : Set H) := by rw [hgen]; trivial
    induction hq using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, k, rfl⟩ := hu
      obtain ⟨i', j', k', rfl⟩ := hv
      refine ⟨i + i', j + j', k + k', ?_⟩
      simp only [pow_add]
      simp only [mul_assoc, mul_left_comm]
    | inv u _ hu =>
      obtain ⟨i, j, k, rfl⟩ := hu
      exact ⟨i, j, k, by rw [inv_eq_iff_mul_eq_one, ← sq]; exact hsq _⟩
  have hsurj : Function.Surjective
      (fun t : Fin 2 × Fin 2 × Fin 2 => a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ)) := by
    intro q
    obtain ⟨i, j, k, rfl⟩ := hword q
    refine ⟨(⟨i % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩,
      ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only
    rw [← pow_eq_pow_mod_two hsq, ← pow_eq_pow_mod_two hsq, ← pow_eq_pow_mod_two hsq]
  calc Nat.card H ≤ Nat.card (Fin 2 × Fin 2 × Fin 2) := Nat.card_le_card_of_surjective _ hsurj
    _ = 8 := by simp

/-- **Transport of a spanning family into a subgroup.**  If `N` is contained in the closure
of a set `S` of its own elements, then the corresponding subtype elements generate `N`. -/
private theorem closure_subtype_eq_top {H : Type*} [Group H] {N : Subgroup H} {S : Set H}
    (hSN : S ⊆ (N : Set H)) (hN : N ≤ Subgroup.closure S) :
    Subgroup.closure (N.subtype ⁻¹' S) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have h : Subgroup.closure S ≤
      Subgroup.map N.subtype (Subgroup.closure (N.subtype ⁻¹' S)) := by
    rw [Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, hSN hg⟩, Subgroup.subset_closure (by simpa using hg), rfl⟩
  obtain ⟨v, hv, hveq⟩ := h (hN w.2)
  exact Subtype.ext hveq ▸ hv

/-- **An abelian group of exponent 2 on five generators has at most `2⁵` elements.**  The
`Z₂`-side counterpart of `card_le_eight_of_three_gens`, stated abstractly for the same
reason (the commutative normalisation never meets the quotient's instance stack). -/
private theorem card_le_thirtytwo_of_five_gens {H : Type*} [Group H] [Finite H]
    (hc : ∀ u v : H, u * v = v * u) (hsq : ∀ u : H, u ^ 2 = 1) {a b c d e : H} {S : Set H}
    (hS : S ⊆ ({a, b, c, d, e} : Set H)) (hgen : Subgroup.closure S = ⊤) :
    Nat.card H ≤ 32 := by
  letI : CommGroup H := { ‹Group H› with mul_comm := hc }
  have hword : ∀ q : H, ∃ i j k l m : ℕ, q = a ^ i * b ^ j * c ^ k * d ^ l * e ^ m := by
    intro q
    have hq : q ∈ Subgroup.closure S := by rw [hgen]; trivial
    induction hq using Subgroup.closure_induction with
    | mem z hz =>
      have hz := hS hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, 0, 0, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, 0, 0, by simp⟩
      · exact ⟨0, 0, 1, 0, 0, by simp⟩
      · exact ⟨0, 0, 0, 1, 0, by simp⟩
      · exact ⟨0, 0, 0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, 0, 0, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, k, l, m, rfl⟩ := hu
      obtain ⟨i', j', k', l', m', rfl⟩ := hv
      refine ⟨i + i', j + j', k + k', l + l', m + m', ?_⟩
      simp only [pow_add]
      simp only [mul_assoc, mul_left_comm]
    | inv u _ hu =>
      obtain ⟨i, j, k, l, m, rfl⟩ := hu
      exact ⟨i, j, k, l, m, by rw [inv_eq_iff_mul_eq_one, ← sq]; exact hsq _⟩
  have hsurj : Function.Surjective
      (fun t : Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2.1 : ℕ) * d ^ (t.2.2.2.1 : ℕ)
          * e ^ (t.2.2.2.2 : ℕ)) := by
    intro q
    obtain ⟨i, j, k, l, m, rfl⟩ := hword q
    refine ⟨(⟨i % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩,
      ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨l % 2, Nat.mod_lt _ (by norm_num)⟩,
      ⟨m % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only
    rw [← pow_eq_pow_mod_two hsq, ← pow_eq_pow_mod_two hsq, ← pow_eq_pow_mod_two hsq,
      ← pow_eq_pow_mod_two hsq, ← pow_eq_pow_mod_two hsq]
  calc Nat.card H ≤ Nat.card (Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = 32 := by simp

/-- `|Q₂| ≤ 8`: abelian of exponent 2 on three generators. -/
private theorem card_levelQuot_two_le : Nat.card (levelQuot (DR : Type) 2) ≤ 8 := by
  haveI : Finite (levelQuot (DR : Type) 2) := finite_levelQuot (DR : Type) drFg isProP_DR 2
  have h : Subgroup.closure ({levelMk (DR : Type) 2 drS, levelMk (DR : Type) 2 drX,
      levelMk (DR : Type) 2 drY} : Set (levelQuot (DR : Type) 2)) = ⊤ := by
    have h0 := closure_drGens_eq_top 2
    rwa [show levelMk (DR : Type) 2 '' {drS, drX, drY}
        = ({levelMk (DR : Type) 2 drS, levelMk (DR : Type) 2 drX,
            levelMk (DR : Type) 2 drY} : Set (levelQuot (DR : Type) 2)) from by
          rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]] at h0
  exact card_le_eight_of_three_gens levelQuot_two_mul_comm levelQuot_two_sq h

/-- `|Q₂| ≥ 8`: the elementary-abelian marking is onto. -/
private theorem card_levelQuot_two_ge : 8 ≤ Nat.card (levelQuot (DR : Type) 2) := by
  haveI : Finite (levelQuot (DR : Type) 2) := finite_levelQuot (DR : Type) drFg isProP_DR 2
  have hpsi : Function.Surjective psiR.toMonoidHom := by
    intro v
    have hv : v = vrS ^ (Multiplicative.toAdd v).1.val * vrX ^ (Multiplicative.toAdd v).2.1.val
        * vrY ^ (Multiplicative.toAdd v).2.2.val := by revert v; decide
    have hmS : vrS ∈ psiR.toMonoidHom.range := ⟨drS, psiR_drS⟩
    have hmX : vrX ∈ psiR.toMonoidHom.range := ⟨drX, psiR_drX⟩
    have hmY : vrY ∈ psiR.toMonoidHom.range := ⟨drY, psiR_drY⟩
    have hmem : v ∈ psiR.toMonoidHom.range := by
      rw [hv]
      exact mul_mem (mul_mem (pow_mem hmS _) (pow_mem hmX _)) (pow_mem hmY _)
    exact hmem
  have hlift : Function.Surjective
      (QuotientGroup.lift (twoCentralSeries (DR : Type) 2) psiR.toMonoidHom
        (fun g hg => twoCentralSeries_two_le_ker_psiR hg)) := by
    intro v
    obtain ⟨g, rfl⟩ := hpsi v
    exact ⟨levelMk (DR : Type) 2 g, rfl⟩
  calc (8 : ℕ) = Nat.card VR := card_VR.symm
    _ ≤ Nat.card (levelQuot (DR : Type) 2) := Nat.card_le_card_of_surjective _ hlift

/-- `|Q₂(D_R)| = 8` (spike §1, k = 1 row).  Fill: L3. -/
theorem card_levelQuot_two : Nat.card (levelQuot (DR : Type) 2) = 8 :=
  le_antisymm card_levelQuot_two_le card_levelQuot_two_ge

/-! `Q₃` sits in the extension `1 → Z₂ → Q₃ → Q₂ → 1`.  The layer `Z₂` is spanned by the
five classes `s², x², [s,x], [s,y], [x,y]`: `zLayer_two_le_of_gens` offers the three
generator squares and the three generator brackets, and the relator relation
`y² = [x,s]` (`levelMk_drY_sq`) deletes one of the six.  Hence `|Z₂| ≤ 2⁵`, and
`|Q₃| = |Q₂| · |Z₂| ≤ 8 · 32 = 256`. -/

/-- `|Z₂(D_R)| ≤ 2⁵` (spike §1: `dim Z₂ = 6 − 1 = 5`). -/
private theorem card_zLayer_two_le : Nat.card (zLayer (DR : Type) 2) ≤ 32 := by
  haveI : Finite (levelQuot (DR : Type) 3) := finite_levelQuot (DR : Type) drFg isProP_DR 3
  have h0 := closure_drGens_eq_top 3
  rw [show levelMk (DR : Type) 3 '' {drS, drX, drY}
      = ({levelMk (DR : Type) 3 drS, levelMk (DR : Type) 3 drX,
          levelMk (DR : Type) 3 drY} : Set (levelQuot (DR : Type) 3)) from by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]] at h0
  have hy2 := levelMk_drY_sq
  set s := levelMk (DR : Type) 3 drS with hsdef
  set x := levelMk (DR : Type) 3 drX with hxdef
  set y := levelMk (DR : Type) 3 drY with hydef
  set S : Set (levelQuot (DR : Type) 3) := {s ^ 2, x ^ 2, commP s x, commP s y, commP x y}
    with hSdef
  have hSZ : S ⊆ (zLayer (DR : Type) 2 : Set (levelQuot (DR : Type) 3)) := by
    intro w hw
    rw [hSdef] at hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    exacts [sq_mem_zLayer_two s, sq_mem_zLayer_two x, commP_mem_zLayer_two s x,
      commP_mem_zLayer_two s y, commP_mem_zLayer_two x y]
  have hy2K : y ^ 2 ∈ Subgroup.closure S := by
    rw [hy2, ← commP_inv]
    exact (Subgroup.closure S).inv_mem (Subgroup.subset_closure (by rw [hSdef]; simp))
  have hZK : zLayer (DR : Type) 2 ≤ Subgroup.closure S :=
    zLayer_two_le_of_gens (isOpen_dr 3) h0
      (Subgroup.subset_closure (by rw [hSdef]; simp))
      (Subgroup.subset_closure (by rw [hSdef]; simp)) hy2K
      (Subgroup.subset_closure (by rw [hSdef]; simp))
      (Subgroup.subset_closure (by rw [hSdef]; simp))
      (Subgroup.subset_closure (by rw [hSdef]; simp))
  -- inside the layer the five classes span an elementary abelian group
  have hcommZ : ∀ u v : zLayer (DR : Type) 2, u * v = v * u := fun u v =>
    Subtype.ext (Subgroup.mem_center_iff.mp (zLayer_le_center (DR : Type) 2 u.2) v.1).symm
  have hsqZ : ∀ u : zLayer (DR : Type) 2, u ^ 2 = 1 := fun u =>
    Subtype.ext (by simpa using zLayer_sq (DR : Type) u.2)
  have hSsub : (zLayer (DR : Type) 2).subtype ⁻¹' S ⊆
      ({⟨s ^ 2, sq_mem_zLayer_two s⟩, ⟨x ^ 2, sq_mem_zLayer_two x⟩,
        ⟨commP s x, commP_mem_zLayer_two s x⟩, ⟨commP s y, commP_mem_zLayer_two s y⟩,
        ⟨commP x y, commP_mem_zLayer_two x y⟩} : Set (zLayer (DR : Type) 2)) := by
    intro v hv
    simp only [Set.mem_preimage] at hv
    rw [hSdef] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
    rcases hv with h | h | h | h | h
    exacts [Or.inl (Subtype.ext h), Or.inr (Or.inl (Subtype.ext h)),
      Or.inr (Or.inr (Or.inl (Subtype.ext h))),
      Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h))))]
  exact card_le_thirtytwo_of_five_gens hcommZ hsqZ hSsub (closure_subtype_eq_top hSZ hZK)

/-- `|Q₃| ≤ 2⁸`: the extension `1 → Z₂ → Q₃ → Q₂ → 1` with `|Q₂| = 8` and `|Z₂| ≤ 32`. -/
private theorem card_levelQuot_three_le : Nat.card (levelQuot (DR : Type) 3) ≤ 256 := by
  haveI : Finite (levelQuot (DR : Type) 3) := finite_levelQuot (DR : Type) drFg isProP_DR 3
  have hindex : (zLayer (DR : Type) 2).index = 8 := by
    rw [zLayer_eq_ker_levelProj, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (levelProj (DR : Type) 2)
        (levelProj_surjective (DR : Type) 2)).toEquiv]
    exact card_levelQuot_two
  have h := Subgroup.card_mul_index (zLayer (DR : Type) 2)
  rw [hindex] at h
  rw [← h]
  calc Nat.card (zLayer (DR : Type) 2) * 8 ≤ 32 * 8 :=
        Nat.mul_le_mul_right 8 card_zLayer_two_le
    _ = 256 := by norm_num

end TowerSizes

section LevelThreeModel

/-! ## The order-256 model (spike §2.3, plan §2.3)

`Q₃` is realised on the nose by the central extension `M = 𝔽₂³ ×_f 𝔽₂⁵` with the **bilinear**
cocycle `f a b = (a₀b₀, a₁b₁, a₀b₁ + a₂b₂, a₀b₂, a₁b₂)`.  Bilinearity is the whole design:
the cocycle identity `f a b + f (a+b) c = f b c + f a (b+c)` is then a polynomial identity,
so associativity is `ring` on each coordinate rather than a `256³`-case `decide`.

The five `z`-coordinates are the five spanning classes of `Z₂`: `s²`, `x²`, `[s,x]`, `[s,y]`,
`[x,y]`.  The `a₀b₁ + a₂b₂` entry in the third slot is exactly the relator relation
`y² = [s,x]` (`levelMk_drY_sq`) built into the model, which is why `drWord` dies at the
standard basis. -/

/-- Carrier of the order-256 model: `𝔽₂³` (exponents of `s, x, y`) times `𝔽₂⁵` (the
`Z₂`-coordinates `s², x², [s,x], [s,y], [x,y]`). -/
private structure MR where
  /-- `s`-exponent. -/
  a0 : ZMod 2
  /-- `x`-exponent. -/
  a1 : ZMod 2
  /-- `y`-exponent. -/
  a2 : ZMod 2
  /-- `s²`-coordinate. -/
  z0 : ZMod 2
  /-- `x²`-coordinate. -/
  z1 : ZMod 2
  /-- `[s,x]`-coordinate — also carries `y²`. -/
  z2 : ZMod 2
  /-- `[s,y]`-coordinate. -/
  z3 : ZMod 2
  /-- `[x,y]`-coordinate. -/
  z4 : ZMod 2
deriving DecidableEq

/-- Coordinates of the model, as a plain `𝔽₂⁸`. -/
private def mrEquiv :
    MR ≃ ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 where
  toFun m := (m.a0, m.a1, m.a2, m.z0, m.z1, m.z2, m.z3, m.z4)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2⟩
  left_inv m := by cases m; rfl
  right_inv t := rfl

private instance : Fintype MR := Fintype.ofEquiv _ mrEquiv.symm

private instance : Mul MR :=
  ⟨fun m n => ⟨m.a0 + n.a0, m.a1 + n.a1, m.a2 + n.a2, m.z0 + n.z0 + m.a0 * n.a0,
    m.z1 + n.z1 + m.a1 * n.a1, m.z2 + n.z2 + (m.a0 * n.a1 + m.a2 * n.a2),
    m.z3 + n.z3 + m.a0 * n.a2, m.z4 + n.z4 + m.a1 * n.a2⟩⟩

private instance : One MR := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩⟩

private instance : Inv MR :=
  ⟨fun m => ⟨m.a0, m.a1, m.a2, m.z0 + m.a0 * m.a0, m.z1 + m.a1 * m.a1,
    m.z2 + (m.a0 * m.a1 + m.a2 * m.a2), m.z3 + m.a0 * m.a2, m.z4 + m.a1 * m.a2⟩⟩

@[simp] private theorem mrMul_def (m n : MR) : m * n =
    ⟨m.a0 + n.a0, m.a1 + n.a1, m.a2 + n.a2, m.z0 + n.z0 + m.a0 * n.a0,
      m.z1 + n.z1 + m.a1 * n.a1, m.z2 + n.z2 + (m.a0 * n.a1 + m.a2 * n.a2),
      m.z3 + n.z3 + m.a0 * n.a2, m.z4 + n.z4 + m.a1 * n.a2⟩ := rfl

@[simp] private theorem mrOne_def : (1 : MR) = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ := rfl

@[simp] private theorem mrInv_def (m : MR) : m⁻¹ =
    ⟨m.a0, m.a1, m.a2, m.z0 + m.a0 * m.a0, m.z1 + m.a1 * m.a1,
      m.z2 + (m.a0 * m.a1 + m.a2 * m.a2), m.z3 + m.a0 * m.a2, m.z4 + m.a1 * m.a2⟩ := rfl

private instance : Group MR where
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp only [mrMul_def, MR.mk.injEq]
    and_intros <;> ring
  one_mul a := by cases a; simp only [mrMul_def, mrOne_def, MR.mk.injEq]; and_intros <;> ring
  mul_one a := by cases a; simp only [mrMul_def, mrOne_def, MR.mk.injEq]; and_intros <;> ring
  inv_mul_cancel a := by
    obtain ⟨a0, a1, a2, z0, z1, z2, z3, z4⟩ := a
    revert a0 a1 a2 z0 z1 z2 z3 z4
    decide

private instance : TopologicalSpace MR := ⊥
private instance : DiscreteTopology MR := ⟨rfl⟩
private instance : IsTopologicalGroup MR where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology

private theorem card_MR : Nat.card MR = 256 := by
  rw [Nat.card_congr mrEquiv, Nat.card_eq_fintype_card]
  simp [ZMod.card]

private theorem isProP_two_MR : IsProP 2 MR :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 8) (by rw [card_MR]; norm_num))

/-- `t + t = 0` in `𝔽₂`. -/
private theorem mr_add_self (t : ZMod 2) : t + t = 0 := by revert t; decide

/-- `a + b + a + b = 0` in `𝔽₂` — the commutator's `𝔽₂³`-coordinate. -/
private theorem mr_add_four (a b : ZMod 2) : a + b + a + b = 0 := by revert a b; decide

/-- The marked generator `s` of the model. -/
private def mrS : MR := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
/-- The marked generator `x` of the model. -/
private def mrX : MR := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
/-- The marked generator `y` of the model. -/
private def mrY : MR := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩

/-- **The relator dies at the standard basis.**  The third cocycle slot `a₀b₁ + a₂b₂`
encodes `y² = [s,x]`, which is precisely what `drWord` asserts modulo `x⁴ = 1`. -/
private theorem drWord_MR : drWord mrS mrX mrY = 1 := by decide

/-- The `Z₂`-part of the model: the elements with vanishing `𝔽₂³`-coordinate. -/
private def mrCentral : Subgroup MR where
  carrier := {m | m.a0 = 0 ∧ m.a1 = 0 ∧ m.a2 = 0}
  mul_mem' := by
    rintro a b ⟨ha0, ha1, ha2⟩ ⟨hb0, hb1, hb2⟩
    exact ⟨by simp [ha0, hb0], by simp [ha1, hb1], by simp [ha2, hb2]⟩
  one_mem' := ⟨rfl, rfl, rfl⟩
  inv_mem' := by rintro a ⟨ha0, ha1, ha2⟩; exact ⟨ha0, ha1, ha2⟩

/-- `λ₂` of the model lands in the `Z₂`-part: squares and commutators kill the
`𝔽₂³`-coordinate, and every subset of a discrete space is closed. -/
private theorem twoCentralSeries_two_MR_le : twoCentralSeries MR 2 ≤ mrCentral := by
  show twoCentralSucc (⊤ : Subgroup MR) ≤ mrCentral
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_discrete _)
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, -, rfl⟩
    exact ⟨show (g ^ 2).a0 = 0 by rw [pow_two]; exact mr_add_self _,
      show (g ^ 2).a1 = 0 by rw [pow_two]; exact mr_add_self _,
      show (g ^ 2).a2 = 0 by rw [pow_two]; exact mr_add_self _⟩
  · rw [Subgroup.commutator_le]
    intro u _ v _
    rw [commutatorElement_def]
    exact ⟨mr_add_four _ _, mr_add_four _ _, mr_add_four _ _⟩

/-- The `Z₂`-part is central: the cocycle vanishes when either argument does. -/
private theorem mrCentral_le_center : mrCentral ≤ Subgroup.center MR := by
  rintro ⟨m0, m1, m2, u0, u1, u2, u3, u4⟩ ⟨h0, h1, h2⟩
  rw [Subgroup.mem_center_iff]
  rintro ⟨n0, n1, n2, w0, w1, w2, w3, w4⟩
  simp only at h0 h1 h2
  subst h0; subst h1; subst h2
  simp only [mrMul_def, MR.mk.injEq]
  and_intros <;> ring

/-- The `Z₂`-part has exponent 2. -/
private theorem mrCentral_sq {m : MR} (hm : m ∈ mrCentral) : m ^ 2 = 1 := by
  obtain ⟨m0, m1, m2, u0, u1, u2, u3, u4⟩ := m
  obtain ⟨h0, h1, h2⟩ := hm
  simp only at h0 h1 h2
  subst h0; subst h1; subst h2
  revert u0 u1 u2 u3 u4
  decide

/-- **`λ₃` of the model is trivial**: `λ₂ ≤ Z₂-part`, which is central of exponent 2. -/
private theorem twoCentralSeries_three_MR : twoCentralSeries MR 3 = ⊥ :=
  twoCentralSucc_eq_bot_of_le_center
    (le_trans twoCentralSeries_two_MR_le mrCentral_le_center)
    fun _ hx => mrCentral_sq (twoCentralSeries_two_MR_le hx)

/-- The `s²`-coordinate vector. -/
private def mrZ0 : MR := ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
/-- The `x²`-coordinate vector. -/
private def mrZ1 : MR := ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
/-- The `[s,x] = y²`-coordinate vector. -/
private def mrZ2 : MR := ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
/-- The `[s,y]`-coordinate vector. -/
private def mrZ3 : MR := ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
/-- The `[x,y]`-coordinate vector. -/
private def mrZ4 : MR := ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

private theorem mrZ0_eq : mrS * mrS = mrZ0 := by decide
private theorem mrZ1_eq : mrX * mrX = mrZ1 := by decide
private theorem mrZ2_eq : mrY * mrY = mrZ2 := by decide
private theorem mrZ3_eq : mrS * mrY * mrS⁻¹ * mrY⁻¹ = mrZ3 := by decide
private theorem mrZ4_eq : mrX * mrY * mrX⁻¹ * mrY⁻¹ = mrZ4 := by decide

/-- The five coordinate vectors span the `Z₂`-part. -/
private theorem mr_central_word (n : MR) (h0 : n.a0 = 0) (h1 : n.a1 = 0) (h2 : n.a2 = 0) :
    n = mrZ0 ^ n.z0.val * mrZ1 ^ n.z1.val * mrZ2 ^ n.z2.val * mrZ3 ^ n.z3.val
      * mrZ4 ^ n.z4.val := by
  obtain ⟨n0, n1, n2, v0, v1, v2, v3, v4⟩ := n
  simp only at h0 h1 h2
  subst h0; subst h1; subst h2
  revert v0 v1 v2 v3 v4
  decide

/-- The generator word `s^{t₀} x^{t₁} y^{t₂}` has `𝔽₂³`-coordinate `(t₀, t₁, t₂)`. -/
private theorem mr_word_a (t0 t1 t2 : ZMod 2) :
    (mrS ^ t0.val * mrX ^ t1.val * mrY ^ t2.val).a0 = t0 ∧
      (mrS ^ t0.val * mrX ^ t1.val * mrY ^ t2.val).a1 = t1 ∧
      (mrS ^ t0.val * mrX ^ t1.val * mrY ^ t2.val).a2 = t2 := by
  revert t0 t1 t2; decide

/-- The marking of `D_R` at the order-256 model. -/
private noncomputable def psiM : ContinuousMonoidHom (DR : Type) MR :=
  drLiftHom isProP_two_MR ![mrS, mrX, mrY] (by show drWord mrS mrX mrY = 1; exact drWord_MR)

@[simp] private theorem psiM_drS : psiM drS = mrS := drLiftHom_S _ _ _
@[simp] private theorem psiM_drX : psiM drX = mrX := drLiftHom_X _ _ _
@[simp] private theorem psiM_drY : psiM drY = mrY := drLiftHom_Y _ _ _

/-- **The marking is onto**: the three generators reach every `𝔽₂³`-coordinate, and their
squares and brackets are the five `Z₂`-coordinate vectors. -/
private theorem psiM_surjective : Function.Surjective psiM.toMonoidHom := by
  intro m
  refine MonoidHom.mem_range.mp ?_
  obtain ⟨e0, e1, e2⟩ := mr_word_a m.a0 m.a1 m.a2
  set w := mrS ^ m.a0.val * mrX ^ m.a1.val * mrY ^ m.a2.val with hwdef
  set R := psiM.toMonoidHom.range with hRdef
  have hS : mrS ∈ R := ⟨drS, psiM_drS⟩
  have hX : mrX ∈ R := ⟨drX, psiM_drX⟩
  have hY : mrY ∈ R := ⟨drY, psiM_drY⟩
  have hZ0 : mrZ0 ∈ R := mrZ0_eq ▸ R.mul_mem hS hS
  have hZ1 : mrZ1 ∈ R := mrZ1_eq ▸ R.mul_mem hX hX
  have hZ2 : mrZ2 ∈ R := mrZ2_eq ▸ R.mul_mem hY hY
  have hZ3 : mrZ3 ∈ R :=
    mrZ3_eq ▸ R.mul_mem (R.mul_mem (R.mul_mem hS hY) (R.inv_mem hS)) (R.inv_mem hY)
  have hZ4 : mrZ4 ∈ R :=
    mrZ4_eq ▸ R.mul_mem (R.mul_mem (R.mul_mem hX hY) (R.inv_mem hX)) (R.inv_mem hY)
  have hw : w ∈ R := R.mul_mem (R.mul_mem (R.pow_mem hS _) (R.pow_mem hX _)) (R.pow_mem hY _)
  have hn0 : (w⁻¹ * m).a0 = 0 := by show w.a0 + m.a0 = 0; rw [e0]; exact mr_add_self _
  have hn1 : (w⁻¹ * m).a1 = 0 := by show w.a1 + m.a1 = 0; rw [e1]; exact mr_add_self _
  have hn2 : (w⁻¹ * m).a2 = 0 := by show w.a2 + m.a2 = 0; rw [e2]; exact mr_add_self _
  have hrem : w⁻¹ * m ∈ R := by
    rw [mr_central_word _ hn0 hn1 hn2]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem hZ0 _) (R.pow_mem hZ1 _))
      (R.pow_mem hZ2 _)) (R.pow_mem hZ3 _)) (R.pow_mem hZ4 _)
  have hm : m = w * (w⁻¹ * m) := by group
  rw [hm]
  exact R.mul_mem hw hrem

/-- `|Q₃| ≥ 2⁸`: the marking kills `λ₃` (the model's own `λ₃` is trivial) and is onto. -/
private theorem card_levelQuot_three_ge : 256 ≤ Nat.card (levelQuot (DR : Type) 3) := by
  haveI : Finite (levelQuot (DR : Type) 3) := finite_levelQuot (DR : Type) drFg isProP_DR 3
  have hker : twoCentralSeries (DR : Type) 3 ≤ psiM.toMonoidHom.ker := by
    intro g hg
    have h : psiM.toMonoidHom g ∈ twoCentralSeries MR 3 :=
      map_twoCentralSeries_le psiM.toMonoidHom psiM.continuous_toFun 3 ⟨g, hg, rfl⟩
    rw [twoCentralSeries_three_MR, Subgroup.mem_bot] at h
    exact MonoidHom.mem_ker.mpr h
  have hlift : Function.Surjective
      (QuotientGroup.lift (twoCentralSeries (DR : Type) 3) psiM.toMonoidHom
        (fun g hg => hker hg)) := by
    intro v
    obtain ⟨g, rfl⟩ := psiM_surjective v
    exact ⟨levelMk (DR : Type) 3 g, rfl⟩
  calc (256 : ℕ) = Nat.card MR := card_MR.symm
    _ ≤ Nat.card (levelQuot (DR : Type) 3) := Nat.card_le_card_of_surjective _ hlift

end LevelThreeModel

/-- `|Q₃(D_R)| = 256` — the base-case budget (spike §1, `k₀ = 3` lives here).  Fill: L3. -/
theorem card_levelQuot_three : Nat.card (levelQuot (DR : Type) 3) = 256 :=
  le_antisymm card_levelQuot_three_le card_levelQuot_three_ge

/-- `|Z₁(D_R)| = 2³` (spike §1: `dim Z₁ = 3`).  Fill: L3.

`Z₁ = λ₁λ₂/λ₂` is the image of `λ₁ = ⊤`, i.e. all of `Q₂`, so this is `card_levelQuot_two`
read through `Subgroup.topEquiv`. -/
theorem card_zLayer_one : Nat.card (zLayer (DR : Type) 1) = 8 := by
  have h : zLayer (DR : Type) 1 = (⊤ : Subgroup (levelQuot (DR : Type) 2)) := by
    show (twoCentralSeries (DR : Type) 1).map (levelMk (DR : Type) 2) = ⊤
    rw [twoCentralSeries_one]
    exact Subgroup.map_top_of_surjective _ (levelMk_surjective (DR : Type) 2)
  rw [h, Nat.card_congr (Subgroup.topEquiv (G := levelQuot (DR : Type) 2)).toEquiv]
  exact card_levelQuot_two

/-- Smoke: the level-1 set is inhabited by the trivial triple (`Q₁ = 1`; every clause
degenerates — validates that the three-clause definition elaborates and composes). -/
theorem sPR0_one_nonempty : (sPR0 1).Nonempty := by
  haveI hsub : Subsingleton (levelQuot (DR : Type) 1) :=
    QuotientGroup.subsingleton_quotient_top
  haveI : Subsingleton (ZMod (2 ^ 1))ˣ := ⟨by decide⟩
  refine ⟨fun _ => 1, ⟨?_, ?_⟩, fun i => Subsingleton.elim _ _⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end GQ2.Roe.Labute
