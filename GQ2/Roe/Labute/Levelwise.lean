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

/-- `χ₀(A) = −1`.  Fill: L3 (replicate the private `d0LiftHom_A` evaluation pattern of
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
  sorry

/-- The defect of a relator-killing triple lies in the graded layer `Zₖ`
(minimal hypothesis: only the relator clause of `S⁰ₖ` is consumed).  Fill: L4a. -/
theorem defectR0_mem_zLayer (k : ℕ) {T : Fin 3 → levelQuot (DR : Type) k}
    (hrel : d0Word (T 0) (T 1) (T 2) = 1) :
    defectR0 k T ∈ zLayer (DR : Type) k := by
  sorry

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
  sorry

/-- The direction-2 defect of a relator-killing triple lies in `Zₖ`.  Fill: L4a. -/
theorem defectR2_mem_zLayer (k : ℕ) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hrel : drWord (T 0) (T 1) (T 2) = 1) :
    defectR2 k T ∈ zLayer (D0 : Type) k := by
  sorry

/-! ## Restriction maps (plan §2.1 item 2: all three clauses weaken) -/

/-- **Restriction `S^P_{k+1} → S^P_ₖ`, direction 1**: projecting a level-`(k+1)` triple
along the tower lands in the level-`k` set (relator: hom-push; generation: surjectivity
of `levelProj`; χ-clause: `chiLevel_levelProj` + `chiTargetR0_castHom`).  Fill: L4a. -/
theorem sPR0_levelProj {k : ℕ} {T : Fin 3 → levelQuot (DR : Type) (k + 1)}
    (hT : T ∈ sPR0 (k + 1)) :
    (fun i => levelProj (DR : Type) k (T i)) ∈ sPR0 k := by
  sorry

/-- Restriction `S^P_{k+1} → S^P_ₖ`, direction 2.  Fill: L4a. -/
theorem sPR2_levelProj {k : ℕ} {T : Fin 3 → levelQuot (D0 : Type) (k + 1)}
    (hT : T ∈ sPR2 (k + 1)) :
    (fun i => levelProj (D0 : Type) k (T i)) ∈ sPR2 k := by
  sorry

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
  have hrel : drWord s x y = 1 := by
    rw [hs, hx, hy, ← map_drWord (levelMk (DR : Type) 3), dr_relation, map_one]
  have hzys : commP y s ∈ zLayer (DR : Type) 2 := levelMk_commP_mem_zLayer drY drS
  have hzsx : commP s x ∈ zLayer (DR : Type) 2 := levelMk_commP_mem_zLayer drS drX
  have hx4 : x ^ 4 = 1 := levelMk_pow_four drX
  have hsx4 : (s * x) ^ 4 = 1 := by rw [← hsx]; exact levelMk_pow_four _
  -- the `[y, yˢ]` block is inert
  have hyys : commP y (conjP y s) = 1 := by
    rw [conjP_eq_mul_commP, commP_mul_right, commP_self, conjP_one_left, mul_one]
    exact commP_of_mem_zLayer_right y hzys
  -- the source relator pins `y²` against the surviving cross term
  have hy2 : y ^ 2 = commP x s := by
    set c := commP x s with hc
    have h : (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s) = 1 := hrel
    rw [hyys, mul_one, conjP_eq_mul_commP, ← hc] at h
    have hstep : (x * c)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 = c⁻¹ * ((x ^ 4)⁻¹ * y ^ 2) := by group
    rw [hstep, hx4, inv_one, one_mul] at h
    exact (inv_mul_eq_one.mp h).symm
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

/-- `|Q₂(D_R)| = 8` (spike §1, k = 1 row).  Fill: L3. -/
theorem card_levelQuot_two : Nat.card (levelQuot (DR : Type) 2) = 8 := by
  sorry

/-- `|Q₃(D_R)| = 256` — the base-case budget (spike §1, `k₀ = 3` lives here).  Fill: L3. -/
theorem card_levelQuot_three : Nat.card (levelQuot (DR : Type) 3) = 256 := by
  sorry

/-- `|Z₁(D_R)| = 2³` (spike §1: `dim Z₁ = 3`).  Fill: L3. -/
theorem card_zLayer_one : Nat.card (zLayer (DR : Type) 1) = 8 := by
  sorry

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
