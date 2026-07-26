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
  sorry

/-- `χ₀(S) = 1`.  Fill: L3. -/
theorem chiD0pres_d0S : chiD0pres d0S = 1 := by
  sorry

/-- `χ₀(Y) = η`.  Fill: L3. -/
theorem chiD0pres_d0Y : chiD0pres d0Y = etaUnit := by
  sorry

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

/-- Direction-1 targets mod `8`: `(−1, 1, η) ≡ (7, 1, 5)`.  Fill: L3. -/
theorem chiTargetR0_three (i : Fin 3) :
    (chiTargetR0 3 i : ZMod (2 ^ 3)) = ![7, 1, 5] i := by
  sorry

/-- Direction-2 targets mod `8`: `(S, X, Y) ≡ (5, 5, 7)`.  Fill: L3. -/
theorem chiTargetR2_three (i : Fin 3) :
    (chiTargetR2 3 i : ZMod (2 ^ 3)) = ![5, 5, 7] i := by
  sorry

/-- Direction-1 targets mod `2^9` (stress): `(−1, 1, η) ≡ (511, 1, 341)`.  Fill: L3. -/
theorem chiTargetR0_nine (i : Fin 3) :
    (chiTargetR0 9 i : ZMod (2 ^ 9)) = ![511, 1, 341] i := by
  sorry

/-- Direction-2 targets mod `2^9` (stress): `(S, X, Y) ≡ (253, 437, 7)` — the spike's
level-9 numerics, re-verified by hand during L1.  Fill: L3. -/
theorem chiTargetR2_nine (i : Fin 3) :
    (chiTargetR2 9 i : ZMod (2 ^ 9)) = ![253, 437, 7] i := by
  sorry

/-- Naturality of the direction-1 targets in `k` (consumed by the restriction maps).
Fill: L3 (from `PadicInt.zmod_cast_comp_toZModPow`-style compatibility). -/
theorem chiTargetR0_castHom (k : ℕ) (i : Fin 3) :
    Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k))).toMonoidHom
      (chiTargetR0 (k + 1) i) = chiTargetR0 k i := by
  sorry

/-- Naturality of the direction-2 targets in `k`.  Fill: L3. -/
theorem chiTargetR2_castHom (k : ℕ) (i : Fin 3) :
    Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k))).toMonoidHom
      (chiTargetR2 (k + 1) i) = chiTargetR2 k i := by
  sorry

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

/-- **Base case, direction 1** (spike §2.4: `S^P₃ ≠ ∅` by explicit witness).  Fill: L3
(`decide`/structured verification in a 256-element model of `Q₃`). -/
theorem witnessR0_mem : witnessR0 ∈ sPR0 3 := by
  sorry

/-- `S^P₃ ≠ ∅`, direction 1 (packaging; not a fill target). -/
theorem sPR0_three_nonempty : (sPR0 3).Nonempty := ⟨witnessR0, witnessR0_mem⟩

/-- The direction-2 base witness in `Q₃(D₀)` (spike §3.1/§3.4): the `(s,x,y)`-slot triple
`(S·Y, Y, A)` — mod-8 χ₀-values `(5, 5, 7)`, matching `chiTargetR2_three`. -/
noncomputable def witnessR2 : Fin 3 → levelQuot (D0 : Type) 3 :=
  ![levelMk (D0 : Type) 3 (d0S * d0Y), levelMk (D0 : Type) 3 d0Y, levelMk (D0 : Type) 3 d0A]

/-- **Base case, direction 2**.  Fill: L3. -/
theorem witnessR2_mem : witnessR2 ∈ sPR2 3 := by
  sorry

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
