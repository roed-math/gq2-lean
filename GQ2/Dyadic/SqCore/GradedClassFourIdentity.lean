/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedGammaThreeFour

/-!
# W70-CFOUR: the class-four identity, and where it actually lives

Wave 69 reduced `SqClassClearingSupply h 4` to the single `Q₄`-identity
`cfourEichDefect nu' j = 1` (`cfour_supply_of_eichDefect`), with the **trivial** dressing, and
flagged that this is sufficient and not necessary.  This file settles the status of that route
and replaces it with one whose obligation is a full graded layer smaller.

## §1 The trivial-dressing route is vacuous

⭐⭐ `cfourId_eichDefect_levelProj`: the class-four Eichler defect projects to wave 68's
class-three defect,

```text
  levelProj (D_sq h) 3 (cfourEichDefect nu' j) = bridgeDefect nu' j .
```

So `cfourEichDefect nu' j = 1` **forces** `bridgeDefect nu' j = 1`
(`cfourId_bridgeDefect_of_eichDefect`), and then the undressed frame already solves the
class-three clearing problem (`cfourId_base_relator_three_of_eichDefect`): wave 68's dressing
would have been unnecessary at every marking and handle.  Since wave 68's whole argument is the
construction of that dressing to cancel exactly this defect, the hypothesis of
`cfour_supply_of_eichDefect` is not a plausible thing to prove; it is what one gets by asking
the trivial dressing to do a job wave 68 already had to hire a dressing for.  Nothing here is a
refutation of class four, and nothing here refutes the residual: it locates the route.

## §2 The route that is one graded layer better

Dress with wave 68's tuple and correct **inside `γ₂`**.  Writing

```text
  LEFTOVER = levelMk (D_sq h) 4 (sqRelWord (sqArbFrame h nu' j (bridgeTuple nu' j)))
```

wave 68's `bridge_relator_mem` says the leftover already lies in `γ₃`, so
⭐ `cfourId_leftover_mem_zLayer`: **the leftover lies in the central layer `Z = γ₃/γ₄`**, an
elementary abelian 2-group, and it is its own inverse.  A `γ₂`-valued correction of the frame
costs nothing on either row and nothing on mod-2 independence
(`cfourId_modTwoIndep_mul`, through `cfourId_twoCentral_le_index_two`), so

⭐⭐⭐ `cfourId_supply_of_reach`: **`SqClassClearingSupply h 4` follows as soon as some
`γ₂`-valued, exactly row-trivial correction of wave 68's frame kills the relator in `Q₄`.**

Against wave 69 this trades an identity in `Y = γ₂/γ₄` for a membership in `Z = γ₃/γ₄`: one
graded layer down, and a subgroup to hit rather than a point.

## §3 The knob inventory, completed

Wave 69 computed what a `γ₂`-valued correction buys on the three core slots.  This section adds
the two families it did not have, the **handle slots**, which is where the brackets against the
handle letters come from:

| slot | knob | name |
| --- | --- | --- |
| `σ` | `commP c (m 1)` | `cfour_dress_zero` (wave 69) |
| `x₀` | `commP (m 0) c` | `cfour_dress_one` (wave 69) |
| `x₁` | `c² · commP c (m 2)` | `cfour_dress_two` (wave 69) |
| `u_{j'}` | `commP c (m (sqHandleIdxV j'))` | `cfourId_dress_handleU` |
| `v_{j'}` | `commP (m (sqHandleIdxU j')) c` | `cfourId_dress_handleV` |

So a `γ₂`-valued correction reaches `commP c g` for `c ∈ γ₂` and `g` **every** frame letter,
with the `x₁`-letter alone arriving bundled with the square `c²`, and `c²` itself available only
through that bundle.  `cfourId_dress_core` composes the three core knobs into one.

## §4 The `x₁`-bundle: wave 69's analysis verified, its justification corrected

Wave 69's §5 recorded, as analysis and not as proof, that the delicate direction is
`⁅⁅x₁, g⁆, x₁⁆`, that Jacobi does not reach it, and that it is instead reached "by a correction
whose square part involves `x₁`", admissible because "the `x₁`-coordinate functional is never in
the span of `λ` and `ν'` modulo 2".

The mechanism is confirmed and is now a theorem, but the justification is simpler and stronger
than the span argument.  ⭐ `cfourId_x1_sq_knob`: the correction `c = x₁²` is a `γ₂`-element
whose knob against a slot `q` is exactly the iterated bracket, modulo one square,

```text
  commP (x₁²) q = (commP x₁ q)² · commP (commP x₁ q) x₁ ,
```

by `gThreeFour_commP_sq_left`, so it lands in the direction Jacobi cannot produce.  And it is
admissible not by any span argument but on the nose: ⭐ `cfourId_x1_sq_rows` gives
`λ(x₁²) = 4` and `ν'(x₁²) = 0` at every selected marking, both in `4ℤ₂`, because `λ(x₁) = 2`
(`nuLam_x1`) and `ν'(x₁) = 2ν'(x₀) = 0` (`toAdd_nu_dsqX1` at a selected marking).  Rows in
`4ℤ₂` are repairable **inside `γ₃`** by wave 68's `bridge_row_image` at `m = 2`
(`cfourId_row_repair`), and a `γ₃`-repair does not move the knob at all, since
`⁅γ₃, G⁆ ≤ γ₄`.  That is the whole of it, and the `x₁`-coordinate functional never enters.

Lane W70-CFOUR.  New file; no edits to existing files.  Prefix `cfourId`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The trivial-dressing route -/

section BaseThree

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The undressed frame's class-three relator is wave 68's defect.**  This is the class-three
face of `cfour_relator_base`, and it is the reason wave 68 needed a dressing at all. -/
theorem cfourId_base_relator_three :
    sqRelWord (fun i => levelMk (DSq h : Type) 3 (sqArbBase h nu' j i)) = bridgeDefect nu' j := by
  have hgen : sqRelWord (fun i => levelMk (DSq h : Type) 3 (sqGen h i)) = 1 := by
    rw [← map_sqRelWord, dsq_relation, map_one]
  have h0 : sqArbBase h nu' j 0 = sqGen h 0 := cfour_base_eq_gen nu' j
    (by rw [sqVal_zero, sqHandleIdxU_val]; omega) (by rw [sqVal_zero, sqHandleIdxV_val]; omega)
  have h1 : sqArbBase h nu' j 1 = sqGen h 1 := cfour_base_eq_gen nu' j
    (by rw [sqVal_one, sqHandleIdxU_val]; omega) (by rw [sqVal_one, sqHandleIdxV_val]; omega)
  have h2 : sqArbBase h nu' j 2 = sqGen h 2 := cfour_base_eq_gen nu' j
    (by rw [sqVal_two, sqHandleIdxU_val]; omega) (by rw [sqVal_two, sqHandleIdxV_val]; omega)
  have hhandle : handleWord
      (fun i => levelMk (DSq h : Type) 3 (sqArbBase h nu' j (sqHandleIdxU i)))
      (fun i => levelMk (DSq h : Type) 3 (sqArbBase h nu' j (sqHandleIdxV i)))
      = handleWord (fun i => levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxU i)))
          (fun i => levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxV i))) *
        bridgeDefect nu' j := by
    refine bridge_handleWord_update _ _ _ _ j _ (bridge_defect_central nu' j) ?_ ?_
    · intro i hi
      simp only [sqArbBase_handleU_ne hi, sqArbBase_handleV_ne hi]
    · simp only [sqArbBase_handleU, sqArbBase_handleV]
      exact bridge_handle_comm nu' j
  rw [bridge_sqRelWord] at hgen
  rw [bridge_sqRelWord, h0, h1, h2, hhandle, ← mul_assoc, hgen, one_mul]

/-- ⭐⭐ **The class-four Eichler defect projects to the class-three defect.**  Both are the
amount by which the two cleared handle letters miss the plain handle bracket, read one level
apart, so the tower projection carries one to the other. -/
theorem cfourId_eichDefect_levelProj :
    levelProj (DSq h : Type) 3 (cfourEichDefect nu' j) = bridgeDefect nu' j := by
  have hp : ∀ a b : (DSq h : Type),
      levelProj (DSq h : Type) 3
          (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b))
        = commP (levelMk (DSq h : Type) 3 a) (levelMk (DSq h : Type) 3 b) := by
    intro a b
    simp only [commP, map_mul, map_inv, levelProj_levelMk]
  rw [cfourEichDefect, map_mul, map_inv, hp, hp, bridge_handle_comm, inv_mul_cancel_left]

/-- ⭐ **The trivial-dressing hypothesis forces wave 68's defect to vanish.**  So
`cfour_supply_of_eichDefect` can only fire where wave 68's dressing was unnecessary. -/
theorem cfourId_bridgeDefect_of_eichDefect (H : cfourEichDefect nu' j = 1) :
    bridgeDefect nu' j = 1 := by
  rw [← cfourId_eichDefect_levelProj nu' j, H, map_one]

/-- ⭐ **The trivial-dressing hypothesis makes the undressed frame solve class three.**  This is
the statement that measures how strong `cfour_supply_of_eichDefect`'s hypothesis is: it implies
the whole of wave 68's construction was avoidable. -/
theorem cfourId_base_relator_three_of_eichDefect (H : cfourEichDefect nu' j = 1) :
    sqRelWord (sqArbBase h nu' j) ∈ twoCentralSeries (DSq h : Type) 3 := by
  rw [lim_mem_twoCentralSeries_iff_levelMk, map_sqRelWord, cfourId_base_relator_three nu' j,
    cfourId_bridgeDefect_of_eichDefect nu' j H]

end BaseThree

/-! ## §2 A `γ₂`-valued correction is free on the rows and on mod-2 independence -/

section GammaTwoFree

variable {h : ℕ}

/-- `γ₂` sits inside every index-two open normal subgroup: such a subgroup is closed, contains
every square, and contains every commutator. -/
theorem cfourId_twoCentral_le_index_two {M : OpenNormalSubgroup (DSq h : Type)}
    (hM : M.toSubgroup.index = 2) :
    twoCentralSeries (DSq h : Type) 2 ≤ M.toSubgroup := by
  rw [cfour_lambda_two, twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
    (Subgroup.isClosed_of_isOpen _ M.isOpen')
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, -, rfl⟩
    show g ^ 2 ∈ M.toSubgroup
    rw [pow_two]
    exact (mul_mem_iff_of_index_two hM g g).mpr Iff.rfl
  · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [commutatorElement_def]
    show a * b * a⁻¹ * b⁻¹ ∈ M.toSubgroup
    have heq : a * b * a⁻¹ * b⁻¹ = a * b * (a⁻¹ * b⁻¹) := by group
    rw [heq, mul_mem_iff_of_index_two hM, mul_mem_iff_of_index_two hM,
      mul_mem_iff_of_index_two hM, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]

/-- **Mod-2 independence survives a `γ₂`-valued correction**: membership in an index-two open
normal subgroup does not see a `γ₂`-factor. -/
theorem cfourId_modTwoIndep_mul {m d : Fin (sqRank h) → (DSq h : Type)}
    (hm : SqModTwoIndep m) (hd : ∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) :
    SqModTwoIndep fun i => m i * d i := by
  intro M hM
  obtain ⟨i, hi⟩ := hm M hM
  refine ⟨i, fun hc => hi ?_⟩
  have hdi : d i ∈ M.toSubgroup := cfourId_twoCentral_le_index_two hM (hd i)
  have hprod := M.toSubgroup.mul_mem hc (M.toSubgroup.inv_mem hdi)
  rwa [mul_inv_cancel_right] at hprod

end GammaTwoFree

/-! ## §3 The leftover, and the reduction -/

section Leftover

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The class-four leftover of wave 68's frame**: the relator of the class-three witness, read
in `Q₄`.  Wave 68 proved it dies to class three; class four asks it to die outright. -/
noncomputable def cfourIdLeftover : levelQuot (DSq h : Type) 4 :=
  levelMk (DSq h : Type) 4 (sqRelWord (sqArbFrame h nu' j (bridgeTuple nu' j)))

/-- ⭐ **The leftover lives in the central layer `Z = γ₃/γ₄`.**  This is the whole gain over
wave 69: the class-four obligation is an element of an elementary abelian 2-group, not of
`Y`. -/
theorem cfourId_leftover_mem_zLayer : cfourIdLeftover nu' j ∈ zLayer (DSq h : Type) 3 :=
  ⟨_, bridge_relator_mem nu' j, rfl⟩

/-- The leftover is its own inverse. -/
theorem cfourId_leftover_inv_self : (cfourIdLeftover nu' j)⁻¹ = cfourIdLeftover nu' j :=
  zLayer_inv_self (cfourId_leftover_mem_zLayer nu' j)

/-- The leftover is the relator value of wave 68's frame, read in `Q₄`. -/
theorem cfourId_leftover_eq :
    sqRelWord (fun i => levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) i))
      = cfourIdLeftover nu' j := by
  rw [cfourIdLeftover, map_sqRelWord]

end Leftover

section Reduction

variable {h : ℕ}

/-- ⭐⭐⭐ **The class-four supply from a `γ₂`-valued correction of wave 68's frame.**  Rows
multiply, so an exactly row-trivial correction keeps the frame exactly row-trivial; mod-2
independence is blind to a `γ₂`-factor; and the relator clause is read in `Q₄` by
`cfour_supply_iff`.  So the entire class-four obligation is: **some `γ₂`-valued, exactly
row-trivial correction of wave 68's class-three witness kills the relator one class up.**  By
`cfourId_leftover_mem_zLayer` the amount to be killed is a single element of `γ₃/γ₄`. -/
theorem cfourId_supply_of_reach
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ d : Fin (sqRank h) → (DSq h : Type),
          (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) ∧
            (∀ i, nuLam h (d i) = 1) ∧ (∀ i, nu' (d i) = 1) ∧
              sqRelWord (fun i => levelMk (DSq h : Type) 4
                  (sqArbFrame h nu' j (bridgeTuple nu' j) i * d i)) = 1) :
    SqClassClearingSupply h 4 := by
  rw [cfour_supply_iff]
  intro nu' j hs hx
  obtain ⟨d, hd2, hdl, hdn, hrel⟩ := H nu' j hs hx
  have hfr : sqArbFrame h nu' j (fun i => bridgeTuple nu' j i * d i)
      = fun i => sqArbFrame h nu' j (bridgeTuple nu' j) i * d i := by
    funext i
    simp only [sqArbFrame, mul_assoc]
  refine ⟨fun i => bridgeTuple nu' j i * d i, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [map_mul, bridge_tuple_nuLam nu' j i, hdl i, one_mul]
  · intro i
    rw [map_mul, bridge_tuple_nu nu' j hs hx i, hdn i, one_mul]
  · rw [hfr]
    exact cfourId_modTwoIndep_mul (bridge_modTwoIndep nu' j) hd2
  · rw [hfr]
    exact hrel

end Reduction

/-! ## §4 The knob inventory, completed: the handle slots -/

section HandleKnobs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A `Y`-valued correction of the near slot of a bracket adds one bracket. -/
theorem cfourId_comm_dress_left (p q : levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) : commP (p * c) q = commP p q * commP c q := by
  rw [cfour_commP_mul_left, cfour_commP_lambdaTwo (cfour_commP_mem_lambdaTwo p q) hc, mul_one]

/-- A `Y`-valued correction of the far slot of a bracket adds one bracket. -/
theorem cfourId_comm_dress_right (p q : levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) : commP p (q * c) = commP p q * commP p c := by
  rw [cfour_commP_mul_right, cfour_commP_lambdaTwo (cfour_commP_mem_lambdaTwo p q) hc, mul_one,
    cfour_zLayer_comm (cfour_commP_mem_zLayer_right p hc)]

/-- A `Z`-valued correction of the near slot of a bracket is invisible. -/
theorem cfourId_comm_zLayer_dress {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (p q : levelQuot G 4) : commP (p * z) q = commP p q := by
  rw [cfour_commP_mul_left, cfour_commP_zLayer_right hz (commP p q),
    cfour_commP_zLayer_left hz q, mul_one, mul_one]

/-- A `Z`-valued correction is invisible to a square. -/
theorem cfourId_sq_zLayer_dress {z : levelQuot G 4} (hz : z ∈ zLayer G 3) (p : levelQuot G 4) :
    (p * z) ^ 2 = p ^ 2 := by
  rw [cfour_sq_mul, cfour_commP_zLayer_left hz p, cfour_one_comm, zLayer_sq G hz, mul_one,
    mul_one, mul_one]

/-- **A relator whose only change is one handle bracket, changed by a central factor.**  The
core slots are untouched, so `cfour_sqRelWord`'s first four factors agree and the whole move is
the handle surgery of `cfour_handleWord_update`. -/
theorem cfourId_dress_handle {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) (j' : Fin n)
    {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hne : ∀ i, i ≠ j' → commP (m' (sqHandleIdxU i)) (m' (sqHandleIdxV i))
        = commP (m (sqHandleIdxU i)) (m (sqHandleIdxV i)))
    (hj : commP (m' (sqHandleIdxU j')) (m' (sqHandleIdxV j'))
        = commP (m (sqHandleIdxU j')) (m (sqHandleIdxV j')) * z) :
    sqRelWord m' = sqRelWord m * z := by
  have hhandle := cfour_handleWord_update (fun i => m' (sqHandleIdxU i))
    (fun i => m' (sqHandleIdxV i)) (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i))
    j' z (fun i => cfour_commute_lambdaTwo (cfour_commP_mem_lambdaTwo _ _)
      (cfour_zLayer_le_lambdaTwo hz)) hne hj
  rw [cfour_sqRelWord, cfour_sqRelWord, h0, h1, h2, hhandle, ← mul_assoc]

/-- ⭐ **The `u_{j'}`-slot knob**: a `γ₂`-valued correction of a handle's first letter moves the
class-four relator by the single bracket `commP c (m (sqHandleIdxV j'))`.  This family is not in
wave 69's inventory, and it is the only source of brackets against the handle letters. -/
theorem cfourId_dress_handleU {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) (j' : Fin n)
    {c : levelQuot G 4} (hc : c ∈ lambdaImage G 2 4)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hUj : m' (sqHandleIdxU j') = m (sqHandleIdxU j') * c)
    (hUne : ∀ i, i ≠ j' → m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP c (m (sqHandleIdxV j')) := by
  refine cfourId_dress_handle m m' j' (cfour_commP_mem_zLayer_left hc _) h0 h1 h2 ?_ ?_
  · intro i hi
    rw [hUne i hi, hV i]
  · rw [hUj, hV j', cfourId_comm_dress_left _ _ hc]

/-- ⭐ **The `v_{j'}`-slot knob**: `commP (m (sqHandleIdxU j')) c`. -/
theorem cfourId_dress_handleV {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) (j' : Fin n)
    {c : levelQuot G 4} (hc : c ∈ lambdaImage G 2 4)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hVj : m' (sqHandleIdxV j') = m (sqHandleIdxV j') * c)
    (hVne : ∀ i, i ≠ j' → m' (sqHandleIdxV i) = m (sqHandleIdxV i))
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i)) :
    sqRelWord m' = sqRelWord m * commP (m (sqHandleIdxU j')) c := by
  refine cfourId_dress_handle m m' j' (cfour_commP_mem_zLayer_right _ hc) h0 h1 h2 ?_ ?_
  · intro i hi
    rw [hU i, hVne i hi]
  · rw [hVj, hU j', cfourId_comm_dress_right _ _ hc]

end HandleKnobs

/-! ## §5 The `x₁`-bundle -/

section X1Bundle

variable {h : ℕ}

/-- The `x₁`-square is a `γ₂`-element, so it is a legal knob. -/
theorem cfourId_x1_sq_mem : dsqX1 h ^ 2 ∈ twoCentralSeries (DSq h : Type) 2 :=
  sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) (Subgroup.mem_top _)

/-- ⭐ **The direction the `x₁`-square knob reaches**: against a slot `q` its knob is the
iterated bracket `commP (commP x₁ q) x₁`, modulo one square.  This is the direction
`⁅⁅x₁, q⁆, x₁⁆` that Jacobi cannot produce from brackets with outer slot different from `x₁`
(`gThreeFour_jacobi` degenerates there in characteristic two), and it is exactly wave 69's
"correction whose square part involves `x₁`". -/
theorem cfourId_x1_sq_direction (q : levelQuot (DSq h : Type) 4) :
    commP (levelMk (DSq h : Type) 4 (dsqX1 h ^ 2)) q
      = (commP (levelMk (DSq h : Type) 4 (dsqX1 h)) q) ^ 2 *
        commP (commP (levelMk (DSq h : Type) 4 (dsqX1 h)) q)
          (levelMk (DSq h : Type) 4 (dsqX1 h)) := by
  rw [map_pow, gThreeFour_commP_sq_left]

/-- **The `λ`-row of the `x₁`-square is `4`**, by the core's own row `λ(x₁) = 2`. -/
theorem cfourId_x1_sq_nuLam : toAdd (nuLam h (dsqX1 h ^ 2)) = (4 : ℤ_[2]) := by
  rw [map_pow, pow_two, toAdd_mul, nuLam_x1, toAdd_ofAdd]
  norm_num

/-- **The `ν'`-row of the `x₁`-square is `0` at a selected marking**, by the core's own row
`ν'(x₁) = 2ν'(x₀)` (`toAdd_nu_dsqX1`), which holds for every `ν'`. -/
theorem cfourId_x1_sq_nu (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : toAdd (nu' (dsqX1 h ^ 2)) = (0 : ℤ_[2]) := by
  rw [map_pow, pow_two, toAdd_mul, toAdd_nu_dsqX1, hx0, toAdd_ofAdd]
  ring

/-- ⭐⭐ **Rows in `4ℤ₂` are repairable inside `γ₃`, at no cost to the knob.**  Wave 68's
`bridge_row_image` at `m = 2` supplies a `γ₃`-element with any prescribed rows in `4ℤ₂ × 4ℤ₂`,
and a `γ₃`-factor is invisible both to a bracket (`cfourId_comm_zLayer_dress`) and to a square
(`cfourId_sq_zLayer_dress`).  So a `γ₂`-correction whose two rows already lie in `4ℤ₂` may be
replaced by one with **exactly** trivial rows and exactly the same knob. -/
theorem cfourId_row_repair (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    {c : (DSq h : Type)} (hc : c ∈ twoCentralSeries (DSq h : Type) 2) {a b : ℤ_[2]}
    (hla : toAdd (nuLam h c) = 4 * a) (hnb : toAdd (nu' c) = 4 * b) :
    ∃ c' ∈ twoCentralSeries (DSq h : Type) 2, nuLam h c' = 1 ∧ nu' c' = 1 ∧
      (∀ q : levelQuot (DSq h : Type) 4,
          commP (levelMk (DSq h : Type) 4 c') q = commP (levelMk (DSq h : Type) 4 c) q) ∧
        levelMk (DSq h : Type) 4 c' ^ 2 = levelMk (DSq h : Type) 4 c ^ 2 := by
  obtain ⟨v, hv, hvl, hvn⟩ := bridge_row_image nu' hsigma hx0 2 (-a) (-b)
  have hfour : ((2 : ℤ_[2]) ^ 2) = 4 := by norm_num
  have hz : levelMk (DSq h : Type) 4 v ∈ zLayer (DSq h : Type) 3 := ⟨v, hv, rfl⟩
  refine ⟨c * v, (twoCentralSeries (DSq h : Type) 2).mul_mem hc
      (twoCentralSeries_antitone (G := (DSq h : Type)) (by norm_num) hv), ?_, ?_, ?_, ?_⟩
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, toAdd_mul, hla, hvl, hfour, toAdd_one]
    ring
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, toAdd_mul, hnb, hvn, hfour, toAdd_one]
    ring
  · intro q
    rw [map_mul]
    exact cfourId_comm_zLayer_dress hz _ q
  · rw [map_mul]
    exact cfourId_sq_zLayer_dress hz _

/-- ⭐⭐ **The `x₁`-square is an admissible knob at every selected marking.**  Wave 69 justified
this by a span argument on the `x₁`-coordinate functional; the real reason is simpler and does
not mention that functional at all.  Both rows of `x₁²` lie in `4ℤ₂` outright, `λ(x₁²) = 4` and
`ν'(x₁²) = 0`, so `cfourId_row_repair` produces a correction with exactly trivial rows and the
same knob, namely the direction of `cfourId_x1_sq_direction`. -/
theorem cfourId_x1_sq_admissible
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ c ∈ twoCentralSeries (DSq h : Type) 2, nuLam h c = 1 ∧ nu' c = 1 ∧
      (∀ q : levelQuot (DSq h : Type) 4,
          commP (levelMk (DSq h : Type) 4 c) q
            = (commP (levelMk (DSq h : Type) 4 (dsqX1 h)) q) ^ 2 *
              commP (commP (levelMk (DSq h : Type) 4 (dsqX1 h)) q)
                (levelMk (DSq h : Type) 4 (dsqX1 h))) := by
  obtain ⟨c', hc', hl, hn, hknob, -⟩ := cfourId_row_repair nu' hsigma hx0 cfourId_x1_sq_mem
    (a := 1) (b := 0) (by rw [cfourId_x1_sq_nuLam]; ring)
    (by rw [cfourId_x1_sq_nu nu' hx0]; ring)
  exact ⟨c', hc', hl, hn, fun q => by rw [hknob q, cfourId_x1_sq_direction q]⟩

end X1Bundle

/-! ## §6 The layer at `D_sq h`, with no closedness side condition -/

section LayerDsq

variable {h : ℕ}

/-- Every level of the tower of `D_sq h` is discrete: the group is topologically finitely
generated (`lim_dsq_finsetGen`) and pro-2 (`isProP_DSq`). -/
theorem cfourId_discreteTopology : DiscreteTopology (levelQuot (DSq h : Type) 4) :=
  discreteTopology_levelQuot (DSq h : Type) (lim_dsq_finsetGen h) (isProP_DSq h) 4

/-- Every subgroup of `Q₄` is closed, `Q₄` being discrete. -/
theorem cfourId_isClosed (S : Subgroup (levelQuot (DSq h : Type) 4)) :
    IsClosed ((S : Subgroup (levelQuot (DSq h : Type) 4)) : Set (levelQuot (DSq h : Type) 4)) := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) 4) := cfourId_discreteTopology
  exact isClosed_discrete _

/-- ⭐⭐ **Generation of the layer at `D_sq h`, with no side condition**: a subgroup of `Q₄`
holding every square and every bracket of a `Y`-element holds the whole of `Z = γ₃/γ₄`.  This is
`gThreeFour_zLayer_le` with its closedness hypothesis discharged, and it is the form a class-four
witness search consumes: to reach the leftover it is enough to reach every square of `γ₂` and
every bracket `commP γ₂ Q₄`. -/
theorem cfourId_zLayer_le {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hsq : ∀ y ∈ lambdaImage (DSq h : Type) 2 4, y ^ 2 ∈ S)
    (hcomm : ∀ y ∈ lambdaImage (DSq h : Type) 2 4, ∀ q, commP y q ∈ S) :
    zLayer (DSq h : Type) 3 ≤ S :=
  gThreeFour_zLayer_le (cfourId_isClosed S) hsq hcomm

end LayerDsq

/-! ## §7 The residual, restated -/

section Residual

variable {h : ℕ}

/-- **The class-four remainder after this wave**, as a named target for the next one: at every
selected marking and every handle, wave 68's class-three witness admits a `γ₂`-valued, exactly
row-trivial correction that kills the relator one class up.  By `cfourId_leftover_mem_zLayer` the
amount such a correction has to move is a single element of `γ₃/γ₄`. -/
def CfourIdReachable (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ d : Fin (sqRank h) → (DSq h : Type),
        (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) ∧
          (∀ i, nuLam h (d i) = 1) ∧ (∀ i, nu' (d i) = 1) ∧
            sqRelWord (fun i => levelMk (DSq h : Type) 4
                (sqArbFrame h nu' j (bridgeTuple nu' j) i * d i)) = 1

/-- The reachability target discharges the class-four supply. -/
theorem cfourId_supply_of_reachable (H : CfourIdReachable h) : SqClassClearingSupply h 4 :=
  cfourId_supply_of_reach H

/-- **The residual, restated from this wave**: with reachability in hand the `h ≥ 1` residual
starts at class five. -/
theorem cfourId_residual_of_reachable (H : CfourIdReachable h) (H5 : ClassFourResidual h) :
    BridgeFinalResidual h :=
  cfour_residual_of_classFour (cfourId_supply_of_reachable H) H5

/-- **The campaign-level statement**: reachability plus the classes `k ≥ 5` give
`SqLamMarkTransitivity h` outright, through wave 68's standing equivalence. -/
theorem cfourId_markTransitivity_of_reachable (H : CfourIdReachable h)
    (H5 : ClassFourResidual h) : SqLamMarkTransitivity h :=
  bridgeFinal_residual_iff.mpr (cfourId_residual_of_reachable H H5)

end Residual

/-! ## §8 Axiom pins -/

section AxiomPins

#print axioms cfourId_base_relator_three
#print axioms cfourId_eichDefect_levelProj
#print axioms cfourId_bridgeDefect_of_eichDefect
#print axioms cfourId_base_relator_three_of_eichDefect
#print axioms cfourId_twoCentral_le_index_two
#print axioms cfourId_modTwoIndep_mul
#print axioms cfourIdLeftover
#print axioms cfourId_leftover_mem_zLayer
#print axioms cfourId_leftover_inv_self
#print axioms cfourId_leftover_eq
#print axioms cfourId_supply_of_reach
#print axioms cfourId_comm_dress_left
#print axioms cfourId_comm_dress_right
#print axioms cfourId_comm_zLayer_dress
#print axioms cfourId_sq_zLayer_dress
#print axioms cfourId_dress_handle
#print axioms cfourId_dress_handleU
#print axioms cfourId_dress_handleV
#print axioms cfourId_x1_sq_mem
#print axioms cfourId_x1_sq_direction
#print axioms cfourId_x1_sq_nuLam
#print axioms cfourId_x1_sq_nu
#print axioms cfourId_row_repair
#print axioms cfourId_x1_sq_admissible
#print axioms cfourId_discreteTopology
#print axioms cfourId_isClosed
#print axioms cfourId_zLayer_le
#print axioms CfourIdReachable
#print axioms cfourId_supply_of_reachable
#print axioms cfourId_residual_of_reachable
#print axioms cfourId_markTransitivity_of_reachable

end AxiomPins

end SqCore

end Dyadic

end GQ2
