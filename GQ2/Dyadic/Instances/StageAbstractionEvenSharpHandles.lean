/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpanStep
import GQ2.Dyadic.Instances.StageAbstractionDeepCorrections

/-!
# W51-EV3F2 §A: the even sharp-neutral correction layer (block H-sharp)

Ticket **EV-3f**, assembly half, of `docs/dyadic/ev4b-stage-abstraction.md` §4, cut against
the F1/F2 seam recorded in `docs/dyadic/w51-ev3f-seam.md` §2.  This file is the even clone of
**block H-sharp** of the L template
`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteStageHandles.lean` (lines 416-1293), the
half of that file whose every declaration is stated against the character.  Block H-lit is
*not* cloned here: by the seam note §1.1 its even form is delivered below us by F1 in
`StageAbstractionEvenRawSpan.lean` as `evenRawDbarWord` and friends, and we import it.

Two changes relative to the L template, both forced and both recorded on the board.

* **The character precision is `s`, not `1`.**  The committed `SharpExactLevelFibreLiftSupply`
  is false in even degree, and the corrected seam (board crux ii, as upgraded by the
  orchestrator) is `EvenRowDeepFibreLiftSupply s` at `s = α - 1` uniformly on both branches.
  So every row condition here carries a depth parameter `s`, and the neutral corrections are
  the ones trivial for the depth-`s` character shadow.  The substitution dictionary is
  `StageAbstractionDeepCorrections.lean`; we build on its `DeepSharpAdmissibleCorrection s`
  rather than on `Tuple.SharpAdmissibleCorrection`.
* **One crossed-derivation word serves both even relators.**  The L template's
  `stageShift_eq_dbarWordR2_mul_sqHandleDbarWord` has two even analogues on paper, one per
  branch, but by the seam note §3(a) they are the *same* word `evenRawDbarWord` at `2 ≤ α`.
  §5 packages that as the single supply `EvenSharpDbarShiftSupply`, discharged for `N` and for
  `M` by one lemma each on top of F1's `evenRawStageShift_n` / `evenRawStageShift_m`.  This is
  the board's crux (i), and it is one comparison, not two.

## Numbering

1. the depth witness making the deep character shadow well defined at level `k+1`;
2. the depth-`s` sharp-neutral corrections and their group structure;
3. the neutral action on deep admissible corrections, and the torsor property;
4. existence of deep admissible corrections at every depth;
5. the shift supply `EvenSharpDbarShiftSupply` and its two discharges (crux i);
6. the actual-defect supply and its passage to `Tuple.DefectReachable`;
7. the residual element and the reachability criterion.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.EvenRowSupply

/-! ## §1 The depth witness

The deep character shadow `evenSharpDeepChiLevel chi (k+1) s` is defined only when `chi` kills
`λ_{k+1}` to precision `2^(k+1+s)`.  On the even lane that holds at `s = α - 1` and, from this
bound, at no larger `s`: the two exponents match on the nose.  This is a fact about the even
lane the L template has no analogue of, and it is an independent confirmation of the
orchestrator's uniform depth verdict. -/

section DeepDefined

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **The depth `α - 1` is exactly the well-defined one.**  If every character value is
`≡ ±1 (mod 2^α)` then `chi` kills `λ_{k+1}` modulo `2^(k+1+(α-1))`, which is the side
condition of `evenSharpDeepChiLevel chi (k+1) (α-1)`.

The arithmetic is an equality, not an inequality: `evenSharp_map_twoCentralSeries_le` applied
at `m = k - 1` produces the exponent `α + (k-1) + 1 = k + α`, and the shadow at level `k+1`
and depth `α - 1` asks for `k + 1 + (α - 1) = k + α`.  Neither side has slack, so this bound
supports the depth `α - 1` and no deeper one. -/
theorem evenSharpDeepDefined {α k : ℕ} (hα : 1 ≤ α) (hk : 1 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) :
    (twoCentralSeries G (k + 1)).map chi.toMonoidHom ≤
      (Units.map (PadicInt.toZModPow (k + 1 + (α - 1))).toMonoidHom).ker := by
  have h := evenSharp_map_twoCentralSeries_le hα hbound (k - 1)
  have e1 : k - 1 + 2 = k + 1 := by omega
  have e2 : α + (k - 1) + 1 = k + 1 + (α - 1) := by omega
  rwa [e1, e2] at h

end DeepDefined

/-! ## §2 The depth-`s` sharp-neutral corrections

The clone of `SharpNeutralCorrection` (L template, line 542): the homogeneous directions of
the affine space of corrections.  As in `DeepSharpAdmissibleCorrection`, the row condition is
stated on a *representative*, so the structure carries no well-definedness side condition and
§1 is needed only where the shadow itself is used.

Indexing note (F1's porting note, carried): everything is stated at `levelQuot G (k + 1)` with
`k` the caller's level, never at a free level index, because `evenRawDbarWord` is indexed that
way and a free index sends unification into a `whnf` blowup. -/

section Neutral

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- A depth-`k-1` correction of the even marking all of whose coordinates are trivial for the
depth-`s` character shadow.  These are exactly the directions along which a deep admissible
correction may be moved without disturbing its rows (§3). -/
structure EvenSharpNeutralCorrection (s : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chi : ContinuousMonoidHom G ℤ_[2]ˣ) (h k : ℕ) where
  /-- The correction, one coordinate per even generator. -/
  correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)
  /-- Every coordinate has depth `k-1`. -/
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)
  /-- Every coordinate has a representative of trivial character to `s` fresh digits. -/
  neutral : ∀ i, ∃ g : G, correction i = levelMk G (k + 1) g ∧
    Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom (chi g) = 1

namespace EvenSharpNeutralCorrection

variable {s h k : ℕ}

@[ext]
theorem ext {N N' : EvenSharpNeutralCorrection s G chi h k}
    (H : N.correction = N'.correction) : N = N' := by
  cases N; cases N'; cases H; rfl

/-- The trivial neutral correction. -/
protected def one : EvenSharpNeutralCorrection s G chi h k where
  correction _ := 1
  depth _ := Subgroup.one_mem _
  neutral _ := ⟨1, (map_one (levelMk G (k + 1))).symm, by rw [map_one, map_one]⟩

/-- Coordinatewise product of neutral corrections. -/
protected def mul (N N' : EvenSharpNeutralCorrection s G chi h k) :
    EvenSharpNeutralCorrection s G chi h k where
  correction i := N.correction i * N'.correction i
  depth i := Subgroup.mul_mem _ (N.depth i) (N'.depth i)
  neutral i := by
    obtain ⟨g, hg, hgchi⟩ := N.neutral i
    obtain ⟨g', hg', hg'chi⟩ := N'.neutral i
    exact ⟨g * g', by rw [hg, hg', map_mul], by rw [map_mul, map_mul, hgchi, hg'chi, one_mul]⟩

/-- Coordinatewise inverse of a neutral correction. -/
protected def inv (N : EvenSharpNeutralCorrection s G chi h k) :
    EvenSharpNeutralCorrection s G chi h k where
  correction i := (N.correction i)⁻¹
  depth i := Subgroup.inv_mem _ (N.depth i)
  neutral i := by
    obtain ⟨g, hg, hgchi⟩ := N.neutral i
    exact ⟨g⁻¹, by rw [hg, map_inv], by rw [map_inv, map_inv, hgchi, inv_one]⟩

instance instGroup : Group (EvenSharpNeutralCorrection s G chi h k) where
  one := EvenSharpNeutralCorrection.one
  mul := EvenSharpNeutralCorrection.mul
  inv := EvenSharpNeutralCorrection.inv
  mul_assoc N₁ N₂ N₃ := by ext i; exact mul_assoc _ _ _
  one_mul N := by ext i; exact one_mul _
  mul_one N := by ext i; exact mul_one _
  inv_mul_cancel N := by ext i; exact inv_mul_cancel _

@[simp] theorem one_correction (i : Fin (MarkedCore.coreRank h)) :
    (1 : EvenSharpNeutralCorrection s G chi h k).correction i = 1 := rfl

@[simp] theorem mul_correction (N N' : EvenSharpNeutralCorrection s G chi h k)
    (i : Fin (MarkedCore.coreRank h)) :
    (N * N').correction i = N.correction i * N'.correction i := rfl

@[simp] theorem inv_correction (N : EvenSharpNeutralCorrection s G chi h k)
    (i : Fin (MarkedCore.coreRank h)) :
    (N⁻¹).correction i = (N.correction i)⁻¹ := rfl

/-- Forgetting the character condition: the underlying raw depth correction of F1's span
calculus.  This is the one place the two halves of EV-3f touch at the level of data. -/
def toRaw (N : EvenSharpNeutralCorrection s G chi h k) : EvenRawDepthCorrection G h k where
  correction := N.correction
  depth := N.depth

@[simp] theorem toRaw_correction (N : EvenSharpNeutralCorrection s G chi h k)
    (i : Fin (MarkedCore.coreRank h)) : N.toRaw.correction i = N.correction i := rfl

/-- Forgetting the character condition is a homomorphism. -/
def toRawHom : EvenSharpNeutralCorrection s G chi h k →* EvenRawDepthCorrection G h k where
  toFun := toRaw
  map_one' := by ext i; rfl
  map_mul' N N' := by ext i; rfl

@[simp] theorem toRawHom_correction (N : EvenSharpNeutralCorrection s G chi h k)
    (i : Fin (MarkedCore.coreRank h)) :
    (toRawHom N : EvenRawDepthCorrection G h k).correction i = N.correction i := rfl

/-- Precision may be lowered, exactly as for `DeepSharpAdmissibleCorrection.toDepthLe`. -/
def toDepthLe (N : EvenSharpNeutralCorrection s G chi h k) {s' : ℕ} (hs : s' ≤ s) :
    EvenSharpNeutralCorrection s' G chi h k where
  correction := N.correction
  depth := N.depth
  neutral i := by
    obtain ⟨g, hg, hgchi⟩ := N.neutral i
    refine ⟨g, hg, ?_⟩
    have := deep_units_congr_of_le (i := k + 1 + s') (j := k + 1 + s) (by omega)
      (u := chi g) (w := 1) (by rw [map_one]; exact hgchi)
    rw [map_one] at this
    exact this

@[simp] theorem toDepthLe_correction (N : EvenSharpNeutralCorrection s G chi h k) {s' : ℕ}
    (hs : s' ≤ s) : (N.toDepthLe hs).correction = N.correction := rfl

end EvenSharpNeutralCorrection

end Neutral

end

end GQ2.Dyadic.StageGeneric
