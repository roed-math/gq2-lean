/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenRowSupply

/-!
# The deep correction layer  (W51-EV4A, follow-on)

`GQ2/Dyadic/Instances/StageAbstractionEvenRowSupply.lean` showed that the committed sharp
seam `RowExactLevelFibreLiftSupply` is false in even degree for `α ≥ 3`, and that the repair
is to carry `s = α - 1` fresh digits instead of one (`EvenRowDeepFibreLiftSupply s`).  This
file makes that repair usable **without editing** `StageAbstraction.lean`: it builds the
depth-`s` correction structures alongside the committed ones and lands their output in the
committed `Tuple.DefectReachable`, which is the narrow waist the stage induction consumes.
Everything downstream of `DefectReachable` therefore runs unchanged, and the LSq pins stay
byte-identical because nothing committed is touched.

## The dictionary EV-3f uses

Read the left column in the L template, write the right column in the even clone.  `s` is
the depth; the even lane takes `s = α - 1`.

| committed (L template) | deep replacement | rows correct modulo |
|---|---|---|
| `Tuple.TruncatedAdmissibleCorrection T` | `DeepSharpAdmissibleCorrection 0 T` | `2^(k+1)` |
| `Tuple.SharpAdmissibleCorrection T hk` | `DeepSharpAdmissibleCorrection 1 T` | `2^(k+2)` |
| — (no committed analogue) | `DeepSharpAdmissibleCorrection s T` | `2^(k+1+s)` |
| `Tuple.SharpAdmissibleCorrection.toTruncated` | `DeepSharpAdmissibleCorrection.toTruncated` | any `s` |
| `Tuple.SharpAdmissibleCorrection.toAdmissible Hlift` | `DeepSharpAdmissibleCorrection.toAdmissible Hlift hk` | `Hlift : EvenRowDeepFibreLiftSupply s v G chi` |
| `Tuple.FreshDigitStrictificationSupply T hk` | `DeepFreshDigitStrictificationSupply s T` | must deliver `s` digits, not one |
| `Tuple.TruncatedDefectReachable.toDefectReachable` | `deepTruncatedDefectReachable_toDefectReachable` | output is the **same** `Tuple.DefectReachable` |
| `Tuple.DefectReachable`, `stage_nonempty_all_levels`, … | unchanged | — |

Two indexing warnings, both load-bearing:

* `s` counts digits past the **level index**, not past the committed sharp seam: a depth-`s`
  row is correct modulo `2^(m+s)` at level `m`.  So the committed truncated correction is
  `s = 0`, the committed sharp correction is `s = 1`, and the even lane needs `s = α - 1`.
  At `α = 2` the even lane is the committed seam exactly.
* rows are stated on a **representative**: `∃ g, modified i = levelMk g ∧ chi g ≡ v i`.  This
  avoids carrying the well-definedness side condition of `evenSharpDeepChiLevel` in the
  structure; `DeepSharpAdmissibleCorrection.rows_shadow` and `.of_rows_shadow` translate to
  and from the shadow form when that side condition is available, so either may be used.

## Regression pins

`deepSharp_ofSharp`/`deepSharp_toSharp` and `deepSharp_ofTruncated`/`deepSharp_toTruncated0`
convert against the committed structures at `s = 1` and `s = 0`, and the four
`…_correction` pins record that every conversion is the identity on the correction datum
(the rest of a `Prop`-valued field is proof-irrelevant), so the round trips are literal.

## Numbering

1. the depth-`s` correction and its precision calculus;
2. conversion to the committed correction interface;
3. the `s = 0` and `s = 1` regressions against the committed structures;
4. the defect-reachability chain landing in `Tuple.DefectReachable`.
-/

namespace GQ2.Dyadic.EvenRowSupply

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.LSquare.SqCyclotomicStageTuple (sharpChiLevel sharpChiLevel_levelMk)

/-! ## §1 The depth-`s` sharp correction -/

section DeepCorrection

variable {n : ℕ} {W : StageWord n} {v : Fin n → ℤ_[2]ˣ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- Reduction mod `2^j` detects differences up to `2^j` (local restatement of the private
helper in `StageAbstractionEvenRowSupply.lean`; hoist request recorded there). -/
private theorem deep_toZModPow_eq_iff_dvd {j : ℕ} {x y : ℤ_[2]} :
    PadicInt.toZModPow j x = PadicInt.toZModPow j y ↔ (2 : ℤ_[2]) ^ j ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]
  norm_num

/-- **Precision is monotone**: a congruence modulo `2^j` survives every coarser modulus.
This is the only arithmetic the correction layer needs. -/
theorem deep_units_congr_of_le {i j : ℕ} (hij : i ≤ j) {u w : ℤ_[2]ˣ}
    (h : Units.map (PadicInt.toZModPow j).toMonoidHom u =
      Units.map (PadicInt.toZModPow j).toMonoidHom w) :
    Units.map (PadicInt.toZModPow i).toMonoidHom u =
      Units.map (PadicInt.toZModPow i).toMonoidHom w := by
  have h' : PadicInt.toZModPow j (u : ℤ_[2]) = PadicInt.toZModPow j (w : ℤ_[2]) := by
    simpa using congrArg Units.val h
  refine Units.ext ?_
  show PadicInt.toZModPow i (u : ℤ_[2]) = PadicInt.toZModPow i (w : ℤ_[2])
  rw [deep_toZModPow_eq_iff_dvd] at h' ⊢
  exact (pow_dvd_pow 2 hij).trans h'

/-- **The depth-`s` sharp correction.**  The `Tuple.SharpAdmissibleCorrection` clone whose
rows are correct modulo `2^(k+1+s)` instead of `2^(k+2)`.  Rows are stated on a
representative, so the structure carries no well-definedness side condition; at `s = 1` it
converts both ways against the committed sharp correction (§3). -/
structure DeepSharpAdmissibleCorrection (s : ℕ) {k : ℕ} (T : Tuple W v G chi k) where
  /-- The coordinatewise correction at level `k+1`. -/
  correction : Fin n → levelQuot G (k + 1)
  /-- The correction has depth `k-1`. -/
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)
  /-- Every modified row has a representative whose character value matches the table value
  modulo `2^(k+1+s)`. -/
  rows : ∀ i, ∃ g : G,
    stageModified (fun i ↦ canonLift G k (T.generators i)) correction i =
        levelMk G (k + 1) g ∧
      Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom (chi g) =
        Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom (v i)

namespace DeepSharpAdmissibleCorrection

variable {s k : ℕ} {T : Tuple W v G chi k}

/-- Precision may be lowered: a depth-`s` correction is a depth-`s'` correction for `s' ≤ s`.
The correction datum is untouched. -/
def toDepthLe (Wc : DeepSharpAdmissibleCorrection s T) {s' : ℕ} (hs : s' ≤ s) :
    DeepSharpAdmissibleCorrection s' T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨g, hmod, hcong⟩ := Wc.rows i
    exact ⟨g, hmod, deep_units_congr_of_le (by omega) hcong⟩

@[simp] theorem toDepthLe_correction (Wc : DeepSharpAdmissibleCorrection s T) {s' : ℕ}
    (hs : s' ≤ s) : (Wc.toDepthLe hs).correction = Wc.correction := rfl

/-- The shadow form of the rows, available once the depth-`s` shadow is well defined.  This is
the shape a fresh-digit calculation naturally produces when it works on the quotient. -/
theorem rows_shadow (Wc : DeepSharpAdmissibleCorrection s T)
    (Hdef : (twoCentralSeries G (k + 1)).map chi.toMonoidHom ≤
      (Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom).ker) (i : Fin n) :
    evenSharpDeepChiLevel chi (k + 1) s Hdef
        (stageModified (fun i ↦ canonLift G k (T.generators i)) Wc.correction i) =
      Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom (v i) := by
  obtain ⟨g, hmod, hcong⟩ := Wc.rows i
  rw [hmod, evenSharpDeepChiLevel_levelMk]
  exact hcong

/-- Conversely, the shadow form gives the representative form: pick any representative. -/
def of_rows_shadow
    (Hdef : (twoCentralSeries G (k + 1)).map chi.toMonoidHom ≤
      (Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom).ker)
    (correction : Fin n → levelQuot G (k + 1))
    (depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1))
    (rows : ∀ i, evenSharpDeepChiLevel chi (k + 1) s Hdef
        (stageModified (fun i ↦ canonLift G k (T.generators i)) correction i) =
      Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom (v i)) :
    DeepSharpAdmissibleCorrection s T where
  correction := correction
  depth := depth
  rows i := by
    obtain ⟨g, hg⟩ := levelMk_surjective G (k + 1)
      (stageModified (fun i ↦ canonLift G k (T.generators i)) correction i)
    refine ⟨g, hg.symm, ?_⟩
    have := rows i
    rw [hg.symm, evenSharpDeepChiLevel_levelMk] at this
    exact this

/-! ### §2 Conversion to the committed correction interface -/

/-- Forgetting every fresh digit: a depth-`s` correction is a committed truncated correction.
The `Tuple.SharpAdmissibleCorrection.toTruncated` clone, valid at every `s`. -/
def toTruncated (Wc : DeepSharpAdmissibleCorrection s T) :
    Tuple.TruncatedAdmissibleCorrection T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨g, hmod, hcong⟩ := Wc.rows i
    rw [hmod, chiLevel_levelMk]
    exact deep_units_congr_of_le (by omega) hcong

/-- **The seam.**  Depth-`s` rows plus the depth-`s` supply give exact fibres: the
`Tuple.SharpAdmissibleCorrection.toAdmissible` clone, with
`EvenRowDeepFibreLiftSupply s` in place of the committed `RowExactLevelFibreLiftSupply`
(which §5 of `StageAbstractionEvenRowSupply.lean` refutes in even degree). -/
def toAdmissible (Wc : DeepSharpAdmissibleCorrection s T)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) (hk : 1 ≤ k) :
    Tuple.AdmissibleCorrection T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨g, hmod, hcong⟩ := Wc.rows i
    obtain ⟨x, hxchi, hx⟩ := Hlift.lift (k + 1) (by omega) i g hcong
    exact ⟨x, hxchi, by rw [hmod, hx]⟩

@[simp] theorem toTruncated_correction (Wc : DeepSharpAdmissibleCorrection s T) :
    Wc.toTruncated.correction = Wc.correction := rfl

@[simp] theorem toAdmissible_correction (Wc : DeepSharpAdmissibleCorrection s T)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) (hk : 1 ≤ k) :
    (Wc.toAdmissible Hlift hk).correction = Wc.correction := rfl

/-! ### §3 The `s = 0` and `s = 1` regressions against the committed structures -/

/-- `s = 1` is the committed sharp correction: forward. -/
def ofSharp {hk : 1 ≤ k} (Wc : Tuple.SharpAdmissibleCorrection T hk) :
    DeepSharpAdmissibleCorrection 1 T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨g, hg⟩ := levelMk_surjective G (k + 1)
      (stageModified (fun i ↦ canonLift G k (T.generators i)) Wc.correction i)
    refine ⟨g, hg.symm, ?_⟩
    have h := Wc.rows i
    rw [← hg, sharpChiLevel_levelMk] at h
    exact h

/-- `s = 1` is the committed sharp correction: back. -/
def toSharp (Wc : DeepSharpAdmissibleCorrection 1 T) (hk : 1 ≤ k) :
    Tuple.SharpAdmissibleCorrection T hk where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨g, hmod, hcong⟩ := Wc.rows i
    rw [hmod, sharpChiLevel_levelMk]
    exact hcong

/-- `s = 0` is the committed truncated correction: forward (`toTruncated` is the way back). -/
def ofTruncated (Wc : Tuple.TruncatedAdmissibleCorrection T) :
    DeepSharpAdmissibleCorrection 0 T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨g, hg⟩ := levelMk_surjective G (k + 1)
      (stageModified (fun i ↦ canonLift G k (T.generators i)) Wc.correction i)
    refine ⟨g, hg.symm, ?_⟩
    have h := Wc.rows i
    rw [← hg, chiLevel_levelMk] at h
    exact h

@[simp] theorem ofSharp_correction {hk : 1 ≤ k} (Wc : Tuple.SharpAdmissibleCorrection T hk) :
    (ofSharp Wc).correction = Wc.correction := rfl

@[simp] theorem toSharp_correction (Wc : DeepSharpAdmissibleCorrection 1 T) (hk : 1 ≤ k) :
    (Wc.toSharp hk).correction = Wc.correction := rfl

@[simp] theorem ofTruncated_correction (Wc : Tuple.TruncatedAdmissibleCorrection T) :
    (ofTruncated Wc).correction = Wc.correction := rfl

/-- Round trip at `s = 1`: the committed sharp correction survives the deep detour
unchanged. -/
theorem ofSharp_toSharp_correction {hk : 1 ≤ k}
    (Wc : Tuple.SharpAdmissibleCorrection T hk) :
    ((ofSharp Wc).toSharp hk).correction = Wc.correction := rfl

/-- Round trip at `s = 0`: likewise for the committed truncated correction. -/
theorem ofTruncated_toTruncated_correction (Wc : Tuple.TruncatedAdmissibleCorrection T) :
    (ofTruncated Wc).toTruncated.correction = Wc.correction := rfl

/-- The committed `toTruncated` and the deep one agree at `s = 1`: reading the committed
sharp correction through the deep layer loses nothing. -/
theorem ofSharp_toTruncated_correction {hk : 1 ≤ k}
    (Wc : Tuple.SharpAdmissibleCorrection T hk) :
    (ofSharp Wc).toTruncated.correction = (Wc.toTruncated).correction := rfl

end DeepSharpAdmissibleCorrection

/-! ## §4 The defect-reachability chain

The output is the **committed** `Tuple.DefectReachable`, so the stage induction
(`Tuple.stage_nonempty_all_levels`, `openTuple_nonempty_of_base_and_corrections`) consumes
the even lane's corrections with no change at all. -/

section DefectChain

variable {s k : ℕ} {T : Tuple W v G chi k}

/-- The depth-`s` fresh-digit station: the even lane's `SL1`/`SL2` output must be
strictifiable to `s` fresh digits, not one.  This is the single station EV-3f has to
strengthen relative to the L template. -/
def DeepFreshDigitStrictificationSupply (s : ℕ) {k : ℕ} (T : Tuple W v G chi k) : Prop :=
  ∀ Wc : Tuple.TruncatedAdmissibleCorrection T,
    ∃ Wdeep : DeepSharpAdmissibleCorrection s T,
      stageShift W (fun i ↦ canonLift G k (T.generators i)) Wdeep.correction =
        stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction

/-- **The money lemma.**  Finite-precision reachability plus the depth-`s` fresh digits plus
the depth-`s` supply give the committed `DefectReachable`.  Clone of
`Tuple.TruncatedDefectReachable.toDefectReachable` with the seam replaced. -/
theorem deepTruncatedDefectReachable_toDefectReachable
    (H : Tuple.TruncatedDefectReachable T) (hk : 1 ≤ k)
    (Hfresh : DeepFreshDigitStrictificationSupply s T)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) :
    Tuple.DefectReachable T := by
  obtain ⟨Wc, hW⟩ := H
  obtain ⟨Wdeep, hdeep⟩ := Hfresh Wc
  exact ⟨Wdeep.toAdmissible Hlift hk, hdeep.trans hW⟩

/-- Direct form: a depth-`s` correction that already kills the defect is enough. -/
theorem deep_defectReachable_of_kills
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) (hk : 1 ≤ k)
    (Wc : DeepSharpAdmissibleCorrection s T)
    (hkill : stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction =
      (stageDefect W G k T.generators)⁻¹) :
    Tuple.DefectReachable T :=
  ⟨Wc.toAdmissible Hlift hk, hkill⟩

/-- Regression: at `s = 1` the deep fresh-digit station is the committed one, so the deep
chain specialises to the committed chain. -/
theorem deepFresh_of_freshDigitStrictification (hk : 1 ≤ k)
    (Hfresh : Tuple.FreshDigitStrictificationSupply T hk) :
    DeepFreshDigitStrictificationSupply 1 T := by
  intro Wc
  obtain ⟨Wsharp, hsharp⟩ := Hfresh Wc
  exact ⟨DeepSharpAdmissibleCorrection.ofSharp Wsharp, hsharp⟩

end DefectChain

end DeepCorrection

end

end GQ2.Dyadic.EvenRowSupply

/-! ## Axiom pins -/

#print axioms GQ2.Dyadic.EvenRowSupply.deep_units_congr_of_le
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toDepthLe
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toDepthLe_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.rows_shadow
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.of_rows_shadow
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toTruncated
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toTruncated_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toAdmissible
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toAdmissible_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofSharp
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofSharp_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toSharp
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.toSharp_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofTruncated
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofTruncated_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofSharp_toSharp_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofTruncated_toTruncated_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepSharpAdmissibleCorrection.ofSharp_toTruncated_correction
#print axioms GQ2.Dyadic.EvenRowSupply.DeepFreshDigitStrictificationSupply
#print axioms GQ2.Dyadic.EvenRowSupply.deepTruncatedDefectReachable_toDefectReachable
#print axioms GQ2.Dyadic.EvenRowSupply.deep_defectReachable_of_kills
#print axioms GQ2.Dyadic.EvenRowSupply.deepFresh_of_freshDigitStrictification
