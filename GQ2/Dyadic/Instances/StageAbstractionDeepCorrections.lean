/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenRowSupply
import GQ2.Dyadic.SqCore.PivotLemma

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

`DeepSharpAdmissibleCorrection.ofSharp`/`.toSharp` convert against the committed sharp
correction at `s = 1`, `.ofTruncated`/`.toTruncated` against the committed truncated one at
`s = 0`, and the `…_correction` pins record that every conversion is the identity on the
correction datum (the remaining fields are `Prop`-valued, hence proof-irrelevant), so the
round trips are literal.

## The two seam questions, answered

* **Is `s = α - 1` enough?**  Yes, and on the `M` branch unconditionally:
  `evenRow_deepSupply_imChiM` (§6.4).  With `evenSharp_not_imageRelLe_imChiM` ruling out
  every smaller depth, the even `M` seam sits exactly at `s = α - 1`.
* **What happens at `α = 2`?**  The committed seam is *true* there:
  `evenRow_rowSupply_imChiM_two` (§6.4), because `imChiM 2 = ⊤`.  So `α ≥ 3` is precisely the
  regime that needs this file.

The `N` branch is not settled here; see the note at `evenRow_deepSupply_of_deepUnits`.

## Numbering

1. the depth-`s` correction and its precision calculus;
2. conversion to the committed correction interface;
3. the `s = 0` and `s = 1` regressions against the committed structures;
4. the defect-reachability chain landing in `Tuple.DefectReachable`;
5. sufficiency of the depth `s = α - 1`, reduced to iterated deep square roots;
6. the image identification discharging that reduction on the `M` branch, and the `α = 2`
   verdict.
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

/-! ## §5 Sufficiency of the depth `s = α - 1`

`StageAbstractionEvenRowSupply.lean` proved `s = α - 1` is *necessary* (no smaller depth
works) and *attainable* (`evenSharp_map_le_deep`).  Here is the other half: `s = α - 1` is
*enough*, reduced through `evenRow_deepSupply_of_powRoots` to a single input.

The 2-adic content is `evenDeep_exists_pow_root`: for `s ≥ 2`, every unit that is `1` modulo
`2^(s+1+t)` is a `2^t`-th power of a unit that is `1` modulo `2^(s+1)`.  That is
`DyadicSquares.exists_deep_unit_sq` iterated `t` times, and it is proved here outright.
With `s = α - 1` the root lands in `1 + 2^αℤ₂` exactly, which is why the depth matches.

The other input is a statement about the character, not about `ℤ₂`: the root must itself be
a character value, i.e. `1 + 2^αℤ₂ ≤ im chi`.  It is carried here as a named hypothesis
(`evenRow_deepSupply_of_deepUnits`) and then **discharged on the `M` branch** in §6, so the
`M` seam is unconditional.
-/

section Sufficiency

variable {n : ℕ} {v : Fin n → ℤ_[2]ˣ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **Iterated deep square roots.**  For `s ≥ 2`, a unit which is `1` modulo `2^(s+1+t)` is a
`2^t`-th power of a unit which is `1` modulo `2^(s+1)`.  Each step is
`DyadicSquares.exists_deep_unit_sq`, which trades one digit of precision for one square
root; the hypothesis `2 ≤ s` is what keeps every intermediate level in that lemma's range. -/
theorem evenDeep_exists_pow_root {s : ℕ} (hs : 2 ≤ s) (t : ℕ) {y : ℤ_[2]ˣ}
    (hy : PadicInt.toZModPow (s + 1 + t) (y : ℤ_[2]) = 1) :
    ∃ z : ℤ_[2]ˣ, y = z ^ 2 ^ t ∧ PadicInt.toZModPow (s + 1) (z : ℤ_[2]) = 1 := by
  induction t generalizing y with
  | zero => exact ⟨y, by rw [pow_zero, pow_one], hy⟩
  | succ t ih =>
    obtain ⟨w, hyw, hw⟩ := GQ2.DyadicSquares.exists_deep_unit_sq (n := s + t) (by omega)
      (show PadicInt.toZModPow (s + t + 2) (y : ℤ_[2]) = 1 by
        rw [show s + t + 2 = s + 1 + (t + 1) by omega]; exact hy)
    obtain ⟨z, hwz, hz⟩ := ih (show PadicInt.toZModPow (s + 1 + t) (w : ℤ_[2]) = 1 by
      rw [show s + 1 + t = s + t + 1 by omega]; exact hw)
    refine ⟨z, ?_, hz⟩
    rw [hyw, hwz, ← pow_mul, ← pow_succ]

/-- **The sufficiency chain.**  If every unit that is `1` modulo `2^α` is a character value,
then the depth-`(α - 1)` supply holds for every table with values in the image.  §6 discharges
the hypothesis on the `M` branch.  On the `N` branch it is *false* as stated — `imChiN α`
contains no unit of exact level `α` congruent to `1` mod `4`, its elements of that shape
starting only at level `α + 1` — so the `N` branch needs the roots taken up to sign, i.e. the
exponent-valuation form of procyclic surjectivity rather than the congruence form; that is
the one piece this file leaves open.  This is the
positive counterpart of the §5 refutation of `StageAbstractionEvenRowSupply.lean`: at the
corrected depth the seam works, and it works for the same reason the odd-degree seam does. -/
theorem evenRow_deepSupply_of_deepUnits {α : ℕ} (hα : 3 ≤ α)
    (hsub : ∀ z : ℤ_[2]ˣ, PadicInt.toZModPow α (z : ℤ_[2]) = 1 → z ∈ Set.range chi)
    (hv : ∀ i, v i ∈ Set.range chi) :
    EvenRowDeepFibreLiftSupply (α - 1) v G chi := by
  refine evenRow_deepSupply_of_powRoots (fun m hm y hyker ↦ ?_) hv
  have hy : PadicInt.toZModPow (α - 1 + 1 + (m - 1)) (y : ℤ_[2]) = 1 := by
    have h1 : (2 : ℤ_[2]) ^ (m + (α - 1)) ∣ (y : ℤ_[2]) - 1 := evenSharp_mem_ker_iff.mp hyker
    rw [show α - 1 + 1 + (m - 1) = m + (α - 1) by omega]
    have := evenSharp_mem_ker_iff (j := m + (α - 1)) (u := y)
    exact (by simpa using congrArg Units.val (MonoidHom.mem_ker.mp (this.mpr h1)))
  obtain ⟨z, hyz, hz⟩ := evenDeep_exists_pow_root (s := α - 1) (by omega) (m - 1) hy
  obtain ⟨w, hw⟩ := hsub z (by rw [show α = α - 1 + 1 by omega]; exact hz)
  exact ⟨w, by rw [hw, ← hyz]⟩

end Sufficiency

/-! ## §6 Discharging the image hypothesis on the `M` branch

The hypothesis `1 + 2^αℤ₂ ≤ im chi` of §5 is not owed after all on the `M` branch.  The
committed `GQ2.exists_zpowZtwo_eq_of_exact_level` (`GQ2/Dyadic/SqCore/PivotLemma.lean:153`)
is exactly the required procyclic surjectivity, but only at exact level `2`; §6.1 ports it to
exact level `s ≥ 2`, which is mechanical — the only level-specific input is the telescoping
lemma, whose general form `mExists_unit_pow_two_pow_sub_one` is committed.  §6.2 adds the
missing bridge from `zpowZtwo` to `topologicalClosure`, and §6.3 concludes
`1 + 2^αℤ₂ ≤ imChiM α`, since `mUnit α` has exact level `α` (`mUnit_sub_one`).
-/

section ImageIdentification

open GQ2.Dyadic.MarkedCore (mUnit imChiM mUnit_sub_one mExists_unit_pow_two_pow_sub_one)

/-! ### §6.1 The pivot lemma at exact level `s` -/

/-- **The approximation half at exact level `s`.**  Port of `GQ2.exists_nat_pow_sub_dvd` from
`4` to `2^s`: if `η - 1 = 2^s·a` with `a` a unit, every `ξ ≡ 1 mod 2^s` is matched by a
natural power of `η` modulo `2^(s+k)`.  The digit step is
`mExists_unit_pow_two_pow_sub_one`. -/
theorem pivot_exists_nat_pow_sub_dvd (η a : ℤ_[2]ˣ) (s : ℕ) (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * (a : ℤ_[2]))
    {ξ : ℤ_[2]} (hξ : (2 : ℤ_[2]) ^ s ∣ ξ - 1) (k : ℕ) :
    ∃ n : ℕ, (2 : ℤ_[2]) ^ (s + k) ∣ ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) - ξ := by
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := hξ
    refine ⟨0, -t, ?_⟩
    rw [pow_zero, Units.val_one]
    linear_combination -ht
  | succ j ih =>
    obtain ⟨n, d, hd⟩ := ih
    by_cases hdiv : (2 : ℤ_[2]) ∣ d
    · obtain ⟨e, he⟩ := hdiv
      exact ⟨n, e, by rw [hd, he]; ring⟩
    obtain ⟨u, hu⟩ := mExists_unit_pow_two_pow_sub_one η a s hs hη j
    have hval : ((η ^ (n + 2 ^ j) : ℤ_[2]ˣ) : ℤ_[2])
        = ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) * ((η ^ 2 ^ j : ℤ_[2]ˣ) : ℤ_[2]) := by
      rw [pow_add, Units.val_mul]
    have hstep : ((η ^ (n + 2 ^ j) : ℤ_[2]ˣ) : ℤ_[2]) - ξ
        = 2 ^ (s + j) * (d + (u : ℤ_[2]) * ((η ^ n : ℤ_[2]ˣ) : ℤ_[2])) := by
      rw [show j + s = s + j by omega] at hu
      rw [hval]
      linear_combination hd + ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) * hu
    obtain ⟨e, he⟩ := GQ2.two_dvd_add_of_isUnit (GQ2.isUnit_of_not_two_dvd hdiv)
      (u.isUnit.mul (η ^ n).isUnit)
    exact ⟨n + 2 ^ j, e, by rw [show s + (j + 1) = s + j + 1 by omega, hstep, he]; ring⟩

/-- **Procyclic surjectivity at exact level `s`.**  Port of
`GQ2.exists_zpowZtwo_eq_of_exact_level`: an element of exact level `s ≥ 2` hits every
`ξ ≡ 1 mod 2^s` at some `2`-adic exponent.  The Cantor-intersection argument is
level-agnostic; only the approximation input changed. -/
theorem pivot_exists_zpowZtwo_eq (η a : ℤ_[2]ˣ) (s : ℕ) (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * (a : ℤ_[2]))
    {ξ : ℤ_[2]ˣ} (hξ : (2 : ℤ_[2]) ^ s ∣ ((ξ : ℤ_[2])) - 1) :
    ∃ c : ℤ_[2], zpowZtwo isProP_two_unitsPadicInt η c = ξ := by
  set f : ℤ_[2] → ℤ_[2] :=
    fun c ↦ ((zpowZtwo isProP_two_unitsPadicInt η c : ℤ_[2]ˣ) : ℤ_[2]) with hf
  have hcont : Continuous f :=
    Units.continuous_val.comp (continuous_zpowZtwo isProP_two_unitsPadicInt η)
  set A : ℕ → Set ℤ_[2] := fun k ↦ {c | (2 : ℤ_[2]) ^ (s + k) ∣ f c - (ξ : ℤ_[2])} with hA
  have hball : ∀ k, A k = f ⁻¹' Metric.closedBall ((ξ : ℤ_[2]))
      (((2 : ℕ) : ℝ) ^ (-((s + k : ℕ) : ℤ))) := by
    intro k
    ext c
    show (2 : ℤ_[2]) ^ (s + k) ∣ f c - (ξ : ℤ_[2]) ↔ _
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    norm_cast
  have hclosed : ∀ k, IsClosed (A k) := fun k ↦ by
    rw [hball k]; exact Metric.isClosed_closedBall.preimage hcont
  have hne : ∀ k, (A k).Nonempty := by
    intro k
    obtain ⟨n, hn⟩ := pivot_exists_nat_pow_sub_dvd η a s hs hη hξ k
    refine ⟨(n : ℤ_[2]), ?_⟩
    have hpow : f ((n : ℕ) : ℤ_[2]) = ((η ^ n : ℤ_[2]ˣ) : ℤ_[2]) :=
      congrArg Units.val (zpowZtwo_natCast isProP_two_unitsPadicInt η n)
    show (2 : ℤ_[2]) ^ (s + k) ∣ f ((n : ℕ) : ℤ_[2]) - (ξ : ℤ_[2])
    rw [hpow]
    exact hn
  have hmono : ∀ k, A (k + 1) ⊆ A k := fun k c hc ↦
    dvd_trans (pow_dvd_pow (2 : ℤ_[2]) (by omega)) hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hmono
    hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hc
  refine ⟨c, Units.ext ?_⟩
  have hzero : f c - (ξ : ℤ_[2]) = 0 := by
    refine PadicInt.ext_of_toZModPow.mp fun m ↦ ?_
    have hdvd : (2 : ℤ_[2]) ^ m ∣ f c - (ξ : ℤ_[2]) :=
      dvd_trans (pow_dvd_pow (2 : ℤ_[2]) (by omega)) (hc m)
    rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hdvd
  exact sub_eq_zero.mp hzero

/-! ### §6.2 From `zpowZtwo` to the topological closure -/

/-- **The missing bridge.**  A `2`-adic power of `η` lies in the closed subgroup generated by
`η`: the exponent map is continuous and `ℕ` is dense in `ℤ₂`, so every `2`-adic power is a
limit of honest integer powers. -/
theorem mem_topologicalClosure_of_zpowZtwo (η : ℤ_[2]ˣ) (c : ℤ_[2]) :
    zpowZtwo isProP_two_unitsPadicInt η c ∈
      (Subgroup.closure ({η} : Set ℤ_[2]ˣ)).topologicalClosure := by
  have hgen : η ∈ Subgroup.closure ({η} : Set ℤ_[2]ˣ) := Subgroup.subset_closure (by simp)
  refine PadicInt.denseRange_natCast.induction_on c ?_ ?_
  · exact (Subgroup.isClosed_topologicalClosure _).preimage
      (continuous_zpowZtwo isProP_two_unitsPadicInt η)
  · intro m
    rw [zpowZtwo_natCast]
    exact Subgroup.le_topologicalClosure _ (pow_mem hgen m)

/-! ### §6.3 The `M`-branch image contains the principal units at level `α` -/

/-- **The image identification, `M` branch.**  Every unit `≡ 1 mod 2^α` is a character value
whenever the character has the `M` image: `mUnit α` has exact level `α`, so it topologically
generates `1 + 2^αℤ₂`, which is therefore inside `imChiM α`.  This discharges the named
hypothesis of `evenRow_deepSupply_of_deepUnits`. -/
theorem principalUnits_le_imChiM {α : ℕ} (hα : 2 ≤ α) {ξ : ℤ_[2]ˣ}
    (hξ : (2 : ℤ_[2]) ^ α ∣ ((ξ : ℤ_[2])) - 1) : ξ ∈ imChiM α := by
  obtain ⟨c, hc⟩ := pivot_exists_zpowZtwo_eq (mUnit α) (mUnit α) α hα
    (mUnit_sub_one (by omega)) hξ
  have hmem := mem_topologicalClosure_of_zpowZtwo (mUnit α) c
  rw [hc] at hmem
  exact Subgroup.topologicalClosure_mono
    (Subgroup.closure_mono (by simp : ({mUnit α} : Set ℤ_[2]ˣ) ⊆ {-1, mUnit α})) hmem

/-! ### §6.4 The discharge, and the `α = 2` verdict -/

section Branch

variable {n : ℕ} {v : Fin n → ℤ_[2]ˣ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- Every unit `≡ 1 mod 2^α` is a character value on the `M` branch. -/
theorem evenRow_deepUnits_mem_range_of_imChiM {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (z : ℤ_[2]ˣ)
    (hz : PadicInt.toZModPow α (z : ℤ_[2]) = 1) : z ∈ Set.range chi := by
  rw [← map_one (PadicInt.toZModPow (p := 2) α), deep_toZModPow_eq_iff_dvd] at hz
  exact evenRow_mem_range_of_mem_of_range_eq hrange (principalUnits_le_imChiM hα hz)

/-- **Sufficiency, discharged on the `M` branch.**  For `α ≥ 3` and a character with the `M`
image, the depth-`(α - 1)` supply *holds* — no hypothesis remains.  Together with
`evenSharp_not_imageRelLe_imChiM`, which rules out every smaller depth, this pins the even
`M` seam exactly at `s = α - 1`. -/
theorem evenRow_deepSupply_imChiM {α : ℕ} (hα : 3 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α)
    (hv : ∀ i, v i ∈ Set.range chi) :
    EvenRowDeepFibreLiftSupply (α - 1) v G chi :=
  evenRow_deepSupply_of_deepUnits hα
    (evenRow_deepUnits_mem_range_of_imChiM (by omega) hrange) hv

/-- Every `2`-adic unit is `≡ ±1 mod 4`: `u - 1 = 2t`, and `t` is either even (then
`4 ∣ u - 1`) or a unit (then `2 ∣ t - 1`, hence `2 ∣ t + 1` and `4 ∣ u + 1`). -/
theorem evenSharp_pmOne_two (u : ℤ_[2]ˣ) : EvenSharpPmOne 2 u := by
  obtain ⟨t, ht⟩ := GQ2.two_dvd_val_sub_one u
  by_cases h2 : (2 : ℤ_[2]) ∣ t
  · obtain ⟨e, he⟩ := h2
    exact Or.inl ⟨e, by rw [ht, he]; ring⟩
  · obtain ⟨e, he⟩ := GQ2.two_dvd_sub_one_of_isUnit (GQ2.isUnit_of_not_two_dvd h2)
    refine Or.inr ⟨e + 1, ?_⟩
    have hu : ((u : ℤ_[2]) + 1) = ((u : ℤ_[2]) - 1) + 2 := by ring
    rw [hu, ht]
    linear_combination 2 * he

/-- **The `M` image is everything at `α = 2`.**  `mUnit 2` has exact level `2`, so it
generates `1 + 4ℤ₂`, and `-1 ∈ imChiM 2` supplies the other coset: every unit is `±` a unit
`≡ 1 mod 4`. -/
theorem imChiM_two_eq_top : imChiM 2 = ⊤ := by
  refine Subgroup.eq_top_iff' _ |>.mpr fun u ↦ ?_
  rcases evenSharp_pmOne_two u with h | h
  · exact principalUnits_le_imChiM (le_refl 2) h
  · have hneg : (2 : ℤ_[2]) ^ 2 ∣ ((-u : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      obtain ⟨e, he⟩ := h
      refine ⟨-e, ?_⟩
      rw [Units.val_neg]
      linear_combination -he
    have h1 : (-u : ℤ_[2]ˣ) ∈ imChiM 2 := principalUnits_le_imChiM (le_refl 2) hneg
    have h2 : ((-1 : ℤ_[2]ˣ) * (-u : ℤ_[2]ˣ)) ∈ imChiM 2 :=
      mul_mem (GQ2.Dyadic.MarkedCore.neg_one_mem_imChiM 2) h1
    simpa using h2

/-- **The `α = 2` verdict on the `M` branch: the committed seam holds outright.**  At `α = 2`
the `M` image is the whole unit group, so the character is surjective there and the committed
`RowExactLevelFibreLiftSupply` — the very statement refuted for `α ≥ 3` — is true, for every
row table, with no membership hypothesis at all.  The `α = 2` escape is therefore real, and
`α ≥ 3` is exactly the regime that needs the deep seam. -/
theorem evenRow_rowSupply_imChiM_two
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM 2) (v : Fin n → ℤ_[2]ˣ) :
    RowExactLevelFibreLiftSupply v G chi :=
  evenRow_rowSupply_of_surjective v
    (MonoidHom.range_eq_top.mp (by rw [hrange, imChiM_two_eq_top]))

end Branch

end ImageIdentification

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
#print axioms GQ2.Dyadic.EvenRowSupply.evenDeep_exists_pow_root
#print axioms GQ2.Dyadic.EvenRowSupply.evenRow_deepSupply_of_deepUnits
#print axioms GQ2.Dyadic.EvenRowSupply.pivot_exists_nat_pow_sub_dvd
#print axioms GQ2.Dyadic.EvenRowSupply.pivot_exists_zpowZtwo_eq
#print axioms GQ2.Dyadic.EvenRowSupply.mem_topologicalClosure_of_zpowZtwo
#print axioms GQ2.Dyadic.EvenRowSupply.principalUnits_le_imChiM
#print axioms GQ2.Dyadic.EvenRowSupply.evenRow_deepUnits_mem_range_of_imChiM
#print axioms GQ2.Dyadic.EvenRowSupply.evenRow_deepSupply_imChiM
#print axioms GQ2.Dyadic.EvenRowSupply.evenSharp_pmOne_two
#print axioms GQ2.Dyadic.EvenRowSupply.imChiM_two_eq_top
#print axioms GQ2.Dyadic.EvenRowSupply.evenRow_rowSupply_imChiM_two
