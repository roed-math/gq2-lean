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

/-! ## §3 The neutral action, and the torsor property

The clone of `SharpAdmissibleCorrection.mulNeutral` / `.differenceNeutral` /
`.mulNeutral_difference_correction` (L template, lines 978-1068).  The content is that the
depth-`s` admissible corrections of a fixed tuple form a torsor under the depth-`s` neutral
corrections: rows are a character condition, and the character is a homomorphism. -/

section Action

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
variable {T : Tuple W v G chi k}

/-- **Translating a deep admissible correction by a neutral one.**  Rows survive because the
neutral coordinate contributes the character value `1` to `s` fresh digits. -/
def evenSharpMulNeutral (Wc : DeepSharpAdmissibleCorrection s T)
    (N : EvenSharpNeutralCorrection s G chi h k) : DeepSharpAdmissibleCorrection s T where
  correction i := Wc.correction i * N.correction i
  depth i := Subgroup.mul_mem _ (Wc.depth i) (N.depth i)
  rows i := by
    obtain ⟨g, hmod, hcong⟩ := Wc.rows i
    obtain ⟨g', hn, hnchi⟩ := N.neutral i
    simp only [stageModified] at hmod ⊢
    refine ⟨g * g', ?_, ?_⟩
    · rw [← mul_assoc, hmod, hn, map_mul]
    · simp only [map_mul, hnchi, mul_one]
      exact hcong

@[simp] theorem evenSharpMulNeutral_correction (Wc : DeepSharpAdmissibleCorrection s T)
    (N : EvenSharpNeutralCorrection s G chi h k) (i : Fin (MarkedCore.coreRank h)) :
    (evenSharpMulNeutral Wc N).correction i = Wc.correction i * N.correction i := rfl

/-- **Two deep admissible corrections differ by a neutral one.**  The character values of the
two modified rows agree to `s` fresh digits with the same table value, so their ratio is
trivial there. -/
def evenSharpDifferenceNeutral (Wc Wc' : DeepSharpAdmissibleCorrection s T) :
    EvenSharpNeutralCorrection s G chi h k where
  correction i := (Wc.correction i)⁻¹ * Wc'.correction i
  depth i := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Wc.depth i)) (Wc'.depth i)
  neutral i := by
    obtain ⟨g, hmod, hcong⟩ := Wc.rows i
    obtain ⟨g', hmod', hcong'⟩ := Wc'.rows i
    simp only [stageModified] at hmod hmod'
    refine ⟨g⁻¹ * g', ?_, ?_⟩
    · rw [map_mul, map_inv, ← hmod, ← hmod']
      group
    · simp only [map_mul, map_inv, hcong, hcong']
      exact inv_mul_cancel _

@[simp] theorem evenSharpDifferenceNeutral_correction
    (Wc Wc' : DeepSharpAdmissibleCorrection s T) (i : Fin (MarkedCore.coreRank h)) :
    (evenSharpDifferenceNeutral Wc Wc').correction i =
      (Wc.correction i)⁻¹ * Wc'.correction i := rfl

/-- **The torsor identity.**  Translating by the difference lands on the target. -/
theorem evenSharpMulNeutral_difference_correction (Wc Wc' : DeepSharpAdmissibleCorrection s T)
    (i : Fin (MarkedCore.coreRank h)) :
    (evenSharpMulNeutral Wc (evenSharpDifferenceNeutral Wc Wc')).correction i =
      Wc'.correction i :=
  mul_inv_cancel_left _ _

end Action

/-! ## §4 Existence of deep admissible corrections

The clone of `admissibleCorrection_nonempty` / `sharpAdmissibleCorrection_nonempty` (L
template, lines 454 and 507).  The even proof is shorter than the L one and needs no character
input at all: a stage tuple's rows are *exact* fibres already at level `k`, so the correction
carrying the canonical lift onto an exact representative works at every depth `s`
simultaneously.  Only the depth bookkeeping is new, and it is `zLayer G k ≤ λ_{k-1}`. -/

section Existence

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- The central layer sits inside the modification space, because the two-central tower is
antitone.  This is the only depth bookkeeping §4 needs. -/
theorem evenSharpZLayer_le_lambdaImage (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (k : ℕ) : zLayer G k ≤ lambdaImage G (k - 1) (k + 1) := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, twoCentralSeries_antitone G (by omega : k - 1 ≤ k) hg, rfl⟩

/-- **Deep admissible corrections always exist**, at every depth `s` at once.  Take the
correction moving the canonical lift of each row onto an exact representative of that row's
table value; it has depth `k-1` because the two lifts agree one level down. -/
theorem evenSharpDeepAdmissible_nonempty (s : ℕ) (T : Tuple W v G chi k) :
    Nonempty (DeepSharpAdmissibleCorrection s T) := by
  classical
  choose x hxchi hx using T.rows
  refine ⟨⟨fun i ↦ (canonLift G k (T.generators i))⁻¹ * levelMk G (k + 1) (x i), ?_, ?_⟩⟩
  · intro i
    refine evenSharpZLayer_le_lambdaImage G k ?_
    rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, map_mul, map_inv, levelProj_canonLift,
      levelProj_levelMk, ← hx i, inv_mul_cancel]
  · intro i
    refine ⟨x i, ?_, by rw [hxchi i]⟩
    simp only [stageModified]
    exact mul_inv_cancel_left _ _

end Existence

/-! ## §5 The shift supply: the board's crux (i), once for both even relators

The L template's `stageShift_zero_eq_dbarWordR2` identifies the exact relator shift of a
depth-`k-1` correction with the literal crossed-derivation word.  Its even analogue is F1's
`evenRawStageShift_n` / `evenRawStageShift_m`, and by the seam note §3(a) **the two even
relators produce the same word** `evenRawDbarWord` once `2 ≤ α`: the `N` first letter has
exponent `2 + 2^α` and the `M` first letter exponent `2`, and both contribute `p² · [p, -]`
because `binom (2 + 2^α) 2` is odd and `p^(2 + 2^α) = p²`, while the `M` third letter has
exponent `2^α` and contributes nothing.

So the crux is packaged here as a single `Prop` about a word datum, and each even branch
discharges it in one line.  This is the "one comparison serving `N` and `M`" the seam note
promised; nothing downstream ever needs to know which branch it is on. -/

section ShiftSupply

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **The crossed-derivation comparison, as an interface.**  A word datum satisfies this when
its exact relator shift along a depth-`k-1` correction is the even literal shift word. -/
def EvenSharpDbarShiftSupply {h : ℕ} (W : StageWord (MarkedCore.coreRank h)) (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : ℕ) : Prop :=
  ∀ base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1),
    (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) →
      stageShift W base correction = evenRawDbarWord base correction

/-- **Crux (i) on the `N` branch.** -/
theorem evenSharpDbarShiftSupply_n {α h k : ℕ} (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (hk : 3 ≤ k) :
    EvenSharpDbarShiftSupply (nStageWord α h hα₁) G k :=
  fun base correction hdepth ↦ evenRawStageShift_n hα hα₁ h k hk base correction hdepth

/-- **Crux (i) on the `M` branch**, the same comparison against the same word. -/
theorem evenSharpDbarShiftSupply_m {α h k : ℕ} (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (hk : 3 ≤ k) :
    EvenSharpDbarShiftSupply (mStageWord α h hα₁) G k :=
  fun base correction hdepth ↦ evenRawStageShift_m hα hα₁ h k hk base correction hdepth

end ShiftSupply

/-! ## §6 The actual-defect supply

The clone of `CoreHandleSharpActualDefectSupply` (L template, line 1070) and of its
`toDefectReachable` (line 1253).  As in the template the hit condition is stated against the
*literal* word, so the structure is independent of which even relator is in play; §5 converts
it to a statement about `stageShift` exactly once.

The passage to the committed `Tuple.DefectReachable` is the corrected seam: where the L
template invokes `SharpExactLevelFibreLiftSupply` (false in even degree), we invoke
`deep_defectReachable_of_kills` against `EvenRowDeepFibreLiftSupply s`, which the even row
lane supplies at `s = α - 1` on both branches. -/

section ActualDefect

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **A depth-`s` correction that literally hits the inverse defect.**  The even analogue of
the L template's core-plus-handle actual-defect supply. -/
structure EvenSharpActualDefectSupply (s : ℕ) (T : Tuple W v G chi k) where
  /-- The underlying depth-`s` admissible correction. -/
  correction : DeepSharpAdmissibleCorrection s T
  /-- Its literal even shift word inverts the current defect. -/
  hitsDefect : evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) correction.correction =
    (stageDefect W G k T.generators)⁻¹

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The endpoint of the character-refined half.**  An actual-defect supply at depth `s`,
together with the crossed-derivation comparison and the depth-`s` row supply, gives the
committed `Tuple.DefectReachable`. -/
theorem EvenSharpActualDefectSupply.toDefectReachable {T : Tuple W v G chi k}
    (S : EvenSharpActualDefectSupply s T) (hk : 1 ≤ k)
    (Hshift : EvenSharpDbarShiftSupply W G k)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) :
    Tuple.DefectReachable T :=
  deep_defectReachable_of_kills Hlift hk S.correction
    (by rw [Hshift _ _ S.correction.depth]; exact S.hitsDefect)

end ActualDefect

/-! ## §7 The residual element and the reachability criterion

The clone of `sharpNeutralResidualElement`, `SharpNeutralResidualReachable` and
`nonempty_coreHandleSharpActualDefectSupply_iff_neutralResidual` (L template, lines 1082-1229).

Fix any depth-`s` correction (§4 says one exists).  Its literal shift misses the inverse
defect by a definite element of the central layer, the *residual*; and because the corrections
form a torsor under the neutral ones (§3) while the literal shift word is a homomorphism on
depth corrections (F1's `evenRawDbarWord_mul`), an actual-defect supply exists precisely when
that residual is a literal shift of a *neutral* correction.  This is the statement the bracket
span of §B identifies with a membership. -/

section Residual

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
variable {T : Tuple W v G chi k}

/-- **The residual of a depth-`s` correction**: the element a neutral correction must produce
in order to repair it into an actual-defect supply. -/
def evenSharpNeutralResidualElement (Wc : DeepSharpAdmissibleCorrection s T) :
    levelQuot G (k + 1) :=
  (evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) Wc.correction)⁻¹ *
    (stageDefect W G k T.generators)⁻¹

/-- The residual is reachable when some neutral correction has it as its literal shift. -/
def EvenSharpNeutralResidualReachable (Wc : DeepSharpAdmissibleCorrection s T) : Prop :=
  ∃ N : EvenSharpNeutralCorrection s G chi h k,
    evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) N.correction =
      evenSharpNeutralResidualElement Wc

/-- **The criterion.**  Repairing a fixed depth-`s` correction into an actual-defect supply is
possible exactly when its residual is a neutral literal shift.  The choice of `Wc` is
immaterial: both directions are proved by the torsor identity of §3. -/
theorem nonempty_evenSharpActualDefectSupply_iff_residual (hk : 3 ≤ k)
    (Wc : DeepSharpAdmissibleCorrection s T) :
    Nonempty (EvenSharpActualDefectSupply s T) ↔ EvenSharpNeutralResidualReachable Wc := by
  constructor
  · rintro ⟨S⟩
    refine ⟨evenSharpDifferenceNeutral Wc S.correction, ?_⟩
    have hmul := evenRawDbarWord_mul h k hk (fun i ↦ canonLift G k (T.generators i))
      Wc.depth (evenSharpDifferenceNeutral Wc S.correction).depth
    have hfun : (fun i ↦ Wc.correction i *
        (evenSharpDifferenceNeutral Wc S.correction).correction i) =
        S.correction.correction :=
      funext fun i ↦ evenSharpMulNeutral_difference_correction Wc S.correction i
    rw [hfun] at hmul
    rw [evenSharpNeutralResidualElement, ← S.hitsDefect, hmul]
    group
  · rintro ⟨N, hN⟩
    refine ⟨⟨evenSharpMulNeutral Wc N, ?_⟩⟩
    have hmul := evenRawDbarWord_mul h k hk (fun i ↦ canonLift G k (T.generators i))
      Wc.depth N.depth
    show evenRawDbarWord _ (fun i ↦ Wc.correction i * N.correction i) = _
    rw [hmul, hN, evenSharpNeutralResidualElement]
    group

end Residual

end

end GQ2.Dyadic.StageGeneric

/-! ## §8 Axiom pins

Every public declaration of this file, printed.  All are expected at std-3,
`[propext, Classical.choice, Quot.sound]`, which is what the corresponding L template file
`GammaLSylowPreimageFieldLabuteStageHandles.lean` prints on all twenty-six of its pins: this
file adds no arithmetic input, and the two seam-relative supplies
(`EvenRowDeepFibreLiftSupply`, `EvenSharpDbarShiftSupply`) are hypotheses, never discharged
here. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 the depth witness
#print axioms evenSharpDeepDefined

-- §2 the neutral corrections
#print axioms EvenSharpNeutralCorrection
#print axioms EvenSharpNeutralCorrection.ext
#print axioms EvenSharpNeutralCorrection.instGroup
#print axioms EvenSharpNeutralCorrection.toRaw
#print axioms EvenSharpNeutralCorrection.toRawHom
#print axioms EvenSharpNeutralCorrection.toDepthLe

-- §3 the neutral action
#print axioms evenSharpMulNeutral
#print axioms evenSharpDifferenceNeutral
#print axioms evenSharpMulNeutral_difference_correction

-- §4 existence
#print axioms evenSharpZLayer_le_lambdaImage
#print axioms evenSharpDeepAdmissible_nonempty

-- §5 the crossed-derivation comparison, crux (i)
#print axioms EvenSharpDbarShiftSupply
#print axioms evenSharpDbarShiftSupply_n
#print axioms evenSharpDbarShiftSupply_m

-- §6 the actual-defect supply
#print axioms EvenSharpActualDefectSupply
#print axioms EvenSharpActualDefectSupply.toDefectReachable

-- §7 the residual criterion
#print axioms evenSharpNeutralResidualElement
#print axioms EvenSharpNeutralResidualReachable
#print axioms nonempty_evenSharpActualDefectSupply_iff_residual

end AxiomPins
