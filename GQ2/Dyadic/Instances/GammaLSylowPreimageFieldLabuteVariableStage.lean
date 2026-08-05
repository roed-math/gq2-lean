/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteRawSpanStep
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageRegression

/-!
# The variable-rank augmented span at the field, and the exact tail frontier

The augmented-span theorem (`rawAugmentedSpan_of_base_of_step`) was previously instantiated
only at the free model `DSq h`.  This file instantiates it at the maximal pro-`2` quotient of
an arbitrary finite dyadic field, over ambient lifts of any stage tuple's generators: every
central layer from degree three on is spanned by the literal raw improved-word shifts together
with the `2h + 2` non-twisted tails (`stageResidual_zLayer_le_rawAugmentedSpan`).

Consequently the inverse actual defect — and the sharp neutral residual of every base point —
decomposes as a literal raw shift times an explicit tail word
(`stageResidual_defect_decomposition`, `stageResidual_residual_decomposition`), and raw
variable-rank Labute reachability is *equivalent* to raw-shift membership of that tail factor
(`stageResidual_sqRawDefectReachable_iff_tail_factor_mem`).  By the model refutation
(`sqCore_sigma_rawTail_not_mem_rawShiftSpan`) the tails themselves are genuinely outside the
raw shift span at the cubic layer, so the content of the remaining `SL1`-type obligation is
precisely that the *defect's* tail factor can be taken trivial — a statement about the
finitely many non-twisted tail classes of the current stage, not about the whole layer.

The `h = 0`, `K = ⊥` oracle is rechecked against every new interface: raw reachability holds
and the tail factor of the defect is literally trivial there.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Generation of every tower level from one marked level -/

/-- Push a generating marked level down the tower. -/
private theorem stageResidual_levelMk_generates_down
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h : ℕ} (x : Fin (SqCore.sqRank h) → G) (m : ℕ) :
    ∀ d : ℕ,
      Subgroup.closure (Set.range fun i ↦ levelMk G (m + d) (x i)) = ⊤ →
        Subgroup.closure (Set.range fun i ↦ levelMk G m (x i)) = ⊤
  | 0, H => H
  | d + 1, H => by
      apply stageResidual_levelMk_generates_down x m d
      have hproj := closure_range_levelProj
        (T := fun i ↦ levelMk G (m + d + 1) (x i)) H
      simpa only [levelProj_levelMk] using hproj

/-- Push a generating marked level up the tower; the kernel of each step is Frattini. -/
private theorem stageResidual_levelMk_generates_up
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h : ℕ} (x : Fin (SqCore.sqRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) (hm : 2 ≤ m)
    (H : Subgroup.closure (Set.range fun i ↦ levelMk G m (x i)) = ⊤) :
    ∀ d : ℕ,
      Subgroup.closure (Set.range fun i ↦ levelMk G (m + d) (x i)) = ⊤
  | 0 => H
  | d + 1 => by
      apply eq_top_of_map_levelProj_eq_top G hfg hpro (by omega : 2 ≤ m + d)
      rw [MonoidHom.map_closure]
      have himg : ⇑(levelProj G (m + d)) ''
          (Set.range fun i ↦ levelMk G (m + (d + 1)) (x i)) =
            Set.range fun i ↦ levelMk G (m + d) (x i) := by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun i ↦ levelProj_levelMk _ (m + d) (x i))
      rw [himg]
      exact stageResidual_levelMk_generates_up x hfg hpro m hm H d

/-- A tuple whose classes generate one level `k ≥ 2` has classes generating every level
`m ≥ 2`.  Downwards this is surjectivity of the tower maps; upwards the step kernel `Z_m` is
contained in the Frattini-like subgroup `λ₂`. -/
private theorem stageResidual_levelMk_generates
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h : ℕ} (x : Fin (SqCore.sqRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (k : ℕ) (hk : 2 ≤ k)
    (H : Subgroup.closure (Set.range fun i ↦ levelMk G k (x i)) = ⊤)
    (m : ℕ) :
    Subgroup.closure (Set.range fun i ↦ levelMk G m (x i)) = ⊤ := by
  rcases le_total m k with hle | hle
  · apply stageResidual_levelMk_generates_down x m (k - m)
    have hEq : m + (k - m) = k := by omega
    rw [hEq]
    exact H
  · have hup := stageResidual_levelMk_generates_up x hfg hpro k hk H (m - k)
    have hEq : k + (m - k) = m := by omega
    rwa [hEq] at hup

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Ambient representatives of the canonical stage base: their level-`k+1` classes are the
chosen `canonLift`s and their level-`k` classes are the tuple's generators. -/
theorem exists_stageResidualAmbientLift {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) :
    ∃ x : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K),
      (∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (x i) =
        canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) ∧
      ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (x i) = T.generators i := by
  choose x hx using fun i ↦
    levelMk_surjective (maxProPQuotient 2 (GalK K)) (k + 1)
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
  refine ⟨x, hx, fun i ↦ ?_⟩
  have hproj := congrArg
    (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k) (hx i)
  rwa [levelProj_levelMk, levelProj_canonLift] at hproj

/-- Ambient lifts of a stage tuple's generators generate every finite tower level. -/
theorem stageResidual_ambientLift_generates {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    {x : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)}
    (hx : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (x i) = T.generators i)
    (hk : 2 ≤ k) (m : ℕ) :
    Subgroup.closure
      (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) m (x i)) = ⊤ := by
  have Hk : Subgroup.closure
      (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) k (x i)) = ⊤ := by
    have hfun : (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) k (x i)) =
        T.generators := funext hx
    rw [hfun]
    exact T.topGen
  exact stageResidual_levelMk_generates x
    (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient k hk Hk m

/-- **The variable-rank augmented span at the field.**  For ambient lifts of any stage
tuple's generators, every central layer of the maximal pro-`2` quotient from degree three on
is contained in the span of the literal raw improved-word shifts and the non-twisted tails.
This ports `sqCore_rawAugmentedSpan_all` from the free model to the arithmetic group. -/
theorem stageResidual_zLayer_le_rawAugmentedSpan {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    {x : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)}
    (hx : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (x i) = T.generators i)
    (hk : 2 ≤ k) (m : ℕ) (hm : 3 ≤ m) :
    zLayer (maxProPQuotient 2 (GalK K)) m ≤ rawAugmentedSpan x m hm := by
  apply rawAugmentedSpan_of_base_of_step x
    (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient
  · intro m' _
    exact stageResidual_ambientLift_generates T hx hk (m' + 2)
  · apply rawAugmentedSpanBaseSupply_of_generates x
      (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient
    exact stageResidual_ambientLift_generates T hx hk 4

/-! ## The canonical tail span of a stage -/

/-- The relator-adapted non-twisted tails of a stage, phrased through the canonical lift.
These `2h + 2` classes are the exact difference between the augmented span and the literal
raw shift span. -/
noncomputable def stageResidualTailSpan {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) :
    Subgroup (levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :=
  Subgroup.closure
    {z | ∃ i : Fin (SqCore.sqRank h), i ≠ 2 ∧
      z = canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) ^ 2 ^ (k - 1)}

/-- For ambient lifts matching the canonical base, the abstract tail span is the stage's
canonical tail span. -/
theorem stageResidual_rawTailSpan_eq {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    {x : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)}
    (hx1 : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (x i) =
      canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) :
    rawTailSpan x k = stageResidualTailSpan T := by
  have hset : rawTailAtomSet x k =
      {z | ∃ i : Fin (SqCore.sqRank h), i ≠ 2 ∧
        z = canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) ^ 2 ^ (k - 1)} := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, congrArg (fun t ↦ t ^ 2 ^ (k - 1)) (hx1 i)⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, (congrArg (fun t ↦ t ^ 2 ^ (k - 1)) (hx1 i)).symm⟩
  unfold rawTailSpan stageResidualTailSpan
  exact congrArg Subgroup.closure hset

/-- The tails are central: each lies in the involutive graded layer. -/
theorem stageResidualTailSpan_le_zLayer {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 1 ≤ k) :
    stageResidualTailSpan T ≤ zLayer (maxProPQuotient 2 (GalK K)) k := by
  unfold stageResidualTailSpan
  rw [Subgroup.closure_le]
  rintro z ⟨i, hi, rfl⟩
  have hmem := pow_two_pow_mem_lambdaImage
    (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) (k - 1)
  rwa [show 1 + (k - 1) = k by omega] at hmem

/-- Elements of a join with a central second factor decompose as literal products. -/
private theorem stageResidual_mem_mul_of_mem_sup_of_le_center
    {H : Type*} [Group H] {A B : Subgroup H}
    (hB : B ≤ Subgroup.center H) {z : H} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  let S : Subgroup H :=
    { carrier := {w | ∃ a ∈ A, ∃ b ∈ B, w = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by group⟩
      mul_mem' := by
        rintro w w' ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have hcomm := Subgroup.mem_center_iff.mp (hB hb) a'
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hcomm]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro w ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hcomm := Subgroup.mem_center_iff.mp
          (Subgroup.inv_mem _ (hB hb)) a⁻¹
        rw [mul_inv_rev]
        exact hcomm.symm }
  have hA : A ≤ S := fun a ha ↦ ⟨a, ha, 1, B.one_mem, by group⟩
  have hBle : B ≤ S := fun b hb ↦ ⟨1, A.one_mem, b, hb, by group⟩
  exact sup_le hA hBle hz

/-! ## Shift-times-tail decomposition of central classes -/

/-- **Every central class is a literal raw shift times a tail word.**  In particular this
holds for the inverse actual defect and for every sharp neutral residual.  The tail factor is
the only obstruction between the augmented span (a theorem at the field, above) and the raw
reachability consumed by the stage induction. -/
theorem stageResidual_exists_shift_mul_tail {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    {z : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hz : z ∈ zLayer (maxProPQuotient 2 (GalK K)) k) :
    ∃ V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k,
      ∃ t ∈ stageResidualTailSpan T,
        z = sqCoreHandleDbarWord
            (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
            V.correction * t := by
  obtain ⟨x, hx1, hx0⟩ := exists_stageResidualAmbientLift T
  have hbase : rawMarkedBase x k =
      fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) := funext hx1
  have hsup := stageResidual_zLayer_le_rawAugmentedSpan T hx0 (by omega) k hk hz
  rw [rawAugmentedSpan, hbase, stageResidual_rawTailSpan_eq T hx1] at hsup
  obtain ⟨a, ha, t, ht, rfl⟩ := stageResidual_mem_mul_of_mem_sup_of_le_center
    (le_trans (stageResidualTailSpan_le_zLayer T (by omega))
      (zLayer_le_center (maxProPQuotient 2 (GalK K)) k)) hsup
  obtain ⟨q, ⟨V, hV⟩, hqa⟩ := ha
  refine ⟨V, t, ht, ?_⟩
  rw [← hqa, ← hV]
  rfl

/-- The inverse actual defect decomposes as a literal raw shift times a tail word. -/
theorem stageResidual_defect_decomposition {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) :
    ∃ V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k,
      ∃ t ∈ stageResidualTailSpan T,
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ =
          sqCoreHandleDbarWord
            (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
            V.correction * t :=
  stageResidual_exists_shift_mul_tail T hk
    (Subgroup.inv_mem _ (sqStageDefect_mem_zLayer h k T.relation))

/-! ## The exact frontier: raw reachability is tail-factor membership -/

/-- Raw variable-rank reachability is exactly raw-shift membership of any tail factor of the
inverse defect.  Together with the decomposition theorem this reduces the remaining `SL1`-type
obligation to the position of finitely many tail classes relative to the raw shift span. -/
theorem stageResidual_sqRawDefectReachable_iff_tail_factor_mem {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    {V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k}
    {t : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hdec : (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ =
      sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        V.correction * t) :
    sqRawDefectReachable (maxProPQuotient 2 (GalK K)) h k T.generators ↔
      t ∈ rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk := by
  have hshift : sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      V.correction ∈ rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk :=
    rawDepthShift_mem_rawShiftSpan
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk V
  rw [sqRawDefectReachable_iff_defect_mem_rawShiftSpan T hk, hdec]
  constructor
  · intro hmem
    have hcancel := Subgroup.mul_mem _ (Subgroup.inv_mem _ hshift) hmem
    simpa using hcancel
  · intro hmem
    exact Subgroup.mul_mem _ hshift hmem

/-- The sharp neutral residual of any base point detects raw reachability: it lies in the raw
shift span exactly when the current defect is raw-reachable.  This ties the residual studied
by the transgression chain to the raw span frontier. -/
theorem stageResidual_residual_mem_rawShiftSpan_iff {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) :
    (sharpNeutralResidualElement T hk W).1 ∈
        rawShiftSpan
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk ↔
      sqRawDefectReachable (maxProPQuotient 2 (GalK K)) h k T.generators := by
  have hW : sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      W.correction ∈ rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk :=
    rawDepthShift_mem_rawShiftSpan
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk
      ⟨W.correction, W.depth⟩
  have hres : (sharpNeutralResidualElement T hk W).1 =
      (sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        W.correction)⁻¹ *
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := rfl
  rw [sqRawDefectReachable_iff_defect_mem_rawShiftSpan T hk, hres]
  constructor
  · intro hmem
    have hcancel := Subgroup.mul_mem _ hW hmem
    simpa using hcancel
  · intro hmem
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hW) hmem

/-- The residual itself decomposes as a raw shift times a tail word, and raw reachability is
equivalent to raw-shift membership of that tail factor.  This is the exact remaining frontier
of the variable-rank `SL1` lane in one statement. -/
theorem stageResidual_residual_decomposition {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) :
    ∃ V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k,
      ∃ t ∈ stageResidualTailSpan T,
        (sharpNeutralResidualElement T hk W).1 =
            sqCoreHandleDbarWord
              (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
              V.correction * t ∧
          (sqRawDefectReachable (maxProPQuotient 2 (GalK K)) h k T.generators ↔
            t ∈ rawShiftSpan
              (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk) := by
  obtain ⟨V, t, ht, hdec⟩ := stageResidual_exists_shift_mul_tail T hk
    (sharpNeutralResidualElement T hk W).2
  refine ⟨V, t, ht, hdec, ?_⟩
  rw [← stageResidual_residual_mem_rawShiftSpan_iff T hk W, hdec]
  have hshift : sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      V.correction ∈ rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk :=
    rawDepthShift_mem_rawShiftSpan
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk V
  constructor
  · intro hmem
    have hcancel := Subgroup.mul_mem _ (Subgroup.inv_mem _ hshift) hmem
    simpa using hcancel
  · intro hmem
    exact Subgroup.mul_mem _ hshift hmem

/-- Raw reachability plus the finite character-match supply yield the primitive-residual
capstone premise.  With the decomposition above, the whole forward capstone is thereby
reduced to (i) triviality of one tail factor of the defect and (ii) the finite ∃-form sharp
character match. -/
theorem stageResidual_exists_primitiveVanishing_of_raw_of_characterMatch {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (Hmatch : RawDefectSharpCharacterMatchSupply T hk) :
    ∃ W : SharpAdmissibleCorrection T (by omega),
      SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg :=
  stageResidual_exists_primitiveVanishing_of_actualDefectSupply hfg
    (rawDefectSharpCharacterMatchSupply_iff_nonempty_actualDefectSupply.mp Hmatch)

end SqCyclotomicStageTuple

/-! ## Rank-one calibration of the new interfaces -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The bottom field satisfies the raw variable-rank reachability interface at every level. -/
theorem stageResidual_bot_sqRawDefectReachable (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) :
    SqCyclotomicStageTuple.sqRawDefectReachable
      (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) 0 k
      T.generators :=
  (sqCyclotomicStageTuple_bot_all_defectReachable k hk T).toRaw

/-- At the bottom field the tail factor of the inverse defect can be taken literally trivial:
the defect is itself a raw shift.  This pins the constant calibration of the decomposition
theorem against the rank-one oracle. -/
theorem stageResidual_bot_defect_trivial_tail (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) :
    ∃ V : RawDepthCorrection
        (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) 0 k,
      (sqStageDefect
          (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) 0 k
          T.generators)⁻¹ =
        sqCoreHandleDbarWord
          (fun i ↦ canonLift
            (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
            (T.generators i))
          V.correction := by
  obtain ⟨c, hd, hkill⟩ := stageResidual_bot_sqRawDefectReachable k hk T
  refine ⟨⟨c, hd⟩, ?_⟩
  rw [← hkill, stageShift_eq_dbarWordR2_mul_sqHandleDbarWord 0 k hk
    (fun i ↦ canonLift
      (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
      (T.generators i)) c hd]
  rfl

#print axioms SqCyclotomicStageTuple.exists_stageResidualAmbientLift
#print axioms SqCyclotomicStageTuple.stageResidual_ambientLift_generates
#print axioms SqCyclotomicStageTuple.stageResidual_zLayer_le_rawAugmentedSpan
#print axioms SqCyclotomicStageTuple.stageResidual_rawTailSpan_eq
#print axioms SqCyclotomicStageTuple.stageResidualTailSpan_le_zLayer
#print axioms SqCyclotomicStageTuple.stageResidual_exists_shift_mul_tail
#print axioms SqCyclotomicStageTuple.stageResidual_defect_decomposition
#print axioms SqCyclotomicStageTuple.stageResidual_sqRawDefectReachable_iff_tail_factor_mem
#print axioms SqCyclotomicStageTuple.stageResidual_residual_mem_rawShiftSpan_iff
#print axioms SqCyclotomicStageTuple.stageResidual_residual_decomposition
#print axioms SqCyclotomicStageTuple.stageResidual_exists_primitiveVanishing_of_raw_of_characterMatch
#print axioms stageResidual_bot_sqRawDefectReachable
#print axioms stageResidual_bot_defect_trivial_tail

end

end GQ2.Dyadic.LSquare
