/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenKernelAdapted
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpanStep

/-!
# W52-EV3FB §1: the even derivation-kernel criterion

Boundary one of the three that `StageAbstractionEvenKernelAdapted.lean` §3 isolates inside
`EvenClimbResidualSupply`, namely `EvenKernelDerivKerCriterion`: *a central class killed by
every functional of an even coordinate derivation family lies in the literal raw shift span*.
This is the even clone of the L template's
`GammaLSylowPreimageFieldLabuteKernelAdaptedSupply.lean` crux
`stageResidual_mem_rawShiftSpan_of_forall_derivKer`.

## What had to be built, and what did not

The crossed-derivation calculus itself needed no port.  `WL`, `IsChiShadowDeriv`, `derivKer`
and the four row/tail lemmas of `GammaLSylowPreimageFieldLabuteStageFunctionals.lean`
(`stageDeriv_commP_row_mem_derivKer`, `stageDeriv_diagonal_row_mem_derivKer`,
`stageDeriv_tail_mem_derivKer_of_even`, `stageDeriv_tail_not_mem_derivKer_of_odd`) are stated
for an arbitrary group, character and functional, and are consumed here verbatim.  What the
even lane had to supply is the *span input* on the field side, and that is §1 to §4 below.

The route is the L one, not model transport.  F1's `evenRawAugmentedSpan_all_dn` / `_all_dm`
are statements about the free presented cores, and the criterion is needed at
`maxProPQuotient 2 (GalK K)`; but F1 also delivered the *engine*
`evenRawAugmentedSpan_of_base_of_step`, which is polymorphic in the group, so the field-side
augmented span is obtained the way the L template obtains its own
(`stageResidual_zLayer_le_rawAugmentedSpan`): apply the engine to ambient lifts of the stage
generators.  Nothing crosses the model equivalence.

Two bookkeeping facts drive the whole file.

* **The two bases differ.**  F1's augmented span is stated at `evenRawMarkedBase x k`, the
  literal level classes of ambient generators; the criterion is stated at
  `fun i ↦ canonLift G k (T.generators i)`.  §1 picks ambient lifts for which the two agree on
  the nose, which is possible because `canonLift` is just some chosen preimage.
* **The family's own lifts are a third base.**  A family's `lifts` reduce to the generators at
  level `k`, not to their canonical lifts at level `k+1`, so they differ from the canonical
  base by coordinatewise central classes.  §5 shows the even shift word does not see that
  difference, which is the `sqCoreHandleDbarWord_central_base_shift` clone.

## Where the mod-`4` alignment is spent

Exactly once, in §5's `evenDeriv_coordinateShift_mem_derivKer`.  Five of the six even
coordinate rows are plain brackets `[p, base i]` at indices `i ≠ 1`, and take
`stageDeriv_commP_row_mem_derivKer` with `χ(base i) ≡ 1 (mod 4)`.  The sixth, coordinate `0`,
is `p² · [p, base 0] · [p, base 1]`, which is *not* of the diagonal shape for any single
letter; regrouping it as `p² · [p, base 0 · base 1]` by
`commP_mul_right_of_mem` puts it in the shape `stageDeriv_diagonal_row_mem_derivKer` wants,
with partner character `v 0 · v 1`.  That is the product-partner resolution recorded in
`StageAbstractionEvenKernelAdapted.lean` §1, and it is why the hypotheses of §5 are indexed by
`i ≠ 1` even though the square sits on coordinate `0`.

## Numbering

1. ambient lifts of the canonical base, and generation at every tower level;
2. the field-side augmented span at the canonical base;
3. the canonical tail span and the shift-times-tail decomposition;
4. squarefree normal form for the tail span;
5. every family functional kills the raw shift span;
6. the criterion, and its discharge of `EvenKernelDerivKerCriterion`.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.LSquare (IsChiShadowDeriv)

/-! ## §1 Ambient lifts of the canonical base

The clone of the L template's `exists_stageResidualAmbientLift` and its generation lemma
(`GammaLSylowPreimageFieldLabuteVariableStage.lean` lines 44 to 137, all private there, hence
re-derived rather than imported).  Downwards, generation passes along the surjective tower
maps; upwards, the step kernel is central and therefore Frattini, which is
`eq_top_of_map_levelProj_eq_top`. -/

section Lifts

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h : ℕ}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Generation descends the tower: the level-`m` classes generate as soon as the level-`m+d`
classes do. -/
private theorem evenDeriv_levelMk_generates_down
    (x : Fin (MarkedCore.coreRank h) → G) (m : ℕ) :
    ∀ d : ℕ,
      Subgroup.closure (Set.range fun i ↦ levelMk G (m + d) (x i)) = ⊤ →
        Subgroup.closure (Set.range fun i ↦ levelMk G m (x i)) = ⊤
  | 0, H => H
  | d + 1, H => by
      apply evenDeriv_levelMk_generates_down x m d
      have hproj := closure_range_levelProj
        (T := fun i ↦ levelMk G (m + d + 1) (x i)) H
      simpa only [levelProj_levelMk] using hproj

/-- Generation climbs the tower: the step kernel `Z_m` lies in the Frattini-like subgroup, so
generation at level `m ≥ 2` propagates to every higher level. -/
private theorem evenDeriv_levelMk_generates_up
    (x : Fin (MarkedCore.coreRank h) → G)
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
      exact evenDeriv_levelMk_generates_up x hfg hpro m hm H d

/-- **Generation at one level `k ≥ 2` gives generation at every level.**  This is the input
F1's augmented-span engine asks for, in the form the engine consumes it. -/
theorem evenDeriv_levelMk_generates
    (x : Fin (MarkedCore.coreRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (k : ℕ) (hk : 2 ≤ k)
    (H : Subgroup.closure (Set.range fun i ↦ levelMk G k (x i)) = ⊤) (m : ℕ) :
    Subgroup.closure (Set.range fun i ↦ levelMk G m (x i)) = ⊤ := by
  rcases le_total m k with hle | hle
  · exact evenDeriv_levelMk_generates_down x m (k - m)
      (by rw [show m + (k - m) = k by omega]; exact H)
  · have hup := evenDeriv_levelMk_generates_up x hfg hpro k hk H (m - k)
    rwa [show k + (m - k) = m by omega] at hup

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **Ambient representatives of the canonical base.**  Their level-`k+1` classes are the
chosen canonical lifts on the nose, and their level-`k` classes are the marking. -/
theorem evenDeriv_exists_ambientLift {k : ℕ}
    (T : Fin (MarkedCore.coreRank h) → levelQuot G k) :
    ∃ x : Fin (MarkedCore.coreRank h) → G,
      (∀ i, levelMk G (k + 1) (x i) = canonLift G k (T i)) ∧
      ∀ i, levelMk G k (x i) = T i := by
  choose x hx using fun i ↦ levelMk_surjective G (k + 1) (canonLift G k (T i))
  refine ⟨x, hx, fun i ↦ ?_⟩
  have hproj := congrArg (GQ2.Roe.Labute.levelProj G k) (hx i)
  rwa [levelProj_levelMk, levelProj_canonLift] at hproj

end Lifts

/-! ## §2 The field-side augmented span at the canonical base

F1's engine, applied at an arbitrary topologically finitely generated pro-`2` group.  The
statement is at the canonical base because §1 arranges `evenRawMarkedBase x k` to be exactly
that function; the L template does the same at
`GammaLSylowPreimageFieldLabuteVariableStage.lean:143`. -/

section AugmentedSpan

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h k : ℕ}

/-- **The even augmented span theorem at any pro-`2` carrier.**  For ambient lifts of a
marking that generates one level, every central layer from degree three on is contained in the
span of the literal even shifts together with the non-twisted tails. -/
theorem evenDeriv_zLayer_le_augmentedSpan
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {x : Fin (MarkedCore.coreRank h) → G}
    {T : Fin (MarkedCore.coreRank h) → levelQuot G k}
    (hx : ∀ i, levelMk G k (x i) = T i) (hkk : 2 ≤ k)
    (htop : Subgroup.closure (Set.range T) = ⊤) (m : ℕ) (hm : 3 ≤ m) :
    zLayer G m ≤ evenRawAugmentedSpan x m hm := by
  have Hk : Subgroup.closure (Set.range fun i ↦ levelMk G k (x i)) = ⊤ := by
    rw [show (fun i ↦ levelMk G k (x i)) = T from funext hx]
    exact htop
  have hgen : ∀ j : ℕ, Subgroup.closure
      (Set.range (evenRawMarkedBase x j)) = ⊤ := fun j ↦
    evenDeriv_levelMk_generates x hfg hpro k hkk Hk (j + 1)
  refine evenRawAugmentedSpan_of_base_of_step x hfg hpro (fun j _ ↦ hgen (j + 1)) ?_ m hm
  exact evenRawAugmentedSpanBaseSupply_of_generates x hfg hpro (hgen 3)

end AugmentedSpan

/-! ## §3 The canonical tail span, and the shift-times-tail decomposition

The clone of `stageResidualTailSpan` and `stageResidual_exists_shift_mul_tail`
(`GammaLSylowPreimageFieldLabuteVariableStage.lean` lines 162 and 232).  The tail atoms are
the `2^(k-1)`-th powers of the canonical base at every index *except* `1`: F1's
`evenRawTailAtomSet` omits `1`, not the L template's `2`, and §5 shows that is also the set on
which the mod-`4` hypothesis of the tail dichotomy is available. -/

section TailSpan

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

/-- **The canonical tail span of a marking.**  The `2h + 3` non-twisted tails, phrased through
the canonical lift; these are the exact difference between the augmented span and the literal
even shift span. -/
def evenDerivTailSpan (T : Fin (MarkedCore.coreRank h) → levelQuot G k) :
    Subgroup (levelQuot G (k + 1)) :=
  Subgroup.closure
    {z | ∃ i : Fin (MarkedCore.coreRank h), i ≠ 1 ∧ z = canonLift G k (T i) ^ 2 ^ (k - 1)}

/-- For ambient lifts matching the canonical base, F1's abstract tail span is the canonical
tail span. -/
theorem evenDeriv_rawTailSpan_eq {x : Fin (MarkedCore.coreRank h) → G}
    {T : Fin (MarkedCore.coreRank h) → levelQuot G k}
    (hx1 : ∀ i, levelMk G (k + 1) (x i) = canonLift G k (T i)) :
    evenRawTailSpan x k = evenDerivTailSpan T := by
  refine congrArg Subgroup.closure ?_
  ext z
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, congrArg (fun t ↦ t ^ 2 ^ (k - 1)) (hx1 i)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (congrArg (fun t ↦ t ^ 2 ^ (k - 1)) (hx1 i)).symm⟩

/-- The tails are central: each lies in the involutive graded layer. -/
theorem evenDerivTailSpan_le_zLayer (T : Fin (MarkedCore.coreRank h) → levelQuot G k)
    (hk : 1 ≤ k) : evenDerivTailSpan T ≤ zLayer G k := by
  rw [evenDerivTailSpan, Subgroup.closure_le]
  rintro z ⟨i, _, rfl⟩
  have hmem := pow_two_pow_mem_lambdaImage (canonLift G k (T i)) (k - 1)
  rwa [show 1 + (k - 1) = k by omega] at hmem

/-- Elements of a join with a central second factor decompose as literal products.  The clone
of the L template's private `stageResidual_mem_mul_of_mem_sup_of_le_center`. -/
private theorem evenDeriv_mem_mul_of_mem_sup_of_le_center
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
        have hcomm := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hB hb)) a⁻¹
        rw [mul_inv_rev]
        exact hcomm.symm }
  have hA : A ≤ S := fun a ha ↦ ⟨a, ha, 1, B.one_mem, by group⟩
  have hBle : B ≤ S := fun b hb ↦ ⟨1, A.one_mem, b, hb, by group⟩
  exact sup_le hA hBle hz

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **Every central class is a literal even shift times a tail word.**  The tail factor is the
only obstruction between the augmented span, a theorem by §2, and the literal raw shift span
that the derivation family cuts out. -/
theorem evenDeriv_exists_shift_mul_tail
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {T : Fin (MarkedCore.coreRank h) → levelQuot G k}
    (htop : Subgroup.closure (Set.range T) = ⊤) (hk : 3 ≤ k)
    {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) :
    ∃ V : EvenRawDepthCorrection G h k, ∃ t ∈ evenDerivTailSpan T,
      z = evenRawDbarWord (fun i ↦ canonLift G k (T i)) V.correction * t := by
  obtain ⟨x, hx1, hx0⟩ := evenDeriv_exists_ambientLift T
  have hbase : evenRawMarkedBase x k = fun i ↦ canonLift G k (T i) := funext hx1
  have hsup := evenDeriv_zLayer_le_augmentedSpan hfg hpro hx0 (by omega) htop k hk hz
  rw [evenRawAugmentedSpan, hbase, evenDeriv_rawTailSpan_eq hx1] at hsup
  obtain ⟨a, ha, t, ht, rfl⟩ := evenDeriv_mem_mul_of_mem_sup_of_le_center
    (le_trans (evenDerivTailSpan_le_zLayer T (by omega)) (zLayer_le_center G k)) hsup
  obtain ⟨q, ⟨V, hV⟩, hqa⟩ := ha
  exact ⟨V, t, ht, by rw [← hqa, ← hV]; rfl⟩

end TailSpan
