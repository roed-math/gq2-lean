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

/-- The graded layer is abelian, which is what puts the tail span in squarefree normal form.
Kept local, exactly as the L template keeps `stageSupplyZLayerCommGroup` local. -/
local instance evenDerivZLayerCommGroup {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (k : ℕ) : CommGroup ↥(zLayer G k) :=
  { (inferInstance : Group ↥(zLayer G k)) with
    mul_comm := fun a b ↦ Subtype.ext (zLayer_commute a.2 b.1).eq }

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

/-! ## §4 Squarefree normal form for the canonical tail span

The clone of `stageResidualTailSpan_exists_finset_prod` (L template, line 275).  The tails are
central of exponent two, so the subgroup they generate is an elementary abelian group in which
every element is a *squarefree* finset product; the symmetric difference is what makes the
carrier of §4 a subgroup.  §6 then argues by emptiness of that finset. -/

section Squarefree

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

/-- A relator-adapted non-twisted tail, bundled in the graded layer. -/
def evenDerivTailLayer (T : Fin (MarkedCore.coreRank h) → levelQuot G k) (hk : 3 ≤ k)
    (i : {i : Fin (MarkedCore.coreRank h) // i ≠ 1}) : ↥(zLayer G k) :=
  ⟨canonLift G k (T i.1) ^ 2 ^ (k - 1), by
    have hmem := pow_two_pow_mem_lambdaImage (canonLift G k (T i.1)) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at hmem⟩

/-- In an involutive abelian group, a product of two finset products is the finset product
over the symmetric difference. -/
private theorem evenDeriv_prod_mul_prod_eq_prod_symmDiff
    {I H : Type*} [DecidableEq I] [CommGroup H]
    (f : I → H) (hsq : ∀ i, f i * f i = 1) (s t : Finset I) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) = ∏ i ∈ symmDiff s t, f i := by
  induction s using Finset.induction generalizing t with
  | empty => simp [Finset.symmDiff_def]
  | @insert a s ha ih =>
      by_cases hat : a ∈ t
      · let t' := t.erase a
        have hat' : a ∉ t' := by simp [t']
        have ht : insert a t' = t := Finset.insert_erase hat
        have hsd : symmDiff (insert a s) t = symmDiff s t' := by
          ext y
          simp only [Finset.mem_symmDiff, Finset.mem_insert]
          by_cases hya : y = a
          · subst y; simp [ha, hat, t']
          · simp [hya, t']
        calc
          (∏ i ∈ insert a s, f i) * (∏ i ∈ t, f i) =
              (f a * ∏ i ∈ s, f i) * (f a * ∏ i ∈ t', f i) := by
                rw [Finset.prod_insert ha, ← ht, Finset.prod_insert hat']
          _ = (f a * f a) * ((∏ i ∈ s, f i) * (∏ i ∈ t', f i)) := by ac_rfl
          _ = (∏ i ∈ s, f i) * (∏ i ∈ t', f i) := by rw [hsq, one_mul]
          _ = ∏ i ∈ symmDiff s t', f i := ih t'
          _ = ∏ i ∈ symmDiff (insert a s) t, f i := by rw [hsd]
      · have hnot : a ∉ symmDiff s t := by simp [Finset.mem_symmDiff, ha, hat]
        have hsd : symmDiff (insert a s) t = insert a (symmDiff s t) := by
          ext y
          simp only [Finset.mem_symmDiff, Finset.mem_insert]
          by_cases hya : y = a
          · subst y; simp [ha, hat]
          · simp [hya]
        calc
          (∏ i ∈ insert a s, f i) * (∏ i ∈ t, f i) =
              (f a * ∏ i ∈ s, f i) * (∏ i ∈ t, f i) := by rw [Finset.prod_insert ha]
          _ = f a * ((∏ i ∈ s, f i) * (∏ i ∈ t, f i)) := by rw [mul_assoc]
          _ = f a * ∏ i ∈ symmDiff s t, f i := by rw [ih t]
          _ = ∏ i ∈ insert a (symmDiff s t), f i := (Finset.prod_insert hnot).symm
          _ = ∏ i ∈ symmDiff (insert a s) t, f i := by rw [hsd]

private theorem evenDerivTailLayer_mul_self
    (T : Fin (MarkedCore.coreRank h) → levelQuot G k) (hk : 3 ≤ k)
    (i : {i : Fin (MarkedCore.coreRank h) // i ≠ 1}) :
    evenDerivTailLayer T hk i * evenDerivTailLayer T hk i = 1 := by
  apply Subtype.ext
  simpa [pow_two] using zLayer_sq G (evenDerivTailLayer T hk i).2

/-- **Every element of the canonical tail span is a squarefree finset product of tails.** -/
theorem evenDerivTailSpan_exists_finset_prod
    (T : Fin (MarkedCore.coreRank h) → levelQuot G k) (hk : 3 ≤ k)
    {t : levelQuot G (k + 1)} (ht : t ∈ evenDerivTailSpan T) :
    ∃ (hmem : t ∈ zLayer G k) (s : Finset {i : Fin (MarkedCore.coreRank h) // i ≠ 1}),
      (⟨t, hmem⟩ : ↥(zLayer G k)) = ∏ i ∈ s, evenDerivTailLayer T hk i := by
  classical
  have hmem : t ∈ zLayer G k := evenDerivTailSpan_le_zLayer T (by omega) ht
  refine ⟨hmem, ?_⟩
  let P : Subgroup ↥(zLayer G k) :=
    { carrier := {y | ∃ s : Finset {i : Fin (MarkedCore.coreRank h) // i ≠ 1},
          y = ∏ i ∈ s, evenDerivTailLayer T hk i}
      one_mem' := ⟨∅, by simp⟩
      mul_mem' := by
        rintro y y' ⟨s, rfl⟩ ⟨u, rfl⟩
        exact ⟨symmDiff s u, (evenDeriv_prod_mul_prod_eq_prod_symmDiff
          (evenDerivTailLayer T hk) (evenDerivTailLayer_mul_self T hk) s u).symm ▸ rfl⟩
      inv_mem' := by
        rintro y ⟨s, rfl⟩
        refine ⟨s, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [evenDeriv_prod_mul_prod_eq_prod_symmDiff
          (evenDerivTailLayer T hk) (evenDerivTailLayer_mul_self T hk) s s, symmDiff_self]
        simp }
  suffices hsuff : ∀ y, y ∈ evenDerivTailSpan T →
      y ∈ zLayer G k ∧ ∀ hy : y ∈ zLayer G k, (⟨y, hy⟩ : ↥(zLayer G k)) ∈ P by
    exact (hsuff t ht).2 hmem
  intro y hy
  refine Subgroup.closure_induction (p := fun w _ ↦
      w ∈ zLayer G k ∧ ∀ hw : w ∈ zLayer G k, (⟨w, hw⟩ : ↥(zLayer G k)) ∈ P)
    ?_ ?_ ?_ ?_ hy
  · rintro w ⟨i, hi, rfl⟩
    exact ⟨(evenDerivTailLayer T hk ⟨i, hi⟩).2, fun hw ↦ ⟨{⟨i, hi⟩}, by
      rw [Finset.prod_singleton]; exact Subtype.ext rfl⟩⟩
  · exact ⟨Subgroup.one_mem _, fun _ ↦ ⟨∅, Subtype.ext (by simp)⟩⟩
  · rintro a b _ _ ⟨haz, hap⟩ ⟨hbz, hbp⟩
    refine ⟨Subgroup.mul_mem _ haz hbz, fun hw ↦ ?_⟩
    rw [show (⟨a * b, hw⟩ : ↥(zLayer G k)) = (⟨a, haz⟩ : ↥(zLayer G k)) * ⟨b, hbz⟩ from
      Subtype.ext rfl]
    exact P.mul_mem (hap haz) (hbp hbz)
  · rintro a _ ⟨haz, hap⟩
    refine ⟨Subgroup.inv_mem _ haz, fun hw ↦ ?_⟩
    rw [show (⟨a⁻¹, hw⟩ : ↥(zLayer G k)) = (⟨a, haz⟩ : ↥(zLayer G k))⁻¹ from Subtype.ext rfl]
    exact P.inv_mem (hap haz)

end Squarefree

/-! ## §5 Every family functional kills the raw shift span

The clone of `stageDeriv_coordinateShift_mem_derivKer` and
`stageDeriv_rawShiftSpan_le_derivKer` (L template, `StageFunctionals.lean` lines 635 and 675),
together with the two base changes the even lane needs.  This is the only section that
consumes arithmetic about the value table, and it consumes exactly the two facts
`StageAbstractionEvenKernelAdapted.lean` §1 proves. -/

section SpanKill

open GQ2.Dyadic.LSquare (stageDeriv_commP_row_mem_derivKer stageDeriv_diagonal_row_mem_derivKer
  stageDeriv_tail_mem_derivKer_of_even stageDeriv_tail_not_mem_derivKer_of_odd)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

/-! ### §5.1 The four index disequalities the tail set needs

`evenIndex_cases` never needs them, because it can discharge the twisted branch by `rfl`.
The functional rows do need them, since the mod-`4` hypothesis is indexed by `i ≠ 1`. -/

private theorem evenDeriv_zero_ne_one : (0 : Fin (MarkedCore.coreRank h)) ≠ 1 := fun hcon ↦ by
  have hval := congrArg Fin.val hcon
  rw [MarkedCore.coreVal_zero, MarkedCore.coreVal_one] at hval
  omega

private theorem evenDeriv_two_ne_one : (2 : Fin (MarkedCore.coreRank h)) ≠ 1 := fun hcon ↦ by
  have hval := congrArg Fin.val hcon
  rw [MarkedCore.coreVal_two, MarkedCore.coreVal_one] at hval
  omega

private theorem evenDeriv_three_ne_one : (3 : Fin (MarkedCore.coreRank h)) ≠ 1 := fun hcon ↦ by
  have hval := congrArg Fin.val hcon
  rw [MarkedCore.coreVal_three, MarkedCore.coreVal_one] at hval
  omega

private theorem evenDeriv_handleU_ne_one (j : Fin h) :
    (MarkedCore.handleIdxU j : Fin (MarkedCore.coreRank h)) ≠ 1 := fun hcon ↦ by
  have hval := congrArg Fin.val hcon
  rw [MarkedCore.handleIdxU_val, MarkedCore.coreVal_one] at hval
  omega

private theorem evenDeriv_handleV_ne_one (j : Fin h) :
    (MarkedCore.handleIdxV j : Fin (MarkedCore.coreRank h)) ≠ 1 := fun hcon ↦ by
  have hval := congrArg Fin.val hcon
  rw [MarkedCore.handleIdxV_val, MarkedCore.coreVal_one] at hval
  omega

/-! ### §5.2 Central base shifts do not move the even shift word -/

/-- A central left factor in the bracket's ambient slot is invisible. -/
private theorem evenDeriv_commP_central_right (hk : 3 ≤ k)
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) (b : levelQuot G (k + 1)) :
    commP p (z * b) = commP p b := by
  rw [commP_mul_right_of_mem k hk hp z b,
    commP_eq_one_of_mul_comm (zLayer_commute hz p).symm.eq, one_mul]

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The even clone of `sqCoreHandleDbarWord_central_base_shift`.**  Shifting the base by
coordinatewise central classes leaves the literal even shift word unchanged: every bracket
loses its central factor, and the diagonal square does not involve the base at all. -/
theorem evenDeriv_dbarWord_central_base_shift (hk : 3 ≤ k)
    {z : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)} (hz : ∀ i, z i ∈ zLayer G k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {c : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hc : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawDbarWord (fun i ↦ z i * base i) c = evenRawDbarWord base c := by
  have key : ∀ j i : Fin (MarkedCore.coreRank h),
      commP (c j) (z i * base i) = commP (c j) (base i) :=
    fun j i ↦ evenDeriv_commP_central_right hk (hc j) (hz i) (base i)
  simp only [evenRawDbarWord, evenRawCoreDbarWord, evenRawHandleDbarWord, key]

end SpanKill

/-! ### §5.3 The three bases of a family, reconciled -/

section Family

open GQ2.Dyadic.LSquare (stageDeriv_commP_row_mem_derivKer stageDeriv_diagonal_row_mem_derivKer)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
variable {T : Tuple W v G chi k}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The canonical-lift base differs from the family base by coordinatewise central classes. -/
theorem EvenKernelDerivationFamily.evenDeriv_exists_central_shift
    (F : EvenKernelDerivationFamily T) :
    ∃ z : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1),
      (∀ i, z i ∈ zLayer G k) ∧
      ∀ i, canonLift G k (T.generators i) = z i * levelMk G (k + 1) (F.lifts i) := by
  have hproj : ∀ i, GQ2.Roe.Labute.levelProj G k (canonLift G k (T.generators i)) =
      GQ2.Roe.Labute.levelProj G k (levelMk G (k + 1) (F.lifts i)) := by
    intro i
    rw [levelProj_canonLift, levelProj_levelMk, F.lifts_level i]
  choose z hz heq using fun i ↦ exists_zLayer_mul (G := G) (hproj i)
  exact ⟨z, hz, heq⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The literal even shift word over the canonical-lift base equals the one over the family
base. -/
theorem EvenKernelDerivationFamily.evenDeriv_dbarWord_eq
    (F : EvenKernelDerivationFamily T) (hk : 3 ≤ k)
    {c : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hc : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) c =
      evenRawDbarWord (fun i ↦ levelMk G (k + 1) (F.lifts i)) c := by
  obtain ⟨z, hz, heq⟩ := F.evenDeriv_exists_central_shift
  rw [show (fun i ↦ canonLift G k (T.generators i)) =
      fun i ↦ z i * levelMk G (k + 1) (F.lifts i) from funext heq]
  exact evenDeriv_dbarWord_central_base_shift hk hz _ hc

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Non-twisted tails over the canonical-lift base are level classes of ambient tail powers of
the family lifts: the central discrepancy dies because `Z_k` has exponent two and the tail
exponent is even. -/
theorem EvenKernelDerivationFamily.evenDeriv_tail_eq
    (F : EvenKernelDerivationFamily T) (hk : 3 ≤ k) (i : Fin (MarkedCore.coreRank h)) :
    canonLift G k (T.generators i) ^ 2 ^ (k - 1) =
      levelMk G (k + 1) (F.lifts i ^ 2 ^ (k - 1)) := by
  obtain ⟨z, hz, heq⟩ := F.evenDeriv_exists_central_shift
  rw [map_pow, heq i]
  have hcomm : Commute (z i) (levelMk G (k + 1) (F.lifts i)) := zLayer_commute (hz i) _
  rw [hcomm.mul_pow]
  have hzpow : z i ^ 2 ^ (k - 1) = 1 := by
    rw [show (2 : ℕ) ^ (k - 1) = 2 * 2 ^ (k - 2) by rw [← pow_succ']; congr 1; omega,
      pow_mul, zLayer_sq G (hz i), one_pow]
  rw [hzpow, one_mul]

end Family

/-! ### §5.4 The coordinate rows are killed

Five plain brackets and one diagonal.  The diagonal is the even lane's own step: coordinate
`0` reads `p² · [p, base 0] · [p, base 1]`, and `commP_mul_right_of_mem` regroups it as
`p² · [p, base 0 · base 1]`, which is the shape the committed diagonal-row lemma consumes,
with partner character `v 0 · v 1`.  Only then do roles 1 and 3 of the twisted index coincide
again, at index `1`, exactly as `StageAbstractionEvenKernelAdapted.lean` §1 predicts. -/

section CoordinateRows

open GQ2.Dyadic.LSquare (stageDeriv_commP_row_mem_derivKer stageDeriv_diagonal_row_mem_derivKer)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}
variable {Φ : ContinuousMonoidHom G (WL (k + 1))}

/-- **Every one-coordinate even shift over exactly `χ`-marked ambient lifts is killed.** -/
theorem evenDeriv_coordinateShift_mem_derivKer (hk : 3 ≤ k) (hbase : IsChiShadowDeriv chi Φ)
    (xb : Fin (MarkedCore.coreRank h) → G) (vv : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
    (hchi : ∀ i, chi (xb i) = vv i)
    (hv1 : ∀ i : Fin (MarkedCore.coreRank h), i ≠ 1 →
      (2 : ℤ_[2]) ^ 2 ∣ ((vv i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hvd : (2 : ℤ_[2]) ^ 2 ∣ ((vv 0 * vv 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1)
    (i : Fin (MarkedCore.coreRank h)) (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom (fun j ↦ levelMk G (k + 1) (xb j)) hk)
      (evenRawDepthCoordinateCorrection i p)).1 ∈ derivKer Φ k := by
  obtain ⟨a, ha, hpa⟩ := p.2
  have hbracket : ∀ b : Fin (MarkedCore.coreRank h), b ≠ 1 →
      commP p.1 (levelMk G (k + 1) (xb b)) ∈ derivKer Φ k := by
    intro b hb
    rw [← hpa, show commP (levelMk G (k + 1) a) (levelMk G (k + 1) (xb b)) =
      levelMk G (k + 1) (commP a (xb b)) from (Marking.map_commP _ _ _).symm]
    refine stageDeriv_commP_row_mem_derivKer hk hbase ha (xb b) ?_
    rw [hchi b]
    exact hv1 b hb
  refine evenIndex_cases
    (P := fun i ↦ ((evenRawDepthShiftHom (fun j ↦ levelMk G (k + 1) (xb j)) hk)
      (evenRawDepthCoordinateCorrection i p)).1 ∈ derivKer Φ k) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [evenRawDepthShiftHom_zero_apply]
    have hrw : levelMk G (k + 1) (a ^ 2 * commP a (xb 0 * xb 1)) =
        p.1 ^ 2 * commP p.1 (levelMk G (k + 1) (xb 0)) *
          commP p.1 (levelMk G (k + 1) (xb 1)) := by
      rw [map_mul, map_pow, Marking.map_commP, map_mul, hpa,
        commP_mul_right_of_mem k hk p.2, ← mul_assoc]
    rw [← hrw]
    refine stageDeriv_diagonal_row_mem_derivKer hk hbase ha (xb 0 * xb 1) ?_
    rw [map_mul, hchi 0, hchi 1]
    exact hvd
  · rw [evenRawDepthShiftHom_one_apply]
    exact hbracket 0 evenDeriv_zero_ne_one
  · rw [evenRawDepthShiftHom_two_apply]
    exact hbracket 3 evenDeriv_three_ne_one
  · rw [evenRawDepthShiftHom_three_apply]
    exact hbracket 2 evenDeriv_two_ne_one
  · intro j
    rw [evenRawDepthShiftHom_handleU_apply]
    exact hbracket _ (evenDeriv_handleV_ne_one j)
  · intro j
    rw [evenRawDepthShiftHom_handleV_apply]
    exact hbracket _ (evenDeriv_handleU_ne_one j)

end CoordinateRows

/-! ### §5.5 The whole raw shift span is killed

A raw depth correction is the ordered product of its six families of one-coordinate
corrections, and the shift is a homomorphism, so §5.4 suffices. -/

section SpanLe

open GQ2.Dyadic.LSquare (stageDeriv_commP_row_mem_derivKer stageDeriv_diagonal_row_mem_derivKer)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

/-- A list product collapses to its single non-trivial factor. -/
private theorem evenDeriv_list_single {H I : Type*} [Monoid H] (l : List I) (j : I) (f : I → H)
    (hj : j ∈ l) (hnodup : l.Nodup) (hf : ∀ i ∈ l, i ≠ j → f i = 1) :
    (l.map f).prod = f j := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
      have hnd := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hj with hij | hj
      · subst i
        have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro y hy
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
          exact hf b (List.mem_cons_of_mem _ hb) (fun hbj ↦ hnd.1 (hbj ▸ hb))
        simp [htail]
      · have hij : i ≠ j := fun hcon ↦ hnd.1 (hcon ▸ hj)
        rw [List.map_cons, List.prod_cons, hf i (by simp) hij, one_mul,
          ih hj hnd.2 (fun b hb hbj ↦ hf b (List.mem_cons_of_mem _ hb) hbj)]

/-- A raw depth correction is the ordered product of its one-coordinate corrections. -/
private theorem evenDeriv_rawDepthCorrection_eq_prod (V : EvenRawDepthCorrection G h k) :
    V = ((List.finRange (MarkedCore.coreRank h)).map fun i ↦
      evenRawDepthCoordinateCorrection i
        (⟨V.correction i, V.depth i⟩ : lambdaImage G (k - 1) (k + 1))).prod := by
  classical
  ext j
  let ev : EvenRawDepthCorrection G h k →* levelQuot G (k + 1) :=
    { toFun := fun U ↦ U.correction j
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  change ev V = ev (((List.finRange (MarkedCore.coreRank h)).map fun i ↦
    evenRawDepthCoordinateCorrection i
      (⟨V.correction i, V.depth i⟩ : lambdaImage G (k - 1) (k + 1))).prod)
  rw [map_list_prod]
  have hsingle := evenDeriv_list_single
    (List.finRange (MarkedCore.coreRank h)) j
    (fun i ↦ ev (evenRawDepthCoordinateCorrection i
      (⟨V.correction i, V.depth i⟩ : lambdaImage G (k - 1) (k + 1))))
    (by simp) (List.nodup_finRange _) (by
      intro i _ hij
      simp [ev, evenRawDepthCoordinateCorrection_apply, Ne.symm hij])
  simpa [List.map_map, Function.comp_def, ev, evenRawDepthCoordinateCorrection_apply] using
    hsingle.symm

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {Φ : ContinuousMonoidHom G (WL (k + 1))}

/-- **The even raw shift span is killed by every `χ`-shadowed derivation.** -/
theorem evenDeriv_rawShiftSpan_le_derivKer (hk : 3 ≤ k) (hbase : IsChiShadowDeriv chi Φ)
    (xb : Fin (MarkedCore.coreRank h) → G) (vv : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
    (hchi : ∀ i, chi (xb i) = vv i)
    (hv1 : ∀ i : Fin (MarkedCore.coreRank h), i ≠ 1 →
      (2 : ℤ_[2]) ^ 2 ∣ ((vv i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hvd : (2 : ℤ_[2]) ^ 2 ∣ ((vv 0 * vv 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1) :
    evenRawShiftSpan (h := h) (fun i ↦ levelMk G (k + 1) (xb i)) hk ≤ derivKer Φ k := by
  rintro z ⟨q, hq, rfl⟩
  obtain ⟨V, rfl⟩ := hq
  rw [evenDeriv_rawDepthCorrection_eq_prod V, map_list_prod, map_list_prod]
  simp only [List.map_map]
  refine Subgroup.list_prod_mem _ ?_
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  exact evenDeriv_coordinateShift_mem_derivKer hk hbase xb vv hchi hv1 hvd i
    ⟨V.correction i, V.depth i⟩

end SpanLe

/-! ## §6 The criterion

The clone of `stageResidual_mem_rawShiftSpan_of_forall_derivKer` (L template, line 340), and
with it boundary one of `StageAbstractionEvenKernelAdapted.lean` §3.  Decompose the class as
shift times tail by §3, put the tail in squarefree normal form by §4, and separate with the
diagonal offset pattern: every tail *other* than the chosen one is killed by the chosen
functional, so if the finset were non-empty its distinguished tail would be killed too, which
the odd-offset lemma forbids. -/

section Criterion

open GQ2.Dyadic.LSquare (stageDeriv_tail_mem_derivKer_of_even
  stageDeriv_tail_not_mem_derivKer_of_odd)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
variable {T : Tuple W v G chi k}

/-- **Span membership from simultaneous kernel membership**, the even clone of the L crux.
The two arithmetic hypotheses are exactly what `StageAbstractionEvenKernelAdapted.lean` §1
proves for `vN α` and `vM α`. -/
theorem evenDeriv_mem_rawShiftSpan_of_forall_derivKer
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (hk : 3 ≤ k) (F : EvenKernelDerivationFamily T)
    (hv1 : ∀ i : Fin (MarkedCore.coreRank h), i ≠ 1 →
      (2 : ℤ_[2]) ^ 2 ∣ ((v i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hvd : (2 : ℤ_[2]) ^ 2 ∣ ((v 0 * v 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1)
    {zc : levelQuot G (k + 1)} (hzc : zc ∈ zLayer G k)
    (hker : ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
      zc ∈ derivKer (F.deriv i₀ hi₀) k) :
    zc ∈ evenRawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk := by
  classical
  obtain ⟨V, t, ht, hdec⟩ := evenDeriv_exists_shift_mul_tail hfg hpro T.topGen hk hzc
  have hshift_ker : ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) V.correction ∈
        derivKer (F.deriv i₀ hi₀) k := by
    intro i₀ hi₀
    rw [F.evenDeriv_dbarWord_eq hk V.depth]
    exact evenDeriv_rawShiftSpan_le_derivKer hk (F.deriv_base i₀ hi₀) F.lifts v F.lifts_chi
      hv1 hvd (evenRawDepthShift_mem_shiftSpan (fun i ↦ levelMk G (k + 1) (F.lifts i)) hk V)
  have ht_ker : ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
      t ∈ derivKer (F.deriv i₀ hi₀) k := by
    intro i₀ hi₀
    have h1 : t = (evenRawDbarWord (fun i ↦ canonLift G k (T.generators i))
        V.correction)⁻¹ * zc := by rw [hdec]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hshift_ker i₀ hi₀)) (hker i₀ hi₀)
  obtain ⟨hmem, s, hs⟩ := evenDerivTailSpan_exists_finset_prod T.generators hk ht
  have hsempty : s = ∅ := by
    by_contra hne
    obtain ⟨i₀, hi₀s⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hKb : ∀ j : {i : Fin (MarkedCore.coreRank h) // i ≠ 1}, j ≠ i₀ →
        evenDerivTailLayer T.generators hk j ∈
          (derivKer (F.deriv i₀.1 i₀.2) k).comap (zLayer G k).subtype := by
      intro j hj
      rw [Subgroup.mem_comap]
      show canonLift G k (T.generators j.1) ^ 2 ^ (k - 1) ∈ derivKer (F.deriv i₀.1 i₀.2) k
      rw [F.evenDeriv_tail_eq hk j.1]
      refine stageDeriv_tail_mem_derivKer_of_even hk (F.deriv_base i₀.1 i₀.2) ?_ ?_
      · rw [F.lifts_chi j.1]
        exact hv1 j.1 j.2
      · exact F.deriv_off i₀.1 i₀.2 j.1 j.2 (fun hval ↦ hj (Subtype.ext hval))
    have htb : (⟨t, hmem⟩ : ↥(zLayer G k)) ∈
        (derivKer (F.deriv i₀.1 i₀.2) k).comap (zLayer G k).subtype := by
      rw [Subgroup.mem_comap]
      exact ht_ker i₀.1 i₀.2
    have hprodb : (∏ j ∈ s.erase i₀, evenDerivTailLayer T.generators hk j) ∈
        (derivKer (F.deriv i₀.1 i₀.2) k).comap (zLayer G k).subtype :=
      Subgroup.prod_mem _ fun j hj ↦ hKb j (Finset.mem_erase.mp hj).1
    have hdiag : evenDerivTailLayer T.generators hk i₀ ∈
        (derivKer (F.deriv i₀.1 i₀.2) k).comap (zLayer G k).subtype := by
      have hsplit : evenDerivTailLayer T.generators hk i₀ =
          (⟨t, hmem⟩ : ↥(zLayer G k)) *
            (∏ j ∈ s.erase i₀, evenDerivTailLayer T.generators hk j)⁻¹ := by
        rw [hs, ← Finset.mul_prod_erase s _ hi₀s]
        group
      rw [hsplit]
      exact Subgroup.mul_mem _ htb (Subgroup.inv_mem _ hprodb)
    rw [Subgroup.mem_comap] at hdiag
    have hdiag' : canonLift G k (T.generators i₀.1) ^ 2 ^ (k - 1) ∈
      derivKer (F.deriv i₀.1 i₀.2) k := hdiag
    rw [F.evenDeriv_tail_eq hk i₀.1] at hdiag'
    refine stageDeriv_tail_not_mem_derivKer_of_odd hk (F.deriv_base i₀.1 i₀.2) ?_
      (F.deriv_diag i₀.1 i₀.2) hdiag'
    rw [F.lifts_chi i₀.1]
    exact hv1 i₀.1 i₀.2
  have ht1 : t = 1 := by
    have hval := hs
    rw [hsempty, Finset.prod_empty] at hval
    exact congrArg Subtype.val hval
  rw [hdec, ht1, mul_one]
  exact evenRawDepthShift_mem_shiftSpan (fun i ↦ canonLift G k (T.generators i)) hk V

/-- **Boundary one, discharged.**  The derivation criterion of
`StageAbstractionEvenKernelAdapted.lean` §3 holds at every topologically finitely generated
pro-`2` carrier whose value table satisfies the two mod-`4` conditions. -/
theorem evenDeriv_derivKerCriterion
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (hk : 3 ≤ k) (F : EvenKernelDerivationFamily T)
    (hv1 : ∀ i : Fin (MarkedCore.coreRank h), i ≠ 1 →
      (2 : ℤ_[2]) ^ 2 ∣ ((v i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hvd : (2 : ℤ_[2]) ^ 2 ∣ ((v 0 * v 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1) :
    EvenKernelDerivKerCriterion F hk :=
  fun _ hz hkerz ↦
    evenDeriv_mem_rawShiftSpan_of_forall_derivKer hfg hpro hk F hv1 hvd hz hkerz

end Criterion

end

end GQ2.Dyadic.StageGeneric

/-! ## §7 Axiom pins

Every public declaration of this file, printed.  All are expected at std-3,
`[propext, Classical.choice, Quot.sound]`.

This is *lower* than the corresponding L file.  `KernelAdaptedSupply.lean` prints
`absGalQ2_isTopologicallyFinitelyGenerated` on five of its eleven pins, because it works at
`maxProPQuotient 2 (GalK K)` and calls `maxProTwoGalK_isTopologicallyFinGen` for the span
input.  Here topological finite generation and pro-`2`-ness are named hypotheses `hfg`, `hpro`
of §2 onwards, so the arithmetic is deferred to the caller and this station stays at std-3,
in keeping with the even lane's policy of acquiring the census axioms only in
`StageAbstractionEvenAssembly.lean` §1. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 ambient lifts and level generation
#print axioms evenDeriv_levelMk_generates
#print axioms evenDeriv_exists_ambientLift

-- §2 the field-side augmented span
#print axioms evenDeriv_zLayer_le_augmentedSpan

-- §3 the canonical tail span and the decomposition
#print axioms evenDerivTailSpan
#print axioms evenDeriv_rawTailSpan_eq
#print axioms evenDerivTailSpan_le_zLayer
#print axioms evenDeriv_exists_shift_mul_tail

-- §4 squarefree normal form
#print axioms evenDerivZLayerCommGroup
#print axioms evenDerivTailLayer
#print axioms evenDerivTailSpan_exists_finset_prod

-- §5 the span kill
#print axioms evenDeriv_dbarWord_central_base_shift
#print axioms EvenKernelDerivationFamily.evenDeriv_exists_central_shift
#print axioms EvenKernelDerivationFamily.evenDeriv_dbarWord_eq
#print axioms EvenKernelDerivationFamily.evenDeriv_tail_eq
#print axioms evenDeriv_coordinateShift_mem_derivKer
#print axioms evenDeriv_rawShiftSpan_le_derivKer

-- §6 the criterion
#print axioms evenDeriv_mem_rawShiftSpan_of_forall_derivKer
#print axioms evenDeriv_derivKerCriterion

end AxiomPins
