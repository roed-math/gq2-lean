/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedDelta

/-!
# Structural exactness and head reflection for the marked Mpc successor

This module isolates the remaining all-degree marked-source problem.  It packages the four
unrestricted depth-`r` source slots and their cost map, pulls the corrected `(nu, deltaD)`
obstruction back to the source, and proves all routine exactness implications and base-row
independence.

The main structural result is `mpcMk_headReflection`.  Vanishing of the two corrected output
digits forces the square-bearing head to agree modulo `lambda_(r+1)` with an element of the
marked `B^2` carrier.  The proof uses the canonical M-frame: the torsion row dies from depth
two onward, the `B` row is automatically even, and the two vanished digits allow the `C` and
`D` rows to be removed by one-deeper `Z_2`-powers.  Density rounding then produces an actual
member of `mpcSxKill r` without changing the graded cost.

After head reflection, the sole open theorem is `MpcMkHeadCompletion`: the image of the
head-marked cost must equal the image of the fully marked cost.  Exact finite 2-quotient
calculations verify that equality for `r = 2, 3, 4`, but those calculations are not a proof.
The completion statement is defined for a falsifiable interface and used only as an explicit
hypothesis in the implication theorem; it is not assumed, axiomatized, or claimed here.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new
axiom, no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric GQ2.Dyadic.EvenFamily

noncomputable section

/-- The four unrestricted depth-`r` source slots. -/
abbrev MpcMkRawSource (r : ℕ) :=
  twoCentralSeries (DM 2 0 : Type) r ×
    twoCentralSeries (DM 2 0 : Type) r ×
    twoCentralSeries (DM 2 0 : Type) r ×
    twoCentralSeries (DM 2 0 : Type) r

/-- Package an unrestricted source tuple as the canonical raw correction. -/
def mpcMkRawSourceCorrection (r : ℕ) :
    MpcMkRawSource r →* EvenRawDepthCorrection (DM 2 0 : Type) 0 (r + 1) where
  toFun u := mpcMkRawCorrection r u.1 u.2.1 u.2.2.1 u.2.2.2
    u.1.2 u.2.1.2 u.2.2.1.2 u.2.2.2.2
  map_one' := by
    ext i
    fin_cases i <;> rfl
  map_mul' u v := by
    ext i
    fin_cases i <;> rfl

/-- The unrestricted source-to-cost homomorphism. -/
def mpcMkRawCost (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MpcMkRawSource r →* zLayer (DM 2 0 : Type) (r + 1) :=
  (evenRawDepthShiftHom (mpcMkRawBase r t n) (by omega)).comp
    (mpcMkRawSourceCorrection r)

theorem mpcMkRawCost_apply (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type))
    (u : MpcMkRawSource r) :
    (mpcMkRawCost r hr t n u).1 =
      levelMk (DM 2 0 : Type) (r + 2)
        (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2) := by
  exact mpcMk_rawShift_eq_cost r hr t n u.1 u.2.1 u.2.2.1 u.2.2.2
    u.1.2 u.2.1.2 u.2.2.1.2 u.2.2.2.2

/-- Forget the four marked carrier constraints. -/
def mpcMkMarkedSource (r : ℕ) : MpcMkCostDomain r →* MpcMkRawSource r where
  toFun u :=
    (⟨u.1, u.1.2.2⟩, ⟨u.2.1, u.2.1.2.2⟩,
      ⟨u.2.2.1, u.2.2.1.2.2⟩, ⟨u.2.2.2, u.2.2.2.2.2⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Sources in which only the square-bearing head slot is already marked. -/
abbrev MpcMkHeadMarkedSource (r : ℕ) :=
  mpcSxKill r ×
    twoCentralSeries (DM 2 0 : Type) r ×
    twoCentralSeries (DM 2 0 : Type) r ×
    twoCentralSeries (DM 2 0 : Type) r

/-- Forget the head-slot marked constraint. -/
def mpcMkHeadMarkedSource (r : ℕ) :
    MpcMkHeadMarkedSource r →* MpcMkRawSource r where
  toFun u :=
    (⟨u.1, u.1.2.2⟩, u.2.1, u.2.2.1, u.2.2.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cost map with only the square-bearing head slot restricted. -/
def mpcMkHeadMarkedCost (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MpcMkHeadMarkedSource r →* zLayer (DM 2 0 : Type) (r + 1) :=
  (mpcMkRawCost r hr t n).comp (mpcMkHeadMarkedSource r)

theorem mpcMkRawCost_markedSource (r : ℕ) (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type)) (u : MpcMkCostDomain r) :
    mpcMkRawCost r hr t n (mpcMkMarkedSource r u) =
      mpcMkCost r hr t n u := by
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  rfl

/-- The two corrected source obstructions, evaluated on the cost target. -/
def mpcMkTargetObstruction (r : ℕ) :
    zLayer (DM 2 0 : Type) (r + 1) →*
      Multiplicative (ZMod (2 ^ (r + 1))) ×
        Multiplicative (ZMod (2 ^ (r + 1))) :=
  ((mpcMkNuLevel (r + 1)).comp (zLayer (DM 2 0 : Type) (r + 1)).subtype).prod
    ((mpcMkDeltaDLevel (r + 1)).comp
      (zLayer (DM 2 0 : Type) (r + 1)).subtype)

/-- Pull the two corrected target obstructions back to the unrestricted source. -/
def mpcMkRawObstruction (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MpcMkRawSource r →*
      Multiplicative (ZMod (2 ^ (r + 1))) ×
        Multiplicative (ZMod (2 ^ (r + 1))) :=
  (mpcMkTargetObstruction r).comp (mpcMkRawCost r hr t n)

/-- Depth-two changes in the two base rows do not change the graded source map. -/
theorem mpcMkRawCost_base_indep
    (r : ℕ) (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    mpcMkRawCost r hr t n = mpcMkRawCost r hr 1 1 := by
  ext u
  rw [mpcMkRawCost_apply, mpcMkRawCost_apply]
  let f := levelMk (DM 2 0 : Type) (r + 2)
  have hdrop : ∀ {a x e : levelQuot (DM 2 0 : Type) (r + 2)},
      a ∈ lambdaImage (DM 2 0 : Type) r (r + 2) →
      e ∈ lambdaImage (DM 2 0 : Type) 2 (r + 2) →
      commP a (x * e) = commP a x := by
    intro a x e ha he
    have hea : commP e a = 1 := mpcLad_vanish he ha
    have hae : commP a e = 1 := by rw [mpcSx_swap, hea, inv_one]
    rw [cfour_commP_mul_right,
      cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left ha x) e,
      hae]
    simp only [one_mul, mul_one]
  have hus : f u.1 ∈ lambdaImage (DM 2 0 : Type) r (r + 2) :=
    ⟨u.1, u.1.2, rfl⟩
  have hum : f u.2.2.1 ∈ lambdaImage (DM 2 0 : Type) r (r + 2) :=
    ⟨u.2.2.1, u.2.2.1.2, rfl⟩
  have ht' : f t ∈ lambdaImage (DM 2 0 : Type) 2 (r + 2) := ⟨t, ht, rfl⟩
  have hn' : f n ∈ lambdaImage (DM 2 0 : Type) 2 (r + 2) := ⟨n, hn, rfl⟩
  simp only [mpcBldIncr, map_mul, map_pow, mpcBld_map_commP,
    mpcWordLetB, mpcWordLetD, mul_one]
  rw [hdrop hus ht', hdrop hum hn']

theorem mpcMkRawObstruction_base_indep
    (r : ℕ) (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    mpcMkRawObstruction r hr t n = mpcMkRawObstruction r hr 1 1 := by
  rw [mpcMkRawObstruction, mpcMkRawObstruction,
    mpcMkRawCost_base_indep r hr ht hn]

theorem mpcMkCost_mem_nuKernel {r : ℕ} (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type)) (u : MpcMkCostDomain r) :
    (((mpcMkCost r hr t n u : zLayer (DM 2 0 : Type) (r + 1)) :
        levelQuot (DM 2 0 : Type) (r + 2))) ∈
      mpcMkNuKernel (r + 1) := by
  rw [mpcMkNuKernel, MonoidHom.mem_ker]
  change mpcMkNuMod (r + 1)
    (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2) = 1
  have hs : mpcMkNuMod (r + 1) u.1 = 1 := by
    change Multiplicative.ofAdd
      (PadicInt.toZModPow (r + 1) (nuM 2 0 (by omega) u.1).toAdd) = 1
    rw [mpcSx_marked_nu u.1.2.1]
    simp
  simp only [mpcBldIncr, map_mul, map_pow, hs, one_pow, one_mul]
  simp [commP, mul_comm]

theorem mpcMk_markedSource_le_rawObstructionKernel
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    (mpcMkMarkedSource r).range ≤ (mpcMkRawObstruction r hr t n).ker := by
  rintro _ ⟨u, rfl⟩
  rw [MonoidHom.mem_ker, mpcMkRawObstruction, MonoidHom.comp_apply,
    mpcMkRawCost_markedSource]
  apply Prod.ext
  · change mpcMkNuLevel (r + 1) (mpcMkCost r hr t n u).1 = 1
    exact MonoidHom.mem_ker.mp (mpcMkCost_mem_nuKernel hr t n u)
  · change mpcMkDeltaDLevel (r + 1) (mpcMkCost r hr t n u).1 = 1
    exact MonoidHom.mem_ker.mp (mpcMkCost_mem_deltaDKernel hr t n u)

theorem mpcMk_rawCostKernel_le_rawObstructionKernel
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    (mpcMkRawCost r hr t n).ker ≤ (mpcMkRawObstruction r hr t n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [mpcMkRawObstruction, MonoidHom.comp_apply, hu, map_one]

theorem mpcMk_routineSource_le_rawObstructionKernel
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    (mpcMkMarkedSource r).range ⊔ (mpcMkRawCost r hr t n).ker ≤
      (mpcMkRawObstruction r hr t n).ker :=
  sup_le (mpcMk_markedSource_le_rawObstructionKernel r hr t n)
    (mpcMk_rawCostKernel_le_rawObstructionKernel r hr t n)

/-- The sole missing exactness statement, in the source group where its finite-rank content
is directly testable. -/
def MpcMkSourceExact (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) : Prop :=
  (mpcMkRawObstruction r hr t n).ker =
    (mpcMkMarkedSource r).range ⊔ (mpcMkRawCost r hr t n).ker

/-- M-frame reflection marks the head slot whenever the two output digits vanish. -/
def MpcMkHeadReflection (r : ℕ) (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type)) : Prop :=
  ∀ u : MpcMkRawSource r,
    u ∈ (mpcMkRawObstruction r hr t n).ker →
      mpcMkRawCost r hr t n u ∈
        MonoidHom.range (mpcMkHeadMarkedCost r hr t n)

/-- The remaining carrier-completion identity after the head is marked. -/
def MpcMkHeadCompletion (r : ℕ) (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type)) : Prop :=
  MonoidHom.range (mpcMkHeadMarkedCost r hr t n) =
    MonoidHom.range (mpcMkCost r hr t n)

theorem mpcMk_sourceExact_of_headReflection_of_headCompletion
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type))
    (hreflect : MpcMkHeadReflection r hr t n)
    (hcomplete : MpcMkHeadCompletion r hr t n) :
    MpcMkSourceExact r hr t n := by
  apply le_antisymm
  · intro u hu
    obtain ⟨h, hh⟩ := hreflect u hu
    have hcost : mpcMkHeadMarkedCost r hr t n h ∈
        MonoidHom.range (mpcMkCost r hr t n) := by
      rw [← hcomplete]
      exact ⟨h, rfl⟩
    obtain ⟨v, hv⟩ := hcost
    let a : MpcMkRawSource r := mpcMkMarkedSource r v
    let b : MpcMkRawSource r := a⁻¹ * u
    have ha : a ∈ (mpcMkMarkedSource r).range := ⟨v, rfl⟩
    have hb : b ∈ (mpcMkRawCost r hr t n).ker := by
      rw [MonoidHom.mem_ker]
      dsimp only [b]
      rw [map_mul, map_inv]
      have hav : mpcMkRawCost r hr t n a = mpcMkCost r hr t n v :=
        mpcMkRawCost_markedSource r hr t n v
      have hhu : mpcMkHeadMarkedCost r hr t n h =
          mpcMkRawCost r hr t n u := hh
      rw [hav, hv, hhu, inv_mul_cancel]
    apply Subgroup.mem_sup_of_normal_right.mpr
    exact ⟨a, ha, b, hb, by simp [b]⟩
  · exact mpcMk_routineSource_le_rawObstructionKernel r hr t n

theorem mpcMk_sourceExact_iff_base
    (r : ℕ) (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    MpcMkSourceExact r hr t n ↔ MpcMkSourceExact r hr 1 1 := by
  rw [MpcMkSourceExact, MpcMkSourceExact,
    mpcMkRawCost_base_indep r hr ht hn,
    mpcMkRawObstruction_base_indep r hr ht hn]

theorem mpcMk_sourceExact_iff_missing_inclusion
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MpcMkSourceExact r hr t n ↔
      (mpcMkRawObstruction r hr t n).ker ≤
        (mpcMkMarkedSource r).range ⊔ (mpcMkRawCost r hr t n).ker := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm h (mpcMk_routineSource_le_rawObstructionKernel r hr t n)

theorem mpcMk_exists_markedSource_of_exact
    {r : ℕ} (hr : 2 ≤ r) (t n : (DM 2 0 : Type))
    (hexact : MpcMkSourceExact r hr t n) (u : MpcMkRawSource r)
    (hu : u ∈ (mpcMkRawObstruction r hr t n).ker) :
    ∃ v : MpcMkCostDomain r,
      mpcMkRawCost r hr t n u =
        mpcMkRawCost r hr t n (mpcMkMarkedSource r v) := by
  rw [hexact] at hu
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hu
  obtain ⟨v, rfl⟩ := ha
  refine ⟨v, ?_⟩
  rw [← hab, map_mul, MonoidHom.mem_ker.mp hb, mul_one]

/-- The source exactness statement is precisely strong enough to replace the existing
unrestricted witness by a full marked witness. -/
theorem mpcMk_mem_markedCostRange_of_sourceExact
    {r : ℕ} (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hexact : MpcMkSourceExact r hr t n)
    (q : zLayer (DM 2 0 : Type) (r + 1))
    (hfive : (q : levelQuot (DM 2 0 : Type) (r + 2)) ∈
      mpcMkFiveCarrierKernel (r + 1)) :
    q ∈ MonoidHom.range (mpcMkCost r hr t n) := by
  obtain ⟨us, ut, um, un, hus, hut, hum, hun, hq⟩ :=
    mpcMk_exists_unrestrictedCost_of_fiveCarrierKernel hr ht hn q.2 hfive
  let u : MpcMkRawSource r :=
    (⟨us, hus⟩, ⟨ut, hut⟩, ⟨um, hum⟩, ⟨un, hun⟩)
  have hraw : mpcMkRawCost r hr t n u = q := by
    apply Subtype.ext
    rw [mpcMkRawCost_apply]
    exact hq.symm
  have hu : u ∈ (mpcMkRawObstruction r hr t n).ker := by
    rw [MonoidHom.mem_ker, mpcMkRawObstruction, MonoidHom.comp_apply, hraw]
    apply Prod.ext
    · exact MonoidHom.mem_ker.mp hfive.1.2
    · exact MonoidHom.mem_ker.mp hfive.2
  obtain ⟨v, hv⟩ := mpcMk_exists_markedSource_of_exact hr t n hexact u hu
  refine ⟨v, ?_⟩
  rw [← mpcMkRawCost_markedSource]
  exact hv.symm.trans hraw

/-! ## Scratch: head reflection through the canonical M-frame -/

/-- Divisibility locus for a continuous additive row on `DM 2 0`. -/
private def mpcMkRowSub
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (m : ℕ) : Subgroup (DM 2 0 : Type) where
  carrier := {g | (2 ^ m : ℤ_[2]) ∣ toAdd (f g)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at ha hb ⊢
    exact dvd_add ha hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv, toAdd_inv] at ha ⊢
    exact ha.neg_right

private theorem mpcMk_isClosed_dvd (m : ℕ) :
    IsClosed {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := by
  rw [show {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} =
      (PadicInt.toZModPow m) ⁻¹' {0} by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    norm_num]
  exact isClosed_singleton.preimage (by
    rw [continuous_def]
    intro T _
    exact isOpen_preimage_toZModPow m T)

private theorem mpcMk_isClosed_rowSub
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (m : ℕ) : IsClosed ((mpcMkRowSub f m : Subgroup (DM 2 0 : Type)) :
      Set (DM 2 0 : Type)) := by
  have hset : ((mpcMkRowSub f m : Subgroup (DM 2 0 : Type)) :
      Set (DM 2 0 : Type)) =
      (fun g : (DM 2 0 : Type) => toAdd (f g)) ⁻¹'
        {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := rfl
  rw [hset]
  exact (mpcMk_isClosed_dvd m).preimage
    (continuous_toAdd.comp f.continuous)

/-- Every additive row of a depth-`k` element is divisible by `2^(k-1)`. -/
private theorem mpcMk_row_dvd
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    {k : ℕ} {g : (DM 2 0 : Type)}
    (hg : g ∈ twoCentralSeries (DM 2 0 : Type) k) :
    (2 ^ (k - 1) : ℤ_[2]) ∣ toAdd (f g) := by
  have hmain : ∀ m : ℕ,
      twoCentralSeries (DM 2 0 : Type) (m + 1) ≤ mpcMkRowSub f m := by
    intro m
    induction m with
    | zero =>
      intro v _
      change (2 ^ 0 : ℤ_[2]) ∣ toAdd (f v)
      rw [pow_zero]
      exact one_dvd _
    | succ m ih =>
      rw [twoCentralSeries_succ (G := (DM 2 0 : Type)) (by omega),
        twoCentralSucc]
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        (mpcMk_isClosed_rowSub f (m + 1))
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨v, hv, rfl⟩
        change (2 ^ (m + 1) : ℤ_[2]) ∣ toAdd (f (v ^ 2))
        rw [map_pow, toAdd_pow]
        change (2 ^ (m + 1) : ℤ_[2]) ∣ (2 : ℤ_[2]) * toAdd (f v)
        obtain ⟨c, hc⟩ := ih hv
        refine ⟨c, ?_⟩
        rw [hc, pow_succ]
        ring
      · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        change (2 ^ (m + 1) : ℤ_[2]) ∣
          toAdd (f (a * b * a⁻¹ * b⁻¹))
        simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
        have hz : toAdd (f a) + toAdd (f b) + -toAdd (f a) +
            -toAdd (f b) = 0 := by ring
        rw [hz]
        exact dvd_zero _
  match k with
  | 0 =>
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | (k + 1) =>
    rw [Nat.add_sub_cancel]
    exact hmain k hg

theorem mpcMkNu_eq_mCHom :
    nuM 2 0 (by omega) = (mCHom (by omega) 0).comp (mAbMkHom 2 0) := by
  apply dm_hom_ext
  intro i
  rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
  all_goals
    change nuM 2 0 (by omega) (dmGen 2 0 _) =
      mCHom (by omega) 0 (GQ2.SectionThree.abMk (dmGen 2 0 _))
    rw [nuM, mLiftHom_gen, mCHom, mCoordHom_gen]
    simp

theorem mpcMkNu_eq_mCHom_apply (x : (DM 2 0 : Type)) :
    nuM 2 0 (by omega) x =
      mCHom (by omega) 0 (GQ2.SectionThree.abMk x) := by
  exact DFunLike.congr_fun mpcMkNu_eq_mCHom x

private theorem mpcMk_mod_succ_sq_eq_one_imp_mod_eq_one
    (r : ℕ) (a : ℤ_[2])
    (h : (ofAdd (PadicInt.toZModPow (r + 1) a) :
      Multiplicative (ZMod (2 ^ (r + 1)))) ^ 2 = 1) :
    (ofAdd (PadicInt.toZModPow r a) :
      Multiplicative (ZMod (2 ^ r))) = 1 := by
  have hz : (2 : ZMod (2 ^ (r + 1))) *
      PadicInt.toZModPow (r + 1) a = 0 := by
    have hz' := congrArg Multiplicative.toAdd h
    simpa [toAdd_pow, two_nsmul] using hz'
  have hprod : PadicInt.toZModPow (r + 1) ((2 : ℤ_[2]) * a) = 0 := by
    simpa only [map_mul, map_ofNat] using hz
  have hd : (2 : ℤ_[2]) ^ (r + 1) ∣ (2 : ℤ_[2]) * a := by
    have hker : (2 : ℤ_[2]) * a ∈
        RingHom.ker (PadicInt.toZModPow (r + 1)) := by
      rw [RingHom.mem_ker]
      exact hprod
    rw [PadicInt.ker_toZModPow] at hker
    exact Ideal.mem_span_singleton.mp hker
  have hd' : (2 : ℤ_[2]) * (2 : ℤ_[2]) ^ r ∣
      (2 : ℤ_[2]) * a := by
    simpa [pow_succ'] using hd
  have ha : (2 : ℤ_[2]) ^ r ∣ a :=
    (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ_[2]) ≠ 0)).mp hd'
  apply Multiplicative.toAdd.injective
  change PadicInt.toZModPow r a = 0
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]
  exact ha

/-- Vanishing of the raw output obstruction forces the two head digits to vanish one
filtration level earlier. -/
theorem mpcMk_headDigits_of_rawObstruction
    {r : ℕ} (hr : 2 ≤ r) (t n : (DM 2 0 : Type))
    (u : MpcMkRawSource r)
    (hu : u ∈ (mpcMkRawObstruction r hr t n).ker) :
    mpcMkNuMod r u.1 = 1 ∧ mpcMkDeltaDMod r u.1 = 1 := by
  rw [MonoidHom.mem_ker] at hu
  have hnu := congrArg Prod.fst hu
  have hd := congrArg Prod.snd hu
  simp only [mpcMkRawObstruction, MonoidHom.comp_apply,
    mpcMkTargetObstruction] at hnu hd
  change mpcMkNuLevel (r + 1) (mpcMkRawCost r hr t n u).1 = 1 at hnu
  change mpcMkDeltaDLevel (r + 1) (mpcMkRawCost r hr t n u).1 = 1 at hd
  rw [mpcMkRawCost_apply] at hnu hd
  change mpcMkNuMod (r + 1)
      (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2) = 1 at hnu
  change mpcMkDeltaDMod (r + 1)
      (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2) = 1 at hd
  have hnuSq : (mpcMkNuMod (r + 1) u.1) ^ 2 = 1 := by
    simpa [mpcBldIncr, commP, mul_comm] using hnu
  have hdSq : (mpcMkDeltaDMod (r + 1) u.1) ^ 2 = 1 := by
    simpa [mpcBldIncr, commP, mul_comm] using hd
  constructor
  · exact mpcMk_mod_succ_sq_eq_one_imp_mod_eq_one r
      (nuM 2 0 (by omega) u.1).toAdd hnuSq
  · exact mpcMk_mod_succ_sq_eq_one_imp_mod_eq_one r
      (mpcMkDeltaD u.1).toAdd hdSq

private theorem mpcMk_zpow_pow_two_mem
    (g : (DM 2 0 : Type)) (m : ℕ) (a : ℤ_[2]) :
    zpowZtwo (isProP_DM 2 0) g (2 ^ m * a) ∈
      twoCentralSeries (DM 2 0 : Type) (m + 1) := by
  have hcast : ((2 ^ m : ℕ) : ℤ_[2]) = 2 ^ m := by
    push_cast
    ring
  have heq : zpowZtwo (isProP_DM 2 0) g a ^ (2 ^ m) =
      zpowZtwo (isProP_DM 2 0) g (2 ^ m * a) := by
    rw [← zpowZtwo_natCast (isProP_DM 2 0)
      (zpowZtwo (isProP_DM 2 0) g a) (2 ^ m),
      zpowZtwo_zpowZtwo, hcast, mul_comm]
  rw [← heq]
  exact pow_two_pow_mem_twoCentralSeries_succ
    (G := (DM 2 0 : Type)) _ m

private theorem mpcMk_dvd_of_mod_eq_one
    (r : ℕ) (a : ℤ_[2])
    (h : (ofAdd (PadicInt.toZModPow r a) :
      Multiplicative (ZMod (2 ^ r))) = 1) :
    (2 : ℤ_[2]) ^ r ∣ a := by
  have hz : PadicInt.toZModPow r a = 0 := by
    exact congrArg Multiplicative.toAdd h
  have hker : a ∈ RingHom.ker (PadicInt.toZModPow r) := by
    rw [RingHom.mem_ker]
    exact hz
  rw [PadicInt.ker_toZModPow] at hker
  exact Ideal.mem_span_singleton.mp hker

private theorem mpcMk_torsion_eq_one_of_depth
    {r : ℕ} (hr : 2 ≤ r) {x : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) :
    (mTHom 2 0) (GQ2.SectionThree.abMk x) = 1 := by
  let f : ContinuousMonoidHom (DM 2 0 : Type)
      (Multiplicative (ZMod 2)) :=
    (mTHom 2 0).comp (mAbMkHom 2 0)
  have him : f x ∈ twoCentralSeries (Multiplicative (ZMod 2)) r :=
    map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun r
      ⟨x, hx, rfl⟩
  have him2 : f x ∈ twoCentralSeries (Multiplicative (ZMod 2)) 2 :=
    twoCentralSeries_antitone (G := Multiplicative (ZMod 2)) hr him
  obtain ⟨a, ha⟩ :=
    evenStratumShift_twoCentralSeries_le_pow 1 him2
  change f x = 1
  rw [← ha]
  obtain ⟨z, rfl⟩ : ∃ z : ZMod 2, ofAdd z = a :=
    ⟨toAdd a, rfl⟩
  change ofAdd z ^ 2 = 1
  rw [← ofAdd_nsmul, show (2 : ℕ) • z = 0 by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul],
    ofAdd_zero]

/-- The two head digits cut out the marked `B^2` line in every positive graded rung. -/
theorem mpcMk_exists_headCarrier_approx
    {r : ℕ} (hr : 2 ≤ r) {x : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hnu : mpcMkNuMod r x = 1)
    (hd : mpcMkDeltaDMod r x = 1) :
    ∃ y ∈ mpcSxKill r,
      x * y⁻¹ ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) := by
  let fB : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]) :=
    (mBHom 2 0).comp (mAbMkHom 2 0)
  let fT : ContinuousMonoidHom (DM 2 0 : Type)
      (Multiplicative (ZMod 2)) :=
    (mTHom 2 0).comp (mAbMkHom 2 0)
  let b : ℤ_[2] := toAdd (fB x)
  have hbdivLarge : (2 ^ (r - 1) : ℤ_[2]) ∣ b :=
    mpcMk_row_dvd fB hx
  obtain ⟨q, hq⟩ := hbdivLarge
  have hrsub : r - 1 = (r - 2) + 1 := by omega
  let b0 : ℤ_[2] := (2 : ℤ_[2]) ^ (r - 2) * q
  have hb : b = (2 : ℤ_[2]) * b0 := by
    rw [hq]
    dsimp only [b0]
    rw [hrsub, pow_succ']
    ring
  let c : ℤ_[2] := toAdd (nuM 2 0 (by omega) x)
  have hcdiv : (2 : ℤ_[2]) ^ r ∣ c := by
    apply mpcMk_dvd_of_mod_eq_one r c
    exact hnu
  obtain ⟨c0, hc⟩ := hcdiv
  let d : ℤ_[2] := toAdd (mpcMkDeltaD x)
  have hddiv : (2 : ℤ_[2]) ^ r ∣ d := by
    apply mpcMk_dvd_of_mod_eq_one r d
    exact hd
  obtain ⟨d0, hd0⟩ := hddiv
  let eC : (DM 2 0 : Type) :=
    zpowZtwo (isProP_DM 2 0) (dmC 2 0) ((2 : ℤ_[2]) ^ r * c0)
  let eD : (DM 2 0 : Type) :=
    zpowZtwo (isProP_DM 2 0) (dmD 2 0) ((2 : ℤ_[2]) ^ r * d0)
  let e : (DM 2 0 : Type) := eC * eD
  have heC : eC ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    exact mpcMk_zpow_pow_two_mem (dmC 2 0) r c0
  have heD : eD ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    exact mpcMk_zpow_pow_two_mem (dmD 2 0) r d0
  have he : e ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    Subgroup.mul_mem _ heC heD
  let z : (DM 2 0 : Type) := x * e⁻¹
  have hzdepth : z ∈ twoCentralSeries (DM 2 0 : Type) r := by
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _
      (twoCentralSeries_antitone (G := (DM 2 0 : Type)) (by omega) he))
  let yB : (DM 2 0 : Type) :=
    zpowZtwo (isProP_DM 2 0) (dmB 2 0 ^ 2) b0
  have hTB : (mTHom 2 0) (GQ2.SectionThree.abMk (dmB 2 0)) = 1 := by
    change mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1)) = 1
    rw [mTHom, mCoordHom_gen, coreMark_one]
  have hTC : (mTHom 2 0) (GQ2.SectionThree.abMk (dmC 2 0)) = 1 := by
    change mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2)) = 1
    rw [mTHom, mCoordHom_gen, coreMark_two]
  have hTD : (mTHom 2 0) (GQ2.SectionThree.abMk (dmD 2 0)) = 1 := by
    change mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3)) = 1
    rw [mTHom, mCoordHom_gen, coreMark_three]
  change fT (dmB 2 0) = 1 at hTB
  change fT (dmC 2 0) = 1 at hTC
  change fT (dmD 2 0) = 1 at hTD
  have hBB : fB (dmB 2 0) = ofAdd (1 : ℤ_[2]) := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1)) =
      ofAdd (1 : ℤ_[2])
    rw [mBHom, mCoordHom_gen, coreMark_one]
  have hBC : fB (dmC 2 0) = 1 := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2)) = 1
    rw [mBHom, mCoordHom_gen, coreMark_two]
  have hBD : fB (dmD 2 0) = 1 := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3)) = 1
    rw [mBHom, mCoordHom_gen, coreMark_three]
  have hTx := mpcMk_torsion_eq_one_of_depth hr hx
  change fT x = 1 at hTx
  have hab : GQ2.SectionThree.abMk z = GQ2.SectionThree.abMk yB := by
    apply mPhiHom_injective (by omega) 0
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · change toAdd (fT z) = toAdd (fT yB)
      dsimp only [z, yB, e, eC, eD]
      rw [map_mul fT, map_inv fT, map_mul fT,
        map_zpowZtwo (isProP_DM 2 0)
          GQ2.SectionThree.isProP_two_multZMod2,
        map_zpowZtwo (isProP_DM 2 0)
          GQ2.SectionThree.isProP_two_multZMod2,
        map_zpowZtwo (isProP_DM 2 0)
          GQ2.SectionThree.isProP_two_multZMod2,
        map_pow fT, hTB, hTC, hTD]
      simp only [one_pow, zpowZtwo_one_base, inv_one, mul_one]
      rw [hTx]
    · apply Prod.ext
      · change toAdd (fB z) = toAdd (fB yB)
        dsimp only [z, yB, e, eC, eD]
        rw [map_mul fB, map_inv fB, map_mul fB,
          toAdd_mul, toAdd_inv, toAdd_mul,
          toAdd_map_zpowZtwo (isProP_DM 2 0),
          toAdd_map_zpowZtwo (isProP_DM 2 0),
          toAdd_map_zpowZtwo (isProP_DM 2 0),
          map_pow fB, hBB, hBC, hBD]
        change b + -(2 ^ r * c0 * 0 + 2 ^ r * d0 * 0) =
          b0 * toAdd ((ofAdd (1 : ℤ_[2])) ^ 2)
        rw [toAdd_pow, toAdd_ofAdd, hb]
        ring
      · apply Prod.ext
        · change toAdd (mCHom (by omega) 0 (GQ2.SectionThree.abMk z)) =
            toAdd (mCHom (by omega) 0 (GQ2.SectionThree.abMk yB))
          rw [← mpcMkNu_eq_mCHom_apply,
            ← mpcMkNu_eq_mCHom_apply]
          dsimp only [z, yB, e, eC, eD]
          rw [map_mul (nuM 2 0 (by omega)),
            map_inv (nuM 2 0 (by omega)),
            map_mul (nuM 2 0 (by omega)),
            toAdd_mul, toAdd_inv, toAdd_mul,
            toAdd_map_zpowZtwo (isProP_DM 2 0),
            toAdd_map_zpowZtwo (isProP_DM 2 0),
            toAdd_map_zpowZtwo (isProP_DM 2 0),
            map_pow (nuM 2 0 (by omega)),
            nuM_dmB, nuM_dmC, nuM_dmD]
          change c + -(2 ^ r * c0 * toAdd (ofAdd (1 : ℤ_[2])) +
              2 ^ r * d0 * toAdd (ofAdd (0 : ℤ_[2]))) =
            b0 * toAdd ((ofAdd (0 : ℤ_[2])) ^ 2)
          rw [toAdd_pow, hc]
          simp only [toAdd_ofAdd]
          ring
        · apply Prod.ext
          · change toAdd (mpcMkDeltaD z) = toAdd (mpcMkDeltaD yB)
            dsimp only [z, yB, e, eC, eD]
            rw [map_mul mpcMkDeltaD, map_inv mpcMkDeltaD,
              map_mul mpcMkDeltaD,
              toAdd_mul, toAdd_inv, toAdd_mul,
              toAdd_map_zpowZtwo (isProP_DM 2 0),
              toAdd_map_zpowZtwo (isProP_DM 2 0),
              toAdd_map_zpowZtwo (isProP_DM 2 0),
              map_pow mpcMkDeltaD,
              mpcMkDeltaD_dmB, mpcMkDeltaD_dmC,
              mpcMkDeltaD_dmD]
            change d + -(2 ^ r * c0 * 0 + 2 ^ r * d0 * 1) =
              b0 * (2 : ℕ) • toAdd (1 : Multiplicative ℤ_[2])
            rw [toAdd_one, nsmul_zero, hd0]
            ring
          · exact funext fun i => absurd i.2 (by omega)
  have hyBtop : yB ∈ mpcSxMarked.topologicalClosure := by
    have hbase : dmB 2 0 ^ 2 ∈ mpcSxMarked :=
      Subgroup.subset_closure (Or.inl rfl)
    have hle : (Subgroup.closure ({dmB 2 0 ^ 2} :
        Set (DM 2 0 : Type))).topologicalClosure ≤
        mpcSxMarked.topologicalClosure :=
      Subgroup.topologicalClosure_mono ((Subgroup.closure_le _).2
        (by
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          simpa [ha] using hbase))
    exact hle (zpowZtwo_mem_topologicalClosure
      (isProP_DM 2 0) (dmB 2 0 ^ 2) b0)
  have hzcomm : z * yB⁻¹ ∈
      (commutator (DM 2 0 : Type)).topologicalClosure := by
    apply (QuotientGroup.eq_one_iff (z * yB⁻¹)).mp
    change GQ2.SectionThree.abMk (z * yB⁻¹) = 1
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hcommle : (commutator (DM 2 0 : Type)).topologicalClosure ≤
      mpcSxMarked.topologicalClosure := by
    apply Subgroup.topologicalClosure_mono
    rw [← mpcMkDerived_eq_commutator, mpcMkDerived, mpcSxMarked]
    apply Subgroup.closure_mono
    rintro a ⟨g, h, rfl⟩
    exact Or.inr ⟨g, h, rfl⟩
  have hztop : z ∈ mpcSxMarked.topologicalClosure := by
    have hz' := Subgroup.mul_mem _ (hcommle hzcomm) hyBtop
    simpa [z, yB] using hz'
  obtain ⟨y, hy, hzy⟩ := mpcMk_exists_sxKill_approx hzdepth hztop
  refine ⟨y, hy, ?_⟩
  have heconj : y * e * y⁻¹ ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    (twoCentralSeries_normal (DM 2 0 : Type) (r + 1)).conj_mem e he y
  have hout := Subgroup.mul_mem (twoCentralSeries (DM 2 0 : Type) (r + 1))
    hzy heconj
  have heq : (z * y⁻¹) * (y * e * y⁻¹) = x * y⁻¹ := by
    dsimp only [z]
    group
  rw [heq] at hout
  exact hout

/-- The corrected two-coordinate obstruction reflects an unrestricted source cost to a
source whose square-bearing head is marked. -/
theorem mpcMk_headReflection
    (r : ℕ) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MpcMkHeadReflection r hr t n := by
  intro u hu
  obtain ⟨hnu, hd⟩ := mpcMk_headDigits_of_rawObstruction hr t n u hu
  obtain ⟨y, hy, huy⟩ :=
    mpcMk_exists_headCarrier_approx hr u.1.2 hnu hd
  let v : MpcMkHeadMarkedSource r :=
    (⟨y, hy⟩, u.2.1, u.2.2.1, u.2.2.2)
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change (mpcMkRawCost r hr t n (mpcMkHeadMarkedSource r v)).1 =
    (mpcMkRawCost r hr t n u).1
  rw [mpcMkRawCost_apply, mpcMkRawCost_apply]
  symm
  exact mpcMk_rawCost_congr_of_mod_succ hr t n
    u.1 u.2.1 u.2.2.1 u.2.2.2
    y u.2.1 u.2.2.1 u.2.2.2
    u.1.2 u.2.1.2 u.2.2.1.2 u.2.2.2.2
    hy.2 u.2.1.2 u.2.2.1.2 u.2.2.2.2
    huy (by simp) (by simp) (by simp)

/-! ## Axiom pins -/

#print axioms mpcMkRawSourceCorrection
#print axioms mpcMkRawCost
#print axioms mpcMkRawCost_base_indep
#print axioms mpcMkRawObstruction_base_indep
#print axioms MpcMkSourceExact
#print axioms MpcMkHeadReflection
#print axioms MpcMkHeadCompletion
#print axioms mpcMk_sourceExact_of_headReflection_of_headCompletion
#print axioms mpcMk_sourceExact_iff_base
#print axioms mpcMk_mem_markedCostRange_of_sourceExact
#print axioms mpcMkNu_eq_mCHom
#print axioms mpcMk_headDigits_of_rawObstruction
#print axioms mpcMk_exists_headCarrier_approx
#print axioms mpcMk_headReflection

end

end GQ2.Dyadic.Instances.MpcMk
