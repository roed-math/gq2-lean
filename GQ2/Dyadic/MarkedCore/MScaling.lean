/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
module

public import GQ2.Dyadic.MarkedCore.CoreMixM
public import GQ2.Foundations.Axioms

@[expose] public section

/-!
# The compact `M` unit-scaling automorphism

At handle level zero, the two B8 peripheral triples can be spliced canonically.  Retaining the
actual `deltaHom` conjugators, rather than merely their existence, supplies the closed-subgroup
support needed for the Frattini and orientation arguments.
-/

open Multiplicative

namespace GQ2
namespace Dyadic
namespace MarkedCore

open scoped GQ2

section Construction

variable (R : PeripheralCyclotomicAction) (α : ℕ) (u : ℤ_[2]ˣ)

local notation "hP" => isProP_DM α 0
local notation "A" => dmA α 0
local notation "B" => dmB α 0
local notation "C" => dmC α 0
local notation "D" => dmD α 0
local notation "W" => mHead A B

private theorem mScale_conjP_inv {G : Type*} [Group G] (x c : G) :
    conjP x⁻¹ c = (conjP x c)⁻¹ := by
  simp only [conjP]
  group

private theorem mScale_conjP_pow {G : Type*} [Group G] (x c : G) (n : ℕ) :
    conjP x c ^ n = conjP (x ^ n) c := by
  induction n with
  | zero => simp [conjP]
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [conjP]
      group

/-! The three canonical conjugators for each of the nested peripheral triples. -/

noncomputable def mScaleIP : DM α 0 := peripheralScaleP R hP A (conjP A B) u
noncomputable def mScaleIT : DM α 0 := peripheralScaleT R hP A (conjP A B) u
noncomputable def mScaleIC : DM α 0 := peripheralScaleC R hP A (conjP A B) u

noncomputable def mScaleOP : DM α 0 := peripheralScaleP R hP W (C ^ (2 ^ α - 1)) u
noncomputable def mScaleOT : DM α 0 := peripheralScaleT R hP W (C ^ (2 ^ α - 1)) u
noncomputable def mScaleOC : DM α 0 := peripheralScaleC R hP W (C ^ (2 ^ α - 1)) u

/-- The connector which identifies the inner transported head with the outer transported head. -/
noncomputable def mScaleQ : DM α 0 := (mScaleIC R α u)⁻¹ * mScaleOP R α u

/-- The four images defining the compact `M` scaling endomorphism. -/
noncomputable def mScaleMark : Fin (coreRank 0) → DM α 0 :=
  coreMark
    (conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u * mScaleQ R α u))
    ((mScaleQ R α u)⁻¹ * ((mScaleIP R α u)⁻¹ * B * mScaleIT R α u) *
      mScaleQ R α u)
    (conjP (zpowZtwo hP C (u : ℤ_[2])) (mScaleOT R α u))
    ((mScaleOT R α u)⁻¹ * D * mScaleOC R α u)

private theorem mScale_inner_identity :
    conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u) *
        conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2])) (mScaleIT R α u) *
        conjP (zpowZtwo hP W⁻¹ (u : ℤ_[2])) (mScaleIC R α u) = 1 :=
  peripheralTriple_scaling_canonical R hP (mWord_innerTriple A B) u

private theorem mScale_outer_identity :
    conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleOP R α u) *
        conjP (zpowZtwo hP (C ^ (2 ^ α - 1)) (u : ℤ_[2])) (mScaleOT R α u) *
        conjP (zpowZtwo hP (conjP C D) (u : ℤ_[2])) (mScaleOC R α u) = 1 := by
  apply peripheralTriple_scaling_canonical R hP
  simpa [handleWord, mRelWord_triple] using dm_outer_triple α 0

@[simp] theorem mScaleMark_zero :
    mScaleMark R α u 0 =
      conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u * mScaleQ R α u) := by
  rw [mScaleMark, coreMark_zero]

@[simp] theorem mScaleMark_one :
    mScaleMark R α u 1 =
      (mScaleQ R α u)⁻¹ * ((mScaleIP R α u)⁻¹ * B * mScaleIT R α u) *
        mScaleQ R α u := by
  rw [mScaleMark, coreMark_one]

@[simp] theorem mScaleMark_two :
    mScaleMark R α u 2 =
      conjP (zpowZtwo hP C (u : ℤ_[2])) (mScaleOT R α u) := by
  rw [mScaleMark, coreMark_two]

@[simp] theorem mScaleMark_three :
    mScaleMark R α u 3 = (mScaleOT R α u)⁻¹ * D * mScaleOC R α u := by
  rw [mScaleMark, coreMark_three]

/-- The inner B8 identity makes the head of the new marking exactly the outer transported head. -/
theorem mHead_mScaleMark :
    mHead (mScaleMark R α u 0) (mScaleMark R α u 1) =
      conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleOP R α u) := by
  rw [mHead, mScaleMark_zero, mScaleMark_one]
  have hi := mScale_inner_identity R α u
  rw [mZpowZtwo_inv, mScale_conjP_inv] at hi
  have hprod :
      conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u) *
          conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2])) (mScaleIT R α u) =
        conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleIC R α u) := by
    apply eq_of_mul_inv_eq_one
    exact hi
  have hsecond :
      conjP
          (conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u * mScaleQ R α u))
          ((mScaleQ R α u)⁻¹ * ((mScaleIP R α u)⁻¹ * B * mScaleIT R α u) *
            mScaleQ R α u) =
        conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2]))
          (mScaleIT R α u * mScaleQ R α u) := by
    rw [← mConjP_zpowZtwo hP A B (u : ℤ_[2])]
    simp only [conjP]
    group
  rw [hsecond]
  have hcombine :
      conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u * mScaleQ R α u) *
          conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2]))
            (mScaleIT R α u * mScaleQ R α u) =
        conjP
          (conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleIP R α u) *
            conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2])) (mScaleIT R α u))
          (mScaleQ R α u) := by
    simp only [conjP]
    group
  rw [hcombine, hprod]
  simp only [mScaleQ, conjP]
  group

/-- The new `C` natural power is the transported middle factor of the outer triple. -/
theorem mScaleMark_two_pow :
    mScaleMark R α u 2 ^ (2 ^ α - 1) =
      conjP (zpowZtwo hP (C ^ (2 ^ α - 1)) (u : ℤ_[2])) (mScaleOT R α u) := by
  rw [mScaleMark_two, mScale_conjP_pow, mZpowZtwo_pow]

/-- The new `C^D` is the transported third factor of the outer triple. -/
theorem conjP_mScaleMark_two_three :
    conjP (mScaleMark R α u 2) (mScaleMark R α u 3) =
      conjP (zpowZtwo hP (conjP C D) (u : ℤ_[2])) (mScaleOC R α u) := by
  rw [mScaleMark_two, mScaleMark_three,
    ← mConjP_zpowZtwo hP C D (u : ℤ_[2])]
  simp only [conjP]
  group

/-- The assembled four-generator marking satisfies the `M_α` relator. -/
theorem mRelWord_mScaleMark : mRelWord α (mScaleMark R α u) = 1 := by
  rw [mRelWord_triple, mHead_mScaleMark, mScaleMark_two_pow,
    conjP_mScaleMark_two_three]
  simpa [handleWord] using mScale_outer_identity R α u

/-- The compact `M` scaling endomorphism supplied by the two canonical B8 triples. -/
noncomputable def mScaleHom : ContinuousMonoidHom (DM α 0 : Type) (DM α 0 : Type) :=
  mLiftHom α 0 hP (mScaleMark R α u) (mRelWord_mScaleMark R α u)

@[simp] theorem mScaleHom_gen (i : Fin (coreRank 0)) :
    mScaleHom R α u (dmGen α 0 i) = mScaleMark R α u i :=
  mLiftHom_gen _ _ _ _ _ _

/-! ## Closed-subgroup support and orientation -/

private theorem mScale_topClosure_le_ker {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (q : ContinuousMonoidHom G H) {S : Set G} (hs : ∀ x ∈ S, q x = 1) :
    (Subgroup.closure S).topologicalClosure ≤ q.toMonoidHom.ker := by
  refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr hs) ?_
  have hker : (q.toMonoidHom.ker : Set G) = q ⁻¹' {1} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [hker]
  exact isClosed_singleton.preimage q.continuous_toFun

theorem mScaleIP_mem_inner :
    mScaleIP R α u ∈ (Subgroup.closure ({A, conjP A B} : Set (DM α 0))).topologicalClosure := by
  simpa [mScaleIP, peripheralScaleP] using
    deltaHom_mem_topologicalClosure hP A (conjP A B) (R.cP u)

theorem mScaleIT_mem_inner :
    mScaleIT R α u ∈ (Subgroup.closure ({A, conjP A B} : Set (DM α 0))).topologicalClosure := by
  simpa [mScaleIT, peripheralScaleT] using
    deltaHom_mem_topologicalClosure hP A (conjP A B) (R.cT u)

theorem mScaleIC_mem_inner :
    mScaleIC R α u ∈ (Subgroup.closure ({A, conjP A B} : Set (DM α 0))).topologicalClosure := by
  simpa [mScaleIC, peripheralScaleC] using
    deltaHom_mem_topologicalClosure hP A (conjP A B) (R.cC u)

theorem mScaleOP_mem_outer :
    mScaleOP R α u ∈
      (Subgroup.closure ({W, C ^ (2 ^ α - 1)} : Set (DM α 0))).topologicalClosure := by
  simpa [mScaleOP, peripheralScaleP] using
    deltaHom_mem_topologicalClosure hP W (C ^ (2 ^ α - 1)) (R.cP u)

theorem mScaleOT_mem_outer :
    mScaleOT R α u ∈
      (Subgroup.closure ({W, C ^ (2 ^ α - 1)} : Set (DM α 0))).topologicalClosure := by
  simpa [mScaleOT, peripheralScaleT] using
    deltaHom_mem_topologicalClosure hP W (C ^ (2 ^ α - 1)) (R.cT u)

theorem mScaleOC_mem_outer :
    mScaleOC R α u ∈
      (Subgroup.closure ({W, C ^ (2 ^ α - 1)} : Set (DM α 0))).topologicalClosure := by
  simpa [mScaleOC, peripheralScaleC] using
    deltaHom_mem_topologicalClosure hP W (C ^ (2 ^ α - 1)) (R.cC u)

private theorem chiM_one_of_mem_inner {x : DM α 0}
    (hx : x ∈ (Subgroup.closure ({A, conjP A B} : Set (DM α 0))).topologicalClosure) :
    chiM α 0 x = 1 := by
  have hle := mScale_topClosure_le_ker (chiM α 0) (S := {A, conjP A B}) (by
    rintro y (rfl | rfl)
    · exact chiM_dmA α 0
    · rw [mChar_conjP, chiM_dmA])
  exact MonoidHom.mem_ker.mp (hle hx)

private theorem chiM_one_of_mem_outer {x : DM α 0}
    (hx : x ∈
      (Subgroup.closure ({W, C ^ (2 ^ α - 1)} : Set (DM α 0))).topologicalClosure) :
    chiM α 0 x = 1 := by
  have hle := mScale_topClosure_le_ker (chiM α 0)
    (S := {W, C ^ (2 ^ α - 1)}) (by
      rintro y (rfl | rfl)
      · simp [mHead, mChar_conjP]
      · simp)
  exact MonoidHom.mem_ker.mp (hle hx)

@[simp] theorem chiM_mScaleIP : chiM α 0 (mScaleIP R α u) = 1 :=
  chiM_one_of_mem_inner α (mScaleIP_mem_inner R α u)

@[simp] theorem chiM_mScaleIT : chiM α 0 (mScaleIT R α u) = 1 :=
  chiM_one_of_mem_inner α (mScaleIT_mem_inner R α u)

@[simp] theorem chiM_mScaleIC : chiM α 0 (mScaleIC R α u) = 1 :=
  chiM_one_of_mem_inner α (mScaleIC_mem_inner R α u)

@[simp] theorem chiM_mScaleOP : chiM α 0 (mScaleOP R α u) = 1 :=
  chiM_one_of_mem_outer α (mScaleOP_mem_outer R α u)

@[simp] theorem chiM_mScaleOT : chiM α 0 (mScaleOT R α u) = 1 :=
  chiM_one_of_mem_outer α (mScaleOT_mem_outer R α u)

@[simp] theorem chiM_mScaleOC : chiM α 0 (mScaleOC R α u) = 1 :=
  chiM_one_of_mem_outer α (mScaleOC_mem_outer R α u)

@[simp] theorem chiM_mScaleQ : chiM α 0 (mScaleQ R α u) = 1 := by
  simp [mScaleQ]

@[simp] theorem chiM_mScaleMark_zero :
    chiM α 0 (mScaleMark R α u 0) = chiM α 0 A := by
  rw [mScaleMark_zero, mChar_conjP,
    map_zpowZtwo hP isProP_two_unitsPadicInt (chiM α 0), chiM_dmA,
    zpowZtwo_one_base]

@[simp] theorem chiM_mScaleMark_one :
    chiM α 0 (mScaleMark R α u 1) = chiM α 0 B := by
  simp [mScaleMark_one]

@[simp] theorem chiM_mScaleMark_two :
    chiM α 0 (mScaleMark R α u 2) = chiM α 0 C := by
  rw [mScaleMark_two, mChar_conjP,
    map_zpowZtwo hP isProP_two_unitsPadicInt (chiM α 0), chiM_dmC,
    zpowZtwo_one_base]

@[simp] theorem chiM_mScaleMark_three :
    chiM α 0 (mScaleMark R α u 3) = chiM α 0 D := by
  simp [mScaleMark_three]

@[simp] theorem mScaleHom_A : mScaleHom R α u A = mScaleMark R α u 0 := by
  rw [dmA, mScaleHom_gen]

@[simp] theorem mScaleHom_B : mScaleHom R α u B = mScaleMark R α u 1 := by
  rw [dmB, mScaleHom_gen]

@[simp] theorem mScaleHom_C : mScaleHom R α u C = mScaleMark R α u 2 := by
  rw [dmC, mScaleHom_gen]

@[simp] theorem mScaleHom_D : mScaleHom R α u D = mScaleMark R α u 3 := by
  rw [dmD, mScaleHom_gen]

theorem chiM_mScaleHom (x : DM α 0) : chiM α 0 (mScaleHom R α u x) = chiM α 0 x := by
  have hext := dm_hom_ext ((chiM α 0).comp (mScaleHom R α u)) (chiM α 0) (fun i => by
    change chiM α 0 (mScaleHom R α u (dmGen α 0 i)) = chiM α 0 (dmGen α 0 i)
    rw [mScaleHom_gen]
    fin_cases i
    · change chiM α 0 (mScaleMark R α u 0) = chiM α 0 A
      exact chiM_mScaleMark_zero R α u
    · change chiM α 0 (mScaleMark R α u 1) = chiM α 0 B
      exact chiM_mScaleMark_one R α u
    · change chiM α 0 (mScaleMark R α u 2) = chiM α 0 C
      exact chiM_mScaleMark_two R α u
    · change chiM α 0 (mScaleMark R α u 3) = chiM α 0 D
      exact chiM_mScaleMark_three R α u)
  exact DFunLike.congr_fun hext x

/-! ## Frattini surjectivity -/

private lemma mScale_discreteTopology_quotient (M : OpenNormalSubgroup (DM α 0 : Type)) :
    DiscreteTopology ((DM α 0 : Type) ⧸ M.toSubgroup) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hpre : (QuotientGroup.mk : (DM α 0 : Type) → (DM α 0 : Type) ⧸ M.toSubgroup) ⁻¹' {1}
      = (M.toSubgroup : Set (DM α 0 : Type)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      QuotientGroup.eq_one_iff]
  rw [← (QuotientGroup.isQuotientMap_mk M.toSubgroup).isOpen_preimage, hpre]
  exact M.isOpen'

private lemma mScale_zpowZtwo_eq_self_of_sq_eq_one {P : Type} [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] (hpro : IsProP 2 P) {x : P} (hx : x ^ 2 = 1)
    (v : ℤ_[2]ˣ) : zpowZtwo hpro x (v : ℤ_[2]) = x := by
  obtain ⟨w, hw⟩ := two_dvd_val_sub_one v
  have hv : (v : ℤ_[2]) = 1 + 2 * w := by rw [← hw]; ring
  rw [hv, zpowZtwo_add]
  have h2w : zpowZtwo hpro x (2 * w) = 1 := by
    have hcomp := zpowZtwo_zpowZtwo hpro x (2 : ℤ_[2]) w
    have h2 : zpowZtwo hpro x (2 : ℤ_[2]) = x ^ (2 : ℕ) := by
      have hcast : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
      rw [hcast, zpowZtwo_natCast]
    rw [h2, hx, zpowZtwo_one_base] at hcomp
    exact hcomp.symm
  rw [h2w, mul_one, zpowZtwo_one_exp]

private lemma mScale_quotient_mul_comm (M : OpenNormalSubgroup (DM α 0 : Type))
    (hM : M.toSubgroup.index = 2) (z w : (DM α 0 : Type) ⧸ M.toSubgroup) : z * w = w * z := by
  have : Finite ((DM α 0 : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM α 0 : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isCyclic_of_prime_card (p := 2) hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (DM α 0 : Type) ⧸ M.toSubgroup)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg w)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

private lemma mScale_quotient_sq_eq_one (M : OpenNormalSubgroup (DM α 0 : Type))
    (hM : M.toSubgroup.index = 2) (z : (DM α 0 : Type) ⧸ M.toSubgroup) : z ^ 2 = 1 := by
  have : Finite ((DM α 0 : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM α 0 : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have hdvd : orderOf z ∣ 2 := hcard ▸ orderOf_dvd_natCard z
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private lemma mScale_quotient_map_conjP (M : OpenNormalSubgroup (DM α 0 : Type))
    (hM : M.toSubgroup.index = 2) (x c : DM α 0) :
    QuotientGroup.mk' M.toSubgroup (conjP x c) = QuotientGroup.mk' M.toSubgroup x := by
  rw [conjP, map_mul, map_mul, map_inv]
  calc
    (QuotientGroup.mk' M.toSubgroup c)⁻¹ * QuotientGroup.mk' M.toSubgroup x *
          QuotientGroup.mk' M.toSubgroup c =
        QuotientGroup.mk' M.toSubgroup x * (QuotientGroup.mk' M.toSubgroup c)⁻¹ *
          QuotientGroup.mk' M.toSubgroup c := by
            rw [mScale_quotient_mul_comm α M hM
              ((QuotientGroup.mk' M.toSubgroup c)⁻¹)]
    _ = QuotientGroup.mk' M.toSubgroup x := by rw [mul_assoc, inv_mul_cancel, mul_one]

private lemma mScale_quotient_map_zpowZtwo (M : OpenNormalSubgroup (DM α 0 : Type))
    (hM : M.toSubgroup.index = 2) (x : DM α 0) (v : ℤ_[2]ˣ) :
    QuotientGroup.mk' M.toSubgroup (zpowZtwo hP x (v : ℤ_[2])) =
      QuotientGroup.mk' M.toSubgroup x := by
  letI := mScale_discreteTopology_quotient α M
  letI : Finite ((DM α 0 : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hpro : IsProP 2 ((DM α 0 : Type) ⧸ M.toSubgroup) := by
    refine isProP_of_isPGroup (IsPGroup.of_card (n := 1) ?_)
    rw [← Subgroup.index_eq_card, hM, pow_one]
  have hnat := map_zpowZtwo hP hpro
    (⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ :
      ContinuousMonoidHom (DM α 0 : Type) ((DM α 0 : Type) ⧸ M.toSubgroup)) x (v : ℤ_[2])
  calc
    QuotientGroup.mk' M.toSubgroup (zpowZtwo hP x (v : ℤ_[2])) =
        zpowZtwo hpro (QuotientGroup.mk' M.toSubgroup x) (v : ℤ_[2]) := hnat
    _ = QuotientGroup.mk' M.toSubgroup x :=
      mScale_zpowZtwo_eq_self_of_sq_eq_one hpro
        (mScale_quotient_sq_eq_one α M hM _) v

theorem dm_topologicallyFinGen_zero :
    ∃ s : Finset (DM α 0 : Type),
      (Subgroup.closure (s : Set (DM α 0 : Type))).topologicalClosure = ⊤ := by
  have hfin : (Set.range (dmGen α 0)).Finite := Set.finite_range _
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact dm_topGen α 0

/-- The B8 scaling endomorphism is surjective by the pro-2 Frattini criterion. -/
theorem mScaleHom_surjective : Function.Surjective (mScaleHom R α u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective hP (mScaleHom R α u) ?_
  intro M hM
  letI := mScale_discreteTopology_quotient α M
  letI : Finite ((DM α 0 : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM α 0 : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  letI : Fact (Nat.Prime (Nat.card ((DM α 0 : Type) ⧸ M.toSubgroup))) :=
    ⟨hcard ▸ Nat.prime_two⟩
  let q : ContinuousMonoidHom (DM α 0 : Type) ((DM α 0 : Type) ⧸ M.toSubgroup) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  let c : (DM α 0 : Type) →* ((DM α 0 : Type) ⧸ M.toSubgroup) :=
    (QuotientGroup.mk' M.toSubgroup).comp (mScaleHom R α u).toMonoidHom
  rcases c.range.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · exfalso
    have hval : ∀ g : DM α 0, QuotientGroup.mk' M.toSubgroup (mScaleHom R α u g) = 1 := by
      intro g
      have hg : c g ∈ c.range := ⟨g, rfl⟩
      rw [hbot] at hg
      exact Subgroup.mem_bot.mp hg
    have hqA : QuotientGroup.mk' M.toSubgroup A = 1 := by
      have hg := hval A
      rw [mScaleHom_A, mScaleMark_zero, mScale_quotient_map_conjP α M hM,
        mScale_quotient_map_zpowZtwo α M hM] at hg
      exact hg
    have hqC : QuotientGroup.mk' M.toSubgroup C = 1 := by
      have hg := hval C
      rw [mScaleHom_C, mScaleMark_two, mScale_quotient_map_conjP α M hM,
        mScale_quotient_map_zpowZtwo α M hM] at hg
      exact hg
    have hkerInner := mScale_topClosure_le_ker q (S := {A, conjP A B}) (by
      rintro x (rfl | rfl)
      · change QuotientGroup.mk' M.toSubgroup A = 1
        exact hqA
      · change QuotientGroup.mk' M.toSubgroup (conjP A B) = 1
        rw [mScale_quotient_map_conjP α M hM]
        exact hqA)
    have hqIP : QuotientGroup.mk' M.toSubgroup (mScaleIP R α u) = 1 :=
      MonoidHom.mem_ker.mp (hkerInner (mScaleIP_mem_inner R α u))
    have hqIT : QuotientGroup.mk' M.toSubgroup (mScaleIT R α u) = 1 :=
      MonoidHom.mem_ker.mp (hkerInner (mScaleIT_mem_inner R α u))
    have hqB : QuotientGroup.mk' M.toSubgroup B = 1 := by
      have hg := hval B
      rw [mScaleHom_B, mScaleMark_one] at hg
      simp only [map_mul, map_inv, hqIP, hqIT, inv_one, one_mul, mul_one] at hg
      have hconj := mScale_quotient_map_conjP α M hM B (mScaleQ R α u)
      simp only [conjP, map_mul, map_inv] at hconj
      exact hconj.symm.trans hg
    have hqW : QuotientGroup.mk' M.toSubgroup W = 1 := by
      rw [mHead, map_mul, mScale_quotient_map_conjP α M hM, hqA, one_mul]
    have hqCpow : QuotientGroup.mk' M.toSubgroup (C ^ (2 ^ α - 1)) = 1 := by
      rw [map_pow, hqC, one_pow]
    have hkerOuter := mScale_topClosure_le_ker q
      (S := {W, C ^ (2 ^ α - 1)}) (by
        rintro x (rfl | rfl)
        · exact hqW
        · exact hqCpow)
    have hqOT : QuotientGroup.mk' M.toSubgroup (mScaleOT R α u) = 1 :=
      MonoidHom.mem_ker.mp (hkerOuter (mScaleOT_mem_outer R α u))
    have hqOC : QuotientGroup.mk' M.toSubgroup (mScaleOC R α u) = 1 :=
      MonoidHom.mem_ker.mp (hkerOuter (mScaleOC_mem_outer R α u))
    have hqD : QuotientGroup.mk' M.toSubgroup D = 1 := by
      have hg := hval D
      rw [mScaleHom_D, mScaleMark_three, map_mul, map_mul, map_inv, hqOT, hqOC,
        inv_one, one_mul, mul_one] at hg
      exact hg
    have hkerAll := mScale_topClosure_le_ker q (S := Set.range (dmGen α 0)) (by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · change QuotientGroup.mk' M.toSubgroup A = 1
        exact hqA
      · change QuotientGroup.mk' M.toSubgroup B = 1
        exact hqB
      · change QuotientGroup.mk' M.toSubgroup C = 1
        exact hqC
      · change QuotientGroup.mk' M.toSubgroup D = 1
        exact hqD)
    have : Nontrivial ((DM α 0 : Type) ⧸ M.toSubgroup) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    obtain ⟨z, hz⟩ := exists_ne (1 : (DM α 0 : Type) ⧸ M.toSubgroup)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
    refine hz (MonoidHom.mem_ker.mp (hkerAll ?_))
    rw [dm_topGen]
    exact Subgroup.mem_top g
  · intro z
    have hz : z ∈ c.range := htop ▸ Subgroup.mem_top z
    exact hz

/-- The compact `M` unit scaling is a continuous automorphism. -/
noncomputable def mScaleEquiv : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type) :=
  continuousMulEquivOfBijective (mScaleHom R α u)
    ⟨profinite_hopfian (dm_topologicallyFinGen_zero α) (mScaleHom R α u)
        (mScaleHom_surjective R α u),
      mScaleHom_surjective R α u⟩

@[simp] theorem mScaleEquiv_apply (x : DM α 0) :
    mScaleEquiv R α u x = mScaleHom R α u x := rfl

/-- The scaling automorphism preserves the canonical orientation. -/
theorem chiM_mScaleEquiv (x : DM α 0) :
    chiM α 0 (mScaleEquiv R α u x) = chiM α 0 x := by
  rw [mScaleEquiv_apply]
  exact chiM_mScaleHom R α u x

/-- Every additive `ℤ₂`-character sees the requested unit scaling on the `C` row. -/
theorem mScaleEquiv_C_row
    (f : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2])) :
    toAdd (f (mScaleEquiv R α u C)) = (u : ℤ_[2]) * toAdd (f C) := by
  rw [mScaleEquiv_apply, mScaleHom_C, mScaleMark_two, map_conjP_comm,
    toAdd_map_zpowZtwo]

end Construction

/-! ## Discharge of the compact scaling binder -/

/-- An explicit peripheral cyclotomic action supplies the complete compact `M` scaling face.
This theorem keeps the B8 dependency as a parameter, so its axiom footprint is standard only. -/
theorem mScalingHypothesis_zero_of_peripheral (R : PeripheralCyclotomicAction) (α : ℕ) :
    MScalingHypothesis α 0 := by
  intro u
  exact ⟨mScaleEquiv R α u, chiM_mScaleEquiv R α u, mScaleEquiv_C_row R α u⟩

/-- The preferred compact scaling discharge, consuming the repository's existing B8 witness. -/
theorem mScalingHypothesis_zero (α : ℕ) : MScalingHypothesis α 0 :=
  mScalingHypothesis_zero_of_peripheral peripheralCyclotomicAction α

end MarkedCore
end Dyadic
end GQ2
