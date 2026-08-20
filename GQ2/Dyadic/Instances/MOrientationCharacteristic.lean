/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MOrientationNaturalityBoundary
import GQ2.Roe.MarkedMatching

/-!
# Characteristic orientation of the general M core

The arbitrary-rank master crossed derivations separate every generator modulo two.
Their evaluation matrix stays invertible after every continuous core automorphism.
Consequently every pulled-back canonical character satisfies the complete Fox-row
descent condition, including all handle rows, and hence equals the canonical `chiM`.

This proves characteristic orientation uniformly for every `DM alpha h`; no
rank-by-rank or quadratic-class argument enters.
-/

namespace GQ2.Dyadic.Instances.MOrientationCharacteristic

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative FoxH
open GQ2.SectionThree
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MOrientationNaturalityBoundary
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary

noncomputable local instance instTopWordLift : TopologicalSpace (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  TopologicalSpace.induced (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) inferInstance

private lemma isInducing_equivProd :
    Topology.IsInducing (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) :=
  ⟨rfl⟩

private noncomputable def wordLiftHomeo : WordLift ℤ_[2] ℤ_[2]ˣ ≃ₜ ℤ_[2] × ℤ_[2]ˣ :=
  (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)).toHomeomorphOfIsInducing
    isInducing_equivProd

private lemma continuous_wordLift_u : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ => p.u :=
  continuous_fst.comp wordLiftHomeo.continuous

private lemma continuous_wordLift_g : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ => p.g :=
  continuous_snd.comp wordLiftHomeo.continuous

private lemma continuous_wordLift_mk {X : Type*} [TopologicalSpace X]
    {u : X → ℤ_[2]} {g : X → ℤ_[2]ˣ} (hu : Continuous u) (hg : Continuous g) :
    Continuous fun x => (⟨u x, g x⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
  rw [isInducing_equivProd.continuous_iff]
  exact hu.prodMk hg

local instance instTopGroupWordLift : IsTopologicalGroup (WordLift ℤ_[2] ℤ_[2]ˣ) where
  continuous_mul := by
    have : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ × WordLift ℤ_[2] ℤ_[2]ˣ =>
        (⟨p.1.u + p.1.g • p.2.u, p.1.g * p.2.g⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
      refine continuous_wordLift_mk (Continuous.add ?_ ?_) ?_
      · exact continuous_wordLift_u.comp continuous_fst
      · simp only [Units.smul_def, smul_eq_mul]
        exact (Units.continuous_val.comp (continuous_wordLift_g.comp continuous_fst)).mul
          (continuous_wordLift_u.comp continuous_snd)
      · exact (continuous_wordLift_g.comp continuous_fst).mul
          (continuous_wordLift_g.comp continuous_snd)
    exact this
  continuous_inv := by
    have : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ =>
        (⟨-(p.g⁻¹ • p.u), p.g⁻¹⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
      refine continuous_wordLift_mk (Continuous.neg ?_) continuous_wordLift_g.inv
      simp only [Units.smul_def, smul_eq_mul]
      exact (Units.continuous_val.comp continuous_wordLift_g.inv).mul continuous_wordLift_u
    exact this

local instance : CompactSpace (WordLift ℤ_[2] ℤ_[2]ˣ) := wordLiftHomeo.symm.compactSpace
local instance : T2Space (WordLift ℤ_[2] ℤ_[2]ˣ) := wordLiftHomeo.isEmbedding.t2Space
local instance : TotallyDisconnectedSpace (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  wordLiftHomeo.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

private theorem isProP_two_wordLift' : IsProP 2 (WordLift ℤ_[2] ℤ_[2]ˣ) := by
  exact GQ2.isProP_two_wordLift

/-- The arbitrary-rank master crossed derivation on `DM`. -/
noncomputable def masterH {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) :
    ContinuousMonoidHom (DM alpha h : Type) (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  mLiftHom alpha h isProP_two_wordLift' (mMasterMark alpha c)
    (mRelWord_mMasterMark halpha c)

@[simp] theorem masterH_gen {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) (i : Fin (coreRank h)) :
    masterH halpha c (dmGen alpha h i) = mMasterMark alpha c i := by
  simp [masterH]

private def wordLiftBaseHom : ContinuousMonoidHom (WordLift ℤ_[2] ℤ_[2]ˣ) ℤ_[2]ˣ where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_wordLift_g

theorem masterH_base {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) (x : DM alpha h) :
    (masterH halpha c x).g = chiM alpha h x := by
  have heq : wordLiftBaseHom.comp (masterH halpha c) = chiM alpha h := by
    apply dm_hom_ext
    intro i
    change (masterH halpha c (dmGen alpha h i)).g = chiM alpha h (dmGen alpha h i)
    rw [masterH_gen]
    change coreMark 1 (-1) 1 (mUnit alpha) i = chiM alpha h (dmGen alpha h i)
    rw [chiM, mLiftHom_gen]
  exact DFunLike.congr_fun heq x

theorem masterH_mul_u {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) (x y : DM alpha h) :
    (masterH halpha c (x * y)).u =
      (masterH halpha c x).u + chiM alpha h x • (masterH halpha c y).u := by
  rw [map_mul, WordLift.mul_u, masterH_base]

/-- Linear contraction of the basis masters. -/
noncomputable def masterContract {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) :
    (DM alpha h : Type) →* WordLift ℤ_[2] ℤ_[2]ˣ where
  toFun x := ⟨∑ j, c j * (masterH halpha (Pi.single j 1) x).u, chiM alpha h x⟩
  map_one' := by
    refine WordLift.ext ?_ ?_
    · simp
    · exact map_one _
  map_mul' x y := by
    refine WordLift.ext ?_ ?_
    · simp only [masterH_mul_u, WordLift.mul_u, Units.smul_def, smul_eq_mul,
        Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    · exact map_mul _ _ _

@[simp] theorem masterContract_apply_u {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) (x : DM alpha h) :
    (masterContract halpha c x).u =
      ∑ j, c j * (masterH halpha (Pi.single j 1) x).u := rfl

@[simp] theorem masterContract_apply_g {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (c : Fin (coreRank h) → ℤ_[2]) (x : DM alpha h) :
    (masterContract halpha c x).g = chiM alpha h x := rfl

local instance instTopZModTwo : TopologicalSpace (ZMod (2 ^ 1)) := ⊥
local instance : DiscreteTopology (ZMod (2 ^ 1)) := ⟨rfl⟩

private lemma continuous_toZModPow_one : Continuous (PadicInt.toZModPow (p := 2) 1) := by
  rw [continuous_def]
  intro T _
  exact isOpen_preimage_toZModPow 1 T

private lemma zmod2_eq_one_of_isUnit {z : ZMod (2 ^ 1)} (hz : IsUnit z) : z = 1 := by
  haveI : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
  exact (by decide : ∀ w : ZMod (2 ^ 1), w ≠ 0 → w = 1) z hz.ne_zero

private lemma isUnit_of_toZModPow_one_eq_one {x : ℤ_[2]}
    (hx : PadicInt.toZModPow 1 x = 1) : IsUnit x := by
  haveI : NeZero (2 ^ 1) := ⟨by norm_num⟩
  rw [PadicInt.isUnit_iff]
  by_contra hne
  have hlt : ‖x‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one x) hne
  have hdvd : (2 : ℤ_[2]) ∣ x := by
    exact (PadicInt.norm_lt_one_iff_dvd x).mp hlt
  obtain ⟨y, rfl⟩ := hdvd
  rw [map_mul] at hx
  have h2 : (PadicInt.toZModPow (p := 2) 1) 2 = 0 := by
    rw [show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by push_cast; ring, map_natCast]
    decide
  rw [h2, zero_mul] at hx
  exact absurd hx (by decide)

/-- The simultaneous mod-two reductions of the basis masters. -/
noncomputable def masterMod2 {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    (DM alpha h : Type) →* Multiplicative (Fin (coreRank h) → ZMod (2 ^ 1)) where
  toFun x := ofAdd fun j => PadicInt.toZModPow 1 (masterH halpha (Pi.single j 1) x).u
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext j
    rw [map_one]
    exact map_zero _
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    funext j
    rw [masterH_mul_u, map_add]
    congr 1
    rw [Units.smul_def, smul_eq_mul, map_mul,
      zmod2_eq_one_of_isUnit ((chiM alpha h x).isUnit.map
        (PadicInt.toZModPow (p := 2) 1)), one_mul]

private theorem continuous_masterMod2 {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    Continuous (masterMod2 (h := h) halpha) := by
  refine continuous_ofAdd.comp (continuous_pi fun j => ?_)
  exact continuous_toZModPow_one.comp
    (continuous_wordLift_u.comp (masterH halpha (Pi.single j 1)).continuous_toFun)

private theorem topGen_dm_of_aut {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    (Subgroup.closure (Set.range fun i => Psi (dmGen alpha h i))).topologicalClosure = ⊤ := by
  have htop := topGen_map (f := Psi.toMulEquiv.toMonoidHom) Psi.continuous_toFun
    (EquivLike.surjective Psi) (dm_topGen alpha h)
  have himage : ⇑Psi.toMonoidHom '' Set.range (dmGen alpha h) =
      Set.range fun i => Psi (dmGen alpha h i) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨dmGen alpha h i, ⟨i, rfl⟩, rfl⟩
  rw [himage] at htop
  exact htop

private theorem mem_closure_gens_of_aut {T : Type*} [Group T] [TopologicalSpace T]
    [DiscreteTopology T] {alpha h : ℕ} (φ : (DM alpha h : Type) →* T)
    (hφ : Continuous φ)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (x : DM alpha h) :
    φ x ∈ Subgroup.closure (Set.range fun i => φ (Psi (dmGen alpha h i))) := by
  let K : Subgroup (DM alpha h : Type) :=
    (Subgroup.closure (Set.range fun i => φ (Psi (dmGen alpha h i)))).comap φ
  have hKclosed : IsClosed (K : Set (DM alpha h : Type)) := by
    have hset : (K : Set (DM alpha h : Type)) =
        ⇑φ ⁻¹' (Subgroup.closure (Set.range fun i => φ (Psi (dmGen alpha h i))) : Set T) :=
      rfl
    rw [hset]
    exact (isClosed_discrete _).preimage hφ
  have hle : Subgroup.closure (Set.range fun i => Psi (dmGen alpha h i)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have htop : (⊤ : Subgroup (DM alpha h : Type)) ≤ K := by
    rw [← topGen_dm_of_aut Psi]
    exact Subgroup.topologicalClosure_minimal _ hle hKclosed
  exact htop (Subgroup.mem_top x)

private theorem toAdd_mem_span_of_mem_closure {n : ℕ}
    {s : Fin n → Multiplicative (Fin n → ZMod (2 ^ 1))}
    {w : Multiplicative (Fin n → ZMod (2 ^ 1))}
    (hw : w ∈ Subgroup.closure (Set.range s)) :
    w.toAdd ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range fun i => (s i).toAdd) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
  | one => exact Submodule.zero_mem _
  | mul x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | inv x _ hx => exact Submodule.neg_mem _ hx

/-- Evaluation of the basis masters at an automorphic generating tuple. -/
noncomputable def evalMatrix {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2] :=
  Matrix.of fun i j => (masterH halpha (Pi.single j 1) (Psi (dmGen alpha h i))).u

private theorem evalMatrixMod_row {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (i : Fin (coreRank h)) :
    ((evalMatrix halpha Psi).map (PadicInt.toZModPow 1)) i =
      (masterMod2 halpha (Psi (dmGen alpha h i))).toAdd := rfl

private theorem masterMod2_gen {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (i : Fin (coreRank h)) :
    (masterMod2 halpha (dmGen alpha h i)).toAdd =
      Pi.single i (1 : ZMod (2 ^ 1)) := by
  funext j
  show PadicInt.toZModPow 1 (masterH halpha (Pi.single j 1) (dmGen alpha h i)).u = _
  rw [masterH_gen]
  change PadicInt.toZModPow 1 ((Pi.single j (1 : ℤ_[2]) :
    Fin (coreRank h) → ℤ_[2]) i) = _
  rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (Ne.symm hji), map_zero]

/-- The master evaluation matrix of every core automorphism is invertible. -/
theorem isUnit_evalMatrix {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    IsUnit (evalMatrix halpha Psi) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  let Mb : Matrix (Fin (coreRank h)) (Fin (coreRank h)) (ZMod (2 ^ 1)) :=
    (evalMatrix halpha Psi).map (PadicInt.toZModPow 1)
  have hspan : ∀ v : Fin (coreRank h) → ZMod (2 ^ 1),
      v ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range Mb.row) := by
    have hmem : ∀ x : DM alpha h, (masterMod2 halpha x).toAdd ∈
        Submodule.span (ZMod (2 ^ 1)) (Set.range Mb.row) := by
      intro x
      have hclose := mem_closure_gens_of_aut (masterMod2 halpha)
        (continuous_masterMod2 halpha) Psi x
      have hspan' := toAdd_mem_span_of_mem_closure hclose
      refine Submodule.span_mono ?_ hspan'
      rintro _ ⟨i, rfl⟩
      exact ⟨i, (evalMatrixMod_row halpha Psi i).symm⟩
    intro v
    have hv : v = ∑ i, v i • Pi.single (M := fun _ => ZMod (2 ^ 1)) i 1 := by
      funext k
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact masterMod2_gen halpha i ▸ hmem (dmGen alpha h i)
  have hMbUnit : IsUnit Mb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    have hv := hspan v
    rw [← range_vecMulLinear, LinearMap.mem_range] at hv
    exact hv
  have hdet2 : PadicInt.toZModPow 1 ((evalMatrix halpha Psi).det) = 1 := by
    calc
      PadicInt.toZModPow 1 ((evalMatrix halpha Psi).det) = Mb.det := by
        rw [show Mb = (evalMatrix halpha Psi).map (PadicInt.toZModPow 1) from rfl,
          ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      _ = 1 := zmod2_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det Mb).mp hMbUnit)
  exact isUnit_of_toZModPow_one_eq_one hdet2

/-- Full crossed-derivation descent for all `4+2h` generator values. -/
def IsFullOrientationDatumM (alpha h : ℕ)
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ) : Prop :=
  ∀ b : Fin (coreRank h) → ℤ_[2],
    mRelWord alpha (fun i =>
      (⟨b i, chi (dmGen alpha h i)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)) = 1

/-- The master evaluation matrix proves full descent after every core automorphism. -/
theorem fullOrientationDatumM_pullback_aut {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    IsFullOrientationDatumM alpha h (pullbackCharacter (chiM alpha h) Psi) := by
  intro b
  obtain ⟨c, hc⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr (isUnit_evalMatrix halpha Psi)) b
  let H : (DM alpha h : Type) →* WordLift ℤ_[2] ℤ_[2]ˣ :=
    (masterContract halpha c).comp Psi.toMulEquiv.toMonoidHom
  have hval : ∀ i : Fin (coreRank h),
      H (dmGen alpha h i) =
        ⟨b i, chiM alpha h (Psi (dmGen alpha h i))⟩ := by
    intro i
    refine WordLift.ext ?_ rfl
    show (masterContract halpha c (Psi (dmGen alpha h i))).u = b i
    rw [masterContract_apply_u]
    have hci := congrFun hc i
    simp only [Matrix.mulVec, dotProduct] at hci
    rw [← hci]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hword : mRelWord alpha (fun i => H (dmGen alpha h i)) = 1 := by
    rw [← map_mRelWord, dm_relation, map_one]
  have hfun : (fun i => H (dmGen alpha h i)) = fun i =>
      (⟨b i, chiM alpha h (Psi (dmGen alpha h i))⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) :=
    funext hval
  rw [hfun] at hword
  exact hword

private theorem list_prod_wordLift_of_base_one
    (l : List (WordLift ℤ_[2] ℤ_[2]ˣ)) (hl : ∀ z ∈ l, z.g = 1) :
    l.prod = ⟨(l.map WordLift.u).sum, 1⟩ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : a.g = 1 := hl a (by simp)
      have htail : ∀ z ∈ l, z.g = 1 := by
        intro z hz
        exact hl z (by simp [hz])
      rw [List.prod_cons, ih htail]
      apply WordLift.ext
      · simp [WordLift.mul_u, ha]
      · simp [ha]

/-- Closed formula for the full handle crossed-derivation block. -/
theorem handleWord_wordLift_formula {h : ℕ}
    (Du Dv : Fin h → ℤ_[2]) (Xu Xv : Fin h → ℤ_[2]ˣ) :
    handleWord (fun j => (⟨Du j, Xu j⟩ : WordLift ℤ_[2] ℤ_[2]ˣ))
        (fun j => ⟨Dv j, Xv j⟩) =
      ⟨∑ j,
          ((((Xu j)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              ((((Xv j)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) * Du j
            + (((Xv j)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              (1 - (((Xu j)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * Dv j),
        1⟩ := by
  rw [handleWord]
  let l := (List.finRange h).map fun j =>
    commP (⟨Du j, Xu j⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dv j, Xv j⟩
  have hl : ∀ z ∈ l, z.g = 1 := by
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    simp [commP, mul_comm]
  rw [show ((List.finRange h).map fun j =>
      commP (⟨Du j, Xu j⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dv j, Xv j⟩) = l from rfl,
    list_prod_wordLift_of_base_one l hl, List.map_map, Fin.sum_univ_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  change (commP (⟨Du j, Xu j⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dv j, Xv j⟩).u = _
  rw [commP_wordLift]

private theorem character_core_relation {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ) :
    chi (dmGen alpha h 0) ^ 2 * chi (dmGen alpha h 2) ^ (2 ^ alpha) = 1 := by
  have hmap : mRelWord alpha (fun i => chi (dmGen alpha h i)) = 1 := by
    rw [← map_mRelWord, dm_relation, map_one]
  rw [mRelWord_comm] at hmap
  exact hmap

/-- Full Fox-row formula for the presented `M` relator, including all handles. -/
theorem mRelWord_wordLift_formula {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ)
    (b : Fin (coreRank h) → ℤ_[2]) :
    mRelWord alpha (fun i =>
      (⟨b i, chi (dmGen alpha h i)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)) =
      ⟨mCoeffA (chi (dmGen alpha h 0)) (chi (dmGen alpha h 1)) * b 0
          + mCoeffB (chi (dmGen alpha h 0)) (chi (dmGen alpha h 1)) * b 1
          + mCoeffC alpha (chi (dmGen alpha h 0)) (chi (dmGen alpha h 2))
              (chi (dmGen alpha h 3)) * b 2
          + mCoeffD alpha (chi (dmGen alpha h 0)) (chi (dmGen alpha h 2))
              (chi (dmGen alpha h 3)) * b 3
          + ∑ j,
              ((((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
                  ((((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) *
                    b (handleIdxU j)
                + (((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
                  (1 - (((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) *
                    b (handleIdxV j)),
        1⟩ := by
  rw [mRelWord, mWord_wordLift, handleWord_wordLift_formula]
  apply WordLift.ext
  · rw [WordLift.mul_u]
    simp only [character_core_relation chi, one_smul]
  · simp [character_core_relation chi]

private theorem fullOrientationDatumM_handleV {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ)
    (H : IsFullOrientationDatumM alpha h chi) (j : Fin h) :
    chi (dmGen alpha h (handleIdxV j)) = 1 := by
  let b : Fin (coreRank h) → ℤ_[2] := Pi.single (handleIdxU j) 1
  have hz := congrArg WordLift.u (H b)
  rw [mRelWord_wordLift_formula] at hz
  simp only [WordLift.one_u] at hz
  have hb0 : b (0 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxU j) 1 0 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxU_ne_of_val_lt j (by rw [coreVal_zero]; omega)).symm
  have hb1 : b (1 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxU j) 1 1 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxU_ne_of_val_lt j (by rw [coreVal_one]; omega)).symm
  have hb2 : b (2 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxU j) 1 2 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega)).symm
  have hb3 : b (3 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxU j) 1 3 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxU_ne_of_val_lt j (by rw [coreVal_three]; omega)).symm
  have hsum :
      (∑ k : Fin h,
          ((((chi (dmGen alpha h (handleIdxU k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              ((((chi (dmGen alpha h (handleIdxV k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) *
                b (handleIdxU k)
            + (((chi (dmGen alpha h (handleIdxV k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              (1 - (((chi (dmGen alpha h (handleIdxU k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) *
                b (handleIdxV k))) =
        (((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
    rw [Finset.sum_eq_single j]
    · simp [b, handleIdxU_ne_handleIdxV j j]
    · intro k _ hkj
      have huu : handleIdxU j ≠ handleIdxU k :=
        fun hk => hkj (handleIdxU_injective hk.symm)
      have huv : handleIdxU j ≠ handleIdxV k := handleIdxU_ne_handleIdxV j k
      simp [b, huu, huv]
    · simp
  rw [hb0, hb1, hb2, hb3, hsum] at hz
  simp only [mul_zero, zero_add] at hz
  have hv : ((((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) = 0 := by
    exact (mul_eq_zero.mp hz).resolve_left (Units.ne_zero _)
  apply inv_eq_one.mp
  apply Units.ext
  exact sub_eq_zero.mp hv

private theorem fullOrientationDatumM_handleU {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ)
    (H : IsFullOrientationDatumM alpha h chi) (j : Fin h) :
    chi (dmGen alpha h (handleIdxU j)) = 1 := by
  let b : Fin (coreRank h) → ℤ_[2] := Pi.single (handleIdxV j) 1
  have hz := congrArg WordLift.u (H b)
  rw [mRelWord_wordLift_formula] at hz
  simp only [WordLift.one_u] at hz
  have hb0 : b (0 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxV j) 1 0 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxV_ne_of_val_lt j (by rw [coreVal_zero]; omega)).symm
  have hb1 : b (1 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxV j) 1 1 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxV_ne_of_val_lt j (by rw [coreVal_one]; omega)).symm
  have hb2 : b (2 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxV j) 1 2 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxV_ne_of_val_lt j (by rw [coreVal_two]; omega)).symm
  have hb3 : b (3 : Fin (coreRank h)) = 0 := by
    change Pi.single (M := fun _ : Fin (coreRank h) => ℤ_[2])
      (handleIdxV j) 1 3 = 0
    rw [Pi.single_eq_of_ne]
    exact (handleIdxV_ne_of_val_lt j (by rw [coreVal_three]; omega)).symm
  have hsum :
      (∑ k : Fin h,
          ((((chi (dmGen alpha h (handleIdxU k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              ((((chi (dmGen alpha h (handleIdxV k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) *
                b (handleIdxU k)
            + (((chi (dmGen alpha h (handleIdxV k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              (1 - (((chi (dmGen alpha h (handleIdxU k)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) *
                b (handleIdxV k))) =
        (((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          (1 - (((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
    rw [Finset.sum_eq_single j]
    · simp [b, handleIdxU_ne_handleIdxV j j]
    · intro k _ hkj
      have hvv : handleIdxV j ≠ handleIdxV k :=
        fun hk => hkj (handleIdxV_injective hk.symm)
      have hvu : handleIdxV j ≠ handleIdxU k :=
        (handleIdxU_ne_handleIdxV k j).symm
      simp [b, hvv, hvu]
    · simp
  rw [hb0, hb1, hb2, hb3, hsum] at hz
  simp only [mul_zero, zero_add] at hz
  have hu :
      (1 - (((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = 0 := by
    exact (mul_eq_zero.mp hz).resolve_left (Units.ne_zero _)
  apply inv_eq_one.mp
  apply Units.ext
  exact (sub_eq_zero.mp hu).symm

private theorem fullOrientationDatumM_core_single {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ)
    (H : IsFullOrientationDatumM alpha h chi)
    (i : Fin (coreRank h)) (hi : (i : ℕ) < 4) :
    mCoeffA (chi (dmGen alpha h 0)) (chi (dmGen alpha h 1)) *
          (Pi.single i 1 : Fin (coreRank h) → ℤ_[2]) 0
        + mCoeffB (chi (dmGen alpha h 0)) (chi (dmGen alpha h 1)) *
          (Pi.single i 1 : Fin (coreRank h) → ℤ_[2]) 1
        + mCoeffC alpha (chi (dmGen alpha h 0)) (chi (dmGen alpha h 2))
            (chi (dmGen alpha h 3)) *
              (Pi.single i 1 : Fin (coreRank h) → ℤ_[2]) 2
        + mCoeffD alpha (chi (dmGen alpha h 0)) (chi (dmGen alpha h 2))
            (chi (dmGen alpha h 3)) *
              (Pi.single i 1 : Fin (coreRank h) → ℤ_[2]) 3 = 0 := by
  let b : Fin (coreRank h) → ℤ_[2] := Pi.single i 1
  have hz := congrArg WordLift.u (H b)
  rw [mRelWord_wordLift_formula] at hz
  simp only [WordLift.one_u] at hz
  have hsum :
      (∑ j : Fin h,
          ((((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              ((((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) *
                b (handleIdxU j)
            + (((chi (dmGen alpha h (handleIdxV j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              (1 - (((chi (dmGen alpha h (handleIdxU j)))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) *
                b (handleIdxV j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hiu : i ≠ handleIdxU j := (handleIdxU_ne_of_val_lt j hi).symm
    have hiv : i ≠ handleIdxV j := (handleIdxV_ne_of_val_lt j hi).symm
    simp [b, hiu, hiv]
  rw [hsum, add_zero] at hz
  exact hz

private theorem coreSingle_eq_same {h : ℕ} (i : Fin (coreRank h)) :
    (Pi.single i 1 : Fin (coreRank h) → ℤ_[2]) i = 1 := by
  exact Pi.single_eq_same i 1

private theorem coreSingle_eq_zero {h : ℕ} {i k : Fin (coreRank h)}
    (hki : k ≠ i) :
    (Pi.single i 1 : Fin (coreRank h) → ℤ_[2]) k = 0 := by
  exact Pi.single_eq_of_ne hki 1

private theorem fullOrientationDatumM_core {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ)
    (H : IsFullOrientationDatumM alpha h chi) :
    IsLabuteOrientationDatumM alpha
      (chi (dmA alpha h)) (chi (dmB alpha h))
      (chi (dmC alpha h)) (chi (dmD alpha h)) := by
  rw [isLabuteOrientationDatumM_iff_coeffs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [dmA, dmC] using character_core_relation chi
  · have hz := fullOrientationDatumM_core_single chi H
      (0 : Fin (coreRank h)) (by rw [coreVal_zero]; omega)
    rw [coreSingle_eq_same,
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_zero]; omega)),
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_two, coreVal_zero]; omega)),
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_three, coreVal_zero]; omega))]
      at hz
    simpa [dmA, dmB] using hz
  · have hz := fullOrientationDatumM_core_single chi H
      (1 : Fin (coreRank h)) (by rw [coreVal_one]; omega)
    rw [coreSingle_eq_zero
        (Fin.ne_of_val_ne (by rw [coreVal_zero, coreVal_one]; omega)),
      coreSingle_eq_same,
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_two, coreVal_one]; omega)),
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_three, coreVal_one]; omega))]
      at hz
    simpa [dmA, dmB] using hz
  · have hz := fullOrientationDatumM_core_single chi H
      (2 : Fin (coreRank h)) (by rw [coreVal_two]; omega)
    rw [coreSingle_eq_zero
        (Fin.ne_of_val_ne (by rw [coreVal_zero, coreVal_two]; omega)),
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_two]; omega)),
      coreSingle_eq_same,
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_three, coreVal_two]; omega))]
      at hz
    simpa [dmA, dmC, dmD] using hz
  · have hz := fullOrientationDatumM_core_single chi H
      (3 : Fin (coreRank h)) (by rw [coreVal_three]; omega)
    rw [coreSingle_eq_zero
        (Fin.ne_of_val_ne (by rw [coreVal_zero, coreVal_three]; omega)),
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega)),
      coreSingle_eq_zero (Fin.ne_of_val_ne (by rw [coreVal_two, coreVal_three]; omega)),
      coreSingle_eq_same] at hz
    simpa [dmA, dmC, dmD] using hz

theorem isPresentedOrientationM_of_fullDatum {alpha h : ℕ}
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ)
    (H : IsFullOrientationDatumM alpha h chi) :
    IsPresentedOrientationM alpha h chi :=
  ⟨fullOrientationDatumM_core chi H,
    fullOrientationDatumM_handleU chi H,
    fullOrientationDatumM_handleV chi H⟩

/-- The improved `M` orientation is characteristic in every rank. -/
theorem mCoreOrientationCharacteristic_all {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    MCoreOrientationCharacteristic alpha h := by
  intro Psi x
  have Hfull := fullOrientationDatumM_pullback_aut halpha Psi
  have Hpresent := isPresentedOrientationM_of_fullDatum _ Hfull
  have heq := (isPresentedOrientationM_iff halpha _).mp Hpresent
  exact DFunLike.congr_fun heq x

#print axioms masterH
#print axioms masterH_gen
#print axioms masterH_base
#print axioms masterH_mul_u
#print axioms masterContract
#print axioms masterContract_apply_u
#print axioms masterContract_apply_g
#print axioms masterMod2
#print axioms evalMatrix
#print axioms isUnit_evalMatrix
#print axioms IsFullOrientationDatumM
#print axioms fullOrientationDatumM_pullback_aut
#print axioms handleWord_wordLift_formula
#print axioms mRelWord_wordLift_formula
#print axioms fullOrientationDatumM_handleV
#print axioms fullOrientationDatumM_handleU
#print axioms fullOrientationDatumM_core_single
#print axioms fullOrientationDatumM_core
#print axioms isPresentedOrientationM_of_fullDatum
#print axioms mCoreOrientationCharacteristic_all

end

end GQ2.Dyadic.Instances.MOrientationCharacteristic
