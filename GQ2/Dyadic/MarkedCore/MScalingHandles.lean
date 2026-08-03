/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
module

public import GQ2.Dyadic.MarkedCore.MScaling

@[expose] public section

/-!
# Splitting B8 scaling across positive-handle tails

The compact construction sees the third outer factor as one element.  At positive handle level
that element is `C^D * ∏[u_j,v_j]`.  This file develops the missing, non-circular operation:
recursively apply B8 to a finite product and retain one conjugator for every factor.
-/

namespace GQ2
namespace Dyadic
namespace MarkedCore

open scoped GQ2

section ListScaling

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- Conjugators which split the `u`-scaling of a finite product into scaled individual factors.
For a nontrivial split `x * rest`, B8 supplies conjugators for `x`, `rest`, and their product;
the third conjugator is spliced to the requested conjugator `g`, and recursion continues on the
rest. -/
noncomputable def peripheralScaleListConj (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) : (xs : List H) → H → List H
  | [], _ => []
  | [_], g => [g]
  | x :: y :: ys, g =>
      let rest := (y :: ys).prod
      let q := (peripheralScaleC R hH x rest u)⁻¹ * g
      peripheralScaleP R hH x rest u * q ::
        peripheralScaleListConj R hH u (y :: ys) (peripheralScaleT R hH x rest u * q)
termination_by xs => xs.length

@[simp] theorem peripheralScaleListConj_nil (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) (g : H) : peripheralScaleListConj R hH u [] g = [] := by
  rw [peripheralScaleListConj]

@[simp] theorem peripheralScaleListConj_singleton (R : PeripheralCyclotomicAction)
    (hH : IsProP 2 H) (u : ℤ_[2]ˣ) (x g : H) :
    peripheralScaleListConj R hH u [x] g = [g] := by
  rw [peripheralScaleListConj]

theorem length_peripheralScaleListConj (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) (xs : List H) (g : H) :
    (peripheralScaleListConj R hH u xs g).length = xs.length := by
  induction xs generalizing g with
  | nil => rw [peripheralScaleListConj]
  | cons x xs ih =>
      cases xs with
      | nil => rw [peripheralScaleListConj]; rfl
      | cons y ys =>
          simp only [peripheralScaleListConj, List.length_cons]
          rw [ih]
          simp only [List.length_cons]

omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] in
private theorem scaleList_conjP_inv (x c : H) : conjP x⁻¹ c = (conjP x c)⁻¹ := by
  simp only [conjP]
  group

/-- The two visible terms in a canonical B8 triple multiply to the transported product term. -/
theorem peripheralPair_scaling (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) (x y : H) :
    conjP (zpowZtwo hH x (u : ℤ_[2])) (peripheralScaleP R hH x y u) *
        conjP (zpowZtwo hH y (u : ℤ_[2])) (peripheralScaleT R hH x y u) =
      conjP (zpowZtwo hH (x * y) (u : ℤ_[2])) (peripheralScaleC R hH x y u) := by
  have htriple := peripheralTriple_scaling_canonical R hH
    (X := x) (Y := y) (Z := (x * y)⁻¹) (by rw [mul_inv_cancel]) u
  rw [mZpowZtwo_inv, scaleList_conjP_inv] at htriple
  apply eq_of_mul_inv_eq_one
  exact htriple

/-- **Finite-product B8 splitting.**  Pairing every factor with its recursively assigned
conjugator gives the requested conjugate of the scaled total product. -/
theorem peripheralScaleList_product (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) (xs : List H) (g : H) :
    (List.zipWith (fun x c => conjP (zpowZtwo hH x (u : ℤ_[2])) c) xs
      (peripheralScaleListConj R hH u xs g)).prod =
      conjP (zpowZtwo hH xs.prod (u : ℤ_[2])) g := by
  induction xs generalizing g with
  | nil => simp [conjP]
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
          let rest := (y :: ys).prod
          let c := peripheralScaleC R hH x rest u
          let q := c⁻¹ * g
          have hpair := peripheralPair_scaling R hH u x rest
          rw [peripheralScaleListConj]
          simp only [List.zipWith_cons_cons, List.prod_cons]
          have htail := ih (peripheralScaleT R hH x rest u * q)
          change
            conjP (zpowZtwo hH x (u : ℤ_[2]))
                (peripheralScaleP R hH x rest u * q) *
                (List.zipWith (fun z d => conjP (zpowZtwo hH z (u : ℤ_[2])) d) (y :: ys)
                  (peripheralScaleListConj R hH u (y :: ys)
                    (peripheralScaleT R hH x rest u * q))).prod =
              conjP (zpowZtwo hH (x * rest) (u : ℤ_[2])) g
          rw [htail]
          change
            conjP (zpowZtwo hH x (u : ℤ_[2]))
                (peripheralScaleP R hH x rest u * q) *
                conjP (zpowZtwo hH rest (u : ℤ_[2]))
                  (peripheralScaleT R hH x rest u * q) =
              conjP (zpowZtwo hH (x * rest) (u : ℤ_[2])) g
          have hcombine :
              conjP (zpowZtwo hH x (u : ℤ_[2]))
                  (peripheralScaleP R hH x rest u * q) *
                  conjP (zpowZtwo hH rest (u : ℤ_[2]))
                    (peripheralScaleT R hH x rest u * q) =
                conjP
                  (conjP (zpowZtwo hH x (u : ℤ_[2])) (peripheralScaleP R hH x rest u) *
                    conjP (zpowZtwo hH rest (u : ℤ_[2]))
                      (peripheralScaleT R hH x rest u)) q := by
            simp only [conjP]
            group
          rw [hcombine, hpair]
          simp only [q, c, conjP]
          group

omit [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] in
private theorem scaleList_topClosure_le_ker
    {A : Type} [Group A] [TopologicalSpace A] [T2Space A]
    (f : ContinuousMonoidHom H A) {S : Set H} (hs : ∀ x ∈ S, f x = 1) :
    (Subgroup.closure S).topologicalClosure ≤ f.toMonoidHom.ker := by
  refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr hs) ?_
  have hker : (f.toMonoidHom.ker : Set H) = f ⁻¹' {1} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [hker]
  exact isClosed_singleton.preimage f.continuous_toFun

private theorem map_peripheralScale_eq_one
    {A : Type} [Group A] [TopologicalSpace A] [T2Space A]
    (f : ContinuousMonoidHom H A) (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) {x y : H} (hx : f x = 1) (hy : f y = 1) :
    f (peripheralScaleP R hH x y u) = 1 ∧
      f (peripheralScaleT R hH x y u) = 1 ∧
      f (peripheralScaleC R hH x y u) = 1 := by
  have hle := scaleList_topClosure_le_ker f (S := {x, y}) (by
    rintro z (rfl | rfl)
    · exact hx
    · exact hy)
  exact ⟨MonoidHom.mem_ker.mp (hle (by
      simpa [peripheralScaleP] using deltaHom_mem_topologicalClosure hH x y (R.cP u))),
    MonoidHom.mem_ker.mp (hle (by
      simpa [peripheralScaleT] using deltaHom_mem_topologicalClosure hH x y (R.cT u))),
    MonoidHom.mem_ker.mp (hle (by
      simpa [peripheralScaleC] using deltaHom_mem_topologicalClosure hH x y (R.cC u)))⟩

/-- If a character kills every input factor and the requested total conjugator, it kills every
conjugator produced by the finite-product splitting. -/
theorem map_peripheralScaleListConj_eq_one
    {A : Type} [Group A] [TopologicalSpace A] [T2Space A]
    (f : ContinuousMonoidHom H A) (R : PeripheralCyclotomicAction) (hH : IsProP 2 H)
    (u : ℤ_[2]ˣ) (xs : List H) (g : H)
    (hxs : ∀ x ∈ xs, f x = 1) (hg : f g = 1) :
    ∀ c ∈ peripheralScaleListConj R hH u xs g, f c = 1 := by
  induction xs generalizing g with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simpa using hg
      | cons y ys =>
          let rest := (y :: ys).prod
          have hx : f x = 1 := hxs x (by simp)
          have hrest : f rest = 1 := by
            rw [show rest = (y :: ys).prod from rfl, map_list_prod]
            refine List.prod_eq_one fun z hz => ?_
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
            exact hxs w (by simp [hw])
          obtain ⟨hp, ht, hc⟩ := map_peripheralScale_eq_one f R hH u hx hrest
          have hgP : f (peripheralScaleP R hH x rest u *
              ((peripheralScaleC R hH x rest u)⁻¹ * g)) = 1 := by
            simp [hp, hc, hg]
          have hgT : f (peripheralScaleT R hH x rest u *
              ((peripheralScaleC R hH x rest u)⁻¹ * g)) = 1 := by
            simp [ht, hc, hg]
          intro z hz
          rw [peripheralScaleListConj] at hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · simpa only [rest, List.prod_cons] using hgP
          · apply ih (peripheralScaleT R hH x rest u *
                ((peripheralScaleC R hH x rest u)⁻¹ * g))
              (fun z hz => hxs z (by simp [hz])) hgT z
            simpa only [rest, List.prod_cons] using hz

end ListScaling

/-! ## A constructor retaining nontrivial handle letters -/

section FullMark

variable {G : Type} {h : ℕ}

/-- Interleave the two letters of each of `h` handles in the order `u₀,v₀,u₁,v₁,…`. -/
def handlePairMark (u v : Fin h → G) : Fin (2 * h) → G := fun k =>
  let k' : Fin (h * 2) := Fin.cast (Nat.mul_comm 2 h) k
  if k'.modNat = 0 then u k'.divNat else v k'.divNat

/-- Four core letters followed by `h` nontrivial handle pairs. -/
def fullMark (a b c d : G) (u v : Fin h → G) : Fin (coreRank h) → G :=
  Fin.append ![a, b, c, d] (handlePairMark u v)

@[simp] theorem fullMark_zero (a b c d : G) (u v : Fin h → G) :
    fullMark a b c d u v 0 = a := by
  rw [fullMark]
  change Fin.append ![a, b, c, d] (handlePairMark u v) (Fin.castAdd (2 * h) 0) = a
  rw [Fin.append_left]
  rfl

@[simp] theorem fullMark_one (a b c d : G) (u v : Fin h → G) :
    fullMark a b c d u v 1 = b := by
  rw [fullMark]
  have hi : (1 : Fin (coreRank h)) = Fin.castAdd (2 * h) (1 : Fin 4) := Fin.ext (by
    rw [coreVal_one]
    rfl)
  rw [hi, Fin.append_left]
  rfl

@[simp] theorem fullMark_two (a b c d : G) (u v : Fin h → G) :
    fullMark a b c d u v 2 = c := by
  rw [fullMark]
  have hi : (2 : Fin (coreRank h)) = Fin.castAdd (2 * h) (2 : Fin 4) := Fin.ext (by
    rw [coreVal_two]
    rfl)
  rw [hi, Fin.append_left]
  rfl

@[simp] theorem fullMark_three (a b c d : G) (u v : Fin h → G) :
    fullMark a b c d u v 3 = d := by
  rw [fullMark]
  have hi : (3 : Fin (coreRank h)) = Fin.castAdd (2 * h) (3 : Fin 4) := Fin.ext (by
    rw [coreVal_three]
    rfl)
  rw [hi, Fin.append_left]
  rfl

@[simp] theorem fullMark_handleU (a b c d : G) (u v : Fin h → G) (j : Fin h) :
    fullMark a b c d u v (handleIdxU j) = u j := by
  rw [fullMark]
  let k : Fin (2 * h) := ⟨2 * j, by omega⟩
  change Fin.append ![a, b, c, d] (handlePairMark u v) (Fin.natAdd 4 k) = u j
  rw [Fin.append_right]
  simp only [handlePairMark]
  split
  · congr 1
    apply Fin.ext
    simp [k, Fin.divNat]
  · rename_i hn
    exfalso
    apply hn
    apply Fin.ext
    simp [k, Fin.modNat]

@[simp] theorem fullMark_handleV (a b c d : G) (u v : Fin h → G) (j : Fin h) :
    fullMark a b c d u v (handleIdxV j) = v j := by
  rw [fullMark]
  let k : Fin (2 * h) := ⟨2 * j + 1, by omega⟩
  have hi : (handleIdxV j : Fin (coreRank h)) = Fin.natAdd 4 k := Fin.ext (by
    simp only [handleIdxV_val, k, Fin.val_natAdd]
    omega)
  rw [hi, Fin.append_right]
  simp only [handlePairMark]
  split
  · rename_i hz
    exfalso
    have hv := congrArg Fin.val hz
    simp [k, Fin.modNat] at hv
  · congr 1
    apply Fin.ext
    simp [k, Fin.divNat]
    omega

end FullMark

/-! ## Uniform `M` scaling -/

section MConstruction

open Multiplicative

variable (R : PeripheralCyclotomicAction) (α h : ℕ) (u : ℤ_[2]ˣ)

local notation "hP" => isProP_DM α h
local notation "A" => dmA α h
local notation "B" => dmB α h
local notation "C" => dmC α h
local notation "D" => dmD α h
local notation "W" => mHead A B
local notation "U" => fun j : Fin h => dmGen α h (handleIdxU j)
local notation "V" => fun j : Fin h => dmGen α h (handleIdxV j)

noncomputable def mScaleHIP : DM α h := peripheralScaleP R hP A (conjP A B) u
noncomputable def mScaleHIT : DM α h := peripheralScaleT R hP A (conjP A B) u
noncomputable def mScaleHIC : DM α h := peripheralScaleC R hP A (conjP A B) u

noncomputable def mScaleHOP : DM α h := peripheralScaleP R hP W (C ^ (2 ^ α - 1)) u
noncomputable def mScaleHOT : DM α h := peripheralScaleT R hP W (C ^ (2 ^ α - 1)) u
noncomputable def mScaleHOC : DM α h := peripheralScaleC R hP W (C ^ (2 ^ α - 1)) u

noncomputable def mScaleHQ : DM α h := (mScaleHIC R α h u)⁻¹ * mScaleHOP R α h u

/-- The outer third factor split into its conjugacy leaf and its individual handle leaves. -/
noncomputable def mScaleHTailFactors : List (DM α h : Type) :=
  conjP C D :: (List.finRange h).map fun j => commP (U j) (V j)

@[simp] theorem length_mScaleHTailFactors : (mScaleHTailFactors α h).length = h + 1 := by
  simp [mScaleHTailFactors]

theorem prod_mScaleHTailFactors :
    (mScaleHTailFactors α h).prod = conjP C D * handleWord U V := by
  simp [mScaleHTailFactors, handleWord]

noncomputable def mScaleHTailConjs : List (DM α h : Type) :=
  peripheralScaleListConj R hP u (mScaleHTailFactors α h) (mScaleHOC R α h u)

@[simp] theorem length_mScaleHTailConjs : (mScaleHTailConjs R α h u).length = h + 1 := by
  rw [mScaleHTailConjs, length_peripheralScaleListConj, length_mScaleHTailFactors]

theorem mScaleHTailConjs_ne_nil : mScaleHTailConjs R α h u ≠ [] := by
  intro hz
  have hl := length_mScaleHTailConjs R α h u
  rw [hz] at hl
  simp at hl

theorem length_mScaleHTailConjs_tail : (mScaleHTailConjs R α h u).tail.length = h := by
  have hl := length_mScaleHTailConjs R α h u
  have hn := mScaleHTailConjs_ne_nil R α h u
  cases hc : mScaleHTailConjs R α h u with
  | nil => exact (hn hc).elim
  | cons z zs =>
      rw [hc] at hl
      simp only [List.tail_cons, List.length_cons] at hl ⊢
      omega

noncomputable def mScaleHDConj : DM α h :=
  (mScaleHTailConjs R α h u).head (mScaleHTailConjs_ne_nil R α h u)

noncomputable def mScaleHHandleConj (j : Fin h) : DM α h :=
  (mScaleHTailConjs R α h u).tail.getD j 1

theorem mScaleHTailConjs_eq :
    mScaleHTailConjs R α h u =
      mScaleHDConj R α h u :: List.ofFn (mScaleHHandleConj R α h u) := by
  have hn := mScaleHTailConjs_ne_nil R α h u
  cases hc : mScaleHTailConjs R α h u with
  | nil => exact (hn hc).elim
  | cons z zs =>
      have hzs : zs.length = h := by
        have hl := length_mScaleHTailConjs R α h u
        rw [hc] at hl
        simp only [List.length_cons] at hl
        omega
      have hd : mScaleHDConj R α h u = z := by simp [mScaleHDConj, hc]
      have hh : ∀ j : Fin h, mScaleHHandleConj R α h u j =
          zs.get (Fin.cast hzs.symm j) := by
        intro j
        simp [mScaleHHandleConj, hc, List.getD, j.isLt, hzs]
      calc
        z :: zs = mScaleHDConj R α h u :: List.ofFn (mScaleHHandleConj R α h u) := by
          rw [hd]
          congr 1
          rw [show mScaleHHandleConj R α h u = fun j => zs.get (Fin.cast hzs.symm j)
            from funext hh]
          refine List.ext_get (by simp [hzs]) ?_
          intro n hn₁ hn₂
          rw [List.get_ofFn]
          congr 1

/-! Each handle commutator is itself split by one more B8 triple. -/

noncomputable def mScaleHUP (j : Fin h) : DM α h :=
  peripheralScaleP R hP (U j)⁻¹ (conjP (U j) (V j)) u

noncomputable def mScaleHUT (j : Fin h) : DM α h :=
  peripheralScaleT R hP (U j)⁻¹ (conjP (U j) (V j)) u

noncomputable def mScaleHUC (j : Fin h) : DM α h :=
  peripheralScaleC R hP (U j)⁻¹ (conjP (U j) (V j)) u

noncomputable def mScaleHUQ (j : Fin h) : DM α h :=
  (mScaleHUC R α h u j)⁻¹ * mScaleHHandleConj R α h u j

noncomputable def mScaleHNewU (j : Fin h) : DM α h :=
  conjP (zpowZtwo hP (U j) (u : ℤ_[2]))
    (mScaleHUP R α h u j * mScaleHUQ R α h u j)

noncomputable def mScaleHNewV (j : Fin h) : DM α h :=
  (mScaleHUQ R α h u j)⁻¹ *
      ((mScaleHUP R α h u j)⁻¹ * V j * mScaleHUT R α h u j) *
    mScaleHUQ R α h u j

noncomputable def mScaleHMark : Fin (coreRank h) → DM α h :=
  fullMark
    (conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u * mScaleHQ R α h u))
    ((mScaleHQ R α h u)⁻¹ * ((mScaleHIP R α h u)⁻¹ * B * mScaleHIT R α h u) *
      mScaleHQ R α h u)
    (conjP (zpowZtwo hP C (u : ℤ_[2])) (mScaleHOT R α h u))
    ((mScaleHOT R α h u)⁻¹ * D * mScaleHDConj R α h u)
    (mScaleHNewU R α h u) (mScaleHNewV R α h u)

@[simp] theorem mScaleHMark_zero :
    mScaleHMark R α h u 0 =
      conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u * mScaleHQ R α h u) := by
  rw [mScaleHMark, fullMark_zero]

@[simp] theorem mScaleHMark_one :
    mScaleHMark R α h u 1 =
      (mScaleHQ R α h u)⁻¹ * ((mScaleHIP R α h u)⁻¹ * B * mScaleHIT R α h u) *
        mScaleHQ R α h u := by
  rw [mScaleHMark, fullMark_one]

@[simp] theorem mScaleHMark_two :
    mScaleHMark R α h u 2 =
      conjP (zpowZtwo hP C (u : ℤ_[2])) (mScaleHOT R α h u) := by
  rw [mScaleHMark, fullMark_two]

@[simp] theorem mScaleHMark_three :
    mScaleHMark R α h u 3 =
      (mScaleHOT R α h u)⁻¹ * D * mScaleHDConj R α h u := by
  rw [mScaleHMark, fullMark_three]

@[simp] theorem mScaleHMark_handleU (j : Fin h) :
    mScaleHMark R α h u (handleIdxU j) = mScaleHNewU R α h u j := by
  rw [mScaleHMark, fullMark_handleU]

@[simp] theorem mScaleHMark_handleV (j : Fin h) :
    mScaleHMark R α h u (handleIdxV j) = mScaleHNewV R α h u j := by
  rw [mScaleHMark, fullMark_handleV]

private theorem mScaleH_conjP_pow {G : Type*} [Group G] (x c : G) (n : ℕ) :
    conjP x c ^ n = conjP (x ^ n) c := by
  induction n with
  | zero => simp [conjP]
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [conjP]
      group

private theorem mScaleH_inner_identity :
    conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u) *
        conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2])) (mScaleHIT R α h u) *
        conjP (zpowZtwo hP W⁻¹ (u : ℤ_[2])) (mScaleHIC R α h u) = 1 :=
  peripheralTriple_scaling_canonical R hP (mWord_innerTriple A B) u

private theorem mScaleH_outer_identity :
    conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleHOP R α h u) *
        conjP (zpowZtwo hP (C ^ (2 ^ α - 1)) (u : ℤ_[2])) (mScaleHOT R α h u) *
        conjP (zpowZtwo hP (conjP C D * handleWord U V) (u : ℤ_[2]))
          (mScaleHOC R α h u) = 1 :=
  peripheralTriple_scaling_canonical R hP (dm_outer_triple α h) u

theorem mHead_mScaleHMark :
    mHead (mScaleHMark R α h u 0) (mScaleHMark R α h u 1) =
      conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleHOP R α h u) := by
  rw [mHead, mScaleHMark_zero, mScaleHMark_one]
  have hi := mScaleH_inner_identity R α h u
  rw [mZpowZtwo_inv, scaleList_conjP_inv] at hi
  have hprod :
      conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u) *
          conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2])) (mScaleHIT R α h u) =
        conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleHIC R α h u) := by
    apply eq_of_mul_inv_eq_one
    exact hi
  have hsecond :
      conjP
          (conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u * mScaleHQ R α h u))
          ((mScaleHQ R α h u)⁻¹ * ((mScaleHIP R α h u)⁻¹ * B * mScaleHIT R α h u) *
            mScaleHQ R α h u) =
        conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2]))
          (mScaleHIT R α h u * mScaleHQ R α h u) := by
    rw [← mConjP_zpowZtwo hP A B (u : ℤ_[2])]
    simp only [conjP]
    group
  rw [hsecond]
  have hcombine :
      conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u * mScaleHQ R α h u) *
          conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2]))
            (mScaleHIT R α h u * mScaleHQ R α h u) =
        conjP
          (conjP (zpowZtwo hP A (u : ℤ_[2])) (mScaleHIP R α h u) *
            conjP (zpowZtwo hP (conjP A B) (u : ℤ_[2])) (mScaleHIT R α h u))
          (mScaleHQ R α h u) := by
    simp only [conjP]
    group
  rw [hcombine, hprod]
  simp only [mScaleHQ, conjP]
  group

theorem mScaleHMark_two_pow :
    mScaleHMark R α h u 2 ^ (2 ^ α - 1) =
      conjP (zpowZtwo hP (C ^ (2 ^ α - 1)) (u : ℤ_[2])) (mScaleHOT R α h u) := by
  rw [mScaleHMark_two, mScaleH_conjP_pow, mZpowZtwo_pow]

theorem conjP_mScaleHMark_two_three :
    conjP (mScaleHMark R α h u 2) (mScaleHMark R α h u 3) =
      conjP (zpowZtwo hP (conjP C D) (u : ℤ_[2])) (mScaleHDConj R α h u) := by
  rw [mScaleHMark_two, mScaleHMark_three,
    ← mConjP_zpowZtwo hP C D (u : ℤ_[2])]
  simp only [conjP]
  group

theorem commP_mScaleHNewU_newV (j : Fin h) :
    commP (mScaleHNewU R α h u j) (mScaleHNewV R α h u j) =
      conjP (zpowZtwo hP (commP (U j) (V j)) (u : ℤ_[2]))
        (mScaleHHandleConj R α h u j) := by
  have hpair := peripheralPair_scaling R hP u (U j)⁻¹ (conjP (U j) (V j))
  have hfirst :
      (mScaleHNewU R α h u j)⁻¹ =
        conjP (zpowZtwo hP (U j)⁻¹ (u : ℤ_[2]))
          (mScaleHUP R α h u j * mScaleHUQ R α h u j) := by
    rw [mScaleHNewU, mZpowZtwo_inv, scaleList_conjP_inv]
  have hsecond :
      conjP (mScaleHNewU R α h u j) (mScaleHNewV R α h u j) =
        conjP (zpowZtwo hP (conjP (U j) (V j)) (u : ℤ_[2]))
          (mScaleHUT R α h u j * mScaleHUQ R α h u j) := by
    rw [mScaleHNewU, mScaleHNewV,
      ← mConjP_zpowZtwo hP (U j) (V j) (u : ℤ_[2])]
    simp only [conjP]
    group
  rw [commP_eq_inv_mul_conjP, hfirst, hsecond]
  have hcombine :
      conjP (zpowZtwo hP (U j)⁻¹ (u : ℤ_[2]))
          (mScaleHUP R α h u j * mScaleHUQ R α h u j) *
          conjP (zpowZtwo hP (conjP (U j) (V j)) (u : ℤ_[2]))
            (mScaleHUT R α h u j * mScaleHUQ R α h u j) =
        conjP
          (conjP (zpowZtwo hP (U j)⁻¹ (u : ℤ_[2])) (mScaleHUP R α h u j) *
            conjP (zpowZtwo hP (conjP (U j) (V j)) (u : ℤ_[2]))
              (mScaleHUT R α h u j))
          (mScaleHUQ R α h u j) := by
    simp only [conjP]
    group
  rw [hcombine]
  have hpair' :
      conjP (zpowZtwo hP (U j)⁻¹ (u : ℤ_[2])) (mScaleHUP R α h u j) *
          conjP (zpowZtwo hP (conjP (U j) (V j)) (u : ℤ_[2]))
            (mScaleHUT R α h u j) =
        conjP (zpowZtwo hP (commP (U j) (V j)) (u : ℤ_[2]))
          (mScaleHUC R α h u j) := by
    simpa only [mScaleHUP, mScaleHUT, mScaleHUC, commP_eq_inv_mul_conjP] using hpair
  rw [hpair']
  simp only [mScaleHUQ, conjP]
  group

theorem mScaleH_tail_identity :
    conjP (mScaleHMark R α h u 2) (mScaleHMark R α h u 3) *
        handleWord (mScaleHNewU R α h u) (mScaleHNewV R α h u) =
      conjP (zpowZtwo hP (conjP C D * handleWord U V) (u : ℤ_[2]))
        (mScaleHOC R α h u) := by
  have hs := peripheralScaleList_product R hP u (mScaleHTailFactors α h)
    (mScaleHOC R α h u)
  change
    (List.zipWith
        (fun x g => conjP (zpowZtwo hP x (u : ℤ_[2])) g)
        (mScaleHTailFactors α h) (mScaleHTailConjs R α h u)).prod =
      conjP (zpowZtwo hP (mScaleHTailFactors α h).prod (u : ℤ_[2]))
        (mScaleHOC R α h u) at hs
  rw [prod_mScaleHTailFactors] at hs
  rw [mScaleHTailFactors, mScaleHTailConjs_eq] at hs
  simp only [List.zipWith_cons_cons, List.prod_cons] at hs
  rw [conjP_mScaleHMark_two_three]
  rw [handleWord, ← List.ofFn_eq_map]
  have hhandles :
      List.ofFn (fun j => commP (mScaleHNewU R α h u j) (mScaleHNewV R α h u j)) =
        List.ofFn (fun j => conjP (zpowZtwo hP (commP (U j) (V j)) (u : ℤ_[2]))
          (mScaleHHandleConj R α h u j)) := by
    simp_rw [commP_mScaleHNewU_newV]
  rw [hhandles]
  simpa [List.ofFn_eq_map] using hs

theorem mRelWord_mScaleHMark : mRelWord α (mScaleHMark R α h u) = 1 := by
  rw [mRelWord_triple, mHead_mScaleHMark, mScaleHMark_two_pow]
  simp_rw [mScaleHMark_handleU, mScaleHMark_handleV]
  change
    conjP (zpowZtwo hP W (u : ℤ_[2])) (mScaleHOP R α h u) *
        conjP (zpowZtwo hP (C ^ (2 ^ α - 1)) (u : ℤ_[2])) (mScaleHOT R α h u) *
        (conjP (mScaleHMark R α h u 2) (mScaleHMark R α h u 3) *
          handleWord (mScaleHNewU R α h u) (mScaleHNewV R α h u)) = 1
  rw [mScaleH_tail_identity]
  exact mScaleH_outer_identity R α h u

/-- The positive-handle scaling endomorphism. -/
noncomputable def mScaleHHom : ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h hP (mScaleHMark R α h u) (mRelWord_mScaleHMark R α h u)

@[simp] theorem mScaleHHom_gen (i : Fin (coreRank h)) :
    mScaleHHom R α h u (dmGen α h i) = mScaleHMark R α h u i :=
  mLiftHom_gen _ _ _ _ _ _

/-! ## Orientation -/

private theorem chiM_mScaleH_core_conjugators :
    chiM α h (mScaleHIP R α h u) = 1 ∧
      chiM α h (mScaleHIT R α h u) = 1 ∧
      chiM α h (mScaleHIC R α h u) = 1 ∧
      chiM α h (mScaleHOP R α h u) = 1 ∧
      chiM α h (mScaleHOT R α h u) = 1 ∧
      chiM α h (mScaleHOC R α h u) = 1 := by
  have hinner := map_peripheralScale_eq_one (chiM α h) R hP u
    (x := A) (y := conjP A B) (by simp) (by rw [mChar_conjP]; simp)
  have houter := map_peripheralScale_eq_one (chiM α h) R hP u
    (x := W) (y := C ^ (2 ^ α - 1)) (by simp [mHead, mChar_conjP]) (by simp)
  simpa only [mScaleHIP, mScaleHIT, mScaleHIC, mScaleHOP, mScaleHOT, mScaleHOC] using
    ⟨hinner.1, hinner.2.1, hinner.2.2, houter.1, houter.2.1, houter.2.2⟩

private theorem chiM_mScaleH_tail_factor (x : DM α h)
    (hx : x ∈ mScaleHTailFactors α h) : chiM α h x = 1 := by
  rw [mScaleHTailFactors] at hx
  simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hx
  rcases hx with rfl | ⟨j, rfl⟩
  · rw [mChar_conjP]
    simp
  · rw [commP_eq_inv_mul_conjP, map_mul, map_inv, mChar_conjP]
    simp

private theorem chiM_mScaleH_tail_conjugator (x : DM α h)
    (hx : x ∈ mScaleHTailConjs R α h u) : chiM α h x = 1 := by
  have hc := (chiM_mScaleH_core_conjugators R α h u).2.2.2.2.2
  exact map_peripheralScaleListConj_eq_one (chiM α h) R hP u
    (mScaleHTailFactors α h) (mScaleHOC R α h u)
    (chiM_mScaleH_tail_factor α h) hc x (by simpa [mScaleHTailConjs] using hx)

@[simp] theorem chiM_mScaleHDConj : chiM α h (mScaleHDConj R α h u) = 1 := by
  apply chiM_mScaleH_tail_conjugator R α h u
  rw [mScaleHTailConjs_eq]
  simp

@[simp] theorem chiM_mScaleHHandleConj (j : Fin h) :
    chiM α h (mScaleHHandleConj R α h u j) = 1 := by
  apply chiM_mScaleH_tail_conjugator R α h u
  rw [mScaleHTailConjs_eq]
  simp

private theorem chiM_mScaleH_handle_conjugators (j : Fin h) :
    chiM α h (mScaleHUP R α h u j) = 1 ∧
      chiM α h (mScaleHUT R α h u j) = 1 ∧
      chiM α h (mScaleHUC R α h u j) = 1 := by
  have hp := map_peripheralScale_eq_one (chiM α h) R hP u
    (x := (U j)⁻¹) (y := conjP (U j) (V j)) (by simp) (by rw [mChar_conjP]; simp)
  simpa only [mScaleHUP, mScaleHUT, mScaleHUC] using hp

@[simp] theorem chiM_mScaleHQ : chiM α h (mScaleHQ R α h u) = 1 := by
  simp [mScaleHQ, chiM_mScaleH_core_conjugators R α h u]

@[simp] theorem chiM_mScaleHUQ (j : Fin h) :
    chiM α h (mScaleHUQ R α h u j) = 1 := by
  simp [mScaleHUQ, chiM_mScaleH_handle_conjugators R α h u j]

@[simp] theorem chiM_mScaleHMark_zero :
    chiM α h (mScaleHMark R α h u 0) = chiM α h A := by
  rw [mScaleHMark_zero, mChar_conjP,
    map_zpowZtwo hP isProP_two_unitsPadicInt (chiM α h), chiM_dmA,
    zpowZtwo_one_base]

@[simp] theorem chiM_mScaleHMark_one :
    chiM α h (mScaleHMark R α h u 1) = chiM α h B := by
  simp [mScaleHMark_one, chiM_mScaleH_core_conjugators R α h u]

@[simp] theorem chiM_mScaleHMark_two :
    chiM α h (mScaleHMark R α h u 2) = chiM α h C := by
  rw [mScaleHMark_two, mChar_conjP,
    map_zpowZtwo hP isProP_two_unitsPadicInt (chiM α h), chiM_dmC,
    zpowZtwo_one_base]

@[simp] theorem chiM_mScaleHMark_three :
    chiM α h (mScaleHMark R α h u 3) = chiM α h D := by
  simp [mScaleHMark_three, chiM_mScaleH_core_conjugators R α h u]

@[simp] theorem chiM_mScaleHMark_handleU (j : Fin h) :
    chiM α h (mScaleHMark R α h u (handleIdxU j)) =
      chiM α h (dmGen α h (handleIdxU j)) := by
  rw [mScaleHMark_handleU, mScaleHNewU, mChar_conjP,
    map_zpowZtwo hP isProP_two_unitsPadicInt (chiM α h), chiM_handleU,
    zpowZtwo_one_base]

@[simp] theorem chiM_mScaleHMark_handleV (j : Fin h) :
    chiM α h (mScaleHMark R α h u (handleIdxV j)) =
      chiM α h (dmGen α h (handleIdxV j)) := by
  simp [mScaleHMark_handleV, mScaleHNewV,
    chiM_mScaleH_handle_conjugators R α h u j]

theorem chiM_mScaleHHom (x : DM α h) :
    chiM α h (mScaleHHom R α h u x) = chiM α h x := by
  have hext := dm_hom_ext ((chiM α h).comp (mScaleHHom R α h u)) (chiM α h) (fun i => by
    change chiM α h (mScaleHHom R α h u (dmGen α h i)) = chiM α h (dmGen α h i)
    rw [mScaleHHom_gen]
    rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact chiM_mScaleHMark_zero R α h u
    · exact chiM_mScaleHMark_one R α h u
    · exact chiM_mScaleHMark_two R α h u
    · exact chiM_mScaleHMark_three R α h u
    · exact chiM_mScaleHMark_handleU R α h u j
    · exact chiM_mScaleHMark_handleV R α h u j)
  exact DFunLike.congr_fun hext x

/-! ## Frattini surjectivity -/

private lemma mScaleH_discreteTopology_quotient (M : OpenNormalSubgroup (DM α h : Type)) :
    DiscreteTopology ((DM α h : Type) ⧸ M.toSubgroup) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  rw [← (QuotientGroup.isQuotientMap_mk M.toSubgroup).isOpen_preimage]
  have hpre : QuotientGroup.mk ⁻¹'
      ({1} : Set ((DM α h : Type) ⧸ M.toSubgroup)) =
      (M.toSubgroup : Set (DM α h : Type)) := by
    ext x
    exact QuotientGroup.eq_one_iff x
  rw [hpre]
  exact M.isOpen'

private lemma mScaleH_zpowZtwo_eq_self_of_sq_eq_one {P : Type} [Group P]
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

private lemma mScaleH_quotient_mul_comm (M : OpenNormalSubgroup (DM α h : Type))
    (hM : M.toSubgroup.index = 2) (z w : (DM α h : Type) ⧸ M.toSubgroup) : z * w = w * z := by
  have : Finite ((DM α h : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM α h : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isCyclic_of_prime_card (p := 2) hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (DM α h : Type) ⧸ M.toSubgroup)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg w)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

private lemma mScaleH_quotient_sq_eq_one (M : OpenNormalSubgroup (DM α h : Type))
    (hM : M.toSubgroup.index = 2) (z : (DM α h : Type) ⧸ M.toSubgroup) : z ^ 2 = 1 := by
  have : Finite ((DM α h : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM α h : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have hdvd : orderOf z ∣ 2 := hcard ▸ orderOf_dvd_natCard z
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private lemma mScaleH_quotient_map_conjP (M : OpenNormalSubgroup (DM α h : Type))
    (hM : M.toSubgroup.index = 2) (x c : DM α h) :
    QuotientGroup.mk' M.toSubgroup (conjP x c) = QuotientGroup.mk' M.toSubgroup x := by
  rw [conjP, map_mul, map_mul, map_inv]
  calc
    (QuotientGroup.mk' M.toSubgroup c)⁻¹ * QuotientGroup.mk' M.toSubgroup x *
          QuotientGroup.mk' M.toSubgroup c =
        QuotientGroup.mk' M.toSubgroup x * (QuotientGroup.mk' M.toSubgroup c)⁻¹ *
          QuotientGroup.mk' M.toSubgroup c := by
            rw [mScaleH_quotient_mul_comm α h M hM
              ((QuotientGroup.mk' M.toSubgroup c)⁻¹)]
    _ = QuotientGroup.mk' M.toSubgroup x := by rw [mul_assoc, inv_mul_cancel, mul_one]

private lemma mScaleH_quotient_map_zpowZtwo (M : OpenNormalSubgroup (DM α h : Type))
    (hM : M.toSubgroup.index = 2) (x : DM α h) (v : ℤ_[2]ˣ) :
    QuotientGroup.mk' M.toSubgroup (zpowZtwo hP x (v : ℤ_[2])) =
      QuotientGroup.mk' M.toSubgroup x := by
  letI := mScaleH_discreteTopology_quotient α h M
  letI : Finite ((DM α h : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hpro : IsProP 2 ((DM α h : Type) ⧸ M.toSubgroup) := by
    refine isProP_of_isPGroup (IsPGroup.of_card (n := 1) ?_)
    rw [← Subgroup.index_eq_card, hM, pow_one]
  have hnat := map_zpowZtwo hP hpro
    (⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ :
      ContinuousMonoidHom (DM α h : Type) ((DM α h : Type) ⧸ M.toSubgroup)) x (v : ℤ_[2])
  calc
    QuotientGroup.mk' M.toSubgroup (zpowZtwo hP x (v : ℤ_[2])) =
        zpowZtwo hpro (QuotientGroup.mk' M.toSubgroup x) (v : ℤ_[2]) := hnat
    _ = QuotientGroup.mk' M.toSubgroup x :=
      mScaleH_zpowZtwo_eq_self_of_sq_eq_one hpro
        (mScaleH_quotient_sq_eq_one α h M hM _) v

theorem dm_topologicallyFinGen (α h : ℕ) :
    ∃ s : Finset (DM α h : Type),
      (Subgroup.closure (s : Set (DM α h : Type))).topologicalClosure = ⊤ := by
  have hfin : (Set.range (dmGen α h)).Finite := Set.finite_range _
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact dm_topGen α h

/-- The uniform B8 scaling endomorphism is surjective by the pro-2 Frattini criterion. -/
theorem mScaleHHom_surjective : Function.Surjective (mScaleHHom R α h u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective hP (mScaleHHom R α h u) ?_
  intro M hM
  letI := mScaleH_discreteTopology_quotient α h M
  letI : Finite ((DM α h : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM α h : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  letI : Fact (Nat.Prime (Nat.card ((DM α h : Type) ⧸ M.toSubgroup))) :=
    ⟨hcard ▸ Nat.prime_two⟩
  let q : ContinuousMonoidHom (DM α h : Type) ((DM α h : Type) ⧸ M.toSubgroup) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  have q_conjP (x c : DM α h) : q (conjP x c) = q x := by
    change QuotientGroup.mk' M.toSubgroup (conjP x c) = QuotientGroup.mk' M.toSubgroup x
    exact mScaleH_quotient_map_conjP α h M hM x c
  have q_zpowZtwo (x : DM α h) (v : ℤ_[2]ˣ) :
      q (zpowZtwo hP x (v : ℤ_[2])) = q x := by
    change QuotientGroup.mk' M.toSubgroup (zpowZtwo hP x (v : ℤ_[2])) =
      QuotientGroup.mk' M.toSubgroup x
    exact mScaleH_quotient_map_zpowZtwo α h M hM x v
  let c : (DM α h : Type) →* ((DM α h : Type) ⧸ M.toSubgroup) :=
    (QuotientGroup.mk' M.toSubgroup).comp (mScaleHHom R α h u).toMonoidHom
  rcases c.range.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · exfalso
    have hval : ∀ g : DM α h, QuotientGroup.mk' M.toSubgroup (mScaleHHom R α h u g) = 1 := by
      intro g
      have hg : c g ∈ c.range := ⟨g, rfl⟩
      rw [hbot] at hg
      exact Subgroup.mem_bot.mp hg
    have hqA : q A = 1 := by
      have hg := hval A
      change q (mScaleHHom R α h u A) = 1 at hg
      rw [show A = dmGen α h 0 from rfl, mScaleHHom_gen, mScaleHMark_zero,
        q_conjP, q_zpowZtwo] at hg
      exact hg
    have hqC : q C = 1 := by
      have hg := hval C
      change q (mScaleHHom R α h u C) = 1 at hg
      rw [show C = dmGen α h 2 from rfl, mScaleHHom_gen, mScaleHMark_two,
        q_conjP, q_zpowZtwo] at hg
      exact hg
    have hqConjAB : q (conjP A B) = 1 := by
      rw [q_conjP, hqA]
    have hinner := map_peripheralScale_eq_one q R hP u hqA hqConjAB
    have hqIP : q (mScaleHIP R α h u) = 1 := by
      simpa only [mScaleHIP] using hinner.1
    have hqIT : q (mScaleHIT R α h u) = 1 := by
      simpa only [mScaleHIT] using hinner.2.1
    have hqB : q B = 1 := by
      have hg := hval B
      change q (mScaleHHom R α h u B) = 1 at hg
      rw [show B = dmGen α h 1 from rfl, mScaleHHom_gen, mScaleHMark_one] at hg
      simp only [map_mul, map_inv, hqIP, hqIT, inv_one, one_mul, mul_one] at hg
      have hconj := q_conjP B (mScaleHQ R α h u)
      simp only [conjP, map_mul, map_inv] at hconj
      exact hconj.symm.trans hg
    have hqW : q W = 1 := by
      rw [mHead, map_mul, q_conjP, hqA, one_mul]
    have hqCpow : q (C ^ (2 ^ α - 1)) = 1 := by
      rw [map_pow, hqC, one_pow]
    have houter := map_peripheralScale_eq_one q R hP u hqW hqCpow
    have hqOT : q (mScaleHOT R α h u) = 1 := by
      simpa only [mScaleHOT] using houter.2.1
    have hqOC : q (mScaleHOC R α h u) = 1 := by
      simpa only [mScaleHOC] using houter.2.2
    have hqTailFactor : ∀ x ∈ mScaleHTailFactors α h,
        q x = 1 := by
      intro x hx
      rw [mScaleHTailFactors] at hx
      simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hx
      rcases hx with rfl | ⟨j, rfl⟩
      · rw [q_conjP, hqC]
      · rw [commP_eq_inv_mul_conjP, map_mul, map_inv,
          q_conjP, inv_mul_cancel]
    have hqTailConj : ∀ x ∈ mScaleHTailConjs R α h u,
        q x = 1 := by
      intro x hx
      exact map_peripheralScaleListConj_eq_one q R hP u
        (mScaleHTailFactors α h) (mScaleHOC R α h u) hqTailFactor hqOC x
        (by simpa [mScaleHTailConjs] using hx)
    have hqDConj : q (mScaleHDConj R α h u) = 1 := by
      apply hqTailConj
      rw [mScaleHTailConjs_eq]
      simp
    have hqHandleConj (j : Fin h) :
        q (mScaleHHandleConj R α h u j) = 1 := by
      apply hqTailConj
      rw [mScaleHTailConjs_eq]
      simp
    have hqD : q D = 1 := by
      have hg := hval D
      change q (mScaleHHom R α h u D) = 1 at hg
      rw [show D = dmGen α h 3 from rfl, mScaleHHom_gen, mScaleHMark_three,
        map_mul, map_mul, map_inv, hqOT, hqDConj, inv_one, one_mul, mul_one] at hg
      exact hg
    have hqU (j : Fin h) : q (U j) = 1 := by
      have hg := hval (U j)
      change q (mScaleHHom R α h u (U j)) = 1 at hg
      rw [show U j = dmGen α h (handleIdxU j) from rfl, mScaleHHom_gen,
        mScaleHMark_handleU, mScaleHNewU, q_conjP, q_zpowZtwo] at hg
      exact hg
    have hqV (j : Fin h) : q (V j) = 1 := by
      have hqInvU : q (U j)⁻¹ = 1 := by rw [map_inv, hqU j, inv_one]
      have hqConjUV : q (conjP (U j) (V j)) = 1 := by
        rw [q_conjP, hqU j]
      have hhandle := map_peripheralScale_eq_one q R hP u hqInvU hqConjUV
      have hqUP : q (mScaleHUP R α h u j) = 1 := by
        simpa only [mScaleHUP] using hhandle.1
      have hqUT : q (mScaleHUT R α h u j) = 1 := by
        simpa only [mScaleHUT] using hhandle.2.1
      have hg := hval (V j)
      change q (mScaleHHom R α h u (V j)) = 1 at hg
      rw [show V j = dmGen α h (handleIdxV j) from rfl, mScaleHHom_gen,
        mScaleHMark_handleV, mScaleHNewV] at hg
      simp only [map_mul, map_inv, hqUP, hqUT, inv_one, one_mul, mul_one] at hg
      have hconj := q_conjP (V j) (mScaleHUQ R α h u j)
      simp only [conjP, map_mul, map_inv] at hconj
      exact hconj.symm.trans hg
    have hkerAll := scaleList_topClosure_le_ker q (S := Set.range (dmGen α h)) (by
      rintro _ ⟨i, rfl⟩
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact hqA
      · exact hqB
      · exact hqC
      · exact hqD
      · exact hqU j
      · exact hqV j)
    have : Nontrivial ((DM α h : Type) ⧸ M.toSubgroup) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    obtain ⟨z, hz⟩ := exists_ne (1 : (DM α h : Type) ⧸ M.toSubgroup)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
    refine hz (MonoidHom.mem_ker.mp (hkerAll ?_))
    rw [dm_topGen]
    exact Subgroup.mem_top g
  · intro z
    have hz : z ∈ c.range := htop ▸ Subgroup.mem_top z
    exact hz

/-- The uniform `M` unit scaling at arbitrary handle count is a continuous automorphism. -/
noncomputable def mScaleHEquiv : ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  continuousMulEquivOfBijective (mScaleHHom R α h u)
    ⟨profinite_hopfian (dm_topologicallyFinGen α h) (mScaleHHom R α h u)
        (mScaleHHom_surjective R α h u),
      mScaleHHom_surjective R α h u⟩

@[simp] theorem mScaleHEquiv_apply (x : DM α h) :
    mScaleHEquiv R α h u x = mScaleHHom R α h u x := rfl

/-- The uniform scaling automorphism preserves the canonical orientation. -/
theorem chiM_mScaleHEquiv (x : DM α h) :
    chiM α h (mScaleHEquiv R α h u x) = chiM α h x := by
  rw [mScaleHEquiv_apply]
  exact chiM_mScaleHHom R α h u x

/-- Every additive `ℤ₂`-character sees the requested unit scaling on the `C` row. -/
theorem mScaleHEquiv_C_row
    (f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    toAdd (f (mScaleHEquiv R α h u C)) = (u : ℤ_[2]) * toAdd (f C) := by
  change toAdd (f (mScaleHEquiv R α h u (dmGen α h 2))) =
    (u : ℤ_[2]) * toAdd (f (dmGen α h 2))
  rw [mScaleHEquiv_apply, mScaleHHom_gen,
    mScaleHMark_two, map_conjP_comm, toAdd_map_zpowZtwo, dmC]

end MConstruction

/-! ## Uniform discharge and regression -/

/-- An explicit peripheral cyclotomic action supplies the full `M` scaling face at every
handle count.  Keeping the B8 dependency as a parameter gives this theorem the standard
axiom footprint only. -/
theorem mScalingHypothesis_of_peripheral (R : PeripheralCyclotomicAction) (α h : ℕ) :
    MScalingHypothesis α h := by
  intro u
  exact ⟨mScaleHEquiv R α h u, chiM_mScaleHEquiv R α h u, mScaleHEquiv_C_row R α h u⟩

/-- Preferred uniform scaling discharge, consuming the repository's canonical B8 witness. -/
theorem mScalingHypothesis (α h : ℕ) : MScalingHypothesis α h :=
  mScalingHypothesis_of_peripheral peripheralCyclotomicAction α h

/-- **Regression theorem.**  The old all-in-one `M` correction contract now follows at every
handle count, with no residual scaling binder. -/
theorem mMixHypothesis (α h : ℕ) (hα : 2 ≤ α) : MMixHypothesis α h (by omega) :=
  mMixHypothesis_of_scaling α h hα (mScalingHypothesis α h)

end MarkedCore
end Dyadic
end GQ2
