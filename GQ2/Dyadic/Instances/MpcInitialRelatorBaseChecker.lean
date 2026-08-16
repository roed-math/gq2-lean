/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/

import GQ2.Dyadic.Instances.MpcC6WeightedChecker

/-!
# Cutoff-four checked collector

This specializes the weighted checker to the quotient at depth four. It reuses the
same reflected syntax and derivation language, interprets `deep` at depth four, and
permits Jacobi only when the three inputs have total depth at least three.

The checker and every soundness rule are kernel proved. The external collector used
by the companion trace module is not part of the trusted argument.
-/

namespace GQ2.Dyadic.Instances.MpcInitialRelatorBaseChecker

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord
open GQ2.Dyadic.SqCore
open GQ2.Roe.Labute
open scoped commutatorElement

structure Model4 (Q : Type*) [Group Q] where
  val : Gen4 → Q
  rel : eval val mRel = 1
  deep : ∀ w, 4 ≤ w.depth → eval val w = 1

noncomputable def towerModel4
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (val : Gen4 → G) (hrel : levelMk G 4 (eval val mRel) = 1) :
    Model4 (levelQuot G 4) where
  val := fun g ↦ levelMk G 4 (val g)
  rel := by
    rw [eval_map (levelMk G 4) val mRel]
    exact hrel
  deep := by
    intro w hw
    rw [eval_map (levelMk G 4) val w]
    apply (lim_mem_twoCentralSeries_iff_levelMk (G := G) 4 (eval val w)).mp
    exact twoCentralSeries_antitone (G := G) hw
      (eval_mem_twoCentralSeries val w)

noncomputable def dmModel4 : Model4 (levelQuot (DM 2 0 : Type) 4) :=
  towerModel4 (G := (DM 2 0 : Type))
    (fun | .A => dmA 2 0 | .B => dmB 2 0 | .C => dmC 2 0 | .D => dmD 2 0) (by
      rw [eval_mRel, mpcOrb_relation, map_one])

noncomputable def dmVal4 : Gen4 → (DM 2 0 : Type)
  | .A => dmA 2 0
  | .B => dmB 2 0
  | .C => dmC 2 0
  | .D => dmD 2 0

theorem eval_dmModel4 (w : CWord) :
    eval dmModel4.val w = levelMk (DM 2 0 : Type) 4 (eval dmVal4 w) := by
  simpa only [dmModel4, towerModel4, dmVal4] using
    eval_map (levelMk (DM 2 0 : Type) 4) dmVal4 w

private theorem commute_of_commP_eq_one {Q : Type*} [Group Q] {a b : Q}
    (h : commP a b = 1) : Commute a b := by
  change a * b = b * a
  simp only [commP] at h
  have hc : b⁻¹ * a * b = a := by
    calc
      b⁻¹ * a * b = a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = a := by rw [h, mul_one]
  calc
    a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [hc]

private theorem deep_commute4 {Q : Type*} [Group Q] (M : Model4 Q)
    (x y : CWord) (h : 4 ≤ x.depth + y.depth) :
    Commute (eval M.val x) (eval M.val y) := by
  apply commute_of_commP_eq_one
  simpa only [eval] using M.deep (.comm x y) (by
    simpa only [depth] using h)

private theorem deep_inv_self4 {Q : Type*} [Group Q] (M : Model4 Q)
    (x : CWord) (h : 3 ≤ x.depth) : (eval M.val x)⁻¹ = eval M.val x := by
  have hs : eval M.val x ^ 2 = 1 := by
    simpa only [eval] using M.deep (.sq x) (by
      simpa only [depth] using Nat.succ_le_succ h)
  calc
    (eval M.val x)⁻¹ = (eval M.val x)⁻¹ * 1 := by group
    _ = (eval M.val x)⁻¹ * eval M.val x ^ 2 := by rw [hs]
    _ = eval M.val x := by group

private theorem depth_pos (x : CWord) : 1 ≤ x.depth := by
  induction x <;> simp only [depth] at * <;> omega

private theorem conj_eq_self_of_commute {Q : Type*} [Group Q] {a b : Q}
    (h : Commute a b) : b⁻¹ * a * b = a := by
  calc
    b⁻¹ * a * b = b⁻¹ * (a * b) := by group
    _ = b⁻¹ * (b * a) := by rw [h.eq]
    _ = a := by group

private theorem comm_inv_snd_sound4 {Q : Type*} [Group Q] (M : Model4 Q)
    (x y z : CWord) (h : 3 ≤ x.depth + y.depth + z.depth) :
    commP (commP (eval M.val x) (eval M.val y)⁻¹) (eval M.val z) =
      commP (commP (eval M.val x) (eval M.val y)) (eval M.val z) := by
  let a := eval M.val x
  let b := eval M.val y
  let c := eval M.val z
  let w := commP a b
  let u := commP w c
  let ζ := commP b⁻¹ w
  have hypos := depth_pos y
  have hxy : 2 ≤ x.depth + y.depth := by
    have := depth_pos x
    omega
  have huInv : u⁻¹ = u := by
    simpa only [eval] using deep_inv_self4 M (.comm (.comm x y) z) (by
      simpa only [depth, add_assoc] using h)
  have hζz : commP ζ c = 1 := by
    simpa only [eval] using M.deep (.comm (.comm (.inv y) (.comm x y)) z) (by
      simp only [depth]
      omega)
  have hcor : commP u⁻¹ w⁻¹ = 1 := by
    simpa only [eval] using
      M.deep (.comm (.inv (.comm (.comm x y) z)) (.inv (.comm x y))) (by
        simp only [depth]
        omega)
  have hA : commP a b⁻¹ = ζ * w⁻¹ := by
    simp only [a, b, w, ζ, commP]
    group
  have hmul : commP (ζ * w⁻¹) c =
      (commP ζ c * commP (commP ζ c) w⁻¹) * commP w⁻¹ c := by
    simp only [commP]
    group
  have hinv : commP w⁻¹ c = u⁻¹ * commP u⁻¹ w⁻¹ := by
    simp only [u, commP]
    group
  have hone : commP (1 : Q) w⁻¹ = 1 := by
    simp only [commP]
    group
  change commP (commP a b⁻¹) c = u
  rw [hA, hmul, hζz, hone, one_mul, hinv, hcor, mul_one, huInv]
  exact one_mul u

private theorem hallWitt {Q : Type*} [Group Q] (a b c : Q) :
    b⁻¹ * commP (commP a b⁻¹) c * b *
        (c⁻¹ * commP (commP b c⁻¹) a * c) *
      (a⁻¹ * commP (commP c a⁻¹) b * a) = 1 := by
  simp only [commP]
  group

theorem jacobi_sound4 {Q : Type*} [Group Q] (M : Model4 Q)
    (x y z : CWord) (h : 3 ≤ x.depth + y.depth + z.depth) :
    eval M.val (.mul (.mul (.comm (.comm x y) z) (.comm (.comm y z) x))
      (.comm (.comm z x) y)) = 1 := by
  let a := eval M.val x
  let b := eval M.val y
  let c := eval M.val z
  let u := commP (commP a b) c
  let v := commP (commP b c) a
  let w := commP (commP c a) b
  have hxpos := depth_pos x
  have hypos := depth_pos y
  have hzpos := depth_pos z
  have h1 : commP (commP a b⁻¹) c = u :=
    comm_inv_snd_sound4 M x y z h
  have h2 : commP (commP b c⁻¹) a = v :=
    comm_inv_snd_sound4 M y z x (by omega)
  have h3 : commP (commP c a⁻¹) b = w :=
    comm_inv_snd_sound4 M z x y (by omega)
  have huComm : Commute u b := by
    simpa only [eval] using deep_commute4 M (.comm (.comm x y) z) y (by
      simp only [depth]
      omega)
  have hvComm : Commute v c := by
    simpa only [eval] using deep_commute4 M (.comm (.comm y z) x) z (by
      simp only [depth]
      omega)
  have hwComm : Commute w a := by
    simpa only [eval] using deep_commute4 M (.comm (.comm z x) y) x (by
      simp only [depth]
      omega)
  have hHW := hallWitt a b c
  rw [h1, h2, h3, conj_eq_self_of_commute huComm,
    conj_eq_self_of_commute hvComm, conj_eq_self_of_commute hwComm] at hHW
  simpa only [eval, a, b, c, u, v, w] using hHW

end GQ2.Dyadic.Instances.MpcInitialRelatorBaseChecker

namespace GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord.Deriv

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord
open GQ2.Dyadic.Instances.MpcInitialRelatorBaseChecker
open GQ2.Dyadic.SqCore
open GQ2.Roe.Labute
open scoped commutatorElement

def check4 : Deriv → Bool
  | .refl _ | .rel | .assoc _ _ _ | .one_mul _ | .mul_one _ | .inv_mul _ |
      .mul_inv _ | .swap _ _ | .comm_mul_left _ _ _ | .comm_mul_right _ _ _ |
      .sq_mul _ _ | .comm_inv_left _ _ | .comm_inv_right _ _ | .comm_self _ |
      .inv_sq _ | .inv_comm _ _ | .mul_self _ | .one_comm _ | .comm_one _ |
      .sq_one | .inv_one => true
  | .jacobi x y z => decide (3 ≤ x.depth + y.depth + z.depth)
  | .deep w => decide (4 ≤ w.depth)
  | .symm d | .inv d | .sq d => d.check4
  | .trans d e => d.check4 && e.check4 && decide (d.rhs = e.lhs)
  | .mul d e | .comm d e => d.check4 && e.check4

theorem sound4 {Q : Type*} [Group Q] (M : Model4 Q) :
    ∀ d : Deriv, d.check4 = true → eval M.val d.lhs = eval M.val d.rhs := by
  intro d hd
  induction d with
  | refl w => rfl
  | deep w => exact M.deep w (of_decide_eq_true hd)
  | rel => exact M.rel
  | symm d ih => exact (ih hd).symm
  | trans d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      have hs' := Bool.and_eq_true_iff.mp hs.1
      have hmid : d.rhs = e.lhs := of_decide_eq_true hs.2
      exact (ihd hs'.1).trans
        ((congrArg (eval M.val) hmid).trans (ihe hs'.2))
  | mul d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      simp only [lhs, rhs, eval]
      rw [ihd hs.1, ihe hs.2]
  | inv d ih =>
      simp only [lhs, rhs, eval]
      rw [ih hd]
  | sq d ih =>
      simp only [lhs, rhs, eval]
      rw [ih hd]
  | comm d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      simp only [lhs, rhs, eval]
      rw [ihd hs.1, ihe hs.2]
  | assoc x y z => simp only [lhs, rhs, eval, mul_assoc]
  | one_mul x => exact _root_.one_mul (eval M.val x)
  | mul_one x => exact _root_.mul_one (eval M.val x)
  | inv_mul x => simp only [lhs, rhs, eval, inv_mul_cancel]
  | mul_inv x => simp only [lhs, rhs, eval, mul_inv_cancel]
  | swap x y => simp only [lhs, rhs, eval, commP]; group
  | comm_mul_left x z y => simp only [lhs, rhs, eval, commP]; group
  | comm_mul_right x y z => simp only [lhs, rhs, eval, commP]; group
  | sq_mul x y => simp only [lhs, rhs, eval, commP, pow_two]; group
  | comm_inv_left x y => simp only [lhs, rhs, eval, commP]; group
  | comm_inv_right x y => simp only [lhs, rhs, eval, commP]; group
  | comm_self x => simp only [lhs, rhs, eval, commP]; group
  | inv_sq x => simp only [lhs, rhs, eval, pow_two]; group
  | inv_comm x y => simp only [lhs, rhs, eval, commP]; group
  | mul_self x => simp only [lhs, rhs, eval, pow_two]
  | one_comm x => simp only [lhs, rhs, eval, commP]; group
  | comm_one x => simp only [lhs, rhs, eval, commP]; group
  | sq_one => simp only [lhs, rhs, eval, one_pow]
  | inv_one => simp only [lhs, rhs, eval]; group
  | jacobi x y z => exact jacobi_sound4 M x y z (of_decide_eq_true hd)

#print axioms sound4

end GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord.Deriv
