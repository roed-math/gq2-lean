/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcC6WeightedChecker

/-!
The concrete reflection layer for the checked class-six collector.  This module only identifies
the already-proved closed defect and the explicit sparse increment with small `CWord` terms.  It
does not assert the remaining certificate equality.
-/

namespace GQ2.Dyadic.Instances.MpcC6WeightedCertificate

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx GQ2.Dyadic.Instances.MpcMkC6
open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

namespace Bridge

private abbrev A : CWord := .gen .A
private abbrev B : CWord := .gen .B
private abbrev C : CWord := .gen .C
private abbrev D : CWord := .gen .D

private abbrev B2 : CWord := .sq B
private abbrev B4 : CWord := .sq B2
private abbrev B8 : CWord := .sq B4
private abbrev W : CWord := .comm D B
private abbrev Z : CWord := .inv B4
private abbrev N : CWord := .mul B4 (.comm B2 D)
private abbrev T : CWord := .mul W B4

def sxE1 (p σ z : CWord) : CWord :=
  .mul (.mul (.mul (.sq σ) (.comm σ p)) (.mul (.sq z) (.comm z p)))
    (.mul (.mul (.comm σ z) (.comm (.comm σ p) z)) (.comm (.comm σ p) σ))

def sxE2 (p q σ τ z : CWord) : CWord :=
  .mul
    (.mul (.mul (.comm p τ) (.comm σ q))
      (.mul (.mul (.mul (.comm σ τ) (.comm z q)) (.comm (.comm p q) σ))
        (.comm (.comm p q) τ)))
    (.mul
        (.mul
          (.mul
            (.mul
              (.mul (.comm (.comm p τ) z) (.comm z τ))
              (.comm (.comm p τ) σ))
            (.comm (.comm p q) z))
          (.comm (.comm σ q) τ))
        (.comm (.comm p τ) (.comm p q)))

def sxE3 (q r : CWord) : CWord :=
  .mul (.mul (.sq (.sq (.sq q))) (.sq (.comm r (.sq q))))
    (.mul
      (.mul
        (.mul (.comm (.sq r) (.sq (.sq q))) (.comm (.comm r (.sq q)) (.sq r)))
        (.comm (.comm r (.sq q)) (.sq (.sq q))))
      (.sq (.comm (.comm r (.sq q)) r)))

def sxE4 (q r w ν : CWord) : CWord :=
  .mul
    (.mul (.mul (.comm r ν) (.comm (.sq q) w))
      (.mul (.mul (.comm (.sq q) ν) (.comm (.comm (.sq q) w) r))
        (.comm (.comm r w) ν)))
    (.mul
        (.mul
          (.mul (.comm (.comm r ν) (.comm r w))
            (.comm (.comm (.sq q) w) (.comm r w)))
          (.comm (.comm (.sq q) ν) r))
        (.comm (.comm (.sq q) w) ν))

def closedDefect : CWord :=
  .mul
    (.mul
      (.mul
        (.mul (sxE1 A W Z) (sxE2 A B W T Z))
        (sxE3 B C))
      (sxE4 B C D N))
    (.mul
      (.comm (sxE1 A W Z) (.mul (.mul (.comm A B) (.sq (.sq C))) (.comm C D)))
      (.comm (sxE2 A B W T Z) (.mul (.sq (.sq C)) (.comm C D))))

def mkUs : CWord :=
  .mul (.mul (.mul (.mul (.mul (.mul
    (.sq (.comm (.comm B D) A))
    (.sq (.comm B2 A)))
    (.sq (.comm (.comm B C) B)))
    (.comm (.comm (.comm B D) B) A))
    (.comm (.comm (.comm B C) B) B))
    (.comm (.comm (.comm B D) B) B))
    (.comm (.comm (.comm B D) D) B)

def mkUt : CWord :=
  .mul (.mul (.mul (.mul B8
    (.sq (.comm (.comm B C) B)))
    (.sq (.comm (.comm B D) B)))
    (.comm (.comm (.comm B C) B) B))
    (.comm (.comm (.comm B D) D) B)

def mkUm : CWord :=
  .mul (.sq (.comm (.comm B D) B)) (.comm (.comm (.comm B D) B) B)

def mkUn : CWord :=
  .mul (.mul (.mul (.sq (.sq (.comm B C)))
    (.sq (.comm (.comm B C) B)))
    (.sq (.comm (.comm B C) C)))
    (.comm (.comm (.comm B C) C) B)

def sparseIncrement : CWord :=
  .mul (.mul (.mul (.mul (.mul
    (.sq mkUs)
    (.comm mkUs A))
    (.comm mkUs (.mul B T)))
    (.comm mkUm (.mul D N)))
    (.comm A mkUt))
    (.comm C mkUn)

theorem eval_sxE1 (val : Gen4 → levelQuot (DM 2 0 : Type) 6) (p σ z : CWord) :
    eval val (sxE1 p σ z) = mpcSxE1 (eval val p) (eval val σ) (eval val z) := rfl

theorem eval_sxE2 (val : Gen4 → levelQuot (DM 2 0 : Type) 6) (p q σ τ z : CWord) :
    eval val (sxE2 p q σ τ z) =
      mpcSxE2 (eval val p) (eval val q) (eval val σ) (eval val τ) (eval val z) := rfl

theorem eval_sxE3 (val : Gen4 → levelQuot (DM 2 0 : Type) 6) (q r : CWord) :
    eval val (sxE3 q r) = mpcSxE3 (eval val q) (eval val r) := by
  simp only [sxE3, eval, mpcSxE3]
  congr 1 <;> norm_num [← pow_mul]

theorem eval_sxE4 (val : Gen4 → levelQuot (DM 2 0 : Type) 6) (q r w ν : CWord) :
    eval val (sxE4 q r w ν) =
      mpcSxE4 (eval val q) (eval val r) (eval val w) (eval val ν) := rfl

theorem eval_closedDefect_shape (val : Gen4 → levelQuot (DM 2 0 : Type) 6) :
    eval val closedDefect =
      mpcSxE1 (eval val A) (eval val W) (eval val Z) *
        mpcSxE2 (eval val A) (eval val B) (eval val W) (eval val T) (eval val Z) *
        mpcSxE3 (eval val B) (eval val C) *
        mpcSxE4 (eval val B) (eval val C) (eval val D) (eval val N) *
        (commP (mpcSxE1 (eval val A) (eval val W) (eval val Z))
            (commP (eval val A) (eval val B) * eval val (.sq (.sq C)) *
              commP (eval val C) (eval val D)) *
          commP (mpcSxE2 (eval val A) (eval val B) (eval val W) (eval val T) (eval val Z))
            (eval val (.sq (.sq C)) * commP (eval val C) (eval val D))) := by
  simp only [closedDefect, eval, eval_sxE1, eval_sxE2, eval_sxE3, eval_sxE4]

theorem eval_sparseIncrement_shape {Q : Type*} [Group Q] (val : Gen4 → Q) :
    eval val sparseIncrement =
      eval val mkUs ^ 2 * commP (eval val mkUs) (eval val A) *
        commP (eval val mkUs) (eval val (.mul B T)) *
        commP (eval val mkUm) (eval val (.mul D N)) *
        commP (eval val A) (eval val mkUt) * commP (eval val C) (eval val mkUn) := rfl

private theorem eval_A : eval dmModel.val A = mpcSxA := rfl
private theorem eval_B : eval dmModel.val B = mpcSxB := rfl
private theorem eval_C : eval dmModel.val C = mpcSxC := rfl
private theorem eval_D : eval dmModel.val D = mpcSxD := rfl

private theorem eval_B4 : eval dmModel.val B4 = mpcSxB ^ 4 := by
  simp only [eval, dmModel, towerModel, mpcSxB]
  norm_num [← pow_mul]

private theorem eval_C4 : eval dmModel.val (.sq (.sq C)) = mpcSxC ^ 4 := by
  simp only [eval, dmModel, towerModel, mpcSxC]
  norm_num [← pow_mul]

private theorem eval_W : eval dmModel.val W = mpcSxW := rfl

private theorem eval_Z : eval dmModel.val Z = mpcSxZ := by
  change (eval dmModel.val B4)⁻¹ = (mpcSxB ^ 4)⁻¹
  rw [eval_B4]

private theorem eval_T : eval dmModel.val T = mpcSxW * mpcSxB ^ 4 := by
  change eval dmModel.val W * eval dmModel.val B4 = _
  rw [eval_W, eval_B4]

private theorem eval_N : eval dmModel.val N = mpcSxN := by
  change eval dmModel.val B4 * commP (eval dmModel.val B2) (eval dmModel.val D) = _
  rw [eval_B4]
  rfl

private theorem eval_BT : eval dmModel.val (.mul B T) = mpcSxB * (mpcSxW * mpcSxB ^ 4) := by
  change eval dmModel.val B * eval dmModel.val T = _
  rw [eval_B, eval_T]

private theorem eval_DN : eval dmModel.val (.mul D N) = mpcSxD * mpcSxN := by
  change eval dmModel.val D * eval dmModel.val N = _
  rw [eval_D, eval_N]

theorem eval_closedDefect :
    eval dmModel.val closedDefect = levelMk (DM 2 0 : Type) 6 (mpcLadDefect mpcFvW5) := by
  rw [mpcSx_w5_defect]
  rw [eval_closedDefect_shape, eval_A, eval_B, eval_C, eval_D, eval_W, eval_Z, eval_T,
    eval_N, eval_C4]

theorem eval_mkUs : eval dmModel.val mkUs = levelMk (DM 2 0 : Type) 6 mpcMkC6Us := by
  simp only [mkUs, eval, dmModel, towerModel, B2, map_mul, map_pow,
    MpcMkC6.mpcMkC6Us]
  rfl

theorem eval_mkUt : eval dmModel.val mkUt = levelMk (DM 2 0 : Type) 6 mpcMkC6Ut := by
  simp only [mkUt, eval, dmModel, towerModel, B2, B4, B8, map_mul, map_pow,
    MpcMkC6.mpcMkC6Ut]
  rfl

theorem eval_mkUm : eval dmModel.val mkUm = levelMk (DM 2 0 : Type) 6 mpcMkC6Um := by
  simp only [mkUm, eval, dmModel, towerModel, map_mul, map_pow,
    MpcMkC6.mpcMkC6Um]
  rfl

theorem eval_mkUn : eval dmModel.val mkUn = levelMk (DM 2 0 : Type) 6 mpcMkC6Un := by
  simp only [mkUn, eval, dmModel, towerModel, map_mul, map_pow,
    MpcMkC6.mpcMkC6Un]
  rfl

theorem eval_sparseIncrement :
    eval dmModel.val sparseIncrement = levelMk (DM 2 0 : Type) 6
      (mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
        mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) := by
  rw [show mpcFvW5.2.1 = mpcBldW * mpcFvUt from rfl,
    show mpcFvW5.2.2.2 = mpcFvUn from by simp only [mpcFvW5, one_mul]]
  rw [eval_sparseIncrement_shape, eval_mkUs, eval_mkUt, eval_mkUm, eval_mkUn,
    eval_A, eval_C, eval_BT, eval_DN]
  simp only [mpcSxA, mpcSxB, mpcSxC, mpcSxD, mpcSxW, mpcSxN, mpcBldIncr,
    mpcWordLetB, mpcWordLetD, mpcBldW, mpcFvUt, mpcFvUn,
    map_mul, map_pow, mpcBld_map_commP]

/-- The single reflected word whose checked reduction to `one` is the remaining certificate. -/
def certificateWord : CWord := .mul closedDefect sparseIncrement

theorem closedDefect_depth : closedDefect.depth = 3 := by decide
theorem sparseIncrement_depth : sparseIncrement.depth = 5 := by decide
theorem certificateWord_depth : certificateWord.depth = 3 := by decide

theorem eval_certificateWord :
    eval dmModel.val certificateWord = levelMk (DM 2 0 : Type) 6
      (mpcLadDefect mpcFvW5 *
        mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
          mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) := by
  simp only [certificateWord, eval, eval_closedDefect, eval_sparseIncrement, map_mul]

theorem certificateKill_iff_checkedWord :
    MpcMkC6CertificateKill ↔ eval dmModel.val certificateWord = 1 := by
  rw [eval_certificateWord]
  rfl

#print axioms eval_closedDefect
#print axioms eval_sparseIncrement
#print axioms eval_certificateWord
#print axioms certificateKill_iff_checkedWord

end Bridge
end GQ2.Dyadic.Instances.MpcC6WeightedCertificate
