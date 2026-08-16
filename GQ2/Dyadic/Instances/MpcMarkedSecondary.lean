/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedSuccessor
import GQ2.Roe.Labute.StageLemma.Congruence

/-!
# The secondary marked defect for the procyclic-M ladder

This module computes the first error term beyond the marked affine cost formula.  In the
class-`(j+3)` quotient, the defect of `mpcMkAdvance` is the old defect, the visible marked
increment, and an explicit eight-factor Hall word.  That Hall word lies in `lambda_(j+2)`, so
the secondary defect splits canonically into the old kill equation lifted one layer and a
top-layer Hall class.

The calculation deliberately stops before the missing uniform `M6` theorem.  It does not
assert that the resulting secondary class lies in the fixed successor cost range; proving
that range membership (equivalently, its five obstruction coordinates vanish) remains the
new mathematical input.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new axiom,
no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {j : ℕ}

private theorem mem_one (x : levelQuot G (j + 3)) :
    x ∈ lambdaImage G 1 (j + 3) := by
  rw [lambdaImage_one_eq_top]
  trivial

private theorem comm_mem {a b : ℕ} {x y : levelQuot G (j + 3)}
    (hx : x ∈ lambdaImage G a (j + 3))
    (hy : y ∈ lambdaImage G b (j + 3)) :
    commP x y ∈ lambdaImage G (a + b) (j + 3) :=
  commP_mem_lambdaImage_add hx hy

private theorem sq_mem {a : ℕ} {x : levelQuot G (j + 3)}
    (hx : x ∈ lambdaImage G a (j + 3)) :
    x ^ 2 ∈ lambdaImage G (a + 1) (j + 3) := by
  obtain ⟨xx, hxx, rfl⟩ := hx
  exact ⟨xx ^ 2, sq_mem_twoCentralSeries_succ G hxx, by rw [map_pow]⟩

private theorem comm_vanish {a b : ℕ} {x y : levelQuot G (j + 3)}
    (hab : j + 3 ≤ a + b) (hx : x ∈ lambdaImage G a (j + 3))
    (hy : y ∈ lambdaImage G b (j + 3)) : commP x y = 1 := by
  have h := lambdaImage_le_of_le (G := G) (m := j + 3) hab (comm_mem hx hy)
  rw [lambdaImage_self] at h
  simpa using h

private theorem commute_of_vanish {a b : ℕ} {x y : levelQuot G (j + 3)}
    (hab : j + 3 ≤ a + b) (hx : x ∈ lambdaImage G a (j + 3))
    (hy : y ∈ lambdaImage G b (j + 3)) : Commute x y := by
  have h := comm_vanish hab hx hy
  have hh : x * y = y * x := by
    calc
      x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
      _ = y * x := by
        rw [show x⁻¹ * y⁻¹ * x * y = commP x y from rfl, h, mul_one]
  exact hh

private theorem gather3 {Q : Type*} [Group Q]
    {a b c z₁ z₂ z₃ : Q}
    (h₁ : ∀ x, Commute z₁ x) (h₂ : ∀ x, Commute z₂ x)
    (_h₃ : ∀ x, Commute z₃ x) :
    a * z₁ * (b * z₂ * c) * z₃ = a * b * c * (z₁ * z₂ * z₃) := by
  calc
    a * z₁ * (b * z₂ * c) * z₃ = a * (z₁ * b) * z₂ * c * z₃ := by group
    _ = a * (b * z₁) * z₂ * c * z₃ := by rw [(h₁ b).eq]
    _ = a * b * (z₁ * (z₂ * c)) * z₃ := by group
    _ = a * b * (z₁ * (c * z₂)) * z₃ := by rw [(h₂ c).eq]
    _ = a * b * ((z₁ * c) * z₂) * z₃ := by group
    _ = a * b * ((c * z₁) * z₂) * z₃ := by rw [(h₁ c).eq]
    _ = a * b * c * z₁ * z₂ * z₃ := by group
    _ = a * b * c * (z₁ * z₂ * z₃) := by group

private theorem gather4 {Q : Type*} [Group Q]
    {b₁ b₂ b₃ b₄ z₁ z₂ z₃ z₄ : Q}
    (h₁ : ∀ x, Commute z₁ x) (h₂ : ∀ x, Commute z₂ x)
    (h₃ : ∀ x, Commute z₃ x) (_h₄ : ∀ x, Commute z₄ x) :
    b₁ * z₁ * (b₂ * z₂) * (b₃ * z₃) * (b₄ * z₄) =
      b₁ * b₂ * b₃ * b₄ * (z₁ * z₂ * z₃ * z₄) := by
  have h123 : b₁ * z₁ * (b₂ * z₂ * b₃) * z₃ =
      b₁ * b₂ * b₃ * (z₁ * z₂ * z₃) :=
    gather3 h₁ h₂ h₃
  have hz123 : Commute (z₁ * z₂ * z₃) b₄ :=
    ((h₁ b₄).mul_left (h₂ b₄)).mul_left (h₃ b₄)
  calc
    b₁ * z₁ * (b₂ * z₂) * (b₃ * z₃) * (b₄ * z₄) =
        (b₁ * z₁ * (b₂ * z₂ * b₃) * z₃) * (b₄ * z₄) := by group
    _ = (b₁ * b₂ * b₃ * (z₁ * z₂ * z₃)) * (b₄ * z₄) := by rw [h123]
    _ = b₁ * b₂ * b₃ * ((z₁ * z₂ * z₃) * b₄) * z₄ := by group
    _ = b₁ * b₂ * b₃ * (b₄ * (z₁ * z₂ * z₃)) * z₄ := by rw [hz123.eq]
    _ = b₁ * b₂ * b₃ * b₄ * (z₁ * z₂ * z₃ * z₄) := by group

private theorem gatherCosts {Q : Type*} [Group Q]
    {a₁ a₂ a₃ a₄ c₁ c₂ c₃ : Q}
    (h₁₂ : Commute c₁ a₂) (h₁₃ : Commute c₁ a₃)
    (h₁₄ : Commute c₁ a₄) (h₂₃ : Commute c₂ a₃)
    (h₂₄ : Commute c₂ a₄) :
    a₁ * c₁ * (a₂ * c₂) * a₃ * a₄ * c₃ =
      a₁ * a₂ * a₃ * a₄ * (c₁ * c₂ * c₃) := by
  have h12_3 : Commute (c₁ * c₂) a₃ := h₁₃.mul_left h₂₃
  have h12_4 : Commute (c₁ * c₂) a₄ := h₁₄.mul_left h₂₄
  calc
    a₁ * c₁ * (a₂ * c₂) * a₃ * a₄ * c₃ =
        a₁ * (c₁ * a₂) * c₂ * a₃ * a₄ * c₃ := by group
    _ = a₁ * (a₂ * c₁) * c₂ * a₃ * a₄ * c₃ := by rw [h₁₂.eq]
    _ = a₁ * a₂ * (c₁ * c₂) * a₃ * a₄ * c₃ := by group
    _ = a₁ * a₂ * ((c₁ * c₂) * a₃) * a₄ * c₃ := by group
    _ = a₁ * a₂ * (a₃ * (c₁ * c₂)) * a₄ * c₃ := by rw [h12_3.eq]
    _ = a₁ * a₂ * a₃ * ((c₁ * c₂) * a₄) * c₃ := by group
    _ = a₁ * a₂ * a₃ * (a₄ * (c₁ * c₂)) * c₃ := by rw [h12_4.eq]
    _ = a₁ * a₂ * a₃ * a₄ * (c₁ * c₂ * c₃) := by group

private def nextCost (A C beta delta s t m n : levelQuot G (j + 3)) :
    levelQuot G (j + 3) :=
  s ^ 2 * commP s A * commP s beta * commP A t * commP m delta * commP C n

private def nextHall (alpha beta gamma delta yA yC s t m n : levelQuot G (j + 3)) :
    levelQuot G (j + 3) :=
  commP s yA *
    (commP yA t * commP (commP alpha beta) s *
      commP (commP (alpha * s) beta) t) *
    (m ^ 2 * commP m gamma) ^ 2 *
    (commP yC n * commP (commP gamma delta) m *
      commP (commP (gamma * m) delta) n)

private theorem nextCost_eq_incrementOrder
    (hj : 3 ≤ j) {A C beta delta s t m n : levelQuot G (j + 3)}
    (ht : t ∈ lambdaImage G j (j + 3))
    (hm : m ∈ lambdaImage G j (j + 3)) :
    nextCost A C beta delta s t m n =
      s ^ 2 * commP s A * commP s beta * commP m delta * commP A t * commP C n := by
  have hAt : commP A t ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa [add_comm] using comm_mem (mem_one A) ht
  have hmd : commP m delta ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa using comm_mem hm (mem_one delta)
  have hc : Commute (commP A t) (commP m delta) :=
    commute_of_vanish (a := j + 1) (b := j + 1) (by omega) hAt hmd
  simp only [nextCost, mul_assoc]
  change s ^ 2 * (commP s A * (commP s beta *
    (commP A t * (commP m delta * commP C n)))) = _
  rw [← mul_assoc (commP A t), hc.eq, mul_assoc (commP m delta)]

private theorem headSq
    (hj : 3 ≤ j) {A alpha y s : levelQuot G (j + 3)}
    (halpha : alpha = A * y) (hy : y ∈ lambdaImage G 2 (j + 3))
    (hs : s ∈ lambdaImage G j (j + 3)) :
    (alpha * s) ^ 2 =
      alpha ^ 2 * (s ^ 2 * commP s A) * commP s y := by
  have hA : A ∈ lambdaImage G 1 (j + 3) := mem_one A
  have hsA : commP s A ∈ lambdaImage G (j + 1) (j + 3) := comm_mem hs hA
  have hsy : commP s y ∈ zLayer G (j + 2) := by
    simpa only [show j + 2 = j + 2 from rfl] using comm_mem hs hy
  have hsalpha : commP s alpha ∈ lambdaImage G (j + 1) (j + 3) :=
    comm_mem hs (mem_one alpha)
  have hdeep : commP (commP s alpha) s = 1 :=
    comm_vanish (by omega) hsalpha hs
  have hAy : commP (commP s A) y = 1 :=
    comm_vanish (by omega) hsA hy
  rw [cfour_sq_mul, hdeep, mul_one, halpha, cfour_commP_mul_right, hAy, mul_one]
  rw [(zLayer_commute hsy (commP s A)).eq]
  group

private theorem headComm
    (hj : 3 ≤ j) {A alpha beta y s t : levelQuot G (j + 3)}
    (halpha : alpha = A * y) (hy : y ∈ lambdaImage G 2 (j + 3))
    (hs : s ∈ lambdaImage G j (j + 3))
    (ht : t ∈ lambdaImage G j (j + 3)) :
    commP (alpha * s) (beta * t) =
      commP alpha beta * (commP s beta * commP A t) *
        (commP y t * commP (commP alpha beta) s *
          commP (commP (alpha * s) beta) t) := by
  have hA : A ∈ lambdaImage G 1 (j + 3) := mem_one A
  have halpha1 : alpha ∈ lambdaImage G 1 (j + 3) := mem_one alpha
  have hbeta1 : beta ∈ lambdaImage G 1 (j + 3) := mem_one beta
  have hAt : commP A t ∈ lambdaImage G (1 + j) (j + 3) := comm_mem hA ht
  have hst : commP s t = 1 := comm_vanish (by omega) hs ht
  have halphat : commP alpha t ∈ lambdaImage G (1 + j) (j + 3) :=
    comm_mem halpha1 ht
  have hats : commP (commP alpha t) s = 1 :=
    comm_vanish (by omega) halphat hs
  have hAty : commP (commP A t) y = 1 :=
    comm_vanish (by omega) hAt hy
  have hyT : commP y t ∈ zLayer G (j + 2) := by
    simpa [add_comm] using comm_mem hy ht
  have hab : commP alpha beta ∈ lambdaImage G 2 (j + 3) :=
    comm_mem halpha1 hbeta1
  have habs : commP (commP alpha beta) s ∈ zLayer G (j + 2) := by
    simpa only [show 2 + j = j + 2 by omega] using comm_mem hab hs
  have hasb : commP (alpha * s) beta ∈ lambdaImage G 2 (j + 3) :=
    comm_mem (mem_one _) hbeta1
  have hasbt : commP (commP (alpha * s) beta) t ∈ zLayer G (j + 2) := by
    simpa only [show 2 + j = j + 2 by omega] using comm_mem hasb ht
  have hsb : commP s beta ∈ lambdaImage G (j + 1) (j + 3) :=
    comm_mem hs hbeta1
  have hcostComm : Commute (commP s beta) (commP A t) :=
    commute_of_vanish (a := j + 1) (b := j + 1) (by omega) hsb
      (by simpa [add_comm] using hAt)
  have holdS : Commute (commP alpha beta) (commP s beta) :=
    commute_of_vanish (a := 2) (b := j + 1) (by omega) hab hsb
  have holdT : Commute (commP alpha beta) (commP A t) :=
    commute_of_vanish (a := 2) (b := j + 1) (by omega) hab
      (by simpa [add_comm] using hAt)
  have hAtS : Commute (commP A t) (commP s beta) :=
    commute_of_vanish (a := j + 1) (b := j + 1) (by omega)
      (by simpa [add_comm] using hAt) hsb
  have h1 : commP (alpha * s) (beta * t) =
      commP (alpha * s) t * commP (alpha * s) beta *
        commP (commP (alpha * s) beta) t :=
    cfour_commP_mul_right _ _ _
  have h2 : commP (alpha * s) t = commP alpha t := by
    rw [cfour_commP_mul_left, hats, hst, mul_one, mul_one]
  have h3 : commP alpha t = commP A t * commP y t := by
    rw [halpha, cfour_commP_mul_left, hAty, mul_one]
  have h4 : commP (alpha * s) beta =
      commP alpha beta * commP (commP alpha beta) s * commP s beta :=
    cfour_commP_mul_left _ _ _
  rw [h1, h2, h3]
  nth_rewrite 1 [h4]
  calc
    commP A t * commP y t *
          (commP alpha beta * commP (commP alpha beta) s * commP s beta) *
        commP (commP (alpha * s) beta) t =
        commP A t * commP alpha beta * commP s beta *
          (commP y t * commP (commP alpha beta) s *
            commP (commP (alpha * s) beta) t) :=
      gather3 (fun x ↦ zLayer_commute hyT x) (fun x ↦ zLayer_commute habs x)
        (fun x ↦ zLayer_commute hasbt x)
    _ = commP alpha beta * (commP s beta * commP A t) *
          (commP y t * commP (commP alpha beta) s *
            commP (commP (alpha * s) beta) t) := by
      calc
        commP A t * commP alpha beta * commP s beta *
              (commP y t * commP (commP alpha beta) s *
                commP (commP (alpha * s) beta) t) =
            commP alpha beta * commP A t * commP s beta *
              (commP y t * commP (commP alpha beta) s *
                commP (commP (alpha * s) beta) t) := by rw [← holdT.eq]
        _ = commP alpha beta * (commP A t * commP s beta) *
              (commP y t * commP (commP alpha beta) s *
                commP (commP (alpha * s) beta) t) := by group
        _ = commP alpha beta * (commP s beta * commP A t) *
              (commP y t * commP (commP alpha beta) s *
                commP (commP (alpha * s) beta) t) := by rw [hAtS.eq]
        _ = _ := by group

private theorem pivotPow
    (hj : 3 ≤ j) {gamma m : levelQuot G (j + 3)}
    (hm : m ∈ lambdaImage G j (j + 3)) :
    (gamma * m) ^ 4 = gamma ^ 4 * (m ^ 2 * commP m gamma) ^ 2 := by
  have hmg : commP m gamma ∈ lambdaImage G (j + 1) (j + 3) :=
    comm_mem hm (mem_one gamma)
  have hdeep : commP (commP m gamma) m = 1 :=
    comm_vanish (by omega) hmg hm
  have hm2 : m ^ 2 ∈ lambdaImage G (j + 1) (j + 3) := sq_mem hm
  have hh : m ^ 2 * commP m gamma ∈ lambdaImage G (j + 1) (j + 3) :=
    Subgroup.mul_mem _ hm2 hmg
  have hgamma2 : gamma ^ 2 ∈ lambdaImage G 2 (j + 3) := sq_mem (mem_one gamma)
  have hc : Commute (gamma ^ 2) (m ^ 2 * commP m gamma) :=
    commute_of_vanish (by omega) hgamma2 hh
  rw [show (gamma * m) ^ 4 = ((gamma * m) ^ 2) ^ 2 by norm_num [← pow_mul],
    cfour_sq_mul, hdeep, mul_one]
  rw [mul_assoc]
  rw [hc.mul_pow]
  norm_num [← pow_mul]

private theorem pivotComm
    (hj : 3 ≤ j) {C gamma delta y m n : levelQuot G (j + 3)}
    (hgamma : gamma = C * y) (hy : y ∈ lambdaImage G 2 (j + 3))
    (hm : m ∈ lambdaImage G j (j + 3))
    (hn : n ∈ lambdaImage G j (j + 3)) :
    commP (gamma * m) (delta * n) =
      commP gamma delta * (commP m delta * commP C n) *
        (commP y n * commP (commP gamma delta) m *
          commP (commP (gamma * m) delta) n) :=
  headComm hj hgamma hy hm hn

private theorem mWordNext
    (hj : 3 ≤ j)
    {A C alpha beta gamma delta yA yC s t m n : levelQuot G (j + 3)}
    (halpha : alpha = A * yA) (hgamma : gamma = C * yC)
    (hyA : yA ∈ lambdaImage G 2 (j + 3))
    (hyC : yC ∈ lambdaImage G 2 (j + 3))
    (hs : s ∈ lambdaImage G j (j + 3))
    (ht : t ∈ lambdaImage G j (j + 3))
    (hm : m ∈ lambdaImage G j (j + 3))
    (hn : n ∈ lambdaImage G j (j + 3)) :
    mWord 2 (alpha * s) (beta * t) (gamma * m) (delta * n) =
      mWord 2 alpha beta gamma delta * nextCost A C beta delta s t m n *
        nextHall alpha beta gamma delta yA yC s t m n := by
  let a₁ := alpha ^ 2
  let a₂ := commP alpha beta
  let a₃ := gamma ^ 4
  let a₄ := commP gamma delta
  let c₁ := s ^ 2 * commP s A
  let c₂ := commP s beta * commP A t
  let c₃ := commP m delta * commP C n
  let e₁ := commP s yA
  let e₂ := commP yA t * commP (commP alpha beta) s *
    commP (commP (alpha * s) beta) t
  let e₃ := (m ^ 2 * commP m gamma) ^ 2
  let e₄ := commP yC n * commP (commP gamma delta) m *
    commP (commP (gamma * m) delta) n
  have hA1 : A ∈ lambdaImage G 1 (j + 3) := mem_one A
  have hC1 : C ∈ lambdaImage G 1 (j + 3) := mem_one C
  have halpha1 : alpha ∈ lambdaImage G 1 (j + 3) := mem_one alpha
  have hbeta1 : beta ∈ lambdaImage G 1 (j + 3) := mem_one beta
  have hgamma1 : gamma ∈ lambdaImage G 1 (j + 3) := mem_one gamma
  have hdelta1 : delta ∈ lambdaImage G 1 (j + 3) := mem_one delta
  have ha₁ : a₁ ∈ lambdaImage G 2 (j + 3) := sq_mem halpha1
  have ha₂ : a₂ ∈ lambdaImage G 2 (j + 3) := comm_mem halpha1 hbeta1
  have ha₃' : gamma ^ 2 ∈ lambdaImage G 2 (j + 3) := sq_mem hgamma1
  have ha₃deep : a₃ ∈ lambdaImage G 3 (j + 3) := by
    simpa [a₃, show gamma ^ 4 = (gamma ^ 2) ^ 2 by norm_num [← pow_mul]] using sq_mem ha₃'
  have ha₃ : a₃ ∈ lambdaImage G 2 (j + 3) :=
    lambdaImage_le_of_le (by omega) ha₃deep
  have ha₄ : a₄ ∈ lambdaImage G 2 (j + 3) := comm_mem hgamma1 hdelta1
  have hs2 : s ^ 2 ∈ lambdaImage G (j + 1) (j + 3) := sq_mem hs
  have hsA : commP s A ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa using comm_mem hs hA1
  have hsb : commP s beta ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa using comm_mem hs hbeta1
  have hAt : commP A t ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa [add_comm] using comm_mem hA1 ht
  have hmd : commP m delta ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa using comm_mem hm hdelta1
  have hCn : commP C n ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa [add_comm] using comm_mem hC1 hn
  have hc₁ : c₁ ∈ lambdaImage G (j + 1) (j + 3) := Subgroup.mul_mem _ hs2 hsA
  have hc₂ : c₂ ∈ lambdaImage G (j + 1) (j + 3) := Subgroup.mul_mem _ hsb hAt
  have hc₃ : c₃ ∈ lambdaImage G (j + 1) (j + 3) := Subgroup.mul_mem _ hmd hCn
  have hcostOld : ∀ {c a : levelQuot G (j + 3)},
      c ∈ lambdaImage G (j + 1) (j + 3) →
      a ∈ lambdaImage G 2 (j + 3) → Commute c a := by
    intro c a hc ha
    exact commute_of_vanish (a := j + 1) (b := 2) (by omega) hc ha
  have he₁ : e₁ ∈ zLayer G (j + 2) := by simpa [e₁] using comm_mem hs hyA
  have he₂ : e₂ ∈ zLayer G (j + 2) := by
    have h1 : commP yA t ∈ zLayer G (j + 2) := by simpa [add_comm] using comm_mem hyA ht
    have h2 : commP (commP alpha beta) s ∈ zLayer G (j + 2) := by
      simpa only [show 2 + j = j + 2 by omega] using comm_mem ha₂ hs
    have hasb : commP (alpha * s) beta ∈ lambdaImage G 2 (j + 3) :=
      comm_mem (a := 1) (b := 1) (x := alpha * s) (y := beta) (mem_one _) hbeta1
    have h3 : commP (commP (alpha * s) beta) t ∈ zLayer G (j + 2) := by
      simpa only [show 2 + j = j + 2 by omega] using comm_mem hasb ht
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have hm2 : m ^ 2 ∈ lambdaImage G (j + 1) (j + 3) := sq_mem hm
  have hmg : commP m gamma ∈ lambdaImage G (j + 1) (j + 3) := by
    simpa using comm_mem hm hgamma1
  have he₃ : e₃ ∈ zLayer G (j + 2) := by
    simpa [e₃] using sq_mem (Subgroup.mul_mem _ hm2 hmg)
  have he₄ : e₄ ∈ zLayer G (j + 2) := by
    have h1 : commP yC n ∈ zLayer G (j + 2) := by simpa [add_comm] using comm_mem hyC hn
    have h2 : commP (commP gamma delta) m ∈ zLayer G (j + 2) := by
      simpa only [show 2 + j = j + 2 by omega] using comm_mem ha₄ hm
    have hgmd : commP (gamma * m) delta ∈ lambdaImage G 2 (j + 3) :=
      comm_mem (a := 1) (b := 1) (x := gamma * m) (y := delta) (mem_one _) hdelta1
    have h3 : commP (commP (gamma * m) delta) n ∈ zLayer G (j + 2) := by
      simpa only [show 2 + j = j + 2 by omega] using comm_mem hgmd hn
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have hblocks :
      a₁ * c₁ * e₁ * (a₂ * c₂ * e₂) * (a₃ * e₃) * (a₄ * c₃ * e₄) =
        a₁ * a₂ * a₃ * a₄ * (c₁ * c₂ * c₃) * (e₁ * e₂ * e₃ * e₄) := by
    calc
      a₁ * c₁ * e₁ * (a₂ * c₂ * e₂) * (a₃ * e₃) * (a₄ * c₃ * e₄) =
          (a₁ * c₁) * e₁ * ((a₂ * c₂) * e₂) * (a₃ * e₃) *
            ((a₄ * c₃) * e₄) := by group
      _ = (a₁ * c₁) * (a₂ * c₂) * a₃ * (a₄ * c₃) *
            (e₁ * e₂ * e₃ * e₄) :=
        gather4 (fun x ↦ zLayer_commute he₁ x) (fun x ↦ zLayer_commute he₂ x)
          (fun x ↦ zLayer_commute he₃ x) (fun x ↦ zLayer_commute he₄ x)
      _ = a₁ * c₁ * (a₂ * c₂) * a₃ * a₄ * c₃ *
            (e₁ * e₂ * e₃ * e₄) := by group
      _ = a₁ * a₂ * a₃ * a₄ * (c₁ * c₂ * c₃) *
            (e₁ * e₂ * e₃ * e₄) := by
        rw [gatherCosts (hcostOld hc₁ ha₂) (hcostOld hc₁ ha₃)
          (hcostOld hc₁ ha₄) (hcostOld hc₂ ha₃) (hcostOld hc₂ ha₄)]
  rw [mWord, show (2 : ℕ) ^ 2 = 4 from rfl,
    headSq hj halpha hyA hs, headComm hj halpha hyA hs ht,
    pivotPow hj hm, pivotComm hj hgamma hyC hm hn]
  simpa only [a₁, a₂, a₃, a₄, c₁, c₂, c₃, e₁, e₂, e₃, e₄,
    nextCost, nextHall, mWord, show (2 : ℕ) ^ 2 = 4 from rfl, mul_assoc] using hblocks

end Generic

/-- A correction quadruple in head, `B`, pivot, and `D` order. -/
abbrev MpcMkPoint :=
  (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)

private def aCorr (p : MpcMkPoint) : (DM 2 0 : Type) :=
  (dmB 2 0 ^ 4)⁻¹ * p.1

private def cCorr (p : MpcMkPoint) : (DM 2 0 : Type) :=
  dmB 2 0 ^ 2 * commP (dmB 2 0 ^ 2) (dmC 2 0) * p.2.2.1

private def killWord {j : ℕ} (p : MpcMkPoint) (u : MpcMkCostDomain j) :
    (DM 2 0 : Type) :=
  mpcLadDefect p * mpcBldIncr p.2.1 p.2.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2

open scoped commutatorElement in
private theorem twoCentral_commP_mem_add {a b : ℕ} {x y : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) a)
    (hy : y ∈ twoCentralSeries (DM 2 0 : Type) b) :
    commP x y ∈ twoCentralSeries (DM 2 0 : Type) (a + b) := by
  rw [show commP x y = ⁅x⁻¹, y⁻¹⁆ by simp only [commP, commutatorElement_def, inv_inv]]
  exact commutator_mem_twoCentralSeries_add (DM 2 0 : Type)
    ((twoCentralSeries (DM 2 0 : Type) a).inv_mem hx)
    ((twoCentralSeries (DM 2 0 : Type) b).inv_mem hy)

/-- The eight top-order Hall factors created by a depth-`j` full marked move. -/
def mpcMkAdvanceHall (j : ℕ) (p : MpcMkPoint) (u : MpcMkCostDomain j) :
    (DM 2 0 : Type) :=
  commP (u.1 : (DM 2 0 : Type)) (aCorr p) *
    (commP (aCorr p) (u.2.1 : (DM 2 0 : Type)) *
      commP (commP (mpcWordLetA p.1) (mpcWordLetB p.2.1))
        (u.1 : (DM 2 0 : Type)) *
      commP (commP (mpcWordLetA p.1 * (u.1 : (DM 2 0 : Type)))
        (mpcWordLetB p.2.1)) (u.2.1 : (DM 2 0 : Type))) *
    ((u.2.2.1 : (DM 2 0 : Type)) ^ 2 *
      commP (u.2.2.1 : (DM 2 0 : Type)) (mpcWordLetC p.2.2.1)) ^ 2 *
    (commP (cCorr p) (u.2.2.2 : (DM 2 0 : Type)) *
      commP (commP (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2))
        (u.2.2.1 : (DM 2 0 : Type)) *
      commP (commP (mpcWordLetC p.2.2.1 * (u.2.2.1 : (DM 2 0 : Type)))
        (mpcWordLetD p.2.2.2)) (u.2.2.2 : (DM 2 0 : Type)))

/-- The explicit Hall correction lies exactly in the secondary top layer. -/
theorem mpcMk_advanceHall_mem {j : ℕ} {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j) :
    mpcMkAdvanceHall j p u ∈ twoCentralSeries (DM 2 0 : Type) (j + 2) := by
  let e₁ := commP (u.1 : (DM 2 0 : Type)) (aCorr p)
  let e₂ := commP (aCorr p) (u.2.1 : (DM 2 0 : Type)) *
    commP (commP (mpcWordLetA p.1) (mpcWordLetB p.2.1))
      (u.1 : (DM 2 0 : Type)) *
    commP (commP (mpcWordLetA p.1 * (u.1 : (DM 2 0 : Type)))
      (mpcWordLetB p.2.1)) (u.2.1 : (DM 2 0 : Type))
  let e₃ := ((u.2.2.1 : (DM 2 0 : Type)) ^ 2 *
    commP (u.2.2.1 : (DM 2 0 : Type)) (mpcWordLetC p.2.2.1)) ^ 2
  let e₄ := commP (cCorr p) (u.2.2.2 : (DM 2 0 : Type)) *
    commP (commP (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2))
      (u.2.2.1 : (DM 2 0 : Type)) *
    commP (commP (mpcWordLetC p.2.2.1 * (u.2.2.1 : (DM 2 0 : Type)))
      (mpcWordLetD p.2.2.2)) (u.2.2.2 : (DM 2 0 : Type))
  have hone (x : (DM 2 0 : Type)) :
      x ∈ twoCentralSeries (DM 2 0 : Type) 1 := by
    rw [twoCentralSeries_one]
    trivial
  have hyA : aCorr p ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
    mpcBld_letA_corr_mem hp.1.1
  have hyC : cCorr p ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
    mpcBld_letC_corr_mem hp.2.2.1.1.1
  have hs := u.1.2.2
  have ht := u.2.1.2.2
  have hm := u.2.2.1.2.2
  have hn := u.2.2.2.2.2
  have he₁ : e₁ ∈ twoCentralSeries (DM 2 0 : Type) (j + 2) := by
    simpa [e₁] using twoCentral_commP_mem_add hs hyA
  have he₂ : e₂ ∈ twoCentralSeries (DM 2 0 : Type) (j + 2) := by
    have h1 : commP (aCorr p) (u.2.1 : (DM 2 0 : Type)) ∈
        twoCentralSeries (DM 2 0 : Type) (j + 2) := by
      simpa [add_comm] using twoCentral_commP_mem_add hyA ht
    have hab : commP (mpcWordLetA p.1) (mpcWordLetB p.2.1) ∈
        twoCentralSeries (DM 2 0 : Type) 2 :=
      twoCentral_commP_mem_add (hone _) (hone _)
    have h2 : commP (commP (mpcWordLetA p.1) (mpcWordLetB p.2.1))
        (u.1 : (DM 2 0 : Type)) ∈
          twoCentralSeries (DM 2 0 : Type) (j + 2) := by
      simpa [add_comm] using twoCentral_commP_mem_add hab hs
    have hasb : commP (mpcWordLetA p.1 * (u.1 : (DM 2 0 : Type)))
        (mpcWordLetB p.2.1) ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
      twoCentral_commP_mem_add (hone _) (hone _)
    have h3 : commP (commP (mpcWordLetA p.1 * (u.1 : (DM 2 0 : Type)))
        (mpcWordLetB p.2.1)) (u.2.1 : (DM 2 0 : Type)) ∈
          twoCentralSeries (DM 2 0 : Type) (j + 2) := by
      simpa [add_comm] using twoCentral_commP_mem_add hasb ht
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have he₃ : e₃ ∈ twoCentralSeries (DM 2 0 : Type) (j + 2) := by
    have hm2 : (u.2.2.1 : (DM 2 0 : Type)) ^ 2 ∈
        twoCentralSeries (DM 2 0 : Type) (j + 1) :=
      sq_mem_twoCentralSeries_succ (DM 2 0 : Type) hm
    have hmc : commP (u.2.2.1 : (DM 2 0 : Type)) (mpcWordLetC p.2.2.1) ∈
        twoCentralSeries (DM 2 0 : Type) (j + 1) := by
      simpa using twoCentral_commP_mem_add hm (hone _)
    simpa [e₃] using sq_mem_twoCentralSeries_succ (DM 2 0 : Type)
      (Subgroup.mul_mem _ hm2 hmc)
  have he₄ : e₄ ∈ twoCentralSeries (DM 2 0 : Type) (j + 2) := by
    have h1 : commP (cCorr p) (u.2.2.2 : (DM 2 0 : Type)) ∈
        twoCentralSeries (DM 2 0 : Type) (j + 2) := by
      simpa [add_comm] using twoCentral_commP_mem_add hyC hn
    have hcd : commP (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2) ∈
        twoCentralSeries (DM 2 0 : Type) 2 :=
      twoCentral_commP_mem_add (hone _) (hone _)
    have h2 : commP (commP (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2))
        (u.2.2.1 : (DM 2 0 : Type)) ∈
          twoCentralSeries (DM 2 0 : Type) (j + 2) := by
      simpa [add_comm] using twoCentral_commP_mem_add hcd hm
    have hcmd : commP (mpcWordLetC p.2.2.1 * (u.2.2.1 : (DM 2 0 : Type)))
        (mpcWordLetD p.2.2.2) ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
      twoCentral_commP_mem_add (hone _) (hone _)
    have h3 : commP (commP (mpcWordLetC p.2.2.1 * (u.2.2.1 : (DM 2 0 : Type)))
        (mpcWordLetD p.2.2.2)) (u.2.2.2 : (DM 2 0 : Type)) ∈
          twoCentralSeries (DM 2 0 : Type) (j + 2) := by
      simpa [add_comm] using twoCentral_commP_mem_add hcmd hn
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  simpa only [mpcMkAdvanceHall, e₁, e₂, e₃, e₄, mul_assoc] using
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ he₁ he₂) he₃) he₄

theorem mpcMk_defect_advance_nextHall {j : ℕ} (hj : 3 ≤ j) {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j) :
    levelMk (DM 2 0 : Type) (j + 3) (mpcLadDefect (mpcMkAdvance j p u)) =
      levelMk (DM 2 0 : Type) (j + 3)
        (mpcLadDefect p *
          mpcBldIncr p.2.1 p.2.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2 *
          mpcMkAdvanceHall j p u) := by
  let f := levelMk (DM 2 0 : Type) (j + 3)
  have hyA0 : aCorr p ∈ twoCentralSeries (DM 2 0 : Type) 2 := by
    exact mpcBld_letA_corr_mem hp.1.1
  have hyC0 : cCorr p ∈ twoCentralSeries (DM 2 0 : Type) 2 := by
    exact mpcBld_letC_corr_mem hp.2.2.1.1.1
  have hyA : f (aCorr p) ∈ lambdaImage (DM 2 0 : Type) 2 (j + 3) :=
    ⟨aCorr p, hyA0, rfl⟩
  have hyC : f (cCorr p) ∈ lambdaImage (DM 2 0 : Type) 2 (j + 3) :=
    ⟨cCorr p, hyC0, rfl⟩
  have hs : f u.1 ∈ lambdaImage (DM 2 0 : Type) j (j + 3) :=
    ⟨u.1, u.1.2.2, rfl⟩
  have ht : f u.2.1 ∈ lambdaImage (DM 2 0 : Type) j (j + 3) :=
    ⟨u.2.1, u.2.1.2.2, rfl⟩
  have hm : f u.2.2.1 ∈ lambdaImage (DM 2 0 : Type) j (j + 3) :=
    ⟨u.2.2.1, u.2.2.1.2.2, rfl⟩
  have hn : f u.2.2.2 ∈ lambdaImage (DM 2 0 : Type) j (j + 3) :=
    ⟨u.2.2.2, u.2.2.2.2.2, rfl⟩
  have hAshape : f (mpcWordLetA p.1) = f (dmA 2 0) * f (aCorr p) := by
    rw [mpcBld_letA_shape, map_mul]
    rfl
  have hCshape : f (mpcWordLetC p.2.2.1) = f (dmC 2 0) * f (cCorr p) := by
    rw [mpcBld_letC_shape, map_mul]
    rfl
  have hmain := mWordNext (G := (DM 2 0 : Type)) hj
    (A := f (dmA 2 0)) (C := f (dmC 2 0))
    (alpha := f (mpcWordLetA p.1)) (beta := f (mpcWordLetB p.2.1))
    (gamma := f (mpcWordLetC p.2.2.1)) (delta := f (mpcWordLetD p.2.2.2))
    (yA := f (aCorr p)) (yC := f (cCorr p))
    (s := f u.1) (t := f u.2.1) (m := f u.2.2.1) (n := f u.2.2.2)
    hAshape hCshape hyA hyC hs ht hm hn
  rw [nextCost_eq_incrementOrder hj ht hm] at hmain
  change mWord 2 (f (mpcWordLetA p.1) * f u.1)
      (f (mpcWordLetB p.2.1) * f u.2.1)
      (f (mpcWordLetC p.2.2.1) * f u.2.2.1)
      (f (mpcWordLetD p.2.2.2) * f u.2.2.2) = _ at hmain
  have hLA : mpcWordLetA (p.1 * (u.1 : (DM 2 0 : Type))) =
      mpcWordLetA p.1 * (u.1 : (DM 2 0 : Type)) := by
    simp only [mpcWordLetA]
    group
  have hLB : mpcWordLetB (p.2.1 * (u.2.1 : (DM 2 0 : Type))) =
      mpcWordLetB p.2.1 * (u.2.1 : (DM 2 0 : Type)) := by
    simp only [mpcWordLetB]
    group
  have hLC : mpcWordLetC (p.2.2.1 * (u.2.2.1 : (DM 2 0 : Type))) =
      mpcWordLetC p.2.2.1 * (u.2.2.1 : (DM 2 0 : Type)) := by
    simp only [mpcWordLetC]
    group
  have hLD : mpcWordLetD (p.2.2.2 * (u.2.2.2 : (DM 2 0 : Type))) =
      mpcWordLetD p.2.2.2 * (u.2.2.2 : (DM 2 0 : Type)) := by
    simp only [mpcWordLetD]
    group
  simpa only [mpcLadDefect, mpcMkAdvance, map_mul, map_pow, mpcBld_map_commP,
    map_mWord, hLA, hLB, hLC, hLD, mpcBldIncr, mpcMkAdvanceHall, aCorr, cCorr,
    nextHall, f, mul_assoc] using hmain

/-- The old marked kill equation, retained one layer higher as a canonical residual. -/
def mpcMkKillLiftResidual {j : ℕ} (hj : 2 ≤ j) {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j hj p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    zLayer (DM 2 0 : Type) (j + 2) := by
  refine ⟨levelMk (DM 2 0 : Type) (j + 3) (killWord p u), ?_⟩
  refine ⟨killWord p u, ?_, rfl⟩
  apply (mpcWord_mem_iff_levelMk (j + 2) (killWord p u)).mpr
  rw [killWord, map_mul]
  have heq : levelMk (DM 2 0 : Type) (j + 2)
      (mpcBldIncr p.2.1 p.2.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2) =
      levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) :=
    congrArg Subtype.val hu
  rw [heq, ← pow_two]
  exact zLayer_sq _ (mpcMkDefectTop j p hp).2

/-- The Hall correction as a class in the secondary top layer. -/
def mpcMkAdvanceHallTop {j : ℕ} {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j) :
    zLayer (DM 2 0 : Type) (j + 2) :=
  ⟨levelMk (DM 2 0 : Type) (j + 3) (mpcMkAdvanceHall j p u),
    ⟨mpcMkAdvanceHall j p u, mpcMk_advanceHall_mem hp u, rfl⟩⟩

/-- Exact secondary decomposition: the advanced defect is the lifted old kill residual times
the explicit eight-factor Hall correction.  Showing this product lies in the successor cost
range is the remaining uniform `M6` input. -/
theorem mpcMkDefectTop_advance_eq_liftResidual_mul_hall {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    mpcMkDefectTop (j + 1) (mpcMkAdvance j p u)
        (mpcMk_advance_mem (by omega) hp u hu) =
      mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u := by
  apply Subtype.ext
  change levelMk (DM 2 0 : Type) (j + 3) (mpcLadDefect (mpcMkAdvance j p u)) =
    levelMk (DM 2 0 : Type) (j + 3) (killWord p u) *
      levelMk (DM 2 0 : Type) (j + 3) (mpcMkAdvanceHall j p u)
  rw [← map_mul]
  simpa only [killWord, mul_assoc] using mpcMk_defect_advance_nextHall hj hp u

#print axioms MpcMkPoint
#print axioms mpcMkAdvanceHall
#print axioms mpcMk_advanceHall_mem
#print axioms mpcMk_defect_advance_nextHall
#print axioms mpcMkKillLiftResidual
#print axioms mpcMkAdvanceHallTop
#print axioms mpcMkDefectTop_advance_eq_liftResidual_mul_hall

end


end GQ2.Dyadic.Instances.MpcMk
