import GQ2.Roe.Labute.MixedPowerCongruence
import GQ2.Dyadic.SqCore.GradedGammaThreeFour

/-!
# A relative mixed correction in actual two-central quotients

This file proves the five-factor cancellation underlying the proposed relative
N-plane correction.  Its parameters are arbitrary group elements and an arbitrary
depth, not a finite list of nilpotency classes.  It is not yet a relator-preserving
automorphism or a producer of `NPlaneScalingHypothesis`.
-/

namespace GQ2.Dyadic.MarkedCore

open Roe.Labute SqCore

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem mixedGroup_map_commP {H : Type*} [Group H] (f : G →* H) (x y : G) :
    f (commP x y) = commP (f x) (f y) := by simp only [commP, map_mul, map_inv]

/-- The grouped derivative contributions of one ordinary correction and its
four compensators.  The two equal head-slot brackets have already canceled. -/
def nMixedCorrectionWord (v g b : G) (n : ℕ) : G :=
  commP (v ^ (2 ^ (n + 1))) g * (commP v g ^ (2 ^ n)) ^ 2 *
    commP (commP v g ^ (2 ^ n)) b *
    commP ((commP v g * commP g b) ^ (2 ^ n)) v *
    commP (commP v b ^ (2 ^ n)) g

private theorem mixedGroup_comm_mem (v g : G) : commP v g ∈ twoCentralSeries G 2 :=
  commP_mem_twoCentralSeries_add (G := G) (a := 1) (b := 1)
    (by rw [twoCentralSeries_one]; trivial) (by rw [twoCentralSeries_one]; trivial)

/-- Hall--Witt gives the initial actual-group cancellation. -/
theorem nMixedCorrectionWord_level_four (v g b : G) :
    levelMk G 4 (nMixedCorrectionWord v g b 0) = 1 := by
  let f := levelMk G 4
  let q := commP (f v) (f g)
  let t := commP q (f v)
  let B := commP q (f b)
  let C := commP (commP (f g) (f b)) (f v)
  let D := commP (commP (f v) (f b)) (f g)
  have hq : q ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo (f v) (f g)
  have ht : t ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hq (f v)
  have hq2 : q ^ 2 ∈ zLayer G 3 := by
    refine ⟨commP v g ^ 2, sq_mem_twoCentralSeries_succ G (mixedGroup_comm_mem v g), ?_⟩
    simp only [map_pow, mixedGroup_map_commP, q, f]
  have hcancel : (q ^ 2 * t) * q ^ 2 = t := by
    rw [(zLayer_commute hq2 t).eq]
    calc
      t * q ^ 2 * q ^ 2 = t * (q ^ 2) ^ 2 := by simp only [pow_two]; group
      _ = t := by rw [zLayer_sq G hq2, mul_one]
  have hj : B * C * D = 1 := by
    have hh := gThreeFour_jacobi (f v) (f g) (f b)
    have hi : commP (f b) (f v) = (commP (f v) (f b))⁻¹ := by
      simp only [commP]; group
    rw [hi, gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo (f v) (f b))] at hh
    exact hh
  change f (nMixedCorrectionWord v g b 0) = 1
  simp only [nMixedCorrectionWord, Nat.zero_add, pow_zero, pow_one, map_mul,
    mixedGroup_map_commP, map_pow]
  rw [gThreeFour_commP_sq_left, gThreeFour_ad_left hq
    (commP (f g) (f b)) (f v)]
  change (q ^ 2 * t) * q ^ 2 * B * (t * C) * D = 1
  rw [hcancel]
  calc
    t * B * (t * C) * D = B * (t * t) * C * D := by
      rw [(zLayer_commute ht B).eq]; group
    _ = B * C * D := by rw [← pow_two, zLayer_sq G ht, mul_one]
    _ = 1 := hj

private theorem mixedGroup_image_comm {j k : ℕ} {x : levelQuot G k}
    (hx : x ∈ lambdaImage G j k) (y : levelQuot G k) :
    commP x y ∈ lambdaImage G (j + 1) k := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := levelMk_surjective G k y
  refine ⟨commP a b, commP_mem_twoCentralSeries_add ha
    (by rw [twoCentralSeries_one]; trivial), ?_⟩
  exact mixedGroup_map_commP _ _ _

private theorem mixedGroup_image_sq {j k : ℕ} {x : levelQuot G k}
    (hx : x ∈ lambdaImage G j k) : x ^ 2 ∈ lambdaImage G (j + 1) k := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a ^ 2, sq_mem_twoCentralSeries_succ G ha, by rw [map_pow]⟩

private theorem mixedGroup_five_sq (k : ℕ) (hk : 4 ≤ k)
    (v g b : levelQuot G (k + 1)) (u : Fin 4 → levelQuot G (k + 1))
    (hu : ∀ i, u i ∈ lambdaImage G (k - 2) (k + 1)) :
    (commP (u 0) g * (u 1) ^ 2 * commP (u 1) b * commP (u 2) v * commP (u 3) g) ^ 2 =
      commP ((u 0) ^ 2) g * ((u 1) ^ 2) ^ 2 * commP ((u 1) ^ 2) b *
        commP ((u 2) ^ 2) v * commP ((u 3) ^ 2) g := by
  have hc (i : Fin 4) (z : levelQuot G (k + 1)) :
      commP (u i) z ∈ lambdaImage G (k - 1) (k + 1) := by
    simpa only [show k - 2 + 1 = k - 1 by omega] using mixedGroup_image_comm (hu i) z
  have hs : (u 1) ^ 2 ∈ lambdaImage G (k - 1) (k + 1) := by
    simpa only [show k - 2 + 1 = k - 1 by omega] using mixedGroup_image_sq (hu 1)
  have h01 := (lambdaImage G (k - 1) (k + 1)).mul_mem (hc 0 g) hs
  have h012 := (lambdaImage G (k - 1) (k + 1)).mul_mem h01 (hc 1 b)
  have h0123 := (lambdaImage G (k - 1) (k + 1)).mul_mem h012 (hc 2 v)
  rw [sq_mul_of_mem_lambdaImage_pred k (by omega) h0123 (hc 3 g),
    sq_mul_of_mem_lambdaImage_pred k (by omega) h012 (hc 2 v),
    sq_mul_of_mem_lambdaImage_pred k (by omega) h01 (hc 1 b),
    sq_mul_of_mem_lambdaImage_pred k (by omega) (hc 0 g) hs,
    commP_sq_of_mem_lambdaImage k hk g (hu 0),
    commP_sq_of_mem_lambdaImage k hk b (hu 1),
    commP_sq_of_mem_lambdaImage k hk v (hu 2),
    commP_sq_of_mem_lambdaImage k hk g (hu 3)]

/-- Every correction depth follows from Hall--Witt at the initial degree and
the two-central square transport.  This is the concrete uniform kernel word. -/
theorem nMixedCorrectionWord_level (v g b : G) (n : ℕ) :
    levelMk G (n + 4) (nMixedCorrectionWord v g b n) = 1 := by
  induction n with
  | zero => exact nMixedCorrectionWord_level_four v g b
  | succ n ih =>
      let f := levelMk G (n + 5)
      let u : Fin 4 → G := ![v ^ (2 ^ (n + 1)), commP v g ^ (2 ^ n),
        (commP v g * commP g b) ^ (2 ^ n), commP v b ^ (2 ^ n)]
      have hu : ∀ i, u i ∈ twoCentralSeries G (n + 2) := by
        intro i
        fin_cases i
        · simpa [u] using pow_two_pow_mem_twoCentralSeries_succ G v (n + 1)
        · simpa [u, Nat.add_comm] using
            pow_two_pow_mem_twoCentralSeries_add (mixedGroup_comm_mem v g) n
        · simpa [u, Nat.add_comm] using pow_two_pow_mem_twoCentralSeries_add
            ((twoCentralSeries G 2).mul_mem (mixedGroup_comm_mem v g) (mixedGroup_comm_mem g b)) n
        · simpa [u, Nat.add_comm] using
            pow_two_pow_mem_twoCentralSeries_add (mixedGroup_comm_mem v b) n
      have huf : ∀ i, f (u i) ∈ lambdaImage G ((n + 4) - 2) (n + 5) := by
        intro i
        exact ⟨u i, by simpa using hu i, rfl⟩
      have ht := mixedGroup_five_sq (n + 4) (by omega) (f v) (f g) (f b) (fun i => f (u i)) huf
      have htransport : f (nMixedCorrectionWord v g b n) ^ 2 =
          f (nMixedCorrectionWord v g b (n + 1)) := by
        simpa [nMixedCorrectionWord, u, mixedGroup_map_commP, map_mul, map_pow,
          pow_succ, pow_mul] using ht
      have hz := levelMk_sq_eq_of_eq (n + 4) (x := nMixedCorrectionWord v g b n) (y := 1)
        (by simpa using ih)
      change f (nMixedCorrectionWord v g b (n + 1)) = 1
      rw [← htransport]
      simpa only [f, map_one, one_pow] using hz

/-- The corresponding filtration-membership statement. -/
theorem nMixedCorrectionWord_mem (v g b : G) (n : ℕ) :
    nMixedCorrectionWord v g b n ∈ twoCentralSeries G (n + 4) :=
  (QuotientGroup.eq_one_iff _).mp (nMixedCorrectionWord_level v g b n)

/-- The identical cancellation before suppressing the two head-letter brackets.
This is the literal order of the five single-slot derivative contributions. -/
theorem nMixedCorrectionWord_with_head_level (a b v g : G) (n : ℕ) :
    let p := commP v g ^ (2 ^ n)
    levelMk G (n + 4)
      (commP (v ^ (2 ^ (n + 1))) g *
        ((p ^ 2 * commP p a) * commP p b) * commP p a *
        commP ((commP v g * commP g b) ^ (2 ^ n)) v *
        commP (commP v b ^ (2 ^ n)) g) = 1 := by
  let f := levelMk G (n + 4)
  let p := commP v g ^ (2 ^ n)
  have hp : p ∈ twoCentralSeries G (n + 2) := by
    simpa [p, Nat.add_comm] using
      pow_two_pow_mem_twoCentralSeries_add (mixedGroup_comm_mem v g) n
  have hpa : f (commP p a) ∈ zLayer G (n + 3) := by
    refine ⟨commP p a, ?_, rfl⟩
    exact commP_mem_twoCentralSeries_add (a := n + 2) (b := 1) hp
      (by rw [twoCentralSeries_one]; trivial)
  have he : ((f p ^ 2 * f (commP p a)) * f (commP p b)) * f (commP p a) =
      f p ^ 2 * f (commP p b) := by
    calc
      ((f p ^ 2 * f (commP p a)) * f (commP p b)) * f (commP p a) =
          f p ^ 2 * (f (commP p a) * f (commP p b)) * f (commP p a) := by group
      _ = f p ^ 2 * (f (commP p b) * f (commP p a)) * f (commP p a) := by
        rw [(zLayer_commute hpa _).eq]
      _ = (f p ^ 2 * f (commP p b)) * f (commP p a) ^ 2 := by simp only [pow_two]; group
      _ = f p ^ 2 * f (commP p b) := by rw [zLayer_sq G hpa, mul_one]
  change f _ = 1
  simp only [map_mul]
  rw [map_pow]
  rw [show f (commP (v ^ (2 ^ (n + 1))) g) *
      (f p ^ 2 * f (commP p a) * f (commP p b)) * f (commP p a) =
      f (commP (v ^ (2 ^ (n + 1))) g) * (f p ^ 2 * f (commP p b)) by
        rw [mul_assoc, he]]
  simpa only [nMixedCorrectionWord, p, f, map_mul, map_pow, mul_assoc] using
    nMixedCorrectionWord_level v g b n

#print axioms nMixedCorrectionWord_level_four
#print axioms nMixedCorrectionWord_level
#print axioms nMixedCorrectionWord_mem
#print axioms nMixedCorrectionWord_with_head_level

end GQ2.Dyadic.MarkedCore
