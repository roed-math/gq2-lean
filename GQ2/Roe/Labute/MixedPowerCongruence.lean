import GQ2.Roe.Labute.GradedLie.SpanIdentities

/-!
# The actual group mixed-power congruence

For the one-based lower two-central series, the exceptional mixed-square term
persists at every depth:

`[v^(2^m), g] = [v,g]^(2^m) * [[v,g],v]^(2^(m-1))` modulo `λ_(m+3)`.

This is an identity in actual group quotients, uniform in `m ≥ 1`.  It does not
construct a graded Lie ring, a relative relator correction, or an automorphism.
No finiteness, free-group, or pro-two hypothesis is needed.
-/

namespace GQ2.Roe.Labute

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An iterated square raises the lower two-central depth by its iteration count. -/
theorem pow_two_pow_mem_twoCentralSeries_add {j : ℕ} {x : G}
    (hx : x ∈ twoCentralSeries G j) (n : ℕ) :
    x ^ (2 ^ n) ∈ twoCentralSeries G (j + n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      simpa only [pow_succ, pow_mul, Nat.add_assoc] using
        sq_mem_twoCentralSeries_succ G ih

open scoped commutatorElement in
/-- The additive grading bound in the repository's inverse-first convention. -/
theorem commP_mem_twoCentralSeries_add {a b : ℕ} {x y : G}
    (hx : x ∈ twoCentralSeries G a) (hy : y ∈ twoCentralSeries G b) :
    commP x y ∈ twoCentralSeries G (a + b) := by
  have h : commP x y = ⁅x⁻¹, y⁻¹⁆ := by
    simp only [commP, commutatorElement_def, inv_inv]
  rw [h]
  exact commutator_mem_twoCentralSeries_add G
    ((twoCentralSeries G a).inv_mem hx) ((twoCentralSeries G b).inv_mem hy)

/-- Congruent elements have congruent squares one level deeper. -/
theorem levelMk_sq_eq_of_eq (k : ℕ) {x y : G}
    (h : levelMk G k x = levelMk G k y) :
    levelMk G (k + 1) x ^ 2 = levelMk G (k + 1) y ^ 2 := by
  rw [sq_levelMk_eq_sq_canonLift G k x, sq_levelMk_eq_sq_canonLift G k y, h]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem map_commP_mixed {H : Type*} [Group H] (f : G →* H) (x y : G) :
    f (commP x y) = commP (f x) (f y) := by
  simp only [commP, map_mul, map_inv]

private theorem mixed_comm_mem (v g : G) : commP v g ∈ twoCentralSeries G 2 :=
  commP_mem_twoCentralSeries_add (G := G) (a := 1) (b := 1)
    (by rw [twoCentralSeries_one]; trivial)
    (by rw [twoCentralSeries_one]; trivial)

private theorem mixed_triple_mem (v g : G) :
    commP (commP v g) v ∈ twoCentralSeries G 3 :=
  commP_mem_twoCentralSeries_add (mixed_comm_mem v g)
    (by rw [twoCentralSeries_one]; trivial)

/-- The mixed-square identity, with its triple commutator, in the actual fourth
quotient.  The order of the two displayed factors follows `commP x y=x⁻¹y⁻¹xy`. -/
theorem commP_sq_level_four (v g : G) :
    levelMk G 4 (commP (v ^ 2) g) =
      levelMk G 4 (commP v g) ^ 2 * levelMk G 4 (commP (commP v g) v) := by
  let f := levelMk G 4
  have ht : f (commP (commP v g) v) ∈ zLayer G 3 :=
    ⟨commP (commP v g) v, mixed_triple_mem v g, rfl⟩
  have hc := (zLayer_commute ht (f (commP v g))).eq
  have he : commP (v ^ 2) g =
      commP v g * commP (commP v g) v * commP v g := by
    simp only [commP, pow_two]
    group
  change f (commP (v ^ 2) g) = f (commP v g) ^ 2 * f (commP (commP v g) v)
  rw [he, map_mul, map_mul]
  calc
    f (commP v g) * f (commP (commP v g) v) * f (commP v g) =
        f (commP v g) * (f (commP (commP v g) v) * f (commP v g)) := by group
    _ = f (commP v g) * (f (commP v g) * f (commP (commP v g) v)) := by rw [hc]
    _ = f (commP v g) ^ 2 * f (commP (commP v g) v) := by rw [pow_two]; group

/-- Uniform actual-group version of the exceptional mixed-power identity.  The
index `n+1` on the power covers every positive exponent iteration. -/
theorem commP_pow_two_succ_level (v g : G) (n : ℕ) :
    levelMk G (n + 4) (commP (v ^ (2 ^ (n + 1))) g) =
      levelMk G (n + 4) (commP v g) ^ (2 ^ (n + 1)) *
        levelMk G (n + 4) (commP (commP v g) v) ^ (2 ^ n) := by
  induction n with
  | zero => simpa using commP_sq_level_four v g
  | succ n ih =>
      let f := levelMk G (n + 5)
      let q := commP v g
      let t := commP q v
      have hv : f (v ^ (2 ^ (n + 1))) ∈ lambdaImage G ((n + 4) - 2) (n + 5) := by
        refine ⟨v ^ (2 ^ (n + 1)), ?_, rfl⟩
        simpa using pow_two_pow_mem_twoCentralSeries_succ G v (n + 1)
      have hq : f q ^ (2 ^ (n + 1)) ∈ lambdaImage G ((n + 4) - 1) (n + 5) := by
        refine ⟨q ^ (2 ^ (n + 1)), ?_, by rw [map_pow]⟩
        simpa [q, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          pow_two_pow_mem_twoCentralSeries_add (mixed_comm_mem v g) (n + 1)
      have ht : f t ^ (2 ^ n) ∈ lambdaImage G ((n + 4) - 1) (n + 5) := by
        refine ⟨t ^ (2 ^ n), ?_, by rw [map_pow]⟩
        simpa [t, q, Nat.add_comm] using
          pow_two_pow_mem_twoCentralSeries_add (mixed_triple_mem v g) n
      have hs : f (commP (v ^ (2 ^ (n + 1))) g) ^ 2 =
          (f q ^ (2 ^ (n + 1)) * f t ^ (2 ^ n)) ^ 2 := by
        have hh := levelMk_sq_eq_of_eq (n + 4)
          (x := commP (v ^ (2 ^ (n + 1))) g)
          (y := q ^ (2 ^ (n + 1)) * t ^ (2 ^ n))
          (by simpa only [q, t, map_mul, map_pow] using ih)
        simpa only [f, map_mul, map_pow] using hh
      have hc := commP_sq_of_mem_lambdaImage (G := G) (n + 4) (by omega) (f g) hv
      change f (commP (v ^ (2 ^ (n + 1 + 1))) g) =
        f q ^ (2 ^ (n + 1 + 1)) * f t ^ (2 ^ (n + 1))
      calc
        f (commP (v ^ (2 ^ (n + 1 + 1))) g) =
            f (commP (v ^ (2 ^ (n + 1))) g) ^ 2 := by
          rw [pow_succ, pow_mul, map_commP_mixed, map_pow]
          simpa only [map_commP_mixed] using hc.symm
        _ = (f q ^ (2 ^ (n + 1)) * f t ^ (2 ^ n)) ^ 2 := hs
        _ = (f q ^ (2 ^ (n + 1))) ^ 2 * (f t ^ (2 ^ n)) ^ 2 :=
          sq_mul_of_mem_lambdaImage_pred (n + 4) (by omega) hq ht
        _ = f q ^ (2 ^ (n + 1 + 1)) * f t ^ (2 ^ (n + 1)) := by
          simp only [pow_succ, pow_mul]

/-- The same identity indexed by an arbitrary positive iteration count. -/
theorem commP_pow_two_level (v g : G) {m : ℕ} (hm : 1 ≤ m) :
    levelMk G (m + 3) (commP (v ^ (2 ^ m)) g) =
      levelMk G (m + 3) (commP v g) ^ (2 ^ m) *
        levelMk G (m + 3) (commP (commP v g) v) ^ (2 ^ (m - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_assoc] using
    commP_pow_two_succ_level v g n

/-- A subgroup-membership formulation, so the mixed identity can be consumed by
filtered group arguments without choosing or interpreting quotient notation. -/
theorem commP_pow_two_congruence (v g : G) {m : ℕ} (hm : 1 ≤ m) :
    (commP (v ^ (2 ^ m)) g)⁻¹ *
        ((commP v g) ^ (2 ^ m) * (commP (commP v g) v) ^ (2 ^ (m - 1))) ∈
      twoCentralSeries G (m + 3) := by
  apply (QuotientGroup.eq_one_iff _).mp
  change levelMk G (m + 3) _ = 1
  rw [map_mul, map_inv, map_mul, map_pow, map_pow,
    ← commP_pow_two_level v g hm, inv_mul_cancel]

/-- Above degree one, the exceptional mixed-square term vanishes: power and
bracket commute at their first nonzero graded degree, uniformly in both depth
and iteration count. -/
theorem commP_pow_two_level_of_mem {j : ℕ} (hj : 2 ≤ j) {x : G}
    (hx : x ∈ twoCentralSeries G j) (g : G) (n : ℕ) :
    levelMk G (j + n + 2) (commP (x ^ (2 ^ n)) g) =
      levelMk G (j + n + 2) (commP x g) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let f := levelMk G (j + n + 3)
      have hu : f (x ^ (2 ^ n)) ∈ lambdaImage G ((j + n + 2) - 2) (j + n + 3) := by
        refine ⟨x ^ (2 ^ n), ?_, rfl⟩
        simpa using pow_two_pow_mem_twoCentralSeries_add hx n
      have hs : f (commP (x ^ (2 ^ n)) g) ^ 2 =
          (f (commP x g) ^ (2 ^ n)) ^ 2 := by
        have hh := levelMk_sq_eq_of_eq (j + n + 2)
          (x := commP (x ^ (2 ^ n)) g) (y := (commP x g) ^ (2 ^ n))
          (by simpa only [map_pow] using ih)
        simpa only [f, map_pow] using hh
      have hc := commP_sq_of_mem_lambdaImage (G := G) (j + n + 2) (by omega) (f g) hu
      change f (commP (x ^ (2 ^ (n + 1))) g) = f (commP x g) ^ (2 ^ (n + 1))
      calc
        f (commP (x ^ (2 ^ (n + 1))) g) = f (commP (x ^ (2 ^ n)) g) ^ 2 := by
          rw [pow_succ, pow_mul, map_commP_mixed, map_pow]
          simpa only [map_commP_mixed] using hc.symm
        _ = (f (commP x g) ^ (2 ^ n)) ^ 2 := hs
        _ = f (commP x g) ^ (2 ^ (n + 1)) := by simp only [pow_succ, pow_mul]

#print axioms pow_two_pow_mem_twoCentralSeries_add
#print axioms commP_mem_twoCentralSeries_add
#print axioms levelMk_sq_eq_of_eq
#print axioms commP_sq_level_four
#print axioms commP_pow_two_succ_level
#print axioms commP_pow_two_level
#print axioms commP_pow_two_congruence
#print axioms commP_pow_two_level_of_mem

end GQ2.Roe.Labute
