import GQ2.Dyadic.MarkedCore.NScalingAudit

/-!
# Central plane-defect absorption for N, uniformly in the handle tail

This is NOT a producer of NPlaneScalingHypothesis. It proves that the central
commutator test cannot obstruct an odd plane determinant: a commutator power in
the torsion-head letter absorbs the defect and is invisible to every character.
The full DN commutator need not be central, so no full-group lift is inferred.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 Multiplicative

section Powers
variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

private theorem central_zpow (hP : IsProP 2 P) (z : P)
    (hz : ∀ g : P, Commute z g) (s : ℤ_[2]) (g : P) :
    Commute (zpowZtwo hP z s) g := by
  change zpowZtwo hP z s * g = g * zpowZtwo hP z s
  refine PadicInt.denseRange_natCast.induction_on s ?_ ?_
  · exact isClosed_eq ((continuous_zpowZtwo hP z).mul continuous_const)
      (continuous_const.mul (continuous_zpowZtwo hP z))
  · intro n
    rw [zpowZtwo_natCast]
    exact ((hz g).pow_left n).eq

private theorem commP_zpow_of_central (hP : IsProP 2 P) (c d : P)
    (hz : ∀ g : P, Commute (commP c d) g) (s : ℤ_[2]) :
    commP (zpowZtwo hP c s) d = zpowZtwo hP (commP c d) s := by
  refine PadicInt.denseRange_natCast.induction_on s ?_ ?_
  · exact isClosed_eq
      ((((continuous_zpowZtwo hP c).inv.mul continuous_const).mul
        (continuous_zpowZtwo hP c)).mul continuous_const) (continuous_zpowZtwo hP _)
  · intro n
    rw [zpowZtwo_natCast, zpowZtwo_natCast]
    induction n with
    | zero => simp [commP]
    | succ n ih =>
      rw [pow_succ, commP_mul_left, ih]
      have hc : conjP (commP c d ^ n) c = commP c d ^ n := by
        rw [conjP, mul_assoc, ((hz c).pow_left n).eq, inv_mul_cancel_left]
      rw [hc, pow_succ]

/-- The head coefficient is twice a unit; every unit plane-scaling defect is
divisible by that coefficient, at all valid N exponents. -/
theorem exists_nPlaneCentralCorrectionExponent {alpha : ℕ} (ha : 2 ≤ alpha)
    (kappa : ℤ_[2]ˣ) :
    ∃ s : ℤ_[2], s * (2 + 2^alpha) + (kappa : ℤ_[2]) = 1 := by
  obtain ⟨t, ht⟩ := two_dvd_val_sub_one kappa
  let u := onePlusTwoPow (alpha-1)
  have hu : (u : ℤ_[2]) = 1 + 2^(alpha-1) := onePlusTwoPow_val (by omega)
  have he : (2 + 2^alpha : ℤ_[2]) = 2 * (u : ℤ_[2]) := by
    rw [hu]
    have ha' : alpha = (alpha-1)+1 := by omega
    conv_lhs => rw [ha', pow_succ]
    ring
  refine ⟨-t * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), ?_⟩
  rw [he]
  calc
    -t * (u⁻¹ : ℤ_[2]ˣ) * (2 * (u : ℤ_[2])) + (kappa : ℤ_[2])
        = -(2*t) * ((u⁻¹ : ℤ_[2]ˣ) * (u : ℤ_[2])) + (kappa : ℤ_[2]) := by ring
    _ = -(2*t) + (kappa : ℤ_[2]) := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    _ = 1 := by linear_combination ht

/-- Exact central-defect cancellation, not merely equality after taking
characters. The same equality survives an arbitrary unchanged right tail. -/
theorem nWord_central_plane_correction (hP : IsProP 2 P) (alpha : ℕ)
    (a b c d : P) (hz : ∀ g : P, Commute (commP c d) g)
    (s k : ℤ_[2]) (hs : s * (2 + 2^alpha) + k = 1) :
    nWord alpha (zpowZtwo hP (commP c d) s * a) b (zpowZtwo hP c k) d =
      nWord alpha a b c d := by
  let z := commP c d
  let e := 2 + 2^alpha
  have hcen := central_zpow hP z hz s
  have hcp := commP_zpow_of_central hP c d hz k
  have hpow : (zpowZtwo hP z s)^e * zpowZtwo hP z k = z := by
    rw [← zpowZtwo_natCast hP (zpowZtwo hP z s) e, zpowZtwo_zpowZtwo, ← zpowZtwo_add]
    have hse : s * (e : ℤ_[2]) + k = 1 := by simpa [e] using hs
    rw [hse, zpowZtwo_one_exp]
  calc
    nWord alpha (zpowZtwo hP z s * a) b (zpowZtwo hP c k) d
        = (zpowZtwo hP z s)^e * (a^e * commP a b) * zpowZtwo hP z k := by
          rw [nWord, (hcen a).mul_pow, commP_pre_mul_left_of_commute (hcen b), hcp]
          simp only [z, e, mul_assoc]
    _ = (a^e * commP a b) * ((zpowZtwo hP z s)^e * zpowZtwo hP z k) := by
      rw [((hcen (a^e * commP a b)).pow_left e).eq, mul_assoc]
    _ = nWord alpha a b c d := by rw [hpow]; rfl

/-- At every handle rank, whenever the selected plane commutator is central,
every unit determinant has an exact relator-preserving substitution fixing the
other free-character rows simultaneously. This does not assert the substitution
is an automorphism, or that the centrality premise holds in DN itself. -/
theorem exists_nWord_planeScale_of_central_comm (hP : IsProP 2 P)
    {alpha : ℕ} (ha : 2 ≤ alpha) (a b c d : P)
    (hz : ∀ g : P, Commute (commP c d) g) (kappa : ℤ_[2]ˣ) :
    ∃ a' c' : P,
      (∀ (h : ℕ) (u v : Fin h → P),
        nWord alpha a' b c' d * handleWord u v =
          nWord alpha a b c d * handleWord u v) ∧
      (∀ f : ContinuousMonoidHom P (Multiplicative ℤ_[2]),
        f a' = f a ∧ toAdd (f c') = (kappa : ℤ_[2]) * toAdd (f c)) := by
  obtain ⟨s, hs⟩ := exists_nPlaneCentralCorrectionExponent ha kappa
  refine ⟨zpowZtwo hP (commP c d) s * a, zpowZtwo hP c (kappa : ℤ_[2]), ?_, ?_⟩
  · intro h u v
    rw [nWord_central_plane_correction hP alpha a b c d hz s (kappa : ℤ_[2]) hs]
  · intro f
    constructor
    · have hf : f (commP c d) = 1 := by simp [commP, map_mul, map_inv, mul_comm]
      rw [map_mul, map_zpowZtwo hP PropOneOne.isProP_two_multPadicInt, hf,
        zpowZtwo_one_base, one_mul]
    · exact toAdd_map_zpowZtwo hP f c (kappa : ℤ_[2])

#print axioms exists_nPlaneCentralCorrectionExponent
#print axioms nWord_central_plane_correction
#print axioms exists_nWord_planeScale_of_central_comm

end Powers
end GQ2.Dyadic.MarkedCore

