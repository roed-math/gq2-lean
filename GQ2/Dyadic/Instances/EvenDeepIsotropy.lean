import GQ2.Dyadic.Instances.StageAbstractionEvenFrameDeep

/-!
# W54-BOCK (draft): the depth class is isotropic
-/

namespace GQ2.Dyadic.EvenDeepIsotropy

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply
open GQ2.Dyadic.EvenFrameDeep

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The Bockstein vanishing -/

section Bockstein

variable {G : Type*} [Group G] [TopologicalSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- The reduction `ℤ/4 → ℤ/2`. -/
def lowerDigit (a : ZMod 4) : ZMod 2 := ((a.val : ℕ) : ZMod 2)

/-- The upper binary digit of a residue mod four. -/
def upperDigit (a : ZMod 4) : ZMod 2 := ((a.val / 2 : ℕ) : ZMod 2)

theorem lowerDigit_eq_castHom (a : ZMod 4) :
    lowerDigit a = ZMod.castHom (by norm_num) (ZMod 2) a := by
  rw [lowerDigit, ZMod.castHom_apply, ZMod.natCast_val]

/-- The carry identity. -/
theorem upperDigit_add (a b : ZMod 4) :
    upperDigit b - upperDigit (a + b) + upperDigit a = lowerDigit a * lowerDigit b := by
  revert a b
  decide

/-- **The Bockstein vanishing.** -/
theorem trivialCup_self_eq_zero_of_liftFour
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (z : Z1 G (ZMod 2)) (F : G → ZMod 4) (hFc : Continuous F)
    (hFmul : ∀ g h : G, F (g * h) = F g + F h)
    (hFred : ∀ g : G, z.1 g = lowerDigit (F g)) :
    H1mk G (ZMod 2) z ⌣[htriv] H1mk G (ZMod 2) z = 0 := by
  rw [trivialCupPairing, cup11_mk_mk]
  refine (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  refine AddSubgroup.mem_map.mpr ⟨fun g => upperDigit (F g), ?_, ?_⟩
  · exact Continuous.comp' (continuous_of_discreteTopology (f := upperDigit)) hFc
  · funext p
    show p.1 • upperDigit (F p.2) - upperDigit (F (p.1 * p.2)) + upperDigit (F p.1)
      = z.1 p.1 * (p.1 • z.1 p.2)
    rw [htriv, htriv, hFmul, hFred, hFred]
    exact upperDigit_add (F p.1) (F p.2)

end Bockstein

/-! ## §2 The mod-four depth digit -/

section DigitFour

private theorem evenDeepFour_natMod (α m : ℕ) :
    2 ^ (α + 1) * m % 2 ^ (α + 3) / 2 ^ (α + 1) = m % 4 := by
  rw [show (2 : ℕ) ^ (α + 3) = 2 ^ (α + 1) * 4 from by ring, Nat.mul_mod_mul_left,
    Nat.mul_div_cancel_left _ (by positivity)]

private theorem evenDeepFour_dvd (α : ℕ) : (4 : ℕ) ∣ 2 ^ (α + 3) :=
  Dvd.intro (2 ^ (α + 1)) (by ring)

private theorem evenDeepFour_scale (α : ℕ) (c : ZMod (2 ^ (α + 3))) :
    ((((2 : ZMod (2 ^ (α + 3))) ^ (α + 1) * c).val / 2 ^ (α + 1) : ℕ) : ZMod 4)
      = ZMod.castHom (evenDeepFour_dvd α) (ZMod 4) c := by
  have hval : ((2 : ZMod (2 ^ (α + 3))) ^ (α + 1)) = ((2 ^ (α + 1) : ℕ) : ZMod (2 ^ (α + 3))) := by
    push_cast
    ring
  have hv : ((2 : ZMod (2 ^ (α + 3))) ^ (α + 1)).val = 2 ^ (α + 1) := by
    rw [hval, ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
  rw [ZMod.val_mul, hv, evenDeepFour_natMod, ZMod.natCast_mod, ZMod.castHom_apply,
    ZMod.natCast_val]

private theorem evenDeepFour_cast (α : ℕ) (x : ℤ_[2]) :
    ZMod.castHom (evenDeepFour_dvd α) (ZMod 4) (PadicInt.toZModPow (α + 3) x)
      = PadicInt.toZModPow 2 x := by
  have h := PadicInt.zmod_cast_comp_toZModPow (p := 2) 2 (α + 3) (by omega)
  have h2 := congrArg (fun f : ℤ_[2] →+* ZMod (2 ^ 2) => f x) h
  simp only [RingHom.comp_apply] at h2
  rw [← h2, ZMod.castHom_apply, ZMod.castHom_apply]

/-- The mod-four cofactor, read off a residue. -/
def evenDeepFourOfSq (α : ℕ) (w : ZMod (2 ^ (α + 3))) : ZMod 4 :=
  (((w - 1).val / 2 ^ (α + 1) : ℕ) : ZMod 4)

/-- **The mod-four depth-`α` digit** of a two-adic unit. -/
def evenDeepDigitFour (α : ℕ) (u : ℤ_[2]ˣ) : ZMod 4 :=
  evenDeepFourOfSq α (PadicInt.toZModPow (α + 3) ((u : ℤ_[2]) ^ 2))

/-- The defining identity: the mod-four digit is the cofactor read modulo four. -/
theorem evenDeepDigitFour_eq {α : ℕ} {u : ℤ_[2]ˣ} {x : ℤ_[2]}
    (hx : ((u : ℤ_[2]) ^ 2 - 1) = 2 ^ (α + 1) * x) :
    evenDeepDigitFour α u = PadicInt.toZModPow 2 x := by
  have hstep : PadicInt.toZModPow (α + 3) ((u : ℤ_[2]) ^ 2) - 1
      = (2 : ZMod (2 ^ (α + 3))) ^ (α + 1) * PadicInt.toZModPow (α + 3) x := by
    have h1 : PadicInt.toZModPow (α + 3) ((u : ℤ_[2]) ^ 2 - 1)
        = PadicInt.toZModPow (α + 3) (2 ^ (α + 1) * x) := by rw [hx]
    rw [map_sub, map_one] at h1
    rw [h1, map_mul, map_pow, map_ofNat]
  rw [evenDeepDigitFour, evenDeepFourOfSq, hstep, evenDeepFour_scale, evenDeepFour_cast]

/-- The mod-four digit is a homomorphism on the units `≡ ±1 (mod 2^α)`. -/
theorem evenDeepDigitFour_mul {α : ℕ} (hα : 1 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : EvenSharpPmOne α a) (hb : EvenSharpPmOne α b) :
    evenDeepDigitFour α (a * b) = evenDeepDigitFour α a + evenDeepDigitFour α b := by
  obtain ⟨x, hx⟩ := evenDeep_sq_sub_one hα ha
  obtain ⟨y, hy⟩ := evenDeep_sq_sub_one hα hb
  have hxy : (((a * b : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 - 1) =
      2 ^ (α + 1) * (x + y + 2 ^ (α + 1) * (x * y)) := by
    push_cast
    linear_combination ((b : ℤ_[2]) ^ 2) * hx + (1 + 2 ^ (α + 1) * x) * hy
  have h0 : (2 : ZMod 4) ^ (α + 1) = 0 := by
    obtain ⟨β, rfl⟩ : ∃ β, α = β + 1 := ⟨α - 1, by omega⟩
    rw [show β + 1 + 1 = 2 + β from by omega, pow_add,
      show ((2 : ZMod 4) ^ 2) = 0 from by decide, zero_mul]
  rw [evenDeepDigitFour_eq hx, evenDeepDigitFour_eq hy, evenDeepDigitFour_eq hxy,
    map_add, map_add, map_mul, map_pow, map_ofNat, h0, zero_mul, add_zero]

/-- The reduction of the mod-four digit is the depth digit. -/
theorem evenDeepDigit_eq_lowerDigit {α : ℕ} (hα : 1 ≤ α) {u : ℤ_[2]ˣ}
    (hu : EvenSharpPmOne α u) :
    evenDeepDigit α u = lowerDigit (evenDeepDigitFour α u) := by
  obtain ⟨x, hx⟩ := evenDeep_sq_sub_one hα hu
  have hlow : lowerDigit (PadicInt.toZModPow 2 x) = PadicInt.toZModPow 1 x := by
    rw [lowerDigit_eq_castHom]
    have h := PadicInt.zmod_cast_comp_toZModPow (p := 2) 1 2 (by norm_num)
    have h2 := congrArg (fun f : ℤ_[2] →+* ZMod (2 ^ 1) => f x) h
    simp only [RingHom.comp_apply] at h2
    rw [← h2, ZMod.castHom_apply, ZMod.castHom_apply]
  have hdvd : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZModPow 1 x = 0 := by
    rw [show (0 : ZMod (2 ^ 1)) = PadicInt.toZModPow 1 (0 : ℤ_[2]) from (map_zero _).symm,
      GQ2.toZModPow_eq_iff_two_pow_dvd, pow_one, sub_zero]
  rw [evenDeepDigitFour_eq hx, hlow]
  by_cases hd : evenDeepDigit α u = 0
  · rw [hd, hdvd.mp ((evenDeepDigit_eq_zero_iff_two_dvd hx).mp hd)]
  · rw [evenDeepDigit_eq_one_of_ne_zero hd]
    have hne : PadicInt.toZModPow 1 x ≠ 0 := fun hc ↦
      hd ((evenDeepDigit_eq_zero_iff_two_dvd hx).mpr (hdvd.mpr hc))
    rcases ZMod.eq_zero_or_eq_one (PadicInt.toZModPow 1 x) with h' | h'
    · exact absurd h' hne
    · rw [h']

end DigitFour

/-! ### §2.1 Continuity -/

section DigitFourChar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The mod-four depth digit of a continuous character value is continuous in the argument. -/
theorem continuous_evenDeepDigitFour (α : ℕ) (chi : ContinuousMonoidHom G ℤ_[2]ˣ) :
    Continuous (fun g : G ↦ evenDeepDigitFour α (chi g)) := by
  refine IsLocallyConstant.continuous fun s ↦ ?_
  have hfact : (fun g : G ↦ evenDeepDigitFour α (chi g)) ⁻¹' s =
      (fun g : G ↦ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) ⁻¹'
        (PadicInt.toZModPow (p := 2) (α + 3) ⁻¹'
          {c : ZMod (2 ^ (α + 3)) | evenDeepFourOfSq α c ∈ s}) := rfl
  show IsOpen ((fun g : G ↦ evenDeepDigitFour α (chi g)) ⁻¹' s)
  rw [hfact]
  exact (isOpen_preimage_toZModPow (α + 3) _).preimage
    ((continuous_pow 2).comp (Units.continuous_val.comp chi.continuous_toFun))

end DigitFourChar

/-! ## §3 The Bockstein vanishing at the field cup form -/

section FieldBockstein

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenDeepIsotropyScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenDeepIsotropyContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [T2Space (GalK K)] in
/-- **The field-level Bockstein vanishing.** -/
theorem frattiniFrameCup_self_eq_zero_of_liftFour
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
    (F : maxProPQuotient 2 (GalK K) → ZMod 4) (hFc : Continuous F)
    (hFmul : ∀ g h : maxProPQuotient 2 (GalK K), F (g * h) = F g + F h)
    (hFred : ∀ g : maxProPQuotient 2 (GalK K), Multiplicative.toAdd (c g) = lowerDigit (F g)) :
    frattiniFrameCup (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) c) = 0 := by
  have hz : trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) Count.smul_zmod2
      (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) c) = 0 :=
    trivialCup_self_eq_zero_of_liftFour Count.smul_zmod2 (Count.homEquivZ1 c) F hFc hFmul hFred
  have hgal : trivialCupPairing 2 (GalK K) (htriv_galK K)
      (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      = 0 := by
    rw [← inf2_trivialCupPairing_maxProPMk_galK, hz, map_zero]
  unfold frattiniFrameCup FieldData.cupFormK
  rw [show (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        ⌣[FieldData.smul_zmodTwo_galK K]
      (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      = 0 from hgal, map_zero]

/-! ## §4 The discharge -/

omit [T2Space (GalK K)] in
/-- **The depth class is isotropic**, for every `α ≥ 2`. -/
theorem evenDeep_isotropic {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
      (evenDeepClass α (Nat.le_of_succ_le hα) hrange) = 0 := by
  have hbound := evenDeep_bound_of_range (Nat.le_of_succ_le hα) hrange
  unfold evenDeepClass
  refine frattiniFrameCup_self_eq_zero_of_liftFour _
    (fun g ↦ evenDeepDigitFour α (chiCycKTwo (K := K) g))
    (continuous_evenDeepDigitFour α (chiCycKTwo (K := K))) (fun g h ↦ ?_) (fun g ↦ ?_)
  · rw [map_mul, evenDeepDigitFour_mul (by omega) (hbound g) (hbound h)]
  · rw [evenDeepDigitChar_apply, toAdd_ofAdd]
    exact evenDeepDigit_eq_lowerDigit (by omega) (hbound g)

/-- **The per-field isotropy supply is a theorem.** -/
theorem evenDeepMIsotropicSupply_holds : EvenDeepMIsotropicSupply K :=
  fun _ hα hrange ↦ evenDeep_isotropic hα hrange

/-! ## §5 The unconditional corollaries -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The ramified-`i` binder is implied by the `M`-branch sign datum. -/
theorem evenDeep_kappa_ne_zero_of_neg
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 := by
  obtain ⟨g, hg⟩ := hneg
  intro h0
  have h1 : frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g = 0 := by
    rw [h0]
    exact frattiniFrameEval_zero g
  rw [frattiniFrameEval_modFour, show chiCycKTwo (K := K) g = -1 from hg,
    evenDegreeM_parity_negOne] at h1
  exact one_ne_zero h1

/-- The `M`-row cup-adapted frame, with no isotropy hypothesis. -/
theorem evenDeepIsotropy_mFrame {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    ∃ F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) :=
  evenFrameDeep_mFrame_of_range hα hdeg hkappa hrange (evenDeep_isotropic hα hrange)

/-- The `M` level-three stage base, with no isotropy hypothesis. -/
theorem evenDeepIsotropy_mStageBase {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    Nonempty (Tuple (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) :=
  evenFrameDeep_mStageBase hα hdeg hkappa hrange (evenDeep_isotropic hα hrange)

/-- **The even `M` endpoint**, with the isotropy discharged and the ramified-`i` binder derived. -/
theorem evenDeepIsotropy_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : EvenPerK.EvenPerKMFamilySupply h K) (Hup : EvenPerK.EvenPerKMRawToBracket h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenFrameDeep_orientedEquivM B hneg (evenDeep_kappa_ne_zero_of_neg hneg) h hev
    evenDeepMIsotropicSupply_holds Hfam Hup

end FieldBockstein

end

end GQ2.Dyadic.EvenDeepIsotropy

section AxiomPins

open GQ2.Dyadic.EvenDeepIsotropy

#print axioms lowerDigit
#print axioms upperDigit
#print axioms lowerDigit_eq_castHom
#print axioms upperDigit_add
#print axioms trivialCup_self_eq_zero_of_liftFour
#print axioms evenDeepFourOfSq
#print axioms evenDeepDigitFour
#print axioms evenDeepDigitFour_eq
#print axioms evenDeepDigitFour_mul
#print axioms evenDeepDigit_eq_lowerDigit
#print axioms continuous_evenDeepDigitFour
#print axioms evenDeepIsotropyScalar
#print axioms evenDeepIsotropyContinuousScalar
#print axioms frattiniFrameCup_self_eq_zero_of_liftFour
#print axioms evenDeep_isotropic
#print axioms evenDeep_kappa_ne_zero_of_neg
#print axioms evenDeepMIsotropicSupply_holds
#print axioms evenDeepIsotropy_mFrame
#print axioms evenDeepIsotropy_mStageBase
#print axioms evenDeepIsotropy_orientedEquivM

end AxiomPins
