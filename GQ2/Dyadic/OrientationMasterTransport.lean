import GQ2.Dyadic.Instances.MOrientationCharacteristic

/-!
# Transport of a full crossed-derivation basis under automorphisms

This is the group-independent content of the master-matrix argument used for the M core.
A full basis of integral crossed derivations, reducing to the generator-coordinate basis
modulo two, remains full after any continuous automorphism. The proof uses invertibility of
the mod-two evaluation matrix and the local-ring unit criterion in `Z₂`, not a classification
of automorphisms or any rank-specific calculation.

Only continuity of the additive coordinates is required; no global topology on `WordLift`
is installed. Concrete presentation modules can therefore reuse their existing lift topology.
-/

namespace GQ2.Dyadic.OrientationMasterTransport

open GQ2 GQ2.SectionThree FoxH Multiplicative

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}
  (gen : Fin d → G) (χ : G →* ℤ_[2]ˣ)

/-- Actual crossed homomorphisms realizing every generator-value vector. -/
structure DerivationBasis where
  lift : (Fin d → ℤ_[2]) → G →* WordLift ℤ_[2] ℤ_[2]ˣ
  gen_u : ∀ c i, (lift c (gen i)).u = c i
  base : ∀ c x, (lift c x).g = χ x
  continuous_u : ∀ c, Continuous fun x => (lift c x).u

namespace DerivationBasis

variable {gen χ} (D : DerivationBasis gen χ)

omit [IsTopologicalGroup G] in
theorem lift_mul_u (c : Fin d → ℤ_[2]) (x y : G) :
    (D.lift c (x * y)).u = (D.lift c x).u + χ x • (D.lift c y).u := by
  rw [map_mul, WordLift.mul_u, D.base]

/-- A linear combination of basis derivations, retaining the same character. -/
def contract (c : Fin d → ℤ_[2]) : G →* WordLift ℤ_[2] ℤ_[2]ˣ where
  toFun x := ⟨∑ j, c j * (D.lift (Pi.single j 1) x).u, χ x⟩
  map_one' := by
    refine WordLift.ext ?_ (map_one χ)
    simp
  map_mul' x y := by
    refine WordLift.ext ?_ (map_mul χ x y)
    simp only [D.lift_mul_u, WordLift.mul_u, Units.smul_def, smul_eq_mul,
      Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

local instance : TopologicalSpace (ZMod (2 ^ 1)) := ⊥
local instance : DiscreteTopology (ZMod (2 ^ 1)) := ⟨rfl⟩

private theorem continuous_toZModPow_one : Continuous (PadicInt.toZModPow (p := 2) 1) := by
  rw [continuous_def]
  intro T _
  exact isOpen_preimage_toZModPow 1 T

private theorem modTwo_unit_eq_one {z : ZMod (2 ^ 1)} (hz : IsUnit z) : z = 1 := by
  haveI : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
  exact (by decide : ∀ w : ZMod (2 ^ 1), w ≠ 0 → w = 1) z hz.ne_zero

private theorem isUnit_of_modTwo_eq_one {x : ℤ_[2]}
    (hx : PadicInt.toZModPow 1 x = 1) : IsUnit x := by
  haveI : NeZero (2 ^ 1) := ⟨by norm_num⟩
  rw [PadicInt.isUnit_iff]
  by_contra hne
  have hlt : ‖x‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one x) hne
  have hdvd : (2 : ℤ_[2]) ∣ x := (PadicInt.norm_lt_one_iff_dvd x).mp hlt
  obtain ⟨y, rfl⟩ := hdvd
  have h2 : (PadicInt.toZModPow (p := 2) 1) 2 = 0 := by
    rw [show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by push_cast; ring, map_natCast]
    decide
  rw [map_mul, h2, zero_mul] at hx
  exact absurd hx (by decide)

/-- The mod-two additive coordinates form an ordinary homomorphism. -/
def modTwo : G →* Multiplicative (Fin d → ZMod (2 ^ 1)) where
  toFun x := ofAdd fun j => PadicInt.toZModPow 1 (D.lift (Pi.single j 1) x).u
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
    rw [D.lift_mul_u, map_add, Units.smul_def, smul_eq_mul, map_mul,
      modTwo_unit_eq_one ((χ x).isUnit.map (PadicInt.toZModPow (p := 2) 1)), one_mul]
    rfl

omit [IsTopologicalGroup G] in
theorem continuous_modTwo : Continuous D.modTwo := by
  refine continuous_ofAdd.comp (continuous_pi fun j => ?_)
  exact continuous_toZModPow_one.comp (D.continuous_u (Pi.single j 1))

omit [IsTopologicalGroup G] in
theorem modTwo_gen (i : Fin d) :
    (D.modTwo (gen i)).toAdd = Pi.single i (1 : ZMod (2 ^ 1)) := by
  funext j
  change PadicInt.toZModPow 1 (D.lift (Pi.single j 1) (gen i)).u = _
  rw [D.gen_u]
  rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (Ne.symm hji), map_zero]

/-- Evaluation of basis derivations on an automorphic generating tuple. -/
def matrix (e : ContinuousMulEquiv G G) : Matrix (Fin d) (Fin d) ℤ_[2] :=
  Matrix.of fun i j => (D.lift (Pi.single j 1) (e (gen i))).u

private theorem toAdd_mem_span_of_mem_closure
    {s : Fin d → Multiplicative (Fin d → ZMod (2 ^ 1))}
    {w : Multiplicative (Fin d → ZMod (2 ^ 1))}
    (hw : w ∈ Subgroup.closure (Set.range s)) :
    w.toAdd ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range fun i => (s i).toAdd) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
  | one => exact Submodule.zero_mem _
  | mul x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | inv x _ hx => exact Submodule.neg_mem _ hx

theorem matrix_isUnit
    (htop : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤)
    (e : ContinuousMulEquiv G G) : IsUnit (D.matrix e) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  let Mb := (D.matrix e).map (PadicInt.toZModPow 1)
  have htop' : (Subgroup.closure (Set.range fun i => e (gen i))).topologicalClosure = ⊤ := by
    have H := topGen_map (f := e.toMonoidHom) e.continuous_toFun e.surjective htop
    have himage : e.toMonoidHom '' Set.range gen = Set.range fun i => e (gen i) := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨gen i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at H
    exact H
  have hmem : ∀ x : G, (D.modTwo x).toAdd ∈
      Submodule.span (ZMod (2 ^ 1)) (Set.range Mb.row) := by
    intro x
    let K : Subgroup G :=
      (Subgroup.closure (Set.range fun i => D.modTwo (e (gen i)))).comap D.modTwo
    have hc : IsClosed (K : Set G) := by
      change IsClosed (D.modTwo ⁻¹' (Subgroup.closure
        (Set.range fun i => D.modTwo (e (gen i))) : Set _))
      exact (isClosed_discrete _).preimage D.continuous_modTwo
    have hg : Subgroup.closure (Set.range fun i => e (gen i)) ≤ K := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hK : (⊤ : Subgroup G) ≤ K := by
      rw [← htop']
      exact Subgroup.topologicalClosure_minimal _ hg hc
    exact toAdd_mem_span_of_mem_closure (hK (Subgroup.mem_top x))
  have hMb : IsUnit Mb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    have hv : v ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range Mb.row) := by
      have heq : v = ∑ i, v i • Pi.single (M := fun _ => ZMod (2 ^ 1)) i 1 := by
        funext k
        simp [Pi.single_apply]
      rw [heq]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact D.modTwo_gen i ▸ hmem (gen i)
    rw [← range_vecMulLinear, LinearMap.mem_range] at hv
    exact hv
  apply isUnit_of_modTwo_eq_one
  calc
    PadicInt.toZModPow 1 ((D.matrix e).det) = Mb.det := by
      rw [show Mb = (D.matrix e).map (PadicInt.toZModPow 1) from rfl,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    _ = 1 := modTwo_unit_eq_one ((Matrix.isUnit_iff_isUnit_det Mb).mp hMb)

include D in
/-- All crossed-derivation generator values remain realizable after an automorphism. -/
theorem exists_lift_of_aut
    (htop : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤)
    (e : ContinuousMulEquiv G G) (b : Fin d → ℤ_[2]) :
    ∃ H : G →* WordLift ℤ_[2] ℤ_[2]ˣ,
      (∀ x, (H x).g = χ (e x)) ∧
      ∀ i, H (gen i) = ⟨b i, χ (e (gen i))⟩ := by
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr (D.matrix_isUnit htop e)) b
  refine ⟨(D.contract c).comp e.toMonoidHom, fun _ => rfl, ?_⟩
  intro i
  refine WordLift.ext ?_ rfl
  change (∑ j, c j * (D.lift (Pi.single j 1) (e (gen i))).u) = b i
  have hci := congrFun hc i
  simp only [Matrix.mulVec, dotProduct, matrix, Matrix.of_apply] at hci
  rw [← hci]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

#print axioms DerivationBasis
#print axioms lift_mul_u
#print axioms contract
#print axioms modTwo
#print axioms continuous_modTwo
#print axioms modTwo_gen
#print axioms matrix
#print axioms matrix_isUnit
#print axioms exists_lift_of_aut

end DerivationBasis

/-- A full zero crossed-derivation row on a product of disjoint handles forces both
characters on every handle to be trivial. The head of the presentation is irrelevant. -/
theorem handle_characters_one_of_lift_relations {ι : Type} [DecidableEq ι] {h : ℕ}
    (u v : Fin h → ι) (hu : Function.Injective u) (hv : Function.Injective v)
    (huv : ∀ i j, u i ≠ v j) (ξ : ι → ℤ_[2]ˣ)
    (H : ∀ b : ι → ℤ_[2],
      MarkedCore.handleWord (fun j => (⟨b (u j), ξ (u j)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ))
        (fun j => ⟨b (v j), ξ (v j)⟩) = 1) :
    (∀ j, ξ (u j) = 1) ∧ (∀ j, ξ (v j) = 1) := by
  have hrow := fun b => congrArg WordLift.u (H b)
  simp only [Instances.MOrientationCharacteristic.handleWord_wordLift_formula,
    WordLift.one_u] at hrow
  have hU : ∀ j, ξ (u j) = 1 := by
    intro j
    have hz := hrow (Pi.single (v j) 1)
    have hsum :
        (∑ k : Fin h,
          ((((ξ (u k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              ((((ξ (v k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) *
                (Pi.single (v j) 1 : ι → ℤ_[2]) (u k) +
            (((ξ (v k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              (1 - (((ξ (u k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) *
                (Pi.single (v j) 1 : ι → ℤ_[2]) (v k))) =
        (((ξ (v j))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          (1 - (((ξ (u j))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
      rw [Finset.sum_eq_single j]
      · simp [huv]
      · intro k _ hkj
        simp [huv, hv.ne (Ne.symm hkj)]
      · simp
    rw [hsum] at hz
    apply inv_eq_one.mp
    apply Units.ext
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (Units.ne_zero _))).symm
  have hV : ∀ j, ξ (v j) = 1 := by
    intro j
    have hz := hrow (Pi.single (u j) 1)
    have hsum :
        (∑ k : Fin h,
          ((((ξ (u k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              ((((ξ (v k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) *
                (Pi.single (u j) 1 : ι → ℤ_[2]) (u k) +
            (((ξ (v k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
              (1 - (((ξ (u k))⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) *
                (Pi.single (u j) 1 : ι → ℤ_[2]) (v k))) =
        (((ξ (u j))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((((ξ (v j))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
      rw [Finset.sum_eq_single j]
      · simp [huv]
      · intro k _ hkj
        simp [huv, hu.ne (Ne.symm hkj)]
      · simp
    rw [hsum] at hz
    apply inv_eq_one.mp
    apply Units.ext
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (Units.ne_zero _))
  exact ⟨hU, hV⟩

#print axioms handle_characters_one_of_lift_relations

end

end GQ2.Dyadic.OrientationMasterTransport
