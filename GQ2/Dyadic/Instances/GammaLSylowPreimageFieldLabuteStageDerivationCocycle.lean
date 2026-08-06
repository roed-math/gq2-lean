/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageDigitFlipDamage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageFunctionalsModel

/-!
# Coordinate derivation families from twisted one-cocycles

A χ-shadowed derivation into `WL (k+1)` is exactly a continuous χ-twisted one-cocycle at
precision `2^(k+1)`: the offset function of the derivation satisfies
`u(gg') = u(g) + χ̄(g)·u(g')`, and conversely every such cocycle assembles into a continuous
homomorphism with base the mod-`2^(k+1)` shadow of `χ` (`chiShadowDerivOfCocycle`).  This
file records the equivalence and restates the family input of the kernel-adapted reduction
in purely cocycle-theoretic terms:

* `SqStageTwistedCocycleParitySupply`: per stage, exact-fibre lifts and, for each
  non-twisted slot, a continuous χ-twisted cocycle mod `2^(k+1)` whose values at the lifts
  have the Kronecker parity pattern.  This is the arithmetic form of the family — the
  mod-`2` surjectivity of `Z¹(χ mod 2^(k+1)) → Z¹(𝔽₂)` on the prescribed coordinates that
  higher Kummer theory must supply;
* the supply is *equivalent* to the family
  (`nonempty_family_iff_twistedCocycleParitySupply`), and holds whenever the presentation
  theorem itself holds (`sqStageTwistedCocycleParitySupply_of_orientedEquiv`), so the
  reduction is exactly calibrated;
* the campaign endpoint (`nonempty_orientedEquiv_oddDegree_of_cocycleParity_of_bracketSquare`):
  the cocycle parity supply and the bracket-square residual at every stage deliver the
  forward presentation theorem for every odd-degree field.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Twisted one-cocycles and χ-shadowed derivations -/

section Cocycle

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A continuous χ-twisted one-cocycle at precision `2^N`**: a locally constant function
`u : G → ℤ/2^N` with `u(gg') = u(g) + χ̄(g)·u(g')`, the crossed-homomorphism identity for
the multiplication action through the mod-`2^N` shadow of `χ`.  Openness of the value fibres
replaces continuity because `ZMod` carries no ambient topology here. -/
def IsChiTwistedCocycle (chi : ContinuousMonoidHom G ℤ_[2]ˣ) (N : ℕ)
    (u : G → ZMod (2 ^ N)) : Prop :=
  (∀ v : ZMod (2 ^ N), IsOpen {g : G | u g = v}) ∧
  ∀ g g' : G, u (g * g') =
    u g + PadicInt.toZModPow N ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * u g'

omit [IsTopologicalGroup G] in
/-- A twisted cocycle vanishes at the identity. -/
theorem IsChiTwistedCocycle.map_one {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {N : ℕ}
    {u : G → ZMod (2 ^ N)} (hu : IsChiTwistedCocycle chi N u) : u 1 = 0 := by
  have hone := hu.2 1 1
  rw [mul_one, show chi 1 = 1 from _root_.map_one chi, Units.val_one,
    show PadicInt.toZModPow N (1 : ℤ_[2]) = 1 from _root_.map_one _, one_mul] at hone
  have h0 : u 1 + 0 = u 1 + u 1 := by
    rw [add_zero]
    exact hone
  exact (add_left_cancel h0).symm

/-- **The derivation of a twisted cocycle**: the continuous homomorphism `G → WL N` with
offset `u` and base the mod-`2^N` shadow of `χ`. -/
def chiShadowDerivOfCocycle [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) {N : ℕ} (u : G → ZMod (2 ^ N))
    (hu : IsChiTwistedCocycle chi N u) : ContinuousMonoidHom G (WL N) where
  toFun g := ⟨u g, Units.map (PadicInt.toZModPow N).toMonoidHom (chi g)⟩
  map_one' := by
    refine WordLift.ext ?_ ?_
    · rw [WordLift.one_u]
      exact hu.map_one
    · rw [WordLift.one_g, map_one, map_one]
  map_mul' g g' := by
    refine WordLift.ext ?_ ?_
    · rw [WordLift.mul_u]
      show u (g * g') = u g +
        Units.map (PadicInt.toZModPow N).toMonoidHom (chi g) • u g'
      rw [Units.smul_def, smul_eq_mul, Units.coe_map]
      exact hu.2 g g'
    · rw [WordLift.mul_g]
      show Units.map (PadicInt.toZModPow N).toMonoidHom (chi (g * g')) = _
      rw [map_mul, map_mul]
  continuous_toFun := by
    letI := discreteTopology_levelQuot G hfg hpro N
    have hchi : Continuous fun g : G ↦
        Units.map (PadicInt.toZModPow N).toMonoidHom (chi g) := by
      have hfun : (fun g : G ↦
          Units.map (PadicInt.toZModPow N).toMonoidHom (chi g)) =
          fun g ↦ chiLevel chi N (levelMk G N g) := by
        funext g
        rw [chiLevel_levelMk]
      rw [hfun]
      exact (continuous_of_discreteTopology (f := ⇑(chiLevel chi N))).comp
        (continuous_levelMk G N)
    rw [continuous_discrete_rng]
    intro b
    have hset : (fun g : G ↦
        (⟨u g, Units.map (PadicInt.toZModPow N).toMonoidHom (chi g)⟩ : WL N)) ⁻¹' {b} =
        {g : G | u g = b.u} ∩
          (fun g : G ↦ Units.map (PadicInt.toZModPow N).toMonoidHom (chi g)) ⁻¹' {b.g} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · intro hEq
        exact ⟨congrArg WordLift.u hEq, congrArg WordLift.g hEq⟩
      · rintro ⟨h1, h2⟩
        exact WordLift.ext h1 h2
    rw [hset]
    exact (hu.1 b.u).inter (hchi.isOpen_preimage _ (isOpen_discrete _))

@[simp] theorem chiShadowDerivOfCocycle_u [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) {N : ℕ} (u : G → ZMod (2 ^ N))
    (hu : IsChiTwistedCocycle chi N u) (x : G) :
    (chiShadowDerivOfCocycle hfg hpro chi u hu x).u = u x := rfl

/-- The derivation of a twisted cocycle is χ-shadowed. -/
theorem isChiShadowDeriv_chiShadowDerivOfCocycle [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) {N : ℕ} (u : G → ZMod (2 ^ N))
    (hu : IsChiTwistedCocycle chi N u) :
    IsChiShadowDeriv chi (chiShadowDerivOfCocycle hfg hpro chi u hu) :=
  fun _ ↦ rfl

omit [IsTopologicalGroup G] in
/-- **The converse**: the offset function of any χ-shadowed derivation is a continuous
χ-twisted one-cocycle. -/
theorem isChiTwistedCocycle_of_isChiShadowDeriv {chi : ContinuousMonoidHom G ℤ_[2]ˣ}
    {N : ℕ} {Φ : ContinuousMonoidHom G (WL N)} (hbase : IsChiShadowDeriv chi Φ) :
    IsChiTwistedCocycle chi N (fun g ↦ (Φ g).u) := by
  constructor
  · intro v
    have hset : {g : G | (Φ g).u = v} = ⇑Φ ⁻¹' {p : WL N | p.u = v} := rfl
    rw [hset]
    exact Φ.continuous_toFun.isOpen_preimage _ (isOpen_discrete _)
  · intro g g'
    show (Φ (g * g')).u = (Φ g).u +
      PadicInt.toZModPow N ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * (Φ g').u
    have hmul := congrArg WordLift.u (map_mul Φ g g')
    rw [WordLift.mul_u, Units.smul_def, smul_eq_mul] at hmul
    rw [hmul, hbase.base_val g]

end Cocycle

/-! ## The cocycle parity supply -/

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- **The twisted-cocycle parity supply.**  For a stage tuple: exact-fibre ambient lifts of
the generators and, for each non-twisted slot `i₀`, a continuous χ-twisted one-cocycle at
precision `2^(k+1)` whose value at the `i₀`-lift is odd and whose values at the other
non-twisted lifts are even.  The twisted slot `2` is unconstrained.  This is the exact
arithmetic content of the coordinate derivation family: mod-`2` surjectivity of the
reduction `Z¹(χ mod 2^(k+1)) → Z¹(𝔽₂)` on the prescribed coordinates. -/
def SqStageTwistedCocycleParitySupply {h k : ℕ} (T : SqCyclotomicStageTuple K h k) : Prop :=
  ∃ lifts : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K),
    (∀ i, chiCycKTwo (K := K) (lifts i) = sqStageChiTargetUnit h i) ∧
    (∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i) ∧
    ∀ i₀ : Fin (SqCore.sqRank h), i₀ ≠ 2 →
      ∃ u : maxProPQuotient 2 (GalK K) → ZMod (2 ^ (k + 1)),
        IsChiTwistedCocycle (chiCycKTwo (K := K)) (k + 1) u ∧
        ¬ (2 : ZMod (2 ^ (k + 1))) ∣ u (lifts i₀) ∧
        ∀ j : Fin (SqCore.sqRank h), j ≠ 2 → j ≠ i₀ →
          (2 : ZMod (2 ^ (k + 1))) ∣ u (lifts j)

/-- **The family from the parity supply.** -/
theorem nonempty_family_of_twistedCocycleParitySupply {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k}
    (H : SqStageTwistedCocycleParitySupply T) :
    Nonempty (SqStageCoordinateDerivationFamily T) := by
  obtain ⟨lifts, hchi, hlvl, hcoc⟩ := H
  choose u hu hdiag hoff using hcoc
  exact ⟨{ lifts := lifts
           lifts_chi := hchi
           lifts_level := hlvl
           deriv := fun i₀ hi₀ ↦ chiShadowDerivOfCocycle
             (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient
             (chiCycKTwo (K := K)) (u i₀ hi₀) (hu i₀ hi₀)
           deriv_base := fun i₀ hi₀ ↦ isChiShadowDeriv_chiShadowDerivOfCocycle _ _ _ _ _
           deriv_diag := fun i₀ hi₀ ↦ hdiag i₀ hi₀
           deriv_off := fun i₀ hi₀ j hj hji ↦ hoff i₀ hi₀ j hj hji }⟩

/-- **The parity supply from the family.** -/
theorem twistedCocycleParitySupply_of_family {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k}
    (F : SqStageCoordinateDerivationFamily T) :
    SqStageTwistedCocycleParitySupply T := by
  refine ⟨F.lifts, F.lifts_chi, F.lifts_level, fun i₀ hi₀ ↦
    ⟨fun g ↦ ((F.deriv i₀ hi₀) g).u,
      isChiTwistedCocycle_of_isChiShadowDeriv (F.deriv_base i₀ hi₀),
      F.deriv_diag i₀ hi₀, fun j hj hji ↦ F.deriv_off i₀ hi₀ j hj hji⟩⟩

/-- The family exists exactly when the parity supply holds. -/
theorem nonempty_family_iff_twistedCocycleParitySupply {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} :
    Nonempty (SqStageCoordinateDerivationFamily T) ↔
      SqStageTwistedCocycleParitySupply T :=
  ⟨fun ⟨F⟩ ↦ twistedCocycleParitySupply_of_family F,
   nonempty_family_of_twistedCocycleParitySupply⟩

/-- **Exact calibration**: the parity supply holds whenever the presentation theorem itself
does — the model coordinate derivations transport along any oriented equivalence. -/
theorem sqStageTwistedCocycleParitySupply_of_orientedEquiv {h k : ℕ}
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))) :
    SqStageTwistedCocycleParitySupply
      (SqCyclotomicStageTuple.ofOrientedEquiv (K := K) (k := k) e) :=
  twistedCocycleParitySupply_of_family (sqStageFamilyOfOrientedEquiv e)

/-! ## The campaign endpoint -/

/-- **The kernel-adapted supply from the cocycle parities and the bracket-square
residual.** -/
theorem sqKernelAdaptedDefectSupply_of_cocycleParity_of_bracketSquare {h : ℕ}
    (Hpar : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      SqStageTwistedCocycleParitySupply T)
    (Hsq : ∀ (k : ℕ) (hk : 3 ≤ k), ∀ T : SqCyclotomicStageTuple K h k,
      SqStageBracketSquareNeutralSupply T hk) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_family_of_bracketSquare
    (fun k hk T ↦ nonempty_family_of_twistedCocycleParitySupply (Hpar k hk T)) Hsq

/-- **The forward presentation theorem over the cocycle parities and the bracket-square
residual.**  For every odd-degree field: continuous χ-twisted one-cocycles mod `2^(k+1)`
with Kronecker parities at the exact-fibre lifts, together with neutral realizations of the
`2h` half-damage bracket squares, deliver the oriented presentation equivalence at every
stage.  These two per-stage statements are the campaign's entire remaining L-row gap. -/
theorem nonempty_orientedEquiv_oddDegree_of_cocycleParity_of_bracketSquare
    {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hpar : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageTwistedCocycleParitySupply T)
    (Hsq : ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageBracketSquareNeutralSupply T hk) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply B hodd
    (sqKernelAdaptedDefectSupply_of_cocycleParity_of_bracketSquare Hpar Hsq)

#print axioms chiShadowDerivOfCocycle
#print axioms isChiTwistedCocycle_of_isChiShadowDeriv
#print axioms nonempty_family_of_twistedCocycleParitySupply
#print axioms nonempty_family_iff_twistedCocycleParitySupply
#print axioms sqStageTwistedCocycleParitySupply_of_orientedEquiv
#print axioms sqKernelAdaptedDefectSupply_of_cocycleParity_of_bracketSquare
#print axioms nonempty_orientedEquiv_oddDegree_of_cocycleParity_of_bracketSquare

end

end GQ2.Dyadic.LSquare
