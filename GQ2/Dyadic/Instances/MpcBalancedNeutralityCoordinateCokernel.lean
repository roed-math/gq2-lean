import GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleZModFour
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates

/-! ## The interaction row in the two finite coordinates -/

/-- Send a literal `C`-versus-`ABD` interaction source to its two deep handle digits. -/
noncomputable def oneHandleBalancedCoreNeutralityCoordinateRow
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (oneHandleRelativeCCoordinates k hk).comp
    (oneHandleBalancedCoreNeutralityInteractionSource p k hk).subtype

/-- The two-coordinate factor onto the neutrality cokernel. -/
noncomputable def oneHandleBalancedCoreNeutralityCoordinateFactor
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      OneHandleBalancedCoreNeutralityCokernel p k hk :=
  (oneHandleBalancedCoreNeutralitySourceFactor p k hk).comp
    (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).symm.toMonoidHom

@[simp] theorem oneHandleBalancedCoreNeutralityCoordinateFactor_coordinates
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk
        (oneHandleRelativeCCoordinates k hk x) =
      oneHandleBalancedCoreNeutralityClassHom p k hk x := by
  rw [oneHandleBalancedCoreNeutralityCoordinateFactor,
    oneHandleRelativeCCoordinates, MonoidHom.comp_apply,
    MonoidHom.comp_apply]
  change oneHandleBalancedCoreNeutralitySourceFactor p k hk
      ((oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).symm
        (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk
          (oneHandleRelativeCModuloNeutralMk k hk x))) = _
  rw [MulEquiv.symm_apply_apply,
    oneHandleBalancedCoreNeutralitySourceFactor_mk]

theorem oneHandleBalancedCoreNeutralityCoordinateFactor_surjective
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Function.Surjective
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk) := by
  intro q
  obtain ⟨x, hx⟩ :=
    oneHandleBalancedCoreNeutralitySourceFactor_surjective p k hk q
  refine ⟨oneHandleRelativeCModuloNeutralEquivZModFourSq k hk x, ?_⟩
  rw [oneHandleBalancedCoreNeutralityCoordinateFactor,
    MonoidHom.comp_apply]
  change oneHandleBalancedCoreNeutralitySourceFactor p k hk
    ((oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).symm
      (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk x)) = q
  rw [MulEquiv.symm_apply_apply, hx]

/-- The coordinate interaction row has exactly the kernel of the coordinate factor as its
range. -/
theorem oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range =
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk).ker := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    rw [MonoidHom.mem_ker,
      oneHandleBalancedCoreNeutralityCoordinateRow,
      MonoidHom.comp_apply,
      oneHandleBalancedCoreNeutralityCoordinateFactor_coordinates]
    change oneHandleBalancedCoreNeutralitySourceFactor p k hk
      (oneHandleBalancedCoreNeutralityInteractionToSource p k hk x) = 1
    apply MonoidHom.mem_ker.mp
    change oneHandleBalancedCoreNeutralityInteractionToSource p k hk x ∈
      oneHandleBalancedCoreNeutralityInteraction p k hk
    rw [← oneHandleBalancedCoreNeutralityInteraction_range_eq p k hk]
    exact ⟨x, rfl⟩
  · intro z hz
    have hzker :
        (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).symm z ∈
          oneHandleBalancedCoreNeutralityInteraction p k hk := by
      change oneHandleBalancedCoreNeutralitySourceFactor p k hk
        ((oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).symm z) = 1
      exact MonoidHom.mem_ker.mp hz
    rw [← oneHandleBalancedCoreNeutralityInteraction_range_eq p k hk] at hzker
    obtain ⟨x, hx⟩ := hzker
    refine ⟨x, ?_⟩
    change oneHandleRelativeCCoordinates k hk x.1 = z
    rw [oneHandleRelativeCCoordinates]
    change oneHandleRelativeCModuloNeutralEquivZModFourSq k hk
      (oneHandleBalancedCoreNeutralityInteractionToSource p k hk x) = z
    rw [hx, MulEquiv.apply_symm_apply]

/-! ## The explicit quotient -/

/-- The neutrality cokernel is a quotient of the sixteen-element coordinate group by the
image of the literal interaction row. -/
noncomputable def oneHandleBalancedCoreNeutralityCokernelEquivCoordinates
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    ((Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ⧸
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range) ≃*
      OneHandleBalancedCoreNeutralityCokernel p k hk :=
  (QuotientGroup.quotientMulEquivOfEq
      (oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker p k hk)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk)
      (oneHandleBalancedCoreNeutralityCoordinateFactor_surjective p k hk))

/-- Consequently, the residual neutrality cokernel has order dividing sixteen. -/
theorem natCard_oneHandleBalancedCoreNeutralityCokernel_dvd_sixteen
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Nat.card (OneHandleBalancedCoreNeutralityCokernel p k hk) ∣ 16 := by
  rw [← Nat.card_congr
    (oneHandleBalancedCoreNeutralityCokernelEquivCoordinates p k hk).toEquiv]
  refine (Subgroup.card_quotient_dvd_card
    (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range).trans ?_
  change Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∣ 16
  rw [Nat.card_prod]
  change Nat.card (ZMod 4) * Nat.card (ZMod 4) ∣ 16
  norm_num [Nat.card_zmod]

/-! ## Literal coordinate criteria -/

/-- Membership in the coordinate interaction subgroup is exactly solvability of the
central-layer CABD equation with the prescribed pair of digits. -/
theorem mem_oneHandleBalancedCoreNeutralityCoordinateRow_range_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    z ∈ (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCCoordinates k hk y = z ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, d, heq⟩ :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk y.1).mp y.2
    exact ⟨y.1, a, b, d, hy, heq⟩
  · rintro ⟨y, a, b, d, hy, heq⟩
    have hymem : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff p k hk y).mpr
        ⟨a, b, d, heq⟩
    exact ⟨⟨y, hymem⟩, hy⟩

/-- The coordinate factor kills exactly the digit pairs admitting a CABD solution. -/
theorem oneHandleBalancedCoreNeutralityCoordinateFactor_eq_one_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z = 1 ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCCoordinates k hk y = z ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  rw [← MonoidHom.mem_ker,
    ← oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker p k hk,
    mem_oneHandleBalancedCoreNeutralityCoordinateRow_range_iff]

/-- Any chosen `C` representative identifies target vanishing with membership of its two
digits in the explicit coordinate interaction subgroup. -/
theorem neutralityObstruction_eq_one_iff_coordinateInteraction
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1))
    (hx : oneHandleBalancedCoreNeutralityClassHom p k hk x =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel) :
    oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1 ↔
      oneHandleRelativeCCoordinates k hk x ∈
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
  rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker,
    MonoidHom.mem_ker,
    oneHandleBalancedCoreNeutralityCoordinateFactor_coordinates, hx]

#print axioms oneHandleBalancedCoreNeutralityCoordinateRow
#print axioms oneHandleBalancedCoreNeutralityCoordinateFactor
#print axioms oneHandleBalancedCoreNeutralityCoordinateFactor_coordinates
#print axioms oneHandleBalancedCoreNeutralityCoordinateFactor_surjective
#print axioms oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker
#print axioms oneHandleBalancedCoreNeutralityCokernelEquivCoordinates
#print axioms natCard_oneHandleBalancedCoreNeutralityCokernel_dvd_sixteen
#print axioms mem_oneHandleBalancedCoreNeutralityCoordinateRow_range_iff
#print axioms oneHandleBalancedCoreNeutralityCoordinateFactor_eq_one_iff
#print axioms neutralityObstruction_eq_one_iff_coordinateInteraction

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
