/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationFox
import GQ2.Dyadic.Count.HTwoStronglyFree

/-!
# Universal Fox retractions give split strongly-free relation summands

The universal Fox matrix criterion is a first-order certificate in the free regular generator
module.  This file connects it to the explicit classical quotient `R / (R²[R,R])`: when the
marking generates the target, the coordinate map supplied by a Fox retraction splits the
canonical orbit map of the displayed relators.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH

section ElementaryRelationQuotient

variable {X L : Type} [Group L] (m : X → L)

/-- The elementary relation quotient is commutative, since its defining subgroup contains all
commutators. -/
theorem freeRelationModTwoQuotient_mul_comm
    (a b : FreeRelationModTwoQuotient m) : a * b = b * a := by
  refine Quotient.inductionOn₂' a b ?_
  intro r s
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_iff_div_mem]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc] using
    (freeRelation_commutator_mem_modTwoSubgroup m r s)

/-- The elementary relation quotient has exponent two. -/
theorem freeRelationModTwoQuotient_pow_two
    (a : FreeRelationModTwoQuotient m) : a ^ 2 = 1 := by
  refine QuotientGroup.induction_on a ?_
  intro r
  simpa using freeRelationModTwoQuotient_sq m r

/-- The commutative-group structure on the elementary relation quotient. -/
@[implicit_reducible] noncomputable def freeRelationModTwoQuotientCommGroup :
    CommGroup (FreeRelationModTwoQuotient m) :=
  { QuotientGroup.Quotient.group (freeRelationModTwoSubgroup m) with
    mul_comm := freeRelationModTwoQuotient_mul_comm m }

/-- Conjugation of a relation class depends only on the image of the conjugating word in the
marked target. -/
theorem relationKernelConj_modTwo_eq_of_lift_eq
    (f g : FreeGroup X) (s : FreeRelationKernel m)
    (hfg : FreeGroup.lift m f = FreeGroup.lift m g) :
    QuotientGroup.mk' (freeRelationModTwoSubgroup m)
        (relationKernelConj m f s) =
      QuotientGroup.mk' (freeRelationModTwoSubgroup m)
        (relationKernelConj m g s) := by
  let u : FreeRelationKernel m :=
    ⟨g⁻¹ * f, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfg]
      group⟩
  change (↑(relationKernelConj m f s) : FreeRelationModTwoQuotient m) =
    ↑(relationKernelConj m g s)
  rw [QuotientGroup.eq_iff_div_mem]
  have hc := freeRelation_commutator_mem_modTwoSubgroup m
    (relationKernelConj m g u) (relationKernelConj m g s)
  convert hc using 1
  ext
  dsimp [relationKernelConj, u]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  group

end ElementaryRelationQuotient

section CanonicalOrbit

variable {X rel L : Type} [Group L] {m : X → L}
  {w : rel → FreeGroup X} {hrel : ∀ k, FreeGroup.lift m (w k) = 1}

/-- The unique additive map from `ZMod 2` sending `1` to an element of the elementary relation
quotient. -/
noncomputable def freeRelationModTwoZModHom
    (a : FreeRelationModTwoQuotient m) :
    ZMod 2 →+ Additive (FreeRelationModTwoQuotient m) := by
  letI := freeRelationModTwoQuotientCommGroup m
  exact ZMod.lift 2 ⟨zmultiplesHom _ (Additive.ofMul a), by
    change (2 : ℤ) • Additive.ofMul a = 0
    change a ^ (2 : ℤ) = 1
    rw [zpow_two]
    refine QuotientGroup.induction_on a ?_
    intro r
    change (↑r : FreeRelationModTwoQuotient m) * ↑r = 1
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    simpa [pow_two] using freeRelation_sq_mem_modTwoSubgroup m r⟩

@[simp]
theorem freeRelationModTwoZModHom_one
    (a : FreeRelationModTwoQuotient m) :
    freeRelationModTwoZModHom a (1 : ZMod 2) = Additive.ofMul a := by
  letI := freeRelationModTwoQuotientCommGroup m
  simp only [freeRelationModTwoZModHom]
  rw [show (1 : ZMod 2) = (1 : ℤ) by norm_num, ZMod.lift_coe]
  simp

/-- For a generating marking, the canonical orbit map sends the regular basis vector `(g,k)`
to the class of any conjugate of the `k`-th relator by a word lifting `g`. -/
noncomputable def modTwoRelatorOrbit
    (heval : Function.Surjective (FreeGroup.lift m)) :
    Multiplicative (RegularModTwoRelationModule L rel) →*
      FreeRelationModTwoQuotient m := by
  letI := freeRelationModTwoQuotientCommGroup m
  let liftSection : L → FreeGroup X := Function.surjInv heval
  let orbitAdd : RegularModTwoRelationModule L rel →+
      Additive (FreeRelationModTwoQuotient m) :=
    Finsupp.liftAddHom fun p => freeRelationModTwoZModHom
      (QuotientGroup.mk' (freeRelationModTwoSubgroup m)
        (relationKernelConj m (liftSection p.1)
          ⟨w p.2, MonoidHom.mem_ker.mpr (hrel p.2)⟩))
  exact AddMonoidHom.toMultiplicative orbitAdd

/-- The canonical orbit map has the advertised value on every relator-orbit basis vector. -/
theorem modTwoRelatorOrbit_basis
    (heval : Function.Surjective (FreeGroup.lift m))
    (f : FreeGroup X) (k : rel) :
    modTwoRelatorOrbit (w := w) (hrel := hrel) heval
        (Multiplicative.ofAdd
          (Finsupp.single (FreeGroup.lift m f, k) (1 : ZMod 2))) =
      QuotientGroup.mk' (freeRelationModTwoSubgroup m)
        (relationKernelConj m f
          ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) := by
  letI := freeRelationModTwoQuotientCommGroup m
  let liftSection : L → FreeGroup X := Function.surjInv heval
  have hsection : FreeGroup.lift m (liftSection (FreeGroup.lift m f)) =
      FreeGroup.lift m f := Function.surjInv_eq heval _
  change (Finsupp.liftAddHom fun p => freeRelationModTwoZModHom
      (QuotientGroup.mk' (freeRelationModTwoSubgroup m)
        (relationKernelConj m (liftSection p.1)
          ⟨w p.2, MonoidHom.mem_ker.mpr (hrel p.2)⟩)))
      (Finsupp.single (FreeGroup.lift m f, k) (1 : ZMod 2)) = _
  rw [Finsupp.liftAddHom_apply_single]
  rw [freeRelationModTwoZModHom_one]
  change QuotientGroup.mk' (freeRelationModTwoSubgroup m)
      (relationKernelConj m (liftSection (FreeGroup.lift m f))
        ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) = _
  exact relationKernelConj_modTwo_eq_of_lift_eq m _ _ _ hsection

/-- For a generating marking, relation-basis coordinates split the canonical relator-orbit
map in the genuine quotient `R / (R²[R,R])`. -/
noncomputable def ModTwoRelationBasisCoordinates.toStronglyFreeModTwoRelatorSummand
    (B : ModTwoRelationBasisCoordinates w hrel)
    (heval : Function.Surjective (FreeGroup.lift m)) :
    StronglyFreeModTwoRelatorSummand w hrel where
  orbit := modTwoRelatorOrbit (w := w) (hrel := hrel) heval
  coordinates := B.quotientCoordinates
  retract := by
    apply Finsupp.mulHom_ext
    rintro ⟨g, k⟩ y
    rcases ZMod.eq_zero_or_eq_one y with rfl | rfl
    · simp
    · obtain ⟨f, rfl⟩ := heval g
      rw [MonoidHom.comp_apply,
        modTwoRelatorOrbit_basis (w := w) (hrel := hrel)]
      change B.quotientCoordinates
        (freeRelationModTwoMk m (relationKernelConj m f
          ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩)) = _
      rw [B.quotientCoordinates_mk, B.conjugation, B.relator]
      simp
  orbit_basis := modTwoRelatorOrbit_basis (w := w) (hrel := hrel) heval
  conjugation f s := by
    change B.quotientCoordinates
        (freeRelationModTwoMk m (relationKernelConj m f s)) =
      Multiplicative.ofAdd
        (regularModTwoTranslate L rel (FreeGroup.lift m f)
          (Multiplicative.toAdd
            (B.quotientCoordinates (freeRelationModTwoMk m s))))
    rw [B.quotientCoordinates_mk, B.quotientCoordinates_mk]
    exact B.conjugation f s

/-- Under a surjective marking, the older coordinate interface and the explicit split-summand
strong-freeness interface are logically equivalent. -/
theorem nonempty_stronglyFreeModTwoRelatorSummand_iff_relationBasisCoordinates
    (heval : Function.Surjective (FreeGroup.lift m)) :
    Nonempty (StronglyFreeModTwoRelatorSummand w hrel) ↔
      Nonempty (ModTwoRelationBasisCoordinates w hrel) := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.toModTwoRelationBasisCoordinates⟩
  · rintro ⟨B⟩
    exact ⟨B.toStronglyFreeModTwoRelatorSummand heval⟩

/-- An equivariant retraction of the universal Fox relation matrix gives the actual classical
split strongly-free relator summand, provided the marking generates the target. -/
noncomputable def ModTwoFoxRelationRetraction.toStronglyFreeModTwoRelatorSummand
    (R : ModTwoFoxRelationRetraction m w)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (heval : Function.Surjective (FreeGroup.lift m)) :
    StronglyFreeModTwoRelatorSummand w hrel :=
  ModTwoRelationBasisCoordinates.toStronglyFreeModTwoRelatorSummand
    (ModTwoRelationBasisCoordinates.ofFoxRetraction hrel R) heval

/-- A certified universal Fox pivot normal form gives the actual classical split strongly-free
relator summand. -/
noncomputable def ModTwoFoxRelationNormalForm.toStronglyFreeModTwoRelatorSummand
    (N : ModTwoFoxRelationNormalForm m w)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (heval : Function.Surjective (FreeGroup.lift m)) :
    StronglyFreeModTwoRelatorSummand w hrel :=
  N.toRetraction.toStronglyFreeModTwoRelatorSummand hrel heval

end CanonicalOrbit

end

end GQ2.Dyadic.Count
