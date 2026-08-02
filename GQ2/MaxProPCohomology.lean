/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex GPT-5
-/
module

public import GQ2.Cohomology
public import GQ2.MaxProP

@[expose] public section

/-!
# Degree-one cohomology of a maximal pro-`p` quotient

For a trivial coefficient module `M`, continuous `1`-cocycles are exactly continuous
homomorphisms to `Multiplicative M`.  If that target is pro-`p`, the universal property of
`maxProPQuotient p G` therefore says that pullback along `maxProPMk p G` is an equivalence on
`Z¹`, and hence on `H¹` because trivial action also makes `B¹ = 0`.

The final computation theorem records that the resulting `H¹` equivalence is not merely an
abstract cardinality comparison: its forward map is the existing inflation map `inf1`.

There is intentionally no degree-two analogue here.  The maximal pro-`p` universal property in
`MaxProP.lean` controls homomorphisms into pro-`p` groups, which is exactly what is needed in
degree one with trivial coefficients.  An `H²` comparison needs an additional extension/cohomology
theorem and does not follow from that universal property alone.
-/

namespace GQ2

open ContCoh

namespace ContCoh

section InflationComputations

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction Q M] [ContinuousSMul Q M]
variable (pi : ContinuousMonoidHom G Q) (hpi : ∀ (g : G) (m : M), pi g • m = g • m)

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] [ContinuousSMul G M] [ContinuousSMul Q M] in
/-- Inflation in degree one computes by cocycle pullback on a represented class. -/
@[simp] theorem inf1_H1mk (z : Z1 Q M) :
    inf1 pi hpi (H1mk Q M z) =
      H1mk G M (Z1comap pi (AddMonoidHom.id M) continuous_id hpi z) :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] [ContinuousSMul G M] [ContinuousSMul Q M] in
/-- Inflation in degree two computes by cocycle pullback on a represented class. -/
@[simp] theorem inf2_H2mk (z : Z2 Q M) :
    inf2 pi hpi (H2mk Q M z) =
      H2mk G M (Z2comap pi (AddMonoidHom.id M) continuous_id hpi z) :=
  rfl

end InflationComputations

end ContCoh

section TrivialCoefficients

variable {p : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
variable [DistribMulAction G M] [ContinuousSMul G M]
variable [DistribMulAction (maxProPQuotient p G) M]
  [ContinuousSMul (maxProPQuotient p G) M]

/-- A continuous `1`-cocycle for a trivial action, regarded as a continuous character into the
multiplicative copy of its additive coefficient group. -/
private def z1ToContinuousCharOfTrivial (htriv : ∀ (g : G) (m : M), g • m = m)
    (z : Z1 G M) : ContinuousMonoidHom G (Multiplicative M) where
  toFun g := Multiplicative.ofAdd (z.1 g)
  map_one' := congrArg Multiplicative.ofAdd (Z1_apply_one z)
  map_mul' g h :=
    congrArg Multiplicative.ofAdd (((mem_Z1_iff_of_trivial htriv).mp z.2).2 g h)
  continuous_toFun := ((mem_Z1_iff_of_trivial htriv).mp z.2).1

/-- A continuous character into a multiplicative copy, regarded as a `1`-cocycle for a trivial
action. -/
private def continuousCharToZ1OfTrivial (htriv : ∀ (g : G) (m : M), g • m = m)
    (f : ContinuousMonoidHom G (Multiplicative M)) : Z1 G M :=
  ⟨fun g => Multiplicative.toAdd (f g), (mem_Z1_iff_of_trivial htriv).mpr
    ⟨f.continuous_toFun, fun g h => congrArg Multiplicative.toAdd (map_mul f g h)⟩⟩

omit [T2Space M] [ContinuousSMul G M]
  [ContinuousSMul (maxProPQuotient p G) M] in
/-- Pullback on `1`-cocycles along `G → G(p)` is bijective for a trivial pro-`p` coefficient
group. -/
theorem bijective_Z1comap_maxProPMk_of_trivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    Function.Bijective
      (Z1comap (maxProPMk p G) (AddMonoidHom.id M) continuous_id
        (fun g m => (htrivQ (maxProPMk p G g) m).trans (htrivG g m).symm)) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel p G) q
    exact congrFun (congrArg Subtype.val hab) g
  · intro z
    let f : ContinuousMonoidHom G (Multiplicative M) :=
      z1ToContinuousCharOfTrivial htrivG z
    let fbar : ContinuousMonoidHom (maxProPQuotient p G) (Multiplicative M) :=
      (maxProPHomEquiv hM).symm f
    refine ⟨continuousCharToZ1OfTrivial htrivQ fbar, ?_⟩
    apply Subtype.ext
    funext g
    exact congrArg (fun u => Multiplicative.toAdd (u g))
      ((maxProPHomEquiv hM).apply_symm_apply f)

/-- Pullback along `G → G(p)` as an additive equivalence on continuous `1`-cocycles with
trivial pro-`p` coefficients. -/
noncomputable def maxProPZ1EquivOfTrivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    Z1 (maxProPQuotient p G) M ≃+ Z1 G M :=
  AddEquiv.ofBijective
    (Z1comap (maxProPMk p G) (AddMonoidHom.id M) continuous_id
      (fun g m => (htrivQ (maxProPMk p G g) m).trans (htrivG g m).symm))
    (bijective_Z1comap_maxProPMk_of_trivial hM htrivG htrivQ)

/-- Inflation along `G → G(p)` as an additive equivalence on `H¹` with trivial pro-`p`
coefficients. -/
noncomputable def maxProPH1EquivOfTrivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    H1 (maxProPQuotient p G) M ≃+ H1 G M :=
  (H1equivZ1OfTrivial htrivQ).trans
    ((maxProPZ1EquivOfTrivial hM htrivG htrivQ).trans
      (H1equivZ1OfTrivial htrivG).symm)

omit [T2Space M] [ContinuousSMul G M]
  [ContinuousSMul (maxProPQuotient p G) M] in
/-- The forward map of `maxProPH1EquivOfTrivial` is the existing degree-one inflation map. -/
theorem maxProPH1EquivOfTrivial_apply
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m)
    (x : H1 (maxProPQuotient p G) M) :
    maxProPH1EquivOfTrivial hM htrivG htrivQ x =
      inf1 (maxProPMk p G)
        (fun g m => (htrivQ (maxProPMk p G g) m).trans (htrivG g m).symm) x := by
  obtain ⟨z, rfl⟩ := H1mk_surjective (G := maxProPQuotient p G) (M := M) x
  rfl

end TrivialCoefficients

end GQ2
