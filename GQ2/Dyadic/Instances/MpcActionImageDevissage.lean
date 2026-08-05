/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcActionImageDevissage
import GQ2.Dyadic.Instances.MpcExact

/-!
# Action-image devissage for the corrected procyclic-`M` row

The row-independent half of the argument is `RowActionImage`, built in
`NpcActionImageDevissage`.  This file supplies the procyclic-`M` inputs and the pushed residue
layer, exactly as its procyclic-`N` twin does.

The one structural difference is the resolver.  The `M` row's family is *display-dependent*: the
`ω₂`-only displays `.one` and `.lit k` use the constant resolver `omega2Exp N`, while a genuine
`.hat num den` display uses the two-valued `npcResolver N ⟨num, den⟩` shared with the `N` row.
`MProcyclicExact.resolvedFamily` already records that case split, and `levelResolver` below
discharges the `LevelResolver` interface one display at a time.  Nothing in the devissage sees
the split: the action-map transport theorem compares two Stokes complexes with *different* words,
so a per-display resolver is no obstacle at all.

What is left over is the same as for the `N` row, and is the honest state of both procyclic rows:
`SimpleActionImageStokes` — Stokes duality at the canonical action-image marking of a *simple*
elementary coefficient — is still an interface, not a theorem, and it splits along the
`tau`-dichotomy into an unramified obligation on a procyclic target
(`finiteActionImage_unramified_closure_sigma`) and a ramified obligation.
-/

namespace GQ2.Dyadic.MProcyclicExact

noncomputable section

open GQ2 GQ2.SectionEight GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The row's level-indexed resolver -/

/-- The corrected procyclic-`M` row supplies a level-indexed resolver, one display at a time:
`resolvesAt_mpcFam` for the two `ω₂`-only displays and `resolvesAt_mpcFamOf_hat` for a genuine
`η̂`-display, with `resolvedFamily_isStokesEndpoint` as the common endpoint half. -/
theorem levelResolver {alpha r pp h q : ℕ} (d : EtaDisplay) (hα : 1 ≤ alpha) (hqe : Even q) :
    LevelResolver (2 + 2 * h) q (mpcW alpha r pp d h) (resolvedFamily alpha r pp h q d) where
  resolves := fun _ _ _ _ _ _ hN hord ↦ by
    cases d with
    | one => exact resolvesAt_mpcFam hN hord alpha r pp h q trivial
    | lit k => exact resolvesAt_mpcFam hN hord alpha r pp h q trivial
    | hat num den => exact resolvesAt_mpcFamOf_hat hN hord alpha r pp h q num den (fun _ ↦ 0)
  endpoint := fun _ hN hv ↦ resolvedFamily_isStokesEndpoint hN hv hα hqe d

/-! ## The pushed residues -/

/-- The source-facing residue for the corrected procyclic-`M` row: markings pushed forward from
the candidate group only, and the three induced word-cohomology bijections in place of the six
`StokesDuality` clauses. -/
def PushedHsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C) (N : ℕ),
    N ≠ 0 → N.factorization 2 ≠ 0 →
    ∀ (hr : ∀ k, FreeGroup.lift
        (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
        (resolvedFamily alpha r pp h q d N k) = 1)
      (hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d N))
      (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesCohomologyBijections
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
          (resolvedFamily alpha r pp h q d N) V hr hend

/-- The coefficient-independent residue at the uniform level `4 * Monoid.exponent C`, in the
shape produced by action-image devissage. -/
def UniformPushedHsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        StokesDuality
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
          (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) A

/-- The historical all-markings residue implies the pushed cohomological one. -/
theorem pushedHsimp_of_hsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) : PushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho N hN hv hr hend V _ _ _ hV₂ hsimple
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g)⟩ with ht
  exact (stokesDuality_iff_cohomologyBijections ⇑t (resolvedFamily alpha r pp h q d N) V hr
    hend).mp (hsimp C t N hN hv hr V hV₂ hsimple)

/-! ## The pushed replacements for the two chain entry points -/

/-- The devissage step of the pushed residue, once relator death at the pushed marking is in
hand. -/
private theorem stokesDuality_of_pushed_of_relators {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hr : ∀ k, FreeGroup.lift
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N k) = 1)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A := by
  have hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d N) :=
    resolvedFamily_isStokesEndpoint hN hv hα hqe d
  exact stokesDuality_of_simple _ (resolvedFamily alpha r pp h q d N) hr hend
    (fun V _ _ _ hV₂ hsimple ↦
      (stokesDuality_iff_cohomologyBijections _ (resolvedFamily alpha r pp h q d N) V hr
        hend).mpr (hsimp C rho N hN hv hr hend V hV₂ hsimple)) A hA₂

/-- `MProcyclicExact.stokesDuality` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_of_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  stokesDuality_of_pushed_of_relators hsimp hα hqe rho hN hv
    (fun k ↦ lower_rel (A := ZMod 2) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres k) A hA₂

/-- `MProcyclicExact.stokesDuality_T` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_T_of_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) := by
  have hb := resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) orderOf_dvd_heisLevel_scal
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  exact stokesDuality_of_pushed hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hb.1
    (Additive ↥D.T) (radT_add_self D)

/-! ## The uniform residue, and the action-image route to it -/

/-- The pushed residue supplies the uniform one. -/
theorem uniformPushedHsimp_of_pushedHsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace (WordLift A C) := ⊥
  letI : DiscreteTopology (WordLift A C) := ⟨rfl⟩
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) (WordLift A C) := by
    refine (levelResolver d hα hqe).resolves (WordLift A C) (4 * Monoid.exponent C)
      (fourMulExponent_ne_zero_and_even C).1 ?_
    intro x
    refine (WordLift.orderOf_dvd_two_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) x).trans ?_
    exact mul_dvd_mul_right (by norm_num) (Monoid.exponent C)
  exact stokesDuality_of_pushed_of_relators hsimp hα hqe rho
    (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
    (fun k ↦ lower_rel (A := A) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres k) A hA₂

/-- Both weakenings composed. -/
theorem uniformPushedHsimp_of_hsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_pushedHsimp (pushedHsimp_of_hsimp hsimp) hα hqe

/-- **The action-image route for the corrected procyclic-`M` row, at every admissible level.**
The only remaining input is the simple-module branch at the canonical action image. -/
theorem stokesDuality_of_actionImage {alpha r pp h q : ℕ} {d : EtaDisplay} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {N : ℕ} (hN : N ≠ 0)
    (hord : ∀ x : HeisLift A C, orderOf x ∣ N) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  pushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂ hN hord

/-- The uniform residue from the action image. -/
theorem uniformPushedHsimp_of_actionImage {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d)) :
    UniformPushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  exact uniformPushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂

/-- The residue split along the `tau`-dichotomy, at the corrected procyclic-`M` word. -/
theorem uniformPushedHsimp_of_branches {alpha r pp h q : ℕ} {d : EtaDisplay} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hunram : UnramifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    (hram : RamifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d)) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_actionImage hα hqe (simpleActionImageStokes_of_branches hunram hram)

/-! ## Regression: the historical entry points factor through the pushed ones -/

/-- `MProcyclicExact.stokesDuality`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_via_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  stokesDuality_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho hN hv hres A hA₂

/-- `MProcyclicExact.stokesDuality_T`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_T_via_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) :=
  stokesDuality_T_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho

end

/-! ## Axiom footprint -/

#print axioms GQ2.Dyadic.MProcyclicExact.levelResolver
#print axioms GQ2.Dyadic.MProcyclicExact.pushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_of_actionImage
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_actionImage
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_branches
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_via_pushed
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_T_via_pushed

end GQ2.Dyadic.MProcyclicExact
