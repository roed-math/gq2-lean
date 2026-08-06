/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLOddDegreeSingleResidual

/-!
# A presenting Frattini frame exists unconditionally, and the square shift cannot see it

Two frames are in play on the odd-degree row, and this file builds the missing one.

* The **arithmetic frame** (`MarkedFrame.exists_isCupAdapted_nuRows_of_cupOne`) is cup-adapted
  and carries the two `ν`-rows, unconditionally in odd degree.  What it does not carry is the
  improved relator; supplying that is exactly the binder `SqCupAdaptedFrameRelator K`.
* The **presentation frame** built here, `frameOfOrientedEquiv`, is the image of the canonical
  generating tuple under the unconditional oriented equivalence
  `f : D_sq(h) ≃ₜ* G_K(2)` of `nonempty_orientedEquiv_oddDegree`.  It carries the improved
  relator (`sqRelWord_frameOfOrientedEquiv`: `sqRelWord (f ∘ sqGen) = f (sqRelWord (sqGen)) =
  f 1 = 1`), the full cyclotomic constructor table (the orientation clause), topological
  generation, and the level-three relation — all with **no hypothesis**.  What it does not
  carry is `ν`.

So the two horns of the reconciliation are literal frames, and §3 prices the only elementary
move between them.

## The square shift is invisible to everything the frame lane records

`MarkedFrame.squareShiftFrame` is the move P3 uses to turn mod-2 `ν`-rows into exact ones.  It
already preserves the cyclotomic table (by hypothesis), the Frattini classes and hence
generation (built into the definition), and cup-adaptation
(`MarkedFrame.isCupAdapted_squareShiftFrame`).  §3 adds the last invariant:

  `levelThreeRelation_squareShiftFrame` — the shift also preserves `LevelThreeRelation`.

The proof is the reason: in `Q₃ = G/λ₃` a square lies in `Z₂ = λ₂/λ₃`, which is central of
exponent `2`, and `levelThreeTransgression.sqRelWord_mul_central` says the improved word does
not move under central square-one offsets.  Consequently **no level-three argument can decide
whether a square shift preserves the improved relator**: the shift is invisible there, exactly
as it is invisible to the cup form.  Whatever obstruction exists lives strictly above level
three — the same place the frame residual's gap already lives
(`GammaLSqCupAdaptedFrameGeneration`, §2 docstring).

§4 prices the shift route anyway: `sqMarkedForwardSupply_of_shiftedFrame` says a square shift of
*any* frame which still kills the relator and lands on the two exact `ν`-rows discharges the
whole marked forward supply.  Its relator hypothesis is a relator statement about the shifted
frame — i.e. the shift route converts the `ν`-half of the residual back into a relator half.
The two horns are therefore coupled, not independent.

## What is *not* proved here

`frameOfOrientedEquiv` is **not** shown to be cup-adapted.  Cup-adaptation is never derived from
a presentation anywhere in the repo: it is always constructed from the arithmetic by Witt
adaptation of the Frattini cup form.  The missing step is the converse Labute direction — that
the cup form of `G_K(2)` in the basis dual to a *presenting* tuple is the relator's quadratic
initial Gram.  Since the cup form is functorial along an isomorphism and `H²(·, 𝔽₂)` is
one-dimensional here (so its identification with `𝔽₂` is unique), that statement transports
along `f` to a statement about the model group `D_sq(h)` alone; the repo has no `H²(D_sq(h))`
cup computation to land it on, so it is recorded as an open reduction rather than proved.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 A dense subgroup surjects onto every discrete quotient -/

section Density

/-- **Density plus a discrete target is surjectivity of the abstract subgroup.**  If a tuple
generates topologically and `φ` is a continuous surjection onto a discrete group, then the
`φ`-images of the tuple generate the target on the nose. -/
theorem closure_range_comp_eq_top_of_dense {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [DiscreteTopology H] {ι : Type*}
    (φ : G →* H)
    (hφ : Continuous φ) (hsurj : Function.Surjective φ) (g : ι → G)
    (hdense : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤) :
    Subgroup.closure (Set.range fun i ↦ φ (g i)) = ⊤ := by
  have hmap : (Subgroup.closure (Set.range g)).map φ =
      Subgroup.closure (Set.range fun i ↦ φ (g i)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← hmap, Subgroup.eq_top_iff']
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : x ∈ closure ((Subgroup.closure (Set.range g) : Subgroup G) : Set G) := by
    have hmem : x ∈ (Subgroup.closure (Set.range g)).topologicalClosure := by
      rw [hdense]; trivial
    exact hmem
  obtain ⟨a, haU, haA⟩ :=
    mem_closure_iff.mp hx (φ ⁻¹' {φ x}) ((isOpen_discrete {φ x}).preimage hφ) rfl
  exact ⟨a, haA, haU⟩

end Density

/-! ## §2 The frame of the unconditional oriented equivalence -/

section PresentingFrame

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The frame of an oriented equivalence.**  The images of the canonical generating tuple of
`D_sq(h)` form a Frattini frame of `G_K(2)`: the five cyclotomic rows are the orientation clause
read at the generators, and level-two generation is `dsq_topGen` pushed through a continuous
surjection onto the discrete quotient `Q₂`. -/
def frameOfOrientedEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) :
    SqCyclotomicFrattiniFrame K h where
  generators i := f (sqGen h i)
  sigma := by rw [horient]; exact chiSq_sigma h
  x0 := by rw [horient]; exact chiSq_x0 h
  x1 := by rw [horient]; exact chiSq_x1 h
  handleU j := by
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (f (sqGen h (sqHandleIdxU j))) = 1
    rw [horient]; exact chiSq_handleU h j
  handleV j := by
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (f (sqGen h (sqHandleIdxV j))) = 1
    rw [horient]; exact chiSq_handleV h j
  levelTwoGen := by
    haveI : DiscreteTopology (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      discreteTopology_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K)
        isProP_maxProPQuotient 2
    exact closure_range_comp_eq_top_of_dense
      ((levelMk (maxProPQuotient 2 (GalK K)) 2).comp f.toMulEquiv.toMonoidHom)
      ((continuous_levelMk (maxProPQuotient 2 (GalK K)) 2).comp f.continuous_toFun)
      ((levelMk_surjective (maxProPQuotient 2 (GalK K)) 2).comp (EquivLike.surjective f))
      (sqGen h) (dsq_topGen h)

@[simp] theorem frameOfOrientedEquiv_generators {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) (i : Fin (sqRank h)) :
    (frameOfOrientedEquiv f horient).generators i = f (sqGen h i) := rfl

/-- **The frame of an equivalence satisfies the improved relator, unconditionally.**  The word
is a monoid-hom image of the defining relation `dsq_relation` of `D_sq(h)`. -/
theorem sqRelWord_frameOfOrientedEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) :
    sqRelWord (frameOfOrientedEquiv f horient).generators = 1 := by
  show sqRelWord (fun i ↦ f (sqGen h i)) = 1
  rw [← map_sqRelWord f (sqGen h), dsq_relation h, map_one]

/-- The same frame generates topologically — free from
`sqCyclotomicFrattiniFrame_topologicalClosure_eq_top`. -/
theorem topologicalClosure_frameOfOrientedEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) :
    (Subgroup.closure (Set.range (frameOfOrientedEquiv f horient).generators)).topologicalClosure
      = ⊤ :=
  sqCyclotomicFrattiniFrame_topologicalClosure_eq_top _

/-- The level-three shadow, as a consequence rather than a hypothesis: the relator holds
globally, so it holds modulo `λ₃`. -/
theorem levelThreeRelation_frameOfOrientedEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) :
    (frameOfOrientedEquiv f horient).LevelThreeRelation := by
  show sqRelWord (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3
    ((frameOfOrientedEquiv f horient).generators i)) = 1
  rw [← map_sqRelWord (levelMk (maxProPQuotient 2 (GalK K)) 3)
    (frameOfOrientedEquiv f horient).generators, sqRelWord_frameOfOrientedEquiv, map_one]

/-- **A presenting Frattini frame exists at every odd degree, with no hypothesis.**  This is the
conclusion of `SqCupAdaptedFrameRelator` (and of `SqCupAdaptedFramePresentation`) witnessed on a
frame — not on *every* cup-adapted frame, which is the binder's actual content, but on one built
by the forward presentation theorem. -/
theorem exists_presentingFrame_oddDegree {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ F : SqCyclotomicFrattiniFrame K h, sqRelWord F.generators = 1 ∧
      (Subgroup.closure (Set.range F.generators)).topologicalClosure = ⊤ ∧
        F.LevelThreeRelation := by
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree (K := K) hdeg
  exact ⟨frameOfOrientedEquiv f horient, sqRelWord_frameOfOrientedEquiv f horient,
    topologicalClosure_frameOfOrientedEquiv f horient,
    levelThreeRelation_frameOfOrientedEquiv f horient⟩

end PresentingFrame

/-! ## §3 The square shift is invisible at level three -/

section SquareShift

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The square shift preserves the level-three relation.**  In `Q₃` a square lies in the
central exponent-`2` layer `Z₂`, and the improved word does not move under central square-one
offsets.  So the level-three machinery — the only part of the frame lane that is a theorem —
cannot see the shift at all. -/
theorem levelThreeRelation_squareShiftFrame {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (s : Fin (sqRank h) → maxProPQuotient 2 (GalK K))
    (hs : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i)) (hrel : F.LevelThreeRelation) :
    (MarkedFrame.squareShiftFrame F s hs).LevelThreeRelation := by
  have hmem : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) 3 (s i) ^ 2 ∈
      zLayer (maxProPQuotient 2 (GalK K)) 2 := fun i ↦ sq_mem_zLayer_two _
  have hstep : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) 3
      ((MarkedFrame.squareShiftFrame F s hs).generators i) =
      levelMk (maxProPQuotient 2 (GalK K)) 3 (F.generators i) *
        levelMk (maxProPQuotient 2 (GalK K)) 3 (s i) ^ 2 := by
    intro i
    rw [MarkedFrame.squareShiftFrame_generators, map_mul, map_mul, ← pow_two]
  show sqRelWord (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3
    ((MarkedFrame.squareShiftFrame F s hs).generators i)) = 1
  rw [funext hstep, levelThreeTransgression.sqRelWord_mul_central
    (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3 (F.generators i))
    (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3 (s i) ^ 2)
    (fun i w ↦ zLayer_commute (hmem i) w)
    (fun i ↦ zLayer_sq (maxProPQuotient 2 (GalK K)) (hmem i))]
  exact hrel

/-- **The shift's total invisibility, in one statement.**  A square shift preserves the exact
cyclotomic table (hypothesis `hs`), topological generation (`squareShiftFrame`'s own
`levelTwoGen`), cup-adaptation (`isCupAdapted_squareShiftFrame`) and the level-three relation.
Every invariant of the frame lane that is currently a theorem is therefore blind to it, and only
the *global* relator can distinguish the shifted frame from the original. -/
theorem squareShiftFrame_invariants {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (s : Fin (sqRank h) → maxProPQuotient 2 (GalK K))
    (hs : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i))
    (hcup : F.IsCupAdapted) (hrel : F.LevelThreeRelation) :
    (MarkedFrame.squareShiftFrame F s hs).IsCupAdapted ∧
      (MarkedFrame.squareShiftFrame F s hs).LevelThreeRelation ∧
      (Subgroup.closure (Set.range (MarkedFrame.squareShiftFrame F s hs).generators)
        ).topologicalClosure = ⊤ :=
  ⟨MarkedFrame.isCupAdapted_squareShiftFrame F s hs hcup,
    levelThreeRelation_squareShiftFrame F s hs hrel,
    sqCyclotomicFrattiniFrame_topologicalClosure_eq_top _⟩

end SquareShift

/-! ## §4 Pricing the shift route -/

section ShiftRoute

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **A presenting frame with the two exact `ν`-rows is the whole marked forward supply.**  This
is `MarkedFrame.oddDegreeGalKSqMarkedForwardSupply` with cup-adaptation and the binder replaced
by the two clauses they were used to produce. -/
theorem sqMarkedForwardSupply_of_presentingFrame (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2))
    (hrel : sqRelWord F.generators = 1)
    (hsigma : nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (F.generators 1) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    SqMarkedForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) :=
  MarkedFrame.sqMarkedForwardSupply_of_forwardGeneratorData B hodd
    (MarkedFrame.forwardGeneratorDataOfFrame F hrel
      (sqCyclotomicFrattiniFrame_topologicalClosure_eq_top F)) hsigma hx0

/-- **The shift route, priced.**  If a square shift of a frame both keeps killing the relator and
lands on the two exact `ν`-rows, the odd-degree row's `ν`-half is discharged.  The relator
hypothesis is the crux, and §3 shows it is exactly the part no level-three or cup argument can
supply: the shift route converts the `ν`-half of the residual back into a relator half. -/
theorem sqMarkedForwardSupply_of_shiftedFrame (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2))
    (s : Fin (sqRank ((Module.finrank ℚ_[2] K - 1) / 2)) → maxProPQuotient 2 (GalK K))
    (hs : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i))
    (hrel : sqRelWord (MarkedFrame.squareShiftFrame F s hs).generators = 1)
    (hsigma : nuUrKTwo B (F.generators 0 * (s 0 * s 0)) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (F.generators 1 * (s 1 * s 1)) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    SqMarkedForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) :=
  sqMarkedForwardSupply_of_presentingFrame B hodd (MarkedFrame.squareShiftFrame F s hs) hrel
    hsigma hx0

end ShiftRoute

end

#print axioms GQ2.Dyadic.LSquare.closure_range_comp_eq_top_of_dense
#print axioms GQ2.Dyadic.LSquare.frameOfOrientedEquiv
#print axioms GQ2.Dyadic.LSquare.sqRelWord_frameOfOrientedEquiv
#print axioms GQ2.Dyadic.LSquare.topologicalClosure_frameOfOrientedEquiv
#print axioms GQ2.Dyadic.LSquare.levelThreeRelation_frameOfOrientedEquiv
#print axioms GQ2.Dyadic.LSquare.exists_presentingFrame_oddDegree
#print axioms GQ2.Dyadic.LSquare.levelThreeRelation_squareShiftFrame
#print axioms GQ2.Dyadic.LSquare.squareShiftFrame_invariants
#print axioms GQ2.Dyadic.LSquare.sqMarkedForwardSupply_of_presentingFrame
#print axioms GQ2.Dyadic.LSquare.sqMarkedForwardSupply_of_shiftedFrame

end GQ2.Dyadic.LSquare
