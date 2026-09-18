import GQ2.Dyadic.MarkedCore.MFullFrameCompactness
import GQ2.Dyadic.MarkedCore.FreeProTwoBasisCorrection

/-!
# Arbitrarily deep exact M stages, and the conditional full-stabilizer shape

The M relator has the **two-letter** ordinary row `2 f(A) + 2^alpha f(C)`, not
the single-letter N row. Its primitive relation vector is therefore carried by
the composite word `T = A * C^(2^(alpha-1))`, and it is fixation of `T`, not of
`A`, that supplies the exact ordinary relator row. That is the one place where
this file is not a text substitution of the N argument.

Contents:

* `mStageRelWord_ordinary_row`, `mStageTorsionWord` and
  `mStageRelWord_row_of_torsionWord`: the actual two-letter M row, and the
  exact ordinary row obtained from a fixed primitive torsion word.
* `MStageStep`: the **named** depth-step interface. It is a hypothesis
  everywhere below; nothing in this file proves that any `(alpha, h)` has it.
* `exists_mStageBasis_exact_stage`: from one initial depth-three basis and that
  interface, an actual free basis at every depth with exactly the initial
  coordinate matrix.
* `mFullStabilizer_lift`: the composition shape. It is **conditional** on the
  three named sibling interfaces listed in its own docstring; it is not a
  proved lifting theorem.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

/-! ## The two-letter ordinary M row and its primitive torsion word -/

/-- The **primitive relation word** of the M core on an arbitrary marking:
`T = y_0 * y_2 ^ (2 ^ (alpha - 1))`. On the standard marking of `D_M` this is
literally the torsion generator `A * C^(2^(alpha-1))` whose class spans the
`ZMod 2` slot of `MFrameModel h` (`mPhiHom_mStageTorsionWord`). -/
def mStageTorsionWord {G : Type*} [Group G] {h : ℕ} (alpha : ℕ)
    (y : Fin (coreRank h) → G) : G :=
  y 0 * y 2 ^ (2 ^ (alpha - 1))

theorem mStageTorsionWord_dmGen (alpha h : ℕ) :
    mStageTorsionWord alpha (dmGen alpha h) =
      dmA alpha h * dmC alpha h ^ (2 ^ (alpha - 1)) := rfl

/-- The word fixed below really is the actual M torsion class, not the class of
`Abar` alone: it occupies the torsion slot of the full frame. -/
theorem mPhiHom_mStageTorsionWord {alpha : ℕ} (ha : 1 ≤ alpha) (h : ℕ) :
    mPhiHom ha h (abMk (mStageTorsionWord alpha (dmGen alpha h))) =
      ofAdd (1, 0, 0, 0, 0) := mPhiHom_t ha h

section OrdinaryRows
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h : ℕ}

omit [IsTopologicalGroup G] in
/-- The ordinary row of the literal full M relator, every handle included.
Unlike the N row it reads **two** letters: `2 f(y_0) + 2^alpha f(y_2)`. -/
theorem mStageRelWord_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y : Fin (coreRank h) → G) :
    toAdd (f (mRelWord alpha y)) =
      2 * toAdd (f (y 0)) + (2 : ℤ_[2]) ^ alpha * toAdd (f (y 2)) := by
  rw [map_mRelWord, mRelWord_comm, toAdd_mul, toAdd_pow, toAdd_pow,
    nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

omit [IsTopologicalGroup G] in
/-- Agreement of the primitive torsion word under one ordinary character forces
agreement of the whole M relator row under that character. This is the exact
M replacement for the N head-fixation argument, and it uses `alpha >= 1` only
through `2 * 2^(alpha-1) = 2^alpha`. -/
theorem mStageRelWord_row_of_torsionWord {alpha : ℕ} (ha : 1 ≤ alpha)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y z : Fin (coreRank h) → G)
    (hT : f (mStageTorsionWord alpha y) = f (mStageTorsionWord alpha z)) :
    f (mRelWord alpha y) = f (mRelWord alpha z) := by
  have hpow : (2 : ℤ_[2]) ^ alpha = 2 * (2 : ℤ_[2]) ^ (alpha - 1) := by
    conv_lhs => rw [show alpha = (alpha - 1) + 1 by omega]
    ring
  have hf := congrArg Multiplicative.toAdd hT
  simp only [mStageTorsionWord, map_mul, map_pow, toAdd_mul, toAdd_pow,
    nsmul_eq_mul] at hf
  push_cast at hf
  apply toAdd.injective
  rw [mStageRelWord_ordinary_row, mStageRelWord_ordinary_row, hpow]
  linear_combination (2 : ℤ_[2]) * hf

end OrdinaryRows

/-! ## The named depth-step interface -/

/-- **The M stage-step interface** (the MKERNEL obligation), named so that the
results below can consume it without waiting for its producer.

Read with `d = n + 2`. Given an actual free basis whose orientation and whose
ordinary relator row already match the standard marking, and whose literal
relator error lies in `lambda_(d+1)`, it returns a correction of depth `d`
which

* is invisible to the orientation,
* is invisible to **every** ordinary character, hence leaves every integral
  coordinate of the basis unchanged, and
* pushes the literal relator error into `lambda_(d+2)`.

Nothing in this file proves that any `(alpha, h)` satisfies this. It is the
exact M analogue of the composite of `NAmbientStageSupply` with
`exists_nBasis_full_relative_correction`, and it is stated on the actual free
pro-two group, with no assumed derivative image and no diagonal restriction. -/
def MStageStep (alpha h : ℕ) : Prop :=
  ∀ n : ℕ, ∀ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    (∀ i, mStageOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      mStageOrientation alpha h (freeTwoRankGen (coreRank h) i)) →
    (∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) =
        f (mRelWord alpha (freeTwoRankGen (coreRank h)))) →
    mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 3) →
    ∃ s : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, s i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 2)) ∧
      (∀ i, mStageOrientation alpha h (s i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (s i) = 1) ∧
      mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i) * s i) *
        (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 4)

/-! ## Exact stages at every depth -/

private theorem mStage_relator_row_transport {alpha h : ℕ}
    (e e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hcoords : ∀ j v,
      toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) v))) =
        toAdd (freeTwoCoordinate (coreRank h) j (e0 (freeTwoRankGen (coreRank h) v))))
    (target : FreeTwoRank (coreRank h))
    (hrow0 : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) = f target)
    (f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2])) :
    f (mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) = f target := by
  have hchar : ∀ v, f (e (freeTwoRankGen (coreRank h) v)) =
      f (e0 (freeTwoRankGen (coreRank h) v)) := fun v =>
    freeTwo_commutative_eq_of_coordinates PropOneOne.isProP_two_multPadicInt
      (coreRank h) _ _ (fun j => hcoords j v) f
  calc
    f (mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) =
        f (mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) := by
      apply toAdd.injective
      rw [mStageRelWord_ordinary_row, mStageRelWord_ordinary_row, hchar 0, hchar 2]
    _ = f target := hrow0 f

/-- **The M twin of `exists_nBasis_exact_stage`.** Every depth has an actual
free-basis stage with exactly the initial coordinate matrix and the initial
orientation. The correction supply is the named `MStageStep` interface; the
initial basis, its exact ordinary relator row and its literal depth-three error
are explicit hypotheses, not consequences. No compatible choice of the
separately quantified stage witnesses is asserted or needed.

There is deliberately **no** `2 ≤ alpha` binder here: the iteration is pure
bookkeeping over the named interface, and every `alpha`-dependent fact of the
M route sits inside `MStageStep` and inside the initial data. This is not a
claim that anything is available at `alpha = 1`, where `MStageStep` has no
producer at all. -/
theorem exists_mStageBasis_exact_stage {alpha h : ℕ}
    (hstep : MStageStep alpha h)
    (e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hchi0 : ∀ i, mStageOrientation alpha h (e0 (freeTwoRankGen (coreRank h) i)) =
      mStageOrientation alpha h (freeTwoRankGen (coreRank h) i))
    (hrow0 : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) =
        f (mRelWord alpha (freeTwoRankGen (coreRank h))))
    (herror0 : mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3)
    (n : ℕ) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
        (FreeTwoRank (coreRank h) : Type),
      (∀ i, mStageOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
        mStageOrientation alpha h (freeTwoRankGen (coreRank h) i)) ∧
      (∀ j v,
        toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) v))) =
          toAdd (freeTwoCoordinate (coreRank h) j (e0 (freeTwoRankGen (coreRank h) v)))) ∧
      mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
        (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 3) := by
  induction n with
  | zero => exact ⟨e0, hchi0, fun _ _ => rfl, herror0⟩
  | succ n ih =>
    obtain ⟨e, hechi, hecoords, heerror⟩ := ih
    obtain ⟨s, hs, hschi, hsrow, hserror⟩ := hstep n e hechi
      (mStage_relator_row_transport e e0 hecoords _ hrow0) heerror
    obtain ⟨e', he'⟩ := exists_freeTwoBasisCorrection (coreRank h) e s
      (fun i => twoCentralSeries_antitone (G := (FreeTwoRank (coreRank h) : Type))
        (by omega : 2 ≤ n + 2) (hs i))
    refine ⟨e', ?_, ?_, ?_⟩
    · intro i
      rw [he', map_mul, hschi, mul_one, hechi]
    · intro j v
      rw [he', map_mul, hsrow, mul_one]
      exact hecoords j v
    · have htuple : (fun i => e' (freeTwoRankGen (coreRank h) i)) =
          (fun i => e (freeTwoRankGen (coreRank h) i) * s i) := funext he'
      rw [htuple, show n + 1 + 3 = n + 4 by omega]
      exact hserror

/-! ## The conditional composition -/

/-- The actual full abelian frame quotient of `D_M`. -/
def mStageFrameHom {alpha : ℕ} (ha : 1 ≤ alpha) (h : ℕ) :
    ContinuousMonoidHom (DM alpha h : Type) (MFrameModel h) :=
  (⟨(mFrameExists_phiEquiv ha h).toMulEquiv.toMonoidHom,
    (mFrameExists_phiEquiv ha h).continuous_toFun⟩ : ContinuousMonoidHom _ _).comp
      ⟨abMk, continuous_abMk⟩

theorem mStageFrameHom_apply {alpha : ℕ} (ha : 1 ≤ alpha) (h : ℕ) (x : DM alpha h) :
    mStageFrameHom ha h x = mPhiHom ha h (abMk x) := rfl

/-- **Conditional full M-frame stabilizer lifting.** This is *not* a proved
lift: every one of its hypotheses is an unproved sibling interface, named here
so that the composition is settled in advance.

* `e0`, `hT`, `hchi0`, `hframe0` -- the MINIT obligation: an actual initial
  free basis fixing the primitive torsion word `T = A * C^(2^(alpha-1))`,
  preserving the canonical orientation, and inducing `phi` on the full frame.
* `herror0` -- the MCUP obligation: that same basis has literal relator error
  in `lambda_3`.
* `hstep` -- the MKERNEL obligation: the named `MStageStep` depth interface.

Everything else is proved here: the exact ordinary relator row from `hT`, all
higher exact stages, the transfer to `D_M` and the torsion-sensitive compact
limit. The conclusion is an all-element commuting square for the **full**
abelianization `mPhiHom`, torsion slot included, not for a selected unramified
marking. -/
theorem mFullStabilizer_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hT : mStageTorsionWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) =
      mStageTorsionWord alpha (freeTwoRankGen (coreRank h)))
    (hchi0 : ∀ i, mStageOrientation alpha h (e0 (freeTwoRankGen (coreRank h) i)) =
      mStageOrientation alpha h (freeTwoRankGen (coreRank h) i))
    (hframe0 : ∀ i, mPhiHom (mStageOneLe ha) h
        (abMk (mStageProjection alpha h (e0 (freeTwoRankGen (coreRank h) i)))) =
      phi (mPhiHom (mStageOneLe ha) h (abMk (dmGen alpha h i))))
    (herror0 : mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3)
    (hstep : MStageStep alpha h) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x))) := by
  have hrow0 : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      (Multiplicative ℤ_[2]),
      f (mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) =
        f (mRelWord alpha (freeTwoRankGen (coreRank h))) := fun f =>
    mStageRelWord_row_of_torsionWord (mStageOneLe ha) f _ _ (congrArg f hT)
  have hstages : ∀ k, (mStageFullFrameStageSet (mStageOneLe ha)
      (fun i => mPhiHom (mStageOneLe ha) h
        (abMk (mStageProjection alpha h (e0 (freeTwoRankGen (coreRank h) i))))) k).Nonempty := by
    intro k
    obtain ⟨e, hechi, hecoords, heerror⟩ :=
      exists_mStageBasis_exact_stage hstep e0 hchi0 hrow0 herror0 k
    refine ⟨fun i => mStageProjection alpha h (e (freeTwoRankGen (coreRank h) i)), ?_⟩
    exact mStageFullFrameStageSet_antitone (mStageOneLe ha) _ (by omega : k ≤ k + 3)
      (mStageFullFrameStageSet_of_free_exact_stage (mStageOneLe ha) (k + 3)
        (fun i => e0 (freeTwoRankGen (coreRank h) i)) e hechi hecoords heerror)
  obtain ⟨Psi, hPsi⟩ :=
    exists_mStageFullFrameRealizes_of_stages (mStageOneLe ha) _ hstages
  refine ⟨Psi, hPsi.1, ?_⟩
  let P : ContinuousMonoidHom (DM alpha h : Type) (DM alpha h : Type) :=
    ⟨Psi.toMonoidHom, Psi.continuous_toFun⟩
  let F : ContinuousMonoidHom (MFrameModel h) (MFrameModel h) :=
    ⟨phi.toMonoidHom, phi.continuous_toFun⟩
  have heq : (mStageFrameHom (mStageOneLe ha) h).comp P =
      F.comp (mStageFrameHom (mStageOneLe ha) h) := by
    apply dm_hom_ext
    intro i
    change mPhiHom (mStageOneLe ha) h (abMk (Psi (dmGen alpha h i))) =
      phi (mPhiHom (mStageOneLe ha) h (abMk (dmGen alpha h i)))
    rw [hPsi.2 i]
    exact hframe0 i
  intro x
  exact DFunLike.congr_fun heq x

/-- The MINIT and MCUP obligations bundled as one named interface, so the
final composition has exactly two hypotheses. Still conditional: this file
supplies no instance of it. -/
def MStageInitialLift {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) : Prop :=
  ∃ e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    mStageTorsionWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) =
        mStageTorsionWord alpha (freeTwoRankGen (coreRank h)) ∧
    (∀ i, mStageOrientation alpha h (e0 (freeTwoRankGen (coreRank h) i)) =
      mStageOrientation alpha h (freeTwoRankGen (coreRank h) i)) ∧
    (∀ i, mPhiHom (mStageOneLe ha) h
        (abMk (mStageProjection alpha h (e0 (freeTwoRankGen (coreRank h) i)))) =
      phi (mPhiHom (mStageOneLe ha) h (abMk (dmGen alpha h i)))) ∧
    mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3

/-- The same conditional composition, with the initial data packaged.
`MStageInitialLift` and `MStageStep` are both unproved interfaces here. -/
theorem mFullStabilizer_lift_of_initialLift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hinit : MStageInitialLift ha h phi) (hstep : MStageStep alpha h) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x))) := by
  obtain ⟨e0, hT, hchi0, hframe0, herror0⟩ := hinit
  exact mFullStabilizer_lift ha phi e0 hT hchi0 hframe0 herror0 hstep

#print axioms mStageTorsionWord
#print axioms mStageTorsionWord_dmGen
#print axioms mPhiHom_mStageTorsionWord
#print axioms mStageRelWord_ordinary_row
#print axioms mStageRelWord_row_of_torsionWord
#print axioms MStageStep
#print axioms mStage_relator_row_transport
#print axioms exists_mStageBasis_exact_stage
#print axioms mStageFrameHom
#print axioms mStageFrameHom_apply
#print axioms mFullStabilizer_lift
#print axioms MStageInitialLift
#print axioms mFullStabilizer_lift_of_initialLift

end
end GQ2.Dyadic.MarkedCore
