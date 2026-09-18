/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MInitialCupDepth
import GQ2.Dyadic.MarkedCore.NFrameCupCoordinates
import GQ2.Dyadic.Instances.M0C0PivotAutomorphism

/-!
# The full M frame cup condition, its reduced coordinates, and the converse

The semantic cup-isometry predicate at M quantifies over **every** continuous
mod-two character of the actual full M frame, torsion coordinate included. It
assumes no group lift and no matrix realization.

Two M-specific points are checked here rather than copied from the N file.

* **The relator obligation is the M one.** A frame coordinate character is built
  through `mCoordHom`, whose obligation is `m 0 ^ 2 * m 2 ^ (2 ^ alpha) = 1`,
  not the N obligation `m 0 ^ (2 + 2 ^ alpha) = 1`. Every mod-two coordinate
  marking satisfies it, including the `C` coordinate `i = 2`, because squares
  are trivial in `Multiplicative (ZMod 2)` and `2 ^ alpha` is even. So all
  `4 + 2h` mod-two coordinates of the M frame really are characters. What is
  proved below is exactly that relator obligation; no statement is made here
  about the integral `C` coordinate, which `mPhiHom_word` shows is twisted.
* **The variance is the column-image one.** `NInitialCupDepth.reducedRows m i`
  is the `i`-th coordinate row of the matrix whose **columns** are the images of
  the generators, so the condition proved below is `Abar G Abar^T = G`.
  `MarkedCore/Variance.lean` is the dictionary: `M.lean` stores frame images in
  rows and therefore states the same condition as `Mbar^T G Mbar = G`. The Gram
  is literally shared (`mGram_eq_nGram`, `evenCupForm`), so no M-specific Gram
  appears.

The converse ingredient is the last section: every continuous automorphism of
the actual core `D_M` induces a frame cup isometry, through `dmObs` and the
uniqueness of the one-dimensional degree-two obstruction.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative GQ2.Roe.Labute
open GQ2.Dyadic.EvenModel
open NInitialCupDepth
open scoped GQ2.SectionThree.TopAbInstances

/-- The `alpha >= 1` hypothesis that the M frame construction consumes, named
once so that every frame term in this file is syntactically the same. -/
theorem mCupOneLe {alpha : ℕ} (ha : 2 ≤ alpha) : 1 ≤ alpha := Nat.le_of_succ_le ha

/-! ## The frame of the actual core, and its canonical columns -/

/-- The actual full M frame read off an element of the core. -/
def mCupFrameOfDM {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) :
    ContinuousMonoidHom (DM alpha h : Type) (MFrameModel h) :=
  (⟨mPhiHom (mCupOneLe ha) h, continuous_mPhiHom (mCupOneLe ha) h⟩ :
      ContinuousMonoidHom (topAbelianization (DM alpha h : Type)) (MFrameModel h)).comp
    ⟨abMk, continuous_abMk⟩

/-- The actual canonical columns of the full topological M abelianization. -/
def mCupFrameCanonicalMark {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (i : Fin (coreRank h)) : MFrameModel h :=
  mCupFrameOfDM ha h (dmGen alpha h i)

theorem mCupFrameCanonicalMark_eq {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (i : Fin (coreRank h)) :
    mCupFrameCanonicalMark ha h i =
      mPhiHom (mCupOneLe ha) h (abMk (dmGen alpha h i)) := rfl

/-- **Full mod-two cup preservation at M**, stated on actual continuous frame
characters. There is no orientation condition here, and no identity-handle
condition: those are separate inputs to the eventual group-lifting theorem. -/
def MCupFrameCupIsometry {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) : Prop :=
  ∀ c d : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)),
    evenCupForm (fun i => toAdd (c (phi (mCupFrameCanonicalMark ha h i))))
        (fun i => toAdd (d (phi (mCupFrameCanonicalMark ha h i)))) =
      evenCupForm (fun i => toAdd (c (mCupFrameCanonicalMark ha h i)))
        (fun i => toAdd (d (mCupFrameCanonicalMark ha h i)))

/-! ## The mod-two coordinates of the M frame are characters -/

/-- The M relator obligation for a mod-two coordinate marking. Unlike the N
obligation this one has two blocks; the `C` block dies because `2 ^ alpha` is
even, which is why the `i = 2` coordinate exists as a character. -/
private theorem mCupFrameCoordinate_head_relation {alpha h : ℕ} (ha : 2 ≤ alpha)
    (i : Fin (coreRank h)) :
    (ofAdd (if (0 : Fin (coreRank h)) = i then (1 : ZMod 2) else 0)) ^ 2 *
      (ofAdd (if (2 : Fin (coreRank h)) = i then (1 : ZMod 2) else 0)) ^ (2 ^ alpha)
        = 1 := by
  have hs : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  have hy : ∀ z : Multiplicative (ZMod 2), z ^ 2 ^ alpha = 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, alpha = a + 1 := ⟨alpha - 1, by omega⟩
    intro z
    rw [pow_succ, pow_mul, hs]
  rw [hs, hy, one_mul]

/-- Coordinate `i` of the full M frame, including its torsion coordinate, as a
genuine continuous F2 character. -/
def mCupFrameModTwoCoordinate {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (i : Fin (coreRank h)) :
    ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)) :=
  (mCoordHom alpha h isProP_two_multZMod2
    (fun j => ofAdd (if j = i then (1 : ZMod 2) else 0))
    (mCupFrameCoordinate_head_relation ha i)).comp
      ⟨(mFrameExists_phiEquiv (mCupOneLe ha) h).symm.toMulEquiv.toMonoidHom,
        (mFrameExists_phiEquiv (mCupOneLe ha) h).symm.continuous_toFun⟩

theorem mCupFrameModTwoCoordinate_canonicalMark {alpha : ℕ} (ha : 2 ≤ alpha)
    (h : ℕ) (i j : Fin (coreRank h)) :
    toAdd (mCupFrameModTwoCoordinate ha h i (mCupFrameCanonicalMark ha h j)) =
      if j = i then 1 else 0 := by
  change toAdd (mCoordHom alpha h isProP_two_multZMod2
    (fun k => ofAdd (if k = i then (1 : ZMod 2) else 0))
    (mCupFrameCoordinate_head_relation ha i)
    ((mFrameExists_phiEquiv (mCupOneLe ha) h).symm
      (mFrameExists_phiEquiv (mCupOneLe ha) h (abMk (dmGen alpha h j))))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, mCoordHom_gen, toAdd_ofAdd]

/-! ## The free pro-two basis over the M frame -/

/-- The actual free pro-two cover of the core, sending the free generators to
the marked generators. -/
def mCupFreeMProjection (alpha h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (DM alpha h : Type) :=
  presLiftHom 1 (isProP_DM alpha h) (dmGen alpha h) (map_one _)

theorem mCupFreeMProjection_gen (alpha h : ℕ) (i : Fin (coreRank h)) :
    mCupFreeMProjection alpha h (freeTwoRankGen (coreRank h) i) = dmGen alpha h i :=
  presLiftHom_gen _ _ _ _ _

/-- The composite free cover of the full M frame. -/
def mCupFreeFrameProjection {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (MFrameModel h) :=
  (mCupFrameOfDM ha h).comp (mCupFreeMProjection alpha h)

theorem mCupFreeFrameProjection_gen {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (i : Fin (coreRank h)) :
    mCupFreeFrameProjection ha h (freeTwoRankGen (coreRank h) i) =
      mCupFrameCanonicalMark ha h i :=
  congrArg (fun z => mCupFrameOfDM ha h z) (mCupFreeMProjection_gen alpha h i)

/-- Exact pullback of a frame mod-two coordinate to the reduced free
coordinate, on every free element and not only on generators. -/
theorem mCupFrameModTwoCoordinate_projection {alpha : ℕ} (ha : 2 ≤ alpha)
    (h : ℕ) (i : Fin (coreRank h)) (x : FreeTwoRank (coreRank h)) :
    toAdd (mCupFrameModTwoCoordinate ha h i (mCupFreeFrameProjection ha h x)) =
      nRed (toAdd (freeTwoCoordinate (coreRank h) i x)) := by
  have he : (mCupFrameModTwoCoordinate ha h i).comp (mCupFreeFrameProjection ha h) =
      freeTwoReducedCoordinate (coreRank h) i := by
    apply presPro2_hom_ext
    intro j
    apply toAdd.injective
    change toAdd (mCupFrameModTwoCoordinate ha h i
      (mCupFreeFrameProjection ha h (freeTwoRankGen (coreRank h) j))) =
        nRed (toAdd (freeTwoCoordinate (coreRank h) i (freeTwoRankGen (coreRank h) j)))
    rw [mCupFreeFrameProjection_gen, mCupFrameModTwoCoordinate_canonicalMark,
      freeTwoCoordinate_gen, toAdd_ofAdd]
    split_ifs <;> simp
  exact congrArg (fun f : ContinuousMonoidHom _ _ => toAdd (f x)) he

/-! ## The semantic condition gives the exact reduced-coordinate equations -/

/-- **T1.** The semantic M cup condition, read on any free tuple projecting to
the prescribed frame columns, is exactly the reduced-coordinate cup system in
the column-image variance `Abar G Abar^T = G`. -/
theorem MCupFrameCupIsometry.reducedRows_of_projection {alpha h : ℕ} {ha : 2 ≤ alpha}
    {phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)}
    (hcup : MCupFrameCupIsometry ha phi)
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hproj : ∀ k, mCupFreeFrameProjection ha h (m k) =
      phi (mCupFrameCanonicalMark ha h k))
    (i j : Fin (coreRank h)) :
    evenCupForm (reducedRows m i) (reducedRows m j) =
      evenCupForm (reducedRows (freeTwoRankGen (coreRank h)) i)
        (reducedRows (freeTwoRankGen (coreRank h)) j) := by
  have hc := hcup (mCupFrameModTwoCoordinate ha h i) (mCupFrameModTwoCoordinate ha h j)
  have hleft (l k : Fin (coreRank h)) :
      toAdd (mCupFrameModTwoCoordinate ha h l (phi (mCupFrameCanonicalMark ha h k))) =
        reducedRows m l k := by
    rw [← hproj, mCupFrameModTwoCoordinate_projection]
    rfl
  have hright (l k : Fin (coreRank h)) :
      toAdd (mCupFrameModTwoCoordinate ha h l (mCupFrameCanonicalMark ha h k)) =
        reducedRows (freeTwoRankGen (coreRank h)) l k := by
    show _ = nRed (toAdd (freeTwoCoordinate (coreRank h) l (freeTwoRankGen (coreRank h) k)))
    rw [mCupFrameModTwoCoordinate_canonicalMark, freeTwoCoordinate_gen, toAdd_ofAdd]
    split_ifs <;> simp
  simpa only [hleft, hright] using hc

/-- **T1 composed with T2.** The full M frame cup condition plus an `A` letter
agreeing with the reference `A` letter modulo lambda-two puts the actual M
relator error in lambda-three. -/
theorem mCupRelWord_error_mem_three_of_frame {alpha h : ℕ} {ha : 2 ≤ alpha}
    {phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)}
    (hcup : MCupFrameCupIsometry ha phi)
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hproj : ∀ k, mCupFreeFrameProjection ha h (m k) =
      phi (mCupFrameCanonicalMark ha h k))
    (hhead : m 0 * (freeTwoRankGen (coreRank h) 0)⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 2) :
    mRelWord alpha m * (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 :=
  mCupRelWord_error_mem_three ha m (freeTwoRankGen (coreRank h)) hhead
    (hcup.reducedRows_of_projection m hproj)

/-- The same composite with the fixed-`T` head hypothesis in place of the
mod-two one: a lift preserving the full frame cup form and fixing the composite
letter `T = A * C^(2^(alpha-1))` has its actual M relator error in
lambda-three. -/
theorem mCupRelWord_error_mem_three_of_frame_fixedT {alpha h : ℕ} {ha : 2 ≤ alpha}
    {phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)}
    (hcup : MCupFrameCupIsometry ha phi)
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hproj : ∀ k, mCupFreeFrameProjection ha h (m k) =
      phi (mCupFrameCanonicalMark ha h k))
    (hT : m 0 * m 2 ^ 2 ^ (alpha - 1) =
      freeTwoRankGen (coreRank h) 0 *
        freeTwoRankGen (coreRank h) 2 ^ 2 ^ (alpha - 1)) :
    mRelWord alpha m * (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 :=
  mCupRelWord_error_mem_three_of_fixed_T ha m (freeTwoRankGen (coreRank h)) hT
    (hcup.reducedRows_of_projection m hproj)

/-! ## The converse ingredient -/

/-- **T3.** Any continuous automorphism of the actual core whose frame action is
`phi` makes `phi` a cup isometry. This is the converse half of the eventual
iff: it needs no matrix, and it is proved through `dmObs` and uniqueness of the
one-dimensional degree-two obstruction, not through a coordinate computation. -/
theorem mCupFrameCupIsometry_of_aut {alpha h : ℕ} (ha : 2 ≤ alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hphi : ∀ i, phi (mCupFrameCanonicalMark ha h i) =
      mCupFrameOfDM ha h (Psi (dmGen alpha h i))) :
    MCupFrameCupIsometry ha phi := by
  intro c d
  have hkey := GQ2.Dyadic.Instances.M0C0PivotAutomorphism.evenCupForm_comp_dm_aut
    (alpha := alpha) (h := h) ha Psi (c.comp (mCupFrameOfDM ha h))
    (d.comp (mCupFrameOfDM ha h))
  have hl (e : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)))
      (i : Fin (coreRank h)) :
      toAdd (((e.comp (mCupFrameOfDM ha h)).comp (autHom Psi)) (dmGen alpha h i)) =
        toAdd (e (phi (mCupFrameCanonicalMark ha h i))) :=
    congrArg (fun z => toAdd (e z)) (hphi i).symm
  have hr (e : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)))
      (i : Fin (coreRank h)) :
      toAdd ((e.comp (mCupFrameOfDM ha h)) (dmGen alpha h i)) =
        toAdd (e (mCupFrameCanonicalMark ha h i)) := rfl
  simpa only [hl, hr] using hkey

#print axioms mCupOneLe
#print axioms mCupFrameOfDM
#print axioms mCupFrameCanonicalMark
#print axioms mCupFrameCanonicalMark_eq
#print axioms MCupFrameCupIsometry
#print axioms mCupFrameModTwoCoordinate
#print axioms mCupFrameModTwoCoordinate_canonicalMark
#print axioms mCupFreeMProjection
#print axioms mCupFreeMProjection_gen
#print axioms mCupFreeFrameProjection
#print axioms mCupFreeFrameProjection_gen
#print axioms mCupFrameModTwoCoordinate_projection
#print axioms MCupFrameCupIsometry.reducedRows_of_projection
#print axioms mCupRelWord_error_mem_three_of_frame
#print axioms mCupRelWord_error_mem_three_of_frame_fixedT
#print axioms mCupFrameCupIsometry_of_aut

end
end GQ2.Dyadic.MarkedCore
