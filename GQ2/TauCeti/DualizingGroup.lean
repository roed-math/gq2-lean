/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import GQ2.TateDuality
public import GQ2.TauCeti.GaloisDict

@[expose] public section

/-!
# B6, part 1: a local dualizing group is `G_K` for a finite `K/ℚ₂`, and the `μₙ` seam

Ticket B6 of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`, recon memo
`docs/orchestration/tauceti-t2-recon.md` §B6).  Everything lives in `GQ2.TauCetiBridge`.

gq2's local Tate duality `GQ2.LiteratureInputs.tateDualityAt` is stated for an abstract
topological group `G` with `hloc : GQ2.IsLocalDualizingGroup G n`, i.e. an open embedding
`ι : G →* G_ℚ₂` compatible with the action on `μₙ = GQ2.MuN n`.  Tau Ceti's duality theorem is
stated for `Field.absoluteGaloisGroup K` of a nonarchimedean local field `K`, with coefficients
`μₙ(Kˢᵉᵖ) = (TauCeti.ClassFieldTheory.muNRep n K).V`.  This file supplies the two translations
that do not involve cohomology:

* **The group** (`section Reconstruction`).  From `ι` and `hι : IsOpenEmbedding ι`, Krull's
  correspondence (A1, `GQ2/TauCeti/GaloisDict.lean`) gives the finite field
  `dualizingField ι = fixedField ι.range` with `fixingSubgroup = ι.range`, and
  `dualizingEquiv ι hι : G ≃ₜ* Field.absoluteGaloisGroup (dualizingField ι)` with
  `absoluteGaloisGroupExtend ℚ₂ K (sepEmb K) (dualizingEquiv ι hι g) = ι g`
  (`absoluteGaloisGroupExtend_dualizingEquiv`).
* **The coefficients** (`section MuSeam`).  For any `k : IntermediateField ℚ_[2] ℚ̄₂`,
  `muNEquivKummerCoeff n k : GQ2.MuN n ≃+ TauCeti.KummerCoeff k n` is A1's `sepClosureEquiv k`
  restricted to `n`-th roots of unity, and `muNEquiv n k : GQ2.MuN n ≃+ (muNRep n k).V`
  continues through Tau Ceti's `kummerCoeffEquivMuNRep`.  They are equivariant for
  `h : Field.absoluteGaloisGroup k` acting on `ℚ̄₂` through `absoluteGaloisGroupExtend`
  (`muNEquivKummerCoeff_smul`, `muNEquiv_smul`), hence, for a dualizing group, for `G` acting on
  `GQ2.MuN n` through `hloc` (`muNEquiv_dualizingEquiv_smul`).

`GQ2/TauCeti/B6.lean` adds the cohomological transports and the duality bundle itself.

Tau Ceti names are written fully qualified; nothing here is a global instance on `↥k`.
-/

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ### From an open embedding `ι : G →* G_ℚ₂` to a finite `K/ℚ₂` and `G ≃ₜ* G_K` -/

section Reconstruction

variable {G : Type} [Group G] [TopologicalSpace G] (ι : G →* GQ2.AbsGalQ2)
  (hι : Topology.IsOpenEmbedding ι)

include hι in
/-- The image of an open embedding of groups is an open subgroup. -/
theorem isOpen_range_of_isOpenEmbedding : IsOpen (ι.range : Set GQ2.AbsGalQ2) := by
  rw [MonoidHom.coe_range]
  exact hι.isOpen_range

/-- **The dualizing field** of `ι : G →* G_ℚ₂`: the fixed field of its image.  For an open
embedding it is finite over `ℚ₂` and `ι` identifies `G` with its absolute Galois group. -/
def dualizingField : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.fixedField ι.range

include hι in
/-- Krull: the fixing subgroup of the dualizing field is the image of `ι`. -/
theorem fixingSubgroup_dualizingField : (dualizingField ι).fixingSubgroup = ι.range :=
  fixingSubgroup_fixedField_of_isOpen ι.range (isOpen_range_of_isOpenEmbedding ι hι)

include hι in
/-- The dualizing field of an open embedding is finite over `ℚ₂`. -/
theorem finiteDimensional_dualizingField : FiniteDimensional ℚ_[2] (dualizingField ι) :=
  finiteDimensional_fixedField_of_isOpen ι.range (isOpen_range_of_isOpenEmbedding ι hι)

include hι in
/-- The degree of the dualizing field is the index of the image of `ι`. -/
theorem finrank_dualizingField : Module.finrank ℚ_[2] (dualizingField ι) = ι.range.index :=
  finrank_fixedField_of_isOpen ι.range (isOpen_range_of_isOpenEmbedding ι hι)

/-- **`G` is the absolute Galois group of its dualizing field**: `ι` onto its range, followed
by A1's `absGalFixedFieldEquiv`. -/
def dualizingEquiv : G ≃ₜ* Field.absoluteGaloisGroup (dualizingField ι) :=
  ((⟨ι, hι.continuous⟩ : G →ₜ* GQ2.AbsGalQ2).equivRangeOfIsEmbedding hι.isEmbedding).trans
    (absGalFixedFieldEquiv ι.range (isOpen_range_of_isOpenEmbedding ι hι)).symm

/-- `dualizingEquiv ι hι g`, read back in `G_ℚ₂` through Tau Ceti's `absoluteGaloisGroupExtend`,
is `ι g`. -/
theorem absoluteGaloisGroupExtend_dualizingEquiv (g : G) :
    haveI := finiteDimensional_dualizingField ι hι
    TauCeti.absoluteGaloisGroupExtend ℚ_[2] (dualizingField ι) (sepEmb (dualizingField ι))
      (dualizingEquiv ι hι g) = ι g := by
  have := finiteDimensional_dualizingField ι hι
  refine (coe_absGalFixedFieldEquiv_apply ι.range (isOpen_range_of_isOpenEmbedding ι hι)
    (dualizingEquiv ι hι g)).symm.trans ?_
  -- `dualizingEquiv ι hι g` is `(absGalFixedFieldEquiv …).symm (equivRange g)` by definition
  exact (congrArg Subtype.val ((absGalFixedFieldEquiv ι.range
    (isOpen_range_of_isOpenEmbedding ι hι)).apply_symm_apply _)).trans
    (congrArg Subtype.val (ContinuousMonoidHom.equivRangeOfIsEmbedding_apply _ hι.isEmbedding g))

/-- The inverse: `ι ((dualizingEquiv ι hι).symm h)` is `h` read in `G_ℚ₂`. -/
theorem apply_dualizingEquiv_symm (h : Field.absoluteGaloisGroup (dualizingField ι)) :
    haveI := finiteDimensional_dualizingField ι hι
    ι ((dualizingEquiv ι hι).symm h) =
      TauCeti.absoluteGaloisGroupExtend ℚ_[2] (dualizingField ι) (sepEmb (dualizingField ι)) h := by
  have := finiteDimensional_dualizingField ι hι
  rw [← absoluteGaloisGroupExtend_dualizingEquiv ι hι, ContinuousMulEquiv.apply_symm_apply]

end Reconstruction

/-! ### The `μₙ` seam: `μₙ(ℚ̄₂) ≃+ μₙ(kˢᵉᵖ) ≃+ (muNRep n k).V` -/

section MuSeam

variable (n : ℕ) (k : IntermediateField ℚ_[2] ℚ̄₂)

variable [NeZero n] in
/-- `μₙ(ℚ̄₂)` is discrete (a finite subset of the `T₁` space `ℚ̄₂`; finiteness needs `n ≠ 0`).
Named so that heavy files can make it a local instance instead of searching for it (memo,
cross-cutting finding 2). -/
theorem discreteTopology_muN : DiscreteTopology (GQ2.MuN n) := inferInstance

/-- `μₙ(ℚ̄₂)` is a topological additive group (a subgroup of the units of `ℚ̄₂`); named for the
same reason as `discreteTopology_muN`. -/
theorem isTopologicalAddGroup_muN : IsTopologicalAddGroup (GQ2.MuN n) := inferInstance

/-- **`μₙ(ℚ̄₂)` is `μₙ(kˢᵉᵖ)`**, through A1's `sepClosureEquiv k : kˢᵉᵖ ≃ₐ[k] ℚ̄₂`. -/
def muNEquivKummerCoeff : GQ2.MuN n ≃+ TauCeti.KummerCoeff k n :=
  MulEquiv.toAdditive ((sepClosureEquiv k).symm.toRingEquiv.toMulEquiv.restrictRootsOfUnity n)

@[simp] theorem coe_toMul_muNEquivKummerCoeff (x : GQ2.MuN n) :
    (((muNEquivKummerCoeff n k x).toMul : (SeparableClosure k)ˣ) : SeparableClosure k) =
      (sepClosureEquiv k).symm ((x.toMul : ℚ̄₂ˣ) : ℚ̄₂) := rfl

@[simp] theorem coe_toMul_muNEquivKummerCoeff_symm (y : TauCeti.KummerCoeff k n) :
    ((((muNEquivKummerCoeff n k).symm y).toMul : ℚ̄₂ˣ) : ℚ̄₂) =
      sepClosureEquiv k ((y.toMul : (SeparableClosure k)ˣ) : SeparableClosure k) := rfl

/-- **`μₙ(ℚ̄₂)` is the carrier of Tau Ceti's coefficient object `muNRep n k`.** -/
def muNEquiv : GQ2.MuN n ≃+ (TauCeti.ClassFieldTheory.muNRep n k).V :=
  (muNEquivKummerCoeff n k).trans (TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep n k)

theorem muNEquiv_apply (x : GQ2.MuN n) :
    muNEquiv n k x =
      TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep n k (muNEquivKummerCoeff n k x) := rfl

variable [FiniteDimensional ℚ_[2] k]

/-- `h : G_k` acts on `kˢᵉᵖ` (through Tau Ceti's `absoluteGaloisGroupRestrictEquiv`) as its image
`σ` in `G_ℚ₂` acts on `ℚ̄₂`, under `sepClosureEquiv k`.  (`σ` is quantified separately, at the
automorphism type `GQ2.Kummer.GaloisGroup ℚ₂` of `ℚ̄₂`, because `Field.absoluteGaloisGroup ℚ₂` is
that type by definition but not reducibly, so its elements are not `FunLike`.) -/
theorem sepClosureEquiv_absoluteGaloisGroupRestrictEquiv_apply (h : Field.absoluteGaloisGroup k)
    (σ : GQ2.Kummer.GaloisGroup ℚ_[2])
    (hσ : TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k) h = σ) (x : SeparableClosure k) :
    sepClosureEquiv k (TauCeti.absoluteGaloisGroupRestrictEquiv k h x) = σ (sepClosureEquiv k x) := by
  have := sepClosureEquiv_fixingEquivAbsGal_apply k (absGalEquivFixing k h) x
  rwa [fixingEquivAbsGal_apply, ContinuousMulEquiv.symm_apply_apply,
    coe_absGalEquivFixing_apply, hσ] at this

/-- The inverse form of `sepClosureEquiv_absoluteGaloisGroupRestrictEquiv_apply`. -/
theorem absoluteGaloisGroupRestrictEquiv_apply_sepClosureEquiv_symm
    (h : Field.absoluteGaloisGroup k) (σ : GQ2.Kummer.GaloisGroup ℚ_[2])
    (hσ : TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k) h = σ) (y : ℚ̄₂) :
    TauCeti.absoluteGaloisGroupRestrictEquiv k h ((sepClosureEquiv k).symm y) =
      (sepClosureEquiv k).symm (σ y) := by
  apply (sepClosureEquiv k).injective
  rw [sepClosureEquiv_absoluteGaloisGroupRestrictEquiv_apply k h σ hσ, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-- **`muNEquivKummerCoeff` is equivariant**: `h : G_k` acting on `μₙ(ℚ̄₂)` through its image
`σ` in `G_ℚ₂` corresponds to its restriction to `kˢᵉᵖ` acting on `μₙ(kˢᵉᵖ)`. -/
theorem muNEquivKummerCoeff_smul (h : Field.absoluteGaloisGroup k)
    (σ : GQ2.Kummer.GaloisGroup ℚ_[2])
    (hσ : TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k) h = σ) (x : GQ2.MuN n) :
    muNEquivKummerCoeff n k (σ • x) =
      TauCeti.absoluteGaloisGroupRestrictEquiv k h • muNEquivKummerCoeff n k x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  -- the gq2 action on `μₙ(ℚ̄₂)` is the field automorphism on the underlying element
  have hσx : ((((σ • x : GQ2.MuN n).toMul : rootsOfUnity n ℚ̄₂) : ℚ̄₂ˣ) : ℚ̄₂) =
      σ (((x.toMul : rootsOfUnity n ℚ̄₂) : ℚ̄₂ˣ) : ℚ̄₂) :=
    GQ2.val_smul_units σ _
  rw [Additive.toMul_smul, TauCeti.rootsOfUnity.coe_smul, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_ofClass, coe_toMul_muNEquivKummerCoeff, coe_toMul_muNEquivKummerCoeff,
    absoluteGaloisGroupRestrictEquiv_apply_sepClosureEquiv_symm k h σ hσ, hσx]

/-- **`muNEquiv` is equivariant**: `h : G_k` acting on `μₙ(ℚ̄₂)` through its image `σ` in `G_ℚ₂`
corresponds to the operator `(muNRep n k).ρ h`. -/
theorem muNEquiv_smul (h : Field.absoluteGaloisGroup k) (σ : GQ2.Kummer.GaloisGroup ℚ_[2])
    (hσ : TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k) h = σ) (x : GQ2.MuN n) :
    muNEquiv n k (σ • x) = (TauCeti.ClassFieldTheory.muNRep n k).ρ h (muNEquiv n k x) := by
  rw [muNEquiv_apply, muNEquiv_apply, muNEquivKummerCoeff_smul n k h σ hσ,
    TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep_smul]

end MuSeam

/-! ### The seam for a local dualizing group -/

section Dualizing

variable {G : Type} [Group G] [TopologicalSpace G] (n : ℕ) [DistribMulAction G (GQ2.MuN n)]
  (ι : G →* GQ2.AbsGalQ2) (hι : Topology.IsOpenEmbedding ι)
  (hμ : ∀ (g : G) (x : GQ2.MuN n), g • x = ι g • x)

include hμ in
/-- For a dualizing group (`hloc`'s compatibility `g • x = ι g • x`), `muNEquiv` carries the
action of `g : G` on `μₙ(ℚ̄₂)` to the operator of `dualizingEquiv ι hι g` on `muNRep n K`. -/
theorem muNEquiv_dualizingEquiv_smul (g : G) (x : GQ2.MuN n) :
    haveI := finiteDimensional_dualizingField ι hι
    muNEquiv n (dualizingField ι) (g • x) =
      (TauCeti.ClassFieldTheory.muNRep n (dualizingField ι)).ρ (dualizingEquiv ι hι g)
        (muNEquiv n (dualizingField ι) x) := by
  have := finiteDimensional_dualizingField ι hι
  rw [hμ]
  exact muNEquiv_smul n (dualizingField ι) (dualizingEquiv ι hι g) (ι g)
    (absoluteGaloisGroupExtend_dualizingEquiv ι hι g) x

include hμ in
/-- `muNEquiv_dualizingEquiv_smul` for `h : G_K` acting on `μₙ(ℚ̄₂)` through
`(dualizingEquiv ι hι).symm`: the compatibility hypothesis of Tau Ceti's `explicitMap{1,2}Equiv`
along `(dualizingEquiv ι hι).symm` and `muNEquiv`. -/
theorem muNEquiv_dualizingEquiv_symm_smul (h : Field.absoluteGaloisGroup (dualizingField ι))
    (x : GQ2.MuN n) :
    haveI := finiteDimensional_dualizingField ι hι
    muNEquiv n (dualizingField ι) ((dualizingEquiv ι hι).symm h • x) =
      (TauCeti.ClassFieldTheory.muNRep n (dualizingField ι)).ρ h
        (muNEquiv n (dualizingField ι) x) := by
  have := finiteDimensional_dualizingField ι hι
  rw [hμ]
  exact muNEquiv_smul n (dualizingField ι) h _ (apply_dualizingEquiv_symm ι hι h).symm x

end Dualizing

end GQ2.TauCetiBridge
