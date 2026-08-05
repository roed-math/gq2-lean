/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.DemushkinEpimorphismRigidity
import GQ2.Dyadic.MaxProTwoCohomology
import GQ2.Dyadic.OrientationCorrection

/-!
# The even-degree forward route (P10 spike skeleton)

This file is the Prop-level interface layer for route **(A)** of the P10 spike: cloning the
odd-degree forward-generator + equal-rank Demushkin-rigidity architecture to the even branch
rows `N` (cores `DN α h`) and `M` (cores `DM α h`), instead of proving the never-proved
`NLabHypothesis` / `MLabHypothesis`.

## Why the forward route, in one paragraph

`demushkinEpimorphism_bijective` (`GQ2/Dyadic/Count/DemushkinEpimorphismRigidity.lean:873`)
consumes exactly *surjectivity*, `IsDemushkin 2` at both ends, *equal* `demushkinRank`, and
positivity of that rank.  It consumes **no** `demushkinQ`, **no** orientation image, and **no**
canonicity predicate.  Consequently the even rows, routed forward, need none of

* `demushkinQ (maxProPQuotient 2 (GalK K)) = 2` (still unproved at every parity),
* `MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α` / `= imChiN α`,
* an abstract canonical-orientation predicate on a general profinite group,
* Labute's even-rank classification theorem itself.

Orientation is moreover *free* on this route: the forward map is built from a generator tuple
whose cyclotomic values are prescribed, so `orientedEquivN_of_datum` / `orientedEquivM_of_datum`
(`GQ2/Dyadic/OrientationCorrection.lean:468`, `:456`) apply directly.  This dissolves the
recorded interface finding that `NLabHypothesis`/`MLabHypothesis` conclude only an *unoriented*
`Nonempty (ContinuousMulEquiv …)` (`docs/dyadic/followup/labute-interface-status.md`).

## What is proved here and what is not

Proved: the whole rigidity plumbing, uniformly in the branch, given the two *model-side* facts
as hypotheses; and the even-degree rank identity
`[K : ℚ₂] = 2 + 2h ⟹ demushkinRank = coreRank h`.

Not proved, and deliberately carried as named hypotheses or `Prop`s, never as an admitted goal:

* `IsDemushkin 2 (DN α h : Type)` and `IsDemushkin 2 (DM α h : Type)`, with their rank
  identities.  These are the even analogues of `isDemushkin_DSq` / `demushkinRank_DSq`
  (`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteDegreeThree.lean:297`,
  `…LabuteElementaryH2.lean:683`).  Both even cores have the *same* relator Gram
  `mGram = nGram = [[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]`
  (`GQ2/Dyadic/MarkedCore/Variance.lean:107`, a `rfl`), so one nondegeneracy argument serves
  both.  Note the even head `[[1,1],[1,0]]` has *no* dual-basis permutation: its inverse Gram is
  `[[0,1],[1,1]]`, so the odd `sqInitialPartner : Equiv.Perm` must become a dual-*vector* map.
* The forward-generator supply itself (`Even…ForwardGeneratorSupply` below), which is the even
  analogue of the odd level-three seed plus stage climb.

## Statements deliberately left in comments

```text
-- EV-1e  theorem isDemushkin_DN (α h : ℕ) (hα : 2 ≤ α) : IsDemushkin 2 (DN α h : Type)
-- EV-1e  theorem isDemushkin_DM (α h : ℕ) (hα : 2 ≤ α) : IsDemushkin 2 (DM α h : Type)
-- EV-1b  theorem demushkinRank_DN (α h : ℕ) : demushkinRank 2 (DN α h : Type) = coreRank h
-- EV-1b  theorem demushkinRank_DM (α h : ℕ) : demushkinRank 2 (DM α h : Type) = coreRank h
-- EV-3c  theorem evenDegreeNCyclotomicFrattiniFrameSupply_holds : … (FD2 head + κ-slot pin)
-- EV-4a  theorem evenDegree_sharpCharacterFiltrationExact :
--            SharpCharacterFiltrationExact (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))
--          -- NOT via `of_surjective`: `chiCycKTwo` is *not* surjective in even degree.
```

The `α ≥ 2` hypotheses above are not decoration: at `α = 1` the `N` relator exponent is
`2 + 2 = 4`, whose mod-2 quadratic initial form vanishes, and the core is not Demushkin.
-/

namespace GQ2.Dyadic.EvenForward

noncomputable section

open GQ2 MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Forward-generator data at the two even cores -/

section GeneralTarget

variable {α h : ℕ} {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}

local instance evenScalarActionG : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
local instance evenContinuousScalarG : ContinuousSMul G (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul G
local instance evenScalarActionDN (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _
local instance evenContinuousScalarDN (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _
local instance evenScalarActionDM (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _
local instance evenContinuousScalarDM (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Generator-level data for the forward epimorphism out of the `N_α` core.  The four core rows
are the frozen constructor table `(x₀, x₁, σ, x₂) ↦ (1, −(1+2^α)⁻¹, 1, 1)` of `chiN`
(`GQ2/Dyadic/MarkedCore/Cores.lean:1078`); the handle rows are trivial. -/
structure NForwardGeneratorData (α h : ℕ)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) where
  /-- The chosen rank-`coreRank h` tuple in the target. -/
  generators : Fin (coreRank h) → G
  /-- The `N_α` relator dies at the chosen tuple. -/
  relation : nRelWord α generators = 1
  /-- The tuple topologically generates the target. -/
  topGen : (Subgroup.closure (Set.range generators)).topologicalClosure = ⊤
  /-- Constructor row `x₀`. -/
  x0 : chiG (generators 0) = 1
  /-- Constructor row `x₁`, the only nontrivial `N` value. -/
  x1 : chiG (generators 1) = nUnit α
  /-- Constructor row `σ`. -/
  sigma : chiG (generators 2) = 1
  /-- Constructor row `x₂`. -/
  x2 : chiG (generators 3) = 1
  /-- The `U`-handle rows. -/
  handleU : ∀ j : Fin h, chiG (generators (handleIdxU j)) = 1
  /-- The `V`-handle rows. -/
  handleV : ∀ j : Fin h, chiG (generators (handleIdxV j)) = 1

/-- Generator-level data for the forward epimorphism out of the `M_α` core, at the frozen
constructor table `(A, B, C₀, D) ↦ (1, −1, 1, (1−2^α)⁻¹)` of `chiM`. -/
structure MForwardGeneratorData (α h : ℕ)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) where
  /-- The chosen rank-`coreRank h` tuple in the target. -/
  generators : Fin (coreRank h) → G
  /-- The `M_α` relator dies at the chosen tuple. -/
  relation : mRelWord α generators = 1
  /-- The tuple topologically generates the target. -/
  topGen : (Subgroup.closure (Set.range generators)).topologicalClosure = ⊤
  /-- Constructor row `A`. -/
  a : chiG (generators 0) = 1
  /-- Constructor row `B`; this row is why `M` needs `−1 ∈ im χ_cyc`. -/
  b : chiG (generators 1) = -1
  /-- Constructor row `C₀`. -/
  c : chiG (generators 2) = 1
  /-- Constructor row `D`. -/
  d : chiG (generators 3) = mUnit α
  /-- The `U`-handle rows. -/
  handleU : ∀ j : Fin h, chiG (generators (handleIdxU j)) = 1
  /-- The `V`-handle rows. -/
  handleV : ∀ j : Fin h, chiG (generators (handleIdxV j)) = 1

namespace NForwardGeneratorData

/-- The homomorphism classified by a relator-killing generator tuple. -/
def forward (D : NForwardGeneratorData α h chiG) (hpro : IsProP 2 G) :
    ContinuousMonoidHom (DN α h : Type) G :=
  nLiftHom α h hpro D.generators D.relation

@[simp] theorem forward_gen (D : NForwardGeneratorData α h chiG) (hpro : IsProP 2 G)
    (i : Fin (coreRank h)) : D.forward hpro (dnGen α h i) = D.generators i :=
  nLiftHom_gen α h hpro D.generators D.relation i

/-- Topological generation of the chosen tuple makes the classified map surjective. -/
theorem forward_surjective (D : NForwardGeneratorData α h chiG) (hpro : IsProP 2 G) :
    Function.Surjective (D.forward hpro) := by
  have hclosed : IsClosed ((D.forward hpro).toMonoidHom.range : Set G) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (D.forward hpro).continuous_toFun).isClosed
  have hgen : Subgroup.closure (Set.range D.generators) ≤
      (D.forward hpro).toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨dnGen α h i, D.forward_gen hpro i⟩
  have htop : (Subgroup.closure (Set.range D.generators)).topologicalClosure ≤
      (D.forward hpro).toMonoidHom.range :=
    Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [D.topGen] at htop
  intro y
  exact htop (Subgroup.mem_top y)

end NForwardGeneratorData

namespace MForwardGeneratorData

/-- The homomorphism classified by a relator-killing generator tuple. -/
def forward (D : MForwardGeneratorData α h chiG) (hpro : IsProP 2 G) :
    ContinuousMonoidHom (DM α h : Type) G :=
  mLiftHom α h hpro D.generators D.relation

@[simp] theorem forward_gen (D : MForwardGeneratorData α h chiG) (hpro : IsProP 2 G)
    (i : Fin (coreRank h)) : D.forward hpro (dmGen α h i) = D.generators i :=
  mLiftHom_gen α h hpro D.generators D.relation i

/-- Topological generation of the chosen tuple makes the classified map surjective. -/
theorem forward_surjective (D : MForwardGeneratorData α h chiG) (hpro : IsProP 2 G) :
    Function.Surjective (D.forward hpro) := by
  have hclosed : IsClosed ((D.forward hpro).toMonoidHom.range : Set G) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (D.forward hpro).continuous_toFun).isClosed
  have hgen : Subgroup.closure (Set.range D.generators) ≤
      (D.forward hpro).toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨dmGen α h i, D.forward_gen hpro i⟩
  have htop : (Subgroup.closure (Set.range D.generators)).topologicalClosure ≤
      (D.forward hpro).toMonoidHom.range :=
    Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [D.topGen] at htop
  intro y
  exact htop (Subgroup.mem_top y)

end MForwardGeneratorData

/-! ## §2 The two model-side obligations

These are the only even-core facts the rigidity step needs.  They are the even analogues of
`isDemushkin_DSq` and `demushkinRank_DSq`, and they are stated here as `Prop`s so that every
downstream statement in this file names them explicitly rather than assuming them. -/

/-- The model-side package for the `N_α` core: Demushkin, at the literal marking rank. -/
def NModelDemushkin (α h : ℕ) : Prop :=
  IsDemushkin 2 (DN α h : Type) ∧ demushkinRank 2 (DN α h : Type) = coreRank h

/-- The model-side package for the `M_α` core. -/
def MModelDemushkin (α h : ℕ) : Prop :=
  IsDemushkin 2 (DM α h : Type) ∧ demushkinRank 2 (DM α h : Type) = coreRank h

/-! ## §3 Rigidity: the forward map is an oriented equivalence -/

namespace NForwardGeneratorData

/-- **Even-row rigidity bypass at the `N` core.**  A forward presentation map is bijective as
soon as the target is Demushkin of the literal even rank.  No `demushkinQ`, no orientation
image, no canonicity predicate, and no classification theorem occurs. -/
theorem forward_bijective (D : NForwardGeneratorData α h chiG)
    (hmodel : NModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) :
    Function.Bijective (D.forward hD.isProP) := by
  apply demushkinEpimorphism_bijective
    (D.forward hD.isProP) (D.forward_surjective hD.isProP) hmodel.1 hD
  · rw [hmodel.2, hrank]
  · rw [hmodel.2]
    simp only [coreRank]
    omega

/-- The bijective forward map, bundled as a topological group equivalence. -/
def forwardContinuousMulEquiv (D : NForwardGeneratorData α h chiG)
    (hmodel : NModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) :
    ContinuousMulEquiv (DN α h : Type) G :=
  continuousMulEquivOfBijective (D.forward hD.isProP) (D.forward_bijective hmodel hD hrank)

@[simp] theorem forwardContinuousMulEquiv_apply (D : NForwardGeneratorData α h chiG)
    (hmodel : NModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) (x : DN α h) :
    D.forwardContinuousMulEquiv hmodel hD hrank x = D.forward hD.isProP x := rfl

/-- **Orientation is free on the forward route.**  The four constructor rows stored in `D` are
exactly the `N` Labute orientation datum, so the bundled equivalence is oriented without any
canonicity predicate on `G`. -/
def orientedEquiv (D : NForwardGeneratorData α h chiG) (hα : 1 ≤ α)
    (hmodel : NModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) :
    OrientedContinuousMulEquiv (chiN α h) chiG := by
  refine orientedEquivN_of_datum hα chiG (D.forwardContinuousMulEquiv hmodel hD hrank) ?_ ?_ ?_
  · have h0 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dnX0 α h)) = 1 := by
      change chiG (D.forward hD.isProP (dnGen α h 0)) = 1
      rw [D.forward_gen]
      exact D.x0
    have h1 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dnX1 α h)) = nUnit α := by
      change chiG (D.forward hD.isProP (dnGen α h 1)) = nUnit α
      rw [D.forward_gen]
      exact D.x1
    have h2 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dnSigma α h)) = 1 := by
      change chiG (D.forward hD.isProP (dnGen α h 2)) = 1
      rw [D.forward_gen]
      exact D.sigma
    have h3 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dnX2 α h)) = 1 := by
      change chiG (D.forward hD.isProP (dnGen α h 3)) = 1
      rw [D.forward_gen]
      exact D.x2
    rw [h0, h1, h2, h3]
    exact isLabuteOrientationDatumN_nUnit hα
  · intro j
    change chiG (D.forward hD.isProP (dnGen α h (handleIdxU j))) = 1
    rw [D.forward_gen]
    exact D.handleU j
  · intro j
    change chiG (D.forward hD.isProP (dnGen α h (handleIdxV j))) = 1
    rw [D.forward_gen]
    exact D.handleV j

end NForwardGeneratorData

namespace MForwardGeneratorData

/-- **Even-row rigidity bypass at the `M` core.** -/
theorem forward_bijective (D : MForwardGeneratorData α h chiG)
    (hmodel : MModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) :
    Function.Bijective (D.forward hD.isProP) := by
  apply demushkinEpimorphism_bijective
    (D.forward hD.isProP) (D.forward_surjective hD.isProP) hmodel.1 hD
  · rw [hmodel.2, hrank]
  · rw [hmodel.2]
    simp only [coreRank]
    omega

/-- The bijective forward map, bundled as a topological group equivalence. -/
def forwardContinuousMulEquiv (D : MForwardGeneratorData α h chiG)
    (hmodel : MModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) :
    ContinuousMulEquiv (DM α h : Type) G :=
  continuousMulEquivOfBijective (D.forward hD.isProP) (D.forward_bijective hmodel hD hrank)

@[simp] theorem forwardContinuousMulEquiv_apply (D : MForwardGeneratorData α h chiG)
    (hmodel : MModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) (x : DM α h) :
    D.forwardContinuousMulEquiv hmodel hD hrank x = D.forward hD.isProP x := rfl

/-- Oriented form at the `M` core: the constructor rows are the `M` Labute orientation datum. -/
def orientedEquiv (D : MForwardGeneratorData α h chiG) (hα : 1 ≤ α)
    (hmodel : MModelDemushkin α h) (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = coreRank h) :
    OrientedContinuousMulEquiv (chiM α h) chiG := by
  refine orientedEquivM_of_datum hα chiG (D.forwardContinuousMulEquiv hmodel hD hrank) ?_ ?_ ?_
  · have h0 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dmA α h)) = 1 := by
      change chiG (D.forward hD.isProP (dmGen α h 0)) = 1
      rw [D.forward_gen]
      exact D.a
    have h1 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dmB α h)) = -1 := by
      change chiG (D.forward hD.isProP (dmGen α h 1)) = -1
      rw [D.forward_gen]
      exact D.b
    have h2 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dmC α h)) = 1 := by
      change chiG (D.forward hD.isProP (dmGen α h 2)) = 1
      rw [D.forward_gen]
      exact D.c
    have h3 : chiG (D.forwardContinuousMulEquiv hmodel hD hrank (dmD α h)) = mUnit α := by
      change chiG (D.forward hD.isProP (dmGen α h 3)) = mUnit α
      rw [D.forward_gen]
      exact D.d
    rw [h0, h1, h2, h3]
    exact isLabuteOrientationDatumM_mUnit hα
  · intro j
    change chiG (D.forward hD.isProP (dmGen α h (handleIdxU j))) = 1
    rw [D.forward_gen]
    exact D.handleU j
  · intro j
    change chiG (D.forward hD.isProP (dmGen α h (handleIdxV j))) = 1
    rw [D.forward_gen]
    exact D.handleV j

end MForwardGeneratorData

end GeneralTarget

/-! ## §4 The even-degree field specialization

The only parity-dependent step in the whole rigidity chain is the rank identity.  Its odd form
is `demushkinRank_maxProTwoGalK_eq_sqRank_half_pred`
(`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldRigidity.lean:216`); here is the even form. -/

section EvenDegreeField

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenFieldScalarAction :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _
local instance evenFieldContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [T2Space (GalK K)] in
/-- For an even-degree dyadic field the literal even core rank equals the Demushkin rank of its
maximal pro-two Galois group.  This is the even twin of the odd `sqRank` identity: no `q`, no
image, no branch datum is involved. -/
theorem demushkinRank_maxProTwoGalK_eq_coreRank (h : ℕ)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h := by
  rw [demushkinRank_maxProTwoGalK (K := K), hev]
  simp only [coreRank]
  omega

omit [T2Space (GalK K)] in
/-- **The `N`-row even-degree capstone.**  A forward-generator package at the descended
cyclotomic character produces an oriented equivalence `D_N ≃ G_K(2)`, on exactly two unproved
inputs: the model-side Demushkin package and the package itself. -/
theorem nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData (α h : ℕ) (hα : 1 ≤ α)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (hmodel : NModelDemushkin α h)
    (hdata : Nonempty (NForwardGeneratorData α h (chiCycKTwo (K := K)))) :
    Nonempty (OrientedContinuousMulEquiv (chiN α h) (chiCycKTwo (K := K))) :=
  hdata.map fun D =>
    D.orientedEquiv hα hmodel (isDemushkin_maxProTwoGalK (K := K))
      (demushkinRank_maxProTwoGalK_eq_coreRank h hev)

omit [T2Space (GalK K)] in
/-- **The `M`-row even-degree capstone.** -/
theorem nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData (α h : ℕ) (hα : 1 ≤ α)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (hmodel : MModelDemushkin α h)
    (hdata : Nonempty (MForwardGeneratorData α h (chiCycKTwo (K := K)))) :
    Nonempty (OrientedContinuousMulEquiv (chiM α h) (chiCycKTwo (K := K))) :=
  hdata.map fun D =>
    D.orientedEquiv hα hmodel (isDemushkin_maxProTwoGalK (K := K))
      (demushkinRank_maxProTwoGalK_eq_coreRank h hev)

end EvenDegreeField

/-! ## §5 The uniform supplies, named

These are the even-row analogues of `OddDegreeGalKSqForwardGeneratorSupply`
(`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldVariableCoreRigidity.lean:33`).  They are the
targets of the even seed (`EV-3`) and the even stage climb (`EV-4`). -/

/-- Uniform even-degree `N` forward-generator supply at branch depth `α`. -/
def EvenDegreeGalKNForwardGeneratorSupply (α : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      Nonempty (NForwardGeneratorData α h (chiCycKTwo (K := K)))

/-- Uniform even-degree `M` forward-generator supply at branch depth `α`. -/
def EvenDegreeGalKMForwardGeneratorSupply (α : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      Nonempty (MForwardGeneratorData α h (chiCycKTwo (K := K)))

/-- The uniform `N` classification obtained from the two supplies.  Compare
`OddDegreeGalKSqOrientedForwardClassification`, which likewise carries no `demushkinQ`. -/
theorem orientedEquivN_of_supplies (α : ℕ) (hα : 1 ≤ α)
    (hmodel : ∀ h : ℕ, NModelDemushkin α h)
    (hsupply : EvenDegreeGalKNForwardGeneratorSupply α)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiN α h) (chiCycKTwo (K := K))) :=
  nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData α h hα hev (hmodel h)
    (hsupply K h hev)

/-- The uniform `M` classification obtained from the two supplies. -/
theorem orientedEquivM_of_supplies (α : ℕ) (hα : 1 ≤ α)
    (hmodel : ∀ h : ℕ, MModelDemushkin α h)
    (hsupply : EvenDegreeGalKMForwardGeneratorSupply α)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiM α h) (chiCycKTwo (K := K))) :=
  nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData α h hα hev (hmodel h)
    (hsupply K h hev)

end

end GQ2.Dyadic.EvenForward
