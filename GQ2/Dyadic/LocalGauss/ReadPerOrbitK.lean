/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.DeepPackage
import GQ2.Dyadic.LocalGauss.OrbitVanishK
import GQ2.Shapiro.Read

/-!
# The per-orbit Shapiro read over a general local source (LG4c, part 2)

`GQ2/Shapiro/Read.lean` §PerOrbit and §DeepCoordinate, retyped from `G_ℚ₂` to an arbitrary
topological group `Γ`.  The `ℚ₂` original is untouched (design memo `docs/dyadic/lg-design.md`
§2: clone, zero in-place edits).

## What actually needed retyping

`GQ2/Shapiro/Read.lean`'s first two sections (§Read, §Z1Layer) are stated over an **abstract `G`**
already — `shapiroCoord`, `shapiroPrim`, `shapiroCoord_mul`, `shapiroFun_shapiroCoord_apply`,
`shapiroFun_shapiroCoord_eq`, `shapiroCoord_mem_Z1` and the `Prelim` brick `graphPullback_comap`
are consumed **verbatim** here.  So are the whole of `GQ2/OrbitDecomp.lean` (block datums,
projections, orbit datums, equivariance) and `GQ2.SectionSix.lemma_6_15_{square,free,involution}`.
Only §PerOrbit (which fixes `G := G_ℚ₂`) and §DeepCoordinate (which speaks of
`SectionSix.deepPart` / `LocalKummer.phiRes`) are `AbsGalQ2`-typed, and only they are cloned:

* §1 the block-coordinate bricks and the shared `B²`-shift engine;
* §2 `hcoh_square_K`, `hcoh_free_K`, `hcoh_involution_K` — the Lemma-6.15 eq. (103)/(104)/(105)
  cohomologies at the block coordinates;
* §3 the deep coordinate: `phiResK_evalWK` and `shapiroCoord_mem_deepClassesAt`, phrased against
  LG4a's anchored `deepPartK` / `deepClassesAt` (`LocalGauss/DeepPackage.lean` §2–§3);
* §4 deepness transport along an equivariant coefficient map (`deepPartK_mapCoeff1`), the retype
  of `GQ2.ShapiroDeepness.deepPart_mapCoeff1` — the deepness half of the Lemma-6.14 transport.

## The degree-2 σ-twist trap (LG1 memo risk 6): verified inapplicable here

The memo flags that a Shapiro **section** at *nontrivial* coefficients must use the inverse word
`c ((wElt g x)⁻¹)`, and that `GQ2/Shapiro/Finiteness.lean`'s `sigmaFun` (`c (wElt g x)`) is
correct only because `𝔽₂`-inversion is trivial.  That trap does **not** reach this file, for two
independent reasons, both checked:

1. The corestriction layer this file consumes is *already in the inverse (τ) form*:
   `Corestriction.lWord U u γ = u.out⁻¹ * γ * (γ⁻¹ • u).out`, which is literally
   `(wElt γ u)⁻¹` for the same transversal (`wElt g x = (sect (g⁻¹ • x))⁻¹ * g⁻¹ * sect x`,
   `GQ2/Shapiro/Finiteness.lean` :179).  `shapiroFun`, `cor1Fun` and `cor2Fun` are all built from
   `lTrans`, hence carry the correct twist in degrees 1 **and** 2.
2. The coefficient module here is `RegRep N = (Γ ⧸ N) → 𝔽₂` with the *untwisted* left-regular
   action `(c • x) h = x (c⁻¹ * h)` (`GQ2/OrbitData.lean` :110) — the coinduced module of the
   **trivial** `𝔽₂`-module, where the `U`-twist acts trivially by construction.

So the retype below is a straight ambient swap; no section had to be re-derived.  The correction
the memo prescribes belongs to LG2a's `IndMod`, at genuinely nontrivial coefficients.

Axioms: `∅` beyond the standard three (the `ℚ₂` model's set) — everything here is finite group
theory plus the banked Lemma-6.15 ledger.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.Corestriction GQ2.SectionSix GQ2.ShapiroRead

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The `AlgEquiv`-flavoured spelling of `G_ℚ₂` (LG4a's anchoring convention; see
`LocalGauss/DeepPackage.lean` §1). -/
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

/-! ## §1 Block-coordinate bricks and the shared `B²`-shift engine

`GQ2/Shapiro/Read.lean` :190–:252 retyped.  Instance context as in the `ℚ₂` model: `RegRep N` is
a type synonym with no registered topology, so its topological instances and the `Γ`-action (the
`mk'`-pullback of the left-regular action) enter as instance arguments with the compatibility
hypothesis `hmk`; the assembly supplies them as `letI`s, for which `hmk` is `rfl`. -/

section PerOrbit

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable (N : Subgroup Γ) [N.Normal] [Finite (Γ ⧸ N)]
variable [TopologicalSpace (RegRep N)] [DiscreteTopology (RegRep N)] [Finite (RegRep N)]
  [DistribMulAction Γ (RegRep N)] [ContinuousSMul Γ (RegRep N)]
variable (hmk : ∀ (g : Γ) (y : RegRep N), g • y = QuotientGroup.mk' N g • y)

/-- `mk' N` as a continuous monoid hom (quotient topology). -/
private noncomputable def mkQK : ContinuousMonoidHom Γ (Γ ⧸ N) :=
  ⟨QuotientGroup.mk' N, continuous_quotient_mk'⟩

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [Finite (Γ ⧸ N)] [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
include hmk in
/-- The block coordinate of a `Z¹`-representative is an `mk'`-cocycle (raw form). -/
theorem block_cocycleK {K : ℕ} (b : ↥(Z1 Γ (Fin K → RegRep N))) (j : Fin K) :
    ∀ g h : Γ, b.1 (g * h) j = b.1 g j + QuotientGroup.mk' N g • b.1 h j := by
  intro g h
  rw [(mem_Z1_iff.mp b.2).2 g h]
  show b.1 g j + (g • b.1 h) j = b.1 g j + QuotientGroup.mk' N g • b.1 h j
  rw [Pi.smul_apply, hmk]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [Finite (Γ ⧸ N)] [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
/-- The base-coset evaluation of a block coordinate is continuous (`RegRep N` is discrete). -/
theorem block_continuousK {K : ℕ} (b : ↥(Z1 Γ (Fin K → RegRep N))) (j : Fin K) :
    Continuous fun g => b.1 g j (1 : Γ ⧸ N) :=
  (continuous_of_discreteTopology
    (f := fun F : Fin K → RegRep N => F j (1 : Γ ⧸ N))).comp (mem_Z1_iff.mp b.2).1

include hmk in
omit [Finite (Γ ⧸ N)] [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
/-- The shared `B²`-shift engine: replacing the `Z¹`-representative by its `δ⁰W₀`-shift does not
change the `H²ofFun` class of any equivariant graph pullback (LG2's
`GQ2.Dyadic.graphPullback_sub_mem_B2`). -/
private theorem H2ofFun_graphPullback_shiftK {K : ℕ} {qW : (Fin K → RegRep N) → ZMod 2}
    (dat : FactorSet (Γ ⧸ N) (Fin K → RegRep N))
    (hdat : IsEquivariantFactorSet qW dat) (hNo : IsOpen (N : Set Γ))
    (b : ↥(Z1 Γ (Fin K → RegRep N))) (W₀ : Fin K → RegRep N) :
    H2ofFun Γ (graphPullback dat (⇑(QuotientGroup.mk' N))
        (fun g => b.1 g + (g • W₀ - W₀)))
      = H2ofFun Γ (graphPullback dat (⇑(QuotientGroup.mk' N)) b.1) := by
  haveI : DiscreteTopology (Γ ⧸ N) := QuotientGroup.discreteTopology hNo
  have hρW : ∀ (g : Γ) (F : Fin K → RegRep N), g • F = (mkQK N) g • F :=
    fun g F => funext fun k => hmk g (F k)
  exact ShapiroLedger.H2ofFun_eq_of_sub_mem_B2
    (graphPullback_sub_mem_B2 dat hdat (mkQK N) hρW b W₀)

include hmk in
omit [Finite (Γ ⧸ N)] [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
/-- **The shared `hcoh` spine**: the `δ⁰W₀`-shift is invisible in `H²`, the block datum is the
definitional `comap` of the orbit datum along the equivariant projection `i`
(`ShapiroRead.graphPullback_comap`, ambient-free), and the projected shift is the Shapiro
target (`hblock`). -/
private theorem H2ofFun_graphPullback_comap_shiftK {K : ℕ} {W : Type*} [AddCommGroup W]
    [DistribMulAction (Γ ⧸ N) W] {qW : (Fin K → RegRep N) → ZMod 2}
    (dat : FactorSet (Γ ⧸ N) W) (i : (Fin K → RegRep N) →+ W)
    (hi : ∀ (c : Γ ⧸ N) (v : Fin K → RegRep N), i (c • v) = c • i v)
    (hdat : IsEquivariantFactorSet qW (dat.comap i)) (hNo : IsOpen (N : Set Γ))
    (b : ↥(Z1 Γ (Fin K → RegRep N))) (W₀ : Fin K → RegRep N) {target : Γ → W}
    (hblock : (fun g => i (b.1 g + (g • W₀ - W₀))) = target) :
    H2ofFun Γ (graphPullback (dat.comap i) (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun Γ (graphPullback dat (⇑(QuotientGroup.mk' N)) target) :=
  calc H2ofFun Γ (graphPullback (dat.comap i) (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun Γ (graphPullback (dat.comap i) (⇑(QuotientGroup.mk' N))
          (fun g => b.1 g + (g • W₀ - W₀))) :=
        (H2ofFun_graphPullback_shiftK N hmk (dat.comap i) hdat hNo b W₀).symm
    _ = H2ofFun Γ (graphPullback dat (⇑(QuotientGroup.mk' N))
          (fun g => i (b.1 g + (g • W₀ - W₀)))) :=
        congrArg (H2ofFun Γ)
          (graphPullback_comap dat i hi (⇑(QuotientGroup.mk' N))
            (fun g => b.1 g + (g • W₀ - W₀)))
    _ = H2ofFun Γ (graphPullback dat (⇑(QuotientGroup.mk' N)) target) := by rw [hblock]

/-! ## §2 The three per-orbit `hcoh` cohomologies -/

include hmk in
omit [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
/-- **Square-orbit `hcoh`** (Lemma 6.15 eq. (103) at a block coordinate) at a general local
source: the graph pullback of the square block datum at any `Z¹`-representative is, in `H²`, the
corestriction of the cup square of the block's scalar Shapiro coordinate. -/
theorem hcoh_square_K {K : ℕ} (j : Fin K) (hNo : IsOpen (N : Set Γ))
    (b : ↥(Z1 Γ (Fin K → RegRep N))) :
    H2ofFun Γ (graphPullback (squareBlockDatum N j) (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun Γ (cor2Fun N (fun p =>
          shapiroCoord N (fun g => b.1 g j) p.1 * shapiroCoord N (fun g => b.1 g j) p.2)) := by
  classical
  have hβ := block_cocycleK N hmk b j
  have htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m := fun n m => smul_zmodTwo n m
  set W₀ : Fin K → RegRep N :=
    Pi.single j (shapiroPrim N (fun g => b.1 g j)) with hW₀def
  have hblock : (fun g => blockProj N j (b.1 g + (g • W₀ - W₀)))
      = shapiroFun N (shapiroCoord N (fun g => b.1 g j)) := by
    funext g
    show b.1 g j + ((g • W₀) j - W₀ j) = _
    rw [hW₀def, Pi.smul_apply, Pi.single_eq_same, hmk,
      shapiroFun_shapiroCoord_eq hβ g]
  refine (H2ofFun_graphPullback_comap_shiftK N hmk (squareOrbitDatum N) (blockProj N j)
    (fun c v => blockProj_smul N j c v) (isEquivariantFactorSet_squareBlockDatum N j) hNo b W₀
    hblock).trans ?_
  exact lemma_6_15_square N hNo
    ⟨shapiroCoord N (fun g => b.1 g j),
      shapiroCoord_mem_Z1 hβ (block_continuousK N b j) htriv⟩

include hmk in
omit [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
/-- **Free-orbit `hcoh`** (Lemma 6.15 eq. (104) at a block pair) at a general local source: the
graph pullback of the free block datum with shift `mk' ĝ` at any `Z¹`-representative is, in `H²`,
the corestriction of `α_j ⌣ ĝα_k` (conjugated second coordinate). -/
theorem hcoh_free_K {K : ℕ} (j k : Fin K) (ghat : Γ) (hNo : IsOpen (N : Set Γ))
    (b : ↥(Z1 Γ (Fin K → RegRep N))) :
    H2ofFun Γ (graphPullback (freeBlockDatum N j k (QuotientGroup.mk' N ghat))
        (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun Γ (cor2Fun N (fun p =>
          shapiroCoord N (fun g => b.1 g j) p.1 *
            shapiroCoord N (fun g => b.1 g k) ⟨ghat⁻¹ * (p.2 : Γ) * ghat, by
              simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ p.2.2 ghat⁻¹⟩)) := by
  classical
  have hβj := block_cocycleK N hmk b j
  have hβk := block_cocycleK N hmk b k
  have htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m := fun n m => smul_zmodTwo n m
  set W₀ : Fin K → RegRep N :=
    Function.update (Pi.single j (shapiroPrim N (fun g => b.1 g j))) k
      (shapiroPrim N (fun g => b.1 g k)) with hW₀def
  have hW₀k : W₀ k = shapiroPrim N (fun g => b.1 g k) := by
    rw [hW₀def, Function.update_self]
  have hW₀j : W₀ j = shapiroPrim N (fun g => b.1 g j) := by
    by_cases hjk : j = k
    · subst hjk
      rw [hW₀def, Function.update_self]
    · rw [hW₀def, Function.update_of_ne hjk, Pi.single_eq_same]
  have hblock : (fun g => blockProj₂ N j k (b.1 g + (g • W₀ - W₀)))
      = fun g => (shapiroFun N (shapiroCoord N (fun g' => b.1 g' j)) g,
          shapiroFun N (shapiroCoord N (fun g' => b.1 g' k)) g) := by
    funext g
    refine Prod.ext ?_ ?_
    · show b.1 g j + ((g • W₀) j - W₀ j)
          = shapiroFun N (shapiroCoord N (fun g' => b.1 g' j)) g
      rw [Pi.smul_apply, hW₀j, hmk]
      exact (shapiroFun_shapiroCoord_eq (β := fun g' => b.1 g' j) hβj g).symm
    · show b.1 g k + ((g • W₀) k - W₀ k)
          = shapiroFun N (shapiroCoord N (fun g' => b.1 g' k)) g
      rw [Pi.smul_apply, hW₀k, hmk]
      exact (shapiroFun_shapiroCoord_eq (β := fun g' => b.1 g' k) hβk g).symm
  refine (H2ofFun_graphPullback_comap_shiftK N hmk (freeOrbitDatum N (QuotientGroup.mk' N ghat))
    (blockProj₂ N j k) (fun c v => blockProj₂_smul N j k c v)
    (isEquivariantFactorSet_freeBlockDatum N j k (QuotientGroup.mk' N ghat)) hNo b W₀
    hblock).trans ?_
  exact lemma_6_15_free N hNo
    ⟨shapiroCoord N (fun g => b.1 g j),
      shapiroCoord_mem_Z1 hβj (block_continuousK N b j) htriv⟩
    ⟨shapiroCoord N (fun g => b.1 g k),
      shapiroCoord_mem_Z1 hβk (block_continuousK N b k) htriv⟩ ghat

include hmk in
omit [Finite (RegRep N)] [ContinuousSMul Γ (RegRep N)] in
/-- **Involution-orbit `hcoh`** (Lemma 6.15 eq. (105) at a block coordinate) at a general local
source: the graph pullback of the involution block datum at any `Z¹`-representative is, in `H²`,
the `U₀`-corestriction of the Evens norm of the block's scalar Shapiro coordinate. -/
theorem hcoh_involution_K {K : ℕ} (j : Fin K) (ghat : Γ) (hNo : IsOpen (N : Set Γ))
    (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup Γ) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (hs : (⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩ : U₀)
        ∉ N.subgroupOf U₀)
    (b : ↥(Z1 Γ (Fin K → RegRep N))) :
    H2ofFun Γ (graphPullback (invBlockDatum N j (QuotientGroup.mk' N ghat))
        (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun Γ (cor2Fun U₀ (fun p =>
          evensNormFun (N.subgroupOf U₀)
            ⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩
            (fun u => shapiroCoord N (fun g => b.1 g j) ⟨u.1.1, u.2⟩) (p.1, p.2))) := by
  classical
  have hβ := block_cocycleK N hmk b j
  have htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m := fun n m => smul_zmodTwo n m
  have hu2 : QuotientGroup.mk' N ghat * QuotientGroup.mk' N ghat = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hg2
  set W₀ : Fin K → RegRep N :=
    Pi.single j (shapiroPrim N (fun g => b.1 g j)) with hW₀def
  have hblock : (fun g => blockProj N j (b.1 g + (g • W₀ - W₀)))
      = shapiroFun N (shapiroCoord N (fun g => b.1 g j)) := by
    funext g
    show b.1 g j + ((g • W₀) j - W₀ j) = _
    rw [hW₀def, Pi.smul_apply, Pi.single_eq_same, hmk,
      shapiroFun_shapiroCoord_eq hβ g]
  refine (H2ofFun_graphPullback_comap_shiftK N hmk (invOrbitDatum N (QuotientGroup.mk' N ghat))
    (blockProj N j) (fun c v => blockProj_smul N j c v)
    (isEquivariantFactorSet_invBlockDatum N j hu2) hNo b W₀ hblock).trans ?_
  exact lemma_6_15_involution N hNo
    ⟨shapiroCoord N (fun g => b.1 g j),
      shapiroCoord_mem_Z1 hβ (block_continuousK N b j) htriv⟩ ghat hg hg2 U₀ hU₀ hs

end PerOrbit

/-! ## §3 The deep coordinate: `shapiroCoord = phiResK` at the block functional

`GQ2/Shapiro/Read.lean` §DeepCoordinate retyped against LG4a's anchored vocabulary
(`LocalGauss/DeepPackage.lean` §2–§3): the scalar restriction at the block functional **is** the
`H1ofFun` of the block's Shapiro coordinate, on the nose, so a class in the anchored deep half
hands every block a deep anchored Kummer class. -/

section DeepCoordinate

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The block-coordinate evaluation functional `F ↦ F j (1̄)` at a general local source. -/
noncomputable def evalWK (N : Subgroup Γ) [N.Normal] {K : ℕ} (j : Fin K) :
    (Fin K → RegRep N) →+ ZMod 2 where
  toFun F := F j (1 : Γ ⧸ N)
  map_zero' := rfl
  map_add' _ _ := rfl

variable (ρ : ContinuousMonoidHom Γ C)

section

variable {K : ℕ}
  [TopologicalSpace (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [DiscreteTopology (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [Finite (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [DistribMulAction Γ (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [ContinuousSMul Γ (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [DistribMulAction C (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]

omit [DiscreteTopology C] [Finite C]
  [Finite (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [ContinuousSMul Γ (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [DistribMulAction C (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))] in
/-- **The deep-coordinate identification** at a general local source: LG4a's scalar restriction
`phiResK` of a class at the block functional `evalWK j` **is** the `H1ofFun` of the Shapiro
coordinate of its canonical representative's block — on the nose. -/
theorem phiResK_evalWK (j : Fin K)
    (x : H1 Γ (Fin K → RegRep (ρ.toMonoidHom.ker : Subgroup Γ))) :
    phiResK ρ x (evalWK _ j)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (shapiroCoord _ (fun g => (Quotient.out x).1 g j)) := rfl

omit [DiscreteTopology C] [Finite C]
  [Finite (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [ContinuousSMul Γ (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))]
  [DistribMulAction C (RegRep (ρ.toMonoidHom.ker : Subgroup Γ))] in
/-- **The block coordinates of a deep class are deep** (the `hvanish` feed) at a general local
source: for `x` in the anchored deep half `deepPartK anc ρ` on the block module, every block's
scalar Shapiro coordinate has an anchored deep Kummer class. -/
theorem shapiroCoord_mem_deepClassesAt (anc : ContinuousMonoidHom Γ GalQ2) (j : Fin K)
    {x : H1 Γ (Fin K → RegRep (ρ.toMonoidHom.ker : Subgroup Γ))}
    (hx : x ∈ deepPartK (V := Fin K → RegRep (ρ.toMonoidHom.ker : Subgroup Γ)) anc ρ) :
    H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
        (shapiroCoord _ (fun g => (Quotient.out x).1 g j))
      ∈ deepClassesAt (kerAnc anc ρ) := by
  have h := (mem_deepPartK_iff anc ρ x).mp hx (evalWK _ j)
  rwa [phiResK_evalWK] at h

end

end DeepCoordinate

/-! ## §4 Deepness transport along an equivariant coefficient map

`GQ2.ShapiroDeepness.deepPart_mapCoeff1` (`GQ2/Shapiro/Deepness.lean` :99) and its naturality
input `GQ2.ShapiroExtend.phiRes_mapCoeff1` (`GQ2/Shapiro/Extend.lean` :237), retyped against
LG4a's `phiResK` / `deepPartK`.  This carries the anchored deep half `X₊` across the Lemma-6.14
regular embedding `ι : V →+ W` (the deepness companion of the isometry). -/

section DeepTransport

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable {W₁ W₂ : Type}
  [AddCommGroup W₁] [TopologicalSpace W₁] [DiscreteTopology W₁]
  [DistribMulAction Γ W₁] [DistribMulAction C W₁]
  [AddCommGroup W₂] [TopologicalSpace W₂] [DiscreteTopology W₂]
  [DistribMulAction Γ W₂] [DistribMulAction C W₂]
variable {ρ : ContinuousMonoidHom Γ C}

/-- **Naturality of the scalar restriction** in the coefficient map — `phiRes_mapCoeff1`
retyped: `phiResK` of a pushed-forward class at `φ` is `phiResK` of the class at `φ ∘ f`. -/
theorem phiResK_mapCoeff1 (hρ₁ : ∀ (g : Γ) (w : W₁), g • w = ρ g • w)
    (hρ₂ : ∀ (g : Γ) (w : W₂), g • w = ρ g • w)
    (f : W₁ →+ W₂) (hf : Continuous f) (hcompat : ∀ (g : Γ) (w : W₁), f (g • w) = g • f w)
    (x : H1 Γ W₁) (φ : W₂ →+ ZMod 2) :
    phiResK ρ (mapCoeff1 f hf hcompat x) φ = phiResK ρ x (φ.comp f) := by
  have hb : H1mk Γ W₁ (Quotient.out x) = x := Quotient.out_eq x
  have hmap : H1mk Γ W₂
      (Z1comap (ContinuousMonoidHom.id Γ) f hf (fun g n => hcompat g n)
        (Quotient.out x)) = mapCoeff1 f hf hcompat x := by
    conv_rhs => rw [← hb]
    exact (mapCoeff1_H1mk f hf hcompat (Quotient.out x)).symm
  have h1 := phiResK_of_rep ρ hρ₂ hmap φ
  have h2 := phiResK_of_rep ρ hρ₁ hb (φ.comp f)
  rw [← h1, ← h2]
  rfl

/-- **Deepness transports along an equivariant coefficient map** at a general local source —
`GQ2.ShapiroDeepness.deepPart_mapCoeff1` retyped: if `x ∈ deepPartK anc ρ` over `W₁` and
`f : W₁ →+ W₂` is a continuous `Γ`-equivariant map, then `mapCoeff1 f x ∈ deepPartK anc ρ`
over `W₂`. -/
theorem deepPartK_mapCoeff1 (anc : ContinuousMonoidHom Γ GalQ2)
    (hρ₁ : ∀ (g : Γ) (w : W₁), g • w = ρ g • w)
    (hρ₂ : ∀ (g : Γ) (w : W₂), g • w = ρ g • w)
    (f : W₁ →+ W₂) (hf : Continuous f) (hcompat : ∀ (g : Γ) (w : W₁), f (g • w) = g • f w)
    {x : H1 Γ W₁} (hx : x ∈ deepPartK (V := W₁) anc ρ) :
    mapCoeff1 f hf hcompat x ∈ deepPartK (V := W₂) anc ρ := by
  rw [mem_deepPartK_iff] at hx ⊢
  intro φ
  rw [phiResK_mapCoeff1 hρ₁ hρ₂ f hf hcompat x φ]
  exact hx (φ.comp f)

end DeepTransport

end GQ2.Dyadic
