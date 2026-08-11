/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.Instances.EvenFamilyConstruct
import GQ2.Dyadic.Instances.EvenRouteFinal

/-!
# W65-HFAM: the status re-cut, and what `Hfam` is after this wave

## The theorem of this file

**`Hfam` at a field is the even endpoint at that field.**  Given the two arithmetic binders of
`EvenRouteFinalCarried{N,M}` (the measured branch identification and the proved degree), the
even route's one carried input `EvenRouteFinalFamily{N,M} h K` is *equivalent* to its one
conclusion, `Nonempty (OrientedContinuousMulEquiv (chi{N,M} alpha h) chiCycKTwo)`
(`hfamFinal_family{N,M}_iff_orientedEquiv`; unfolded to the depth-level supply it is
`hfamFinal_status{N,M}_atDepth`).

The forward direction is the committed wave-58 endpoint.  The backward direction is this
wave's: an oriented equivalence pulls every field-side stage tuple back to a model tuple,
`EvenFamilyConstruct.lean` §5 builds the family at *every* model tuple, and the equivalence
pushes the family forward again (§1, §2 below).  So the supply carries **no slack**: it is
not an input strictly weaker than the goal, it *is* the goal, stated one station earlier.

## What this settles about the ticket

* `Hfam` cannot be **refuted** at any field without refuting the even classification itself
  there: a refutation of the supply at `K` is a proof that `G_K(2)` is not oriented-isomorphic
  to the even core, by `hfamFinal_not_family{N,M}_iff`.  The wave-56-style failure mode (a published
  supply falsified by a sibling lane) is structurally impossible for `Hfam`.
* `Hfam` cannot be **discharged** at any field by soft means either: any proof of it at `K`
  proves the classification at `K`.  The honest residual is therefore exactly the theorem the
  campaign wants, and §3 restates it in the arithmetic form where the remaining work lives:
  continuous `χ`-twisted one-cocycles at precision `2^(k+1)` with prescribed mod-2 reduction
  at the exact-fibre lifts (`EvenFamParitySupply{N,M}`), the even clone of the odd route's
  `SqStageTwistedCocycleParitySupply`.  That statement is mod-2 surjectivity of
  `Z¹(χ mod 2^(k+1)) → Z¹(𝔽₂)` on prescribed coordinates: higher Kummer theory at `K`.
* On the presented cores themselves the supply is a **theorem** (census-free, std-3), so the
  even route's remaining gap is purely about transporting cocycles across the arithmetic of a
  real field, not about the word combinatorics, the tail calculus, or the relator.

## Numbering

1. pullback of a field stage tuple along an oriented equivalence;
2. the family follows from the endpoint, at every tuple and level;
3. the arithmetic residual: the twisted-cocycle parity supply, and its exact calibration;
4. the status theorems;
5. axiom pins.
-/

namespace GQ2.Dyadic.EvenFamily

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenRouteFinal
open GQ2.Dyadic.LSquare (IsChiShadowDeriv IsChiTwistedCocycle chiShadowDerivOfCocycle
  isChiShadowDeriv_chiShadowDerivOfCocycle isChiTwistedCocycle_of_isChiShadowDeriv
  levelQuotCongr levelQuotCongr_levelMk)
open scoped GQ2.Dyadic.LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Pullback of a field stage tuple along an oriented equivalence

`levelQuotCongr` (the committed tower functoriality of W-RankOne) turns an oriented
equivalence `e : D → G_K(2)` into an isomorphism of every finite level, and a stage tuple of
the even word data over the field pulls back to one over the model with the same word datum
and table. -/

section Pullback

variable {C G : Type}
variable [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {chiC : ContinuousMonoidHom C ℤ_[2]ˣ} {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
variable {n : ℕ} {W : StageWord n} {v : Fin n → ℤ_[2]ˣ} {k : ℕ}

/-- **Pullback of a stage tuple along an orientation-compatible equivalence.**  The word
datum and the value table do not move; the generators, rows, relation and generation all
transport through `levelQuotCongr`. -/
def evenFamTuplePullback (e : ContinuousMulEquiv C G)
    (horient : ∀ x, chiG (e x) = chiC x)
    (T : Tuple W v G chiG k) : Tuple W v C chiC k where
  generators i := (levelQuotCongr e k).symm (T.generators i)
  rows i := by
    obtain ⟨y, hy1, hy2⟩ := T.rows i
    refine ⟨e.symm y, ?_, ?_⟩
    · have := horient (e.symm y)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      rw [← this, hy1]
    · rw [hy2]
      have hmk : levelQuotCongr e k (levelMk C k (e.symm y)) = levelMk G k y := by
        rw [levelQuotCongr_levelMk, ContinuousMulEquiv.apply_symm_apply]
      exact ((MulEquiv.symm_apply_eq (levelQuotCongr e k)).mpr hmk.symm).symm
  relation := by
    have hmap : W.word (fun i ↦ (levelQuotCongr e k).symm (T.generators i)) =
        (levelQuotCongr e k).symm (W.word T.generators) :=
      (W.map_word (levelQuotCongr e k).symm.toMonoidHom T.generators).symm
    rw [hmap, T.relation, map_one]
  topGen := by
    have hcomp : (Set.range fun i ↦ (levelQuotCongr e k).symm (T.generators i)) =
        ⇑(levelQuotCongr e k).symm.toMonoidHom '' Set.range T.generators := by
      rw [← Set.range_comp]
      rfl
    rw [hcomp, ← MonoidHom.map_closure, T.topGen]
    exact Subgroup.map_top_of_surjective _ (levelQuotCongr e k).symm.surjective

@[simp] theorem evenFamTuplePullback_generators (e : ContinuousMulEquiv C G)
    (horient : ∀ x, chiG (e x) = chiC x) (T : Tuple W v G chiG k)
    (i : Fin n) :
    (evenFamTuplePullback e horient T).generators i =
      (levelQuotCongr e k).symm (T.generators i) := rfl

end Pullback

section Transport

variable {C G : Type}
variable [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {chiC : ContinuousMonoidHom C ℤ_[2]ˣ} {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
variable {h k : ℕ} {W : StageWord (MarkedCore.coreRank h)}
variable {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **Transport of a derivation family along an orientation-compatible equivalence.**  Lifts
push forward through `e`, functionals pull back through `e.symm`, and the parity pattern is
untouched because `e.symm ∘ e` is the identity on the lifts. -/
def evenFamFamilyTransport (e : ContinuousMulEquiv C G)
    (horient : ∀ x, chiG (e x) = chiC x) {T : Tuple W v G chiG k}
    (F : EvenKernelDerivationFamily (evenFamTuplePullback e horient T)) :
    EvenKernelDerivationFamily T where
  lifts i := e (F.lifts i)
  lifts_chi i := by rw [horient (F.lifts i), F.lifts_chi i]
  lifts_level i := by
    have hmk : levelMk G k (e (F.lifts i)) =
        levelQuotCongr e k (levelMk C k (F.lifts i)) :=
      (levelQuotCongr_levelMk e k (F.lifts i)).symm
    rw [hmk, F.lifts_level i, evenFamTuplePullback_generators,
      MulEquiv.apply_symm_apply]
  deriv i₀ hi₀ := (F.deriv i₀ hi₀).comp
    ⟨e.symm.toMonoidHom, e.symm.continuous_toFun⟩
  deriv_base i₀ hi₀ g := by
    show ((F.deriv i₀ hi₀) (e.symm g)).g = _
    rw [F.deriv_base i₀ hi₀ (e.symm g)]
    have := horient (e.symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    rw [this]
  deriv_diag i₀ hi₀ := by
    show ¬ (2 : ZMod (2 ^ (k + 1))) ∣ ((F.deriv i₀ hi₀) (e.symm (e (F.lifts i₀)))).u
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact F.deriv_diag i₀ hi₀
  deriv_off i₀ hi₀ j hj hji := by
    show (2 : ZMod (2 ^ (k + 1))) ∣ ((F.deriv i₀ hi₀) (e.symm (e (F.lifts j)))).u
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact F.deriv_off i₀ hi₀ j hj hji

end Transport

/-! ## §2 The family follows from the endpoint

At any field with the even oriented equivalence at `(alpha, h)`, `Hfam` holds at that depth:
every field tuple pulls back to a model tuple, the model carries the family at every tuple
(`evenFam_modelFamily{N,M}`), and the family transports forward.  The relator kill rides
along free (§2 of the construction file). -/

section FromEndpoint

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **`Hfam` from the endpoint, `N` branch**: an oriented equivalence with the `N` core at
depth `alpha` delivers the derivation family with its relator kill at every level and every
tuple, in the exact binder shape of `EvenRouteFinalFamilyN`. -/
theorem evenFam_hfamN_of_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :
    ∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F := by
  intro k hk T
  obtain ⟨F'⟩ := evenFam_modelFamilyN alpha h halpha (Nat.le_of_succ_le halpha) hk
    (evenFamTuplePullback e.1 e.2 T)
  exact ⟨evenFamFamilyTransport e.1 e.2 F',
    evenFam_relatorKillN (evenFamFamilyTransport e.1 e.2 F')⟩

/-- **`Hfam` from the endpoint, `M` branch.** -/
theorem evenFam_hfamM_of_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    ∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F := by
  intro k hk T
  obtain ⟨F'⟩ := evenFam_modelFamilyM alpha h halpha (Nat.le_of_succ_le halpha) hk
    (evenFamTuplePullback e.1 e.2 T)
  exact ⟨evenFamFamilyTransport e.1 e.2 F',
    evenFam_relatorKillM (evenFamFamilyTransport e.1 e.2 F')⟩

end FromEndpoint

/-! ## §3 The arithmetic residual: the twisted-cocycle parity supply

The even clone of the odd route's `SqStageTwistedCocycleParitySupply`, generic in the word
datum and value table: exact-fibre lifts and, per non-twisted slot, a continuous `χ`-twisted
one-cocycle at precision `2^(k+1)` with the Kronecker parity pattern at the lifts.  This is
the exact arithmetic content of `Hfam` at a field, and by §4 it is exactly calibrated: it
holds at every stage if and only if the even classification holds at the field.  Mod-2
surjectivity of `Z¹(χ mod 2^(k+1)) → Z¹(𝔽₂)` on the prescribed coordinates, which is where
higher Kummer theory enters, is what remains. -/

section Parity

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The even twisted-cocycle parity supply at a stage tuple.**  Exact-fibre lifts of the
generators and, for each non-twisted slot `i₀ ≠ 1`, a continuous `χ`-twisted one-cocycle at
precision `2^(k+1)` odd at the `i₀`-lift and even at the other non-twisted lifts.  The
twisted slot `1` is unconstrained.  Generic in the even word datum and table. -/
def EvenFamParitySupply {h k : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) : Prop :=
  ∃ lifts : Fin (MarkedCore.coreRank h) → maxProPQuotient 2 (GalK K),
    (∀ i, chiCycKTwo (K := K) (lifts i) = v i) ∧
    (∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i) ∧
    ∀ i₀ : Fin (MarkedCore.coreRank h), i₀ ≠ 1 →
      ∃ u : maxProPQuotient 2 (GalK K) → ZMod (2 ^ (k + 1)),
        IsChiTwistedCocycle (chiCycKTwo (K := K)) (k + 1) u ∧
        ¬ (2 : ZMod (2 ^ (k + 1))) ∣ u (lifts i₀) ∧
        ∀ j : Fin (MarkedCore.coreRank h), j ≠ 1 → j ≠ i₀ →
          (2 : ZMod (2 ^ (k + 1))) ∣ u (lifts j)

/-- **The family from the parity supply**: cocycles assemble into `χ`-shadowed derivations
(`chiShadowDerivOfCocycle`), and the parity pattern is the family's Kronecker fields. -/
theorem evenFam_nonempty_family_of_paritySupply {h k : ℕ}
    {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    {T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k}
    (H : EvenFamParitySupply T) : Nonempty (EvenKernelDerivationFamily T) := by
  obtain ⟨lifts, hchi, hlvl, hcoc⟩ := H
  choose u hu hdiag hoff using hcoc
  exact ⟨{ lifts := lifts
           lifts_chi := hchi
           lifts_level := hlvl
           deriv := fun i₀ hi₀ ↦ chiShadowDerivOfCocycle
             (GQ2.Dyadic.LSquare.maxProTwoGalK_isTopologicallyFinGen K)
             isProP_maxProPQuotient (chiCycKTwo (K := K)) (u i₀ hi₀) (hu i₀ hi₀)
           deriv_base := fun i₀ hi₀ ↦
             isChiShadowDeriv_chiShadowDerivOfCocycle _ _ _ _ _
           deriv_diag := fun i₀ hi₀ ↦ hdiag i₀ hi₀
           deriv_off := fun i₀ hi₀ j hj hji ↦ hoff i₀ hi₀ j hj hji }⟩

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The parity supply from the family**: the offset of each functional is a twisted
cocycle. -/
theorem evenFam_paritySupply_of_family {h k : ℕ}
    {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    {T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k}
    (F : EvenKernelDerivationFamily T) : EvenFamParitySupply T :=
  ⟨F.lifts, F.lifts_chi, F.lifts_level, fun i₀ hi₀ ↦
    ⟨fun g ↦ ((F.deriv i₀ hi₀) g).u,
      isChiTwistedCocycle_of_isChiShadowDeriv (F.deriv_base i₀ hi₀),
      F.deriv_diag i₀ hi₀, fun j hj hji ↦ F.deriv_off i₀ hi₀ j hj hji⟩⟩

/-- The family exists exactly when the parity supply holds. -/
theorem evenFam_nonempty_family_iff_paritySupply {h k : ℕ}
    {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    {T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k} :
    Nonempty (EvenKernelDerivationFamily T) ↔ EvenFamParitySupply T :=
  ⟨fun ⟨F⟩ ↦ evenFam_paritySupply_of_family F, evenFam_nonempty_family_of_paritySupply⟩

end Parity

/-! ## §4 The status theorems

The headline: over the two arithmetic binders, the even route's carried input is its
conclusion.  The forward halves are the committed wave-58 endpoints; the backward halves are
§2.  Stated per branch at the field's own depth, and for the artefact `Prop`s themselves. -/

section Status

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **THE `N` STATUS AFTER THIS WAVE: `Hfam` is the endpoint.**  At a field on the `N` branch
at depth `alpha` with the even degree `2 + 2h`, the single-depth `Hfam` holds if and only if
the even oriented equivalence holds.  The supply the campaign has carried for eleven waves is
not an input to the theorem; it is the theorem. -/
theorem hfamFinal_statusN_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    (∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) ↔
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  ⟨fun Hfam ↦ evenRouteFinal_orientedEquivN_atDepth halpha hrange hev Hfam,
    fun ⟨e⟩ ↦ evenFam_hfamN_of_orientedEquiv halpha e⟩

/-- **THE `M` STATUS AFTER THIS WAVE: `Hfam` is the endpoint.** -/
theorem hfamFinal_statusM_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    (∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) ↔
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  ⟨fun Hfam ↦ evenRouteFinal_orientedEquivM_atDepth halpha hrange hev Hfam,
    fun ⟨e⟩ ↦ evenFam_hfamM_of_orientedEquiv halpha e⟩

/-- **The guarded artefact field is the endpoint, `N` branch.**  The wave-58 artefact's
`family` field, over the identification and the degree, is equivalent to the oriented
equivalence at the field's own depth. -/
theorem hfamFinal_familyN_iff_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalFamilyN h K ↔
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  rw [evenRouteFinal_familyN_iff_atDepth halpha hrange]
  exact hfamFinal_statusN_atDepth halpha hrange hev

/-- **The guarded artefact field is the endpoint, `M` branch.** -/
theorem hfamFinal_familyM_iff_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalFamilyM h K ↔
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  rw [evenRouteFinal_familyM_iff_atDepth halpha hrange]
  exact hfamFinal_statusM_atDepth halpha hrange hev

/-- **The whole artefact is the endpoint, `N` branch**: over the identification and the
degree, `EvenRouteFinalCarriedN` holds exactly when the even classification holds.  With
`evenRouteFinal_statusN` this closes the circle: artefact, family field, and endpoint are one
statement at every real field. -/
theorem hfamFinal_carriedN_iff_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalCarriedN h K ↔
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  constructor
  · exact fun C ↦ evenRouteFinal_orientedEquivN_of_carried halpha hrange C
  · intro he
    exact ⟨hev, ⟨alpha, halpha, hrange⟩,
      (hfamFinal_familyN_iff_orientedEquiv halpha hrange hev).mpr he⟩

/-- **The whole artefact is the endpoint, `M` branch.** -/
theorem hfamFinal_carriedM_iff_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalCarriedM h K ↔
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  constructor
  · exact fun C ↦ evenRouteFinal_orientedEquivM_of_carried halpha hrange C
  · intro he
    exact ⟨hev, ⟨alpha, halpha, hrange⟩,
      (hfamFinal_familyM_iff_orientedEquiv halpha hrange hev).mpr he⟩

/-- **A refutation of `Hfam` is a refutation of the classification.**  The contrapositive
form of the status theorem, recorded because it is the sentence that rules out the wave-56
failure mode for this supply: no lane can falsify `EvenRouteFinalFamilyN` at a field without
proving that field is not oriented-equivalent to the even core. -/
theorem hfamFinal_not_familyN_iff {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteFinalFamilyN h K ↔
      IsEmpty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  rw [hfamFinal_familyN_iff_orientedEquiv halpha hrange hev,
    not_nonempty_iff]

/-- The `M` contrapositive. -/
theorem hfamFinal_not_familyM_iff {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteFinalFamilyM h K ↔
      IsEmpty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  rw [hfamFinal_familyM_iff_orientedEquiv halpha hrange hev,
    not_nonempty_iff]

/-- **The residual, in arithmetic form and exactly costed, `N` branch**: the per-stage
twisted-cocycle parity supply holds at every level and tuple if and only if the even
classification holds at the field.  This is the statement left open, and its cost is
exact. -/
theorem hfamFinal_parityN_iff_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    (∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        EvenFamParitySupply T) ↔
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  rw [← hfamFinal_statusN_atDepth halpha hrange hev]
  constructor
  · intro H k hk T
    exact evenFam_exists_kill_iff_nonemptyN.mpr
      (evenFam_nonempty_family_of_paritySupply (H k hk T))
  · intro H k hk T
    exact evenFam_nonempty_family_iff_paritySupply.mp
      (evenFam_exists_kill_iff_nonemptyN.mp (H k hk T))

/-- **The residual, in arithmetic form and exactly costed, `M` branch.** -/
theorem hfamFinal_parityM_iff_orientedEquiv {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    (∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        EvenFamParitySupply T) ↔
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  rw [← hfamFinal_statusM_atDepth halpha hrange hev]
  constructor
  · intro H k hk T
    exact evenFam_exists_kill_iff_nonemptyM.mpr
      (evenFam_nonempty_family_of_paritySupply (H k hk T))
  · intro H k hk T
    exact evenFam_nonempty_family_iff_paritySupply.mp
      (evenFam_exists_kill_iff_nonemptyM.mp (H k hk T))

end Status

end

end GQ2.Dyadic.EvenFamily

/-! ## §5 Axiom pins

Every public declaration, printed.  §1, §2 and most of §3 stay at std-3.  ⚠ Two §3 declarations
do not: `evenFam_nonempty_family_of_paritySupply` reaches
`absGalQ2_isTopologicallyFinitelyGenerated`, and so does the iff it feeds,
`evenFam_nonempty_family_iff_paritySupply`.  That axiom is already inside the set `S` below, so
nothing new leaks from this file; only the per-section split is coarser than std-3.  §4's status
theorems consume the
committed even endpoint chain in their forward halves, so they print the seven-element set
`S = std-3 + {hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic}` that
`EvenRouteFinal.lean` §8 records for the endpoints; the backward halves add nothing.  The
committed endpoints are printed alongside for the side-by-side. -/

section AxiomPins

open GQ2.Dyadic.EvenFamily

-- §1 pullback and transport
#print axioms evenFamTuplePullback
#print axioms evenFamTuplePullback_generators
#print axioms evenFamFamilyTransport

-- §2 the family from the endpoint
#print axioms evenFam_hfamN_of_orientedEquiv
#print axioms evenFam_hfamM_of_orientedEquiv

-- §3 the arithmetic residual
#print axioms EvenFamParitySupply
#print axioms evenFam_nonempty_family_of_paritySupply
#print axioms evenFam_paritySupply_of_family
#print axioms evenFam_nonempty_family_iff_paritySupply

-- §4 the status theorems
#print axioms hfamFinal_statusN_atDepth
#print axioms hfamFinal_statusM_atDepth
#print axioms hfamFinal_familyN_iff_orientedEquiv
#print axioms hfamFinal_familyM_iff_orientedEquiv
#print axioms hfamFinal_carriedN_iff_orientedEquiv
#print axioms hfamFinal_carriedM_iff_orientedEquiv
#print axioms hfamFinal_not_familyN_iff
#print axioms hfamFinal_not_familyM_iff
#print axioms hfamFinal_parityN_iff_orientedEquiv
#print axioms hfamFinal_parityM_iff_orientedEquiv

-- the committed endpoints, for the side-by-side
#print axioms GQ2.Dyadic.EvenRouteFinal.evenRouteFinal_orientedEquivN_atDepth
#print axioms GQ2.Dyadic.EvenRouteFinal.evenRouteFinal_orientedEquivM_atDepth
#print axioms GQ2.Dyadic.EvenRouteFinal.evenRouteFinal_statusN
#print axioms GQ2.Dyadic.EvenRouteFinal.evenRouteFinal_statusM

end AxiomPins
