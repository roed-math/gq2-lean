/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenPerK
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageDerivationCocycle
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageRankOne
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteReverse

/-!
# W65-HFAM: the even derivation family, constructed where it can be and calibrated where it
cannot

## What this file is

The first direct assault on `Hfam`, the even route's one remaining supply
(`EvenRouteFinal.evenRouteFinal_status`): for every stage tuple of the even word data, a
coordinate derivation family with its relator kill.  Four results, in decreasing order of
finality.

1. **The relator kill costs nothing** (§1, §2).  The even relator words are universally closed
   in the word-lift group `ℤ₂ ⋊ ℤ₂ˣ` at their value tables, for *every* offset vector: that is
   exactly the statement that `(1, nUnit α, 1, 1)` and `(1, −1, 1, mUnit α)` are Labute
   orientation data, which is committed (`isLabuteOrientationDatum{N,M}_{n,m}Unit`), plus the
   handle lemma.  Hence `EvenKernelRelatorKill F` is a **theorem for every family `F`** over an
   even tuple, on both branches, and `Hfam`'s conjunction `∃ F, EvenKernelRelatorKill F`
   collapses to bare existence, `Nonempty (EvenKernelDerivationFamily T)` (§2.3).

2. **The model derivations exist at every offset** (§3).  The even clone of `sqDerivModel`: a
   continuous homomorphism `D_{N,M}(α, h) → WL N` for every precision and every offset vector,
   with base the mod-`2^N` shadow of the canonical orientation.  Existence is the universal
   closure of §1 again, read through `redWL`.

3. **The model carries the family at every tuple** (§4 and §5).  Not only at the canonical
   marking: for *every* stage tuple `T` of the even word data over the presented core itself,
   the family exists.  The point is the mod-`2` linear algebra: parities of a shadow derivation
   descend to a linear functional on the Frattini quotient, the Frattini quotient has
   `𝔽₂`-dimension exactly `coreRank h` because the cores are Demushkin of that rank (EV-1b/1e),
   and any tuple's generator classes therefore form a *basis*, so Kronecker parity patterns are
   dual-basis functionals and every one of them is hit by a model derivation.  So `Hfam`'s
   statement, verbatim but with the field's group replaced by the model core, is a theorem.

4. **Transport: the family follows from the endpoint** (`EvenFamilyStatus.lean`, the sequel
   file).  An oriented equivalence of the field group with the model core transports §5's
   at-every-tuple families to the field, giving `Hfam` at that field and depth outright.  With
   the committed endpoint (`evenRouteFinal_orientedEquivN_atDepth`) this makes `Hfam` at a field
   *equivalent* to the even oriented equivalence there, so the supply carries no slack: the
   campaign's one open question and its one open theorem are the same statement.  The honest
   residual, `Hfam` at a real field, is re-expressed there in its arithmetic form (twisted
   cocycles mod `2^(k+1)` with prescribed mod-`2` reduction), which is where higher Kummer
   theory enters and this wave stops.

## What this does NOT do

No statement below discharges `Hfam` at any *field*: the wave-55 witnesses
(`evenRouteWitness_orientedEquiv{N,M}_*`) still carry the family as a hypothesis, so no field
in the tree has an unconditional even endpoint to transport from.  §4 and §5 discharge the
verbatim `Hfam` statement at the model carrier; the sequel file proves that at field carriers
it is exactly as strong as the endpoint, and no stronger.

## Numbering

1. the universal word-lift closure of the even relators at their value tables;
2. the relator kill is free, and `Hfam` collapses to family existence;
3. the model derivations at every precision and offset;
4. mod-2 parity linear algebra on the Frattini quotient;
5. the family at every tuple of the model cores.
-/

namespace GQ2.Dyadic.EvenFamily

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.LSquare (IsChiShadowDeriv IsChiTwistedCocycle chiShadowDerivOfCocycle)
open scoped GQ2.Dyadic.LSquare

/-! ## §1 The universal word-lift closure of the even relators

The even value tables close their relator words in `ℤ₂ ⋊ ℤ₂ˣ` for every offset vector.  The
core letters are the committed orientation data; the handles are base-one commutators, killed
by the committed handle lemma.  This is the even clone of the L template's
`sqStageChiTarget_relWord_wordLift`, and it is what makes both §2 and §3 free. -/

section Closure

/-- **The `N_α` relator is universally closed at the `N` table**: for every offset vector the
word-lift evaluation dies.  The core is `isLabuteOrientationDatumN_nUnit`; the handles are the
handle lemma. -/
theorem evenFam_nRelWord_wordLift (α : ℕ) (hα : 1 ≤ α) {h : ℕ}
    (u : Fin (MarkedCore.coreRank h) → ℤ_[2]) :
    MarkedCore.nRelWord α
      (fun i ↦ (⟨u i, vN α i⟩ : FoxH.WordLift ℤ_[2] ℤ_[2]ˣ)) = 1 := by
  have hcore := isLabuteOrientationDatumN_nUnit hα (u 0) (u 1) (u 2) (u 3)
  simp only [MarkedCore.nRelWord, vN_zero, vN_one, vN_two, vN_three, vN_handleU, vN_handleV,
    hcore, MarkedCore.handleWord_wordLift_one, one_mul]

/-- **The `M_α` relator is universally closed at the `M` table.** -/
theorem evenFam_mRelWord_wordLift (α : ℕ) (hα : 1 ≤ α) {h : ℕ}
    (u : Fin (MarkedCore.coreRank h) → ℤ_[2]) :
    MarkedCore.mRelWord α
      (fun i ↦ (⟨u i, vM α i⟩ : FoxH.WordLift ℤ_[2] ℤ_[2]ˣ)) = 1 := by
  have hcore := isLabuteOrientationDatumM_mUnit hα (u 0) (u 1) (u 2) (u 3)
  simp only [MarkedCore.mRelWord, vM_zero, vM_one, vM_two, vM_three, vM_handleU, vM_handleV,
    hcore, MarkedCore.handleWord_wordLift_one, one_mul]

end Closure

/-! ## §2 The relator kill is free

The even clone of the L template's `SqStageCoordinateDerivationFamily.defect_mem_derivKer`,
stated once for any word datum with a universally closed table and instantiated on both even
branches.  Consequence: the pair `∃ F, EvenKernelRelatorKill F` that every even endpoint
carries is equivalent to bare `Nonempty (EvenKernelDerivationFamily T)`. -/

section Kill

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

/-- **The ambient relator kill, generic form.**  If the value table closes the word
universally in the word-lift group, then the level-`k+1` class of the word at any exact-fibre
lifts whose level-`k` classes satisfy the relation is killed by every `χ`-shadowed
derivation, regardless of its offsets. -/
theorem evenFam_word_mem_derivKer {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (huniv : ∀ u : Fin (MarkedCore.coreRank h) → ℤ_[2],
      W.word (fun i ↦ (⟨u i, v i⟩ : FoxH.WordLift ℤ_[2] ℤ_[2]ˣ)) = 1)
    {Φ : ContinuousMonoidHom G (WL (k + 1))}
    (hbase : IsChiShadowDeriv chi Φ) (x : Fin (MarkedCore.coreRank h) → G)
    (hchi : ∀ i, chi (x i) = v i)
    (hrel : W.word (fun i ↦ levelMk G k (x i)) = 1) :
    levelMk G (k + 1) (W.word x) ∈ derivKer Φ k := by
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  refine ⟨W.word x, ?_, rfl, ?_⟩
  · apply (QuotientGroup.eq_one_iff _).mp
    show levelMk G k (W.word x) = 1
    rw [W.map_word (levelMk G k) x]
    exact hrel
  · have hΦx : ∀ i, Φ (x i) = redWL (k + 1)
        ⟨(((Φ (x i)).u.val : ℕ) : ℤ_[2]), v i⟩ := by
      intro i
      refine FoxH.WordLift.ext ?_ ?_
      · show (Φ (x i)).u = PadicInt.toZModPow (k + 1) (((Φ (x i)).u.val : ℕ) : ℤ_[2])
        rw [map_natCast]
        exact (ZMod.natCast_rightInverse (Φ (x i)).u).symm
      · show (Φ (x i)).g =
          Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (v i)
        rw [hbase (x i), hchi i]
    have hword : Φ (W.word x) = 1 := by
      calc Φ (W.word x)
          = W.word (fun i ↦ Φ (x i)) := W.map_word Φ.toMonoidHom x
        _ = W.word (fun i ↦ redWL (k + 1)
            ⟨(((Φ (x i)).u.val : ℕ) : ℤ_[2]), v i⟩) :=
              congrArg W.word (funext hΦx)
        _ = redWL (k + 1) (W.word (fun i ↦
            (⟨(((Φ (x i)).u.val : ℕ) : ℤ_[2]), v i⟩ :
              FoxH.WordLift ℤ_[2] ℤ_[2]ˣ))) :=
              (W.map_word (redWL (k + 1)) _).symm
        _ = 1 := by
              rw [huniv (fun i ↦ (((Φ (x i)).u.val : ℕ) : ℤ_[2]))]
              exact map_one _
    rw [hword]
    show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ (0 : ZMod (2 ^ (k + 1)))
    exact dvd_zero _

/-- **Every family functional kills the stage defect**, for any word datum with a universally
closed table.  The defect is the level class of the ambient word value at the family's own
lifts, and that class is killed by §2's generic kill. -/
theorem evenFam_relatorKill_of_univ {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (huniv : ∀ u : Fin (MarkedCore.coreRank h) → ℤ_[2],
      W.word (fun i ↦ (⟨u i, v i⟩ : FoxH.WordLift ℤ_[2] ℤ_[2]ˣ)) = 1)
    {T : Tuple W v G chi k} (F : EvenKernelDerivationFamily T) :
    EvenKernelRelatorKill F := by
  intro i₀ hi₀
  have hdef : stageDefect W G k T.generators = levelMk G (k + 1) (W.word F.lifts) := by
    rw [W.map_word (levelMk G (k + 1)) F.lifts]
    exact (stageDefect_eq_of_lift W k T.generators _ (fun i ↦ by
      rw [levelProj_levelMk, F.lifts_level i])).symm
  rw [hdef]
  refine evenFam_word_mem_derivKer huniv (F.deriv_base i₀ hi₀) F.lifts F.lifts_chi ?_
  rw [show (fun i ↦ levelMk G k (F.lifts i)) = T.generators from funext F.lifts_level]
  exact T.relation

/-- **The relator kill is a theorem on the `N` branch**: every derivation family over an
`N`-branch stage tuple kills the relator.  The first conjunct of `Hfam` that costs anything
is therefore existence, not the kill. -/
theorem evenFam_relatorKillN {α : ℕ} {hα : 1 ≤ α}
    {T : Tuple (nStageWord α h hα) (vN α) G chi k} (F : EvenKernelDerivationFamily T) :
    EvenKernelRelatorKill F :=
  evenFam_relatorKill_of_univ (evenFam_nRelWord_wordLift α hα) F

/-- **The relator kill is a theorem on the `M` branch.** -/
theorem evenFam_relatorKillM {α : ℕ} {hα : 1 ≤ α}
    {T : Tuple (mStageWord α h hα) (vM α) G chi k} (F : EvenKernelDerivationFamily T) :
    EvenKernelRelatorKill F :=
  evenFam_relatorKill_of_univ (evenFam_mRelWord_wordLift α hα) F

/-- **`Hfam`'s inner statement collapses to bare existence, `N` branch**: the pair the even
endpoints demand at a tuple is exactly nonemptiness of the family. -/
theorem evenFam_exists_kill_iff_nonemptyN {α : ℕ} {hα : 1 ≤ α}
    {T : Tuple (nStageWord α h hα) (vN α) G chi k} :
    (∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) ↔
      Nonempty (EvenKernelDerivationFamily T) :=
  ⟨fun ⟨F, _⟩ ↦ ⟨F⟩, fun ⟨F⟩ ↦ ⟨F, evenFam_relatorKillN F⟩⟩

/-- **`Hfam`'s inner statement collapses to bare existence, `M` branch.** -/
theorem evenFam_exists_kill_iff_nonemptyM {α : ℕ} {hα : 1 ≤ α}
    {T : Tuple (mStageWord α h hα) (vM α) G chi k} :
    (∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) ↔
      Nonempty (EvenKernelDerivationFamily T) :=
  ⟨fun ⟨F, _⟩ ↦ ⟨F⟩, fun ⟨F⟩ ↦ ⟨F, evenFam_relatorKillM F⟩⟩

end Kill

/-! ## §3 The model derivations at every precision and offset

The even clone of `sqDerivModel`: for every offset vector a continuous homomorphism from the
presented core to the finite lift group, with base the mod-`2^N` shadow of the canonical
orientation.  Existence is §1's universal closure read through `redWL`; everything else is the
universal property of the cores. -/

section Model

/-- The finite lift group is pro-`2` (the third private clone of this fifteen-line count; the
committed original and both prior clones are `private`). -/
private theorem evenFam_isProP_WL {N : ℕ} (hN : 1 ≤ N) : IsProP 2 (WL N) := by
  refine isProP_of_isPGroup (IsPGroup.of_card (n := N + (N - 1)) ?_)
  have h1 : Nat.card (WL N) = Nat.card (ZMod (2 ^ N)) * Nat.card ((ZMod (2 ^ N))ˣ) := by
    rw [Nat.card_congr (FoxH.WordLift.equivProd (A := ZMod (2 ^ N)) (C := (ZMod (2 ^ N))ˣ)),
      Nat.card_prod]
  have h2 : Nat.card (ZMod (2 ^ N)) = 2 ^ N := by
    haveI : NeZero (2 ^ N) := ⟨by positivity⟩
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card ((ZMod (2 ^ N))ˣ) = 2 ^ (N - 1) := by
    haveI : NeZero (2 ^ N) := ⟨by positivity⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  rw [h1, h2, h3, ← pow_add]

/-- The `N` core is topologically finitely generated, in the `Finset` shape the tower and
discreteness lemmas consume. -/
theorem evenFam_isTopFinGen_DN (α h : ℕ) : IsTopologicallyFinGen (DN α h : Type) := by
  refine ⟨(Set.finite_range (dnGen α h)).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact dn_topGen α h

/-- The `M` core is topologically finitely generated. -/
theorem evenFam_isTopFinGen_DM (α h : ℕ) : IsTopologicallyFinGen (DM α h : Type) := by
  refine ⟨(Set.finite_range (dmGen α h)).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact dm_topGen α h

/-- The canonical orientation takes its table values on the generators, `N` branch. -/
theorem evenFam_chiN_dnGen (α h : ℕ) (i : Fin (MarkedCore.coreRank h)) :
    chiN α h (dnGen α h i) = vN α i := by
  rw [chiN, nLiftHom_gen]
  rfl

/-- The canonical orientation takes its table values on the generators, `M` branch. -/
theorem evenFam_chiM_dmGen (α h : ℕ) (i : Fin (MarkedCore.coreRank h)) :
    chiM α h (dmGen α h i) = vM α i := by
  rw [chiM, mLiftHom_gen]
  rfl

variable {N : ℕ}

/-- **The `N` model derivation.**  The continuous homomorphism `D_N(α, h) → WL N` carrying the
`i`-th generator to the lift with offset `w i` over the `N` table.  It exists at every
precision and offset because the relator is universally closed at the table (§1). -/
def evenFamDerivModelN (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) :
    ContinuousMonoidHom (DN α h : Type) (WL N) :=
  nLiftHom α h (evenFam_isProP_WL hN)
    (fun i ↦ redWL N ⟨w i, vN α i⟩) (by
      rw [← MarkedCore.map_nRelWord (redWL N), evenFam_nRelWord_wordLift α hα, map_one])

/-- **The `M` model derivation.** -/
def evenFamDerivModelM (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) :
    ContinuousMonoidHom (DM α h : Type) (WL N) :=
  mLiftHom α h (evenFam_isProP_WL hN)
    (fun i ↦ redWL N ⟨w i, vM α i⟩) (by
      rw [← MarkedCore.map_mRelWord (redWL N), evenFam_mRelWord_wordLift α hα, map_one])

@[simp] theorem evenFamDerivModelN_gen (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) (i : Fin (MarkedCore.coreRank h)) :
    evenFamDerivModelN α h hα hN w (dnGen α h i) = redWL N ⟨w i, vN α i⟩ :=
  nLiftHom_gen _ _ _ _ _ i

@[simp] theorem evenFamDerivModelM_gen (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) (i : Fin (MarkedCore.coreRank h)) :
    evenFamDerivModelM α h hα hN w (dmGen α h i) = redWL N ⟨w i, vM α i⟩ :=
  mLiftHom_gen _ _ _ _ _ i

/-- The base component of the `N` model derivation is the mod-`2^N` shadow of the canonical
orientation: the model derivation is `χ_N`-shadowed. -/
theorem evenFamDerivModelN_isChiShadow (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) :
    IsChiShadowDeriv (chiN α h) (evenFamDerivModelN α h hα hN w) := by
  intro a
  let baseMap : ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ) :=
    { toFun := fun p ↦ p.g
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_of_discreteTopology }
  haveI := discreteTopology_levelQuot (DN α h : Type) (evenFam_isTopFinGen_DN α h)
    (isProP_DN α h) N
  let targetMap : ContinuousMonoidHom (DN α h : Type) ((ZMod (2 ^ N))ˣ) :=
    { toMonoidHom := (chiLevel (chiN α h) N).comp (levelMk (DN α h : Type) N)
      continuous_toFun := (continuous_of_discreteTopology
        (f := ⇑(chiLevel (chiN α h) N))).comp (continuous_levelMk (DN α h : Type) N) }
  have heq : baseMap.comp (evenFamDerivModelN α h hα hN w) = targetMap := by
    apply dn_hom_ext
    intro i
    change (evenFamDerivModelN α h hα hN w (dnGen α h i)).g =
      chiLevel (chiN α h) N (levelMk (DN α h : Type) N (dnGen α h i))
    rw [evenFamDerivModelN_gen, chiLevel_levelMk, GQ2.Roe.Labute.redWL_g,
      evenFam_chiN_dnGen]
  have htarget : targetMap a =
      Units.map (PadicInt.toZModPow N).toMonoidHom (chiN α h a) := by
    show chiLevel (chiN α h) N (levelMk (DN α h : Type) N a) = _
    rw [chiLevel_levelMk]
  rw [← htarget]
  exact DFunLike.congr_fun heq a

/-- The `M` model derivation is `χ_M`-shadowed. -/
theorem evenFamDerivModelM_isChiShadow (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) :
    IsChiShadowDeriv (chiM α h) (evenFamDerivModelM α h hα hN w) := by
  intro a
  let baseMap : ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ) :=
    { toFun := fun p ↦ p.g
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_of_discreteTopology }
  haveI := discreteTopology_levelQuot (DM α h : Type) (evenFam_isTopFinGen_DM α h)
    (isProP_DM α h) N
  let targetMap : ContinuousMonoidHom (DM α h : Type) ((ZMod (2 ^ N))ˣ) :=
    { toMonoidHom := (chiLevel (chiM α h) N).comp (levelMk (DM α h : Type) N)
      continuous_toFun := (continuous_of_discreteTopology
        (f := ⇑(chiLevel (chiM α h) N))).comp (continuous_levelMk (DM α h : Type) N) }
  have heq : baseMap.comp (evenFamDerivModelM α h hα hN w) = targetMap := by
    apply dm_hom_ext
    intro i
    change (evenFamDerivModelM α h hα hN w (dmGen α h i)).g =
      chiLevel (chiM α h) N (levelMk (DM α h : Type) N (dmGen α h i))
    rw [evenFamDerivModelM_gen, chiLevel_levelMk, GQ2.Roe.Labute.redWL_g,
      evenFam_chiM_dmGen]
  have htarget : targetMap a =
      Units.map (PadicInt.toZModPow N).toMonoidHom (chiM α h a) := by
    show chiLevel (chiM α h) N (levelMk (DM α h : Type) N a) = _
    rw [chiLevel_levelMk]
  rw [← htarget]
  exact DFunLike.congr_fun heq a

/-- The offset of the `N` model derivation at a generator. -/
theorem evenFamDerivModelN_u (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) (i : Fin (MarkedCore.coreRank h)) :
    (evenFamDerivModelN α h hα hN w (dnGen α h i)).u = PadicInt.toZModPow N (w i) := by
  rw [evenFamDerivModelN_gen]
  rfl

/-- The offset of the `M` model derivation at a generator. -/
theorem evenFamDerivModelM_u (α h : ℕ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (w : Fin (MarkedCore.coreRank h) → ℤ_[2]) (i : Fin (MarkedCore.coreRank h)) :
    (evenFamDerivModelM α h hα hN w (dmGen α h i)).u = PadicInt.toZModPow N (w i) := by
  rw [evenFamDerivModelM_gen]
  rfl

end Model

/-! ## §4 Mod-2 parity linear algebra on the Frattini quotient

The offsets of a `χ`-shadowed derivation reduce mod `2` to a group homomorphism into `𝔽₂`
(the twist dies: every `2`-adic unit is odd), and that homomorphism factors through the
level-`2` quotient.  Conversely, level-`2` functionals with prescribed values on a generating
family exist by pure counting: if the level-`2` quotient has order `2^n` then no `n − 1`
elements span it, so each index of a generating `n`-family carries a dual functional.  This
section is generic in the carrier; §5 instantiates it at the presented cores, where the
count is the committed Demushkin rank identity. -/

section Parity

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {N : ℕ}

/-- Two divides every power `2^N` with `N ≥ 1`; the witness the mod-`2` cast rides on. -/
theorem evenFam_two_dvd_two_pow (hN : 1 ≤ N) : 2 ∣ 2 ^ N :=
  dvd_pow_self 2 (by omega)

/-- Units of `ℤ/2^N` cast to `1` mod `2`: the mod-`2` shadow of any character is trivial. -/
theorem evenFam_castHom_unit (hN : 1 ≤ N) (u : (ZMod (2 ^ N))ˣ) :
    ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (u : ZMod (2 ^ N)) = 1 := by
  have hunit : IsUnit (ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2)
      (u : ZMod (2 ^ N))) := (u.isUnit).map _
  have hone : ∀ z : ZMod 2, IsUnit z → z = 1 := by decide
  exact hone _ hunit

/-- **The parity bridge**: divisibility by `2` in `ℤ/2^N` is vanishing of the mod-`2` cast. -/
theorem evenFam_two_dvd_iff_castHom_eq_zero (hN : 1 ≤ N) (x : ZMod (2 ^ N)) :
    (2 : ZMod (2 ^ N)) ∣ x ↔
      ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) x = 0 := by
  haveI : NeZero (2 ^ N) := ⟨by positivity⟩
  constructor
  · rintro ⟨y, rfl⟩
    rw [map_mul, show (2 : ZMod (2 ^ N)) = ((2 : ℕ) : ZMod (2 ^ N)) by push_cast; ring,
      map_natCast, show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
  · intro hcast
    have hval : x = ((x.val : ℕ) : ZMod (2 ^ N)) := (ZMod.natCast_rightInverse x).symm
    have hcastval : ((x.val : ℕ) : ZMod 2) = 0 := by
      rw [hval, map_natCast] at hcast
      exact hcast
    obtain ⟨y, hy⟩ := (CharP.cast_eq_zero_iff (ZMod 2) 2 x.val).mp hcastval
    refine ⟨((y : ℕ) : ZMod (2 ^ N)), ?_⟩
    rw [hval, hy]
    push_cast
    ring

/-- **The mod-2 offset functional of a word-lift-valued homomorphism.**  The twist is
invisible mod `2` because base values are units, so the offset reduces to an honest
homomorphism into `𝔽₂`; no shadow hypothesis is needed. -/
def evenFamParityHom (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N)) :
    G →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd
    (ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ g).u)
  map_one' := by
    show Multiplicative.ofAdd
      (ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ 1).u) = 1
    rw [map_one Φ, show ((1 : WL N)).u = 0 from rfl, map_zero]
    rfl
  map_mul' g g' := by
    have hmul : (Φ (g * g')).u = (Φ g).u + ((Φ g).g : ZMod (2 ^ N)) * (Φ g').u := by
      rw [map_mul Φ, FoxH.WordLift.mul_u, Units.smul_def, smul_eq_mul]
    have hcast : ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ (g * g')).u =
        ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ g).u +
          ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ g').u := by
      rw [hmul, map_add, map_mul, evenFam_castHom_unit hN ((Φ g).g), one_mul]
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, hcast]

/-- The parity functional vanishes on the second two-central step: offsets there are even. -/
theorem evenFamParityHom_eq_one_of_mem (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {d : G} (hd : d ∈ twoCentralSeries G 2) :
    evenFamParityHom hN Φ d = 1 := by
  have hdvd := GQ2.Dyadic.LSquare.stageDeriv_u_dvd hN Φ (by omega : 1 ≤ 2) hd
  rw [pow_one] at hdvd
  have hzero := (evenFam_two_dvd_iff_castHom_eq_zero hN _).mp hdvd
  show Multiplicative.ofAdd
    (ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ d).u) = 1
  rw [ofAdd_eq_one]
  exact hzero

/-- **The parity functional at level two**: the mod-2 offset functional descends to the
level-`2` quotient, where §4's counting lives. -/
def evenFamParityLevel (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N)) :
    levelQuot G 2 →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift (twoCentralSeries G 2) (evenFamParityHom hN Φ)
    (fun _ hd ↦ evenFamParityHom_eq_one_of_mem hN Φ hd)

@[simp] theorem evenFamParityLevel_levelMk (hN : 1 ≤ N)
    (Φ : ContinuousMonoidHom G (WL N)) (g : G) :
    evenFamParityLevel hN Φ (levelMk G 2 g) = evenFamParityHom hN Φ g :=
  rfl

/-- **Parity of an offset is a level-two statement**: divisibility of the offset by `2` at any
element is read off the parity functional at its level-`2` class. -/
theorem evenFam_two_dvd_u_iff (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N)) (g : G) :
    (2 : ZMod (2 ^ N)) ∣ (Φ g).u ↔
      evenFamParityLevel hN Φ (levelMk G 2 g) = 1 := by
  rw [evenFamParityLevel_levelMk, evenFam_two_dvd_iff_castHom_eq_zero hN]
  show _ ↔ Multiplicative.ofAdd
    (ZMod.castHom (evenFam_two_dvd_two_pow hN) (ZMod 2) (Φ g).u) = 1
  rw [ofAdd_eq_one]

end Parity

/-! ### §4.2 Dual functionals on a level-two quotient of known order

Pure counting, generic in the group: if `levelQuot G 2` has order `2^n` and `x : Fin n`
generates it, then no proper subfamily generates, so each slot carries a mod-`2` functional
that is `1` there and `0` on the other slots.  The proof runs through the `ℤ/2`-module
structure of the elementary abelian level-two quotient. -/

section Dual

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every element of the level-two quotient squares to one. -/
theorem evenFam_levelTwo_sq (q : levelQuot G 2) : q ^ 2 = 1 := by
  have hq : q ∈ zLayer G 1 := by
    rw [GQ2.Dyadic.LSquare.zLayer_one_eq_top]; trivial
  exact zLayer_sq G hq

/-- The level-two quotient is abelian. -/
theorem evenFam_levelTwo_comm (a b : levelQuot G 2) : a * b = b * a :=
  (zLayer_commute (z := a)
    (by rw [GQ2.Dyadic.LSquare.zLayer_one_eq_top]; trivial) b).eq

/-- **Dual functionals exist on a generated level-two quotient of full order.**  If the
level-two quotient has order `2^n` and an `n`-family generates it, every slot `i₀` carries a
functional into `𝔽₂` equal to `1` at slot `i₀` and `0` elsewhere.  The counting heart of the
family construction: an `(n-1)`-subfamily spans at most `2^(n-1)` classes. -/
theorem evenFam_exists_levelTwo_dual {n : ℕ}
    (hcard : Nat.card (levelQuot G 2) = 2 ^ n)
    (x : Fin n → levelQuot G 2)
    (htop : Subgroup.closure (Set.range x) = ⊤) (i₀ : Fin n) :
    ∃ φ : levelQuot G 2 →* Multiplicative (ZMod 2),
      φ (x i₀) = Multiplicative.ofAdd 1 ∧
      ∀ j : Fin n, j ≠ i₀ → φ (x j) = 1 := by
  classical
  -- the elementary abelian module structure
  letI : CommGroup (levelQuot G 2) :=
    { (inferInstance : Group (levelQuot G 2)) with mul_comm := evenFam_levelTwo_comm }
  letI : Module (ZMod 2) (Additive (levelQuot G 2)) :=
    AddCommGroup.zmodModule (fun q ↦ by
      show q.toMul ^ 2 = 1
      exact evenFam_levelTwo_sq q.toMul)
  set V := Additive (levelQuot G 2)
  set xa : Fin n → V := fun i ↦ Additive.ofMul (x i) with hxa
  -- the subfamily span
  set H : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range fun j : {j : Fin n // j ≠ i₀} ↦ xa j.1) with hH
  -- a submodule is in particular closed under the group operations of `levelQuot G 2`
  have hsubmul : ∀ (W : Submodule (ZMod 2) V) (a b : levelQuot G 2),
      Additive.ofMul a ∈ W → Additive.ofMul b ∈ W → Additive.ofMul (a * b) ∈ W :=
    fun W a b ha hb ↦ W.add_mem ha hb
  have hsubinv : ∀ (W : Submodule (ZMod 2) V) (a : levelQuot G 2),
      Additive.ofMul a ∈ W → Additive.ofMul a⁻¹ ∈ W :=
    fun W a ha ↦ W.neg_mem ha
  -- membership of every slot forces the submodule to be everything
  have hall : ∀ (W : Submodule (ZMod 2) V), (∀ j, xa j ∈ W) → ∀ v : V, v ∈ W := by
    intro W hW v
    have hmem : v.toMul ∈ Subgroup.closure (Set.range x) := by rw [htop]; trivial
    have hind := Subgroup.closure_induction
      (p := fun w _ ↦ Additive.ofMul w ∈ W)
      (by rintro a ⟨j, rfl⟩; exact hW j)
      W.zero_mem
      (fun a b _ _ ha hb ↦ hsubmul W a b ha hb)
      (fun a _ ha ↦ hsubinv W a ha) hmem
    exact hind
  -- the distinguished class is outside the subfamily span, by counting
  have hnotmem : xa i₀ ∉ H := by
    intro hmem
    have hWall : ∀ j, xa j ∈ H := by
      intro j
      by_cases hj : j = i₀
      · rwa [hj]
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    -- H is everything, so its card is the full 2^n
    have hHtop : ∀ v : V, v ∈ H := hall H hWall
    -- but H is spanned by n-1 vectors, so its card is at most 2^(n-1)
    have hsurj : Function.Surjective
        (fun c : {j : Fin n // j ≠ i₀} → ZMod 2 ↦
          (⟨∑ j, c j • xa j.1, Submodule.sum_mem H
            (fun j _ ↦ Submodule.smul_mem H _ (Submodule.subset_span ⟨j, rfl⟩))⟩ : H)) := by
      rintro ⟨v, hv⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hv
      exact ⟨c, Subtype.ext hc⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    have hcardfun : Nat.card ({j : Fin n // j ≠ i₀} → ZMod 2) =
        2 ^ Fintype.card {j : Fin n // j ≠ i₀} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun]
      congr 1
    have hlt : Fintype.card {j : Fin n // j ≠ i₀} < n := by
      simpa using Fintype.card_subtype_lt (p := fun j : Fin n ↦ j ≠ i₀)
        (x := i₀) (by simp)
    have hcardV : Nat.card H = 2 ^ n := by
      have hequiv : Function.Bijective (fun v : V ↦ (⟨v, hHtop v⟩ : H)) :=
        ⟨fun a b hab ↦ by simpa using congrArg Subtype.val hab,
          fun ⟨v, hv⟩ ↦ ⟨v, rfl⟩⟩
      rw [← Nat.card_congr (Equiv.ofBijective _ hequiv)]
      exact hcard
    have hlt2 : (2 : ℕ) ^ Fintype.card {j : Fin n // j ≠ i₀} < 2 ^ n :=
      Nat.pow_lt_pow_right one_lt_two hlt
    omega
  -- quotient by the subfamily span and identify it with 𝔽₂
  set q₀ : V ⧸ H := Submodule.Quotient.mk (xa i₀) with hq₀
  have hq₀ne : q₀ ≠ 0 := fun hc ↦
    hnotmem ((Submodule.Quotient.mk_eq_zero H).mp hc)
  have hspanq : ∀ w : V ⧸ H, ∃ c : ZMod 2, c • q₀ = w := by
    intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective H w
    have hvtop : v ∈ Submodule.span (ZMod 2) (Set.range xa) := by
      have := hall (Submodule.span (ZMod 2) (Set.range xa))
        (fun j ↦ Submodule.subset_span ⟨j, rfl⟩) v
      exact this
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hvtop
    refine ⟨c i₀, ?_⟩
    have hsum : H.mkQ (∑ i, c i • xa i) = c i₀ • q₀ := by
      rw [map_sum]
      rw [Finset.sum_eq_single i₀]
      · rw [map_smul]
        rfl
      · intro j _ hj
        have hjH : xa j ∈ H := Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
        have hz : H.mkQ (xa j) = 0 := (Submodule.Quotient.mk_eq_zero H).mpr hjH
        rw [map_smul, hz, smul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i₀) hi
    have hmk : H.mkQ v = c i₀ • q₀ := by rw [← hc, hsum]
    exact hmk.symm
  -- the induced functional
  have hker : ∀ c : ZMod 2, c • q₀ = 0 → c = 0 := by
    intro c hc
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with h0 | h1
    · exact h0
    · rw [h1, one_smul] at hc
      exact absurd hc hq₀ne
  set e : ZMod 2 ≃ₗ[ZMod 2] (V ⧸ H) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ZMod 2) (V ⧸ H) q₀)
      ⟨fun a b hab ↦ by
        have hsub : (a - b) • q₀ = 0 := by
          rw [sub_smul]
          rw [show LinearMap.toSpanSingleton (ZMod 2) (V ⧸ H) q₀ a = a • q₀ from rfl,
            show LinearMap.toSpanSingleton (ZMod 2) (V ⧸ H) q₀ b = b • q₀ from rfl] at hab
          rw [hab, sub_self]
        exact sub_eq_zero.mp (hker _ hsub),
        fun w ↦ hspanq w⟩ with he
  set delta : V →ₗ[ZMod 2] ZMod 2 := e.symm.toLinearMap.comp H.mkQ with hdelta
  have he1 : e 1 = q₀ := by
    rw [he]
    show LinearMap.toSpanSingleton (ZMod 2) (V ⧸ H) q₀ 1 = q₀
    rw [LinearMap.toSpanSingleton_apply_one]
  have hdelta_i₀ : delta (xa i₀) = 1 := by
    have hstep : delta (xa i₀) = e.symm (H.mkQ (xa i₀)) := rfl
    rw [hstep, show H.mkQ (xa i₀) = q₀ from rfl, ← he1, LinearEquiv.symm_apply_apply]
  have hdelta_off : ∀ j : Fin n, j ≠ i₀ → delta (xa j) = 0 := by
    intro j hj
    have hjH : xa j ∈ H := Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    have hz : H.mkQ (xa j) = 0 := (Submodule.Quotient.mk_eq_zero H).mpr hjH
    have hstep : delta (xa j) = e.symm (H.mkQ (xa j)) := rfl
    rw [hstep, hz, map_zero]
  -- repackage as a monoid homomorphism
  refine ⟨{ toFun := fun q ↦ Multiplicative.ofAdd (delta (Additive.ofMul q))
            map_one' := by
              show Multiplicative.ofAdd (delta 0) = 1
              rw [map_zero]
              rfl
            map_mul' := fun a b ↦ by
              show Multiplicative.ofAdd (delta (Additive.ofMul a + Additive.ofMul b)) = _
              rw [map_add]
              rfl }, ?_, ?_⟩
  · show Multiplicative.ofAdd (delta (xa i₀)) = Multiplicative.ofAdd 1
    rw [hdelta_i₀]
  · intro j hj
    show Multiplicative.ofAdd (delta (xa j)) = 1
    rw [hdelta_off j hj]
    rfl

end Dual

end

end GQ2.Dyadic.EvenFamily
