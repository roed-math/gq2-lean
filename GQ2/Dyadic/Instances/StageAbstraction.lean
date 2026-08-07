/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage

/-!
# The stage machinery, abstracted over (word, rank, rows)  (EV-4b)

This file lifts the level-three stage architecture of the odd-degree forward route —
`SqCyclotomicStageTuple` and its chain in
`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteStage.lean` and
`…LabuteLevelThreeSeed.lean` — to an arbitrary relator shape, so that the even-degree cores
`DN α h` / `DM α h` can reuse it without re-deriving any group theory.

## Parameters

* **word**: a `StageWord n` bundles a rank-`n` relator shape `word`, its naturality
  `map_word` (the `map_sqRelWord` clone), and its invariance `zshift` under coordinatewise
  shifts from the central exponent-two layer `Z_k` (the `sqRelWord_zLayer_shift` clone).
  `zshift_of_core_handles` derives `zshift` for any word of the campaign's core-plus-handles
  shape from the core case alone, reusing `handleWord_central_shift`.
* **rank**: the index type is `Fin n`; the L instance takes `n = SqCore.sqRank h = 3 + 2h`,
  the even instances take `n = MarkedCore.coreRank h = 4 + 2h`.
* **rows**: a single value table `v : Fin n → ℤ_[2]ˣ`.  A pinned constructor row records its
  cyclotomic value; a kernel (handle) row records the value `1`.  The five separate fibre
  fields of the committed L structures are recovered through converters in
  `GQ2/Dyadic/Instances/StageAbstractionLSq.lean`.

Beyond the standing (word, rank, rows) recommendation, the survey forced two refinements:

* the seed layer also consumes the **quadratic-initial Gram** of the word
  (`IsCupAdapted` contracts the field cup form against it), so `Frame.IsCupAdapted` takes a
  `gram` parameter; and
* the sharp exact-lifting seam must be **row-target-relative**: the committed
  `SharpExactLevelFibreLiftSupply` demands lifts at *every* target of `ℤ₂ˣ`, which is
  unprovable in even degree where the descended cyclotomic character is not surjective.  The
  machinery only ever lifts at the row values, so `RowExactLevelFibreLiftSupply` asks exactly
  for that; `rowSupply_of_sharpSupply` recovers the odd-degree situation.

The ambient group is an arbitrary profinite `G` with a character
`chi : ContinuousMonoidHom G ℤ_[2]ˣ`; nothing here mentions `GalK`, so the layer is equally
usable on the field side and on the model side.  The `sharpChiLevel` calculus is reused from
the committed stage file, where it is already word-generic.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.LSquare.SqCyclotomicStageTuple (sharpChiLevel sharpChiLevel_cast_eq_chiLevel
  sharpChiLevel_levelMk SharpExactLevelFibreLiftSupply)

/-! ## §1 The word datum -/

/-- A variable-rank relator shape together with the two facts the stage machinery consumes:
naturality along arbitrary monoid homomorphisms and invariance under coordinatewise central
exponent-two shifts.  The L instance is `SqCore.sqRelWord` with `map_sqRelWord` and
`sqRelWord_zLayer_shift`; the even instances are `MarkedCore.nRelWord α` / `mRelWord α`. -/
structure StageWord (n : ℕ) : Type 1 where
  /-- The relator shape, as a word in any group. -/
  word : ∀ {G : Type} [Group G], (Fin n → G) → G
  /-- Naturality of the shape (the `map_sqRelWord` clone). -/
  map_word : ∀ {G H F : Type} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]
    (φ : F) (m : Fin n → G), φ (word m) = word fun i ↦ φ (m i)
  /-- The shape is insensitive to coordinatewise shifts from the central exponent-two layer
  `Z_k` of the lower two-central tower (the `sqRelWord_zLayer_shift` clone). -/
  zshift : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}
    (z m : Fin n → levelQuot G (k + 1)), (∀ i, z i ∈ zLayer G k) →
    word (fun i ↦ z i * m i) = word m

/-- Central exponent-two shift invariance for any word of the campaign's core-plus-handles
shape follows from the core case: the handles are honest commutators, killed by
`handleWord_central_shift`.  The even tickets discharge `StageWord.zshift` for
`nRelWord α` / `mRelWord α` through this lemma with `c = 4`. -/
theorem zshift_of_core_handles {n c hh : ℕ}
    (coreW : ∀ {G : Type} [Group G], (Fin c → G) → G)
    (emb : Fin c → Fin n) (uIdx vIdx : Fin hh → Fin n)
    (w : ∀ {G : Type} [Group G], (Fin n → G) → G)
    (hw : ∀ {G : Type} [Group G] (m : Fin n → G),
      w m = coreW (fun a ↦ m (emb a)) *
        MarkedCore.handleWord (fun j ↦ m (uIdx j)) (fun j ↦ m (vIdx j)))
    (hcore : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}
      (z m : Fin c → levelQuot G (k + 1)), (∀ a, z a ∈ zLayer G k) →
      coreW (fun a ↦ z a * m a) = coreW m)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}
    (z m : Fin n → levelQuot G (k + 1)) (hz : ∀ i, z i ∈ zLayer G k) :
    w (fun i ↦ z i * m i) = w m := by
  calc
    w (fun i ↦ z i * m i) =
        coreW (fun a ↦ z (emb a) * m (emb a)) *
          MarkedCore.handleWord (fun j ↦ z (uIdx j) * m (uIdx j))
            (fun j ↦ z (vIdx j) * m (vIdx j)) := hw _
    _ = coreW (fun a ↦ m (emb a)) *
          MarkedCore.handleWord (fun j ↦ m (uIdx j)) (fun j ↦ m (vIdx j)) := by
        rw [hcore _ _ (fun a ↦ hz (emb a)),
          LSquare.handleWord_central_shift (fun j ↦ m (uIdx j)) (fun j ↦ m (vIdx j))
            (fun j ↦ z (uIdx j)) (fun j ↦ z (vIdx j))
            (fun j t ↦ zLayer_commute (hz (uIdx j)) t)
            (fun j t ↦ zLayer_commute (hz (vIdx j)) t)]
    _ = w m := (hw m).symm

variable {n : ℕ}

/-! ## §2 Level sets, defect calculus, and the correction interface

Clones of `sqStageZero`, `sqStageDefect`, `stageModified`, `stageShift`, and
`sqRawDefectReachable` with `SqCore.sqRelWord` replaced by `W.word`.  The proofs are the
committed proofs with the two word facts routed through the datum's fields. -/

section Defect

variable (W : StageWord n)

/-- A relator-killing generating marking of the `k`-th lower two-central quotient
(the `sqStageZero` clone). -/
def stageZero (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : ℕ) :
    Set (Fin n → levelQuot G k) :=
  {T | W.word T = 1 ∧ Subgroup.closure (Set.range T) = ⊤}

/-- Restriction of a marking down one level preserves the literal relation and generation. -/
theorem stageZero_levelProj
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {k : ℕ} {T : Fin n → levelQuot G (k + 1)}
    (hT : T ∈ stageZero W G (k + 1)) :
    (fun i ↦ levelProj G k (T i)) ∈ stageZero W G k := by
  obtain ⟨hrel, hgen⟩ := hT
  refine ⟨?_, closure_range_levelProj hgen⟩
  rw [← W.map_word (levelProj G k) T, hrel, map_one]

/-- The relator defect of the canonical coordinatewise lift to level `k+1`
(the `sqStageDefect` clone). -/
def stageDefect (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) (T : Fin n → levelQuot G k) : levelQuot G (k + 1) :=
  W.word (fun i ↦ canonLift G k (T i))

/-- Any coordinatewise lift computes the same defect. -/
theorem stageDefect_eq_of_lift
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) (T : Fin n → levelQuot G k)
    (T' : Fin n → levelQuot G (k + 1))
    (hT' : ∀ i, levelProj G k (T' i) = T i) :
    W.word T' = stageDefect W G k T := by
  choose z hz heq using fun i ↦ exists_zLayer_mul (G := G)
    (show levelProj G k (T' i) = levelProj G k (canonLift G k (T i)) by
      rw [hT', levelProj_canonLift])
  have hfun : T' = fun i ↦ z i * canonLift G k (T i) := funext heq
  rw [hfun, stageDefect]
  exact W.zshift z (fun i ↦ canonLift G k (T i)) hz

/-- The defect of a relator-killing marking lies in the graded kernel `Z_k`. -/
theorem stageDefect_mem_zLayer
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) {T : Fin n → levelQuot G k}
    (hrel : W.word T = 1) :
    stageDefect W G k T ∈ zLayer G k := by
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, stageDefect, W.map_word]
  simpa only [levelProj_canonLift] using hrel

/-- A tuple in `stageZero` has a graded-layer defect. -/
theorem stageZero_defect_mem_zLayer
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) {T : Fin n → levelQuot G k}
    (hT : T ∈ stageZero W G k) :
    stageDefect W G k T ∈ zLayer G k :=
  stageDefect_mem_zLayer W k hT.1

/-- Vanishing of the canonical defect is equivalent to the literal relation at any lift. -/
theorem stageDefect_eq_one_iff_lift_relation
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) (T : Fin n → levelQuot G k)
    (T' : Fin n → levelQuot G (k + 1))
    (hT' : ∀ i, levelProj G k (T' i) = T i) :
    stageDefect W G k T = 1 ↔ W.word T' = 1 := by
  rw [stageDefect_eq_of_lift W k T T' hT']

end Defect

/-- Coordinatewise right modification of a marking (the `stageModified` clone). -/
def stageModified {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}
    (base correction : Fin n → levelQuot G k) : Fin n → levelQuot G k :=
  fun i ↦ base i * correction i

section Shift

variable (W : StageWord n)

/-- The exact relator shift caused by a coordinatewise modification. -/
def stageShift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}
    (base correction : Fin n → levelQuot G (k + 1)) : levelQuot G (k + 1) :=
  (W.word base)⁻¹ * W.word (stageModified base correction)

/-- The load-bearing shift identity, fixing the multiplication orientation. -/
theorem word_stageModified
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}
    (base correction : Fin n → levelQuot G (k + 1)) :
    W.word (stageModified base correction) =
      W.word base * stageShift W base correction := by
  simp only [stageShift]
  group

/-- The presentation-theoretic actual-defect statement before exact fibres: one depth-`k-1`
correction hits the inverse of the current defect (the `sqRawDefectReachable` clone). -/
def rawDefectReachable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) (T : Fin n → levelQuot G k) : Prop :=
  ∃ correction : Fin n → levelQuot G (k + 1),
    (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) ∧
      stageShift W (fun i ↦ canonLift G k (T i)) correction =
        (stageDefect W G k T)⁻¹

end Shift

/-! ## §3 Oriented stage tuples -/

variable (W : StageWord n) (v : Fin n → ℤ_[2]ˣ)
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (chi : ContinuousMonoidHom G ℤ_[2]ˣ)

/-- A level-`k` marking for the relator shape `W`, with orientation stated by liftability to
the exact `chi`-fibres of the value table `v` (the `SqCyclotomicStageTuple` clone).  A pinned
constructor row carries its value; a handle row carries the value `1`, which is exactly
membership of a lift in `ker chi`. -/
structure Tuple (k : ℕ) where
  /-- The chosen rank-`n` marking of the `k`-th lower two-central quotient. -/
  generators : Fin n → levelQuot G k
  /-- Every row lifts into the exact `chi`-fibre of its table value. -/
  rows : ∀ i, ∃ x : G, chi x = v i ∧ generators i = levelMk G k x
  /-- The literal relator dies on the marking. -/
  relation : W.word generators = 1
  /-- The marking generates the finite level. -/
  topGen : Subgroup.closure (Set.range generators) = ⊤

namespace Tuple

variable {W v G chi}

/-- Restriction down the two-central tower preserves the relation, generation, and all exact
fibres (the `SqCyclotomicStageTuple.levelProj` clone). -/
def levelProj {k : ℕ} (T : Tuple W v G chi (k + 1)) : Tuple W v G chi k where
  generators i := GQ2.Roe.Labute.levelProj G k (T.generators i)
  rows i := by
    obtain ⟨x, hxchi, hx⟩ := T.rows i
    exact ⟨x, hxchi, by rw [hx, levelProj_levelMk]⟩
  relation := by
    rw [← W.map_word (GQ2.Roe.Labute.levelProj G k) T.generators, T.relation, map_one]
  topGen := closure_range_levelProj T.topGen

/-- The underlying tuple of a stage belongs to `stageZero`. -/
theorem generators_mem_stageZero {k : ℕ} (T : Tuple W v G chi k) :
    T.generators ∈ stageZero W G k :=
  ⟨T.relation, T.topGen⟩

end Tuple

/-! ## §4 Descent to arbitrary open quotients -/

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The plain homomorphism from a tower quotient to a coarser open quotient
(the `toOpenMap` clone, generic in `G`). -/
def openMap (k : ℕ) (U : OpenNormalSubgroup (ProfiniteGrp.of G))
    (hle : twoCentralSeries G k ≤ U.toSubgroup) :
    levelQuot G k →* G ⧸ U.toSubgroup :=
  QuotientGroup.lift (twoCentralSeries G k) (QuotientGroup.mk' U.toSubgroup) (by
    rw [QuotientGroup.ker_mk']
    exact hle)

omit [T2Space G] in
@[simp] theorem openMap_levelMk (k : ℕ)
    (U : OpenNormalSubgroup (ProfiniteGrp.of G))
    (hle : twoCentralSeries G k ≤ U.toSubgroup) (x : G) :
    openMap G k U hle (levelMk G k x) = QuotientGroup.mk x :=
  rfl

omit [T2Space G] in
theorem openMap_surjective (k : ℕ)
    (U : OpenNormalSubgroup (ProfiniteGrp.of G))
    (hle : twoCentralSeries G k ≤ U.toSubgroup) :
    Function.Surjective (openMap G k U hle) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨levelMk G k x, rfl⟩

/-- A relator-killing oriented marking of an arbitrary open quotient of `G`: the
model-independent content of `SqCyclotomicFiniteLevelEpiData`.  The committed adapter
`finiteLevelEpiDataOfTuple` (and, for the even cores, its `nLiftHom`/`mLiftHom` clones)
upgrades this datum to the marked epimorphism out of the presented model. -/
structure OpenTuple (U : OpenNormalSubgroup (ProfiniteGrp.of G)) where
  /-- The chosen rank-`n` tuple in the open quotient. -/
  generators : Fin n → G ⧸ U.toSubgroup
  /-- Every row lifts into the exact `chi`-fibre of its table value. -/
  rows : ∀ i, ∃ x : G, chi x = v i ∧ generators i = QuotientGroup.mk x
  /-- The literal relator dies on the tuple. -/
  relation : W.word generators = 1
  /-- The tuple generates the open quotient. -/
  topGen : Subgroup.closure (Set.range generators) = ⊤

namespace Tuple

variable {W v G chi}

/-- A single stage at any tower level contained in `U` produces the finite datum at `U`
(the `toFiniteLevelEpiData` clone, stopped before the presented model enters). -/
def toOpenTuple {k : ℕ} (T : Tuple W v G chi k)
    (U : OpenNormalSubgroup (ProfiniteGrp.of G))
    (hle : twoCentralSeries G k ≤ U.toSubgroup) :
    OpenTuple W v G chi U where
  generators i := openMap G k U hle (T.generators i)
  rows i := by
    obtain ⟨x, hxchi, hx⟩ := T.rows i
    refine ⟨x, hxchi, ?_⟩
    rw [hx]
    exact openMap_levelMk G k U hle x
  relation := by
    rw [← W.map_word (openMap G k U hle) T.generators, T.relation, map_one]
  topGen := by
    have h := congrArg (Subgroup.map (openMap G k U hle)) T.topGen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
      (openMap_surjective G k U hle), ← Set.range_comp] at h
    exact h

omit [T2Space G] in
/-- Regression: open-quotient descent records the literal relator shape. -/
theorem toOpenTuple_relation_regression {k : ℕ} (T : Tuple W v G chi k)
    (U : OpenNormalSubgroup (ProfiniteGrp.of G))
    (hle : twoCentralSeries G k ≤ U.toSubgroup) :
    W.word (T.toOpenTuple U hle).generators = 1 :=
  (T.toOpenTuple U hle).relation

omit [T2Space G] in
/-- Regression: every row of the descended tuple remains liftability to its exact fibre. -/
theorem toOpenTuple_rows_regression {k : ℕ} (T : Tuple W v G chi k)
    (U : OpenNormalSubgroup (ProfiniteGrp.of G))
    (hle : twoCentralSeries G k ≤ U.toSubgroup) (i : Fin n) :
    ∃ x : G, chi x = v i ∧ (T.toOpenTuple U hle).generators i = QuotientGroup.mk x :=
  (T.toOpenTuple U hle).rows i

/-! ## §5 The correction interface -/

/-- A depth-`k-1` correction whose modified canonical lifts remain in all exact fibres
(the `AdmissibleCorrection` clone). -/
structure AdmissibleCorrection {k : ℕ} (T : Tuple W v G chi k) where
  /-- The coordinatewise correction at level `k+1`. -/
  correction : Fin n → levelQuot G (k + 1)
  /-- The correction has depth `k-1`. -/
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)
  /-- Every modified row lies in the exact `chi`-fibre of its table value. -/
  rows : ∀ i, ∃ x : G, chi x = v i ∧
    stageModified (fun i ↦ canonLift G k (T.generators i)) correction i =
      levelMk G (k + 1) x

/-- The finite-precision correction: rows correct modulo `2^(k+1)` only
(the `TruncatedAdmissibleCorrection` clone). -/
structure TruncatedAdmissibleCorrection {k : ℕ} (T : Tuple W v G chi k) where
  /-- The coordinatewise correction at level `k+1`. -/
  correction : Fin n → levelQuot G (k + 1)
  /-- The correction has depth `k-1`. -/
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)
  /-- Every modified row has the correct character value modulo `2^(k+1)`. -/
  rows : ∀ i, chiLevel chi (k + 1)
      (stageModified (fun i ↦ canonLift G k (T.generators i)) correction i) =
    Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (v i)

/-- The sharp-precision correction: rows correct modulo `2^(k+2)`
(the `SharpAdmissibleCorrection` clone). -/
structure SharpAdmissibleCorrection {k : ℕ} (T : Tuple W v G chi k) (hk : 1 ≤ k) where
  /-- The coordinatewise correction at level `k+1`. -/
  correction : Fin n → levelQuot G (k + 1)
  /-- The correction has depth `k-1`. -/
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)
  /-- Every modified row has the correct character value modulo `2^(k+2)`. -/
  rows : ∀ i, sharpChiLevel chi (k + 1) (by omega)
      (stageModified (fun i ↦ canonLift G k (T.generators i)) correction i) =
    Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom (v i)

/-- Forgetting the fresh digit recovers the finite-precision correction. -/
def SharpAdmissibleCorrection.toTruncated {k : ℕ}
    {T : Tuple W v G chi k} {hk : 1 ≤ k}
    (Wc : SharpAdmissibleCorrection T hk) : TruncatedAdmissibleCorrection T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    rw [← sharpChiLevel_cast_eq_chiLevel chi (k + 1) (by omega), Wc.rows i]
    ext
    simp

end Tuple

/-! ## §6 Row-target-relative exact lifting

The committed `SharpExactLevelFibreLiftSupply` asks for exact lifts at *every* target of
`ℤ₂ˣ`, which is provable only when `chi` is surjective — true in odd degree, false in even
degree.  Every use in the stage machinery lifts at a row value, so the abstraction demands
only that.  In odd degree the full supply specialises (`rowSupply_of_sharpSupply`); in even
degree the image-relative filtration (ticket EV-4a) produces the row supply directly. -/

/-- Exact representatives exist in every sharp level coset whose fresh digit matches a *row
value* of the table `v`.  This is the row-relative weakening of
`SharpExactLevelFibreLiftSupply` forced by the even-degree lanes. -/
structure RowExactLevelFibreLiftSupply : Prop where
  /-- Exact lifting at each row target. -/
  lift : ∀ (m : ℕ) (hm : 2 ≤ m) (i : Fin n) (q : levelQuot G m),
    sharpChiLevel chi m hm q =
        Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom (v i) →
      ∃ x : G, chi x = v i ∧ q = levelMk G m x

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The full sharp supply restricts to the row supply at any value table. -/
theorem rowSupply_of_sharpSupply
    (H : SharpExactLevelFibreLiftSupply G chi) :
    RowExactLevelFibreLiftSupply v G chi :=
  ⟨fun m hm i q hq ↦ H.lift m hm (v i) q hq⟩

namespace Tuple

variable {W v G chi}

/-- Row-relative sharp lifting upgrades a sharp correction to exact fibres without changing
the level-`k+1` tuple (the `SharpAdmissibleCorrection.toAdmissible` clone). -/
def SharpAdmissibleCorrection.toAdmissible {k : ℕ}
    {T : Tuple W v G chi k} {hk : 1 ≤ k}
    (Wc : SharpAdmissibleCorrection T hk)
    (Hlift : RowExactLevelFibreLiftSupply v G chi) :
    AdmissibleCorrection T where
  correction := Wc.correction
  depth := Wc.depth
  rows i := by
    obtain ⟨x, hxchi, hx⟩ := Hlift.lift (k + 1) (by omega) i _ (Wc.rows i)
    exact ⟨x, hxchi, hx⟩

/-- The exact additional output missing from a truncated stage calculation: fix the fresh
digit while preserving the literal-word shift (the `FreshDigitStrictificationSupply`
clone). -/
def FreshDigitStrictificationSupply {k : ℕ}
    (T : Tuple W v G chi k) (hk : 1 ≤ k) : Prop :=
  ∀ Wc : TruncatedAdmissibleCorrection T,
    ∃ Wsharp : SharpAdmissibleCorrection T hk,
      stageShift W (fun i ↦ canonLift G k (T.generators i)) Wsharp.correction =
        stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction

/-- The exact arithmetic premise of one stage step: the inverse of the current defect is
realized by an admissible depth-`k-1` correction (the `DefectReachable` clone). -/
def DefectReachable {k : ℕ} (T : Tuple W v G chi k) : Prop :=
  ∃ Wc : AdmissibleCorrection T,
    stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction =
      (stageDefect W G k T.generators)⁻¹

/-- The Labute `SL1`+`SL2` output at finite precision (the `TruncatedDefectReachable`
clone). -/
def TruncatedDefectReachable {k : ℕ} (T : Tuple W v G chi k) : Prop :=
  ∃ Wc : TruncatedAdmissibleCorrection T,
    stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction =
      (stageDefect W G k T.generators)⁻¹

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The finite-precision output upgrades to exact fibres through the fresh digit and the
row-relative sharp lifting. -/
theorem TruncatedDefectReachable.toDefectReachable {k : ℕ}
    {T : Tuple W v G chi k} (H : TruncatedDefectReachable T)
    (hk : 1 ≤ k) (Hfresh : FreshDigitStrictificationSupply T hk)
    (Hlift : RowExactLevelFibreLiftSupply v G chi) :
    DefectReachable T := by
  obtain ⟨Wc, hW⟩ := H
  obtain ⟨Wsharp, hsharp⟩ := Hfresh Wc
  exact ⟨Wsharp.toAdmissible Hlift, hsharp.trans hW⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Forgetting the exact fibre witnesses leaves raw reachability. -/
theorem DefectReachable.toRaw {k : ℕ} {T : Tuple W v G chi k}
    (H : DefectReachable T) :
    rawDefectReachable W G k T.generators := by
  obtain ⟨Wc, hW⟩ := H
  exact ⟨Wc.correction, Wc.depth, hW⟩

/-- The exact-fibre upgrade isolated from the span calculation
(the `ExactFibreStrictification` clone). -/
def ExactFibreStrictification {k : ℕ} (T : Tuple W v G chi k) : Prop :=
  ∀ correction : Fin n → levelQuot G (k + 1),
    (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) →
    stageShift W (fun i ↦ canonLift G k (T.generators i)) correction =
      (stageDefect W G k T.generators)⁻¹ →
    ∃ Wc : AdmissibleCorrection T,
      stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction =
        stageShift W (fun i ↦ canonLift G k (T.generators i)) correction

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Raw reachability plus the exact-fibre upgrade is sufficient for the stage premise. -/
theorem DefectReachable.of_raw_of_exactFibreStrictification {k : ℕ}
    {T : Tuple W v G chi k}
    (Hraw : rawDefectReachable W G k T.generators)
    (Hstrict : ExactFibreStrictification T) : DefectReachable T := by
  obtain ⟨correction, hdepth, hkill⟩ := Hraw
  obtain ⟨Wc, hW⟩ := Hstrict correction hdepth hkill
  exact ⟨Wc, hW.trans hkill⟩

/-- A one-point crossed-derivation/span package sharpened to the current defect
(the `ActualDefectSpanSupply` clone). -/
structure ActualDefectSpanSupply {k : ℕ} (T : Tuple W v G chi k) where
  /-- The parameter space of the span calculation. -/
  Parameter : Type
  /-- Each parameter yields an admissible correction. -/
  correction : Parameter → AdmissibleCorrection T
  /-- The computed shift of each parameter. -/
  shiftValue : Parameter → zLayer G k
  /-- The computed shift agrees with the literal-word shift. -/
  realizes : ∀ p,
    stageShift W (fun i ↦ canonLift G k (T.generators i)) (correction p).correction =
      (shiftValue p : levelQuot G (k + 1))
  /-- Some parameter hits the inverse of the current defect. -/
  hitsDefect : ∃ p,
    (shiftValue p : levelQuot G (k + 1)) = (stageDefect W G k T.generators)⁻¹

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The one-point span package implies actual-defect reachability. -/
theorem ActualDefectSpanSupply.toDefectReachable {k : ℕ}
    {T : Tuple W v G chi k} (S : ActualDefectSpanSupply T) :
    DefectReachable T := by
  obtain ⟨p, hp⟩ := S.hitsDefect
  exact ⟨S.correction p, (S.realizes p).trans hp⟩

/-- Full correction surjectivity onto the graded layer (the `CorrectionSurjective` clone). -/
def CorrectionSurjective {k : ℕ} (T : Tuple W v G chi k) : Prop :=
  ∀ δ ∈ zLayer G k,
    ∃ Wc : AdmissibleCorrection T,
      stageShift W (fun i ↦ canonLift G k (T.generators i)) Wc.correction = δ

/-- A surjective crossed-derivation/span package
(the `CrossedDerivationSpanSupply` clone). -/
structure CrossedDerivationSpanSupply {k : ℕ} (T : Tuple W v G chi k) where
  /-- The parameter space of the span calculation. -/
  Parameter : Type
  /-- Each parameter yields an admissible correction. -/
  correction : Parameter → AdmissibleCorrection T
  /-- The computed shift of each parameter. -/
  shiftValue : Parameter → zLayer G k
  /-- The computed shift agrees with the literal-word shift. -/
  realizes : ∀ p,
    stageShift W (fun i ↦ canonLift G k (T.generators i)) (correction p).correction =
      (shiftValue p : levelQuot G (k + 1))
  /-- The shift map covers the graded layer. -/
  onto : Function.Surjective shiftValue

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A surjective span calculation implies the exact correction premise. -/
theorem CrossedDerivationSpanSupply.toCorrectionSurjective {k : ℕ}
    {T : Tuple W v G chi k} (S : CrossedDerivationSpanSupply T) :
    CorrectionSurjective T := by
  intro δ hδ
  obtain ⟨p, hp⟩ := S.onto ⟨δ, hδ⟩
  refine ⟨S.correction p, ?_⟩
  rw [S.realizes p]
  exact congrArg Subtype.val hp

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Full correction surjectivity reaches the actual defect. -/
theorem CorrectionSurjective.toDefectReachable {k : ℕ}
    {T : Tuple W v G chi k} (H : CorrectionSurjective T) :
    DefectReachable T := by
  have hδ : (stageDefect W G k T.generators)⁻¹ ∈ zLayer G k :=
    Subgroup.inv_mem _ (stageDefect_mem_zLayer W k T.relation)
  exact H _ hδ

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A covering span supply reaches the actual defect. -/
theorem CrossedDerivationSpanSupply.toDefectReachable {k : ℕ}
    {T : Tuple W v G chi k} (S : CrossedDerivationSpanSupply T) :
    DefectReachable T :=
  S.toCorrectionSurjective.toDefectReachable

/-! ## §7 The stage step and the upward induction -/

/-- An admissible correction with the exact defect-killing equation
(the `DefectKillingCorrection` clone). -/
structure DefectKillingCorrection {k : ℕ}
    (T : Tuple W v G chi k) extends AdmissibleCorrection T where
  /-- The correction's shift kills the current defect. -/
  kills : stageShift W (fun i ↦ canonLift G k (T.generators i)) correction =
    (stageDefect W G k T.generators)⁻¹

/-- Actual-defect reachability supplies a defect-killing admissible correction. -/
def DefectReachable.defectKillingCorrection {k : ℕ}
    (T : Tuple W v G chi k) (H : DefectReachable T) :
    DefectKillingCorrection T := by
  let Wc := Classical.choose H
  exact { Wc with kills := Classical.choose_spec H }

/-- Every non-arithmetic part of the stage step (the `DefectKillingCorrection.toNext`
clone): a defect-killing correction kills the literal relator at the next level, depth
preserves generation by the Frattini argument, and admissibility preserves all rows. -/
def DefectKillingCorrection.toNext {k : ℕ} (T : Tuple W v G chi k)
    (Wc : DefectKillingCorrection T) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    Tuple W v G chi (k + 1) where
  generators := stageModified (fun i ↦ canonLift G k (T.generators i)) Wc.correction
  rows := Wc.rows
  relation := by
    rw [word_stageModified, stageDefect_eq_of_lift W k T.generators
      (fun i ↦ canonLift G k (T.generators i)) (fun i ↦ levelProj_canonLift G k _),
      Wc.kills]
    exact mul_inv_cancel _
  topGen := by
    have hbase : Subgroup.closure
        (Set.range fun i ↦ canonLift G k (T.generators i)) = ⊤ := by
      refine eq_top_of_map_levelProj_eq_top G hfg hpro (by omega) ?_
      have himg : (GQ2.Roe.Labute.levelProj G k) ''
          (Set.range fun i ↦ canonLift G k (T.generators i)) =
            Set.range T.generators := by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun i ↦ levelProj_canonLift G k (T.generators i))
      rw [MonoidHom.map_closure, himg, T.topGen]
    exact closure_range_mul_eq_top_of_mem_lambdaImage_two G hfg hpro _ _ hbase
      (fun i ↦ lambdaImage_le_of_le (by omega) (Wc.depth i))

/-- The sharp stage theorem: reaching the inverse defect yields the next stage. -/
def DefectReachable.toNext {k : ℕ} (T : Tuple W v G chi k) (H : DefectReachable T)
    (hk : 3 ≤ k) (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    Tuple W v G chi (k + 1) :=
  (H.defectKillingCorrection T).toNext T hk hfg hpro

/-- Backward-compatible strong adapter through full correction surjectivity. -/
def CorrectionSurjective.toNext {k : ℕ} (T : Tuple W v G chi k)
    (H : CorrectionSurjective T) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    Tuple W v G chi (k + 1) :=
  H.toDefectReachable.toNext T hk hfg hpro

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Restrict a nonempty stage through finitely many tower maps. -/
private theorem stage_nonempty_of_add :
    ∀ (d k : ℕ), Nonempty (Tuple W v G chi (k + d)) → Nonempty (Tuple W v G chi k)
  | 0, _, H => by simpa using H
  | d + 1, k, H => by
      apply stage_nonempty_of_add d k
      exact H.elim fun T ↦ ⟨T.levelProj⟩

/-- Upward induction from the level-three base (the `stage_nonempty_three_add` clone). -/
private theorem stage_nonempty_three_add (base : Tuple W v G chi 3)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple W v G chi k, DefectReachable T) :
    ∀ d : ℕ, Nonempty (Tuple W v G chi (3 + d))
  | 0 => ⟨base⟩
  | d + 1 => by
      exact (stage_nonempty_three_add base hfg hpro Hcorr d).elim fun T ↦
        ⟨by simpa only [Nat.add_assoc] using
          (Hcorr (3 + d) (by omega) T).toNext T (by omega) hfg hpro⟩

/-- Exact levelwise nonemptiness from the level-three base and the correction premise
(the `stage_nonempty_all_levels` clone). -/
theorem stage_nonempty_all_levels (base : Tuple W v G chi 3)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple W v G chi k, DefectReachable T)
    (k : ℕ) : Nonempty (Tuple W v G chi k) := by
  apply stage_nonempty_of_add 3 k
  simpa only [Nat.add_comm] using stage_nonempty_three_add base hfg hpro Hcorr k

/-- Cofinality endpoint: the level-three base and the correction theorem produce the oriented
finite datum at every open normal quotient (the
`finiteLevelEpiData_nonempty_of_base_and_corrections` clone, stopped at the
model-independent open tuple). -/
theorem openTuple_nonempty_of_base_and_corrections (base : Tuple W v G chi 3)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple W v G chi k, DefectReachable T)
    (U : OpenNormalSubgroup (ProfiniteGrp.of G)) :
    Nonempty (OpenTuple W v G chi U) := by
  obtain ⟨k, hk⟩ := exists_twoCentralSeries_le G hfg hpro U.isOpen'
  exact (stage_nonempty_all_levels base hfg hpro Hcorr k).elim fun T ↦
    ⟨T.toOpenTuple U hk⟩

end Tuple

/-! ## §8 Transport from a presented model

The `ofOrientedEquiv` clone: an already-proved oriented equivalence with a marked model
(for L: `DSq h`; for the even lanes: `DN α h` / `DM α h`) yields an exact stage at every
level, and its defect is reachable.  This is the noncircular regression seam. -/

namespace Tuple

variable {W v G chi}
variable {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]

/-- Transport a marked relator-killing generating tuple of a model `D` through a
character-compatible equivalence `D ≃ G` (the `ofOrientedEquiv` clone). -/
def ofModel (gen : Fin n → D) (hrel : W.word gen = 1)
    (htop : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤)
    (hfgD : IsTopologicallyFinGen D)
    (chiD : ContinuousMonoidHom D ℤ_[2]ˣ) (hrows : ∀ i, chiD (gen i) = v i)
    (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv D G) (he : ∀ x, chi (e x) = chiD x) (k : ℕ) :
    Tuple W v G chi k where
  generators i := levelMk G k (e (gen i))
  rows i := ⟨e (gen i), (he (gen i)).trans (hrows i), rfl⟩
  relation := by
    calc
      W.word (fun i ↦ levelMk G k (e (gen i))) =
          levelMk G k (W.word fun i ↦ e (gen i)) :=
        (W.map_word (levelMk G k) fun i ↦ e (gen i)).symm
      _ = levelMk G k (e (W.word gen)) :=
        congrArg (levelMk G k) (W.map_word e.toMonoidHom gen).symm
      _ = 1 := by rw [hrel, map_one, map_one]
  topGen := by
    have hfgQ : IsTopologicallyFinGen G :=
      IsTopologicallyFinGen.of_surjective e.toMonoidHom e.continuous_toFun
        e.surjective hfgD
    letI := discreteTopology_levelQuot G hfgQ hpro k
    let p : ContinuousMonoidHom D (levelQuot G k) :=
      ⟨(levelMk G k).comp e.toMonoidHom,
        (continuous_levelMk G k).comp e.continuous_toFun⟩
    have hp : Function.Surjective p := (levelMk_surjective G k).comp e.surjective
    let H : Subgroup (levelQuot G k) :=
      Subgroup.closure (Set.range fun i ↦ p (gen i))
    have hclosed : IsClosed (H : Set (levelQuot G k)) := isClosed_discrete _
    have hgen : Subgroup.closure (Set.range gen) ≤ Subgroup.comap p.toMonoidHom H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hpreclosed : IsClosed (Subgroup.comap p.toMonoidHom H : Set D) :=
      hclosed.preimage p.continuous_toFun
    have htoppre : (Subgroup.closure (Set.range gen)).topologicalClosure ≤
        Subgroup.comap p.toMonoidHom H :=
      Subgroup.topologicalClosure_minimal _ hgen hpreclosed
    rw [htop] at htoppre
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hp y
    exact htoppre (by trivial)

@[simp] theorem ofModel_generators (gen : Fin n → D) (hrel : W.word gen = 1)
    (htop : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤)
    (hfgD : IsTopologicallyFinGen D)
    (chiD : ContinuousMonoidHom D ℤ_[2]ˣ) (hrows : ∀ i, chiD (gen i) = v i)
    (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv D G) (he : ∀ x, chi (e x) = chiD x) (k : ℕ) :
    (ofModel gen hrel htop hfgD chiD hrows hpro e he k).generators =
      fun i ↦ levelMk G k (e (gen i)) := rfl

/-- The model-transported stage has a reachable actual defect at every level (the
`ofOrientedEquiv_defectReachable` clone): the witness is the coordinatewise difference
between the canonical lift of the level-`k` marking and the same marking at level `k+1`. -/
theorem ofModel_defectReachable (gen : Fin n → D) (hrel : W.word gen = 1)
    (htop : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤)
    (hfgD : IsTopologicallyFinGen D)
    (chiD : ContinuousMonoidHom D ℤ_[2]ˣ) (hrows : ∀ i, chiD (gen i) = v i)
    (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv D G) (he : ∀ x, chi (e x) = chiD x) (k : ℕ) :
    DefectReachable (ofModel gen hrel htop hfgD chiD hrows hpro e he k) := by
  let T : Tuple W v G chi k := ofModel gen hrel htop hfgD chiD hrows hpro e he k
  let Tnext : Tuple W v G chi (k + 1) := ofModel gen hrel htop hfgD chiD hrows hpro e he (k + 1)
  let base := fun i ↦ canonLift G k (T.generators i)
  let correction := fun i ↦ (base i)⁻¹ * Tnext.generators i
  have hproj : ∀ i, GQ2.Roe.Labute.levelProj G k (Tnext.generators i) = T.generators i := by
    intro i
    simp only [T, Tnext, ofModel, levelProj_levelMk]
  have hmodified : stageModified base correction = Tnext.generators := by
    funext i
    simp only [stageModified, correction, base]
    group
  have hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i
    apply lambdaImage_le_of_le (Nat.sub_le k 1)
    change correction i ∈ zLayer G k
    rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker]
    simp only [correction, map_mul, map_inv, base, levelProj_canonLift, hproj]
    exact inv_mul_cancel _
  let Wc : AdmissibleCorrection T :=
    { correction := correction
      depth := hdepth
      rows := by
        intro i
        change ∃ x, chi x = v i ∧
          stageModified base correction i = levelMk G (k + 1) x
        rw [hmodified]
        exact Tnext.rows i }
  refine ⟨Wc, ?_⟩
  change stageShift W base correction = (stageDefect W G k T.generators)⁻¹
  rw [stageShift, hmodified, Tnext.relation, mul_one]
  rfl

end Tuple

/-! ## §9 The Frattini-frame seed layer

The `SqCyclotomicFrattiniFrame` clone: exact generators of `G` itself with the value table on
the nose and generation in the Frattini quotient, whose sole remaining obligation is the
literal relation modulo `λ₃`.  Cup-adaptedness contracts an abstract character pairing
against the word's quadratic-initial Gram — the Gram is word data, so it is a parameter. -/

/-- Actual generators with the exact value table and a generating image in the Frattini
quotient.  No level-three relation is part of this structure. -/
structure Frame where
  /-- The chosen rank-`n` tuple of actual elements of `G`. -/
  generators : Fin n → G
  /-- Every row has its table value on the nose. -/
  rows : ∀ i, chi (generators i) = v i
  /-- The tuple generates the level-two (Frattini) quotient. -/
  levelTwoGen : Subgroup.closure
    (Set.range fun i ↦ levelMk G 2 (generators i)) = ⊤

namespace Frame

variable {W v G chi}

/-- The sole level-three relation assertion left after constructing a frame.  The word is an
explicit argument: a frame is word-independent data, and only this relation ties it to `W`. -/
def LevelThreeRelation (W : StageWord n) (F : Frame v G chi) : Prop :=
  W.word (fun i ↦ levelMk G 3 (F.generators i)) = 1

/-- A frame is cup-adapted for a pairing `P` on mod-two characters when evaluation on its
generators identifies `P` with the word's quadratic-initial Gram `gram` (the `IsCupAdapted`
clone; for L, `P` is the field cup form transported through `characterClass` and `gram` is
`sqRelatorQuadraticInitialGram h`). -/
def IsCupAdapted (gram : (Fin n → Fin n → ZMod 2) → ZMod 2)
    (P : ContinuousMonoidHom G (Multiplicative (ZMod 2)) →
      ContinuousMonoidHom G (Multiplicative (ZMod 2)) → ZMod 2)
    (F : Frame v G chi) : Prop :=
  ∀ c d : ContinuousMonoidHom G (Multiplicative (ZMod 2)),
    P c d = gram (fun i j ↦ Multiplicative.toAdd (c (F.generators i)) *
      Multiplicative.toAdd (d (F.generators j)))

/-- A frame satisfying the literal relation modulo `λ₃` gives the exact level-three stage
(the `SqCyclotomicFrattiniFrame.toLevelThree` clone).  The `topGen` proof is derived: its
level-two image is `F.levelTwoGen` and the kernel of `Q₃ → Q₂` is Frattini. -/
def toLevelThree (F : Frame v G chi) (hrel : F.LevelThreeRelation W)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) : Tuple W v G chi 3 where
  generators i := levelMk G 3 (F.generators i)
  rows i := ⟨F.generators i, F.rows i, rfl⟩
  relation := hrel
  topGen := by
    let H : Subgroup (levelQuot G 3) :=
      Subgroup.closure (Set.range fun i ↦ levelMk G 3 (F.generators i))
    change H = ⊤
    refine eq_top_of_map_levelProj_eq_top G hfg hpro (by omega) ?_
    change (Subgroup.closure (Set.range fun i ↦ levelMk G 3 (F.generators i))).map
      (GQ2.Roe.Labute.levelProj G 2) = ⊤
    rw [MonoidHom.map_closure]
    have himage : (GQ2.Roe.Labute.levelProj G 2) ''
        (Set.range fun i ↦ levelMk G 3 (F.generators i)) =
      Set.range fun i ↦ levelMk G 2 (F.generators i) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i ↦ levelProj_levelMk G 2 (F.generators i))
    rw [himage]
    exact F.levelTwoGen

@[simp] theorem toLevelThree_generators (F : Frame v G chi)
    (hrel : F.LevelThreeRelation W)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    (F.toLevelThree hrel hfg hpro).generators =
      fun i ↦ levelMk G 3 (F.generators i) := rfl

/-- Regression: the seed adapter retains the literal relator shape. -/
theorem toLevelThree_word_regression (F : Frame v G chi)
    (hrel : F.LevelThreeRelation W)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    W.word (F.toLevelThree hrel hfg hpro).generators = 1 :=
  hrel

end Frame

end

end GQ2.Dyadic.StageGeneric

#print axioms GQ2.Dyadic.StageGeneric.zshift_of_core_handles
#print axioms GQ2.Dyadic.StageGeneric.stageZero_levelProj
#print axioms GQ2.Dyadic.StageGeneric.stageDefect_eq_of_lift
#print axioms GQ2.Dyadic.StageGeneric.stageDefect_mem_zLayer
#print axioms GQ2.Dyadic.StageGeneric.stageDefect_eq_one_iff_lift_relation
#print axioms GQ2.Dyadic.StageGeneric.word_stageModified
#print axioms GQ2.Dyadic.StageGeneric.Tuple.levelProj
#print axioms GQ2.Dyadic.StageGeneric.Tuple.toOpenTuple
#print axioms GQ2.Dyadic.StageGeneric.Tuple.toOpenTuple_relation_regression
#print axioms GQ2.Dyadic.StageGeneric.Tuple.SharpAdmissibleCorrection.toTruncated
#print axioms GQ2.Dyadic.StageGeneric.rowSupply_of_sharpSupply
#print axioms GQ2.Dyadic.StageGeneric.Tuple.SharpAdmissibleCorrection.toAdmissible
#print axioms GQ2.Dyadic.StageGeneric.Tuple.TruncatedDefectReachable.toDefectReachable
#print axioms GQ2.Dyadic.StageGeneric.Tuple.DefectReachable.toRaw
#print axioms GQ2.Dyadic.StageGeneric.Tuple.DefectReachable.of_raw_of_exactFibreStrictification
#print axioms GQ2.Dyadic.StageGeneric.Tuple.ActualDefectSpanSupply.toDefectReachable
#print axioms GQ2.Dyadic.StageGeneric.Tuple.CrossedDerivationSpanSupply.toCorrectionSurjective
#print axioms GQ2.Dyadic.StageGeneric.Tuple.CorrectionSurjective.toDefectReachable
#print axioms GQ2.Dyadic.StageGeneric.Tuple.CrossedDerivationSpanSupply.toDefectReachable
#print axioms GQ2.Dyadic.StageGeneric.Tuple.DefectKillingCorrection.toNext
#print axioms GQ2.Dyadic.StageGeneric.Tuple.DefectReachable.toNext
#print axioms GQ2.Dyadic.StageGeneric.Tuple.CorrectionSurjective.toNext
#print axioms GQ2.Dyadic.StageGeneric.Tuple.stage_nonempty_all_levels
#print axioms GQ2.Dyadic.StageGeneric.Tuple.openTuple_nonempty_of_base_and_corrections
#print axioms GQ2.Dyadic.StageGeneric.Tuple.ofModel
#print axioms GQ2.Dyadic.StageGeneric.Tuple.ofModel_defectReachable
#print axioms GQ2.Dyadic.StageGeneric.Frame.toLevelThree
#print axioms GQ2.Dyadic.StageGeneric.Frame.toLevelThree_word_regression
