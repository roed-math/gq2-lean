/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenWords

/-!
# W51-EV3AB, part b: even row tables, the index eliminator, and the model data

Ticket **EV-3b** of `docs/dyadic/ev4b-stage-abstraction.md` §4, building on EV-3a
(`GQ2/Dyadic/Instances/StageAbstractionEvenWords.lean`).  This file supplies the remaining
three inputs the even-degree forward route needs before the arithmetic tickets EV-3c/d/f/g
can run the W50 generic stage layer:

* the **row tables** `vN α`, `vM α : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ`, matching the
  frozen constructor tables of `MarkedCore.chiN` / `MarkedCore.chiM` — for `N_α` the letters
  `(x₀, x₁, σ, x₂)` carry `(1, nUnit α, 1, 1)` and for `M_α` the letters `(A, B, C₀, D)`
  carry `(1, -1, 1, mUnit α)`, with `1` on every handle letter.  Both are *literally* the
  markings out of which the committed characters are built, so the match is by construction
  rather than by a table comparison;
* the **index eliminator** `evenIndex_cases`, the four-letter analogue of the L file's
  `sqIndex_cases`, by index arithmetic on `Fin (4 + 2 * h)`; and
* the **model data**: topological finite generation of the two cores, the row identities of
  the two characters, and the transported stages `nTupleOfModel` / `mTupleOfModel` together
  with their reachable defects at every level.  That last item is the noncircular regression
  seam the board asks for: an already-proved oriented equivalence `DN α h ≃ G` carrying `chiN`
  to `chi` produces generic stages at every level whose defects are reachable, so the even
  instantiation of the stage induction is exercised end to end without any arithmetic input.

## The `α` hypothesis

`vN`, `vM`, `evenIndex_cases` and the two topological-generation lemmas need no hypothesis on
`α` at all.  The transported stages inherit EV-3a's honest `1 ≤ α` through
`nStageWord` / `mStageWord` and need nothing more, so nothing in this file is stated at the
even lane's standing `2 ≤ α`.

## Nothing here is consumed by the committed route

As with the two EV-4b files, this module is imported by nothing; it is the contract the
EV-3c/d/f/g tickets build against.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## §1 The two even row tables

Both tables are the committed `MarkedCore.coreMark` markings that *define* `chiN` and `chiM`
(`MarkedCore/Cores.lean` §4): four core values followed by `1` on every handle letter.  Taking
the tables to be those markings, rather than re-tabulating them, is what makes §3's row
identities immediate and rules out any drift from the frozen constructor tables. -/

/-- The **`N_α` row table**: `(x₀, x₁, σ, x₂) ↦ (1, nUnit α, 1, 1)` and `1` on every handle
letter — the value table of the committed `MarkedCore.chiN α h`. -/
def vN (α : ℕ) {h : ℕ} : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ :=
  MarkedCore.coreMark 1 (MarkedCore.nUnit α) 1 1

/-- The **`M_α` row table**: `(A, B, C₀, D) ↦ (1, -1, 1, mUnit α)` and `1` on every handle
letter — the value table of the committed `MarkedCore.chiM α h`. -/
def vM (α : ℕ) {h : ℕ} : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ :=
  MarkedCore.coreMark 1 (-1) 1 (MarkedCore.mUnit α)

section RowValues

variable (α : ℕ) {h : ℕ}

/-- The `x₀` row of the `N_α` table. -/
@[simp] theorem vN_zero : vN α (0 : Fin (MarkedCore.coreRank h)) = 1 :=
  MarkedCore.coreMark_zero _ _ _ _

/-- The `x₁` row of the `N_α` table: the orientation unit `v = -(1 + 2 ^ α)⁻¹`. -/
@[simp] theorem vN_one : vN α (1 : Fin (MarkedCore.coreRank h)) = MarkedCore.nUnit α :=
  MarkedCore.coreMark_one _ _ _ _

/-- The `σ` row of the `N_α` table. -/
@[simp] theorem vN_two : vN α (2 : Fin (MarkedCore.coreRank h)) = 1 :=
  MarkedCore.coreMark_two _ _ _ _

/-- The `x₂` row of the `N_α` table. -/
@[simp] theorem vN_three : vN α (3 : Fin (MarkedCore.coreRank h)) = 1 :=
  MarkedCore.coreMark_three _ _ _ _

/-- Handle rows of the `N_α` table are kernel rows. -/
@[simp] theorem vN_handleU (j : Fin h) : vN α (MarkedCore.handleIdxU j) = 1 :=
  MarkedCore.coreMark_handleU _ _ _ _ j

/-- Handle rows of the `N_α` table are kernel rows. -/
@[simp] theorem vN_handleV (j : Fin h) : vN α (MarkedCore.handleIdxV j) = 1 :=
  MarkedCore.coreMark_handleV _ _ _ _ j

/-- The `A` row of the `M_α` table. -/
@[simp] theorem vM_zero : vM α (0 : Fin (MarkedCore.coreRank h)) = 1 :=
  MarkedCore.coreMark_zero _ _ _ _

/-- The `B` row of the `M_α` table: the `-1 ∈ im χ` branch condition of EV-3c. -/
@[simp] theorem vM_one : vM α (1 : Fin (MarkedCore.coreRank h)) = -1 :=
  MarkedCore.coreMark_one _ _ _ _

/-- The `C₀` row of the `M_α` table. -/
@[simp] theorem vM_two : vM α (2 : Fin (MarkedCore.coreRank h)) = 1 :=
  MarkedCore.coreMark_two _ _ _ _

/-- The `D` row of the `M_α` table: the orientation unit `u = (1 - 2 ^ α)⁻¹`. -/
@[simp] theorem vM_three : vM α (3 : Fin (MarkedCore.coreRank h)) = MarkedCore.mUnit α :=
  MarkedCore.coreMark_three _ _ _ _

/-- Handle rows of the `M_α` table are kernel rows. -/
@[simp] theorem vM_handleU (j : Fin h) : vM α (MarkedCore.handleIdxU j) = 1 :=
  MarkedCore.coreMark_handleU _ _ _ _ j

/-- Handle rows of the `M_α` table are kernel rows. -/
@[simp] theorem vM_handleV (j : Fin h) : vM α (MarkedCore.handleIdxV j) = 1 :=
  MarkedCore.coreMark_handleV _ _ _ _ j

end RowValues

/-! ## §2 The index eliminator

The four-letter analogue of `StageAbstractionLSq.sqIndex_cases`.  The board offered either a
clone of `sqInitialAlphabetEquiv` at four core letters or direct index arithmetic; the
arithmetic is short enough to be preferable, and it avoids a dependency on the L alphabet
equivalence, which is stated only at rank `3 + 2h`. -/

/-- **Exhaustive case analysis on the even core alphabet**: every index of
`Fin (MarkedCore.coreRank h) = Fin (4 + 2 * h)` is one of the four core letters `0, 1, 2, 3`
or one of the two letters of the `j`-th handle pair. -/
theorem evenIndex_cases {h : ℕ} {P : Fin (MarkedCore.coreRank h) → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (hU : ∀ j : Fin h, P (MarkedCore.handleIdxU j))
    (hV : ∀ j : Fin h, P (MarkedCore.handleIdxV j))
    (i : Fin (MarkedCore.coreRank h)) : P i := by
  have hlt : (i : ℕ) < 4 + 2 * h := i.isLt
  rcases Nat.lt_or_ge (i : ℕ) 4 with hcore | hhandle
  · have hcases : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by omega
    rcases hcases with hv | hv | hv | hv
    · have hi : i = 0 := Fin.val_injective (hv.trans (MarkedCore.coreVal_zero h).symm)
      rw [hi]; exact h0
    · have hi : i = 1 := Fin.val_injective (hv.trans (MarkedCore.coreVal_one h).symm)
      rw [hi]; exact h1
    · have hi : i = 2 := Fin.val_injective (hv.trans (MarkedCore.coreVal_two h).symm)
      rw [hi]; exact h2
    · have hi : i = 3 := Fin.val_injective (hv.trans (MarkedCore.coreVal_three h).symm)
      rw [hi]; exact h3
  · obtain ⟨j, hj, hij⟩ :
        ∃ j : ℕ, j < h ∧ ((i : ℕ) = 4 + 2 * j ∨ (i : ℕ) = 5 + 2 * j) :=
      ⟨((i : ℕ) - 4) / 2, by omega, by omega⟩
    rcases hij with hij | hij
    · have hi : i = MarkedCore.handleIdxU ⟨j, hj⟩ :=
        Fin.val_injective (hij.trans (MarkedCore.handleIdxU_val ⟨j, hj⟩).symm)
      rw [hi]; exact hU _
    · have hi : i = MarkedCore.handleIdxV ⟨j, hj⟩ :=
        Fin.val_injective (hij.trans (MarkedCore.handleIdxV_val ⟨j, hj⟩).symm)
      rw [hi]; exact hV _

/-! ## §3 The two model inputs

`Tuple.ofModel` consumes, of the model side: the relator identity, topological generation, a
`Finset` witness of topological finite generation, and the row identities of the model's own
character.  The first is the committed `dn_relation` / `dm_relation` and the second the
committed `dn_topGen` / `dm_topGen`; the remaining two are supplied here. -/

/-- **`D_N` is topologically finitely generated**, in the `Finset` form `Tuple.ofModel` needs
(the `dsqFinsetTopGen` clone at the even core). -/
theorem dnFinsetTopGen (α h : ℕ) : IsTopologicallyFinGen (MarkedCore.DN α h : Type) := by
  classical
  refine ⟨Finset.univ.image (MarkedCore.dnGen α h), ?_⟩
  have hset : ((Finset.univ.image (MarkedCore.dnGen α h) :
      Finset (MarkedCore.DN α h : Type)) : Set (MarkedCore.DN α h : Type)) =
      Set.range (MarkedCore.dnGen α h) := by
    ext x
    simp
  rw [hset]
  exact MarkedCore.dn_topGen α h

/-- **`D_M` is topologically finitely generated**. -/
theorem dmFinsetTopGen (α h : ℕ) : IsTopologicallyFinGen (MarkedCore.DM α h : Type) := by
  classical
  refine ⟨Finset.univ.image (MarkedCore.dmGen α h), ?_⟩
  have hset : ((Finset.univ.image (MarkedCore.dmGen α h) :
      Finset (MarkedCore.DM α h : Type)) : Set (MarkedCore.DM α h : Type)) =
      Set.range (MarkedCore.dmGen α h) := by
    ext x
    simp
  rw [hset]
  exact MarkedCore.dm_topGen α h

/-- **The `N_α` character realizes the `N_α` row table on the presented generators.**  This is
the row hypothesis of `Tuple.ofModel`, assembled from the committed constructor simp lemmas
`chiN_dnX0`, `chiN_dnX1`, `chiN_dnSigma`, `chiN_dnX2`, `chiN_handleU`, `chiN_handleV` through
the index eliminator. -/
theorem chiN_dnGen (α h : ℕ) (i : Fin (MarkedCore.coreRank h)) :
    MarkedCore.chiN α h (MarkedCore.dnGen α h i) = vN α i := by
  refine evenIndex_cases
    (P := fun i ↦ MarkedCore.chiN α h (MarkedCore.dnGen α h i) = vN α i) ?_ ?_ ?_ ?_ ?_ ?_ i
  · exact (MarkedCore.chiN_dnX0 α h).trans (vN_zero α).symm
  · exact (MarkedCore.chiN_dnX1 α h).trans (vN_one α).symm
  · exact (MarkedCore.chiN_dnSigma α h).trans (vN_two α).symm
  · exact (MarkedCore.chiN_dnX2 α h).trans (vN_three α).symm
  · exact fun j ↦ (MarkedCore.chiN_handleU α h j).trans (vN_handleU α j).symm
  · exact fun j ↦ (MarkedCore.chiN_handleV α h j).trans (vN_handleV α j).symm

/-- **The `M_α` character realizes the `M_α` row table on the presented generators.** -/
theorem chiM_dmGen (α h : ℕ) (i : Fin (MarkedCore.coreRank h)) :
    MarkedCore.chiM α h (MarkedCore.dmGen α h i) = vM α i := by
  refine evenIndex_cases
    (P := fun i ↦ MarkedCore.chiM α h (MarkedCore.dmGen α h i) = vM α i) ?_ ?_ ?_ ?_ ?_ ?_ i
  · exact (MarkedCore.chiM_dmA α h).trans (vM_zero α).symm
  · exact (MarkedCore.chiM_dmB α h).trans (vM_one α).symm
  · exact (MarkedCore.chiM_dmC α h).trans (vM_two α).symm
  · exact (MarkedCore.chiM_dmD α h).trans (vM_three α).symm
  · exact fun j ↦ (MarkedCore.chiM_handleU α h j).trans (vM_handleU α j).symm
  · exact fun j ↦ (MarkedCore.chiM_handleV α h j).trans (vM_handleV α j).symm

/-! ## §4 The model-transported stages and the reachable-defect regression

The board's endpoint for EV-3b.  Given an oriented equivalence between a marked core and an
ambient group `G` — that is, a `ContinuousMulEquiv` carrying the core's canonical character to
`G`'s character — the generic transport `Tuple.ofModel` produces a stage at *every* level, and
`Tuple.ofModel_defectReachable` says each one has a reachable actual defect.

This is the even analogue of the `h = 0` regression seam of the odd route, and it is
noncircular: no arithmetic supply is consumed anywhere, so it exercises the even
instantiation of the word datum, the row table, and the whole correction interface using only
the committed presentation of the core. -/

section Model

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {α h : ℕ}

/-- **The `N_α` model-transported stage at level `k`**: an oriented equivalence
`e : D_N α h ≃ G` with `chi ∘ e = chiN α h` marks the `k`-th lower two-central quotient of `G`
by the images of the presented generators, with the `N_α` relator dying and every row landing
in the exact `chi`-fibre of `vN α`. -/
def nTupleOfModel (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DN α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiN α h x) (k : ℕ) :
    Tuple (nStageWord α h hα) (vN α) G chi k :=
  Tuple.ofModel (MarkedCore.dnGen α h) (MarkedCore.dn_relation α h)
    (MarkedCore.dn_topGen α h) (dnFinsetTopGen α h) (MarkedCore.chiN α h)
    (chiN_dnGen α h) hpro e he k

/-- **The `M_α` model-transported stage at level `k`**. -/
def mTupleOfModel (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DM α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiM α h x) (k : ℕ) :
    Tuple (mStageWord α h hα) (vM α) G chi k :=
  Tuple.ofModel (MarkedCore.dmGen α h) (MarkedCore.dm_relation α h)
    (MarkedCore.dm_topGen α h) (dmFinsetTopGen α h) (MarkedCore.chiM α h)
    (chiM_dmGen α h) hpro e he k

/-- The transported `N_α` marking is the image of the presented generators. -/
@[simp] theorem nTupleOfModel_generators (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DN α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiN α h x) (k : ℕ) :
    (nTupleOfModel hα hpro e he k).generators =
      fun i ↦ levelMk G k (e (MarkedCore.dnGen α h i)) := rfl

/-- The transported `M_α` marking is the image of the presented generators. -/
@[simp] theorem mTupleOfModel_generators (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DM α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiM α h x) (k : ℕ) :
    (mTupleOfModel hα hpro e he k).generators =
      fun i ↦ levelMk G k (e (MarkedCore.dmGen α h i)) := rfl

/-- **The `N_α` regression**: the model-transported stage has a reachable actual defect at
every level. -/
theorem nTupleOfModel_defectReachable (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DN α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiN α h x) (k : ℕ) :
    Tuple.DefectReachable (nTupleOfModel hα hpro e he k) :=
  Tuple.ofModel_defectReachable (W := nStageWord α h hα) (v := vN α)
    (MarkedCore.dnGen α h) (MarkedCore.dn_relation α h) (MarkedCore.dn_topGen α h)
    (dnFinsetTopGen α h) (MarkedCore.chiN α h) (chiN_dnGen α h) hpro e he k

/-- **The `M_α` regression**: the model-transported stage has a reachable actual defect at
every level. -/
theorem mTupleOfModel_defectReachable (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DM α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiM α h x) (k : ℕ) :
    Tuple.DefectReachable (mTupleOfModel hα hpro e he k) :=
  Tuple.ofModel_defectReachable (W := mStageWord α h hα) (v := vM α)
    (MarkedCore.dmGen α h) (MarkedCore.dm_relation α h) (MarkedCore.dm_topGen α h)
    (dmFinsetTopGen α h) (MarkedCore.chiM α h) (chiM_dmGen α h) hpro e he k

/-- **The EV-3b endpoint, `N_α` side**: for any oriented equivalence `e : D_N α h ≃ G` with
`chi ∘ e = chiN α h`, there is a generic stage at *every* level whose defect is reachable. -/
theorem exists_nTuple_defectReachable (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DN α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiN α h x) (k : ℕ) :
    ∃ T : Tuple (nStageWord α h hα) (vN α) G chi k, Tuple.DefectReachable T :=
  ⟨nTupleOfModel hα hpro e he k, nTupleOfModel_defectReachable hα hpro e he k⟩

/-- **The EV-3b endpoint, `M_α` side**. -/
theorem exists_mTuple_defectReachable (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DM α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiM α h x) (k : ℕ) :
    ∃ T : Tuple (mStageWord α h hα) (vM α) G chi k, Tuple.DefectReachable T :=
  ⟨mTupleOfModel hα hpro e he k, mTupleOfModel_defectReachable hα hpro e he k⟩

/-- Regression: through `DefectReachable.toRaw`, the endpoint lands on the *committed* even
relator shape, confirming that the whole chain runs on `MarkedCore.nRelWord α` and not on a
re-derived copy of it. -/
example (hα : 1 ≤ α) (hpro : IsProP 2 G)
    (e : ContinuousMulEquiv (MarkedCore.DN α h : Type) G)
    (he : ∀ x, chi (e x) = MarkedCore.chiN α h x) (k : ℕ) :
    ∃ correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1),
      (∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) ∧
        (MarkedCore.nRelWord α fun i ↦
              canonLift G k (levelMk G k (e (MarkedCore.dnGen α h i))))⁻¹ *
            MarkedCore.nRelWord α (fun i ↦
              canonLift G k (levelMk G k (e (MarkedCore.dnGen α h i))) * correction i) =
          (MarkedCore.nRelWord α fun i ↦
            canonLift G k (levelMk G k (e (MarkedCore.dnGen α h i))))⁻¹ :=
  (nTupleOfModel_defectReachable hα hpro e he k).toRaw

end Model

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins -/

#print axioms GQ2.Dyadic.StageGeneric.vN
#print axioms GQ2.Dyadic.StageGeneric.vM
#print axioms GQ2.Dyadic.StageGeneric.vN_zero
#print axioms GQ2.Dyadic.StageGeneric.vN_one
#print axioms GQ2.Dyadic.StageGeneric.vN_two
#print axioms GQ2.Dyadic.StageGeneric.vN_three
#print axioms GQ2.Dyadic.StageGeneric.vN_handleU
#print axioms GQ2.Dyadic.StageGeneric.vN_handleV
#print axioms GQ2.Dyadic.StageGeneric.vM_zero
#print axioms GQ2.Dyadic.StageGeneric.vM_one
#print axioms GQ2.Dyadic.StageGeneric.vM_two
#print axioms GQ2.Dyadic.StageGeneric.vM_three
#print axioms GQ2.Dyadic.StageGeneric.vM_handleU
#print axioms GQ2.Dyadic.StageGeneric.vM_handleV
#print axioms GQ2.Dyadic.StageGeneric.evenIndex_cases
#print axioms GQ2.Dyadic.StageGeneric.dnFinsetTopGen
#print axioms GQ2.Dyadic.StageGeneric.dmFinsetTopGen
#print axioms GQ2.Dyadic.StageGeneric.chiN_dnGen
#print axioms GQ2.Dyadic.StageGeneric.chiM_dmGen
#print axioms GQ2.Dyadic.StageGeneric.nTupleOfModel
#print axioms GQ2.Dyadic.StageGeneric.mTupleOfModel
#print axioms GQ2.Dyadic.StageGeneric.nTupleOfModel_generators
#print axioms GQ2.Dyadic.StageGeneric.mTupleOfModel_generators
#print axioms GQ2.Dyadic.StageGeneric.nTupleOfModel_defectReachable
#print axioms GQ2.Dyadic.StageGeneric.mTupleOfModel_defectReachable
#print axioms GQ2.Dyadic.StageGeneric.exists_nTuple_defectReachable
#print axioms GQ2.Dyadic.StageGeneric.exists_mTuple_defectReachable
